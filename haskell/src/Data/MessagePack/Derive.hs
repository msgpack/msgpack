{-# Language TemplateHaskell #-}

module Data.MessagePack.Derive (
  derivePack,
  deriveUnpack,
  deriveObject,
  ) where

import Control.Applicative
import Control.Monad
import Language.Haskell.TH

import Data.MessagePack.Pack
import Data.MessagePack.Unpack
import Data.MessagePack.Object

deriveUnpack :: Name -> Q [Dec]
deriveUnpack typName = do
  TyConI (DataD _ name _ cons _) <- reify typName
  
  return
    [ InstanceD [] (AppT (ConT ''Unpackable) (ConT name))
      [ FunD 'get [Clause [] (NormalB $ ch $ map body cons) []]
        ]]
        
  where
    body (NormalC conName elms) =
      DoE $
      tupOrListP (map VarP names) (VarE 'get) ++
      [ NoBindS $ AppE (VarE 'return) $ foldl AppE (ConE conName) $ map VarE names ]
        where
          names = zipWith (\ix _ -> mkName $ "a" ++ show (ix :: Int)) [1..] elms

    body (RecC conName elms) =
      body (NormalC conName $ map (\(_, b, c) -> (b, c)) elms)

    ch = foldl1 (\e f -> AppE (AppE (VarE '(<|>)) e) f)

derivePack :: Name -> Q [Dec]
derivePack typName = do
  TyConI (DataD _ name _ cons _) <- reify typName
  
  return
    [ InstanceD [] (AppT (ConT ''Packable) (ConT name))
      [ FunD 'put (map body cons)
        ]]
        
  where
    body (NormalC conName elms) =
      Clause
        [ ConP conName $ map VarP names ]
        (NormalB $ AppE (VarE 'put) $ tupOrListE $ map VarE names) []
      where
        names = zipWith (\ix _ -> mkName $ "a" ++ show (ix :: Int)) [1..] elms

    body (RecC conName elms) =
      body (NormalC conName $ map (\(_, b, c) -> (b, c)) elms)

deriveObject :: Name -> Q [Dec]
deriveObject typName = do
  g <- derivePack typName
  p <- deriveUnpack typName

  TyConI (DataD _ name _ cons _) <- reify typName
  let o = InstanceD [] (AppT (ConT ''OBJECT) (ConT name))
          [ FunD 'toObject (map toObjectBody cons),
            FunD 'tryFromObject [Clause [ VarP oname ]
                                 (NormalB $ ch $ map tryFromObjectBody cons) []]]

  return $ g ++ p ++ [o]
  where
    toObjectBody (NormalC conName elms) =
      Clause
        [ ConP conName $ map VarP names ]
        (NormalB $ AppE (VarE 'toObject) $ tupOrListE $ map VarE names) []
      where
        names = zipWith (\ix _ -> mkName $ "a" ++ show (ix :: Int)) [1..] elms
    toObjectBody (RecC conName elms) =
      toObjectBody (NormalC conName $ map (\(_, b, c) -> (b, c)) elms)

    tryFromObjectBody (NormalC conName elms) =
      DoE $
      tupOrListP (map VarP names) (AppE (VarE 'tryFromObject) (VarE oname)) ++
      [ NoBindS $ AppE (VarE 'return) $ foldl AppE (ConE conName) $ map VarE names ]
        where
          names = zipWith (\ix _ -> mkName $ "a" ++ show (ix :: Int)) [1..] elms
    tryFromObjectBody (RecC conName elms) =
      tryFromObjectBody (NormalC conName $ map (\(_, b, c) -> (b, c)) elms)

    oname = mkName "o"
    ch = foldl1 (\e f -> AppE (AppE (VarE '(<|>)) e) f)

tupOrListP :: [Pat] -> Exp -> [Stmt]
tupOrListP ls e
  | length ls == 0 =
    let lsname = mkName "ls" in
    [ BindS (VarP lsname) e
    , NoBindS $ AppE (VarE 'guard) $ AppE (VarE 'null) $ SigE (VarE lsname) (AppT ListT (ConT ''())) ]
  | length ls == 1 = [ BindS (ListP ls) e ]
  | otherwise = [ BindS (TupP ls) e ]

tupOrListE :: [Exp] -> Exp
tupOrListE ls
  | length ls == 0 = SigE (ListE []) (AppT ListT (ConT ''()))
  | length ls == 1 = ListE ls
  | otherwise = TupE ls
