{-# Language TemplateHaskell #-}

module Data.MessagePack.Derive (
  derivePack,
  deriveUnpack,
  deriveObject,
  ) where

import Control.Applicative
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
      DoE
      [ BindS (tupOrListP $ map VarP names) (VarE 'get)
      , NoBindS $ AppE (VarE 'return) $ foldl AppE (ConE conName) $ map VarE names ]
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
      DoE
      [ BindS (tupOrListP $ map VarP names) (AppE (VarE 'tryFromObject) (VarE oname))
      , NoBindS $ AppE (VarE 'return) $ foldl AppE (ConE conName) $ map VarE names ]
        where
          names = zipWith (\ix _ -> mkName $ "a" ++ show (ix :: Int)) [1..] elms
    tryFromObjectBody (RecC conName elms) =
      tryFromObjectBody (NormalC conName $ map (\(_, b, c) -> (b, c)) elms)

    oname = mkName "o"
    ch = foldl1 (\e f -> AppE (AppE (VarE '(<|>)) e) f)

tupOrListP :: [Pat] -> Pat
tupOrListP ls
  | length ls <= 1 = ListP ls
  | otherwise = TupP ls

tupOrListE :: [Exp] -> Exp
tupOrListE ls
  | length ls <= 1 = ListE ls
  | otherwise = TupE ls
