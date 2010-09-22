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

deriveUnpack :: Name -> Q [Dec]
deriveUnpack typName = do
  TyConI (DataD cxt name tyVarBndrs cons names) <- reify typName
  
  return
    [ InstanceD [] (AppT (ConT ''Unpackable) (ConT name))
      [ FunD 'get [Clause [] (NormalB $ ch $ map body cons) []]
        ]]
        
  where
    body (NormalC conName elms) =
      DoE
      [ BindS (tupOrList $ map VarP names) (VarE 'get)
      , NoBindS $ AppE (VarE 'return) $ foldl AppE (ConE conName) $ map VarE names ]
        where
          names = zipWith (\ix _ -> mkName $ "a" ++ show (ix :: Int)) [1..] elms

    tupOrList ls
      | length ls <= 1 = ListP ls
      | otherwise = TupP ls

    ch = foldl1 (\e f -> AppE (AppE (VarE '(<|>)) e) f)

derivePack :: Name -> Q [Dec]
derivePack typName = do
  TyConI (DataD cxt name tyVarBndrs cons names) <- reify typName
  
  return
    [ InstanceD [] (AppT (ConT ''Packable) (ConT name))
      [ FunD 'put (map body cons)
        ]]
        
  where
    body (NormalC conName elms) =
      Clause
        [ ConP conName $ map VarP names ]
        (NormalB $ AppE (VarE 'put) $ tupOrList $ map VarE names) []
      where
        names = zipWith (\ix _ -> mkName $ "a" ++ show (ix :: Int)) [1..] elms

    tupOrList ls
      | length ls <= 1 = ListE ls
      | otherwise = TupE ls

deriveObject :: Name -> Q [Dec]
deriveObject typName = do
  g <- derivePack typName
  p <- deriveUnpack typName
  {-
  TyConI (DataD cxt name tyVarBndrs cons names) <- reify typName
  let o = InstanceD [] (AppT (ConT ''OBJECT) (ConT name))
          [ FunD 'toObject (map toObjectBody cons) ]
  -}
  return $ g ++ p -- ++ [o]
{-
  where
    toObjectBody (NormalC conName elms) =
      Clause
        [ ConP conP
-}
