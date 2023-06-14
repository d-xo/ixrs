{-# LANGUAGE LambdaCase #-}

module Data.Functor.HFoldable.TH where

import Language.Haskell.TH
import Language.Haskell.TH.Datatype as TH.Abs
import Language.Haskell.TH.Datatype.TyVarBndr
import Control.Monad
import Data.Traversable
import Text.Read.Lex
import Data.Maybe

makeBaseFunctor :: Name -> Q [Dec]
makeBaseFunctor tyName = do
  (TyConI tyCon) <- reify tyName
  datatypeinfo <- reifyDatatype tyName
  rName <- newName "r"

  let cons = datatypeCons datatypeinfo
      -- variable parameters
      vars = map toTyVarBndr $ datatypeInstTypes datatypeinfo
      vars' = map VarT (typeVars vars)
      -- Name of base functor
      tyNameF = toFName tyName
      -- Recursive type
      s = conAppsT tyName vars'
      -- Additional argument
      r = VarT rName
      -- Vars
      varsF = vars ++ [plainTV rName]

      mkInstance n = InstanceD Nothing [] (ConT n `AppT` ConT tyName)

  patternFunc <- mkPatternFunc tyName tyCon

  -- instance Recursive
  projDec <- FunD (mkName "hproject") <$> mkMorphism id toFName cons
  let recursiveDec = mkInstance (mkName "HRecursive") [projDec]

  -- instance Corecursive
  embedDec <- FunD (mkName "hembed") <$> mkMorphism toFName id cons
  let corecursiveDec = mkInstance (mkName "HCorecursive") [embedDec]

  pure [patternFunc, recursiveDec, corecursiveDec]

mkPatternFunc :: Name -> Dec -> Q Dec
mkPatternFunc ty (DataD constraints name tyvars kind constructors derivs) = do
  unless (null constraints) $ error (show ty <> " has constraints")
  unless (null derivs) $ error (show ty <> " has deriving clauses")
  unless (isNothing kind) $ error (show ty <> " has kind: " <> show kind)
  unless (length tyvars == 1) $ error (show ty <> " has too many type parameters")

  recname <- newName "r"
  let ret = fromTyVarBndr $ head tyvars
      rec f = KindedTV recname f (AppT (AppT ArrowT ret) StarT)

  pure $
    DataD
      []
      (toFName name)
      (rec () : tyvars)
      Nothing
      (fmap (mkPFCon $ rec SpecifiedSpec) constructors)
      []
mkPatternFunc ty _ = error $ show ty <> " is not a data declaration"

mkPFCon :: TyVarBndr Specificity -> Con -> Con
mkPFCon rec@(KindedTV recname _ _) = \case
  -- monomorphic types. e.g.
  --   Sub :: Exp Number -> Exp Number -> Exp Number
  (GadtC [cname] args (AppT (ConT retname) rettype))
    -> ForallC
        [rec]
        []
        (GadtC
          [toFName cname]
          (fmap (mkArg recname retname) args)
           (AppT (AppT (ConT $ toFName retname) (VarT recname)) rettype)
        )
  -- polymorphic types. e.g.
  --   Var :: Text -> Exp t
  --   Eq  :: Exp t -> Exp t -> Exp Boolean
  (ForallC ts ctx (GadtC [cname] args (AppT (ConT retname) rettype)))
    -> ForallC
         (rec : ts)
         ctx
         (GadtC
           [toFName cname]
           (fmap (mkArg recname retname) args)
           (AppT (AppT (ConT $ toFName retname) (VarT recname)) rettype)
         )
  c -> error $ "unexpected constructor type: " <> show c
mkPFCon _ = error "unexpected typevar"

mkArg :: Name -> Name -> BangType -> BangType
mkArg recname retname bt@(bng,AppT (ConT cname) t)
  | retname == cname = (bng, AppT (VarT recname) t)
  | otherwise = bt
mkArg _ _ a = a

-- | makes clauses to rename constructors
mkMorphism
    :: (Name -> Name)
    -> (Name -> Name)
    -> [ConstructorInfo]
    -> Q [Clause]
mkMorphism nFrom nTo args = for args $ \ci -> do
    let n = constructorName ci
    fs <- replicateM (length (constructorFields ci)) (newName "x")
    pure $ Clause [ConP (nFrom n) [] (map VarP fs)]                   -- patterns
                  (NormalB $ foldl AppE (ConE $ nTo n) (map VarE fs)) -- body
                  []                                                  -- where dec


fromTyVarBndr :: TyVarBndr () -> Kind
fromTyVarBndr (KindedTV _ _ k) = k
fromTyVarBndr (PlainTV _ _)    = error "cannot extract kind from PlainTV"

toTyVarBndr :: Type -> TyVarBndr ()
toTyVarBndr (VarT n)          = plainTV n
toTyVarBndr (SigT (VarT n) k) = kindedTV n k
toTyVarBndr _                 = error "toTyVarBndr"

-- | Extract type variables
typeVars :: [TyVarBndr_ flag] -> [Name]
typeVars = map tvName

toFName :: Name -> Name
toFName = mkName . f . nameBase
  where
    f name | isInfixName name = name ++ "$"
           | otherwise        = name ++ "F"

    isInfixName :: String -> Bool
    isInfixName = all isSymbolChar

-- | Apply arguments to a type constructor.
conAppsT :: Name -> [Type] -> Type
conAppsT conName = foldl AppT (ConT conName)
