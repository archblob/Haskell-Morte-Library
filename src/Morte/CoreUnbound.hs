{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE UndecidableInstances  #-}

module Morte.CoreUnbound (
      fromMtExpr
    , toMtExpr
    , typeOf
    , normalize
    ) where


import Prelude hiding (pi)
import Control.Applicative hiding (Const)
import Control.Monad
import Control.Monad.Trans.Maybe
import Control.Monad.Morph (lift)
import Control.Monad.Trans.Except
import Unbound.LocallyNameless
import Control.Monad.Trans.Either

import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

import Morte.Core (Const(..))
import qualified Morte.Core as Mt

import Data.Text.Lazy (unpack, pack)

star :: Expr
star = Const Star

box :: Expr
box = Const Box

lam :: String -> Expr -> Expr -> Expr
lam b ty te = Lam $ bind (string2Name b, embed ty) te

pi :: String -> Expr -> Expr -> Expr
pi b ty te = Pi $ bind (string2Name b, embed ty) te

var :: String -> Expr
var = Var . string2Name

app :: Expr -> Expr -> Expr
app e1 e2 = App e1 e2

type Context = Map (Name Expr) Expr

type M a = FreshM a


toMtExpr :: Expr -> M (Mt.Expr a)
toMtExpr e = case e of
        Const c  -> return $ Mt.Const c
        Var n    -> return $ Mt.Var $ Mt.V (pack (name2String n)) (fromIntegral (name2Integer n))
        App f a  -> do
            f' <- toMtExpr f
            a' <- toMtExpr a
            return $ Mt.App f' a'
        Lam bnd  -> do
            ((x,_Ae),b') <- unbind bnd
            _A <- toMtExpr $ unembed _Ae
            b  <- toMtExpr b'
            return $ Mt.Lam (pack (name2String x)) _A b
        Pi bnd   -> do
            ((x,_Ae),_B') <- unbind bnd
            _A <- toMtExpr $ unembed _Ae
            _B <- toMtExpr _B'
            return $ Mt.Pi (pack (name2String x)) _A _B

fromMtExpr :: Mt.Expr a -> Expr
fromMtExpr mte = case mte of
        Mt.Const c        -> Const c
        Mt.Var (Mt.V t _) -> Var $ string2Name $ unpack t
        Mt.Lam t a b      -> lam (unpack t) (fromMtExpr a) (fromMtExpr b)
        Mt.Pi  t a b      -> pi  (unpack t) (fromMtExpr a) (fromMtExpr b)
        Mt.App f a        -> app (fromMtExpr f) (fromMtExpr a)
        Mt.Embed    _     -> undefined

data Expr =
    Const Const
  | Var (Name Expr)
  | Lam (Bind (Name Expr, Embed Expr) Expr)
  | Pi  (Bind (Name Expr, Embed Expr) Expr)
  | App Expr Expr 
    deriving Show

$(derive [''Const])
$(derive [''Expr])

instance Alpha Const
instance Alpha Expr

instance Subst Expr Const where
    isvar _ = Nothing

instance Subst Expr Expr where
    isvar (Var v) = Just (SubstName v)
    isvar _       = Nothing

-- | Reduce an expression to weak head normal form
whnf :: Expr -> M Expr
whnf e = case e of
    App f a -> do
        e <- whnf f
        case e of
            Lam bnd -> do
                ((x,_), b) <- unbind bnd
                let b' = subst x a b
                whnf b'
            _       -> return e
    _       -> return e

data TypeMessage
    = UnboundVariable
    | InvalidInputType Expr
    | InvalidOutputType Expr
    | NotAFunction
    | TypeMismatch Expr Expr
    | Untyped Const
        deriving Show

data TypeError = TypeError
      { context     :: Context
      , current     :: Expr
      , typeMessage :: TypeMessage
      } deriving Show

type TcM = EitherT TypeError FreshM Expr

axiom :: Const -> Either TypeError Const
axiom Star = return Box
axiom Box  = Left (TypeError M.empty (Const Box) (Untyped Box))

rule :: Const -> Const -> Either TypeError Const
rule Star Box  = return Box
rule Star Star = return Star
rule Box  Box  = return Box
rule Box  Star = return Star

typeWith :: Context -> Expr -> TcM
typeWith ctx e = case e of
    Const c -> hoistEither $ fmap Const $ axiom c
    Var x   -> case M.lookup x ctx of
        Nothing -> hoistEither $ Left $ TypeError ctx e UnboundVariable
        Just a  -> return a
    Lam bnd -> do
        ((x,_Ae),b) <- lift $ unbind bnd
        let _A   = unembed _Ae
            ctx' = M.insert x _A ctx
        _B <- typeWith ctx' b
        let p = Pi $ bind (x,embed _A) _B
        _t <- typeWith ctx p
        return p
    Pi bnd -> do
        ((x,_Ae),_B) <- lift $ unbind bnd
        let _A = unembed _Ae
        eS' <- typeWith ctx _A
        eS  <- lift $ whnf eS'
        s <- hoistEither $ case eS of
                Const s -> return s
                _       -> Left $ TypeError ctx e (InvalidInputType _A)
        let ctx' = M.insert x _A ctx
        eT' <- typeWith ctx' _B
        eT  <- lift $ whnf eT'
        t <- hoistEither $ case eT of
                Const t -> return t
                _       -> Left $ TypeError ctx' e (InvalidOutputType _B)

        hoistEither $ fmap Const (rule s t)
    App f a -> do
        e'' <- typeWith ctx f
        e'  <- lift $ whnf e''
        (x,_A,_B) <- case e' of
                        Pi bnd -> do
                            ((x,_Ae),_B) <- lift $ unbind bnd
                            let _A = unembed _Ae
                            return (x,_A,_B)
                        _      -> hoistEither $ Left (TypeError ctx e NotAFunction)
        _A' <- typeWith ctx a
        if aeq _A _A'
            then return $ subst x a _B
            else do
                nf_A <- lift $ normalize _A
                nf_A' <- lift $ normalize _A'
                hoistEither $ Left $ TypeError ctx e (TypeMismatch nf_A nf_A')

typeOf :: Expr -> TcM
typeOf e = typeWith M.empty e

normalize :: Expr -> M Expr
normalize e = case e of
    Lam bnd -> do
        ((x,_Ae),b) <- unbind bnd
        b' <- normalize b
        let e' = do
             let _A = unembed _Ae
             _A' <- normalize _A
             return $ Lam $ bind (x, embed _A') b' 
        case b' of
            App f a -> case a of
                         Var v | v == x && x `S.notMember` fv f -> return f
                         _                                      -> e'
            _       -> e'
    Pi bnd -> do
        ((x,_Ae),_B) <- unbind bnd
        let _A = unembed _Ae
        _A' <- normalize _A
        _B' <- normalize _B
        return $ Pi $ bind (x, embed _A') _B'
    App f a -> do
        f' <- normalize f
        case f' of
            Lam bnd -> do
                ((x,_),b) <- unbind bnd
                a' <- normalize a
                let b' = subst x a' b
                normalize b'
            f''     -> do
                    a' <- normalize a
                    return $ App f' a'
    Var _   -> return e
    Const _ -> return e
