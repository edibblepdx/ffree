-- Where f is a functor. This Free monad structure is similar to that of a linked
-- list, wherein Free is a functor and the next element, or Pure. "A free monad
-- allows chaining computations with markers to satisfy the type system, but
-- otherwise imposes no deeper semantics itself" (Wikipedia). The Maybe monad is
-- a free monad entirely through the Just and Nothing markers.

-- import Data.Functor.Sum
import System.Exit

data Free f a = Pure a | Free (f (Free f a))

instance (Functor f) => Functor (Free f) where
  fmap g (Pure a) = Pure (g a)
  fmap g (Free fa) = Free (fmap g <$> fa)

instance (Functor f) => Applicative (Free f) where
  pure = Pure
  Pure a <*> Pure b = Pure $ a b
  Pure a <*> Free mb = Free $ fmap a <$> mb
  Free ma <*> b = Free $ (<*> b) <$> ma

instance (Functor f) => Monad (Free f) where
  -- return = Pure
  Pure a >>= f = f a
  Free m >>= f = Free ((>>= f) <$> m)

liftF :: (Functor f) => f a -> Free f a
liftF = Free . fmap Pure

-- Log -------------------------------------------------------------------------

data LogF a
  = Debug Int a
  | Info String a
  | Fatal String

type Log = Free LogF

debug :: Int -> Log ()
debug n = liftF $ Debug n ()

info :: String -> Log ()
info s = liftF $ Info s ()

fatal :: String -> Log ()
fatal s = liftF $ Fatal s ()

instance Functor LogF where
  fmap g (Debug n a) = Debug n (g a)
  fmap g (Info s a) = Info s (g a)
  fmap g (Fatal s) = Fatal s (g a)

program1 :: Log ()
program1 = do
  info "hi"
  debug 42
  fatal "bye"

logger :: Log r -> IO r
logger (Pure r) = return r
logger (Free (Debug n k)) = putStrLn ("DEBUG: " ++ show n) >> logger k
logger (Free (Info s k)) = putStrLn ("INFO: " ++ s) >> logger k
logger (Free (Fatal s)) = putStrLn ("FATAL: " ++ s) >> exitFailure

-- Expr ------------------------------------------------------------------------

data ExprF a
  = Val Int (Int -> a)
  | Add Int Int (Int -> a)
  | Sub Int Int (Int -> a)
  | Mul Int Int (Int -> a)

type Expr = Free ExprF

val :: Int -> Expr Int
val n = liftF $ Val n id

{-
liftF (Val x id)
= Free (fmap Pure (Val x id))
= Free (Val x (Pure . id))
= Free (Val x Pure) :: Free ExprF Int
-}

add :: Int -> Int -> Expr Int
add n m = liftF $ Add n m id

sub :: Int -> Int -> Expr Int
sub n m = liftF $ Sub n m id

mul :: Int -> Int -> Expr Int
mul n m = liftF $ Mul n m id

instance Functor ExprF where
  fmap g (Val n k) = Val n (g . k)
  fmap g (Add n m k) = Add n m (g . k)
  fmap g (Sub n m k) = Sub n m (g . k)
  fmap g (Mul n m k) = Mul n m (g . k)

program2 :: Expr Int
program2 = do
  n <- val 1
  m <- val 2
  add n m

{-
program :: Expr Int
program = do
  n <- val 1
  m <- val 2
  add n m

program =
  val 1 >>= \x ->
  val 2 >>= \y ->
  add x y

program =
  Free (Val 1 Pure) >>= \x ->
  Free (Val 2 Pure) >>= \y ->
  Free (Add x y Pure)
-}

-- run :: Expr Int :+: Log () -> IO Int

wrap :: String -> String
wrap s = "(" ++ s ++ ")"

pretty :: Expr Int -> String
pretty (Pure n) = show n
pretty (Free (Val n k)) = pretty . k $ n
pretty (Free (Add n m k)) =
  let g = pretty . k
   in wrap $ g n ++ "+" ++ g m
pretty (Free (Sub n m k)) =
  let g = pretty . k
   in wrap $ g n ++ "-" ++ g m
pretty (Free (Mul n m k)) =
  let g = pretty . k
   in wrap $ g n ++ "*" ++ g m

eval :: Expr Int -> Int
eval (Pure n) = n
eval (Free (Val n k)) = eval . k $ n
eval (Free (Add n m k)) = eval . k $ n + m
eval (Free (Sub n m k)) = eval . k $ n - m
eval (Free (Mul n m k)) = eval . k $ n * m

-- coproduct -------------------------------------------------------------------

data (f :+: g) a = InL (f a) | InR (g a)

instance (Functor f, Functor g) => Functor (f :+: g) where
  fmap f (InL e) = InL (fmap f e)
  fmap f (InR e) = InR (fmap f e)

liftFL :: ExprF a -> DSL a
liftFL = liftF . InL

liftFR :: LogF a -> DSL a
liftFR = liftF . InR

type DSL = Free (ExprF :+: LogF)

val' :: Int -> DSL Int
val' n = liftFL $ Val n id

add' :: Int -> Int -> DSL Int
add' n m = liftFL $ Add n m id

sub' :: Int -> Int -> DSL Int
sub' n m = liftFL $ Sub n m id

mul' :: Int -> Int -> DSL Int
mul' n m = liftFL $ Mul n m id

debug' :: Int -> DSL ()
debug' n = liftFR $ Debug n ()

info' :: String -> DSL ()
info' s = liftFR $ Info s ()

fatal' :: String -> DSL ()
fatal' s = liftFR $ Fatal s ()

program3 :: DSL Int
program3 = do
  info' "starting execution"
  a <- val' 1
  b <- val' 2
  info' "adding 1 and 2"
  c <- add' a b
  debug' c
  info' "multiplying by 12"
  d <- mul' c 12
  debug' d
  fatal' "fatal error"
  return d

pretty2 :: DSL Int -> String
pretty2 (Pure n) = show n
pretty2 (Free (InL x)) = case x of
  (Val n k) -> pretty2 . k $ n
  (Add n m k) ->
    let g = pretty2 . k
     in wrap $ g n ++ "+" ++ g m
  (Sub n m k) ->
    let g = pretty2 . k
     in wrap $ g n ++ "-" ++ g m
  (Mul n m k) ->
    let g = pretty2 . k
     in wrap $ g n ++ "*" ++ g m
pretty2 (Free (InR x)) = case x of
  (Debug n k) -> pretty2 k
  (Info s k) -> pretty2 k
  (Fatal s) -> ""

prettyprint :: DSL Int -> IO ()
prettyprint = putStrLn . pretty2

run :: DSL Int -> IO Int
run (Pure n) = return n
run (Free (InL x)) = case x of
  (Val n k) -> run . k $ n
  (Add n m k) -> run . k $ n + m
  (Sub n m k) -> run . k $ n - m
  (Mul n m k) -> run . k $ n * m
run (Free (InR x)) = case x of
  (Debug n k) -> putStrLn ("DEBUG: " ++ show n) >> run k
  (Info s k) -> putStrLn ("INFO: " ++ s) >> run k
  (Fatal s) -> putStrLn ("FATAL: " ++ s) >> exitFailure
