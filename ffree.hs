-- This file contains code. The sister file contains proofs for the functor,
-- applicative, and monad laws for Free, as well as an explanation of free
-- monads. My sources are also in the other file.
--
-- I define two domain specific languages: one of solely impure actions
-- (a logger), and another of pure actions (arithmetic expressions). Except I
-- show that free monads can isolate impure parts such that you can reason
-- mathematically about impure programs. Then I sum (or take the coproduct) of
-- the functorial languages, which itself is also a functor and therefore can be
-- made into a free monad, and I get one combined domain specific language with
-- both logging and arithmetic expressions.

-- This import is for the logging language
import System.Exit

{-
== Free ========================================================================
-}
-- Where f is a functor. This Free monad structure is similar to that of a linked
-- list, wherein Free is a functor and the next element, or Pure. "A free monad
-- allows chaining computations with markers to satisfy the type system, but
-- otherwise imposes no deeper semantics itself" (Wikipedia).

-- This implementation of free comes from Control.Monad.Free
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

{-
== Logging Language ============================================================
-}
-- Define a logging DSL of solely impure actions over some type a.
--
-- This section is mostly based on Haskell for all; Purifying code using free
-- monads: https://www.haskellforall.com/2012/07/purify-code-using-free-monads.html
--
-- Challenges: If you fmap over a Log program, it will not modify the value
-- inside of Debug like how it modifies the *result* of evaluating arithmetic
-- expressions. I could not figure out how to modify the debug value.

data LogF a b
  = Debug a b
  | Info String b
  | Fatal String

instance Functor (LogF a) where
  fmap g (Debug n a) = Debug n (g a)
  fmap g (Info s a) = Info s (g a)
  fmap g (Fatal s) = Fatal s

type Log b = Free (LogF b)

debug :: Int -> Log Int ()
debug a = liftF $ Debug a ()

{-
liftF (Debug a ())
= Free (fmap Pure (Debug a ()))
= Free (Debug a (Pure ())) :: Free (Log Int ())
-}

info :: String -> Log Int ()
info s = liftF $ Info s ()

{-
liftF (Info s ())
= Free (fmap Pure (Info s ()))
= Free (Info s (Pure ())) :: Free (Log Int ())
-}

fatal :: String -> Log Int ()
fatal s = liftF $ Fatal s

{-
liftF (Fatal s)
= Free (fmap Pure (Fatal s)
= Free (Fatal s) :: Free (Log Int ())
-}

-- Write a logging program over integers
-- The helpful constructors: debug, info, and fatal were also defined over Int
program1 :: Log Int ()
program1 = do
  info "hi"
  debug 42
  fatal "bye"
  info "are we still here?"

{-
We can reason mathematically about the syntactic structure of program1

program1 = do
  Free (Info "hi" (Pure ()) >>= \_ ->
  Free (Debug 42 (Pure ()) >>= \_ ->
  Free (Fatal "bye") >>= \_ ->
  Free (Info "info "are we still here?" (Pure ())

program1 = do
  Free (fmap (>>= \_ -> ...) Info "hi" (Pure ()))

program1 = do
  Free (fmap (>>= \_ -> ...) Info "hi" (Pure ()))

program1 = do
  Free (Info "hi" ((\_ -> ...) () ))

program1 = do
  Free (Info "hi" (...)))

program1 = do
  Free (Info "hi" (
    Free (Debug 42 (Pure ()) >>= \_ ->
    Free (Fatal "bye") >>= \_ ->
    Free (Info "info "are we still here?" (Pure ()))
  )

{ Debug Follows similarly }

program1 = do
  Free (Info "hi" (
  Free (Debug 42 (
    Free (Fatal "bye") >>= \_ ->
    Free (Info "info "are we still here?" (Pure ()))
  ))

{ evaluate
  Free (Fatal "bye") >>= \_ -> ...
}

Free (Fatal "bye") >>= \_ -> ...
= Free (fmap (>>= \_ -> ...) (Fatal "bye"))
= Free (Fatal "bye")

{ apply to program1 }

program1 = do
  Free (Info "hi" (
  Free (Debug 42 (
  Free (Fatal "bye")))
-}

-- You might have noticed that Fatal terminated the program prematurely. We will
-- get back to this more formally in a little bit to show that this is always the
-- case. And that it allows us to reason about impure actions.

-- Define a logger which will interpret the program's syntax. Debug will print
-- an integer value, Info will print a string, and Fatal will print a string,
-- then terminate the program.
logger :: Log Int r -> IO r
logger (Pure r) = return r
logger (Free (Debug n k)) = putStrLn ("DEBUG: " ++ show n) >> logger k
logger (Free (Info s k)) = putStrLn ("INFO: " ++ s) >> logger k
logger (Free (Fatal s)) = putStrLn ("FATAL: " ++ s) >> exitFailure

-- https://www.haskellforall.com/2012/07/purify-code-using-free-monads.html
--
-- Now back to Fatal's exit semantics. Notice that free monads allowed us to
-- purify our code. All of the impure IO is isolated into the logger function
-- that interprets the program. The above program is equivalent to the
-- following one:
main :: IO ()
main = do
  putStrLn "hi"
  print 42
  putStrLn "bye"
  exitFailure
  putStrLn "are we still here?"

-- Will the program print "are we still here"? We might think not, but what if
-- exitFailure was redefined to be this function? Then it would be printed.
exitFailure' :: IO ()
exitFailure' = return ()

-- In the above program, we cannot prove that the message: "are we still here",
-- will be printed or not. But through purification via free monads, we can prove
-- that any command after fatal does not execute using equational reasoning;
-- i.e. that fatal s >> m = fatal s.

{-
fatal s >> m

=   { fatal s = liftF (Fatal s)}
liftF (Fatal s) >> m

=   { m >> m' = m >>= \_ -> m' }
liftF (Fatal s) >>= \_ -> m

=   { liftF f = Free (fmap Pure f) }
Free (fmap Pure (Fatal s)) >>= \_ -> m

=   { fmap g (Fatal s) = Fatal s }
Free (Fatal s) >>= \_ -> m

=   { Free m >>= f = Free (fmap (>>= f) m) }
Free (fmap (>>= \_ -> m) (Fatal s))

=   { fmap g (Fatal s) = Fatal s }
Free (Fatal s)

=   { fmap g (Fatal s) = Fatal s }
Free (fmap Pure (Fatal s))

=   { liftF f = Free (fmap Pure f) }
liftF (Fatal s)

=   { fatal s = liftF (Fatal s)}
fatal s
-}

-- In our program syntax we have proved that fatal will always terminate the
-- program no matter the interpreter (however nothing was, nor could be, proved
-- about exitFailure itself). We can assert that the following rule will hold
-- always.

{-# NOINLINE fatal #-}

{-# RULES "terminate" forall s m. fatal s >> m = fatal s #-}

{-
== Arithmetic Expressions Language =============================================
-}
-- Define an arithmetic expression DSL of solely pure actions over integers.
--
-- AI disclosure: In creating ExprF I had difficulty understanding the
-- continuation function. `(Int -> a)` came from Google Gemini and this link
-- https://gist.github.com/avieth/334201aa341d9a00c7fc. So I used equational
-- reasoning to show the structure of the program syntax.
--
-- An alternative definition to our "linked list" type would be a "tree" type
-- which is what I started with. This version doesn't work with do-notation for
-- building syntax. You may also think of 'a' as being a 'next' pointer.
--
-- data TreeExprF a
--   = Val Int
--   | Add a a
--   | Sub a a
--   | Mul a a

data ExprF a
  = Val Int (Int -> a)
  | Add Int Int (Int -> a)
  | Sub Int Int (Int -> a)
  | Mul Int Int (Int -> a)

instance Functor ExprF where
  fmap g (Val n k) = Val n (g . k)
  fmap g (Add n m k) = Add n m (g . k)
  fmap g (Sub n m k) = Sub n m (g . k)
  fmap g (Mul n m k) = Mul n m (g . k)

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

program2 :: Expr Int
program2 = do
  n <- val 1
  m <- val 2
  add n m

{-
We can reason mathematically about the syntactic structure of program2

program :: Expr Int
program = do
  n <- val 1
  m <- val 2
  add n m

program =
  val 1 >>= \x ->
  val 2 >>= \y ->
  add x y

{ evaluate val x }

val x :: Free ExprF Int
= liftF (val x id)
= Free (fmap Pure (Val x id))
= Free (Val x (Pure . id))
= Free (Val 5 Pure)

{ the rest follow similarly }

program =
  Free (Val 1 Pure) >>= \x ->
  Free (Val 2 Pure) >>= \y ->
  Free (Add x y Pure)

program =
  Free (fmap (>>= \x -> ...) (Val 1 Pure))

program =
  Free (Val 1 ((>>= \x -> ...) . Pure))

program =
  Free (Val 1 (\x ->
    Free (Val 2 Pure) >>= \y ->
    Free (Add x y Pure)))

  Free m >>= f = Free ((>>= f) <$> m)

{ repeat for
  \x -> Free (Val 2 Pure) >>= \y -> ...
}

program =
  Free (Val 1 (\x ->
    Free (fmap (>>= \y -> ...) (Val 2 Pure))))

program =
  Free (Val 1 (\x ->
    Free (Val 2 ((>>= \y -> ...) . Pure))))

program =
  Free (Val 1 (\x ->
  Free (Val 2 (\y ->
  Free (Add x y Pure)))))
-}

tinyprogram :: Expr Int
tinyprogram = do
  val 5

{-
tinyprogram = val 5 = Free (Val (5 Pure))
-}

wrap :: String -> String
wrap s = "(" ++ s ++ ")"

-- We can then introduce pretty printing
pretty1 :: Expr Int -> String
pretty1 (Pure n) = show n
pretty1 (Free (Val n k)) = pretty1 . k $ n
pretty1 (Free (Add n m k)) =
  let g = pretty1 . k
   in wrap $ g n ++ "+" ++ g m
pretty1 (Free (Sub n m k)) =
  let g = pretty1 . k
   in wrap $ g n ++ "-" ++ g m
pretty1 (Free (Mul n m k)) =
  let g = pretty1 . k
   in wrap $ g n ++ "*" ++ g m

-- And an arithmetic evaluator
eval1 :: Expr Int -> Int
eval1 (Pure n) = n
eval1 (Free x) = case x of
  (Val n k) -> eval1 . k $ n
  (Add n m k) -> eval1 . k $ n + m
  (Sub n m k) -> eval1 . k $ n - m
  (Mul n m k) -> eval1 . k $ n * m

-- We have isolated the syntax of the program from the semantics of the program.
-- With a single program we can define multiple ways to interpret it.

{-
== coproducts of functors ======================================================
-}
-- for any monad `f`, we can inject it into a free monad over a functor sum
--
-- This section is almost entirely based on the paper: "data types a la carte".
-- I will not go into any depth on category theory as I just do not have the
-- required knowledge at the moment.
--
-- Simplified from "data types a la carte" in that the sum does not support an
-- arbitrary number of languages injected into some larger language. Here I only
-- support two languages. The sum of functors is similar to Data.Either.
--
-- Challenges: It would be helpful to declare type classes that abstract the
-- pretty printing and evaluating semantics (again like in "data types a la
-- carte"), but I was unable to figure it out.
--
-- https://www.cambridge.org/core/journals/journal-of-functional-programming/article/data-types-a-la-carte/14416CB20C4637164EA9F77097909409
--
-- https://gist.github.com/avieth/334201aa341d9a00c7fc

-- The sum of two functors, which similar in form to Data.Either
data (f :+: g) a = InL (f a) | InR (g a)

-- Is itself a functor (same as in Prelude Data.Functor.Sum)
instance (Functor f, Functor g) => Functor (f :+: g) where
  fmap f (InL e) = InL (fmap f e)
  fmap f (InR e) = InR (fmap f e)

-- The type constraint f :<: g is satisfied if there is some injection
-- from f to g.
class (Functor f, Functor g) => f :<: g where
  inject :: f a -> g a

-- :<: is reflexive.
instance (Functor f) => f :<: f where
  inject = id

-- To inject any value of type `f a` into a type `(f :+: g) a`
-- is equivalent to InL.
instance (Functor f, Functor g) => f :<: (f :+: g) where
  inject = InL

-- To inject any value of type `f a` into a type `(g :+: f) a`
-- is equivalent to InR.
instance (Functor f, Functor g) => f :<: (g :+: f) where
  inject = InR

-- This function injects a functor f into a sum of functors g, wherein either
-- the left or right member of g is of type f.
--
-- The type class allows a single inj function rather than an injL and injR
-- which makes it easier to write. This combined DSL still only supports two
-- distinct languages however. "Data types a la carte" has a general impl.
inj :: (Functor f, Functor g, f :<: g) => Free f a -> Free g a
inj (Pure x) = Pure x
inj (Free x) = Free $ inject (fmap inj x)

injF :: (Functor f, f :<: g) => f a -> Free g a
injF = liftF . inject

type DSL = Free (ExprF :+: LogF Int)

program3 :: DSL Int
program3 = do
  inj $ info "starting execution"
  a <- inj $ val 1
  b <- inj $ val 2
  inj $ info "adding a and b, and storing the result in c"
  c <- inj $ add a b
  inj $ debug c
  inj $ info "multiplying c by 12, and storing the result in d"
  d <- inj $ mul c 12
  inj $ debug d
  inj $ fatal "fatal error"
  return d

-- The program will appear to not print properly, but that is because fatal
-- terminated the program early as was proved in the first section.
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

-- Evaluating the program also terminates early because of `fatal`.
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
