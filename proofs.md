Free
================================================================================

```hs
-- Where f :: * -> * is a Functor
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
  Pure a >>= f = f a
  Free m >>= f = Free ((>>= f) <$> m)

liftF :: (Functor f) => f a -> Free f a
liftF = Free . fmap Pure
```

Preamble
================================================================================

## Definitions:
```hs
1. g <$> fa = fmap g fa
2. fmap g <$> fa = fmap (fmap g) fa
3. fmap (fmap g . fmap h) fa = fmap (fmap g) (fmap (fmap h) fa)
4. pure f <*> x = fmap f x
```

## Induction:
1. Base case: `Pure a :: Free f a`
2. Inductive hypothesis: `fa :: f (Free f a)`
2. Inductive step: `Free fa :: Free f a`

## Types:
```hs
1. Pure a :: Free f a
2. fa :: f (Free f a)
3. f :: * -> *
```

`fa` contains a Functor `f :: * -> *` and an inner part `b :: Free f a`.  
The inductive hypothesis applies to the inner part `b` when mapping over fa.  
Since `f` is a Functor, it also satisfies the functor laws.  

Prove that Free is a Functor
================================================================================

  ## Functor laws:
  ```hs
  Identity:
    fmap id == id
  Composition:
    fmap (f . g) == fmap f . fmap g
  ```

  ## Identity law:
    Base case:

        fmap id (Pure a)
      =   { applying fmap }
        Pure (id a)
      =   { applying id }
        Pure a
      =   { unapplying id }
        id (Pure a)

    Inductive case:

        fmap id (Free fa)
      =   { applying fmap }
        Free (fmap (fmap id) fa)
      =   { inductive hypothesis }
        Free (fmap id fa)
      =   { functor identity law for f }
        Free (id fa)
      =   { applying id }
        Free fa
      =   { unapplying id }
        id (Free fa)
      □

  ## *Composition law:*
    Base case:

        fmap (g . h) (Pure a)
      =   { applying fmap }
        Pure ((g . h) a)
      =   { applying . }
        Pure (g (h a))
      =   { unapplying fmap }
        fmap g (Pure (h a))
      =   { unapplying fmap }
        fmap g (fmap h (Pure a))
      =   { unapplying . }
        (fmap g . fmap h) (Pure a)

    Inductive case:

        fmap (g . h) (Free fa)
      =   { applying fmap }
        Free (fmap (fmap (g . h)) fa)
      =   { inductive hypothesis }
        Free (fmap (fmap g . fmap h) fa)
      =   { functor composition law for f }
        Free (fmap (fmap g) (fmap (fmap h) fa))
      =   { unapplying fmap }
        fmap g (Free (fmap (fmap h) fa))
      =   { unapplying fmap }
        fmap g (fmap h (Free fa))
      =   { unapplying . }
        (fmap g . fmap h) (Free fa)
      □

Prove that Free is an Applicative
================================================================================

  ## Applicative laws:
  ```hs
  Identity:
    pure id <*> v = v
  Composition:
    pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
  Homomorphism:
    pure f <*> pure x = pure (f x)
  Interchange:
    u <*> pure y = pure ($ y) <*> u
  ```

  ## Identity law:
    Base case:

      pure id <*> Pure a
    =   { applying pure }
      Pure id <*> Pure a
    =   { applying <*> }
      Pure (id a)
    =   { applying id }
      Pure a

    Inductive case:

      pure id <*> Free fa
    =   { applying pure }
      Pure id <*> Free fa
    =   { applying <*> }
      Free (fmap (fmap id) fa)
    =   { inductive hypothesis }
      Free (fmap id fa)
    =   { functor identity law for f }
      Free fa

  ## TODO: Composition law:

  ## Homomorphism law:

      pure f <*> pure x
    =   { applying pure }
      Pure f <*> Pure x
    =   { applying <*> }
      Pure (f x)

  ## Interchange law:
    Base case:

      Pure a <*> pure y
    =   { applying pure }
      Pure a <*> Pure y
    =   { applying <*> }
      Pure (a y)
    =   { unapplying $ }
      Pure (($ y) a)
    =   { unapplying <*> }
      Pure ($ y) <*> Pure a
    =   { unapplying pure }
      pure ($ y) <*> Pure a

    Inductive case:

      Free fa <*> pure y
    =   { applying pure }
      Free fa <*> Pure y
    =   { applying <*> }
      Free (fmap (<*> Pure y) fa)
    =   { inductive hypothesis }
      Free (fmap (fmap ($ y)) fa)
    =   { unapplying <*> }
      Pure ($ y) <*> Free fa
    =   { unapplying pure }
      pure ($ y) <*> Free fa

Prove that Free is a Monad
================================================================================

  ## Monad laws:
  ```hs
  Left identity:
    return a >>= k = k a
    return >=> h = h
  Right identity:
    m >>= return = m
    f >=> return = f
  Associativity:
    m >>= (\x -> k x >>= h) = (m >>= k) >>= h
    (f >=> g) >=> h = f >=> (g >=> h)
  ```

  ## Left identity law:

      return a >>= k
    =   { applying return }
      Pure a >>= k
    =   { applying >>= }
      k a

  ## Right identity law:
    Base case:

      Pure a >>= return
    =   { applying >>= }
      return a
    =   { return }
      Pure a

    Inductive case:

      Free fa >>= return
    =   { applying >>= }
      Free (fmap (>>= return) fa)
    =   { inductive hypothesis }
      Free (fmap id fa)
    =   { functor identity law for f }
      Free fa

  ## Associativity law:
    Base case:

      Pure a >>= (\x -> k x >>= h)
    =   { applying >>= }
      (\x -> k x >>= h) Pure a
    =   { applying lambda }
      k (Pure a) >>= h
    =   { unapplying >>= }
      (Pure a >>= k) >>= h

    Inductive case:

      Free fa >>= (\x -> k x >>= h)
    =   { applying >>= }
      Free (fmap (>>= (\x -> k x >>= h)) fa)
    =   { inductive hypothesis }
      Free (fmap ((>>= h) . (>>= k)) fa)
    =   { functor composition law for f }
      Free ((fmap (>>= h) . fmap (>>= k)) fa)
    =   { applying . }
      Free (fmap (>>= h) (fmap (>>= k) fa))
    =   { unapplying >>= }
      Free (fmap (>>= k) fa) >>= h
    =   { applying >>= }
      (Free fa >>= k) >>= h
