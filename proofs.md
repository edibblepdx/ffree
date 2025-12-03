# Free

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

# Prove that Free is a Functor

## *Functor laws:*
```hs
Identity:
  fmap id == id
Composition:
  fmap (f . g) == fmap f . fmap g
```

## *Definitions:*
```hs
fmap g <$> fa = fmap (fmap g) fa
fmap (fmap g . fmap h) fa = fmap (fmap g) (fmap (fmap h) fa)
```

## *Induction:*
1. Base case: `Pure a :: Free f a`
2. Inductive hypothesis: `fa :: f (Free f a)`
2. Inductive step: `Free fa :: Free f a`  

## *Types:*
```hs
Pure a :: Free f a
fa :: f (Free f a)
f :: * -> *
```
*`fa` contains a Functor `f :: * -> *` and an inner part `b :: Free f a`.*  
*The inductive hypothesis applies to the inner part `b` when mapping over fa.*  
*Since `f` is a Functor, it satisfies the functor laws.*  

## *Identity law:*
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
      =   { identity law for functor f }
        Free (id fa)
      =   { applying id }
        Free fa
      =   { unapplying id }
        id (Free fa)

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
      =   { composition law for functor f }
        Free (fmap (fmap g) (fmap (fmap h) fa))
      =   { unapplying fmap }
        fmap g (Free (fmap (fmap h) fa))
      =   { unapplying fmap }
        fmap g (fmap h (Free fa))
      =   { unapplying . }
        (fmap g . fmap h) (Free fa)

