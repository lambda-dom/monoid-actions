{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveFunctor #-}

module Data.Monoid.Action
    (
        -- $documentation

        -- * Type classes.
        Action (..)
        , RightAction (..)

        -- ** Class-related functions.
        , homomorphism

        -- * Left and right adjoints to the underlying-type functor.
        -- $adjoints
        , Free (..)
        , Cofree (..)

        -- ** Adjunction-related functions.
        , free
        , extract
        , cofree
        , copure
        , coextract

        -- * 'Monoid' wrappers.
        , Endomorphisms (..)

        -- * 'Num' wrappers.
        , Summation (..)
        , Multiplication (..)
    )
    where

-- Imports.
import Data.Monoid (Dual (..))
import Data.Foldable (Foldable(foldl'))

-- $documentation
-- 'Action' instances fall in two main families. The first is the construction of
-- @Action m@ instances from the fact that the underlying-type functor creates all
-- limits and colimits. The second family are instances @Action Natural@ where
-- 'Natural' are the (Peano) natural numbers and roughly correspond to /do something @n@ times/.

-- | The type class for a left 'Monoid' action. It must satisfy the following two
-- laws:
--
-- __Identity__:
--
-- prop> mempty |*> x = x
--
-- __Associativity__:
--
-- prop> m |*> (n |*> x) = (m <> n) |*> x
class Monoid m => Action m a where
    (|*>) :: m -> a -> a
    infixl 6 |*>


-- | A right 'Monoid' action. It must satisfy:
--
-- __Identity__:
--
-- prop> x <*| mempty = x
--
-- __Associativity__:
--
-- prop> (x <*| n) <*| m = x <*| (n <> m)
class Monoid m => RightAction m a where
    (<*|) :: a -> m -> a
    infixr 6 <*|


-- Class-related functions.
-- | Actions @Action m a@ are in bijection with (monoid) homomorphisms @m -> Endomorphisms a@.
homomorphism :: Action m a => m -> Endomorphisms a
homomorphism m = Endomorphisms (m |*>)


-- Instances.
-- | Action of a monoid @m@ on itself.
instance Monoid m => Action m m where
    (|*>) = (<>)


-- | The (trivial) action on the terminal.
instance Monoid m => Action m () where
    (|*>) _ x = x


-- | Product of actions.
instance (Action m a , Action m b) => Action m (a, b) where
    (|*>) m (x, y) = (m |*> x, m |*> y)


-- | Pointwise action on action-valued maps.
instance Action m b => Action m (a -> b) where
    (|*>) m f = \x -> m |*> f x


-- | Lift an action to 'Maybe'.
--
-- More generally, any action can be lifted over a functor. We do not provide such an
-- action to avoid instance overlapping.
instance Action m a => Action m (Maybe a) where
    (|*>) m = fmap (m |*>)

-- | Coproduct of actions.
instance (Action m a , Action m b) => Action m (Either a b) where
    (|*>) m (Left x) = Left (m |*> x)
    (|*>) m (Right y) = Right (m |*> y)


-- | Isomorphism between the categories of left and right actions.
instance RightAction m a => Action (Dual m) a where
    (|*>) (Dual m) x = x <*| m


-- $adjoints
-- The functor (in the strict mathematical sense) sending @Act m a@ to @a@ has both a left
-- adjoint @Free m@ and a right adjoint @Cofree m@. The former adjunction generates a
-- monad on the category of types and the latter a /comonad/. Since base does not have a
-- type class for comonad (one can be found in [comonad](https://hackage.haskell.org/package/comonad)),
-- we just give the monad instance for 'Free', pun intended.

-- | The free action on @a@.
--
-- The underlying type is @(m, a)@ with action
--
-- @
--  m |*> (n, x) = (m <> n, x)
-- @
--
-- Use a wrapper instead of a plain old product to avoid overlapping with product actions.
-- The monad instance is the one coming from the fact that @Free m@ is a left adjoint, not the
-- one automatically derived from the constructor shape @Free m a@.
data Free m a
    = Free m a  -- ^ The constructor for @(x, y) :: (m, a)@.
    deriving (Eq, Ord, Functor)


instance Monoid m => Action m (Free m a) where
    (|*>) m (Free n x) = Free (m <> n) x


instance Monoid m => Applicative (Free m) where
    -- | The unit of the Free adjunction.
    pure = Free mempty
    (<*>) (Free m f) (Free n x) = Free (m <> n) (f x)


instance Monoid m => Monad (Free m) where
    -- | The monad induced by the Free adjunction.
    (>>=) (Free m x) phi = m |*> phi x


-- | The cofree action on @a@.
--
-- The underlying type is @m -> a@ with action
--
-- @
--  m |*> t = \ n -> t (n <> m)
-- @
--
-- Note that multiplication inside @t@ is on the /right/. This is a functor with values
-- in actions so @fmap f@ is an equivariant map.
newtype Cofree m a
    = Cofree (m -> a)   -- ^ The constructor for @t :: m -> a@.
    deriving (Functor)


instance Monoid m => Action m (Cofree m a) where
    (|*>) m (Cofree t) = Cofree (t . (<> m))


-- Adjunction-related functions.
-- | Universal property of @Free m a@.
--
-- An adjunction, although involving two universal properties, is completely determined
-- by any one of them. We give the one /not/ involving equivariant maps.
free :: (Action m b) => (a -> b) -> Free m a -> b
free f (Free m x) = m |*> f x

-- | The counit of the 'Free' adjunction.
extract :: Action m b => Free m b -> b
extract (Free m x) = m |*> x

-- | Universal property of @Cofree m a@.
cofree :: Action m b => (a -> b) -> Cofree m a -> b
cofree f (Cofree t) = f (t mempty)

-- | The counit of the 'Cofree' adjunction.
--
-- This map has formal properties similar to an integral map \(f\mapsto \int f\).
-- If such a map is to be /equivariant/ when @a@ is an action, and denoting the actions
-- by \(\cdot\), then,
--
-- \[
--  \int_{M} f(m) = \int_{M} f(m 1) = \int_{M} (m\cdot f)1 = (\int_{M} m)\cdot f(1)
-- \]
--
-- so that \(\int f\) is, up to a multiple, just evaluation on the monoid identity.
-- If the integral itself is to be equivariant then that leaves \(\int_{M} f(m) = 1\) as the only
-- option.
--
-- Evaluation is integration against a Dirac delta distribution. Less trivial examples
-- are obtained by, for example, taking the Haar measure on a compact group.
coextract :: Monoid m => Cofree m a -> a
coextract (Cofree f) = f mempty

-- | The unit of the 'Cofree' adjunction.
copure :: Action m b => b -> Cofree m b
copure x = Cofree (|*> x)

-- Monoid wrappers.
-- | Endomorphisms action.
--
-- Wrapper for the @a -> a@ type to construct non-overlapping action instance.
newtype Endomorphisms a
    = Endomorphisms (a -> a)    -- ^ The constructor for @f :: a -> a@.


instance Semigroup (Endomorphisms a) where
    (<>) (Endomorphisms g) (Endomorphisms f) = Endomorphisms (g . f)


instance Monoid (Endomorphisms a) where
    mempty = Endomorphisms id


instance Action (Endomorphisms a) a where
    (|*>) (Endomorphisms f) x = f x


-- Num wrappers.
-- | A wrapper to construct the action @Integer -> Num -> Num@ given by
--
--  @
--      n |*> x = x + ... + x = n x
--  @
--
-- Instead of constructing the action on arbitrary precision integers, we bring it
-- down to 'Int'. Strictly speaking this is not an action because of overflow,
-- but if you are hitting overflow you have bigger problems than violation of the
-- action laws.
newtype Summation a
    = Summation a      -- ^ The constructor for @x :: a@.


instance Semigroup (Summation Int) where
    (<>) (Summation m) (Summation n) = Summation (m + n)


instance Monoid (Summation Int) where
    mempty = Summation 0


instance Num b => Action (Summation Int) (Summation b) where
    (|*>) (Summation n) (Summation x)
        = Summation (sum (replicate (abs n) y))
        where y = if n >= 0 then x else -x


-- | A wrapper to construct the right action @Natural -> Num -> Num@.
--
--  @
--      x <*| n = x * ... * x = x ^ n
--  @
--
-- Instead of constructing the action on arbitrary precision positive integers (or Peano
-- naturals), we bring it down to 'Word'. Strictly speaking this is not an action because
-- of overflow, but if you are hitting overflow you have bigger problems than violation of
-- the action laws.
--
-- Note that besides the action law,
--
-- prop> (x ^ m) ^ n = x ^ (mn)
--
-- it also satisfies:
--
-- prop> x ^ (m + n) = x^m x^n
newtype Multiplication a
    = Multiplication a      -- ^ The constructor for @x :: a@.


instance Semigroup (Multiplication Word) where
    (<>) (Multiplication m) (Multiplication n) = Multiplication (m * n)


instance Monoid (Multiplication Word) where
    mempty = Multiplication 1


instance Num b => RightAction (Multiplication Word) (Multiplication b) where
    (<*|) (Multiplication x) (Multiplication n) = Multiplication (product (replicate (fromIntegral n) x))


-- | The action @Monoid m => Natural -> m -> m@ given by (written multiplicatively)
--
--  @
--    m \<*| n = m \<\> ... \<\> m = m ^ n
--  @
--
instance Monoid m => RightAction (Multiplication Word) m where
    (<*|) x (Multiplication n) = foldl' (<>) mempty (replicate (fromIntegral n) x)
