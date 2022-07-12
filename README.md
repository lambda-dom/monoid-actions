# Monoid actions.

## Some mathematics.

Let $M$ be a monoid. Then a (left) *action* of $M$ on a set $X$ is a map $\mu\colon M\times X\to X$ (and putting $\mu (m, x) = m \cdot x$ and denoting multiplication in $M$ by juxtaposition to simplify the notation) such that:

$$
\text{Identity}: 1 \cdot x = x = x \cdot 1, \forall x\in X\newline
\text{Associativity}: n \cdot (m \cdot x) = (nm) \cdot x, \forall x\in X, \forall n, m \in M
$$

We can also define right actions in an obvious way (do not forget to suitably change associativity), but since there is an isomorphism between the category of left $M$-actions and the category of right $M^{\ast}$-actions, where $M^{\ast}$ is the opposite (or dual) monoid, for most mathematical purposes there is no loss of generality in sticking to left actions alone. Speaking of categories of actions, here is their definition: if $\mu\colon M\times X\to X$ and $\nu\colon M\times Y\to Y$ are two $M$-actions, than an *equivariant* map $\mu\to \nu$ is a map $f\colon X\to Y$ such that

$$
\text{Equivariance}: f (m \cdot x) = m \cdot f(x), \forall x\in X, \forall m\in M
$$

In this way, we obtain the category of $M$-actions and equivariant maps, which we denote by $\mathbf{Act}(M)$. If $\mathbf{Set}$ is the category of sets [^1], then there is an obvious forgetful functor $\mathbf{Act}(M)\to \mathbf{Set}$. This functor has a left adjoint and creates all (small) limits and colimits. Furthermore, $\mathbf{Act}(M)$ is cartesian closed, and even a (Grothendieck) topos with a natural number object. This topos is Boolean iff $M$ is a group.

[^1]: More generally, the construction of the category of actions can be internalized to any topos, and even to any monoidal category. Of course, the available theorems change.

## The package.

Actions are two-parameter type classes. We follow [monoid-extras package](https://github.com/diagrams/monoid-extras) and have instance selection on the second type parameter. It has the advantage of making clearer that the underlying-type functor creates all limits and colimits.

## Installation.

The package only depends on base; use the usual Haskell facilities to install it. To build the package, just:

    stack build

or if wanting to see the documentation locally,

    stack build --haddock
