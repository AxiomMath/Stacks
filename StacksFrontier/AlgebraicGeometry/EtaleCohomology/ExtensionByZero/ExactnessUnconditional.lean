module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Exactness
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Exactness

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Sites.Abelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Formula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleAbelian

/-!
# Injectives and restriction along an étale morphism

Let `j : U ⟶ X` be an étale morphism of schemes.  Extension by zero `j_!` is left adjoint to
restriction `j^{-1}` and preserves monomorphisms, so restriction carries an injective abelian
sheaf on the small étale site of `X` to an injective abelian sheaf on the small étale site of `U`.

## Main results

* `Stacks.EtaleCohomology.etaleRestriction_preservesInjectiveObjects`: restriction along an étale
  morphism preserves injective abelian sheaves.

## References

* [Stacks, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3) (1), for `𝒜 = ℤ`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w w'

attribute [local instance] AlgebraicGeometry.Etale.isStableUnderComposition
attribute [local instance] AlgebraicGeometry.Etale.instIsMultiplicativeScheme

namespace AlgebraicGeometry.Scheme.Etale

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

end AlgebraicGeometry.Scheme.Etale

namespace Stacks.EtaleCohomology

open AlgebraicGeometry.Scheme.Etale

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

section LeftExact

variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]

end LeftExact

/-- Restriction along an étale morphism `j : U ⟶ X` preserves injective objects: if `I` is an
injective abelian sheaf on the small étale site of `X`, then `I|_U` is an injective abelian
sheaf on the small étale site of `U`. -/
instance etaleRestriction_preservesInjectiveObjects :
    (etaleRestriction.{u, v} j).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (extensionByZeroAdj.{u, v} j)

section Mono

variable [Mono j]

end Mono

end Stacks.EtaleCohomology

end
