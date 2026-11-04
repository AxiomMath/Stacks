module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Perfect objects of the derived category of a ring

Let `R` be a ring and let `D(R)` be the derived category of the category of `R`-modules. An
object `K` of `D(R)` is *perfect* when it is quasi-isomorphic to a bounded complex of finite
projective `R`-modules, and an `R`-module `M` is *perfect* when the complex consisting of `M`
placed in degree zero is a perfect object of `D(R)`.

## Main definitions

* `StacksDraft.Perfect.IsPerfect`: perfect objects of the derived category of a ring
  ([stacks 0657] (1)).
* `StacksDraft.Perfect.IsPerfectModule`: perfect modules over a ring ([stacks 0657] (2)).

## Implementation notes

Quasi-isomorphism to a complex is expressed as an isomorphism, in the derived category, with the
image of that complex under the localization functor `DerivedCategory.Q`. Since `Iso` is data
rather than a proposition, the existential records `Nonempty` of it. Boundedness is expressed by
the strict lower and upper bound classes `CochainComplex.IsStrictlyGE` and
`CochainComplex.IsStrictlyLE` on the terms of the complex.

## References

* [Stacks Project, Tag 0657](https://stacks.math.columbia.edu/tag/0657)
-/

open CategoryTheory

universe u v w

namespace StacksDraft.Perfect

/-- **Stacks 0657 (1).** An object of the derived category of `R`-modules is *perfect* if it is
isomorphic to a bounded complex of finite projective `R`-modules. -/
@[stacks 0657 "(1)", sga "6 I 4.8" "affine (ring) case", sga "6 II 2.2.1" "affine case, perfect"]
def IsPerfect {R : Type u} [Ring R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (K : DerivedCategory (ModuleCat.{v} R)) : Prop :=
  ∃ (P : CochainComplex (ModuleCat.{v} R) ℤ) (a b : ℤ),
    P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Finite R (P.X i)) ∧
      (∀ i : ℤ, Module.Projective R (P.X i)) ∧
      Nonempty (K ≅ DerivedCategory.Q.obj P)

/-- **Stacks 0657 (2).** An `R`-module is *perfect* if the complex consisting of it placed in
degree zero is a perfect object of the derived category of `R`-modules. -/
@[stacks 0657 "(2)",
  sga "6 I 4.8" "affine case, module",
  sga "6 II 2.2.1" "affine, degree-0 module"]
def IsPerfectModule {R : Type u} [Ring R]
    (M : Type v) [AddCommGroup M] [Module R M]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)] : Prop :=
  IsPerfect ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj (ModuleCat.of R M))

end StacksDraft.Perfect
