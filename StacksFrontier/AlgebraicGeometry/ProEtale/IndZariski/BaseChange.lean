module

public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski
public import StacksCore.Tactic.StacksAttribute

/-!
# Base change of ind-Zariski ring maps

The base change of an ind-Zariski map of commutative rings is again ind-Zariski.

## Main results

* `Algebra.IsIndZariski.tensorProduct`: if `B` is ind-Zariski over `A` and `A'` is any
  `A`-algebra, then `B ⊗[A] A'` is ind-Zariski over `A'`.
* `Algebra.IsIndZariski.tensorProduct'`: the same statement for `A' ⊗[A] B`, which carries the
  base-change algebra structure as an instance.

## Implementation notes

Over a single universe the statement is immediate: being ind-Zariski is the property
`MorphismProperty.ind` of `CommRingCat.localIso` applied to the structure map, and that
property is stable under cobase change because `CommRingCat.localIso` is. The work is in the
universes: `Algebra.IsIndZariski` lets the base and the algebra live in independent universes,
so the three rings are first lifted into their common universe with `ULift`, and the
single-universe statement is transported back along `Algebra.IsIndZariski.of_equiv`.

## References

* [Stacks Project, Tag 096P](https://stacks.math.columbia.edu/tag/096P)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace Algebra

/-- Base change of an ind-Zariski algebra, with the base, the algebra and the new base all in
one universe. -/
private theorem isIndZariski_tensorProduct_sameUniverse (A B A' : Type u) [CommRing A]
    [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A'] (h : IsIndZariski A B) :
    IsIndZariski A' (A' ⊗[A] B) := by
  rw [isIndZariski_iff_ind_localIso] at h ⊢
  exact MorphismProperty.IsStableUnderCobaseChange.of_isPushout
    (CommRingCat.isPushout_tensorProduct A A' B) h

attribute [local instance] ULift.algebra' in
/-- The base change `A' ⊗[A] B` of an ind-Zariski `A`-algebra `B` along an arbitrary
`A`-algebra `A'` is ind-Zariski over `A'`. -/
theorem IsIndZariski.tensorProduct' (A : Type u) (B : Type v) (A' : Type w) [CommRing A]
    [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A'] (h : IsIndZariski A B) :
    IsIndZariski A' (A' ⊗[A] B) := by
  have h₀ : IsIndZariski (ULift.{max v w} A) (ULift.{max u w} B) :=
    IsIndZariski.of_equiv ULift.ringEquiv.symm ULift.ringEquiv.symm (fun _ ↦ rfl) h
  have hT := isIndZariski_tensorProduct_sameUniverse (ULift.{max v w} A) (ULift.{max u w} B)
    (ULift.{max u v} A') h₀
  refine IsIndZariski.of_equiv ULift.ringEquiv
    (((TensorProduct.uliftEquiv.{u, max u v, max v w, max u w} A A' A' B).symm.trans
      ULift.algEquiv).toRingEquiv) ?_ hT
  intro a
  simp [Algebra.TensorProduct.algebraMap_apply, TensorProduct.uliftEquiv_symm_tmul,
    show ULift.ringEquiv a = a.down from rfl]

attribute [local instance] TensorProduct.rightAlgebra in
/-- The base change of an ind-Zariski algebra map is ind-Zariski: if `B` is ind-Zariski over `A`
and `A'` is any `A`-algebra, then `B ⊗[A] A'` is ind-Zariski over `A'`. -/
@[stacks 096P]
theorem IsIndZariski.tensorProduct (A : Type u) (B : Type v) (A' : Type w) [CommRing A]
    [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A'] (h : IsIndZariski A B) :
    IsIndZariski A' (B ⊗[A] A') := by
  refine IsIndZariski.of_equiv (RingEquiv.refl A')
    (TensorProduct.comm A A' B).toRingEquiv ?_ (IsIndZariski.tensorProduct' A B A' h)
  intro a
  show TensorProduct.comm A A' B (a ⊗ₜ[A] (1 : B)) = (1 : B) ⊗ₜ[A] a
  rw [TensorProduct.comm_tmul]

end Algebra

end
