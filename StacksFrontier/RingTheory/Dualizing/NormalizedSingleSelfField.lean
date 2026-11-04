module

public import Mathlib.RingTheory.KrullDimension.Field
public import StacksFrontier.RingTheory.Dualizing.DualizingComplexes.FieldExtensionBaseChange
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Normalized

/-!
# The field in degree zero is normalized, with modules in the universe of the field

Over a field `k` the complex `k[0]` is a normalized dualizing complex. The statement
`Dualizing.isNormalizedDualizingComplex_singleSelfLifted_of_field` records this with the residue
field lifted to universe `0`; this file records it at
`Dualizing.IsNormalizedDualizingComplex.{u, u}`, the reading used by the dimension function
`Dualizing.dualizingDimension.{u, u}` and by [Stacks, Tag 0E9N], and for a commutative ring which
is a field rather than for a `Field` instance, so that it applies to rings of sections such as
`Γ(Spec k, ⊤)`.

## Main results

* `Dualizing.isNormalizedDualizingComplex_single_self_of_isField` — `A[0]` is a normalized
  dualizing complex over a commutative ring `A` which is a field.
-/

@[expose] public section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

/-- **A field in degree zero is a normalized dualizing complex.** For a commutative ring `A`
which is a field, `A[0]` is a dualizing complex, `A` is injective over itself, the ring has
dimension `0`, and the complex has cohomology exactly in degree `0`; so it is normalized. -/
theorem isNormalizedDualizingComplex_single_self_of_isField {A : Type u} [CommRing A]
    (hA : IsField A) [IsNoetherianRing A] [IsLocalRing A] :
    IsNormalizedDualizingComplex.{u, u}
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) := by
  let := hA.toField
  have hnt : Nontrivial A := ⟨⟨0, 1, zero_ne_one⟩⟩
  refine isNormalizedDualizingComplex_of_homology_bounds _ (isDualizingComplex_single_self_field A)
    0 (by rw [ringKrullDim_eq_zero_of_isField hA]; rfl) (fun i hi => ?_) ?_
  · exact DerivedCategory.isZero_of_isGE _ 0 i (by simpa using hi)
  · have e := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) 0).app
      (ModuleCat.of A A)
    rw [Nat.cast_zero, neg_zero]
    exact e.toLinearEquiv.toEquiv.nontrivial_congr.mpr (inferInstanceAs (Nontrivial A))

end Dualizing
