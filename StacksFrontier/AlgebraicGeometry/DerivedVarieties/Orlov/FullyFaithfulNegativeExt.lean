module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Countability.DerivedEquivalenceKernel

/-!
# A fully faithful exact functor has no negative Ext between images of sheaves

Let `F : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` be fully faithful and commute with the shift. For perfect
objects `A ∈ D^{≤ 0}` and `B ∈ D^{≥ 0}` — for instance two modules placed in degree zero — every
morphism `F(A)[t] ⟶ F(B)` with `t > 0` vanishes: through the commutation of `F` with the shift
and full faithfulness it is the image of a morphism `A[t] ⟶ B`, and `A[t] ∈ D^{≤ -t}` has no
nonzero morphism to `B ∈ D^{≥ 0}`.

This is the vanishing that makes the Postnikov systems of [Stacks, Section 0G07] unique: the
terms `F(Vᵢ ⊗ 𝒢ᵢ)` of the complex obtained by transforming a resolution of the diagonal are images
of sheaves under the fully faithful `F`, and the source's appeal to "as `F` is fully faithful" is
exactly this statement.

## Main results

* `AlgebraicGeometry.map_shift_hom_eq_zero_of_fullyFaithful`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Perfect.BoundedLocallyFreeComplexes (PerfectDerivedCategory)

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

/-- **A fully faithful functor of perfect complexes commuting with the shift has no negative
`Ext` between images of objects in `D^{≤ 0}` and in `D^{≥ 0}`.** -/
theorem map_shift_hom_eq_zero_of_fullyFaithful {X Y : Scheme.{u}}
    (F : PerfectDerivedCategory X ⥤ PerfectDerivedCategory Y) (hF : F.FullyFaithful)
    [F.Additive] [F.CommShift ℤ] (A B : PerfectDerivedCategory X) (hA : A.obj.IsLE 0)
    (hB : B.obj.IsGE 0)
    (t : ℤ) (ht : 0 < t) (u : (F.obj A)⟦t⟧ ⟶ F.obj B) : u = 0 := by
  obtain ⟨v, hv⟩ : ∃ v : A⟦t⟧ ⟶ B, F.map v = (F.commShiftIso t).hom.app A ≫ u :=
    ⟨hF.preimage _, hF.map_preimage _⟩
  have hv0 : v = 0 := by
    apply (ObjectProperty.fullyFaithfulι _).map_injective
    have : (A.obj⟦t⟧).IsLE (-t) :=
      DerivedCategory.TStructure.t.isLE_shift A.obj 0 t (-t) (by omega)
    have : ((ObjectProperty.ι _).obj (A⟦t⟧)).IsLE (-t) :=
      ⟨(DerivedCategory.TStructure.t.isLE_of_iso
        (X := A.obj⟦t⟧) (((ObjectProperty.ι _).commShiftIso t).app A).symm (-t)).le⟩
    rw [Functor.map_zero]
    exact DerivedCategory.TStructure.t.zero_of_isLE_of_isGE _ (-t) 0 (by omega) this hB
  have : (F.commShiftIso t).hom.app A ≫ u = 0 := by rw [← hv, hv0, F.map_zero]
  rwa [Preadditive.IsIso.comp_left_eq_zero] at this

end AlgebraicGeometry
