module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.CurveDegreeInvariance.Morphism
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.PerfectFibreBands

/-!
# A finite set of closed points of a scheme of finite type over a field

A finite set `T` of closed points of a scheme `Y` locally of finite type over a field `k` is the
image of a closed immersion `i : Z ⟶ Y` with `Z` finite over `k`: the reduced closed subscheme on
`T`. It is finite as a set and its points are closed, so its topology is discrete; a scheme locally
of finite type over a field with discrete underlying space is locally quasi-finite, and being
quasi-compact over the Artinian scheme `Spec k` it is finite.

## Main results

* `AlgebraicGeometry.exists_isClosedImmersion_isFinite_range_eq_of_finite`: a finite set of closed
  points is the range of a closed immersion finite over `k`.
* `AlgebraicGeometry.exists_isClosedImmersion_isFinite_range_eq_compl`: on a scheme locally of
  finite type over `k` whose underlying space is Noetherian of dimension at most one, the
  complement of an open containing every generic point is the range of a closed immersion finite
  over `k`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **A finite set of closed points is a closed subscheme finite over the base field.** -/
public theorem exists_isClosedImmersion_isFinite_range_eq_of_finite (k : Type u) [Field k]
    {Y : Scheme.{u}} (π : Y ⟶ Spec (.of k)) [LocallyOfFiniteType π] (T : Set Y)
    (hT : T.Finite) (hcl : ∀ y ∈ T, IsClosed ({y} : Set Y)) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ Y), IsClosedImmersion i ∧ IsFinite (i ≫ π) ∧
      Set.range i.base = T := by
  have hTc : IsClosed T := by
    rw [← Set.biUnion_of_singleton T]
    exact hT.isClosed_biUnion hcl
  let I := Scheme.IdealSheafData.vanishingIdeal ⟨T, hTc⟩
  have hrange : Set.range I.subschemeι.base = T := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  refine ⟨I.subscheme, I.subschemeι, inferInstance, ?_, hrange⟩
  have hfin : Finite I.subscheme := by
    have : Finite (Set.range I.subschemeι.base) := by rw [hrange]; exact hT.to_subtype
    exact Finite.of_injective (Set.rangeFactorization I.subschemeι.base) fun a b h =>
      I.subschemeι.isClosedEmbedding.injective (by simpa [Set.rangeFactorization] using h)
  have : T1Space I.subscheme := by
    refine ⟨fun z => ?_⟩
    have h := hcl _ (hrange ▸ Set.mem_range_self z)
    rw [I.subschemeι.isClosedEmbedding.isClosed_iff_image_isClosed, Set.image_singleton]
    exact h
  have : CompactSpace I.subscheme := Finite.compactSpace
  have : QuasiCompact (I.subschemeι ≫ π) := quasiCompact_of_compactSpace _
  have : LocallyQuasiFinite (I.subschemeι ≫ π) := by
    rw [locallyQuasiFinite_iff_isDiscrete_preimage_singleton]
    intro x
    exact (Set.toFinite _).isDiscrete_of_subset_closedPoints fun z _ => isClosed_singleton
  exact IsFinite.of_locallyQuasiFinite _

/-- **The complement of an open containing the generic points of a curve is finite over `k`.** -/
public theorem exists_isClosedImmersion_isFinite_range_eq_compl (k : Type u) [Field k]
    {Y : Scheme.{u}} (π : Y ⟶ Spec (.of k)) [LocallyOfFiniteType π]
    [TopologicalSpace.NoetherianSpace Y]
    (hdim : topologicalKrullDim Y ≤ 1) (W : Y.Opens) (hW : genericPoints Y ⊆ W) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ Y), IsClosedImmersion i ∧ IsFinite (i ≫ π) ∧
      Set.range i.base = (W : Set Y)ᶜ := by
  have hcl : IsClosed (W : Set Y)ᶜ := W.isOpen.isClosed_compl
  have h0 := topologicalKrullDim_le_zero_of_isClosed_of_forall_notMem_genericPointsOne hdim hcl
    fun x hx hx1 =>
      hx (hW (Stacks.AlgebraicGeometry.ComponentDegrees.mem_genericPointsOne_iff.mp hx1).1)
  obtain ⟨hfin, hpts⟩ := finite_and_subset_closedPoints_of_topologicalKrullDim_le_zero hcl h0
  exact exists_isClosedImmersion_isFinite_range_eq_of_finite k π _ hfin fun y hy => hpts hy

end AlgebraicGeometry

end
