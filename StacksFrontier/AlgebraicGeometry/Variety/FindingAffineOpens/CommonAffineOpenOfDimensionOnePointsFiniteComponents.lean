module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.KrullDimension.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Limits.EventuallySeparatedOverBase
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.Variety.FindingAffineOpens.CommonAffineOpenOfComponents
public import StacksFrontier.AlgebraicGeometry.Variety.FindingAffineOpens.CommonAffineOpenOfDimensionOnePoints

/-!
# One-dimensional points of a separated scheme lie in a common affine open

Let `X` be a separated scheme each of whose quasi-compact opens has finitely many irreducible
components, and let `x₁, …, x_r` be points of `X` whose local rings are Noetherian of Krull
dimension at most one. Then a single affine open subscheme of `X` contains all of them.

## Main results

* `AlgebraicGeometry.exists_isAffineOpen_containing_of_stalk_krullDimLE_one_of_finite_components`:
  the common affine open.

## Implementation notes

The finite family is given as a function from an arbitrary finite type, matching the integral
case; repetitions are allowed. The hypothesis on `X` is phrased as finiteness of
`irreducibleComponents` of the open subspace attached to a quasi-compact open.

## References

* [Stacks Project, Tag 09NN](https://stacks.math.columbia.edu/tag/09NN)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry

/-- A surjective ring homomorphism preserves being Noetherian of Krull dimension at most one. -/
private theorem isNoetherianRing_and_krullDimLE_one_of_surjective {A B : Type*} [CommRing A]
    [CommRing B] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] (f : A →+* B)
    (hf : Function.Surjective f) : IsNoetherianRing B ∧ Ring.KrullDimLE 1 B :=
  ⟨isNoetherianRing_of_surjective A B f hf,
    Ring.krullDimLE_iff.mpr ((ringKrullDim_le_of_surjective f hf).trans
      (Ring.krullDimLE_iff.mp inferInstance))⟩

/-- Let `S` be a separated scheme and let `y : ι → S` be a finite family of points whose local
rings are Noetherian of Krull dimension at most one. For a closed immersion `f : Y ⟶ S` with `Y`
integral, the part of the family lying on `Y` is contained in an affine open of `Y`. -/
private theorem exists_isAffineOpen_inter_range_of_stalk_krullDimLE_one
    {S Y : Scheme.{u}} (f : Y ⟶ S) [IsClosedImmersion f] [IsIntegral Y] [S.IsSeparated]
    {ι : Type v} [Finite ι] (y : ι → S)
    (h_noetherian : ∀ i, IsNoetherianRing (S.presheaf.stalk (y i)))
    (h_dimension : ∀ i, Ring.KrullDimLE 1 (S.presheaf.stalk (y i))) :
    ∃ V : Y.Opens, IsAffineOpen V ∧
      Set.range y ∩ Set.range f ⊆ Set.range (V.ι ≫ f) := by
  have : Y.IsSeparated := Scheme.IsSeparated.of_isSeparated f
  choose z hz using fun j : {i : ι // y i ∈ Set.range f} => Set.mem_range.mp j.2
  have h (j : {i : ι // y i ∈ Set.range f}) :
      IsNoetherianRing (Y.presheaf.stalk (z j)) ∧ Ring.KrullDimLE 1 (Y.presheaf.stalk (z j)) := by
    have : IsNoetherianRing (S.presheaf.stalk (f (z j))) := hz j ▸ h_noetherian j.1
    have : Ring.KrullDimLE 1 (S.presheaf.stalk (f (z j))) := hz j ▸ h_dimension j.1
    exact isNoetherianRing_and_krullDimLE_one_of_surjective _ (f.stalkMap_surjective (z j))
  obtain ⟨V, hV, hzV⟩ := exists_isAffineOpen_containing_of_stalk_krullDimLE_one Y z
    (fun j => (h j).1) fun j => (h j).2
  refine ⟨V, hV, ?_⟩
  rintro t ⟨⟨i, rfl⟩, hi⟩
  exact ⟨⟨z ⟨i, hi⟩, hzV ⟨i, hi⟩⟩, hz ⟨i, hi⟩⟩

/-- **[Stacks, Tag 09NN]** Let `X` be a separated scheme such that every quasi-compact open of
`X` has finitely many irreducible components. A finite family of points of `X` whose local rings
are Noetherian of Krull dimension at most one is contained in an affine open subscheme of `X`. -/
@[stacks 09NN]
theorem exists_isAffineOpen_containing_of_stalk_krullDimLE_one_of_finite_components
    (X : Scheme.{u}) [X.IsSeparated]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    {ι : Type v} [Finite ι] (x : ι → X)
    (h_noetherian : ∀ i, IsNoetherianRing (X.presheaf.stalk (x i)))
    (h_dimension : ∀ i, Ring.KrullDimLE 1 (X.presheaf.stalk (x i))) :
    ∃ U : X.Opens, IsAffineOpen U ∧ ∀ i, x i ∈ U := by
  obtain ⟨W, hWcompact, hxW⟩ : ∃ W : X.Opens, IsCompact (W : Set X) ∧ ∀ i, x i ∈ W := by
    have hnbhd (i : ι) : ∃ V : X.Opens, IsAffineOpen V ∧ x i ∈ V :=
      (exists_isAffineOpen_mem_and_subset (x := x i) (U := ⊤) (by simp)).imp
        fun _ h => ⟨h.1, h.2.1⟩
    choose V hV hxV using hnbhd
    refine ⟨⨆ i, V i, ?_, fun i => Opens.mem_iSup.mpr ⟨i, hxV i⟩⟩
    simpa [Opens.coe_iSup] using isCompact_iUnion fun i => (hV i).isCompact
  have : Scheme.IsSeparated W.toScheme := Scheme.IsSeparated.of_isSeparated W.ι
  have hW (i : ι) : IsNoetherianRing (W.toScheme.presheaf.stalk (⟨x i, hxW i⟩ : W.toScheme)) ∧
      Ring.KrullDimLE 1 (W.toScheme.presheaf.stalk (⟨x i, hxW i⟩ : W.toScheme)) := by
    have := h_noetherian i
    have := h_dimension i
    exact isNoetherianRing_and_krullDimLE_one_of_surjective
      (W.stalkIso (⟨x i, hxW i⟩ : W.toScheme)).inv.hom
      (W.stalkIso (⟨x i, hxW i⟩ : W.toScheme)).symm.commRingCatIsoToRingEquiv.surjective
  have hlocal : ∀ Z : Closeds W.toScheme,
      (Z : Set W.toScheme) ∈ irreducibleComponents W.toScheme →
      ∃ V : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.Opens,
        IsAffineOpen V ∧
          Set.range (fun i => (⟨x i, hxW i⟩ : W.toScheme)) ∩ (Z : Set W.toScheme) ⊆
            Set.range (V.ι ≫ (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι) := by
    intro Z hZ
    have : IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
      Scheme.IdealSheafData.irreducibleSpace_subscheme _ _ (by
        rw [Scheme.IdealSheafData.range_subschemeι_vanishingIdeal]; exact hZ.1)
    have : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
      isIntegral_of_irreducibleSpace_of_isReduced _
    obtain ⟨V, hVaff, hVsub⟩ :=
      exists_isAffineOpen_inter_range_of_stalk_krullDimLE_one
        (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι
        (fun i => (⟨x i, hxW i⟩ : W.toScheme)) (fun i => (hW i).1) fun i => (hW i).2
    exact ⟨V, hVaff, by rwa [← Scheme.IdealSheafData.range_subschemeι_vanishingIdeal Z]⟩
  obtain ⟨V, hVaff, hVsub⟩ :=
    exists_isAffineOpen_containing_of_components W.toScheme
      (Set.finite_range fun i => (⟨x i, hxW i⟩ : W.toScheme)) (hX W hWcompact) hlocal
  exact ⟨W.ι ''ᵁ V, W.ι.isAffineOpen_iff_of_isOpenImmersion.mpr hVaff, fun i =>
    (W.mem_ι_image_iff (x := (⟨x i, hxW i⟩ : W.toScheme))).mpr (hVsub ⟨i, rfl⟩)⟩

end AlgebraicGeometry

end
