module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.OpenImmersionFromDenseOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteDenseOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImagePartialSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionSurjectiveOnPointsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupSeparation
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.StrongSplittingDerealizationSubgroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange

/-!
# A flat closure of the open part of a modification is the base

Let `f : X ⟶ W` be a proper morphism of algebraic spaces which is an isomorphism over an open
subspace `U ⊆ W`, and let `b : T ⟶ W` be a morphism such that the inverse image `U_T = b⁻¹(U)`
is scheme-theoretically dense in `T` with quasi-compact inclusion. Over `U_T` the base change
`X ×_W T ⟶ T` has a canonical section `s`; let `X'` be its scheme-theoretic image. If `X'` is
flat over `T`, then `X' ⟶ T` is an isomorphism, and so `b` factors through `f`.

The morphism `X' ⟶ T` is finite by Stacks 0B4J and an open immersion by Stacks 0879; its image
is closed and contains the dense open `U_T`, so it is an isomorphism.

## Main definitions

* `AlgebraicGeometry.Space.modificationSection`: the section `s : U_T ⟶ X ×_W T`.

## Main results

* `AlgebraicGeometry.Space.isIso_ι_comp_snd_of_isFlat`: `X' ⟶ T` is an isomorphism.
* `AlgebraicGeometry.Space.exists_comp_eq_of_isFlat`: `b` factors through `f`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {W T X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The canonical section over `U_T = b⁻¹(U)` of the base change `X ×_W T ⟶ T` of a morphism
`f : X ⟶ W` which is an isomorphism over `U`. -/
def modificationSection (f : X ⟶ W) (U : Subfunctor W) [IsIso (pullback.snd f U.ι)]
    (b : T ⟶ W) : (U.preimage b).toFunctor ⟶ pullback f b :=
  pullback.lift (U.fromPreimage b ≫ inv (pullback.snd f U.ι) ≫ pullback.fst f U.ι)
    (U.preimage b).ι (by
      rw [Category.assoc, Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc,
        Subfunctor.fromPreimage_ι])

/-- The section `modificationSection f U b` composed with the projection `X ×_W T ⟶ T` is the
inclusion `U_T ⟶ T`. -/
theorem modificationSection_snd (f : X ⟶ W) (U : Subfunctor W) [IsIso (pullback.snd f U.ι)]
    (b : T ⟶ W) : modificationSection f U b ≫ pullback.snd f b = (U.preimage b).ι :=
  pullback.lift_snd _ _ _

/-- **The closure of the open part of a modification is the base once it is flat.** Let
`f : X ⟶ W` be proper and an isomorphism over the open subspace `U ⊆ W`, and let `b : T ⟶ W` be a
morphism of algebraic spaces such that `U_T = b⁻¹(U)` is scheme-theoretically dense in `T` with
quasi-compact inclusion. If the scheme-theoretic image `X'` of the canonical section
`U_T ⟶ X ×_W T` is flat over `T`, then `X' ⟶ T` is an isomorphism. -/
theorem isIso_ι_comp_snd_of_isFlat (hW : IsAlgebraicSpace B S hS W)
    (hT : IsAlgebraicSpace B S hS T) (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ W)
    (hf : IsProper B S hS f) (U : Subfunctor W) (hU : IsOpenSubspace B S hS U)
    [IsIso (pullback.snd f U.ι)] (b : T ⟶ W)
    (hqc : IsQuasiCompact B S hS (U.preimage b).ι)
    (hdense : IsSchemeTheoreticallyDense B S hS (U.preimage b))
    (hflat : IsFlat B S hS
      ((schemeTheoreticImageSubfunctor B S hS (modificationSection f U b)).ι ≫
        pullback.snd f b)) :
    IsIso ((schemeTheoreticImageSubfunctor B S hS (modificationSection f U b)).ι ≫
        pullback.snd f b) := by
  set X' := schemeTheoreticImageSubfunctor B S hS (modificationSection f U b) with hX'def
  set φ := X'.ι ≫ pullback.snd f b with hφ
  have hY : IsAlgebraicSpace B S hS (pullback f b) := isAlgebraicSpace_pullback B S hS f b hX hT hW
  have hX'cl : IsClosedSubspace B S hS X' :=
    isClosedSubspace_schemeTheoreticImageSubfunctor B S hS _ hY
  have hX' : IsAlgebraicSpace B S hS X'.toFunctor := hX'cl.1
  have hU' : IsOpenSubspace B S hS (U.preimage b) := isOpenSubspace_preimage B S hS b U hW hT hU
  have hp : IsProper B S hS (pullback.snd f b) :=
    isProper_of_isPullback B S hS hY hX hT hW (IsPullback.of_hasPullback f b) hf
  have hproper : IsProper B S hS φ :=
    isProper_comp B S hS hX' hY hT _ _ (isProper_of_isClosedImmersion B S hS hX' hY _ hX'cl.2) hp
  have hiso : IsIso (pullback.snd φ (U.preimage b).ι) :=
    isIso_pullback_snd_schemeTheoreticImageSubfunctor_comp_of_section B S hS hY hT
      (pullback.snd f b) hp.1 (U.preimage b) hU' hqc (modificationSection f U b)
      (modificationSection_snd f U b)
  have hpdense : Dense (Set.range (pointsMap B S hS (U.preimage b).toFunctor
      (U.preimage b).ι)) :=
    dense_subspacePointSet_of_isSchemeTheoreticallyDense B S hS (X := ⟨T, hT⟩) _ hdense
  have hfin : IsFinite B S hS φ :=
    isFinite_of_isFinite_over_dense_open B S hS hX' hT φ hflat hproper (U.preimage b) hU'
      hpdense (isFinite_of_isIso B S hS _) (Or.inr hqc)
  have hopen : IsOpenImmersion B S hS φ :=
    isOpenImmersion_of_isIso_pullback_snd B S hS hX' hT φ (U.preimage b) hU' hproper.1
      hproper.2.1.1 hflat hiso hqc hdense
  have hclosed : IsClosed (Set.range (pointsMap B S hS X'.toFunctor φ)) := by
    have := isClosed_of_universallyClosed B S hS hT φ hproper.2.2 Set.univ isClosed_univ
    rwa [Set.image_univ] at this
  have hsub : Set.range (pointsMap B S hS (U.preimage b).toFunctor (U.preimage b).ι) ⊆
      Set.range (pointsMap B S hS X'.toFunctor φ) := by
    rintro _ ⟨y, rfl⟩
    refine ⟨pointsMap B S hS _ (pullback.fst φ (U.preimage b).ι)
      (pointsMap B S hS _ (inv (pullback.snd φ (U.preimage b).ι)) y), ?_⟩
    rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, pullback.condition,
      IsIso.inv_hom_id_assoc]
  have hsurj : Function.Surjective (pointsMap B S hS X'.toFunctor φ) := by
    rw [← Set.range_eq_univ, ← hclosed.closure_eq]
    exact Set.eq_univ_of_univ_subset
      (hpdense.closure_eq ▸ closure_mono hsub)
  exact isIso_of_isOpenImmersion_of_surjective_pointsMap B S hS φ hopen hsurj

/-- **A modification is dominated by `b` once the closure of its open part is flat over the
source of `b`.** In the situation of `AlgebraicGeometry.Space.isIso_ι_comp_snd_of_isFlat`, the
morphism `b : T ⟶ W` factors through `f : X ⟶ W`. -/
theorem exists_comp_eq_of_isFlat (hW : IsAlgebraicSpace B S hS W)
    (hT : IsAlgebraicSpace B S hS T) (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ W)
    (hf : IsProper B S hS f) (U : Subfunctor W) (hU : IsOpenSubspace B S hS U)
    [IsIso (pullback.snd f U.ι)] (b : T ⟶ W)
    (hqc : IsQuasiCompact B S hS (U.preimage b).ι)
    (hdense : IsSchemeTheoreticallyDense B S hS (U.preimage b))
    (hflat : IsFlat B S hS
      ((schemeTheoreticImageSubfunctor B S hS (modificationSection f U b)).ι ≫
        pullback.snd f b)) :
    ∃ g : T ⟶ X, g ≫ f = b := by
  have := isIso_ι_comp_snd_of_isFlat hW hT hX f hf U hU b hqc hdense hflat
  refine ⟨inv ((schemeTheoreticImageSubfunctor B S hS (modificationSection f U b)).ι ≫
      pullback.snd f b) ≫
    (schemeTheoreticImageSubfunctor B S hS (modificationSection f U b)).ι ≫
      pullback.fst f b, ?_⟩
  rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc
    (schemeTheoreticImageSubfunctor B S hS (modificationSection f U b)).ι,
    IsIso.inv_hom_id_assoc]

end AlgebraicGeometry.Space

end
