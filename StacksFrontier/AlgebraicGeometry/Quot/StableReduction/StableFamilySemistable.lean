module

public import StacksFrontier.AlgebraicGeometry.Quot.StableReduction.PrestableMinimalModel
public import StacksFrontier.AlgebraicGeometry.Quot.StableReduction.CompleteRepresentable
public import StacksFrontier.AlgebraicGeometry.Curves.Models.MinimalModelCompletion
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.NodalSpecialFibre
public import StacksFrontier.AlgebraicGeometry.Topologies.FppfAdicCompletion

/-!
# A curve which is the generic fibre of a stable family of curves has semistable reduction

Let `R` be a discrete valuation ring with fraction field `K` and `C` a smooth projective curve over
`K` with `H⁰(C, 𝒪_C) = K`. If `C` is the generic fibre of a stable family of curves `F` over `R`
(an algebraic space, [Stacks, Tag 0E75]), then `C` has semistable reduction
([Stacks, Tag 0CDH]). This is the implication (2) ⟹ (1) of [Stacks, Tag 0E8D], for families of
curves in the sense of the source, whose total spaces are algebraic spaces.

## Main results

* `Stacks.Models.hasSemistableReduction_of_isStableCurveFamily`: the implication (2) ⟹ (1) of
  [Stacks, Tag 0E8D].

## References

* [Stacks Project, Tag 0E8D](https://stacks.math.columbia.edu/tag/0E8D)
* [Stacks Project, Tag 0AE7](https://stacks.math.columbia.edu/tag/0AE7)
* [Stacks Project, Tag 0CDG](https://stacks.math.columbia.edu/tag/0CDG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

namespace Stacks.Models

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

local notation "𝓡" => AdicCompletion (IsLocalRing.maximalIdeal R) R
local notation "𝓚" => IsDiscreteValuationRing.AdicCompletionFractionField R
local notation "gR" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "gK" => Spec.map (CommRingCat.ofHom (algebraMap K 𝓚))
local notation "gΛ" => Spec.map (CommRingCat.ofHom (algebraMap R 𝓡))
local notation "gΛK" => Spec.map (CommRingCat.ofHom (algebraMap 𝓡 𝓚))

/-- The `K`-algebra structure on the fraction field of the completion of `R`. -/
local instance : Algebra K 𝓚 :=
  IsDiscreteValuationRing.algebraAdicCompletionFractionField R K

/-- The algebra maps `R → K → K^` form a scalar tower, where `K^` is the fraction field of the
completion of `R`. -/
local instance : IsScalarTower R K 𝓚 :=
  IsDiscreteValuationRing.isScalarTower_adicCompletionFractionField R K

/-- A morphism of schemes of the site which is proper as a morphism of algebraic spaces is proper
as a morphism of schemes. -/
theorem isProper_of_space_isProper {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}
    {T U : BigFppfOver B integerBase hZ} (g : T ⟶ U)
    (h : Space.IsProper B integerBase hZ (yoneda.map g)) :
    IsProper ((BigFppfOver.toScheme B integerBase hZ).map g) := by
  have : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsProper.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B integerBase hZ)).IsStableUnderBaseChange :=
    ⟨fun hsq hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @_root_.AlgebraicGeometry.IsProper)
      (hsq.map (BigFppfOver.toScheme B integerBase hZ)) hg⟩
  exact (MorphismProperty.relative_map_iff (F := yoneda)
    (P := MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsProper.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B integerBase hZ))).mp
    ((Space.presheaf_isProper_iff B integerBase hZ (yoneda.map g)
      (isAlgebraicSpace_yoneda B integerBase hZ _) (isAlgebraicSpace_yoneda B integerBase hZ _)
      (Functor.relativelyRepresentable.map yoneda g)).mp h)

/-- **The base change of a stable family of curves with generic fibre `C` to the completion is a
nodal model of `C_{K^}`.** -/
theorem hasSemistableReduction_adicCompletion_of_isStableCurveFamily (B : BigFppfSite.{u})
    (hZ : B.Contains integerBase) (hR : B.Contains (Spec (.of R))) {C : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsCurve K c] [Smooth c] [IsProper c] (hc : IsProjective c)
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)]
    (F : CurveFamily B hZ) (ψ : F.base ≅ integerSiteObject B hZ hR)
    (φ : @curveFamilyOfScheme K _ (Over.mk c) hc.isProper B hZ
      (contains_spec_of_isFractionRing hR)
      (IsCurve.topologicalKrullDim_eq_one (k := K) (f := c)).le ⟶ F)
    (hφ : φ.baseMap ≫ ψ.hom = integerSiteMap B hZ (contains_spec_of_isFractionRing hR) hR (gR))
    (hF : IsStableCurveFamily B hZ F) :
    HasSemistableReduction 𝓡 (pullback.snd c (gK)) (IsProjective.pullback_snd (gK) hc) := by
  have hK : B.Contains (Spec (.of K)) := contains_spec_of_isFractionRing hR
  have hΛ : B.Contains (Spec (.of 𝓡)) :=
    BigFppfSite.contains_spec_adicCompletion B hR (maximalIdeal R)
  let w : integerSiteObject B hZ hΛ ⟶ F.base := integerSiteMap B hZ hΛ hR (gΛ) ≫ ψ.inv
  obtain ⟨Q, qQ, r, hrQ⟩ := CurveFamily.exists_isPullback_schemeSpace_of_isAdicComplete 𝓡 hΛ hF w
  have hprop : IsProper ((BigFppfOver.toScheme B integerBase hZ).map qQ) :=
    isProper_of_space_isProper qQ
      ((Space.isProper_isStableUnderBaseChange B integerBase hZ).of_isPullback hrQ F.proper)
  have hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map qQ) :=
    (Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
      Flat.isEtaleLocalOnSourceAndTarget qQ).1
      ((Space.isFlat_isStableUnderBaseChange B integerBase hZ).of_isPullback hrQ F.flat)
  have hnod :
      IsAtWorstNodalOfRelativeDimensionOne ((BigFppfOver.toScheme B integerBase hZ).map qQ) :=
    (Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
      isAtWorstNodalOfRelativeDimensionOne_isEtaleLocalOnSourceAndTarget qQ).1
      ((Space.isAtWorstNodalOfRelativeDimensionOne_isStableUnderBaseChange B integerBase hZ
        ).of_isPullback hrQ hF.1.1)
  have hK' : B.Contains (Spec (.of 𝓚)) := contains_spec_of_isFractionRing (R := 𝓡) hΛ
  have hC : B.Contains C := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact c hK
  have hC' : B.Contains (pullback c (gK)) :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (pullback.snd c (gK)) hK'
  have S1 := isPullback_schemeSpaceMap_integerSiteMap (B := B) (hZ := hZ) (hP := hC') (hQ := hC)
    (hR := hK') (hW := hK) (IsPullback.of_hasPullback c (gK))
  have hcart := φ.cartesian
  change IsPullback φ.totalMap (schemeSpaceMap (integerSiteMap B hZ hC hK c)) F.toBase
    (schemeSpaceMap φ.baseMap) at hcart
  have hbase : φ.baseMap = integerSiteMap B hZ hK hR (gR) ≫ ψ.inv := (Iso.eq_comp_inv ψ).2 hφ
  have hbot : integerSiteMap B hZ hK' hK (gK) ≫ φ.baseMap =
      integerSiteMap B hZ hK' hΛ (gΛK) ≫ w := by
    calc integerSiteMap B hZ hK' hK (gK) ≫ φ.baseMap
        = integerSiteMap B hZ hK' hK (gK) ≫ (integerSiteMap B hZ hK hR (gR) ≫ ψ.inv) := by
          rw [hbase]
      _ = integerSiteMap B hZ hK' hR ((gK) ≫ (gR)) ≫ ψ.inv := by
          rw [← Category.assoc, integerSiteMap_comp]
      _ = integerSiteMap B hZ hK' hR ((gΛK) ≫ (gΛ)) ≫ ψ.inv := by
          rw [spec_map_algebraMap_comp_adicCompletion]
      _ = integerSiteMap B hZ hK' hΛ (gΛK) ≫ w := by
          rw [← integerSiteMap_comp (hT' := hΛ), Category.assoc]
  have hbot' : schemeSpaceMap (integerSiteMap B hZ hK' hK (gK)) ≫ schemeSpaceMap φ.baseMap =
      schemeSpaceMap (integerSiteMap B hZ hK' hΛ (gΛK)) ≫ schemeSpaceMap w := by
    change (schemeSpaceFunctor B integerBase hZ).map _ ≫ (schemeSpaceFunctor B integerBase hZ).map _
      = (schemeSpaceFunctor B integerBase hZ).map _ ≫ (schemeSpaceFunctor B integerBase hZ).map _
    have := congrArg (fun f => (schemeSpaceFunctor B integerBase hZ).map f) hbot
    simp only [Functor.map_comp] at this
    exact this
  have hbig := S1.paste_horiz hcart
  rw [hbot'] at hbig
  let lsp := hrQ.lift (schemeSpaceMap (integerSiteMap B hZ hC' hC (pullback.fst c (gK))) ≫
      φ.totalMap) (schemeSpaceMap (integerSiteMap B hZ hC' hK' (pullback.snd c (gK))) ≫
      schemeSpaceMap (integerSiteMap B hZ hK' hΛ (gΛK))) hbig.w
  have hl : IsPullback lsp (schemeSpaceMap (integerSiteMap B hZ hC' hK' (pullback.snd c (gK))))
      (schemeSpaceMap qQ) (schemeSpaceMap (integerSiteMap B hZ hK' hΛ (gΛK))) :=
    IsPullback.of_right (by rw [hrQ.lift_fst]; exact hbig) (hrQ.lift_snd _ _ _) hrQ
  let hff := schemeSpaceFunctorFullyFaithful B (S := integerBase) hZ
  let lsite := hff.preimage lsp
  have hlsite : schemeSpaceMap lsite = lsp := hff.map_preimage lsp
  have hsite : IsPullback lsite (integerSiteMap B hZ hC' hK' (pullback.snd c (gK))) qQ
      (integerSiteMap B hZ hK' hΛ (gΛK)) := by
    refine IsPullback.of_map (schemeSpaceFunctor B integerBase hZ) ?_ ?_
    · apply hff.map_injective
      change schemeSpaceMap (lsite ≫ qQ) = schemeSpaceMap (_ ≫ _)
      rw [schemeSpaceMap_comp, schemeSpaceMap_comp, hlsite]
      exact hl.w
    · change IsPullback (schemeSpaceMap lsite) _ _ _
      rw [hlsite]
      exact hl
  have hsch : IsPullback ((BigFppfOver.toScheme B integerBase hZ).map lsite)
      (pullback.snd c (gK)) ((BigFppfOver.toScheme B integerBase hZ).map qQ) (gΛK) :=
    hsite.map (BigFppfOver.toScheme B integerBase hZ)
  have := hprop
  have := hflat
  exact ⟨(BigFppfOver.toScheme B integerBase hZ).obj Q,
    ((BigFppfOver.toScheme B integerBase hZ).map qQ : _ ⟶ Spec (.of 𝓡)), hsch.isoPullback,
    ⟨hflat, hprop.toLocallyOfFiniteType,
      (inferInstance : QuasiCompact ((BigFppfOver.toScheme B integerBase hZ).map qQ)),
      hsch.isoPullback_hom_snd⟩, hprop, hnod⟩

/-- A morphism to the spectrum of a field which is at-worst-nodal of relative dimension one has
at-worst-nodal singularities over the field. -/
theorem hasAtWorstNodalSingularities_of_isAtWorstNodal {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (hf : IsAtWorstNodalOfRelativeDimensionOne f) :
    letI : X.Over (Spec (.of k)) := ⟨f⟩
    Stacks.Curves.HasAtWorstNodalSingularities k X := by
  let : X.Over (Spec (.of k)) := ⟨f⟩
  rcases isEmpty_or_nonempty X with hX | hX
  · exact fun x => (IsEmpty.false x).elim
  have hsurj : Function.Surjective (RingHom.id k) := fun x => ⟨x, rfl⟩
  have hiso : IsIso ((Spec (.of k)).descResidueField
      (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom (RingHom.id k))))) :=
    isIso_descResidueField_of_surjective (RingHom.id k) hsurj
  obtain ⟨E, -, hE⟩ := exists_iso_fiber_pullback_of_isIso_descResidueField f
    (Spec.map (CommRingCat.ofHom (RingHom.id k)))
  obtain ⟨-, hlfp, hfib⟩ := (Stacks.Curves.hasAtWorstNodalFibresOfDimensionOne_iff f).mpr hf
  have : LocallyOfFinitePresentation f := hlfp
  have hid : Spec.map (CommRingCat.ofHom (RingHom.id k)) = 𝟙 _ := by
    rw [show CommRingCat.ofHom (RingHom.id k) = 𝟙 _ from rfl, Spec.map_id]
  have : IsIso (Spec.map (CommRingCat.ofHom (RingHom.id k))) := by rw [hid]; infer_instance
  have : Nonempty (f.fiber ((Spec.map (CommRingCat.ofHom (RingHom.id k)))
      (IsLocalRing.closedPoint k))) := by
    obtain ⟨x⟩ := hX
    exact ⟨E.inv (inv (pullback.fst f (Spec.map (CommRingCat.ofHom (RingHom.id k)))) x)⟩
  obtain ⟨-, hdim, hnod⟩ := hfib ((Spec.map (CommRingCat.ofHom (RingHom.id k)))
    (IsLocalRing.closedPoint k)) inferInstance
  have : LocallyOfFiniteType f := inferInstance
  let f₁ : f.fiber ((Spec.map (CommRingCat.ofHom (RingHom.id k))) (IsLocalRing.closedPoint k)) ⟶
      Spec (.of ((Spec (.of k)).residueField
        ((Spec.map (CommRingCat.ofHom (RingHom.id k))) (IsLocalRing.closedPoint k)))) :=
    f.fiberToSpecResidueField _
  have : LocallyOfFiniteType f₁ := Scheme.Hom.locallyOfFiniteType_fiberToSpecResidueField f _
  let ψ : CommRingCat.of k ⟶ CommRingCat.of ((Spec (.of k)).residueField
      ((Spec.map (CommRingCat.ofHom (RingHom.id k))) (IsLocalRing.closedPoint k))) :=
    inv ((Spec (.of k)).descResidueField
      (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom (RingHom.id k)))))
  have : IsIso ψ := by dsimp only [ψ]; infer_instance
  have h₁ := Stacks.Curves.hasAtWorstNodalSingularities_of_isIso f₁
    (pullback.snd f (Spec.map (CommRingCat.ofHom (RingHom.id k)))) hdim E.inv ψ (by
      dsimp only [f₁, ψ]
      rw [← hE, Category.assoc, Category.assoc, ← Spec.map_comp, IsIso.inv_hom_id, Spec.map_id,
        Category.comp_id, Iso.inv_hom_id_assoc]) hnod
  have hdim₂ : topologicalKrullDim
      (pullback f (Spec.map (CommRingCat.ofHom (RingHom.id k))) : Scheme.{u}) = 1 := by
    rw [← (Scheme.homeoOfIso E).isHomeomorph.topologicalKrullDim_eq]
    exact hdim
  refine Stacks.Curves.hasAtWorstNodalSingularities_of_isIso
    (pullback.snd f (Spec.map (CommRingCat.ofHom (RingHom.id k)))) f hdim₂
    (inv (pullback.fst f (Spec.map (CommRingCat.ofHom (RingHom.id k))))) (𝟙 _) ?_ h₁
  rw [Spec.map_id, Category.comp_id, IsIso.inv_comp_eq, pullback.condition, hid,
    Category.comp_id]

/-- **The implication (2) ⟹ (1) of [Stacks, Tag 0E8D].** Let `C` be a smooth projective curve
over the fraction field `K` of a discrete valuation ring `R`, with `H⁰(C, 𝒪_C) = K`. If `C` is the
generic fibre of a stable family of curves `F` over `R` — a morphism of families of curves from
`C ⟶ Spec K` to `F` lying over `Spec K ⟶ Spec R` — then `C` has semistable reduction. -/
theorem hasSemistableReduction_of_isStableCurveFamily (B : BigFppfSite.{u})
    (hZ : B.Contains integerBase) (hR : B.Contains (Spec (.of R))) {C : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsCurve K c] [Smooth c] (hc : IsProjective c)
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)]
    (F : CurveFamily B hZ) (ψ : F.base ≅ integerSiteObject B hZ hR)
    (φ : @curveFamilyOfScheme K _ (Over.mk c) hc.isProper B hZ
      (contains_spec_of_isFractionRing hR)
      (IsCurve.topologicalKrullDim_eq_one (k := K) (f := c)).le ⟶ F)
    (hφ : φ.baseMap ≫ ψ.hom = integerSiteMap B hZ (contains_spec_of_isFractionRing hR) hR (gR))
    (hF : IsStableCurveFamily B hZ F) :
    HasSemistableReduction R c hc := by
  have : IsProper c := hc.isProper
  have hss := hasSemistableReduction_adicCompletion_of_isStableCurveFamily B hZ hR c hc F ψ φ hφ hF
  have hH : Stacks.HProjective.IsHProjective c :=
    (isProjective_iff_isProjectiveMorphism_of_isAffine c).mp hc
  obtain ⟨Y, q, eY, hY⟩ := exists_isMinimalModel (R := R) c hH inferInstance
  obtain ⟨e', hY'⟩ := isMinimalModel_pullback_adicCompletion c hY
  obtain ⟨M, pM, eM, hM, hnM⟩ := exists_isMinimalModel_isAtWorstNodal_of_hasSemistableReduction
    (R := 𝓡) (pullback.snd c (gK)) (IsProjective.pullback_snd (gK) hc) hss
  have hnY' : IsAtWorstNodalOfRelativeDimensionOne (pullback.snd q (gΛ)) :=
    forall_of_exists_isMinimalModel (R := 𝓡) (pullback.snd c (gK))
      (IsProjective.pullback_snd (gK) hc) (fun p ↦ IsAtWorstNodalOfRelativeDimensionOne p)
      (fun φ p hp ↦ isAtWorstNodalOfRelativeDimensionOne_comp_etale p φ.hom hp)
      (fun _ _ hn ↦ hn) ⟨M, pM, eM, hM, hnM⟩ _ _ e' hY'
  have hsnd : IsAtWorstNodalOfRelativeDimensionOne (pullback.snd (pullback.snd q (gΛ))
      (Spec.map (CommRingCat.ofHom
        (algebraMap 𝓡 (𝓡 ⧸ (maximalIdeal R).map (algebraMap R 𝓡)))))) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) hnY'
  have : MorphismProperty.RespectsIso
      (@IsAtWorstNodalOfRelativeDimensionOne.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hsq := isPullback_closedFibre_adicCompletion q
  obtain ⟨hflat, hlft, hqc, hce⟩ := hY.isModel
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let S : RegularProperModelSituation.{u} :=
    { R := R, K := K, k := IsLocalRing.ResidueField R, residueEquiv := AlgEquiv.refl,
      C := C, C_to_K := c, X := Y, X_to_R := q, flat := hflat,
      locallyOfFiniteType := hlft, quasiCompact := hqc, regular := hY.regular,
      genericFiberIso := eY, genericFiberIso_over_K := hce,
      π := π, uniformizer := hπ, curveProjective := hY.curveProjective,
      modelProper := hY.isProper }
  have hsq' : IsPullback _ _ S.X_to_R (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))) := hsq
  have hS : IsAtWorstNodalOfRelativeDimensionOne S.specialFiberToSpec := by
    have he : S.specialFiberToSpec = hsq'.isoPullback.inv ≫
        (pullback.snd (pullback.snd q (gΛ)) (Spec.map (CommRingCat.ofHom
          (algebraMap 𝓡 (𝓡 ⧸ (maximalIdeal R).map (algebraMap R 𝓡))))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (R ⧸ maximalIdeal R)
          (𝓡 ⧸ (maximalIdeal R).map (algebraMap R 𝓡))))) :=
      (Iso.eq_inv_comp _).2 (IsPullback.isoPullback_hom_snd hsq')
    have h₂ := (MorphismProperty.cancel_right_of_respectsIso
      (@IsAtWorstNodalOfRelativeDimensionOne.{u}) _ (Spec.map (CommRingCat.ofHom
        (algebraMap (R ⧸ maximalIdeal R) (𝓡 ⧸ (maximalIdeal R).map (algebraMap R 𝓡)))))).mpr hsnd
    have h₃ := (MorphismProperty.cancel_left_of_respectsIso
      (@IsAtWorstNodalOfRelativeDimensionOne.{u}) hsq'.isoPullback.inv _).mpr h₂
    rw [he]
    exact h₃
  exact ⟨Y, q, eY, hY.isModel, hY.isProper, S.isAtWorstNodalOfRelativeDimensionOne_of_specialFiber
    (hasAtWorstNodalSingularities_of_isAtWorstNodal S.specialFiberToSpec hS)⟩

end Stacks.Models

end
