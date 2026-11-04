module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.StableModel.Existence
public import StacksFrontier.AlgebraicGeometry.Curves.Models.StableModel.SpecialFibreIso.FibreCohomology
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.DualizingAmple
public import StacksFrontier.AlgebraicGeometry.Quot.ContractionUniquenessComplete
public import StacksFrontier.AlgebraicGeometry.Models.BaseChange

/-!
# The contraction of a minimal model onto the stable model, as a morphism

Let `R` be a discrete valuation ring with fraction field `K` and residue field `k`, and let
`X ⟶ Spec R` be a minimal model, at-worst-nodal, of a smooth projective curve `C` over `K` with
`H⁰(C, 𝒪_C) = K` and genus `g ≥ 2`. The proof of
`Stacks.Models.exists_stableModel_of_hasSemistableReduction` produces a proper model `Y` of `C`
whose special fibre is the stable contraction of `X_k` ([Stacks, Tag 0E7Q]), as the target of the
first factor `c : X ⟶ Y` of a Stein factorization. This file records the morphism `c`: it is a
morphism of models, and its special fibre `c_k : X_k ⟶ Y_k` is a stable contraction. This is the
morphism of [Stacks, Tag 0E8A] over a discrete valuation ring.

## Main results

* `Stacks.Curves.StableModel.IsStableContraction.comp_iso`: a stable contraction followed by an
  isomorphism of targets over `k` is a stable contraction.
* `Stacks.Models.RegularProperModelSituation.exists_modelHom_of_isStableContraction`: the variant
  of `Stacks.Models.RegularProperModelSituation.exists_model_of_isStableContraction` exposing the
  contraction `c`.
* `Stacks.Models.exists_stableContraction_of_isMinimalModel`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Curves.StableModel

variable {k : Type u} [Field k] {X Y Y' : Scheme.{u}}

/-- **A stable contraction followed by an isomorphism of targets is a stable contraction.** Let
`c : X ⟶ Y` satisfy the conditions of [Stacks, Tag 0E7Q], with `Rⁱc_*𝒪_X = 0` for all `i > 0`,
`H⁰(Y, 𝒪_Y) = k` and `Y` of genus at least two without rational tails or rational bridges. If
`e : Y ≅ Y'` is an isomorphism over `k` (and `X` is proper over `k`), then `c ≫ e` satisfies the
conditions of Tag 0E7Q. -/
theorem IsStableContraction.comp_iso {f : X ⟶ Spec (.of k)} {gY : Y ⟶ Spec (.of k)}
    {c : X ⟶ Y} [IsProper f] (h : IsStableContraction f gY c)
    (hR : ∀ i : ℕ, 0 < i → IsZero (((Scheme.Modules.pushforward c).rightDerived i).obj
      (SheafOfModules.unit X.ringCatSheaf)))
    (hglob : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ gY.appTop))
    (hstable : HasGenusTwoNoRationalTailNoRationalBridge k gY)
    (gY' : Y' ⟶ Spec (.of k)) (e : Y ≅ Y') (he : e.hom ≫ gY' = gY) :
    IsStableContraction f gY' (c ≫ e.hom) := by
  have : IsProper gY := h.isProper
  have : IsProper (c ≫ gY) := by rw [h.comp_eq]; infer_instance
  have : IsProper c := IsProper.of_comp c gY
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace gY
  have hgY' : gY' = e.inv ≫ gY := by rw [← he, Iso.inv_hom_id_assoc]
  have : IsProper gY' := by rw [hgY']; infer_instance
  have hw : e.hom ≫ gY' = gY ≫ Spec.map (𝟙 (CommRingCat.of k)) := by
    rw [Spec.map_id, Category.comp_id, he]
  have hw' : e.inv ≫ gY ≫ Spec.map (𝟙 (CommRingCat.of k)) = gY' := by
    rw [Spec.map_id, Category.comp_id, hgY']
  have hdim : topologicalKrullDim Y' = 1 := by
    rw [IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e.symm).isHomeomorph,
      h.topologicalKrullDim_eq]
  have hnodal : let : Y'.Over (Spec (.of k)) := ⟨gY'⟩
      Stacks.Curves.HasAtWorstNodalSingularities k Y' :=
    Stacks.Curves.hasAtWorstNodalSingularities_of_isIso gY gY' h.topologicalKrullDim_eq e.inv
      (𝟙 _) hw' h.hasAtWorstNodalSingularities
  have hglob' : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ gY'.appTop) :=
    isIso_ΓSpecIso_inv_comp_appTop_of_iso (𝟙 _) gY' gY e.hom hw hglob
  obtain ⟨hg2, htail, hpr, hbridge⟩ :=
    HasGenusTwoNoRationalTailNoRationalBridge.of_iso (𝟙 _) gY' gY e.hom hw hstable
  have hO : IsIso (SheafOfModules.unitToPushforwardObjUnit e.hom.toRingCatSheafHom) :=
    isIso_unitToPushforwardObjUnit_of_forall_isIso_app _ fun W =>
      Functor.map_isIso (forget₂ CommRingCat RingCat) (e.hom.app W.unop)
  let : Y'.Over (Spec (.of k)) := ⟨gY'⟩
  have : IsProper (Y' ↘ Spec (.of k)) := inferInstanceAs (IsProper gY')
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (Y' ↘ Spec (.of k)).appTop) := hglob'
  refine ⟨by rw [Category.assoc, he, h.comp_eq], inferInstance, hdim, hnodal,
    isIso_unitToPushforwardObjUnit_comp c e.hom h.isIso_unitToPushforwardObjUnit hO, ?_, ?_⟩
  · exact (Stacks.Models.SpecialFibreIso.isZero_rightDerived_unit_of_isAffineHom e.hom 1
      one_pos).of_iso (rightDerivedCompUnitIso c e.hom h.isIso_unitToPushforwardObjUnit hR 1)
  · exact isAmple_dualizingSheafOverField_of_hasAtWorstNodalSingularities k Y' hdim hnodal htail
      hbridge hg2

end Stacks.Curves.StableModel

namespace Stacks.Models.RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-- **The contraction of a regular proper model onto the stable model of its special fibre.**
The variant of `Stacks.Models.RegularProperModelSituation.exists_model_of_isStableContraction`
exposing the contraction: the first factor `c : X ⟶ Y` of the Stein factorization of `φ` is a
morphism of models, and its special fibre is `c₀` followed by the isomorphism `Y_k ≅ Y₀`. -/
theorem exists_modelHom_of_isStableContraction
    {Y₀ : Scheme.{u}} {g₀ : Y₀ ⟶ Spec (.of S.k)} {c₀ : S.specialFiber ⟶ Y₀}
    (hc₀ : Stacks.Curves.StableModel.IsStableContraction S.specialFiberToSpec g₀ c₀)
    (L₀ : Y₀.Modules) [SheafOfModules.IsInvertible Y₀.toRingedSpace.presheaf
      (structureSheafRing Y₀.toRingedSpace).property L₀]
    (hL₀ : Scheme.Modules.IsAmple Y₀ L₀)
    {P : Scheme.{u}} (q : P ⟶ Spec (.of S.R)) [IsProper q] [IsLocallyNoetherian P]
    (φ : S.X ⟶ P) (hφ : φ ≫ q = S.X_to_R)
    (A : P.Modules) [SheafOfModules.IsInvertible P.toRingedSpace.presheaf
      (structureSheafRing P.toRingedSpace).property A]
    (hA : Scheme.Modules.IsAmple P A)
    (α : (Scheme.Modules.pullback c₀).obj L₀ ≅
      (Scheme.Modules.pullback S.specialFiberι).obj ((Scheme.Modules.pullback φ).obj A)) :
    ∃ (Y : Scheme.{u}) (pY : Y ⟶ Spec (.of S.R))
      (eK : S.C ≅ pullback pY (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K))))
      (c : S.X ⟶ Y) (hc : c ≫ pY = S.X_to_R),
      IsModel S.C_to_K pY eK ∧ IsProper pY ∧ IsModelHom S.X_to_R pY S.genericFiberIso eK c ∧
        ∃ e₀ : pullback pY (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))) ≅ Y₀,
          e₀.hom ≫ g₀ = pullback.snd _ _ ∧ S.specialFiberMap pY c hc ≫ e₀.hom = c₀ := by
  obtain ⟨Y, c, π, hcπ, hcp, hπ, hsurj, hO, -, hflat⟩ :=
    S.exists_steinFactorization_model q φ hφ
  have hc : c ≫ π ≫ q = S.X_to_R := by rw [← Category.assoc, hcπ, hφ]
  obtain ⟨h, hfin, hh⟩ :=
    S.exists_isFinite_comp_eq_specialFiberMap hc₀ L₀ hL₀ q φ hφ A hA α c π hcπ hsurj hO
  have hgen := S.isIso_genericFiberMap hc₀ (π ≫ q) c hc hO h hh
  obtain ⟨e, he⟩ := S.exists_iso_comp_eq_specialFiberMap hc₀ (π ≫ q) c hc hsurj hO h hh hgen
  refine ⟨Y, π ≫ q, S.genericFiberIso ≪≫ asIso (S.genericFiberMap (π ≫ q) c hc), c, hc,
    ⟨hflat, inferInstance, inferInstance, ?_⟩, inferInstance, ⟨hc, rfl⟩, e.symm, ?_, ?_⟩
  · simp only [Iso.trans_hom, asIso_hom, Category.assoc, genericFiberMap_snd]
    exact S.genericFiberIso_over_K
  · have : IsProper g₀ := hc₀.isProper
    rw [Iso.symm_hom, Iso.inv_comp_eq]
    refine hc₀.ext (gY' := 𝟙 (Spec (.of S.k))) ?_
    rw [reassoc_of% he, specialFiberMap_snd, hc₀.comp_eq]
  · rw [← he, Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Stacks.Models.RegularProperModelSituation

namespace Stacks.Models

/-- **The contraction of a nodal minimal model onto a stable model** ([Stacks, Tag 0E8A] over a
discrete valuation ring). Let `R` be a discrete valuation ring with fraction field `K` and `C` a
smooth projective curve over `K` with `H⁰(C, 𝒪_C) = K` and genus `g ≥ 2`, and let
`p : Y ⟶ Spec R` be a minimal model of `C` which is at-worst-nodal of relative dimension one. Then
there are a proper model `pZ : Z ⟶ Spec R` of `C`, at-worst-nodal of relative dimension one with
stable fibres of genus `g`, and a morphism of models `cZ : Y ⟶ Z` whose special fibre
`Y_k ⟶ Z_k` is a stable contraction ([Stacks, Tag 0E7Q]).

This follows the proof of `Stacks.Models.exists_stableModel_of_hasSemistableReduction`, keeping
the contraction: `cZ` is the first factor of a Stein factorization, and its special fibre is the
stable contraction `c₀` of `Y_k` followed by an isomorphism of targets over `k`. -/
theorem exists_stableContraction_of_isMinimalModel (R K : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] {C Y : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsCurve K c] [Smooth c] (_hc : IsProjective c)
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)] (hg : 2 ≤ genus c)
    (p : Y ⟶ Spec (.of R)) (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hmin : IsMinimalModel c p e) (hnod : IsAtWorstNodalOfRelativeDimensionOne p) :
    ∃ (Z : Scheme.{u}) (pZ : Z ⟶ Spec (.of R))
      (eZ : C ≅ pullback pZ (Spec.map (CommRingCat.ofHom (algebraMap R K))))
      (cZ : Y ⟶ Z) (hcZ : cZ ≫ pZ = p),
      IsModel c pZ eZ ∧ IsProper pZ ∧ IsModelHom p pZ e eZ cZ ∧
        Stacks.Curves.StableModel.IsStableContraction
          (pullback.snd p (ContractionUniquenessComplete.closedPoint R))
          (pullback.snd pZ (ContractionUniquenessComplete.closedPoint R))
          (ContractionUniquenessComplete.specialMap p pZ cZ hcZ) ∧
        IsAtWorstNodalOfRelativeDimensionOne pZ ∧
          ∀ s, IsStableFibreOfGenus (genus c) pZ s := by
  clear _hc
  have := hmin.isProper
  let S := regularProperModelSituation c hmin.curveProjective p e hmin.isModel hmin.regular
  -- its special fibre
  obtain ⟨hprop, hdim, hglob, hnodal, hgen, htail, -, hm⟩ :=
    S.specialFiber_standing hmin.not_hasExceptionalCurveOfFirstKind hnod
  have := hprop
  have := hglob
  have hgS : 2 ≤ genus S.specialFiberToSpec := hgen ▸ hg
  -- the stable contraction of the special fibre ([Stacks, Tag 0E3Q])
  obtain ⟨Y₀, g₀, c₀, hseq, -, hbridge⟩ :=
    IsIteratedContractionOfRationalBridges.exists_forall_not_isRationalBridge (k := S.k)
      (fX := S.specialFiberToSpec) hdim hnodal
  have hc₀ := hseq.isStableContraction hdim hnodal htail hgS hbridge
  obtain ⟨hYp, hYdim, hYglob, hYnodal, hYgenus, -, -⟩ :=
    hseq.standing_target inferInstance hdim inferInstance hnodal
  have hYtail : let : Y₀.Over (Spec (.of S.k)) := ⟨g₀⟩
      ∀ D : Y₀.IdealSheafData, ¬ IsRationalTail S.k Y₀ D := by
    let : S.specialFiber.Over (Spec (.of S.k)) := ⟨S.specialFiberToSpec⟩
    let : Y₀.Over (Spec (.of S.k)) := ⟨g₀⟩
    have : IsProper (Y₀ ↘ Spec (.of S.k)) := hYp
    have : IsIso ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (Y₀ ↘ Spec (.of S.k)).appTop) := hYglob
    have : IsProper (S.specialFiber ↘ Spec (.of S.k)) := hprop
    have : IsIso ((Scheme.ΓSpecIso (.of S.k)).inv ≫
        (S.specialFiber ↘ Spec (.of S.k)).appTop) := hglob
    have : IsProper g₀ := hYp
    have : IsProper c₀ := by
      have : IsProper (c₀ ≫ g₀) := by rw [hc₀.comp_eq]; infer_instance
      exact IsProper.of_comp c₀ g₀
    obtain ⟨eω⟩ := hseq.nonempty_pullback_dualizingSheafOverField_iso hdim hnodal
    exact Stacks.Curves.forall_not_isRationalTail_of_pullback_dualizingSheafOverField_iso
      hdim hnodal hYdim hYnodal htail hgS c₀ hseq.comp_structureMorphism
      (c₀.surjective_of_isIso_app fun U =>
        Stacks.Curves.DualizingPullback.isIso_app_of_isIso_unitToPushforwardObjUnit c₀
          hc₀.isIso_unitToPushforwardObjUnit U).surj eω
  have hYstable : HasGenusTwoNoRationalTailNoRationalBridge S.k g₀ :=
    ⟨hYgenus ▸ hgS, hYtail, hYp, fun D => hbridge D hYp⟩
  -- an invertible module on the model restricting to a pullback of an ample module on `Y₀`
  obtain ⟨M, hM, L₀, hL₀i, hL₀, ⟨α⟩⟩ :=
    S.exists_isAmple_pullback_iso_specialFiberι hm hdim hglob hnodal hseq hc₀
  -- a morphism to projective space through it
  obtain ⟨L₀', hL₀'i, P, q, hq, hP, φ, A, hAi, hL₀', hφ, hA, ⟨α'⟩⟩ :=
    S.exists_projectiveSpace_pullback_iso hc₀ M L₀ hL₀ α
  -- the contraction of its Stein factorization
  obtain ⟨Z, pZ, eZ, cZ, hcZ, hmod, hpZ, hhom, e₀, he₀, hsp⟩ : ∃ (Z : Scheme.{u})
      (pZ : Z ⟶ Spec (.of R)) (eZ : C ≅ pullback pZ (Spec.map (CommRingCat.ofHom (algebraMap R K))))
      (cZ : Y ⟶ Z) (hcZ : cZ ≫ pZ = p),
      IsModel c pZ eZ ∧ IsProper pZ ∧ IsModelHom p pZ e eZ cZ ∧
        ∃ e₀ : pullback pZ
            (Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R)))) ≅ Y₀,
          e₀.hom ≫ g₀ = pullback.snd _ _ ∧ S.specialFiberMap pZ cZ hcZ ≫ e₀.hom = c₀ :=
    S.exists_modelHom_of_isStableContraction hc₀ L₀' hL₀' q φ hφ A hA α'
  -- the fibre criterion, with the instances on `R` and `K` the ambient ones
  have : IsProper pZ := hpZ
  have hcrit := @isAtWorstNodal_and_isStableFibreOfGenus_of_fibres R K _ _ _ _ _ _
  obtain ⟨hnodZ, hfib⟩ := hcrit c hg pZ eZ hmod g₀
    e₀ he₀ hYp hYdim hYglob hYnodal (hYgenus.trans hgen) hYstable
  -- the special fibre of the contraction is a stable contraction
  have hst := hc₀.comp_iso (S.isZero_rightDerived_unit_of_isStableContraction hc₀) hYglob
    hYstable (pullback.snd pZ (ContractionUniquenessComplete.closedPoint R)) e₀.symm
    ((Iso.inv_comp_eq e₀).mpr he₀.symm)
  have hsp' : c₀ ≫ e₀.symm.hom = ContractionUniquenessComplete.specialMap p pZ cZ hcZ :=
    ((Iso.eq_comp_inv e₀).mpr hsp).symm
  have hst' : Stacks.Curves.StableModel.IsStableContraction
      (pullback.snd p (ContractionUniquenessComplete.closedPoint R))
      (pullback.snd pZ (ContractionUniquenessComplete.closedPoint R)) (c₀ ≫ e₀.symm.hom) := hst
  exact ⟨Z, pZ, eZ, cZ, hcZ, hmod, hpZ, hhom, hsp' ▸ hst', hnodZ, hfib⟩

end Stacks.Models

end
