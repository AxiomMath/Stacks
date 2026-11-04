module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.Reduction
public import StacksFrontier.AlgebraicGeometry.Quot.StableReduction.FamilyCriterion
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ModelSituation
public import StacksFrontier.AlgebraicGeometry.Curves.Models.StableModel.SpecialFibre
public import StacksFrontier.AlgebraicGeometry.Curves.Models.StableModel.TwistDescent
public import StacksFrontier.AlgebraicGeometry.Curves.Models.StableModel.SectionsGeneration
public import StacksFrontier.AlgebraicGeometry.Curves.Models.StableModel.Contraction
public import StacksFrontier.AlgebraicGeometry.Curves.Models.StableModel.FibreConditions

/-!
# Semistable reduction gives a stable model (towards Stacks 0E8D)

Let `R` be a discrete valuation ring with fraction field `K` and `C` a smooth projective curve over
`K` with `H⁰(C, 𝒪_C) = K` and genus `g ≥ 2`. If `C` has semistable reduction, then `C` is the
generic fibre of a proper model `Y ⟶ Spec R`, at-worst-nodal of relative dimension one, both of
whose fibres are stable curves of genus `g`.

This is the implication (1) ⟹ (2) of [Stacks, Tag 0E8D], whose proof contracts a prestable family
of genus `g ≥ 2` to a stable one ([Stacks, Tag 0E8A]). Over a discrete valuation ring the
contraction is produced here directly: the stable contraction `c₀ : X_k ⟶ Y₀` of the special
fibre of a minimal model `X` ([Stacks, Tag 0E7Q]) is realized as the special fibre of the Stein
factorization of a morphism `X ⟶ ℙᴺ_R` given by sections of an invertible module `ℳ` on `X` with
`ℳ|_{X_k} ≅ c₀^*ℒ₀`, `ℒ₀` ample on `Y₀`.

## Main results

* `Stacks.Models.exists_stableModel_of_hasSemistableReduction`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Models

/-- **Semistable reduction gives a stable model.** Let `R` be a discrete valuation ring with
fraction field `K` and `C` a smooth projective curve over `K` with `H⁰(C, 𝒪_C) = K` and genus
`g ≥ 2` having semistable reduction. Then `C` is the generic fibre of a proper model
`p : Y ⟶ Spec R` which is at-worst-nodal of relative dimension one and all of whose fibres are
stable curves of genus `g`. -/
theorem exists_stableModel_of_hasSemistableReduction (R K : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] {C : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsCurve K c] [Smooth c] (hc : IsProjective c)
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)] (hg : 2 ≤ genus c)
    (h : HasSemistableReduction R c hc) :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ Spec (.of R))
      (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
      IsModel c p e ∧ IsProper p ∧ IsAtWorstNodalOfRelativeDimensionOne p ∧
        ∀ s, IsStableFibreOfGenus (genus c) p s := by
  -- a minimal model, at-worst-nodal ([Stacks, Tag 0CDG])
  obtain ⟨X, p, e, hmin, hnod⟩ := ((tfae_hasSemistableReduction (R := R) c hc).out 1 2).mp h
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
  -- an invertible module on the model restricting to a pullback of an ample module on `Y₀`
  obtain ⟨M, hM, L₀, hL₀i, hL₀, ⟨α⟩⟩ :=
    S.exists_isAmple_pullback_iso_specialFiberι hm hdim hglob hnodal hseq hc₀
  -- a morphism to projective space through it
  obtain ⟨L₀', hL₀'i, P, q, hq, hP, φ, A, hAi, hL₀', hφ, hA, ⟨α'⟩⟩ :=
    S.exists_projectiveSpace_pullback_iso hc₀ M L₀ hL₀ α
  -- the contraction of its Stein factorization
  obtain ⟨Y, pY, eK, hmod, hpY, e₀, he₀⟩ : ∃ (Y : Scheme.{u}) (pY : Y ⟶ Spec (.of R))
      (eK : C ≅ pullback pY (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
      IsModel c pY eK ∧ IsProper pY ∧
        ∃ e₀ : pullback pY
            (Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R)))) ≅ Y₀,
          e₀.hom ≫ g₀ = pullback.snd _ _ :=
    S.exists_model_of_isStableContraction hc₀ L₀' hL₀' q φ hφ A hA α'
  -- the fibre criterion, with the instances on `R` and `K` the ambient ones
  have : IsProper pY := hpY
  have hcrit := @isAtWorstNodal_and_isStableFibreOfGenus_of_fibres R K _ _ _ _ _ _
  obtain ⟨hnodY, hfib⟩ := hcrit c hg pY eK hmod g₀
    e₀ he₀ hYp hYdim hYglob hYnodal (hYgenus.trans hgen)
    ⟨hYgenus ▸ hgS, hYtail, hYp, fun D => hbridge D hYp⟩
  exact ⟨Y, pY, eK, hmod, hpY, hnodY, hfib⟩

end Stacks.Models

end
