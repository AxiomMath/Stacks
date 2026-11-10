module

public import StacksFrontier.AlgebraicGeometry.Curves.FunctionFieldCategories
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricGenusNormalizationBound
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.SeparableDegreeFibres
public import StacksFrontier.AlgebraicGeometry.Curves.Models.MinimalModelExistence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.FirstVanishing.GenericFibre
public import StacksFrontier.AlgebraicGeometry.Quot.StableModelSpecialFibre
public import StacksFrontier.AlgebraicGeometry.Quot.StableModelUniqueness

/-!
# Uniqueness of stable models (Stacks 0E97)

Let `R` be a discrete valuation ring with fraction field `K` and `C` a smooth proper curve over
`K` with `K = H⁰(C, 𝒪_C)` and genus `g`. [Stacks, Tag 0E97]: if `X` and `X'` are models of `C`
which are stable families of genus `g` curves over `R`, there is a unique isomorphism of models
`X ≅ X'`.

The curve is projective and of genus at least two, being the generic
fibre of a stable family, so it has a minimal model `Y` ([Stacks, Tag 0C2W]). Both `X` and `X'`
receive morphisms of models `a : Y ⟶ X` and `a' : Y ⟶ X'` whose special fibres are stable
contractions of the special fibre `Yₛ`
(`Stacks.Models.exists_isModelHom_isStableContraction_specialFibre`), so the special fibres of
`X` and `X'` are identified under `Yₛ` by [Stacks, Tag 0E7Q]. Then `a'` is constant on the
fibres of `a` and factors through it, and symmetrically; the two factorizations are mutually
inverse morphisms of models.

## Main results

* `Stacks.Models.two_le_genus_of_isStableFamilyOfSchemes`: the generic fibre of a stable family
  over `R` has genus at least two.
* `Stacks.Models.exists_comp_eq_of_specialFibre`: the factorization of `a'` through `a`.
* `Stacks.Models.existsUnique_isModelHom_iso_of_isStableFamilyOfSchemesOfGenus`:
  [Stacks, Tag 0E97].

## References

* [Stacks Project, Tag 0E97](https://stacks.math.columbia.edu/tag/0E97)
* [Stacks Project, Tag 0E7Q](https://stacks.math.columbia.edu/tag/0E7Q)
* [Stacks Project, Tag 0C2W](https://stacks.math.columbia.edu/tag/0C2W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

namespace Stacks.Models

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- A morphism with `𝒪_X = a_*𝒪_Y` out of a reduced scheme has a reduced target, its rings of
sections being those of the source. -/
theorem isReduced_of_isIso_unitToPushforwardObjUnit {X Y : Scheme.{u}} (a : Y ⟶ X)
    (hO : IsIso (SheafOfModules.unitToPushforwardObjUnit a.toRingCatSheafHom)) [IsReduced Y] :
    IsReduced X := by
  refine ⟨fun U => ?_⟩
  have := Stacks.Curves.DualizingPullback.isIso_app_of_isIso_unitToPushforwardObjUnit a hO U
  exact isReduced_of_injective (a.app U).hom (ConcreteCategory.bijective_of_isIso (a.app U)).1

/-- The image of a presentation of the fibre of `p` over `s` is the preimage of `s`. -/
theorem range_eq_preimage_of_isPullback {X S V : Scheme.{u}} {p : X ⟶ S} {s : S}
    {j : V ⟶ X} {g : V ⟶ Spec (S.residueField s)}
    (sq : IsPullback j g p (S.fromSpecResidueField s)) : Set.range j = p ⁻¹' {s} := by
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    change p (j v) = s
    rw [← Scheme.Hom.comp_apply, sq.w, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  · intro hx
    obtain ⟨t⟩ : Nonempty (Spec (S.residueField s)) := inferInstance
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p)
      (g := S.fromSpecResidueField s) x t (by rw [Scheme.fromSpecResidueField_apply]; exact hx)
    exact ⟨sq.isoPullback.inv z, by rw [← Scheme.Hom.comp_apply, sq.isoPullback_inv_fst, hz]⟩

/-- A morphism over a proper base with proper source and `𝒪_X = a_*𝒪_Y` is proper and
surjective. -/
private theorem isProper_and_surjective_of_isIso_unitToPushforwardObjUnit {X Y S : Scheme.{u}}
    {q : Y ⟶ S} {p : X ⟶ S} (a : Y ⟶ X) (h : a ≫ p = q)
    (hO : IsIso (SheafOfModules.unitToPushforwardObjUnit a.toRingCatSheafHom))
    [IsProper q] [IsProper p] : IsProper a ∧ Surjective a := by
  have : IsProper (a ≫ p) := by rw [h]; infer_instance
  have : IsProper a := IsProper.of_comp a p
  exact ⟨this, a.surjective_of_isIso_app fun U =>
    Stacks.Curves.DualizingPullback.isIso_app_of_isIso_unitToPushforwardObjUnit a hO U⟩

/-- **A morphism of models out of `Y` factors through another one, given their special
fibres.** Let `a : Y ⟶ X` and `a' : Y ⟶ X'` be morphisms of proper models with `𝒪_X = a_*𝒪_Y`
and `X` reduced, let `V`, `V'` present the special fibres of `X`, `X'`, and let
`aₛ : Yₛ ⟶ V`, `a'ₛ : Yₛ ⟶ V'` be the induced morphisms on special fibres. If `a'ₛ` factors
through `aₛ`, then `a'` factors through `a`: it is constant on the fibres of `a`, over the
generic point because `a` is an isomorphism of generic fibres, and over the closed point by the
factorization of `a'ₛ`. -/
theorem exists_comp_eq_of_specialFibre {V₀ : Scheme.{u}} {Y X X' : Scheme.{u}}
    {q : Y ⟶ Spec (.of R)} {p : X ⟶ Spec (.of R)} {p' : X' ⟶ Spec (.of R)}
    {eY : V₀ ≅ pullback q (genericPointInclusion R K)}
    {e : V₀ ≅ pullback p (genericPointInclusion R K)}
    {e' : V₀ ≅ pullback p' (genericPointInclusion R K)} {a : Y ⟶ X} {a' : Y ⟶ X'}
    (ha : IsModelHom q p eY e a) (_ha' : IsModelHom q p' eY e' a')
    (hOa : IsIso (SheafOfModules.unitToPushforwardObjUnit a.toRingCatSheafHom))
    [IsProper q] [IsProper p] [IsProper p'] [IsReduced X] {s₀ : Spec (.of R)}
    (hs₀ : s₀ = closedPoint R)
    {V V' : Scheme.{u}} {jX : V ⟶ X} {gX : V ⟶ Spec ((Spec (.of R)).residueField s₀)}
    (hVsq : IsPullback jX gX p ((Spec (.of R)).fromSpecResidueField s₀))
    {jX' : V' ⟶ X'} {gX' : V' ⟶ Spec ((Spec (.of R)).residueField s₀)}
    (_hVsq' : IsPullback jX' gX' p' ((Spec (.of R)).fromSpecResidueField s₀))
    {as : q.fiber s₀ ⟶ V} {as' : q.fiber s₀ ⟶ V'}
    (has : as ≫ jX = q.fiberι s₀ ≫ a)
    (has' : as' ≫ jX' = q.fiberι s₀ ≫ a') (εh : V ⟶ V') (hε : as ≫ εh = as') :
    ∃ φ : X ⟶ X', a ≫ φ = a' := by
  obtain ⟨_, _⟩ := isProper_and_surjective_of_isIso_unitToPushforwardObjUnit a ha.1 hOa
  have : X'.IsSeparated := ⟨by rw [← terminal.comp_from p']; infer_instance⟩
  have : IsIso (genericFiberMapOfHomOver (K := K) q p a ha.1) := by
    have : genericFiberMapOfHomOver (K := K) q p a ha.1 = eY.inv ≫ e.hom := by
      rw [← ha.2, Iso.inv_hom_id_assoc]
    rw [this]
    infer_instance
  have : IsPreimmersion jX := MorphismProperty.of_isPullback hVsq.flip inferInstance
  have hqw : ∀ w : Y, q w = p (a w) := fun w => by
    have := congrArg (fun f : Y ⟶ Spec (.of R) => f w) ha.1
    simpa only [Scheme.Hom.comp_apply] using this.symm
  refine Stacks.ContractionComparison.exists_comp_eq_of_forall_fiber a a' hOa fun y => ?_
  by_cases hy : p y = s₀
  · obtain ⟨x, rfl⟩ : y ∈ Set.range jX := by
      rwa [range_eq_preimage_of_isPullback hVsq]
    refine ⟨jX' (εh x), fun w hw => ?_⟩
    obtain ⟨ws, rfl⟩ : w ∈ Set.range (q.fiberι s₀) := by
      rw [Scheme.Hom.range_fiberι]
      change q w = s₀
      rwa [hqw, hw]
    have h₁ := congrArg (fun f => f ws) has
    have h₂ := congrArg (fun f => f ws) has'
    have h₃ := congrArg (fun f => f ws) hε
    simp only [Scheme.Hom.comp_apply] at h₁ h₂ h₃
    have hx : as ws = x := jX.isEmbedding.injective (h₁.trans hw)
    rw [← h₂, ← h₃, hx]
  · obtain ⟨w₀, rfl⟩ := a.surjective y
    refine ⟨a' w₀, fun w hw => ?_⟩
    have hx : q w₀ ≠ closedPoint R := by
      rwa [hqw, ← hs₀]
    rw [eq_of_isIso_genericFiberMapOfHomOver (K := K) ha.1 hx hw.symm]

/-- **The generic fibre of a stable family over `R` has genus at least two.** If `X` is a model
of `C` which is a stable family of curves, the fibre of `X` over the generic point of `Spec R`
has genus at least two (Stacks 0E75), and it is `C` up to the identification of the residue field
of the generic point with `K`. -/
theorem two_le_genus_of_isStableFamilyOfSchemes (B : BigFppfSite.{u})
    (hZ : B.Contains integerBase) (hR : B.Contains (Spec (.of R))) {C X : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) {p : X ⟶ Spec (.of R)} {e : C ≅ pullback p (genericPointInclusion R K)}
    (hX : IsModel c p e) (hst : IsStableFamilyOfSchemes B hZ p hR) : 2 ≤ genus c := by
  have : IsProper p := hst.isProper
  set η : Spec (.of R) := genericPoint (Spec (.of R)) with hη
  obtain ⟨Vη, jη, gη, hsq, ⟨hg2, -, hprop, -⟩, -⟩ := hst.exists_isPullback_fiber η
  have : IsProper gη := hprop
  have := isSchemeTheoreticallyDominant_Spec_map_algebraMap_of_isFractionRing R K
  obtain ⟨φ, hφ⟩ :=
    Stacks.EtaleCohomology.SmoothBaseChange.exists_spec_map_comp_fromSpecResidueField_eq
      (genericPointInclusion R K)
  let l := hsq.lift (pullback.fst p (genericPointInclusion R K))
    (pullback.snd p (genericPointInclusion R K) ≫ Spec.map φ) (by
      rw [Category.assoc, hφ, pullback.condition])
  have hl : IsPullback l (pullback.snd p (genericPointInclusion R K)) gη (Spec.map φ) :=
    IsPullback.of_right (by
      rw [hsq.lift_fst, hφ]
      exact IsPullback.of_hasPullback p (genericPointInclusion R K)) (hsq.lift_snd _ _ _) hsq
  have hgen := genus_eq_of_isPullback ((Spec (.of R)).residueField η) K φ.hom l
    (pullback.snd p (genericPointInclusion R K)) gη hl
  have : IsProper (pullback.snd p (genericPointInclusion R K)) := inferInstance
  rwa [← hX.2.2.2, genus_comp_iso_eq K _ e, hgen]

open Stacks.Curves.StableModel in
/-- Let `R` be a discrete valuation ring with fraction field `K` and `C` a smooth proper curve over
`K` with `K = H⁰(C, 𝒪_C)` and genus `g`. If `X` and `X'` are models of `C` (Section 0C2R) which are
stable families of genus `g` curves over `R`, then there exists a unique isomorphism of models
`X ≅ X'`. -/
@[stacks 0E97]
theorem existsUnique_isModelHom_iso_of_isStableFamilyOfSchemesOfGenus (B : BigFppfSite.{u})
    (hZ : B.Contains integerBase) (hR : B.Contains (Spec (.of R))) {C : Scheme.{u}}
    (C_to_K : C ⟶ Spec (.of K)) [IsCurve K C_to_K] [Smooth C_to_K] [IsProper C_to_K]
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ C_to_K.appTop)] (g : ℕ) (_hg : genus C_to_K = g)
    {X X' : Scheme.{u}} {p : X ⟶ Spec (.of R)} {p' : X' ⟶ Spec (.of R)}
    {e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K)))}
    {e' : C ≅ pullback p' (Spec.map (CommRingCat.ofHom (algebraMap R K)))}
    (hX : IsModel C_to_K p e) (hX' : IsModel C_to_K p' e')
    (hst : IsStableFamilyOfSchemesOfGenus B hZ g p hR)
    (hst' : IsStableFamilyOfSchemesOfGenus B hZ g p' hR) :
    ∃! f : X ≅ X', IsModelHom p p' e e' f.hom := by
  have hst₀ := hst.isStableFamilyOfSchemes
  have hst₀' := hst'.isStableFamilyOfSchemes
  have : IsProper p := hst.isProper
  have : IsProper p' := hst'.isProper
  have hproj : Stacks.HProjective.IsHProjective C_to_K :=
    isProjectiveMorphism_of_isProper_of_isCurve K C_to_K
  have hg2 : 2 ≤ genus C_to_K := two_le_genus_of_isStableFamilyOfSchemes B hZ hR C_to_K hX hst₀
  obtain ⟨Y, q, eY, hY⟩ := exists_isMinimalModel (R := R) C_to_K hproj inferInstance
  obtain ⟨a, ha, hOa, V, jX, gX, hVsq, as, has, hasst, hdimY, hH0Y, hg2Y, hnodY⟩ :=
    exists_isModelHom_isStableContraction_specialFibre B hZ hR C_to_K hproj (by omega) hY hX hst₀
  obtain ⟨a', ha', hOa', V', jX', gX', hVsq', as', has', hasst', -⟩ :=
    exists_isModelHom_isStableContraction_specialFibre B hZ hR C_to_K hproj (by omega) hY hX'
      hst₀'
  have : IsProper q := hY.isProper
  have : IsReduced Y := isReduced_of_isRegular hY.regular
  have : IsReduced X := isReduced_of_isIso_unitToPushforwardObjUnit a hOa
  have : IsReduced X' := isReduced_of_isIso_unitToPushforwardObjUnit a' hOa'
  set s₀ : Spec (.of R) := closedPoint R with hs₀
  let ft : pullback q ((Spec (.of R)).fromSpecResidueField s₀) ⟶
      Spec (.of ((Spec (.of R)).residueField s₀)) := pullback.snd _ _
  have sqY : IsPullback (q.fiberι s₀) ft q ((Spec (.of R)).fromSpecResidueField s₀) :=
    IsPullback.of_hasPullback _ _
  have : IsProper ft := MorphismProperty.of_isPullback sqY inferInstance
  have : Nontrivial ↑(CommRingCat.of ↑((Spec (.of R)).residueField s₀)) :=
    inferInstanceAs (Nontrivial ↑((Spec (.of R)).residueField s₀))
  have : Nonempty (pullback q ((Spec (.of R)).fromSpecResidueField s₀) : Scheme.{u}) :=
    @nonempty_of_isIso_globalSections (.of ((Spec (.of R)).residueField s₀)) _ _ ft hH0Y
  have : Nonempty (q.fiber s₀) :=
    (inferInstance : Nonempty (pullback q ((Spec (.of R)).fromSpecResidueField s₀) : Scheme.{u}))
  obtain ⟨-, hnodYs⟩ := hasAtWorstNodalSingularities_of_isPullback_fiber hnodY s₀ sqY
  have : IsIso ((Scheme.ΓSpecIso (.of ((Spec (.of R)).residueField s₀))).inv ≫ ft.appTop) :=
    hH0Y
  obtain ⟨ε, hε, -⟩ := existsUnique_iso_of_isStableContraction
    (k := (Spec (.of R)).residueField s₀) ft hdimY hg2Y hnodYs hasst hasst'
  obtain ⟨φ, hφ⟩ := exists_comp_eq_of_specialFibre ha ha' hOa hs₀ hVsq hVsq' has has' ε.hom hε
  obtain ⟨ψ, hψ⟩ := exists_comp_eq_of_specialFibre ha' ha hOa' hs₀ hVsq' hVsq has' has ε.inv
    (by
      rw [← hε]
      exact (Category.assoc _ _ _).trans ((congrArg _ ε.hom_inv_id).trans (Category.comp_id _)))
  obtain ⟨_, _⟩ := isProper_and_surjective_of_isIso_unitToPushforwardObjUnit a ha.1 hOa
  obtain ⟨_, _⟩ := isProper_and_surjective_of_isIso_unitToPushforwardObjUnit a' ha'.1 hOa'
  have : IsDominant a := ⟨a.surjective.denseRange⟩
  have : IsDominant a' := ⟨a'.surjective.denseRange⟩
  have hφp : φ ≫ p' = p := ext_of_isDominant a (by rw [← Category.assoc, hφ, ha'.1, ha.1])
  have hψp : ψ ≫ p = p' := ext_of_isDominant a' (by rw [← Category.assoc, hψ, ha.1, ha'.1])
  have hφM : IsModelHom p p' e e' φ := IsModelHom.of_comp_eq ha ha' hφp hφ
  have hψM : IsModelHom p' p e' e ψ := IsModelHom.of_comp_eq ha' ha hψp hψ
  have h₁ : φ ≫ ψ = 𝟙 X := (hφM.comp hψM).eq_of_isModel_of_isSeparated hX (isModelHom_id p e)
  have h₂ : ψ ≫ φ = 𝟙 X' :=
    (hψM.comp hφM).eq_of_isModel_of_isSeparated hX' (isModelHom_id p' e')
  exact existsUnique_isModelHom_iso_of_comp_eq hX ha ha' ⟨φ, ψ, h₁, h₂⟩ hφp hφ

end Stacks.Models

end
