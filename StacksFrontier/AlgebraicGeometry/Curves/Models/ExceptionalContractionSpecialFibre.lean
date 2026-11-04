module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.MinimalModelMappingProperty
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.NodalMinimalModel
public import StacksFrontier.AlgebraicGeometry.Models.GenericFibreModelHom
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RegularPointBlowupCohomology
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NodalBlowupChainSpecialFibre

/-!
# Contractions of exceptional curves on special fibres

Let `R` be a discrete valuation ring and `g : X ⟶ Y` a sequence of contractions of exceptional
curves of the first kind between regular proper models of a curve over the fraction field of
`R` ([Stacks, Tag 0CD9]), with `X` at-worst-nodal of relative dimension one over `R`. Each
contraction `b : X ⟶ X'` is the blowup of a regular point of dimension two of the special fibre,
so `𝒪_{X'} = b_*𝒪_X` and `R¹b_*𝒪_X = 0` ([Stacks, Tag 0AGS]); `X'` is at-worst-nodal
([Stacks, Tag 0CDF]), so its special fibre is reduced. On special fibres the restriction
`bₛ : Xₛ ⟶ X'ₛ` therefore satisfies `𝒪_{X'ₛ} = bₛ,*𝒪_{Xₛ}` and `Rⁱbₛ,*𝒪_{Xₛ} = 0` for `i > 0`
([Stacks, Tag 0E7F], [Stacks, Tag 0E7G], [Stacks, Tag 0E7I], [Stacks, Tag 0E7H]), and so does
the composite `gₛ`. This is the claim of the proof of [Stacks, Tag 0E97] for the morphisms
`Y_{i+1,s} ⟶ Y_{i,s}`.

## Main results

* `Stacks.Models.isZero_firstDirectImageStructureSheaf_isoHom_comp`: `R¹` is unchanged by
  precomposition with an isomorphism.
* `Stacks.Models.ExceptionalContractionSequence.specialFibre`: the sequence on special fibres.

## References

* [Stacks Project, Tag 0E97](https://stacks.math.columbia.edu/tag/0E97)
* [Stacks Project, Tag 0CD9](https://stacks.math.columbia.edu/tag/0CD9)
* [Stacks Project, Tag 0CDF](https://stacks.math.columbia.edu/tag/0CDF)
* [Stacks Project, Tag 0AGS](https://stacks.math.columbia.edu/tag/0AGS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace IsLocalRing

universe u

namespace Stacks.Models

attribute [local instance 2000] HasDerivedCategory.standard

/-- **`R¹` is unchanged by precomposition with an isomorphism**: for an isomorphism `e` and
`g` with `R¹g_*𝒪 = 0`, `R¹(e ≫ g)_*𝒪 = 0`. -/
theorem isZero_firstDirectImageStructureSheaf_isoHom_comp {X X₁ Y : Scheme.{u}} (e : X ⟶ X₁)
    [IsIso e] (g : X₁ ⟶ Y) [CompactSpace X₁]
    (h : IsZero (Stacks.AlgebraicGeometry.TopDegreeBaseChange.firstDirectImageStructureSheaf g)) :
    IsZero (Stacks.AlgebraicGeometry.TopDegreeBaseChange.firstDirectImageStructureSheaf
      (e ≫ g)) := by
  have h1 : IsZero (((Scheme.Modules.pushforward g).rightDerived 1).obj
      (SheafOfModules.unit X₁.ringCatSheaf)) :=
    h.of_iso ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward g) 1).app _)
  refine IsZero.of_iso ?_ ((Stacks.DerivedIndexing.rightDerivedIso
    (Scheme.Modules.pushforward (e ≫ g)) 1).app _).symm
  exact h1.of_iso (Stacks.Curves.StableModel.rightDerivedCompUnitIso e g
    (Stacks.AlgebraicGeometry.TopDegreeBaseChange.isIso_unitToPushforwardObjUnit_of_isIso e)
    (Stacks.SemistableReduction.isZero_rightDerived_of_isIso e) 1)

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The target of a contraction of an exceptional curve over `Spec R` is at-worst-nodal. -/
private theorem isAtWorstNodal_of_contraction {X X' : Scheme.{u}} {p : X ⟶ Spec (.of R)}
    {p' : X' ⟶ Spec (.of R)} (D : X.IdealSheafData) (k : Type u) [Field k]
    (eE : projectiveLineProj k ≅ D.subscheme) (hE : D.IsExceptionalCurveOfFirstKind k eE)
    (b : X ⟶ X') (hb : IsContractionOfExceptionalCurve D b)
    (hp : IsAtWorstNodalOfRelativeDimensionOne p) (hbp : b ≫ p' = p) :
    IsAtWorstNodalOfRelativeDimensionOne p' := by
  obtain ⟨f', hf', hn⟩ :=
    isAtWorstNodalOfRelativeDimensionOne_of_isContractionOfExceptionalCurve D k eE hE b hb _ hp
  obtain ⟨_, -, huniq⟩ := exists_factor_of_contraction D k eE b hb (A := R) _
  rw [← (huniq _ hf').trans (huniq _ hbp).symm]
  exact hn

/-- The centre of a contraction of an exceptional curve lies over the closed point of `Spec R`. -/
private theorem image_eq_closedPoint_of_contraction {X X' : Scheme.{u}} {p : X ⟶ Spec (.of R)}
    {p' : X' ⟶ Spec (.of R)} (D : X.IdealSheafData) (k : Type u) [Field k]
    (eE : projectiveLineProj k ≅ D.subscheme) (hE : D.IsExceptionalCurveOfFirstKind k eE)
    (b : X ⟶ X') (z : X') (hz : IsClosed ({z} : Set X'))
    (hD : D = (Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds X')).comap b)
    (hp : IsAtWorstNodalOfRelativeDimensionOne p) (hbp : b ≫ p' = p) :
    p' z = closedPoint R := by
  have := isIntegral_subscheme_of_iso_projectiveLineProj D k eE
  obtain ⟨x₀⟩ : Nonempty D.subscheme := inferInstance
  exact eq_closedPoint_of_isEffectiveCartierDivisor D hE.1 b z hz hD p hp p' hbp x₀
    (topologicalKrullDimAt_subscheme_eq_one_of_iso_projectiveLineProj D k eE x₀)

/-- **The contractions of [Stacks, Tag 0CD9] on special fibres.** Let `g : X ⟶ Y` be a sequence
of contractions of exceptional curves of the first kind from `p : X ⟶ Spec R` to
`q : Y ⟶ Spec R`, with `p` at-worst-nodal of relative dimension one. Then `𝒪_Y = g_*𝒪_X`, and for
special fibres `Xₛ`, `Yₛ` (cartesian squares over `Spec κ ⟶ Spec R`) and a morphism
`gₛ : Xₛ ⟶ Yₛ` over `g` and `Spec κ`, `𝒪_{Yₛ} = gₛ,*𝒪_{Xₛ}` and `Rⁱgₛ,*𝒪_{Xₛ} = 0` for
`i > 0`. -/
theorem ExceptionalContractionSequence.specialFibre {C : Scheme.{u}} {c : C ⟶ Spec (.of K)}
    {X Y : Scheme.{u}} {p : X ⟶ Spec (.of R)} {q : Y ⟶ Spec (.of R)} {g : X ⟶ Y}
    (hs : ExceptionalContractionSequence c p q g) (hp : IsAtWorstNodalOfRelativeDimensionOne p) :
    IsIso (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) ∧
    ∀ {Xs : Scheme.{u}} {jX : Xs ⟶ X}
      {gX : Xs ⟶ Spec ((Spec (.of R)).residueField (closedPoint R))},
      IsPullback jX gX p ((Spec (.of R)).fromSpecResidueField (closedPoint R)) →
      ∀ {Ys : Scheme.{u}} {jY : Ys ⟶ Y}
        {gY : Ys ⟶ Spec ((Spec (.of R)).residueField (closedPoint R))},
        IsPullback jY gY q ((Spec (.of R)).fromSpecResidueField (closedPoint R)) →
        ∀ {gs : Xs ⟶ Ys}, gs ≫ jY = jX ≫ g → gs ≫ gY = gX →
          IsIso (SheafOfModules.unitToPushforwardObjUnit gs.toRingCatSheafHom) ∧
          ∀ i : ℕ, 0 < i → IsZero (((Scheme.Modules.pushforward gs).rightDerived i).obj
            (SheafOfModules.unit Xs.ringCatSheaf)) := by
  induction hs with
  | refl p =>
    refine ⟨Stacks.AlgebraicGeometry.TopDegreeBaseChange.isIso_unitToPushforwardObjUnit_of_isIso _,
      fun {Xs jX gX} hXs {Ys jY gY} hYs {gs} h1 h2 => ?_⟩
    have hgs : gs = (hXs.isoIsPullback _ _ hYs).hom := hYs.hom_ext
      (by rw [h1, IsPullback.isoIsPullback_hom_fst, Category.comp_id])
      (by rw [h2, IsPullback.isoIsPullback_hom_snd])
    subst hgs
    exact ⟨Stacks.AlgebraicGeometry.TopDegreeBaseChange.isIso_unitToPushforwardObjUnit_of_isIso _,
      Stacks.SemistableReduction.isZero_rightDerived_of_isIso _⟩
  | @step X X' Y p p' q g' b D k _ eE hE hb hbp e' hmod hproper hreg rest ih =>
    have hp' := isAtWorstNodal_of_contraction D k eE hE b hb hp hbp
    obtain ⟨hO', hs'⟩ := ih hp'
    have hb' := hb
    obtain ⟨_hZ, z, hz, hreg2, hdim2, hD, ε, hε⟩ := hb'
    have := hreg2
    have : IsLocallyNoetherian X' := inferInstance
    have : IsProper p' := hproper
    have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace p'
    have hpz := image_eq_closedPoint_of_contraction D k eE hE b z hz hD hp hbp
    have : Flat p' := flat hp'.1.1
    have : Flat p := flat hp.1.1
    have hblp : blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds X')) ≫ p' =
        ε.inv ≫ p := by
      rw [← hbp, ← hε, Category.assoc, Iso.inv_hom_id_assoc]
    have : Flat (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds X')) ≫
        p') := by rw [hblp]; infer_instance
    have := Stacks.SemistableReduction.isReduced_fiber_of_isAtWorstNodal p' hp' (closedPoint R)
    have hObl := isIso_unitToPushforwardObjUnit_blowUpToBase_point p' z hz hpz
    have := surjective_blowUpToBase_point p' z hz hpz
    have : CompactSpace (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds X'))) :=
      QuasiCompact.compactSpace_of_compactSpace (blowUpToBase _)
    have hOb : IsIso (SheafOfModules.unitToPushforwardObjUnit b.toRingCatSheafHom) := by
      rw [← hε]
      exact Stacks.SemistableReduction.isIso_unitToPushforwardObjUnit_comp_of_acyclic _ _
        (Stacks.AlgebraicGeometry.TopDegreeBaseChange.isIso_unitToPushforwardObjUnit_of_isIso _)
        hObl
    have hR1b : IsZero (Stacks.AlgebraicGeometry.TopDegreeBaseChange.firstDirectImageStructureSheaf
        b) := by
      rw [← hε]
      exact isZero_firstDirectImageStructureSheaf_isoHom_comp ε.hom _
        (isZero_rightDerivedPlus_one_pushforward_blowUp_pointIdeal z hz hdim2)
    have : Surjective b := by rw [← hε]; infer_instance
    have : IsProper b := by rw [← hε]; infer_instance
    have hdim : ∀ y, topologicalKrullDim (b.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞) := fun y =>
      (Stacks.AlgebraicGeometry.TopDegreeBaseChange.topologicalKrullDim_fiber_le_fiber_comp
        b p' y).trans (by
          rw [hbp]
          exact Stacks.SemistableReduction.topologicalKrullDim_fiber_le_one_of_isAtWorstNodal
            p hp _)
    refine ⟨Stacks.SemistableReduction.isIso_unitToPushforwardObjUnit_comp_of_acyclic _ _ hOb hO',
      fun {Xs jX gX} hXs {Ys jY gY} hYs {gs} h1 h2 => ?_⟩
    let t' := IsPullback.of_hasPullback p'
      ((Spec (.of R)).fromSpecResidueField (closedPoint R))
    let bs : Xs ⟶ pullback p' ((Spec (.of R)).fromSpecResidueField (closedPoint R)) :=
      pullback.lift (jX ≫ b) gX (by rw [Category.assoc, hbp, hXs.w])
    have hbs₁ : bs ≫ pullback.fst _ _ = jX ≫ b := pullback.lift_fst _ _ _
    have hbs₂ : bs ≫ pullback.snd _ _ = gX := pullback.lift_snd _ _ _
    have sqb : IsPullback jX bs b (pullback.fst _ _) :=
      IsPullback.of_bot (by rw [hbs₂, hbp]; exact hXs) hbs₁.symm t'
    have hg'q : g' ≫ q = p' := comp_eq_of_exceptionalContractionSequence rest
    let rs : pullback p' ((Spec (.of R)).fromSpecResidueField (closedPoint R)) ⟶ Ys :=
      hYs.lift (pullback.fst _ _ ≫ g') (pullback.snd _ _) (by
        rw [Category.assoc, hg'q, t'.w])
    obtain ⟨hOr, hRr⟩ := hs' t' hYs (hYs.lift_fst _ _ _) (hYs.lift_snd _ _ _)
    have hgs : gs = bs ≫ rs := hYs.hom_ext
      (by rw [h1, Category.assoc, hYs.lift_fst, ← Category.assoc bs, hbs₁, Category.assoc])
      (by rw [h2, Category.assoc, hYs.lift_snd, hbs₂])
    subst hgs
    have : IsReduced (pullback p' ((Spec (.of R)).fromSpecResidueField (closedPoint R))) :=
      Stacks.SemistableReduction.isReduced_fiber_of_isAtWorstNodal p' hp' (closedPoint R)
    have : Surjective bs := MorphismProperty.of_isPullback sqb inferInstance
    have : IsProper bs := MorphismProperty.of_isPullback sqb inferInstance
    have : IsProper (pullback.snd p' ((Spec (.of R)).fromSpecResidueField (closedPoint R))) :=
      MorphismProperty.of_isPullback t' inferInstance
    have : CompactSpace
        (pullback p' ((Spec (.of R)).fromSpecResidueField (closedPoint R)) : Scheme.{u}) :=
      QuasiCompact.compactSpace_of_compactSpace (pullback.snd p' _)
    have hOs :=
      Stacks.AlgebraicGeometry.TopDegreeBaseChange.isIso_unitToPushforwardObjUnit_of_isPullback
        b sqb hdim hR1b (h0 := by
          have : IsIso (Scheme.Modules.unitToPushforwardUnit b) := hOb
          infer_instance)
    have hRs :=
      Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_rightDerived_of_isPullback b sqb hdim hR1b
    exact ⟨Stacks.SemistableReduction.isIso_unitToPushforwardObjUnit_comp_of_acyclic _ _ hOs hOr,
      Stacks.SemistableReduction.isZero_rightDerived_comp_of_acyclic _ _ hOs hRs hRr⟩

/-- **The contractions of [Stacks, Tag 0CD9] are isomorphisms on generic fibres**, the centre of
each blowup lying over the closed point of `Spec R`. -/
theorem ExceptionalContractionSequence.isIso_genericFiberMapOfHomOver {C : Scheme.{u}}
    {c : C ⟶ Spec (.of K)} {X Y : Scheme.{u}} {p : X ⟶ Spec (.of R)} {q : Y ⟶ Spec (.of R)}
    {g : X ⟶ Y} (hs : ExceptionalContractionSequence c p q g)
    (hp : IsAtWorstNodalOfRelativeDimensionOne p) :
    IsIso (genericFiberMapOfHomOver (K := K) p q g
      (comp_eq_of_exceptionalContractionSequence hs)) := by
  induction hs with
  | refl p =>
    rw [genericFiberMapOfHomOver_id]
    infer_instance
  | @step X X' Y p p' q g' b D k _ eE hE hb hbp e' hmod hproper hreg rest ih =>
    have hp' := isAtWorstNodal_of_contraction D k eE hE b hb hp hbp
    have ih' := ih hp'
    have hb' := hb
    obtain ⟨_hZ, z, hz, -, -, hD, ε, hε⟩ := hb'
    have hpz := image_eq_closedPoint_of_contraction D k eE hE b z hz hD hp hbp
    have := genericFiberSpec_isOpenImmersion (R := R) (K := K)
    have hU : ((p' ⁻¹ᵁ (genericPointInclusion R K).opensRange : X'.Opens) : Set X') ⊆
        ((Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds X')).support : Set X')ᶜ := by
      intro x hx hxz
      have hxz' : x = z := by simpa using hxz
      subst hxz'
      have hx' : p' x ∈ Set.range (genericPointInclusion R K).base := hx
      rw [hpz] at hx'
      exact closedPoint_notMem_range_genericPointInclusion (K := K) hx'
    have hres : IsIso (b ∣_ (p' ⁻¹ᵁ (genericPointInclusion R K).opensRange)) := by
      rw [← hε, morphismRestrict_comp]
      have h₂ := isIso_blowUpToBase_restrict_of_subset_compl_support _ _ hU
      have h₁ : IsIso (ε.hom ∣_ (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
          (⟨{z}, hz⟩ : Closeds X')) ⁻¹ᵁ p' ⁻¹ᵁ (genericPointInclusion R K).opensRange)) :=
        IsZariskiLocalAtTarget.restrict (P := MorphismProperty.isomorphisms Scheme)
          (inferInstanceAs (IsIso ε.hom)) _
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ h₂
    have := isIso_genericFiberMapOfHomOver_of_isIso_morphismRestrict (K := K) p p' b hbp hres
    rw [genericFiberMapOfHomOver_comp p p' q b g' hbp
      (comp_eq_of_exceptionalContractionSequence rest)]
    infer_instance

end Stacks.Models

end
