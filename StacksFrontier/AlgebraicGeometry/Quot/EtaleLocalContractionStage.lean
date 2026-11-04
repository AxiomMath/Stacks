module

public import StacksFrontier.AlgebraicGeometry.Quot.ContractionUniquenessLocalRingApproximation

/-!
# A family of curves and a morphism to it, at a stage of a limit of affine objects

Let `W = lim Wᵢ` be a directed limit of affine objects of a big fppf site, realised in the site,
mapping compatibly to an object `T` through `τᵢ : Wᵢ ⟶ T`, and let `f : X ⟶ T` be an algebraic
space of finite presentation over `T`. A family of curves `g : Y ⟶ W` (flat, proper, of finite
presentation and of relative dimension at most one) together with a morphism `c : X_W ⟶ Y` over
`W` is, through cartesian squares, the base change of a family of curves `Yₘ ⟶ Wₘ` and a morphism
`X_{Wₘ} ⟶ Yₘ` over a stage `Wₘ` ([Stacks, Tags 07SK, 08K0, 08K1, 0D4K]).

This is the limit step used three times in the proof of [Stacks, Tag 0E7C].

## Main results

* `AlgebraicGeometry.Space.exists_stage_hasRelativeDimensionLE`: relative dimension at most one
  of the base change to the limit holds at a stage ([Stacks, Tag 0D4K]).
* `AlgebraicGeometry.Space.exists_stage_family_hom`: the statement above.

## References

* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 0D4K](https://stacks.math.columbia.edu/tag/0D4K)
* [Stacks Project, Tag 0E7C](https://stacks.math.columbia.edu/tag/0E7C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "𝒯S" => BigFppfOver.toScheme B S hS

variable (B S hS) in
/-- **Relative dimension at most one together with local finite type is stable under base
change** of algebraic spaces. -/
theorem hasRelativeDimensionLE_one_and_isLocallyOfFiniteType_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (k : F ⟶ G) =>
        HasRelativeDimensionLE 1 B S hS k.hom ∧ IsLocallyOfFiniteType B S hS k.hom) where
  of_isPullback {X Y Y' Z} {f g f' g'} sq hg := by
    have sq₀ : IsPullback f'.hom g'.hom g.hom f.hom := sq.map (ObjectProperty.ι _)
    refine ⟨fun x' => ?_, ?_⟩
    · obtain ⟨e, he, h⟩ := hg.1 (pointsMap B S hS Y'.obj f'.hom x')
      exact ⟨e, he, (hasRelativeDimensionAt_iff_of_isPullback B S hS sq₀ Y.property X.property
        Z.property hg.2 x' e).1 h⟩
    · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := fun ⦃F G : AlgebraicSpaces B S hS⦄ (k : F ⟶ G) ↦ IsLocallyOfFiniteType B S hS k.hom)
        sq hg.2

/-- A base change of a finitely presented morphism to a representable base is locally of finite
type. -/
private theorem isLocallyOfFiniteType_of_isPullback_yoneda
    {Z₀ Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T₀ T : BigFppfOver B S hS}
    (hZ₀ : IsAlgebraicSpace B S hS Z₀) (hZ : IsAlgebraicSpace B S hS Z)
    {f₀ : Z₀ ⟶ yoneda.obj T₀} {f : Z ⟶ yoneda.obj T} {q : Z ⟶ Z₀} {t : T ⟶ T₀}
    (sq : IsPullback q f f₀ (yoneda.map t)) (hfp : IsFinitePresentation B S hS f₀) :
    IsLocallyOfFiniteType B S hS f :=
  isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
    (isFinitePresentation_of_isPullback B S hS hZ hZ₀ (isAlgebraicSpace_yoneda B S hS _)
      (isAlgebraicSpace_yoneda B S hS _) sq hfp).1

/-- **Relative dimension at most one at a stage** ([Stacks, Tag 0D4K]). Let `W = lim Wᵢ` be a
directed limit of affine objects of the site, realised in the site. If `f : Z ⟶ W` is the base
change of `f₀ : Z₀ ⟶ W_l`, of finite presentation, and `f` has relative dimension at most one,
then the base change of `f₀` to a later stage has relative dimension at most one. -/
theorem exists_stage_hasRelativeDimensionLE {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    [Nonempty Λ] (D : Λᵒᵖ ⥤ BigFppfOver B S hS) (hD : ∀ j, IsAffine ((𝒯S).obj (D.obj j)))
    (c : Cone D) (hc : IsLimit ((𝒯S).mapCone c)) (l : Λ)
    {Z₀ Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ₀ : IsAlgebraicSpace B S hS Z₀)
    (hZ : IsAlgebraicSpace B S hS Z) (f₀ : Z₀ ⟶ yoneda.obj (D.obj (op l)))
    (hfp : IsFinitePresentation B S hS f₀) (f : Z ⟶ yoneda.obj c.pt) (q : Z ⟶ Z₀)
    (sq : IsPullback q f f₀ (yoneda.map (c.π.app (op l))))
    (hd : HasRelativeDimensionLE 1 B S hS f) :
    ∃ (i : Λ) (hi : l ≤ i),
      HasRelativeDimensionLE 1 B S hS (pullback.snd f₀ (yoneda.map (D.map (homOfLE hi).op))) := by
  have := hasRelativeDimensionLE_one_and_isLocallyOfFiniteType_isStableUnderBaseChange B S hS
  have hft : IsLocallyOfFiniteType B S hS f :=
    isLocallyOfFiniteType_of_isPullback_yoneda hZ₀ hZ sq hfp
  obtain ⟨i, hi, h⟩ := exists_stage_of_isLimit_of_isPullback
    (fun ⦃_ _⦄ k => HasRelativeDimensionLE 1 B S hS k ∧ IsLocallyOfFiniteType B S hS k)
    (fun Dsit hconv hfp' h => by
      obtain ⟨i, hi, hd'⟩ :=
        Dsit.exists_hasRelativeDimensionLE_mapAt_of_siteContainsBaseChangeLimits
          hconv 1 h.1 (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hfp')
      refine ⟨i, hi, hd', ?_⟩
      have sq₁ : IsPullback (pullback.snd (Dsit.baseAtToInitial i hi) Dsit.sourceToBase)
          (Dsit.mapAt i hi) Dsit.map₀
          (pullback.snd (Dsit.baseAtToInitial i hi) Dsit.targetToBase) := by
        refine IsPullback.of_bot ?_ (Dsit.mapAt_snd i hi).symm
          (Dsit.targetAt_isPullback i hi).flip
        exact (Dsit.sourceAt_isPullback i hi).flip.of_iso (Iso.refl _) (Iso.refl _)
          (Iso.refl _) (Iso.refl _)
          (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
          (by
            simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
            exact (Dsit.mapAt_fst i hi).symm)
          (by
            simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
            exact Dsit.map₀_over.symm)
          (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
      exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := fun ⦃F G : AlgebraicSpaces B S hS⦄ (k : F ⟶ G) ↦ IsLocallyOfFiniteType B S hS k.hom)
        (isPullback_homMk B S hS Dsit.source₀_isAlgebraicSpace
          (Dsit.targetAt_isAlgebraicSpace i hi) Dsit.target₀_isAlgebraicSpace
          (Dsit.sourceAt_isAlgebraicSpace i hi) sq₁)
        (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hfp'))
    D hD c hc l hZ₀ hZ f₀ hfp f q sq ⟨hd, hft⟩
  exact ⟨i, hi, h.1⟩

/-- **A family of curves with a morphism to it, at a stage.** Let `W = lim Wᵢ` be a directed limit
of affine objects of the site, realised in the site, with compatible morphisms `τᵢ : Wᵢ ⟶ T`, and
let `f : X ⟶ T` be an algebraic space of finite presentation over `T` with base change `P` to `W`.
A flat, proper morphism `g : Y ⟶ W` of finite presentation and relative dimension at most one,
with a morphism `c : P ⟶ Y` over `W`, is, through cartesian squares, the base change of a flat,
proper `gₘ : Yₘ ⟶ Wₘ` of finite presentation and relative dimension at most one, with a morphism
`cₘ : Xₘ ⟶ Yₘ` over `Wₘ`, where `Xₘ` is the base change of `X` to `Wₘ` ([Stacks, Tags 07SK,
08K0, 08K1, 0D4K]). -/
theorem exists_stage_family_hom {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    [Nonempty Λ] (D : Λᵒᵖ ⥤ BigFppfOver B S hS) (hD : ∀ j, IsAffine ((𝒯S).obj (D.obj j)))
    (c : Cone D) (hc : IsLimit ((𝒯S).mapCone c)) {T : BigFppfOver B S hS}
    (τ : ∀ j, D.obj j ⟶ T) (hτ : ∀ {i j : Λᵒᵖ} (e : i ⟶ j), D.map e ≫ τ j = τ i)
    {X P Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (_hP : IsAlgebraicSpace B S hS P) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ yoneda.obj T) (hfp : IsFinitePresentation B S hS f) (fP : P ⟶ yoneda.obj c.pt)
    (qP : P ⟶ X) (l : Λ) (sqP : IsPullback qP fP f (yoneda.map (c.π.app (op l) ≫ τ (op l))))
    (g : Y ⟶ yoneda.obj c.pt) (hfl : IsFlat B S hS g) (hpr : IsProper B S hS g)
    (hfpg : IsFinitePresentation B S hS g) (hd : HasRelativeDimensionLE 1 B S hS g)
    (cP : P ⟶ Y) (hcP : cP ≫ g = fP) :
    ∃ (M : Λᵒᵖ) (XM YM : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (fM : XM ⟶ yoneda.obj (D.obj M)) (gM : YM ⟶ yoneda.obj (D.obj M)) (pM : XM ⟶ X)
      (qXM : P ⟶ XM) (qYM : Y ⟶ YM) (cM : XM ⟶ YM),
      IsAlgebraicSpace B S hS XM ∧ IsAlgebraicSpace B S hS YM ∧
      IsPullback pM fM f (yoneda.map (τ M)) ∧
      IsFlat B S hS gM ∧ IsProper B S hS gM ∧ IsFinitePresentation B S hS gM ∧
      HasRelativeDimensionLE 1 B S hS gM ∧ cM ≫ gM = fM ∧
      IsPullback qXM fP fM (yoneda.map (c.π.app M)) ∧ qXM ≫ pM = qP ∧
      IsPullback qYM g gM (yoneda.map (c.π.app M)) ∧ cP ≫ qYM = qXM ≫ cM := by
  have : IsCofiltered Λᵒᵖ := inferInstance
  have hT := isAlgebraicSpace_yoneda B S hS T
  have Pfp := isFinitePresentationColimit_of_isLimit_of_isAffine hD hc
  -- the vertex lies over `T` independently of the stage
  have hw : ∀ j : Λᵒᵖ, c.π.app j ≫ τ j = c.π.app (op l) ≫ τ (op l) := by
    intro j
    obtain ⟨k, hk₁, hk₂⟩ := directed_of (· ≤ ·) j.unop l
    rw [← c.w (homOfLE hk₁).op, ← c.w (homOfLE hk₂).op, Category.assoc, Category.assoc, hτ, hτ]
  -- a model of `Y` with the four properties
  obtain ⟨i₀, Y₀, g₀, q₀, hY₀, hfp₀, sq₀⟩ :=
    exists_isPullback_of_isFinitePresentationColimit Pfp hY g hfpg
  obtain ⟨N₁, hN₁, hflN₁, hprN₁⟩ :=
    exists_stage_isFlat_isProper D hD c hc i₀.unop hY₀ hY g₀ hfp₀ g q₀ sq₀ hfl hpr
  obtain ⟨N₂, hN₂, hdN₂⟩ :=
    exists_stage_hasRelativeDimensionLE D hD c hc i₀.unop hY₀ hY g₀ hfp₀ g q₀ sq₀ hd
  obtain ⟨N, hN₁N, hN₂N⟩ := directed_of (· ≤ ·) N₁ N₂
  have hT₀ := isAlgebraicSpace_yoneda B S hS (D.obj i₀)
  have hTN := isAlgebraicSpace_yoneda B S hS (D.obj (op N))
  set eN : op N ⟶ i₀ := (homOfLE (hN₁.trans hN₁N)).op
  set YN := pullback g₀ (yoneda.map (D.map eN))
  set gN : YN ⟶ yoneda.obj (D.obj (op N)) := pullback.snd g₀ (yoneda.map (D.map eN))
  have hYN : IsAlgebraicSpace B S hS YN := isAlgebraicSpace_pullback B S hS g₀ _ hY₀ hTN hT₀
  have hfac : ∀ {i : Λ} (h₁ : i₀.unop ≤ i) (h₂ : i ≤ N),
      yoneda.map (D.map (homOfLE h₂).op) ≫ yoneda.map (D.map (homOfLE h₁).op) =
        yoneda.map (D.map eN) := by
    intro i h₁ h₂
    rw [← Functor.map_comp, ← D.map_comp]
    rfl
  have := isFlat_isStableUnderBaseChange B S hS
  have := hasRelativeDimensionLE_one_and_isLocallyOfFiniteType_isStableUnderBaseChange B S hS
  have hflN : IsFlat B S hS gN :=
    prop_pullback_snd_of_factor (fun ⦃_ _⦄ k => IsFlat B S hS k) hY₀ hT₀ g₀ _ _ _
      (hfac hN₁ hN₁N) hflN₁
  have hprN : IsProper B S hS gN :=
    prop_pullback_snd_of_factor (fun ⦃_ _⦄ k => IsProper B S hS k) hY₀ hT₀ g₀ _ _ _
      (hfac hN₁ hN₁N) hprN₁
  have hfpN : IsFinitePresentation B S hS gN :=
    isFinitePresentation_of_isPullback B S hS hYN hY₀ hTN hT₀
      (IsPullback.of_hasPullback g₀ (yoneda.map (D.map eN))) hfp₀
  have hdN : HasRelativeDimensionLE 1 B S hS gN := by
    have hft₂ : IsLocallyOfFiniteType B S hS
        (pullback.snd g₀ (yoneda.map (D.map (homOfLE hN₂).op))) :=
      isLocallyOfFiniteType_of_isPullback_yoneda hY₀
        (isAlgebraicSpace_pullback B S hS g₀ _ hY₀ (isAlgebraicSpace_yoneda B S hS _) hT₀)
        (IsPullback.of_hasPullback g₀ _) hfp₀
    exact (prop_pullback_snd_of_factor
      (fun ⦃_ _⦄ k => HasRelativeDimensionLE 1 B S hS k ∧ IsLocallyOfFiniteType B S hS k)
      hY₀ hT₀ g₀ _ _ _ (hfac hN₂ hN₂N) ⟨hdN₂, hft₂⟩).1
  have sqN := isPullback_lift_cone c eN sq₀
  -- the model of `P` at the stage `N`
  have sqXN := isPullback_lift_of_isPullback_of_fac B S hS sqP (yoneda.map (c.π.app (op N)))
    (yoneda.map (τ (op N))) (by rw [← Functor.map_comp, hw])
  have hXN : IsAlgebraicSpace B S hS (pullback f (yoneda.map (τ (op N)))) :=
    isAlgebraicSpace_pullback B S hS f _ hX hTN hT
  have hfpXN : IsFinitePresentation B S hS (pullback.snd f (yoneda.map (τ (op N)))) :=
    isFinitePresentation_of_isPullback B S hS hXN hX hTN hT (IsPullback.of_hasPullback f _) hfp
  -- the morphism at a later stage
  obtain ⟨j, e, cj, hcjs, hcj⟩ :=
    exists_isPullback_hom_of_isFinitePresentationColimit Pfp (op N) hXN hYN hfpXN hfpN sqXN sqN
      cP hcP
  have hTj := isAlgebraicSpace_yoneda B S hS (D.obj j)
  obtain ⟨hflM, hprM, hfpM, hdM⟩ := curveFamilyConditions_of_isPullback B S hS
    (IsPullback.of_hasPullback gN (yoneda.map (D.map e))) hYN
    (isAlgebraicSpace_pullback B S hS gN _ hYN hTj hTN) hflN hprN hfpN hdN
  refine ⟨j, pullback (pullback.snd f (yoneda.map (τ (op N)))) (yoneda.map (D.map e)),
    pullback gN (yoneda.map (D.map e)), pullback.snd _ _, pullback.snd _ _,
    pullback.fst _ _ ≫ pullback.fst _ _, _, _, cj,
    isAlgebraicSpace_pullback B S hS _ _ hXN hTj hTN,
    isAlgebraicSpace_pullback B S hS gN _ hYN hTj hTN, ?_, hflM, hprM, hfpM, hdM, hcjs,
    isPullback_lift_cone c e sqXN, ?_, isPullback_lift_cone c e sqN, hcj⟩
  · have h := (IsPullback.of_hasPullback (pullback.snd f (yoneda.map (τ (op N))))
      (yoneda.map (D.map e))).paste_horiz (IsPullback.of_hasPullback f (yoneda.map (τ (op N))))
    rwa [← Functor.map_comp, hτ] at h
  · exact (pullback.lift_fst_assoc _ _ _ _).trans (pullback.lift_fst _ _ _)

end AlgebraicGeometry.Space

end
