module

public import StacksFrontier.AlgebraicGeometry.Quot.EtaleLocalContractionNoetherian

/-!
# The conclusion of Stacks 0E7C is stable under base change

Let `f : X ⟶ T` be an algebraic space over an object of the big fppf site of the integers and
`k : K ⟶ T` a point at which the fibre of `X` is presented by `F` and `h₀ : F ⟶ Y₀` is given.
If the conclusion of [Stacks, Tag 0E7C] holds for `X` at `k`, it holds for any base change `X'` of
`X` along `τ : T' ⟶ T`, at any point `k' : K' ⟶ T'` lying over `k` through `m : K' ⟶ K`, for the
base change of `h₀` along `m`: the étale neighbourhood, the family of curves and the morphism are
base changed along `τ`.

This is the step of the proof of [Stacks, Tag 0E7C] which returns from a stage of a limit to the
limit, and which passes to a smaller base (an open neighbourhood) or an isomorphic point.

## Main results

* `AlgebraicGeometry.EtaleLocalContraction.HasEtaleLocalExtension.baseChange`.

## References

* [Stacks Project, Tag 0E7C](https://stacks.math.columbia.edu/tag/0E7C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.EtaleLocalContraction

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

attribute [local instance] Space.preservesLimitsOfShape_walkingCospan_toScheme

/-- Given a pullback square `R` and an outer pullback square whose bottom map factors as
`u ≫ e`, the induced map from the top-left corner makes the left square a pullback. -/
private theorem exists_isPullback_lift {C : Type*} [Category C] {P X Y Z A B : C} {p : P ⟶ X}
    {s : P ⟶ Y} {f : X ⟶ Z} {e : Y ⟶ Z} (R : IsPullback p s f e) {i : A ⟶ X} {t : A ⟶ B}
    {u : B ⟶ Y} {k : B ⟶ Z} (outer : IsPullback i t f k) (hk : u ≫ e = k) :
    ∃ l : A ⟶ P, l ≫ p = i ∧ l ≫ s = t ≫ u ∧ IsPullback l t s u := by
  subst hk
  have hl := R.lift_snd i (t ≫ u) (by rw [Category.assoc, outer.w])
  refine ⟨_, R.lift_fst _ _ _, hl, IsPullback.of_right ?_ hl R⟩
  rwa [R.lift_fst]

/-- **Base change of the conclusion of [Stacks, Tag 0E7C].** If the conclusion holds for
`f : X ⟶ T` at `k : K ⟶ T` with the presentation `F` and `h₀ : F ⟶ Y₀`, it holds for the base
change `f' : X' ⟶ T'` of `f` along `τ : T' ⟶ T` at a point `k' : K' ⟶ T'` lying over `k` through
`m : K' ⟶ K`, with a presentation `F'` of the fibre of `X'` mapping to `F` over `m`, and
`h₀' : F' ⟶ Y₀'` the base change of `h₀`: `Y₀' = Y₀ ×_K K'` and `h₀'` is compatible with `h₀`. -/
theorem HasEtaleLocalExtension.baseChange {T K F : BigFppfOver B integerBase hZ}
    {X : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} {f : X ⟶ yoneda.obj T} {k : K ⟶ T}
    {tX : F ⟶ K} {iX : yoneda.obj F ⟶ X} {Y₀ : Scheme.{u}} {pY₀ : Y₀ ⟶ (𝒯).obj K}
    {h₀ : (𝒯).obj F ⟶ Y₀} (H : HasEtaleLocalExtension f k tX iX pY₀ h₀)
    {T' K' F' : BigFppfOver B integerBase hZ} {X' : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u}
    (f' : X' ⟶ yoneda.obj T') (q : X' ⟶ X) (τ : T' ⟶ T) (sq : IsPullback q f' f (yoneda.map τ))
    (k' : K' ⟶ T') (m : K' ⟶ K) (hkm : k' ≫ τ = m ≫ k)
    (tX' : F' ⟶ K') (iX' : yoneda.obj F' ⟶ X')
    (hiX' : IsPullback iX' (yoneda.map tX') f' (yoneda.map k'))
    (aF : F' ⟶ F) (haF : iX' ≫ q = yoneda.map aF ≫ iX) (haFt : aF ≫ tX = tX' ≫ m)
    {Y₀' : Scheme.{u}} (pY₀' : Y₀' ⟶ (𝒯).obj K') (bY : Y₀' ⟶ Y₀)
    (hbY : IsPullback bY pY₀' pY₀ ((𝒯).map m)) (h₀' : (𝒯).obj F' ⟶ Y₀')
    (hh₀' : h₀' ≫ pY₀' = (𝒯).map tX') (hh₀b : h₀' ≫ bY = (𝒯).map aF ≫ h₀) :
    HasEtaleLocalExtension f' k' tX' iX' pY₀' h₀' := by
  obtain ⟨U, e, ū, he, hū, Y, XU, g, pXU, fXU, h, hY, hXU, hflg, hprg, hfpg, hdg, sqXU, hhg,
    iXU, G, tG, iG, φ, a, hiXU, hiXUp, hiG, hφ, hat, hcomp, ha⟩ := H
  -- the étale neighbourhood
  let fstU := pullback.fst e τ
  let e' := pullback.snd e τ
  have he' : Etale ((𝒯).map e') :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale)
      ((IsPullback.of_hasPullback e τ).map (𝒯)) he
  let ū' : K' ⟶ pullback e τ := pullback.lift (m ≫ ū) k' (by rw [Category.assoc, hū, hkm])
  have hū' : ū' ≫ e' = k' := pullback.lift_snd _ _ _
  have hū'f : ū' ≫ fstU = m ≫ ū := pullback.lift_fst _ _ _
  have hUa := isAlgebraicSpace_yoneda B integerBase hZ U
  have hU'a := isAlgebraicSpace_yoneda B integerBase hZ (pullback e τ)
  -- the family of curves
  have hY' := isAlgebraicSpace_pullback B integerBase hZ g (yoneda.map fstU) hY hU'a hUa
  obtain ⟨hfl', hpr', hfp', hd'⟩ := Space.curveFamilyConditions_of_isPullback B integerBase hZ
    (IsPullback.of_hasPullback g (yoneda.map fstU)) hY hY' hflg hprg hfpg hdg
  -- the base change of `X`
  have hXU' := isAlgebraicSpace_pullback B integerBase hZ fXU (yoneda.map fstU) hXU hU'a hUa
  have hwU : yoneda.map fstU ≫ yoneda.map e = yoneda.map e' ≫ yoneda.map τ := by
    rw [← Functor.map_comp, ← Functor.map_comp, pullback.condition]
  obtain ⟨pXU', hpXU'q, hpXU'f, sqXU'⟩ := exists_isPullback_lift sq
    ((IsPullback.of_hasPullback fXU (yoneda.map fstU)).paste_horiz sqXU) hwU.symm
  let h' : pullback fXU (yoneda.map fstU) ⟶ pullback g (yoneda.map fstU) :=
    pullback.map _ _ _ _ h (𝟙 _) (𝟙 _) (by simp [hhg]) (by simp)
  have hh' : h' ≫ pullback.snd g (yoneda.map fstU) = pullback.snd fXU (yoneda.map fstU) := by
    simp [h']
  -- the fibre of the base change of `X` over `ū'`
  have hūk : yoneda.map ū' ≫ yoneda.map e' = yoneda.map k' := by rw [← Functor.map_comp, hū']
  obtain ⟨iXU', hiXU'p, hiXU's, hiXU'⟩ := exists_isPullback_lift sqXU' hiX' hūk
  -- the fibre of the family over `ū'`
  let fstG := pullback.fst tG m
  let tG' := pullback.snd tG m
  obtain ⟨iG', hf, hs, hiG'⟩ := exists_isPullback_lift
    (IsPullback.of_hasPullback g (yoneda.map fstU))
    (((IsPullback.of_hasPullback tG m).map yoneda).paste_horiz hiG)
    (by rw [← Functor.map_comp, hū'f, Functor.map_comp])
  -- the identification of the fibre with `Y₀'`
  have hGT : IsPullback ((𝒯).map fstG ≫ φ.hom) ((𝒯).map tG') pY₀ ((𝒯).map m) := by
    have h₁ := (IsPullback.of_hasPullback tG m).map (𝒯)
    exact IsPullback.of_iso h₁ (Iso.refl _) φ (Iso.refl _) (Iso.refl _) (by simp; rfl)
      (by simp; rfl) (by simp [hφ]) (by simp)
  obtain ⟨φ', hφ'1, hφ'2⟩ : ∃ φ' : (𝒯).obj (pullback tG m) ≅ Y₀',
      φ'.hom ≫ bY = (𝒯).map fstG ≫ φ.hom ∧ φ'.hom ≫ pY₀' = (𝒯).map tG' :=
    ⟨hGT.isoIsPullback _ _ hbY, IsPullback.isoIsPullback_hom_fst _ _ _ _,
      IsPullback.isoIsPullback_hom_snd _ _ _ _⟩
  let a' : F' ⟶ pullback tG m := pullback.lift (aF ≫ a) tX' (by rw [Category.assoc, hat, haFt])
  have ha'f : a' ≫ fstG = aF ≫ a := pullback.lift_fst _ _ _
  have ha's : a' ≫ tG' = tX' := pullback.lift_snd _ _ _
  -- compatibilities
  have hfib : iXU' ≫ pullback.fst fXU (yoneda.map fstU) = yoneda.map aF ≫ iXU := by
    apply sqXU.hom_ext
    · rw [Category.assoc, ← hpXU'q, reassoc_of% hiXU'p, haF, Category.assoc, hiXUp]
    · rw [Category.assoc, pullback.condition, reassoc_of% hiXU's, Category.assoc, hiXU.w,
        ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp_assoc, ← Functor.map_comp,
        hū'f, haFt, Category.assoc]
  have hcompat : iXU' ≫ h' = yoneda.map a' ≫ iG' := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, hf,
        ← Category.assoc, hfib, Category.assoc, hcomp, ← Category.assoc, ← Functor.map_comp,
        ← Functor.map_comp_assoc, ha'f, Functor.map_comp, Category.assoc]
    · rw [Category.assoc, Category.assoc, hh', hiXU's, hs,
        ← Functor.map_comp_assoc, ha's]
  have hfinal : (𝒯).map a' ≫ φ'.hom = h₀' := by
    apply hbY.hom_ext
    · rw [Category.assoc, hφ'1, ← Category.assoc, ← Functor.map_comp, ha'f, Functor.map_comp,
        Category.assoc, ha, hh₀b]
    · rw [Category.assoc, hφ'2, ← Functor.map_comp, ha's, hh₀']
  exact ⟨pullback e τ, e', ū', he', hū', _, _, pullback.snd g (yoneda.map fstU), pXU',
    pullback.snd fXU (yoneda.map fstU), h', hY', hXU', hfl', hpr', hfp', hd', sqXU', hh', iXU',
    pullback tG m, tG', iG', φ', a', hiXU', hiXU'p, hiG', hφ'2, ha's, hcompat, hfinal⟩

end AlgebraicGeometry.EtaleLocalContraction

end
