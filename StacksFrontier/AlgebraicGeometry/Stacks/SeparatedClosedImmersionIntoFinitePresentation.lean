module

public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedImmersionIntoFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackModelRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemProperModelSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.ProperMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.BaseChangeLimitsConvention
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ConventionAlongMonomorphicComparison

/-!
# The relation of a separated groupoid is proper at every late stage

Let `Y = lim Y_i` be the limit of a Noetherian limit system (Situation 0CP6) and let
`(U, R, s, t, c)` be a groupoid in algebraic spaces over `Y` with a descent
`(U_i, R_i, s_i, t_i, c_i)` to the late stages of the system
(`AlgebraicGeometry.GroupoidInAlgebraicSpaces.LimitDescent`). The second paragraph of the proof
of Stacks 0CQ2 shows that if `(s, t) : R ⟶ U ×_Y U` is proper, then so is
`(s_i, t_i) : R_i ⟶ U_i ×_{Y_i} U_i` for all large `i`; this is what makes the quotient stack
`[U_i/R_i]` separated over `Y_i`, by
`AlgebraicGeometry.Stack.QuotientStackModel.isSeparated_structureMorphism_iff`.

## Main results

* `CategoryTheory.Limits.isLimitSelfPullbackCone`: limits commute with the fibre square of a
  natural transformation, `X ×_Y X = lim X_i ×_{Y_i} X_i`.
* `AlgebraicGeometry.Space.isClosedImmersion_pullback_map`: a fibre product of closed immersions
  over a common base is a closed immersion.
* `AlgebraicGeometry.Space.isAffineHom_pullback_map_of_isClosedImmersion`: the fibre square of a
  closed subspace `U' ⊆ Y' ×_Y U` is affine over `U ×_Y U` when `Y' ⟶ Y` is affine.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.LimitDescent.isPullback_relationMap_stage`:
  `R = (U ×_Y U) ×_{U_k ×_{Y_k} U_k} R_k`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.LimitDescent.isProper_relationLimitMap`: the base
  change of `(s_k, t_k)` to `U ×_Y U = lim U_i ×_{Y_i} U_i` is proper when `(s, t)` is.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.LimitDescent.`
  `eventually_isProper_relationMap_stageGroupoid`: `(s_i, t_i)` is proper for all large `i`,
  for stages satisfying the chapter's convention.

## Implementation notes

The source applies Stacks 0CPE to `(s, t)` and Stacks 0CPF to the projections of `U ×_Y U`,
through the limit description `(V_i)` of `U ×_Y U`. Here the limit description is
`(U_i ×_{Y_i} U_i)` itself: it is an inverse system with affine transition morphisms
(`isAffineHom_pullback_map_of_isClosedImmersion`) and limit `U ×_Y U`
(`isLimitSelfPullbackCone`). Since `U ⟶ Y ×_{Y_k} U_k` is a closed immersion and
`R = U ×_{U_k} R_k`, the morphism `(s, t)` is the base change of `(s_k, t_k)` to that limit, so
Stacks 08K1 makes its base change to some `U_j ×_{Y_j} U_j` proper, hence its base changes to all
later stages; and `R_i` is a closed subspace of the base change
`(U_i ×_{Y_i} U_i) ×_{U_k ×_{Y_k} U_k} R_k`, because it is one of `Y_i ×_{Y_k} R_k`. So neither
0CPE nor 0CPF is used.

Stacks 08K1 is applied in its form under the chapter's convention of Section 70.2
(`AlgebraicGeometry.Space.MorphismDescentSituation.`
`exists_isProper_mapAt_of_siteContainsBaseChangeLimits`), to the system `U_i ×_{Y_i} U_i`, which
satisfies the convention when the stages `Y_i` do
(`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits.of_mono_lift`). Without the convention
Stacks 08K1 fails for an index set larger than the site
(`AlgebraicGeometry.Space.SiteConventionCounterexample.not_siteContainsBaseChangeLimits`).

## References

* [Stacks Project, Tag 0CQ2](https://stacks.math.columbia.edu/tag/0CQ2)
* [Stacks Project, Tag 08K1](https://stacks.math.columbia.edu/tag/08K1)
* [Stacks Project, Tag 0CP9](https://stacks.math.columbia.edu/tag/0CP9)
* [Stacks Project, Tag 0CPA](https://stacks.math.columbia.edu/tag/0CPA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.Limits

/-- A morphism into a fibre product is a monomorphism if its two components jointly cancel. -/
private theorem mono_pullback_lift_of {C : Type*} [Category C] {X Y Z A : C} {f : X ⟶ Z}
    {g : Y ⟶ Z} [HasPullback f g] (a : A ⟶ X) (b : A ⟶ Y) (w : a ≫ f = b ≫ g)
    (h : ∀ {T : C} (x y : T ⟶ A), x ≫ a = y ≫ a → x ≫ b = y ≫ b → x = y) :
    Mono (pullback.lift a b w) :=
  ⟨fun x y hxy => h x y
    (by simpa only [Category.assoc, pullback.lift_fst] using congrArg (· ≫ pullback.fst f g) hxy)
    (by simpa only [Category.assoc, pullback.lift_snd] using congrArg (· ≫ pullback.snd f g) hxy)⟩

section SelfPullback

variable {K : Type*} [Category K] {C : Type*} [Category C] [HasPullbacks C]
  {FX FY : K ⥤ C} (b : FX ⟶ FY)

/-- The functor `k ↦ FX k ×_{FY k} FX k` of fibre products of a natural transformation with
itself. -/
noncomputable abbrev selfPullbackFunctor : K ⥤ C where
  obj k := pullback (b.app k) (b.app k)
  map a := pullback.map _ _ _ _ (FX.map a) (FX.map a) (FY.map a) (b.naturality a).symm
    (b.naturality a).symm
  map_id k := by apply pullback.hom_ext <;> simp
  map_comp a a' := by apply pullback.hom_ext <;> simp

/-- The value of `selfPullbackFunctor b` at `k` is `FX k ×_{FY k} FX k`. -/
lemma selfPullbackFunctor_obj (k : K) :
    (selfPullbackFunctor b).obj k = pullback (b.app k) (b.app k) := rfl

/-- The transition maps of `selfPullbackFunctor b` commute with the first projections. -/
@[reassoc (attr := simp)]
lemma selfPullbackFunctor_map_fst {k k' : K} (a : k ⟶ k') :
    (selfPullbackFunctor b).map a ≫ (pullback.fst (b.app k') (b.app k') :
      (selfPullbackFunctor b).obj k' ⟶ _) = pullback.fst (b.app k) (b.app k) ≫ FX.map a :=
  pullback.lift_fst _ _ _

/-- The transition maps of `selfPullbackFunctor b` commute with the second projections. -/
@[reassoc (attr := simp)]
lemma selfPullbackFunctor_map_snd {k k' : K} (a : k ⟶ k') :
    (selfPullbackFunctor b).map a ≫ (pullback.snd (b.app k') (b.app k') :
      (selfPullbackFunctor b).obj k' ⟶ _) = pullback.snd (b.app k) (b.app k) ≫ FX.map a :=
  pullback.lift_snd _ _ _

/-- The structure morphism `FX k ×_{FY k} FX k ⟶ FY k` of the fibre squares. -/
noncomputable abbrev selfPullbackToBase : selfPullbackFunctor b ⟶ FY where
  app k := pullback.fst (b.app k) (b.app k) ≫ b.app k
  naturality k k' a := by
    simp only [selfPullbackFunctor_map_fst_assoc, Category.assoc, b.naturality]

/-- **The fibre squares of a system embed into their base changes when the system does.** If
every comparison `FX k ⟶ FX k' ×_{FY k'} FY k` is a monomorphism, so is every comparison
`FX k ×_{FY k} FX k ⟶ (FX k' ×_{FY k'} FX k') ×_{FY k'} FY k`. -/
theorem mono_lift_selfPullbackToBase
    (h : ∀ {k k' : K} (a : k ⟶ k'), Mono (pullback.lift (FX.map a) (b.app k) (b.naturality a) :
      FX.obj k ⟶ pullback (b.app k') (FY.map a)))
    {k k' : K} (a : k ⟶ k') :
    Mono (pullback.lift ((selfPullbackFunctor b).map a) ((selfPullbackToBase b).app k)
      ((selfPullbackToBase b).naturality a) :
      (selfPullbackFunctor b).obj k ⟶ pullback ((selfPullbackToBase b).app k') (FY.map a)) := by
  refine mono_pullback_lift_of _ _ _ fun {W} x y h₁ h₂ => ?_
  have := h a
  have hc : ∀ z : W ⟶ (selfPullbackFunctor b).obj k,
      z ≫ pullback.snd (b.app k) (b.app k) ≫ b.app k =
        z ≫ pullback.fst (b.app k) (b.app k) ≫ b.app k := fun z => by
    rw [pullback.condition]
  apply pullback.hom_ext
  · refine (cancel_mono (pullback.lift (FX.map a) (b.app k) (b.naturality a))).1
      (pullback.hom_ext ?_ ?_)
    · have h₃ := congrArg (· ≫ pullback.fst (b.app k') (b.app k')) h₁
      simpa only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.map] using h₃
    · simpa only [Category.assoc, pullback.lift_snd] using h₂
  · refine (cancel_mono (pullback.lift (FX.map a) (b.app k) (b.naturality a))).1
      (pullback.hom_ext ?_ ?_)
    · have h₃ := congrArg (· ≫ pullback.snd (b.app k') (b.app k')) h₁
      simpa only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.map] using h₃
    · simp only [Category.assoc, pullback.lift_snd]
      rw [hc x, hc y]
      simpa only [Category.assoc] using h₂

variable {b} {cX : Cone FX} {cY : Cone FY} (p : cX.pt ⟶ cY.pt)
  (hp : ∀ k, cX.π.app k ≫ b.app k = p ≫ cY.π.app k)

/-- The cone with vertex `X ×_Y X` over `selfPullbackFunctor b`, for cones `X` over `FX` and `Y`
over `FY` and a morphism `p : X ⟶ Y` compatible with `b`. -/
noncomputable abbrev selfPullbackCone : Cone (selfPullbackFunctor b) where
  pt := pullback p p
  π :=
    { app k := (pullback.map _ _ _ _ (cX.π.app k) (cX.π.app k) (cY.π.app k) (hp k).symm
        (hp k).symm : pullback p p ⟶ (selfPullbackFunctor b).obj k)
      naturality k k' a := by
        apply pullback.hom_ext <;> simp }

/-- The vertex of `selfPullbackCone p hp` is `X ×_Y X`. -/
lemma selfPullbackCone_pt : (selfPullbackCone p hp).pt = pullback p p := rfl

/-- The legs of `selfPullbackCone p hp` commute with the first projections. -/
@[reassoc (attr := simp)]
lemma selfPullbackCone_π_app_fst (k : K) :
    (selfPullbackCone p hp).π.app k ≫ (pullback.fst (b.app k) (b.app k) :
      (selfPullbackFunctor b).obj k ⟶ _) = pullback.fst p p ≫ cX.π.app k :=
  pullback.lift_fst _ _ _

/-- The legs of `selfPullbackCone p hp` commute with the second projections. -/
@[reassoc (attr := simp)]
lemma selfPullbackCone_π_app_snd (k : K) :
    (selfPullbackCone p hp).π.app k ≫ (pullback.snd (b.app k) (b.app k) :
      (selfPullbackFunctor b).obj k ⟶ _) = pullback.snd p p ≫ cX.π.app k :=
  pullback.lift_snd _ _ _

/-- **Limits commute with fibre products.** If `X` and `Y` are limits of `FX` and `FY`, then
`X ×_Y X` is the limit of `FX k ×_{FY k} FX k`. -/
noncomputable def isLimitSelfPullbackCone (hX : IsLimit cX) (hY : IsLimit cY) :
    IsLimit (selfPullbackCone p hp) := by
  let pr₁ (s : Cone (selfPullbackFunctor b)) (k : K) : s.pt ⟶ FX.obj k :=
    s.π.app k ≫ (pullback.fst (b.app k) (b.app k) : (selfPullbackFunctor b).obj k ⟶ _)
  let pr₂ (s : Cone (selfPullbackFunctor b)) (k : K) : s.pt ⟶ FX.obj k :=
    s.π.app k ≫ (pullback.snd (b.app k) (b.app k) : (selfPullbackFunctor b).obj k ⟶ _)
  have n₁ (s : Cone (selfPullbackFunctor b)) {k k' : K} (a : k ⟶ k') :
      pr₁ s k ≫ FX.map a = pr₁ s k' := by
    dsimp only [pr₁]
    rw [← s.w a]
    simp
  have n₂ (s : Cone (selfPullbackFunctor b)) {k k' : K} (a : k ⟶ k') :
      pr₂ s k ≫ FX.map a = pr₂ s k' := by
    dsimp only [pr₂]
    rw [← s.w a]
    simp
  let l₁ (s : Cone (selfPullbackFunctor b)) : s.pt ⟶ cX.pt :=
    hX.lift ⟨s.pt, { app k := pr₁ s k
                     naturality k k' a := (Category.id_comp _).trans (n₁ s a).symm }⟩
  let l₂ (s : Cone (selfPullbackFunctor b)) : s.pt ⟶ cX.pt :=
    hX.lift ⟨s.pt, { app k := pr₂ s k
                     naturality k k' a := (Category.id_comp _).trans (n₂ s a).symm }⟩
  have h₁ (s : Cone (selfPullbackFunctor b)) (k : K) : l₁ s ≫ cX.π.app k = pr₁ s k :=
    hX.fac _ k
  have h₂ (s : Cone (selfPullbackFunctor b)) (k : K) : l₂ s ≫ cX.π.app k = pr₂ s k :=
    hX.fac _ k
  have hw (s : Cone (selfPullbackFunctor b)) : l₁ s ≫ p = l₂ s ≫ p := by
    refine hY.hom_ext fun k => ?_
    rw [Category.assoc, Category.assoc, ← hp, ← Category.assoc, h₁, ← Category.assoc, h₂]
    simp only [pr₁, pr₂, Category.assoc]
    exact congrArg (s.π.app k ≫ ·) pullback.condition
  exact
    { lift s := pullback.lift (l₁ s) (l₂ s) (hw s)
      fac s k := by
        apply pullback.hom_ext
        · rw [Category.assoc, selfPullbackCone_π_app_fst, pullback.lift_fst_assoc, h₁]
        · rw [Category.assoc, selfPullbackCone_π_app_snd, pullback.lift_snd_assoc, h₂]
      uniq s m hm := by
        apply pullback.hom_ext
        · rw [pullback.lift_fst]
          refine hX.hom_ext fun k => ?_
          rw [h₁]
          dsimp only [pr₁]
          rw [← hm k]
          simp
        · rw [pullback.lift_snd]
          refine hX.hom_ext fun k => ?_
          rw [h₂]
          dsimp only [pr₂]
          rw [← hm k]
          simp }

end SelfPullback

section SubPullback

variable {C : Type*} [Category C] [HasPullbacks C] {U' U Y' Y : C} (b : U' ⟶ Y') (b₀ : U ⟶ Y)
  (τ : U' ⟶ U) (τY : Y' ⟶ Y) (w : τ ≫ b₀ = b ≫ τY)

omit [HasPullbacks C] in
/-- The compatibility making `(pr₁ ≫ b, pullback.map b b b₀ b₀ τ τ τY)` a morphism into
`Y' ×_Y (U ×_Y U)`. -/
theorem pullback_map_fst_cond [HasPullback b b] [HasPullback b₀ b₀] :
    (pullback.fst b b ≫ b) ≫ τY =
      pullback.map b b b₀ b₀ τ τ τY w.symm w.symm ≫ pullback.fst b₀ b₀ ≫ b₀ := by
  rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, w]

/-- If `(b, τ) : U' ⟶ Y' ×_Y U` is a monomorphism, so is
`U' ×_{Y'} U' ⟶ Y' ×_Y (U ×_Y U)`. -/
theorem mono_lift_pullback_map (hκ : Mono (pullback.lift b τ w.symm : U' ⟶ pullback τY b₀)) :
    Mono (pullback.lift (pullback.fst b b ≫ b) (pullback.map b b b₀ b₀ τ τ τY w.symm w.symm)
      (pullback_map_fst_cond b b₀ τ τY w) :
        pullback b b ⟶ pullback τY (pullback.fst b₀ b₀ ≫ b₀)) := by
  refine mono_pullback_lift_of _ _ _ fun x y h₁ h₂ => ?_
  have h₂₁ := congrArg (· ≫ pullback.fst _ _) h₂
  have h₂₂ := congrArg (· ≫ pullback.snd _ _) h₂
  simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd] at h₂₁ h₂₂
  apply pullback.hom_ext
  · refine (cancel_mono (pullback.lift b τ w.symm : U' ⟶ pullback τY b₀)).1 ?_
    apply pullback.hom_ext
    · simpa only [Category.assoc, pullback.lift_fst] using h₁
    · simpa only [Category.assoc, pullback.lift_snd] using h₂₁
  · refine (cancel_mono (pullback.lift b τ w.symm : U' ⟶ pullback τY b₀)).1 ?_
    apply pullback.hom_ext
    · simpa only [Category.assoc, pullback.lift_fst, pullback.condition] using h₁
    · simpa only [Category.assoc, pullback.lift_snd] using h₂₂

/-- If `U' ×_{Y'} U' ⟶ Y' ×_Y (U ×_Y U)` is a monomorphism then so is, for `c₀ : R₀ ⟶ U ×_Y U`
with `c₀ ≫ pr₁ ≫ b₀ = bR₀`, the comparison
`(U' ×_{Y'} U') ×_{U ×_Y U} R₀ ⟶ Y' ×_Y R₀`. -/
theorem mono_lift_pullback_fst {R₀ : C} (c₀ : R₀ ⟶ pullback b₀ b₀) (bR₀ : R₀ ⟶ Y)
    (h : c₀ ≫ pullback.fst b₀ b₀ ≫ b₀ = bR₀)
    (hν : Mono (pullback.lift (pullback.fst b b ≫ b) (pullback.map b b b₀ b₀ τ τ τY w.symm w.symm)
      (pullback_map_fst_cond b b₀ τ τY w) :
        pullback b b ⟶ pullback τY (pullback.fst b₀ b₀ ≫ b₀))) :
    Mono (pullback.lift (pullback.fst _ _ ≫ pullback.fst b b ≫ b) (pullback.snd _ c₀) (by
      rw [Category.assoc, Category.assoc, ← Category.assoc (pullback.fst b b),
        pullback_map_fst_cond b b₀ τ τY w,
        ← h, ← Category.assoc, pullback.condition, Category.assoc]) :
        pullback (pullback.map b b b₀ b₀ τ τ τY w.symm w.symm) c₀ ⟶ pullback τY bR₀) := by
  refine mono_pullback_lift_of _ _ _ fun x y h₁ h₂ => ?_
  apply pullback.hom_ext _ h₂
  refine (cancel_mono (pullback.lift (pullback.fst b b ≫ b)
    (pullback.map b b b₀ b₀ τ τ τY w.symm w.symm) (pullback_map_fst_cond b b₀ τ τY w))).1 ?_
  apply pullback.hom_ext
  · simpa only [Category.assoc, pullback.lift_fst] using h₁
  · simp only [Category.assoc, pullback.lift_snd]
    rw [pullback.condition, reassoc_of% h₂, ← pullback.condition]

end SubPullback

end CategoryTheory.Limits

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A fibre product of closed immersions is a closed immersion.** If `κ₁ : A₁ ⟶ P₁` and
`κ₂ : A₂ ⟶ P₂` are closed immersions over `Z`, then so is `A₁ ×_Z A₂ ⟶ P₁ ×_Z P₂`. -/
theorem isClosedImmersion_pullback_map {A₁ A₂ P₁ P₂ Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p₁ : P₁ ⟶ Z) (p₂ : P₂ ⟶ Z) (κ₁ : A₁ ⟶ P₁) (κ₂ : A₂ ⟶ P₂)
    (h₁ : IsClosedImmersion B S hS κ₁) (h₂ : IsClosedImmersion B S hS κ₂) :
    IsClosedImmersion B S hS (pullback.map (κ₁ ≫ p₁) (κ₂ ≫ p₂) p₁ p₂ κ₁ κ₂ (𝟙 Z)
      (Category.comp_id _) (Category.comp_id _)) := by
  have hBC := isClosedImmersion_isStableUnderBaseChange B S hS
  -- `A₁ ×_Z A₂ ⟶ P₁ ×_Z A₂` is a base change of `κ₁`
  let m₁ : pullback (κ₁ ≫ p₁) (κ₂ ≫ p₂) ⟶ pullback p₁ (κ₂ ≫ p₂) :=
    pullback.map _ _ _ _ κ₁ (𝟙 _) (𝟙 Z) (Category.comp_id _) (by simp)
  have sq₁ : IsPullback m₁ (pullback.fst _ _) (pullback.fst _ _) κ₁ := by
    refine IsPullback.of_right (h₁₂ := pullback.snd _ _) (h₂₂ := p₁) ?_
      (by simp [m₁]) (IsPullback.of_hasPullback p₁ (κ₂ ≫ p₂)).flip
    simpa [m₁] using (IsPullback.of_hasPullback (κ₁ ≫ p₁) (κ₂ ≫ p₂)).flip
  -- `P₁ ×_Z A₂ ⟶ P₁ ×_Z P₂` is a base change of `κ₂`
  let m₂ : pullback p₁ (κ₂ ≫ p₂) ⟶ pullback p₁ p₂ :=
    pullback.map _ _ _ _ (𝟙 _) κ₂ (𝟙 Z) (by simp) (Category.comp_id _)
  have sq₂ : IsPullback m₂ (pullback.snd _ _) (pullback.snd _ _) κ₂ := by
    refine IsPullback.of_right (h₁₂ := pullback.fst _ _) (h₂₂ := p₂) ?_
      (by simp [m₂]) (IsPullback.of_hasPullback p₁ p₂)
    simpa [m₂] using IsPullback.of_hasPullback p₁ (κ₂ ≫ p₂)
  have e : pullback.map (κ₁ ≫ p₁) (κ₂ ≫ p₂) p₁ p₂ κ₁ κ₂ (𝟙 Z) (Category.comp_id _)
      (Category.comp_id _) = m₁ ≫ m₂ := by
    apply pullback.hom_ext <;> simp [m₁, m₂]
  rw [e]
  exact isClosedImmersion_comp B S hS _ _ (hBC.of_isPullback sq₁.flip h₁)
    (hBC.of_isPullback sq₂.flip h₂)

/-- **The fibre square of a closed subspace of a base change is affine over the fibre square.**
Let `b : U' ⟶ Y'` and `b₀ : U ⟶ Y` be morphisms of presheaves, `τ : U' ⟶ U` and an affine
`τY : Y' ⟶ Y` with `τ ≫ b₀ = b ≫ τY`, and suppose that `(b, τ) : U' ⟶ Y' ×_Y U` is a closed
immersion. Then the induced morphism `U' ×_{Y'} U' ⟶ U ×_Y U` is affine: it is the closed
immersion `U' ×_{Y'} U' ⟶ (Y' ×_Y U) ×_{Y'} (Y' ×_Y U)` followed by the base change along `τY`
of `U ×_Y U ⟶ Y`. -/
theorem isAffineHom_pullback_map_of_isClosedImmersion
    {U' U Y' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (b : U' ⟶ Y') (b₀ : U ⟶ Y) (τ : U' ⟶ U)
    (τY : Y' ⟶ Y) (w : τ ≫ b₀ = b ≫ τY) (hτY : IsAffineHom B S hS τY)
    (hκ : IsClosedImmersion B S hS (pullback.lift b τ w.symm : U' ⟶ pullback τY b₀)) :
    IsAffineHom B S hS (pullback.map b b b₀ b₀ τ τ τY w.symm w.symm) := by
  let κ : U' ⟶ pullback τY b₀ := pullback.lift b τ w.symm
  have hκq : κ ≫ pullback.fst τY b₀ = b := pullback.lift_fst _ _ _
  have hκs : κ ≫ pullback.snd τY b₀ = τ := pullback.lift_snd _ _ _
  -- the closed immersion `U' ×_{Y'} U' ⟶ P ×_{Y'} P`, `P = Y' ×_Y U`
  let m : pullback b b ⟶ pullback (pullback.fst τY b₀) (pullback.fst τY b₀) :=
    pullback.map _ _ _ _ κ κ (𝟙 Y') (by rw [Category.comp_id, hκq])
      (by rw [Category.comp_id, hκq])
  have hm : IsClosedImmersion B S hS m := by
    have := isClosedImmersion_pullback_map B S hS (pullback.fst τY b₀) (pullback.fst τY b₀) κ κ
      hκ hκ
    convert this using 2 <;> simp [hκq]
  -- the base change `P ×_{Y'} P ⟶ U ×_Y U` of `τY`
  have c₁ : pullback.fst (pullback.fst τY b₀) (pullback.fst τY b₀) ≫ pullback.snd τY b₀ ≫ b₀ =
      pullback.fst (pullback.fst τY b₀) (pullback.fst τY b₀) ≫ pullback.fst τY b₀ ≫ τY := by
    rw [pullback.condition]
  have c₂ : pullback.snd (pullback.fst τY b₀) (pullback.fst τY b₀) ≫ pullback.snd τY b₀ ≫ b₀ =
      pullback.fst (pullback.fst τY b₀) (pullback.fst τY b₀) ≫ pullback.fst τY b₀ ≫ τY := by
    rw [← pullback.condition, ← Category.assoc, ← pullback.condition, Category.assoc]
  let n : pullback (pullback.fst τY b₀) (pullback.fst τY b₀) ⟶ pullback b₀ b₀ :=
    pullback.lift (pullback.fst _ _ ≫ pullback.snd _ _) (pullback.snd _ _ ≫ pullback.snd _ _)
      (by simp only [Category.assoc]; rw [c₁, c₂])
  have hn₁ : n ≫ pullback.fst b₀ b₀ = pullback.fst _ _ ≫ pullback.snd τY b₀ :=
    pullback.lift_fst _ _ _
  have hn₂ : n ≫ pullback.snd b₀ b₀ = pullback.snd _ _ ≫ pullback.snd τY b₀ :=
    pullback.lift_snd _ _ _
  have sq : IsPullback (pullback.fst (pullback.fst τY b₀) (pullback.fst τY b₀) ≫
      pullback.fst τY b₀) n τY (pullback.fst b₀ b₀ ≫ b₀) := by
    refine IsPullback.of_isLimit' ⟨by
      rw [reassoc_of% hn₁]; simp only [Category.assoc]; exact c₁.symm⟩ ?_
    refine PullbackCone.IsLimit.mk _
      (fun c => pullback.lift (pullback.lift c.fst (c.snd ≫ pullback.fst _ _)
          (by rw [c.condition, Category.assoc]))
        (pullback.lift c.fst (c.snd ≫ pullback.snd _ _)
          (by rw [c.condition, Category.assoc]; exact congrArg (c.snd ≫ ·) pullback.condition))
        (by rw [pullback.lift_fst, pullback.lift_fst]))
      (fun c => by rw [pullback.lift_fst_assoc, pullback.lift_fst])
      (fun c => ?_) (fun c l h₁ h₂ => ?_)
    · apply pullback.hom_ext
      · rw [Category.assoc, hn₁, pullback.lift_fst_assoc, pullback.lift_snd]
      · rw [Category.assoc, hn₂, pullback.lift_snd_assoc, pullback.lift_snd]
    · have h₁' : l ≫ pullback.snd _ _ ≫ pullback.fst τY b₀ = c.fst := by
        rw [← h₁, ← pullback.condition]
      apply pullback.hom_ext
      · apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_fst]
          exact h₁
        · simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, ← h₂, hn₁]
      · apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_snd, pullback.lift_fst]
          exact h₁'
        · simp only [Category.assoc, pullback.lift_snd, ← h₂, hn₂]
  have hn : IsAffineHom B S hS n := isAffineHom_of_isPullback sq hτY
  have e : pullback.map b b b₀ b₀ τ τ τY w.symm w.symm = m ≫ n := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hn₁, m, pullback.lift_fst, pullback.lift_fst_assoc, hκs]
    · simp only [Category.assoc, hn₂, m, pullback.lift_snd, pullback.lift_snd_assoc, hκs]
  rw [e]
  exact isAffineHom_comp B S hS _ _ (isAffineHom_of_isClosedImmersion B S hS _ hm) hn

namespace GoodDiagram

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
  {D : NoetherianLimitSystem B S hS hZ I}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {pX : X ⟶ D.limitCone.pt}

/-- The structure morphisms `X_i ⟶ B_i` of the members of the image system of a diagram, on the
tail above a stage `i₀`, as a natural transformation to the system `(B_i)`. -/
@[simps]
noncomputable def toStageBase (G : GoodDiagram B S hS hZ D pX) {i₀ : I} (le : G.index ≤ i₀) :
    (Over.map (homOfLE le).op ⋙ imageSystem G) ⟶ (Over.forget (op i₀) ⋙ D.system) where
  app j := (stageImage G ((Over.map (homOfLE le).op).obj j)).ι ≫ pullback.fst _ _
  naturality j j' a := by
    simp only [Functor.comp_map]
    rw [imageSystem_map_ι_assoc, stageTargetMap_fst]
    rfl

/-- The leg `X ⟶ X_i` of the image cone is compatible with the structure morphisms to the
stages. -/
@[reassoc]
theorem imageCone_π_toStageBase (G : GoodDiagram B S hS hZ D pX) {i₀ : I} (le : G.index ≤ i₀)
    (j : Over (op i₀)) :
    (imageCone G).π.app ((Over.map (homOfLE le).op).obj j) ≫ (toStageBase G le).app j =
      pX ≫ D.limitCone.π.app j.left := by
  rw [toStageBase_app, imageCone_π_ι_assoc, stageMap_fst]
  rfl

omit [Nonempty I] in
/-- The tail of the index set above `i₀`, mapped to the stages above `i ≤ i₀`, is initial. -/
theorem tailFunctor_comp_map_initial (i₀ : I) {i : I} (le : i ≤ i₀) :
    (tailFunctor i₀ ⋙ Over.map (homOfLE le).op).Initial := by
  have := isDirected_tail i₀
  have : Nonempty {j : I // i₀ ≤ j} := ⟨⟨i₀, le_rfl⟩⟩
  refine Functor.initial_of_exists_of_isCofiltered _ (fun d => ?_)
    (fun {_ c} _ _ => ⟨c, 𝟙 _, Over.OverMorphism.ext (Subsingleton.elim _ _)⟩)
  obtain ⟨m, h₁, h₂⟩ := exists_ge_ge d.left.unop i₀
  exact ⟨op ⟨m, h₂⟩, ⟨Over.homMk (homOfLE h₁).op (Subsingleton.elim _ _)⟩⟩

omit [Nonempty I] in
/-- The tail of the index set above `i₀`, mapped to the index set, is initial. -/
theorem tailFunctor_comp_forget_initial (i₀ : I) :
    (tailFunctor i₀ ⋙ Over.forget (op i₀)).Initial := by
  have := isDirected_tail i₀
  have : Nonempty {j : I // i₀ ≤ j} := ⟨⟨i₀, le_rfl⟩⟩
  refine Functor.initial_of_exists_of_isCofiltered _ (fun d => ?_)
    (fun {_ c} _ _ => ⟨c, 𝟙 _, Subsingleton.elim _ _⟩)
  obtain ⟨m, h₁, h₂⟩ := exists_ge_ge d.unop i₀
  exact ⟨op ⟨m, h₂⟩, ⟨(homOfLE h₁).op⟩⟩

omit [Nonempty I] [IsDirectedOrder I] in
/-- The tail of the index set above `i₀`, mapped to the index set, is the inclusion of the
stages at or above `i₀`. -/
theorem tailFunctor_comp_forget_eq (i₀ : I) :
    tailFunctor i₀ ⋙ Over.forget (op i₀) = (Subtype.mono_coe fun j : I => i₀ ≤ j).functor.op :=
  CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => Subsingleton.elim _ _)

/-- **The image system embeds into its base changes.** For `a : j ⟶ k` over a stage `i₀`
above the index of a diagram, the comparison `X_j ⟶ X_k ×_{B_k} B_j` of the image system with
the base change of a later member is a monomorphism: both members are subspaces of the base
changes of the model, compatibly. -/
theorem mono_lift_toStageBase (G : GoodDiagram B S hS hZ D pX) {i₀ : I} (le : G.index ≤ i₀)
    {j k : Over (op i₀)} (a : j ⟶ k) :
    Mono (pullback.lift ((Over.map (homOfLE le).op ⋙ imageSystem G).map a)
      ((toStageBase G le).app j) ((toStageBase G le).naturality a) :
      (Over.map (homOfLE le).op ⋙ imageSystem G).obj j ⟶
        pullback ((toStageBase G le).app k) ((Over.forget (op i₀) ⋙ D.system).map a)) := by
  refine mono_pullback_lift_of _ _ _ fun {W} x y h₁ h₂ => ?_
  refine (cancel_mono (stageImage G ((Over.map (homOfLE le).op).obj j)).ι).1
    (pullback.hom_ext ?_ ?_)
  · simpa only [toStageBase_app, Category.assoc] using h₂
  · have h₃ := congrArg (· ≫ (stageImage G ((Over.map (homOfLE le).op).obj k)).ι ≫
      pullback.snd _ _) h₁
    simpa only [Functor.comp_map, Category.assoc, imageSystem_map_ι_assoc,
      stageTargetMap_snd] using h₃

end GoodDiagram

end AlgebraicGeometry.Space


namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

open Space Space.GoodDiagram

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
  {D : NoetherianLimitSystem B S hS hZ I}

namespace LimitDescent

variable {G : GroupoidInAlgebraicSpaces B S hS D.limitSpace} (Δ : LimitDescent G)

/-- The object spaces `U_i`, on the tail `{i // Δ.index ≤ i}`. -/
noncomputable abbrev objectsTail : {j : I // Δ.index ≤ j}ᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  tailFunctor Δ.index ⋙ (Over.map (homOfLE Δ.le_objects).op ⋙ imageSystem Δ.objects)

/-- The arrow spaces `R_i`, on the tail `{i // Δ.index ≤ i}`. -/
noncomputable abbrev arrowsTail : {j : I // Δ.index ≤ j}ᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  tailFunctor Δ.index ⋙ (Over.map (homOfLE Δ.le_arrows).op ⋙ imageSystem Δ.arrows)

/-- The stages `Y_i`, on the tail `{i // Δ.index ≤ i}`. -/
noncomputable abbrev baseTail : {j : I // Δ.index ≤ j}ᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  tailFunctor Δ.index ⋙ (Over.forget (op Δ.index) ⋙ D.system)

/-- The structure morphisms `U_i ⟶ Y_i`. -/
noncomputable abbrev objectsToBaseTail : Δ.objectsTail ⟶ Δ.baseTail :=
  Functor.whiskerLeft (tailFunctor Δ.index) (toStageBase Δ.objects Δ.le_objects)

/-- The fibre squares `U_i ×_{Y_i} U_i`. -/
noncomputable abbrev pairsTail : {j : I // Δ.index ≤ j}ᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  selfPullbackFunctor Δ.objectsToBaseTail

/-- The morphisms `(s_i, t_i) : R_i ⟶ U_i ×_{Y_i} U_i`. -/
noncomputable def relationTail : Δ.arrowsTail ⟶ Δ.pairsTail where
  app k := pullback.lift (Δ.source.maps.app ((tailFunctor Δ.index).obj k))
    (Δ.target.maps.app ((tailFunctor Δ.index).obj k))
    ((Δ.source.over_base _).trans (Δ.target.over_base _).symm)
  naturality k k' a := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      exact (congrArg (_ ≫ ·) (pullback.lift_fst _ _ _)).trans
        ((Δ.source.maps.naturality ((tailFunctor Δ.index).map a)).trans
          (pullback.lift_fst_assoc _ _ _ _).symm)
    · simp only [Category.assoc, pullback.lift_snd]
      exact (congrArg (_ ≫ ·) (pullback.lift_snd _ _ _)).trans
        ((Δ.target.maps.naturality ((tailFunctor Δ.index).map a)).trans
          (pullback.lift_snd_assoc _ _ _ _).symm)

/-- The cone `U ⟶ U_i` of the object spaces, on the tail. -/
noncomputable abbrev objectsCone : Cone Δ.objectsTail :=
  (imageCone Δ.objects).whisker (tailFunctor Δ.index ⋙ Over.map (homOfLE Δ.le_objects).op)

/-- The cone `Y ⟶ Y_i` of the stages, on the tail. -/
noncomputable abbrev baseCone : Cone Δ.baseTail :=
  D.limitCone.whisker (tailFunctor Δ.index ⋙ Over.forget (op Δ.index))

/-- **Stacks 0CP9, on the tail:** `U = lim U_i`. -/
noncomputable def isLimitObjectsCone : IsLimit Δ.objectsCone :=
  haveI := tailFunctor_comp_map_initial Δ.index Δ.le_objects
  (Functor.Initial.isLimitWhiskerEquiv _ _).symm
    (isLimit_imageCone_of_algebraicLimit Δ.objects G.objects.property)

/-- `Y = lim Y_i`, on the tail. -/
noncomputable def isLimitBaseCone : IsLimit Δ.baseCone :=
  haveI := tailFunctor_comp_forget_initial Δ.index
  (Functor.Initial.isLimitWhiskerEquiv _ _).symm D.isLimit

/-- The legs `U ⟶ U_i` are compatible with the structure morphisms to `Y` and `Y_i`. -/
theorem objectsCone_π_toBase (k : {j : I // Δ.index ≤ j}ᵒᵖ) :
    Δ.objectsCone.π.app k ≫ Δ.objectsToBaseTail.app k =
      G.objectsToBase.hom ≫ Δ.baseCone.π.app k :=
  imageCone_π_toStageBase Δ.objects Δ.le_objects _

/-- The cone `U ×_Y U ⟶ U_i ×_{Y_i} U_i`. -/
noncomputable abbrev pairsCone : Cone Δ.pairsTail :=
  selfPullbackCone (b := Δ.objectsToBaseTail) (cX := Δ.objectsCone) (cY := Δ.baseCone)
    G.objectsToBase.hom Δ.objectsCone_π_toBase

/-- `U ×_Y U = lim U_i ×_{Y_i} U_i`. -/
noncomputable def isLimitPairsCone : IsLimit Δ.pairsCone :=
  isLimitSelfPullbackCone (b := Δ.objectsToBaseTail) (cX := Δ.objectsCone) (cY := Δ.baseCone)
    G.objectsToBase.hom Δ.objectsCone_π_toBase Δ.isLimitObjectsCone Δ.isLimitBaseCone

/-- The initial stage of the tail. -/
abbrev tailInitial : {j : I // Δ.index ≤ j} := ⟨Δ.index, le_rfl⟩

/-- **`R = (U ×_Y U) ×_{U_k ×_{Y_k} U_k} R_k`** at the stage `k = Δ.index`, written with plain
fibre products: from `R = U ×_{U_k} R_k` along `s` and the closed immersion
`U ⟶ Y ×_{Y_k} U_k`. -/
theorem isPullback_relationMap_stage :
    let πR := (imageCone Δ.arrows).π.app
      ((Over.map (homOfLE Δ.le_arrows).op).obj (Over.mk (homOfLE (le_refl Δ.index)).op))
    let πU := (imageCone Δ.objects).π.app
      ((Over.map (homOfLE Δ.le_objects).op).obj (Over.mk (homOfLE (le_refl Δ.index)).op))
    let b₀ := (toStageBase Δ.objects Δ.le_objects).app (Over.mk (homOfLE (le_refl Δ.index)).op)
    let s₀ := Δ.source.maps.app (Over.mk (homOfLE (le_refl Δ.index)).op)
    let t₀ := Δ.target.maps.app (Over.mk (homOfLE (le_refl Δ.index)).op)
    ∀ (hp : G.objectsToBase.hom ≫ D.limitCone.π.app (op Δ.index) = πU ≫ b₀)
      (hst : s₀ ≫ b₀ = t₀ ≫ b₀),
    IsPullback (relationMap G) πR
      (pullback.map _ _ _ _ πU πU (D.limitCone.π.app (op Δ.index)) hp hp)
      (pullback.lift s₀ t₀ hst) := by
  intro πR πU b₀ s₀ t₀ hp hst
  have hsP : IsPullback πR G.source.hom s₀ πU := Δ.source_isPullback Δ.index le_rfl
  have hsi : πR ≫ s₀ = G.source.hom ≫ πU := Δ.source.induces _
  have hti : πR ≫ t₀ = G.target.hom ≫ πU := Δ.target.induces _
  let κ : G.objects.obj ⟶ pullback (D.limitCone.π.app (op Δ.index)) b₀ :=
    pullback.lift G.objectsToBase.hom πU hp
  have hκ : Mono κ :=
    mono_of_isClosedImmersion B S hS _ (Δ.isClosedImmersion_objects Δ.index le_rfl)
  refine IsPullback.of_isLimit' ⟨?_⟩ ?_
  · apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst,
        pullback.lift_fst_assoc, hsi]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd,
        pullback.lift_snd_assoc, hti]
  have e₁ (c : PullbackCone (pullback.map _ _ _ _ πU πU (D.limitCone.π.app (op Δ.index)) hp hp)
      (pullback.lift s₀ t₀ hst)) : c.snd ≫ s₀ = (c.fst ≫ pullback.fst _ _) ≫ πU := by
    have := congrArg (· ≫ pullback.fst _ _) c.condition
    simp only [Category.assoc, pullback.lift_fst] at this
    exact this.symm
  have e₂ (c : PullbackCone (pullback.map _ _ _ _ πU πU (D.limitCone.π.app (op Δ.index)) hp hp)
      (pullback.lift s₀ t₀ hst)) : c.snd ≫ t₀ = (c.fst ≫ pullback.snd _ _) ≫ πU := by
    have := congrArg (· ≫ pullback.snd _ _) c.condition
    simp only [Category.assoc, pullback.lift_snd] at this
    exact this.symm
  refine PullbackCone.IsLimit.mk _ (fun c => hsP.lift c.snd (c.fst ≫ pullback.fst _ _) (e₁ c))
    (fun c => ?_) (fun c => hsP.lift_fst _ _ _) (fun c l h₁ h₂ => ?_)
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, hsP.lift_snd]
    · rw [Category.assoc, pullback.lift_snd]
      refine (cancel_mono κ).1 ?_
      apply pullback.hom_ext
      · simp only [κ, Category.assoc, pullback.lift_fst]
        have ht : G.target.hom ≫ G.objectsToBase.hom = G.source.hom ≫ G.objectsToBase.hom :=
          (target_comp_objectsToBase G).trans (source_comp_objectsToBase G).symm
        rw [ht, ← Category.assoc, hsP.lift_snd, Category.assoc, pullback.condition]
      · simp only [κ, Category.assoc, pullback.lift_snd]
        rw [← hti, ← Category.assoc, hsP.lift_fst, e₂, Category.assoc]
  · refine hsP.hom_ext ?_ ?_
    · rw [hsP.lift_fst, h₂]
    · rw [hsP.lift_snd, ← h₁, Category.assoc, pullback.lift_fst]

/-- **`X_i ⟶ Y_i ×_{Y_k} X_k` is a closed immersion** for a diagram `GX` and stages
`GX.index ≤ k ≤ i`: the scheme-theoretic image `X_i` sits inside the closed subspace
`Y_i ×_{Y_k} X_k` of the base-changed model. -/
theorem _root_.AlgebraicGeometry.Space.GoodDiagram.isClosedImmersion_lift_imageSystem_map
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {pX : X ⟶ D.limitCone.pt}
    (GX : GoodDiagram B S hS hZ D pX) {k i : I} (hk : GX.index ≤ k) (hki : k ≤ i) :
    Space.IsClosedImmersion B S hS (pullback.lift
      ((stageImage GX (Over.mk (homOfLE (hk.trans hki)).op)).ι ≫ pullback.fst _ _)
      ((imageSystem GX).map (Over.homMk (homOfLE hki).op (Subsingleton.elim _ _) :
        Over.mk (homOfLE (hk.trans hki)).op ⟶ Over.mk (homOfLE hk).op))
      (by rw [imageSystem_map_ι_assoc, stageTargetMap_fst, Category.assoc]; rfl) :
        (imageSystem GX).obj (Over.mk (homOfLE (hk.trans hki)).op) ⟶
          pullback (D.system.map (homOfLE hki).op)
            ((stageImage GX (Over.mk (homOfLE hk).op)).ι ≫ pullback.fst _ _)) :=
  isClosedImmersion_lift_stage GX hk (D.system.map (homOfLE hki).op)
    (D.system.map (homOfLE (hk.trans hki)).op)
    (by rw [← Functor.map_comp]; rfl)
    (stageImage GX (Over.mk (homOfLE (hk.trans hki)).op)).ι
    (isClosedSubspace_stageImage GX _).2 _ (imageSystem_map_ι GX _)

attribute [local instance] GoodDiagram.isDirected_tail

/-- The stages `U_i ×_{Y_i} U_i` are algebraic spaces. -/
theorem isAlgebraicSpace_pairsTail (l : {j : I // Δ.index ≤ j}ᵒᵖ) :
    IsAlgebraicSpace B S hS (Δ.pairsTail.obj l) :=
  isAlgebraicSpace_pullback B S hS _ _ (imageSystem_isAlgebraicSpace Δ.objects _)
    (imageSystem_isAlgebraicSpace Δ.objects _) (D.system_isAlgebraicSpace _)

/-- The transition morphisms of `(U_i ×_{Y_i} U_i)_{i ≥ k}` are affine. -/
theorem isAffineHom_pairsTail_map {j j' : {j : I // Δ.index ≤ j}ᵒᵖ} (a : j ⟶ j') :
    Space.IsAffineHom B S hS (Δ.pairsTail.map a) :=
  isAffineHom_pullback_map_of_isClosedImmersion B S hS _ _ _ _
    (Δ.objectsToBaseTail.naturality a) (D.transition_affine _)
    (isClosedImmersion_lift_imageSystem_map Δ.objects (Δ.le_objects.trans j'.unop.2)
      (leOfHom a.unop))

/-- The limit `U ×_Y U` of `(U_i ×_{Y_i} U_i)_{i ≥ k}` is an algebraic space. -/
theorem isAlgebraicSpace_limit_pairsTail : IsAlgebraicSpace B S hS (limit Δ.pairsTail) :=
  isAlgebraicSpace_of_iso B S hS (limit.isoLimitCone ⟨Δ.pairsCone, Δ.isLimitPairsCone⟩)
    (isAlgebraicSpace_pullback B S hS _ _ G.objects.property G.objects.property
      D.limit_isAlgebraicSpace)

variable {Δ} in
/-- `U_k ×_{Y_k} U_k` is quasi-compact. -/
theorem isQuasiCompactSpace_pairsTail_initial :
    IsQuasiCompactSpace B S hS (Δ.pairsTail.obj (op Δ.tailInitial)) :=
  isQuasiCompactSpace_pullback B S hS hZ _ _
    (imageSystem_isAlgebraicSpace Δ.objects _) (D.system_isAlgebraicSpace _)
    (imageSystem_isQuasiCompactSpace Δ.objects _) (imageSystem_isQuasiCompactSpace Δ.objects _)
    (D.noetherian _).2.1

variable {Δ} in
/-- `U_k ×_{Y_k} U_k` is quasi-separated. -/
theorem isAbsolutelyQuasiSeparated_pairsTail_initial
    (hUqs : Space.IsQuasiSeparated B S hS G.objectsToBase.hom) :
    IsAbsolutelyQuasiSeparated B S hS hZ (Δ.pairsTail.obj (op Δ.tailInitial)) :=
  isAbsolutelyQuasiSeparated_pullback B S hS hZ _ _
    (imageSystem_isAlgebraicSpace Δ.objects _) (imageSystem_isAlgebraicSpace Δ.objects _)
    (D.system_isAlgebraicSpace _)
    (imageSystem_isAbsolutelyQuasiSeparated_of_isQuasiSeparated_of_algebraicLimit Δ.objects
      G.objects.property hUqs _)
    (imageSystem_isAbsolutelyQuasiSeparated_of_isQuasiSeparated_of_algebraicLimit Δ.objects
      G.objects.property hUqs _)

/-- The base change `(U ×_Y U) ×_{U_k ×_{Y_k} U_k} R_k ⟶ U ×_Y U` of
`(s_k, t_k) : R_k ⟶ U_k ×_{Y_k} U_k` to the limit, at the stage `k = Δ.index`, with target written
as `(U ×_Y U) ×_{U_k ×_{Y_k} U_k} (U_k ×_{Y_k} U_k)`. -/
noncomputable abbrev relationLimitMap :
    pullback (limit.π Δ.pairsTail (op Δ.tailInitial)) (Δ.relationTail.app (op Δ.tailInitial)) ⟶
      pullback (limit.π Δ.pairsTail (op Δ.tailInitial)) (𝟙 (Δ.pairsTail.obj (op Δ.tailInitial))) :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ Δ.relationTail.app (op Δ.tailInitial))
    (by rw [Category.assoc, Category.comp_id]; exact pullback.condition)

variable {Δ} in
/-- **The base change of `(s_k, t_k)` to the limit `U ×_Y U` is `(s, t)`**, so it is proper when
the groupoid's relation is. -/
theorem isProper_relationLimitMap (hst : Space.IsProper B S hS (relationMap G)) :
    Space.IsProper B S hS Δ.relationLimitMap := by
  let L := limit.isoLimitCone ⟨Δ.pairsCone, Δ.isLimitPairsCone⟩
  have sq := Δ.isPullback_relationMap_stage (Δ.objectsCone_π_toBase (op Δ.tailInitial)).symm
    ((Δ.source.over_base _).trans (Δ.target.over_base _).symm)
  have sq' : IsPullback (relationMap G ≫ L.inv) ((imageCone Δ.arrows).π.app
        ((Over.map (homOfLE Δ.le_arrows).op).obj (Over.mk (homOfLE (le_refl Δ.index)).op)))
      (limit.π Δ.pairsTail (op Δ.tailInitial)) (Δ.relationTail.app (op Δ.tailInitial)) :=
    IsPullback.of_iso sq (Iso.refl _) L.symm (Iso.refl _) (Iso.refl _)
      (Category.id_comp _).symm ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.comp_id _).trans (limit.isoLimitCone_inv_π
        (⟨Δ.pairsCone, Δ.isLimitPairsCone⟩ : LimitCone Δ.pairsTail) (op Δ.tailInitial)).symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  have hI : IsIso (pullback.fst (limit.π Δ.pairsTail (op Δ.tailInitial))
      (𝟙 (Δ.pairsTail.obj (op Δ.tailInitial)))) :=
    isIso_pullback_fst_id (limit.π Δ.pairsTail (op Δ.tailInitial))
  have he₁ : sq'.isoPullback.hom ≫ pullback.fst (limit.π Δ.pairsTail (op Δ.tailInitial))
        (Δ.relationTail.app (op Δ.tailInitial)) =
      relationMap G ≫ L.inv := sq'.isoPullback_hom_fst
  refine @isProper_of_arrowIso B S hS _ _ _ _ (relationMap G) Δ.relationLimitMap
    sq'.isoPullback.hom
    (L.inv ≫ @inv _ _ _ _ (pullback.fst (limit.π Δ.pairsTail (op Δ.tailInitial))
      (𝟙 (Δ.pairsTail.obj (op Δ.tailInitial)))) hI)
    ⟨⟨sq'.isoPullback.inv, sq'.isoPullback.hom_inv_id, sq'.isoPullback.inv_hom_id⟩⟩
    (@IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance (@IsIso.inv_isIso _ _ _ _ _ hI)) ?_ hst
  refine (cancel_mono (pullback.fst (limit.π Δ.pairsTail (op Δ.tailInitial))
    (𝟙 (Δ.pairsTail.obj (op Δ.tailInitial))))).1 ?_
  refine (Category.assoc _ _ _).trans ((congrArg (sq'.isoPullback.hom ≫ ·)
    (pullback.lift_fst _ _ _)).trans (he₁.trans ?_))
  exact ((Category.assoc _ _ _).trans (congrArg (relationMap G ≫ ·)
    ((Category.assoc _ _ _).trans ((congrArg (L.inv ≫ ·) (@IsIso.inv_hom_id _ _ _ _ _ hI)).trans
      (Category.comp_id _))))).symm

variable {Δ} in
/-- `(s_k, t_k) : R_k ⟶ U_k ×_{Y_k} U_k` is locally of finite type. -/
theorem isLocallyOfFiniteType_relationTail_initial :
    Space.IsLocallyOfFiniteType B S hS (Δ.relationTail.app (op Δ.tailInitial)) := by
  have hR : Space.IsLocallyOfFiniteType B S hS
      ((toStageBase Δ.arrows Δ.le_arrows).app (Over.mk (homOfLE (le_refl Δ.index)).op)) :=
    isLocallyOfFiniteType_comp B S hS (imageSystem_isAlgebraicSpace Δ.arrows _)
      (isAlgebraicSpace_stageTarget Δ.arrows _) (D.system_isAlgebraicSpace _) _ _
      (isLocallyOfFiniteType_of_isClosedImmersion B S hS _
        (isClosedSubspace_stageImage Δ.arrows _).2)
      (isLocallyOfFiniteType_stageTarget_fst Δ.arrows _)
  have hc : Δ.relationTail.app (op Δ.tailInitial) ≫
      (pullback.fst _ _ ≫ Δ.objectsToBaseTail.app (op Δ.tailInitial)) =
      (toStageBase Δ.arrows Δ.le_arrows).app (Over.mk (homOfLE (le_refl Δ.index)).op) :=
    (pullback.lift_fst_assoc _ _ _ _).trans (Δ.source.over_base _)
  rw [← hc] at hR
  exact isLocallyOfFiniteType_of_comp B S hS (imageSystem_isAlgebraicSpace Δ.arrows _)
    (Δ.isAlgebraicSpace_pairsTail _) (D.system_isAlgebraicSpace _) _ _ hR

variable {Δ} in
/-- **The fibre squares `U_i ×_{Y_i} U_i` satisfy the chapter's convention** of Section 70.2 when
the stages `Y_i` do: they embed into the base changes `(U_k ×_{Y_k} U_k) ×_{Y_k} Y_i`, the image
system of `U` embedding into its own base changes. -/
theorem siteContainsBaseChangeLimits_pairsTail
    (hconv : SiteContainsBaseChangeLimits B S hS D.system) :
    SiteContainsBaseChangeLimits B S hS Δ.pairsTail := by
  have hbase : SiteContainsBaseChangeLimits B S hS Δ.baseTail := by
    have h := hconv.comp_subtypeGe Δ.index
    rw [← tailFunctor_comp_forget_eq] at h
    exact h
  exact SiteContainsBaseChangeLimits.of_mono_lift hbase (fun f => D.transition_affine _)
    (selfPullbackToBase Δ.objectsToBaseTail)
    (fun f => mono_lift_selfPullbackToBase Δ.objectsToBaseTail
      (fun a => mono_lift_toStageBase Δ.objects Δ.le_objects ((tailFunctor Δ.index).map a)) f)

variable {Δ} in
/-- **At every late stage `(s_i, t_i) : R_i ⟶ U_i ×_{Y_i} U_i` is proper**, if
`(s, t) : R ⟶ U ×_Y U` is and the stages satisfy the chapter's convention: Stacks 08K1 under the
convention
(`Space.MorphismDescentSituation.exists_isProper_mapAt_of_siteContainsBaseChangeLimits`), for the
system `U_i ×_{Y_i} U_i` (`siteContainsBaseChangeLimits_pairsTail`), makes the base change of
`(s_k, t_k)` to some `U_j ×_{Y_j} U_j` proper, hence also its base changes to all later stages,
and `R_i` is a closed subspace of that base change. -/
theorem eventually_isProper_relationTail
    (hUqs : Space.IsQuasiSeparated B S hS G.objectsToBase.hom)
    (hRqs : Space.IsQuasiSeparated B S hS G.arrowsToBase.hom)
    (hst : Space.IsProper B S hS (relationMap G))
    (hconv : SiteContainsBaseChangeLimits B S hS D.system) :
    ∃ j : {j : I // Δ.index ≤ j}, ∀ k : {j : I // Δ.index ≤ j}, j ≤ k →
      Space.IsProper B S hS (Δ.relationTail.app (op k)) := by
  have hRalg := imageSystem_isAlgebraicSpace Δ.arrows
    (Over.mk (homOfLE (Δ.le_arrows.trans (le_refl Δ.index))).op)
  have : Nonempty {j : I // Δ.index ≤ j} := ⟨Δ.tailInitial⟩
  let M : MorphismDescentSituation B S hS hZ {j : I // Δ.index ≤ j} :=
    { base := Δ.pairsTail
      base_isAlgebraicSpace := fun j => Δ.isAlgebraicSpace_pairsTail (op j)
      transition_affine := fun a => Δ.isAffineHom_pairsTail_map a
      limit_isAlgebraicSpace := Δ.isAlgebraicSpace_limit_pairsTail
      initial := Δ.tailInitial
      source₀ := Δ.arrowsTail.obj (op Δ.tailInitial)
      target₀ := Δ.pairsTail.obj (op Δ.tailInitial)
      sourceToBase := Δ.relationTail.app (op Δ.tailInitial)
      targetToBase := 𝟙 _
      map₀ := Δ.relationTail.app (op Δ.tailInitial)
      map₀_over := Category.comp_id _
      source₀_isAlgebraicSpace := hRalg
      target₀_isAlgebraicSpace := Δ.isAlgebraicSpace_pairsTail _
      base₀_quasiCompact := isQuasiCompactSpace_pairsTail_initial
      base₀_quasiSeparated := isAbsolutelyQuasiSeparated_pairsTail_initial hUqs
      source₀_quasiCompact := imageSystem_isQuasiCompactSpace Δ.arrows _
      source₀_quasiSeparated :=
        imageSystem_isAbsolutelyQuasiSeparated_of_isQuasiSeparated_of_algebraicLimit Δ.arrows
          G.arrows.property hRqs _
      target₀_quasiCompact := isQuasiCompactSpace_pairsTail_initial
      target₀_quasiSeparated := isAbsolutelyQuasiSeparated_pairsTail_initial hUqs }
  obtain ⟨j, hj, hP⟩ := M.exists_isProper_mapAt_of_siteContainsBaseChangeLimits
    (siteContainsBaseChangeLimits_pairsTail hconv) (isProper_relationLimitMap hst)
    isLocallyOfFiniteType_relationTail_initial
  replace hj : Δ.tailInitial ≤ j := hj
  change Space.IsProper B S hS (pullback.lift
    (pullback.fst (Δ.pairsTail.map (homOfLE hj).op) (Δ.relationTail.app (op Δ.tailInitial)))
    (pullback.snd (Δ.pairsTail.map (homOfLE hj).op) (Δ.relationTail.app (op Δ.tailInitial)) ≫
      Δ.relationTail.app (op Δ.tailInitial)) _ :
    pullback (Δ.pairsTail.map (homOfLE hj).op) (Δ.relationTail.app (op Δ.tailInitial)) ⟶
      pullback (Δ.pairsTail.map (homOfLE hj).op) (𝟙 (Δ.pairsTail.obj (op Δ.tailInitial)))) at hP
  refine ⟨j, fun k hjk => ?_⟩
  have hk : Δ.tailInitial ≤ k := hj.trans hjk
  have hWalg : ∀ l, IsAlgebraicSpace B S hS (Δ.pairsTail.obj l) := Δ.isAlgebraicSpace_pairsTail
  have hXalg : ∀ (l : {j : I // Δ.index ≤ j}) (hl : Δ.tailInitial ≤ l),
      IsAlgebraicSpace B S hS (pullback (Δ.pairsTail.map (homOfLE hl).op)
        (Δ.relationTail.app (op Δ.tailInitial))) := fun l _ =>
    isAlgebraicSpace_pullback B S hS _ _ (hWalg _) hRalg (hWalg _)
  -- the base change of `(s₀, t₀)` to the stage `j` is proper
  have hIj : IsIso (pullback.fst (Δ.pairsTail.map (homOfLE hj).op)
      (𝟙 (Δ.pairsTail.obj (op Δ.tailInitial)))) :=
    isIso_pullback_fst_id (Δ.pairsTail.map (homOfLE hj).op)
  have hfj : Space.IsProper B S hS (pullback.fst (Δ.pairsTail.map (homOfLE hj).op)
      (Δ.relationTail.app (op Δ.tailInitial))) := by
    have h := isProper_comp B S hS (hXalg j hj)
      (isAlgebraicSpace_pullback B S hS _ _ (hWalg _) (hWalg _) (hWalg _)) (hWalg _) _ _ hP
      (@isProper_of_isIso B S hS _ _ _ hIj)
    convert h using 2
    exact (pullback.lift_fst _ _ _).symm
  -- hence so is its base change to the stage `k`
  have hmap : Δ.pairsTail.map (homOfLE hjk).op ≫ Δ.pairsTail.map (homOfLE hj).op =
      Δ.pairsTail.map (homOfLE hk).op := by
    rw [← Functor.map_comp]
    rfl
  have sqk : IsPullback
      (pullback.lift (pullback.fst _ _ ≫ Δ.pairsTail.map (homOfLE hjk).op) (pullback.snd _ _)
        (by rw [Category.assoc, hmap, pullback.condition]) :
          pullback (Δ.pairsTail.map (homOfLE hk).op) (Δ.relationTail.app (op Δ.tailInitial)) ⟶
            pullback (Δ.pairsTail.map (homOfLE hj).op) (Δ.relationTail.app (op Δ.tailInitial)))
      (pullback.fst (Δ.pairsTail.map (homOfLE hk).op) (Δ.relationTail.app (op Δ.tailInitial)))
      (pullback.fst (Δ.pairsTail.map (homOfLE hj).op) (Δ.relationTail.app (op Δ.tailInitial)))
      (Δ.pairsTail.map (homOfLE hjk).op) := by
    refine IsPullback.of_right (h₁₂ := pullback.snd _ _)
      (h₂₂ := Δ.pairsTail.map (homOfLE hj).op) ?_
      (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback _ _).flip
    rw [pullback.lift_snd, hmap]
    exact (IsPullback.of_hasPullback _ _).flip
  have hfk : Space.IsProper B S hS (pullback.fst (Δ.pairsTail.map (homOfLE hk).op)
      (Δ.relationTail.app (op Δ.tailInitial))) :=
    isProper_of_isPullback B S hS (hXalg k hk)
      (hXalg j hj) (hWalg _) (hWalg _) sqk hfj
  -- `R_k` is a closed subspace of that base change
  let a : op k ⟶ op Δ.tailInitial := (homOfLE (show Δ.tailInitial ≤ k from k.2)).op
  let bU := Δ.objectsToBaseTail.app (op k)
  let bU₀ := Δ.objectsToBaseTail.app (op Δ.tailInitial)
  let c₀ := Δ.relationTail.app (op Δ.tailInitial)
  let bR₀ := (stageImage Δ.arrows (Over.mk (homOfLE Δ.le_arrows).op)).ι ≫ pullback.fst _ _
  have hc₀ : c₀ ≫ pullback.fst bU₀ bU₀ ≫ bU₀ = bR₀ :=
    (pullback.lift_fst_assoc _ _ _ _).trans (Δ.source.over_base _)
  let lam : Δ.arrowsTail.obj (op k) ⟶ pullback (Δ.pairsTail.map a) c₀ :=
    pullback.lift (Δ.relationTail.app (op k)) (Δ.arrowsTail.map a)
      (Δ.relationTail.naturality a).symm
  have hlam : lam ≫ pullback.fst _ _ = Δ.relationTail.app (op k) := pullback.lift_fst _ _ _
  have hκU := isClosedImmersion_lift_imageSystem_map Δ.objects Δ.le_objects k.2
  have hκR := isClosedImmersion_lift_imageSystem_map Δ.arrows Δ.le_arrows k.2
  have hν := mono_lift_pullback_map bU bU₀ (Δ.objectsTail.map a) (Δ.baseTail.map a)
    (Δ.objectsToBaseTail.naturality a) (mono_of_isClosedImmersion B S hS _ hκU)
  have hμ := mono_lift_pullback_fst bU bU₀ (Δ.objectsTail.map a) (Δ.baseTail.map a)
    (Δ.objectsToBaseTail.naturality a) c₀ bR₀ hc₀ hν
  have hlamc : Space.IsClosedImmersion B S hS lam := by
    refine @isClosedImmersion_of_comp_mono B S hS _ _ _ lam _ hμ ?_
    convert hκR using 1
    all_goals try rfl
    apply heq_of_eq
    apply pullback.hom_ext
    · erw [Category.assoc, pullback.lift_fst, pullback.lift_fst, ← Category.assoc, hlam]
      exact (pullback.lift_fst_assoc _ _ _ _).trans (Δ.source.over_base _)
    · erw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
      exact (pullback.lift_snd _ _ _).symm
  rw [← hlam]
  exact isProper_comp B S hS (imageSystem_isAlgebraicSpace Δ.arrows _)
    (hXalg k hk) (hWalg _) _ _
    (isProper_of_isClosedImmersion B S hS (imageSystem_isAlgebraicSpace Δ.arrows _)
      (hXalg k hk) _ hlamc) hfk

variable {Δ} in
/-- **The relation of a separated groupoid is proper at every late stage of its descent.** If
`(s, t) : R ⟶ U ×_Y U` is proper, then so is `(s_i, t_i) : R_i ⟶ U_i ×_{Y_i} U_i` for the stage
groupoid `(U_i, R_i, s_i, t_i, c_i)` at every sufficiently large `i`.

This is the second paragraph of the proof of Stacks 0CQ2, for stages satisfying the chapter's
convention of Section 70.2 (`hconv`), under which Stacks 08K1 holds. The source
routes it through Stacks 0CPE and 0CPF for the system `V_i` of `U ×_Y U`; here the system is
`U_i ×_{Y_i} U_i` itself, whose limit is `U ×_Y U`, and `R_i` is a closed subspace of the base
change of `R_k` to it. -/
theorem eventually_isProper_relationMap_stageGroupoid
    (hUqs : Space.IsQuasiSeparated B S hS G.objectsToBase.hom)
    (hRqs : Space.IsQuasiSeparated B S hS G.arrowsToBase.hom)
    (hst : Space.IsProper B S hS (relationMap G))
    (hconv : SiteContainsBaseChangeLimits B S hS D.system) :
    ∃ (i₃ : I) (hi₃ : Δ.index ≤ i₃), ∀ (i : I) (h : i₃ ≤ i),
      Space.IsProper B S hS (relationMap (Δ.stageGroupoid i (hi₃.trans h))) := by
  obtain ⟨j, hj⟩ := eventually_isProper_relationTail (Δ := Δ) hUqs hRqs hst hconv
  exact ⟨j.1, j.2, fun i h => hj ⟨i, j.2.trans h⟩ h⟩

end LimitDescent

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
