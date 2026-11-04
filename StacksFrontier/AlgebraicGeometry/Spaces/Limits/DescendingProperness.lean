module

public import StacksFrontier.AlgebraicGeometry.ChowFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.OneAffineOpenStep
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.SeparatedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.SiteObjectBase
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenLiftOverHenselianPair
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineChartSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartSystemMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ProperCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Properness of a morphism of algebraic spaces descends to a stage of a limit of bases

Let `B = lim B_i` be a directed limit of algebraic spaces over a scheme `S` with affine
transition morphisms, let `f₀ : X₀ ⟶ Y₀` be a morphism of quasi-compact quasi-separated
algebraic spaces over `B₀`, and let `f_i : X_i ⟶ Y_i` and `f : X ⟶ Y` be its base changes to a
stage `B_i` and to the limit `B`. This is the situation of Stacks 084W, encoded by
`AlgebraicGeometry.Space.MorphismDescentSystem`. If `f₀` is locally of finite type and `f` is
proper, then `f_i` is proper for some `i ≥ 0`.

The proof is the one of the source. Choose an affine étale surjective chart `V₀ ⟶ Y₀`; its base
changes `V_i ⟶ Y_i` are affine étale surjective charts, the `V_i` form a directed system of affine
schemes with limit the base change `V ⟶ Y`, and by Stacks 083R it suffices to make the base
change of `f_i` to `V_i` proper. Separatedness descends to a stage `i₁` by Stacks 0851. Over the
affine scheme `V_{i₁}` the base change of `f_{i₁}` is separated and of finite type, so Chow's
lemma, Stacks 089J, gives a scheme `X'` which is H-quasi-projective over `V_{i₁}` together with a
proper surjective morphism from `X'` to that base change. The base change of `X'` to the limit
`V` is proper over `V`, being proper over the base change of `f`; so by the scheme case,
Stacks 081F, the base change `X'_i ⟶ V_i` is proper for some `i ≥ i₁`. Since `X'_i` surjects onto
the base change of `f_i` to `V_i`, which is separated and of finite type, Stacks 08AJ makes that
base change proper.

## Main results

* `AlgebraicGeometry.Space.MorphismDescentSystem.exists_isProper_mapAt`: **Stacks 08K1**.
* `AlgebraicGeometry.Space.exists_chowSchemeCover_of_affine`: Chow's lemma over an affine
  object of the site, with the cover lying over it, for an algebraic space separated and of
  finite type over that object.

## Implementation notes

The source first replaces `Y₀` by an affine chart, then `0` by a stage at which `f` becomes
separated. Neither replacement is carried out on the descent system itself: the chart enters
only through the base changes of `f_i` to the charts `V_i`, which is the form in which Stacks
083R reads properness, and the stage `i₁` enters only as the stage at which Chow's lemma is
applied. The charts `V_i` and their limit are an
`AlgebraicGeometry.Space.AffineChartSystem` together with its
`AlgebraicGeometry.Space.AffineChartSystem.LimitBridge`, through which the descent statement
becomes one about a cofiltered limit of affine schemes, and the scheme case is
`AlgebraicGeometry.exists_isProper_baseChange_of_isLimit_of_isOneAffineOpenStep` with its step
discharged by `AlgebraicGeometry.Scheme.FiniteTypeApproximation.isOneAffineOpenStep`.

## References

* [Stacks Project, Tag 08K1](https://stacks.math.columbia.edu/tag/08K1)
* [Stacks Project, Tag 084W](https://stacks.math.columbia.edu/tag/084W)
* [Stacks Project, Tag 083R](https://stacks.math.columbia.edu/tag/083R)
* [Stacks Project, Tag 0851](https://stacks.math.columbia.edu/tag/0851)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
* [Stacks Project, Tag 081F](https://stacks.math.columbia.edu/tag/081F)
* [Stacks Project, Tag 08AJ](https://stacks.math.columbia.edu/tag/08AJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-! ### Pasting statements for base changes -/

namespace CategoryTheory

variable {A : Type*} [Category* A] [HasPullbacks A]

omit [HasPullbacks A] in
/-- Given a cartesian square `a, q, q₁, s` and a morphism `p` into its upper right corner, every
cartesian square on `p ≫ q₁` and `s` factors through it by a cartesian square on `p` and `a`. -/
theorem IsPullback.isPullback_lift_of_comp {Q Q₁ T T₁ V W : A} {a : Q ⟶ Q₁} {q : Q ⟶ T}
    {q₁ : Q₁ ⟶ T₁} {s : T ⟶ T₁} (hA : IsPullback a q q₁ s) (p : V ⟶ Q₁) {w₁ : W ⟶ V}
    {w₂ : W ⟶ T} (hW : IsPullback w₁ w₂ (p ≫ q₁) s) :
    IsPullback w₁ (hA.lift (w₁ ≫ p) w₂ (by rw [Category.assoc, hW.w])) p a :=
  IsPullback.of_bot (by rwa [hA.lift_snd]) (hA.lift_fst _ _ _).symm hA

/-- The morphism `B' ×_{B₀} X₀ ⟶ B' ×_{B₀} Y₀` induced by a morphism `f₀ : X₀ ⟶ Y₀` over `B₀` is
a base change of `f₀`. -/
theorem Limits.isPullback_pullback_lift_snd {B₀ B' X₀ Y₀ : A} (b : B' ⟶ B₀) {x : X₀ ⟶ B₀}
    {y : Y₀ ⟶ B₀} {f₀ : X₀ ⟶ Y₀} (h : pullback.fst b x ≫ b = (pullback.snd b x ≫ f₀) ≫ y)
    (hf₀ : f₀ ≫ y = x) :
    IsPullback (pullback.snd b x) (pullback.lift (pullback.fst b x) (pullback.snd b x ≫ f₀) h)
      f₀ (pullback.snd b y) := by
  refine IsPullback.of_bot (h₂₁ := pullback.snd b y) (v₂₁ := pullback.fst b y) (v₂₂ := y)
    (h₃₁ := b) ?_ (pullback.lift_snd _ _ _).symm (IsPullback.of_hasPullback b y).flip
  rw [pullback.lift_fst, hf₀]
  exact (IsPullback.of_hasPullback b x).flip

/-- The projections of the base change along `b' = c ≫ b` are compatible with `c` and `b`. -/
private theorem fst_comp_comp_eq_snd_comp {B₀ B' B'' X₀ : A} (b : B' ⟶ B₀) (b' : B'' ⟶ B₀)
    (c : B'' ⟶ B') (hc : c ≫ b = b') (x : X₀ ⟶ B₀) :
    (pullback.fst b' x ≫ c) ≫ b = pullback.snd b' x ≫ x := by
  rw [Category.assoc, hc, pullback.condition]

/-- Let `c : B'' ⟶ B'` be a morphism over `B₀`. The morphisms of base changes of `f₀ : X₀ ⟶ Y₀`
to `B''` and to `B'` form a cartesian square with the morphisms induced by `c`. -/
theorem Limits.isPullback_pullback_lift_transition {B₀ B' B'' X₀ Y₀ : A} (b : B' ⟶ B₀)
    (b' : B'' ⟶ B₀) (c : B'' ⟶ B') (hc : c ≫ b = b') {x : X₀ ⟶ B₀} {y : Y₀ ⟶ B₀}
    {f₀ : X₀ ⟶ Y₀} (hf₀ : f₀ ≫ y = x)
    (h : pullback.fst b x ≫ b = (pullback.snd b x ≫ f₀) ≫ y)
    (h' : pullback.fst b' x ≫ b' = (pullback.snd b' x ≫ f₀) ≫ y)
    (hX : (pullback.fst b' x ≫ c) ≫ b = pullback.snd b' x ≫ x)
    (hY : (pullback.fst b' y ≫ c) ≫ b = pullback.snd b' y ≫ y) :
    IsPullback (pullback.lift (pullback.fst b' x ≫ c) (pullback.snd b' x) hX)
      (pullback.lift (pullback.fst b' x) (pullback.snd b' x ≫ f₀) h')
      (pullback.lift (pullback.fst b x) (pullback.snd b x ≫ f₀) h)
      (pullback.lift (pullback.fst b' y ≫ c) (pullback.snd b' y) hY) := by
  refine IsPullback.of_right ?_ ?_ (isPullback_pullback_lift_snd b h hf₀)
  · rw [pullback.lift_snd, pullback.lift_snd]
    exact isPullback_pullback_lift_snd b' h' hf₀
  · apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
        pullback.lift_snd_assoc]

/-- Let `st, ba` exhibit `T` as the fibre product of `bm : B' ⟶ B₀` and `v ≫ y`. Then the
induced morphism `T ⟶ B' ×_{B₀} Y₀` exhibits `T` as the base change of `v` along
`B' ×_{B₀} Y₀ ⟶ Y₀`. -/
theorem IsPullback.isPullback_pullback_lift {B₀ B' Y₀ W T : A} {st : T ⟶ B'} {ba : T ⟶ W}
    {bm : B' ⟶ B₀} {v : W ⟶ Y₀} {y : Y₀ ⟶ B₀} (hT : IsPullback st ba bm (v ≫ y))
    (h : st ≫ bm = (ba ≫ v) ≫ y) :
    IsPullback (pullback.lift st (ba ≫ v) h) ba (pullback.snd bm y) v := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback bm y)
  rw [pullback.lift_fst]
  exact hT

/-- **Charts of two base changes of a morphism.** Let `f₀ : X₀ ⟶ Y₀` be a morphism over `B₀`, let
`c : B'' ⟶ B'` be a morphism over `B₀`, and let `v : V₀ ⟶ Y₀`. Points `W ⟶ B' ×_{B₀} Y₀` and
`W' ⟶ B'' ×_{B₀} Y₀` given by their projections to the bases and to `V₀`, compatible along a
morphism `s : W' ⟶ W`, give base changes of the two base changes of `f₀`; the one over `W'` is a
base change of the one over `W` along `s`. -/
@[ega "I 3.3.9" "partial"]
theorem Limits.exists_isPullback_chart_transition {B₀ B' B'' X₀ Y₀ V₀ W W' : A}
    (b : B' ⟶ B₀) (b' : B'' ⟶ B₀) (c : B'' ⟶ B') (hc : c ≫ b = b') {x : X₀ ⟶ B₀}
    {y : Y₀ ⟶ B₀} {f₀ : X₀ ⟶ Y₀} (hf₀ : f₀ ≫ y = x) (v : V₀ ⟶ Y₀) {st : W ⟶ B'}
    {ba : W ⟶ V₀} (hw : st ≫ b = (ba ≫ v) ≫ y) {st' : W' ⟶ B''} {ba' : W' ⟶ V₀}
    (hw' : st' ≫ b' = (ba' ≫ v) ≫ y) (s : W' ⟶ W) (hs₁ : s ≫ st = st' ≫ c)
    (hs₂ : s ≫ ba = ba')
    (h : pullback.fst b x ≫ b = (pullback.snd b x ≫ f₀) ≫ y)
    (h' : pullback.fst b' x ≫ b' = (pullback.snd b' x ≫ f₀) ≫ y) :
    ∃ a, IsPullback a
      (pullback.fst (pullback.lift st' (ba' ≫ v) hw')
        (pullback.lift (pullback.fst b' x) (pullback.snd b' x ≫ f₀) h'))
      (pullback.fst (pullback.lift st (ba ≫ v) hw)
        (pullback.lift (pullback.fst b x) (pullback.snd b x ≫ f₀) h)) s := by
  set m := pullback.lift (pullback.fst b x) (pullback.snd b x ≫ f₀) h
  set m' := pullback.lift (pullback.fst b' x) (pullback.snd b' x ≫ f₀) h'
  set g := pullback.lift st (ba ≫ v) hw
  set g' := pullback.lift st' (ba' ≫ v) hw'
  have hX := fst_comp_comp_eq_snd_comp b b' c hc x
  have hY := fst_comp_comp_eq_snd_comp b b' c hc y
  have T := isPullback_pullback_lift_transition b b' c hc hf₀ h h' hX hY
  have outer := (IsPullback.of_hasPullback g' m').flip.paste_horiz T
  have hcompat : g' ≫ pullback.lift (pullback.fst b' y ≫ c) (pullback.snd b' y) hY = s ≫ g := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, g', g, hs₁]
    · simp only [Category.assoc, pullback.lift_snd, g', g, ← hs₂]
  have hw₀ : (pullback.fst g' m' ≫ s) ≫ g =
      (pullback.snd g' m' ≫ pullback.lift (pullback.fst b' x ≫ c) (pullback.snd b' x) hX) ≫ m := by
    rw [Category.assoc, ← hcompat, outer.w]
  refine ⟨pullback.lift (pullback.fst g' m' ≫ s) (pullback.snd g' m' ≫
    pullback.lift (pullback.fst b' x ≫ c) (pullback.snd b' x) hX) hw₀, ?_⟩
  refine IsPullback.of_right (h₁₂ := pullback.snd g m) (v₁₂ := pullback.fst g m) (h₂₂ := g)
    ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback g m).flip
  rw [pullback.lift_snd, ← hcompat]
  exact outer

end CategoryTheory

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Base change of properties of morphisms of algebraic spaces along cartesian squares -/

section BaseChange

variable {X Y X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- A base change of a separated morphism of algebraic spaces is separated (Stacks 03KL), for an
arbitrary cartesian square of presheaves. -/
theorem isSeparated_baseChange_of_isPullback (sq : IsPullback g' f' f g)
    (hf : IsSeparated B S hS f) : IsSeparated B S hS f' :=
  isSeparated_of_arrowIso B S hS (pullback.snd f g) f' sq.isoPullback.inv (𝟙 _)
    (by simp) (isSeparated_pullback B S hS f g hf)

/-- A base change of a morphism of algebraic spaces locally of finite type is locally of finite
type (Stacks 03XH), for an arbitrary cartesian square of algebraic spaces. -/
theorem isLocallyOfFiniteType_baseChange_of_isPullback (hX' : IsAlgebraicSpace B S hS X')
    (hX : IsAlgebraicSpace B S hS X) (hY' : IsAlgebraicSpace B S hS Y')
    (hY : IsAlgebraicSpace B S hS Y) (sq : IsPullback g' f' f g)
    (hf : IsLocallyOfFiniteType B S hS f) : IsLocallyOfFiniteType B S hS f' :=
  (isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback
    (isPullback_homMk B S hS hX hY' hY hX' sq) hf

/-- A base change of a quasi-compact morphism of algebraic spaces is quasi-compact
(Stacks 03HF), for an arbitrary cartesian square of algebraic spaces. -/
theorem isQuasiCompact_baseChange_of_isPullback (hX' : IsAlgebraicSpace B S hS X')
    (hX : IsAlgebraicSpace B S hS X) (hY' : IsAlgebraicSpace B S hS Y')
    (hY : IsAlgebraicSpace B S hS Y) (sq : IsPullback g' f' f g)
    (hf : IsQuasiCompact B S hS f) : IsQuasiCompact B S hS f' :=
  (isQuasiCompact_isStableUnderBaseChange B S hS).of_isPullback
    (isPullback_homMk B S hS hX hY' hY hX' sq) hf

/-- A base change of a surjective morphism of algebraic spaces is surjective (Stacks 03MH), for
an arbitrary cartesian square of algebraic spaces. -/
theorem isSurjective_baseChange_of_isPullback (hX' : IsAlgebraicSpace B S hS X')
    (hX : IsAlgebraicSpace B S hS X) (hY' : IsAlgebraicSpace B S hS Y')
    (hY : IsAlgebraicSpace B S hS Y) (sq : IsPullback g' f' f g)
    (hf : IsSurjective B S hS f) : IsSurjective B S hS f' :=
  isSurjective_of_isPullback B S hS (isPullback_homMk B S hS hX hY' hY hX' sq) hf

/-- A base change of a morphism of algebraic spaces of finite type is of finite type, for an
arbitrary cartesian square of algebraic spaces. -/
private theorem isFiniteType_baseChange_of_isPullback (hX' : IsAlgebraicSpace B S hS X')
    (hX : IsAlgebraicSpace B S hS X) (hY' : IsAlgebraicSpace B S hS Y')
    (hY : IsAlgebraicSpace B S hS Y) (sq : IsPullback g' f' f g)
    (hf : IsFiniteType B S hS f) : IsFiniteType B S hS f' :=
  ⟨isLocallyOfFiniteType_baseChange_of_isPullback hX' hX hY' hY sq hf.1,
    isQuasiCompact_baseChange_of_isPullback hX' hX hY' hY sq hf.2⟩

end BaseChange

/-! ### Properness and surjectivity through a factorization of a base change -/

section Factorization

variable {P Q₁ W₁ Q W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P)
  (hQ₁ : IsAlgebraicSpace B S hS Q₁) (hW₁ : IsAlgebraicSpace B S hS W₁)
  (hQ : IsAlgebraicSpace B S hS Q) (hW : IsAlgebraicSpace B S hS W)
  (p : P ⟶ Q₁) (q₁ : Q₁ ⟶ W₁) (t : W ⟶ W₁) {a : Q ⟶ Q₁} {q : Q ⟶ W}
  (sq : IsPullback a q q₁ t)

include hP hQ₁ hW₁ hQ hW sq in
/-- If `q` is a base change of `q₁` along `t`, then the base change of `p ≫ q₁` along `t` factors
as a base change of `p` followed by `q`. So it is proper as soon as `p` and `q` are. -/
theorem isProper_pullback_snd_comp_of_isPullback (hp : IsProper B S hS p)
    (hq : IsProper B S hS q) {k : P ⟶ W₁} (hk : p ≫ q₁ = k) :
    IsProper B S hS (pullback.snd k t) := by
  subst hk
  have hpb := sq.isPullback_lift_of_comp p (IsPullback.of_hasPullback (p ≫ q₁) t)
  have hPt : IsAlgebraicSpace B S hS (pullback (p ≫ q₁) t) :=
    isAlgebraicSpace_pullback B S hS _ _ hP hW hW₁
  have hl := isProper_of_isPullback B S hS hPt hP hQ hQ₁ hpb hp
  have h := isProper_comp B S hS hPt hQ hW _ q hl hq
  rwa [sq.lift_snd] at h

include hP hQ₁ hW₁ hQ hW sq in
/-- If `q` is a base change of `q₁` along `t` and `p` is surjective, the base change of `p ≫ q₁`
along `t` maps surjectively onto the source of `q`, compatibly with the projections to `W`. -/
theorem exists_isSurjective_comp_eq_pullback_snd (hp : IsSurjective B S hS p) {k : P ⟶ W₁}
    (hk : p ≫ q₁ = k) :
    ∃ l : pullback k t ⟶ Q, IsSurjective B S hS l ∧ l ≫ q = pullback.snd k t := by
  subst hk
  have hpb := sq.isPullback_lift_of_comp p (IsPullback.of_hasPullback (p ≫ q₁) t)
  have hPt : IsAlgebraicSpace B S hS (pullback (p ≫ q₁) t) :=
    isAlgebraicSpace_pullback B S hS _ _ hP hW hW₁
  exact ⟨_, isSurjective_baseChange_of_isPullback hPt hP hQ hQ₁ hpb hp, sq.lift_snd _ _ _⟩

end Factorization

/-- Properness of the base change of a morphism of the site along another, read on the represented
presheaves, on the morphism of schemes, and in the category of schemes over the target. -/
theorem isProper_pullback_snd_yoneda_iff {X' W T : BigFppfOver B S hS} (ψ : X' ⟶ W)
    (t : T ⟶ W) :
    IsProper B S hS (pullback.snd (yoneda.map ψ) (yoneda.map t)) ↔
      _root_.AlgebraicGeometry.IsProper ((Over.pullback ((BigFppfOver.toScheme B S hS).map t)).map
        (Over.homMk ((BigFppfOver.toScheme B S hS).map ψ) :
          Over.mk ((BigFppfOver.toScheme B S hS).map ψ) ⟶
            Over.mk (𝟙 ((BigFppfOver.toScheme B S hS).obj W)))).left := by
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) := by
    dsimp [BigFppfOver.toScheme]
    infer_instance
  rw [prop_overPullback_map_left_iff_pullback_snd (@_root_.AlgebraicGeometry.IsProper) _ _,
    prop_snd_iff_of_isPullback (@_root_.AlgebraicGeometry.IsProper) (IsPullback.of_hasPullback _ _)
      ((IsPullback.of_hasPullback ψ t).map (BigFppfOver.toScheme B S hS)),
    ← isProper_yoneda_map_iff, ← ((IsPullback.of_hasPullback ψ t).map yoneda).isoPullback_hom_snd,
    isProper_isIso_comp_iff]

/-! ### Chow's lemma over an affine object of the site -/

/-- **Chow's lemma over an affine object of the site** (Stacks 089J). Let `U` be an object of
the big fppf site of `S` whose underlying scheme is affine, and let `q : Q ⟶ h_U` be a separated
morphism of finite type from an algebraic space. Then there are an object `X'` of the site, a
morphism `ψ : X' ⟶ U` which is separated and of finite type on underlying schemes, and a proper
surjective morphism `p : h_{X'} ⟶ Q` with `p ≫ q = h_ψ`.

The object `U` is replaced by the isomorphic object of the site whose underlying scheme is
literally `Spec Γ(U, 𝒪)`, and `AlgebraicGeometry.Space.exists_chowSchemeCover_over_base` is
applied over that object. -/
theorem exists_chowSchemeCover_of_affine (U : BigFppfOver B S hS)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hQ : IsAlgebraicSpace B S hS Q)
    (q : Q ⟶ yoneda.obj U) (hsep : IsSeparated B S hS q) (hft : IsFiniteType B S hS q) :
    ∃ (X' : BigFppfOver B S hS) (ψ : X' ⟶ U) (p : yoneda.obj X' ⟶ Q),
      IsProper B S hS p ∧ IsSurjective B S hS p ∧ p ≫ q = yoneda.map ψ ∧
        LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map ψ) ∧
        QuasiCompact ((BigFppfOver.toScheme B S hS).map ψ) ∧
        _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map ψ) := by
  classical
  let : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
  let A : CommRingCat.{u} := Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
  let eT : Spec A ≅ (BigFppfOver.toScheme B S hS).obj U :=
    ((BigFppfOver.toScheme B S hS).obj U).isoSpec.symm
  have hA : B.Contains (Spec A) := (Scheme.size_congr eT).trans_lt U.left.property
  let εiso : B.obj hA ≅ U.left :=
    { hom := B.inclusion.preimage eT.hom
      inv := B.inclusion.preimage eT.inv
      hom_inv_id := B.inclusion.map_injective (by
        rw [CategoryTheory.Functor.map_comp, B.inclusion.map_preimage,
          B.inclusion.map_preimage, eT.hom_inv_id, CategoryTheory.Functor.map_id]
        rfl)
      inv_hom_id := B.inclusion.map_injective (by
        rw [CategoryTheory.Functor.map_comp, B.inclusion.map_preimage,
          B.inclusion.map_preimage, eT.inv_hom_id, CategoryTheory.Functor.map_id]
        rfl) }
  let g₀ : B.obj hA ⟶ B.obj hS := εiso.hom ≫ U.hom
  let θ : (Over.mk g₀ : BigFppfOver B S hS) ≅ U := Over.isoMk εiso rfl
  let q' : Q ⟶ yoneda.obj (Over.mk g₀ : BigFppfOver B S hS) := q ≫ yoneda.map θ.inv
  have hsep' : IsSeparated B S hS q' :=
    isSeparated_of_arrowIso B S hS q q' (𝟙 _) (yoneda.map θ.inv) (by simp [q']) hsep
  have hft' : IsFiniteType B S hS q' :=
    isFiniteType_of_arrowIso B S hS q q' (𝟙 _) (yoneda.map θ.inv) (by simp [q']) hft
  obtain ⟨X', ψ', p, hp, hps, hpq, hhqp⟩ :=
    exists_chowSchemeCover_over_base B S hS A hA g₀ hQ q' hsep' hft'
  have := hhqp.locallyOfFiniteType
  have := hhqp.quasiCompact
  have := hhqp.isSeparated
  refine ⟨X', ψ' ≫ θ.hom, p, hp, hps, ?_, ?_, ?_, ?_⟩
  · rw [yoneda.map_comp, ← hpq]
    simp [q', ← yoneda.map_comp]
  all_goals rw [Functor.map_comp]; infer_instance

/-! ### Stacks 08K1 -/

namespace MorphismDescentSystem

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]

attribute [local instance] MorphismProperty.relative_isStableUnderBaseChange in
/-- **Properness descends to a stage of a limit of bases** (Stacks 08K1). In the situation of
Stacks 084W, if the base change `f` of `f₀` to the limit `B` is proper and `f₀` is locally of
finite type, then the base change `f_i` of `f₀` to some stage `B_i` is proper. -/
theorem exists_isProper_mapAt (D : MorphismDescentSystem B S hS hZ I)
    (proper : IsProper B S hS D.mapLimit) (ft : IsLocallyOfFiniteType B S hS D.map₀) :
    ∃ (i : I) (hi : D.initial ≤ i), IsProper B S hS (D.mapAt i hi) := by
  classical
  have : Nonempty I := ⟨D.initial⟩
  have : IsDirectedOrder I := inferInstance
  have : IsFiltered I := inferInstance
  have : IsCofiltered Iᵒᵖ := inferInstance
  have : IsCofiltered (Over (op D.initial)) := inferInstance
  set x := D.sourceToBase
  set y := D.targetToBase
  have hf₀ : D.map₀ ≫ y = x := D.map₀_over
  have hX₀ := D.source₀_isAlgebraicSpace
  have hY₀ := D.target₀_isAlgebraicSpace
  -- Stacks 0851: separatedness at a stage `i₁`.
  obtain ⟨i₁, hi₁, hsep₁⟩ := D.exists_isSeparated_mapAt_of_isSeparated_mapLimit proper.1
  -- `f₀` is of finite type.
  have hft₀ : IsFiniteType B S hS D.map₀ :=
    ⟨ft, isQuasiCompact_of_isQuasiCompactSpace B S hS hZ hY₀ D.target₀_quasiSeparated
      D.source₀_quasiCompact D.map₀⟩
  -- an affine étale surjective chart `V₀ ⟶ Y₀`, and the chart system of the stages
  obtain ⟨V₀, v, hV₀, hvsurj, hvet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS D.target₀ hY₀).mp
      D.target₀_quasiCompact
  let U₀ : BigAffineFppf B S hS := ⟨V₀, hV₀⟩
  let C := affineChartSystem B S hS (op D.initial) D.base U₀ (v ≫ y)
    (fun {_ _} g ↦ D.transition_affine g)
  let L : C.LimitBridge := by
    refine AffineChartSystem.limitBridge C ?_ fun _ _ ↦
      (Cardinal.le_one_iff_subsingleton.mpr inferInstance).trans_lt
        (Cardinal.one_lt_aleph0.trans B.aleph0_lt_cutoff_cof)
    rw [Cardinal.mk_congr (show Iᵒᵖ ≃ I from ⟨unop, op, fun _ ↦ rfl, fun _ ↦ rfl⟩)]
    exact D.indexSize
  -- the chart of a stage and its compatibility square
  have hw : ∀ j : Over (op D.initial),
      C.stageMap j ≫ D.base.map j.hom = (C.baseMap j ≫ v) ≫ y := fun j ↦ by
    rw [Category.assoc]; exact (C.isPullback j).w
  have hwL : L.toLimit ≫ limit.π D.base (op D.initial) = (L.toBase ≫ v) ≫ y := by
    rw [Category.assoc]; exact L.isPullback.w
  have hm : ∀ {B' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (b : B' ⟶ D.base.obj (op D.initial)),
      pullback.fst b x ≫ b = (pullback.snd b x ≫ D.map₀) ≫ y := fun b ↦ by
    rw [Category.assoc, hf₀]; exact pullback.condition
  have hXa : ∀ j : Over (op D.initial),
      IsAlgebraicSpace B S hS (pullback (D.base.map j.hom) x) := fun j ↦
    D.sourceAt_isAlgebraicSpace j.left.unop (leOfHom j.hom.unop)
  have hYa : ∀ j : Over (op D.initial),
      IsAlgebraicSpace B S hS (pullback (D.base.map j.hom) y) := fun j ↦
    D.targetAt_isAlgebraicSpace j.left.unop (leOfHom j.hom.unop)
  have hmft : ∀ j : Over (op D.initial), IsFiniteType B S hS (pullback.lift
      (pullback.fst (D.base.map j.hom) x) (pullback.snd (D.base.map j.hom) x ≫ D.map₀) (hm _)) :=
    fun j ↦ isFiniteType_baseChange_of_isPullback (hXa j) hX₀ (hYa j) hY₀
      (isPullback_pullback_lift_snd _ (hm _) hf₀) hft₀
  -- the stage `i₁`
  let j₁ : Over (op D.initial) := Over.mk (homOfLE hi₁).op
  let W₁ := C.siteDiagram.obj j₁
  have hW₁ : IsAlgebraicSpace B S hS (yoneda.obj W₁) := isAlgebraicSpace_yoneda B S hS W₁
  let g₁ := pullback.lift (C.stageMap j₁) (C.baseMap j₁ ≫ v) (hw j₁)
  let m₁ := pullback.lift (pullback.fst (D.base.map j₁.hom) x)
    (pullback.snd (D.base.map j₁.hom) x ≫ D.map₀) (hm _)
  have hm₁ : m₁ = D.mapAt i₁ hi₁ := rfl
  let q₁ := pullback.fst g₁ m₁
  have hQ₁ : IsAlgebraicSpace B S hS (pullback g₁ m₁) :=
    isAlgebraicSpace_pullback B S hS _ _ hW₁ (hXa j₁) (hYa j₁)
  have hq₁sep : IsSeparated B S hS q₁ :=
    isSeparated_baseChange_of_isPullback (IsPullback.of_hasPullback g₁ m₁).flip hsep₁
  have hq₁ft : IsFiniteType B S hS q₁ :=
    isFiniteType_baseChange_of_isPullback hQ₁ (hXa j₁) hW₁ (hYa j₁)
      (IsPullback.of_hasPullback g₁ m₁).flip (hmft j₁)
  -- Stacks 089J over the affine chart `W₁`
  obtain ⟨X', ψ, p, hp, hps, hpq, hψlft, hψqc, hψsep⟩ :=
    exists_chowSchemeCover_of_affine W₁ (C.isAffine_obj j₁) hQ₁ q₁ hq₁sep hq₁ft
  have hX' : IsAlgebraicSpace B S hS (yoneda.obj X') := isAlgebraicSpace_yoneda B S hS X'
  -- the limit: the base change of `X'` to the chart of the limit is proper
  let gL := pullback.lift L.toLimit (L.toBase ≫ v) hwL
  have hLa : IsAlgebraicSpace B S hS (yoneda.obj L.cone.pt) :=
    isAlgebraicSpace_yoneda B S hS L.cone.pt
  have hQL : IsAlgebraicSpace B S hS (pullback gL D.mapLimit) :=
    isAlgebraicSpace_pullback B S hS _ _ hLa D.sourceLimit_isAlgebraicSpace
      D.targetLimit_isAlgebraicSpace
  have hqL : IsProper B S hS (pullback.fst gL D.mapLimit) :=
    isProper_of_isPullback B S hS hQL D.sourceLimit_isAlgebraicSpace hLa
      D.targetLimit_isAlgebraicSpace (IsPullback.of_hasPullback gL D.mapLimit).flip proper
  obtain ⟨aL, haL⟩ := exists_isPullback_chart_transition (D.base.map j₁.hom)
    (limit.π D.base (op D.initial)) (limit.π D.base j₁.left) (limit.w _ _) hf₀ v (hw j₁) hwL
    (yoneda.map (L.cone.π.app j₁)) (L.toLimit_comp_limitπ j₁).symm (L.baseMap_comp j₁)
    (hm _) (hm _)
  have hlimit := isProper_pullback_snd_comp_of_isPullback hX' hQ₁ hW₁ hQL hLa p q₁
    (yoneda.map (L.cone.π.app j₁)) haL hp hqL hpq
  rw [isProper_pullback_snd_yoneda_iff] at hlimit
  -- Stacks 081F for the scheme `X'` over the affine charts
  have : ∀ {j k : Over (op D.initial)} (g : j ⟶ k),
      _root_.AlgebraicGeometry.IsAffineHom (C.schemeDiagram.map g) :=
    fun g ↦ C.isAffineHom_map g
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj W₁) := C.isAffine_obj j₁
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj W₁) := Scheme.compactSpace_of_isAffine _
  have : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj W₁) := inferInstance
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj X') :=
    QuasiCompact.compactSpace_of_compactSpace ((BigFppfOver.toScheme B S hS).map ψ)
  have : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj X') :=
    quasiSeparatedSpace_of_quasiSeparated ((BigFppfOver.toScheme B S hS).map ψ)
  obtain ⟨j, g, hstage⟩ :=
    @exists_isProper_baseChange_of_isLimit_of_isOneAffineOpenStep
      Scheme.FiniteTypeApproximation.isOneAffineOpenStep (Over (op D.initial)) _ _ _
      C.schemeDiagram _ ((BigFppfOver.toScheme B S hS).mapCone L.cone) L.schemeIsLimit j₁
      (Over.mk ((BigFppfOver.toScheme B S hS).map ψ))
      (Over.mk (𝟙 (C.schemeDiagram.obj j₁)))
      (Over.homMk ((BigFppfOver.toScheme B S hS).map ψ))
      (inferInstanceAs (CompactSpace ((BigFppfOver.toScheme B S hS).obj W₁)))
      (inferInstanceAs (QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj W₁)))
      (inferInstanceAs (CompactSpace ((BigFppfOver.toScheme B S hS).obj X')))
      (inferInstanceAs (QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj X')))
      (inferInstanceAs (CompactSpace ((BigFppfOver.toScheme B S hS).obj W₁)))
      (inferInstanceAs (QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj W₁)))
      hψlft hψsep hlimit
  replace hstage := (isProper_pullback_snd_yoneda_iff ψ (C.siteDiagram.map g)).mpr hstage
  -- the stage `i`
  set i := j.left.unop
  have hi : D.initial ≤ i := leOfHom j.hom.unop
  let W := C.siteDiagram.obj j
  have hW : IsAlgebraicSpace B S hS (yoneda.obj W) := isAlgebraicSpace_yoneda B S hS W
  let gj := pullback.lift (C.stageMap j) (C.baseMap j ≫ v) (hw j)
  let mj := pullback.lift (pullback.fst (D.base.map j.hom) x)
    (pullback.snd (D.base.map j.hom) x ≫ D.map₀) (hm _)
  have hmj : mj = D.mapAt i hi := rfl
  have hQ : IsAlgebraicSpace B S hS (pullback gj mj) :=
    isAlgebraicSpace_pullback B S hS _ _ hW (hXa j) (hYa j)
  have hc : D.base.map g.left ≫ D.base.map j₁.hom = D.base.map j.hom := by
    rw [← Functor.map_comp, Over.w g]
  obtain ⟨a, ha⟩ := exists_isPullback_chart_transition (D.base.map j₁.hom) (D.base.map j.hom)
    (D.base.map g.left) hc hf₀ v (hw j₁) (hw j) (yoneda.map (C.siteDiagram.map g))
    (C.stageMap_naturality g) (C.baseMap_naturality g)
    (hm _) (hm _)
  obtain ⟨l, hl, hlq⟩ := exists_isSurjective_comp_eq_pullback_snd hX' hQ₁ hW₁ hQ hW p q₁
    (yoneda.map (C.siteDiagram.map g)) ha hps hpq
  have hmjsep : IsSeparated B S hS mj :=
    isSeparated_baseChange_of_isPullback (isPullback_pullback_lift_transition (D.base.map j₁.hom)
      (D.base.map j.hom) (D.base.map g.left) hc hf₀ (hm _) (hm _)
      (fst_comp_comp_eq_snd_comp _ _ _ hc x) (fst_comp_comp_eq_snd_comp _ _ _ hc y)) hsep₁
  have hPj : IsAlgebraicSpace B S hS (pullback (yoneda.map ψ) (yoneda.map (C.siteDiagram.map g))) :=
    isAlgebraicSpace_pullback B S hS _ _ hX' hW hW₁
  have hqj : IsProper B S hS (pullback.fst gj mj) := by
    refine isProper_of_isSurjective_comp B S hS hPj hQ hW l (pullback.fst gj mj) ?_ hl
      (isSeparated_baseChange_of_isPullback (IsPullback.of_hasPullback gj mj).flip hmjsep)
      (isFiniteType_baseChange_of_isPullback hQ (hXa j) hW (hYa j)
        (IsPullback.of_hasPullback gj mj).flip (hmft j))
    rw [hlq]
    exact hstage.2.2
  -- the chart `W ⟶ Y_i` is étale and surjective, and Stacks 083R concludes
  have hgj : IsPullback (C.baseMap j) gj v (pullback.snd (D.base.map j.hom) y) :=
    ((C.isPullback j).isPullback_pullback_lift (hw j)).flip
  have hgjet : IsEtale B S hS gj :=
    (isEtale_iff_presheaf_of_yoneda B S hS gj).mpr
      (MorphismProperty.of_isPullback hgj ((isEtale_iff_presheaf_of_yoneda B S hS v).mp hvet))
  have hgjsurj : IsSurjective B S hS gj :=
    isSurjective_of_presheafSurjective B S hS gj (MorphismProperty.of_isPullback hgj hvsurj)
  have htfae := isProper_tfae B S hS (D.sourceAt_isAlgebraicSpace i hi)
    (D.targetAt_isAlgebraicSpace i hi) (D.mapAt i hi)
  have h4 : ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ D.targetAt i hi),
      IsSurjective B S hS g ∧ IsEtale B S hS g ∧
        IsProper B S hS (pullback.fst g (D.mapAt i hi)) :=
    ⟨W, gj, hgjsurj, hgjet, hqj⟩
  exact ⟨i, hi, (htfae.out 4 1).mp h4⟩

end MorphismDescentSystem

end AlgebraicGeometry.Space

end
