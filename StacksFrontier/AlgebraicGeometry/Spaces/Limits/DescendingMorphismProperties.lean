module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.ModuleIsoFlatness
public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Limits.RelativeApproximation.FlatDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FlatLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PullbackFlatness
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSquares
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleGeometricPointCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineChartSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.RelativeDimensionDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonoCriteria

/-!
# Properties of a morphism of algebraic spaces that descend along a directed limit

Let `B = lim_i B_i` be a directed limit of algebraic spaces over a scheme `S` with affine
transition morphisms, let `f₀ : X₀ ⟶ Y₀` be a morphism of quasi-compact quasi-separated
algebraic spaces over `B₀`, and let `f_i : X_i ⟶ Y_i` and `f : X ⟶ Y` be the base changes of
`f₀` to a stage `B_i` and to the limit `B`. This is the situation of Stacks 084W, carried by
`AlgebraicGeometry.Space.MorphismDescentSystem`. If `f₀` is locally of finite presentation
and `f` is étale, surjective, smooth, flat, or universally injective, then so is `f_i` for some
`i ≥ 0`; and if `f₀` is locally of finite type and `f` has relative dimension at most `d`, then
so does `f_i` for some `i ≥ 0`. Likewise, if `f₀` is locally of finite presentation and the
pullback `F` to `X` of a quasi-coherent `𝒪_{X₀}`-module `F₀` of finite presentation is flat over
`Y`, then its pullback `F_i` to `X_i` is flat over `Y_i` for some `i ≥ 0`.

All three proofs are the same. One chooses an affine étale surjective chart `V₀ ⟶ Y₀` of the
target and an affine étale surjective chart `U₀ ⟶ X₀ ×_{Y₀} V₀`, giving a morphism of affine
schemes `U₀ ⟶ V₀` over which the three properties can be read off; base changing the chart
square to each `B_i` and to `B` turns the chart of the target into the directed system of
affine schemes `V_i` whose limit is `V`, and the statement becomes the corresponding descent
statement for the morphism of schemes `U₀ ⟶ V₀` over `V₀`. The shared part of this argument is
carried out once, with the property and the scheme-level descent theorem as parameters.

## Main results

* `AlgebraicGeometry.Space.MorphismDescentSystem.exists_isEtale_mapAt`: **Stacks 07SL**.
* `AlgebraicGeometry.Space.MorphismDescentSystem.exists_isSurjective_mapAt`: **Stacks 07SN**.
* `AlgebraicGeometry.Space.MorphismDescentSystem.exists_isSmooth_mapAt`: **Stacks 0CN2**.
* `AlgebraicGeometry.Space.MorphismDescentSystem.exists_isFlatOver_mapAt`: **Stacks 08K0**,
  flatness of a finitely presented module over the target.
* `AlgebraicGeometry.Space.MorphismDescentSystem.exists_isFlat_mapAt`: the case `F₀ = 𝒪_{X₀}`
  of Stacks 08K0, flatness of the morphism.
* `AlgebraicGeometry.Space.MorphismDescentSystem.exists_universallyInjective_mapAt`:
  **Stacks 084X**.
* `MorphismDescentSituation.exists_hasRelativeDimensionLE_mapAt_of_siteContainsBaseChangeLimits`
  (namespace `AlgebraicGeometry.Space`): **Stacks 0D4K**, in the situation of Stacks 084W
  under the chapter's convention of Section 70.2 (tag 07SD), with no bound on the index;
  `AlgebraicGeometry.Space.MorphismDescentSystem.exists_hasRelativeDimensionLE_mapAt` is the
  special case of an index of cardinality below the cofinality of the site's cutoff.
* `CategoryTheory.prop_snd_iff_of_isPullback`,
  `CategoryTheory.prop_overPullback_map_left_iff_pullback_snd` and
  `CategoryTheory.prop_iteratedPullback_snd_iff` transfer a property of morphisms between the
  various descriptions of a base change that the three statements run through.

## Implementation notes

Étaleness and smoothness of a morphism of algebraic spaces are conditions on its squares of
étale charts, so for them the chart square obtained by base changing `U₀ ⟶ V₀` is used in both
directions, through Stacks 03XT and 03FS for étaleness and through Stacks 03MJ for
smoothness. Surjectivity is a condition on the point sets instead, and the corresponding
transfer is proved directly from the behaviour of point sets under base change and
composition, Stacks 03MH and 03H5.

For a module `F₀` the chart square is used the same way. The restriction of the pullback of
`F₀` to the base-changed chart `U_i` of `X_i` is the pullback of `F₀|_{U₀}` along
`U_i ⟶ U₀`, by the compatibility of chart restriction with inverse images, so flatness of
`F_i|_{U_i}` over `V_i` is the scheme statement of Stacks 05LY for the finitely presented module
`F₀|_{U₀}` on `U₀`. Since `U_i ⟶ X_i` is surjective, flatness on this one square is flatness
of `F_i` over `Y_i`, by Stacks 05VU.

## References

* [Stacks Project, Tag 07SL](https://stacks.math.columbia.edu/tag/07SL)
* [Stacks Project, Tag 07SN](https://stacks.math.columbia.edu/tag/07SN)
* [Stacks Project, Tag 0CN2](https://stacks.math.columbia.edu/tag/0CN2)
* [Stacks Project, Tag 084W](https://stacks.math.columbia.edu/tag/084W)
* [Stacks Project, Tag 084X](https://stacks.math.columbia.edu/tag/084X)
* [Stacks Project, Tag 08K0](https://stacks.math.columbia.edu/tag/08K0)
* [Stacks Project, Tag 0D4K](https://stacks.math.columbia.edu/tag/0D4K)
* [Stacks Project, Tag 05LY](https://stacks.math.columbia.edu/tag/05LY)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe w v u

namespace CategoryTheory

variable {A : Type*} [Category* A]

/-- Two fibre products of the same pair of morphisms have the same second projection, up to
isomorphism; so a property of morphisms which respects isomorphisms holds for one exactly when
it holds for the other. -/
theorem prop_snd_iff_of_isPullback (P : MorphismProperty A) [P.RespectsIso]
    {X Y Z W W' : A} {f : X ⟶ Z} {g : Y ⟶ Z} {a : W ⟶ X} {b : W ⟶ Y}
    {a' : W' ⟶ X} {b' : W' ⟶ Y} (h : IsPullback a b f g) (h' : IsPullback a' b' f g) :
    P b ↔ P b' := by
  rw [← h.isoIsPullback_hom_snd X Y h']
  exact P.cancel_left_of_respectsIso (h.isoIsPullback X Y h').hom b'

variable [HasPullbacks A]

/-- Base changing a morphism `r : X ⟶ Y`, viewed as a morphism from `X` to the identity of `Y`
in the category over `Y`, along `q : Z ⟶ Y` gives the second projection of `X ×_Y Z` up to
isomorphism. -/
theorem prop_overPullback_map_left_iff_pullback_snd (P : MorphismProperty A)
    [P.RespectsIso] {X Y Z : A} (r : X ⟶ Y) (q : Z ⟶ Y) :
    P ((Over.pullback q).map (Over.homMk r : Over.mk r ⟶ Over.mk (𝟙 Y))).left ↔
      P (pullback.snd r q) := by
  have hw := Over.w ((Over.pullback q).map (Over.homMk r : Over.mk r ⟶ Over.mk (𝟙 Y)))
  change _ ≫ pullback.snd (𝟙 Y) q = pullback.snd r q at hw
  rw [← hw, P.cancel_right_of_respectsIso]

/-- Base changing `V ×_U W₀ ⟶ W₀` along a morphism `W ⟶ W₀` lying over `U` gives the image of
`V ×_U W ⟶ W` up to isomorphism. The two fibre products are formed in different categories,
the inner one before and the outer one after applying a functor preserving fibre products. -/
theorem prop_iteratedPullback_snd_iff {C : Type*} [Category* C] [HasPullbacks C]
    (T : A ⥤ C) [PreservesLimitsOfShape WalkingCospan T] (P : MorphismProperty C) [P.RespectsIso]
    {U V W₀ W : A} (r : V ⟶ U) (q₀ : W₀ ⟶ U) (q : W ⟶ U) (t : T.obj W ⟶ T.obj W₀)
    (ht : t ≫ T.map q₀ = T.map q) :
    P (pullback.snd (pullback.snd (T.map r) (T.map q₀)) t) ↔ P (T.map (pullback.snd r q)) := by
  have h := (IsPullback.of_hasPullback (pullback.snd (T.map r) (T.map q₀)) t).paste_horiz
    (IsPullback.of_hasPullback (T.map r) (T.map q₀))
  rw [ht] at h
  exact prop_snd_iff_of_isPullback P h ((IsPullback.of_hasPullback r q).map T)

end CategoryTheory

namespace AlgebraicGeometry

/-! ### Flatness of a pulled back module over the second factor of a fibre product -/

/-- Flatness over `Y` of the pullback of an `𝒪_X`-module to a fibre product `X ×_Z Y` does not
depend on the fibre product chosen: two cartesian squares on the same cospan differ by an
isomorphism of their apexes compatible with both projections, and flatness over the target is
invariant under such an isomorphism. -/
private theorem isFlatOver_modulePullback_iff_of_isPullback
    {P P' X Y Z : Scheme.{u}} {p : P ⟶ X} {q : P ⟶ Y} {p' : P' ⟶ X} {q' : P' ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback p q f g) (h' : IsPullback p' q' f g)
    (F : X.Modules) :
    IsFlatOver q.toLRSHom.toShHom ((Scheme.Modules.pullback p).obj F) ↔
      IsFlatOver q'.toLRSHom.toShHom ((Scheme.Modules.pullback p').obj F) := by
  let e := h.isoIsPullback X Y h'
  have hp : e.hom ≫ p' = p := h.isoIsPullback_hom_fst X Y h'
  have hq : e.hom ≫ q' = q := h.isoIsPullback_hom_snd X Y h'
  let E : (Scheme.Modules.pullback e.hom).obj ((Scheme.Modules.pullback p').obj F) ≅
      (Scheme.Modules.pullback p).obj F :=
    (schemeModulePullbackCompIso e.hom p').app F ≪≫ eqToIso (by rw [hp]; rfl)
  have H := isFlatOver_iff_modulePullback_isFlatOver e.hom q' ((Scheme.Modules.pullback p').obj F)
  rw [hq] at H
  exact (isFlatOver_iff_of_iso q E).symm.trans H.symm

/-- **Stacks 05LY**, read on the projections of a fibre product. Let `X` be a quasi-compact
quasi-separated scheme of finite presentation over one stage `E_i` of a cofiltered system of
quasi-compact quasi-separated schemes with affine transition morphisms, and let `F` be a
quasi-coherent `𝒪_X`-module of finite presentation. If the pullback of `F` to `X ×_{E_i} E` is
flat over the limit `E`, then the pullback of `F` to `X ×_{E_i} E_j` is flat over `E_j` for some
stage `j ⟶ i`. -/
private theorem exists_isFlatOver_modulePullback_pullback_snd
    {J : Type v} [Category.{w} J] [IsCofiltered J] [EssentiallySmall.{u} J]
    (E : J ⥤ Scheme.{u}) (c : Cone E) (hc : IsLimit c)
    [∀ {i j : J} (e : i ⟶ j), IsAffineHom (E.map e)]
    [∀ j : J, CompactSpace (E.obj j)] [∀ j : J, QuasiSeparatedSpace (E.obj j)]
    (i : J) {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] (f : X ⟶ E.obj i)
    [LocallyOfFinitePresentation f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation]
    (flat : IsFlatOver (pullback.snd f (c.π.app i)).toLRSHom.toShHom
      ((Scheme.Modules.pullback (pullback.fst f (c.π.app i))).obj F)) :
    ∃ (j : J) (e : j ⟶ i), IsFlatOver (pullback.snd f (E.map e)).toLRSHom.toShHom
      ((Scheme.Modules.pullback (pullback.fst f (E.map e))).obj F) := by
  have fpX : FinitePresentation f := finitePresentation_of_compactSpace f inferInstance
  have fpY : FinitePresentation (𝟙 (E.obj i)) := ⟨inferInstance, inferInstance, inferInstance⟩
  have : SheafOfModules.IsQuasicoherent (R := structureSheafRing X.toRingedSpace) F := ‹_›
  have : SheafOfModules.IsFinitePresentation (R := structureSheafRing X.toRingedSpace) F := ‹_›
  obtain ⟨j, e, hj⟩ := eventually_isFlatOver_modulePullback E c hc i (Over.mk f)
    (Over.mk (𝟙 (E.obj i))) fpX fpY (Over.homMk f) F
    ((isFlatOver_overPullback_map_iff (Over.mk f) (c.π.app i) _).mpr flat)
  exact ⟨j, e, (isFlatOver_overPullback_map_iff (Over.mk f) (E.map e) _).mp hj⟩

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

/- Pullback instances of `FibreDegreeStratification`, which instance search does not find
under Lean v4.35.0. -/
/-- Pullbacks of presheaves on the big fppf site over `S`, given directly: instance search for
them times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_DescendingMorphismProperties
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  CategoryTheory.Limits.functorCategoryHasLimitsOfShape

/-- The pullback of two morphisms of presheaves on the big fppf site over `S`. -/
local instance (priority := high) hasPullback_presheaf_DescendingMorphismProperties
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Chart squares of a base change -/

section BaseChangeSquares

variable {A : Type*} [Category* A] [HasPullbacks A]

/-- A morphism between the two base changes of a morphism `f` along a common morphism `t`,
compatible with both projections, is itself a base change of `f`. -/
private theorem isPullback_of_proj_eq {X Y Bs B' : A} (x : X ⟶ Bs) (y : Y ⟶ Bs) (f : X ⟶ Y)
    (hf : f ≫ y = x) (t : B' ⟶ Bs) (f' : pullback t x ⟶ pullback t y)
    (hf₁ : f' ≫ pullback.fst t y = pullback.fst t x)
    (hf₂ : f' ≫ pullback.snd t y = pullback.snd t x ≫ f) :
    IsPullback (pullback.snd t x) f' f (pullback.snd t y) := by
  refine IsPullback.of_bot ?_ hf₂.symm (IsPullback.of_hasPullback t y).flip
  rw [hf₁, hf]
  exact (IsPullback.of_hasPullback t x).flip

/-- A chart `a` of `X` lifts to a chart of the base change `B' ×_Bs X` along any
representation of the base change of `a ≫ x` along `t`. -/
private theorem isPullback_chart_baseChange {U X Bs W B' : A} (a : U ⟶ X) (x : X ⟶ Bs)
    (t : B' ⟶ Bs) (p : W ⟶ B') (q : W ⟶ U) (h : IsPullback p q t (a ≫ x)) :
    IsPullback q (pullback.lift (f := t) (g := x) p (q ≫ a)
        (by simpa only [Category.assoc] using h.w)) a (pullback.snd t x) := by
  refine IsPullback.of_bot (t := (IsPullback.of_hasPullback t x).flip) ?_
    (pullback.lift_snd _ _ _).symm
  simpa only [pullback.lift_fst] using h.flip

/-- A base change of a chart square. Given a square of charts `a` of `X` and `b` of `Y` over
`r`, a fibre product `R` of `r` and `q`, and a representation by `q` of the base change of
`b ≫ y` along `t`, the base change `f'` of `f` along `t` fits into a square of charts over
`R ⟶ W`, obtained by base changing the original one. -/
private theorem exists_chart_square_baseChange {X Y Bs B' U V W R : A} (x : X ⟶ Bs)
    (y : Y ⟶ Bs) (f : X ⟶ Y) (hf : f ≫ y = x) (t : B' ⟶ Bs) (a : V ⟶ X) (b : U ⟶ Y) (r : V ⟶ U)
    (hr : r ≫ b = a ≫ f) (p : W ⟶ B') (q : W ⟶ U) (hp : IsPullback p q t (b ≫ y))
    {ρ : R ⟶ V} {σ : R ⟶ W} (hσ : IsPullback ρ σ r q)
    (f' : pullback t x ⟶ pullback t y)
    (hf₁ : f' ≫ pullback.fst t y = pullback.fst t x)
    (hf₂ : f' ≫ pullback.snd t y = pullback.snd t x ≫ f) :
    ∃ (a' : R ⟶ pullback t x) (b' : W ⟶ pullback t y),
      IsPullback ρ a' a (pullback.snd t x) ∧
        IsPullback q b' b (pullback.snd t y) ∧ σ ≫ b' = a' ≫ f' := by
  have hbase : r ≫ b ≫ y = a ≫ x := by rw [← Category.assoc, hr, Category.assoc, hf]
  have hp' : IsPullback (σ ≫ p) ρ t (a ≫ x) := by
    simpa only [hbase] using (hσ.paste_vert hp.flip).flip
  refine ⟨_, _, isPullback_chart_baseChange a x t (σ ≫ p) ρ hp',
    isPullback_chart_baseChange b y t p q hp, pullback.hom_ext ?_ ?_⟩
  · simp only [Category.assoc, hf₁, pullback.lift_fst]
  · simp only [Category.assoc, hf₂, pullback.lift_snd, pullback.lift_snd_assoc]
    rw [← Category.assoc, ← hσ.w, Category.assoc, hr]

end BaseChangeSquares

/-! ### Relative étaleness and surjectivity of charts -/

/-- Relative étaleness of a morphism of presheaves on the big fppf site over `S`: every
representable base change of it is an étale morphism of schemes. -/
private abbrev relEtale (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf

/-- Relative surjectivity of a morphism of presheaves on the big fppf site over `S`: every
representable base change of it is a surjective morphism of schemes. -/
private abbrev relSurjective (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf

attribute [local instance] MorphismProperty.relative_isStableUnderBaseChange

/-! ### Transferring a chart-local property to the morphism of charts -/

section Transfer

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- If a property of morphisms of schemes holds on every square of étale charts of the base
change `f'` of `f` along `t`, then it holds for the morphism of schemes underlying the base
change of the chart morphism `r`. -/
private theorem prop_chartMap_of_holdsOnEveryEtaleChart (P : MorphismProperty Scheme.{u})
    {X Y Bs B' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (x : X ⟶ Bs) (y : Y ⟶ Bs) (f : X ⟶ Y)
    (hf : f ≫ y = x) (t : B' ⟶ Bs) {U V W : BigFppfOver B S hS}
    (a : yoneda.obj V ⟶ X) (b : yoneda.obj U ⟶ Y) (r : V ⟶ U)
    (hr : yoneda.map r ≫ b = a ≫ f) (ha : relEtale B S hS a) (hb : relEtale B S hS b)
    (p : yoneda.obj W ⟶ B') (q : W ⟶ U) (hp : IsPullback p (yoneda.map q) t (b ≫ y))
    (f' : pullback t x ⟶ pullback t y)
    (hf₁ : f' ≫ pullback.fst t y = pullback.fst t x)
    (hf₂ : f' ≫ pullback.snd t y = pullback.snd t x ≫ f)
    (hevery : HoldsOnEveryEtaleChart B S hS P f') :
    P ((BigFppfOver.toScheme B S hS).map (pullback.snd r q)) := by
  obtain ⟨a', b', sa, sb, comm⟩ := exists_chart_square_baseChange x y f hf t a b (yoneda.map r)
    hr p (yoneda.map q) hp ((IsPullback.of_hasPullback r q).map yoneda) f' hf₁ hf₂
  exact hevery _ _ a' b' (pullback.snd r q) (MorphismProperty.of_isPullback sa ha)
    (MorphismProperty.of_isPullback sb hb) comm

/-- Conversely, if the chart morphism `r` has a property of morphisms of schemes after base
change and the chart `a` is in addition surjective, then that property holds on a surjective
square of étale charts of the base change `f'` of `f` along `t`. -/
private theorem holdsOnSurjectiveEtaleChart_of_prop_chartMap (P : MorphismProperty Scheme.{u})
    {X Y Bs B' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (x : X ⟶ Bs) (y : Y ⟶ Bs) (f : X ⟶ Y)
    (hf : f ≫ y = x) (t : B' ⟶ Bs) {U V W : BigFppfOver B S hS}
    (a : yoneda.obj V ⟶ X) (b : yoneda.obj U ⟶ Y) (r : V ⟶ U)
    (hr : yoneda.map r ≫ b = a ≫ f) (ha : relEtale B S hS a) (hb : relEtale B S hS b)
    (hs : relSurjective B S hS a)
    (p : yoneda.obj W ⟶ B') (q : W ⟶ U) (hp : IsPullback p (yoneda.map q) t (b ≫ y))
    (f' : pullback t x ⟶ pullback t y)
    (hf₁ : f' ≫ pullback.fst t y = pullback.fst t x)
    (hf₂ : f' ≫ pullback.snd t y = pullback.snd t x ≫ f)
    (hP : P ((BigFppfOver.toScheme B S hS).map (pullback.snd r q))) :
    HoldsOnSurjectiveEtaleChart B S hS P f' := by
  obtain ⟨a', b', sa, sb, comm⟩ := exists_chart_square_baseChange x y f hf t a b (yoneda.map r)
    hr p (yoneda.map q) hp ((IsPullback.of_hasPullback r q).map yoneda) f' hf₁ hf₂
  exact ⟨_, _, a', b', pullback.snd r q, MorphismProperty.of_isPullback sa ha,
    MorphismProperty.of_isPullback sb hb, MorphismProperty.of_isPullback sa hs, comm, hP⟩

end Transfer

/-! ### Transferring surjectivity to the morphism of charts -/

section SurjectiveTransfer

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Surjectivity on points passes from a composite to its second factor. -/
private theorem isSurjective_of_comp {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    {g : Y ⟶ Z} (h : IsSurjective B S hS (f ≫ g)) : IsSurjective B S hS g := by
  refine Function.Surjective.of_comp (g := pointsMap B S hS X f) ?_
  simpa only [← pointsMap_comp] using h

/-- Two fibre products of the same pair of morphisms of algebraic spaces have the same second
projection up to isomorphism, so one is surjective exactly when the other is. -/
private theorem isSurjective_snd_iff {Pb Pb' X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : Pb ⟶ X} {b : Pb ⟶ Y} {a' : Pb' ⟶ X} {b' : Pb' ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback a b f g) (h' : IsPullback a' b' f g) :
    IsSurjective B S hS b ↔ IsSurjective B S hS b' := by
  constructor
  · intro hs
    exact isSurjective_of_comp (f := h'.lift a b h.w) (by simpa using hs)
  · intro hs
    exact isSurjective_of_comp (f := h.lift a' b' h'.w) (by simpa using hs)

/-- **Stacks 03MH** for presheaf fibre products: a base change of a morphism of algebraic
spaces surjective on points is surjective on points. -/
private theorem isSurjective_of_isPullback_presheaf
    {Pb X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a : Pb ⟶ X} {b : Pb ⟶ Y} {f : X ⟶ Z}
    {g : Y ⟶ Z} (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (h : IsPullback a b f g)
    (hf : IsSurjective B S hS f) : IsSurjective B S hS b := by
  have hb := isSurjective_of_isPullback B S hS
    (AlgebraicSpaces.isPullback_fiberProduct B S hS
      (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Z, hZ⟩)
      (ObjectProperty.homMk g : (⟨Y, hY⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Z, hZ⟩)) hf
  exact (isSurjective_snd_iff (IsPullback.of_hasPullback f g) h).mp hb

/-- Surjectivity of a morphism of algebraic spaces is read off from a square of charts whose
chart of the source covers the fibre product: the base change `f'` is surjective exactly when
the base change of the chart morphism is. -/
private theorem isSurjective_chart_iff {X Y X' Y' Uu Vv Ww : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hX' : IsAlgebraicSpace B S hS X') (hY' : IsAlgebraicSpace B S hS Y')
    (hU : IsAlgebraicSpace B S hS Uu) (hV : IsAlgebraicSpace B S hS Vv)
    (hW : IsAlgebraicSpace B S hS Ww) {f : X ⟶ Y} {f' : X' ⟶ Y'} {xx : X' ⟶ X} {yy : Y' ⟶ Y}
    {v : Vv ⟶ Y} {v' : Ww ⟶ Y'} {qq : Ww ⟶ Vv} (u : Uu ⟶ pullback f v)
    (hfsq : IsPullback xx f' f yy) (hvsq : IsPullback qq v' v yy)
    (hsu : IsSurjective B S hS u) (hsv : IsSurjective B S hS v) :
    IsSurjective B S hS (pullback.snd (u ≫ pullback.snd f v) qq) ↔ IsSurjective B S hS f' := by
  let a := pullback.snd f v
  let cmp : pullback (u ≫ a) qq ⟶ pullback a qq :=
    pullback.lift (pullback.fst (u ≫ a) qq ≫ u) (pullback.snd (u ≫ a) qq)
      (by simp [Category.assoc, pullback.condition])
  have hcmp : IsPullback (pullback.fst (u ≫ a) qq) cmp u (pullback.fst a qq) := by
    apply IsPullback.of_bot (h₂₁ := pullback.fst a qq) (v₂₁ := pullback.snd a qq) (v₂₂ := a)
      (h₃₁ := qq)
    · simpa only [cmp, pullback.lift_snd] using IsPullback.of_hasPullback (u ≫ a) qq
    · simp only [cmp, pullback.lift_fst]
    · exact IsPullback.of_hasPullback a qq
  have hP := isAlgebraicSpace_pullback B S hS f v hX hV hY
  have hP' := isAlgebraicSpace_pullback B S hS a qq hP hW hV
  have hcmps : IsSurjective B S hS cmp :=
    isSurjective_of_isPullback_presheaf hU hP' hP hcmp hsu
  have houter := (IsPullback.of_hasPullback a qq).paste_horiz (IsPullback.of_hasPullback f v)
  have houter' := (IsPullback.of_hasPullback f' v').paste_horiz hfsq
  have heq : IsSurjective B S hS (pullback.snd a qq) ↔
      IsSurjective B S hS (pullback.snd f' v') := by
    rw [hvsq.w] at houter
    exact isSurjective_snd_iff houter houter'
  constructor
  · intro hs
    have hps : IsSurjective B S hS (pullback.snd a qq) := by
      refine isSurjective_of_comp (f := cmp) ?_
      simpa only [cmp, pullback.lift_snd] using hs
    have hvs : IsSurjective B S hS v' := isSurjective_of_isPullback_presheaf hV hY' hY hvsq hsv
    have hc := isSurjective_comp B S hS (heq.mp hps) hvs
    rw [← pullback.condition] at hc
    exact isSurjective_of_comp hc
  · intro hs
    have hps := heq.mpr (isSurjective_of_isPullback_presheaf hX' hW hY'
      (IsPullback.of_hasPullback f' v') hs)
    simpa only [cmp, pullback.lift_snd] using isSurjective_comp B S hS hcmps hps

/-- Surjectivity of the morphism of schemes underlying a fibre product of the site is
surjectivity on points of the fibre product of the represented presheaves. -/
private theorem surjective_map_pullback_snd_iff {Uu Vv Ww : BigFppfOver B S hS}
    (r : Vv ⟶ Uu) (q : Ww ⟶ Uu) :
    Surjective ((BigFppfOver.toScheme B S hS).map (pullback.snd r q)) ↔
      IsSurjective B S hS (pullback.snd (yoneda.map r) (yoneda.map q)) := by
  rw [← presheaf_yoneda_map_iff B S hS (P := @Surjective.{u}) inferInstance (pullback.snd r q),
    presheafSurjective_iff_isSurjective_yoneda B S hS (yoneda.obj Ww)
      (isAlgebraicSpace_yoneda B S hS Ww) (pullback r q) (yoneda.map (pullback.snd r q))]
  exact isSurjective_snd_iff ((IsPullback.of_hasPullback r q).map yoneda)
    (IsPullback.of_hasPullback (yoneda.map r) (yoneda.map q))

end SurjectiveTransfer

/-! ### The descent results for the situation of Stacks 084W

The results above, stated for `AlgebraicGeometry.Space.MorphismDescentSituation`, which imposes
no condition on the size of the index. What the proofs need is that the limits of the affine
charts of the system are formed inside the site, which is the chapter's convention of Section
70.2 (tag 07SD), the explicit hypothesis
`hconv : AlgebraicGeometry.Space.SiteContainsBaseChangeLimits B S hS D.base`. Each result is
also stated under `hb : AlgebraicGeometry.Space.IsSiteSmall B S hS D.base`, which implies the
convention by `AlgebraicGeometry.Space.IsSiteSmall.siteContainsBaseChangeLimits`. -/

section SituationChartData

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]

/-- A square of affine étale charts for a morphism descent system: an affine étale surjective
chart `V₀ ⟶ Y₀` of the target at the distinguished stage, an affine étale surjective chart
`U₀ ⟶ X₀ ×_{Y₀} V₀` of the fibre product, and the morphism `U₀ ⟶ V₀` of affine objects of the
site that the square induces. -/
private structure SituationChartSquare (D : MorphismDescentSituation B S hS hZ I) where
  /-- The chapter's convention (Section 70.2, tag 07SD) for the inverse system, so that the
  limits of its affine charts are formed inside the site. -/
  siteContains : SiteContainsBaseChangeLimits B S hS D.base
  /-- The affine object of the site charting the target. -/
  targetObj : BigAffineFppf B S hS
  /-- The affine object of the site charting the fibre product of the morphism with the chart
  of the target. -/
  sourceObj : BigAffineFppf B S hS
  /-- The chart `V₀ ⟶ Y₀` of the target. -/
  targetChart : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj targetObj) ⟶ D.target₀
  /-- The chart `U₀ ⟶ X₀ ×_{Y₀} V₀` of the fibre product. -/
  cover : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj sourceObj) ⟶
    pullback D.map₀ targetChart
  /-- The morphism `U₀ ⟶ V₀` of affine objects of the site. -/
  chartMap : (BigAffineFppf.inclusion B S hS).obj sourceObj ⟶
    (BigAffineFppf.inclusion B S hS).obj targetObj
  /-- The chart of the target is étale. -/
  targetChart_etale : relEtale B S hS targetChart
  /-- The chart of the target is surjective. -/
  targetChart_surjective : relSurjective B S hS targetChart
  /-- The chart of the fibre product is étale. -/
  cover_etale : relEtale B S hS cover
  /-- The chart of the fibre product is surjective. -/
  cover_surjective : relSurjective B S hS cover
  /-- The morphism of affine objects is the second projection of the chart of the fibre
  product. -/
  yoneda_map_chartMap : yoneda.map chartMap = cover ≫ pullback.snd D.map₀ targetChart

/-- **Stacks 07SL, 07SN and 0CN2**, the choice of charts the three proofs begin with. A
quasi-compact quasi-separated morphism descent system admits a square of affine étale
charts. -/
private theorem nonempty_situationChartSquare (D : MorphismDescentSituation B S hS hZ I)
    (hconv : SiteContainsBaseChangeLimits B S hS D.base) : Nonempty (SituationChartSquare D) := by
  obtain ⟨U, chart, hU, hchartS, hchartE⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS D.target₀
      D.target₀_isAlgebraicSpace).mp D.target₀_quasiCompact
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
  have hfibSpace : IsAlgebraicSpace B S hS (pullback D.map₀ chart) :=
    isAlgebraicSpace_pullback B S hS D.map₀ chart D.source₀_isAlgebraicSpace
      (isAlgebraicSpace_yoneda B S hS U) D.target₀_isAlgebraicSpace
  have hfib : IsQuasiCompactSpace B S hS (pullback D.map₀ chart) :=
    isQuasiCompactSpace_pullback B S hS hZ D.map₀ chart D.source₀_isAlgebraicSpace
      D.target₀_isAlgebraicSpace D.source₀_quasiCompact
      (isQuasiCompactSpace_yoneda_obj B S hS inferInstance) D.target₀_quasiSeparated
  obtain ⟨V, cover, hV, hcoverS, hcoverE⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS _ hfibSpace).mp hfib
  exact ⟨{ siteContains := hconv
           targetObj := ⟨U, hU⟩
           sourceObj := ⟨V, hV⟩
           targetChart := chart
           cover := cover
           chartMap := yoneda.preimage (cover ≫ pullback.snd D.map₀ chart)
           targetChart_etale := (isEtale_iff_presheaf_of_yoneda B S hS chart).mp hchartE
           targetChart_surjective := hchartS
           cover_etale := (isEtale_iff_presheaf_of_yoneda B S hS cover).mp hcoverE
           cover_surjective := hcoverS
           yoneda_map_chartMap := yoneda.map_preimage _ }⟩

/-- The index category of a morphism descent situation, read covariantly, is cofiltered. -/
private theorem isCofiltered_op_aux (D : MorphismDescentSituation B S hS hZ I) :
    IsCofiltered Iᵒᵖ :=
  haveI : Nonempty I := ⟨D.initial⟩
  inferInstance

namespace SituationChartSquare

/-- The chart `U₀ ⟶ X₀` of the source. -/
private noncomputable def sourceChart {D : MorphismDescentSituation B S hS hZ I}
    (C : SituationChartSquare D) :
    yoneda.obj ((BigAffineFppf.inclusion B S hS).obj C.sourceObj) ⟶ D.source₀ :=
  C.cover ≫ pullback.fst D.map₀ C.targetChart

private theorem sourceChart_etale {D : MorphismDescentSituation B S hS hZ I} (C :
    SituationChartSquare D) :
    relEtale B S hS C.sourceChart := by
  have := isMultiplicative_presheaf_etale B S hS
  exact MorphismProperty.comp_mem _ _ _ C.cover_etale
    (MorphismProperty.of_isPullback (IsPullback.of_hasPullback D.map₀ C.targetChart).flip
      C.targetChart_etale)

private theorem sourceChart_surjective {D : MorphismDescentSituation B S hS hZ I}
    (C : SituationChartSquare D) : relSurjective B S hS C.sourceChart := by
  have := isMultiplicative_presheaf_surjective B S hS
  exact MorphismProperty.comp_mem _ _ _ C.cover_surjective
    (MorphismProperty.of_isPullback (IsPullback.of_hasPullback D.map₀ C.targetChart).flip
      C.targetChart_surjective)

private theorem comm {D : MorphismDescentSituation B S hS hZ I} (C : SituationChartSquare D) :
    yoneda.map C.chartMap ≫ C.targetChart = C.sourceChart ≫ D.map₀ := by
  rw [C.yoneda_map_chartMap]
  simp only [sourceChart, Category.assoc, pullback.condition]

/-- The chart of the distinguished stage `B₀` obtained from the chart of the target. -/
private noncomputable def baseChart {D : MorphismDescentSituation B S hS hZ I} (C :
    SituationChartSquare D) :
    yoneda.obj ((BigAffineFppf.inclusion B S hS).obj C.targetObj) ⟶ D.base.obj (op D.initial) :=
  C.targetChart ≫ D.targetToBase

/-- The system of affine charts of the stages, obtained by base changing the chart of the
distinguished stage along the transition morphisms. -/
private noncomputable def system {D : MorphismDescentSituation B S hS hZ I} (C :
    SituationChartSquare D) :
    AffineChartSystem B S hS (op D.initial) D.base C.targetObj C.baseChart :=
  affineChartSystem B S hS (op D.initial) D.base C.targetObj C.baseChart
    (fun {_ _} g ↦ D.transition_affine g)

/-- The limit of the system of affine charts of the stages. -/
private noncomputable def bridge {D : MorphismDescentSituation B S hS hZ I} (C :
    SituationChartSquare D) :
    AffineChartSystem.LimitBridge C.system := by
  haveI := isCofiltered_op_aux D
  exact AffineChartSystem.limitBridgeOfLimitInSite C.system
    (C.system.limitInSite_of_siteContainsBaseChangeLimits C.siteContains)

/-- The diagram of affine schemes charting the stages at or beyond the distinguished one. -/
private noncomputable abbrev diagram {D : MorphismDescentSituation B S hS hZ I}
    (C : SituationChartSquare D) : Over (op D.initial) ⥤ Scheme.{u} :=
  C.system.schemeDiagram

/-- The limit cone of the diagram of affine schemes charting the stages. -/
private noncomputable abbrev cone {D : MorphismDescentSituation B S hS hZ I} (C :
    SituationChartSquare D) :
    Cone C.diagram :=
  (BigFppfOver.toScheme B S hS).mapCone C.bridge.cone

/-- The cone of charts of the stages is a limit cone. -/
private noncomputable def isLimit_cone {D : MorphismDescentSituation B S hS hZ I}
    (C : SituationChartSquare D) : IsLimit C.cone := C.bridge.schemeIsLimit

private theorem isAffine_diagram_obj {D : MorphismDescentSituation B S hS hZ I} (C :
    SituationChartSquare D)
    (j : Over (op D.initial)) : IsAffine (C.diagram.obj j) :=
  C.system.isAffine_obj j

private theorem isAffineHom_diagram_map {D : MorphismDescentSituation B S hS hZ I}
    (C : SituationChartSquare D) {j k : Over (op D.initial)} (g : j ⟶ k) :
    _root_.AlgebraicGeometry.IsAffineHom (C.diagram.map g) :=
  C.system.isAffineHom_map g

/-- The chart of a stage, as a morphism of the site. -/
private noncomputable def stageChart {D : MorphismDescentSituation B S hS hZ I} (C :
    SituationChartSquare D)
    (j : Over (op D.initial)) :
    C.system.siteDiagram.obj j ⟶ (BigAffineFppf.inclusion B S hS).obj C.targetObj :=
  yoneda.preimage (C.system.baseMap j)

private theorem yoneda_map_stageChart {D : MorphismDescentSituation B S hS hZ I} (C :
    SituationChartSquare D)
    (j : Over (op D.initial)) : yoneda.map (C.stageChart j) = C.system.baseMap j :=
  yoneda.map_preimage _

private theorem isPullback_stageChart {D : MorphismDescentSituation B S hS hZ I} (C :
    SituationChartSquare D)
    (j : Over (op D.initial)) :
    IsPullback (C.system.stageMap j) (yoneda.map (C.stageChart j))
      (D.baseAtToInitial j.left.unop (leOfHom j.hom.unop)) C.baseChart := by
  rw [C.yoneda_map_stageChart,
    show D.baseAtToInitial j.left.unop (leOfHom j.hom.unop) = D.base.map j.hom from
      congrArg D.base.map (Subsingleton.elim _ _)]
  exact C.system.isPullback j

private theorem siteDiagram_map_comp_stageChart {D : MorphismDescentSituation B S hS hZ I}
    (C : SituationChartSquare D) {j k : Over (op D.initial)} (g : j ⟶ k) :
    C.system.siteDiagram.map g ≫ C.stageChart k = C.stageChart j := by
  have hnat : yoneda.map (C.system.siteDiagram.map g) ≫ C.system.iso.hom.app k =
      C.system.iso.hom.app j ≫ (stageBaseChangeDiagram B S hS (op D.initial) D.base
        C.targetObj C.baseChart).map g := C.system.iso.hom.naturality g
  have hw : (stageBaseChangeDiagram B S hS (op D.initial) D.base C.targetObj C.baseChart).map g ≫
      stageBaseChangeSnd B S hS (op D.initial) D.base C.targetObj C.baseChart k =
      stageBaseChangeSnd B S hS (op D.initial) D.base C.targetObj C.baseChart j :=
    Over.w ((Over.post (X := op D.initial) D.base ⋙ Over.pullback C.baseChart).map g)
  apply yoneda.map_injective
  rw [yoneda.map_comp, C.yoneda_map_stageChart, C.yoneda_map_stageChart]
  simp only [AffineChartSystem.baseMap]
  rw [← Category.assoc, hnat, Category.assoc, hw]

/-- The chart of the limit, as a morphism of the site. -/
private noncomputable def limitChart {D : MorphismDescentSituation B S hS hZ I}
    (C : SituationChartSquare D) :
    C.bridge.cone.pt ⟶ (BigAffineFppf.inclusion B S hS).obj C.targetObj :=
  yoneda.preimage C.bridge.toBase

private theorem yoneda_map_limitChart {D : MorphismDescentSituation B S hS hZ I}
    (C : SituationChartSquare D) : yoneda.map C.limitChart = C.bridge.toBase :=
  yoneda.map_preimage _

private theorem isPullback_limitChart {D : MorphismDescentSituation B S hS hZ I}
    (C : SituationChartSquare D) :
    IsPullback C.bridge.toLimit (yoneda.map C.limitChart) (limit.π D.base (op D.initial))
      C.baseChart := by
  rw [C.yoneda_map_limitChart]
  exact C.bridge.isPullback

private theorem cone_π_comp_stageChart {D : MorphismDescentSituation B S hS hZ I}
    (C : SituationChartSquare D) (j : Over (op D.initial)) :
    C.bridge.cone.π.app j ≫ C.stageChart j = C.limitChart := by
  apply yoneda.map_injective
  rw [yoneda.map_comp, C.yoneda_map_stageChart, C.yoneda_map_limitChart]
  exact C.bridge.baseMap_comp j

private theorem toScheme_cone_π_comp_stageChart {D : MorphismDescentSituation B S hS hZ I}
    (C : SituationChartSquare D) (j : Over (op D.initial)) :
    C.cone.π.app j ≫ (BigFppfOver.toScheme B S hS).map (C.stageChart j) =
      (BigFppfOver.toScheme B S hS).map C.limitChart := by
  change (BigFppfOver.toScheme B S hS).map (C.bridge.cone.π.app j) ≫ _ = _
  rw [← Functor.map_comp, C.cone_π_comp_stageChart j]

private theorem toScheme_diagram_map_comp_stageChart {D : MorphismDescentSituation B S hS hZ I}
    (C : SituationChartSquare D) {j k : Over (op D.initial)} (g : j ⟶ k) :
    C.diagram.map g ≫ (BigFppfOver.toScheme B S hS).map (C.stageChart k) =
      (BigFppfOver.toScheme B S hS).map (C.stageChart j) := by
  change (BigFppfOver.toScheme B S hS).map (C.system.siteDiagram.map g) ≫ _ = _
  rw [← Functor.map_comp, C.siteDiagram_map_comp_stageChart g]

/-- The base change of the chart morphism along the chart of a stage is a morphism of schemes with
affine source. -/
private theorem isAffine_pullback_chartMap_stageChart {D : MorphismDescentSituation B S hS hZ I}
    (C : SituationChartSquare D) (j : Over (op D.initial)) :
    IsAffine (pullback ((BigFppfOver.toScheme B S hS).map C.chartMap)
      ((BigFppfOver.toScheme B S hS).map (C.stageChart j))) := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (C.system.siteDiagram.obj j)) :=
    C.isAffine_diagram_obj j
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((BigAffineFppf.inclusion B S hS).obj C.targetObj)) := C.targetObj.property
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((BigAffineFppf.inclusion B S hS).obj C.sourceObj)) := C.sourceObj.property
  have : _root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B S hS).map (C.stageChart j)) := isAffineHom_of_isAffine _
  exact isAffine_of_isAffineHom (pullback.fst ((BigFppfOver.toScheme B S hS).map C.chartMap)
    ((BigFppfOver.toScheme B S hS).map (C.stageChart j)))

/-- The hypotheses on the index category and the diagram of affine charts that the descent
theorems for schemes require. -/
private theorem stage_instances {D : MorphismDescentSituation B S hS hZ I}
    (C : SituationChartSquare D) :
    IsCofiltered (Over (op D.initial)) ∧
      (∀ {j k : Over (op D.initial)} (g : j ⟶ k),
        _root_.AlgebraicGeometry.IsAffineHom (C.diagram.map g)) ∧
      (∀ j, CompactSpace (C.diagram.obj j)) ∧ ∀ j, QuasiSeparatedSpace (C.diagram.obj j) := by
  have := isCofiltered_op_aux D
  exact ⟨inferInstance, fun g ↦ C.isAffineHom_diagram_map g,
    fun j ↦ have := C.isAffine_diagram_obj j; Scheme.compactSpace_of_isAffine _,
    fun j ↦ have := C.isAffine_diagram_obj j; inferInstance⟩

private theorem locallyOfFinitePresentation_chartMap {D : MorphismDescentSituation B S hS hZ I}
    (C : SituationChartSquare D) (fp : IsLocallyOfFinitePresentation B S hS D.map₀) :
    LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map C.chartMap) :=
  fp _ _ C.sourceChart C.targetChart C.chartMap C.sourceChart_etale C.targetChart_etale C.comm

/-- A property `Q` of morphisms of algebraic spaces which holds exactly when a property `P` of
morphisms of schemes holds on every square of étale charts, or on one square with surjective chart
of the source, is read off the base change of the chart morphism. -/
private theorem iff_prop_chartMap {D : MorphismDescentSituation B S hS hZ I}
    (C : SituationChartSquare D) (P : MorphismProperty Scheme.{u})
    (Q : ∀ {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, (F ⟶ G) → Prop)
    (hQ : ∀ {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS F →
      IsAlgebraicSpace B S hS G → ∀ f : F ⟶ G, Q f → HoldsOnEveryEtaleChart B S hS P f)
    (hQ' : ∀ {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS F →
      IsAlgebraicSpace B S hS G → ∀ f : F ⟶ G, HoldsOnSurjectiveEtaleChart B S hS P f → Q f)
    (B' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (t : B' ⟶ D.base.obj (op D.initial))
    (W : BigFppfOver B S hS) (p : yoneda.obj W ⟶ B')
    (q : W ⟶ (BigAffineFppf.inclusion B S hS).obj C.targetObj)
    (hp : IsPullback p (yoneda.map q) t C.baseChart)
    (f' : pullback t D.sourceToBase ⟶ pullback t D.targetToBase)
    (hf₁ : f' ≫ pullback.fst t D.targetToBase = pullback.fst t D.sourceToBase)
    (hf₂ : f' ≫ pullback.snd t D.targetToBase = pullback.snd t D.sourceToBase ≫ D.map₀)
    (hX : IsAlgebraicSpace B S hS (pullback t D.sourceToBase))
    (hY : IsAlgebraicSpace B S hS (pullback t D.targetToBase)) :
    Q f' ↔ P ((BigFppfOver.toScheme B S hS).map (pullback.snd C.chartMap q)) :=
  ⟨fun h ↦ prop_chartMap_of_holdsOnEveryEtaleChart _ D.sourceToBase D.targetToBase D.map₀
    D.map₀_over t C.sourceChart C.targetChart C.chartMap C.comm C.sourceChart_etale
    C.targetChart_etale p q hp f' hf₁ hf₂ (hQ hX hY f' h), fun h ↦ hQ' hX hY f'
    (holdsOnSurjectiveEtaleChart_of_prop_chartMap _ D.sourceToBase D.targetToBase D.map₀
      D.map₀_over t C.sourceChart C.targetChart C.chartMap C.comm C.sourceChart_etale
      C.targetChart_etale C.sourceChart_surjective p q hp f' hf₁ hf₂ h)⟩

end SituationChartSquare

/-! ### Descending a property of the morphism along the limit -/

/-- The shared argument behind Stacks 07SL, 07SN and 0CN2. Suppose a property `Q` of morphisms
of algebraic spaces over `S` can be read off, for each base change of the given morphism along
a transition morphism, from the property `P` of the morphism of schemes obtained by base
changing the chart morphism `U₀ ⟶ V₀` of a square of affine étale charts, and suppose `P`
descends from a limit of affine schemes to a finite stage under a finiteness hypothesis `R`
stable under base change. If the chart morphism of `f₀` has `R` and the base change of `f₀` to
the limit has `Q`, then its base change to some stage has `Q`. -/
private theorem exists_prop_mapAt_of_prop_mapLimit_situation {D : MorphismDescentSituation B S hS hZ
    I}
    (C : SituationChartSquare D) (Q : ∀ {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, (F ⟶ G) → Prop)
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (R : MorphismProperty Scheme.{u}) [R.IsStableUnderBaseChange]
    (hR : R ((BigFppfOver.toScheme B S hS).map C.chartMap))
    (htransfer : ∀ (B' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (t : B' ⟶ D.base.obj (op D.initial)) (W : BigFppfOver B S hS) (p : yoneda.obj W ⟶ B')
      (q : W ⟶ (BigAffineFppf.inclusion B S hS).obj C.targetObj),
      IsPullback p (yoneda.map q) t C.baseChart →
      ∀ f' : pullback t D.sourceToBase ⟶ pullback t D.targetToBase,
        f' ≫ pullback.fst t D.targetToBase = pullback.fst t D.sourceToBase →
        f' ≫ pullback.snd t D.targetToBase = pullback.snd t D.sourceToBase ≫ D.map₀ →
        IsAlgebraicSpace B S hS (pullback t D.sourceToBase) →
        IsAlgebraicSpace B S hS (pullback t D.targetToBase) →
        (Q f' ↔ P ((BigFppfOver.toScheme B S hS).map (pullback.snd C.chartMap q))))
    (hdescend : ∀ (j₀ : Over (op D.initial)) (X₀ Y₀ : Over (C.diagram.obj j₀)) (f₀ : X₀ ⟶ Y₀),
      CompactSpace X₀.left → QuasiSeparatedSpace X₀.left → CompactSpace Y₀.left →
      QuasiSeparatedSpace Y₀.left → R f₀.left →
      P ((Over.pullback (C.cone.π.app j₀)).map f₀).left →
      ∃ (j : Over (op D.initial)) (g : j ⟶ j₀),
        P ((Over.pullback (C.diagram.map g)).map f₀).left)
    (hlimit : Q D.mapLimit) :
    ∃ (i : I) (hi : D.initial ≤ i), Q (D.mapAt i hi) := by
  let j₀ : Over (op D.initial) := Over.mk (𝟙 (op D.initial))
  let fbase := pullback.snd ((BigFppfOver.toScheme B S hS).map C.chartMap)
    ((BigFppfOver.toScheme B S hS).map (C.stageChart j₀))
  let X₀ : Over (C.diagram.obj j₀) := Over.mk fbase
  let Y₀ : Over (C.diagram.obj j₀) := Over.mk (𝟙 (C.diagram.obj j₀))
  have hX₀aff : IsAffine X₀.left := C.isAffine_pullback_chartMap_stageChart j₀
  have hY₀aff : IsAffine Y₀.left := C.isAffine_diagram_obj j₀
  have hX₀c : CompactSpace X₀.left := Scheme.compactSpace_of_isAffine _
  have hY₀c : CompactSpace Y₀.left := Scheme.compactSpace_of_isAffine _
  have hX₀qs : QuasiSeparatedSpace X₀.left := inferInstance
  have hY₀qs : QuasiSeparatedSpace Y₀.left := inferInstance
  have hf₀R : R (Over.homMk fbase : X₀ ⟶ Y₀).left :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback
      ((BigFppfOver.toScheme B S hS).map C.chartMap)
      ((BigFppfOver.toScheme B S hS).map (C.stageChart j₀))) hR
  have hover : P ((Over.pullback (C.cone.π.app j₀)).map (Over.homMk fbase : X₀ ⟶ Y₀)).left := by
    refine (prop_overPullback_map_left_iff_pullback_snd P fbase (C.cone.π.app j₀)).mpr ?_
    refine (prop_iteratedPullback_snd_iff (BigFppfOver.toScheme B S hS) P C.chartMap
      (C.stageChart j₀) C.limitChart (C.cone.π.app j₀)
      (C.toScheme_cone_π_comp_stageChart j₀)).mpr ?_
    exact (htransfer (limit D.base) (limit.π D.base (op D.initial)) C.bridge.cone.pt
      C.bridge.toLimit C.limitChart C.isPullback_limitChart D.mapLimit D.mapLimit_fst
      D.mapLimit_snd D.sourceLimit_isAlgebraicSpace D.targetLimit_isAlgebraicSpace).mp hlimit
  obtain ⟨j, g, hstage⟩ := hdescend j₀ X₀ Y₀ (Over.homMk fbase) hX₀c hX₀qs hY₀c hY₀qs hf₀R hover
  refine ⟨j.left.unop, leOfHom j.hom.unop, ?_⟩
  refine (htransfer _ _ _ (C.system.stageMap j) (C.stageChart j) (C.isPullback_stageChart j)
    (D.mapAt _ _)
    (D.mapAt_fst _ _) (D.mapAt_snd _ _) (D.sourceAt_isAlgebraicSpace _ _)
    (D.targetAt_isAlgebraicSpace _ _)).mpr ?_
  exact (prop_iteratedPullback_snd_iff (BigFppfOver.toScheme B S hS) P C.chartMap
    (C.stageChart j₀) (C.stageChart j) (C.diagram.map g)
    (C.toScheme_diagram_map_comp_stageChart g)).mp
    ((prop_overPullback_map_left_iff_pullback_snd P fbase (C.diagram.map g)).mp hstage)

/-! ### Reading flatness of a pulled back module on the chart square -/

namespace MorphismDescentSituation

/-- **Stacks 07SL.** In the situation of Stacks 084W, if the base change `f` of `f₀` to the
limit `B` is étale and `f₀` is locally of finite presentation, then the base change `f_i` of
`f₀` to some stage `B_i` is étale.

This is the statement under the chapter's convention of Section 70.2 (tag 07SD), which asks
nothing of the index. -/
theorem exists_isEtale_mapAt_of_siteContainsBaseChangeLimits (D : MorphismDescentSituation B S hS hZ
    I)
    (hconv : SiteContainsBaseChangeLimits B S hS D.base)
    (etale : IsEtale B S hS D.mapLimit) (fp : IsLocallyOfFinitePresentation B S hS D.map₀) :
    ∃ (i : I) (le : D.initial ≤ i), IsEtale B S hS (D.mapAt i le) := by
  obtain ⟨C⟩ := nonempty_situationChartSquare D hconv
  refine exists_prop_mapAt_of_prop_mapLimit_situation C (fun {_ _} f ↦ IsEtale B S hS f)
    (@AlgebraicGeometry.Etale.{u}) (@LocallyOfFinitePresentation)
    (C.locallyOfFinitePresentation_chartMap fp)
    (C.iff_prop_chartMap _ _
      (fun hX hY f' h ↦ (isEtale_iff_holdsOnEveryEtaleChart B S hS hX hY f').mp h)
      fun hX hY f' ⟨_, _, _, _, _, ha, hb, hs, hab, hP⟩ ↦
        (isEtale_iff_exists_etale_chart_square B S hS hX hY f').mpr
          ⟨_, _, _, _, _, hab.symm, hs, ha, hb, hP⟩) ?_ etale
  · intro j₀ X₀ Y₀ f₀ h₁ h₂ h₃ h₄ h₅ h₆
    obtain ⟨_, _, _, _⟩ := C.stage_instances
    have := h₁; have := h₂; have := h₃; have := h₄; have := h₅; have := h₆
    obtain ⟨jj, hjj⟩ :=
      exists_etale_pullback_of_isLimit C.diagram C.cone C.isLimit_cone j₀ X₀ Y₀ f₀
    exact ⟨jj.left, jj.hom, hjj⟩

/-- **Stacks 07SL.** In the situation of Stacks 084W, if the base change `f` of `f₀` to the
limit `B` is étale and `f₀` is locally of finite presentation, then the base change `f_i` of
`f₀` to some stage `B_i` is étale.

This is the statement under smallness of the system for the site, which implies the chapter's
convention; see `exists_isEtale_mapAt_of_siteContainsBaseChangeLimits`. -/
theorem exists_isEtale_mapAt (D : MorphismDescentSituation B S hS hZ I)
    (hb : IsSiteSmall B S hS D.base)
    (etale : IsEtale B S hS D.mapLimit) (fp : IsLocallyOfFinitePresentation B S hS D.map₀) :
    ∃ (i : I) (le : D.initial ≤ i), IsEtale B S hS (D.mapAt i le) :=
  haveI : Nonempty I := ⟨D.initial⟩
  exists_isEtale_mapAt_of_siteContainsBaseChangeLimits D
    (IsSiteSmall.siteContainsBaseChangeLimits B S hS D.base hb) etale fp

/-- **Stacks 07SN.** In the situation of Stacks 084W, if the base change `f` of `f₀` to the
limit `B` is surjective and `f₀` is locally of finite presentation, then the base change `f_i`
of `f₀` to some stage `B_i` is surjective.

This is the statement under the chapter's convention of Section 70.2 (tag 07SD), which asks
nothing of the index. -/
theorem exists_isSurjective_mapAt_of_siteContainsBaseChangeLimits
    (D : MorphismDescentSituation B S hS hZ I) (hconv : SiteContainsBaseChangeLimits B S hS D.base)
        (surjective : IsSurjective B S hS D.mapLimit)
    (fp : IsLocallyOfFinitePresentation B S hS D.map₀) :
    ∃ (i : I) (le : D.initial ≤ i), IsSurjective B S hS (D.mapAt i le) := by
  obtain ⟨C⟩ := nonempty_situationChartSquare D hconv
  have hfibSpace : IsAlgebraicSpace B S hS (pullback D.map₀ C.targetChart) :=
    isAlgebraicSpace_pullback B S hS D.map₀ C.targetChart D.source₀_isAlgebraicSpace
      (isAlgebraicSpace_yoneda B S hS _) D.target₀_isAlgebraicSpace
  have hcover : IsSurjective B S hS C.cover :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS _ hfibSpace _ C.cover).mp
      C.cover_surjective
  have hchart : IsSurjective B S hS C.targetChart :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS _ D.target₀_isAlgebraicSpace _
      C.targetChart).mp C.targetChart_surjective
  refine exists_prop_mapAt_of_prop_mapLimit_situation C (fun {_ _} f ↦ IsSurjective B S hS f)
    (@Surjective.{u}) (@LocallyOfFinitePresentation)
    (C.locallyOfFinitePresentation_chartMap fp) ?_ ?_ surjective
  · intro B' t W p q hp f' hf₁ hf₂ hX hY
    rw [surjective_map_pullback_snd_iff, C.yoneda_map_chartMap]
    exact (isSurjective_chart_iff D.source₀_isAlgebraicSpace D.target₀_isAlgebraicSpace hX hY
      (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _)
      (isAlgebraicSpace_yoneda B S hS W) C.cover
      (isPullback_of_proj_eq D.sourceToBase D.targetToBase D.map₀ D.map₀_over t f' hf₁ hf₂)
      (isPullback_chart_baseChange C.targetChart D.targetToBase t p (yoneda.map q) hp)
      hcover hchart).symm
  · intro j₀ X₀ Y₀ f₀ h₁ h₂ h₃ h₄ h₅ h₆
    obtain ⟨_, _, _, _⟩ := C.stage_instances
    have := h₁; have := h₂; have := h₃; have := h₄; have := h₅; have := h₆
    exact exists_surjective_baseChange_of_surjective_limitBaseChange C.diagram C.cone
      C.isLimit_cone j₀ X₀ Y₀ f₀

/-- **Stacks 07SN.** In the situation of Stacks 084W, if the base change `f` of `f₀` to the
limit `B` is surjective and `f₀` is locally of finite presentation, then the base change `f_i`
of `f₀` to some stage `B_i` is surjective.

This is the statement under smallness of the system for the site, which implies the chapter's
convention; see `exists_isSurjective_mapAt_of_siteContainsBaseChangeLimits`. -/
theorem exists_isSurjective_mapAt
    (D : MorphismDescentSituation B S hS hZ I) (hb : IsSiteSmall B S hS D.base) (surjective :
        IsSurjective B S hS D.mapLimit)
    (fp : IsLocallyOfFinitePresentation B S hS D.map₀) :
    ∃ (i : I) (le : D.initial ≤ i), IsSurjective B S hS (D.mapAt i le) :=
  haveI : Nonempty I := ⟨D.initial⟩
  exists_isSurjective_mapAt_of_siteContainsBaseChangeLimits D
    (IsSiteSmall.siteContainsBaseChangeLimits B S hS D.base hb) surjective fp

/-- **Stacks 0CN2.** In the situation of Stacks 084W, if the base change `f` of `f₀` to the
limit `B` is smooth and `f₀` is locally of finite presentation, then the base change `f_i` of
`f₀` to some stage `B_i` is smooth.

This is the statement under the chapter's convention of Section 70.2 (tag 07SD), which asks
nothing of the index. -/
theorem exists_isSmooth_mapAt_of_siteContainsBaseChangeLimits (D : MorphismDescentSituation B S hS
    hZ I)
    (hconv : SiteContainsBaseChangeLimits B S hS D.base)
    (smooth : IsSmooth B S hS D.mapLimit) (fp : IsLocallyOfFinitePresentation B S hS D.map₀) :
    ∃ (i : I) (le : D.initial ≤ i), IsSmooth B S hS (D.mapAt i le) := by
  obtain ⟨C⟩ := nonempty_situationChartSquare D hconv
  have : MorphismProperty.RespectsIso (@Smooth.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine exists_prop_mapAt_of_prop_mapLimit_situation C (fun {_ _} f ↦ IsSmooth B S hS f)
    (@Smooth.{u}) (@LocallyOfFinitePresentation)
    (C.locallyOfFinitePresentation_chartMap fp)
    (C.iff_prop_chartMap _ _ (fun _ _ _ h ↦ h) fun hX hY f' ↦
      (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS (@Smooth.{u})
        Smooth.isEtaleLocalOnSourceAndTarget hX hY f').mpr) ?_ smooth
  · intro j₀ X₀ Y₀ f₀ h₁ h₂ h₃ h₄ h₅ h₆
    obtain ⟨_, _, _, _⟩ := C.stage_instances
    have := h₁; have := h₂; have := h₃; have := h₄; have := h₅; have := h₆
    exact exists_smooth_baseChange_of_smooth_limitBaseChange C.diagram C.cone j₀ X₀ Y₀ f₀
      C.isLimit_cone

/-- **Stacks 0CN2.** In the situation of Stacks 084W, if the base change `f` of `f₀` to the
limit `B` is smooth and `f₀` is locally of finite presentation, then the base change `f_i` of
`f₀` to some stage `B_i` is smooth.

This is the statement under smallness of the system for the site, which implies the chapter's
convention; see `exists_isSmooth_mapAt_of_siteContainsBaseChangeLimits`. -/
theorem exists_isSmooth_mapAt (D : MorphismDescentSituation B S hS hZ I)
    (hb : IsSiteSmall B S hS D.base)
    (smooth : IsSmooth B S hS D.mapLimit) (fp : IsLocallyOfFinitePresentation B S hS D.map₀) :
    ∃ (i : I) (le : D.initial ≤ i), IsSmooth B S hS (D.mapAt i le) :=
  haveI : Nonempty I := ⟨D.initial⟩
  exists_isSmooth_mapAt_of_siteContainsBaseChangeLimits D
    (IsSiteSmall.siteContainsBaseChangeLimits B S hS D.base hb) smooth fp

/-- **Stacks 08K0**, flatness of the morphism. In the situation of Stacks 084W, if `f₀` is locally
of finite presentation and its base change `f : X ⟶ Y` to the limit is flat, then its base change
`f_i : X_i ⟶ Y_i` to some stage `i ≥ 0` is flat.

This is the statement under the chapter's convention of Section 70.2 (tag 07SD), which asks
nothing of the index. -/
@[stacks 08K0 "in particular: flatness of the morphism, under the convention of Section 70.2 \
  (tag 07SD) and with no condition on the index"]
theorem exists_isFlat_mapAt_of_siteContainsBaseChangeLimits
    (D : MorphismDescentSituation B S hS hZ I) (hconv : SiteContainsBaseChangeLimits B S hS D.base)
        (flat : IsFlat B S hS D.mapLimit)
    (fp : IsLocallyOfFinitePresentation B S hS D.map₀) :
    ∃ (i : I) (le : D.initial ≤ i), IsFlat B S hS (D.mapAt i le) := by
  obtain ⟨C⟩ := nonempty_situationChartSquare D hconv
  have : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine exists_prop_mapAt_of_prop_mapLimit_situation C (fun {_ _} f ↦ IsFlat B S hS f)
    (@_root_.AlgebraicGeometry.Flat.{u}) (@LocallyOfFinitePresentation)
    (C.locallyOfFinitePresentation_chartMap fp)
    (C.iff_prop_chartMap _ _ (fun _ _ _ h ↦ h) fun hX hY f' ↦
      (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS (@_root_.AlgebraicGeometry.Flat.{u})
        _root_.AlgebraicGeometry.Flat.isEtaleLocalOnSourceAndTarget hX hY f').mpr) ?_ flat
  · intro j₀ X₀ Y₀ f₀ h₁ h₂ h₃ h₄ h₅ h₆
    obtain ⟨_, _, _, _⟩ := C.stage_instances
    have := h₁; have := h₂; have := h₃; have := h₄; have := h₅; have := h₆
    exact exists_flat_baseChange_of_limitBaseChange C.diagram C.cone j₀ X₀ Y₀ f₀ C.isLimit_cone

/-- **Stacks 08K0**, flatness of the morphism. In the situation of Stacks 084W, if `f₀` is locally
of finite presentation and its base change `f : X ⟶ Y` to the limit is flat, then its base change
`f_i : X_i ⟶ Y_i` to some stage `i ≥ 0` is flat.

This is the statement under smallness of the system for the site, which implies the chapter's
convention; see `exists_isFlat_mapAt_of_siteContainsBaseChangeLimits`. -/
theorem exists_isFlat_mapAt
    (D : MorphismDescentSituation B S hS hZ I) (hb : IsSiteSmall B S hS D.base) (flat : IsFlat B S
        hS D.mapLimit)
    (fp : IsLocallyOfFinitePresentation B S hS D.map₀) :
    ∃ (i : I) (le : D.initial ≤ i), IsFlat B S hS (D.mapAt i le) :=
  haveI : Nonempty I := ⟨D.initial⟩
  exists_isFlat_mapAt_of_siteContainsBaseChangeLimits D
    (IsSiteSmall.siteContainsBaseChangeLimits B S hS D.base hb) flat fp

/-- **Stacks 084X.** In the situation of Stacks 084W, if the base change `f` of `f₀` to the
limit `B` is universally injective and `f₀` is locally of finite type, then the base change
`f_i` of `f₀` to some stage `B_i` is universally injective.

This is the statement under the chapter's convention of Section 70.2 (tag 07SD), which asks
nothing of the index. -/
theorem exists_universallyInjective_mapAt_of_siteContainsBaseChangeLimits
    (D : MorphismDescentSituation B S hS hZ I)
    (hconv : SiteContainsBaseChangeLimits B S hS D.base)
    (injective : UniversallyInjective B S hS D.mapLimit)
    (ft : IsLocallyOfFiniteType B S hS D.map₀) :
    ∃ (i : I) (le : D.initial ≤ i), UniversallyInjective B S hS (D.mapAt i le) := by
  let Δ : MorphismDescentSituation B S hS hZ I :=
    { D with
      target₀ := pullback D.map₀ D.map₀
      targetToBase := pullback.fst D.map₀ D.map₀ ≫ D.sourceToBase
      map₀ := pullback.diagonal D.map₀
      map₀_over := by rw [pullback.diagonal_fst_assoc]
      target₀_isAlgebraicSpace :=
        isAlgebraicSpace_pullback B S hS D.map₀ D.map₀ D.source₀_isAlgebraicSpace
          D.source₀_isAlgebraicSpace D.target₀_isAlgebraicSpace
      target₀_quasiCompact :=
        isQuasiCompactSpace_pullback B S hS hZ D.map₀ D.map₀ D.source₀_isAlgebraicSpace
          D.target₀_isAlgebraicSpace D.source₀_quasiCompact D.source₀_quasiCompact
          D.target₀_quasiSeparated
      target₀_quasiSeparated :=
        isAbsolutelyQuasiSeparated_pullback B S hS hZ D.map₀ D.map₀
          D.source₀_isAlgebraicSpace D.source₀_isAlgebraicSpace D.target₀_isAlgebraicSpace
          D.source₀_quasiSeparated D.source₀_quasiSeparated }
  have hdiag₀ : IsLocallyOfFinitePresentation B S hS Δ.map₀ :=
    isLocallyOfFinitePresentation_pullbackDiagonal B S hS D.map₀ D.source₀_isAlgebraicSpace
      D.target₀_isAlgebraicSpace ft
  have hdiagLim : IsSurjective B S hS Δ.mapLimit :=
    (isSurjective_baseChange_diagonal_iff B S hS D.sourceToBase D.targetToBase
      (limit.π D.base (op D.initial)) D.map₀ D.map₀_over D.mapLimit D.mapLimit_fst
      D.mapLimit_snd).mpr
      (isSurjective_diagonal_of_universallyInjective B S hS D.sourceLimit_isAlgebraicSpace
        D.mapLimit injective)
  obtain ⟨i, hi, hsurj⟩ := exists_isSurjective_mapAt_of_siteContainsBaseChangeLimits Δ hconv
      hdiagLim hdiag₀
  refine ⟨i, hi, universallyInjective_of_isSurjective_diagonal B S hS (D.mapAt i hi) ?_⟩
  exact (isSurjective_baseChange_diagonal_iff B S hS D.sourceToBase D.targetToBase
    (D.baseAtToInitial i hi) D.map₀ D.map₀_over (D.mapAt i hi) (D.mapAt_fst i hi)
    (D.mapAt_snd i hi)).mp hsurj

/-- **Stacks 084X.** In the situation of Stacks 084W, if the base change `f` of `f₀` to the
limit `B` is universally injective and `f₀` is locally of finite type, then the base change
`f_i` of `f₀` to some stage `B_i` is universally injective.

This is the statement under smallness of the system for the site, which implies the chapter's
convention; see `exists_universallyInjective_mapAt_of_siteContainsBaseChangeLimits`. -/
theorem exists_universallyInjective_mapAt
    (D : MorphismDescentSituation B S hS hZ I)
    (hb : IsSiteSmall B S hS D.base)
    (injective : UniversallyInjective B S hS D.mapLimit)
    (ft : IsLocallyOfFiniteType B S hS D.map₀) :
    ∃ (i : I) (le : D.initial ≤ i), UniversallyInjective B S hS (D.mapAt i le) :=
  haveI : Nonempty I := ⟨D.initial⟩
  exists_universallyInjective_mapAt_of_siteContainsBaseChangeLimits D
    (IsSiteSmall.siteContainsBaseChangeLimits B S hS D.base hb) injective ft

/-- **Stacks 0D4K.** In the situation of Stacks 084W, if the base change `f` of `f₀` to the
limit `B` has relative dimension at most `d` and `f₀` is locally of finite type, then the base
change `f_i` of `f₀` to some stage `B_i` has relative dimension at most `d`.

This is the statement under the chapter's convention of Section 70.2 (tag 07SD), which asks
nothing of the index: the situation `D` carries no bound on the size of `I`, and the convention
is the hypothesis `hconv`, `AlgebraicGeometry.Space.SiteContainsBaseChangeLimits` for the system
`(B_i)`. -/
@[stacks 0D4K]
theorem exists_hasRelativeDimensionLE_mapAt_of_siteContainsBaseChangeLimits (D :
    MorphismDescentSituation B S hS hZ I)
    (hconv : SiteContainsBaseChangeLimits B S hS D.base) (d : ℕ)
    (dimension : HasRelativeDimensionLE d B S hS D.mapLimit)
    (ft : IsLocallyOfFiniteType B S hS D.map₀) :
    ∃ (i : I) (le : D.initial ≤ i), HasRelativeDimensionLE d B S hS (D.mapAt i le) := by
  obtain ⟨C⟩ := nonempty_situationChartSquare D hconv
  have hchartFt : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map C.chartMap) :=
    ft _ _ C.sourceChart C.targetChart C.chartMap C.sourceChart_etale C.targetChart_etale C.comm
  refine exists_prop_mapAt_of_prop_mapLimit_situation C (fun {_ _} f ↦ HasRelativeDimensionLE d B S
      hS f)
    (fiberDimensionLE d) (@LocallyOfFiniteType) hchartFt
    (C.iff_prop_chartMap _ _
      (fun _ _ f' ↦ fiberDimensionLE_chartMap_of_hasRelativeDimensionLE B S hS f' d)
      fun hX _ f' ↦ hasRelativeDimensionLE_of_holdsOnSurjectiveEtaleChart B S hS hX f' d)
    ?_ dimension
  · intro j₀ X₀ Y₀ f₀ h₁ h₂ h₃ h₄ h₅ h₆
    obtain ⟨_, _, _, _⟩ := C.stage_instances
    have := h₁; have := h₂; have := h₃; have := h₄; have := h₅
    exact exists_fiberDimensionLE_baseChange_of_limitBaseChange C.diagram C.isLimit_cone j₀
      X₀ Y₀ f₀ d h₆

/-- **Stacks 0D4K.** In the situation of Stacks 084W, if the base change `f` of `f₀` to the
limit `B` has relative dimension at most `d` and `f₀` is locally of finite type, then the base
change `f_i` of `f₀` to some stage `B_i` has relative dimension at most `d`.

This is the statement under smallness of the system for the site, which implies the chapter's
convention; see `exists_hasRelativeDimensionLE_mapAt_of_siteContainsBaseChangeLimits`. -/
theorem exists_hasRelativeDimensionLE_mapAt (D : MorphismDescentSituation B S hS hZ I)
    (hb : IsSiteSmall B S hS D.base) (d : ℕ)
    (dimension : HasRelativeDimensionLE d B S hS D.mapLimit)
    (ft : IsLocallyOfFiniteType B S hS D.map₀) :
    ∃ (i : I) (le : D.initial ≤ i), HasRelativeDimensionLE d B S hS (D.mapAt i le) :=
  haveI : Nonempty I := ⟨D.initial⟩
  exists_hasRelativeDimensionLE_mapAt_of_siteContainsBaseChangeLimits D
    (IsSiteSmall.siteContainsBaseChangeLimits B S hS D.base hb) d dimension ft

/-! ### The covariant indexing of Stacks 07SK

Stacks 084W, and every statement above, indexes the system by a directed preorder `I` and carries
it as the *contravariant* diagram `base : Iᵒᵖ ⥤ …`, reading a stage beyond the distinguished one
as an inequality `0 ≤ i`. The library's Stacks 07SK —
`AlgebraicGeometry.Space.exists_model_of_finitePresentation` and its fullness and faithfulness
companions — instead consumes a *cofiltered category* together with a *covariant* diagram out of
it, and states its conclusions over a morphism `j ⟶ i` of that category.

These are two readings of one and the same system: `base` is already a covariant functor on the
category `Iᵒᵖ`, which is cofiltered because a directed preorder is filtered. The declarations
below record that, and restate Stacks 0CN2 over a morphism of `Iᵒᵖ` rather than over an
inequality in `I`, so that it composes with Stacks 07SK without either result being reindexed.
-/

/-- The index category of a morphism descent system, read covariantly, is cofiltered. This is the
indexing the library's Stacks 07SK consumes: a directed preorder is filtered, so its opposite is
cofiltered, and the distinguished stage makes the index nonempty. -/
theorem isCofiltered_op (D : MorphismDescentSituation B S hS hZ I) : IsCofiltered Iᵒᵖ :=
  haveI : Nonempty I := ⟨D.initial⟩
  inferInstance

/-- A morphism of the index category `Iᵒᵖ` into the distinguished stage induces exactly the
transition morphism of the inequality it encodes. The morphisms of a preorder read as a category
are unique, so there is nothing to choose. -/
theorem base_map_eq_baseAtToInitial (D : MorphismDescentSituation B S hS hZ I) {j : Iᵒᵖ}
    (g : j ⟶ op D.initial) :
    D.base.map g = D.baseAtToInitial j.unop (leOfHom g.unop) :=
  congrArg D.base.map (congrArg Quiver.Hom.op (homOfLE_leOfHom g.unop)).symm

/-- **Stacks 0CN2 in the covariant indexing of Stacks 07SK.** In the situation of Stacks 084W, if
the base change `f` of `f₀` to the limit `B` is smooth and `f₀` is locally of finite presentation,
then there is a morphism `j ⟶ 0` of the cofiltered index category `Iᵒᵖ` along which the base
change of `f₀` is smooth.

This is `AlgebraicGeometry.Space.MorphismDescentSystem.exists_isSmooth_mapAt` with its conclusion
read over a morphism of `Iᵒᵖ` instead of an inequality of `I`; the transition morphism is the same
one, by `AlgebraicGeometry.Space.MorphismDescentSystem.base_map_eq_baseAtToInitial`. It is the
shape in which the conclusions of Stacks 07SK are stated, so the two can be used together.

This is the statement under the chapter's convention of Section 70.2 (tag 07SD), which asks
nothing of the index. -/
theorem exists_isSmooth_mapAt_op_of_siteContainsBaseChangeLimits (D : MorphismDescentSituation B S
    hS hZ I)
    (hconv : SiteContainsBaseChangeLimits B S hS D.base)
    (smooth : IsSmooth B S hS D.mapLimit) (fp : IsLocallyOfFinitePresentation B S hS D.map₀) :
    ∃ (j : Iᵒᵖ) (g : j ⟶ op D.initial),
      IsSmooth B S hS (D.mapAt j.unop (leOfHom g.unop)) := by
  obtain ⟨i, hi, h⟩ := exists_isSmooth_mapAt_of_siteContainsBaseChangeLimits D hconv smooth fp
  exact ⟨op i, (homOfLE hi).op, h⟩

/-- **Stacks 0CN2 in the covariant indexing of Stacks 07SK.** In the situation of Stacks 084W, if
the base change `f` of `f₀` to the limit `B` is smooth and `f₀` is locally of finite presentation,
then there is a morphism `j ⟶ 0` of the cofiltered index category `Iᵒᵖ` along which the base
change of `f₀` is smooth.

This is `AlgebraicGeometry.Space.MorphismDescentSystem.exists_isSmooth_mapAt` with its conclusion
read over a morphism of `Iᵒᵖ` instead of an inequality of `I`; the transition morphism is the same
one, by `AlgebraicGeometry.Space.MorphismDescentSystem.base_map_eq_baseAtToInitial`. It is the
shape in which the conclusions of Stacks 07SK are stated, so the two can be used together.

This is the statement under smallness of the system for the site, which implies the chapter's
convention; see `exists_isSmooth_mapAt_op_of_siteContainsBaseChangeLimits`. -/
theorem exists_isSmooth_mapAt_op (D : MorphismDescentSituation B S hS hZ I)
    (hb : IsSiteSmall B S hS D.base)
    (smooth : IsSmooth B S hS D.mapLimit) (fp : IsLocallyOfFinitePresentation B S hS D.map₀) :
    ∃ (j : Iᵒᵖ) (g : j ⟶ op D.initial),
      IsSmooth B S hS (D.mapAt j.unop (leOfHom g.unop)) :=
  haveI : Nonempty I := ⟨D.initial⟩
  exists_isSmooth_mapAt_op_of_siteContainsBaseChangeLimits D
    (IsSiteSmall.siteContainsBaseChangeLimits B S hS D.base hb) smooth fp

end MorphismDescentSituation

end SituationChartData

/-! ### The affine chart square of a morphism descent system -/

section ChartData

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]

/-- A square of affine étale charts for a morphism descent system, that of the morphism descent
situation it determines. -/
private abbrev ChartSquare (D : MorphismDescentSystem B S hS hZ I) :=
  SituationChartSquare D.toSituation

/-- **Stacks 07SL, 07SN and 0CN2**, the choice of charts the three proofs begin with. A
quasi-compact quasi-separated morphism descent system admits a square of affine étale
charts. -/
private theorem nonempty_chartSquare (D : MorphismDescentSystem B S hS hZ I) :
    Nonempty (ChartSquare D) :=
  haveI : Nonempty I := ⟨D.initial⟩
  nonempty_situationChartSquare D.toSituation
    (IsSiteSmall.siteContainsBaseChangeLimits B S hS D.base (IsSiteSmall.of_lt_cof_op D.indexSize))

namespace ChartSquare

/-- The chart `U₀ ⟶ X₀` of the source, as an object of the small étale site of `X₀`. -/
private noncomputable def sourceSmallEtale {D : MorphismDescentSystem B S hS hZ I}
    (C : ChartSquare D) : SmallEtale B S hS D.source₀ :=
  ⟨CostructuredArrow.mk C.sourceChart, C.sourceChart_etale⟩

end ChartSquare

/-! ### Reading flatness of a pulled back module on the chart square -/

/-- Let `t : B' ⟶ B₀` be a base change of the distinguished stage represented over the chart
`V₀` of the target by a morphism `q : W ⟶ V₀` of the site, and let `f'` be the base change of
`f₀` along `t`. A quasi-coherent `𝒪_{X₀}`-module `F₀` pulled back to `B' ×_{B₀} X₀` is flat over
`B' ×_{B₀} Y₀` exactly when the pullback of `F₀|_{U₀}` to `U₀ ×_{V₀} W` is flat over `W`. The
chart of `B' ×_{B₀} X₀` obtained by base change from `U₀ ⟶ X₀` is surjective, so the one chart
square suffices, by Stacks 05VU. -/
private theorem isFlatOver_modulePullback_baseChange_iff {D : MorphismDescentSystem B S hS hZ I}
    (C : ChartSquare D) (F₀ : Modules.{u, u} B S hS D.source₀ D.source₀_isAlgebraicSpace)
    [F₀.IsQuasicoherentOnSite] (B' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (t : B' ⟶ D.base.obj (op D.initial)) (W : BigFppfOver B S hS) (p : yoneda.obj W ⟶ B')
    (q : W ⟶ (BigAffineFppf.inclusion B S hS).obj C.targetObj)
    (hp : IsPullback p (yoneda.map q) t C.baseChart)
    (f' : pullback t D.sourceToBase ⟶ pullback t D.targetToBase)
    (hf₁ : f' ≫ pullback.fst t D.targetToBase = pullback.fst t D.sourceToBase)
    (hf₂ : f' ≫ pullback.snd t D.targetToBase = pullback.snd t D.sourceToBase ≫ D.map₀)
    (hX : IsAlgebraicSpace B S hS (pullback t D.sourceToBase))
    (hY : IsAlgebraicSpace B S hS (pullback t D.targetToBase)) :
    IsFlatOver B S hS hX f' ((modulePullback B S hS
      (ObjectProperty.homMk (pullback.snd t D.sourceToBase) :
        (⟨pullback t D.sourceToBase, hX⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨D.source₀, D.source₀_isAlgebraicSpace⟩)).obj F₀) ↔
      _root_.AlgebraicGeometry.IsFlatOver
        ((BigFppfOver.toScheme B S hS).map (pullback.snd C.chartMap q)).toLRSHom.toShHom
        ((Scheme.Modules.pullback
          ((BigFppfOver.toScheme B S hS).map (pullback.fst C.chartMap q))).obj
          (restrictToChart B S hS D.source₀_isAlgebraicSpace F₀ C.sourceSmallEtale)) := by
  obtain ⟨a', b', sa, sb, comm⟩ := exists_chart_square_baseChange D.sourceToBase D.targetToBase
    D.map₀ D.map₀_over t C.sourceChart C.targetChart (yoneda.map C.chartMap) C.comm p
    (yoneda.map q) hp ((IsPullback.of_hasPullback C.chartMap q).map yoneda) f' hf₁ hf₂
  let π : (⟨pullback t D.sourceToBase, hX⟩ : AlgebraicSpaces B S hS) ⟶
      ⟨D.source₀, D.source₀_isAlgebraicSpace⟩ :=
    ObjectProperty.homMk (pullback.snd t D.sourceToBase)
  let U : SmallEtale B S hS (pullback t D.sourceToBase) :=
    ⟨CostructuredArrow.mk a', MorphismProperty.of_isPullback sa C.sourceChart_etale⟩
  let V : SmallEtale B S hS (pullback t D.targetToBase) :=
    ⟨CostructuredArrow.mk b', MorphismProperty.of_isPullback sb C.targetChart_etale⟩
  let d : ChartDiagram B S hS (pullback t D.sourceToBase) (pullback t D.targetToBase) f' :=
    { U := U, V := V, g := pullback.snd C.chartMap q, comm := comm.symm }
  have qc : ((modulePullback B S hS π).obj F₀).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS π F₀ inferInstance
  have hd : IsFlatOverOnChartDiagram B S hS hX ((modulePullback B S hS π).obj F₀) d ↔
      _root_.AlgebraicGeometry.IsFlatOver
        ((BigFppfOver.toScheme B S hS).map (pullback.snd C.chartMap q)).toLRSHom.toShHom
        ((Scheme.Modules.pullback
          ((BigFppfOver.toScheme B S hS).map (pullback.fst C.chartMap q))).obj
          (restrictToChart B S hS D.source₀_isAlgebraicSpace F₀ C.sourceSmallEtale)) :=
    (_root_.AlgebraicGeometry.isFlatOver_iff_of_iso _
      (restrictToChartBaseChangeIso B S hS π F₀ inferInstance C.sourceSmallEtale U
        (pullback.fst C.chartMap q) sa.w)).symm
  refine ⟨fun h ↦ hd.mp (h d), fun h ↦ ?_⟩
  have hs : Function.Surjective (pointsMap B S hS (yoneda.obj d.U.obj.left) d.U.obj.hom) :=
    (surjective_iff_surjective_pointsMap B S hS _ hX _ a').mp
      (MorphismProperty.of_isPullback sa C.sourceChart_surjective)
  have key := (isFlatOver_iff_forall_isFlatOverAtGeometricPoint B S hS
    (Xs := ⟨pullback t D.sourceToBase, hX⟩) (Ys := ⟨pullback t D.targetToBase, hY⟩)
    (ObjectProperty.homMk f') ((modulePullback B S hS π).obj F₀)).mpr fun xbar ↦
      isFlatOver_of_isFlatOverOnChartDiagram_of_surjective B S hS
        (Xs := ⟨pullback t D.sourceToBase, hX⟩) (Ys := ⟨pullback t D.targetToBase, hY⟩)
        (ObjectProperty.homMk f') ((modulePullback B S hS π).obj F₀) d hs (hd.mpr h) xbar
  exact key

namespace MorphismDescentSystem

/-- **Stacks 07SL.** In the situation of Stacks 084W, if the base change `f` of `f₀` to the
limit `B` is étale and `f₀` is locally of finite presentation, then the base change `f_i` of
`f₀` to some stage `B_i` is étale. -/
@[stacks 07SL, ega "IV 17.7.8" "(ii) étale"]
theorem exists_isEtale_mapAt (D : MorphismDescentSystem B S hS hZ I)
    (etale : IsEtale B S hS D.mapLimit) (fp : IsLocallyOfFinitePresentation B S hS D.map₀) :
    ∃ (i : I) (le : D.initial ≤ i), IsEtale B S hS (D.mapAt i le) :=
  D.toSituation.exists_isEtale_mapAt (IsSiteSmall.of_lt_cof_op D.indexSize) etale fp

/-- **Stacks 07SN.** In the situation of Stacks 084W, if the base change `f` of `f₀` to the
limit `B` is surjective and `f₀` is locally of finite presentation, then the base change `f_i`
of `f₀` to some stage `B_i` is surjective. -/
@[stacks 07SN]
theorem exists_isSurjective_mapAt
    (D : MorphismDescentSystem B S hS hZ I) (surjective : IsSurjective B S hS D.mapLimit)
    (fp : IsLocallyOfFinitePresentation B S hS D.map₀) :
    ∃ (i : I) (le : D.initial ≤ i), IsSurjective B S hS (D.mapAt i le) :=
  D.toSituation.exists_isSurjective_mapAt (IsSiteSmall.of_lt_cof_op D.indexSize) surjective fp

/-- **Stacks 0CN2.** In the situation of Stacks 084W, if the base change `f` of `f₀` to the
limit `B` is smooth and `f₀` is locally of finite presentation, then the base change `f_i` of
`f₀` to some stage `B_i` is smooth. -/
@[stacks 0CN2, ega "IV 17.12.6" "f smooth ⇒ ∃λ", ega "IV 17.7.8" "(ii) smooth"]
theorem exists_isSmooth_mapAt (D : MorphismDescentSystem B S hS hZ I)
    (smooth : IsSmooth B S hS D.mapLimit) (fp : IsLocallyOfFinitePresentation B S hS D.map₀) :
    ∃ (i : I) (le : D.initial ≤ i), IsSmooth B S hS (D.mapAt i le) :=
  D.toSituation.exists_isSmooth_mapAt (IsSiteSmall.of_lt_cof_op D.indexSize) smooth fp

/-- **Stacks 08K0**, flatness of the morphism. In the situation of Stacks 084W, if `f₀` is locally
of finite presentation and its base change `f : X ⟶ Y` to the limit is flat, then its base change
`f_i : X_i ⟶ Y_i` to some stage `i ≥ 0` is flat.

The index of the system is bounded by `MorphismDescentSystem.indexSize`; the statement under the
chapter's convention 07SD, with no condition on the index, is
`MorphismDescentSituation.exists_isFlat_mapAt_of_siteContainsBaseChangeLimits`. -/
@[stacks 08K0 "in particular: flatness of the morphism, with the index bounded by indexSize",
  ega "IV 11.2.6" "F = O_X case"]
theorem exists_isFlat_mapAt
    (D : MorphismDescentSystem B S hS hZ I) (flat : IsFlat B S hS D.mapLimit)
    (fp : IsLocallyOfFinitePresentation B S hS D.map₀) :
    ∃ (i : I) (le : D.initial ≤ i), IsFlat B S hS (D.mapAt i le) :=
  D.toSituation.exists_isFlat_mapAt (IsSiteSmall.of_lt_cof_op D.indexSize) flat fp

/-- **Stacks 08K0**, flatness of a module. In the situation of Stacks 084W, let `F₀` be a
quasi-coherent `𝒪_{X₀}`-module, with pullbacks `F_i` to `X_i` and `F` to `X`. If `F` is flat over
`Y`, `F₀` is of finite presentation and `f₀` is locally of finite presentation, then `F_i` is flat
over `Y_i` for some stage `i ≥ 0`.

The index of the system is bounded by `MorphismDescentSystem.indexSize`; the statement with no
condition on the index is
`AlgebraicGeometry.Space.exists_isFlatOver_baseChange_of_chartLimitsInSite`. -/
@[stacks 08K0 "flatness of a module, with the index bounded by indexSize"]
theorem exists_isFlatOver_mapAt (D : MorphismDescentSystem B S hS hZ I)
    (F₀ : Modules.{u, u} B S hS D.source₀ D.source₀_isAlgebraicSpace)
    [F₀.IsQuasicoherentOnSite] [F₀.IsFinitePresentationOnSite]
    (flat : IsFlatOver B S hS D.sourceLimit_isAlgebraicSpace D.mapLimit
      ((modulePullback B S hS (ObjectProperty.homMk
        (pullback.snd (limit.π D.base (op D.initial)) D.sourceToBase) :
          (⟨D.sourceLimit, D.sourceLimit_isAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨D.source₀, D.source₀_isAlgebraicSpace⟩)).obj F₀))
    (fp : IsLocallyOfFinitePresentation B S hS D.map₀) :
    ∃ (i : I) (le : D.initial ≤ i), IsFlatOver B S hS (D.sourceAt_isAlgebraicSpace i le)
      (D.mapAt i le) ((modulePullback B S hS (ObjectProperty.homMk
        (pullback.snd (D.baseAtToInitial i le) D.sourceToBase) :
          (⟨D.sourceAt i le, D.sourceAt_isAlgebraicSpace i le⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨D.source₀, D.source₀_isAlgebraicSpace⟩)).obj F₀) := by
  obtain ⟨C⟩ := nonempty_chartSquare D
  let H := BigFppfOver.toScheme B S hS
  let M : (H.obj ((BigAffineFppf.inclusion B S hS).obj C.sourceObj)).Modules :=
    restrictToChart B S hS D.source₀_isAlgebraicSpace F₀ C.sourceSmallEtale
  have : M.IsQuasicoherent :=
    isQuasicoherent_restrictToChart B S hS ⟨D.source₀, D.source₀_isAlgebraicSpace⟩ F₀
      inferInstance C.sourceSmallEtale
  have : M.IsFinitePresentation :=
    isFinitePresentation_restrictToChart B S hS ⟨D.source₀, D.source₀_isAlgebraicSpace⟩ F₀
      inferInstance inferInstance C.sourceSmallEtale
  let j₀ : Over (op D.initial) := Over.mk (𝟙 (op D.initial))
  let st₀ := H.map (C.stageChart j₀)
  let g := pullback.snd (H.map C.chartMap) st₀
  let N := (Scheme.Modules.pullback (pullback.fst (H.map C.chartMap) st₀)).obj M
  have key : ∀ {W : BigFppfOver B S hS} (s : H.obj W ⟶ C.diagram.obj j₀)
      (q : W ⟶ (BigAffineFppf.inclusion B S hS).obj C.targetObj), s ≫ st₀ = H.map q →
      (_root_.AlgebraicGeometry.IsFlatOver (pullback.snd g s).toLRSHom.toShHom
          ((Scheme.Modules.pullback (pullback.fst g s)).obj N) ↔
        _root_.AlgebraicGeometry.IsFlatOver (H.map (pullback.snd C.chartMap q)).toLRSHom.toShHom
          ((Scheme.Modules.pullback (H.map (pullback.fst C.chartMap q))).obj M)) := by
    intro W s q hs
    have h₁ := (IsPullback.of_hasPullback g s).paste_horiz
      (IsPullback.of_hasPullback (H.map C.chartMap) st₀)
    rw [hs] at h₁
    exact (_root_.AlgebraicGeometry.isFlatOver_iff_of_iso _
      ((schemeModulePullbackCompIso (pullback.fst g s) (pullback.fst (H.map C.chartMap) st₀)).app
        M)).trans (isFlatOver_modulePullback_iff_of_isPullback h₁
          ((IsPullback.of_hasPullback C.chartMap q).map H) M)
  have hlimit := (key (C.cone.π.app j₀) C.limitChart (C.toScheme_cone_π_comp_stageChart j₀)).mpr
    ((isFlatOver_modulePullback_baseChange_iff C F₀ (limit D.base) (limit.π D.base (op D.initial))
      C.bridge.cone.pt C.bridge.toLimit C.limitChart C.isPullback_limitChart D.mapLimit
      D.mapLimit_fst D.mapLimit_snd D.sourceLimit_isAlgebraicSpace
      D.targetLimit_isAlgebraicSpace).mp flat)
  obtain ⟨_, _, _, _⟩ := C.stage_instances
  have : IsAffine (pullback (H.map C.chartMap) st₀) :=
    C.isAffine_pullback_chartMap_stageChart j₀
  have : CompactSpace ↥(pullback (H.map C.chartMap) st₀) := Scheme.compactSpace_of_isAffine _
  have : LocallyOfFinitePresentation g :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback (H.map C.chartMap) st₀)
      (C.locallyOfFinitePresentation_chartMap fp)
  have : N.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ M
  have : SheafOfModules.IsFinitePresentation (R := structureSheafRing
      (H.obj ((BigAffineFppf.inclusion B S hS).obj C.sourceObj)).toRingedSpace) M := ‹_›
  have : N.IsFinitePresentation :=
    Stacks.SheafOfModules.modulePullback_isFinitePresentation
      (pullback.fst (H.map C.chartMap) st₀).toLRSHom.toShHom M
  obtain ⟨j, e, hj⟩ := exists_isFlatOver_modulePullback_pullback_snd C.diagram C.cone
    C.isLimit_cone j₀ g N hlimit
  exact ⟨j.left.unop, leOfHom j.hom.unop,
    (isFlatOver_modulePullback_baseChange_iff C F₀ _ _ _ (C.system.stageMap j) (C.stageChart j)
      (C.isPullback_stageChart j) (D.mapAt _ _) (D.mapAt_fst _ _) (D.mapAt_snd _ _)
      (D.sourceAt_isAlgebraicSpace _ _) (D.targetAt_isAlgebraicSpace _ _)).mpr
      ((key (C.diagram.map e) (C.stageChart j) (C.toScheme_diagram_map_comp_stageChart e)).mp hj)⟩

/-- **Stacks 084X.** In the situation of Stacks 084W, if the base change `f` of `f₀` to the
limit `B` is universally injective and `f₀` is locally of finite type, then the base change
`f_i` of `f₀` to some stage `B_i` is universally injective. -/
@[stacks 084X]
theorem exists_universallyInjective_mapAt
    (D : MorphismDescentSystem B S hS hZ I)
    (injective : UniversallyInjective B S hS D.mapLimit)
    (ft : IsLocallyOfFiniteType B S hS D.map₀) :
    ∃ (i : I) (le : D.initial ≤ i), UniversallyInjective B S hS (D.mapAt i le) :=
  D.toSituation.exists_universallyInjective_mapAt (IsSiteSmall.of_lt_cof_op D.indexSize) injective
      ft

/-- **Stacks 0D4K for an index bounded in size.** In the situation of Stacks 084W, if the base
change `f` of `f₀` to the limit `B` has relative dimension at most `d` and `f₀` is locally of
finite type, then the base change `f_i` of `f₀` to some stage `B_i` has relative dimension at
most `d`.

The system `D` here carries the field `indexSize : #I < cof(cutoff.ord)`, a bound on the size of
the index which Stacks does not impose; it implies the chapter's convention of Section 70.2
(tag 07SD). The statement under the convention itself, with no bound on the index, is
`MorphismDescentSituation.exists_hasRelativeDimensionLE_mapAt_of_siteContainsBaseChangeLimits`,
which carries the tag. -/
theorem exists_hasRelativeDimensionLE_mapAt (D : MorphismDescentSystem B S hS hZ I) (d : ℕ)
    (dimension : HasRelativeDimensionLE d B S hS D.mapLimit)
    (ft : IsLocallyOfFiniteType B S hS D.map₀) :
    ∃ (i : I) (le : D.initial ≤ i), HasRelativeDimensionLE d B S hS (D.mapAt i le) :=
  D.toSituation.exists_hasRelativeDimensionLE_mapAt (IsSiteSmall.of_lt_cof_op D.indexSize) d
      dimension ft

/-! ### The covariant indexing of Stacks 07SK

Stacks 084W, and every statement above, indexes the system by a directed preorder `I` and carries
it as the *contravariant* diagram `base : Iᵒᵖ ⥤ …`, reading a stage beyond the distinguished one
as an inequality `0 ≤ i`. The library's Stacks 07SK —
`AlgebraicGeometry.Space.exists_model_of_finitePresentation` and its fullness and faithfulness
companions — instead consumes a *cofiltered category* together with a *covariant* diagram out of
it, and states its conclusions over a morphism `j ⟶ i` of that category.

These are two readings of one and the same system: `base` is already a covariant functor on the
category `Iᵒᵖ`, which is cofiltered because a directed preorder is filtered. The declarations
below record that, and restate Stacks 0CN2 over a morphism of `Iᵒᵖ` rather than over an
inequality in `I`, so that it composes with Stacks 07SK without either result being reindexed.
-/

/-- The index category of a morphism descent system, read covariantly, is cofiltered. This is the
indexing the library's Stacks 07SK consumes: a directed preorder is filtered, so its opposite is
cofiltered, and the distinguished stage makes the index nonempty. -/
theorem isCofiltered_op (D : MorphismDescentSystem B S hS hZ I) : IsCofiltered Iᵒᵖ :=
  D.toSituation.isCofiltered_op

/-- A morphism of the index category `Iᵒᵖ` into the distinguished stage induces exactly the
transition morphism of the inequality it encodes. The morphisms of a preorder read as a category
are unique, so there is nothing to choose. -/
theorem base_map_eq_baseAtToInitial (D : MorphismDescentSystem B S hS hZ I) {j : Iᵒᵖ}
    (g : j ⟶ op D.initial) :
    D.base.map g = D.baseAtToInitial j.unop (leOfHom g.unop) :=
  D.toSituation.base_map_eq_baseAtToInitial g

/-- **Stacks 0CN2 in the covariant indexing of Stacks 07SK.** In the situation of Stacks 084W, if
the base change `f` of `f₀` to the limit `B` is smooth and `f₀` is locally of finite presentation,
then there is a morphism `j ⟶ 0` of the cofiltered index category `Iᵒᵖ` along which the base
change of `f₀` is smooth.

This is `AlgebraicGeometry.Space.MorphismDescentSystem.exists_isSmooth_mapAt` with its conclusion
read over a morphism of `Iᵒᵖ` instead of an inequality of `I`; the transition morphism is the same
one, by `AlgebraicGeometry.Space.MorphismDescentSystem.base_map_eq_baseAtToInitial`. It is the
shape in which the conclusions of Stacks 07SK are stated, so the two can be used together. -/
@[stacks 0CN2 "the cofiltered-covariant form: the conclusion ranges over a morphism of the \
cofiltered index category Iᵒᵖ carrying the covariant diagram `base`, which is the indexing the \
library's Stacks 07SK consumes, rather than over an inequality of the directed preorder I; the \
mathematical content is that of the inequality form beside it"]
theorem exists_isSmooth_mapAt_op (D : MorphismDescentSystem B S hS hZ I)
    (smooth : IsSmooth B S hS D.mapLimit) (fp : IsLocallyOfFinitePresentation B S hS D.map₀) :
    ∃ (j : Iᵒᵖ) (g : j ⟶ op D.initial),
      IsSmooth B S hS (D.mapAt j.unop (leOfHom g.unop)) :=
  D.toSituation.exists_isSmooth_mapAt_op (IsSiteSmall.of_lt_cof_op D.indexSize) smooth fp

end MorphismDescentSystem

end ChartData


end AlgebraicGeometry.Space

end
