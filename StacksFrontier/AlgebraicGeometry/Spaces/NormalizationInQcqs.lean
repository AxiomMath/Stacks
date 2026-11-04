module

public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismToAffineScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInChartRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalizationAlgebraCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace

/-!
# The normalization of an algebraic space in another, for a quasi-compact quasi-separated morphism

Let `f : Y ⟶ X` be a quasi-compact, quasi-separated morphism of algebraic spaces over `S` and let
`𝒪'` be the integral closure of `𝒪_X` in `f_* 𝒪_Y`.  Definition 0822 names the *normalization of
`X` in `Y`*: the morphism `ν : X' = \underline{Spec}_X(𝒪') ⟶ X`, together with its natural
factorization `Y ⟶ X' ⟶ X` of `f`.  This file constructs both at exactly those hypotheses.

`X'` is the chart construction of the relative spectrum,
`AlgebraicGeometry.Space.normalizationInChartAffineOver`, applied to the surjective étale atlas
of `X` and its kernel pair chosen once and for all by
`AlgebraicGeometry.Space.chosenAtlasKernelPair`.  That it is the relative spectrum of `𝒪'` is the
statement that `ν` is affine with `ν_* 𝒪_{X'} ≅ 𝒪'` as `𝒪_X`-algebras.

The factorization `f' : Y ⟶ X'` is built from the mapping property of `X'`: for every object `T`
of the site and every `T`-point `y` of `Y`, the composite `T ⟶ Y ⟶ X` is representable, so the
algebra map `ν_* 𝒪_{X'} ≅ 𝒪' ⊂ f_* 𝒪_Y ⟶ (f ∘ y)_* 𝒪_T` is the direct-image map of a *unique*
morphism `T ⟶ X'` over `X`
(`AlgebraicGeometry.Space.exists_pushforwardAlgebraMap_eq_of_relativelyRepresentable` and
`AlgebraicGeometry.Space.eq_of_pushforwardAlgebraMap_eq_of_relativelyRepresentable`).
Uniqueness makes these points natural in `T`, so they assemble into a morphism of sheaves
`Y ⟶ X'`.

## Main definitions

* `AlgebraicGeometry.Space.normalizationInQcqs`: `X' = \underline{Spec}_X(𝒪')`, as an algebraic
  space over `S`, and `AlgebraicGeometry.Space.normalizationInQcqsHom`: the normalization
  `ν : X' ⟶ X`.
* `AlgebraicGeometry.Space.normalizationInQcqsPushforwardIso`: `ν_* 𝒪_{X'} ≅ 𝒪'` as sheaves of
  `𝒪_X`-algebras.
* `AlgebraicGeometry.Space.toNormalizationInQcqs`: the canonical morphism `f' : Y ⟶ X'`.

## Main results

* `AlgebraicGeometry.Space.isAffineHom_normalizationInQcqsHom`: `ν` is affine.
* `AlgebraicGeometry.Space.toNormalizationInQcqs_comp`: **the factorization** `ν ∘ f' = f`.
* `AlgebraicGeometry.Space.pushforwardAlgebraMap_point_toNormalizationInQcqs` and
  `AlgebraicGeometry.Space.eq_toNormalizationInQcqsOver`: **`f'` is the natural factorization**:
  at every point `y : T ⟶ Y` the direct-image map of `f' ∘ y` is
  `ν_* 𝒪_{X'} ≅ 𝒪' ⊂ f_* 𝒪_Y ⟶ (f ∘ y)_* 𝒪_T`, and `f'` is the only morphism over `X` with that
  property.

## Implementation notes

**The chosen atlas.**  The construction depends on a surjective étale atlas of `X`, which is
chosen by `Classical.choice`.  This is a choice of model, not of object: the characterization of
`f'` above, together with `AlgebraicGeometry.Space.eq_of_pushforwardAlgebraMap_eq`, determines
`X'` with `ν` and `f'` up to unique isomorphism through the direct-image algebra, and
`AlgebraicGeometry.Space.exists_iso_normalizationInChartQuotient_of_contains_prod` compares the
chart models directly.

**Size.**  No size hypothesis is needed: the chart objects of `X'` lie in the site by
`AlgebraicGeometry.Space.contains_chartRelativeSpec_integralClosureSheaf_pushforwardAlgebra`,
whose bound comes from the sections of `f_* 𝒪_Y`, so the refutation
`AlgebraicGeometry.Space.not_nonempty_affineAlgebraAntiEquivalence` of an unbounded relative
spectrum does not bear on it.

## References

* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
* [Stacks Project, Tag 081X](https://stacks.math.columbia.edu/tag/081X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The chosen atlas of `X` and its kernel pair, as étale charts -/

section AtlasPair

variable (X : AlgebraicSpaces B S hS)

/-- **The chosen surjective étale atlas `U ⟶ X`**, as an étale chart of `X`. -/
abbrev chosenAtlasPairTarget : SmallEtale B S hS X.1 :=
  atlasChart B S hS X (chosenAtlasKernelPair B S hS X)

/-- **The kernel pair `U ×_X U` of the chosen atlas**, as an étale chart of `X` through its first
projection. -/
abbrev chosenAtlasPairSource : SmallEtale B S hS X.1 :=
  chartFromEtaleHom B S hS X (chosenAtlasKernelPair B S hS X).R
    (yoneda.map (chosenAtlasKernelPair B S hS X).t ≫ (chosenAtlasKernelPair B S hS X).f)
    (chart_preimage_etale B S hS X _ (chosenAtlasKernelPair B S hS X).etale _
      (chosenAtlasKernelPair B S hS X).tEtale)

/-- The first projection `U ×_X U ⟶ U`, as a morphism of étale charts of `X`. -/
def chosenAtlasPairFst : chosenAtlasPairSource B S hS X ⟶ chosenAtlasPairTarget B S hS X :=
  ObjectProperty.homMk (CostructuredArrow.homMk (chosenAtlasKernelPair B S hS X).t rfl)

/-- The second projection `U ×_X U ⟶ U`, as a morphism of étale charts of `X`. -/
def chosenAtlasPairSnd : chosenAtlasPairSource B S hS X ⟶ chosenAtlasPairTarget B S hS X :=
  ObjectProperty.homMk (CostructuredArrow.homMk (chosenAtlasKernelPair B S hS X).s
    (chosenAtlasKernelPair B S hS X).pullback.w.symm)

/-- The two projections exhibit the source chart as the kernel pair of the atlas. -/
theorem isPullback_chosenAtlasPair :
    IsPullback (yoneda.map ((SmallEtale.toOver B S hS X.1).map (chosenAtlasPairFst B S hS X)))
      (yoneda.map ((SmallEtale.toOver B S hS X.1).map (chosenAtlasPairSnd B S hS X)))
      (chosenAtlasPairTarget B S hS X).obj.hom (chosenAtlasPairTarget B S hS X).obj.hom :=
  (chosenAtlasKernelPair B S hS X).pullback

/-- The chosen atlas is surjective. -/
theorem surjective_chosenAtlasPairTarget :
    MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))
      (chosenAtlasPairTarget B S hS X).obj.hom :=
  (chosenAtlasKernelPair B S hS X).surjective

end AtlasPair

/-! ### The normalization `ν : X' ⟶ X` -/

section Normalization

variable {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)

/-- **`X' = \underline{Spec}_X(𝒪')` with `ν`, as an algebraic space affine over `X`**, for a
quasi-compact quasi-separated `f : Y ⟶ X` and `𝒪'` the integral closure of `𝒪_X` in `f_* 𝒪_Y`.
It is the chart construction of the relative spectrum of `𝒪'` over the chosen atlas of `X`. -/
def normalizationInQcqsAffineOver : AffineOver B S hS X :=
  normalizationInChartAffineOver B S hS f hfqc hfqs (chosenAtlasPairFst B S hS X)
    (chosenAtlasPairSnd B S hS X) (isPullback_chosenAtlasPair B S hS X)
    (surjective_chosenAtlasPairTarget B S hS X)

/-- **The normalization `X' = \underline{Spec}_X(𝒪')` of `X` in `Y`**, as an algebraic space
over `S` (Definition 0822). -/
abbrev normalizationInQcqs : AlgebraicSpaces B S hS :=
  (normalizationInQcqsAffineOver B S hS f hfqc hfqs).obj.left

/-- **The normalization morphism `ν : X' ⟶ X` of `X` in `Y`** (Definition 0822), for a
quasi-compact quasi-separated `f : Y ⟶ X`.  It is affine
(`AlgebraicGeometry.Space.isAffineHom_normalizationInQcqsHom`) with `ν_* 𝒪_{X'}` the integral
closure `𝒪'` of `𝒪_X` in `f_* 𝒪_Y` (`AlgebraicGeometry.Space.normalizationInQcqsPushforwardIso`),
which is what `X' = \underline{Spec}_X(𝒪')` means. -/
@[stacks 0822 "the normalization ν : X' = Spec_X(𝒪') ⟶ X of X in Y, for f qcqs"]
def normalizationInQcqsHom : normalizationInQcqs B S hS f hfqc hfqs ⟶ X :=
  (normalizationInQcqsAffineOver B S hS f hfqc hfqs).obj.hom

/-- **`ν : X' ⟶ X` is affine.** -/
@[stacks 0822 "ν : X' ⟶ X is affine, X' being a relative spectrum over X"]
theorem isAffineHom_normalizationInQcqsHom :
    IsAffineHom B S hS (normalizationInQcqsHom B S hS f hfqc hfqs).hom :=
  (normalizationInQcqsAffineOver B S hS f hfqc hfqs).property

/-- **`ν_* 𝒪_{X'} ≅ 𝒪'`**: the direct image of the structure sheaf of the normalization is the
integral closure of `𝒪_X` in `f_* 𝒪_Y`, as sheaves of `𝒪_X`-algebras.  With affineness of `ν`
this identifies `X'` with `\underline{Spec}_X(𝒪')`. -/
@[stacks 0822 "ν_* 𝒪_{X'} = 𝒪', i.e. X' = Spec_X(𝒪')"]
def normalizationInQcqsPushforwardIso :
    pushforwardAlgebra B S hS (Over.mk (normalizationInQcqsHom B S hS f hfqc hfqs)) ≅
      AlgebraSheaf.integralClosureSheaf (pushforwardAlgebra B S hS (Over.mk f)) :=
  normalizationInChartAffineOverPushforwardIso B S hS f hfqc hfqs (chosenAtlasPairFst B S hS X)
    (chosenAtlasPairSnd B S hS X) (isPullback_chosenAtlasPair B S hS X)
    (surjective_chosenAtlasPairTarget B S hS X)

/-- The algebra map `ν_* 𝒪_{X'} ≅ 𝒪' ⊂ f_* 𝒪_Y` which the factorization `f'` induces. -/
def normalizationInQcqsAlgebraMap :
    pushforwardAlgebra B S hS (normalizationInQcqsAffineOver B S hS f hfqc hfqs).obj ⟶
      pushforwardAlgebra B S hS (Over.mk f) :=
  (normalizationInQcqsPushforwardIso B S hS f hfqc hfqs).hom ≫
    AlgebraSheaf.integralClosureInclusion _

end Normalization

/-! ### The points of `Y` and their lifts to `X'` -/

section Points

variable {B S hS} {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)

/-- A `T`-point `y` of `Y`, composed with `f`, as an algebraic space over `X`. -/
abbrev normalizationInQcqsPointOver {T : BigFppfOver B S hS} (y : yoneda.obj T ⟶ Y.1) :
    Over X :=
  Over.mk (ObjectProperty.homMk (y ≫ f.hom) : schemeSpace T ⟶ X)

/-- A `T`-point `y` of `Y`, as a morphism over `X`. -/
def normalizationInQcqsPointOverHom {T : BigFppfOver B S hS} (y : yoneda.obj T ⟶ Y.1) :
    normalizationInQcqsPointOver f y ⟶ Over.mk f :=
  Over.homMk (ObjectProperty.homMk y) (ObjectProperty.hom_ext _ rfl)

/-- Precomposition of a point with a morphism `u : T' ⟶ T` of the site, as a morphism over
`X`. -/
def normalizationInQcqsPointOverMap {T T' : BigFppfOver B S hS} (u : T' ⟶ T)
    (y : yoneda.obj T ⟶ Y.1) :
    normalizationInQcqsPointOver f (yoneda.map u ≫ y) ⟶ normalizationInQcqsPointOver f y :=
  Over.homMk (schemeSpaceMap u) (ObjectProperty.hom_ext _ (Category.assoc _ _ _).symm)

theorem normalizationInQcqsPointOverMap_comp_pointOverHom {T T' : BigFppfOver B S hS}
    (u : T' ⟶ T) (y : yoneda.obj T ⟶ Y.1) :
    normalizationInQcqsPointOverMap f u y ≫ normalizationInQcqsPointOverHom f y =
      normalizationInQcqsPointOverHom f (yoneda.map u ≫ y) :=
  Over.OverMorphism.ext (ObjectProperty.hom_ext _ (by
    rw [Over.comp_left, ObjectProperty.FullSubcategory.comp_hom]
    rfl))

/-- The structure morphism of `AlgebraicGeometry.Space.normalizationInQcqsPointOver` is
representable, its source being representable and its target an algebraic space. -/
theorem relativelyRepresentable_normalizationInQcqsPointOver {T : BigFppfOver B S hS}
    (y : yoneda.obj T ⟶ Y.1) :
    yoneda.relativelyRepresentable (normalizationInQcqsPointOver f y).hom.hom :=
  relativelyRepresentable_of_isAlgebraicSpace B S hS X.property _

variable (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)

/-- **The mapping property of `X'` at a point.**  For a `T`-point `y` of `Y` there is exactly one
morphism `T ⟶ X'` over `X` whose direct-image map is
`ν_* 𝒪_{X'} ≅ 𝒪' ⊂ f_* 𝒪_Y ⟶ (f ∘ y)_* 𝒪_T`. -/
theorem existsUnique_normalizationInQcqsPointLift {T : BigFppfOver B S hS}
    (y : yoneda.obj T ⟶ Y.1) :
    ∃! d : normalizationInQcqsPointOver f y ⟶
        (normalizationInQcqsAffineOver B S hS f hfqc hfqs).obj,
      pushforwardAlgebraMap B S hS d =
        normalizationInQcqsAlgebraMap B S hS f hfqc hfqs ≫
          pushforwardAlgebraMap B S hS (normalizationInQcqsPointOverHom f y) := by
  obtain ⟨d, hd⟩ := exists_pushforwardAlgebraMap_eq_of_relativelyRepresentable B S hS
    (relativelyRepresentable_normalizationInQcqsPointOver f y)
    (normalizationInQcqsAffineOver B S hS f hfqc hfqs)
    (normalizationInQcqsAlgebraMap B S hS f hfqc hfqs ≫
      pushforwardAlgebraMap B S hS (normalizationInQcqsPointOverHom f y))
  exact ⟨d, hd, fun d' hd' => eq_of_pushforwardAlgebraMap_eq_of_relativelyRepresentable B S hS
    (relativelyRepresentable_normalizationInQcqsPointOver f y) _ (hd'.trans hd.symm)⟩

/-- The morphism `T ⟶ X'` over `X` attached to a `T`-point of `Y`. -/
def normalizationInQcqsPointLift {T : BigFppfOver B S hS} (y : yoneda.obj T ⟶ Y.1) :
    normalizationInQcqsPointOver f y ⟶
      (normalizationInQcqsAffineOver B S hS f hfqc hfqs).obj :=
  (existsUnique_normalizationInQcqsPointLift f hfqc hfqs y).exists.choose

/-- The morphism of presheaves `T ⟶ X'` underlying
`AlgebraicGeometry.Space.normalizationInQcqsPointLift`. -/
def normalizationInQcqsPointLiftHom {T : BigFppfOver B S hS} (y : yoneda.obj T ⟶ Y.1) :
    yoneda.obj T ⟶ (normalizationInQcqs B S hS f hfqc hfqs).1 :=
  (normalizationInQcqsPointLift f hfqc hfqs y).left.hom

theorem pushforwardAlgebraMap_normalizationInQcqsPointLift {T : BigFppfOver B S hS}
    (y : yoneda.obj T ⟶ Y.1) :
    pushforwardAlgebraMap B S hS (normalizationInQcqsPointLift f hfqc hfqs y) =
      normalizationInQcqsAlgebraMap B S hS f hfqc hfqs ≫
        pushforwardAlgebraMap B S hS (normalizationInQcqsPointOverHom f y) :=
  (existsUnique_normalizationInQcqsPointLift f hfqc hfqs y).exists.choose_spec

/-- **The lifts are natural in the point.** -/
theorem normalizationInQcqsPointLift_precomp {T T' : BigFppfOver B S hS} (u : T' ⟶ T)
    (y : yoneda.obj T ⟶ Y.1) :
    normalizationInQcqsPointLift f hfqc hfqs (yoneda.map u ≫ y) =
      normalizationInQcqsPointOverMap f u y ≫ normalizationInQcqsPointLift f hfqc hfqs y := by
  refine (existsUnique_normalizationInQcqsPointLift f hfqc hfqs (yoneda.map u ≫ y)).unique
    (pushforwardAlgebraMap_normalizationInQcqsPointLift f hfqc hfqs _) ?_
  rw [pushforwardAlgebraMap_comp, pushforwardAlgebraMap_normalizationInQcqsPointLift,
    Category.assoc, ← pushforwardAlgebraMap_comp, normalizationInQcqsPointOverMap_comp_pointOverHom]

theorem normalizationInQcqsPointLiftHom_precomp {T T' : BigFppfOver B S hS} (u : T' ⟶ T)
    (y : yoneda.obj T ⟶ Y.1) :
    normalizationInQcqsPointLiftHom f hfqc hfqs (yoneda.map u ≫ y) =
      yoneda.map u ≫ normalizationInQcqsPointLiftHom f hfqc hfqs y := by
  unfold normalizationInQcqsPointLiftHom
  rw [normalizationInQcqsPointLift_precomp, Over.comp_left,
    ObjectProperty.FullSubcategory.comp_hom]
  rfl

/-- Each lift lies over `X`: composed with `ν` it is `f ∘ y`. -/
theorem normalizationInQcqsPointLiftHom_comp {T : BigFppfOver B S hS} (y : yoneda.obj T ⟶ Y.1) :
    normalizationInQcqsPointLiftHom f hfqc hfqs y ≫
        (normalizationInQcqsHom B S hS f hfqc hfqs).hom = y ≫ f.hom :=
  congrArg (fun m => m.hom) (Over.w (normalizationInQcqsPointLift f hfqc hfqs y))

end Points

/-! ### The factorization `Y ⟶ X' ⟶ X` -/

section Factorization

variable {B S hS} {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)

/-- The morphism of presheaves `Y ⟶ X'` assembled from the lifts of the points of `Y`. -/
def toNormalizationInQcqsNatTrans : Y.1 ⟶ (normalizationInQcqs B S hS f hfqc hfqs).1 where
  app T := TypeCat.ofHom fun a =>
    yonedaEquiv (normalizationInQcqsPointLiftHom f hfqc hfqs ((yonedaEquiv (X := T.unop)).symm a))
  naturality T T' u := by
    refine TypeCat.homEquiv.injective (funext fun a => ?_)
    change yonedaEquiv (normalizationInQcqsPointLiftHom f hfqc hfqs
        ((yonedaEquiv (X := T'.unop)).symm (Y.1.map u a))) =
      (normalizationInQcqs B S hS f hfqc hfqs).1.map u
        (yonedaEquiv (normalizationInQcqsPointLiftHom f hfqc hfqs
          ((yonedaEquiv (X := T.unop)).symm a)))
    rw [yonedaEquiv_naturality', yonedaEquiv_symm_map, normalizationInQcqsPointLiftHom_precomp]

/-- **The canonical morphism `f' : Y ⟶ X'`** of Definition 0822: on a `T`-point `y` of `Y` it is
the unique morphism `T ⟶ X'` over `X` inducing `ν_* 𝒪_{X'} ≅ 𝒪' ⊂ f_* 𝒪_Y ⟶ (f ∘ y)_* 𝒪_T`. -/
@[stacks 0822 "the canonical morphism f' : Y ⟶ X'"]
def toNormalizationInQcqs : Y ⟶ normalizationInQcqs B S hS f hfqc hfqs :=
  ObjectProperty.homMk (toNormalizationInQcqsNatTrans f hfqc hfqs)

/-- `f'` precomposed with a point is the lift of that point. -/
theorem point_comp_toNormalizationInQcqs {T : BigFppfOver B S hS} (y : yoneda.obj T ⟶ Y.1) :
    y ≫ (toNormalizationInQcqs f hfqc hfqs).hom =
      normalizationInQcqsPointLiftHom f hfqc hfqs y := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp]
  change yonedaEquiv (normalizationInQcqsPointLiftHom f hfqc hfqs
    ((yonedaEquiv (X := T)).symm (yonedaEquiv y))) = _
  rw [Equiv.symm_apply_apply]

/-- **The factorization of Definition 0822: `ν ∘ f' = f`.** -/
@[stacks 0822 "the natural factorization Y ⟶ X' ⟶ X of f"]
theorem toNormalizationInQcqs_comp :
    toNormalizationInQcqs f hfqc hfqs ≫ normalizationInQcqsHom B S hS f hfqc hfqs = f := by
  refine ObjectProperty.hom_ext _ ?_
  refine hom_ext_yoneda fun T y => ?_
  change (y ≫ (toNormalizationInQcqs f hfqc hfqs).hom) ≫
      (normalizationInQcqsHom B S hS f hfqc hfqs).hom = y ≫ f.hom
  exact (congrArg (fun m => m ≫ (normalizationInQcqsHom B S hS f hfqc hfqs).hom)
    (point_comp_toNormalizationInQcqs f hfqc hfqs y)).trans
    (normalizationInQcqsPointLiftHom_comp f hfqc hfqs y)

/-- `f'` as a morphism of algebraic spaces over `X`. -/
def toNormalizationInQcqsOver :
    Over.mk f ⟶ (normalizationInQcqsAffineOver B S hS f hfqc hfqs).obj :=
  Over.homMk (toNormalizationInQcqs f hfqc hfqs) (toNormalizationInQcqs_comp f hfqc hfqs)

/-- `f'` precomposed with a point, over `X`, is the lift of that point. -/
theorem pointOverHom_comp_toNormalizationInQcqsOver {T : BigFppfOver B S hS}
    (y : yoneda.obj T ⟶ Y.1) :
    normalizationInQcqsPointOverHom f y ≫ toNormalizationInQcqsOver f hfqc hfqs =
      normalizationInQcqsPointLift f hfqc hfqs y :=
  Over.OverMorphism.ext (ObjectProperty.hom_ext _ (point_comp_toNormalizationInQcqs f hfqc hfqs y))

/-- **`f'` is the natural factorization.**  At every `T`-point `y` of `Y`, the direct-image map of
`f' ∘ y` is `ν_* 𝒪_{X'} ≅ 𝒪' ⊂ f_* 𝒪_Y` followed by the direct-image map of `y`. -/
theorem pushforwardAlgebraMap_point_toNormalizationInQcqs {T : BigFppfOver B S hS}
    (y : yoneda.obj T ⟶ Y.1) :
    pushforwardAlgebraMap B S hS
        (normalizationInQcqsPointOverHom f y ≫ toNormalizationInQcqsOver f hfqc hfqs) =
      normalizationInQcqsAlgebraMap B S hS f hfqc hfqs ≫
        pushforwardAlgebraMap B S hS (normalizationInQcqsPointOverHom f y) := by
  rw [pointOverHom_comp_toNormalizationInQcqsOver,
    pushforwardAlgebraMap_normalizationInQcqsPointLift]

/-- **`f'` is the only morphism over `X` with the property of
`AlgebraicGeometry.Space.pushforwardAlgebraMap_point_toNormalizationInQcqs`.** -/
theorem eq_toNormalizationInQcqsOver
    (g : Over.mk f ⟶ (normalizationInQcqsAffineOver B S hS f hfqc hfqs).obj)
    (hg : ∀ (T : BigFppfOver B S hS) (y : yoneda.obj T ⟶ Y.1),
      pushforwardAlgebraMap B S hS (normalizationInQcqsPointOverHom f y ≫ g) =
        normalizationInQcqsAlgebraMap B S hS f hfqc hfqs ≫
          pushforwardAlgebraMap B S hS (normalizationInQcqsPointOverHom f y)) :
    g = toNormalizationInQcqsOver f hfqc hfqs := by
  refine Over.OverMorphism.ext (ObjectProperty.hom_ext _ ?_)
  refine hom_ext_yoneda fun T y => ?_
  have h : normalizationInQcqsPointOverHom f y ≫ g = normalizationInQcqsPointLift f hfqc hfqs y :=
    (existsUnique_normalizationInQcqsPointLift f hfqc hfqs y).unique (hg T y)
      (pushforwardAlgebraMap_normalizationInQcqsPointLift f hfqc hfqs y)
  exact (congrArg (fun m => m.left.hom) h).trans
    (point_comp_toNormalizationInQcqs f hfqc hfqs y).symm

end Factorization

end AlgebraicGeometry.Space

end
