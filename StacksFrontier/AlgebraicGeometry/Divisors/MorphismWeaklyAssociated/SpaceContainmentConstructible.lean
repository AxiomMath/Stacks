module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.RelativeWeakAssassin
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceFibreChartScheme
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceRelativeEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeAssassin.ContainmentConstructible
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple

/-!
# Constructibility of the relative assassin containment locus of an algebraic space

Let `Y` be a scheme, let `X` be an algebraic space over `Y` and let `F` be an `𝒪_X`-module.
For a subset `U` of `|X|` the *containment locus* is the set of points `y` of `Y` over which
every point of the relative assassin of `F` lying above `y` belongs to `U`. The source states
that this locus is locally constructible when `X` and `F` are of finite presentation over `Y`
and `U` is an open subspace which is quasi-compact over `Y`; the argument is to pick an affine
scheme `W` surjective and étale over `X`, to observe that the locus is unchanged when read on
`W`, and to invoke the case of schemes.

## `Ass` versus `WeakAss`

The source writes `Ass_{X_y}(F_y) ⊆ |U_y|`, the condition that the associated points of the
fibre module lie over `U`. In this development the relative notion available for an algebraic
space is the relative weak assassin `WeakAss_{X/Y}(F)` of Stacks 0CV0,
`AlgebraicGeometry.Space.relativeWeaklyAssociatedPoints`; the unrelativized `Ass` of an
algebraic space is not formalized here, only `WeakAss`
(`AlgebraicGeometry.Space.weaklyAssociatedPoints` of Stacks 0CTX). The two agree in the
situation of the source: `X ⟶ Y` of finite presentation is locally of finite type, so its
fibres are locally Noetherian by Stacks 0CUY, and on locally Noetherian fibres Stacks 0CUZ
records that "weakly associated" may be replaced by "associated" — which is exactly why
Stacks 0CV0 writes the one set `WeakAss_{X/Y}(F)` as `Ass_{X/Y}(F)` there. The locus below is
therefore stated with `WeakAss_{X/Y}(F)`, and `Ass_{X_y}(F_y) ⊆ |U_y|` is read as the
condition that the part of `WeakAss_{X/Y}(F)` lying over `y` is contained in `U`. The
replacement of the fibrewise set `Ass_{X_y}(F_y)` by the fibre of the relative set is the
identification Stacks 0CV0 makes by definition.

On the chart, where everything is a scheme, that replacement is not assumed but proved: the
scheme-level relative weak assassin `AlgebraicGeometry.relativeWeaklyAssociatedPoints` of
Stacks 05AV equals the scheme-level relative assassin `Stacks.Divisors.relativeAssassin` of
Stacks 05AT for a morphism locally of finite type, by Stacks 05F2 — which rests on Stacks
05AR — and membership of a point of a scheme-theoretic fibre in the associated points of the
fibre module is membership of its image in the relative assassin, by
`Stacks.Divisors.mem_associatedPoints_fiber_iff_mem_relativeAssassin`. Both steps are taken
inside the proof below.

## Main definitions

* `AlgebraicGeometry.Space.schemeSpacePointToScheme` is the comparison
  `AlgebraicGeometry.Space.pointsToScheme` of Stacks 03BV, with its source named through
  `AlgebraicGeometry.schemeSpace`.
* `AlgebraicGeometry.Space.relativeAssassinContainmentLocus` is the locus `E ⊆ Y`.

## Main results

* `AlgebraicGeometry.Space.relativeAssassinContainmentLocus_modulePullback`: the locus is
  unchanged when the source is replaced by an algebraic space étale and surjective over it.
  This is the étale invariance of Stacks 0CUZ.
* `AlgebraicGeometry.Space.relativeAssassinContainmentLocus_modulePullback_inter`: the same
  reading above a prescribed part of the base, where the chart is only required to be
  surjective over that part. This is the form a reduction to an open of the base can feed,
  since a chart adapted to an open `V' ⊆ V` is surjective over `V'` only.
* `AlgebraicGeometry.Space.chartSchemeToPoints_idEtaleChart`: the point of a represented
  algebraic space cut out by a point of the representing scheme through the identity chart is
  the one the bijection of Stacks 03BV names.

Stacks 0CVV itself is
`AlgebraicGeometry.Space.isLocallyConstructible_relativeAssassinContainmentLocus` of
`StacksFrontier/AlgebraicGeometry/Divisors/MorphismWeaklyAssociated/RepresentedFibreComparison.lean`
(which reads the locus on a chart by the étale invariance proved here and then identifies the
relative weak assassin of the represented chart with the scheme-level one).

## Implementation notes

An open subspace of `X` is recorded by the open subset of `|X|` it determines, and the
definition of the locus is stated for an arbitrary subset of `|X|`, which is more general
than the source and costs nothing.

`AlgebraicGeometry.schemeSpace` is a plain definition, so a projection out of it does
not reduce at the transparency the tactic framework uses to check that a rewrite is
type-correct, and `AlgebraicGeometry.Space.pointsToScheme`, whose source is spelled with
`CategoryTheory.yoneda` directly, cannot be applied to a point of `schemeSpace` inside a goal
without that reduction. `schemeSpacePointToScheme` is that same comparison map with its
source declared in the shape the statements use.

The case of schemes is `Stacks.RelativeAssassin.isLocallyConstructible_fibrewiseContainment`,
Stacks 05KR, whose locus `Stacks.RelativeAssassin.fibrewiseContainment` is stated with
`Stacks.Divisors.associatedPoints` of the fibre module.

## References

* [Stacks Project, Tag 0CVV](https://stacks.math.columbia.edu/tag/0CVV)
* [Stacks Project, Tag 05KR](https://stacks.math.columbia.edu/tag/05KR)
* [Stacks Project, Tag 0CV0](https://stacks.math.columbia.edu/tag/0CV0)
* [Stacks Project, Tag 0CUZ](https://stacks.math.columbia.edu/tag/0CUZ)
* [Stacks Project, Tag 0CUY](https://stacks.math.columbia.edu/tag/0CUY)
* [Stacks Project, Tag 0CTX](https://stacks.math.columbia.edu/tag/0CTX)
* [Stacks Project, Tag 05AT](https://stacks.math.columbia.edu/tag/05AT)
* [Stacks Project, Tag 05AV](https://stacks.math.columbia.edu/tag/05AV)
* [Stacks Project, Tag 05F2](https://stacks.math.columbia.edu/tag/05F2)
* [Stacks Project, Tag 03BV](https://stacks.math.columbia.edu/tag/03BV)
-/

@[expose] public noncomputable section

open CategoryTheory Topology

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The points of a scheme regarded as an algebraic space -/

/-- **Stacks 03BV.** The point of the representing scheme underlying a point of the algebraic
space that a scheme of the site represents: the comparison
`AlgebraicGeometry.Space.pointsToScheme`, with its source declared through
`AlgebraicGeometry.schemeSpace`. -/
def schemeSpacePointToScheme (V : BigFppfOver B S hS) :
    points B S hS (schemeSpace V).1 → (BigFppfOver.toScheme B S hS).obj V :=
  pointsToScheme B S hS V

/-- The comparison of Stacks 03BV is surjective. -/
theorem surjective_schemeSpacePointToScheme (V : BigFppfOver B S hS) :
    Function.Surjective (schemeSpacePointToScheme B S hS V) :=
  surjective_pointsToScheme B S hS V

/-- The comparison of Stacks 03BV is natural in the scheme of the site: it carries the map on
points induced by a morphism of schemes to the morphism of schemes itself. -/
theorem schemeSpacePointToScheme_pointsMap {W V : BigFppfOver B S hS} (α : W ⟶ V)
    (w : points B S hS (schemeSpace W).1) :
    schemeSpacePointToScheme B S hS V
        (pointsMap B S hS (schemeSpace W).1 (schemeSpaceMap α).hom w) =
      (BigFppfOver.toScheme B S hS).map α (schemeSpacePointToScheme B S hS W w) :=
  pointsToScheme_pointsMap_yoneda B S hS α w

/-! ### The containment locus -/

/-- The set of points `y` of a scheme `V` over which every point of the relative weak
assassin `WeakAss_{X/V}(F)` of Stacks 0CV0 lies in a prescribed subset `U` of `|X|`.

When `X ⟶ V` is of finite presentation the fibres are locally Noetherian, so the relative
weak assassin is the relative assassin and this is the locus
`{y | Ass_{X_y}(F_y) ⊆ |U_y|}` of Stacks 0CVV. -/
def relativeAssassinContainmentLocus {X : AlgebraicSpaces B S hS} (V : BigFppfOver B S hS)
    (f : X ⟶ schemeSpace V) (F : Modules.{u, u} B S hS X.1 X.2)
    (U : Set (points B S hS X.1)) : Set ((BigFppfOver.toScheme B S hS).obj V) :=
  {y | ∀ x ∈ relativeWeaklyAssociatedPoints B S hS f F,
    schemeSpacePointToScheme B S hS V (pointsMap B S hS X.1 f.hom x) = y → x ∈ U}

/-- Membership in the containment locus is the containment of the part of the relative weak
assassin lying over the point. -/
theorem mem_relativeAssassinContainmentLocus_iff {X : AlgebraicSpaces B S hS}
    (V : BigFppfOver B S hS) (f : X ⟶ schemeSpace V)
    (F : Modules.{u, u} B S hS X.1 X.2) (U : Set (points B S hS X.1))
    (y : (BigFppfOver.toScheme B S hS).obj V) :
    y ∈ relativeAssassinContainmentLocus B S hS V f F U ↔
      ∀ x ∈ relativeWeaklyAssociatedPoints B S hS f F,
        schemeSpacePointToScheme B S hS V (pointsMap B S hS X.1 f.hom x) = y → x ∈ U :=
  Iff.rfl

/-- A point lies in the containment locus of `(φ ≫ f, φ^*F, |φ|⁻¹ U)` iff it lies in that of
`(f, F, U)`, provided the points of `X` over it are hit by `|φ|`. -/
private theorem mem_containmentLocus_modulePullback_iff {X X' : AlgebraicSpaces B S hS}
    (V : BigFppfOver B S hS) (f : X ⟶ schemeSpace V)
    (F : Modules.{u, u} B S hS X.1 X.2) (U : Set (points B S hS X.1)) (φ : X' ⟶ X)
    (hφ : IsEtale B S hS φ.hom) (y : (BigFppfOver.toScheme B S hS).obj V)
    (hsurj : ∀ x : points B S hS X.1,
      schemeSpacePointToScheme B S hS V (pointsMap B S hS X.1 f.hom x) = y →
        x ∈ Set.range (pointsMap B S hS X'.1 φ.hom)) :
    y ∈ relativeAssassinContainmentLocus B S hS V (φ ≫ f) ((modulePullback B S hS φ).obj F)
        (pointsMap B S hS X'.1 φ.hom ⁻¹' U) ↔
      y ∈ relativeAssassinContainmentLocus B S hS V f F U := by
  have hmap : ∀ x' : points B S hS X'.1,
      pointsMap B S hS X'.1 (φ ≫ f).hom x' =
        pointsMap B S hS X.1 f.hom (pointsMap B S hS X'.1 φ.hom x') :=
    fun x' => congrArg (fun k => k x') (pointsMap_comp B S hS X'.1 φ.hom f.hom)
  refine ⟨fun h x hx hxy => ?_, fun h x' hx' hx'y =>
    h _ ((isRelativeWeaklyAssociatedPoint_modulePullback_iff B S hS φ hφ f F x').1 hx')
      (by rwa [← hmap x'])⟩
  obtain ⟨x', rfl⟩ := hsurj x hxy
  exact h x' ((isRelativeWeaklyAssociatedPoint_modulePullback_iff B S hS φ hφ f F x').2 hx)
    (by rwa [hmap x'])

/-- The containment locus is read on an algebraic space étale and surjective over the source:
for `φ : X' ⟶ X` étale and surjective on points, the locus of `(φ ≫ f, φ^*F, |φ|^{-1} U)` is
that of `(f, F, U)`.

The relative weak assassin of `φ^*F` along `φ ≫ f` is the inverse image of the relative weak
assassin of `F` along `f`, which is the étale invariance of Stacks 0CUZ; surjectivity on
points lets a point of `X` be replaced by one of `X'` above it. -/
theorem relativeAssassinContainmentLocus_modulePullback {X X' : AlgebraicSpaces B S hS}
    (V : BigFppfOver B S hS) (f : X ⟶ schemeSpace V)
    (F : Modules.{u, u} B S hS X.1 X.2) (U : Set (points B S hS X.1)) (φ : X' ⟶ X)
    (hφ : IsEtale B S hS φ.hom)
    (hsurj : Function.Surjective (pointsMap B S hS X'.1 φ.hom)) :
    relativeAssassinContainmentLocus B S hS V (φ ≫ f) ((modulePullback B S hS φ).obj F)
        (pointsMap B S hS X'.1 φ.hom ⁻¹' U) =
      relativeAssassinContainmentLocus B S hS V f F U := by
  ext y
  exact mem_containmentLocus_modulePullback_iff B S hS V f F U φ hφ y fun x _ => hsurj x

/-- The containment locus is read on an algebraic space étale over the source **above a
prescribed part of the base**: it is enough that every point of `X` lying over that part of the
base be hit by `|φ|`, and the two loci then agree there.

`AlgebraicGeometry.Space.relativeAssassinContainmentLocus_modulePullback` is the case of a
subset containing the whole image of `|f|`, where the hypothesis is surjectivity of `|φ|` on
all of `|X|`. The localised form is what a reduction to a part of the base can supply: an
étale chart of `X` adapted to an open `V' ⊆ V` is surjective over `V'` and need not be
surjective over `V`. -/
theorem relativeAssassinContainmentLocus_modulePullback_inter {X X' : AlgebraicSpaces B S hS}
    (V : BigFppfOver B S hS) (f : X ⟶ schemeSpace V)
    (F : Modules.{u, u} B S hS X.1 X.2) (U : Set (points B S hS X.1)) (φ : X' ⟶ X)
    (hφ : IsEtale B S hS φ.hom) (T : Set ((BigFppfOver.toScheme B S hS).obj V))
    (hsurj : ∀ x : points B S hS X.1,
      schemeSpacePointToScheme B S hS V (pointsMap B S hS X.1 f.hom x) ∈ T →
        x ∈ Set.range (pointsMap B S hS X'.1 φ.hom)) :
    relativeAssassinContainmentLocus B S hS V (φ ≫ f) ((modulePullback B S hS φ).obj F)
          (pointsMap B S hS X'.1 φ.hom ⁻¹' U) ∩ T =
      relativeAssassinContainmentLocus B S hS V f F U ∩ T := by
  ext y
  simp only [Set.mem_inter_iff]
  exact and_congr_left fun hyT => mem_containmentLocus_modulePullback_iff B S hS V f F U φ hφ y
    fun x hxy => hsurj x (by rwa [hxy])

/-! ### Weak association at the identity chart of a represented algebraic space -/

/-- The point of the algebraic space represented by a scheme of the site cut out by a point of
that scheme through the identity chart is the one the bijection of Stacks 03BV names. -/
theorem chartSchemeToPoints_idEtaleChart (T : BigFppfOver B S hS)
    (t : (BigFppfOver.toScheme B S hS).obj T) :
    chartSchemeToPoints B S hS (yoneda.obj T) (idEtaleChart B S hS T) t =
      (pointsEquivScheme B S hS T).symm t :=
  (chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm B S hS (yoneda.obj T)
      (idEtaleChart B S hS T) t).trans
    (congrFun (pointsMap_id B S hS (yoneda.obj T)) _)

end AlgebraicGeometry.Space

end
