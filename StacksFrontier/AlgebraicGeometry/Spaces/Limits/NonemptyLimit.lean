module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineChartSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Nonemptiness of an inverse limit of algebraic spaces

The limit of a cofiltered inverse system of nonempty quasi-compact algebraic spaces over a
scheme `S` with affine transition morphisms is again nonempty, provided the index category is
small enough for the big fppf site. This is Stacks 086W.

## Main results

* `AlgebraicGeometry.Space.nonempty_points_limit`: **Stacks 086W**, the limit has a point.
* `AlgebraicGeometry.Space.nonempty_points_limit_of_mono`: the same conclusion from the
  cofinality-free cardinality hypothesis, at the cost of monomorphic transition morphisms.

## Implementation notes

The reduction to schemes is the affine chart system of
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/AffineChartSystem.lean`. Choose a stage `i₀` and,
by Stacks 03FX, an affine surjective étale chart `f₀ : yoneda U₀ ⟶ D i₀` of it; the base
changes of the later stages along `f₀` are then represented by affine objects of the site, and
their limit represents the base change of `limit.π D i₀` along `f₀`.

Each chart is nonempty: a point of its stage and a point of `U₀` above the image of that point
— available because `f₀` is surjective on points, Stacks 03H5 — are the two images of a point
of the chart, by Stacks 03H4. So the chart system is a cofiltered system of nonempty affine
schemes with affine transition morphisms, and Mathlib's
`AlgebraicGeometry.Scheme.nonempty_of_isLimit` (Stacks 01Z2) gives a point of its limit.
That point of a scheme in the site is a point of the presheaf it represents, by the canonical
field-valued representative at it, and pushing it along the projection of the limit of the
chart system to `limit D` gives a point of `limit D`.

The source argues with `U = X ×_{X₀} U₀` and deduces nonemptiness of `X` from nonemptiness of
`U`; here the projection `|U| → |X|` is applied directly, which is the same step.

## References

* [Stacks Project, Tag 086W](https://stacks.math.columbia.edu/tag/086W)
* [Stacks Project, Tag 01Z2](https://stacks.math.columbia.edu/tag/01Z2)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03H5](https://stacks.math.columbia.edu/tag/03H5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

omit [IsCofiltered I] in
/-- Every chart of the affine chart system cut out by a surjective étale chart of a stage has
a point: a point of the chart's own stage and a point above its image in `U₀`, which exists
because the chart of the stage is surjective on points, are the images of a point of the
chart. -/
theorem nonempty_affineChartSystem_obj {i₀ : I} {U₀ : BigAffineFppf B S hS}
    {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀}
    (C : AffineChartSystem B S hS i₀ D U₀ f₀)
    (hsurj : Function.Surjective
      (pointsMap B S hS (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀)) f₀))
    (hNonempty : ∀ i, Nonempty (points B S hS (D.obj i))) (j : Over i₀) :
    Nonempty (C.schemeDiagram.obj j) := by
  obtain ⟨x⟩ := hNonempty j.left
  obtain ⟨y, hy⟩ := hsurj (pointsMap B S hS (D.obj j.left) (D.map j.hom) x)
  obtain ⟨w, -, -⟩ := exists_points_of_isPullback B S hS (C.isPullback j) x y hy.symm
  exact ⟨pointsToScheme B S hS (C.siteDiagram.obj j) w⟩

/-- The common core of the two forms below. Either form uses its cardinality hypotheses for
one thing only — producing the limit of the chart system cut out by a surjective affine étale
chart of a stage — so that limit bridge, for an arbitrary chart system of `D`, is what the
core takes instead. -/
theorem nonempty_points_limit_of_limitBridge
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hCompact : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hNonempty : ∀ i, Nonempty (points B S hS (D.obj i)))
    (hbridge : ∀ {i₀ : I} {U₀ : BigAffineFppf B S hS}
      {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀}
      (C : AffineChartSystem B S hS i₀ D U₀ f₀), AffineChartSystem.LimitBridge C) :
    Nonempty (points B S hS (limit D)) := by
  classical
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  obtain ⟨V₀, f₀, hV₀, hf₀surj, -⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS (D.obj i₀)
      (hD i₀)).mp (hCompact i₀)
  have hsurj : Function.Surjective (pointsMap B S hS (yoneda.obj V₀) f₀) :=
    (surjective_iff_surjective_pointsMap B S hS (D.obj i₀) (hD i₀) V₀ f₀).mp hf₀surj
  set C := affineChartSystem B S hS i₀ D ⟨V₀, hV₀⟩ f₀ hAffine with hC
  set L := hbridge C with hL
  have _ : ∀ j, Nonempty (C.schemeDiagram.obj j) :=
    nonempty_affineChartSystem_obj B S hS D C hsurj hNonempty
  have _ : ∀ j, IsAffine (C.schemeDiagram.obj j) := C.isAffine_obj
  have _ : ∀ j, CompactSpace (C.schemeDiagram.obj j) := fun j ↦ inferInstance
  have _ : ∀ {j k : Over i₀} (g : j ⟶ k),
      _root_.AlgebraicGeometry.IsAffineHom (C.schemeDiagram.map g) := fun g ↦ C.isAffineHom_map g
  obtain ⟨z⟩ : Nonempty ((BigFppfOver.toScheme B S hS).obj L.cone.pt) :=
    Scheme.nonempty_of_isLimit C.schemeDiagram _ L.schemeIsLimit
  exact ⟨pointsMap B S hS (yoneda.obj L.cone.pt) L.toLimit
    ((schemePointRepresentative B S hS L.cone.pt z).class B S hS (yoneda.obj L.cone.pt))⟩

/-- **Stacks 086W.** The inverse limit of a cofiltered inverse system of nonempty
quasi-compact algebraic spaces over `S` with affine transition morphisms has a point, provided
the index category is small enough for the site: its object type and all of its morphism types
have cardinality below the cofinality of the site's size cutoff. -/
@[stacks 086W]
theorem nonempty_points_limit (hSize : #I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hCompact : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hNonempty : ∀ i, Nonempty (points B S hS (D.obj i))) :
    Nonempty (points B S hS (limit D)) :=
  nonempty_points_limit_of_limitBridge B S hS D hD hAffine hCompact hNonempty
    fun C => C.limitBridge hSize hHomSize

/-- **The limit has a point, with no cofinality hypothesis.** This is
`AlgebraicGeometry.Space.nonempty_points_limit` with the cardinality bound on the index
category traded for a bound by the cutoff itself together with monomorphic transition
morphisms, through `AlgebraicGeometry.Space.AffineChartSystem.limitBridgeOfMono`. The two
hypotheses are incomparable, and `@[stacks 086W]` stays on the form carrying the source's
own one. -/
theorem nonempty_points_limit_of_mono {ν : Cardinal.{u}} (hSize : #I < B.cutoff)
    (hν : ν < B.cutoff) (hHomSize : ∀ i j : I, #(i ⟶ j) ≤ ν)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hMono : ∀ {i j : I} (f : i ⟶ j), Mono (D.map f))
    (hCompact : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hNonempty : ∀ i, Nonempty (points B S hS (D.obj i))) :
    Nonempty (points B S hS (limit D)) :=
  nonempty_points_limit_of_limitBridge B S hS D hD hAffine hCompact hNonempty
    fun C => C.limitBridgeOfMono hSize hν hHomSize hMono

end AlgebraicGeometry.Space

end
