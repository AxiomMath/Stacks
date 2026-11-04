module

public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionFunctionFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed
public import StacksFrontier.Topology.Dimension.DimensionFunction
public import StacksFrontier.Topology.Dimension.DimensionFunctionObstruction

/-!
# Recognising a dimension function: locality, and descent along a specializing surjection

Being a dimension function is a local property: a function which is a dimension function on an
open neighbourhood of every point is a dimension function. It also descends along a continuous,
surjective, specializing map: if `δ ∘ g` is a dimension function then so is `δ`. The map on
points of a finite surjective morphism of algebraic spaces is such a map, which gives the
geometric form of the descent, Stacks 0ED9, with no decency or local Noetherianity hypotheses.

## Main results

* `TopologicalSpace.exists_dimensionFunction_of_cover`: a function that is a dimension
  function on an open neighbourhood of every point is a dimension function.
* `TopologicalSpace.exists_dimensionFunction_of_specializingMap`: a function whose
  composition with a continuous, surjective, specializing map is a dimension function is a
  dimension function.
* `AlgebraicGeometry.Space.exists_dimensionFunction_of_isFinite`: a function on the points of
  an algebraic space whose pullback along a surjective finite morphism is a dimension function
  is a dimension function.
* `AlgebraicGeometry.Space.exists_dimensionFunction_inducedDimensionValue_of_isFinite`: the
  previous result at the induced function `AlgebraicGeometry.Space.inducedDimensionValue` of
  Stacks 0EDN.

## Implementation notes

The statements are phrased with the conclusion `∃ d : DimensionFunction X, ∀ x, d x = δ x`,
which `TopologicalSpace.exists_dimensionFunction_iff` (Stacks 02I9) converts into the two
defining conditions.

## References

* [Stacks Project, Tag 02I9](https://stacks.math.columbia.edu/tag/02I9)
* [Stacks Project, Tag 02IB](https://stacks.math.columbia.edu/tag/02IB)
* [Stacks Project, Tag 02IC](https://stacks.math.columbia.edu/tag/02IC)
* [Stacks Project, Tag 0414](https://stacks.math.columbia.edu/tag/0414)
* [Stacks Project, Tag 0415](https://stacks.math.columbia.edu/tag/0415)
* [Stacks Project, Tag 0ED9](https://stacks.math.columbia.edu/tag/0ED9)
* [Stacks Project, Tag 0EDN](https://stacks.math.columbia.edu/tag/0EDN)
-/

@[expose] public section

open CategoryTheory

universe u

namespace TopologicalSpace

/-! ### Being a dimension function is local -/

/-- If every point of `X` has an open neighbourhood `U` on which `δ` restricts to a dimension
function of the subspace `U`, then `δ` is a dimension function on `X`. -/
theorem exists_dimensionFunction_of_cover {X : Type*} [TopologicalSpace X] (δ : X → ℤ)
    (h : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ d : DimensionFunction U, ∀ y : U, d y = δ y.1) :
    ∃ d : DimensionFunction X, ∀ x : X, d x = δ x := by
  rw [exists_dimensionFunction_iff]
  refine ⟨fun x y hxy hne => ?_, fun x y himm => ?_⟩
  · obtain ⟨U, hU, hyU, d, hd⟩ := h y
    have hxU : x ∈ U := hxy.mem_open hU hyU
    have hlt := d.strictAnti_specializes
      (Topology.IsInducing.subtypeVal.specializes_iff.mp
        (show ((⟨x, hxU⟩ : U) : X) ⤳ ((⟨y, hyU⟩ : U) : X) from hxy))
      (fun he => hne (congrArg Subtype.val he))
    rwa [hd, hd] at hlt
  · obtain ⟨U, hU, hyU, d, hd⟩ := h y
    have hstep := d.step_immediate (himm.subtype_of_isOpen hU hyU)
    rwa [hd, hd] at hstep

/-! ### Being a dimension function descends along a specializing surjection -/

/-- Under a specializing map, a specialization of the image of `x` is the image of a
specialization of `x`. -/
private theorem exists_specializes_of_specializingMap {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {g : X → Y} (hspec : SpecializingMap g) {x : X} {y : Y}
    (h : g x ⤳ y) : ∃ x' : X, x ⤳ x' ∧ g x' = y := by
  obtain ⟨x', hx', hgx'⟩ :=
    hspec.closure_singleton_subset x (specializes_iff_mem_closure.mp h)
  exact ⟨x', specializes_iff_mem_closure.mpr hx', hgx'⟩

/-- Let `g : X → Y` be continuous, surjective and specializing, and let `δ : Y → ℤ` be such that
`δ ∘ g` is a dimension function on `X`. Then `δ` is a dimension function on `Y`. -/
theorem exists_dimensionFunction_of_specializingMap {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {g : X → Y} (hcont : Continuous g) (hsurj : Function.Surjective g)
    (hspec : SpecializingMap g) (δ : Y → ℤ) (d : DimensionFunction X)
    (hd : ∀ x : X, d x = δ (g x)) :
    ∃ e : DimensionFunction Y, ∀ y : Y, e y = δ y := by
  have lift : ∀ {y y' : Y}, y ⤳ y' → ∃ x x' : X, x ⤳ x' ∧ g x = y ∧ g x' = y' := by
    intro y y' h
    obtain ⟨x, rfl⟩ := hsurj y
    obtain ⟨x', hxx', rfl⟩ := exists_specializes_of_specializingMap hspec h
    exact ⟨x, x', hxx', rfl, rfl⟩
  rw [exists_dimensionFunction_iff]
  refine ⟨fun y y' hyy' hne => ?_, fun y y' himm => ?_⟩
  · obtain ⟨x, x', hxx', rfl, rfl⟩ := lift hyy'
    have hlt := d.strictAnti_specializes hxx' fun he => hne (by rw [he])
    rwa [hd, hd] at hlt
  · obtain ⟨x, x', hxx', rfl, rfl⟩ := lift himm.1
    have himmx : IsImmediateSpecialization x x' := by
      refine ⟨hxx', fun he => himm.2.1 (by rw [he]), fun z hz hz' => ?_⟩
      rcases himm.2.2 (g z) (hz.map hcont) (hz'.map hcont) with hgz | hgz
      · refine Or.inl (by_contra fun hzx => ?_)
        have hlt := d.strictAnti_specializes hz fun he => hzx he.symm
        rw [hd, hd, hgz] at hlt
        exact lt_irrefl _ hlt
      · refine Or.inr (by_contra fun hzx' => ?_)
        have hlt := d.strictAnti_specializes hz' hzx'
        rw [hd, hd, hgz] at hlt
        exact lt_irrefl _ hlt
    have hstep := d.step_immediate himmx
    rwa [hd, hd] at hstep

end TopologicalSpace

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

open TopologicalSpace

/-- Let `q : Z ⟶ X` be a surjective finite morphism of algebraic spaces and let `δ` be a function
on the points of `X`. If the pullback of `δ` along the map on points of `q` is a dimension
function, then `δ` is a dimension function. -/
@[stacks 0ED9 "decency and local Noetherianity not needed"]
theorem exists_dimensionFunction_of_isFinite
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hZ : IsAlgebraicSpace B S hS Z) (q : Z ⟶ X) (hqfin : IsFinite B S hS q)
    (hqsurj : IsSurjective B S hS q) (δ : points B S hS X → ℤ)
    (hd : ∃ d : DimensionFunction (points B S hS Z), ∀ z : points B S hS Z,
      d z = δ (pointsMap B S hS Z q z)) :
    ∃ d : DimensionFunction (points B S hS X), ∀ x : points B S hS X, d x = δ x := by
  obtain ⟨d, hdz⟩ := hd
  exact exists_dimensionFunction_of_specializingMap (continuous_pointsMap B S hS q) hqsurj
    (isClosedMap_pointsMap_of_pullback_fst_id B S hS q
      (universallyClosed_of_isFinite B S hS hZ hX hqfin X hX (𝟙 X))).specializingMap δ d hdz

/-- Let `f : X ⟶ Y` be a morphism of presheaves on the big fppf site of `S` and let `δ` be a
function on the points of `Y`. If `q : Z ⟶ X` is a surjective finite morphism of algebraic spaces
and the induced function `AlgebraicGeometry.Space.inducedDimensionValue` for `f` and `δ` becomes
a dimension function after pulling it back along `q`, then it is a dimension function on the
points of `X`. -/
theorem exists_dimensionFunction_inducedDimensionValue_of_isFinite
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hZ : IsAlgebraicSpace B S hS Z) (δ : points B S hS Y → ℤ) (f : X ⟶ Y) (q : Z ⟶ X)
    (hqfin : IsFinite B S hS q) (hqsurj : IsSurjective B S hS q)
    (hd : ∃ d : DimensionFunction (points B S hS Z), ∀ z : points B S hS Z,
      d z = inducedDimensionValue B S hS δ f (pointsMap B S hS Z q z)) :
    ∃ d : DimensionFunction (points B S hS X), ∀ x : points B S hS X,
      d x = inducedDimensionValue B S hS δ f x :=
  exists_dimensionFunction_of_isFinite B S hS hX hZ q hqfin hqsurj _ hd

end AlgebraicGeometry.Space

end
