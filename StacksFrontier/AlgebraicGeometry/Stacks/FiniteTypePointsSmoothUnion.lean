module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointSmoothChart
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactPointRepresentative
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointsMorphism

/-!
# The finite type points of an algebraic stack and its smooth scheme charts (Stacks 06FZ)

**Stacks 06FZ** states that the set `𝒳_{ft-pts}` of finite type points of an algebraic stack `𝒳`
over `S` (**Stacks 06FY**, `AlgebraicGeometry.Stack.finiteTypePoints`) is the union
`⋃_{φ : U ⟶ 𝒳 smooth} |φ|(U₀)` of the images of the sets `U₀` of closed points of the schemes
`U` carrying a smooth 1-morphism to `𝒳`, and that the union is unchanged when `U` is restricted
to range over the *affine* schemes smooth over `𝒳`.

Both inclusions and the agreement of the two ranges are proved here, and hence the set equality
itself, for both ranges. The inclusion `⋃ … ⊆ 𝒳_{ft-pts}` is the content of condition (2) of
**Stacks 06FX** implying condition (1); the inclusion `𝒳_{ft-pts} ⊆ ⋃ …` is condition (1) of
Stacks 06FX implying condition (2), i.e.
`AlgebraicGeometry.Stack.exists_isClosed_smoothChart_of_isFiniteTypePoint` of
`StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointSmoothChart`, repackaged as a subset
relation.

The point of `U` that the source writes `u ∈ U` is read through
`AlgebraicGeometry.Stack.pointsHomeomorphScheme`, the identification of the point space of
Stacks 04XL of the algebraic stack of `U` with the topological space of `U`, so `U₀` is the
preimage under that identification of the closed points of `U`.

## Main definitions

* `AlgebraicGeometry.Stack.smoothChartClosedPoints`: the union `⋃_{φ : U ⟶ 𝒳 smooth} |φ|(U₀)`
  over the schemes of the site smooth over `𝒳`.
* `AlgebraicGeometry.Stack.affineSmoothChartClosedPoints`: the same union over the affine schemes
  of the site smooth over `𝒳`.

## Main results

* `AlgebraicGeometry.Stack.affineSmoothChartClosedPoints_eq_smoothChartClosedPoints`:
  **Stacks 06FZ**, the two ranges give the same union.
* `AlgebraicGeometry.Stack.smoothChartClosedPoints_subset_finiteTypePoints`:
  **Stacks 06FZ**, the union over all schemes is contained in `𝒳_{ft-pts}`.
* `AlgebraicGeometry.Stack.finiteTypePoints_subset_smoothChartClosedPoints`:
  **Stacks 06FZ**, `𝒳_{ft-pts}` is contained in the union over all schemes.
* `AlgebraicGeometry.Stack.finiteTypePoints_eq_smoothChartClosedPoints`:
  **Stacks 06FZ**, the set equality `𝒳_{ft-pts} = ⋃_{φ : U ⟶ 𝒳 smooth} |φ|(U₀)`.
* `AlgebraicGeometry.Stack.affineSmoothChartClosedPoints_subset_finiteTypePoints`:
  the union over affine schemes is contained in `𝒳_{ft-pts}`.
* `AlgebraicGeometry.Stack.finiteTypePoints_eq_affineSmoothChartClosedPoints`:
  **Stacks 06FZ**, the same set equality with `U` restricted to the affine schemes of the site.

## Implementation notes

The agreement of the two ranges is proved by shrinking a chart to an affine open neighbourhood of
the given closed point. A closed point of `U` lying in an open subscheme `V` is closed in `V`,
because it is the preimage of itself along the injective continuous inclusion; the inclusion of an
affine open is an open immersion, hence smooth, and so induces a smooth 1-morphism of the
represented algebraic stacks whose composite with the original chart is smooth by **Stacks 075V**.
The point of the affine open which the given point of `U` names is produced from surjectivity of
`AlgebraicGeometry.Stack.pointsHomeomorphScheme`, and is carried to the given point by the
naturality of that identification.

The auxiliaries `affChart`, `affChartHom`, `affChartHom_toScheme`, `isAffine_affChart` and
`smooth_affChartHom` repeat `private` declarations of
`StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedSmoothLocal`, which are not visible from
here; they are `private` here too.

## The inclusion `𝒳_{ft-pts} ⊆ ⋃ …`

That every finite type point of `𝒳` is the image of a closed point of a scheme smooth over `𝒳` is
condition (1) of Stacks 06FX implying condition (2), i.e.
`AlgebraicGeometry.Stack.exists_isClosed_smoothChart_of_isFiniteTypePoint`, which is registered
under Stacks 06FX. That statement exhibits for a finite type point exactly the chart, closed point
and smooth 1-morphism whose existence membership of the union asserts, so
`finiteTypePoints_subset_smoothChartClosedPoints` is its restatement as a subset relation, and
carries the Stacks 06FZ key for this direction of the set equality.

## References

* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 06FX](https://stacks.math.columbia.edu/tag/06FX)
* [Stacks Project, Tag 06FY](https://stacks.math.columbia.edu/tag/06FY)
* [Stacks Project, Tag 06FZ](https://stacks.math.columbia.edu/tag/06FZ)
* [Stacks Project, Tag 075V](https://stacks.math.columbia.edu/tag/075V)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Affine open charts of a scheme of the site -/

/-- The map on points of a composite of 1-morphisms of algebraic stacks over `S` is the composite
of the maps on points. -/
private theorem pointsMap_comp_hom {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵) (z : points B S hS 𝒳.val.val 𝒳.val.property) :
    pointsMap B S hS 𝒴.val.val 𝒴.val.property 𝒵.val.property g.hom.hom
        (pointsMap B S hS 𝒳.val.val 𝒳.val.property 𝒴.val.property f.hom.hom z) =
      pointsMap B S hS 𝒳.val.val 𝒳.val.property 𝒵.val.property (f ≫ g).hom.hom z := by
  induction z using Quotient.inductionOn with
  | h p => rfl

/-- A closed point of a scheme lying in an open subscheme is a closed point of that open
subscheme. -/
private theorem isClosed_singleton_mk {X : Scheme.{u}} (V : X.Opens) {x : X} (hx : x ∈ V)
    (hc : IsClosed ({x} : Set X)) :
    IsClosed ({(⟨x, hx⟩ : V.toScheme)} : Set V.toScheme) := by
  rw [show ({(⟨x, hx⟩ : V.toScheme)} : Set V.toScheme) = Subtype.val ⁻¹' ({x} : Set X) from
    Set.ext fun y => Subtype.ext_iff]
  exact hc.preimage continuous_subtype_val

/-- A closed point of a scheme of the site is the image of a closed point of an affine open chart
of that scheme. -/
private theorem exists_affChart_isClosed (U : BigFppfOver B S hS)
    (z : points B S hS (schemeFibredCategory B S hS U).val
      (schemeFibredCategory B S hS U).property)
    (hz : IsClosed ({pointsHomeomorphScheme B S hS U z} :
      Set ((BigFppfOver.toScheme B S hS).obj U))) :
    ∃ (i : ((BigFppfOver.toScheme B S hS).obj U).affineOpens)
      (y : points B S hS (schemeFibredCategory B S hS (affChart U i)).val
        (schemeFibredCategory B S hS (affChart U i)).property),
      IsClosed ({pointsHomeomorphScheme B S hS (affChart U i) y} :
          Set ((BigFppfOver.toScheme B S hS).obj (affChart U i))) ∧
        pointsMap B S hS (schemeFibredCategory B S hS (affChart U i)).val
          (schemeFibredCategory B S hS (affChart U i)).property
          (schemeFibredCategory B S hS U).property
          (schemeStackMap.{u, w} B S hS (affChartHom U i)).hom.hom y = z := by
  let _ := pointTopology B S hS (schemeFibredCategory B S hS U)
  let _ : ∀ i : ((BigFppfOver.toScheme B S hS).obj U).affineOpens,
      TopologicalSpace (points B S hS (schemeFibredCategory B S hS (affChart U i)).val
        (schemeFibredCategory B S hS (affChart U i)).property) :=
    fun i => pointTopology B S hS (schemeFibredCategory B S hS (affChart U i))
  obtain ⟨-, ⟨V₀, hV₀, rfl⟩, huV₀, -⟩ :=
    ((BigFppfOver.toScheme B S hS).obj U).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (pointsHomeomorphScheme B S hS U z)) isOpen_univ
  obtain ⟨y, hy⟩ := (pointsHomeomorphScheme B S hS (affChart U ⟨V₀, hV₀⟩)).surjective
    ⟨pointsHomeomorphScheme B S hS U z, huV₀⟩
  refine ⟨⟨V₀, hV₀⟩, y, ?_, ?_⟩
  · rw [hy]
    exact isClosed_singleton_mk V₀ huV₀ hz
  · refine (pointsHomeomorphScheme B S hS U).injective ?_
    refine (pointsHomeomorphScheme_naturality B S hS (affChartHom U ⟨V₀, hV₀⟩) y).trans ?_
    rw [hy]
    rfl

/-! ### The union over the smooth scheme charts -/

/-- The union `⋃_{φ : U ⟶ 𝒳 smooth} |φ|(U₀)` of the images of the sets `U₀` of closed points of
the schemes `U` of the site carrying a smooth 1-morphism to an algebraic stack `𝒳` over `S`. -/
abbrev smoothChartClosedPoints (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    Set (points B S hS 𝒳.val.val 𝒳.val.property) :=
  ⋃ (U : BigFppfOver B S hS) (φ : schemeStack.{u, w} B S hS U ⟶ 𝒳)
      (_ : AlgebraicStacks.IsSmooth B S hS φ),
    pointsMap B S hS (schemeFibredCategory B S hS U).val
        (schemeFibredCategory B S hS U).property 𝒳.val.property φ.hom.hom ''
      (⇑(pointsHomeomorphScheme B S hS U) ⁻¹'
        {u | IsClosed ({u} : Set ((BigFppfOver.toScheme B S hS).obj U))})

/-- The union `⋃_{φ : U ⟶ 𝒳 smooth} |φ|(U₀)` of the preceding definition, with `U` restricted to
range over the affine schemes of the site. -/
abbrev affineSmoothChartClosedPoints (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    Set (points B S hS 𝒳.val.val 𝒳.val.property) :=
  ⋃ (U : BigFppfOver B S hS) (_ : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
      (φ : schemeStack.{u, w} B S hS U ⟶ 𝒳) (_ : AlgebraicStacks.IsSmooth B S hS φ),
    pointsMap B S hS (schemeFibredCategory B S hS U).val
        (schemeFibredCategory B S hS U).property 𝒳.val.property φ.hom.hom ''
      (⇑(pointsHomeomorphScheme B S hS U) ⁻¹'
        {u | IsClosed ({u} : Set ((BigFppfOver.toScheme B S hS).obj U))})

/-- **Stacks 06FZ**, the agreement of the two ranges. The union of the images of the closed points
of the schemes of the site smooth over an algebraic stack `𝒳` over `S` is unchanged when the
schemes are restricted to the affine ones.

A closed point of a chart `U` is a closed point of an affine open `V ⊆ U` containing it, the
inclusion of `V` is an open immersion and hence smooth, and the composite of the induced
1-morphism with the chart is smooth by Stacks 075V. -/
@[stacks 06FZ "the union over all schemes smooth over the stack equals the union over the \
affine schemes smooth over it"]
theorem affineSmoothChartClosedPoints_eq_smoothChartClosedPoints
    (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    affineSmoothChartClosedPoints.{u, w} B S hS 𝒳 =
      smoothChartClosedPoints.{u, w} B S hS 𝒳 := by
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨U, -, φ, hφ, hmem⟩ := hx
    exact Set.mem_iUnion.2 ⟨U, Set.mem_iUnion.2 ⟨φ, Set.mem_iUnion.2 ⟨hφ, hmem⟩⟩⟩
  · intro x hx
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_preimage, Set.mem_ofPred_eq] at hx
    obtain ⟨U, φ, hφ, z, hzclosed, hzx⟩ := hx
    obtain ⟨i, y, hyclosed, hyz⟩ := exists_affChart_isClosed.{u, w} B S hS U z hzclosed
    refine Set.mem_iUnion.2 ⟨affChart U i, Set.mem_iUnion.2 ⟨isAffine_affChart U i,
      Set.mem_iUnion.2 ⟨schemeStackMap.{u, w} B S hS (affChartHom U i) ≫ φ,
        Set.mem_iUnion.2 ⟨AlgebraicStacks.isSmooth_comp B S hS _ _
          (isSmooth_schemeStackMap.{u, w} B S hS (affChartHom U i) (smooth_affChartHom U i)) hφ,
          ⟨y, hyclosed, ?_⟩⟩⟩⟩⟩
    rw [← pointsMap_comp_hom.{u, w} B S hS (schemeStackMap.{u, w} B S hS (affChartHom U i)) φ y,
      hyz]
    exact hzx

/-- **Stacks 06FZ**, the inclusion of the union in the set of finite type points. Every image of a
closed point of a scheme of the site smooth over an algebraic stack `𝒳` over `S` is a finite type
point of `𝒳` (Stacks 06FY).

This is condition (2) of Stacks 06FX implying condition (1). -/
@[stacks 06FZ "the inclusion of the union over all schemes smooth over the stack in the set of \
finite type points, i.e. the ⊇ direction of the set equality"]
theorem smoothChartClosedPoints_subset_finiteTypePoints
    (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    smoothChartClosedPoints.{u, w} B S hS 𝒳 ⊆ finiteTypePoints B S hS 𝒳 := by
  intro x hx
  simp only [Set.mem_iUnion, Set.mem_image, Set.mem_preimage, Set.mem_ofPred_eq] at hx
  obtain ⟨U, φ, hφ, z, hz, hzx⟩ := hx
  exact isFiniteTypePoint_of_exists_isClosed_smoothChart.{u, w} B S hS 𝒳 x ⟨U, φ, z, hφ, hz, hzx⟩

/-- **Stacks 06FZ**, the inclusion of the set of finite type points in the union. Every finite
type point of an algebraic stack `𝒳` over `S` (Stacks 06FY) is the image of a closed point of a
scheme of the site smooth over `𝒳`.

This is the restatement as a subset relation of condition (1) of Stacks 06FX implying
condition (2). -/
@[stacks 06FZ "the inclusion of the set of finite type points in the union over all schemes \
smooth over the stack, i.e. the ⊆ direction of the set equality"]
theorem finiteTypePoints_subset_smoothChartClosedPoints
    (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    finiteTypePoints B S hS 𝒳 ⊆ smoothChartClosedPoints.{u, w} B S hS 𝒳 := by
  intro x hx
  obtain ⟨U, φ, z, hφ, hz, hzx⟩ :=
    exists_isClosed_smoothChart_of_isFiniteTypePoint.{u, w} B S hS 𝒳 x hx
  exact Set.mem_iUnion.2 ⟨U, Set.mem_iUnion.2 ⟨φ, Set.mem_iUnion.2 ⟨hφ, ⟨z, hz, hzx⟩⟩⟩⟩

/-- **Stacks 06FZ**, the set equality. The set `𝒳_{ft-pts}` of finite type points of an algebraic
stack `𝒳` over `S` is the union `⋃_{φ : U ⟶ 𝒳 smooth} |φ|(U₀)` of the images of the sets of
closed points of the schemes of the site smooth over `𝒳`. -/
@[stacks 06FZ "the set equality 𝒳_{ft-pts} = ⋃_{φ : U ⟶ 𝒳 smooth} |φ|(U₀) over all schemes \
smooth over the stack"]
theorem finiteTypePoints_eq_smoothChartClosedPoints
    (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    finiteTypePoints B S hS 𝒳 = smoothChartClosedPoints.{u, w} B S hS 𝒳 :=
  Set.Subset.antisymm (finiteTypePoints_subset_smoothChartClosedPoints.{u, w} B S hS 𝒳)
    (smoothChartClosedPoints_subset_finiteTypePoints.{u, w} B S hS 𝒳)

/-- The union over the affine schemes of the site smooth over an algebraic stack `𝒳` over `S` is
contained in the set of finite type points of `𝒳`. -/
@[stacks 06FZ "the inclusion of the union over the affine schemes smooth over the stack in the \
set of finite type points, i.e. the ⊇ direction of the set equality for the affine range"]
theorem affineSmoothChartClosedPoints_subset_finiteTypePoints
    (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    affineSmoothChartClosedPoints.{u, w} B S hS 𝒳 ⊆ finiteTypePoints B S hS 𝒳 :=
  (affineSmoothChartClosedPoints_eq_smoothChartClosedPoints.{u, w} B S hS 𝒳).subset.trans
    (smoothChartClosedPoints_subset_finiteTypePoints.{u, w} B S hS 𝒳)

/-- **Stacks 06FZ**, the set equality for the affine range. The set `𝒳_{ft-pts}` of finite type
points of an algebraic stack `𝒳` over `S` is the union `⋃_{φ : U ⟶ 𝒳 smooth} |φ|(U₀)` of the
images of the sets of closed points of the *affine* schemes of the site smooth over `𝒳`. -/
@[stacks 06FZ "the set equality 𝒳_{ft-pts} = ⋃_{φ : U ⟶ 𝒳 smooth} |φ|(U₀) over the affine \
schemes smooth over the stack"]
theorem finiteTypePoints_eq_affineSmoothChartClosedPoints
    (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    finiteTypePoints B S hS 𝒳 = affineSmoothChartClosedPoints.{u, w} B S hS 𝒳 :=
  (finiteTypePoints_eq_smoothChartClosedPoints.{u, w} B S hS 𝒳).trans
    (affineSmoothChartClosedPoints_eq_smoothChartClosedPoints.{u, w} B S hS 𝒳).symm

end AlgebraicGeometry.Stack

end
