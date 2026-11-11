module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.SerreAffinenessCriterion.ClosedPoints
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointSmoothChart
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointsMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactPointRepresentative
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective

/-!
# Finite type points meet every locally closed subset (Stacks 06G2)

**Stacks 06G2** says that for an algebraic stack `𝒳` and a locally closed subset
`T ⊆ |𝒳|` of its point space (**Stacks 04XL**),
`T ≠ ∅ → T ∩ 𝒳_{ft-pts} ≠ ∅`, and that consequently for a *closed* subset `T` the
intersection `T ∩ 𝒳_{ft-pts}` is dense in `T`.

The set `𝒳_{ft-pts}` of finite type points is `AlgebraicGeometry.Stack.finiteTypePoints`
(**Stacks 06FY**).

## The source's route

This file follows the source's proof, which has two halves.

* The half proved here outright: *a nonempty algebraic stack has a finite type point*,
  `AlgebraicGeometry.Stack.exists_isFiniteTypePoint_of_nonempty`. This is the last step of the
  source's argument — "any nonempty affine scheme `U` with a smooth morphism towards `𝒵` has at
  least one closed point, hence `𝒵` has at least one finite type point by Stacks 06FZ". It is
  obtained from the smooth surjective scheme presentation of **Stacks 026O**
  (`AlgebraicGeometry.Stack.exists_smooth_surjective_schemeStack`), shrunk to an affine open
  chart, where a closed point exists because an affine scheme is a compact `T₀` space, and then
  fed to condition (2) of **Stacks 06FX**.

* The other half uses the *reduced induced substack structure* on a locally closed subset of
  `|𝒳|` (**Stacks 06FK**) and the fact that its inclusion is locally of finite type
  (**Stacks 06FV**). The predicate `AlgebraicGeometry.Stack.HasReducedInducedSubstacks` packages
  exactly what the source's proof uses of it: a locally-of-finite-type 1-morphism onto the
  subset. `StacksFrontier.AlgebraicGeometry.Stacks.ReducedInducedSubstackFiniteTypePoints` derives
  it from the inputs of `AlgebraicGeometry.Stack.exists_reducedInducedSubstack`.

The two theorems `nonempty_inter_finiteTypePoints` and `subset_closure_inter_finiteTypePoints`
below are the source's argument relative to that predicate. Both clauses of **Stacks 06G2** are
proved without it, by a direct affine-chart argument, in
`StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointsLocallyClosedChart`
(`AlgebraicGeometry.Stack.exists_mem_finiteTypePoints_of_isLocallyClosed`), and are stated
together as `AlgebraicGeometry.Stack.nonempty_inter_and_closure_inter_finiteTypePoints` in
`StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointsDense`.

## Main definitions

* `AlgebraicGeometry.Stack.HasReducedInducedSubstacks`: what the source's proof uses of
  **Stacks 06FK**.

## Main results

* `AlgebraicGeometry.Stack.exists_isFiniteTypePoint_of_nonempty`: a nonempty algebraic stack has
  a finite type point.
* `AlgebraicGeometry.Stack.nonempty_inter_finiteTypePoints`: the first clause of **Stacks 06G2**,
  by the source's route.
* `AlgebraicGeometry.Stack.subset_closure_inter_finiteTypePoints`: the second clause of
  **Stacks 06G2**, by the source's route.

## Implementation notes

The point space of `𝒳` carries the topology of **Stacks 04Y8**,
`AlgebraicGeometry.Stack.pointTopology`, which is not an instance; it is introduced with `letI`
in every statement that mentions `IsLocallyClosed`, `IsClosed` or `closure`, in the same style as
`AlgebraicGeometry.Stack.AlgebraicStacks.IsLocallyQuasiFinite` (**Stacks 06PU**).

The affine-chart auxiliaries `affChart`, `affChartHom`, `affChartHom_toScheme`,
`isAffine_affChart` and `smooth_affChartHom` repeat `private` declarations of
`StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointsSmoothUnion` and
`StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedSmoothLocal`, which are not visible from
here; they are `private` here too.

The density clause is stated as `T ⊆ closure (T ∩ 𝒳_{ft-pts})`, which is what "dense in `T`"
means for a subset of `T`: it is `Dense` in the subspace topology of `T` exactly when `T` is
contained in the closure of the intersection.

## References

* [Stacks Project, Tag 06FK](https://stacks.math.columbia.edu/tag/06FK)
* [Stacks Project, Tag 06FV](https://stacks.math.columbia.edu/tag/06FV)
* [Stacks Project, Tag 06FX](https://stacks.math.columbia.edu/tag/06FX)
* [Stacks Project, Tag 06FY](https://stacks.math.columbia.edu/tag/06FY)
* [Stacks Project, Tag 06FZ](https://stacks.math.columbia.edu/tag/06FZ)
* [Stacks Project, Tag 06G0](https://stacks.math.columbia.edu/tag/06G0)
* [Stacks Project, Tag 06G2](https://stacks.math.columbia.edu/tag/06G2)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Affine open charts of a scheme of the site -/

/-! ### A nonempty algebraic stack has a finite type point -/

/-- **A nonempty algebraic stack has a finite type point.**

This is the final step of the source's proof of **Stacks 06G2**. A smooth surjective scheme
presentation `U ⟶ 𝒳` exists by **Stacks 026O**; since `|𝒳|` is nonempty and the presentation is
surjective, `U` is nonempty. An affine open `V ⊆ U` containing a point of `U` is a compact `T₀`
space, hence has a closed point, and the inclusion of `V` is an open immersion and therefore
smooth, so the composite `V ⟶ 𝒳` is smooth by **Stacks 075V**. Condition (2) of **Stacks 06FX**
then makes the image of that closed point a finite type point of `𝒳`. -/
theorem exists_isFiniteTypePoint_of_nonempty (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hne : Nonempty (points B S hS 𝒳.val.val 𝒳.val.property)) :
    ∃ x : points B S hS 𝒳.val.val 𝒳.val.property, IsFiniteTypePoint.{u, w} B S hS 𝒳 x := by
  classical
  obtain ⟨U, a, hasm, hasurj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒳
  obtain ⟨x₀⟩ := hne
  obtain ⟨z₀, -⟩ := hasurj x₀
  let _ := pointTopology B S hS (schemeFibredCategory B S hS U)
  let _ : ∀ i : ((BigFppfOver.toScheme B S hS).obj U).affineOpens,
      TopologicalSpace (points B S hS (schemeFibredCategory B S hS (affChart U i)).val
        (schemeFibredCategory B S hS (affChart U i)).property) :=
    fun i => pointTopology B S hS (schemeFibredCategory B S hS (affChart U i))
  obtain ⟨-, ⟨V₀, hV₀, rfl⟩, hmem, -⟩ :=
    ((BigFppfOver.toScheme B S hS).obj U).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (pointsHomeomorphScheme B S hS U z₀)) isOpen_univ
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (affChart U ⟨V₀, hV₀⟩)) :=
    isAffine_affChart U ⟨V₀, hV₀⟩
  obtain ⟨v, -, hvclosed⟩ :=
    Stacks.SerreAffinenessCriterion.exists_isClosed_singleton_mem
      (X := (BigFppfOver.toScheme B S hS).obj (affChart U ⟨V₀, hV₀⟩)) isClosed_univ
      ⟨⟨pointsHomeomorphScheme B S hS U z₀, hmem⟩, Set.mem_univ _⟩
  obtain ⟨y, hy⟩ := (pointsHomeomorphScheme B S hS (affChart U ⟨V₀, hV₀⟩)).surjective v
  refine ⟨pointsMap B S hS (schemeFibredCategory B S hS (affChart U ⟨V₀, hV₀⟩)).val
      (schemeFibredCategory B S hS (affChart U ⟨V₀, hV₀⟩)).property 𝒳.val.property
      (schemeStackMap.{u, w} B S hS (affChartHom U ⟨V₀, hV₀⟩) ≫ a).hom.hom y, ?_⟩
  refine isFiniteTypePoint_of_exists_isClosed_smoothChart.{u, w} B S hS 𝒳 _
    ⟨affChart U ⟨V₀, hV₀⟩, schemeStackMap.{u, w} B S hS (affChartHom U ⟨V₀, hV₀⟩) ≫ a, y, ?_, ?_,
      rfl⟩
  · exact AlgebraicStacks.isSmooth_comp B S hS _ _
      (isSmooth_schemeStackMap.{u, w} B S hS (affChartHom U ⟨V₀, hV₀⟩)
        (smooth_affChartHom U ⟨V₀, hV₀⟩)) hasm
  · rw [hy]
    exact hvclosed

/-! ### The reduced induced substack structure -/

/-- **The input the source's proof of Stacks 06G2 takes from Stacks 06FK.**

**Stacks 06FK** (Properties of Stacks, Remark `remark-stack-structure-locally-closed-subset`)
equips a locally closed subset `T ⊆ |𝒳|` with its *reduced induced substack structure*: an
algebraic stack `𝒵` with an immersion `i : 𝒵 ⟶ 𝒳` whose image on points is `T`. Since an
immersion is locally of finite type (**Stacks 06FV**), what the proof of Stacks 06G2 uses is a
1-morphism onto `T` which is locally of finite type, and that is what this hypothesis supplies.

`StacksFrontier.AlgebraicGeometry.Stacks.ReducedInducedSubstackFiniteTypePoints` derives it from the
inputs of `AlgebraicGeometry.Stack.exists_reducedInducedSubstack`. -/
abbrev HasReducedInducedSubstacks (𝒳 : AlgebraicStacks.{u, w} B S hS) : Prop :=
  letI := pointTopology B S hS 𝒳.val
  ∀ T : Set (points B S hS 𝒳.val.val 𝒳.val.property), IsLocallyClosed T →
    ∃ (𝒵 : AlgebraicStacks.{u, w} B S hS) (i : 𝒵 ⟶ 𝒳),
      AlgebraicStacks.IsLocallyOfFiniteType B S hS i ∧
        Set.range (pointsMap B S hS 𝒵.val.val 𝒵.val.property 𝒳.val.property i.hom.hom) = T

/-! ### Stacks 06G2 -/

/-- **Stacks 06G2, first clause.** A nonempty locally closed subset of the point space of an
algebraic stack contains a finite type point.

The reduced induced substack `𝒵` of `T` is nonempty because its image on points is `T`, so it
has a finite type point by
`AlgebraicGeometry.Stack.exists_isFiniteTypePoint_of_nonempty`; the image of that point is a
finite type point of `𝒳` by **Stacks 06G0** and lies in `T`.

The substack enters through `AlgebraicGeometry.Stack.HasReducedInducedSubstacks`. The same
statement without that hypothesis is
`AlgebraicGeometry.Stack.exists_mem_finiteTypePoints_of_isLocallyClosed`. -/
theorem nonempty_inter_finiteTypePoints (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hsub : HasReducedInducedSubstacks.{u, w} B S hS 𝒳) :
    letI := pointTopology B S hS 𝒳.val
    ∀ T : Set (points B S hS 𝒳.val.val 𝒳.val.property), IsLocallyClosed T → T.Nonempty →
      (T ∩ finiteTypePoints B S hS 𝒳).Nonempty := by
  intro T hT hTne
  obtain ⟨𝒵, i, hilft, hirange⟩ := hsub T hT
  have hZne : Nonempty (points B S hS 𝒵.val.val 𝒵.val.property) := by
    obtain ⟨t, ht⟩ := hTne
    obtain ⟨z, -⟩ := hirange ▸ ht
    exact ⟨z⟩
  obtain ⟨z, hz⟩ := exists_isFiniteTypePoint_of_nonempty.{u, w} B S hS 𝒵 hZne
  refine ⟨pointsMap B S hS 𝒵.val.val 𝒵.val.property 𝒳.val.property i.hom.hom z, ?_, ?_⟩
  · exact hirange ▸ Set.mem_range_self z
  · exact mapsTo_finiteTypePoints.{u, w} B S hS i hilft hz

/-- **Stacks 06G2, second clause.** For a closed subset `T` of the point space of an algebraic
stack, the finite type points lying in `T` are dense in `T`.

This follows from the first clause by pure topology: given `x ∈ T` and an open `V` containing
`x`, the set `T ∩ V` is locally closed and nonempty, so it meets the set of finite type points,
which is exactly the statement that `V` meets `T ∩ 𝒳_{ft-pts}`. The same statement without the
hypothesis `hsub` is `AlgebraicGeometry.Stack.subset_closure_inter_finiteTypePoints_of_isClosed`. -/
theorem subset_closure_inter_finiteTypePoints (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hsub : HasReducedInducedSubstacks.{u, w} B S hS 𝒳) :
    letI := pointTopology B S hS 𝒳.val
    ∀ T : Set (points B S hS 𝒳.val.val 𝒳.val.property), IsClosed T →
      T ⊆ closure (T ∩ finiteTypePoints B S hS 𝒳) := by
  let _ := pointTopology B S hS 𝒳.val
  intro T hT x hx
  rw [mem_closure_iff]
  intro V hV hxV
  obtain ⟨t, ⟨htT, htV⟩, htft⟩ :=
    nonempty_inter_finiteTypePoints.{u, w} B S hS 𝒳 hsub (T ∩ V)
      (hT.isLocallyClosed.inter hV.isLocallyClosed) ⟨x, hx, hxV⟩
  exact ⟨t, htV, htT, htft⟩

end AlgebraicGeometry.Stack

end
