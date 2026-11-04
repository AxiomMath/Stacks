module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpChartLiftSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpChartSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpLiftChartKernel

/-!
# A comorphism through a thickening is realized by a morphism over an arbitrary base

Let `Z ⊆ X` be a thickening of algebraic spaces over a scheme `S` with inclusion `i : Z ⟶ X`,
let `c : X ⟶ W`, let `qb : W ⟶ Bas` and let `a : 𝒪_W ⟶ (i ≫ c)_*(i^{-1}𝒪_X)` be a morphism of
sheaves of rings.

`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/ThickeningSharpChartLiftSections.lean` glues
the chartwise morphisms attached to `a` into a single morphism `X ⟶ W` over `Bas` agreeing with
`c` on `Z`, *granted* that each chartwise morphism is a lift in the sense of
`AlgebraicGeometry.Space.IsChartLift` for the base morphisms `p : X ⟶ Bas` and `qb`.  This file
supplies that hypothesis, and so turns the gluing into an unconditional statement.

## The two clauses

Clause 2 of `AlgebraicGeometry.Space.IsChartLift` — agreement with `c` on the part of the chart
lying in `Z` — is `AlgebraicGeometry.Space.yoneda_map_comp_chart_hom_eq_restriction`, which
needs only that `a` has the comorphism of `i ≫ c` as its reduction.

Clause 1 — that the chartwise morphism is a morphism over `Bas` — is proved here.  The generic
results available give the triangle over `S`
(`AlgebraicGeometry.Space.thickeningLiftChartHom_comp_structureHom`) and, sharper, the triangle
over the target of the morphism carrying the *chart diagram*
(`AlgebraicGeometry.Space.yoneda_map_comp_chart_hom_comp_eq`), whose index of the base change
of that morphism is an ordinary datum rather than a chart of `W`.  Taking the morphism carrying
the chart diagram to be `qb` itself and converting the chart diagram supplied by
`AlgebraicGeometry.Space.HasAffineChartDiagram` into such an index with
`AlgebraicGeometry.Space.indexOfChartDiagram` gives the triangle over `Bas` for the morphism
`c ≫ qb`, which is `p`.

## Main results

* `AlgebraicGeometry.Space.comp_eq_of_thickeningLiftChartSiteHom_of_hasAffineChartDiagram`:
  **clause 1 of the lifting condition over an arbitrary base** — the chartwise morphism attached
  to `a` over an affine chart of `W` carrying an affine chart diagram over `qb` is a morphism
  over `Bas`.
* `AlgebraicGeometry.Space.isChartLift_thickeningLiftChartSiteHom`: **both clauses** — that
  chartwise morphism is a lift of the restriction of `c` to `Z` along the thickening.
* `AlgebraicGeometry.Space.exists_hom_of_thickeningLiftRingSheaf`: **the morphism of algebraic
  spaces recovered from `a`** — a morphism `ε : X ⟶ W` over `Bas` restricting to `c` on `Z`
  whose restriction to a chart is the chartwise morphism attached to `a`.

## Implementation notes

The affineness of the chart of `W` is restated at the index spelling before
`AlgebraicGeometry.Space.yoneda_map_comp_chart_hom_comp_eq` is applied: instance resolution does
not unfold `AlgebraicGeometry.Space.indexOfChartDiagram`, exactly as in
`AlgebraicGeometry.Space.exists_thickeningLiftChartSiteHom_of_hasAffineChartDiagram`.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map.
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3), diagrams of charts.
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK), thickenings.
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D), the sheaf of lifts.
* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0), the tag whose existence
  clause the recovered morphism is.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X W : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)

/-! ### Clause 1 of the lifting condition over an arbitrary base -/

/-- **Clause 1 of the lifting condition `AlgebraicGeometry.Space.IsChartLift` over an arbitrary
base.**  Let `qb : W ⟶ Bas` and let `p : X ⟶ Bas` be the composite `c ≫ qb`.  The section of `W`
over the chart `j` of `X` given by the morphism of charts attached to `a` followed by the chart
`V ⟶ W` is a morphism over `Bas`, as soon as `V` is affine, carries an affine chart diagram over
`qb`, and `a` agrees with the comorphism of `c` read through the thickening on the regular
functions read from `Bas`.

The chart diagram is turned into an index of the base change of `qb` by
`AlgebraicGeometry.Space.indexOfChartDiagram`, whose chart of `W` is the given chart `V`, and
`AlgebraicGeometry.Space.yoneda_map_comp_chart_hom_comp_eq` read at that index is the triangle
over `Bas` for `c ≫ qb`. -/
theorem comp_eq_of_thickeningLiftChartSiteHom_of_hasAffineChartDiagram
    (hZ : IsThickening B S hS X Z.1) (c : X ⟶ W)
    (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    {Bas : AlgebraicSpaces B S hS} (qb : W ⟶ Bas) (p : X ⟶ Bas) (hp : c ≫ qb = p)
    (hbase : ∀ (V : SmallEtale B S hS W.1)
        (s : ToType ((structureRingSheafInverseImage B S hS qb).obj.obj (op V))),
      a.hom.app (op V) ((structureSharpRingInverseImage B S hS qb).hom.app (op V) s) =
        (structureSharpThroughThickening B S hS Z c).hom.app (op V)
          ((structureSharpRingInverseImage B S hS qb).hom.app (op V) s))
    (V : SmallEtale B S hS W.1)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V))]
    (hV : HasAffineChartDiagram B S hS qb V)
    (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op)
    (ψ : (SmallEtale.toOver B S hS X.1).obj j.right.unop ⟶
      (SmallEtale.toOver B S hS W.1).obj V)
    (hψ : (BigFppfOver.toScheme B S hS).map ψ = thickeningLiftChartHom B S hS Z hZ c a V j) :
    (yoneda.map ψ ≫ V.1.hom) ≫ qb.hom = j.right.unop.1.hom ≫ p.hom := by
  obtain ⟨-, V', q, hq, hV'aff⟩ := hV
  let D : ChartDiagram B S hS W.1 Bas.1 qb.hom := ⟨V, V', q, hq.symm⟩
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((SmallEtale.toOver B S hS Bas.1).obj V')) := hV'aff
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj
      (indexOfChartDiagram B S hS qb D).right.unop)) := ‹IsAffine _›
  have hph : c.hom ≫ qb.hom = p.hom := congrArg (fun n : X ⟶ Bas ↦ n.hom) hp
  refine (yoneda_map_comp_chart_hom_comp_eq B S hS Z hZ c a qb V'
    (indexOfChartDiagram B S hS qb D) j (fun s ↦ hbase _ s) ψ hψ).trans ?_
  exact congrArg (fun z ↦ j.right.unop.1.hom ≫ z) hph

/-! ### Both clauses -/

/-- **The morphism of charts attached to `a` is a lift of the restriction of `c` to `Z`**, that
is a section of the sheaf of lifts of [Stacks Project, Tag 061D] over the chart of `X`, for the
base morphisms `p = c ≫ qb` and `qb`.

Clause 1 is
`AlgebraicGeometry.Space.comp_eq_of_thickeningLiftChartSiteHom_of_hasAffineChartDiagram` and
clause 2 is `AlgebraicGeometry.Space.yoneda_map_comp_chart_hom_eq_restriction`. -/
theorem isChartLift_thickeningLiftChartSiteHom
    (hZ : IsThickening B S hS X Z.1) (c : X ⟶ W)
    (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    (hred : a ≫ thickeningLiftReduction B S hS Z c =
      structureSharp B S hS (subspaceInclusion B S hS X Z ≫ c))
    {Bas : AlgebraicSpaces B S hS} (qb : W ⟶ Bas) (p : X ⟶ Bas) (hp : c ≫ qb = p)
    (hbase : ∀ (V : SmallEtale B S hS W.1)
        (s : ToType ((structureRingSheafInverseImage B S hS qb).obj.obj (op V))),
      a.hom.app (op V) ((structureSharpRingInverseImage B S hS qb).hom.app (op V) s) =
        (structureSharpThroughThickening B S hS Z c).hom.app (op V)
          ((structureSharpRingInverseImage B S hS qb).hom.app (op V) s))
    (V : SmallEtale B S hS W.1)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V))]
    (hV : HasAffineChartDiagram B S hS qb V)
    (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op)
    (ψ : (SmallEtale.toOver B S hS X.1).obj j.right.unop ⟶
      (SmallEtale.toOver B S hS W.1).obj V)
    (hψ : (BigFppfOver.toScheme B S hS).map ψ = thickeningLiftChartHom B S hS Z hZ c a V j) :
    IsChartLift B S hS p qb (Z.1.ι ≫ c.hom) j.right.unop (yoneda.map ψ ≫ V.1.hom) :=
  ⟨comp_eq_of_thickeningLiftChartSiteHom_of_hasAffineChartDiagram B S hS Z hZ c a qb p hp
      hbase V hV j ψ hψ,
    fun Ww k t hkt ↦
      yoneda_map_comp_chart_hom_eq_restriction B S hS Z hZ c a hred V j ψ hψ Ww k t hkt⟩

/-! ### The morphism recovered from the comorphism -/

/-- **The morphism of algebraic spaces recovered from a comorphism through the thickening.**
Let `a : 𝒪_W ⟶ (i ≫ c)_*(i^{-1}𝒪_X)` be a morphism of sheaves of rings whose reduction is the
comorphism of `i ≫ c` and which agrees with the comorphism of `c` read through the thickening on
the regular functions read from `Bas`.  Then there is a morphism `ε : X ⟶ W` over `Bas` whose
restriction to `Z` is `c` and whose restriction to any chart of `X` carrying an index over any
affine chart of `W` is the morphism of charts attached to `a`.

This is `AlgebraicGeometry.Space.exists_hom_eq_thickeningLiftChartSiteHom` with its hypothesis
on the chartwise morphisms discharged by
`AlgebraicGeometry.Space.isChartLift_thickeningLiftChartSiteHom`, read with the morphism
carrying the chart diagrams equal to `qb` itself. -/
theorem exists_hom_of_thickeningLiftRingSheaf
    (hZ : IsThickening B S hS X Z.1) (c : X ⟶ W)
    (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    (hred : a ≫ thickeningLiftReduction B S hS Z c =
      structureSharp B S hS (subspaceInclusion B S hS X Z ≫ c))
    {Bas : AlgebraicSpaces B S hS} (qb : W ⟶ Bas) (p : X ⟶ Bas) (hp : c ≫ qb = p)
    (hbase : ∀ (V : SmallEtale B S hS W.1)
        (s : ToType ((structureRingSheafInverseImage B S hS qb).obj.obj (op V))),
      a.hom.app (op V) ((structureSharpRingInverseImage B S hS qb).hom.app (op V) s) =
        (structureSharpThroughThickening B S hS Z c).hom.app (op V)
          ((structureSharpRingInverseImage B S hS qb).hom.app (op V) s)) :
    ∃ ε : X.1 ⟶ W.1, ε ≫ qb.hom = p.hom ∧ Z.1.ι ≫ ε = Z.1.ι ≫ c.hom ∧
      ∀ (V : SmallEtale B S hS W.1)
        [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V))]
        (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op)
        (ψ : (SmallEtale.toOver B S hS X.1).obj j.right.unop ⟶
          (SmallEtale.toOver B S hS W.1).obj V),
        (BigFppfOver.toScheme B S hS).map ψ = thickeningLiftChartHom B S hS Z hZ c a V j →
        j.right.unop.1.hom ≫ ε = yoneda.map ψ ≫ V.1.hom :=
  exists_hom_eq_thickeningLiftChartSiteHom B S hS Z hZ c a qb hbase p qb (Z.1.ι ≫ c.hom)
    fun V _ j ψ hV hψ ↦
      isChartLift_thickeningLiftChartSiteHom B S hS Z hZ c a hred qb p hp hbase V hV j ψ hψ

end AlgebraicGeometry.Space

end
