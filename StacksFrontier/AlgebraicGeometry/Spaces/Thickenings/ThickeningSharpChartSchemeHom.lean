module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpChartRing
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDerivationAction

/-!
# The morphism of charts attached to a comorphism through a thickening

Let `Z ⊆ X` be a thickening of algebraic spaces over a scheme `S` with inclusion `i : Z ⟶ X`,
let `c : X ⟶ W`, and let `a : 𝒪_W ⟶ (i ≫ c)_*(i^{-1}𝒪_X)` be any morphism of sheaves of rings
into the common target in which the comorphisms of morphisms agreeing on `Z` are compared.

`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/ThickeningSharpChartRing.lean` attaches to
`a`, an étale scheme chart `V` of `W` and an étale scheme chart of `X` above `X ×_W V`, a
homomorphism `Γ(V, ⊤) ⟶ Γ(V', ⊤)` of regular functions.  When `V` is **affine** a morphism into
it is the same thing as such a homomorphism, by `Stacks.Thickenings.homOfAppTop` and
`AlgebraicGeometry.ext_of_isAffine`.  So over an affine chart of `W` the datum `a` produces an
honest morphism of schemes `V' ⟶ V`, and for `a` the comorphism of `c` read through the
thickening that morphism is the one `c` itself induces on charts.

This is the step at which the sheaf-theoretic side of [Stacks Project, Tag 0618] — a
prescribed comorphism — becomes a geometric object, and it is the reason the development's
deformation-theoretic statements for affine schemes are applicable to a morphism of algebraic
spaces at all.

## Main definitions

* `AlgebraicGeometry.Space.thickeningLiftChartHomAppTop`: the map of global regular functions
  of the two charts attached to `a`, at the spelling `Γ(V, ⊤) ⟶ Γ(V', ⊤)`.
* `AlgebraicGeometry.Space.thickeningLiftChartHom`: the morphism of schemes `V' ⟶ V` attached
  to `a` over an affine étale chart `V` of `W`.

## Main results

* `AlgebraicGeometry.Space.thickeningLiftChartHom_appTop`: it acts on regular functions as the
  given map.
* `AlgebraicGeometry.Space.thickeningLiftChartHom_structureSharpThroughThickening`: **for the
  comorphism of `c` read through the thickening it is the morphism of charts `c` induces**,
  `AlgebraicGeometry.Space.chartBaseChangeMap`.
* `AlgebraicGeometry.Space.thickeningLiftChartAppTop_eq_of_thickeningLiftChartHom_eq`:
  **conversely, the attached morphism of charts determines the map of regular functions**, so a
  morphism whose attached morphisms of charts are those of `c` is, by
  `AlgebraicGeometry.Space.eq_structureSharpThroughThickening_of_thickeningLiftChartAppTop`, the
  comorphism of `c` read through the thickening.

## Implementation notes

The affineness of the chart is an instance argument on the *underlying scheme* of the chart,
which is the form in which the development's affine charts carry it; no affineness is asked of
`X`, `W`, `Z` or `S`.

`AlgebraicGeometry.Space.thickeningLiftChartHom_structureSharpThroughThickening` is proved by
`AlgebraicGeometry.ext_of_isAffine` from
`AlgebraicGeometry.Space.thickeningLiftChartAppTop_structureSharpThroughThickening`: both sides
act on regular functions as pullback along
`AlgebraicGeometry.Space.chartBaseChangeMap`, the left by
`Stacks.Thickenings.homOfAppTop_appTop` and the right because the structure sheaf of the small
étale site *is* global regular functions on the charts, which is the definitional identification
`AlgebraicGeometry.Space.chartRestrict_eq_appTop` records for restriction maps.

**What this does not give.**  The morphism produced is a morphism of *schemes*.  To be a
morphism of the big fppf category over `S` — and so to compose with the chart `V ⟶ W` and give
a section of `W` over `V'` — it must commute with the structure morphisms to `S`, which is the
hypothesis of `AlgebraicGeometry.BigFppfOver.exists_hom_of_comp_eq`.  That triangle is *not*
automatic for an arbitrary `a`: the chart map of regular functions of an arbitrary morphism of
sheaves of rings need not be a map over the base.  It holds for the `a` the lifting problem
produces, whose chart map differs from that of a morphism over `S` by a derivation killing the
functions read from the base; deriving the triangle from that is not done here.

**No `@[stacks]` attribute is placed.**  As in the two files this one extends, what is proved
is a comparison of two readings of [Stacks Project, Tag 03G8] internal to this development.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map.
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3), diagrams of charts.
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK), thickenings.
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618), the correspondence
  between lifts and linear maps.
* [Stacks Project, Tag 0CKE](https://stacks.math.columbia.edu/tag/0CKE), the tag this step is an
  input of.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X W : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)

/-- **The map of global regular functions of an affine étale chart of `W` attached to a
morphism `a : 𝒪_W ⟶ (i ≫ c)_*(i^{-1}𝒪_X)` of sheaves of rings**, as a morphism of
`CommRingCat`: the structure sheaf of the small étale site is global regular functions on the
charts, so `AlgebraicGeometry.Space.thickeningLiftChartAppTop` is already a map of the global
regular functions of the two charts, and this records it at that spelling. -/
noncomputable def thickeningLiftChartHomAppTop (hZ : IsThickening B S hS X Z.1) (c : X ⟶ W)
    (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    (V : SmallEtale B S hS W.1)
    (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op) :
    Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V),
        (⊤ : ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS W.1).obj V)).Opens)) ⟶
      Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS X.1).obj j.right.unop),
        (⊤ : ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS X.1).obj j.right.unop)).Opens)) :=
  CommRingCat.ofHom (thickeningLiftChartAppTop B S hS Z hZ c a V j)

/-- **The morphism of schemes `V' ⟶ V` attached to a morphism
`a : 𝒪_W ⟶ (i ≫ c)_*(i^{-1}𝒪_X)` of sheaves of rings and an étale scheme chart `j` of `X`
above `X ×_W V`, for `V` an affine étale chart of `W`:** the morphism into the affine scheme `V`
whose map of global regular functions is
`AlgebraicGeometry.Space.thickeningLiftChartAppTop`. -/
noncomputable def thickeningLiftChartHom (hZ : IsThickening B S hS X Z.1) (c : X ⟶ W)
    (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    (V : SmallEtale B S hS W.1)
    (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V))] :
    (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj j.right.unop) ⟶
      (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V) :=
  Stacks.Thickenings.homOfAppTop (thickeningLiftChartHomAppTop B S hS Z hZ c a V j)

/-- The attached morphism of charts acts on regular functions as the given map. -/
@[simp]
theorem thickeningLiftChartHom_appTop (hZ : IsThickening B S hS X Z.1) (c : X ⟶ W)
    (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    (V : SmallEtale B S hS W.1)
    (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V))] :
    (thickeningLiftChartHom B S hS Z hZ c a V j).appTop =
      thickeningLiftChartHomAppTop B S hS Z hZ c a V j :=
  Stacks.Thickenings.homOfAppTop_appTop _

/-- **For the comorphism of `c` read through the thickening the attached morphism of charts is
the one `c` induces**, `AlgebraicGeometry.Space.chartBaseChangeMap`: both act on regular
functions as pullback along it, and a morphism into an affine scheme is determined by its map of
regular functions. -/
theorem thickeningLiftChartHom_structureSharpThroughThickening
    (hZ : IsThickening B S hS X Z.1) (c : X ⟶ W) (V : SmallEtale B S hS W.1)
    (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V))] :
    thickeningLiftChartHom B S hS Z hZ c
          (structureSharpThroughThickening B S hS Z c) V j =
      (BigFppfOver.toScheme B S hS).map (chartBaseChangeMap B S hS c V j) :=
  AlgebraicGeometry.ext_of_isAffine
    ((thickeningLiftChartHom_appTop B S hS Z hZ c
          (structureSharpThroughThickening B S hS Z c) V j).trans
      (CommRingCat.hom_ext (RingHom.ext fun b ↦
        DFunLike.congr_fun
          (thickeningLiftChartAppTop_structureSharpThroughThickening B S hS Z hZ c V j) b)))

/-- **The attached morphism of charts determines the map of regular functions.**  Over an
affine chart the two determine one another, so a morphism `a` whose attached morphism of charts
over `V` and `j` is the one `c` induces has, over `V` and `j`, the chartwise pullback of regular
functions for its map.

This is the per-chart converse of
`AlgebraicGeometry.Space.thickeningLiftChartHom_structureSharpThroughThickening`.  Fed to
`AlgebraicGeometry.Space.eq_structureSharpThroughThickening_of_thickeningLiftChartAppTop` at
every chart it identifies `a` with the comorphism of `c` read through the thickening; it is left
per-chart because the affineness is an instance argument, and a consumer supplies it one chart
at a time. -/
theorem thickeningLiftChartAppTop_eq_of_thickeningLiftChartHom_eq
    (hZ : IsThickening B S hS X Z.1) (c : X ⟶ W)
    (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    (V : SmallEtale B S hS W.1)
    (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V))]
    (h : thickeningLiftChartHom B S hS Z hZ c a V j =
      (BigFppfOver.toScheme B S hS).map (chartBaseChangeMap B S hS c V j)) :
    thickeningLiftChartAppTop B S hS Z hZ c a V j = chartPullbackRingHom B S hS c V j :=
  congrArg
    (fun m : Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V),
          (⊤ : ((BigFppfOver.toScheme B S hS).obj
            ((SmallEtale.toOver B S hS W.1).obj V)).Opens)) ⟶
        Γ((BigFppfOver.toScheme B S hS).obj
            ((SmallEtale.toOver B S hS X.1).obj j.right.unop),
          (⊤ : ((BigFppfOver.toScheme B S hS).obj
            ((SmallEtale.toOver B S hS X.1).obj j.right.unop)).Opens)) ↦ m.hom)
    ((thickeningLiftChartHom_appTop B S hS Z hZ c a V j).symm.trans
      (congrArg
        (fun m : (BigFppfOver.toScheme B S hS).obj
              ((SmallEtale.toOver B S hS X.1).obj j.right.unop) ⟶
            (BigFppfOver.toScheme B S hS).obj
              ((SmallEtale.toOver B S hS W.1).obj V) ↦ m.appTop) h))

end AlgebraicGeometry.Space

end
