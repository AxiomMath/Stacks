module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpChartProjection
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionRing

/-!
# The chart reading of a comorphism through a thickening, as a map of regular functions

Let `Z ⊆ X` be a thickening of algebraic spaces over a scheme `S` with inclusion `i : Z ⟶ X`,
let `c : X ⟶ W` be a morphism, and let `a : 𝒪_W ⟶ (i ≫ c)_*(i^{-1}𝒪_X)` be any morphism of
sheaves of rings into the common target in which the comorphisms of morphisms agreeing on `Z`
are compared.

`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/ThickeningSharpChartProjection.lean` reads
such an `a` over a commutative diagram of étale scheme charts, and shows that for
`a = c^♯` read through the thickening the reading is the unit `η : 𝒪_X ⟶ i_*i^{-1}𝒪_X` at the
pullback of the regular function along the vertical scheme morphism of the diagram.  Both of
those readings are maps of *sets*: the chart projection
`AlgebraicGeometry.Space.directImageChartProjection` is a natural transformation of set-valued
sections functors, and the sections of a direct image carry the transported ring structure
`CategoryTheory.Sheaf.ringObjRing`.

This file makes the reading a **homomorphism of rings**, and composes it with the inverse of the
unit to land it on the regular functions of the chart.  So every such `a` has, over every
commutative diagram of étale scheme charts, an honest map

`Γ(V, ⊤) ⟶ Γ(V', ⊤)`

of global sections of schemes, which for `a = c^♯` read through the thickening is pullback along
the vertical morphism of the diagram, and which determines `a` completely.

## Main definitions

* `AlgebraicGeometry.Space.thickeningLiftChartRingHom`: the chart reading of the sections of
  `(i ≫ c)_*(i^{-1}𝒪_X)`, **as a homomorphism of rings**.
* `AlgebraicGeometry.Space.thickeningRingUnitChartRingEquiv`: the unit of a thickening on the
  sections over an étale chart, as a **ring isomorphism** `𝒪_X(V') ≅ (i_*i^{-1}𝒪_X)(V')`.
* `AlgebraicGeometry.Space.thickeningLiftChartAppTop`: the resulting homomorphism
  `Γ(V, ⊤) ⟶ Γ(V', ⊤)` of regular functions attached to a morphism
  `a : 𝒪_W ⟶ (i ≫ c)_*(i^{-1}𝒪_X)` and a chart of `X` above `X ×_W V`.

## Main results

* `AlgebraicGeometry.Space.thickeningLiftChartAppTop_structureSharpThroughThickening`: **for the
  comorphism read through the thickening the map of regular functions is pullback of regular
  functions** along the induced morphism of charts.
* `AlgebraicGeometry.Space.eq_structureSharpThroughThickening_of_thickeningLiftChartAppTop`:
  **conversely, a morphism whose maps of regular functions are those pullbacks is the comorphism
  read through the thickening.**

## Implementation notes

The ring-level chart projection is `Stacks.Sheaves.ToposPullback.pullbackRingSectionsHom`
(`StacksFrontier/AlgebraicGeometry/Spaces/DirectImageChartProjectionRing.lean`) at the sheaf of
rings `i_*i^{-1}𝒪_X` on the small étale site of `X`, rather than at the structure sheaf: the
direct image whose sections are being projected here is the direct image of `i_*i^{-1}𝒪_X`, so
the generality in the sheaf of rings is used, not decoration.

The unit's inverse is taken on *sections over one chart*, as a `RingEquiv` built from
`AlgebraicGeometry.Space.bijective_thickeningRingUnit_app`, rather than as the inverse of
`AlgebraicGeometry.Space.thickeningRingUnitIso`.  Both are available; the sectionwise form is
the one whose round-trip equations are `RingEquiv.symm_apply_apply` and
`RingEquiv.apply_symm_apply`, which are the two facts the results below use, and it keeps the
`CategoryTheory.IsIso` instance — which does not resolve at a morphism of sheaves of rings on
the small étale site, and has to be passed positionally — out of the statements.

Both directions are stated at an arbitrary index `j` of the limit of chart sections rather than
at a `AlgebraicGeometry.Space.ChartDiagram`, since that is the form in which the joint
injectivity of the chart projections,
`AlgebraicGeometry.Space.eq_structureSharpThroughThickening_of_directImageChartProjection`,
consumes and produces them.

**No `@[stacks]` attribute is placed.**  As with the file this one extends, what is proved is a
comparison of two readings of [Stacks Project, Tag 03G8] internal to this development.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map.
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3), diagrams of charts.
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK), thickenings.
* [Stacks Project, Tag 0CKE](https://stacks.math.columbia.edu/tag/0CKE), the tag this reading is
  an input of.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X W : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)

/-! ### The chart reading as a ring homomorphism -/

/-- **The chart reading of the sections of `(i ≫ c)_*(i^{-1}𝒪_X)` as a homomorphism of
rings.**  Transport back across the comparison of iterated direct images, then project to the
étale scheme chart `j` of `X` above `X ×_W V`.  Both factors are ring homomorphisms: the first
is a morphism of sheaves of rings on sections, and the second is the chart projection recorded
as a ring homomorphism by `Stacks.Sheaves.ToposPullback.pullbackRingSectionsHom`. -/
noncomputable def thickeningLiftChartRingHom (c : X ⟶ W) (V : SmallEtale B S hS W.1)
    (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op) :
    (thickeningLiftRingSheaf B S hS Z c).obj.obj (op V) ⟶
      ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS
        (subspaceInclusion B S hS X Z))).obj
        (structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS X Z))).obj.obj j.right :=
  (pushforwardRingSheafCompInv B S hS (subspaceInclusion B S hS X Z) c
        (structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS X Z))).hom.app (op V) ≫
    pullbackRingSectionsHom (SmallEtale.topology B S hS W.1)
      (SmallEtale.topology B S hS X.1) (smallEtaleDirectImage B S hS c)
      ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS
        (subspaceInclusion B S hS X Z))).obj
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))
      (op V) j.right (directImageChartProjection B S hS c V j)

/-- On sections the ring homomorphism is the transport followed by the chart projection. -/
theorem thickeningLiftChartRingHom_apply (c : X ⟶ W) (V : SmallEtale B S hS W.1)
    (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op)
    (z : ToType ((thickeningLiftRingSheaf B S hS Z c).obj.obj (op V))) :
    (thickeningLiftChartRingHom B S hS Z c V j).hom z =
      (directImageChartProjection B S hS c V j).app
        ((sheafCompose (SmallEtale.topology B S hS X.1)
          (CategoryTheory.forget RingCat.{u})).obj
          ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS
            (subspaceInclusion B S hS X Z))).obj
            (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))))
        ((pushforwardRingSheafCompInv B S hS (subspaceInclusion B S hS X Z) c
            (structureRingSheafInverseImage B S hS
              (subspaceInclusion B S hS X Z))).hom.app (op V) z) := rfl

/-! ### The unit of a thickening as a ring isomorphism on chart sections -/

/-- **The unit `η : 𝒪_X ⟶ i_*i^{-1}𝒪_X` of a thickening on the sections over an étale chart, as
a ring isomorphism.**  It is a morphism of sheaves of rings, hence a ring homomorphism on
sections, and bijective by `AlgebraicGeometry.Space.bijective_thickeningRingUnit_app`: this is
the identification of the sections of `i^{-1}𝒪_X` over a chart with the regular functions on
that chart. -/
noncomputable def thickeningRingUnitChartRingEquiv (hZ : IsThickening B S hS X Z.1)
    (V : (SmallEtale B S hS X.1)ᵒᵖ) :
    ToType ((structureRingSheaf B S hS X).obj.obj V) ≃+*
      ToType (((pushforwardRingFunctor (smallToposMorphismTypeU B S hS
        (subspaceInclusion B S hS X Z))).obj
        (structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS X Z))).obj.obj V) :=
  RingEquiv.ofBijective ((thickeningRingUnit B S hS Z).hom.app V).hom
    (bijective_thickeningRingUnit_app B S hS Z hZ V)

/-- `AlgebraicGeometry.Space.thickeningRingUnitChartRingEquiv` is the unit. -/
theorem thickeningRingUnitChartRingEquiv_apply (hZ : IsThickening B S hS X Z.1)
    (V : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : ToType ((structureRingSheaf B S hS X).obj.obj V)) :
    thickeningRingUnitChartRingEquiv B S hS Z hZ V x =
      (thickeningRingUnit B S hS Z).hom.app V x := rfl

/-! ### The map of regular functions attached to a comorphism through a thickening -/

/-- **The homomorphism `Γ(V, ⊤) ⟶ Γ(V', ⊤)` of regular functions attached to a morphism
`a : 𝒪_W ⟶ (i ≫ c)_*(i^{-1}𝒪_X)` and an étale scheme chart `j` of `X` above `X ×_W V`:** the
value of `a` over `V`, read on the chart by
`AlgebraicGeometry.Space.thickeningLiftChartRingHom` and brought back to the regular functions
on the chart by the inverse of the unit of the thickening. -/
noncomputable def thickeningLiftChartAppTop (hZ : IsThickening B S hS X Z.1) (c : X ⟶ W)
    (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    (V : SmallEtale B S hS W.1)
    (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op) :
    ToType ((structureRingSheaf B S hS W).obj.obj (op V)) →+*
      ToType ((structureRingSheaf B S hS X).obj.obj j.right) :=
  ((thickeningRingUnitChartRingEquiv B S hS Z hZ j.right).symm : _ →+* _).comp
    (((thickeningLiftChartRingHom B S hS Z c V j).hom).comp (a.hom.app (op V)).hom)

/-- The value of `AlgebraicGeometry.Space.thickeningLiftChartAppTop`: the unit at it is the
chart reading. -/
theorem thickeningRingUnit_thickeningLiftChartAppTop (hZ : IsThickening B S hS X Z.1)
    (c : X ⟶ W) (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    (V : SmallEtale B S hS W.1)
    (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op)
    (b : ToType ((structureRingSheaf B S hS W).obj.obj (op V))) :
    (thickeningRingUnit B S hS Z).hom.app j.right
        (thickeningLiftChartAppTop B S hS Z hZ c a V j b) =
      (directImageChartProjection B S hS c V j).app
        ((sheafCompose (SmallEtale.topology B S hS X.1)
          (CategoryTheory.forget RingCat.{u})).obj
          ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS
            (subspaceInclusion B S hS X Z))).obj
            (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))))
        ((pushforwardRingSheafCompInv B S hS (subspaceInclusion B S hS X Z) c
            (structureRingSheafInverseImage B S hS
              (subspaceInclusion B S hS X Z))).hom.app (op V) (a.hom.app (op V) b)) :=
  (thickeningRingUnitChartRingEquiv B S hS Z hZ j.right).apply_symm_apply _

/-- **For the comorphism read through the thickening the map of regular functions is pullback of
regular functions** along the morphism of étale scheme charts induced by `j`.

This is
`AlgebraicGeometry.Space.directImageChartProjection_structureSharpThroughThickening_chartPullback`
with the unit cancelled, and it is the form a deformation-theoretic statement about morphisms of
affine schemes consumes: `Stacks.Thickenings.homOfAppTop` builds a morphism of schemes from a map
of global sections. -/
theorem thickeningLiftChartAppTop_structureSharpThroughThickening
    (hZ : IsThickening B S hS X Z.1) (c : X ⟶ W) (V : SmallEtale B S hS W.1)
    (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op) :
    thickeningLiftChartAppTop B S hS Z hZ c
        (structureSharpThroughThickening B S hS Z c) V j =
      chartPullbackRingHom B S hS c V j :=
  RingHom.ext fun b ↦
    (thickeningRingUnitChartRingEquiv B S hS Z hZ j.right).injective
      ((thickeningRingUnit_thickeningLiftChartAppTop B S hS Z hZ c
          (structureSharpThroughThickening B S hS Z c) V j b).trans
        (directImageChartProjection_structureSharpThroughThickening_chartPullback
          B S hS Z c V j b))

/-- **A morphism whose maps of regular functions are the chartwise pullbacks is the comorphism
read through the thickening.**  The chart projections determine a morphism into a direct image,
by
`AlgebraicGeometry.Space.eq_structureSharpThroughThickening_of_directImageChartProjection`, and
the map of regular functions determines the chart projection, the unit being injective on the
sections over an étale chart of a thickening.

With `AlgebraicGeometry.Space.thickeningLiftChartAppTop_structureSharpThroughThickening` this is
a complete description of the comorphism read through the thickening by maps of regular
functions of étale scheme charts, in both directions. -/
theorem eq_structureSharpThroughThickening_of_thickeningLiftChartAppTop
    (hZ : IsThickening B S hS X Z.1) (c : X ⟶ W)
    (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    (h : ∀ (V : SmallEtale B S hS W.1)
        (j : StructuredArrow (op (chartBaseChange B S hS c V))
          (comparisonFunctor B S hS X).op),
      thickeningLiftChartAppTop B S hS Z hZ c a V j = chartPullbackRingHom B S hS c V j) :
    a = structureSharpThroughThickening B S hS Z c :=
  eq_structureSharpThroughThickening_of_directImageChartProjection B S hS Z c a
    fun V j b ↦
      (thickeningRingUnit_thickeningLiftChartAppTop B S hS Z hZ c a V j b).symm.trans
        (congrArg ((thickeningRingUnit B S hS Z).hom.app j.right)
          (congrArg (fun φ : ToType ((structureRingSheaf B S hS W).obj.obj (op V)) →+*
              ToType ((structureRingSheaf B S hS X).obj.obj j.right) ↦ φ b) (h V j)))

end AlgebraicGeometry.Space

end
