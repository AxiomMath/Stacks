module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionRing
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.StructureSheafRingUnit

/-!
# A regular function read from a chart of the target is a value of the inverse-image sharp

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, let `V` be an étale scheme
chart of `Y` and let `j` be an étale scheme chart of `X` above `X ×_Y V`.  Pullback along the
induced morphism of charts carries a regular function on `V` to one on the chart of `X`,
`AlgebraicGeometry.Space.chartPullbackRingHom`.

This file shows that **every such function is a value of the inverse-image sharp**
`f^♯ : f^{-1}𝒪_Y ⟶ 𝒪_X` over that chart, by exhibiting the section of `f^{-1}𝒪_Y` it comes
from: the unit of `f^{-1} ⊣ f_*` applied to the function, projected to the chart.

The sections of an inverse image are a sheafified colimit and are not global sections of
anything — the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsRepresented.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/InverseImageChartSections.lean` both record
that — so there is no chart-level *description* of those sections.  What is given here is one
distinguished family of them, which is what a statement about the functions read from the base
needs: a derivation annihilating the image of `f^♯`, such as the one attached to a linear map by
Equation [Stacks Project, Tag 0619], annihilates every chartwise pullback of a function from
`Y`.

## Main definitions

* `AlgebraicGeometry.Space.chartPullbackInverseImageSection`: the section of `f^{-1}𝒪_Y` over a
  chart of `X` attached to a regular function on a chart of `Y`.

## Main results

* `AlgebraicGeometry.Space.structureSharpRingInverseImage_chartPullbackInverseImageSection`:
  **the inverse-image sharp carries it to the chartwise pullback of the function.**
* `AlgebraicGeometry.Space.exists_app_structureSharpRingInverseImage_eq_chartPullbackRingHom`:
  the same as an existence statement, with no reference to the chosen section.

## Implementation notes

The three ingredients are the adjunction identity
`AlgebraicGeometry.Space.ringUnit_comp_map_structureSharpRingInverseImage`, which is the
inverse-image form of [Stacks Project, Tag 03G8]; the naturality of the chart projection in the
sheaf of rings, `AlgebraicGeometry.Space.directImageChartProjection_ringSheafMap`; and the
chart-level computation of the ordinary comorphism,
`AlgebraicGeometry.Space.directImageChartProjection_structureSharpSet`.  The chart projection is
taken at the sheaf of rings `f^{-1}𝒪_Y`, which is why it is
`Stacks.Sheaves.ToposPullback.pullbackRingSectionsHom` rather than
`AlgebraicGeometry.Space.directImageChartProjectionRingHom`: the latter is the same construction
fixed at the structure sheaf of `X`.

**No `@[stacks]` attribute is placed.**  This is a chart-level reading of
[Stacks Project, Tag 03G8] internal to this development.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map.
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3), diagrams of charts.
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619), the derivation attached
  to a linear map, whose defining property is that it annihilates the functions read from the
  base.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- **The section of `f^{-1}𝒪_Y` over an étale scheme chart of `X` attached to a regular
function on an étale scheme chart of `Y`:** the unit of `f^{-1} ⊣ f_*` at the function,
projected to the chart. -/
noncomputable def chartPullbackInverseImageSection (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op) :
    (structureRingSheaf B S hS Y).obj.obj (op V) ⟶
      (structureRingSheafInverseImage B S hS f).obj.obj j.right :=
  (ringUnit (smallToposMorphismTypeU B S hS f) (structureRingSheaf B S hS Y)).hom.app (op V) ≫
    pullbackRingSectionsHom (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)
      (smallEtaleDirectImage B S hS f) (structureRingSheafInverseImage B S hS f) (op V) j.right
      (directImageChartProjection B S hS f V j)

/-- **The inverse-image sharp carries the attached section to the chartwise pullback of the
function.**  So a regular function read from a chart of `Y` is, over the chart of `X`, a value
of `f^♯ : f^{-1}𝒪_Y ⟶ 𝒪_X` — on the nose, with no passage to a covering sieve. -/
theorem structureSharpRingInverseImage_chartPullbackInverseImageSection (f : X ⟶ Y)
    (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (b : ToType ((structureRingSheaf B S hS Y).obj.obj (op V))) :
    (structureSharpRingInverseImage B S hS f).hom.app j.right
        ((chartPullbackInverseImageSection B S hS f V j).hom b) =
      chartPullbackRingHom B S hS f V j b := by
  refine Eq.trans ?_ (directImageChartProjection_structureSharpSet B S hS f V j b)
  refine Eq.trans
    (directImageChartProjection_ringSheafMap B S hS f V j
      (structureSharpRingInverseImage B S hS f)
      ((ringUnit (smallToposMorphismTypeU B S hS f)
        (structureRingSheaf B S hS Y)).hom.app (op V) b)).symm ?_
  exact congrArg ((directImageChartProjection B S hS f V j).app (structureSetSheaf B S hS X))
    (congrArg (fun m : structureRingSheaf B S hS Y ⟶ structureRingSheafDirectImage B S hS f ↦
      m.hom.app (op V) b)
      (ringUnit_comp_map_structureSharpRingInverseImage B S hS f))

/-- **Every chartwise pullback of a regular function from `Y` is a value of the inverse-image
sharp over the chart of `X`.**  This is the form a statement about a derivation annihilating the
functions read from the base consumes. -/
theorem exists_app_structureSharpRingInverseImage_eq_chartPullbackRingHom (f : X ⟶ Y)
    (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (b : ToType ((structureRingSheaf B S hS Y).obj.obj (op V))) :
    ∃ s : ToType ((structureRingSheafInverseImage B S hS f).obj.obj j.right),
      (structureSharpRingInverseImage B S hS f).hom.app j.right s =
        chartPullbackRingHom B S hS f V j b :=
  ⟨_, structureSharpRingInverseImage_chartPullbackInverseImageSection B S hS f V j b⟩

end AlgebraicGeometry.Space

end
