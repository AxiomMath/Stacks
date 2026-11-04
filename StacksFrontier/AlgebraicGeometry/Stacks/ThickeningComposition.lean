module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionFppfLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective
public import StacksFrontier.AlgebraicGeometry.Stacks.Thickening

/-!
# Composing thickenings of algebraic stacks (Stacks 0BPS)

A thickening of algebraic stacks is a closed immersion which is surjective on points, so a
composite of two thickenings is again one: closed immersions compose (Stacks 0502) and a
composite of surjections is surjective.

The same bookkeeping on points gives the square attached to a morphism of thickenings, and with
it one of the two implications of Stacks 0CJ9 part (2).

## Main results

* `AlgebraicGeometry.Stack.isThickening_comp`: **Stacks 0BPS**.
* `AlgebraicGeometry.Stack.pointsMap_thickeningMorphism_comm`: a morphism of thickenings induces
  a commutative square of maps on points.
* `AlgebraicGeometry.Stack.isSurjective_outer_of_inner`: in a morphism of thickenings, if the
  restricted 1-morphism is surjective then so is the ambient one.

## Implementation notes

Everything here is phrased through `AlgebraicGeometry.Stack.AlgebraicStacks.pointsMap`, the map
on points of a 1-morphism of algebraic stacks, and uses its two functoriality facts from
`StacksFrontier.AlgebraicGeometry.Stacks.Surjective`:
`AlgebraicGeometry.Stack.AlgebraicStacks.pointsMap_comp` for a composite and
`AlgebraicGeometry.Stack.AlgebraicStacks.pointsMap_eq_of_hom₂` for invariance under a
2-morphism, the latter being what turns the 2-commutativity of a restriction square into a
genuine commutative square of maps of sets.

`AlgebraicGeometry.Stack.isThickening_comp` assumes nothing beyond the two thickenings. The
target-locality of `AlgebraicGeometry.Space.closedImmersionProperty` that the closed-immersion
half rests on is Stacks 0420, and it is now available at the fppf precoverage the relative
properties of Stacks 03YK are introduced at, as the instance
`AlgebraicGeometry.Space.isClosedImmersion_isLocalAtTarget_fppf`; it used to be a hypothesis of
this theorem.

Only one implication of Stacks 0CJ9 part (2) is here. The converse needs the map on points of a
thickening to be *injective*, which is the part of Stacks 0BPP part (1) asserting that a
thickening induces a homeomorphism of underlying topological spaces. That clause is not
available: it has to be phrased through the point topology of Stacks 04XL, which has no library
site, and `StacksFrontier.AlgebraicGeometry.Stacks.Thickening` records that
`AlgebraicGeometry.Stack.IsThickening` therefore omits it. So Stacks 0CJ9 part (2) is *not*
tagged here — its covering set is incomplete until that clause exists — and only the
unconditional direction is stated.

## References

* [Stacks Project, Tag 0420](https://stacks.math.columbia.edu/tag/0420)
* [Stacks Project, Tag 0BPP](https://stacks.math.columbia.edu/tag/0BPP)
* [Stacks Project, Tag 0BPS](https://stacks.math.columbia.edu/tag/0BPS)
* [Stacks Project, Tag 0502](https://stacks.math.columbia.edu/tag/0502)
* [Stacks Project, Tag 04ZS](https://stacks.math.columbia.edu/tag/04ZS)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0BPS.** A composite of thickenings of algebraic stacks over `S` is a thickening:
the composite is a closed immersion by Stacks 0502, and it is surjective on points because each
factor is. -/
@[stacks 0BPS "the composite of two thickenings is a thickening"]
theorem isThickening_comp
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : IsThickening f) (hg : IsThickening g) :
    IsThickening (f ≫ g) := by
  refine ⟨AlgebraicStacks.isClosedImmersion_comp B S hS f g hf.1 hg.1, ?_⟩
  change Function.Surjective (AlgebraicStacks.pointsMap B S hS (f ≫ g))
  rw [AlgebraicStacks.pointsMap_comp]
  exact hg.2.comp hf.2

/-- A morphism of thickenings of algebraic stacks induces a commutative square of maps on
points: following the ambient 1-morphism after the source thickening is the same as following
the target thickening after the restricted 1-morphism. This is the point-level content of the
2-commutativity of the restriction square. -/
theorem pointsMap_thickeningMorphism_comm {𝒳 𝒳' 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}
    {i : 𝒳 ⟶ 𝒳'} {j : 𝒴 ⟶ 𝒴'} {hi : IsThickening i} {hj : IsThickening j}
    (m : ThickeningMorphism i j hi hj) :
    AlgebraicStacks.pointsMap B S hS m.outer ∘ AlgebraicStacks.pointsMap B S hS i =
      AlgebraicStacks.pointsMap B S hS j ∘ AlgebraicStacks.pointsMap B S hS m.inner := by
  rw [← AlgebraicStacks.pointsMap_comp, ← AlgebraicStacks.pointsMap_comp]
  exact AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS m.comm.symm.hom

/-- In a morphism of thickenings of algebraic stacks, if the restricted 1-morphism is surjective
then so is the ambient 1-morphism.

This is one implication of Stacks 0CJ9 part (2); see the implementation notes of this file for
why the converse is not available. -/
theorem isSurjective_outer_of_inner {𝒳 𝒳' 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}
    {i : 𝒳 ⟶ 𝒳'} {j : 𝒴 ⟶ 𝒴'} {hi : IsThickening i} {hj : IsThickening j}
    (m : ThickeningMorphism i j hi hj) (hm : IsSurjective B S hS m.inner) :
    IsSurjective B S hS m.outer := by
  intro y'
  obtain ⟨y, hy⟩ := hj.2 y'
  obtain ⟨x, hx⟩ := hm y
  refine ⟨AlgebraicStacks.pointsMap B S hS i x, ?_⟩
  have h := congrFun (pointsMap_thickeningMorphism_comm m) x
  simp only [Function.comp_apply] at h
  rw [h, hx]
  exact hy

end AlgebraicGeometry.Stack

end
