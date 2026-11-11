module

public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointsLocallyClosed
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbe

/-!
# Finite type points and residual gerbes (Stacks 06G3)

**Stacks 06G3** says that for an algebraic stack `𝒳` over `S` and a point `x ∈ |𝒳|` the
following are equivalent:

1. `x` is a finite type point (**Stacks 06FY**);
2. there is an algebraic stack `𝒵` whose point space `|𝒵|` is a singleton and a 1-morphism
   `f : 𝒵 ⟶ 𝒳` which is locally of finite type with `{x} = |f|(|𝒵|)`;
3. the residual gerbe `𝒵_x` of `𝒳` at `x` exists and the inclusion `𝒵_x ⟶ 𝒳` is locally of
   finite type.

## The three implications

* **(3) ⟹ (2)** is proved. The source calls it clear, and it is: the residual gerbe is by
  definition (`AlgebraicGeometry.Stack.IsResidualGerbeAt`, the specification of **Stacks 06MT**)
  an algebraic full subcategory with exactly one point lying over `x`, so its inclusion is a
  1-morphism of the kind (2) asks for.

* **(2) ⟹ (1)** is proved. The source argues it through **Stacks 06G0** and **Stacks 06G2**; here
  it is **Stacks 06G0** (`AlgebraicGeometry.Stack.mapsTo_finiteTypePoints`) together with
  `AlgebraicGeometry.Stack.exists_isFiniteTypePoint_of_nonempty`, which is the part of
  Stacks 06G2 the argument actually uses — that the unique point of a nonempty algebraic stack
  is a finite type point of it. No hypothesis is carried for this direction.

* **(1) ⟹ (3)** is stated here as the proposition
  `AlgebraicGeometry.Stack.ExistsLocallyOfFiniteTypeResidualGerbeOfIsFiniteTypePoint` and proved
  in `StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointResidualGerbeExistence`, as
  `AlgebraicGeometry.Stack.existsLocallyOfFiniteTypeResidualGerbe`. This is the substantial
  direction. The source builds the groupoid in algebraic spaces `R = u ×_𝒳 u` on the residue
  field `u` of a closed point of a smooth affine chart and forms `𝒵 = [u/R]`, an algebraic stack
  by **Stacks 06FI**; that file instead cuts the one-point algebraic stack out of `𝒳` as the
  strictly full subcategory of the objects fppf-locally in the image of the field-valued point.
  That proof imports this file, so here the implication is the hypothesis of
  `AlgebraicGeometry.Stack.isFiniteTypePoint_tfae`; the tag itself, with nothing assumed, is
  `AlgebraicGeometry.Stack.isFiniteTypePoint_tfae_unconditional` there.

## Main definitions

* `AlgebraicGeometry.Stack.HasSingletonLocallyOfFiniteTypeCoverAt`: condition (2).
* `AlgebraicGeometry.Stack.HasLocallyOfFiniteTypeResidualGerbeAt`: condition (3).
* `AlgebraicGeometry.Stack.ExistsLocallyOfFiniteTypeResidualGerbeOfIsFiniteTypePoint`: the
  implication (1) ⟹ (3), as a proposition.

## Main results

* `AlgebraicGeometry.Stack.hasSingletonLocallyOfFiniteTypeCoverAt_of_residualGerbe`: (3) ⟹ (2).
* `AlgebraicGeometry.Stack.isFiniteTypePoint_of_hasSingletonLocallyOfFiniteTypeCoverAt`:
  (2) ⟹ (1).
* `AlgebraicGeometry.Stack.isFiniteTypePoint_tfae`: the equivalence of the three conditions of
  **Stacks 06G3**, given the implication (1) ⟹ (3).

## Implementation notes

That `|𝒵|` is a singleton is spelled as `Nonempty` together with `Subsingleton` of the point
space of **Stacks 04XG**, the same way
`StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointStack` spells it; and `{x} = |f|(|𝒵|)` is
spelled as `Set.range _ = {x}`.

`AlgebraicGeometry.Stack.IsResidualGerbeAt` takes its point in
`AlgebraicGeometry.Stack.points` formed with `Classical.choose 𝒳.property`, while
`AlgebraicGeometry.Stack.IsFiniteTypePoint` takes its point formed with `𝒳.val.property`. These
two witnesses are proofs of the same proposition, so the two point types are definitionally
equal by proof irrelevance and a single `x` serves in both; no transport is needed.

Condition (3) existentially quantifies the algebraicity witness `hP` of the full subcategory
alongside the object property `P`, rather than extracting it from `IsResidualGerbeAt` with
`Exists.choose`, so that the inclusion whose local finite type is asserted is syntactically the
same 1-morphism in both conjuncts.

## References

* [Stacks Project, Tag 04ZZ](https://stacks.math.columbia.edu/tag/04ZZ)
* [Stacks Project, Tag 06EV](https://stacks.math.columbia.edu/tag/06EV)
* [Stacks Project, Tag 06FI](https://stacks.math.columbia.edu/tag/06FI)
* [Stacks Project, Tag 06FY](https://stacks.math.columbia.edu/tag/06FY)
* [Stacks Project, Tag 06G0](https://stacks.math.columbia.edu/tag/06G0)
* [Stacks Project, Tag 06G2](https://stacks.math.columbia.edu/tag/06G2)
* [Stacks Project, Tag 06G3](https://stacks.math.columbia.edu/tag/06G3)
* [Stacks Project, Tag 06MT](https://stacks.math.columbia.edu/tag/06MT)
* [Stacks Project, Tag 06MX](https://stacks.math.columbia.edu/tag/06MX)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Condition (2) of Stacks 06G3.** There is an algebraic stack `𝒵` over `S` whose point space
is a singleton, together with a 1-morphism `f : 𝒵 ⟶ 𝒳` which is locally of finite type and whose
image on points is exactly `{x}`. -/
abbrev HasSingletonLocallyOfFiniteTypeCoverAt (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (x : points B S hS 𝒳.val.val 𝒳.val.property) : Prop :=
  ∃ (𝒵 : AlgebraicStacks.{u, w} B S hS) (f : 𝒵 ⟶ 𝒳),
    Nonempty (points B S hS 𝒵.val.val 𝒵.val.property) ∧
      Subsingleton (points B S hS 𝒵.val.val 𝒵.val.property) ∧
        AlgebraicStacks.IsLocallyOfFiniteType B S hS f ∧
          Set.range
            (pointsMap B S hS 𝒵.val.val 𝒵.val.property 𝒳.val.property f.hom.hom) = {x}

/-- **Condition (3) of Stacks 06G3.** The residual gerbe of `𝒳` at `x` exists — some object
property of `𝒳` satisfies the specification `AlgebraicGeometry.Stack.IsResidualGerbeAt` of
**Stacks 06MT** — and the inclusion of the full subcategory it selects is locally of finite
type. -/
abbrev HasLocallyOfFiniteTypeResidualGerbeAt (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (x : points B S hS 𝒳.val.val 𝒳.val.property) : Prop :=
  ∃ (P : ObjectProperty 𝒳.val.val.obj)
    (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P)),
    IsResidualGerbeAt B S hS 𝒳 x P ∧
      AlgebraicStacks.IsLocallyOfFiniteType B S hS (fullSubcategoryInclusion 𝒳 P hP)

/-- **The implication (1) ⟹ (3) of Stacks 06G3, as a proposition.** That every finite type point
of an algebraic stack has a residual gerbe whose inclusion is locally of finite type.

It is proved as `AlgebraicGeometry.Stack.existsLocallyOfFiniteTypeResidualGerbe` in
`StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointResidualGerbeExistence`, which cuts the
one-point algebraic stack out of `𝒳` as a strictly full subcategory rather than forming the
quotient `[u/R]` of the source's proof. -/
abbrev ExistsLocallyOfFiniteTypeResidualGerbeOfIsFiniteTypePoint
    (𝒳 : AlgebraicStacks.{u, w} B S hS) : Prop :=
  ∀ x : points B S hS 𝒳.val.val 𝒳.val.property, IsFiniteTypePoint.{u, w} B S hS 𝒳 x →
    HasLocallyOfFiniteTypeResidualGerbeAt.{u, w} B S hS 𝒳 x

/-- **Condition (3) of Stacks 06G3 implies its condition (2).** The residual gerbe is an
algebraic full subcategory of `𝒳` with exactly one point, lying over `x`, so its inclusion is a
1-morphism from a one-point algebraic stack whose image on points is `{x}`; local finite type of
that inclusion is part of condition (3). -/
theorem hasSingletonLocallyOfFiniteTypeCoverAt_of_residualGerbe
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (x : points B S hS 𝒳.val.val 𝒳.val.property)
    (h : HasLocallyOfFiniteTypeResidualGerbeAt.{u, w} B S hS 𝒳 x) :
    HasSingletonLocallyOfFiniteTypeCoverAt.{u, w} B S hS 𝒳 x := by
  obtain ⟨P, hP, ⟨-, hP', -, -, z, huniq, hzx⟩, hlft⟩ := h
  refine ⟨fullSubcategoryAlgebraicStack 𝒳 P hP, fullSubcategoryInclusion 𝒳 P hP, ⟨z⟩,
    ⟨fun a b => (huniq a).trans (huniq b).symm⟩, hlft, ?_⟩
  refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨z, hzx⟩, ?_⟩
  rintro - ⟨a, rfl⟩
  rw [huniq a]
  exact hzx

/-- **Condition (2) of Stacks 06G3 implies its condition (1).** The one-point algebraic stack `𝒵`
is nonempty, so it has a finite type point by
`AlgebraicGeometry.Stack.exists_isFiniteTypePoint_of_nonempty`; its image under `f` is a finite
type point of `𝒳` by **Stacks 06G0**, and that image is `x` because the image of `|f|` is
`{x}`. -/
theorem isFiniteTypePoint_of_hasSingletonLocallyOfFiniteTypeCoverAt
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (x : points B S hS 𝒳.val.val 𝒳.val.property)
    (h : HasSingletonLocallyOfFiniteTypeCoverAt.{u, w} B S hS 𝒳 x) :
    IsFiniteTypePoint.{u, w} B S hS 𝒳 x := by
  obtain ⟨𝒵, f, hne, -, hlft, hrange⟩ := h
  obtain ⟨z, hz⟩ := exists_isFiniteTypePoint_of_nonempty.{u, w} B S hS 𝒵 hne
  have hmem : pointsMap B S hS 𝒵.val.val 𝒵.val.property 𝒳.val.property f.hom.hom z = x := by
    rw [← Set.mem_singleton_iff, ← hrange]
    exact Set.mem_range_self z
  exact hmem ▸ mapsTo_finiteTypePoints.{u, w} B S hS f hlft hz

/-- **Stacks 06G3, relative to the implication (1) ⟹ (3).** For a point `x` of the point space of
an algebraic stack `𝒳` over `S`, the three conditions of Stacks 06G3 are equivalent once the
implication (1) ⟹ (3) is supplied as `hForward`; the other two implications are proved here.

The library proves `hForward` as
`AlgebraicGeometry.Stack.existsLocallyOfFiniteTypeResidualGerbe`, and **Stacks 06G3** itself,
with nothing assumed, is `AlgebraicGeometry.Stack.isFiniteTypePoint_tfae_unconditional`, both in
`StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointResidualGerbeExistence`. -/
theorem isFiniteTypePoint_tfae (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hForward : ExistsLocallyOfFiniteTypeResidualGerbeOfIsFiniteTypePoint.{u, w} B S hS 𝒳)
    (x : points B S hS 𝒳.val.val 𝒳.val.property) :
    [IsFiniteTypePoint.{u, w} B S hS 𝒳 x,
      HasSingletonLocallyOfFiniteTypeCoverAt.{u, w} B S hS 𝒳 x,
      HasLocallyOfFiniteTypeResidualGerbeAt.{u, w} B S hS 𝒳 x].TFAE := by
  tfae_have 1 → 3 := hForward x
  tfae_have 3 → 2 := hasSingletonLocallyOfFiniteTypeCoverAt_of_residualGerbe.{u, w} B S hS 𝒳 x
  tfae_have 2 → 1 := isFiniteTypePoint_of_hasSingletonLocallyOfFiniteTypeCoverAt.{u, w} B S hS 𝒳 x
  tfae_finish

end AlgebraicGeometry.Stack

end
