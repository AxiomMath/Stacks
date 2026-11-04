module

public import StacksFrontier.AlgebraicGeometry.RelativeProjTwistChartBridge.ThetaTagShape

/-!
# The representation of the functor of quadruples is a representation over the base

In Situation 01NN — a scheme `S` and a quasi-coherent graded `𝒪_S`-algebra `𝒜` — the relative
homogeneous spectrum `Proj_S(𝒜)` of [Stacks, Tag 01NQ] represents the functor `F` of the display
01NX, by `...RelativeProjQcohSheaf.relativeProjRepresentableByFunctorUnconditional`
([Stacks, Tag 01NY] and [Stacks, Tag 01NZ]).  That representation sends a point `ξ` of `F(W)` to
a morphism `W ⟶ Proj_S(𝒜)`, which is
`...RelativeProjInvertibleMorphism.F.classifyingMorphism`.

A point of `F(W)` records a morphism `ξ.1 : W ⟶ S` — the `f` of the quadruples it is a class of —
so the representation ought to be a representation *over* `S`: the attached morphism, followed by
the structure morphism of `Proj_S(𝒜)`, ought to be `ξ.1`.  This file proves that, for an
arbitrary point of `F(W)` and over an arbitrary base.

Before this file the repository had the identity only in three weaker forms: for a *carried*
representation, as the hypothesis field
`...RelativeProjQcohSheaf.RepresentingProjData.homEquiv_symm_incl_comp_toBase`; for a point of
*one degree*, as `...RelativeProjQcohSheaf.Fd.homDegreeOpen_comp_toBase`; and for the morphism
`...RelativeProjTwistChartBridge.thetaMorphism` attached to a *single quadruple*, as
`...RelativeProjTwistChartBridge.thetaMorphism_comp_toBase`.  The content added here is the
passage from the last of those to an arbitrary point of the union `F(W)`.

## Main results

* `...RelativeProjInvertibleMorphism.F.classifyingMorphism_comp_toBase`: the morphism the
  representation attaches to a point of `F(W)`, followed by the structure morphism of
  `Proj_S(𝒜)`, is the morphism to `S` the point records.
* `...RelativeProjInvertibleMorphism.homEquiv_symm_toLim_comp_toBase`: the same identity written
  with the representing bijection itself, which is the shape of the hypothesis field
  `...RelativeProjQcohSheaf.RepresentingProjData.homEquiv_symm_incl_comp_toBase`.  So that field
  is no longer owed for the representation the repository proves.

## Implementation notes

The passage from one quadruple to an arbitrary point of `F(W)` costs nothing beyond bookkeeping,
and that is the whole observation: a point of `F(W)` is a pair of a morphism `f : W ⟶ S` and a
*class* of quadruples of positive degree over `f`, so `Quot.ind` produces a quadruple
representing it, and both sides of the identity are already known for a point of the form
`...RelativeProjQcohSheaf.F.mk`.  No gluing over the quasi-compact opens of `W` is involved: the
point lies in the union `F(W)` and not in its extension
`...RelativeProjQcohSheaf.F.limFunctor`, and the representation is applied to its image under
`...RelativeProjInvertibleMorphism.F.toLim`.

The degree of a quadruple is an integer, while
`...RelativeProjTwistChartBridge.thetaMorphism` is indexed by a natural number; the two are
reconciled by replacing the integer degree with the cast of its `Int.toNat`, which is legitimate
because it is positive.  The positivity proof carried by the subtype
`{d : ℤ // 0 < d}` plays no part, Lean's proof irrelevance identifying the two spellings of the
point.

## References

* [Stacks Project, Tag 01NX](https://stacks.math.columbia.edu/tag/01NX)
* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
* [Stacks Project, Tag 01NZ](https://stacks.math.columbia.edu/tag/01NZ)
* [Stacks Project, Tag 01O1](https://stacks.math.columbia.edu/tag/01O1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

variable {S W : Scheme.{u}} (A : SheafGradedAlgebra.{u} S)

/-- **The representation of `F` by `Proj_S(𝒜)` is a representation over `S`.**

The morphism `W ⟶ Proj_S(𝒜)` that the representation of [Stacks, Tag 01NZ] attaches to a point
`ξ` of `F(W)`, followed by the structure morphism `Proj_S(𝒜) ⟶ S`, is the morphism `W ⟶ S` that
`ξ` records.

Nothing is assumed beyond Situation 01NN: the base is arbitrary, the test scheme `W` is
arbitrary, and no representation is carried as a hypothesis. -/
theorem F.classifyingMorphism_comp_toBase (ξ : F (situationAlgebra A) W) :
    F.classifyingMorphism A ξ ≫ (relativeProj A).toBase = ξ.1 := by
  obtain ⟨f, q⟩ := ξ
  induction q using Quot.ind with
  | _ x =>
    obtain ⟨⟨d, hd⟩, P⟩ := x
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, d = (k : ℤ) := ⟨d.toNat, (Int.toNat_of_nonneg hd.le).symm⟩
    have hk : 0 < k := by exact_mod_cast hd
    show F.classifyingMorphism A (F.mk f hd P) ≫ _ = _
    rw [F.classifyingMorphism,
      ← RelativeProjTwistChartBridge.thetaMorphism_eq_homEquiv_symm hk P]
    exact RelativeProjTwistChartBridge.thetaMorphism_comp_toBase hk P

/-- **The over-`S` identity written with the representing bijection.**

This is `...RelativeProjInvertibleMorphism.F.classifyingMorphism_comp_toBase` with
`...RelativeProjInvertibleMorphism.F.classifyingMorphism` unfolded, which is the shape of the
field `...RelativeProjQcohSheaf.RepresentingProjData.homEquiv_symm_incl_comp_toBase`: that field
is therefore discharged, for the inclusion
`...RelativeProjInvertibleMorphism.F.toLim` of the union into its extension and for the
representation `...RelativeProjQcohSheaf.relativeProjRepresentableByFunctorUnconditional` the
repository proves. -/
theorem homEquiv_symm_toLim_comp_toBase (ξ : F (situationAlgebra A) W) :
    (relativeProjRepresentableByFunctorUnconditional A).homEquiv.symm (F.toLim A ξ) ≫
        (relativeProj A).toBase =
      ξ.1 :=
  F.classifyingMorphism_comp_toBase A ξ

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end
