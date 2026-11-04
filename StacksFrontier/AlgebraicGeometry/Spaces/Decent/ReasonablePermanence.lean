module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReasonableEtaleCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.UniversallyBoundedFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.VeryReasonablePermanence

/-!
# Reasonableness passes to the source of a representable morphism

Stacks 03KF says that each of the properties `(β)`, `(γ)`, `(δ)`, `(ε)` and `(θ)` of
Stacks 03JX passes from the target of a representable morphism of algebraic spaces over a
scheme `S` to its source. This file proves the case `(δ)`, reasonableness.

Reasonableness is one of the two properties Stacks 0ABT names, so the case `(δ)` is at the
same time the reasonable half of that lemma; the decent half is
`AlgebraicGeometry.Space.isDecentSpace_of_relativelyRepresentable`.

The argument is the one Stacks gives. Reasonableness of the target is read through
condition (1) of Stacks 03JT as a jointly surjective family of étale charts by schemes with
universally bounded fibres. Representability of `f : X ⟶ Y` turns each such chart of `Y`
into a chart of `X` by base change, which is again étale and has universally bounded fibres
by Stacks 03JN; the base-changed family is again jointly surjective, so condition (1) of
Stacks 03JT holds for `X` and reasonableness follows.

## Main results

* `AlgebraicGeometry.Space.isReasonableSpace_of_relativelyRepresentable`: the case `(δ)` of
  Stacks 03KF, which is also the reasonable half of Stacks 0ABT.

## Implementation notes

Reasonableness is `AlgebraicGeometry.Space.IsReasonableSpace`, condition (2) of Stacks 03JT:
every étale chart by an affine scheme has universally bounded fibres. That condition cannot
be checked directly on `X`, because an étale chart of `X` need not compose with `f` to an
étale chart of `Y`; the passage through condition (1) of Stacks 03JT, which is
`AlgebraicGeometry.Space.isReasonableSpace_iff_exists_boundedEtaleCover`, is what the source
does as well, and it is why both presheaves are assumed to be algebraic spaces.

Stacks 03JN produces the base-changed chart as an unspecified object of the site rather than
as the chosen fibre product of the representability datum, which is all condition (1) of
Stacks 03JT asks for.

## References

* [Stacks Project, Tag 03JN](https://stacks.math.columbia.edu/tag/03JN)
* [Stacks Project, Tag 03JT](https://stacks.math.columbia.edu/tag/03JT)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 03KF](https://stacks.math.columbia.edu/tag/03KF)
* [Stacks Project, Tag 0ABT](https://stacks.math.columbia.edu/tag/0ABT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03KF, the case `(δ)`, and the reasonable half of Stacks 0ABT.** Property `(δ)`
of Stacks 03JX — reasonableness — passes from the target of a representable morphism of
algebraic spaces over `S` to its source.

A jointly surjective family of étale charts of `Y` with universally bounded fibres, which
reasonableness of `Y` provides through Stacks 03JT, base changes along `f` to a family of
étale charts of `X`; the bounds survive by Stacks 03JN and joint surjectivity survives
because the squares are cartesian, so Stacks 03JT applies to `X`. -/
@[stacks 03KF "property_delta"]
theorem isReasonableSpace_of_relativelyRepresentable
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f) (hYr : IsReasonableSpace B S hS Y) :
    IsReasonableSpace B S hS X := by
  classical
  obtain ⟨I, V, ψ, hcover, hψ⟩ :=
    (isReasonableSpace_iff_exists_boundedEtaleCover B S hS Y hY).1 hYr
  choose U inc p hpb hbnd using fun i =>
    hasUniversallyBoundedFibers_baseChange B S hS f hf (V i) (ψ i) (hψ i).2
  refine (isReasonableSpace_iff_exists_boundedEtaleCover B S hS X hX).2
    ⟨I, U, p, isLocallySurjective_sigmaDesc_of_isPullback B S hS hpb hcover, fun i => ⟨?_, hbnd i⟩⟩
  exact (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).of_isPullback (hpb i) (hψ i).1

end AlgebraicGeometry.Space

add_to_stacks 0ABT "reasonable"
  AlgebraicGeometry.Space.isReasonableSpace_of_relativelyRepresentable

end
