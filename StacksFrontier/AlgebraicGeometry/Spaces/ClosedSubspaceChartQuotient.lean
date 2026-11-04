module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdeals
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingIdealPullback

/-!
# Affine étale charts of a closed subspace, and the quotient presentation of their rings

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let
`Z ⊆ X` be a closed subspace and write `Zs` for `Z` read as an algebraic space in its own
right, with `i : Zs ⟶ X` its inclusion.  An étale scheme chart `W` of `X` whose underlying
scheme is affine produces an étale scheme chart `Z ×_X W` of `Zs` lying over `W`, and that
chart is again affine because `Z ×_X W ⟶ W` is a closed immersion of schemes.  The resulting
diagram of charts presents the chart ring of `Zs` as a quotient of the chart ring of `X`: the
map `𝒪_X(W) ⟶ 𝒪_{Zs}(Z ×_X W)` is surjective, and its kernel is the defining ideal of `Z`
at `W` in the sense of `AlgebraicGeometry.Space.definingIdealAt`.

## Main results

* `AlgebraicGeometry.Space.exists_affine_chartDiagram_of_closedSubspace`: over an affine étale
  scheme chart `W` of `X` there is an affine étale scheme chart `U` of the closed subspace,
  together with a chart diagram over the inclusion, whose map of chart rings is surjective with
  kernel the defining ideal of the closed subspace at `W`.

## The argument

The chart is the canonical base change: the inclusion of a closed subspace is representable,
so the fibre product `Z ×_X W` is represented by an object of the big fppf site, and
`AlgebraicGeometry.Space.isEtaleChart_representablePullback` says that the projection to `Zs`
is an étale chart because étaleness of charts is stable under base change.  The chart diagram
is completed by the cartesian projection to `W` and the cartesian square itself.

Representability also makes the projection `Z ×_X W ⟶ W` a closed immersion of schemes, which
is the only input to the two algebraic assertions: a scheme admitting a closed immersion into
an affine scheme is affine, and a closed immersion is surjective on sections over an affine
open, here the whole of `W`.  The identification of the kernel is
`AlgebraicGeometry.Space.definingIdealAt_eq_ker`, which computes the defining ideal of a closed
subspace on a chart as exactly the kernel of pullback of regular functions along this
projection; since `AlgebraicGeometry.Space.chartDiagramRestrict` is by construction that
pullback map, no comparison intervenes.

## Implementation notes

Affineness of the chart is not assumed of the fibre product but deduced, so the statement takes
only the affineness of `W` as a hypothesis.  Nothing here needs `W` to be surjective, and
nothing needs the closed subspace to be quasi-coherently presented: the content is the
representability of a closed immersion together with the affine-local description of closed
immersions of schemes.

**No `@[stacks]` attribute is carried, and none should be.**  The quotient presentation of the
ring of an affine étale chart of a closed subspace is not a numbered result of the Stacks
Project; it is the chartwise reading of Stacks 03M9 which the source performs inline wherever
a closed subspace is computed on an affine chart.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An affine étale chart of a closed subspace over an affine étale chart of the ambient
space, presenting its ring as a quotient.**  Let `Zc ⊆ X` be a closed subspace of an algebraic
space `X` over `S`, let `Zs` be `Zc` read as an algebraic space and `i : Zs ⟶ X` its inclusion,
and let `W` be an étale scheme chart of `X` whose underlying scheme is affine.  Then there is an
étale scheme chart `U` of `Zs`, a morphism `gm : U ⟶ W` of the big fppf site and a commuting
square making `(U, W, gm)` a diagram of étale charts over `i`, such that the scheme underlying
`U` is affine and the induced map of chart rings `𝒪_X(W) ⟶ 𝒪_{Zs}(U)` is surjective with kernel
the defining ideal of `Zc` at `W`. -/
theorem exists_affine_chartDiagram_of_closedSubspace
    (X : AlgebraicSpaces B S hS) (Zc : ClosedSubspaces B S hS X.1)
    (W : SmallEtale B S hS X.1)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W.1.left)) :
    ∃ (U : SmallEtale B S hS (⟨Zc.1.toFunctor, Zc.2.1⟩ : AlgebraicSpaces B S hS).1)
      (gm : (SmallEtale.toOver B S hS (⟨Zc.1.toFunctor, Zc.2.1⟩ :
            AlgebraicSpaces B S hS).1).obj U ⟶
          (SmallEtale.toOver B S hS X.1).obj W)
      (hcomm : U.1.hom ≫ (ObjectProperty.homMk Zc.1.ι :
            (⟨Zc.1.toFunctor, Zc.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X).hom =
          yoneda.map gm ≫ W.1.hom),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left) ∧
      Function.Surjective (chartDiagramRestrict B S hS
        (ObjectProperty.homMk Zc.1.ι :
          (⟨Zc.1.toFunctor, Zc.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X)
        { U := U, V := W, g := gm, comm := hcomm }) ∧
      RingHom.ker (chartDiagramRestrict B S hS
        (ObjectProperty.homMk Zc.1.ι :
          (⟨Zc.1.toFunctor, Zc.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X)
        { U := U, V := W, g := gm, comm := hcomm }) =
        definingIdealAt B S hS X Zc (op W) := by
  have hci : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (Zc.2.2.rep.snd W.1.hom)) :=
    Zc.2.2.property_snd W.1.hom
  refine ⟨⟨CostructuredArrow.mk (Zc.2.2.rep.fst W.1.hom),
      isEtaleChart_representablePullback B S hS
        (ObjectProperty.homMk Zc.1.ι :
          (⟨Zc.1.toFunctor, Zc.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X) Zc.2.2.rep W⟩,
    Zc.2.2.rep.snd W.1.hom, Zc.2.2.rep.w W.1.hom, ?_, ?_, ?_⟩
  · exact isAffine_of_isAffineHom
      ((BigFppfOver.toScheme B S hS).map (Zc.2.2.rep.snd W.1.hom))
  · exact Scheme.Hom.app_surjective
      ((BigFppfOver.toScheme B S hS).map (Zc.2.2.rep.snd W.1.hom)) ⊤ (isAffineOpen_top _)
  · rw [definingIdealAt_eq_ker]
    rfl

end AlgebraicGeometry.Space

end
