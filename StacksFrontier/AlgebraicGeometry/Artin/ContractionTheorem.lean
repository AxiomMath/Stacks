module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionExistence
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsBigFppfExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.LimitPreservingFunctorOfPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSmallValues
public import StacksFrontier.Deformation.Artin.LocallyNoetherianAlgebraicSpaceCriterionLarge

/-!
# Artin's theorem on contractions (Stacks 0GIB)

In the situation of Stacks 0GH8 (`AlgebraicGeometry.Artin.ContractionSituation`), Artin's
theorem on contractions says that, over a locally Noetherian base whose local rings at finite
type points are G-rings, a formal modification `g : X'_{/T'} ⟶ W` with `X'` and `W` separated
over `S` has a solution: a proper `f : X' ⟶ X`, a closed `T ⊆ |X|` and an isomorphism
`a : X_{/T} ≅ W` with `|f|⁻¹ T = T'`, `f` an isomorphism `X' ∖ T' ≅ X ∖ T`, and
`g = a ∘ f_{/T}`.

The source's proof: by Stacks 0GHC it suffices that Artin's functor `F` of Stacks 0GHA is (the
restriction to locally Noetherian schemes of) an algebraic space locally of finite type over `S`,
and that follows from Stacks 0GE7, whose hypotheses are Stacks 0GHF (the diagonal) and Stacks
0GHG, 0GI5, 0GI6, 0GI7, 0GI8, 0GIA (axioms `[0]`–`[5]`).

This file carries the last steps: from Artin's axioms for `F` to a limit preserving algebraic
space whose restriction to the locally Noetherian site is `F` (Stacks 0GE7, in the form
`AlgebraicGeometry.LocallyNoetherianOver.exists_isAlgebraicSpace_restriction_iso_of_small` for
the `u`-small values of `F`), and from that space to a solution.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.exists_solution_of_restriction_iso`: a limit
  preserving algebraic space `X` of `Type u` whose restriction to the locally Noetherian schemes
  over `S` is `F` is a solution, with `U = X ∖ T`.
* `AlgebraicGeometry.Artin.ContractionSituation.exists_solution_of_isAlgebraicSpaceULift`: the
  same for an algebraic space with values in `Type (u + 1)`, the value universe of `F`.
* `AlgebraicGeometry.Artin.ContractionSituation.exists_solution_of_satisfiesArtinAxioms`: the
  source's reduction of Stacks 0GIB to the diagonal of `F` and Artin's axioms for `F`, through
  Stacks 0GE7.

## References

* [Stacks Project, Tag 05N0](https://stacks.math.columbia.edu/tag/05N0)
* [Stacks Project, Tag 0GE7](https://stacks.math.columbia.edu/tag/0GE7)
* [Stacks Project, Tag 0GHC](https://stacks.math.columbia.edu/tag/0GHC)
* [Stacks Project, Tag 0GIB](https://stacks.math.columbia.edu/tag/0GIB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (c : ContractionSituation B S hS)

/-- **From a representing algebraic space to a solution.** Let `X` be an algebraic space over
`S` (values in `Type u`) whose functor of points is limit preserving, and whose restriction to the
locally Noetherian schemes over `S` is Artin's functor `F`. Then `X` is locally of finite type
over `S` (Stacks 05N0), and by Stacks 0GHC it is a solution, by a solution whose open subspace
`U` is the complement of `T`. -/
theorem exists_solution_of_restriction_iso {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hl : LimitPreserving.{u, u, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) X)
    (e : morOnLocallyNoetherian B S hS X ≅ contractionFunctor c) :
    ∃ s : Solution c X, Set.range (Space.pointsMap B S hS s.U.toFunctor s.U.ι) = s.Tᶜ :=
  exists_solution_of_iso_range_U c e.symm hX
    (Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
      (Space.isLocallyOfFinitePresentation_of_limitPreserving B S hS hX hl))

/-- **From a representing algebraic space with large values to a solution.** Let `F'` be an
algebraic space over `S` with values in `Type (u + 1)`, limit preserving, whose restriction to the
locally Noetherian schemes over `S` is Artin's functor `F`. Then `F'` is the universe lift of an
algebraic space `X` of `Type u`, and `X` is a solution with `U = X ∖ T`. -/
theorem exists_solution_of_isAlgebraicSpaceULift {F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (hF' : Space.IsAlgebraicSpaceULift.{u + 1} B S hS F')
    (hl : LimitPreserving.{u, u + 1, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) F')
    (e : (LocallyNoetherianOver.toBigFppfOver B S hS).op ⋙ F' ≅ contractionFunctor c) :
    ∃ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (s : Solution c X),
      Set.range (Space.pointsMap B S hS s.U.toFunctor s.U.ι) = s.Tᶜ := by
  obtain ⟨X, hX, ⟨eX⟩⟩ := Space.exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS hF'
  have hlX : LimitPreserving.{u, u, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) X := by
    intro I _ _ D c' hc haff hpt
    obtain ⟨hcol⟩ := hl I D c' hc haff hpt
    have h₁ : IsColimit ((X ⋙ uliftFunctor.{u + 1}).mapCocone c'.op) :=
      (IsColimit.precomposeHomEquiv (Functor.isoWhiskerLeft D.op eX).symm _)
        (IsColimit.ofIsoColimit hcol (Cocones.ext (eX.app _).symm (fun j => by
          simp only [Functor.mapCocone_ι_app, Iso.symm_hom, Iso.app_inv,
            Cocone.precompose_obj_ι, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
            Functor.whiskerLeft_app]
          exact eX.inv.naturality _)))
    exact ⟨isColimitOfReflects uliftFunctor.{u + 1} h₁⟩
  exact ⟨X, exists_solution_of_restriction_iso c hX hlX
    (Functor.isoWhiskerLeft (LocallyNoetherianOver.toBigFppfOver B S hS).op eX ≪≫ e)⟩

/-- **Artin's axioms for `F` give a solution** (the proof of Stacks 0GIB, granting the axioms).
If the diagonal of Artin's functor `F` is representable and `F` satisfies Artin's axioms
`[-1]`–`[5]` on the locally Noetherian site, and the local rings of `S` at finite type points are
G-rings, then Stacks 0GE7 (for the `u`-small valued `F`,
`AlgebraicGeometry.Artin.ContractionSituation.small_contractionFunctor_obj`) gives a limit
preserving algebraic space restricting to `F`, which is a solution with `U = X ∖ T`. The
solution's target `X` is limit preserving, which is recorded as well. -/
theorem exists_solution_of_satisfiesArtinAxioms
    (hG : ∀ s : S, IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s))
    (hdiag : (uliftYoneda.{u + 1} (C := LocallyNoetherianOver B S hS)).relativelyRepresentable
      (diag (contractionFunctor c)))
    (hax : LocallyNoetherianOver.SatisfiesArtinAxioms B S hS (contractionFunctor c)) :
    ∃ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (s : Solution c X),
      Set.range (Space.pointsMap B S hS s.U.toFunctor s.U.ι) = s.Tᶜ ∧
        LimitPreserving.{u, u, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) X := by
  have := c.isLocallyNoetherian_base
  obtain ⟨X, hX, hl, ⟨e⟩⟩ := LocallyNoetherianOver.exists_isAlgebraicSpace_restriction_iso_of_small
    (contractionFunctor c) (small_contractionFunctor_obj c) hdiag hax hG
  obtain ⟨s, hs⟩ := exists_solution_of_restriction_iso c hX hl e
  exact ⟨X, s, hs, hl⟩

end AlgebraicGeometry.Artin.ContractionSituation

end
