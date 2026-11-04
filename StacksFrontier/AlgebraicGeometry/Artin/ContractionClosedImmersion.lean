module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionClosedImmersionHypotheses

/-!
# Contractions inside the base: Stacks 0GHE

In Situation 0GH8 (`AlgebraicGeometry.Artin.ContractionSituation`) assume `X' → S` is proper
and let `Z ⊆ S` be a closed subset such that

1. the inverse image of `Z` in `X'` is `T'`,
2. `U' → S ∖ Z` is a closed immersion,
3. `W → S_{/Z}` is a closed immersion.

Then there is a solution `(f : X' → X, T, a)` and moreover `X → S` is a closed immersion
(**Stacks 0GHE**).

The solution is the closed subspace `X ⊆ S` cut out by the ideal sheaf glued from the ideals
`J_U ⊆ Γ(S, U)` over the affine opens `U` of `S`
(`AlgebraicGeometry.Artin.ContractionSituation.ClosedImmersionData.subspace`): it contains the
image of `X'`, meets `S ∖ Z` in the image of `U'`, and its completion along `Z` is `W`
(`ContractionClosedImmersionHypotheses`), so it is a solution by
`AlgebraicGeometry.Artin.ContractionSituation.solution_of_isClosedSubspace`.

The hypothesis that `X' → S` is proper is part of the statement; the proof
uses it (through the theorem on formal functions in the source, through the scheme-theoretic
image of `X'` and Stacks 0GD6 here). Without it the conclusion fails: for `S = 𝔸¹_k`,
`Z = {0}`, `X' = 𝔾_m ⊔ Spec k` with `T' = Spec k`, `W = Spec k` and `g = id`, all three
conditions hold, but a closed subscheme of `S` containing `𝔾_m` is `S`, whose completion along
`Z` is not `W`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0GHE.** In the situation of Stacks 0GH8, let `X' → S` be proper and let `Z ⊆ |S|`
be a closed subset such that the inverse image of `Z` in `X'` is `T'`, the morphism
`u : U' → S ∖ Z` is a closed immersion and the morphism `w : W → S_{/Z}` is a closed immersion.
Then there exists a solution `(f : X' → X, T, a)`, and moreover `X → S` is a closed
immersion. The solution produced also has `|U| = |X| ∖ T` for its open subspace `U`, the reading
of a solution under which Stacks 0GHB holds. -/
theorem exists_solution_of_isClosedImmersion (c : ContractionSituation B S hS)
    (hproper : Space.IsProper B S hS (terminal.from c.X'))
    (Z : Set (Space.points B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))))
    (hZ : IsClosed Z)
    (hT' : Space.pointsMap B S hS c.X' (terminal.from c.X') ⁻¹' Z = c.T')
    (u : c.U'.toFunctor ⟶
      (Space.openSubspaceOfPoints B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) Zᶜ).toFunctor)
    (hu : Space.IsClosedImmersion B S hS u)
    (w : c.W ⟶ Space.completionSheaf B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) Z)
    (hw : FormalSpace.IsClosedImmersion B S hS w) :
    ∃ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (s : c.Solution X),
      Set.range (Space.pointsMap B S hS s.U.toFunctor s.U.ι) = s.Tᶜ ∧
      Space.IsClosedImmersion B S hS (terminal.from X) := by
  let h : ClosedImmersionData c :=
    { hproper := hproper, Z := Z, hZ := hZ, hT' := hT', u := u, hu := hu, w := w, hw := hw }
  obtain ⟨⟨sol, hU⟩, hcl⟩ := solution_of_isClosedSubspace c hproper Z hZ hT' u hu w hw h.subspace
    h.isClosedSubspace_subspace h.range_le_subspace h.subspace_inf_compl
    h.nonempty_hom_W_completion h.nonempty_hom_completion_W
  exact ⟨h.subspace.toFunctor, sol, hU, hcl⟩

end AlgebraicGeometry.Artin.ContractionSituation
