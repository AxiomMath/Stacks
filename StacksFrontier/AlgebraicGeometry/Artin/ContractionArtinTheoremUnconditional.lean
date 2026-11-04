module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionArtinTheorem
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionFormalObjectEffective

/-!
# Artin's theorem on contractions (Stacks 0GIB)

In Situation 0GH8 with `X'` and `W` separated over `S`, and the local rings of `S` at finite type
points G-rings, Artin's contraction functor `F` of Stacks 0GHA satisfies the hypotheses of
Stacks 0GE7: its diagonal is representable by closed immersions (Stacks 0GHF), and it satisfies
`[-1]` (the size bound), `[0]` (Stacks 0GHG), `[1]` (Stacks 0GI5), `[2]` (Stacks 0GI6), `[3]`
(Stacks 0GI7), `[4]` (Stacks 0GI8) and `[5]` (Stacks 0GIA). So `F` is the restriction of a limit
preserving algebraic space `X`, which is a solution by Stacks 0GHC. The assembly with axiom `[4]`
as a hypothesis is
`AlgebraicGeometry.Artin.ContractionSituation.exists_solution_of_hasEffectiveFormalObjects`; here
`[4]` is discharged by
`AlgebraicGeometry.Artin.ContractionSituation.hasEffectiveFormalObjects` (Stacks 0GI8).

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.exists_solution_limitPreserving_of_isSeparated`:
  a solution with `|U| = |X| ∖ T` and limit preserving target.
* `AlgebraicGeometry.Artin.ContractionSituation.exists_solution_of_isSeparated`: Stacks 0GIB.

## References

* [Stacks Project, Tag 0GIB](https://stacks.math.columbia.edu/tag/0GIB)
* [M. Artin, *Algebraization of formal moduli II*, Theorem 3.1]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Artin's contraction, separated case, with a limit preserving target.** In Situation 0GH8,
if the local rings of `S` at finite type points are G-rings and `X'`, `W` are separated over `S`,
then there is a solution `(f : X' ⟶ X, T, a)` with `|U| = |X| ∖ T` whose target `X` is limit
preserving. -/
theorem exists_solution_limitPreserving_of_isSeparated (c : ContractionSituation B S hS)
    (hG : ∀ s : S, IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s))
    (hX' : Space.IsSeparated B S hS (terminal.from c.X'))
    (hW : FormalSpace.IsSeparatedMorphism B S hS (terminal.from c.W)) :
    ∃ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (s : Solution c X),
      Set.range (Space.pointsMap B S hS s.U.toFunctor s.U.ι) = s.Tᶜ ∧
        LimitPreserving.{u, u, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) X :=
  exists_solution_of_hasEffectiveFormalObjects c hG hX' hW (c.hasEffectiveFormalObjects hX')

/-- **Stacks 0GIB (Artin's theorem on contractions).** Let `S` be a locally Noetherian scheme whose
local rings at finite type points are G-rings, `X'` an algebraic space locally of finite type over
`S`, `T' ⊆ |X'|` closed, `W` a locally Noetherian formal algebraic space over `S` with `W_red`
locally of finite type over `S`, and `g : X'_{/T'} ⟶ W` a formal modification (Situation 0GH8,
the data of `c`). If `X'` and `W` are separated over `S`, then there are a proper morphism
`f : X' ⟶ X` of algebraic spaces over `S`, a closed subset `T ⊆ |X|` and an isomorphism
`a : X_{/T} ≅ W` such that (1) `T'` is the inverse image of `T` under `|f|`, (2) `f` maps
`X' ∖ T'` isomorphically onto `X ∖ T` (the open subspace `U` of the solution has `|U| = |X| ∖ T`),
and (3) `g = a ∘ f_{/T}`. -/
@[stacks 0GIB]
theorem exists_solution_of_isSeparated (c : ContractionSituation B S hS)
    (hG : ∀ s : S, IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s))
    (hX' : Space.IsSeparated B S hS (terminal.from c.X'))
    (hW : FormalSpace.IsSeparatedMorphism B S hS (terminal.from c.W)) :
    ∃ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (s : Solution c X),
      Set.range (Space.pointsMap B S hS s.U.toFunctor s.U.ι) = s.Tᶜ := by
  obtain ⟨X, s, hs, -⟩ := exists_solution_limitPreserving_of_isSeparated c hG hX' hW
  exact ⟨X, s, hs⟩

end AlgebraicGeometry.Artin.ContractionSituation

end
