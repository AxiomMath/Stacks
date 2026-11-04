module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionRepresents

/-!
# Stacks 0GHB: the statement decided

In the situation of Stacks 0GH8 (`AlgebraicGeometry.Artin.ContractionSituation`), **Stacks 0GHB**
reads

> if there exists a solution `(f : X' → X, T, a)` then there is a functorial bijection
> `F(V) = Mor_S(V, X)` on the category of locally Noetherian schemes `V` over `S`,

where `F` is Artin's functor of Stacks 0GHA (`AlgebraicGeometry.Artin.contractionFunctor`) and a
solution is defined in the prose after Situation 0GH8: a proper `f`, a closed `T ⊆ |X|` and an
isomorphism `a : X_{/T} → W` with (1) `T' = |f|⁻¹T`, (2) `f` maps `U'` isomorphically to an open
subspace `U` of `X`, (3) `g = a ∘ f_{/T}` (`AlgebraicGeometry.Artin.ContractionSituation.Solution`,
which follows that definition literally).

As printed the lemma is false, the current online version of the tag (with no
comments or corrections) included. Condition (2) only asks for *some* open subspace `U ⊆ X`, and
nothing then ties the part of `X` outside `U ∪ T` to the data `(X', T', W, g)` that `F` sees. Over
any nonempty locally Noetherian `S` take `X' = ∅`, `T' = ∅`, `W = X'_{/T'} = ∅`, `g = id`. Then
`F(V)` is empty for every nonempty `V` (`u' : V ∖ Z → U' = ∅` forces `Z = V`, and then
`x̂ : V_{/V} → W = ∅` is impossible), while `X = S`, `f : ∅ → S`, `T = ∅`, `U = ∅`,
`a = f_{/T}⁻¹` is a solution with `Mor_S(S, S) ≠ ∅`. The formal proof is
`AlgebraicGeometry.Artin.ContractionSituation.not_forall_nonempty_iso_of_solution`.

What the source intends is visible in its proof, which takes `u' : V ∖ Z → U' = U` to be the
restriction of `x : V → X` to `V ∖ Z = x⁻¹(|X| ∖ T)`: the open subspace `U` of condition (2) is
the open subspace of `X` with `|U| = |X| ∖ T`, just as `U'` is the open subspace of `X'` with
`|U'| = |X'| ∖ T'` in Situation 0GH8 (and the solution built in Stacks 0GHC has this property).
For those solutions the lemma holds, by the source's proof
(`AlgebraicGeometry.Artin.ContractionSituation.Solution.contractionFunctorIso`).

This file records both halves in one statement, in the namespace
`AlgebraicGeometry.Artin.ContractionSituation`:

## Main results

* `nonempty_iso_morOnLocallyNoetherian_of_solution_and_not_forall`: **Stacks 0GHB**, corrected;
  the functorial bijection for the solutions with `|U| = |X| ∖ T`, and the failure of the
  printed statement for the literal notion of solution.

## References

* [Stacks Project, Tag 0GH8](https://stacks.math.columbia.edu/tag/0GH8)
* [Stacks Project, Tag 0GHA](https://stacks.math.columbia.edu/tag/0GHA)
* [Stacks Project, Tag 0GHB](https://stacks.math.columbia.edu/tag/0GHB)
* [Stacks Project, Tag 0GHC](https://stacks.math.columbia.edu/tag/0GHC)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0GHB, corrected.** In the situation of Stacks 0GH8, over a locally Noetherian scheme
`S`:

1. for every solution `(f : X' → X, T, a)` whose open subspace `U` of condition (2) is the open
   subspace of `X` with `|U| = |X| ∖ T` — the solutions the source's proof works with, since it
   takes `u' : V ∖ Z → U' = U` to be the restriction of `x` to `V ∖ Z = x⁻¹(|X| ∖ T)` — there is
   a functorial bijection `F(V) = Mor_S(V, X)` on the category of locally Noetherian schemes `V`
   over `S`, where `F` is Artin's functor of Stacks 0GHA; and
2. for the literal notion of solution of the prose after Situation 0GH8, which lets `U` be any
   open subspace of `X` onto which `f` maps `U'` isomorphically, the statement as printed fails
   as soon as `S` is nonempty: the situation `(X' = ∅, T' = ∅, W = ∅, g = id)` has the solution
   `X = S` (with `U = ∅ ≠ S = X ∖ T`), and `F(S) = ∅ ≠ Mor_S(S, S)`.

The bijection of (1) is `x ↦ (x⁻¹T, x|_{V ∖ Z}, a ∘ x_{/Z})`
(`AlgebraicGeometry.Artin.ContractionSituation.Solution.contractionFunctorIso`); its inverse comes
from the existence half of Stacks 0GI3 and its injectivity from the uniqueness of Stacks 0GI1. -/
@[stacks 0GHB "erratum: as printed the lemma is false for the literal notion of solution of \
Situation 0GH8 (part 2, over any nonempty S); it holds for the solutions whose open subspace U \
is the complement X ∖ T, the reading of condition (2) the source's proof uses (part 1)"]
theorem nonempty_iso_morOnLocallyNoetherian_of_solution_and_not_forall
    (hSN : IsLocallyNoetherian S) :
    (∀ (c : ContractionSituation B S hS) (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
        (s : Solution c X), s.U = Space.openSubspaceOfPoints B S hS X s.Tᶜ →
          Nonempty (contractionFunctor c ≅ morOnLocallyNoetherian B S hS X)) ∧
      (Nonempty S → ¬ ∀ (c : ContractionSituation B S hS)
        (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), Solution c X →
          Nonempty (contractionFunctor c ≅ morOnLocallyNoetherian B S hS X)) := by
  refine ⟨fun c X s hU => ⟨s.contractionFunctorIso ?_⟩,
    fun _ => not_forall_nonempty_iso_of_solution hSN⟩
  rw [hU, Space.range_pointsMap_ι_openSubspaceOfPoints]

end AlgebraicGeometry.Artin.ContractionSituation

end
