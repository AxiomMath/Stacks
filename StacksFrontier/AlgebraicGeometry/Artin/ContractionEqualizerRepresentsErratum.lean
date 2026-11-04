module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionEqualizerRepresentsCounterexample

/-!
# Stacks 0GHD, final conclusion: the statement decided

In the situation of Stacks 0GH8 (`AlgebraicGeometry.Artin.ContractionSituation`), let `V` be a
locally Noetherian scheme over `S` and let `(Zᵢ, u'ᵢ, x̂ᵢ) ∈ F(V)`, `i = 1, 2`, with chosen
compatibility witnesses (`AlgebraicGeometry.Artin.ContractionEqualizer`). The last sentence of
**Stacks 0GHD** reads

> We conclude, using Lemmas 0GHB and 0GHC, that if there is a solution `E → V` for the triple in
> (4), then `E` represents `F ×_{Δ, F × F} V` on the category of locally Noetherian schemes over
> `V`,

where the triple of (4) is `E'`, `(E' → V)⁻¹Z`, `E'_{/Z} → E_W`
(`AlgebraicGeometry.Artin.ContractionEqualizer.situation`), and a solution is defined in the prose
after Situation 0GH8: a proper `f : E' → E`, a closed `T ⊆ |E|` and an isomorphism
`a : E_{/T} → E_W` with (1) `(E' → V)⁻¹Z = |f|⁻¹T`, (2) `f` maps `U'` isomorphically to an open
subspace `U` of `E`, (3) `g = a ∘ f_{/T}` (`AlgebraicGeometry.Artin.ContractionSituation.Solution`,
which follows that definition literally).

As printed the conclusion is false, for the reason Stacks 0GHB is: condition (2) only asks for
*some* open subspace `U ⊆ E`, and nothing then ties the part of `E` outside `U ∪ T` to the triple
of (4). Over any nonempty locally Noetherian `S` take `V = S`, the situation
`(X' = S ⨿ S, T' = ∅, W = X'_{/∅}, g = id)` and the triples of the two inclusions `S ⟶ S ⨿ S`.
These agree nowhere, so `E' = ∅`, `Z = ∅` and the triple of (4) is `(∅, ∅, ∅ → ∅)`; then `E = V`,
`f : ∅ → V`, `T = ∅`, `U = ∅`, `a : V_{/∅} ≅ E_W` is a solution, while `Mor_V(V, V) ∋ id` and
`F ×_{Δ, F × F} V` has no element over `V`. The formal proof is
`AlgebraicGeometry.Artin.ContractionEqualizer.not_forall_nonempty_iso_diagonalFibre_of_solution`.

What the source intends is visible in its proof: the conclusion is drawn from Stacks 0GHB, whose
proof takes `u' : V ∖ Z → U' = U` to be the restriction of `x : V → X` to `V ∖ Z = x⁻¹(|X| ∖ T)`,
that is, it reads the open subspace `U` of condition (2) as the one with `|U| = |X| ∖ T`. For
those solutions the conclusion holds, by the source's proof
(`AlgebraicGeometry.Artin.ContractionEqualizer.morIsoDiagonalFibre`: corrected 0GHB for the
situation of (4), and the identification of its functor with `F ×_{Δ, F × F} V` through (5)).

This file records both halves in one statement, in the namespace
`AlgebraicGeometry.Artin.ContractionEqualizer`:

## Main results

* `nonempty_iso_diagonalFibre_of_solution_and_not_forall`: **Stacks 0GHD**, final conclusion,
  corrected; the representability of `F ×_{Δ, F × F} V` by the solutions with `|U| = |E| ∖ T`,
  and the failure of the printed statement for the literal notion of solution.

## References

* [Stacks Project, Tag 0GH8](https://stacks.math.columbia.edu/tag/0GH8)
* [Stacks Project, Tag 0GHB](https://stacks.math.columbia.edu/tag/0GHB)
* [Stacks Project, Tag 0GHC](https://stacks.math.columbia.edu/tag/0GHC)
* [Stacks Project, Tag 0GHD](https://stacks.math.columbia.edu/tag/0GHD)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Artin.ContractionEqualizer

open ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0GHD, final conclusion, corrected.** In the situation of Stacks 0GH8, over a locally
Noetherian scheme `S`, let `V` be a locally Noetherian scheme over `S` and `d` the data of Stacks
0GHD over `V` (two elements of `F(V)` with chosen compatibility witnesses):

1. for every solution `(f : E' → E, T, a)` of the triple of (4) whose open subspace `U` of
   condition (2) is the open subspace of `E` with `|U| = |E| ∖ T` — the solutions the source's
   proof of 0GHB works with, since it takes `u' : V ∖ Z → U' = U` to be the restriction of `x` to
   `V ∖ Z = x⁻¹(|X| ∖ T)` — `E` represents `F ×_{Δ, F × F} V` on the category of locally
   Noetherian schemes over `V`; and
2. for the literal notion of solution of the prose after Situation 0GH8, which lets `U` be any
   open subspace of `E` onto which `f` maps `U'` isomorphically, the statement as printed fails
   as soon as `S` is nonempty: for the situation `(S ⨿ S, ∅, (S ⨿ S)_{/∅}, id)` and the triples
   of the two inclusions `S ⟶ S ⨿ S` over `V = S`, the triple of (4) is `(∅, ∅, ∅ → ∅)`, which
   has the solution `E = V` (with `U = ∅ ≠ V = E ∖ T`), and `Mor_V(V, V) ∋ id` while
   `F ×_{Δ, F × F} V` has no element over `V`.

The isomorphism of (1) is `AlgebraicGeometry.Artin.ContractionEqualizer.morIsoDiagonalFibre`:
corrected Stacks 0GHB for the situation of (4), followed by the identification of its functor with
`F ×_{Δ, F × F} V` through assertion (5). -/
@[stacks 0GHD "erratum: the final conclusion, that a solution E → V of the triple of (4) \
represents F ×_{Δ, F × F} V on locally Noetherian schemes over V, is false as printed for the \
literal notion of solution of Situation 0GH8 (part 2, over any nonempty S); it holds for the \
solutions whose open subspace U is the complement E ∖ T, the reading of condition (2) the \
source's proof of 0GHB uses (part 1)"]
theorem nonempty_iso_diagonalFibre_of_solution_and_not_forall
    (hSN : IsLocallyNoetherian S) :
    (∀ (c : ContractionSituation B S hS) (V : BigFppfOver B S hS)
        (d : ContractionEqualizer c V) (hVN : IsLocallyNoetherian V.left.obj)
        (E : (BigFppfOver B V.left.obj V.left.property)ᵒᵖ ⥤ Type u)
        (s : Solution (d.situation hVN) E),
        s.U = Space.openSubspaceOfPoints B V.left.obj V.left.property E s.Tᶜ →
          Nonempty (morOnLocallyNoetherian B V.left.obj V.left.property E ≅ d.diagonalFibre)) ∧
      (Nonempty S → ¬ ∀ (c : ContractionSituation B S hS) (V : BigFppfOver B S hS)
        (d : ContractionEqualizer c V) (hVN : IsLocallyNoetherian V.left.obj)
        (E : (BigFppfOver B V.left.obj V.left.property)ᵒᵖ ⥤ Type u),
        Solution (d.situation hVN) E →
          Nonempty (morOnLocallyNoetherian B V.left.obj V.left.property E ≅ d.diagonalFibre)) := by
  refine ⟨fun c V d hVN E s hU => ⟨d.morIsoDiagonalFibre hVN s ?_⟩,
    fun _ => not_forall_nonempty_iso_diagonalFibre_of_solution hSN⟩
  rw [hU, Space.range_pointsMap_ι_openSubspaceOfPoints]

end AlgebraicGeometry.Artin.ContractionEqualizer

end
