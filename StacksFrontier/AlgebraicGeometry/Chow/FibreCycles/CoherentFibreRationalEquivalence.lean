module

public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.CoherentFibreComparison

/-!
# Stacks 02S6 at the source's hypotheses

Let `f : X ⟶ S` be locally of finite type over the base scheme of chapter 42, let `F` be a
coherent sheaf on `X ×_S 𝐏¹_S`, and write `F₀ = i₀^* F`, `F_∞ = i_∞^* F` for its pullbacks along
the zero and infinity sections. If

1. `dim_δ(Supp(F)) ≤ k + 1`,
2. `dim_δ(Supp(F₀)) ≤ k` and `dim_δ(Supp(F_∞)) ≤ k`, and
3. every associated point `ξ` of `F` either lies outside `(X ×_S 𝐏¹_S)₀ ∪ (X ×_S 𝐏¹_S)_∞` or
   has `δ(ξ) < k`,

then `[F₀]_k ∼_rat [F_∞]_k` as `k`-cycles on `X`.

The two fibres are coherent by Stacks 0EBF (`Stacks.Chow.isCoherent_zeroFibreModule`,
`Stacks.Chow.isCoherent_infinityFibreModule`); the statement below discharges this inside its
type, so the only hypotheses are the coherence of `F` and the three numbered conditions, each
in the source's form: the delta-dimension of a support is the delta-dimension of the reduced
closed subscheme it underlies, and `δ` on `X ×_S 𝐏¹_S` is the relative dimension along its
structure morphism to `S`.

Condition (3) is on every associated point of `F`. Restricting it to the embedded associated
points makes the lemma false; the counterexample (the structure sheaf of the zero section of
`𝐏¹` over a field, with `k = 0`) is
`Stacks.Chow.not_forall_rationallyEquivalent_of_isEmbeddedAssociatedPoint`.

## Main results

* `Stacks.Chow.rationallyEquivalent_cycleAssociatedToCoherentSheaf_fibres` — Stacks 02S6.

## References

* [Stacks Project, Tag 02S6](https://stacks.math.columbia.edu/tag/02S6)
* [Stacks Project, Tag 0EBF](https://stacks.math.columbia.edu/tag/0EBF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)

/-- **Stacks 02S6.** Let `F` be a coherent sheaf on `X ×_S 𝐏¹_S` with
`dim_δ(Supp(F)) ≤ k + 1`, with `dim_δ(Supp(F₀)) ≤ k` and `dim_δ(Supp(F_∞)) ≤ k`, and such that
every associated point `ξ` of `F` lies outside the union of the two distinguished sections or has
`δ(ξ) < k`. Then `[F₀]_k` and `[F_∞]_k` are rationally equivalent `k`-cycles on `X`.

The coherence of `F₀` and `F_∞`, needed to form their cycles, is Stacks 0EBF and is supplied in
the statement rather than assumed. -/
@[stacks 02S6]
theorem rationallyEquivalent_cycleAssociatedToCoherentSheaf_fibres
    (F : (projectiveLineProduct f).Modules) [F.IsCoherent]
    (hSupp : schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ productBase f) ≤
      ((k + 1 : ℤ) : EInt))
    (h₀ : haveI := isCoherent_zeroFibreModule C f F
      schemeDeltaDimension C ((reducedSupport (zeroFibreModule f F)).subschemeι ≫ f) ≤
        (k : EInt))
    (hInf : haveI := isCoherent_infinityFibreModule C f F
      schemeDeltaDimension C ((reducedSupport (infinityFibreModule f F)).subschemeι ≫ f) ≤
        (k : EInt))
    (hAssociated : ∀ ξ ∈ Stacks.Divisors.associatedPoints F,
      ξ ∉ Set.range (zeroSection f) ∪ Set.range (infinitySection f) ∨
        relativeDimension C.dimensionFunction (productBase f) ξ < k) :
    haveI := isCoherent_zeroFibreModule C f F
    haveI := isCoherent_infinityFibreModule C f F
    RationallyEquivalent C f k
      (cycleAssociatedToCoherentSheaf C f (zeroFibreModule f F) k h₀)
      (cycleAssociatedToCoherentSheaf C f (infinityFibreModule f F) k hInf) :=
  have := isCoherent_zeroFibreModule C f F
  have := isCoherent_infinityFibreModule C f F
  cycleAssociatedToCoherentFibres_rationallyEquivalent_of_decompositionRule C f k F
    (fun _ hξ => relativeDimension_le_of_schemeDeltaDimension_reducedSupport_le C
      (productBase f) (k + 1) hSupp hξ)
    h₀ hInf fun ξ hξ => (hAssociated ξ hξ).imp_left fun h =>
      ⟨fun h₀ => h (Or.inl h₀), fun h₁ => h (Or.inr h₁)⟩

end Stacks.Chow

end
