module

public import Mathlib.FieldTheory.Galois.Basic
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.BlowupPushforward
public import StacksCore.Tactic.StacksAttribute

/-!
# The trace of the unit class on the spectrum of a Galois extension

Let `k'/k` be a finite Galois extension. Then `Spec(k')` is a nonempty smooth projective scheme
over `k`, equidimensional of dimension `0`, so axiom `(A6)` provides a trace map
`∫_{Spec(k')} = λ : H^0(Spec(k'))(0) → F`, and its value on the unit class is the degree:

`∫_{Spec(k')} 1 = [k' : k]`.

The proof is the source's. On the self-product one has the decomposition of cycles

`Spec(k') × Spec(k') = ∐_{σ ∈ Gal(k'/k)} (Spec(σ) × id)^{-1} Δ`,

and the cycle class map sends the fundamental class of a scheme to the unit class, so
`1 ⊗ 1 = γ([Spec(k') × Spec(k')]) = ∑_σ (Spec(σ) × id)^* γ([Δ])`. Applying the contraction
`id ⊗ λ` to both sides and using that it commutes with a pullback acting on the left-hand factor
turns the right-hand side into `∑_σ (Spec(σ))^* ((id ⊗ λ) γ([Δ])) = ∑_σ (Spec(σ))^* 1 = ∑_σ 1`,
by the normalisation `(id ⊗ λ) γ([Δ]) = 1` of `(A6)`, while the left-hand side is `λ(1) · 1`.
Hence `λ(1) · 1` is the sum of `|Gal(k'/k)|` copies of the unit class, and since the cohomology
of the nonempty scheme `Spec(k')` is nonzero this forces `λ(1) = |Gal(k'/k)| = [k' : k]`.

## Main results

* `Stacks.WeilCohomology.integration_one_eq_finrank`: `∫_{Spec(k')} 1 = [k' : k]` for a finite
  Galois extension `k'/k`.

## Implementation notes

The statement isolates the part of the data `(D0)`, `(D1)`, `(D2')` and of the axioms `(A1)` --
`(A7)` that this argument consumes, which is how the lemmas of Section 45.14 are stated
throughout this directory; compare
`Stacks.WeilCohomology.injective_pullback_of_separable`, Tag 0FVS, and
`StacksFrontier.AlgebraicGeometry.WeilCohomology.BlowupPushforward`.

The coefficient space is `A = H^0(Spec(k'))`. Since `Spec(k')` is zero dimensional the Tate twist
`H^0(Spec(k'))(0)` is `H^0(Spec(k'))` itself, so no twist or degree cast intervenes, and the
cohomology of the self-product in the relevant degree is `A ⊗_F A` by `(A5)` together with
`(A1)`, which is where the diagonal class is read. `Nontrivial A` is the nonvanishing of the
cohomology of a nonempty scheme, which the trace map of `(A6)` yields: for the spectrum of a
finite separable extension that deduction is
`Stacks.WeilCohomology.nontrivial_of_traceMap`, from the value `[k' : k]` the trace takes on the
cycle class of the fundamental class.

The cycles on the self-product are the abelian group `CH`, with `fund` the fundamental class
`[Spec(k') × Spec(k')]` and `diag` the class of the diagonal `[Δ]`; `cyclePull σ` is the pullback
`(Spec(σ) × id)^!` on cycles and `pullback σ` is `(Spec(σ))^*` on cohomology, the latter being
part of the functor of `(D1)`. The hypotheses then read as follows. `decomposition` is the
source's decomposition of the self-product displayed above, an identity of cycles.
`gamma` is the cycle class map `γ` of Lemma 45.14.5, Tag 0FIF, in the degree at issue, and
`gamma_fund` is the source's observation that `γ` sends the fundamental class of a scheme to the
unit class. `gamma_cyclePull` is compatibility of `γ` with pullback, read through the Künneth
identification of `(Spec(σ) × id)^*` with `(Spec(σ))^* ⊗ id`. `pullback_one` is that the pullback
maps of `(D1)` are maps of algebras, hence preserve the unit class. `normalization` is axiom
`(A6)`, the equation `(id ⊗ λ) γ([Δ]) = 1` characterising `λ`; the contraction `id ⊗ λ` is
`Stacks.WeilCohomology.tensorContractRight`. By Remark 45.14.6, Tag 0FIK, that equation
determines `λ`, which is what licenses writing it `∫_{Spec(k')}`.

Galois-ness of `k'/k` is used twice: it indexes the decomposition by the automorphism group, and
it makes the count of that group the degree, which is
`IsGalois.card_aut_eq_finrank`. Finiteness of the extension is the source's, since `Spec(k')` is
projective over `k`.

## References

* [Stacks Project, Tag 0FVR](https://stacks.math.columbia.edu/tag/0FVR)
* [Stacks Project, Tag 0FIF](https://stacks.math.columbia.edu/tag/0FIF)
* [Stacks Project, Tag 0FIK](https://stacks.math.columbia.edu/tag/0FIK)
-/

@[expose] public section

universe u uF uA uC

open scoped TensorProduct

namespace Stacks.WeilCohomology

/-- **Stacks Project, Tag 0FVR.** For a finite Galois extension `k'/k` the trace map
`∫_{Spec(k')} = λ` of axiom `(A6)` takes the unit class to the degree of the extension:
`∫_{Spec(k')} 1 = [k' : k]`.

Here `A` is `H^0(Spec(k'))`, nonzero because `Spec(k')` is nonempty, and `A ⊗_F A` is the
cohomology of `Spec(k') × Spec(k')` in the same degree by axioms `(A5)` and `(A1)`; `CH` is the
group of cycles on the self-product, carrying the fundamental class `fund` and the class `diag`
of the diagonal. The hypothesis `decomposition` is the source's identity of cycles
`Spec(k') × Spec(k') = ∐_{σ ∈ Gal(k'/k)} (Spec(σ) × id)^{-1} Δ`, and `normalization` is the
equation of axiom `(A6)` that characterises `λ`. The module documentation reads each hypothesis
against the data `(D0)`, `(D1)`, `(D2')` and the axioms. -/
@[stacks 0FVR "the value of the trace map of axiom (A6) on the unit class of the spectrum of a \
  finite Galois extension; the part of the data (D0), (D1), (D2') and of the axioms (A1) -- (A7) \
  the argument consumes is carried as hypotheses, as elsewhere in Section 45.14, and the \
  decomposition of the self-product into Galois translates of the diagonal is the hypothesis \
  `decomposition`"]
theorem integration_one_eq_finrank
    (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] [IsGalois k k']
    {F : Type uF} [Field F] {A : Type uA} [Ring A] [Algebra F A] [Nontrivial A]
    {CH : Type uC} [AddCommGroup CH]
    (fund diag : CH)
    (cyclePull : (k' ≃ₐ[k] k') → CH →+ CH)
    (gamma : CH →+ A ⊗[F] A)
    (pullback : (k' ≃ₐ[k] k') → A →ₗ[F] A)
    (decomposition : fund = ∑ σ : k' ≃ₐ[k] k', cyclePull σ diag)
    (gamma_fund : gamma fund = (1 : A) ⊗ₜ[F] (1 : A))
    (gamma_cyclePull : ∀ (σ : k' ≃ₐ[k] k') (c : CH),
      gamma (cyclePull σ c) = TensorProduct.map (pullback σ) LinearMap.id (gamma c))
    (pullback_one : ∀ σ : k' ≃ₐ[k] k', pullback σ 1 = 1)
    (lam : A →ₗ[F] F)
    (normalization : tensorContractRight lam (gamma diag) = (1 : A)) :
    lam 1 = (Module.finrank k k' : F) := by
  classical
  have hunit : tensorContractRight lam (gamma fund) = lam 1 • (1 : A) := by
    rw [gamma_fund, tensorContractRight_tmul]
  have hsum : tensorContractRight lam (gamma fund) = ∑ _σ : k' ≃ₐ[k] k', (1 : A) := by
    rw [decomposition, map_sum, map_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [gamma_cyclePull, tensorContractRight_map, LinearMap.comp_id, normalization,
      pullback_one]
  rw [hunit, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    ← Nat.cast_smul_eq_nsmul F, IsGalois.card_aut_eq_finrank k k'] at hsum
  exact (algebraMap F A).injective (by simpa [Algebra.smul_def] using hsum)

end Stacks.WeilCohomology

end
