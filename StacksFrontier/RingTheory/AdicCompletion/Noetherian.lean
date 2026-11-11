module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

@[expose] public section

/-!
# The adic completion over a Noetherian ring is adically complete

Proof of Stacks 031C. Let `R` be a Noetherian ring, let `I ⊆ R` be an ideal and let `M` be an
`R`-module. Then the `I`-adic completion `M^∧ = lim M/IⁿM` is again `I`-adically complete.

Over a general ring this fails, and the single property of `R` that the source's argument uses is
that `I` is finitely generated; over a Noetherian ring that is automatic, `I` being a submodule of
`R`. So the proof is the general form of the statement, Lemma 05GG, fed the finite generation that
`IsNoetherianRing R` supplies.

## Main results

* `Stacks.AdicCompletion.NoetherianComplete.solution`: the first assertion of Stacks 031C, that
  `M^∧` is `I`-adically complete. The whole lemma is
  `AdicCompletion.isAdicComplete_and_pow_smul_top_eq_range_ofPowSMul_and_bijective_liftQ_eval`
  in `StacksFrontier.RingTheory.AdicCompletion.NoetherianQuotPow`.

## Implementation notes

The general form is Mathlib's `AdicCompletion.isAdicComplete`, which already carries the tag
`05GG` upstream, and `IsNoetherian.noetherian I : I.FG` is the specialisation the source's
"because `I` is a finitely generated ideal" names.

## References

* [StackProject 031C](https://stacks.math.columbia.edu/tag/031C)
* [StackProject 05GG](https://stacks.math.columbia.edu/tag/05GG)
-/

@[expose] public section

namespace Stacks.AdicCompletion.NoetherianComplete

public theorem solution {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M] :
    IsAdicComplete I (AdicCompletion I M) :=
  AdicCompletion.isAdicComplete (IsNoetherian.noetherian I)

end Stacks.AdicCompletion.NoetherianComplete

end

/-!
# The adic completion over a Noetherian ring is adically complete

Let `R` be a Noetherian ring, let `I ⊆ R` be an ideal and let `M` be an `R`-module. Then the
`I`-adic completion `M^∧ = lim M/IⁿM` is again `I`-adically complete, `IⁿM^∧ = (IⁿM)^∧` inside
`M^∧`, and `M^∧/IⁿM^∧ = M/IⁿM`. Over a general ring none of this need hold: the completion of
`k[x₁, x₂, x₃, …]` along `(x₁, x₂, x₃, …)` is not complete for that ideal (Stacks 05JA). What
makes the three assertions go through is finite generation of `I`, which over a Noetherian ring
is automatic, and the source uses the Noetherian hypothesis for nothing else.

## Main results

* `AdicCompletion.isAdicComplete_and_pow_smul_top_eq_range_ofPowSMul_and_bijective_liftQ_eval`:
  the three assertions of Stacks 031C, in `StacksFrontier.RingTheory.AdicCompletion.NoetherianQuotPow`.
* `AdicCompletion.instIsAdicComplete`: over a Noetherian ring, `AdicCompletion I M` is
  `I`-adically complete — as an instance, so that completeness of a completion is available to
  type class inference.

## Implementation notes

The Noetherian hypothesis is carried as the class `IsNoetherianRing R` rather than as the
finite-generation hypothesis it is used through. That is the whole point of the lemma in Lean, and
the reason it deserves a declaration of its own rather than being a specialisation spelled out at
each call site: the general form of the statement, Lemma 05GG, takes `I.FG` as an *explicit*
argument and therefore cannot be an instance, whereas over a Noetherian ring `I.FG` is a
consequence of a class and completeness of `M^∧` becomes a fact inference can find. Downstream
this is how the source itself uses the lemma — "`A^∧` is `IA^∧`-adically complete, see Algebra,
Lemma 031C" — where the completeness is a hypothesis of the next lemma, not a term to be built.

The other two assertions specialise from Lemma 05GG and Mathlib by the same one step
`IsNoetherian.noetherian I : I.FG`. Writing `IⁿM` Mathlib's way as `I ^ n • (⊤ : Submodule R M)`
and taking `(IⁿM)^∧ → M^∧` to be `AdicCompletion.ofPowSMul I M n`, the completion of the inclusion
`IⁿM ⊆ M`, the equality `IⁿM^∧ = (IⁿM)^∧` of submodules of `M^∧` is

`(AdicCompletion.pow_smul_top_eq_ker_eval (IsNoetherian.noetherian I)).trans`
`  (AdicCompletion.restrictScalars_range_ofPowSMul_eq_ker_eval I).symm`,

the map `(IⁿM)^∧ → M^∧` is injective by Mathlib's `AdicCompletion.ofPowSMul_injective`, and the
map `M^∧/IⁿM^∧ → M/IⁿM` induced by the projection `M^∧ → M/IⁿM` is bijective by
`AdicCompletion.bijective_liftQ_eval (IsNoetherian.noetherian I) M n` (the isomorphism itself is
`AdicCompletion.quotPowSMulTopEquiv`).

Both assertions are stated for every `n : ℕ`, as in the source; at `n = 0` they hold trivially.

Faithfulness. (1) The hypotheses are the source's and both are live: `IsNoetherianRing R` cannot
be dropped, since over `k[x₁, x₂, …]` and `I = (x₁, x₂, …)` the completion `R^∧` is not
`I`-adically complete (Stacks 05JA); `I` and `M` occur in the conclusion. (2) The scalars are the
source's: `M` is an `R`-module and `IsAdicComplete I (AdicCompletion I M)` is completeness of
`M^∧` for `I` acting through `R`, which is the source's "`I`-adically complete" and not the
a priori different completeness for the ideal `IR^∧` of `R^∧`. (3) The module completed is the
source's, `AdicCompletion I M = lim M/IⁿM`. (4) The instantiation is not degenerate: for `R = ℤ`,
`I = (p)` and `M = ℤ` this says that the ring `ℤ_p` of `p`-adic integers is `p`-adically complete.

## References

* [StackProject 031C](https://stacks.math.columbia.edu/tag/031C)
* [StackProject 05GG](https://stacks.math.columbia.edu/tag/05GG)

## Tags

adic completion, complete, Noetherian ring
-/

@[expose] public section

namespace AdicCompletion

/-- Adic completeness over a Noetherian ring, as an instance. Let `R` be a Noetherian ring, `I` an
ideal of `R` and `M` an `R`-module. Then the `I`-adic completion `M^∧` of `M` is `I`-adically
complete. This is the Noetherian form of `AdicCompletion.isAdicComplete`, stated as an instance:
over a Noetherian ring the finite generation of `I` that the proof needs is automatic, so no side
condition has to be supplied. The three assertions of Stacks 031C together are
`AdicCompletion.isAdicComplete_and_pow_smul_top_eq_range_ofPowSMul_and_bijective_liftQ_eval`. -/
@[stacks 031C "The first assertion, `M^∧` is `I`-adically complete, as an instance for type class
inference. The full lemma, all three assertions, is
`AdicCompletion.isAdicComplete_and_pow_smul_top_eq_range_ofPowSMul_and_bijective_liftQ_eval`."]
public instance instIsAdicComplete {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M] :
    IsAdicComplete I (AdicCompletion I M) :=
      by apply Stacks.AdicCompletion.NoetherianComplete.solution

end AdicCompletion

end
