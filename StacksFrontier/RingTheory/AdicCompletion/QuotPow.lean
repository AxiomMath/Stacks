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
# The quotients of an adic completion along a finitely generated ideal

Let `R` be a ring, let `I ⊆ R` be an ideal and let `M` be an `R`-module, and write
`M^∧ = lim M/IⁿM` for the `I`-adic completion of `M`. When `I` is finitely generated the
projection `M^∧ → M/IⁿM` induces, for every `n`, an isomorphism of `R`-modules

`M^∧/IⁿM^∧ ≃ M/IⁿM`.

Surjectivity is free, the projection `M^∧ → M/IⁿM` being surjective; injectivity says that `IⁿM^∧`
exhausts the kernel of that projection, and this is where finite generation enters. Indeed the
kernel is always the image of `(IⁿM)^∧` under the completion of the inclusion `IⁿM ⊆ M`, and
finite generation of `Iⁿ` — say by `f₁, …, f_r` — fills it up, because completing the surjection
`(f₁, …, f_r) : M^{⊕ r} → IⁿM` gives a surjection `(M^∧)^{⊕ r} → (IⁿM)^∧` whose image in `M^∧` is
exactly `IⁿM^∧`. Taking `M = R` this says `R^∧/IⁿR^∧ = R/Iⁿ`.

Without finite generation the isomorphism fails: `IⁿM^∧` can be strictly smaller than the kernel,
and `M^∧` need not be `I`-adically complete either (Stacks 05JA).

## Main definitions

* `AdicCompletion.quotPowSMulTopEquiv`: for a finitely generated ideal `I`, the isomorphism
  `AdicCompletion I M ⧸ Iⁿ • AdicCompletion I M ≃ₗ[R] M ⧸ IⁿM` induced by
  `AdicCompletion.eval I M n`.

## Main results

* `AdicCompletion.bijective_liftQ_eval`: for a finitely generated ideal `I`, the map that
  `AdicCompletion.eval I M n` induces on `AdicCompletion I M ⧸ Iⁿ • AdicCompletion I M` is
  bijective. This is the whole content of the statement, and the only place finite generation
  of `I` is used; `AdicCompletion.quotPowSMulTopEquiv` packages it as an isomorphism.

## Implementation notes

The submodule `IⁿM` is written Mathlib's way, as `I ^ n • (⊤ : Submodule R M)`, so that `IⁿM^∧` is
`I ^ n • (⊤ : Submodule R (AdicCompletion I M))` and the source's projection `M^∧ → M/IⁿM` is
`AdicCompletion.eval I M n`.

The isomorphism is not a bare existence statement: it is `LinearEquiv.ofBijective` applied to the
map that `eval I M n` induces on the quotient by `IⁿM^∧`, so its underlying linear map *is* that
induced map, and `quotPowSMulTopEquiv hI M n ⟦x⟧ = x n` holds by `rfl`. What is left to prove is
bijectivity of the induced map, which is stated separately as
`AdicCompletion.bijective_liftQ_eval`: surjectivity is `AdicCompletion.eval_surjective`, and
injectivity says that `IⁿM^∧` is not merely contained in the kernel of `eval I M n` but equal to
it, which is `AdicCompletion.pow_smul_top_eq_ker_eval` and is where finite generation is used.

The source's `n ≥ 1` is dropped: for `n = 0` one has `I⁰M = M`, both quotients vanish and the
assertion holds, so restricting to `1 ≤ n` would only weaken it. The source's "in particular" is
stated for an arbitrary module `M` rather than for `M = R` alone; at `M = R` it is
`R^∧/IⁿR^∧ ≃ R/Iⁿ` as `R`-modules, and `AdicCompletion.quotMapPowAlgEquiv` (in
`StacksFrontier.RingTheory.AdicCompletion.PowSMulCompletion`) records the ring structure as well, as
an isomorphism of `R`-algebras induced by `AdicCompletion.evalₐ`.

Scope of this file inside the lemma. Part (1), that `M^∧` is `I`-adically complete, is Mathlib's
`AdicCompletion.isAdicComplete`, and the first equality of part (2), `IⁿM^∧ = Ker(M^∧ → M/IⁿM)`,
is `AdicCompletion.pow_smul_top_eq_ker_eval`; both carry the tag upstream. The second equality of
part (2), `Ker(M^∧ → M/IⁿM) = (IⁿM)^∧`, says that the completion `(IⁿM)^∧ → M^∧` of the inclusion
`IⁿM ⊆ M` is injective with image the kernel: these are Mathlib's
`AdicCompletion.ofPowSMul_injective` and
`AdicCompletion.restrictScalars_range_ofPowSMul_eq_ker_eval`, neither of which needs finite
generation; `StacksFrontier.RingTheory.AdicCompletion.PowSMulCompletion` registers them under the
tag and packages them as the isomorphism `AdicCompletion.ofPowSMulEquivKerEval`. That module
also states and registers the concluding "in particular": `R^∧` is `I`-adically complete is
part (1) at `M = R`; `IⁿR^∧ = (Iⁿ)^∧` is
`AdicCompletion.map_pow_eq_range_map_subtype` with `AdicCompletion.map_subtype_pow_injective`,
the ideal `IⁿR^∧` being the ideal `(Iⁿ).map (algebraMap R R^∧)` that `Iⁿ` generates; and
`R^∧/IⁿR^∧ = R/Iⁿ` is `AdicCompletion.quotMapPowAlgEquiv`, an isomorphism of `R`-algebras, and
`AdicCompletion.quotPowSMulTopEquiv` of this file for an arbitrary module `M`.

Faithfulness. (1) Every hypothesis is used: `I`, `M` and `n` all occur in the statement, and
finite generation is not decoration — for `R = k[x₁, x₂, …]`, `M = R` and `I = (x₁, x₂, …)` the
submodule `IR^∧` is strictly smaller than the kernel of `R^∧ → R/I`, so the induced map on
`R^∧/IR^∧` is not injective (Stacks 05JA). (2) The scalars and the base are the source's: `M` is
an `R`-module and both quotients are quotients of `R`-modules by `R`-submodules, `eval` being
`R`-linear; the `R^∧`-module structure on `M^∧` does not enter. (3) The map is the source's, the
one induced by the projection `M^∧ → M/IⁿM`. (4) The instantiation is not degenerate: for `R = ℤ`,
`I = (p)` and `M = ℤ` the completion is the ring `ℤ_p` of `p`-adic integers and the statement is
`ℤ_p/pⁿℤ_p ≃ ℤ/pⁿ`.

## References

* [StackProject 05GG](https://stacks.math.columbia.edu/tag/05GG), which attributes the lemma to
  Matlis, Theorem 15, and the proof sketched above to Bjorn Poonen

## Tags

adic completion, complete, finitely generated ideal
-/

namespace AdicCompletion

/-- **Stacks 05GG**, the content of the concluding "in particular": for a finitely generated ideal
`I` of a ring `R` and an `R`-module `M`, the map that the projection `M^∧ → M/IⁿM` out of the
`I`-adic completion induces on `M^∧/IⁿM^∧` is bijective. -/
public theorem bijective_liftQ_eval {R : Type*} [CommRing R] {I : Ideal R} (hI : I.FG)
    (M : Type*) [AddCommGroup M] [Module R M] (n : ℕ) :
    Function.Bijective
      ((I ^ n • ⊤ : Submodule R (AdicCompletion I M)).liftQ (eval I M n)
        (pow_smul_top_le_ker_eval I n)) := by
  refine ⟨LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _
    (pow_smul_top_eq_ker_eval hI).ge), fun y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := eval_surjective I M n y
  exact ⟨Submodule.Quotient.mk x, rfl⟩

/-- **Stacks 05GG**, the concluding "in particular". Let `R` be a ring, `I` a finitely generated
ideal of `R` and `M` an `R`-module. For every `n` the projection `M^∧ → M/IⁿM` out of the
`I`-adic completion induces an isomorphism `M^∧/IⁿM^∧ ≃ M/IⁿM` of `R`-modules; at `M = R` this is
`R^∧/IⁿR^∧ = R/Iⁿ`. -/
public noncomputable def quotPowSMulTopEquiv {R : Type*} [CommRing R] {I : Ideal R} (hI : I.FG)
    (M : Type*) [AddCommGroup M] [Module R M] (n : ℕ) :
    (AdicCompletion I M ⧸ (I ^ n • ⊤ : Submodule R (AdicCompletion I M))) ≃ₗ[R]
      M ⧸ (I ^ n • ⊤ : Submodule R M) :=
  LinearEquiv.ofBijective _ (bijective_liftQ_eval hI M n)

/-- The isomorphism `quotPowSMulTopEquiv` sends the class of `x ∈ M^∧` in `M^∧/IⁿM^∧` to the
`n`-th component `x.val n ∈ M/IⁿM` of `x`. -/
@[simp]
public theorem quotPowSMulTopEquiv_mk {R : Type*} [CommRing R] {I : Ideal R} (hI : I.FG)
    (M : Type*) [AddCommGroup M] [Module R M] (n : ℕ) (x : AdicCompletion I M) :
    quotPowSMulTopEquiv hI M n (Submodule.Quotient.mk x) = x.val n :=
  rfl

/-- **Stacks 05GG**, the second equality of part (2). For a finitely generated ideal `I` of a ring
`R` and an `R`-module `M`, the submodule `IⁿM^∧` of the `I`-adic completion is the image of
`(IⁿM)^∧` under the completion of the inclusion `IⁿM ⊆ M`. -/
theorem pow_smul_top_eq_restrictScalars_range_ofPowSMul {R : Type*} [CommRing R] {I : Ideal R}
    {M : Type*} [AddCommGroup M] [Module R M] (hI : I.FG) (n : ℕ) :
    (I ^ n • ⊤ : Submodule R (AdicCompletion I M))
      = ((ofPowSMul I M n).range).restrictScalars R :=
  (pow_smul_top_eq_ker_eval hI).trans (restrictScalars_range_ofPowSMul_eq_ker_eval I).symm

end AdicCompletion

end
