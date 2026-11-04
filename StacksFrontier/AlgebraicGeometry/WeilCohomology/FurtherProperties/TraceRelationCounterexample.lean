module

public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Tag 0FHT is false without a common section

Tag 0FHT reads: let `F` be a field of characteristic `0`, let `F'` and `F i`, `i = 1, …, r`, be
finite separable `F`-algebras, let `A` be a finite `F`-algebra, and let `σ, σ' : A → F'` and
`σ i : A → F i` be `F`-algebra maps with `σ` and `σ'` surjective. If

```
Tr_{F'/F} ∘ σ - Tr_{F'/F} ∘ σ' = n (∑ m i * Tr_{F i/F} ∘ σ i)
```

with `n > 1` and `m i` integers, then `σ = σ'`.

That statement is **false**. `Stacks.WeilCohomology.traceRelationStatement` is it, written out
with no hypothesis added and no conclusion dropped, and
`Stacks.WeilCohomology.not_traceRelationStatement` refutes it.

## The counterexample

Take `F = ℝ`, `F' = A = ℂ`, `σ = id` and `σ' = ` complex conjugation. Then `ℂ` is a finite
separable field extension of a field of characteristic `0`, both maps are surjective
`ℝ`-algebra maps, and `Tr_{ℂ/ℝ}(z) = z + conj z` is conjugation-invariant
(`Algebra.trace_eq_of_algEquiv`), so the left-hand side of the relation vanishes identically. The
relation therefore holds with `n = 2`, and, to leave nothing degenerate, with `r = 2`,
`F 1 = F 2 = ℂ`, `σ 1 = id`, `σ 2 = ` conjugation and `m = (1, -1)`: the right-hand side is
`2 • (Tr ∘ id - Tr ∘ conj) = 0` as well. But `σ ≠ σ'`, since conjugation moves `i`.

## Where the source proof breaks

The source reduces to `F` algebraically closed, where `A`, `F'` and the `F i` are products of
copies of `F`, and then asserts: if `σ ≠ σ'` one can choose a minimal idempotent `e ∈ A` with
`σ(e) = 0` and `σ'(e) ≠ 0`, or the other way round. That step is the gap. Writing
`A = ∏_{j ∈ J} F` and `F' = ∏_{l ∈ L} F`, a surjection `σ : A → F'` is a *injective* map
`f : L → J` (with `σ(x) l = x (f l)`), and `σ(e j) = 0` exactly when `j ∉ f '' L`. So the
idempotent the proof asks for exists only when `f` and `f'` have different images, whereas
`σ ≠ σ'` only gives `f ≠ f'`: two surjections differing by an automorphism of `F'` — which is
what conjugation is in the example above, after base change to `ℂ`, where `σ` and `σ'` become
the identity and the swap of `ℂ ⊗_ℝ ℂ ≅ ℂ × ℂ` — have the same image and are not separated by
any idempotent, nor indeed by the trace relation, which cannot see an automorphism at all.

What the hypotheses do force is that `σ' = θ ∘ σ` for an `F`-algebra automorphism `θ` of `F'`:
in the notation above the multiplicity of a character of `A` in either sum is `0` or `1` by
surjectivity, the two multiplicities are congruent mod `n`, and `n > 1`, so the two maps meet
the same characters of `A`, have the same kernel, and therefore differ by an automorphism of
`F'`; equivalently `Tr_{F'/F} ∘ σ` and `Tr_{F'/F} ∘ σ'` agree. That is the corrected statement
recorded as a Stacks erratum, proved as
`AlgHom.exists_algEquiv_comp_eq_of_trace_sub_trace_eq_zsmul` in
`StacksFrontier.AlgebraicGeometry.WeilCohomology.FurtherProperties.Basic`, which carries the
registration of Tag 0FHT.

Pinning down `σ` itself needs an input that breaks the symmetry; in the one place the chapter
uses 0FHT (Tag 0FHU, Lemma 45.10.6) the input available is a common section, the pullback along
`H^0(Spec k') → H^0(X)`, whose composites with both `σ` and `σ'` are the identity and which
therefore forces `θ` to be the identity. That version is
`AlgHom.eq_of_trace_sub_trace_eq_zsmul` in the same module, and it is enough for
Tag 0FHU; the counterexample here has no common section, as any `τ` with
`id ∘ τ = conj ∘ τ = id` would force `id = conj`.

## References

* [Stacks Project, Tag 0FHT](https://stacks.math.columbia.edu/tag/0FHT)
-/

@[expose] public section

universe u v w x

namespace Stacks.WeilCohomology

/-- The statement of Stacks Tag 0FHT, verbatim: over a field `F` of characteristic zero, two
surjections `σ, σ'` from a finite `F`-algebra `A` onto a finite separable `F`-algebra `F'` whose
trace forms differ by `n > 1` times an integral combination of trace forms of maps to finite
separable `F`-algebras are equal.

This Prop is refuted by `Stacks.WeilCohomology.not_traceRelationStatement`. -/
def traceRelationStatement : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F]
    (F' : Type v) [CommRing F'] [Algebra F F'] [FiniteDimensional F F']
    [Algebra.IsSeparable F F']
    (A : Type w) [CommRing A] [Algebra F A] [FiniteDimensional F A]
    (r : ℕ) (F_i : Fin r → Type x) [∀ i, CommRing (F_i i)] [∀ i, Algebra F (F_i i)]
    [∀ i, FiniteDimensional F (F_i i)] [∀ i, Algebra.IsSeparable F (F_i i)]
    (σ σ' : A →ₐ[F] F') (σ_i : ∀ i, A →ₐ[F] F_i i),
    Function.Surjective σ → Function.Surjective σ' →
    ∀ n : ℤ, 1 < n → ∀ m : Fin r → ℤ,
      (Algebra.trace F F').comp σ.toLinearMap - (Algebra.trace F F').comp σ'.toLinearMap =
        n • ∑ i, m i • (Algebra.trace F (F_i i)).comp (σ_i i).toLinearMap →
      σ = σ'

/-- **Stacks Tag 0FHT is false.** The identity and complex conjugation are two distinct
surjective `ℝ`-algebra maps `ℂ → ℂ` with the same trace form, so they satisfy the relation of
Tag 0FHT with `n = 2`, `r = 2`, `m = (1, -1)`, `σ 1 = id` and `σ 2 = ` conjugation, while
`σ ≠ σ'`.

Refuting the statement for types in `Type 0` refutes it in every universe, since the
universe-polymorphic statement specializes to this one. -/
theorem not_traceRelationStatement : ¬ traceRelationStatement.{0, 0, 0, 0} := by
  intro h
  have key : AlgHom.id ℝ ℂ = Complex.conjAe.toAlgHom := by
    refine @h ℝ _ _ ℂ _ _ _ _ ℂ _ _ _ 2 (fun _ => ℂ) (fun _ => inferInstance)
      (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => inferInstance)
      (AlgHom.id ℝ ℂ) Complex.conjAe.toAlgHom
      ![AlgHom.id ℝ ℂ, Complex.conjAe.toAlgHom]
      Function.surjective_id Complex.conjAe.surjective 2 (by norm_num) ![1, -1] ?_
    ext z
    simp [Fin.sum_univ_two, show Algebra.trace ℝ ℂ ((starRingEnd ℂ) z) = Algebra.trace ℝ ℂ z from
      Algebra.trace_eq_of_algEquiv Complex.conjAe z]
  have hI : Complex.I = (starRingEnd ℂ) Complex.I := AlgHom.congr_fun key Complex.I
  rw [Complex.conj_I] at hI
  exact Complex.I_ne_zero (by linear_combination hI / 2)

end Stacks.WeilCohomology
