module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import StacksFrontier.NumberTheory.Adeles.SwitchingEll

/-!
# Algebraicity of the Hecke eigenvalues

Let `K` be a field and let the coefficients `Λ` be a field, with prime subfield `F ⊂ Λ`: the
bottom subfield `⊥`, which is `𝔽_p` or `ℚ` according to the characteristic of `Λ`. If `f` is a
nonzero element of `C(Λ)` and `T_v f = t f` at a place `v`, then `t` is algebraic over `F`.

The argument is the one the source indicates. Proposition 03VW gives `C(Λ) = C(F) ⊗_F Λ`, so
the values of `f` all lie in the `F`-span of the finitely many coordinates `c_1, …, c_n ∈ Λ` of
`f` in a `Λ`-basis of `C(Λ)` coming from `C(F)`. Hence the `F`-span `V ⊆ Λ` of the values of
`f` is nonzero and finite-dimensional over `F`. It satisfies `t · V ⊆ V`, because `t · f(x)` is
the value at `x` of `T_v f`, which is a finite sum of values of `f`; and a scalar preserving a
nonzero finitely generated submodule is integral over the base, hence algebraic.

## Main results

* `Stacks.Adeles.isAlgebraic_of_isHeckeEigenvalueAt` — a Hecke eigenvalue of a nonzero element
  of `C(Λ)` is algebraic over the prime subfield of `Λ`.
* `Stacks.Adeles.IsEigenform.isAlgebraic_heckeEigenvalue` — the same statement for the
  eigenvalues `t_v` of an eigenform `f ∈ C(Λ)`. Lemma 03VX itself is
  `Stacks.Adeles.GlobalFunctionField.isAlgebraic_eigenvalues_of_isEigenform`, proved
  unconditionally for a function field over a finite field.

## Implementation notes

**Proposition 03VW is carried as a hypothesis.** This file works over an arbitrary field `K`,
where Proposition 03VW is not available, so it is carried as the hypothesis
`Stacks.Adeles.CuspFormsFinite` of `StacksFrontier.NumberTheory.Adeles.SwitchingEll`. For a function
field over a finite field, the source's setting, 03VW is proved as
`Stacks.Adeles.GlobalFunctionField.cuspFormsCentralChar_fg_and_baseChange`, and Lemma 03VX is
proved unconditionally in
`StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.AlgebraicEigenvalues`. Only the
base-change clause of `CuspFormsFinite` is used. The prime subfield of `Λ` is the bottom
subfield `⊥`, as in `CuspFormsFinite`.

**Hecke data at `v`.** `Stacks.Adeles.IsHeckeEigenvalueAt v f t` quantifies over the data of
the source's explicit formula for `T_v` — a uniformizer, a system of representatives of `κ_v`,
and the adelic matrices built from them — so it holds vacuously at a place carrying no such
data, where `t` is then unconstrained. The existence of the data at `v` is therefore a
hypothesis, exactly as it is for the uniqueness of the eigenvalues in
`Stacks.Adeles.IsEigenform.hecke_eigenvalue_unique`. In the source's situation the places have
finite residue fields and the data always exists.

**Nonvanishing.** `Stacks.Adeles.isAlgebraic_of_isHeckeEigenvalueAt` asks only that `f ≠ 0`,
which is weaker than the source's hypothesis that `f` is an eigenform: an eigenform takes a
unit value. Without some such hypothesis the statement is false, since every `t` is a Hecke
eigenvalue of `f = 0`.

## References

* [Stacks Project, Tag 03VX](https://stacks.math.columbia.edu/tag/03VX)
* [Stacks Project, Tag 03VW](https://stacks.math.columbia.edu/tag/03VW)
-/

@[expose] public noncomputable section

open Matrix

universe u w

namespace Stacks.Adeles

/-- The values of an element `f` of `C(Λ)` span a finite-dimensional subspace of `Λ` over the
prime subfield `F ⊂ Λ`: by Proposition 03VW the module `C(Λ)` has a basis coming from `C(F)`,
and the values of `f` lie in the `F`-span of its finitely many coordinates in that basis. -/
public theorem finiteDimensional_span_range_of_mem_cuspFormsCentralChar {K : Type u} [Field K]
    {Λ : Type w} [Field Λ] (hVW : CuspFormsFinite.{u, w} K)
    {f : GL (Fin 2) (AdeleRing K) → Λ} (hf : f ∈ cuspFormsCentralChar K Λ) :
    FiniteDimensional ↥(⊥ : Subfield Λ) ↥(Submodule.span ↥(⊥ : Subfield Λ) (Set.range f)) := by
  obtain ⟨n, b, -, -, hspan, -⟩ := hVW.baseChange Λ
  rw [← hspan] at hf
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Λ).1 hf
  have hvals : ∀ x, f x ∈ Submodule.span ↥(⊥ : Subfield Λ) (Set.range c) := by
    intro x
    rw [← hc]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mapCoeffs]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hmul : c i * algebraMap ↥(⊥ : Subfield Λ) Λ (b i x) = b i x • c i := by
      rw [Algebra.smul_def, mul_comm]
    rw [hmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hle : Submodule.span ↥(⊥ : Subfield Λ) (Set.range f) ≤
      Submodule.span ↥(⊥ : Subfield Λ) (Set.range c) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact hvals x
  have hc' : FiniteDimensional ↥(⊥ : Subfield Λ)
      ↥(Submodule.span ↥(⊥ : Subfield Λ) (Set.range c)) :=
    Module.Finite.span_of_finite _ (Set.finite_range c)
  exact FiniteDimensional.of_injective (Submodule.inclusion hle)
    (Submodule.inclusion_injective hle)

/-- A Hecke eigenvalue of a nonzero element of `C(Λ)` is algebraic over the prime subfield of
the field `Λ`. The hypothesis `hVW` is Proposition 03VW and `hdata` is the data of the source's
formula for `T_v`, without which the eigenvalue equation is vacuous; see the implementation
notes of `StacksFrontier.NumberTheory.Adeles.AlgebraicEigenvalues`. -/
public theorem isAlgebraic_of_isHeckeEigenvalueAt {K : Type u} [Field K] {Λ : Type w} [Field Λ]
    (hVW : CuspFormsFinite.{u, w} K) {f : GL (Fin 2) (AdeleRing K) → Λ}
    (hf : f ∈ cuspFormsCentralChar K Λ) (hf0 : f ≠ 0) {v : Place K} {t : Λ}
    (ht : IsHeckeEigenvalueAt v f t) {q : ℕ} {π : v.integers} {lam : Fin q → v.integers}
    {g₀ : GL (Fin 2) (AdeleRing K)} {g : Fin q → GL (Fin 2) (AdeleRing K)}
    (hdata : IsHeckeDataAt v π lam g₀ g) :
    IsAlgebraic ↥(⊥ : Subfield Λ) t := by
  set V := Submodule.span ↥(⊥ : Subfield Λ) (Set.range f) with hV
  have hfin : FiniteDimensional ↥(⊥ : Subfield Λ) ↥V :=
    finiteDimensional_span_range_of_mem_cuspFormsCentralChar hVW hf
  have hfg : V.FG := (Submodule.fg_iff_finiteDimensional V).2 hfin
  have hne : V ≠ ⊥ := by
    obtain ⟨x, hx⟩ := Function.ne_iff.1 hf0
    intro hbot
    have hmem : f x ∈ V := Submodule.subset_span ⟨x, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact hx hmem
  have hmul : ∀ z ∈ V, t * z ∈ V := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨y, rfl⟩ := hz
      rw [← ht π lam g₀ g hdata y]
      exact V.add_mem (Submodule.subset_span ⟨_, rfl⟩)
        (Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨_, rfl⟩)
    | zero => simp
    | add z z' _ _ hz hz' => rw [mul_add]; exact V.add_mem hz hz'
    | smul a z _ hz =>
      have hcomm : t * (a • z) = a • (t * z) := by
        simp only [Algebra.smul_def]
        ring
      rw [hcomm]
      exact V.smul_mem a hz
  exact (isIntegral_of_smul_mem_submodule V hne hfg t
    fun z hz => by simpa only [smul_eq_mul] using hmul z hz).isAlgebraic

/-- Algebraicity of eigenvalues over a general field `K`, from the hypothesis `hVW`: if `Λ`
is a field then the eigenvalues `t_v` of an eigenform `f ∈ C(Λ)` are algebraic over the prime
subfield `F ⊂ Λ`, the subfield `⊥`, which is `𝔽_p` or `ℚ` according to the characteristic of
`Λ`.

The base-change clause of Proposition 03VW is the hypothesis `hVW`, and `hdata` is the data of
the source's formula for `T_v` at `v`, without which the eigenvalue equation is vacuous; see the
implementation notes of `StacksFrontier.NumberTheory.Adeles.AlgebraicEigenvalues`. Stacks Lemma
03VX itself, in the source's setting of a function field over a finite field, is proved
unconditionally as
`Stacks.Adeles.GlobalFunctionField.isAlgebraic_eigenvalues_of_isEigenform`. -/
public theorem IsEigenform.isAlgebraic_heckeEigenvalue {K : Type u} [Field K] {Λ : Type w}
    [Field Λ] (hVW : CuspFormsFinite.{u, w} K) {f : GL (Fin 2) (AdeleRing K) → Λ}
    {t u : Place K → Λ} (hf : IsEigenform f t u) (hfC : f ∈ cuspFormsCentralChar K Λ)
    {v : Place K} {q : ℕ} {π : v.integers} {lam : Fin q → v.integers}
    {g₀ : GL (Fin 2) (AdeleRing K)} {g : Fin q → GL (Fin 2) (AdeleRing K)}
    (hdata : IsHeckeDataAt v π lam g₀ g) :
    IsAlgebraic ↥(⊥ : Subfield Λ) (t v) := by
  obtain ⟨x, hx⟩ := hf.exists_isUnit
  exact isAlgebraic_of_isHeckeEigenvalueAt hVW hfC (fun h => hx.ne_zero (congrFun h x))
    (hf.hecke v) hdata

end Stacks.Adeles

end
