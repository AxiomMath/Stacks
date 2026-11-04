module

public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.CuspFormsStructure
public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.HeckeData

/-!
# Algebraicity of the Hecke eigenvalues (Stacks 03VX)

Let `k` be a finite field of characteristic `p`, `K` a function field over `k`, and `Λ` a field
in which `p` is invertible, with prime subfield `F ⊂ Λ` (the bottom subfield `⊥`, which is `𝔽_ℓ`
or `ℚ` according to the characteristic of `Λ`). We prove Stacks Lemma 03VX: the eigenvalues
`t_v` of an eigenform `f ∈ C(Λ)` are algebraic over `F`. The eigenvalues `u_v` are then
`q_v⁻¹ ∈ F`, so they are algebraic as well.

The argument is the one the source indicates, from Proposition 03VW
(`Stacks.Adeles.GlobalFunctionField.cuspFormsCentralChar_fg_and_baseChange`). Since
`C(Λ) = Λ ⊗_F C(F)`, every `f ∈ C(Λ)` is a finite sum `∑ c_i · f_i` with `f_i` taking values in
`F`, so the `F`-span `V ⊆ Λ` of the values of `f` lies in the `F`-span of the finitely many
`c_i` and is finite-dimensional. If `f ≠ 0` and `T_v f = t f`, then `V ≠ 0` and `t · V ⊆ V`,
because `t · f(x) = (T_v f)(x)` is a finite sum of values of `f`. A scalar preserving a nonzero
finitely generated submodule is integral, hence algebraic, over `F`.

## Main results

* `fg_span_range_of_mem_cuspFormsCentralChar`: the values of an element of `C(Λ)` span a
  finite-dimensional `F`-subspace of `Λ`.
* `isAlgebraic_of_mem_cuspFormsCentralChar_of_isHeckeEigenvalueAt`: a `T_v`-eigenvalue of a
  nonzero element of `C(Λ)` is algebraic over `F`.
* `isAlgebraic_eigenvalues_of_isEigenform`: **Lemma 03VX**, the Hecke eigenvalues of an
  eigenform are algebraic over `F`.

## Implementation notes

The eigenvalue equation `Stacks.Adeles.IsHeckeEigenvalueAt v f t` is quantified over the data
of the source's formula for `T_v`. On a function field these data exist at every place
(`Stacks.Adeles.GlobalFunctionField.exists_isHeckeDataAt`), so the equation is never vacuous, and
no hypothesis about the data is needed.

## References

* [Stacks Project, Tag 03VX](https://stacks.math.columbia.edu/tag/03VX)
* [Stacks Project, Tag 03VW](https://stacks.math.columbia.edu/tag/03VW)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u w

namespace Stacks.Adeles.GlobalFunctionField

variable (k : Type u) [Field k] [Finite k] {K : Type u} [Field K] [Algebra k K]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]

include k

variable {Λ : Type w} [Field Λ]

/-- The values of an element `f ∈ C(Λ)` span a finite-dimensional subspace of `Λ` over the
prime subfield `F ⊂ Λ`, when `p` is invertible in `Λ`: by Proposition 03VW, `f` is a finite sum
`∑ c_i · f_i` with each `f_i` taking values in `F`, so the values of `f` lie in the `F`-span of
the `c_i`. -/
public theorem fg_span_range_of_mem_cuspFormsCentralChar (hp : IsUnit (ringChar k : Λ))
    {f : GL (Fin 2) (AdeleRing K) → Λ} (hf : f ∈ cuspFormsCentralChar K Λ) :
    (Submodule.span ↥(⊥ : Subfield Λ) (Set.range f)).FG := by
  obtain ⟨e, he, -⟩ := (cuspFormsCentralChar_fg_and_baseChange.{u, w} k K).2 Λ hp
  have key : ∀ z, ∃ s : Finset Λ, ∀ x,
      ((e z : cuspFormsCentralChar K Λ) : GL (Fin 2) (AdeleRing K) → Λ) x ∈
        Submodule.span ↥(⊥ : Subfield Λ) (s : Set Λ) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero =>
      refine ⟨∅, fun x => ?_⟩
      rw [e.map_zero, Submodule.coe_zero, Pi.zero_apply]
      exact Submodule.zero_mem _
    | tmul c g =>
      refine ⟨{c}, fun x => ?_⟩
      rw [he]
      simp only [Pi.smul_apply, smul_eq_mul, mapCoeffs]
      have hmul : c * algebraMap ↥(⊥ : Subfield Λ) Λ
          ((g : GL (Fin 2) (AdeleRing K) → ↥(⊥ : Subfield Λ)) x) =
          (g : GL (Fin 2) (AdeleRing K) → ↥(⊥ : Subfield Λ)) x • c := by
        rw [Algebra.smul_def, mul_comm]
      rw [hmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    | add z z' hz hz' =>
      classical
      obtain ⟨s, hs⟩ := hz
      obtain ⟨s', hs'⟩ := hz'
      refine ⟨s ∪ s', fun x => ?_⟩
      rw [e.map_add, Submodule.coe_add, Pi.add_apply, Finset.coe_union]
      exact Submodule.add_mem _
        (Submodule.span_mono Set.subset_union_left (hs x))
        (Submodule.span_mono Set.subset_union_right (hs' x))
  obtain ⟨z, hz⟩ := e.surjective ⟨f, hf⟩
  obtain ⟨s, hs⟩ := key z
  rw [hz] at hs
  have hle : Submodule.span ↥(⊥ : Subfield Λ) (Set.range f) ≤
      Submodule.span ↥(⊥ : Subfield Λ) (s : Set Λ) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact hs x
  have : FiniteDimensional ↥(⊥ : Subfield Λ) ↥(Submodule.span ↥(⊥ : Subfield Λ) (s : Set Λ)) :=
    Module.Finite.span_of_finite _ s.finite_toSet
  have := Submodule.finiteDimensional_of_le hle
  exact (Submodule.fg_iff_finiteDimensional _).2 this

/-- A `T_v`-eigenvalue of a nonzero element `f ∈ C(Λ)` is algebraic over the prime subfield
`F ⊂ Λ`, when `p` is invertible in `Λ`. -/
public theorem isAlgebraic_of_mem_cuspFormsCentralChar_of_isHeckeEigenvalueAt
    (hp : IsUnit (ringChar k : Λ)) {f : GL (Fin 2) (AdeleRing K) → Λ}
    (hf : f ∈ cuspFormsCentralChar K Λ) (hf0 : f ≠ 0) {v : Place K} {t : Λ}
    (ht : IsHeckeEigenvalueAt v f t) :
    IsAlgebraic ↥(⊥ : Subfield Λ) t := by
  obtain ⟨π, lam, g₀, g, hdata⟩ := exists_isHeckeDataAt k v
  set V := Submodule.span ↥(⊥ : Subfield Λ) (Set.range f) with hV
  have hfg : V.FG := fg_span_range_of_mem_cuspFormsCentralChar k hp hf
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

/-- A `U_v`-eigenvalue of a nonzero element `f ∈ C(Λ)` is `q_v⁻¹`, which lies in the prime
subfield `F ⊂ Λ`. -/
public theorem mem_bot_of_mem_cuspFormsCentralChar_of_isCentralEigenvalueAt
    {f : GL (Fin 2) (AdeleRing K) → Λ} (hf : f ∈ cuspFormsCentralChar K Λ) (hf0 : f ≠ 0)
    {v : Place K} {u : Λ} (hu : IsCentralEigenvalueAt v f u) :
    u ∈ (⊥ : Subfield Λ) := by
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hf0
  have ha := isCentralDataAt_scalarGL_unifInvIdele k v
  have hq := (cuspFormsCentralChar_le_reducedForms k Λ hf).2.2.1 v _ ha x
  have hc : f (scalarGL (unifInvIdele k v) * x) = u * f x := hu _ ha x
  rw [hc, ← mul_assoc] at hq
  have h1 : (v.residueCard : Λ) * u = 1 :=
    (mul_eq_right₀ hx).1 hq
  rw [eq_inv_of_mul_eq_one_right h1]
  exact Subfield.inv_mem _ (natCast_mem _ _)

/-- **Stacks Project, Tag 03VX.** Algebraicity of eigenvalues. Let `k` be a finite field of
characteristic `p`, `K` a function field over `k` (for instance `K = k(X)` for a geometrically
irreducible smooth projective curve `X` over `k`), and `Λ` a field in which `p` is invertible,
with prime subfield `F ⊂ Λ` (the bottom subfield `⊥`). If `f ∈ C(Λ)` is an eigenform, with
`T_v f = t_v f` and `U_v f = u_v f` at every place `v`, then the eigenvalues `t_v` are algebraic
over `F`; so are the `u_v`, which equal `q_v⁻¹ ∈ F`.

`C(Λ)` is `Stacks.Adeles.cuspFormsCentralChar` and an eigenform is `Stacks.Adeles.IsEigenform`
(an unramified cusp form with a unit value, Tag 03VS). The proof uses Proposition 03VW,
`Stacks.Adeles.GlobalFunctionField.cuspFormsCentralChar_fg_and_baseChange`. -/
@[stacks 03VX]
public theorem isAlgebraic_eigenvalues_of_isEigenform (hp : IsUnit (ringChar k : Λ))
    {f : GL (Fin 2) (AdeleRing K) → Λ} {t u : Place K → Λ} (hf : IsEigenform f t u)
    (hfC : f ∈ cuspFormsCentralChar K Λ) (v : Place K) :
    IsAlgebraic ↥(⊥ : Subfield Λ) (t v) ∧ IsAlgebraic ↥(⊥ : Subfield Λ) (u v) := by
  obtain ⟨x, hx⟩ := hf.exists_isUnit
  have hf0 : f ≠ 0 := fun h => hx.ne_zero (congrFun h x)
  refine ⟨isAlgebraic_of_mem_cuspFormsCentralChar_of_isHeckeEigenvalueAt k hp hfC hf0
    (hf.hecke v), ?_⟩
  have hu := mem_bot_of_mem_cuspFormsCentralChar_of_isCentralEigenvalueAt k hfC hf0 (hf.central v)
  exact isAlgebraic_algebraMap (⟨u v, hu⟩ : ↥(⊥ : Subfield Λ))

end Stacks.Adeles.GlobalFunctionField

end
