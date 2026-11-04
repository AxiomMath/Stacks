module

public import StacksFrontier.RingTheory.FormsTrace.AnyFrame
public import StacksFrontier.RingTheory.FormsTrace.MonogenicFrame
public import StacksFrontier.RingTheory.FormsTrace.DegreeOne
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.TraceMapPositive.AbsoluteFormsComparison

/-!
# Trace maps on forms of monogenic algebras

Let `A` be a ring, `f ∈ A[x]` a monic polynomial and `B = A[x]/(f)`, with `t ∈ B` the image of
`x`. The algebra `B` is finite free with the power basis `1, t, …, t^{d - 1}`, and this file
studies the trace maps `Θ_{B/A} : Ω^•_B → Ω^•_A` (`Stacks.FormsTrace.frameTrace`) on the one-forms
`t^i dt`.

* A power basis of positive rank is a frame (`Stacks.FormsTrace.powerBasisFrame`): its first
  vector is `1` and the monogenicity element of the universal ring maps to `1`. So `B` is framed
  or zero, and `Θ_{B/A}` has properties (1) of Lemma 0FLB and (2) of Proposition 0FLC and commutes
  with `d`.
* Since `Θ` commutes with `d` and is the trace in degree zero, `Θ(db) = d Trace_{B/A}(b)`
  (`Stacks.FormsTrace.frameTrace_oneForm_D`). As `d(t^{i+1}) = (i + 1) t^i dt`, this gives
  `(i + 1) Θ(t^i dt) = d Trace_{B/A}(t^{i+1})`
  (`Stacks.FormsTrace.frameTrace_root_pow_smul_oneForm_D`).
* The traces of small powers of `t` in terms of the coefficients of `f`
  (`Stacks.FormsTrace.trace_root`, `trace_root_sq`, `trace_root_cube`) and for `f = x^d - a`
  (`Stacks.FormsTrace.trace_root_pow_X_pow_sub_C`), read off the coordinates of `t^n` in the power
  basis through the recurrence of multiplication by `t`.
* `B` commutes with base change, `A' ⊗_A A[x]/(f) = A'[x]/(f)`
  (`Stacks.FormsTrace.isPushout_adjoinRoot_map`), so `Θ(t^i dt)` is the pull-back of its value
  for any polynomial `f₀` over a ring `A₀` with `f₀ ↦ f`
  (`Stacks.FormsTrace.frameTrace_root_pow_smul_oneForm_D_map`). Over `A₀ = ℤ[x_a : a ∈ A]` the
  one-forms are torsion free (`Stacks.FormsTrace.eq_of_nsmul_eq_nsmul_oneForm`), so there the
  relation `(i + 1) Θ(t^i dt) = d Trace(t^{i+1})` determines `Θ(t^i dt)`.

These are the steps of the computations of Stacks, Example 0FLD, which are assembled in
`StacksFrontier.RingTheory.FormsTrace.MonogenicExample`.

## References

* [Stacks Project, Tag 0FLD](https://stacks.math.columbia.edu/tag/0FLD)
* [Stacks Project, Tag 0FLC](https://stacks.math.columbia.edu/tag/0FLC)
-/

@[expose] public noncomputable section

open Polynomial KaehlerDifferential

universe u

namespace Stacks.FormsTrace

section Frame

open _root_.Stacks.AlgebraicGeometry AlgebraicGeometry.FiniteFreeAlgebra

variable {d : ℕ} [NeZero d] {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- On a power basis of any positive dimension `d` the classifying map sends the monogenicity
element `g_mono` to `1`. -/
theorem classify_monogenicGood_powerBasisFin (pb : PowerBasis A B) (hd : pb.dim = d) :
    (ofBasis (powerBasisFin pb hd) (powerBasisFin_zero pb hd)).classify (monogenicGood d) = 1 := by
  rcases Nat.lt_or_ge 1 d with h2 | h1
  · exact classify_monogenicGood_powerBasis pb hd h2
  · obtain rfl : d = 1 := le_antisymm h1 (Nat.pos_of_ne_zero (NeZero.ne d))
    rw [classify_monogenicGood, monoDet_ofBasis, Matrix.det_unique, Matrix.of_apply]
    have h0 : powerBasisFin pb hd 1 ^ ((default : Fin 1) : ℕ) = powerBasisFin pb hd default := by
      rw [Fin.default_eq_zero, Fin.val_zero, pow_zero, powerBasisFin_zero]
    rw [h0, Module.Basis.repr_self, Finsupp.single_eq_same]

/-- **The power-basis frame** of an algebra with a power basis of positive dimension `d`: the power
basis `1, t, …, t^{d - 1}`, with the syntomic-good element `g_mono`, whose classifying image is
`1`. -/
def powerBasisFrame (pb : PowerBasis A B) (hd : pb.dim = d) : ChartFrame d A B where
  basis := powerBasisFin pb hd
  basis_zero := powerBasisFin_zero pb hd
  g := monogenicGood d
  good := isSyntomicGood_monogenicGood
  isUnit := by rw [classify_monogenicGood_powerBasisFin pb hd]; exact isUnit_one

omit [NeZero d] in
/-- **An algebra with a power basis is framed or zero**: zero if the power basis is empty, framed
by `powerBasisFrame` otherwise. -/
theorem subsingleton_or_nonempty_anyFrame_of_powerBasis (pb : PowerBasis A B) :
    Subsingleton B ∨ Nonempty (AnyFrame A B) := by
  rcases Nat.eq_zero_or_pos pb.dim with h | h
  · left
    have : IsEmpty (Fin pb.dim) := by rw [h]; infer_instance
    exact ⟨fun x y => pb.basis.repr.injective (Finsupp.ext fun i => isEmptyElim i)⟩
  · right
    have : NeZero pb.dim := ⟨h.ne'⟩
    exact ⟨⟨pb.dim, powerBasisFrame pb rfl⟩⟩

end Frame

section DegreeOne

/-- In degree one, `ιMulti` of a single vector is `oneForm` of it. -/
theorem ιMulti_one_eq_oneForm (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
    (v : Fin 1 → M) : exteriorPower.ιMulti R 1 v = oneForm R M (v 0) := by
  refine Subtype.ext ?_
  simp [ExteriorAlgebra.ιMulti_apply]

/-- Every form of degree one is `oneForm` of a vector. -/
theorem range_oneForm (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] :
    LinearMap.range (oneForm R M) = ⊤ := by
  rw [eq_top_iff, ← exteriorPower.ιMulti_span, Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  exact ⟨v 0, (ιMulti_one_eq_oneForm R M v).symm⟩

/-- The de Rham differential of a function `r`, a form of degree zero, is the one-form `dr`. -/
theorem deRhamDifferential_zero_smul (R : Type*) [CommRing R] (r : R) :
    deRhamDifferential (A := ℤ) 0 (r • exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → Ω[R⁄ℤ])) =
      oneForm R Ω[R⁄ℤ] (D ℤ R r) := by
  have h := deRhamDifferential_smul_ιMulti_D (A := ℤ) (B := R) 0 (fun _ => r)
  rw [ιMulti_one_eq_oneForm] at h
  rw [show (Fin.elim0 : Fin 0 → Ω[R⁄ℤ]) = fun i => D ℤ R ((fun _ : Fin 1 => r) i.succ) from
    funext fun i => i.elim0]
  exact h

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- **`Θ(db) = d Trace_{B/A}(b)`.** For an algebra which is framed or zero, the trace map on
one-forms sends `db` to `d Trace_{B/A}(b)`: `Θ` commutes with `d`, and in degree zero it is the
trace. -/
theorem frameTrace_oneForm_D [Module.Finite A B] [Module.Projective A B]
    (hB : Subsingleton B ∨ Nonempty (AnyFrame A B)) (b : B) :
    frameTrace A B 1 (oneForm B Ω[B⁄ℤ] (D ℤ B b)) =
      oneForm A Ω[A⁄ℤ] (D ℤ A (trace A B b)) := by
  have hT := isFormsTrace_frameTrace hB 0 b (exteriorPower.ιMulti A 0 Fin.elim0)
  have hD := commutesWithD_frameTrace hB 0 (b • exteriorPower.ιMulti B 0 Fin.elim0)
  have hpull : formsMap A B 0 (exteriorPower.ιMulti A 0 Fin.elim0) =
      exteriorPower.ιMulti B 0 Fin.elim0 := by
    rw [formsMap_ιMulti]
    congr 1
    funext i
    exact i.elim0
  rw [hpull] at hT
  rw [deRhamDifferential_zero_smul, hT, deRhamDifferential_zero_smul] at hD
  exact hD

end DegreeOne

section Trace

/-- On a finite free algebra the trace of Discriminants, Section 0BVH, is `Algebra.trace`. -/
private theorem trace_eq_algebra_trace {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Module.Free R S] : trace R S = Algebra.trace R S := by
  unfold trace
  rw [Stacks.Discriminant.finiteProjectiveTrace_eq_trace]
  rfl

/-- A polynomial of degree below `deg f` that is congruent to `p` modulo a monic `f` is `p %ₘ f`. -/
private theorem modByMonic_eq_of_degree_lt_of_dvd_sub {R : Type*} [CommRing R] [Nontrivial R]
    {p q f : R[X]} (hf : f.Monic) (hq : degree q < degree f) (h : f ∣ p - q) : p %ₘ f = q := by
  rw [modByMonic_eq_of_dvd_sub hf h, (modByMonic_eq_self_iff hf).mpr hq]

variable {A : Type u} [CommRing A] {f : A[X]} (hf : f.Monic)

include hf in
/-- On a finite free algebra the trace of Discriminants, Section 0BVH, is `Algebra.trace`. -/
theorem trace_adjoinRoot_eq :
    haveI := hf.finite_adjoinRoot
    haveI := hf.free_adjoinRoot
    trace A (AdjoinRoot f) = Algebra.trace A (AdjoinRoot f) := by
  have := hf.finite_adjoinRoot
  have := hf.free_adjoinRoot
  exact trace_eq_algebra_trace

/-- **The trace on `A[x]/(f)` in coordinates**: `Trace(y)` is the sum over `j < deg f` of the
`j`-th coordinate of `y t^j` in the power basis `1, t, …, t^{deg f - 1}`. -/
theorem trace_adjoinRoot_eq_sum (y : AdjoinRoot f) :
    Algebra.trace A (AdjoinRoot f) y = ∑ j ∈ Finset.range f.natDegree,
      (AdjoinRoot.modByMonicHom hf (y * AdjoinRoot.root f ^ j)).coeff j := by
  classical
  rw [Algebra.trace_eq_matrix_trace (AdjoinRoot.powerBasis' hf).basis, Matrix.trace]
  simp only [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul]
  refine (Finset.sum_congr rfl fun j _ => ?_).trans (Fin.sum_univ_eq_sum_range
    (fun j => (AdjoinRoot.modByMonicHom hf (y * AdjoinRoot.root f ^ j)).coeff j) f.natDegree)
  have hj := (AdjoinRoot.powerBasis' hf).basis_eq_pow j
  rw [AdjoinRoot.powerBasis'_gen] at hj
  rw [hj]
  rfl

/-- The coordinates of `t^m` for `m < deg f`: the `m`-th basis vector. -/
theorem coeff_modByMonicHom_root_pow_of_lt {m : ℕ} (hm : m < f.natDegree) (l : ℕ) :
    (AdjoinRoot.modByMonicHom hf (AdjoinRoot.root f ^ m)).coeff l = if l = m then 1 else 0 := by
  nontriviality A
  rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.modByMonicHom_mk,
    (modByMonic_eq_self_iff hf).mpr, coeff_X_pow]
  rw [degree_X_pow, degree_eq_natDegree hf.ne_zero]
  exact_mod_cast hm

/-- The coordinates of `t^{deg f}`: `t^d = -∑_{l < d} f_l t^l`. -/
theorem coeff_modByMonicHom_root_pow_natDegree {l : ℕ} (hl : l < f.natDegree) :
    (AdjoinRoot.modByMonicHom hf (AdjoinRoot.root f ^ f.natDegree)).coeff l = -f.coeff l := by
  nontriviality A
  have hdeg : degree (Polynomial.X ^ f.natDegree - f) < degree f := by
    rw [degree_eq_natDegree hf.ne_zero, degree_lt_iff_coeff_zero]
    intro m hm
    rw [coeff_sub, coeff_X_pow]
    rcases hm.lt_or_eq with hm | rfl
    · rw [ite_eq_right hm.ne', coeff_eq_zero_of_natDegree_lt hm, sub_zero]
    · rw [ite_eq_left rfl, hf.coeff_natDegree, sub_self]
  rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.modByMonicHom_mk,
    modByMonic_eq_of_degree_lt_of_dvd_sub hf hdeg (by rw [sub_sub_cancel]), coeff_sub, coeff_X_pow,
    ite_eq_right hl.ne, zero_sub]

/-- **Multiplication by `t` in coordinates**, away from the constant term: the `(l + 1)`-st
coordinate of `t y` is `y_l - f_{l + 1} y_{d - 1}`. -/
theorem coeff_modByMonicHom_root_mul (hd : 0 < f.natDegree) (y : AdjoinRoot f) (l : ℕ) :
    (AdjoinRoot.modByMonicHom hf (AdjoinRoot.root f * y)).coeff (l + 1) =
      (AdjoinRoot.modByMonicHom hf y).coeff l -
        f.coeff (l + 1) * (AdjoinRoot.modByMonicHom hf y).coeff (f.natDegree - 1) := by
  nontriviality A
  obtain ⟨g₁, rfl⟩ := AdjoinRoot.mk_surjective y
  rw [AdjoinRoot.modByMonicHom_mk]
  set g := g₁ %ₘ f with hg
  have hy : AdjoinRoot.mk f g = AdjoinRoot.mk f g₁ := by
    have := AdjoinRoot.mk_leftInverse hf (AdjoinRoot.mk f g₁)
    rwa [AdjoinRoot.modByMonicHom_mk] at this
  have hgdeg : degree g < f.natDegree := by
    rw [← degree_eq_natDegree hf.ne_zero]
    exact degree_modByMonic_lt _ hf
  set c := g.coeff (f.natDegree - 1)
  have hdeg : degree (Polynomial.X * g - C c * f) < degree f := by
    rw [degree_eq_natDegree hf.ne_zero, degree_lt_iff_coeff_zero]
    intro m hm
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [coeff_sub, coeff_X_mul, coeff_C_mul]
    rcases hm.lt_or_eq with hm | hm
    · rw [coeff_eq_zero_of_natDegree_lt hm, mul_zero, sub_zero]
      exact (degree_lt_iff_coeff_zero g _).mp hgdeg m (by omega)
    · rw [← hm, hf.coeff_natDegree, mul_one, show m = f.natDegree - 1 by omega, sub_self]
  rw [← hy, ← AdjoinRoot.mk_X, ← map_mul, AdjoinRoot.modByMonicHom_mk,
    modByMonic_eq_of_degree_lt_of_dvd_sub hf hdeg (by rw [sub_sub_cancel]; exact dvd_mul_left _ _),
    coeff_sub, coeff_X_mul, coeff_C_mul]
  ring

/-- The coordinates of `t^m` for `m = deg f`, as `coeff_modByMonicHom_root_pow_natDegree`. -/
private theorem coeff_modByMonicHom_root_pow_of_natDegree_eq {m l : ℕ} (hdeg : f.natDegree = m)
    (hl : l < m) : (AdjoinRoot.modByMonicHom hf (AdjoinRoot.root f ^ m)).coeff l = -f.coeff l := by
  subst hdeg
  exact coeff_modByMonicHom_root_pow_natDegree hf hl

/-- The terms below the top of the trace sum of `t^k` vanish: the coordinates of `t^{j + k}`
at `j` for `j + k < deg f`, `k > 0`. -/
theorem coeff_modByMonicHom_root_pow_add {j k : ℕ} (hk : 0 < k) (hjk : j + k < f.natDegree) :
    (AdjoinRoot.modByMonicHom hf (AdjoinRoot.root f ^ k * AdjoinRoot.root f ^ j)).coeff j = 0 := by
  rw [← pow_add, coeff_modByMonicHom_root_pow_of_lt hf (by omega), ite_eq_right (by omega)]

include hf in
/-- **`Trace(t) = -a₁`** for `f = x^{n+1} + a₁ x^n + ⋯`. -/
theorem trace_root {n : ℕ} (hdeg : f.natDegree = n + 1) :
    Algebra.trace A (AdjoinRoot f) (AdjoinRoot.root f) = -f.coeff n := by
  rw [trace_adjoinRoot_eq_sum hf, hdeg, Finset.sum_range_succ, Finset.sum_eq_zero, zero_add]
  · rw [← pow_succ', ← hdeg, coeff_modByMonicHom_root_pow_natDegree hf (by omega)]
  · intro j hj
    rw [Finset.mem_range] at hj
    rw [← pow_succ', coeff_modByMonicHom_root_pow_of_lt hf (by omega), ite_eq_right (by omega)]

include hf in
/-- **`Trace(t²) = a₁² - 2a₂`** for `f = x^{n+2} + a₁ x^{n+1} + a₂ x^n + ⋯`. -/
theorem trace_root_sq {n : ℕ} (hdeg : f.natDegree = n + 2) :
    Algebra.trace A (AdjoinRoot f) (AdjoinRoot.root f ^ 2) =
      f.coeff (n + 1) ^ 2 - 2 * f.coeff n := by
  have hd : 0 < f.natDegree := by omega
  have h₃ : (AdjoinRoot.modByMonicHom hf (AdjoinRoot.root f ^ (n + 3))).coeff (n + 1) =
      -f.coeff n + f.coeff (n + 1) ^ 2 := by
    rw [pow_succ', coeff_modByMonicHom_root_mul hf hd, hdeg, show n + 2 - 1 = n + 1 by omega,
      coeff_modByMonicHom_root_pow_of_natDegree_eq hf hdeg (by omega),
      coeff_modByMonicHom_root_pow_of_natDegree_eq hf hdeg (by omega)]
    ring
  rw [trace_adjoinRoot_eq_sum hf, hdeg, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_eq_zero, zero_add, ← pow_add, ← pow_add, show 2 + n = n + 2 by omega,
    show 2 + (n + 1) = n + 3 by omega,
    coeff_modByMonicHom_root_pow_of_natDegree_eq hf hdeg (by omega), h₃]
  · ring
  · intro j hj
    rw [Finset.mem_range] at hj
    exact coeff_modByMonicHom_root_pow_add hf two_pos (by omega)

include hf in
/-- **`Trace(t³) = -a₁³ + 3a₁a₂ - 3a₃`** for
`f = x^{n+3} + a₁ x^{n+2} + a₂ x^{n+1} + a₃ x^n + ⋯`. -/
theorem trace_root_cube {n : ℕ} (hdeg : f.natDegree = n + 3) :
    Algebra.trace A (AdjoinRoot f) (AdjoinRoot.root f ^ 3) =
      -f.coeff (n + 2) ^ 3 + 3 * f.coeff (n + 2) * f.coeff (n + 1) - 3 * f.coeff n := by
  have hd : 0 < f.natDegree := by omega
  have hd1 : f.natDegree - 1 = n + 2 := by omega
  have h₄ : ∀ l, l + 1 < n + 3 →
      (AdjoinRoot.modByMonicHom hf (AdjoinRoot.root f ^ (n + 4))).coeff (l + 1) =
        -f.coeff l + f.coeff (l + 1) * f.coeff (n + 2) := by
    intro l hl
    rw [pow_succ', coeff_modByMonicHom_root_mul hf hd, hd1,
      coeff_modByMonicHom_root_pow_of_natDegree_eq hf hdeg (by omega),
      coeff_modByMonicHom_root_pow_of_natDegree_eq hf hdeg (by omega)]
    ring
  have h₅ : (AdjoinRoot.modByMonicHom hf (AdjoinRoot.root f ^ (n + 5))).coeff (n + 2) =
      -f.coeff n + 2 * f.coeff (n + 1) * f.coeff (n + 2) - f.coeff (n + 2) ^ 3 := by
    rw [pow_succ', coeff_modByMonicHom_root_mul hf hd, hd1, h₄ n (by omega),
      h₄ (n + 1) (by omega)]
    ring
  rw [trace_adjoinRoot_eq_sum hf, hdeg, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_eq_zero, zero_add, ← pow_add, ← pow_add, ← pow_add,
    show 3 + n = n + 3 by omega, show 3 + (n + 1) = n + 4 by omega,
    show 3 + (n + 2) = n + 5 by omega,
    coeff_modByMonicHom_root_pow_of_natDegree_eq hf hdeg (by omega), h₄ n (by omega), h₅]
  · ring
  · intro j hj
    rw [Finset.mem_range] at hj
    exact coeff_modByMonicHom_root_pow_add hf (by norm_num) (by omega)

end Trace

section PurePower

variable {A : Type u} [CommRing A] {d : ℕ} (hd : 0 < d) (a : A)

include hd in
/-- `x^d - a` is monic. -/
theorem monic_X_pow_sub_C_of_pos : (Polynomial.X ^ d - C a).Monic := monic_X_pow_sub_C a hd.ne'

/-- `t^d = a` in `A[x]/(x^d - a)`. -/
theorem root_pow_X_pow_sub_C :
    AdjoinRoot.root (Polynomial.X ^ d - C a) ^ d = AdjoinRoot.of (Polynomial.X ^ d - C a) a := by
  have h := AdjoinRoot.eval₂_root (Polynomial.X ^ d - C a)
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero] at h
  exact h

include hd in
/-- **The traces of the powers of `t` in `A[x]/(x^d - a)`**: `Trace(t^k) = 0` for `0 < k < d` and
`Trace(t^d) = d a`. -/
theorem trace_root_pow_X_pow_sub_C {k : ℕ} (hk : 0 < k) (hkd : k ≤ d) :
    Algebra.trace A (AdjoinRoot (Polynomial.X ^ d - C a))
        (AdjoinRoot.root (Polynomial.X ^ d - C a) ^ k) =
      if k = d then (d : A) * a else 0 := by
  nontriviality A
  have hf := monic_X_pow_sub_C_of_pos hd a
  have hdeg : (Polynomial.X ^ d - C a).natDegree = d := natDegree_X_pow_sub_C
  split_ifs with hkd'
  · subst hkd'
    rw [root_pow_X_pow_sub_C, ← AdjoinRoot.algebraMap_eq,
      Algebra.trace_algebraMap_of_basis (AdjoinRoot.powerBasis' hf).basis, Fintype.card_fin,
      AdjoinRoot.powerBasis'_dim, hdeg, nsmul_eq_mul]
  · rw [trace_adjoinRoot_eq_sum hf, hdeg]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_range] at hj
    by_cases hjk : j + k < d
    · exact coeff_modByMonicHom_root_pow_add hf hk (by omega)
    · have hpow : AdjoinRoot.root (Polynomial.X ^ d - C a) ^ k *
          AdjoinRoot.root (Polynomial.X ^ d - C a) ^ j =
          a • AdjoinRoot.root (Polynomial.X ^ d - C a) ^ (j + k - d) := by
        rw [← pow_add, show k + j = d + (j + k - d) by omega, pow_add, root_pow_X_pow_sub_C,
          Algebra.smul_def, AdjoinRoot.algebraMap_eq]
      rw [hpow, map_smul, coeff_smul, coeff_modByMonicHom_root_pow_of_lt hf (by omega),
        ite_eq_right (by omega), smul_zero]

end PurePower

section BaseChange

variable {R S M N ι : Type*} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/-- **A map sending a basis to a basis is a base change**: if `g : M → N` is `R`-linear, `N` is an
`S`-module, and `g` carries a basis of `M` over `R` to a basis of `N` over `S`, then `N` is the
base change `S ⊗_R M`. -/
theorem isBaseChange_of_basis (b : Module.Basis ι R M) (b' : Module.Basis ι S N) (g : M →ₗ[R] N)
    (hg : ∀ i, g (b i) = b' i) : IsBaseChange S g := by
  refine IsBaseChange.of_equiv ((Algebra.TensorProduct.basis S b).equiv b' (Equiv.refl ι))
    fun x => ?_
  have : ((((Algebra.TensorProduct.basis S b).equiv b' (Equiv.refl ι)).toLinearMap.restrictScalars
      R).comp (TensorProduct.mk R S M 1)) = g :=
    b.ext fun i => by
      simp only [LinearMap.comp_apply, TensorProduct.mk_apply, LinearMap.restrictScalars_apply,
        LinearEquiv.coe_coe, ← Algebra.TensorProduct.basis_apply, Module.Basis.equiv_apply,
        Equiv.refl_apply, hg]
  exact LinearMap.congr_fun this x

variable {A₀ B₀ A B : Type u} [CommRing A₀] [CommRing B₀] [CommRing A] [CommRing B]
  [Algebra A₀ B₀] [Algebra A B] [Algebra A₀ A] [Algebra B₀ B] [Algebra A₀ B]
  [IsScalarTower A₀ A B] [IsScalarTower A₀ B₀ B]

/-- **Power bases with matching generators give a pushout**: if `B₀` has a power basis over `A₀`,
`B` a power basis over `A` of the same dimension, and `B₀ → B` carries the generator to the
generator, then `B = A ⊗_{A₀} B₀`. -/
theorem isPushout_of_powerBasis (pb₀ : PowerBasis A₀ B₀) (pb : PowerBasis A B)
    (hdim : pb₀.dim = pb.dim) (hgen : algebraMap B₀ B pb₀.gen = pb.gen) :
    Algebra.IsPushout A₀ B₀ A B :=
  Algebra.IsPushout.symm ⟨isBaseChange_of_basis pb₀.basis (pb.basis.reindex (finCongr hdim.symm))
    _ fun i => by
      rw [Module.Basis.reindex_apply, PowerBasis.coe_basis, PowerBasis.coe_basis]
      change algebraMap B₀ B (pb₀.gen ^ (i : ℕ)) = pb.gen ^ (((finCongr hdim.symm).symm i : _) : ℕ)
      rw [map_pow, hgen]
      rfl⟩

omit [Algebra A₀ A] [Algebra B₀ B] [Algebra A₀ B] [IsScalarTower A₀ A B] [IsScalarTower A₀ B₀ B] in
/-- **A power basis transported along ring isomorphisms**: if `e_A : A₀ ≅ A` and `e_B : B₀ ≅ B`
are compatible with `A₀ → B₀` and `A → B`, a power basis of `B₀` over `A₀` with generator `x`
gives a power basis of `B` over `A` with generator `e_B(x)`. -/
def powerBasisOfRingEquiv (eA : A₀ ≃+* A) (eB : B₀ ≃+* B)
    (hcomm : ∀ a, eB (algebraMap A₀ B₀ a) = algebraMap A B (eA a)) (pb : PowerBasis A₀ B₀) :
    PowerBasis A B :=
  letI : Algebra A₀ B := ((algebraMap A B).comp eA.toRingHom).toAlgebra
  let eL : B₀ ≃ₗ[A₀] B :=
    { eB.toAddEquiv with
      map_smul' := fun a b => by
        change eB (a • b) = algebraMap A B (eA a) * eB b
        rw [Algebra.smul_def, map_mul, hcomm] }
  { gen := eB pb.gen
    dim := pb.dim
    basis := (pb.basis.map eL).mapCoeffs eA fun c x => by
      change eA c • x = algebraMap A B (eA c) * x
      rw [Algebra.smul_def]
    basis_eq_pow := fun i => by
      rw [Module.Basis.mapCoeffs_apply, Module.Basis.map_apply, pb.basis_eq_pow]
      exact map_pow eB _ _ }

omit [Algebra A₀ A] [Algebra B₀ B] [Algebra A₀ B] [IsScalarTower A₀ A B] [IsScalarTower A₀ B₀ B] in
/-- The generator of `powerBasisOfRingEquiv eA eB hcomm pb` is `eB pb.gen`. -/
@[simp]
theorem powerBasisOfRingEquiv_gen (eA : A₀ ≃+* A) (eB : B₀ ≃+* B)
    (hcomm : ∀ a, eB (algebraMap A₀ B₀ a) = algebraMap A B (eA a)) (pb : PowerBasis A₀ B₀) :
    (powerBasisOfRingEquiv eA eB hcomm pb).gen = eB pb.gen :=
  rfl

omit [Algebra A₀ A] [Algebra B₀ B] [Algebra A₀ B] [IsScalarTower A₀ A B] [IsScalarTower A₀ B₀ B] in
/-- The dimension of `powerBasisOfRingEquiv eA eB hcomm pb` is `pb.dim`. -/
@[simp]
theorem powerBasisOfRingEquiv_dim (eA : A₀ ≃+* A) (eB : B₀ ≃+* B)
    (hcomm : ∀ a, eB (algebraMap A₀ B₀ a) = algebraMap A B (eA a)) (pb : PowerBasis A₀ B₀) :
    (powerBasisOfRingEquiv eA eB hcomm pb).dim = pb.dim :=
  rfl

end BaseChange

section Forms

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- **`(i + 1) Θ(x^i dx) = d Trace(x^{i+1})`** on an algebra with a power basis:
`d(x^{i+1}) = (i + 1) x^i dx`, and `Θ(db) = d Trace(b)`. -/
theorem frameTrace_pow_smul_oneForm_D (pb : PowerBasis A B) (x : B) (i : ℕ) :
    (i + 1) • frameTrace A B 1 (x ^ i • oneForm B Ω[B⁄ℤ] (D ℤ B x)) =
      oneForm A Ω[A⁄ℤ] (D ℤ A (Algebra.trace A B (x ^ (i + 1)))) := by
  have : Module.Finite A B := .of_basis pb.basis
  have : Module.Free A B := .of_basis pb.basis
  have h := frameTrace_oneForm_D (subsingleton_or_nonempty_anyFrame_of_powerBasis pb) (x ^ (i + 1))
  rw [trace_eq_algebra_trace] at h
  rw [← h, Derivation.leibniz_pow, Nat.add_sub_cancel, map_nsmul (oneForm B Ω[B⁄ℤ]),
    map_smul (oneForm B Ω[B⁄ℤ]), map_nsmul (frameTrace A B 1)]

/-- **Division by a positive integer in degree one**: if the differentials of `A` have no torsion
by positive integers, then `n ω = n v` with `n > 0` forces `ω = v` for one-forms of `A`. -/
theorem eq_of_nsmul_eq_nsmul_oneForm
    (htors : ∀ n : ℕ, 0 < n → ∀ ω : Ω[A⁄ℤ], (n : A) • ω = 0 → ω = 0) {n : ℕ} (hn : 0 < n)
    {ω : ⋀[A]^1 Ω[A⁄ℤ]} {v : Ω[A⁄ℤ]} (h : n • ω = n • oneForm A Ω[A⁄ℤ] v) :
    ω = oneForm A Ω[A⁄ℤ] v := by
  obtain ⟨w, rfl⟩ : ω ∈ LinearMap.range (oneForm A Ω[A⁄ℤ]) := by rw [range_oneForm]; trivial
  rw [← map_nsmul, ← map_nsmul] at h
  have h' := oneForm_injective _ _ h
  have h0 : ((n : A)) • (w - v) = 0 := by
    rw [Nat.cast_smul_eq_nsmul, smul_sub, h', sub_self]
  rw [sub_eq_zero.mp (htors n hn _ h0)]

variable {A₀ B₀ : Type u} [CommRing A₀] [CommRing B₀] [Algebra A₀ B₀] [Algebra A₀ A]
  [Algebra B₀ B] [Algebra A₀ B] [IsScalarTower A₀ A B] [IsScalarTower A₀ B₀ B]

/-- **`Θ(x^i dx)` is compatible with base change**: for a pushout `B = A ⊗_{A₀} B₀` of algebras
with power bases, `Θ_{B/A}` of `x^i dx` for the image `x` of `x₀ ∈ B₀` is the pull-back along
`A₀ → A` of `Θ_{B₀/A₀}(x₀^i dx₀)`. -/
theorem frameTrace_pow_smul_oneForm_D_of_isPushout [Algebra.IsPushout A₀ B₀ A B]
    (pb₀ : PowerBasis A₀ B₀) (pb : PowerBasis A B) (x₀ : B₀) (i : ℕ) :
    frameTrace A B 1 (algebraMap B₀ B x₀ ^ i • oneForm B Ω[B⁄ℤ] (D ℤ B (algebraMap B₀ B x₀))) =
      formsMap A₀ A 1 (frameTrace A₀ B₀ 1 (x₀ ^ i • oneForm B₀ Ω[B₀⁄ℤ] (D ℤ B₀ x₀))) := by
  have hx : formsMap B₀ B 1 (x₀ ^ i • oneForm B₀ Ω[B₀⁄ℤ] (D ℤ B₀ x₀)) =
      algebraMap B₀ B x₀ ^ i • oneForm B Ω[B⁄ℤ] (D ℤ B (algebraMap B₀ B x₀)) := by
    rw [map_smulₛₗ, oneForm_apply, formsMap_one_ι, map_D, map_pow]
    rfl
  rw [← hx]
  exact frameTrace_formsMap_of_isPushout A B (subsingleton_or_nonempty_anyFrame_of_powerBasis pb₀)
    (subsingleton_or_nonempty_anyFrame_of_powerBasis pb) 1 _

/-- **`Θ(x^i dx)` from a torsion-free model.** Let `B = A ⊗_{A₀} B₀` for power bases with matching
generators `x₀ ↦ x`, and suppose the differentials of `A₀` have no torsion by positive integers.
If `w₀ ∈ Ω_{A₀}` satisfies `(i + 1) w₀ = d Trace_{B₀/A₀}(x₀^{i+1})`, then `Θ_{B/A}(x^i dx)` is the
pull-back of `w₀`. -/
theorem frameTrace_gen_pow_smul_oneForm_D_eq
    (htors : ∀ n : ℕ, 0 < n → ∀ ω : Ω[A₀⁄ℤ], (n : A₀) • ω = 0 → ω = 0)
    (pb₀ : PowerBasis A₀ B₀) (pb : PowerBasis A B) (hdim : pb₀.dim = pb.dim)
    (hgen : algebraMap B₀ B pb₀.gen = pb.gen) (i : ℕ) (w₀ : Ω[A₀⁄ℤ])
    (hw : (i + 1) • w₀ = D ℤ A₀ (Algebra.trace A₀ B₀ (pb₀.gen ^ (i + 1)))) :
    frameTrace A B 1 (pb.gen ^ i • oneForm B Ω[B⁄ℤ] (D ℤ B pb.gen)) =
      oneForm A Ω[A⁄ℤ] (KaehlerDifferential.map ℤ ℤ A₀ A w₀) := by
  have h₁ := frameTrace_pow_smul_oneForm_D pb₀ pb₀.gen i
  rw [← hw, map_nsmul] at h₁
  have h₂ := eq_of_nsmul_eq_nsmul_oneForm htors (Nat.succ_pos i) h₁
  have := isPushout_of_powerBasis pb₀ pb hdim hgen
  rw [← hgen, frameTrace_pow_smul_oneForm_D_of_isPushout pb₀ pb pb₀.gen i, h₂, oneForm_apply,
    formsMap_one_ι]
  rfl

end Forms

section Model

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {f : A[X]}
  {A₀ : Type u} [CommRing A₀] (φ : A₀ →+* A) {f₀ : A₀[X]}

/-- **`Θ(t^i dt)` on `A[x]/(f)` from a torsion-free model.** Let `φ : A₀ → A` carry a monic `f₀`
to `f`, let `B ≅ A[x]/(f)` with `t` the image of `x`, and suppose the differentials of `A₀` have no
torsion by positive integers. If `w₀ ∈ Ω_{A₀}` satisfies
`(i + 1) w₀ = d Trace(t₀^{i+1})` in `A₀[x]/(f₀)`, then `Θ_{B/A}(t^i dt)` is the image of `w₀`. -/
theorem frameTrace_root_pow_smul_oneForm_D_eq
    (htors : ∀ n : ℕ, 0 < n → ∀ ω : Ω[A₀⁄ℤ], (n : A₀) • ω = 0 → ω = 0)
    (hf₀ : f₀.Monic) (hmap : f₀.map φ = f) (e : AdjoinRoot f ≃ₐ[A] B) (i : ℕ) (w₀ : Ω[A₀⁄ℤ])
    (hw : (i + 1) • w₀ =
      D ℤ A₀ (Algebra.trace A₀ (AdjoinRoot f₀) (AdjoinRoot.root f₀ ^ (i + 1)))) :
    frameTrace A B 1
        (e (AdjoinRoot.root f) ^ i • oneForm B Ω[B⁄ℤ] (D ℤ B (e (AdjoinRoot.root f)))) =
      oneForm A Ω[A⁄ℤ] (letI := φ.toAlgebra; KaehlerDifferential.map ℤ ℤ A₀ A w₀) := by
  let : Algebra A₀ A := φ.toAlgebra
  rcases subsingleton_or_nontrivial A with hA | hA
  · have := subsingleton_forms A 1
    exact Subsingleton.elim _ _
  have hf : f.Monic := hmap ▸ hf₀.map φ
  have hdeg : f₀.natDegree = f.natDegree := by rw [← hmap]; exact (hf₀.natDegree_map φ).symm
  have hroot : f₀.eval₂ ((algebraMap A B).comp φ) (e (AdjoinRoot.root f)) = 0 := by
    rw [← eval₂_map, hmap, ← aeval_def, aeval_algHom_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self,
      map_zero]
  let : Algebra (AdjoinRoot f₀) B :=
    (AdjoinRoot.lift ((algebraMap A B).comp φ) (e (AdjoinRoot.root f)) hroot).toAlgebra
  let : Algebra A₀ B := ((algebraMap A B).comp φ).toAlgebra
  have : IsScalarTower A₀ A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A₀ (AdjoinRoot f₀) B := IsScalarTower.of_algebraMap_eq fun r => by
    change ((algebraMap A B).comp φ) r =
      AdjoinRoot.lift ((algebraMap A B).comp φ) (e (AdjoinRoot.root f)) hroot (AdjoinRoot.of f₀ r)
    rw [AdjoinRoot.lift_of]
  have h := frameTrace_gen_pow_smul_oneForm_D_eq htors (AdjoinRoot.powerBasis' hf₀)
    ((AdjoinRoot.powerBasis' hf).map e) (by simpa using hdeg)
    (by
      change AdjoinRoot.lift ((algebraMap A B).comp φ) (e (AdjoinRoot.root f)) hroot
        (AdjoinRoot.root f₀) = _
      rw [AdjoinRoot.lift_root, PowerBasis.map_gen, AdjoinRoot.powerBasis'_gen])
    i w₀ (by rwa [AdjoinRoot.powerBasis'_gen])
  rwa [PowerBasis.map_gen, AdjoinRoot.powerBasis'_gen] at h

end Model

section Universal

/-- **The universal ring of coefficients** `ℤ[x_a : a ∈ A]`, as a type synonym carrying only its
ring structure (so that its only `ℤ`-algebra structure is the canonical one, which generic
statements about `Ω[A⁄ℤ]` see). -/
def UniversalCoefficients (A : Type u) : Type u := MvPolynomial A ℤ

/-- The commutative ring structure of `MvPolynomial A ℤ`. -/
instance (A : Type u) : CommRing (UniversalCoefficients A) :=
  inferInstanceAs (CommRing (MvPolynomial A ℤ))

/-- `ℤ[x_a : a ∈ A]` is nontrivial. -/
instance (A : Type u) : Nontrivial (UniversalCoefficients A) :=
  inferInstanceAs (Nontrivial (MvPolynomial A ℤ))

variable {A : Type u} [CommRing A]

/-- The variable `x_a` of `UniversalCoefficients A`. -/
def UniversalCoefficients.var (a : A) : UniversalCoefficients A := MvPolynomial.X a

/-- The evaluation `ℤ[x_a : a ∈ A] → A`, `x_a ↦ a`. -/
def UniversalCoefficients.eval (A : Type u) [CommRing A] : UniversalCoefficients A →+* A :=
  MvPolynomial.eval₂Hom (Int.castRingHom A) id

/-- The evaluation `x_a ↦ a` sends the variable `x_a` to `a`. -/
@[simp]
theorem UniversalCoefficients.eval_var (a : A) : UniversalCoefficients.eval A (var a) = a :=
  MvPolynomial.eval₂_X _ _ _

omit [CommRing A] in
/-- **The differentials of `ℤ[x_a : a ∈ A]` have no torsion by positive integers**: they are free
over the domain `ℤ[x_a]`. -/
theorem UniversalCoefficients.eq_zero_of_natCast_smul {n : ℕ} (hn : 0 < n)
    (ω : Ω[UniversalCoefficients A⁄ℤ]) (h : (n : UniversalCoefficients A) • ω = 0) : ω = 0 :=
  KaehlerDifferential.mvPolynomial_kaehler_eq_zero_of_natCast_smul hn ω h

/-- **The universal polynomial** of degree `deg f` over `ℤ[x_a : a ∈ A]` whose image under
`x_a ↦ a` is `f`: `x^d + ∑_{i < d} x_{f_i} x^i`. -/
def universalPolynomial (f : A[X]) : (UniversalCoefficients A)[X] :=
  Polynomial.X ^ f.natDegree + ∑ i : Fin f.natDegree,
    C (UniversalCoefficients.var (f.coeff i)) * Polynomial.X ^ (i : ℕ)

/-- The universal polynomial is monic. -/
theorem universalPolynomial_monic (f : A[X]) : (universalPolynomial f).Monic :=
  monic_X_pow_add (degree_sum_fin_lt _)

/-- The universal polynomial of `f` has the same degree as `f`. -/
theorem universalPolynomial_natDegree (f : A[X]) :
    (universalPolynomial f).natDegree = f.natDegree :=
  (natDegree_add_eq_left_of_degree_lt (by rw [degree_X_pow]; exact degree_sum_fin_lt _)).trans
    (natDegree_X_pow _)

/-- For monic `f`, the image of `universalPolynomial f` under `x_a ↦ a` is `f`. -/
theorem universalPolynomial_map {f : A[X]} (hf : f.Monic) :
    (universalPolynomial f).map (UniversalCoefficients.eval A) = f := by
  conv_rhs => rw [hf.as_sum]
  simp only [universalPolynomial, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, UniversalCoefficients.eval_var]
  rw [Fin.sum_univ_eq_sum_range (fun i => C (f.coeff i) * Polynomial.X ^ i)]

end Universal

end Stacks.FormsTrace

end
