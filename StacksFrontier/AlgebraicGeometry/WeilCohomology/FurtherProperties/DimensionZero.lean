module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.FieldTheory.Perfect
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Trace.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Weil cohomology of a smooth projective scheme of dimension zero

Let `H^*` be a Weil cohomology theory with coefficient field `F` of characteristic zero and let
`X` be a smooth projective scheme of dimension zero over the base field `k`. Thus `X = Spec(k')`
for a finite separable `k`-algebra `k'`, and `deg(X → Spec(k)) = [k' : k]`. Choosing a finite
Galois extension `k''/k` containing every factor of `k'` and setting `Y = Spec(k'')` and
`Σ = Hom_k(k', k'')`, the decomposition `k' ⊗_k k'' = ∏_{σ ∈ Σ} k''` turns the Künneth axiom
`(B)(a)` for `X × Y` and additivity on disjoint unions into an isomorphism

`⨁_j H^j(X) ⊗_F H^{n - j}(Y) ≅ H^n(X × Y) ≅ ∏_{σ ∈ Σ} H^n(Y)`

of graded `F`-vector spaces, which is `H^*(Y)`-linear and sends `a ⊗ b` to
`(Spec(σ)^*a ∪ b)_σ`. Comparing dimensions in the greatest and the least degree in which
`H^*(Y)` is nonzero forces `H^*(X)` to sit in degree `0` alone and to have dimension
`|Σ| = [k' : k]` there. The displayed isomorphism exhibits `H^0(X)` as an algebra whose
`|Σ|` characters span `H^0(Y)^Σ`, and reducing modulo a maximal ideal of `H^0(Y)` makes those
characters a basis of a vector space over the residue field; so `H^0(X)` embeds into a product
of fields and is reduced, hence — the coefficient field having characteristic zero — a finite
separable `F`-algebra. The projection formula and additivity of integration give
`(∫_X a) · 1 = ∑_σ Spec(σ)^* a` in `H^0(Y)`, and the right-hand side is the trace of
`a ⊗ 1` in the base-changed algebra `H^0(Y) ⊗_F H^0(X)`; so `∫_X` is the trace map of
`H^0(X)` over `F`. Finally `[X]` is the pullback of `[Spec(k)]` along the structure morphism, so
`γ([X]) = 1` and `∫_X γ([X]) = ∫_X 1 = dim_F H^0(X) = deg(X → Spec(k))`.

## Main results

* `Stacks.WeilCohomology.subsingleton_cohomology_of_dimension_zero`: the cohomology of `X`
  vanishes outside degree zero.
* `Stacks.WeilCohomology.finrank_cohomology_zero_eq_degree`: the degree-zero cohomology of `X`
  has dimension `deg(X → Spec(k))` over `F`.
* `Stacks.WeilCohomology.integration_eq_trace`: integration on `X` is the trace map of the
  `F`-algebra `H^0(X)`.
* `Stacks.WeilCohomology.isSeparable_of_isReduced`: a reduced finite-dimensional commutative
  algebra over a field of characteristic zero is separable.
* `Stacks.WeilCohomology.isSeparable_cohomology_zero`: the degree-zero cohomology of `X` is a
  separable `F`-algebra.
* `Stacks.WeilCohomology.cycleClass_fundamental_eq_one`: the cycle class of the fundamental
  class of `X` is the unit.
* `Stacks.WeilCohomology.integration_cycleClass_eq_degree`: integration of that cycle class is
  the degree of `X` over the base field.

## Implementation notes

As elsewhere in this directory the cohomological data is supplied as explicit arguments rather
than through a bundled Weil cohomology theory, and Tate twists are absorbed into the graded
pieces, so that `H^{2d}(X)(d) = H^0(X)` for `d = 0`. The dictionary is as follows.

* `HX`, `HY`, `HXY` are the graded cohomologies of `X`, `Y` and `X × Y`; the hypotheses
  `hsX`, `hsY` say that they vanish outside a finite set of degrees, which follows from axiom
  `(A)` for `X` and `Y`, and the `FiniteDimensional` instances are axiom `(A)(a)`.
* `kunneth` is axiom `(B)(a)` for the product `X × Y` over `k`, and `decomp` is the
  isomorphism of Stacks 0FHJ for the decomposition of `X × Y = Spec(k' ⊗_k k'')` into `|Σ|`
  copies of `Y`, with the index set `Σ` replaced by `Fin n`; so `n = |Σ| = [k' : k]` is the
  degree of `X` over the base field.
* `hm₀` is nonvanishing of the cohomology of `Y`, which is Stacks 0FHF.
* `A` stands for `H^0(X)` and `B` for `H^0(Y)`, commutative because cup product is graded
  commutative. The algebra maps `ψ σ` are the pullbacks `Spec(σ)^*`, and `e` together with
  `he` is the degree-zero part of the displayed isomorphism, written as an isomorphism of
  `B`-algebras `B ⊗_F A ≅ B^Σ` carrying `1 ⊗ a` to `(ψ σ a)_σ`.
* `hint` is the identity `(∫_X a) · 1 = ∑_σ Spec(σ)^* a` in `H^0(Y)`, which the source obtains
  from Stacks 0FHC and Stacks 0FHP.
* For the cycle class, `cycleClass` and `cycleClassPt` are the maps `γ` of `(D2)` for `X` and
  for `Spec(k)` in codimension zero, `pullbackCycle` and `pullbackCohomology` are pullback
  along the structure morphism on cycles and on cohomology, `hcompat` is axiom `(C)(a)`,
  `hfundamental` is the identity `[X] = p^*[Spec(k)]`, and `hpt` is `γ([Spec(k)]) = 1` from
  Stacks 0FHE.

The separability argument differs from the source's. The source checks separability of `H^0(X)`
after the faithfully flat base change `F → H^0(Y)`, where the algebra becomes a product of
copies of `H^0(Y)`; here the base change is pushed all the way to a residue field of `H^0(Y)`,
which is a field, so that the conclusion is read off from `H^0(X)` embedding into a finite
product of fields. Both routes use only the displayed isomorphism.

## References

* [Stacks Project, Tag 0FHQ](https://stacks.math.columbia.edu/tag/0FHQ)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u v w

namespace Stacks.WeilCohomology

/-! ### Dimensions of graded pieces -/

/-- The dimension of a direct sum whose summands vanish outside a finite set of indices is the
sum of the dimensions of the summands over that set. -/
private theorem finrank_directSum_of_subsingleton_notMem
    {F : Type u} [Field F] {ι : Type*} (M : ι → Type v)
    [∀ i, AddCommGroup (M i)] [∀ i, Module F (M i)] [∀ i, FiniteDimensional F (M i)]
    (s : Finset ι) (hs : ∀ i ∉ s, Subsingleton (M i)) :
    Module.finrank F (DirectSum ι M) = ∑ i ∈ s, Module.finrank F (M i) := by
  classical
  set N : {x // x ∈ s} → Type v := fun j => M j.1
  let g : (DirectSum {x // x ∈ s} N) →ₗ[F] (DirectSum ι M) :=
    DirectSum.toModule F _ _ fun i => DirectSum.lof F ι M i.1
  let f : (DirectSum ι M) →ₗ[F] (DirectSum {x // x ∈ s} N) :=
    DirectSum.toModule F _ _ fun i =>
      if h : i ∈ s then DirectSum.lof F _ N ⟨i, h⟩ else 0
  have hfg : f.comp g = LinearMap.id := by
    refine DirectSum.linearMap_ext _ fun i => LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, g, f, LinearMap.id_apply]
    rw [DirectSum.toModule_lof, DirectSum.toModule_lof]
    simp only [i.2, ↓reduceDIte]
    rfl
  have hgf : g.comp f = LinearMap.id := by
    refine DirectSum.linearMap_ext _ fun i => LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, g, f, LinearMap.id_apply]
    rw [DirectSum.toModule_lof]
    by_cases h : i ∈ s
    · simp only [h, ↓reduceDIte]
      rw [DirectSum.toModule_lof]
    · have := hs i h
      rw [Subsingleton.elim x 0, map_zero, map_zero]
      simp
  have e : (DirectSum ι M) ≃ₗ[F] (DirectSum {x // x ∈ s} N) :=
    LinearEquiv.ofLinearMap f g hfg hgf
  rw [e.finrank_eq, Module.finrank_directSum]
  exact Finset.sum_coe_sort s fun i => Module.finrank F (M i)

/-- If the convolution of `P` with `Q` is `n` times `Q`, `P a` and `Q b` are nonzero and `Q`
vanishes at `a + b - j` for every other `j` with `P j` nonzero, then `Q (a + b)` is nonzero. -/
private theorem ne_zero_of_convolution_eq_nsmul
    (P Q : ℤ → ℕ) (sP : Finset ℤ) (hP : ∀ i ∉ sP, P i = 0) (n : ℕ)
    (hconv : ∀ m, ∑ j ∈ sP, P j * Q (m - j) = n * Q m)
    (a b : ℤ) (ha : P a ≠ 0) (hb : Q b ≠ 0)
    (hvanish : ∀ j, P j ≠ 0 → j ≠ a → Q (a + b - j) = 0) : Q (a + b) ≠ 0 := by
  intro h
  have h1 := hconv (a + b)
  rw [Finset.sum_eq_single_of_mem a (not_imp_comm.mp (hP a) ha) fun j _ hne => by
    rcases Nat.eq_zero_or_pos (P j) with h | h
    · rw [h, zero_mul]
    · rw [hvanish j h.ne' hne, mul_zero], h, mul_zero, add_sub_cancel_left] at h1
  exact Nat.mul_ne_zero ha hb h1

/-- If the convolution of `P` with `Q` is `n` times `Q`, `a` is the greatest index where `P` is
nonzero and `b` the greatest where `Q` is nonzero, then `a ≤ 0`. -/
private theorem le_zero_of_convolution_eq_nsmul
    (P Q : ℤ → ℕ) (sP : Finset ℤ) (hP : ∀ i ∉ sP, P i = 0) (n : ℕ)
    (hconv : ∀ m, ∑ j ∈ sP, P j * Q (m - j) = n * Q m)
    (a b : ℤ) (ha : P a ≠ 0) (hb : Q b ≠ 0)
    (hPa : ∀ j, P j ≠ 0 → j ≤ a) (hQb : ∀ j, Q j ≠ 0 → j ≤ b) : a ≤ 0 := by
  have := hQb _ (ne_zero_of_convolution_eq_nsmul P Q sP hP n hconv a b ha hb fun j hj hne => by
    by_contra hc
    have := hQb _ hc
    have := hPa j hj
    omega)
  omega

/-- If the convolution of `P` with `Q` is `n` times `Q`, `a` is the least index where `P` is
nonzero and `b` the least where `Q` is nonzero, then `0 ≤ a`. -/
private theorem zero_le_of_convolution_eq_nsmul
    (P Q : ℤ → ℕ) (sP : Finset ℤ) (hP : ∀ i ∉ sP, P i = 0) (n : ℕ)
    (hconv : ∀ m, ∑ j ∈ sP, P j * Q (m - j) = n * Q m)
    (a b : ℤ) (ha : P a ≠ 0) (hb : Q b ≠ 0)
    (hPa : ∀ j, P j ≠ 0 → a ≤ j) (hQb : ∀ j, Q j ≠ 0 → b ≤ j) : 0 ≤ a := by
  have := hQb _ (ne_zero_of_convolution_eq_nsmul P Q sP hP n hconv a b ha hb fun j hj hne => by
    by_contra hc
    have := hQb _ hc
    have := hPa j hj
    omega)
  omega

/-- Let `P` and `Q` be finitely supported functions on the integers with values in the natural
numbers, with `Q` nonzero, and suppose that the convolution of `P` with `Q` is `n` times `Q`.
Then `P` is supported in `0` and takes the value `n` there.

This is the "look at the greatest and the least nonzero degree" step: in the greatest degree in
which the convolution can be nonzero only one term survives, which bounds the support of `P`
from above by `0`, and symmetrically from below. -/
private theorem eq_single_of_convolution_eq_nsmul
    (P Q : ℤ → ℕ) (sP sQ : Finset ℤ)
    (hP : ∀ i ∉ sP, P i = 0) (hQ : ∀ i ∉ sQ, Q i = 0)
    (m₀ : ℤ) (hm₀ : Q m₀ ≠ 0) (n : ℕ)
    (hconv : ∀ m, ∑ j ∈ sP, P j * Q (m - j) = n * Q m) :
    (∀ i, i ≠ 0 → P i = 0) ∧ P 0 = n := by
  classical
  set TP : Finset ℤ := sP.filter (fun j => P j ≠ 0)
  set TQ : Finset ℤ := sQ.filter (fun j => Q j ≠ 0)
  have hmemsP : ∀ j, P j ≠ 0 → j ∈ sP := fun j hj => not_imp_comm.mp (hP j) hj
  have hmemP : ∀ j, P j ≠ 0 → j ∈ TP := fun j hj => Finset.mem_filter.mpr ⟨hmemsP j hj, hj⟩
  have hmemQ : ∀ j, Q j ≠ 0 → j ∈ TQ := fun j hj =>
    Finset.mem_filter.mpr ⟨not_imp_comm.mp (hQ j) hj, hj⟩
  have hcancel : ∀ p q : ℕ, p * Q m₀ = q * Q m₀ → p = q := fun p q h =>
    Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hm₀) h
  by_cases hPzero : ∀ i, P i = 0
  · refine ⟨fun i _ => hPzero i, hcancel _ _ ?_⟩
    rw [hPzero 0, zero_mul, ← hconv m₀]
    exact (Finset.sum_eq_zero fun j _ => by rw [hPzero j, zero_mul]).symm
  push Not at hPzero
  obtain ⟨i₀, hi₀⟩ := hPzero
  have hTPne : TP.Nonempty := ⟨i₀, hmemP i₀ hi₀⟩
  have hTQne : TQ.Nonempty := ⟨m₀, hmemQ m₀ hm₀⟩
  have hPmax : P (TP.max' hTPne) ≠ 0 := (Finset.mem_filter.mp (TP.max'_mem hTPne)).2
  have hmaxle := le_zero_of_convolution_eq_nsmul P Q sP hP n hconv _ _ hPmax
    (Finset.mem_filter.mp (TQ.max'_mem hTQne)).2 (fun j hj => TP.le_max' j (hmemP j hj))
    (fun j hj => TQ.le_max' j (hmemQ j hj))
  have hminge := zero_le_of_convolution_eq_nsmul P Q sP hP n hconv _ _
    (Finset.mem_filter.mp (TP.min'_mem hTPne)).2 (Finset.mem_filter.mp (TQ.min'_mem hTQne)).2
    (fun j hj => TP.min'_le j (hmemP j hj)) (fun j hj => TQ.min'_le j (hmemQ j hj))
  have hminmax : TP.min' hTPne ≤ TP.max' hTPne := TP.min'_le _ (TP.max'_mem hTPne)
  have hzero : ∀ i, i ≠ 0 → P i = 0 := by
    intro i hi
    by_contra hc
    have h1 := TP.le_max' i (hmemP i hc)
    have h2 := TP.min'_le i (hmemP i hc)
    omega
  refine ⟨hzero, hcancel _ _ ?_⟩
  have h : TP.max' hTPne = 0 := by omega
  rw [← hconv m₀, Finset.sum_eq_single_of_mem 0 (hmemsP 0 (h ▸ hPmax))
    fun j _ hne => by rw [hzero j hne, zero_mul]]
  simp

/-! ### The graded structure of the cohomology of a zero-dimensional scheme -/

section Kunneth

variable (F : Type u) [Field F] (HX HY HXY : ℤ → Type v)
  [∀ i, AddCommGroup (HX i)] [∀ i, Module F (HX i)] [∀ i, FiniteDimensional F (HX i)]
  [∀ i, AddCommGroup (HY i)] [∀ i, Module F (HY i)] [∀ i, FiniteDimensional F (HY i)]
  [∀ i, AddCommGroup (HXY i)] [∀ i, Module F (HXY i)]
  (sX sY : Finset ℤ)
  (hsX : ∀ i ∉ sX, Subsingleton (HX i)) (hsY : ∀ i ∉ sY, Subsingleton (HY i))
  (kunneth : ∀ m : ℤ, DirectSum ℤ (fun j : ℤ => HX j ⊗[F] HY (m - j)) ≃ₗ[F] HXY m)
  (n : ℕ) (decomp : ∀ m : ℤ, HXY m ≃ₗ[F] (Fin n → HY m))
  (m₀ : ℤ) (hm₀ : Nontrivial (HY m₀))

include hsX hsY kunneth decomp hm₀ in
/-- The cohomology of a zero-dimensional smooth projective scheme vanishes outside degree zero
and has dimension `n` in degree zero, where `n` is the number of copies of `Y` in the
decomposition of `X × Y`. -/
private theorem finrank_cohomology_aux :
    (∀ i : ℤ, i ≠ 0 → Module.finrank F (HX i) = 0) ∧ Module.finrank F (HX 0) = n := by
  have hP : ∀ i ∉ sX, Module.finrank F (HX i) = 0 := fun i hi =>
    (Module.finrank_zero_iff (R := F)).mpr (hsX i hi)
  have hQ : ∀ i ∉ sY, Module.finrank F (HY i) = 0 := fun i hi =>
    (Module.finrank_zero_iff (R := F)).mpr (hsY i hi)
  have hconv : ∀ m : ℤ, ∑ j ∈ sX, Module.finrank F (HX j) * Module.finrank F (HY (m - j)) =
      n * Module.finrank F (HY m) := by
    intro m
    have h1 : Module.finrank F (DirectSum ℤ fun j : ℤ => HX j ⊗[F] HY (m - j)) =
        ∑ j ∈ sX, Module.finrank F (HX j) * Module.finrank F (HY (m - j)) := by
      rw [finrank_directSum_of_subsingleton_notMem (F := F) _ sX fun i hi =>
        (Module.finrank_zero_iff (R := F)).mp (by
          rw [Module.finrank_tensorProduct, hP i hi, zero_mul])]
      exact Finset.sum_congr rfl fun j _ => Module.finrank_tensorProduct
    have h2 : Module.finrank F (HXY m) = n * Module.finrank F (HY m) := by
      rw [(decomp m).finrank_eq, Module.finrank_pi_fintype]
      simp [Finset.sum_const]
    rw [← h1, (kunneth m).finrank_eq, h2]
  refine eq_single_of_convolution_eq_nsmul (fun i => Module.finrank F (HX i))
    (fun i => Module.finrank F (HY i)) sX sY hP hQ m₀ ?_ n hconv
  have := hm₀
  exact Module.finrank_pos.ne'

include hsX hsY kunneth decomp hm₀ in
/-- **Stacks Project, Tag 0FHQ, part (1).** The cohomology of a smooth projective scheme of
dimension zero over the base field vanishes in every nonzero degree. -/
@[stacks 0FHQ "part (1): H^i(X) = 0 for i ≠ 0"]
theorem subsingleton_cohomology_of_dimension_zero (i : ℤ) (hi : i ≠ 0) : Subsingleton (HX i) :=
  (Module.finrank_zero_iff (R := F)).mp
    ((finrank_cohomology_aux F HX HY HXY sX sY hsX hsY kunneth n decomp m₀ hm₀).1 i hi)

include hsX hsY kunneth decomp hm₀ in
/-- **Stacks Project, Tag 0FHQ, part (3).** The degree-zero cohomology of a smooth projective
scheme `X` of dimension zero over the base field has dimension `deg(X → Spec(k))` over the
coefficient field; the degree is the number `n` of copies of `Y` in the decomposition of
`X × Y`. -/
@[stacks 0FHQ "part (3): dim_F H^0(X) = deg(X → Spec k)"]
theorem finrank_cohomology_zero_eq_degree : Module.finrank F (HX 0) = n :=
  (finrank_cohomology_aux F HX HY HXY sX sY hsX hsY kunneth n decomp m₀ hm₀).2

end Kunneth

/-! ### Integration in degree zero is the trace -/

/-- The trace of an element of a finite product of copies of a commutative ring, as an algebra
over that ring, is the sum of its components. -/
private theorem trace_pi_const (B : Type w) [CommRing B] (n : ℕ) (y : Fin n → B) :
    Algebra.trace B (Fin n → B) y = ∑ σ, y σ := by
  classical
  rw [Algebra.trace_eq_matrix_trace (Pi.basisFun B (Fin n))]
  simp [Matrix.trace, Matrix.diag_apply, Algebra.leftMulMatrix_apply]

/-- Multiplication by `1 ⊗ a` on the base change `B ⊗_F A` is the base change of multiplication
by `a` on `A`. -/
private theorem lmul_one_tmul (F : Type u) [Field F] (A : Type v) [CommRing A] [Algebra F A]
    (B : Type w) [CommRing B] [Algebra F B] (a : A) :
    Algebra.lmul B (B ⊗[F] A) (1 ⊗ₜ[F] a) = LinearMap.baseChange B (Algebra.lmul F A a) := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b x => simp [Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy =>
    simp only [map_add, hx, hy]

section Trace

variable (F : Type u) [Field F] (A : Type v) [CommRing A] [Algebra F A] [FiniteDimensional F A]
  (B : Type w) [CommRing B] [Algebra F B] [Nontrivial B]
  (n : ℕ) (ψ : Fin n → A →ₐ[F] B)
  (e : B ⊗[F] A ≃ₐ[B] (Fin n → B)) (he : ∀ a : A, e (1 ⊗ₜ[F] a) = fun σ => ψ σ a)
  (integration : A →ₗ[F] F)
  (hint : ∀ a : A, algebraMap F B (integration a) = ∑ σ, ψ σ a)

include e he hint in
/-- **Stacks Project, Tag 0FHQ, part (4).** Integration on a smooth projective scheme of
dimension zero over the base field is the trace map of the `F`-algebra `H^0(X)`.

The hypothesis `hint` is the identity `(∫_X a) · 1 = ∑_σ Spec(σ)^*a` in `H^0(Y)`, and `e`
together with `he` is the isomorphism `H^0(Y) ⊗_F H^0(X) ≅ H^0(Y)^Σ` of `H^0(Y)`-algebras
sending `1 ⊗ a` to `(Spec(σ)^*a)_σ`. The right-hand side of `hint` is therefore the trace of
`1 ⊗ a` over `H^0(Y)`, which is the image of the trace of `a` over `F`. -/
@[stacks 0FHQ "part (4): ∫_X is the trace map"]
theorem integration_eq_trace : integration = Algebra.trace F A := by
  ext a
  refine (algebraMap F B).injective ?_
  rw [hint a]
  have h1 : Algebra.trace B (B ⊗[F] A) (1 ⊗ₜ[F] a) = algebraMap F B (Algebra.trace F A a) := by
    rw [Algebra.trace_apply, Algebra.trace_apply, lmul_one_tmul F A B a,
      LinearMap.trace_baseChange]
  rw [← h1, ← Algebra.trace_eq_of_algEquiv e (1 ⊗ₜ[F] a), he a, trace_pi_const]

end Trace

/-! ### Separability of the degree-zero cohomology -/

/-- A reduced finite-dimensional commutative algebra over a field of characteristic zero is
separable: the minimal polynomial of an element cannot have a repeated factor, since a
polynomial exhibiting such a factor would evaluate to a nonzero nilpotent element. -/
theorem isSeparable_of_isReduced (F : Type u) [Field F] [CharZero F] (A : Type v) [CommRing A]
    [Algebra F A] [FiniteDimensional F A] [IsReduced A] : Algebra.IsSeparable F A := by
  refine ⟨fun a => ?_⟩
  have hne : minpoly F a ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral a)
  refine PerfectField.separable_iff_squarefree.mpr fun q hq => ?_
  obtain ⟨r, hr⟩ := hq
  have hqr : Polynomial.aeval a (q * r) = 0 := by
    refine IsReduced.eq_zero _ ⟨2, ?_⟩
    have hsq : (q * r) ^ 2 = minpoly F a * r := by rw [hr]; ring
    rw [← map_pow, hsq, map_mul, minpoly.aeval, zero_mul]
  obtain ⟨s, hs⟩ := minpoly.dvd F a hqr
  have hq0 : q ≠ 0 := fun h => hne (by rw [hr, h]; ring)
  have hr0 : r ≠ 0 := fun h => hne (by rw [hr, h]; ring)
  have key : q * r = (q * r) * (q * s) := hs.trans (by rw [hr]; ring)
  exact IsUnit.of_mul_eq_one s
    (mul_left_cancel₀ (mul_ne_zero hq0 hr0) (by rw [mul_one]; exact key)).symm

section Separable

variable (F : Type u) [Field F] [CharZero F]
  (A : Type v) [CommRing A] [Algebra F A] [FiniteDimensional F A]
  (B : Type w) [CommRing B] [Algebra F B] [Nontrivial B]
  (n : ℕ) (ψ : Fin n → A →ₐ[F] B)
  (e : B ⊗[F] A ≃ₐ[B] (Fin n → B)) (he : ∀ a : A, e (1 ⊗ₜ[F] a) = fun σ => ψ σ a)
  (hrank : Module.finrank F A = n)

include e he hrank in
/-- **Stacks Project, Tag 0FHQ, part (2).** The degree-zero cohomology of a smooth projective
scheme of dimension zero over the base field is a finite separable algebra over the coefficient
field; finiteness is the hypothesis `[FiniteDimensional F A]`, which is axiom `(A)(a)`.

Reducing the isomorphism `e` modulo a maximal ideal of `B = H^0(Y)` produces `n` characters of
`A = H^0(X)` with values in the residue field `L` which span `L^n` over `L`; as `A` has
dimension `n` over `F` by part (3), the resulting map `A → L^n` is injective, so `A` is
reduced, and a reduced finite-dimensional algebra over a field of characteristic zero is
separable. -/
@[stacks 0FHQ "part (2): H^0(X) is a finite separable F-algebra"]
theorem isSeparable_cohomology_zero : Algebra.IsSeparable F A := by
  classical
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  have : Field (B ⧸ m) := Ideal.Quotient.field m
  set L := B ⧸ m
  set π : B →ₐ[F] L := Ideal.Quotient.mkₐ F m
  have hπsurj : Function.Surjective π := Ideal.Quotient.mkₐ_surjective F m
  set χ : A →ₐ[F] (Fin n → L) := AlgHom.pi fun σ => π.comp (ψ σ) with hχ
  -- the characters span `L^n` over `L`
  have hmem : ∀ z : B ⊗[F] A, (fun σ => π ((e z) σ)) ∈
      Submodule.span L (Set.range fun a => χ a) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero =>
      have hz : (fun σ => π ((e 0) σ)) = (0 : Fin n → L) := by
        funext σ
        simp
      rw [hz]
      exact Submodule.zero_mem _
    | tmul b x =>
      have hb : (b : B) ⊗ₜ[F] x = b • (1 ⊗ₜ[F] x) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have hval : (fun σ => π ((e (b ⊗ₜ[F] x)) σ)) = π b • χ x := by
        funext σ
        rw [hb, map_smul, he x]
        simp [hχ, AlgHom.pi_apply]
      rw [hval]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
    | add x y hx hy =>
      have : (fun σ => π ((e (x + y)) σ)) =
          (fun σ => π ((e x) σ)) + fun σ => π ((e y) σ) := by
        funext σ
        simp
      rw [this]
      exact Submodule.add_mem _ hx hy
  have hspan : Submodule.span L (Set.range fun a => χ a) = ⊤ := by
    refine eq_top_iff.mpr fun y _ => ?_
    obtain ⟨z, hz⟩ : ∃ z : Fin n → B, ∀ σ, π (z σ) = y σ :=
      ⟨fun σ => (hπsurj (y σ)).choose, fun σ => (hπsurj (y σ)).choose_spec⟩
    have := hmem (e.symm z)
    rw [AlgEquiv.apply_symm_apply] at this
    simpa [funext hz] using this
  -- the characters of a basis of `A` span `L^n`
  set bA : Module.Basis (Fin n) F A := Module.finBasisOfFinrankEq F A hrank
  have hreprχ : ∀ a : A, χ a = ∑ i, algebraMap F L (bA.repr a i) • χ (bA i) := by
    intro a
    conv_lhs => rw [← bA.sum_repr a]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, algebraMap_smul]
  have hspan' : ⊤ ≤ Submodule.span L (Set.range fun i => χ (bA i)) := by
    refine le_trans (le_of_eq hspan.symm) (Submodule.span_le.mpr ?_)
    rintro - ⟨a, rfl⟩
    show χ a ∈ Submodule.span L (Set.range fun i => χ (bA i))
    rw [hreprχ a]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hcard : Fintype.card (Fin n) = Module.finrank L (Fin n → L) := by simp
  have hli : LinearIndependent L fun i => χ (bA i) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan' hcard
  -- hence `A` embeds into a product of fields
  have hinj : Function.Injective χ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have hz : ∑ i, algebraMap F L (bA.repr a i) • χ (bA i) = 0 := by rw [← hreprχ a, ha]
    have hzero := Fintype.linearIndependent_iff.mp hli _ hz
    have hrepr0 : bA.repr a = 0 := by
      ext i
      exact (algebraMap F L).injective (by simpa using hzero i)
    simpa using bA.repr.injective (by simpa using hrepr0)
  have : IsReduced (Fin n → L) :=
    ⟨fun y hy => funext fun σ => (hy.map (Pi.evalRingHom (fun _ : Fin n => L) σ)).eq_zero⟩
  have : IsReduced A := isReduced_of_injective χ.toRingHom hinj
  exact isSeparable_of_isReduced F A

end Separable

/-! ### The cycle class of the fundamental class -/

section CycleClass

variable (A : Type v) [CommRing A] (Apt : Type v) [CommRing Apt]
  (CH : Type w) [AddCommGroup CH] (CHpt : Type w) [AddCommGroup CHpt]
  (fundamental : CH) (fundamentalPt : CHpt)
  (cycleClass : CH →+ A) (cycleClassPt : CHpt →+ Apt)
  (pullbackCycle : CHpt →+ CH) (pullbackCohomology : Apt →+ A)
  (hfundamental : pullbackCycle fundamentalPt = fundamental)
  (hcompat : ∀ α, cycleClass (pullbackCycle α) = pullbackCohomology (cycleClassPt α))
  (hpt : cycleClassPt fundamentalPt = 1)
  (hone : pullbackCohomology 1 = 1)

include hfundamental hcompat hpt hone in
/-- **Stacks Project, Tag 0FHQ, part (5).** The cycle class of the fundamental class of a
nonempty smooth projective scheme over the base field is the unit of its cohomology algebra.

The fundamental class of `X` is the pullback of the fundamental class of `Spec(k)` along the
structure morphism (`hfundamental`); the cycle class map commutes with pullback by axiom
`(C)(a)` (`hcompat`); the cycle class of the fundamental class of `Spec(k)` is the unit by
Stacks 0FHE (`hpt`); and cohomological pullback preserves the unit (`hone`). -/
@[stacks 0FHQ "part (5): γ([X]) = 1"]
theorem cycleClass_fundamental_eq_one : cycleClass fundamental = 1 := by
  rw [← hfundamental, hcompat, hpt, hone]

end CycleClass

/-! ### Integrating the fundamental class -/

section Degree

variable (F : Type u) [Field F] (A : Type v) [CommRing A] [Algebra F A] [FiniteDimensional F A]
  (Apt : Type v) [CommRing Apt]
  (B : Type w) [CommRing B] [Algebra F B] [Nontrivial B]
  (CH : Type w) [AddCommGroup CH] (CHpt : Type w) [AddCommGroup CHpt]
  (fundamental : CH) (fundamentalPt : CHpt)
  (cycleClass : CH →+ A) (cycleClassPt : CHpt →+ Apt)
  (pullbackCycle : CHpt →+ CH) (pullbackCohomology : Apt →+ A)
  (hfundamental : pullbackCycle fundamentalPt = fundamental)
  (hcompat : ∀ α, cycleClass (pullbackCycle α) = pullbackCohomology (cycleClassPt α))
  (hpt : cycleClassPt fundamentalPt = 1)
  (hone : pullbackCohomology 1 = 1)
  (n : ℕ) (ψ : Fin n → A →ₐ[F] B)
  (e : B ⊗[F] A ≃ₐ[B] (Fin n → B)) (he : ∀ a : A, e (1 ⊗ₜ[F] a) = fun σ => ψ σ a)
  (integration : A →ₗ[F] F)
  (hint : ∀ a : A, algebraMap F B (integration a) = ∑ σ, ψ σ a)
  (hrank : Module.finrank F A = n)

include hfundamental hcompat hpt hone e he hint hrank in
/-- **Stacks Project, Tag 0FHQ, part (6).** Integration of the cycle class of the fundamental
class of a smooth projective scheme of dimension zero over the base field is its degree over
the base field.

By part (5) that cycle class is the unit, by part (4) integration is the trace map, and the
trace of the unit is the dimension of `H^0(X)` over the coefficient field, which is the degree
by part (3). -/
@[stacks 0FHQ "part (6): ∫_X γ([X]) = deg(X → Spec k)"]
theorem integration_cycleClass_eq_degree : integration (cycleClass fundamental) = (n : F) := by
  rw [cycleClass_fundamental_eq_one A Apt CH CHpt fundamental fundamentalPt cycleClass
      cycleClassPt pullbackCycle pullbackCohomology hfundamental hcompat hpt hone,
    integration_eq_trace F A B n ψ e he integration hint]
  rw [← map_one (algebraMap F A), Algebra.trace_algebraMap, hrank]
  simp

end Degree

end Stacks.WeilCohomology

end
