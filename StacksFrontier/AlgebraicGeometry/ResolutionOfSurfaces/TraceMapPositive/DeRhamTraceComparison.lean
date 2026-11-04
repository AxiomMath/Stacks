module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Trace.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.HigherTrace.Basic
public import StacksFrontier.LinearAlgebra.ExteriorPower.Wedge
public import StacksFrontier.RingTheory.DeRham.Complex
public import StacksFrontier.RingTheory.DeRham.PolynomialHomotopy

/-!
# The trace on differential forms as a map of de Rham complexes

Let `𝐅_p ⊂ Λ ⊂ R ⊂ S` be ring extensions with `S` isomorphic to `R[x]/(x ^ p - a)`, and let
`Tr : Ω^{t+1}_{S/Λ} → Ω^{t+1}_{R/Λ}` be the trace on differential forms,
`KaehlerDifferential.higherTrace`.  Placing `0` in degree zero and `Tr` in every positive degree
produces a map of de Rham complexes `Θ_{S/R} : Ω^•_{S/Λ} ⟶ Ω^•_{R/Λ}`.

## Main definitions

* `KaehlerDifferential.higherTraceOne` is the trace in degree one, `Ω_{S/Λ} → Ω_{R/Λ}`.
* `KaehlerDifferential.higherTraceComplexComponent` is the degree-`i` component of the map of
  complexes.
* `KaehlerDifferential.higherTraceComplexMap` is **the map of de Rham complexes
  `Ω^•_{S/Λ} ⟶ Ω^•_{R/Λ}`**.

## Main results

* `KaehlerDifferential.span_rootExtensionDifferentials`: the differentials of the elements of `R`
  together with `dx` generate `Ω_{S/Λ}` over `S`.
* `KaehlerDifferential.higherTraceOne_smul_baseDifferential` and
  `KaehlerDifferential.higherTraceOne_rootPow`: the values of the degree-one trace.
* `KaehlerDifferential.higherTrace_ιMulti_snoc` and
  `KaehlerDifferential.higherTrace_ιMulti_cons`: **the trace is linear over the differential forms
  of `R`** — a differential pulled back from `R` passes through it.
* `KaehlerDifferential.higherTraceOne_D_eq_zero`: the trace annihilates the exact differentials.
* `KaehlerDifferential.trace_pthRoot_eq_zero`: **`Trace_{S/R}` is identically zero**.
* `KaehlerDifferential.higherTrace_deRhamDifferential` and
  `KaehlerDifferential.higherTrace_deRhamDifferential_zero`: **the trace commutes with the de Rham
  differential**.
* `KaehlerDifferential.higherTraceComplexMap_f_zero` and
  `KaehlerDifferential.higherTraceComplexMap_f_succ`: the components of that map are `0` in degree
  zero and `Tr` in every positive degree.
* `KaehlerDifferential.higherTraceComplexMap_wedgeMul`: **the projection formula
  `Θ_{S/R}(a ∧ b) = a ∧ Θ_{S/R}(b)`** for arbitrary `a ∈ Ω^i_{R/Λ}` (pulled back along
  `KaehlerDifferential.mapExteriorPower`) and `b ∈ Ω^j_{S/Λ}`.
* `KaehlerDifferential.eq_higherTraceComplexMap`: the identification of Remark 0FLF — a map of de
  Rham complexes which is `Trace_{S/R}` in degree zero, satisfies the projection formula and sends
  `x ^ (p - 1) dx` to `da` is the map built from `Tr`.
* `KaehlerDifferential.eq_higherTraceComplexMap_f` and
  `KaehlerDifferential.eq_higherTraceComplexMap_f_of_comm`: the same identification for a family
  of linear maps `θ_n : Ω^n_{S/Λ} → Ω^n_{R/Λ}`.

## References

* [Stacks Project, Tag 0FLC](https://stacks.math.columbia.edu/tag/0FLC)
* [Stacks Project, Tag 0FLF](https://stacks.math.columbia.edu/tag/0FLF)
-/
public noncomputable section

namespace KaehlerDifferential

open Polynomial
open scoped KaehlerDifferential

variable {p t : ℕ} {Λ R S : Type*} [CommRing Λ] [CommRing R] [CommRing S]
  [Algebra Λ R] [Algebra Λ S] [Algebra R S] [IsScalarTower Λ R S]

/-- Appending a vector to a fixed wedge of `n` vectors, as a linear map. -/
private noncomputable def wedgeSnocLinear {K M : Type*} [CommRing K] [AddCommGroup M]
    [Module K M] {n : ℕ} (η : Fin n → M) : M →ₗ[K] ⋀[K]^(n + 1) M where
  toFun m := exteriorPower.ιMulti K (n + 1) (Fin.snoc η m)
  map_add' m₁ m₂ := (exteriorPower.ιMulti K _).toMultilinearMap.snoc_add η m₁ m₂
  map_smul' c m := (exteriorPower.ιMulti K _).toMultilinearMap.snoc_smul η c m

private theorem D_algebraMap_eq_map_D {m : ℕ} (r : Fin m → R) :
    (fun j => D Λ S (algebraMap R S (r j))) =
      fun j => KaehlerDifferential.map Λ Λ R S (D Λ R (r j)) :=
  funext fun j => (KaehlerDifferential.map_D Λ Λ R S (r j)).symm

/-- The trace kills multiples of a wedge of differentials of elements of `R`. -/
private theorem higherTrace_smul_ιMulti_D_algebraMap (hp : p.Prime) [CharP Λ p] (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) (s : S) (r : Fin (t + 1) → R) :
    higherTrace (t := t) hp a e
      (s • exteriorPower.ιMulti S (t + 1) fun j => D Λ S (algebraMap R S (r j))) = 0 := by
  rw [D_algebraMap_eq_map_D]
  exact higherTrace_smul_baseForm hp a e s _

/-- Appending a scalar multiple of a vector to a wedge is a scalar multiple of the wedge. -/
private theorem smul_ιMulti_snoc {K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]
    {n : ℕ} (s : K) (u : Fin n → M) (m : M) :
    s • exteriorPower.ιMulti K (n + 1) (Fin.snoc u m) =
      exteriorPower.ιMulti K (n + 1) (Fin.snoc u (s • m)) :=
  ((exteriorPower.ιMulti K _).toMultilinearMap.snoc_smul u s m).symm

/-- The differentials of a tuple extended by `a` are the extended tuple of differentials. -/
private theorem snoc_D_eq {t : ℕ} (r : Fin t → R) (a : R) :
    Fin.snoc (fun j => D Λ R (r j)) (D Λ R a) =
      fun i => D Λ R ((Fin.snoc r a : Fin (t + 1) → R) i) :=
  (Fin.comp_snoc (D Λ R) r a).symm

omit [Algebra Λ R] [IsScalarTower Λ R S] in
/-- The absolute differentials of `S` are generated over `S` by the differentials of the elements
of `R` together with the differential of the chosen `p`-th root. -/
public theorem span_rootExtensionDifferentials (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) :
    Submodule.span S (Set.range (fun r : R => D Λ S (algebraMap R S r)) ∪
      {D Λ S (e (AdjoinRoot.root (X ^ p - C a)))}) = ⊤ := by
  set x := e (AdjoinRoot.root (X ^ p - C a)) with hx
  set P := Submodule.span S (Set.range (fun r : R => D Λ S (algebraMap R S r)) ∪
    {D Λ S x})
  have htop : Algebra.adjoin R {x} = ⊤ := by
    rw [show ({x} : Set S) = e.toAlgHom '' {AdjoinRoot.root (X ^ p - C a)} by simp [hx],
      Algebra.adjoin_image, AdjoinRoot.adjoinRoot_eq_top, Algebra.map_top, AlgHom.range_eq_top]
    exact e.surjective
  have hD : ∀ s : S, D Λ S s ∈ P := by
    intro s
    have hs : s ∈ Algebra.adjoin R ({x} : Set S) := htop ▸ Algebra.mem_top
    induction hs using Algebra.adjoin_induction with
    | mem y hy =>
        rw [Set.mem_singleton_iff] at hy
        exact hy ▸ Submodule.subset_span (Or.inr rfl)
    | algebraMap r => exact Submodule.subset_span (Or.inl ⟨r, rfl⟩)
    | add y z _ _ iy iz => simpa using P.add_mem iy iz
    | mul y z _ _ iy iz =>
        rw [Derivation.leibniz]
        exact P.add_mem (P.smul_mem _ iz) (P.smul_mem _ iy)
  refine top_unique ?_
  rw [← KaehlerDifferential.span_range_derivation Λ S]
  exact Submodule.span_le.mpr (Set.range_subset_iff.mpr hD)

/-- The power basis `1, x, …, x ^ (p - 1)` of `S` over `R` carried by the presentation. -/
private noncomputable def rootPowerBasis [Nontrivial R] (hp : p.Prime) (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) : PowerBasis R S :=
  (AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C a hp.ne_zero)).map e

private theorem rootPowerBasis_dim [Nontrivial R] (hp : p.Prime) (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) : (rootPowerBasis hp a e).dim = p := by
  rw [rootPowerBasis, PowerBasis.map, AdjoinRoot.powerBasis'_dim,
    Polynomial.natDegree_X_pow_sub_C]

private theorem rootPowerBasis_basis [Nontrivial R] (hp : p.Prime) (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) (i : Fin (rootPowerBasis hp a e).dim) :
    (rootPowerBasis hp a e).basis i = e (AdjoinRoot.root (X ^ p - C a)) ^ (i : ℕ) := by
  rw [PowerBasis.coe_basis]
  rfl

private theorem rootPowerBasis_lt [Nontrivial R] (hp : p.Prime) (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) (i : Fin (rootPowerBasis hp a e).dim) : (i : ℕ) < p :=
  i.isLt.trans_eq (rootPowerBasis_dim hp a e)

/-- Every element of `S` is the sum of its power-basis coefficients times the powers of `x`. -/
private theorem eq_sum_repr_rootPow [Nontrivial R] (hp : p.Prime) (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) (s : S) :
    s = ∑ i : Fin (rootPowerBasis hp a e).dim, (rootPowerBasis hp a e).basis.repr s i •
      e (AdjoinRoot.root (X ^ p - C a)) ^ (i : ℕ) := by
  conv_lhs => rw [← (rootPowerBasis hp a e).basis.sum_repr s]
  exact Finset.sum_congr rfl fun i _ => by rw [rootPowerBasis_basis]

/-- The image of the root of `X ^ n - C a` satisfies `x ^ n = a`. -/
private theorem pow_root_eq_algebraMap {n : ℕ} {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (a : A) (e : AdjoinRoot (X ^ n - C a) ≃ₐ[A] B) :
    e (AdjoinRoot.root (X ^ n - C a)) ^ n = algebraMap A B a := by
  have h := AdjoinRoot.eval₂_root (X ^ n - C a)
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
    sub_eq_zero] at h
  rw [← map_pow, h, ← AdjoinRoot.algebraMap_eq, AlgEquiv.commutes]

/-- The coefficient of `x ^ (p - 1)` in the power-basis expansion of an element of `S`. -/
private noncomputable def topRootCoeff [Nontrivial R] (hp : p.Prime) (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) : S →ₗ[R] R :=
  (rootPowerBasis hp a e).basis.coord
    ⟨p - 1, by rw [rootPowerBasis_dim]; have := hp.pos; omega⟩

/-- A wedge of length one is linear in its single entry. -/
private theorem ιMulti_one_smul {K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]
    (c : K) (m : M) :
    exteriorPower.ιMulti K 1 (fun _ => c • m) = c • exteriorPower.ιMulti K 1 (fun _ => m) := by
  rw [← exteriorPower.oneEquiv_symm_apply, ← exteriorPower.oneEquiv_symm_apply, map_smul]

/-- Appending to the empty tuple produces the constant tuple of length one. -/
private theorem fin_snoc_zero {M : Type*} (f : Fin 0 → M) (m : M) :
    Fin.snoc f m = fun _ => m := by
  funext j
  refine Fin.lastCases ?_ (fun k => k.elim0) j
  exact Fin.snoc_last ..

/-- **The trace on differential forms in degree one**, `Ω_{S/Λ} → Ω_{R/Λ}`: the degree-one part
of the trace of [Stacks, Tag 0AX5], read through the identification of a module with the first
exterior power of itself. -/
public noncomputable def higherTraceOne (hp : p.Prime) [CharP Λ p] (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) : Ω[S⁄Λ] →ₗ[R] Ω[R⁄Λ] :=
  (exteriorPower.oneEquiv R (Ω[R⁄Λ])).toLinearMap.comp
    ((higherTrace (t := 0) hp a e).comp
      ((exteriorPower.oneEquiv S (Ω[S⁄Λ])).symm.toLinearMap.restrictScalars R))

private theorem higherTraceOne_apply (hp : p.Prime) [CharP Λ p] (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) (ω : Ω[S⁄Λ]) :
    higherTraceOne hp a e ω = exteriorPower.oneEquiv R (Ω[R⁄Λ])
      (higherTrace (t := 0) hp a e (exteriorPower.ιMulti S 1 fun _ => ω)) := by
  rw [higherTraceOne]
  simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    exteriorPower.oneEquiv_symm_apply]

/-- The degree-one trace kills every multiple of a differential pulled back from `R`. -/
public theorem higherTraceOne_smul_baseDifferential (hp : p.Prime) [CharP Λ p] (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) (s : S) (η : Ω[R⁄Λ]) :
    higherTraceOne hp a e (s • KaehlerDifferential.map Λ Λ R S η) = 0 := by
  rw [higherTraceOne_apply, ιMulti_one_smul,
    higherTrace_smul_baseForm (t := 0) (Λ := Λ) hp a e s (fun _ => η), map_zero]

/-- The degree-one trace sends `x ^ i dx` to `da` when `i = p - 1` and to zero for the other
powers below `p`. -/
public theorem higherTraceOne_rootPow (hp : p.Prime) [CharP Λ p] (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) (i : ℕ) (hi : i < p) :
    higherTraceOne hp a e
        (e (AdjoinRoot.root (X ^ p - C a)) ^ i • D Λ S (e (AdjoinRoot.root (X ^ p - C a)))) =
      if i = p - 1 then D Λ R a else 0 := by
  rw [higherTraceOne_apply]
  split_ifs with h
  · subst h
    have hval := higherTrace_apply_top (t := 0) (Λ := Λ) hp a e (fun j => j.elim0)
    rw [fin_snoc_zero, fin_snoc_zero] at hval
    rw [hval, ← exteriorPower.oneEquiv_symm_apply, LinearEquiv.apply_symm_apply]
  · have hle : i ≤ p - 2 := by have := hp.two_le; omega
    have hval := higherTrace_apply_of_le (t := 0) (Λ := Λ) hp a e i hle (fun j => j.elim0)
    rw [fin_snoc_zero] at hval
    rw [hval, map_zero]

/-- The trace of a wedge of base differentials with an arbitrary multiple of `dx` appended is the
coefficient of `x ^ (p - 1)` times the wedge with `da` appended. -/
private theorem higherTrace_snoc_smul_rootDifferential [Nontrivial R] (hp : p.Prime) [CharP Λ p]
    (a : R) (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) (η : Fin t → Ω[R⁄Λ]) (s : S) :
    higherTrace (t := t) hp a e (exteriorPower.ιMulti S (t + 1)
        (Fin.snoc (fun j => KaehlerDifferential.map Λ Λ R S (η j))
          (s • D Λ S (e (AdjoinRoot.root (X ^ p - C a)))))) =
      topRootCoeff hp a e s • exteriorPower.ιMulti R (t + 1) (Fin.snoc η (D Λ R a)) := by
  classical
  have hidx : p - 1 < (rootPowerBasis hp a e).dim := by
    rw [rootPowerBasis_dim]
    have := hp.pos
    omega
  set u : Fin t → Ω[S⁄Λ] := fun j => KaehlerDifferential.map Λ Λ R S (η j) with hu
  set L : Ω[S⁄Λ] →ₗ[R] ⋀[R]^(t + 1) Ω[R⁄Λ] :=
    (higherTrace (t := t) hp a e).comp ((wedgeSnocLinear (K := S) u).restrictScalars R)
  have hL : ∀ z : Ω[S⁄Λ],
      L z = higherTrace (t := t) hp a e (exteriorPower.ιMulti S (t + 1) (Fin.snoc u z)) :=
    fun z => rfl
  have hterm : ∀ i : Fin (rootPowerBasis hp a e).dim,
      L (e (AdjoinRoot.root (X ^ p - C a)) ^ (i : ℕ) •
          D Λ S (e (AdjoinRoot.root (X ^ p - C a)))) =
        if (i : ℕ) = p - 1 then exteriorPower.ιMulti R (t + 1) (Fin.snoc η (D Λ R a)) else 0 := by
    intro i
    have hlt := rootPowerBasis_lt hp a e i
    rw [hL]
    split_ifs with h
    · rw [h]
      exact higherTrace_apply_top (t := t) (Λ := Λ) hp a e η
    · exact higherTrace_apply_of_le (t := t) (Λ := Λ) hp a e _
        (by have := hp.two_le; omega) η
  have hsum : s • D Λ S (e (AdjoinRoot.root (X ^ p - C a))) =
      ∑ i : Fin (rootPowerBasis hp a e).dim, (rootPowerBasis hp a e).basis.repr s i •
        (e (AdjoinRoot.root (X ^ p - C a)) ^ (i : ℕ) •
          D Λ S (e (AdjoinRoot.root (X ^ p - C a)))) := by
    conv_lhs => rw [← (rootPowerBasis hp a e).basis.sum_repr s]
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [rootPowerBasis_basis, smul_assoc]
  rw [← hL, hsum, map_sum]
  simp only [map_smul, hterm]
  have hzero : ∀ i ∈ (Finset.univ : Finset (Fin (rootPowerBasis hp a e).dim)),
      i ≠ ⟨p - 1, hidx⟩ → (rootPowerBasis hp a e).basis.repr s i •
        (if (i : ℕ) = p - 1 then exteriorPower.ιMulti R (t + 1) (Fin.snoc η (D Λ R a))
          else 0) = 0 := by
    intro i _ hi
    have : (i : ℕ) ≠ p - 1 := fun h => hi (Fin.ext h)
    simp [this]
  rw [Finset.sum_eq_single_of_mem ⟨p - 1, hidx⟩ (Finset.mem_univ _) hzero]
  simp [topRootCoeff, Module.Basis.coord_apply]

/-- The degree-one trace of an arbitrary multiple of `dx` is the coefficient of `x ^ (p - 1)`
times `da`. -/
private theorem higherTraceOne_smul_rootDifferential [Nontrivial R] (hp : p.Prime) [CharP Λ p]
    (a : R) (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) (s : S) :
    higherTraceOne hp a e (s • D Λ S (e (AdjoinRoot.root (X ^ p - C a)))) =
      topRootCoeff hp a e s • D Λ R a := by
  rw [higherTraceOne_apply]
  have hval := higherTrace_snoc_smul_rootDifferential (t := 0) (Λ := Λ) hp a e
    (fun j => j.elim0) s
  rw [fin_snoc_zero, fin_snoc_zero] at hval
  rw [hval, map_smul, ← exteriorPower.oneEquiv_symm_apply, LinearEquiv.apply_symm_apply]

/-- Appending a multiple of a differential pulled back from `R` to a wedge of differentials
pulled back from `R` gives a form of trace zero. -/
private theorem higherTrace_snoc_smul_baseDifferential (hp : p.Prime) [CharP Λ p] (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) (η : Fin t → Ω[R⁄Λ]) (r : R) (s : S) :
    higherTrace (t := t) hp a e (exteriorPower.ιMulti S (t + 1)
        (Fin.snoc (fun j => KaehlerDifferential.map Λ Λ R S (η j))
          (s • KaehlerDifferential.map Λ Λ R S (D Λ R r)))) = 0 := by
  have htup : Fin.snoc (fun j => KaehlerDifferential.map Λ Λ R S (η j))
      (KaehlerDifferential.map Λ Λ R S (D Λ R r)) =
      fun j => KaehlerDifferential.map Λ Λ R S
        ((Fin.snoc η (D Λ R r) : Fin (t + 1) → Ω[R⁄Λ]) j) := by
    funext j
    refine Fin.lastCases ?_ (fun k => ?_) j <;>
      simp [Fin.snoc_last, Fin.snoc_castSucc]
  have hw : (wedgeSnocLinear (K := S)
        (fun j => KaehlerDifferential.map Λ Λ R S (η j)))
      (s • KaehlerDifferential.map Λ Λ R S (D Λ R r)) =
      s • exteriorPower.ιMulti S (t + 1) (fun j => KaehlerDifferential.map Λ Λ R S
        ((Fin.snoc η (D Λ R r) : Fin (t + 1) → Ω[R⁄Λ]) j)) := by
    rw [map_smul]
    change s • exteriorPower.ιMulti S (t + 1) (Fin.snoc
      (fun j => KaehlerDifferential.map Λ Λ R S (η j))
      (KaehlerDifferential.map Λ Λ R S (D Λ R r))) = _
    rw [htup]
  change higherTrace (t := t) hp a e ((wedgeSnocLinear (K := S)
    (fun j => KaehlerDifferential.map Λ Λ R S (η j)))
      (s • KaehlerDifferential.map Λ Λ R S (D Λ R r))) = 0
  rw [hw]
  exact higherTrace_smul_baseForm hp a e s (Fin.snoc η (D Λ R r))

/-- **The trace is linear over the differential forms of `R`**: appending an arbitrary
differential of `S` to a wedge of differentials pulled back from `R` and taking the trace is the
same as appending its degree-one trace. This is part of [Stacks, Tag 0FLF]. -/
public theorem higherTrace_ιMulti_snoc (hp : p.Prime) [CharP Λ p] (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) (η : Fin t → Ω[R⁄Λ]) (ω : Ω[S⁄Λ]) :
    higherTrace (t := t) hp a e (exteriorPower.ιMulti S (t + 1)
        (Fin.snoc (fun j => KaehlerDifferential.map Λ Λ R S (η j)) ω)) =
      exteriorPower.ιMulti R (t + 1) (Fin.snoc η (higherTraceOne hp a e ω)) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · let := Module.subsingleton R (⋀[R]^(t + 1) Ω[R⁄Λ])
    exact Subsingleton.elim _ _
  set F : Ω[S⁄Λ] →ₗ[R] ⋀[R]^(t + 1) Ω[R⁄Λ] := (higherTrace (t := t) hp a e).comp
    ((wedgeSnocLinear (K := S) (fun j => KaehlerDifferential.map Λ Λ R S (η j))).restrictScalars R)
    with hF
  set G : Ω[S⁄Λ] →ₗ[R] ⋀[R]^(t + 1) Ω[R⁄Λ] :=
    (wedgeSnocLinear (K := R) η).comp (higherTraceOne hp a e) with hG
  suffices hFG : F = G from DFunLike.congr_fun hFG ω
  refine LinearMap.ext fun ω => ?_
  have hmem : ω ∈ Submodule.span S (Set.range (fun r : R => D Λ S (algebraMap R S r)) ∪
      {D Λ S (e (AdjoinRoot.root (X ^ p - C a)))}) := by
    rw [span_rootExtensionDifferentials]
    exact Submodule.mem_top
  suffices hall : ∀ s : S, F (s • ω) = G (s • ω) by simpa using hall 1
  induction hmem using Submodule.span_induction with
  | mem z hz =>
      rcases hz with ⟨r, rfl⟩ | rfl
      · intro s
        change F (s • D Λ S (algebraMap R S r)) = G (s • D Λ S (algebraMap R S r))
        rw [← KaehlerDifferential.map_D Λ Λ R S r]
        have hF' : F (s • KaehlerDifferential.map Λ Λ R S (D Λ R r)) = 0 :=
          higherTrace_snoc_smul_baseDifferential hp a e η r s
        have hG' : G (s • KaehlerDifferential.map Λ Λ R S (D Λ R r)) = 0 := by
          change (wedgeSnocLinear (K := R) η) (higherTraceOne hp a e
            (s • KaehlerDifferential.map Λ Λ R S (D Λ R r))) = 0
          rw [higherTraceOne_smul_baseDifferential, map_zero]
        rw [hF', hG']
      · intro s
        have hF' : F (s • D Λ S (e (AdjoinRoot.root (X ^ p - C a)))) =
            topRootCoeff hp a e s • exteriorPower.ιMulti R (t + 1) (Fin.snoc η (D Λ R a)) :=
          higherTrace_snoc_smul_rootDifferential hp a e η s
        have hG' : G (s • D Λ S (e (AdjoinRoot.root (X ^ p - C a)))) =
            topRootCoeff hp a e s • exteriorPower.ιMulti R (t + 1) (Fin.snoc η (D Λ R a)) := by
          change (wedgeSnocLinear (K := R) η) (higherTraceOne hp a e
            (s • D Λ S (e (AdjoinRoot.root (X ^ p - C a))))) = _
          rw [higherTraceOne_smul_rootDifferential hp a e s, map_smul]
          rfl
        rw [hF', hG']
  | zero =>
      intro s
      simp
  | add z w _ _ iz iw =>
      intro s
      simp only [smul_add, map_add, iz s, iw s]
  | smul c z _ ih =>
      intro s
      simpa [smul_smul] using ih (s * c)

/-- **The trace annihilates exact differentials**: the degree-one trace of `ds` vanishes for
every `s` in `S`. -/
public theorem higherTraceOne_D_eq_zero (hp : p.Prime) [CharP Λ p] (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) (s : S) :
    higherTraceOne hp a e (D Λ S s) = 0 := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · let := Module.subsingleton R (Ω[R⁄Λ])
    exact Subsingleton.elim _ _
  rw [eq_sum_repr_rootPow hp a e s, map_sum, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hlt := rootPowerBasis_lt hp a e i
  rw [Algebra.smul_def, Derivation.leibniz, ← KaehlerDifferential.map_D Λ Λ R S,
    Derivation.leibniz_pow, map_add, higherTraceOne_smul_baseDifferential, add_zero,
    IsScalarTower.algebraMap_smul S, map_smul, map_nsmul,
    higherTraceOne_rootPow hp a e _ (by omega), ite_eq_right (by have := hp.two_le; omega),
    smul_zero, smul_zero]

/-- Prepending a vector to a fixed wedge of `n` vectors, as a linear map. -/
private noncomputable def wedgeConsLinear {K M : Type*} [CommRing K] [AddCommGroup M]
    [Module K M] {n : ℕ} (η : Fin n → M) : M →ₗ[K] ⋀[K]^(n + 1) M where
  toFun m := exteriorPower.ιMulti K (n + 1) (Fin.cons m η)
  map_add' m₁ m₂ := (exteriorPower.ιMulti K _).toMultilinearMap.cons_add η m₁ m₂
  map_smul' c m := (exteriorPower.ιMulti K _).toMultilinearMap.cons_smul η c m

/-- Moving the last entry of a wedge to the front multiplies it by the sign of the cyclic
permutation of `Fin (n + 1)`. -/
private theorem ιMulti_snoc_eq_sign_cons {K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]
    {n : ℕ} (w : Fin n → M) (m : M) :
    exteriorPower.ιMulti K (n + 1) (Fin.snoc w m) =
      Equiv.Perm.sign (finRotate (n + 1)) •
        exteriorPower.ιMulti K (n + 1) (Fin.cons m w) := by
  have hrot : Fin.cons m w ∘ (finRotate (n + 1)) = Fin.snoc w m := by
    funext i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simp
    · rw [Function.comp_apply, finRotate_apply,
        show (Fin.castSucc k) + 1 = k.succ from by
          refine Fin.ext ?_
          rw [Fin.val_add_one_of_lt (Fin.castSucc_lt_last k)]
          simp,
        Fin.cons_succ, Fin.snoc_castSucc]
  rw [← hrot]
  exact AlternatingMap.map_perm ..

/-- **The trace is linear over the differential forms of `R`**, with the arbitrary differential of
`S` placed first. This is part of [Stacks, Tag 0FLF]. -/
public theorem higherTrace_ιMulti_cons (hp : p.Prime) [CharP Λ p] (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) (η : Fin t → Ω[R⁄Λ]) (ω : Ω[S⁄Λ]) :
    higherTrace (t := t) hp a e (exteriorPower.ιMulti S (t + 1)
        (Fin.cons ω (fun j => KaehlerDifferential.map Λ Λ R S (η j)))) =
      exteriorPower.ιMulti R (t + 1) (Fin.cons (higherTraceOne hp a e ω) η) := by
  have hcomm : ∀ z : ⋀[S]^(t + 1) Ω[S⁄Λ],
      higherTrace (t := t) hp a e (Equiv.Perm.sign (finRotate (t + 1)) • z) =
        Equiv.Perm.sign (finRotate (t + 1)) • higherTrace (t := t) hp a e z := fun z => by
    rw [Units.smul_def, Units.smul_def, map_zsmul]
  have hT := higherTrace_ιMulti_snoc hp a e η ω
  rw [ιMulti_snoc_eq_sign_cons (K := S), ιMulti_snoc_eq_sign_cons (K := R), hcomm] at hT
  exact MulAction.injective _ hT

omit [Algebra Λ R] [IsScalarTower Λ R S] in
private theorem comp_orderEmbedding_withTop_cases [LinearOrder R] {n : ℕ}
    (v : WithTop R → Ω[S⁄Λ]) (ω : Ω[S⁄Λ]) (htop : v ⊤ = ω)
    (hcoe : ∀ r : R, v r = D Λ S (algebraMap R S r)) (α : Fin (n + 1) ↪o WithTop R) :
    (∃ r : Fin n → R, v ∘ α = Fin.snoc (fun j => D Λ S (algebraMap R S (r j))) ω) ∨
      ∃ r : Fin (n + 1) → R, v ∘ α = fun j => D Λ S (algebraMap R S (r j)) := by
  by_cases hlast : α (Fin.last n) = ⊤
  · have hex : ∀ j : Fin n, ∃ y : R, (y : WithTop R) = α j.castSucc := fun j =>
      WithTop.ne_top_iff_exists.mp (ne_top_of_lt (α.strictMono (Fin.castSucc_lt_last j)))
    choose r hr using hex
    refine Or.inl ⟨r, funext fun j => Fin.lastCases ?_ (fun k => ?_) j⟩
    · rw [Function.comp_apply, hlast, Fin.snoc_last, htop]
    · rw [Function.comp_apply, Fin.snoc_castSucc, ← hr k, hcoe]
  · have hex : ∀ j : Fin (n + 1), ∃ y : R, (y : WithTop R) = α j := fun j =>
      WithTop.ne_top_iff_exists.mp fun hj => hlast (top_unique (hj ▸ α.monotone (Fin.le_last j)))
    choose r hr using hex
    exact Or.inr ⟨r, funext fun j => by rw [Function.comp_apply, ← hr j, hcoe]⟩

omit [Algebra Λ R] [IsScalarTower Λ R S] in
/-- Two linear maps out of `Ω^{n+1}_{S/Λ}` agree as soon as they agree on the scalar multiples of
the wedges of differentials of elements of `R`, with at most one `dx` appended. -/
private theorem exteriorExt_rootExtension {P : Type*} [AddCommGroup P] [Module Λ P] {n : ℕ}
    (a : R) (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) (F G : (⋀[S]^(n + 1) Ω[S⁄Λ]) →ₗ[Λ] P)
    (hbase : ∀ (s : S) (r : Fin (n + 1) → R),
      F (s • exteriorPower.ιMulti S (n + 1) (fun j => D Λ S (algebraMap R S (r j)))) =
        G (s • exteriorPower.ιMulti S (n + 1) (fun j => D Λ S (algebraMap R S (r j)))))
    (hroot : ∀ (s : S) (r : Fin n → R),
      F (s • exteriorPower.ιMulti S (n + 1) (Fin.snoc (fun j => D Λ S (algebraMap R S (r j)))
          (D Λ S (e (AdjoinRoot.root (X ^ p - C a)))))) =
        G (s • exteriorPower.ιMulti S (n + 1) (Fin.snoc (fun j => D Λ S (algebraMap R S (r j)))
          (D Λ S (e (AdjoinRoot.root (X ^ p - C a))))))) : F = G := by
  classical
  let : LinearOrder R := linearOrderOfSTO WellOrderingRel
  let v : WithTop R → Ω[S⁄Λ] :=
    WithTop.recTopCoe (D Λ S (e (AdjoinRoot.root (X ^ p - C a))))
      (fun r => D Λ S (algebraMap R S r))
  have hv : Submodule.span S (Set.range v) = ⊤ := by
    rw [← span_rootExtensionDifferentials (Λ := Λ) a e]
    congr 1
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      induction i using WithTop.recTopCoe with
      | top => exact Or.inr rfl
      | coe r => exact Or.inl ⟨r, rfl⟩
    · rintro (⟨r, rfl⟩ | rfl)
      · exact ⟨(r : WithTop R), rfl⟩
      · exact ⟨⊤, rfl⟩
  have hw := exteriorPower.ιMulti_family_span_of_span S (n := n + 1) hv
  have hgen : ∀ (α : Fin (n + 1) ↪o WithTop R) (s : S),
      F (s • exteriorPower.ιMulti S (n + 1) (v ∘ α)) =
        G (s • exteriorPower.ιMulti S (n + 1) (v ∘ α)) := by
    intro α s
    obtain ⟨r, hr⟩ | ⟨r, hr⟩ :=
      comp_orderEmbedding_withTop_cases v _ rfl (fun _ => rfl) α
    · rw [hr]
      exact hroot s r
    · rw [hr]
      exact hbase s r
  refine LinearMap.ext fun z => ?_
  have hz : z ∈ Submodule.span S (Set.range (exteriorPower.ιMulti_family S (n + 1) v)) := by
    rw [hw]
    exact Submodule.mem_top
  suffices h : ∀ s : S, F (s • z) = G (s • z) by simpa using h 1
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨z, rfl⟩ := hz
      exact hgen (Set.powersetCard.ofFinEmbEquiv.symm z)
  | zero => simp
  | add z w _ _ iz iw =>
      intro s
      simp [smul_add, iz, iw]
  | smul c z _ ih =>
      intro s
      simpa [smul_smul] using ih (s * c)

omit [Algebra Λ S] [IsScalarTower Λ R S] in
/-- **The trace of `S` over `R` is identically zero.** This is part of [Stacks, Tag 0FLF]. -/
public theorem trace_pthRoot_eq_zero (hp : p.Prime) [CharP Λ p] (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) : Algebra.trace R S = 0 := by
  classical
  have hpR : (p : R) = 0 := by
    have h := congrArg (algebraMap Λ R) (CharP.cast_eq_zero Λ p)
    rw [map_natCast, map_zero] at h
    exact h
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact LinearMap.ext fun y => Subsingleton.elim _ _
  have hdim : (rootPowerBasis hp a e).dim = p := rootPowerBasis_dim hp a e
  have hxp := pow_root_eq_algebraMap a e
  refine (rootPowerBasis hp a e).basis.ext fun k => ?_
  have hk := rootPowerBasis_lt hp a e k
  have hdiag : ∀ j : Fin (rootPowerBasis hp a e).dim,
      Algebra.leftMulMatrix (rootPowerBasis hp a e).basis
        ((rootPowerBasis hp a e).basis k) j j = if (k : ℕ) = 0 then 1 else 0 := by
    intro j
    have hj := rootPowerBasis_lt hp a e j
    rw [Algebra.leftMulMatrix_eq_repr_mul, rootPowerBasis_basis, rootPowerBasis_basis, ← pow_add]
    by_cases hlt : (k : ℕ) + (j : ℕ) < p
    · have hm : (⟨(k : ℕ) + (j : ℕ), by omega⟩ : Fin (rootPowerBasis hp a e).dim) = j ↔
          (k : ℕ) = 0 := by
        simp only [Fin.ext_iff]
        omega
      rw [(rootPowerBasis_basis hp a e ⟨(k : ℕ) + (j : ℕ), by omega⟩).symm,
        Module.Basis.repr_self, Finsupp.single_apply, if_congr hm rfl rfl]
    · have hexp : e (AdjoinRoot.root (X ^ p - C a)) ^ ((k : ℕ) + (j : ℕ)) =
          a • (rootPowerBasis hp a e).basis ⟨(k : ℕ) + (j : ℕ) - p, by omega⟩ := by
        rw [rootPowerBasis_basis, Algebra.smul_def, ← hxp, ← pow_add]
        congr 1
        exact (Nat.add_sub_cancel' (show p ≤ (k : ℕ) + (j : ℕ) by omega)).symm
      have hne : ¬((⟨(k : ℕ) + (j : ℕ) - p, by omega⟩ : Fin (rootPowerBasis hp a e).dim) = j) := by
        simp only [Fin.ext_iff]
        omega
      rw [hexp, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
        ite_eq_right hne, smul_zero, ite_eq_right (show ¬(k : ℕ) = 0 by omega)]
  simp only [Algebra.trace_eq_matrix_trace (rootPowerBasis hp a e).basis, Matrix.trace,
    Matrix.diag_apply, hdiag, Finset.sum_const, Finset.card_univ, Fintype.card_fin, hdim,
    LinearMap.zero_apply]
  by_cases hk0 : (k : ℕ) = 0 <;> simp [hk0, nsmul_eq_mul, hpR]

private theorem topRootCoeff_rootPow [Nontrivial R] (hp : p.Prime) (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) {k : ℕ} (hk : k < p) :
    topRootCoeff hp a e (e (AdjoinRoot.root (X ^ p - C a)) ^ k) = if k = p - 1 then 1 else 0 := by
  have hdim := rootPowerBasis_dim hp a e
  rw [show e (AdjoinRoot.root (X ^ p - C a)) ^ k =
      (rootPowerBasis hp a e).basis ⟨k, by omega⟩ from
        (rootPowerBasis_basis hp a e ⟨k, by omega⟩).symm, topRootCoeff,
    Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  refine if_congr ?_ rfl rfl
  rw [Fin.ext_iff]

private theorem higherTrace_deRhamDifferential_smul_baseForm (hp : p.Prime) [CharP Λ p] (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) (s : S) (r : Fin (t + 1) → R) :
    higherTrace (t := t + 1) hp a e (deRhamDifferential (A := Λ) (t + 1)
        (s • exteriorPower.ιMulti S (t + 1) (fun j => D Λ S (algebraMap R S (r j))))) =
      deRhamDifferential (A := Λ) (t + 1) (higherTrace (t := t) hp a e
        (s • exteriorPower.ιMulti S (t + 1) (fun j => D Λ S (algebraMap R S (r j))))) := by
  have hGval : deRhamDifferential (A := Λ) (t + 1) (higherTrace (t := t) hp a e
      (s • exteriorPower.ιMulti S (t + 1) (fun j => D Λ S (algebraMap R S (r j))))) = 0 := by
    rw [higherTrace_smul_ιMulti_D_algebraMap, map_zero]
  have hd := deRhamDifferential_smul_ιMulti_D (A := Λ) (B := S) (t + 1)
    (Fin.cons s (fun j => algebraMap R S (r j)))
  simp only [Fin.cons_zero, Fin.cons_succ] at hd
  have htup : (fun i => D Λ S ((Fin.cons s (fun j => algebraMap R S (r j)) :
        Fin (t + 1 + 1) → S) i)) =
      (Fin.cons (D Λ S s) (fun j => KaehlerDifferential.map Λ Λ R S (D Λ R (r j))) :
        Fin (t + 1 + 1) → Ω[S⁄Λ]) := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp
    · rw [Fin.cons_succ, Fin.cons_succ, KaehlerDifferential.map_D]
  rw [hGval, hd, htup, higherTrace_ιMulti_cons hp a e (fun j => D Λ R (r j)) (D Λ S s),
    higherTraceOne_D_eq_zero]
  exact (wedgeConsLinear (K := R) (fun j => D Λ R (r j))).map_zero

private theorem higherTrace_wedgeCons_smul_rootDifferential (hp : p.Prime) [CharP Λ p] (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) (r : Fin t → R) (c : S) :
    ((higherTrace (t := t + 1) hp a e).comp
      ((wedgeConsLinear (K := S) (Fin.snoc (fun j => D Λ S (algebraMap R S (r j)))
        (D Λ S (e (AdjoinRoot.root (X ^ p - C a)))))).restrictScalars R))
      (c • D Λ S (e (AdjoinRoot.root (X ^ p - C a)))) = 0 := by
  have hzero : exteriorPower.ιMulti S (t + 2)
      (Fin.cons (D Λ S (e (AdjoinRoot.root (X ^ p - C a))))
        (Fin.snoc (fun j => D Λ S (algebraMap R S (r j)))
          (D Λ S (e (AdjoinRoot.root (X ^ p - C a)))))) = 0 := by
    refine AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := Fin.last (t + 1)) ?_ ?_
    · rw [Fin.cons_zero, ← Fin.succ_last, Fin.cons_succ, Fin.snoc_last]
    · simp [Fin.ext_iff]
  change higherTrace (t := t + 1) hp a e ((wedgeConsLinear (K := S) _)
    (c • D Λ S (e (AdjoinRoot.root (X ^ p - C a))))) = 0
  rw [map_smul]
  change higherTrace (t := t + 1) hp a e (c • exteriorPower.ιMulti S (t + 2)
    (Fin.cons (D Λ S (e (AdjoinRoot.root (X ^ p - C a))))
      (Fin.snoc (fun j => D Λ S (algebraMap R S (r j)))
        (D Λ S (e (AdjoinRoot.root (X ^ p - C a))))))) = 0
  rw [hzero, smul_zero, map_zero]

private theorem higherTrace_wedgeCons_rootPow_smul_baseDifferential (hp : p.Prime) [CharP Λ p]
    (a : R) (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) (r : Fin t → R) (c : R) (k : ℕ) :
    ((higherTrace (t := t + 1) hp a e).comp
      ((wedgeConsLinear (K := S) (Fin.snoc (fun j => D Λ S (algebraMap R S (r j)))
        (D Λ S (e (AdjoinRoot.root (X ^ p - C a)))))).restrictScalars R))
      (e (AdjoinRoot.root (X ^ p - C a)) ^ k • KaehlerDifferential.map Λ Λ R S (D Λ R c)) =
      exteriorPower.ιMulti R (t + 2) (Fin.snoc (Fin.cons (D Λ R c) (fun j => D Λ R (r j)))
        (higherTraceOne hp a e (e (AdjoinRoot.root (X ^ p - C a)) ^ k •
          D Λ S (e (AdjoinRoot.root (X ^ p - C a)))))) := by
  have hbase := D_algebraMap_eq_map_D (Λ := Λ) (S := S) r
  change higherTrace (t := t + 1) hp a e ((wedgeConsLinear (K := S) _)
    (e (AdjoinRoot.root (X ^ p - C a)) ^ k •
      KaehlerDifferential.map Λ Λ R S (D Λ R c))) = _
  rw [map_smul]
  change higherTrace (t := t + 1) hp a e (e (AdjoinRoot.root (X ^ p - C a)) ^ k •
    exteriorPower.ιMulti S (t + 2) (Fin.cons (KaehlerDifferential.map Λ Λ R S (D Λ R c))
      (Fin.snoc (fun j => D Λ S (algebraMap R S (r j)))
        (D Λ S (e (AdjoinRoot.root (X ^ p - C a))))))) = _
  rw [hbase, Fin.cons_snoc_eq_snoc_cons]
  change higherTrace (t := t + 1) hp a e (e (AdjoinRoot.root (X ^ p - C a)) ^ k •
    (wedgeSnocLinear (K := S) (Fin.cons (KaehlerDifferential.map Λ Λ R S (D Λ R c))
      (fun j => KaehlerDifferential.map Λ Λ R S (D Λ R (r j)))))
        (D Λ S (e (AdjoinRoot.root (X ^ p - C a))))) = _
  rw [← map_smul]
  change higherTrace (t := t + 1) hp a e (exteriorPower.ιMulti S (t + 2) (Fin.snoc
    (Fin.cons (KaehlerDifferential.map Λ Λ R S (D Λ R c))
      (fun j => KaehlerDifferential.map Λ Λ R S (D Λ R (r j))))
    (e (AdjoinRoot.root (X ^ p - C a)) ^ k •
      D Λ S (e (AdjoinRoot.root (X ^ p - C a)))))) = _
  rw [show (Fin.cons (KaehlerDifferential.map Λ Λ R S (D Λ R c))
        (fun j => KaehlerDifferential.map Λ Λ R S (D Λ R (r j))) :
          Fin (t + 1) → Ω[S⁄Λ]) =
      fun j => KaehlerDifferential.map Λ Λ R S
        ((Fin.cons (D Λ R c) (fun j => D Λ R (r j)) : Fin (t + 1) → Ω[R⁄Λ]) j) from by
    funext j
    refine Fin.cases ?_ (fun l => ?_) j <;> simp]
  exact higherTrace_ιMulti_snoc hp a e (Fin.cons (D Λ R c) (fun j => D Λ R (r j))) _

private theorem higherTrace_wedgeCons_D [Nontrivial R] (hp : p.Prime) [CharP Λ p] (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) (r : Fin t → R) (y : S) :
    ((higherTrace (t := t + 1) hp a e).comp
      ((wedgeConsLinear (K := S) (Fin.snoc (fun j => D Λ S (algebraMap R S (r j)))
        (D Λ S (e (AdjoinRoot.root (X ^ p - C a)))))).restrictScalars R)) (D Λ S y) =
      (wedgeConsLinear (K := R) (fun j => D Λ R ((Fin.snoc r a : Fin (t + 1) → R) j)))
        (D Λ R (topRootCoeff hp a e y)) := by
  set W : Ω[S⁄Λ] →ₗ[R] ⋀[R]^(t + 2) Ω[R⁄Λ] := (higherTrace (t := t + 1) hp a e).comp
    ((wedgeConsLinear (K := S) (Fin.snoc (fun j => D Λ S (algebraMap R S (r j)))
      (D Λ S (e (AdjoinRoot.root (X ^ p - C a)))))).restrictScalars R)
  have hWdx : ∀ c : S, W (c • D Λ S (e (AdjoinRoot.root (X ^ p - C a)))) = 0 :=
    higherTrace_wedgeCons_smul_rootDifferential hp a e r
  have hdim := rootPowerBasis_dim hp a e
  rw [eq_sum_repr_rootPow hp a e y, map_sum, map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hk := rootPowerBasis_lt hp a e i
  set c := (rootPowerBasis hp a e).basis.repr y i
  set k := (i : ℕ)
  rw [Algebra.smul_def, Derivation.leibniz, Derivation.leibniz_pow,
    ← KaehlerDifferential.map_D Λ Λ R S, map_add,
    show (algebraMap R S c) • (k • e (AdjoinRoot.root (X ^ p - C a)) ^ (k - 1) •
          D Λ S (e (AdjoinRoot.root (X ^ p - C a)))) =
        (algebraMap R S c * (k : S) * e (AdjoinRoot.root (X ^ p - C a)) ^ (k - 1)) •
          D Λ S (e (AdjoinRoot.root (X ^ p - C a))) from by
      rw [← Nat.cast_smul_eq_nsmul S, smul_smul, smul_smul],
    hWdx, zero_add]
  have hsecond : W (e (AdjoinRoot.root (X ^ p - C a)) ^ k •
      KaehlerDifferential.map Λ Λ R S (D Λ R c)) =
      exteriorPower.ιMulti R (t + 2) (Fin.snoc (Fin.cons (D Λ R c) (fun j => D Λ R (r j)))
        (higherTraceOne hp a e (e (AdjoinRoot.root (X ^ p - C a)) ^ k •
          D Λ S (e (AdjoinRoot.root (X ^ p - C a)))))) :=
    higherTrace_wedgeCons_rootPow_smul_baseDifferential hp a e r c k
  have hRHS : topRootCoeff hp a e
      (algebraMap R S c * e (AdjoinRoot.root (X ^ p - C a)) ^ k) =
      if k = p - 1 then c else 0 := by
    rw [← Algebra.smul_def, map_smul, topRootCoeff_rootPow hp a e hk]
    split_ifs <;> simp
  rw [hsecond, higherTraceOne_rootPow hp a e k hk, hRHS]
  by_cases hkp : k = p - 1
  · rw [ite_eq_left hkp, ite_eq_left hkp]
    change exteriorPower.ιMulti R (t + 2)
        (Fin.snoc (Fin.cons (D Λ R c) (fun j => D Λ R (r j))) (D Λ R a)) =
      exteriorPower.ιMulti R (t + 2) (Fin.cons (D Λ R c)
        (fun j => D Λ R ((Fin.snoc r a : Fin (t + 1) → R) j)))
    rw [← snoc_D_eq (Λ := Λ), ← Fin.cons_snoc_eq_snoc_cons]
  · rw [ite_eq_right hkp, ite_eq_right hkp, map_zero,
      show exteriorPower.ιMulti R (t + 2)
          (Fin.snoc (Fin.cons (D Λ R c) (fun j => D Λ R (r j))) 0) = 0 from
        (wedgeSnocLinear (K := R) (Fin.cons (D Λ R c) (fun j => D Λ R (r j)))).map_zero]
    exact ((wedgeConsLinear (K := R)
      (fun j => D Λ R ((Fin.snoc r a : Fin (t + 1) → R) j))).map_zero).symm

private theorem higherTrace_deRhamDifferential_smul_rootForm [Nontrivial R] (hp : p.Prime)
    [CharP Λ p] (a : R) (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) (s : S) (r : Fin t → R) :
    higherTrace (t := t + 1) hp a e (deRhamDifferential (A := Λ) (t + 1)
        (s • exteriorPower.ιMulti S (t + 1) (Fin.snoc (fun j => D Λ S (algebraMap R S (r j)))
          (D Λ S (e (AdjoinRoot.root (X ^ p - C a))))))) =
      deRhamDifferential (A := Λ) (t + 1) (higherTrace (t := t) hp a e
        (s • exteriorPower.ιMulti S (t + 1) (Fin.snoc (fun j => D Λ S (algebraMap R S (r j)))
          (D Λ S (e (AdjoinRoot.root (X ^ p - C a))))))) := by
  have hbase := D_algebraMap_eq_map_D (Λ := Λ) (S := S) r
  have hGval : deRhamDifferential (A := Λ) (t + 1) (higherTrace (t := t) hp a e
      (s • exteriorPower.ιMulti S (t + 1) (Fin.snoc (fun j => D Λ S (algebraMap R S (r j)))
        (D Λ S (e (AdjoinRoot.root (X ^ p - C a))))))) =
      (wedgeConsLinear (K := R) (fun j => D Λ R ((Fin.snoc r a : Fin (t + 1) → R) j)))
        (D Λ R (topRootCoeff hp a e s)) := by
    rw [hbase]
    change deRhamDifferential (A := Λ) (t + 1) (higherTrace (t := t) hp a e
      (s • (wedgeSnocLinear (K := S) (fun j => KaehlerDifferential.map Λ Λ R S (D Λ R (r j))))
        (D Λ S (e (AdjoinRoot.root (X ^ p - C a)))))) = _
    rw [← map_smul]
    change deRhamDifferential (A := Λ) (t + 1) (higherTrace (t := t) hp a e
      (exteriorPower.ιMulti S (t + 1)
        (Fin.snoc (fun j => KaehlerDifferential.map Λ Λ R S (D Λ R (r j)))
          (s • D Λ S (e (AdjoinRoot.root (X ^ p - C a))))))) = _
    rw [higherTrace_snoc_smul_rootDifferential hp a e (fun j => D Λ R (r j)) s, snoc_D_eq]
    have hd := deRhamDifferential_smul_ιMulti_D (A := Λ) (B := R) (t + 1)
      (Fin.cons (topRootCoeff hp a e s) (Fin.snoc r a))
    simp only [Fin.cons_zero, Fin.cons_succ] at hd
    rw [hd]
    change _ = exteriorPower.ιMulti R (t + 2) (Fin.cons (D Λ R (topRootCoeff hp a e s))
      (fun j => D Λ R ((Fin.snoc r a : Fin (t + 1) → R) j)))
    congr 1
    funext i
    refine Fin.cases ?_ (fun l => ?_) i <;> simp
  have htup : (fun i => D Λ S ((Fin.snoc (fun j => algebraMap R S (r j))
        (e (AdjoinRoot.root (X ^ p - C a))) : Fin (t + 1) → S) i)) =
      Fin.snoc (fun j => D Λ S (algebraMap R S (r j)))
        (D Λ S (e (AdjoinRoot.root (X ^ p - C a)))) := by
    funext i
    refine Fin.lastCases ?_ (fun l => ?_) i <;> simp
  have hd := deRhamDifferential_smul_ιMulti_D (A := Λ) (B := S) (t + 1)
    (Fin.cons s (Fin.snoc (fun j => algebraMap R S (r j))
      (e (AdjoinRoot.root (X ^ p - C a)))))
  simp only [Fin.cons_zero, Fin.cons_succ] at hd
  rw [htup] at hd
  have htup2 : (fun i => D Λ S ((Fin.cons s (Fin.snoc (fun j => algebraMap R S (r j))
        (e (AdjoinRoot.root (X ^ p - C a)))) : Fin (t + 1 + 1) → S) i)) =
      (Fin.cons (D Λ S s) (Fin.snoc (fun j => D Λ S (algebraMap R S (r j)))
        (D Λ S (e (AdjoinRoot.root (X ^ p - C a))))) : Fin (t + 1 + 1) → Ω[S⁄Λ]) := by
    funext i
    refine Fin.cases ?_ (fun l => ?_) i
    · simp
    · rw [Fin.cons_succ, Fin.cons_succ]
      exact congrFun htup l
  rw [hGval, hd, htup2]
  exact higherTrace_wedgeCons_D hp a e r s

/-- **The trace commutes with the de Rham differential** in positive degrees:
`Tr(dω) = d(Tr ω)` for `ω` in `Ω^{t+1}_{S/Λ}`. This is the case of [Stacks, Tag 0FLC] for a
purely inseparable extension of degree `p`. -/
public theorem higherTrace_deRhamDifferential (hp : p.Prime) [CharP Λ p] (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) (ω : ⋀[S]^(t + 1) Ω[S⁄Λ]) :
    higherTrace (t := t + 1) hp a e (deRhamDifferential (A := Λ) (t + 1) ω) =
      deRhamDifferential (A := Λ) (t + 1) (higherTrace (t := t) hp a e ω) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · let := Module.subsingleton R (⋀[R]^(t + 1 + 1) Ω[R⁄Λ])
    exact Subsingleton.elim _ _
  set F : (⋀[S]^(t + 1) Ω[S⁄Λ]) →ₗ[Λ] ⋀[R]^(t + 2) Ω[R⁄Λ] :=
    ((higherTrace (t := t + 1) hp a e).restrictScalars Λ).comp
      (deRhamDifferential (A := Λ) (t + 1))
  set G : (⋀[S]^(t + 1) Ω[S⁄Λ]) →ₗ[Λ] ⋀[R]^(t + 2) Ω[R⁄Λ] :=
    (deRhamDifferential (A := Λ) (t + 1)).comp
      ((higherTrace (t := t) hp a e).restrictScalars Λ)
  suffices hFG : F = G from DFunLike.congr_fun hFG ω
  exact exteriorExt_rootExtension a e F G
    (higherTrace_deRhamDifferential_smul_baseForm hp a e)
    (higherTrace_deRhamDifferential_smul_rootForm hp a e)

/-- **The trace annihilates the differentials of degree zero**: the trace of the de Rham
differential of a form of degree zero vanishes. -/
public theorem higherTrace_deRhamDifferential_zero (hp : p.Prime) [CharP Λ p] (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) (ξ : ⋀[S]^0 Ω[S⁄Λ]) :
    higherTrace (t := 0) hp a e (deRhamDifferential (A := Λ) 0 ξ) = 0 := by
  have hmem : ξ ∈ Submodule.span S (Set.range (exteriorPower.ιMulti S 0 (M := Ω[S⁄Λ]))) := by
    rw [exteriorPower.ιMulti_span]
    exact Submodule.mem_top
  suffices hall : ∀ s : S,
      higherTrace (t := 0) hp a e (deRhamDifferential (A := Λ) 0 (s • ξ)) = 0 by
    simpa using hall 1
  induction hmem using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨v, rfl⟩ := hz
      intro s
      have hd := deRhamDifferential_smul_ιMulti_D (A := Λ) (B := S) 0 (fun _ : Fin 1 => s)
      rw [show (fun i : Fin 0 => D Λ S ((fun _ : Fin 1 => s) i.succ)) = v from
        funext fun j => j.elim0] at hd
      rw [hd]
      have h1 := higherTraceOne_apply hp a e (D Λ S s)
      rw [higherTraceOne_D_eq_zero hp a e s] at h1
      have h2 := congrArg (exteriorPower.oneEquiv R (Ω[R⁄Λ])).symm h1.symm
      rw [LinearEquiv.symm_apply_apply, map_zero] at h2
      exact h2
  | zero =>
    intro s
    simp
  | add z w _ _ iz iw =>
    intro s
    simp only [smul_add, map_add, iz s, iw s, add_zero]
  | smul c z _ ih =>
    intro s
    simpa [smul_smul] using ih (s * c)

/-! ### The computation of Example 0FLD for `x ^ d - a` -/

/-- **The computation of Example 0FLD for `B = A[x]/(x ^ d - a)`.**  A map
`θ : Ω_{B/k} → Ω_{A/k}` satisfying the projection formula `θ(b · ω) = Trace_{B/A}(b) · ω` for `ω`
pulled back from `A` sends `x ^ (d - 1) dx` to `da`, provided `Ω_{A/k}` has no `d`-torsion. -/
public theorem eq_D_of_smul_map_eq_trace_smul {k A B : Type*} [CommRing k] [CommRing A]
    [CommRing B] [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B] {d : ℕ}
    (hd : 0 < d) (a : A) (e : AdjoinRoot (X ^ d - C a) ≃ₐ[A] B) (θ : Ω[B⁄k] →ₗ[A] Ω[A⁄k])
    (hθ : ∀ (b : B) (ω : Ω[A⁄k]),
      θ (b • KaehlerDifferential.map k k A B ω) = Algebra.trace A B b • ω)
    (htors : ∀ ω : Ω[A⁄k], (d : A) • ω = 0 → ω = 0) :
    θ (e (AdjoinRoot.root (X ^ d - C a)) ^ (d - 1) • D k B (e (AdjoinRoot.root (X ^ d - C a)))) =
      D k A a := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · let := Module.subsingleton A (Ω[A⁄k])
    exact Subsingleton.elim _ _
  set x := e (AdjoinRoot.root (X ^ d - C a)) with hxdef
  have hmonic := Polynomial.monic_X_pow_sub_C a hd.ne'
  set pb : PowerBasis A B := (AdjoinRoot.powerBasis' hmonic).map e with hpb
  have : Module.Free A B := Module.Free.of_basis pb.basis
  have : Module.Finite A B := Module.Finite.of_basis pb.basis
  have hrank : Module.finrank A B = d := by
    rw [pb.finrank, hpb, PowerBasis.map, AdjoinRoot.powerBasis'_dim,
      Polynomial.natDegree_X_pow_sub_C]
  have hxd : x ^ d = algebraMap A B a := pow_root_eq_algebraMap a e
  have htr : Algebra.trace A B 1 = (d : A) := by
    rw [← map_one (algebraMap A B), Algebra.trace_algebraMap, hrank, nsmul_eq_mul, mul_one]
  have hkey : (d : A) • θ (x ^ (d - 1) • D k B x) = (d : A) • D k A a := by
    have h := hθ 1 (D k A a)
    rw [one_smul, KaehlerDifferential.map_D, ← hxd, Derivation.leibniz_pow, htr] at h
    rw [← h, Nat.cast_smul_eq_nsmul, map_nsmul]
  exact sub_eq_zero.mp (htors _ (by rw [smul_sub, hkey, sub_self]))

/-- The differentials of a polynomial ring over a domain of characteristic zero have no torsion
by positive integers: `Ω_{R[T]/R}` is free of rank one over `R[T]`. -/
public theorem polynomial_kaehler_eq_zero_of_natCast_smul {R : Type*} [CommRing R] [IsDomain R]
    [CharZero R] {d : ℕ} (hd : 0 < d) (ω : Ω[R[X]⁄R]) (h : ((d : R[X])) • ω = 0) : ω = 0 := by
  have h' := congrArg (KaehlerDifferential.polynomialEquiv (R := R)) h
  rw [map_smul, map_zero, smul_eq_mul, mul_eq_zero] at h'
  rcases h' with h' | h'
  · exact absurd h' (by exact_mod_cast hd.ne')
  · exact (KaehlerDifferential.polynomialEquiv (R := R)).injective (h'.trans (map_zero _).symm)

section Complex

open CategoryTheory

universe u

variable {p : ℕ} {Λ R S : Type u} [CommRing Λ] [CommRing R] [CommRing S]
  [Algebra Λ R] [Algebra Λ S] [Algebra R S] [IsScalarTower Λ R S]

/-- The degree-`i` component of the trace map of de Rham complexes: zero in degree zero and the
trace on differential forms in every positive degree. -/
@[expose] public noncomputable def higherTraceComplexComponent (hp : p.Prime) [CharP Λ p] (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) (i : ℕ) :
    (deRhamComplex Λ S).X i ⟶ (deRhamComplex Λ R).X i :=
  match i with
  | 0 => ModuleCat.ofHom 0
  | (n + 1) => ModuleCat.ofHom ((higherTrace (t := n) hp a e).restrictScalars Λ)

/-- **The trace on differential forms as a map of de Rham complexes**
`Θ_{S/R} : Ω^•_{S/Λ} ⟶ Ω^•_{R/Λ}`, for `𝐅_p ⊂ Λ ⊂ R ⊂ S` with `S` isomorphic to
`R[x]/(x ^ p - a)`.  Its degree-zero component is zero — which is the trace `Trace_{S/R}` of `S`
over `R`, by `KaehlerDifferential.trace_pthRoot_eq_zero` — and its component in degree `t + 1`
is the trace `Tr` of [Stacks, Tag 0AX5]. This is the case of [Stacks, Tag 0FLC] for a purely
inseparable extension of degree `p`. -/
@[expose]
public noncomputable def higherTraceComplexMap (hp : p.Prime) [CharP Λ p] (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) : deRhamComplex Λ S ⟶ deRhamComplex Λ R where
  f := higherTraceComplexComponent hp a e
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    cases i with
    | zero =>
        refine ModuleCat.hom_ext ?_
        rw [ModuleCat.hom_comp, ModuleCat.hom_comp]
        refine LinearMap.ext fun ξ => ?_
        simp only [higherTraceComplexComponent, deRhamComplex_d]
        change deRhamDifferential (A := Λ) (B := R) 0 (0 : ⋀[R]^0 Ω[R⁄Λ]) = _
        rw [map_zero]
        exact (higherTrace_deRhamDifferential_zero hp a e ξ).symm
    | succ n =>
        refine ModuleCat.hom_ext ?_
        rw [ModuleCat.hom_comp, ModuleCat.hom_comp]
        refine LinearMap.ext fun ω => ?_
        simp only [higherTraceComplexComponent, deRhamComplex_d]
        exact (higherTrace_deRhamDifferential hp a e ω).symm

/-- The degree-zero component of the trace map of de Rham complexes is zero. -/
public theorem higherTraceComplexMap_f_zero (hp : p.Prime) [CharP Λ p] (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) :
    (higherTraceComplexMap (Λ := Λ) hp a e).f 0 = 0 := ModuleCat.ofHom_zero

/-- In degree `n + 1` the trace map of de Rham complexes is the trace on differential forms. -/
public theorem higherTraceComplexMap_f_succ (hp : p.Prime) [CharP Λ p] (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) (n : ℕ) :
    (higherTraceComplexMap (Λ := Λ) hp a e).f (n + 1) =
      ModuleCat.ofHom ((higherTrace (t := n) (Λ := Λ) hp a e).restrictScalars Λ) := rfl

/-- The trace kills every multiple of a form pulled back from `R`, in positive degree. -/
private theorem higherTrace_smul_mapExteriorPower (hp : p.Prime) [CharP Λ p] (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) (n : ℕ) (s : S) (α : ⋀[R]^(n + 1) Ω[R⁄Λ]) :
    higherTrace (t := n) hp a e (s • mapExteriorPower Λ R S (n + 1) α) = 0 := by
  set F : ⋀[R]^(n + 1) Ω[R⁄Λ] →ₗ[R] ⋀[R]^(n + 1) Ω[R⁄Λ] :=
    (higherTrace (t := n) hp a e).comp
      (((LinearMap.lsmul S (⋀[S]^(n + 1) Ω[S⁄Λ]) s).restrictScalars R).comp
        (mapExteriorPower Λ R S (n + 1))) with hF
  suffices h : F = 0 from DFunLike.congr_fun h α
  refine exteriorPower.linearMap_ext (AlternatingMap.ext fun η => ?_)
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.zero_apply, hF, LinearMap.comp_apply,
    LinearMap.coe_restrictScalars, LinearMap.lsmul_apply, mapExteriorPower_ιMulti]
  exact higherTrace_smul_baseForm hp a e s η

/-- **The trace is linear over the differential forms of `R`**, in full generality in positive
degree: `Tr(a ∧ b) = a ∧ Tr(b)` for `a ∈ Ω^i_{R/Λ}` (pulled back to `S`) and
`b ∈ Ω^{t+1}_{S/Λ}`. -/
private theorem higherTrace_wedgeMul (hp : p.Prime) [CharP Λ p] (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) (i t : ℕ) (α : ⋀[R]^i Ω[R⁄Λ])
    (β : ⋀[S]^(t + 1) Ω[S⁄Λ]) :
    higherTrace (t := i + t) hp a e
        (exteriorPower.wedgeMul i (t + 1) (mapExteriorPower Λ R S i α) β) =
      exteriorPower.wedgeMul i (t + 1) α (higherTrace (t := t) hp a e β) := by
  set F₁ : ⋀[R]^i Ω[R⁄Λ] →ₗ[R] ⋀[R]^(i + t + 1) Ω[R⁄Λ] :=
    (higherTrace (t := i + t) hp a e).comp
      ((((exteriorPower.wedgeMul (R := S) (M := Ω[S⁄Λ]) i (t + 1)).flip β).restrictScalars
        R).comp (mapExteriorPower Λ R S i)) with hF₁
  set F₂ : ⋀[R]^i Ω[R⁄Λ] →ₗ[R] ⋀[R]^(i + t + 1) Ω[R⁄Λ] :=
    (exteriorPower.wedgeMul (R := R) (M := Ω[R⁄Λ]) i (t + 1)).flip
      (higherTrace (t := t) hp a e β) with hF₂
  suffices h : F₁ = F₂ from DFunLike.congr_fun h α
  refine exteriorPower.linearMap_ext (AlternatingMap.ext fun η => ?_)
  simp only [LinearMap.compAlternatingMap_apply, hF₁, hF₂, LinearMap.comp_apply,
    LinearMap.coe_restrictScalars, LinearMap.flip_apply, mapExteriorPower_ιMulti]
  clear hF₁ hF₂ F₁ F₂
  set G₁ : ⋀[S]^(t + 1) Ω[S⁄Λ] →ₗ[Λ] ⋀[R]^(i + t + 1) Ω[R⁄Λ] :=
    ((higherTrace (t := i + t) hp a e).restrictScalars Λ).comp
      ((exteriorPower.wedgeMul (R := S) (M := Ω[S⁄Λ]) i (t + 1)
        (exteriorPower.ιMulti S i fun j => KaehlerDifferential.map Λ Λ R S (η j))).restrictScalars
          Λ) with hG₁
  set G₂ : ⋀[S]^(t + 1) Ω[S⁄Λ] →ₗ[Λ] ⋀[R]^(i + t + 1) Ω[R⁄Λ] :=
    ((exteriorPower.wedgeMul (R := R) (M := Ω[R⁄Λ]) i (t + 1)
        (exteriorPower.ιMulti R i η)).restrictScalars Λ).comp
      ((higherTrace (t := t) hp a e).restrictScalars Λ) with hG₂
  suffices h : G₁ = G₂ from DFunLike.congr_fun h β
  have happend : ∀ {m : ℕ} (ζ : Fin m → Ω[R⁄Λ]),
      Fin.append (fun j => KaehlerDifferential.map Λ Λ R S (η j))
          (fun j => KaehlerDifferential.map Λ Λ R S (ζ j)) =
        fun j => KaehlerDifferential.map Λ Λ R S (Fin.append η ζ j) := fun ζ => by
    funext j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;> simp [Fin.append_left, Fin.append_right]
  refine exteriorExt_rootExtension a e G₁ G₂ ?_ ?_
  · intro s r
    have h₂ : G₂ (s • exteriorPower.ιMulti S (t + 1) fun j => D Λ S (algebraMap R S (r j))) =
        0 := by
      change exteriorPower.wedgeMul i (t + 1) (exteriorPower.ιMulti R i η)
        (higherTrace (t := t) hp a e
          (s • exteriorPower.ιMulti S (t + 1) fun j => D Λ S (algebraMap R S (r j)))) = 0
      rw [higherTrace_smul_ιMulti_D_algebraMap, map_zero]
    rw [h₂]
    change higherTrace (t := i + t) hp a e (exteriorPower.wedgeMul i (t + 1)
      (exteriorPower.ιMulti S i fun j => KaehlerDifferential.map Λ Λ R S (η j))
      (s • exteriorPower.ιMulti S (t + 1) fun j => D Λ S (algebraMap R S (r j)))) = 0
    rw [map_smul, exteriorPower.wedgeMul_ιMulti, D_algebraMap_eq_map_D, happend]
    exact higherTrace_smul_baseForm (t := i + t) hp a e s
      (Fin.append (m := i) (n := t + 1) η fun j => D Λ R (r j))
  · intro s r
    set x := e (AdjoinRoot.root (X ^ p - C a))
    change higherTrace (t := i + t) hp a e (exteriorPower.wedgeMul i (t + 1)
        (exteriorPower.ιMulti S i fun j => KaehlerDifferential.map Λ Λ R S (η j))
        (s • exteriorPower.ιMulti S (t + 1)
          (Fin.snoc (fun j => D Λ S (algebraMap R S (r j))) (D Λ S x)))) =
      exteriorPower.wedgeMul i (t + 1) (exteriorPower.ιMulti R i η)
        (higherTrace (t := t) hp a e (s • exteriorPower.ιMulti S (t + 1)
          (Fin.snoc (fun j => D Λ S (algebraMap R S (r j))) (D Λ S x))))
    rw [smul_ιMulti_snoc, D_algebraMap_eq_map_D, higherTrace_ιMulti_snoc,
      exteriorPower.wedgeMul_ιMulti, exteriorPower.wedgeMul_ιMulti, Fin.append_snoc,
      Fin.append_snoc, happend]
    exact higherTrace_ιMulti_snoc (t := i + t) hp a e
      (Fin.append (m := i) (n := t) η fun j => D Λ R (r j)) (s • D Λ S x)

/-- A wedge with a form of degree zero is a scalar multiple. -/
private theorem wedgeMul_zero_eq_smul {K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]
    (n : ℕ) (x : ⋀[K]^n M) (β : ⋀[K]^0 M) :
    exteriorPower.wedgeMul n 0 x β = exteriorPower.zeroEquiv K M β • x := by
  have hmem : β ∈ Submodule.span K (Set.range (exteriorPower.ιMulti K 0 (M := M))) := by
    rw [exteriorPower.ιMulti_span]
    exact Submodule.mem_top
  induction hmem using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨v, rfl⟩ := hz
      rw [exteriorPower.zeroEquiv_ιMulti, one_smul]
      exact Subtype.ext (by
        simp only [exteriorPower.wedgeMul_apply_coe, exteriorPower.ιMulti_apply_coe,
          ExteriorAlgebra.ιMulti_zero_apply, mul_one])
  | zero => simp
  | add z w _ _ iz iw => simp only [map_add, iz, iw, add_smul]
  | smul c z _ ih => simp only [map_smul, ih, smul_eq_mul, mul_smul]

/-- **`Θ_{S/R}` is linear over the differential forms of `R`**:
`Θ_{S/R}(a ∧ b) = a ∧ Θ_{S/R}(b)` for every `a ∈ Ω^i_{R/Λ}`, read in `Ω^i_{S/Λ}` through the
pullback of forms `KaehlerDifferential.mapExteriorPower`, and every `b ∈ Ω^j_{S/Λ}`. This is
part of [Stacks, Tag 0FLF]. -/
public theorem higherTraceComplexMap_wedgeMul (hp : p.Prime) [CharP Λ p] (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) (i j : ℕ) (α : ⋀[R]^i Ω[R⁄Λ])
    (β : ⋀[S]^j Ω[S⁄Λ]) :
    ((higherTraceComplexMap (Λ := Λ) hp a e).f (i + j)).hom
        (exteriorPower.wedgeMul i j (mapExteriorPower Λ R S i α) β) =
      exteriorPower.wedgeMul i j α (((higherTraceComplexMap (Λ := Λ) hp a e).f j).hom β) := by
  have h0 : ∀ γ : ⋀[S]^0 Ω[S⁄Λ], ((higherTraceComplexMap (Λ := Λ) hp a e).f 0).hom γ = 0 :=
    fun γ => by rw [higherTraceComplexMap_f_zero]; rfl
  cases j with
  | zero =>
      have hR : exteriorPower.wedgeMul i 0 α (((higherTraceComplexMap (Λ := Λ) hp a e).f 0).hom β)
          = 0 := by
        rw [h0]
        exact (exteriorPower.wedgeMul i 0 α).map_zero
      have hL : ((higherTraceComplexMap (Λ := Λ) hp a e).f i).hom
          (exteriorPower.zeroEquiv S (Ω[S⁄Λ]) β • mapExteriorPower Λ R S i α) = 0 := by
        cases i with
        | zero => exact h0 _
        | succ n => exact higherTrace_smul_mapExteriorPower hp a e n _ α
      rw [hR]
      exact (congrArg ((higherTraceComplexMap (Λ := Λ) hp a e).f (i + 0)).hom
        (wedgeMul_zero_eq_smul i _ β)).trans hL
  | succ t => exact higherTrace_wedgeMul hp a e i t α β

/-- The element of degree zero attached to a scalar is that scalar, read in the exterior
algebra. -/
private theorem coe_zeroEquiv_symm {K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]
    (c : K) : (((exteriorPower.zeroEquiv K M).symm c : ⋀[K]^0 M) : ExteriorAlgebra K M) =
      algebraMap K (ExteriorAlgebra K M) c := by
  rw [exteriorPower.zeroEquiv_symm_apply, Submodule.coe_smul, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.ιMulti_zero_apply, Algebra.algebraMap_eq_smul_one]

/-- A wedge with a scalar in degree zero on the left is a scalar multiple. -/
private theorem wedgeMul_zeroEquiv_symm {K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]
    (c : K) (y : ⋀[K]^1 M) :
    exteriorPower.wedgeMul 0 1 ((exteriorPower.zeroEquiv K M).symm c) y = c • y :=
  Subtype.ext (by
    rw [exteriorPower.wedgeMul_apply_coe, coe_zeroEquiv_symm, ← Algebra.smul_def]
    rfl)

/-- The pullback to `S` of a form of degree zero on `R`. -/
private theorem mapExteriorPower_zeroEquiv_symm (c : R) :
    mapExteriorPower Λ R S 0 ((exteriorPower.zeroEquiv R (Ω[R⁄Λ])).symm c) =
      (exteriorPower.zeroEquiv S (Ω[S⁄Λ])).symm (algebraMap R S c) := by
  rw [exteriorPower.zeroEquiv_symm_apply, exteriorPower.zeroEquiv_symm_apply, map_smul,
    mapExteriorPower_ιMulti, algebraMap_smul]
  exact congrArg _ (congrArg _ (funext fun j => j.elim0))

omit [IsScalarTower Λ R S] in
private theorem eq_zero_of_eq_trace (hp : p.Prime) [CharP Λ p] (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) (θ₀ : ⋀[S]^0 Ω[S⁄Λ] →ₗ[Λ] ⋀[R]^0 Ω[R⁄Λ])
    (htrace : ∀ s : S, exteriorPower.zeroEquiv R (Ω[R⁄Λ])
      (θ₀ ((exteriorPower.zeroEquiv S (Ω[S⁄Λ])).symm s)) = Algebra.trace R S s)
    (γ : ⋀[S]^0 Ω[S⁄Λ]) : θ₀ γ = 0 := by
  have h := htrace (exteriorPower.zeroEquiv S (Ω[S⁄Λ]) γ)
  rw [LinearEquiv.symm_apply_apply, trace_pthRoot_eq_zero (Λ := Λ) hp a e,
    LinearMap.zero_apply] at h
  exact (exteriorPower.zeroEquiv R (Ω[R⁄Λ])).injective (h.trans (map_zero _).symm)

private theorem eq_higherTrace_smul_rootDifferential [Nontrivial R] (hp : p.Prime) [CharP Λ p]
    (a : R) (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S)
    (θ : (n : ℕ) → ⋀[S]^n Ω[S⁄Λ] →ₗ[Λ] ⋀[R]^n Ω[R⁄Λ])
    (hwedge : ∀ (i j : ℕ) (α : ⋀[R]^i Ω[R⁄Λ]) (β : ⋀[S]^j Ω[S⁄Λ]),
      θ (i + j) (exteriorPower.wedgeMul i j (mapExteriorPower Λ R S i α) β) =
        exteriorPower.wedgeMul i j α (θ j β))
    (hroot : ∀ k < p, θ 1 (exteriorPower.ιMulti S 1 fun _ =>
        e (AdjoinRoot.root (X ^ p - C a)) ^ k • D Λ S (e (AdjoinRoot.root (X ^ p - C a)))) =
      higherTrace (t := 0) hp a e (exteriorPower.ιMulti S 1 fun _ =>
        e (AdjoinRoot.root (X ^ p - C a)) ^ k • D Λ S (e (AdjoinRoot.root (X ^ p - C a)))))
    (s : S) :
    θ 1 (exteriorPower.ιMulti S 1 fun _ => s • D Λ S (e (AdjoinRoot.root (X ^ p - C a)))) =
      higherTrace (t := 0) hp a e
        (exteriorPower.ιMulti S 1 fun _ => s • D Λ S (e (AdjoinRoot.root (X ^ p - C a)))) := by
  set x := e (AdjoinRoot.root (X ^ p - C a))
  have hR1 : ∀ (c : R) (y : ⋀[S]^1 Ω[S⁄Λ]), θ 1 (algebraMap R S c • y) = c • θ 1 y := by
    intro c y
    have h := hwedge 0 1 ((exteriorPower.zeroEquiv R (Ω[R⁄Λ])).symm c) y
    rw [mapExteriorPower_zeroEquiv_symm, wedgeMul_zeroEquiv_symm, wedgeMul_zeroEquiv_symm] at h
    exact h
  have hsum : s • D Λ S x = ∑ k : Fin (rootPowerBasis hp a e).dim,
      (rootPowerBasis hp a e).basis.repr s k • (x ^ (k : ℕ) • D Λ S x) := by
    conv_lhs => rw [← (rootPowerBasis hp a e).basis.sum_repr s]
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [rootPowerBasis_basis, smul_assoc]
  have hlin : ∀ m : Ω[S⁄Λ], (exteriorPower.ιMulti S 1 fun _ => m) =
      (exteriorPower.oneEquiv S (Ω[S⁄Λ])).symm m := fun m => by
    rw [exteriorPower.oneEquiv_symm_apply]
  rw [hsum, hlin, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk := rootPowerBasis_lt hp a e k
  rw [← algebraMap_smul S ((rootPowerBasis hp a e).basis.repr s k) (x ^ (k : ℕ) • D Λ S x),
    LinearEquiv.map_smul, hR1, algebraMap_smul,
    LinearMap.map_smul (higherTrace (t := 0) hp a e), ← hlin, hroot k hk]

/-- **The identification `Tr = Θ_{S/R}` of Remark 0FLF, as a uniqueness statement.**  A family of
maps `θ_n : Ω^n_{S/Λ} → Ω^n_{R/Λ}` which in degree zero is the trace `Trace_{S/R}`, which
satisfies the projection formula `θ(a ∧ b) = a ∧ θ(b)` for `a ∈ Ω^i_{R/Λ}` and
`b ∈ Ω^j_{S/Λ}`, and which agrees with `Tr` on the forms `x ^ k dx`, is the trace map of de Rham
complexes `Θ_{S/R}` built from `Tr`: it is zero in degree zero and `Tr` in every positive
degree. -/
public theorem eq_higherTraceComplexMap_f (hp : p.Prime) [CharP Λ p] (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S)
    (θ : (n : ℕ) → ⋀[S]^n Ω[S⁄Λ] →ₗ[Λ] ⋀[R]^n Ω[R⁄Λ])
    (htrace : ∀ s : S, exteriorPower.zeroEquiv R (Ω[R⁄Λ])
      (θ 0 ((exteriorPower.zeroEquiv S (Ω[S⁄Λ])).symm s)) = Algebra.trace R S s)
    (hwedge : ∀ (i j : ℕ) (α : ⋀[R]^i Ω[R⁄Λ]) (β : ⋀[S]^j Ω[S⁄Λ]),
      θ (i + j) (exteriorPower.wedgeMul i j (mapExteriorPower Λ R S i α) β) =
        exteriorPower.wedgeMul i j α (θ j β))
    (hroot : ∀ k < p, θ 1 (exteriorPower.ιMulti S 1 fun _ =>
        e (AdjoinRoot.root (X ^ p - C a)) ^ k • D Λ S (e (AdjoinRoot.root (X ^ p - C a)))) =
      higherTrace (t := 0) hp a e (exteriorPower.ιMulti S 1 fun _ =>
        e (AdjoinRoot.root (X ^ p - C a)) ^ k • D Λ S (e (AdjoinRoot.root (X ^ p - C a)))))
    (n : ℕ) : θ n = ((higherTraceComplexMap (Λ := Λ) hp a e).f n).hom := by
  classical
  set x := e (AdjoinRoot.root (X ^ p - C a))
  have h0 := eq_zero_of_eq_trace hp a e (θ 0) htrace
  cases n with
  | zero =>
      refine LinearMap.ext fun γ => ?_
      rw [h0, higherTraceComplexMap_f_zero]
      rfl
  | succ t =>
      change θ (t + 1) = (higherTrace (t := t) hp a e).restrictScalars Λ
      rcases subsingleton_or_nontrivial R with hR | hR
      · let := Module.subsingleton R (⋀[R]^(t + 1) Ω[R⁄Λ])
        exact LinearMap.ext fun _ => Subsingleton.elim _ _
      have hdeg1 := eq_higherTrace_smul_rootDifferential hp a e θ hwedge hroot
      refine exteriorExt_rootExtension a e _ _ ?_ ?_
      · intro s r
        have hG : higherTrace (t := t) hp a e
            (s • exteriorPower.ιMulti S (t + 1) fun j => D Λ S (algebraMap R S (r j))) = 0 := by
          exact higherTrace_smul_ιMulti_D_algebraMap hp a e s r
        refine Eq.trans ?_ hG.symm
        have hel : s • exteriorPower.ιMulti S (t + 1) (fun j => D Λ S (algebraMap R S (r j))) =
            exteriorPower.wedgeMul (t + 1) 0
              (mapExteriorPower Λ R S (t + 1) (exteriorPower.ιMulti R (t + 1) fun j => D Λ R (r j)))
              ((exteriorPower.zeroEquiv S (Ω[S⁄Λ])).symm s) := by
          rw [wedgeMul_zero_eq_smul, LinearEquiv.apply_symm_apply, mapExteriorPower_ιMulti,
            D_algebraMap_eq_map_D]
        rw [hel]
        exact (hwedge (t + 1) 0 _ _).trans (by rw [h0]; exact map_zero _)
      · intro s r
        have hel : s • exteriorPower.ιMulti S (t + 1)
              (Fin.snoc (fun j => D Λ S (algebraMap R S (r j))) (D Λ S x)) =
            exteriorPower.wedgeMul t 1
              (mapExteriorPower Λ R S t (exteriorPower.ιMulti R t fun j => D Λ R (r j)))
              (exteriorPower.ιMulti S 1 fun _ => s • D Λ S x) := by
          rw [smul_ιMulti_snoc, mapExteriorPower_ιMulti,
            exteriorPower.wedgeMul_ιMulti, Fin.append_right_eq_snoc, D_algebraMap_eq_map_D]
        rw [hel]
        change θ (t + 1) _ = higherTrace (t := t + 0) hp a e _
        rw [hwedge t 1, higherTrace_wedgeMul hp a e t 0, hdeg1]

/-- Over a base of characteristic `p`, a natural number strictly between `0` and `p` is a unit:
a scalar multiple by it vanishes only if the element does. -/
private theorem eq_zero_of_natCast_smul_eq_zero {M : Type*} [AddCommGroup M] [Module Λ M]
    (hp : p.Prime) [CharP Λ p] {n : ℕ} (hn₀ : 0 < n) (hn : n < p) {m : M}
    (h : (n : Λ) • m = 0) : m = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hne : ((n : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun hdvd => absurd (Nat.le_of_dvd hn₀ hdvd) (by omega)
  have hu : ZMod.castHom (dvd_refl p) Λ ((n : ZMod p)⁻¹) * (n : Λ) = 1 := by
    rw [← map_natCast (ZMod.castHom (dvd_refl p) Λ) n, ← map_mul, inv_mul_cancel₀ hne, map_one]
  rw [← one_smul Λ m, ← hu, mul_smul, h, smul_zero]

/-- **The identification `Tr = Θ_{S/R}` of Remark 0FLF, for a map of complexes.**  A family of
`Λ`-linear maps `θ_n : Ω^n_{S/Λ} → Ω^n_{R/Λ}` which in degree zero is the trace
`Trace_{S/R}`, which satisfies the projection formula `θ(a ∧ b) = a ∧ θ(b)`, which commutes
with the de Rham differential out of degree zero, and which sends `x ^ (p - 1) dx` to `da`, is
the trace map of de Rham complexes `Θ_{S/R}` built from `Tr`. -/
public theorem eq_higherTraceComplexMap_f_of_comm (hp : p.Prime) [CharP Λ p] (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S)
    (θ : (n : ℕ) → ⋀[S]^n Ω[S⁄Λ] →ₗ[Λ] ⋀[R]^n Ω[R⁄Λ])
    (htrace : ∀ s : S, exteriorPower.zeroEquiv R (Ω[R⁄Λ])
      (θ 0 ((exteriorPower.zeroEquiv S (Ω[S⁄Λ])).symm s)) = Algebra.trace R S s)
    (hwedge : ∀ (i j : ℕ) (α : ⋀[R]^i Ω[R⁄Λ]) (β : ⋀[S]^j Ω[S⁄Λ]),
      θ (i + j) (exteriorPower.wedgeMul i j (mapExteriorPower Λ R S i α) β) =
        exteriorPower.wedgeMul i j α (θ j β))
    (hd : ∀ γ : ⋀[S]^0 Ω[S⁄Λ],
      θ 1 (deRhamDifferential (A := Λ) 0 γ) = deRhamDifferential (A := Λ) 0 (θ 0 γ))
    (htop : θ 1 (exteriorPower.ιMulti S 1 fun _ =>
        e (AdjoinRoot.root (X ^ p - C a)) ^ (p - 1) • D Λ S (e (AdjoinRoot.root (X ^ p - C a)))) =
      exteriorPower.ιMulti R 1 fun _ => D Λ R a)
    (n : ℕ) : θ n = ((higherTraceComplexMap (Λ := Λ) hp a e).f n).hom := by
  set x := e (AdjoinRoot.root (X ^ p - C a))
  refine eq_higherTraceComplexMap_f hp a e θ htrace hwedge (fun k hk => ?_) n
  by_cases hkp : k = p - 1
  · subst hkp
    have hval := higherTrace_apply_top (t := 0) (Λ := Λ) hp a e (fun j => j.elim0)
    rw [fin_snoc_zero, fin_snoc_zero] at hval
    rw [htop, hval]
  · have hle : k ≤ p - 2 := by have := hp.two_le; omega
    have hval := higherTrace_apply_of_le (t := 0) (Λ := Λ) hp a e k hle (fun j => j.elim0)
    rw [fin_snoc_zero] at hval
    rw [hval]
    have hexact : deRhamDifferential (A := Λ) 0
        ((exteriorPower.zeroEquiv S (Ω[S⁄Λ])).symm (x ^ (k + 1))) =
          ((k + 1 : ℕ) : Λ) • exteriorPower.ιMulti S 1 fun _ => x ^ k • D Λ S x := by
      apply (exteriorPower.oneEquiv S (Ω[S⁄Λ])).injective
      rw [oneEquiv_deRhamDifferential_zero, LinearEquiv.apply_symm_apply,
        Derivation.leibniz_pow, Nat.add_sub_cancel, Nat.cast_smul_eq_nsmul, map_nsmul,
        exteriorPower.oneEquiv_ιMulti]
    refine eq_zero_of_natCast_smul_eq_zero (Λ := Λ) hp (n := k + 1) (by omega) (by omega) ?_
    rw [← map_smul, ← hexact, hd, eq_zero_of_eq_trace hp a e (θ 0) htrace, map_zero]

/-- **The identification `Tr = Θ_{S/R}` of Remark 0FLF, for maps of de Rham complexes.**  A map of
complexes `Θ : Ω^•_{S/Λ} ⟶ Ω^•_{R/Λ}` which in degree zero is the trace `Trace_{S/R}`, which
satisfies the projection formula `Θ(a ∧ b) = a ∧ Θ(b)` for `a ∈ Ω^i_{R/Λ}` and
`b ∈ Ω^j_{S/Λ}`, and which sends `x ^ (p - 1) dx` to `da`, is the trace map of de Rham complexes
built from the trace `Tr` of Lemma 0AX5. -/
public theorem eq_higherTraceComplexMap (hp : p.Prime) [CharP Λ p] (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) (Θ : deRhamComplex Λ S ⟶ deRhamComplex Λ R)
    (htrace : ∀ s : S, exteriorPower.zeroEquiv R (Ω[R⁄Λ])
      ((Θ.f 0).hom ((exteriorPower.zeroEquiv S (Ω[S⁄Λ])).symm s)) = Algebra.trace R S s)
    (hwedge : ∀ (i j : ℕ) (α : ⋀[R]^i Ω[R⁄Λ]) (β : ⋀[S]^j Ω[S⁄Λ]),
      (Θ.f (i + j)).hom (exteriorPower.wedgeMul i j (mapExteriorPower Λ R S i α) β) =
        exteriorPower.wedgeMul i j α ((Θ.f j).hom β))
    (htop : (Θ.f 1).hom (exteriorPower.ιMulti S 1 fun _ =>
        e (AdjoinRoot.root (X ^ p - C a)) ^ (p - 1) • D Λ S (e (AdjoinRoot.root (X ^ p - C a)))) =
      exteriorPower.ιMulti R 1 fun _ => D Λ R a) :
    Θ = higherTraceComplexMap hp a e := by
  have hd : ∀ γ : ⋀[S]^0 Ω[S⁄Λ], (Θ.f 1).hom (deRhamDifferential (A := Λ) 0 γ) =
      deRhamDifferential (A := Λ) 0 ((Θ.f 0).hom γ) := fun γ => by
    have h := congrArg (fun φ => φ.hom γ) (Θ.comm 0 1)
    simp only [deRhamComplex_d] at h
    exact h.symm
  ext n : 1
  exact ModuleCat.hom_ext (eq_higherTraceComplexMap_f_of_comm hp a e (fun n => (Θ.f n).hom)
    htrace hwedge hd htop n)

end Complex

end KaehlerDifferential

end
