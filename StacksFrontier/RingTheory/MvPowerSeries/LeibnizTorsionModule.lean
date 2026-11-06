module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.DirectSum.Finsupp
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import StacksFrontier.Algebra.Module.InjectiveHull.Injective
public import StacksFrontier.Algebra.Module.IPowerTorsion
public import StacksFrontier.RingTheory.Dualizing.ResidueFieldHull
public import StacksFrontier.RingTheory.MvPowerSeries.CotangentSpace
public import StacksFrontier.RingTheory.MvPowerSeries.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.MvPowerSeries.RegularLocal

/-!
# Torsion modules with formal differentiation operators

Let `k` be a field of characteristic zero and let `A = k[[x_1, …, x_d]]` be the formal power
series ring in a positive finite number of variables over `k`. An `A`-module supported at the
maximal ideal and equipped with additive operators satisfying the formal partial-derivative
Leibniz rules is a direct sum of copies of an injective hull of `k`.

## Main results

* `MvPowerSeries.pderiv_rename` commutes a formal partial derivative with a renaming of the
  variables along an embedding.
* `MvPowerSeries.exists_linearEquiv_directSum_injectiveHull_of_leibniz` gives the decomposition
  of such a module into copies of the injective hull.

## Implementation notes

The residue field `k` is regarded as an `A`-module by restriction along the constant-coefficient
homomorphism. Being supported at the maximal ideal is expressed by `IsIPowerTorsion`, and the
operators are additive homomorphisms. The conclusion records an arbitrary indexing type and an
`A`-linear equivalence with the corresponding direct sum.

The surjectivity of the comparison map is proved by induction on the number of variables: one
divides by the first variable, uses that the derivation in a later variable preserves the
submodule killed by the first one, and renames the remaining variables to reduce the count.

## References

* [Lyubeznik, Theorem 2.4][Lyubeznik]
* [Stacks Project, Tag 0EC2](https://stacks.math.columbia.edu/tag/0EC2)
-/

@[expose] public section

open CategoryTheory Stacks.MvPowerSeries.RegularParameters
open scoped DirectSum

universe u v

namespace MvPowerSeries


/-- The residue field of a formal power series ring over a field is linearly equivalent to the
base field with the module structure restricted along the constant-coefficient map. -/
private noncomputable def residueFieldLinearEquivConstantCoeff
    (k : Type u) [Field k] (d : ℕ) :
    IsLocalRing.ResidueField (MvPowerSeries (Fin d) k) ≃ₗ[MvPowerSeries (Fin d) k]
      (ModuleCat.restrictScalars
        (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) k →+* k)).obj
          (ModuleCat.of k k) := by
  let A := MvPowerSeries (Fin d) k
  let c : A →+* k := MvPowerSeries.constantCoeff
  have hsurj : Function.Surjective c := fun a => ⟨MvPowerSeries.C a,
    MvPowerSeries.constantCoeff_C a⟩
  have hker : RingHom.ker c = IsLocalRing.maximalIdeal A := by
    ext f
    rw [RingHom.mem_ker, mem_maximalIdeal_iff_constantCoeff_eq_zero_field]
  let e : A ⧸ IsLocalRing.maximalIdeal A ≃+* k :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  letI : Module A k := Module.compHom k c
  let f : (A ⧸ IsLocalRing.maximalIdeal A) →ₗ[A] k :=
    { toFun := e
      map_add' := e.map_add
      map_smul' := by
        intro r x
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
        rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
        simp only [map_mul, RingHom.id_apply]
        change c r * c a = c r • c a
        rw [smul_eq_mul] }
  exact LinearEquiv.ofBijective f e.bijective

/-- If a linear map sends `t` to `a • z` with `a` a power series of nonzero constant coefficient
over a field, then it sends some multiple of `t` to `z`. -/
private theorem exists_linearMap_smul_eq_of_constantCoeff_ne_zero
    {k : Type u} [Field k] {d : ℕ} {M N : Type*} [AddCommGroup M]
    [Module (MvPowerSeries (Fin d) k) M] [AddCommGroup N] [Module (MvPowerSeries (Fin d) k) N]
    (f : M →ₗ[MvPowerSeries (Fin d) k] N)
    {a : MvPowerSeries (Fin d) k} (ha : MvPowerSeries.constantCoeff a ≠ 0) {t : M} {z : N}
    (h : f t = a • z) : ∃ v : MvPowerSeries (Fin d) k, f (v • t) = z := by
  have hu : IsUnit a := MvPowerSeries.isUnit_iff_constantCoeff.2 (isUnit_iff_ne_zero.2 ha)
  exact ⟨↑hu.unit⁻¹, by rw [map_smul, h, smul_smul, hu.val_inv_mul, one_smul]⟩

/-- In a module with Leibniz operators over a characteristic-zero power series ring, every
element killed by a power of a variable is divisible by that variable. -/
private theorem exists_smul_X_eq_of_pow_smul_eq_zero
    (k : Type u) [Field k] [CharZero k] (d : ℕ)
    (M : Type v) [AddCommGroup M] [Module (MvPowerSeries (Fin d) k) M]
    (D : Fin d → M →+ M)
    (hD : ∀ (j : Fin d) (f : MvPowerSeries (Fin d) k) (z : M),
      D j (f • z) = MvPowerSeries.pderiv (R := k) j f • z + f • D j z)
    (j : Fin d) (z : M) (n : ℕ)
    (hn : (MvPowerSeries.X j : MvPowerSeries (Fin d) k) ^ n • z = 0) :
    ∃ y : M, (MvPowerSeries.X j : MvPowerSeries (Fin d) k) • y = z := by
  induction n generalizing z with
  | zero =>
      simp only [pow_zero, one_smul] at hn
      exact ⟨0, by simp [hn]⟩
  | succ n ih =>
      let x : MvPowerSeries (Fin d) k := MvPowerSeries.X j
      have hderiv : MvPowerSeries.pderiv (R := k) j (x ^ (n + 1)) =
          ((n + 1 : ℕ) : MvPowerSeries (Fin d) k) * x ^ n := by
        rw [MvPowerSeries.pderiv_pow, MvPowerSeries.pderiv_X_self]
        simp [Nat.cast_succ, mul_comm, mul_left_comm]
      have hLeib := hD j (x ^ (n + 1)) z
      rw [hn, map_zero, hderiv] at hLeib
      have hfact : x ^ n • (((n + 1 : ℕ) : MvPowerSeries (Fin d) k) • z +
          x • D j z) = 0 := by
        rw [smul_add, smul_smul, smul_smul, mul_comm (x ^ n) _, ← pow_succ]
        exact hLeib.symm
      obtain ⟨y, hy⟩ := ih _ hfact
      obtain ⟨v, hv⟩ := exists_linearMap_smul_eq_of_constantCoeff_ne_zero
        (LinearMap.lsmul (MvPowerSeries (Fin d) k) M x)
        (a := ((n + 1 : ℕ) : MvPowerSeries (Fin d) k)) (t := y - D j z) (z := z)
        (by simpa using (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n) : ((n + 1 : ℕ) : k) ≠ 0))
        (by rw [LinearMap.lsmul_apply, smul_sub, show x • y = _ from hy, add_sub_cancel_right])
      exact ⟨v • (y - D j z), hv⟩

/-- A derivation in a variable other than the first preserves being killed by the first
variable. -/
private theorem smul_X_zero_D_of_ne_zero
    (k : Type u) [Field k] (d : ℕ)
    (M : Type v) [AddCommGroup M] [Module (MvPowerSeries (Fin (d + 1)) k) M]
    (D : Fin (d + 1) → M →+ M)
    (hD : ∀ (j : Fin (d + 1)) (f : MvPowerSeries (Fin (d + 1)) k) (z : M),
      D j (f • z) = MvPowerSeries.pderiv (R := k) j f • z + f • D j z)
    (j : Fin (d + 1)) (hj : j ≠ 0) (z : M)
    (hz : (MvPowerSeries.X (0 : Fin (d + 1)) : MvPowerSeries (Fin (d + 1)) k) • z = 0) :
    (MvPowerSeries.X (0 : Fin (d + 1)) : MvPowerSeries (Fin (d + 1)) k) • D j z = 0 := by
  have h := hD j (MvPowerSeries.X (0 : Fin (d + 1))) z
  rw [hz, map_zero, MvPowerSeries.pderiv_X_of_ne (Ne.symm hj), zero_smul, zero_add] at h
  exact h.symm

/-- An element killed by `x` lies in the submodule annihilated by the ideal generated by `x`. -/
private theorem mem_torsionBySet_span_singleton_of_smul_eq_zero {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {x : R} {y : M} (h : x • y = 0) :
    y ∈ Submodule.torsionBySet R M (Ideal.span {x}) := by
  rw [Submodule.mem_torsionBySet_iff]
  intro a
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp a.2
  rw [← hc, mul_smul, h, smul_zero]

/-- The operators in the variables after the first preserve the submodule annihilated by the
ideal generated by the first variable. -/
private theorem deriv_preserves_torsionBy_firstVariable
    (k : Type u) [Field k] (d : ℕ)
    (M : Type v) [AddCommGroup M] [Module (MvPowerSeries (Fin (d + 1)) k) M]
    (D : Fin (d + 1) → M →+ M)
    (hD : ∀ (j : Fin (d + 1)) (f : MvPowerSeries (Fin (d + 1)) k) (z : M),
      D j (f • z) = MvPowerSeries.pderiv (R := k) j f • z + f • D j z)
    (j : Fin (d + 1)) (hj : j ≠ 0)
    (z : Submodule.torsionBySet (MvPowerSeries (Fin (d + 1)) k) M
      (Ideal.span ({MvPowerSeries.X (0 : Fin (d + 1))} : Set (MvPowerSeries (Fin (d + 1)) k)))) :
    D j z.1 ∈ Submodule.torsionBySet (MvPowerSeries (Fin (d + 1)) k) M
      (Ideal.span ({MvPowerSeries.X (0 : Fin (d + 1))} : Set (MvPowerSeries (Fin (d + 1)) k))) :=
  mem_torsionBySet_span_singleton_of_smul_eq_zero
    (smul_X_zero_D_of_ne_zero k d M D hD j hj z.1 (by simpa using z.2))

/-- An injective hull of the residue field of a formal power series ring is maximal-ideal-power
torsion. -/
private theorem isIPowerTorsion_injectiveHull
    (k : Type u) [Field k] (d : ℕ)
    (E : Type u) [AddCommGroup E] [Module (MvPowerSeries (Fin d) k) E]
    (i : (ModuleCat.restrictScalars
        (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) k →+* k)).obj
          (ModuleCat.of k k) ⟶ ModuleCat.of (MvPowerSeries (Fin d) k) E)
    [Mono i] (hi : Module.IsInjectiveHull i) :
    IsIPowerTorsion (MvPowerSeries (Fin d) k) E
      (IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) k)) := by
  let A := MvPowerSeries (Fin d) k
  let K := (ModuleCat.restrictScalars
    (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) k →+* k)).obj (ModuleCat.of k k)
  let : IsNoetherianRing A := mvPowerSeries_fin_isNoetherianRing k d
  let e : IsLocalRing.ResidueField A ≃ₗ[A] K :=
    residueFieldLinearEquivConstantCoeff k d
  have htop : (⨆ n : ℕ, Dualizing.maximalIdealPowTorsion A (ModuleCat.of A E) n) = ⊤ :=
    Dualizing.iSup_maximalIdealPowTorsion_eq_top A K (ModuleCat.of A E) e i hi
  have hdir : Directed (· ≤ ·)
      (fun n : ℕ => Dualizing.maximalIdealPowTorsion A (ModuleCat.of A E) n) := by
    intro n m
    refine ⟨max n m, ?_, ?_⟩
    · exact Submodule.torsionBySet_le_torsionBySet_pow (n + 1) (max n m + 1)
        (by omega) (IsLocalRing.maximalIdeal A)
    · exact Submodule.torsionBySet_le_torsionBySet_pow (m + 1) (max n m + 1)
        (by omega) (IsLocalRing.maximalIdeal A)
  intro z
  have hz : z ∈ (⨆ n : ℕ, Dualizing.maximalIdealPowTorsion A (ModuleCat.of A E) n) := by
    simp [htop]
  obtain ⟨n, hn⟩ := (Submodule.mem_iSup_of_directed _ hdir).mp hz
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  rw [Submodule.mem_torsionBySet_iff] at hn
  exact fun a ha => hn ⟨a, ha⟩

/-- A direct sum of `I`-power torsion modules is `I`-power torsion. -/
public theorem isIPowerTorsion_directSum
    (R : Type u) [CommRing R] (ι : Type v)
    (E : ι → Type _) [∀ i, AddCommGroup (E i)] [∀ i, Module R (E i)]
    (I : Ideal R) (hE : ∀ i, IsIPowerTorsion R (E i) I) :
    IsIPowerTorsion R (⨁ i, E i) I := by
  classical
  intro x
  let n : ι → ℕ := fun i => Classical.choose (hE i (x i))
  have hkill (i : ι) : ∀ a ∈ I ^ n i, a • x i = 0 :=
    (Classical.choose_spec (hE i (x i))).2
  let N : ℕ := x.support.sup n
  refine ⟨N + 1, Nat.succ_pos N, ?_⟩
  intro a ha
  ext i
  by_cases hi : i ∈ x.support
  · exact hkill i a (Ideal.pow_le_pow_right (by
      have := Finset.le_sup (s := x.support) (f := n) hi
      omega) ha)
  · have hx : x i = 0 := by simpa using hi
    show a • x i = 0
    simp [hx]

/-- A universe lift of an `I`-power torsion module is `I`-power torsion. -/
private theorem isIPowerTorsion_ulift {R : Type*} [CommRing R] {E : Type u} [AddCommGroup E]
    [Module R E] {I : Ideal R} (hE : IsIPowerTorsion R E I) :
    IsIPowerTorsion R (ULift.{v} E) I := by
  intro z
  obtain ⟨n, hnpos, hn⟩ := hE z.down
  exact ⟨n, hnpos, fun a ha => ULift.ext (hn a ha)⟩

/-- In a maximal-ideal-power torsion module every element is killed by a power of each
variable. -/
private theorem coordinateTorsion_of_isIPowerTorsion
    (k : Type u) [Field k] (d : ℕ)
    (M : Type v) [AddCommGroup M] [Module (MvPowerSeries (Fin d) k) M]
    (hM : IsIPowerTorsion (MvPowerSeries (Fin d) k) M
      (IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) k)))
    (j : Fin d) (z : M) :
    ∃ n : ℕ, (MvPowerSeries.X j : MvPowerSeries (Fin d) k) ^ n • z = 0 := by
  obtain ⟨n, -, hn⟩ := hM z
  exact ⟨n, hn _ (Ideal.pow_mem_pow
    ((mem_maximalIdeal_iff_constantCoeff_eq_zero_field _).2
      (MvPowerSeries.constantCoeff_X j)) n)⟩

/-- An element killed by every variable is killed by the maximal ideal. -/
private theorem smul_eq_zero_of_forall_X_smul_eq_zero
    (k : Type u) [Field k] (d : ℕ) {N : Type*} [AddCommGroup N]
    [Module (MvPowerSeries (Fin d) k) N] {z : N}
    (hz : ∀ j : Fin d, (MvPowerSeries.X j : MvPowerSeries (Fin d) k) • z = 0)
    {a : MvPowerSeries (Fin d) k} (ha : a ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) k)) :
    a • z = 0 := by
  rw [maximalIdeal_mvPowerSeries_eq_span_X k d] at ha
  apply Submodule.span_induction
    (s := Set.range (MvPowerSeries.X : Fin d → MvPowerSeries (Fin d) k))
    (p := fun a _ => a • z = 0)
    (mem := by
      rintro _ ⟨j, rfl⟩
      exact hz j)
    (zero := by simp)
    (add := by
      intro a b _ _ ha hb
      rw [add_smul, ha, hb, zero_add])
    (smul := by
      intro r a _ ha
      show (r * a) • z = 0
      rw [← smul_smul, ha, smul_zero]) ha

/-- An element annihilated by the maximal ideal of a formal power series ring over a field is
acted on by every series through its constant coefficient. -/
private theorem smul_eq_C_constantCoeff_smul {k : Type u} [Field k] {d : ℕ} {E : Type v}
    [AddCommGroup E] [Module (MvPowerSeries (Fin d) k) E] {y : E}
    (hy : y ∈ Submodule.torsionBySet (MvPowerSeries (Fin d) k) E
      (IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) k)))
    (r : MvPowerSeries (Fin d) k) :
    r • y = (MvPowerSeries.C (MvPowerSeries.constantCoeff r) : MvPowerSeries (Fin d) k) • y := by
  have hdiff : r - MvPowerSeries.C (MvPowerSeries.constantCoeff r) ∈
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) k) :=
    (mem_maximalIdeal_iff_constantCoeff_eq_zero_field _).mpr (by simp)
  rw [Submodule.mem_torsionBySet_iff] at hy
  rw [← sub_eq_zero, ← sub_smul]
  exact hy ⟨_, hdiff⟩

/-- A linear map is surjective if its source is divisible by `x`, its target is `x`-power
torsion, and every element of the target killed by `x` is hit. -/
private theorem linearMap_surjective_of_smul_divisible_and_torsion
    {R : Type u} {M : Type v} {N : Type _} [Ring R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (x : R) (f : M →ₗ[R] N)
    (hdiv : ∀ m : M, ∃ z, x • z = m)
    (htor : ∀ y : N, ∃ n : ℕ, x ^ n • y = 0)
    (hker : ∀ y : N, x • y = 0 → ∃ z : M, f z = y) :
    Function.Surjective f := by
  intro y
  obtain ⟨n, hn⟩ := htor y
  induction n generalizing y with
  | zero => exact ⟨0, by simpa using hn.symm⟩
  | succ n ih =>
      have hxy : x ^ n • (x • y) = 0 := by
        simpa [pow_succ, smul_smul, mul_comm] using hn
      obtain ⟨m, hm⟩ := ih (x • y) hxy
      obtain ⟨z, hz⟩ := hdiv m
      have hzero : x • (f z - y) = 0 := by
        rw [smul_sub, ← f.map_smul, hz, hm, sub_self]
      obtain ⟨c, hcf⟩ := hker (f z - y) hzero
      refine ⟨z - c, ?_⟩
      simp [map_sub, hcf]

/-- In an `I`-power torsion module every nonzero element has a nonzero multiple annihilated
by `I`. -/
private theorem exists_nonzero_multiple_in_socle
    {R : Type u} [CommRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (hM : IsIPowerTorsion R M I)
    {x : M} (hx : x ≠ 0) :
    ∃ a : R, a • x ∈ Submodule.torsionBySet R M I ∧
      a • x ≠ 0 := by
  classical
  let P : ℕ → Prop := fun n => ∀ a ∈ I ^ n, a • x = 0
  obtain ⟨n₀, hn₀, hkill₀⟩ := hM x
  have hex : ∃ n, P n := ⟨n₀, hkill₀⟩
  let n := Nat.find hex
  have hn : P n := Nat.find_spec hex
  have hnpos : 0 < n := Nat.pos_of_ne_zero fun h0 => hx (by simpa using hn 1 (by simp [h0]))
  obtain ⟨a, ha, hax⟩ : ∃ a : R, a ∈ I ^ (n - 1) ∧ a • x ≠ 0 := by
    by_contra h
    push Not at h
    exact Nat.find_min hex (show n - 1 < n by omega) h
  refine ⟨a, ?_, hax⟩
  rw [Submodule.mem_torsionBySet_iff]
  intro r
  have hra : r.1 * a ∈ I ^ n := by
    rw [← Nat.sub_add_cancel hnpos, pow_succ]
    simpa [mul_comm] using Ideal.mul_mem_mul ha r.2
  rw [← mul_smul]
  exact hn (r.1 * a) hra

/-- A linear map out of an `I`-power torsion module is injective as soon as it is injective on
the submodule annihilated by `I`. -/
private theorem linearMap_injective_of_isIPowerTorsion
    {R : Type u} [CommRing R] (I : Ideal R) {M : Type v} {N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (hM : IsIPowerTorsion R M I) (φ : M →ₗ[R] N)
    (h : ∀ x ∈ Submodule.torsionBySet R M I, φ x = 0 → x = 0) :
    Function.Injective φ := by
  intro x y hxy
  by_contra hne
  obtain ⟨a, haS, ha0⟩ := exists_nonzero_multiple_in_socle I M hM (sub_ne_zero.mpr hne)
  exact ha0 (h _ haS (by rw [map_smul, map_sub, hxy, sub_self, smul_zero]))

/-- A formal partial derivative commutes with renaming the variables along an embedding: the
derivative in the variable `e i` of a renamed series is the renaming of the derivative in `i`. -/
theorem pderiv_rename
    {σ τ k : Type*} [CommRing k] (e : σ ↪ τ) [Filter.TendstoCofinite e]
    (i : σ) (g : MvPowerSeries σ k) :
    MvPowerSeries.pderiv (R := k) (e i) (MvPowerSeries.rename e g) =
      MvPowerSeries.rename e (MvPowerSeries.pderiv (R := k) i g) := by
  classical
  ext β
  rw [MvPowerSeries.coeff_pderiv]
  by_cases hβ : β ∈ Set.range (Finsupp.mapDomain e)
  · obtain ⟨α, rfl⟩ := hβ
    rw [← Finsupp.mapDomain_single (f := e) (a := i) (b := 1),
      ← Finsupp.mapDomain_add]
    show MvPowerSeries.coeff (Finsupp.mapDomain e (α + Finsupp.single i 1))
      (MvPowerSeries.rename e g) *
      ((Finsupp.mapDomain e α) (e i) + 1) =
      MvPowerSeries.coeff (Finsupp.mapDomain e α)
        (MvPowerSeries.rename e (MvPowerSeries.pderiv (R := k) i g))
    rw [← Finsupp.embDomain_eq_mapDomain e (α + Finsupp.single i 1),
      ← Finsupp.embDomain_eq_mapDomain e α]
    simp only [MvPowerSeries.coeff_embDomain_rename, MvPowerSeries.coeff_pderiv]
    rw [Finsupp.embDomain_eq_mapDomain]
    show MvPowerSeries.coeff (α + Finsupp.single i 1) g *
      ((Finsupp.mapDomain e α) (e i) + 1) = _
    rw [Finsupp.mapDomain_apply_of_injective e.injective]
  · have hβ' : β + Finsupp.single (e i) 1 ∉
        Set.range (Finsupp.mapDomain e) := by
      intro h
      apply hβ
      rw [Finsupp.mem_range_mapDomain_iff (f := e) e.injective] at h ⊢
      intro b hb
      have hne : b ≠ e i := fun he => hb ⟨i, he.symm⟩
      simpa [Finsupp.add_apply, Finsupp.single_apply, hne] using h b hb
    rw [MvPowerSeries.coeff_rename_eq_zero (f := e) g hβ',
      MvPowerSeries.coeff_rename_eq_zero (f := e) _ hβ]
    simp

/-- Coordinate torsion in the variables after the first passes to a submodule viewed over the
power series ring in the remaining variables. -/
private theorem coordinateTorsion_rename_succ
    (k : Type u) [Field k] (d : ℕ) {M : Type v} [AddCommGroup M]
    [Module (MvPowerSeries (Fin (d + 1)) k) M]
    (P : Submodule (MvPowerSeries (Fin (d + 1)) k) M) [Module (MvPowerSeries (Fin d) k) P]
    (hP : ∀ (b : MvPowerSeries (Fin d) k) (z : P),
      ((b • z : P) : M) = MvPowerSeries.rename Fin.succ b • (z : M))
    (hT : ∀ j : Fin (d + 1), ∀ z : M,
      ∃ n : ℕ, (MvPowerSeries.X j : MvPowerSeries (Fin (d + 1)) k) ^ n • z = 0)
    (j : Fin d) (z : P) :
    ∃ n : ℕ, (MvPowerSeries.X j : MvPowerSeries (Fin d) k) ^ n • z = 0 := by
  obtain ⟨n, hn⟩ := hT j.succ z
  refine ⟨n, Subtype.ext ?_⟩
  rw [hP, map_pow, MvPowerSeries.rename_X]
  exact hn

/-- A map hitting every element killed by all the variables still does so on submodules killed
by the first variable, viewed over the power series ring in the remaining variables. -/
private theorem socle_lift_rename_succ
    (k : Type u) [Field k] (d : ℕ) {M : Type v} {N : Type*} [AddCommGroup M]
    [Module (MvPowerSeries (Fin (d + 1)) k) M] [AddCommGroup N]
    [Module (MvPowerSeries (Fin (d + 1)) k) N]
    (f : M →ₗ[MvPowerSeries (Fin (d + 1)) k] N)
    (hSoc : ∀ z : N,
      (∀ j : Fin (d + 1), (MvPowerSeries.X j : MvPowerSeries (Fin (d + 1)) k) • z = 0) →
      ∃ y : M, (∀ j : Fin (d + 1), (MvPowerSeries.X j : MvPowerSeries (Fin (d + 1)) k) • y = 0) ∧
        f y = z)
    (P : Submodule (MvPowerSeries (Fin (d + 1)) k) M)
    (Q : Submodule (MvPowerSeries (Fin (d + 1)) k) N)
    [Module (MvPowerSeries (Fin d) k) P] [Module (MvPowerSeries (Fin d) k) Q]
    (hP : ∀ (b : MvPowerSeries (Fin d) k) (z : P),
      ((b • z : P) : M) = MvPowerSeries.rename Fin.succ b • (z : M))
    (hQ : ∀ (b : MvPowerSeries (Fin d) k) (z : Q),
      ((b • z : Q) : N) = MvPowerSeries.rename Fin.succ b • (z : N))
    (hPmem : ∀ y : M, (MvPowerSeries.X 0 : MvPowerSeries (Fin (d + 1)) k) • y = 0 → y ∈ P)
    (hQ0 : ∀ z : Q, (MvPowerSeries.X 0 : MvPowerSeries (Fin (d + 1)) k) • (z : N) = 0)
    (f0 : P →ₗ[MvPowerSeries (Fin d) k] Q) (hf0 : ∀ y : P, (f0 y : N) = f y)
    (z : Q) (hz : ∀ j : Fin d, (MvPowerSeries.X j : MvPowerSeries (Fin d) k) • z = 0) :
    ∃ y : P, (∀ j : Fin d, (MvPowerSeries.X j : MvPowerSeries (Fin d) k) • y = 0) ∧
      f0 y = z := by
  have hzall : ∀ j : Fin (d + 1),
      (MvPowerSeries.X j : MvPowerSeries (Fin (d + 1)) k) • (z : N) = 0 := by
    intro j
    cases j using Fin.cases with
    | zero => exact hQ0 z
    | succ i =>
        have h := congrArg Subtype.val (hz i)
        rwa [hQ, MvPowerSeries.rename_X] at h
  obtain ⟨y, hy, hfy⟩ := hSoc z hzall
  refine ⟨⟨y, hPmem y (hy 0)⟩, fun j => Subtype.ext ?_, Subtype.ext ((hf0 _).trans hfy)⟩
  rw [hP, MvPowerSeries.rename_X]
  exact hy j.succ

/-- A linear map between modules whose elements are killed by powers of each variable is
surjective as soon as it hits the submodule annihilated by all the variables, provided the
source carries operators satisfying the Leibniz rules. -/
private theorem linearMap_surjective_of_coordinateTorsion
    (k : Type u) [Field k] [CharZero k] (d : ℕ)
    (M : Type v) (N : Type _) [AddCommGroup M] [Module (MvPowerSeries (Fin d) k) M]
    [AddCommGroup N] [Module (MvPowerSeries (Fin d) k) N]
    (D : Fin d → M →+ M)
    (hTM : ∀ j : Fin d, ∀ z : M,
      ∃ n : ℕ, (MvPowerSeries.X j : MvPowerSeries (Fin d) k) ^ n • z = 0)
    (hTN : ∀ j : Fin d, ∀ z : N,
      ∃ n : ℕ, (MvPowerSeries.X j : MvPowerSeries (Fin d) k) ^ n • z = 0)
    (hD : ∀ (j : Fin d) (f : MvPowerSeries (Fin d) k) (z : M),
      D j (f • z) = MvPowerSeries.pderiv (R := k) j f • z + f • D j z)
    (f : M →ₗ[MvPowerSeries (Fin d) k] N)
    (hSoc : ∀ z : N,
      (∀ j : Fin d, (MvPowerSeries.X j : MvPowerSeries (Fin d) k) • z = 0) →
      ∃ y : M, (∀ j : Fin d, (MvPowerSeries.X j : MvPowerSeries (Fin d) k) • y = 0) ∧
        f y = z) : Function.Surjective f := by
  induction d using Nat.strong_induction_on generalizing M N with
  | h d ih =>
      cases d with
      | zero => exact fun z => (hSoc z fun j => j.elim0).imp fun _ h => h.2
      | succ d =>
          let A := MvPowerSeries (Fin (d + 1)) k
          let B := MvPowerSeries (Fin d) k
          let I0 : Ideal A := Ideal.span ({MvPowerSeries.X (0 : Fin (d + 1))} : Set A)
          let M0 : Submodule A M := Submodule.torsionBySet A M I0
          let N0 : Submodule A N := Submodule.torsionBySet A N I0
          let ρ : B →+* A := (MvPowerSeries.rename Fin.succ).toRingHom
          let : Module B M0 := Module.compHom M0 ρ
          let : Module B N0 := Module.compHom N0 ρ
          let D0 : Fin d → M0 →+ M0 := fun j =>
            { toFun := fun z => ⟨D (Fin.succ j) z.1,
                deriv_preserves_torsionBy_firstVariable k d M D hD (Fin.succ j)
                  (Fin.succ_ne_zero j) z⟩
              map_zero' := Subtype.ext (D (Fin.succ j)).map_zero
              map_add' := fun x y => Subtype.ext ((D (Fin.succ j)).map_add x y) }
          have hD0 : ∀ (j : Fin d) (g : B) (z : M0),
              D0 j (g • z) = MvPowerSeries.pderiv (R := k) j g • z + g • D0 j z := by
            intro j g z
            apply Subtype.ext
            show D (Fin.succ j) ((MvPowerSeries.rename Fin.succ g) • z.1) = _
            have hren : MvPowerSeries.pderiv (R := k) (Fin.succ j) (MvPowerSeries.rename Fin.succ g) =
                MvPowerSeries.rename Fin.succ (MvPowerSeries.pderiv (R := k) j g) :=
              pderiv_rename ⟨Fin.succ, Fin.succ_injective _⟩ j g
            rw [hD, hren]
            rfl
          let f0 : M0 →ₗ[B] N0 :=
            { toFun := fun z => ⟨f z.1, (Submodule.mem_torsionBySet_iff _ _).2 fun a => by
                rw [← f.map_smul, (Submodule.mem_torsionBySet_iff _ _).1 z.2 a, map_zero]⟩
              map_add' := fun x y => Subtype.ext (map_add f x.1 y.1)
              map_smul' := fun b z => Subtype.ext (f.map_smul (ρ b) z.1) }
          have hN0 (z : N0) : (MvPowerSeries.X 0 : A) • (z : N) = 0 :=
            (Submodule.mem_torsionBySet_iff _ _).1 z.2
              ⟨MvPowerSeries.X 0, Ideal.subset_span (Set.mem_singleton _)⟩
          refine linearMap_surjective_of_smul_divisible_and_torsion (MvPowerSeries.X 0 : A) f
            (fun z => ?_) (hTN 0) fun z hz => ?_
          · obtain ⟨n, hn⟩ := hTM 0 z
            exact exists_smul_X_eq_of_pow_smul_eq_zero k (d + 1) M D hD 0 z n hn
          · obtain ⟨y, hy⟩ := ih d (by omega) M0 N0 D0
              (coordinateTorsion_rename_succ k d M0 (fun _ _ => rfl) hTM)
              (coordinateTorsion_rename_succ k d N0 (fun _ _ => rfl) hTN) hD0 f0
              (socle_lift_rename_succ k d f hSoc M0 N0 (fun _ _ => rfl) (fun _ _ => rfl)
                (fun _ hy => mem_torsionBySet_span_singleton_of_smul_eq_zero hy) hN0 f0
                (fun _ => rfl))
              ⟨z, mem_torsionBySet_span_singleton_of_smul_eq_zero hz⟩
            exact ⟨y.1, congrArg Subtype.val hy⟩

/-- Every nonzero element of the target of an essential monomorphism has a nonzero multiple
in the image. -/
private theorem essentialMono_nonzero_multiple
    {R : Type u} [Ring R] {M N : ModuleCat.{v} R}
    (i : M ⟶ N) [Mono i]
    (hi : Module.IsEssentialMono i)
    (x : N) (hx : x ≠ 0) :
    ∃ r : R, r • x ∈ LinearMap.range i.hom ∧ r • x ≠ 0 := by
  let e := ModuleCat.subobjectModule N
  have hImage : e (Subobject.mk i) = LinearMap.range i.hom := by
    show LinearMap.range (Subobject.mk i).arrow.hom = LinearMap.range i.hom
    rw [← ModuleCat.hom_ext_iff.mp (Subobject.underlyingIso_hom_comp_eq_mk i),
      ModuleCat.hom_comp]
    exact LinearEquiv.range_comp (Subobject.underlyingIso i).toLinearEquiv i.hom
  let P : Submodule R N := R ∙ x
  have hP : P ≠ ⊥ := by
    simpa [P, Submodule.span_singleton_eq_bot] using hx
  have hmeet := hi (e.symm P) (by simpa using hP)
  have hmeet' : P ⊓ LinearMap.range i.hom ≠ ⊥ := by
    intro hz
    apply hmeet
    apply e.injective
    rwa [OrderIso.map_inf, e.apply_symm_apply, hImage, OrderIso.map_bot]
  obtain ⟨y, hy⟩ := Submodule.nonzero_mem_of_bot_lt ((bot_lt_iff_ne_bot).2 hmeet')
  obtain ⟨hyP, hyI⟩ := Submodule.mem_inf.mp y.2
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hyP
  have hy0 : y.1 ≠ 0 := fun hz => hy (Subtype.ext hz)
  exact ⟨r, by simpa [hr] using hyI, by simpa [hr] using hy0⟩

/-- An injective hull of the residue field identifies the residue field with the submodule
annihilated by the maximal ideal. -/
private theorem injectiveHull_socle_equiv
    (k : Type u) [Field k] (d : ℕ)
    (E : Type u) [AddCommGroup E] [Module (MvPowerSeries (Fin d) k) E]
    (i : (ModuleCat.restrictScalars
        (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) k →+* k)).obj
          (ModuleCat.of k k) ⟶ ModuleCat.of (MvPowerSeries (Fin d) k) E)
    [Mono i] (hi : Module.IsInjectiveHull i) :
    ∃ e : ((ModuleCat.restrictScalars
          (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) k →+* k)).obj
            (ModuleCat.of k k)) ≃ₗ[MvPowerSeries (Fin d) k]
        Submodule.torsionBySet (MvPowerSeries (Fin d) k) E
          (IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) k)),
      ∀ a, (e a : E) = i.hom a := by
  classical
  let A := MvPowerSeries (Fin d) k
  let K := (ModuleCat.restrictScalars
    (MvPowerSeries.constantCoeff : A →+* k)).obj (ModuleCat.of k k)
  let I := IsLocalRing.maximalIdeal A
  let S : Submodule A E := Submodule.torsionBySet A E I
  let f : K →ₗ[A] S := {
    toFun := fun a => ⟨i.hom a, by
      rw [Submodule.mem_torsionBySet_iff]
      intro r
      rw [← i.hom.map_smul, ModuleCat.restrictScalars.smul_def,
        (mem_maximalIdeal_iff_constantCoeff_eq_zero_field _).mp r.2, zero_smul]
      show i.hom (0 : K) = 0
      exact i.hom.map_zero⟩
    map_add' := fun a b => Subtype.ext (map_add i.hom a b)
    map_smul' := fun r a => Subtype.ext (i.hom.map_smul r a) }
  have hf : Function.Injective f := fun a b hab =>
    (ModuleCat.mono_iff_injective i).mp inferInstance (congrArg Subtype.val hab)
  have hsurj : Function.Surjective f := by
    intro y
    by_cases hy : (y : E) = 0
    · refine ⟨0, Subtype.ext ?_⟩
      show i.hom (0 : K) = (y : E)
      rw [hy, map_zero]
    obtain ⟨r, ⟨a, ha⟩, hr0⟩ := essentialMono_nonzero_multiple i hi.2 y.1 hy
    have hscale := smul_eq_C_constantCoeff_smul y.2 r
    have hcr : MvPowerSeries.constantCoeff r ≠ 0 := fun h0 =>
      hr0 (by simpa [h0] using hscale)
    obtain ⟨v, hv⟩ := exists_linearMap_smul_eq_of_constantCoeff_ne_zero i.hom
      (a := MvPowerSeries.C (MvPowerSeries.constantCoeff r)) (t := a) (z := (y : E))
      (by simpa using hcr) (by rw [ha, hscale])
    exact ⟨v • a, Subtype.ext hv⟩
  exact ⟨LinearEquiv.ofBijective f ⟨hf, hsurj⟩, fun _ => rfl⟩

/-- The submodule of a module over a formal power series ring annihilated by the maximal ideal
is a direct sum of copies of the residue field. -/
private theorem exists_linearEquiv_torsionBySet_directSum
    (k : Type u) [Field k] (d : ℕ)
    (M : Type v) [AddCommGroup M] [Module (MvPowerSeries (Fin d) k) M] :
    ∃ J : Type v, Nonempty (Submodule.torsionBySet (MvPowerSeries (Fin d) k) M
        (IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) k)) ≃ₗ[MvPowerSeries (Fin d) k]
      ⨁ _ : J, (ModuleCat.restrictScalars
        (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) k →+* k)).obj
          (ModuleCat.of k k)) := by
  let A := MvPowerSeries (Fin d) k
  let c : A →+* k := MvPowerSeries.constantCoeff
  let C : k →+* A := MvPowerSeries.C
  let : Module A k := Module.compHom k c
  let S : Submodule A M := Submodule.torsionBySet A M (IsLocalRing.maximalIdeal A)
  let : Module k S := Module.compHom S C
  let J := Module.Free.ChooseBasisIndex k S
  let K := (ModuleCat.restrictScalars c).obj (ModuleCat.of k k)
  let u : k ≃ₗ[A] K :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let h0 : S ≃ₗ[k] ⨁ _ : J, k :=
    (Module.Free.chooseBasis k S).repr.trans (finsuppLEquivDirectSum k k J)
  let h0A : S →ₗ[A] ⨁ _ : J, k :=
    { toFun := h0
      map_add' := h0.map_add
      map_smul' := fun a x => by
        rw [show a • x = C (c a) • x from Subtype.ext (smul_eq_C_constantCoeff_smul x.2 a)]
        show h0 (c a • x) = c a • h0 x
        exact h0.map_smul _ _ }
  exact ⟨J, ⟨(LinearEquiv.ofBijective h0A h0.bijective).trans
    (DFinsupp.mapRange.linearEquiv fun _ => u)⟩⟩

/-- A direct sum of copies of a linear map hits every element whose coordinates it hits. -/
private theorem exists_lmap_eq_of_forall_exists_eq {R : Type*} [Semiring R] {J P Q : Type*}
    [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module R Q] (g : P →ₗ[R] Q)
    (z : ⨁ _ : J, Q) (hz : ∀ j, ∃ p, g p = z j) :
    ∃ p : ⨁ _ : J, P, DirectSum.lmap (fun _ => g) p = z := by
  classical
  let r : J → Q → P := fun _ x => if hx : x ≠ 0 ∧ ∃ p, g p = x then hx.2.choose else 0
  refine ⟨DFinsupp.mapRange r (fun _ => dite_eq_right fun h => h.1 rfl) z, DFinsupp.ext fun j => ?_⟩
  show g (r j (z j)) = z j
  by_cases h : z j = 0
  · simp [r, h]
  · have hx : z j ≠ 0 ∧ ∃ p, g p = z j := ⟨h, hz j⟩
    rw [show r j (z j) = hx.2.choose from dite_eq_left hx]
    exact hx.2.choose_spec

/-- A maximal-ideal-power torsion module with Leibniz operators is isomorphic to an injective
maximal-ideal-power torsion module into which its socle embeds onto the socle. -/
private theorem nonempty_linearEquiv_of_socle
    (k : Type u) [Field k] [CharZero k] (d : ℕ)
    (M : Type v) [AddCommGroup M] [Module (MvPowerSeries (Fin d) k) M]
    (N : Type (max u v)) [AddCommGroup N] [Module (MvPowerSeries (Fin d) k) N]
    [Module.Injective (MvPowerSeries (Fin d) k) N]
    (hM : IsIPowerTorsion (MvPowerSeries (Fin d) k) M
      (IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) k)))
    (hN : IsIPowerTorsion (MvPowerSeries (Fin d) k) N
      (IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) k)))
    (D : Fin d → M →+ M)
    (hD : ∀ (j : Fin d) (f : MvPowerSeries (Fin d) k) (z : M),
      D j (f • z) = MvPowerSeries.pderiv (R := k) j f • z + f • D j z)
    (g : Submodule.torsionBySet (MvPowerSeries (Fin d) k) M
      (IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) k)) →ₗ[MvPowerSeries (Fin d) k] N)
    (hg : Function.Injective g)
    (hgs : ∀ z : N, (∀ j : Fin d, (MvPowerSeries.X j : MvPowerSeries (Fin d) k) • z = 0) →
      ∃ s, g s = z) :
    Nonempty (M ≃ₗ[MvPowerSeries (Fin d) k] N) := by
  let A := MvPowerSeries (Fin d) k
  let S := Submodule.torsionBySet A M (IsLocalRing.maximalIdeal A)
  let inc' : ULift.{u} S →ₗ[A] ULift.{u} M :=
    ULift.moduleEquiv.symm.toLinearMap.comp (S.subtype.comp ULift.moduleEquiv.toLinearMap)
  have hinc' : Function.Injective inc' :=
    ULift.moduleEquiv.symm.injective.comp
      (Subtype.val_injective.comp ULift.moduleEquiv.injective)
  obtain ⟨φ', hφ'⟩ := Module.Injective.out inc' hinc' (g.comp ULift.moduleEquiv.toLinearMap)
  let φ : M →ₗ[A] N := φ'.comp ULift.moduleEquiv.symm.toLinearMap
  have hφ (x : S) : φ x.1 = g x := by
    show φ' (ULift.up x.1) = g x
    simpa [inc'] using hφ' (ULift.up x)
  have hsurj : Function.Surjective φ := by
    refine linearMap_surjective_of_coordinateTorsion k d M N D
      (coordinateTorsion_of_isIPowerTorsion k d M hM)
      (coordinateTorsion_of_isIPowerTorsion k d N hN) hD φ fun z hz => ?_
    obtain ⟨s, hs⟩ := hgs z hz
    refine ⟨s.1, fun j => ?_, (hφ s).trans hs⟩
    have h := s.2
    rw [Submodule.mem_torsionBySet_iff] at h
    simpa using h ⟨MvPowerSeries.X j,
      (mem_maximalIdeal_iff_constantCoeff_eq_zero_field _).2 (MvPowerSeries.constantCoeff_X j)⟩
  refine ⟨LinearEquiv.ofBijective φ ⟨linearMap_injective_of_isIPowerTorsion _ hM φ
    fun x hx h0 => ?_, hsurj⟩⟩
  have : (⟨x, hx⟩ : S) = 0 := hg (by rw [map_zero, ← hφ ⟨x, hx⟩]; exact h0)
  exact congrArg Subtype.val this

/-- A maximal-ideal-power-torsion module over a characteristic-zero formal power series ring,
equipped with additive operators satisfying the partial-derivative Leibniz rules, is a direct sum
of copies of an injective hull of the residue field. -/
@[stacks 0EC2]
theorem exists_linearEquiv_directSum_injectiveHull_of_leibniz
    (k : Type u) [Field k] [CharZero k]
    (d : ℕ) (_hd : 0 < d)
    (M : Type v) [AddCommGroup M] [Module (MvPowerSeries (Fin d) k) M]
    (E : Type u) [AddCommGroup E] [Module (MvPowerSeries (Fin d) k) E]
    (i : (ModuleCat.restrictScalars
        (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) k →+* k)).obj
          (ModuleCat.of k k) ⟶ ModuleCat.of (MvPowerSeries (Fin d) k) E)
    [Mono i]
    (_hi : Module.IsInjectiveHull i)
    (_hM : IsIPowerTorsion (MvPowerSeries (Fin d) k) M
      (IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) k)))
    (D : Fin d → M →+ M)
    (_hD : ∀ (j : Fin d) (f : MvPowerSeries (Fin d) k) (z : M),
      D j (f • z) = MvPowerSeries.pderiv (R := k) j f • z + f • D j z) :
    ∃ J : Type v, Nonempty (M ≃ₗ[MvPowerSeries (Fin d) k] ⨁ _ : J, E) := by
  classical
  let A := MvPowerSeries (Fin d) k
  let I : Ideal A := IsLocalRing.maximalIdeal A
  let K := (ModuleCat.restrictScalars
    (MvPowerSeries.constantCoeff : A →+* k)).obj (ModuleCat.of k k)
  obtain ⟨J, ⟨e⟩⟩ := exists_linearEquiv_torsionBySet_directSum k d M
  obtain ⟨eE, heE⟩ := injectiveHull_socle_equiv k d E i _hi
  let jE : K →ₗ[A] ULift.{v} E := ULift.moduleEquiv.symm.toLinearMap.comp i.hom
  let N := ⨁ _ : J, ULift.{v} E
  let gS : Submodule.torsionBySet A M I →ₗ[A] N :=
    (DirectSum.lmap fun _ : J => jE).comp e.toLinearMap
  have hjE : Function.Injective jE := fun x y hxy =>
    (ModuleCat.mono_iff_injective i).mp inferInstance (congrArg ULift.down hxy)
  have hgS : Function.Injective gS := by
    show Function.Injective (DirectSum.lmap (fun _ : J => jE) ∘ e)
    exact ((DirectSum.lmap_injective _).mpr fun _ => hjE).comp e.injective
  have : IsNoetherianRing A := mvPowerSeries_fin_isNoetherianRing k d
  have : Module.Injective A (ULift.{v} E) :=
    Module.ulift_injective_of_injective A ((Module.injective_iff_injective_object A E).2 _hi.1)
  have : Module.Injective A N := Module.directSum_injective A fun _ : J => ULift.{v} E
  have hgs (z : N) (hz : ∀ j : Fin d, (MvPowerSeries.X j : A) • z = 0) : ∃ s, gS s = z := by
    have hrange (j : J) : ∃ p : K, jE p = z j := by
      have hc : (z j).down ∈ Submodule.torsionBySet A E I := by
        rw [Submodule.mem_torsionBySet_iff]
        intro a
        have h : (a.1 • z) j = 0 := congrArg (fun w : N => w j)
          (smul_eq_zero_of_forall_X_smul_eq_zero k d hz (a := a.1) a.2)
        have h' := congrArg ULift.down h
        rw [DirectSum.smul_apply] at h'
        simpa using h'
      refine ⟨eE.symm ⟨(z j).down, hc⟩, ULift.ext ?_⟩
      show i.hom (eE.symm _) = _
      rw [← heE, eE.apply_symm_apply]
    obtain ⟨p, hp⟩ := exists_lmap_eq_of_forall_exists_eq jE z hrange
    refine ⟨e.symm p, ?_⟩
    show DirectSum.lmap (fun _ : J => jE) (e (e.symm p)) = z
    rw [e.apply_symm_apply, hp]
  obtain ⟨eφ⟩ := nonempty_linearEquiv_of_socle k d M N _hM
    (isIPowerTorsion_directSum A J _ I fun _ => isIPowerTorsion_ulift
      (isIPowerTorsion_injectiveHull k d E i _hi)) D _hD gS hgS hgs
  exact ⟨J, ⟨eφ.trans (LinearEquiv.ofBijective
    (DirectSum.lmap fun _ : J => ULift.moduleEquiv.toLinearMap)
    ⟨(DirectSum.lmap_injective _).2 fun _ => ULift.moduleEquiv.injective,
      (DirectSum.lmap_surjective _).2 fun _ => ULift.moduleEquiv.surjective⟩)⟩⟩
end MvPowerSeries
