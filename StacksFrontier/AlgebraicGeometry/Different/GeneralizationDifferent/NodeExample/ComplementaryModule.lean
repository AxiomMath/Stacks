module

public import StacksFrontier.AlgebraicGeometry.Different.GeneralizationDifferent.NodeExample.TraceValues

/-!
# The complementary module and the different of the nodal power map

Let `k` be a field and `A = k[x,y]/(xy) → B = k[u,v]/(uv)` the branchwise power map
`x ↦ uⁿ`, `y ↦ vᵐ`.  From the trace values, `1 ∈ L_{B/A}` exactly when `n` and `m` have the
same image in `k`, and in that case `L_{B/A} = B` and the Dedekind different is `B`.

## Main results

* `Stacks.Discriminant.NodeExample.one_mem_complementaryModule_iff_natCast_eq`: `1` lies in the
  complementary module exactly when `(n : k) = (m : k)`.
* `Stacks.Discriminant.NodeExample.complementaryModule_eq_range` and
  `Stacks.Discriminant.NodeExample.dedekindDifferent_eq_range`: in that case both equal `B`.
* `Stacks.Discriminant.NodeExample.dedekindDifferentIdeal_eq_top` and
  `Stacks.Discriminant.NodeExample.exists_dual_trace_iff_natCast_eq`: the chartwise form of the
  generalized different of [Stacks, Tag 0BWM] is defined exactly when `(n : k) = (m : k)`, and
  is then the unit ideal.

## Implementation notes

The source states the criterion for `1 ∈ L_{B/A}` as `n = m`.  What the trace computation gives
is `(n : k) = (m : k)`, which is weaker: over a field of characteristic `3`, `n = 1` and
`m = 4` are both prime to the characteristic and `n ≠ m`, yet `1 ∈ L_{B/A}`.  The statements
below are the ones the computation supports.

Only the affine statements are available: the generalized different of [Stacks, Tag 0BWM] is a
submodule attached to a `Stacks.Discriminant.RelativeDualizingModuleData`, which nothing in the
library constructs, so the last sentence of the source is recorded here through the chartwise
criterion of [Stacks, Tag 0BWN] and the Dedekind different ideal instead.

## References

* [Stacks Project, Tag 0BWP](https://stacks.math.columbia.edu/tag/0BWP)
* [Stacks Project, Tag 0BWM](https://stacks.math.columbia.edu/tag/0BWM)
* [Stacks Project, Tag 0BWN](https://stacks.math.columbia.edu/tag/0BWN)
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Stacks.Discriminant.NodeExample

universe u

variable (k : Type u) [Field k]

private def nodeOrigin : nodeRing k →+* k :=
  Ideal.Quotient.lift _ (MvPolynomial.eval₂Hom (RingHom.id k) (fun _ => 0)) (by
    intro p hp
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hp
    simp)

private lemma nodeOrigin_x : nodeOrigin k (x k) = 0 := by
  simp [nodeOrigin, x]

private lemma nodeOrigin_y : nodeOrigin k (y k) = 0 := by
  simp [nodeOrigin, y]

private lemma nodeOrigin_algebraMap (a : k) :
    nodeOrigin k (algebraMap k (nodeRing k) a) = a := by
  change (nodeOrigin k) (Ideal.Quotient.mk _ (MvPolynomial.C a)) = a
  simp [nodeOrigin]

private lemma node_weighted_sum_in_range (a : nodeRing k) (c d : k)
    (h : a * (x k + y k) = algebraMap k (nodeRing k) c * x k +
      algebraMap k (nodeRing k) d * y k) : c = d := by
  have hrel : x k * (a - algebraMap k (nodeRing k) c) +
      y k * (a - algebraMap k (nodeRing k) d) = 0 := by
    linear_combination h
  obtain ⟨b, e, hb, he⟩ := node_coordinate_syzygy k _ _ hrel
  have hc := congrArg (nodeOrigin k) hb
  have hd := congrArg (nodeOrigin k) he
  simp only [map_sub, map_mul, nodeOrigin_algebraMap, nodeOrigin_y, nodeOrigin_x,
    zero_mul, sub_eq_zero] at hc hd
  exact hc.symm.trans hd

private lemma node_x_add_y_mem_nonZeroDivisors :
    x k + y k ∈ nonZeroDivisors (nodeRing k) := by
  simpa only [pow_one, map_add, x, y] using
    nodal_pow_sum_regular (k := k) (0 : Fin 2) 1 (by decide) 1 1 (by decide) (by decide)

/-- A natural number whose image in `k` is a unit is positive. -/
private lemma pos_of_isUnit_natCast {n : ℕ} (hn : IsUnit (n : k)) : 0 < n :=
  Nat.pos_of_ne_zero fun h => hn.ne_zero (by simp [h])

/-- Induction on `r` that reduces `r` by `d`: it suffices to treat `r < d` and to step from
`r - d` to `r`. -/
private lemma forall_of_lt_of_sub {P : ℕ → Prop} {d : ℕ} (hd : 0 < d) (hlt : ∀ r, r < d → P r)
    (hstep : ∀ r, d ≤ r → P (r - d) → P r) (r : ℕ) : P r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    by_cases hrd : r < d
    · exact hlt r hrd
    · have hle : d ≤ r := Nat.le_of_not_gt hrd
      exact hstep r hle (ih (r - d) (by omega))

private lemma targetNode_span_powers :
    Submodule.span k (Set.range (fun i : ℕ => u k ^ i) ∪
      Set.range (fun i : ℕ => v k ^ i)) = ⊤ := by
  let P := Submodule.span k (Set.range (fun i : ℕ => u k ^ i) ∪
    Set.range (fun i : ℕ => v k ^ i))
  have hu (i : ℕ) : u k ^ i ∈ P :=
    Submodule.subset_span (Or.inl ⟨i, rfl⟩)
  have hv (i : ℕ) : v k ^ i ∈ P :=
    Submodule.subset_span (Or.inr ⟨i, rfl⟩)
  have hmul (b : targetNodeRing k) (hb : b ∈ P) (j : Bool) :
      b * branchCoord k j ∈ P := by
    induction hb using Submodule.span_induction with
    | mem z hz =>
      rcases hz with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · cases j
        · simpa [branchCoord, pow_succ] using hu (i + 1)
        · cases i with
          | zero => simpa [branchCoord] using hv 1
          | succ i =>
            have hz : u k ^ (i + 1) * v k = 0 := by
              rw [pow_succ, mul_assoc, targetNode_uv_zero, mul_zero]
            simpa only [branchCoord, Bool.false_eq_true, ↓reduceIte, hz] using P.zero_mem
      · cases j
        · cases i with
          | zero => simpa [branchCoord] using hu 1
          | succ i =>
            have hz : v k ^ (i + 1) * u k = 0 := by
              rw [pow_succ, mul_assoc, mul_comm (v k), targetNode_uv_zero, mul_zero]
            simpa only [branchCoord, Bool.false_eq_true, ↓reduceIte, hz] using P.zero_mem
        · simpa [branchCoord, pow_succ] using hv (i + 1)
    | zero => simp
    | add a b ha hb ia ib => simpa [add_mul] using P.add_mem ia ib
    | smul c b hb ih => simpa [smul_mul_assoc] using P.smul_mem c ih
  apply top_unique
  intro b hb
  clear hb
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  induction p using MvPolynomial.induction_on with
  | C a =>
    change algebraMap k (targetNodeRing k) a ∈ P
    have h := P.smul_mem a (hu 0)
    rw [pow_zero] at h
    rw [Algebra.smul_def a (1 : targetNodeRing k), mul_one] at h
    exact h
  | add p q hp hq => simpa only [map_add] using P.add_mem hp hq
  | mul_X p j hp =>
    rw [map_mul]
    cases j
    · exact hmul _ hp false
    · exact hmul _ hp true

private lemma trace_mul_base (f : nodeRing k →+* targetNodeRing k)
    (setup : @DedekindDifferentSetup (nodeRing k) (targetNodeRing k) _ _ f.toAlgebra)
    (a : nodeRing k) (b : targetNodeRing k) :
    letI := f.toAlgebra
    setup.trace ((f (a) * b) ⊗ₜ[nodeRing k] (1 : FractionRing (nodeRing k))) =
      algebraMap (nodeRing k) (FractionRing (nodeRing k)) a *
        setup.trace (b ⊗ₜ[nodeRing k] (1 : FractionRing (nodeRing k))) := by
  let := f.toAlgebra
  let : Algebra (FractionRing (nodeRing k))
      (targetNodeRing k ⊗[nodeRing k] FractionRing (nodeRing k)) :=
    Algebra.TensorProduct.rightAlgebra
  have ht : (f a * b) ⊗ₜ[nodeRing k] (1 : FractionRing (nodeRing k)) =
      algebraMap (nodeRing k) (FractionRing (nodeRing k)) a •
        (b ⊗ₜ[nodeRing k] (1 : FractionRing (nodeRing k))) := by
    rw [Algebra.smul_def, Algebra.TensorProduct.right_algebraMap_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    have h := TensorProduct.smul_tmul (R := nodeRing k) a b (1 : FractionRing (nodeRing k))
    rw [Algebra.smul_def a b,
      Algebra.smul_def a (1 : FractionRing (nodeRing k)), mul_one] at h
    exact h
  rw [ht, map_smul, smul_eq_mul]

/-- One belongs to the complementary module exactly when the two branch degrees have the same
image in `k`.  The source states this as `n = m`; what the trace of one, `(nx+my)/(x+y)`, lies
in `A` for is `(n : k) = (m : k)`. -/
@[stacks 0BWP "complementary module criterion"]
theorem one_mem_complementaryModule_iff_natCast_eq
    (n m : ℕ) (hn : IsUnit (n : k)) (hm : IsUnit (m : k))
    (f : nodeRing k →+* targetNodeRing k)
    (hx : f (x k) = u k ^ n) (hy : f (y k) = v k ^ m)
    (hk : ∀ a : k, f (algebraMap k (nodeRing k) a) = algebraMap k (targetNodeRing k) a) :
    letI : Algebra (nodeRing k) (targetNodeRing k) := f.toAlgebra
    ∀ setup : DedekindDifferentSetup (nodeRing k) (targetNodeRing k),
      letI : DedekindDifferentSetup (nodeRing k) (targetNodeRing k) := setup
      ((1 : (targetNodeRing k) ⊗[nodeRing k] FractionRing (nodeRing k)) ∈
        setup.complementaryModule ↔ (n : k) = (m : k))  := by
  let A := nodeRing k
  let B := targetNodeRing k
  let K := FractionRing A
  let : Algebra A B := f.toAlgebra
  intro setup
  let : DedekindDifferentSetup A B := setup
  let : Algebra K (B ⊗[A] K) := Algebra.TensorProduct.rightAlgebra
  have hreg := node_x_add_y_mem_nonZeroDivisors k
  have hinj : Function.Injective (algebraMap A K) := IsLocalization.injective K le_rfl
  constructor
  · intro h
    obtain ⟨a, ha⟩ := (DedekindDifferentSetup.mem_complementaryModule setup 1).mp h 1
    simp only [map_one, one_mul] at ha
    apply node_weighted_sum_in_range k a (n : k) (m : k)
    apply hinj
    rw [map_mul, ha]
    exact trace_one k n m hn hm f hx hy hk setup
  · intro heq
    let : IsScalarTower k A B :=
      IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a => (hk a).symm)
    have hone : setup.trace 1 = algebraMap A K (algebraMap k A (n : k)) := by
      apply (IsLocalization.map_units K ⟨x k + y k, hreg⟩).mul_right_cancel
      rw [trace_one k n m hn hm f hx hy hk setup, ← map_mul (algebraMap A K)]
      apply congrArg (algebraMap A K)
      rw [heq, mul_add]
    have hpow (c : B) (a : A) (d : ℕ) (hd : 0 < d) (hc : f a = c ^ d)
        (htr : ∀ i, 1 ≤ i → i < d → setup.trace ((c ^ i) ⊗ₜ[A] (1 : K)) = 0)
        (r : ℕ) : setup.trace ((c ^ r) ⊗ₜ[A] (1 : K)) ∈ Set.range (algebraMap A K) := by
      refine forall_of_lt_of_sub (P := fun r => setup.trace ((c ^ r) ⊗ₜ[A] (1 : K)) ∈
        Set.range (algebraMap A K)) hd (fun r hrd => ?_) (fun r hle ih => ?_) r
      · rcases r.eq_zero_or_pos with rfl | hr
        · refine ⟨algebraMap k A (n : k), ?_⟩
          simpa only [pow_zero, ← Algebra.TensorProduct.one_def] using hone.symm
        · rw [htr r hr hrd]
          exact ⟨0, map_zero _⟩
      · obtain ⟨b, hb⟩ := ih
        refine ⟨a * b, ?_⟩
        rw [show c ^ r = f a * c ^ (r - d) by rw [hc, ← pow_add, Nat.add_sub_of_le hle],
          trace_mul_base k f setup, map_mul, hb]
    have hu (r : ℕ) := hpow (u k) (x k) n (pos_of_isUnit_natCast k hn) hx
      (trace_u_pow k n m hn hm f hx hy hk setup) r
    have hv (r : ℕ) := hpow (v k) (y k) m (pos_of_isUnit_natCast k hm) hy
      (trace_v_pow k n m hn hm f hx hy hk setup) r
    let T : B →ₗ[k] K :=
      ((setup.trace.restrictScalars A).comp
        ((TensorProduct.mk A B K).flip (1 : K))).restrictScalars k
    let P : Submodule k B :=
      (LinearMap.range (IsScalarTower.toAlgHom k A K).toLinearMap).comap T
    have hP : P = ⊤ := by
      apply top_unique
      rw [← targetNode_span_powers k]
      apply Submodule.span_le.mpr
      rintro b (⟨r, rfl⟩ | ⟨r, rfl⟩)
      exacts [hu r, hv r]
    rw [DedekindDifferentSetup.mem_complementaryModule]
    intro b
    rw [mul_one]
    exact show b ∈ P from hP ▸ Submodule.mem_top

private lemma linearMap_power_pairing
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] (t : S →ₗ[R] M)
    (c : S) (a : R) (n : ℕ) (hc : c ^ n = algebraMap R S a)
    (ht : ∀ i, 1 ≤ i → i < n → t (c ^ i) = 0)
    (i j : ℕ) (hi : 1 ≤ i) (hin : i < n) (hj : 1 ≤ j) (hjn : j < n) :
    t (c ^ (n - j) * c ^ i) = if i = j then a • t 1 else 0 := by
  rw [← pow_add]
  split_ifs with hij
  · subst i
    rw [Nat.sub_add_cancel (Nat.le_of_lt hjn), hc, ← mul_one (algebraMap R S a)]
    simpa only [Algebra.smul_def] using t.map_smul a 1
  · by_cases h : i < j
    · exact ht _ (by omega) (by omega)
    · rw [show n - j + i = n + (i - j) by omega, pow_add, hc]
      rw [← Algebra.smul_def]
      rw [t.map_smul, ht _ (by omega) (by omega), smul_zero]

/-- Pairing the `j`-th complementary power `c ^ (d - (j + 1))` against `c ^ i` under a functional
`t` that kills the powers `c ^ i`, `0 < i < d`, picks out the single term `j + 1 = i`. -/
private lemma sum_mul_power_pairing
    {R S K : Type*} [CommRing R] [CommRing S] [CommRing K] [Algebra R S] [Algebra R K]
    (t : S →ₗ[R] K) (c : S) (a : R) (d : ℕ) (hc : c ^ d = algebraMap R S a)
    (ht : ∀ i, 1 ≤ i → i < d → t (c ^ i) = 0) (γ : Fin (d - 1) → K) (i : ℕ)
    (hi : 1 ≤ i) (hid : i < d) (j : Fin (d - 1)) (hj : j.val + 1 = i) :
    ∑ l : Fin (d - 1), γ l * t (c ^ (d - (l.val + 1)) * c ^ i) =
      γ j * (algebraMap R K a * t 1) := by
  rw [Finset.sum_eq_single j]
  · rw [linearMap_power_pairing t c a d hc ht i (j.val + 1) hi hid (by omega) (by omega)]
    simp [Algebra.smul_def, hj]
  · intro l _ hl
    rw [linearMap_power_pairing t c a d hc ht i (l.val + 1) hi hid (by omega) (by omega)]
    simp [show i ≠ l.val + 1 from fun h => hl (Fin.ext (by omega))]
  · simp

private lemma targetNode_linearMap_ext
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (f : nodeRing k →+* targetNodeRing k)
    (hx : f (x k) = u k ^ n) (hy : f (y k) = v k ^ m)
    (hk : ∀ a : k, f (algebraMap k (nodeRing k) a) = algebraMap k (targetNodeRing k) a)
    {M : Type*} [AddCommGroup M] [Module (nodeRing k) M] :
    letI := f.toAlgebra
    ∀ p q : targetNodeRing k →ₗ[nodeRing k] M,
      p 1 = q 1 →
      (∀ i, 1 ≤ i → i < n → p (u k ^ i) = q (u k ^ i)) →
      (∀ j, 1 ≤ j → j < m → p (v k ^ j) = q (v k ^ j)) → p = q := by
  let := f.toAlgebra
  intro p q h1 hu hv
  have hpow (c : targetNodeRing k) (a : nodeRing k) (d : ℕ)
      (hd : 0 < d) (hc : f a = c ^ d)
      (h : ∀ i, 1 ≤ i → i < d → p (c ^ i) = q (c ^ i)) (r : ℕ) :
      p (c ^ r) = q (c ^ r) := by
    refine forall_of_lt_of_sub (P := fun r => p (c ^ r) = q (c ^ r)) hd (fun r hrd => ?_)
      (fun r hle ih => ?_) r
    · rcases r.eq_zero_or_pos with rfl | hr
      · simpa using h1
      · exact h r hr hrd
    · have he : c ^ r = a • c ^ (r - d) := by
        rw [Algebra.smul_def]
        change c ^ r = f a * c ^ (r - d)
        rw [hc, ← pow_add, Nat.add_sub_of_le hle]
      rw [he, p.map_smul, q.map_smul, ih]
  have hmap : algebraMap k (targetNodeRing k) =
      (algebraMap (nodeRing k) (targetNodeRing k)).comp (algebraMap k (nodeRing k)) := by
    ext a
    exact (hk a).symm
  let : IsScalarTower k (nodeRing k) (targetNodeRing k) :=
    IsScalarTower.of_algebraMap_eq' hmap
  let : Module k M := Module.compHom M (algebraMap k (nodeRing k))
  let : IsScalarTower k (nodeRing k) M := ⟨fun a b m => by
    change (a • b) • m = (algebraMap k (nodeRing k) a) • (b • m)
    rw [Algebra.smul_def a b, mul_smul]⟩
  apply LinearMap.ext
  intro b
  have hb : b ∈ Submodule.span k (Set.range (fun i : ℕ => u k ^ i) ∪
      Set.range (fun i : ℕ => v k ^ i)) := by
    rw [targetNode_span_powers]
    trivial
  induction hb using Submodule.span_induction with
  | mem z hz =>
    rcases hz with ⟨r, rfl⟩ | ⟨r, rfl⟩
    · exact hpow _ _ _ hn hx hu r
    · exact hpow _ _ _ hm hy hv r
  | zero => simp
  | add a b ha hb ia ib => simp only [map_add, ia, ib]
  | smul c b hb ih =>
    exact show p.restrictScalars k (c • b) = q.restrictScalars k (c • b) by
      rw [map_smul, map_smul]
      exact congrArg (c • ·) ih

private lemma node_annihilator_y (a : nodeRing k) (h : y k * a = 0) :
    ∃ b, a = x k * b := by
  obtain ⟨b, c, _, hc⟩ := node_coordinate_syzygy k 0 a (by simpa using h)
  exact ⟨c, hc⟩

private lemma node_annihilator_x (a : nodeRing k) (h : x k * a = 0) :
    ∃ b, a = y k * b := by
  obtain ⟨b, c, hb, _⟩ := node_coordinate_syzygy k a 0 (by simpa using h)
  exact ⟨b, hb⟩

/-- The section of `B` dual to a functional `φ` on `B` under a trace form `T` with the trace
values of the node example: if `φ` is divisible by `x` on the `u`-branch monomials and by `y` on
the `v`-branch monomials, the displayed combination of branch monomials pairs with every element
of `B` under `T` exactly as `φ` does. -/
private lemma node_trace_dual_section
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (f : nodeRing k →+* targetNodeRing k)
    (hx : f (x k) = u k ^ n) (hy : f (y k) = v k ^ m)
    (hk : ∀ a : k, f (algebraMap k (nodeRing k) a) = algebraMap k (targetNodeRing k) a) :
    letI := f.toAlgebra
    ∀ (T : targetNodeRing k →ₗ[nodeRing k] FractionRing (nodeRing k))
      (φ : targetNodeRing k →ₗ[nodeRing k] nodeRing k)
      (α : Fin (n - 1) → nodeRing k) (β : Fin (m - 1) → nodeRing k) (c : nodeRing k),
      T 1 = (n : FractionRing (nodeRing k)) →
      (∀ i, 1 ≤ i → i < n → T (u k ^ i) = 0) →
      (∀ i, 1 ≤ i → i < m → T (v k ^ i) = 0) →
      (∀ j : Fin (n - 1), φ (u k ^ (j.val + 1)) = x k * α j) →
      (∀ j : Fin (m - 1), φ (v k ^ (j.val + 1)) = y k * β j) →
      algebraMap (nodeRing k) (FractionRing (nodeRing k)) c
          * (n : FractionRing (nodeRing k)) = 1 →
      ∀ b : targetNodeRing k,
      b = (c * φ 1) • (1 : targetNodeRing k) +
          ∑ j : Fin (n - 1), (c * α j) • u k ^ (n - (j.val + 1)) +
          ∑ j : Fin (m - 1), (c * β j) • v k ^ (m - (j.val + 1)) →
      ∀ r : targetNodeRing k,
        T (b * r) = algebraMap (nodeRing k) (FractionRing (nodeRing k)) (φ r) := by
  let A := nodeRing k
  let B := targetNodeRing k
  let K := FractionRing A
  let : Algebra A B := f.toAlgebra
  have : SMulCommClass A A B := ⟨fun a b z => by
    change f a * (f b * z) = f b * (f a * z)
    ring⟩
  have : IsScalarTower A A B := ⟨fun a b z => by
    change f (a * b) * z = f a * (f b * z)
    rw [map_mul, mul_assoc]⟩
  let iA : A →+* K := algebraMap A K
  intro T φ α β c hT10 hTu hTv hα hβ hcK0 b hbdef
  have hT1 : T 1 = (n : K) := hT10
  have hcK : iA c * (n : K) = 1 := hcK0
  have hb (r : B) : T (b * r) =
      (iA c * iA (φ 1)) * T r +
      ∑ j : Fin (n - 1), (iA c * iA (α j)) * T (u k ^ (n - (j.val + 1)) * r) +
      ∑ j : Fin (m - 1), (iA c * iA (β j)) * T (v k ^ (m - (j.val + 1)) * r) := by
    have hs (d : A) (s r : B) : T ((d • s) * r) = iA d * T (s * r) := by
      calc
        T ((d • s) * r) = T (d • (s * r)) := congrArg T (smul_mul_assoc d s r)
        _ = d • T (s * r) := T.map_smul d (s * r)
        _ = iA d * T (s * r) := Algebra.smul_def d (T (s * r))
    simp only [hbdef, add_mul, map_add]
    rw [Finset.sum_mul (Finset.univ : Finset (Fin (n - 1)))
      (fun j => (c * α j) • u k ^ (n - (j.val + 1))) r,
      Finset.sum_mul (Finset.univ : Finset (Fin (m - 1)))
      (fun j => (c * β j) • v k ^ (m - (j.val + 1))) r]
    simp only [map_sum, hs, one_mul, map_mul]
  let p : B →ₗ[A] K := T.comp (Algebra.lmul A B b)
  let q : B →ₗ[A] K := (Algebra.linearMap A K).comp φ
  have hpq : p = q := by
    apply targetNode_linearMap_ext k n m hn hm f hx hy hk
    · change T (b * 1) = iA (φ 1)
      rw [hb, hT1]
      have hu0 (j : Fin (n - 1)) : T (u k ^ (n - (j.val + 1)) * 1) = 0 := by
        rw [mul_one]
        exact hTu _ (by omega) (by omega)
      have hv0 (j : Fin (m - 1)) : T (v k ^ (m - (j.val + 1)) * 1) = 0 := by
        rw [mul_one]
        exact hTv _ (by omega) (by omega)
      simp only [hu0, hv0, mul_zero, Finset.sum_const_zero, add_zero]
      calc
        (iA c * iA (φ 1)) * (n : K) = (iA c * (n : K)) * iA (φ 1) := by ring
        _ = iA (φ 1) := by rw [hcK, one_mul]
    · intro i hi hin
      change T (b * u k ^ i) = iA (φ (u k ^ i))
      rw [hb, hTu i hi hin, mul_zero, zero_add]
      have huv (j : Fin (m - 1)) : T (v k ^ (m - (j.val + 1)) * u k ^ i) = 0 := by
        have hzero : v k ^ (m - (j.val + 1)) * u k ^ i = 0 :=
          (mul_comm _ _).trans (targetNode_power_relation k _ _ (by omega) (by omega))
        exact (congrArg T hzero).trans T.map_zero
      simp only [huv, mul_zero, Finset.sum_const_zero, add_zero]
      obtain ⟨ii, hii⟩ : ∃ ii : Fin (n - 1), ii.val + 1 = i := ⟨⟨i - 1, by omega⟩, by simp; omega⟩
      rw [sum_mul_power_pairing T (u k) (x k) n hx.symm hTu _ i hi hin ii hii, hT1, ← hii, hα,
        map_mul]
      calc
        (iA c * iA (α ii)) * (iA (x k) * (n : K)) =
            (iA c * (n : K)) * (iA (x k) * iA (α ii)) := by ring
        _ = _ := by rw [hcK, one_mul]
    · intro i hi hin
      change T (b * v k ^ i) = iA (φ (v k ^ i))
      rw [hb, hTv i hi hin, mul_zero, zero_add]
      have huv (j : Fin (n - 1)) : T (u k ^ (n - (j.val + 1)) * v k ^ i) = 0 := by
        rw [targetNode_power_relation k _ _ (by omega) (by omega), map_zero]
      simp only [huv, mul_zero, Finset.sum_const_zero, zero_add]
      obtain ⟨ii, hii⟩ : ∃ ii : Fin (m - 1), ii.val + 1 = i := ⟨⟨i - 1, by omega⟩, by simp; omega⟩
      rw [sum_mul_power_pairing T (v k) (y k) m hy.symm hTv _ i hi hin ii hii, hT1, ← hii, hβ,
        map_mul]
      calc
        (iA c * iA (β ii)) * (iA (y k) * (n : K)) =
            (iA c * (n : K)) * (iA (y k) * iA (β ii)) := by ring
        _ = _ := by rw [hcK, one_mul]
  exact fun r => LinearMap.congr_fun hpq r

/-- When the branch degrees agree, the complementary module is precisely `B`. -/
@[stacks 0BWP "complementary module equals B"]
theorem complementaryModule_eq_range
    (n m : ℕ) (hn : IsUnit (n : k)) (hm : IsUnit (m : k))
    (f : nodeRing k →+* targetNodeRing k)
    (hx : f (x k) = u k ^ n) (hy : f (y k) = v k ^ m)
    (hk : ∀ a : k, f (algebraMap k (nodeRing k) a) = algebraMap k (targetNodeRing k) a)
    (heq : (n : k) = (m : k)) :
    letI : Algebra (nodeRing k) (targetNodeRing k) := f.toAlgebra
    ∀ setup : DedekindDifferentSetup (nodeRing k) (targetNodeRing k),
      letI : DedekindDifferentSetup (nodeRing k) (targetNodeRing k) := setup
      ∀ z, z ∈ setup.complementaryModule ↔
        z ∈ Set.range (algebraMap (targetNodeRing k)
          ((targetNodeRing k) ⊗[nodeRing k] FractionRing (nodeRing k)))  := by
  let A := nodeRing k
  let B := targetNodeRing k
  let K := FractionRing A
  let : Algebra A B := f.toAlgebra
  let L := B ⊗[A] K
  intro setup
  let : DedekindDifferentSetup A B := setup
  let : Algebra K L := Algebra.TensorProduct.rightAlgebra
  let iA : A →+* K := algebraMap A K
  let iB : B →+* L := Algebra.TensorProduct.includeLeftRingHom
  let T : B →ₗ[A] K := (setup.trace.restrictScalars A).comp
    ((TensorProduct.mk A B K).flip (1 : K))
  have hT (b : B) : T b = setup.trace (iB b) := rfl
  have hnpos := pos_of_isUnit_natCast k hn
  have hmpos := pos_of_isUnit_natCast k hm
  have hinj : Function.Injective iA := IsLocalization.injective K le_rfl
  have hone : (1 : L) ∈ setup.complementaryModule :=
    (one_mem_complementaryModule_iff_natCast_eq k n m hn hm f hx hy hk setup).mpr heq
  have hmem (b : B) : iB b ∈ setup.complementaryModule := by
    have h := setup.complementaryModule.smul_mem b hone
    have he : b • (1 : L) = iB b := by
      calc
        b • (1 : L) = (algebraMap B L b) * (1 : L) := Algebra.smul_def b (1 : L)
        _ = algebraMap B L b := mul_one (algebraMap B L b)
        _ = iB b := rfl
    exact he ▸ h
  have hT1 : T 1 = (n : K) := by
    have hreg := node_x_add_y_mem_nonZeroDivisors k
    apply (IsLocalization.map_units K ⟨x k + y k, hreg⟩).mul_right_cancel
    change setup.trace (iB 1) * _ = _
    rw [map_one, trace_one k n m hn hm f hx hy hk setup]
    have heqA : (n : A) = (m : A) := by
      simpa only [map_natCast] using congrArg (algebraMap k A) heq
    simp only [map_natCast, ← heqA, ← mul_add, map_mul]
    rfl
  have hTu (i : ℕ) (hi : 1 ≤ i) (hin : i < n) : T (u k ^ i) = 0 :=
    trace_u_pow k n m hn hm f hx hy hk setup i hi hin
  have hTv (i : ℕ) (hi : 1 ≤ i) (hin : i < m) : T (v k ^ i) = 0 :=
    trace_v_pow k n m hn hm f hx hy hk setup i hi hin
  intro z
  constructor
  · intro hz
    let e := (Stacks.Discriminant.complementaryModuleEquivDualizingModuleWithFormula setup).1
    let φ : B →ₗ[A] A := e ⟨z, hz⟩
    have hα (j : Fin (n - 1)) : ∃ a : A, φ (u k ^ (j.val + 1)) = x k * a := by
      apply node_annihilator_y
      change (y k) • φ (u k ^ (j.val + 1)) = 0
      rw [← φ.map_smul]
      change φ (f (y k) * u k ^ (j.val + 1)) = 0
      rw [hy]
      have hzero : v k ^ m * u k ^ (j.val + 1) = 0 :=
        (mul_comm _ _).trans (targetNode_power_relation k _ _ (by omega) hmpos)
      exact (congrArg φ hzero).trans φ.map_zero
    have hβ (j : Fin (m - 1)) : ∃ a : A, φ (v k ^ (j.val + 1)) = y k * a := by
      apply node_annihilator_x
      change (x k) • φ (v k ^ (j.val + 1)) = 0
      rw [← φ.map_smul]
      change φ (f (x k) * v k ^ (j.val + 1)) = 0
      rw [hx, targetNode_power_relation k _ _ hnpos (by omega), map_zero]
    choose α hα using hα
    choose β hβ using hβ
    let c : A := algebraMap k A ((n : k)⁻¹)
    have hc : c * (n : A) = 1 := by
      change algebraMap k A ((n : k)⁻¹) * (n : A) = 1
      rw [← map_natCast (algebraMap k A), ← map_mul, inv_mul_cancel₀ hn.ne_zero, map_one]
    have hcK : iA c * (n : K) = 1 := by
      have h := congrArg iA hc
      rwa [map_mul, map_natCast iA n, map_one] at h
    let b : B := (c * φ 1) • (1 : B) +
      ∑ j : Fin (n - 1), (c * α j) • u k ^ (n - (j.val + 1)) +
      ∑ j : Fin (m - 1), (c * β j) • v k ^ (m - (j.val + 1))
    have hpq : ∀ r : B, T (b * r) = iA (φ r) :=
      node_trace_dual_section k n m hnpos hmpos f hx hy hk T φ α β c hT1 hTu hTv hα hβ hcK b rfl
    have heb : e ⟨iB b, hmem b⟩ = φ := by
      apply LinearMap.ext
      intro r
      apply hinj
      rw [(Stacks.Discriminant.complementaryModuleEquivDualizingModuleWithFormula setup).2]
      change setup.trace (iB r * iB b) = iA (φ r)
      rw [← map_mul, mul_comm r b]
      exact hpq r
    exact ⟨b, congrArg Subtype.val (e.injective heb)⟩
  · rintro ⟨b, rfl⟩
    exact hmem b

/-- In that case the Dedekind different is the unit ideal of `B`. -/
@[stacks 0BWP "unit Dedekind different"]
theorem dedekindDifferent_eq_range
    (n m : ℕ) (hn : IsUnit (n : k)) (hm : IsUnit (m : k))
    (f : nodeRing k →+* targetNodeRing k)
    (hx : f (x k) = u k ^ n) (hy : f (y k) = v k ^ m)
    (hk : ∀ a : k, f (algebraMap k (nodeRing k) a) = algebraMap k (targetNodeRing k) a)
    (heq : (n : k) = (m : k)) :
    letI : Algebra (nodeRing k) (targetNodeRing k) := f.toAlgebra
    ∀ setup : DedekindDifferentSetup (nodeRing k) (targetNodeRing k),
      letI : DedekindDifferentSetup (nodeRing k) (targetNodeRing k) := setup
      ∀ z, z ∈ setup.dedekindDifferent ↔
        z ∈ Set.range (algebraMap (targetNodeRing k)
          ((targetNodeRing k) ⊗[nodeRing k] FractionRing (nodeRing k))) := by
  intro setup
  let : Algebra (nodeRing k) (targetNodeRing k) := f.toAlgebra
  let : DedekindDifferentSetup (nodeRing k) (targetNodeRing k) := setup
  intro z
  have hcomp := complementaryModule_eq_range k n m hn hm f hx hy hk heq setup
  constructor
  · intro hz
    rw [DedekindDifferentSetup.mem_dedekindDifferent] at hz
    have hone : (1 : (targetNodeRing k) ⊗[nodeRing k] FractionRing (nodeRing k)) ∈
        setup.complementaryModule :=
      (hcomp 1).2 ⟨1, by simp [Algebra.TensorProduct.one_def]⟩
    obtain ⟨b, hb⟩ := hz 1 hone
    exact ⟨b, by rwa [mul_one] at hb⟩
  · rintro ⟨b, rfl⟩
    rw [DedekindDifferentSetup.mem_dedekindDifferent]
    intro y hy
    have hy' := (hcomp y).1 hy
    rcases hy' with ⟨c, rfl⟩
    exact ⟨b * c, by simp⟩

/-- **The chartwise form of the definedness of the different of [Stacks, Tag 0BWM].** The trace
element of the generic fibre comes from a section of the relative dualizing module
`ω_{B/A} = Hom_A(B, A)` exactly when the two branch degrees have the same image in `k`. -/
@[stacks 0BWP "definedness of the different, on the chart"]
theorem exists_dual_trace_iff_natCast_eq
    (n m : ℕ) (hn : IsUnit (n : k)) (hm : IsUnit (m : k))
    (f : nodeRing k →+* targetNodeRing k)
    (hx : f (x k) = u k ^ n) (hy : f (y k) = v k ^ m)
    (hk : ∀ a : k, f (algebraMap k (nodeRing k) a) = algebraMap k (targetNodeRing k) a) :
    letI : Algebra (nodeRing k) (targetNodeRing k) := f.toAlgebra
    ∀ setup : DedekindDifferentSetup (nodeRing k) (targetNodeRing k),
      letI : Algebra (FractionRing (nodeRing k))
          ((targetNodeRing k) ⊗[nodeRing k] FractionRing (nodeRing k)) :=
        Algebra.TensorProduct.rightAlgebra
      ((∃ φ : Module.Dual (nodeRing k) (targetNodeRing k), ∀ b : targetNodeRing k,
            algebraMap (nodeRing k) (FractionRing (nodeRing k)) (φ b) =
              setup.trace (algebraMap (targetNodeRing k)
                ((targetNodeRing k) ⊗[nodeRing k] FractionRing (nodeRing k)) b)) ↔
        (n : k) = (m : k)) := by
  let : Algebra (nodeRing k) (targetNodeRing k) := f.toAlgebra
  intro setup
  exact (exists_dual_trace_iff_one_mem_complementaryModule setup).trans
    (one_mem_complementaryModule_iff_natCast_eq k n m hn hm f hx hy hk setup)

/-- **The chartwise form of the different of [Stacks, Tag 0BWM] being the unit ideal.** When the
two branch degrees have the same image in `k`, the Dedekind different ideal of `B` is the unit
ideal. -/
@[stacks 0BWP "the different is the unit ideal, on the chart"]
theorem dedekindDifferentIdeal_eq_top
    (n m : ℕ) (hn : IsUnit (n : k)) (hm : IsUnit (m : k))
    (f : nodeRing k →+* targetNodeRing k)
    (hx : f (x k) = u k ^ n) (hy : f (y k) = v k ^ m)
    (hk : ∀ a : k, f (algebraMap k (nodeRing k) a) = algebraMap k (targetNodeRing k) a)
    (heq : (n : k) = (m : k)) :
    letI : Algebra (nodeRing k) (targetNodeRing k) := f.toAlgebra
    ∀ setup : DedekindDifferentSetup (nodeRing k) (targetNodeRing k),
      dedekindDifferentIdeal setup = ⊤ := by
  let : Algebra (nodeRing k) (targetNodeRing k) := f.toAlgebra
  intro setup
  refine (Ideal.eq_top_iff_one _).mpr ?_
  exact (dedekindDifferent_eq_range k n m hn hm f hx hy hk heq setup _).mpr ⟨1, by simp⟩

end Stacks.Discriminant.NodeExample

end
