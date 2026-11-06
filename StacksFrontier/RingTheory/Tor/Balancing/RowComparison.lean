module

public import StacksFrontier.RingTheory.Tor.Balancing.DoubleComplex

/-!
# The row edge comparison `H_i(Tot A) ≃ H_i(R(A)_•)`

Injectivity and surjectivity of the edge map `cmpRfwd` for a double complex whose rows are
exact in positive degree, its inverse `cmpRinv`, and the comparison isomorphism `cmpR`.

This is part of the split of `StacksFrontier.RingTheory.Tor.Balancing`.
-/

@[expose] public section

open LinearMap Submodule

namespace Stacks.Tor.DoubleComplex

universe u
variable {R : Type u} [CommRing R]

/-! ### Bijectivity of `cmpRfwd`, hence the inverse `cmpRinv`. -/

/-! ### Injectivity of `cmpRfwd`

A `Dtot`-cycle `a` whose `k = 0` edge class is an `RDiff`-boundary is itself a `Dtot`-boundary.
With `g := tsign • a`, where `tsign m = (-1)^m·ε_m` and `ε_m = (-1)^{m(m+1)/2}`, the tuple `a` is a
`Dtot`-cycle iff `g` satisfies the sign-free cycle relation `d(g_{m+1}) = -δ(g_m)`. A tuple `c`
with `d(c_{m+1}) = δ(c_m) - g_m` then gives `b_m := ε_m • c_m` with `Dtot A … b = a`. -/

/-- The Koszul accumulation sign `ε_m = bEps m = (-1)^{m(m+1)/2}`. -/
def bEps (R : Type u) [CommRing R] (m : ℕ) : R := (-1 : R) ^ (m * (m + 1) / 2)

/-- `bEps 0 = 1`. -/
theorem bEps_zero : (bEps R 0 : R) = 1 := by simp [bEps]

/-- The recursion `bEps (m+1) = (-1)^(m+1) * bEps m`. -/
theorem bEps_succ (m : ℕ) :
    (bEps R (m + 1) : R) = (-1 : R) ^ (m + 1) * bEps R m := by
  rw [bEps, bEps, ← pow_add]
  congr 1
  have h2 : (m + 1) * (m + 2) / 2 = (m + 1) + m * (m + 1) / 2 := by
    rcases Nat.even_or_odd m with ⟨t, ht⟩ | ⟨t, ht⟩ <;> subst ht <;> ring_nf <;> omega
  omega

/-- The total Koszul sign `tsign m = (-1)^m · bEps m`. -/
def tsign (R : Type u) [CommRing R] (m : ℕ) : R := (-1 : R) ^ m * bEps R m

/-- `tsign 0 = 1`. -/
theorem tsign_zero : (tsign R 0 : R) = 1 := by
  simp [tsign, bEps]

/-- The recursion `tsign (m+1) = (-1)^m * tsign m`. -/
theorem tsign_succ (m : ℕ) :
    (tsign R (m + 1) : R) = (-1 : R) ^ m * tsign R m := by
  rw [tsign, tsign, bEps_succ]
  ring

/-- `tsign m · bEps m = (-1)^m`. -/
theorem tsign_mul_bEps (m : ℕ) :
    (tsign R m : R) * bEps R m = (-1 : R) ^ m := by
  rw [tsign, mul_assoc, bEps, ← pow_add, ← two_mul, pow_mul]
  simp

/-- The sign-free total differential: like `Dtot` but with `+δ` (no Koszul sign). -/
def Dtot0 (A : DoubleCx R) (i : ℕ) :
    TotChain A (i + 1) →ₗ[R] TotChain A i :=
  LinearMap.pi (fun m : Fin (i + 1) =>
    have hd1 : (m.succ : ℕ) = (m : ℕ) + 1 := Fin.val_succ m
    have hd2 : i + 1 - (m.succ : ℕ) = i - (m : ℕ) := by rw [hd1]; omega
    have hδ1 : (m.castSucc : ℕ) = (m : ℕ) := Fin.val_castSucc m
    have hδ2 : i + 1 - (m.castSucc : ℕ) = (i - (m : ℕ)) + 1 := by rw [hδ1]; omega
    ((A.d (m : ℕ) (i - (m : ℕ))).comp
        ((transp A (m.succ : ℕ) ((m : ℕ) + 1) (i + 1 - (m.succ : ℕ)) (i - (m : ℕ)) hd1
            hd2).toLinearMap.comp
          (LinearMap.proj m.succ)))
      + ((A.δ (m : ℕ) (i - (m : ℕ))).comp
          ((transp A (m.castSucc : ℕ) (m : ℕ) (i + 1 - (m.castSucc : ℕ)) ((i - (m : ℕ)) + 1) hδ1
              hδ2).toLinearMap.comp
            (LinearMap.proj m.castSucc))))

/-- The `m`-th component of the sign-free total differential: `A.d` applied to the
component at `m.succ` plus `A.δ` applied to the component at `m.castSucc`. -/
theorem Dtot0_apply (A : DoubleCx R) (i : ℕ)
    (x : ∀ k : Fin (i + 2), A.A k (i + 1 - (k : ℕ))) (m : Fin (i + 1)) :
    Dtot0 A i x m =
      A.d (m : ℕ) (i - (m : ℕ))
          (transp A (m.succ : ℕ) ((m : ℕ) + 1) (i + 1 - (m.succ : ℕ)) (i - (m : ℕ))
            (Fin.val_succ m) (by rw [Fin.val_succ]; omega) (x m.succ))
        + A.δ (m : ℕ) (i - (m : ℕ))
            (transp A (m.castSucc : ℕ) (m : ℕ) (i + 1 - (m.castSucc : ℕ)) ((i - (m : ℕ)) + 1)
              (Fin.val_castSucc m) (by rw [Fin.val_castSucc]; omega) (x m.castSucc)) := by
  rfl

/-- The sign-free cycle relation on `g : TotChain A i`, in `Nat`-index free-`b` form. -/
def CycG (A : DoubleCx R) (i : ℕ) (g : ∀ k : Fin (i + 1), A.A k (i - (k : ℕ))) : Prop :=
  ∀ (m : ℕ) (hm : m + 1 ≤ i) (b : ℕ) (hb : i - 1 - m = b),
    A.d m b
        (transp A (m + 1) (m + 1) (i - (m + 1)) b rfl (by omega)
          (g ⟨m + 1, by omega⟩))
      = - A.δ m b
        (transp A m m (i - m) (b + 1) rfl (by omega)
          (g ⟨m, by omega⟩))

/-- The descent relation on `c : TotChain A (i+1)`: `d(c_{m+1}) = δ(c_m) - g_m`. -/
def RelC (A : DoubleCx R) (i : ℕ) (g : ∀ k : Fin (i + 1), A.A k (i - (k : ℕ)))
    (c : ∀ k : Fin (i + 2), A.A k (i + 1 - (k : ℕ))) : Prop :=
  ∀ (m : ℕ) (hm : m ≤ i) (b : ℕ) (hb : i - m = b),
    A.d m b
        (transp A (m + 1) (m + 1) (i + 1 - (m + 1)) b rfl (by omega)
          (c ⟨m + 1, by omega⟩))
      = A.δ m b
          (transp A m m (i + 1 - m) (b + 1) rfl (by omega)
            (c ⟨m, by omega⟩))
        - transp A m m (i - m) b rfl (by omega) (g ⟨m, by omega⟩)

/-- The tail of a cycle witness `g`, transported onto `A.shiftR`. -/
def tailG (A : DoubleCx R) (i' : ℕ) (g : ∀ k : Fin (i' + 2), A.A k (i' + 1 - (k : ℕ))) :
    ∀ k : Fin (i' + 1), A.shiftR.A k (i' - (k : ℕ)) :=
  fun k => transp A ((k : ℕ) + 1) ((k : ℕ) + 1) (i' + 1 - ((k : ℕ) + 1)) (i' - (k : ℕ))
    rfl (by omega) (g k.succ)

-- Without this option, `rw` does not find its pattern in this proof.
set_option backward.isDefEq.respectTransparency false in
/-- Given a sign-free cycle `g` and `c0` with `δ c0 - g_0 ∈ range d`, there is a tuple `c` with
`c_0 = c0` satisfying the descent relation `RelC`. -/
theorem descent : ∀ (i : ℕ) (A : DoubleCx R) (_ : A.RowResolution)
    (g : ∀ k : Fin (i + 1), A.A k (i - (k : ℕ)))
    (c0 : A.A 0 (i + 1))
    (_ : A.δ 0 i c0 - g ⟨0, by omega⟩ ∈ LinearMap.range (A.d 0 i))
    (_ : CycG A i g),
    ∃ c : ∀ k : Fin (i + 2), A.A k (i + 1 - (k : ℕ)),
      c ⟨0, by omega⟩ = c0 ∧ RelC A i g c := by
  intro i
  induction i with
  | zero =>
      intro A _ g c0 hbase _
      refine ⟨Fin.cases (motive := fun k : Fin 2 => A.A (k : ℕ) (0 + 1 - (k : ℕ))) c0
        (fun j => transp A 1 ((j : ℕ) + 1) 0 (0 + 1 - ((j : ℕ) + 1)) (by omega) (by omega)
          (chooseLift (A.d 0 0) hbase)), ?_, ?_⟩
      · rfl
      · intro m hm b hb
        interval_cases m
        simp only [Nat.sub_zero] at hb
        subst hb
        show A.d 0 0 (transp A 1 1 (0 + 1 - 1) 0 rfl (by omega)
              (transp A 1 (0 + 1) 0 (0 + 1 - (0 + 1)) (by omega) (by omega) (chooseLift (A.d 0 0)
                  hbase)))
          = A.δ 0 0 (transp A 0 0 (0 + 1 - 0) (0 + 1) rfl (by omega) c0)
            - transp A 0 0 (0 - 0) 0 rfl (by omega) (g ⟨0, by omega⟩)
        rw [transp_trans]
        simp only [transp_rfl]
        rw [chooseLift_spec]
  | succ i' ih =>
      intro A hrow g c0 hbase hcyc
      set c1 : A.A 1 (i' + 1) := chooseLift (A.d 0 (i' + 1)) hbase with hc1def
      have hc1 : A.d 0 (i' + 1) c1 = A.δ 0 (i' + 1) c0 - g ⟨0, by omega⟩ :=
        chooseLift_spec (A.d 0 (i' + 1)) hbase
      set g' : ∀ k : Fin (i' + 1), A.shiftR.A k (i' - (k : ℕ)) := tailG A i' g with hg'def
      have hgval : ∀ (k : ℕ) (hk : k < i' + 1) (hk2 : k < i' + 2),
          g' ⟨k, hk⟩ = transp A (k + 1) (k + 1) (i' + 1 - (k + 1)) (i' - k) rfl (by omega)
            (g ⟨k + 1, by omega⟩) := by
        intro k hk hk2
        rfl
      have hcyc' : CycG A.shiftR i' g' := by
        intro m hm b hb
        have hraw := hcyc (m + 1) (by omega) b (by omega)
        show A.d (m + 1) b
            (transp A.shiftR (m + 1) (m + 1) (i' - (m + 1)) b rfl (by omega) (g' ⟨m + 1, by omega⟩))
          = - A.δ (m + 1) b
            (transp A.shiftR m m (i' - m) (b + 1) rfl (by omega) (g' ⟨m, by omega⟩))
        rw [shiftR_transp, shiftR_transp]
        rw [hgval (m + 1) (by omega) (by omega), hgval m (by omega) (by omega)]
        rw [transp_trans, transp_trans]
        convert hraw using 3
      have hbase' : A.shiftR.δ 0 i' c1 - g' ⟨0, by omega⟩ ∈ LinearMap.range (A.shiftR.d 0 i') := by
        have hcomm := congrArg (fun (f : _ →ₗ[R] _) => f c1) (A.comm 0 i')
        simp only [LinearMap.comp_apply] at hcomm
        have hδδ := congrArg (fun (f : _ →ₗ[R] _) => f c0) (A.δδ 0 i')
        simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hδδ
        have hcyc0 := hcyc 0 (by omega) i' (by omega)
        simp only [Nat.sub_zero] at hcyc0
        have step : A.d 0 i' (A.δ 1 i' c1) = - A.δ 0 i' (g ⟨0, by omega⟩) := by
          rw [← hcomm, hc1, map_sub, hδδ, zero_sub]
        have stepg : A.d 0 i' (g' ⟨0, by omega⟩) = - A.δ 0 i' (g ⟨0, by omega⟩) := by
          rw [hgval 0 (by omega) (by omega)]
          simp only [Nat.sub_zero]
          rw [hcyc0]
          simp only [transp_rfl]
        rw [show LinearMap.range (A.shiftR.d 0 i') = LinearMap.range (A.d 1 i') from rfl,
          ← hrow 0 i', LinearMap.mem_ker]
        show A.d 0 i' (A.δ 1 i' c1 - (show A.A 1 i' from g' ⟨0, by omega⟩)) = 0
        rw [map_sub, step, stepg, sub_self]
      obtain ⟨c', hc'0, hc'rel⟩ := ih A.shiftR (A.shiftR_RowResolution hrow) g' c1 hbase' hcyc'
      refine ⟨Fin.cases (motive := fun k : Fin (i' + 3) => A.A (k : ℕ) (i' + 1 + 1 - (k : ℕ))) c0
        (fun j => transp A ((j : ℕ) + 1) ((j : ℕ) + 1) (i' + 1 - (j : ℕ))
          (i' + 1 + 1 - ((j : ℕ) + 1))
          rfl (by omega) (c' j)), ?_, ?_⟩
      · rfl
      · intro m hm b hb
        cases m with
        | zero =>
            simp only [Nat.sub_zero] at hb
            subst hb
            show A.d 0 (i' + 1)
                (transp A 1 1 (i' + 1 + 1 - 1) (i' + 1) rfl (by omega)
                  (transp A 1 1 (i' + 1 - 0) (i' + 1 + 1 - (0 + 1)) rfl (by omega)
                  (c' ⟨0, by omega⟩)))
              = A.δ 0 (i' + 1)
                  (transp A 0 0 (i' + 1 + 1 - 0) (i' + 1 + 1) rfl (by omega) c0)
                - transp A 0 0 (i' + 1 - 0) (i' + 1) rfl (by omega) (g ⟨0, by omega⟩)
            rw [transp_trans, hc'0]
            simp only [Nat.sub_zero, transp_rfl]
            rw [hc1]
        | succ m' =>
            have key := hc'rel m' (by omega) b (by omega)
            rw [shiftR_transp, shiftR_transp, shiftR_transp] at key
            rw [hgval m' (by omega) (by omega)] at key
            rw [transp_trans] at key
            have hkd : A.shiftR.d m' b = A.d (m' + 1) b := rfl
            have hkδ : A.shiftR.δ m' b = A.δ (m' + 1) b := rfl
            rw [hkd, hkδ] at key
            have hcc2 : (Fin.cases
                (motive := fun k : Fin (i' + 3) => A.A (k : ℕ) (i' + 1 + 1 - (k : ℕ))) c0
                  (fun j => transp A ((j : ℕ) + 1) ((j : ℕ) + 1) (i' + 1 - (j : ℕ))
                    (i' + 1 + 1 - ((j : ℕ) + 1))
                    rfl (by omega) (c' j)) ⟨m' + 1 + 1, by omega⟩)
                = transp A (m' + 1 + 1) (m' + 1 + 1) (i' + 1 - (m' + 1)) (i' + 1 + 1 - (m' + 1 + 1))
                    rfl (by omega) (c' ⟨m' + 1, by omega⟩) := rfl
            have hcc1 : (Fin.cases
                (motive := fun k : Fin (i' + 3) => A.A (k : ℕ) (i' + 1 + 1 - (k : ℕ))) c0
                  (fun j => transp A ((j : ℕ) + 1) ((j : ℕ) + 1) (i' + 1 - (j : ℕ))
                    (i' + 1 + 1 - ((j : ℕ) + 1))
                    rfl (by omega) (c' j)) ⟨m' + 1, by omega⟩)
                = transp A (m' + 1) (m' + 1) (i' + 1 - m') (i' + 1 + 1 - (m' + 1))
                    rfl (by omega) (c' ⟨m', by omega⟩) := rfl
            rw [hcc2, hcc1, transp_trans, transp_trans]
            exact key

/-- `g := tsign • a` satisfies the sign-free cycle relation `CycG` whenever `a` is
a `Dtot`-cycle. -/
theorem cycG_of_dtot (A : DoubleCx R) (j : ℕ)
    (a : ∀ k : Fin (j + 2), A.A (k : ℕ) (j + 1 - (k : ℕ)))
    (hcyc : Dtot A j a = 0) :
    CycG A (j + 1) (fun k => tsign R (k : ℕ) • a k) := by
  intro m hm b hb
  obtain rfl : b = j - m := by omega
  have hcm := congrFun hcyc ⟨m, by omega⟩
  rw [Dtot_apply] at hcm
  simp only [Pi.zero_apply] at hcm
  show A.d m (j - m)
      (transp A (m + 1) (m + 1) (j + 1 - (m + 1)) (j - m) rfl (by omega)
        (tsign R (((⟨m + 1, by omega⟩ : Fin (j + 2)) : ℕ)) • a ⟨m + 1, by omega⟩))
    = - A.δ m (j - m)
      (transp A m m (j + 1 - m) (j - m + 1) rfl (by omega)
        (tsign R (((⟨m, by omega⟩ : Fin (j + 2)) : ℕ)) • a ⟨m, by omega⟩))
  simp only [map_smul]
  have hcm' : A.d m (j - m)
        (transp A (m + 1) (m + 1) (j + 1 - (m + 1)) (j - m) rfl (by omega) (a ⟨m + 1, by omega⟩))
      + (-1 : R) ^ m • A.δ m (j - m)
          (transp A m m (j + 1 - m) (j - m + 1) rfl (by omega) (a ⟨m, by omega⟩)) = 0 := hcm
  have hda : A.d m (j - m)
        (transp A (m + 1) (m + 1) (j + 1 - (m + 1)) (j - m) rfl (by omega) (a ⟨m + 1, by omega⟩))
      = - ((-1 : R) ^ m • A.δ m (j - m)
          (transp A m m (j + 1 - m) (j - m + 1) rfl (by omega) (a ⟨m, by omega⟩))) :=
    eq_neg_of_add_eq_zero_left hcm'
  rw [hda, tsign_succ, smul_neg, smul_smul]
  rw [show (-1 : R) ^ m * tsign R m * (-1) ^ m = tsign R m by
    rw [mul_right_comm, ← pow_add, ← two_mul, pow_mul]; simp]

/-- The Koszul signs at `m.succ` and `m.castSucc` cancel: `ε_{m+1} x + (-1)^m ε_m x = 0`. -/
private theorem bEps_succ_smul_add_castSucc_smul {M : Type*} [AddCommGroup M] [Module R M]
    {n : ℕ} (m : Fin n) (x : M) :
    bEps R (m.succ : ℕ) • x + (-1 : R) ^ (m : ℕ) • bEps R (m.castSucc : ℕ) • x = 0 := by
  rw [Fin.val_succ, Fin.val_castSucc, bEps_succ, smul_smul, ← add_smul,
    show (-1 : R) ^ ((m : ℕ) + 1) * bEps R m + (-1) ^ (m : ℕ) * bEps R m = 0 by
      rw [pow_succ]; ring, zero_smul]

/-- With `c` satisfying the descent relation `RelC A (j+1) (tsign • a) c`, the
sign-adjusted tuple `b_m = bEps(↑m) • c_m` is a `Dtot`-preimage of `a`. -/
theorem dtot_b_eq (A : DoubleCx R) (j : ℕ)
    (a : ∀ k : Fin (j + 2), A.A (k : ℕ) (j + 1 - (k : ℕ)))
    (c : ∀ k : Fin (j + 3), A.A (k : ℕ) (j + 1 + 1 - (k : ℕ)))
    (hrel : RelC A (j + 1) (fun k => tsign R (k : ℕ) • a k) c) :
    Dtot A (j + 1) (fun k => bEps R (k : ℕ) • c k) = a := by
  funext m
  rw [Dtot_apply]
  simp only [map_smul]
  have hr := hrel (m : ℕ) (by omega) (j + 1 - (m : ℕ)) rfl
  show bEps R (m.succ : ℕ) •
        A.d (m : ℕ) (j + 1 - (m : ℕ))
          (transp A ((m : ℕ) + 1) ((m : ℕ) + 1) (j + 1 + 1 - ((m : ℕ) + 1)) (j + 1 - (m : ℕ))
            rfl (by omega) (c ⟨(m : ℕ) + 1, by omega⟩))
      + (-1 : R) ^ (m : ℕ) • bEps R (m.castSucc : ℕ) •
          A.δ (m : ℕ) (j + 1 - (m : ℕ))
            (transp A (m : ℕ) (m : ℕ) (j + 1 + 1 - (m : ℕ)) ((j + 1 - (m : ℕ)) + 1)
              rfl (by omega) (c ⟨(m : ℕ), by omega⟩)) = a m
  rw [hr]
  rw [smul_sub]
  rw [show ∀ (P Q S : A.A (m : ℕ) (j + 1 - (m : ℕ))), P - Q + S = (P + S) - Q from
    fun P Q S => by abel]
  rw [bEps_succ_smul_add_castSucc_smul, zero_sub]
  show - (bEps R (m.succ : ℕ) •
      transp A (m : ℕ) (m : ℕ) (j + 1 - (m : ℕ)) (j + 1 - (m : ℕ)) rfl (by omega)
        (tsign R (m : ℕ) • a ⟨(m : ℕ), by omega⟩)) = a m
  rw [transp_rfl, smul_smul, Fin.val_succ, bEps_succ, mul_assoc, mul_comm (bEps R _),
    tsign_mul_bEps, ← pow_add, show (m : ℕ) + 1 + m = 2 * m + 1 by ring, pow_succ, pow_mul]
  simp

/-- A `Dtot A j`-cycle whose `k = 0` component is an edge boundary `δ y + d w` is a
`Dtot A (j+1)`-boundary. -/
theorem mem_range_Dtot_succ_of_cycle (A : DoubleCx R) (hrow : A.RowResolution) (j : ℕ)
    (a : ∀ k : Fin (j + 2), A.A (k : ℕ) (j + 1 - (k : ℕ)))
    (hcyc : Dtot A j a = 0)
    (hbd : ∃ (y : A.A 0 (j + 2)) (w : A.A 1 (j + 1)),
        a (0 : Fin (j + 2)) = A.δ 0 (j + 1) y + A.d 0 (j + 1) w) :
    a ∈ LinearMap.range (Dtot A (j + 1)) := by
  obtain ⟨y, w, hbd⟩ := hbd
  set g : ∀ k : Fin (j + 2), A.A (k : ℕ) (j + 1 - (k : ℕ)) :=
    fun k => tsign R (k : ℕ) • a k with hgdef
  have hcyc' : CycG A (j + 1) g := cycG_of_dtot A j a hcyc
  have hg0 : g ⟨0, by omega⟩ = a (0 : Fin (j + 2)) := by
    show tsign R ((⟨0, by omega⟩ : Fin (j + 2)) : ℕ) • a ⟨0, by omega⟩ = a (0 : Fin (j + 2))
    have : tsign R ((⟨0, by omega⟩ : Fin (j + 2)) : ℕ) = 1 := tsign_zero
    rw [this, one_smul]
    rfl
  have hbase : A.δ 0 (j + 1) y - g ⟨0, by omega⟩ ∈ LinearMap.range (A.d 0 (j + 1)) := by
    rw [hg0, hbd]
    refine ⟨-w, ?_⟩
    rw [map_neg]
    abel
  obtain ⟨c, hc0, hrel⟩ := descent (j + 1) A hrow g y hbase hcyc'
  exact ⟨fun k => bEps R (k : ℕ) • c k, dtot_b_eq A j a c hrel⟩

/-- If the `k = 0` component `a 0` of the degree-0 total chain `a` is an edge boundary
`δ y + d w`, then `a` is a `Dtot`-boundary. -/
theorem injBound_zero (A : DoubleCx R)
    (a : ∀ k : Fin 1, A.A (k : ℕ) (0 - (k : ℕ)))
    (hbd : ∃ (y : A.A 0 1) (w : A.A 1 0),
        a (0 : Fin 1) = A.δ 0 0 y + A.d 0 0 w) :
    a ∈ LinearMap.range (Dtot A 0) := by
  obtain ⟨y, w, hyw⟩ := hbd
  refine ⟨Fin.cases y (fun x => transp A 1 ((x.succ : Fin 2) : ℕ) 0 (0 + 1 - ((x.succ : Fin 2) : ℕ))
      (by simp [Fin.val_succ, Fin.val_eq_zero]) (by simp [Fin.val_succ, Fin.val_eq_zero]) w) , ?_⟩
  funext k
  refine Fin.cases ?_ (fun z => z.elim0) k
  rw [Dtot_apply]
  simp only [Fin.val_zero, pow_zero, one_smul, Nat.sub_zero, Fin.cases_succ, Fin.castSucc_zero,
    Fin.cases_zero, transp_rfl]
  rw [transp_trans]
  simp only [ transp_rfl]
  rw [hyw, add_comm]

/-- A `Dtot A j`-cycle `a` (degree `j+1`) whose `k = 0` component `a 0` is an edge boundary
`δ y + d w` is a `Dtot A (j+1)`-boundary. -/
alias injBound_succ := Stacks.Tor.DoubleComplex.mem_range_Dtot_succ_of_cycle

-- Without this option, `rw` does not find its pattern in this proof.
set_option backward.isDefEq.respectTransparency false in
/-- If `cmpRfwd` sends the `Hthird A 0` class of `a` to `0`, then the `k = 0` component `a 0` is
an edge boundary `δ y + d w`. -/
theorem edgeBoundary_zero (A : DoubleCx R)
    (a : ∀ k : Fin 1, A.A (k : ℕ) (0 - (k : ℕ)))
    (hx : cmpRfwd A 0 (Submodule.Quotient.mk a) = 0) :
    ∃ (y : A.A 0 1) (w : A.A 1 0),
        a (0 : Fin 1) = A.δ 0 0 y + A.d 0 0 w := by
  have hx' : Submodule.Quotient.mk ((A.d 0 0).range.mkQ (a 0)) = (0 : A.RHom 0) := by
    rw [← hx]
    show _ = homologyMap (cmpRChainHom A) 0 (Submodule.Quotient.mk a)
    simp only [homologyMap]
    rfl
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx'
  obtain ⟨ybar, hybar⟩ := hx'
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.range (A.d 0 1)) ybar
  rw [DoubleCx.RDiff_mk] at hybar
  rw [Submodule.Quotient.eq] at hybar
  obtain ⟨w', hw'⟩ := hybar
  refine ⟨y, -w', ?_⟩
  rw [map_neg, hw', ← sub_eq_add_neg, sub_sub_cancel]

-- Without this option, `rw` does not find its pattern in this proof.
set_option backward.isDefEq.respectTransparency false in
/-- If `cmpRfwd` sends the `Hthird A (j+1)` class of a cycle `⟨a, ha⟩` to `0`, then `a 0` is an
edge boundary `δ y + d w`. -/
theorem edgeBoundary_succ (A : DoubleCx R) (j : ℕ)
    (a : ∀ k : Fin (j + 2), A.A (k : ℕ) (j + 1 - (k : ℕ)))
    (ha : Dtot A j a = 0)
    (hx : cmpRfwd A (j + 1) (Submodule.Quotient.mk ⟨a, by
      rw [LinearMap.mem_ker]; exact ha⟩) = 0) :
    ∃ (y : A.A 0 (j + 2)) (w : A.A 1 (j + 1)),
        a (0 : Fin (j + 2)) = A.δ 0 (j + 1) y + A.d 0 (j + 1) w := by
  have hmem : (A.d 0 (j + 1)).range.mkQ (a (0 : Fin (j + 2))) ∈ LinearMap.ker (A.RDiff j) := by
    rw [LinearMap.mem_ker, Submodule.mkQ_apply]
    erw [DoubleCx.RDiff_mk]
    rw [Submodule.Quotient.mk_eq_zero]
    have h0 := congrFun ha (0 : Fin (j + 1))
    rw [Dtot_apply, Pi.zero_apply] at h0
    rw [show ((-1 : R) ^ (((0 : Fin (j + 1)) : ℕ))) • A.δ ((0 : Fin (j + 1)) : ℕ)
        (j - ((0 : Fin (j + 1)) : ℕ))
          (transp A (((0 : Fin (j + 1)).castSucc : ℕ)) (((0 : Fin (j + 1)) : ℕ))
            (j + 1 - (((0 : Fin (j + 1)).castSucc : ℕ))) ((j - ((0 : Fin (j + 1)) : ℕ)) + 1)
            (Fin.val_castSucc _) (by rw [Fin.val_castSucc]; omega)
            (a ((0 : Fin (j + 1)).castSucc)))
        = A.δ 0 j (a (0 : Fin (j + 2))) by
          show (-1 : R) ^ (0 : ℕ) • A.δ 0 j (a (0 : Fin (j + 2))) = _
          rw [pow_zero, one_smul]] at h0
    refine ⟨- (transp A (((0 : Fin (j + 1)).succ : ℕ)) (((0 : Fin (j + 1)) : ℕ) + 1)
        (j + 1 - (((0 : Fin (j + 1)).succ : ℕ))) (j - ((0 : Fin (j + 1)) : ℕ))
        (Fin.val_succ _) (by rw [Fin.val_succ]; omega)
        (a ((0 : Fin (j + 1)).succ))), ?_⟩
    rw [map_neg]
    exact neg_eq_of_add_eq_zero_right h0
  have hx' : Submodule.Quotient.mk
      (⟨(A.d 0 (j + 1)).range.mkQ (a (0 : Fin (j + 2))), hmem⟩ :
        LinearMap.ker (A.RDiff j)) = (0 : A.RHom (j + 1)) := by
    rw [← hx]
    show _ = homologyMap (cmpRChainHom A) (j + 1) (Submodule.Quotient.mk ⟨a, _⟩)
    simp only [homologyMap]
    apply congrArg
    apply Subtype.ext
    show _ = ((cmpRChainHom A).f (j + 1)) a
    show _ = (A.d 0 (j + 1)).range.mkQ (a (0 : Fin (j + 2)))
    rfl
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply] at hx'
  obtain ⟨ybar, hybar⟩ := hx'
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.range (A.d 0 (j + 2))) ybar
  rw [DoubleCx.RDiff_mk] at hybar
  simp only [Submodule.mkQ_apply] at hybar
  rw [Submodule.Quotient.eq] at hybar
  obtain ⟨w', hw'⟩ := hybar
  refine ⟨y, -w', ?_⟩
  rw [map_neg, hw', ← sub_eq_add_neg, sub_sub_cancel]

-- Without this option, `rw` does not find its pattern in this proof.
set_option backward.isDefEq.respectTransparency false in
/-- `cmpRfwd` is injective: a `Dtot`-cycle whose `k = 0` class is an `R`-boundary is itself a
`Dtot`-boundary. -/
theorem cmpRfwd_injective (A : DoubleCx R) (hrow : A.RowResolution) (i : ℕ) :
    Function.Injective (cmpRfwd A i) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  rw [Submodule.mem_bot]
  cases i with
  | zero =>
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      obtain ⟨y, w, hbd⟩ := edgeBoundary_zero A a hx
      rw [Submodule.Quotient.mk_eq_zero]
      exact injBound_zero A a ⟨y, w, hbd⟩
  | succ j =>
      obtain ⟨ac, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      obtain ⟨a, ha⟩ := ac
      rw [LinearMap.mem_ker] at ha
      obtain ⟨y, w, hbd⟩ := edgeBoundary_succ A j a ha hx
      rw [Submodule.Quotient.mk_eq_zero]
      rw [Submodule.mem_comap, Submodule.subtype_apply]
      exact injBound_succ A hrow j a ha ⟨y, w, hbd⟩

/-! ### Surjectivity of `cmpRfwd`

The staircase tuple `t` satisfies the unsigned relation `d(t_{m+1}) = δ(t_m)`, while the `m`-th
component of `Dtot` carries the Koszul sign `(-1)^m`. The sign-adjusted tuple
`c_m := ε_m · t_m`, with `ε_m = (-1)^{m(m+1)/2}`, is a `Dtot`-cycle since
`ε_{m+1} + (-1)^m ε_m = 0`, and `c_0 = t_0 = a` since `ε_0 = 1`. -/

/-- The sign-adjusted staircase tuple `c_m = ε_m · t_m`, a `Dtot`-cycle with `c_0 = a`. -/
noncomputable def stairCycleTuple (A : DoubleCx R) (hrow : A.RowResolution)
    (n : ℕ) (a : A.A 0 (n + 1)) (h : A.StairCycle (n + 1) a) : TotChain A (n + 1) :=
  fun m => (bEps R (m : ℕ)) • A.stairTuple hrow (n + 1) a h m

/-- The `k = 0` component of the sign-adjusted staircase tuple built from `a` is
`a` itself. -/
theorem stairCycleTuple_zero (A : DoubleCx R) (hrow : A.RowResolution)
    (n : ℕ) (a : A.A 0 (n + 1)) (h : A.StairCycle (n + 1) a) :
    stairCycleTuple A hrow n a h (0 : Fin (n + 2)) = a := by
  show (bEps R ((0 : Fin (n + 2)) : ℕ)) • A.stairTuple hrow (n + 1) a h 0 = a
  have hs : (bEps R ((0 : Fin (n + 2)) : ℕ)) = 1 := by
    rw [Fin.val_zero]; exact bEps_zero
  rw [hs, one_smul, stairTuple_zero]

/-- The sign-adjusted staircase tuple is a `Dtot`-cycle. -/
theorem stairTuple_cycle (A : DoubleCx R) (hrow : A.RowResolution)
    (n : ℕ) (a : A.A 0 (n + 1)) (h : A.StairCycle (n + 1) a) :
    Dtot A n (stairCycleTuple A hrow n a h) = 0 := by
  funext m
  show Dtot A n (stairCycleTuple A hrow n a h) m = (0 : ∀ k : Fin (n + 1), A.A k (n - (k : ℕ))) m
  rw [Pi.zero_apply, Dtot_apply]
  show A.d (m : ℕ) (n - (m : ℕ))
        (transp A (m.succ : ℕ) ((m : ℕ) + 1) (n + 1 - (m.succ : ℕ)) (n - (m : ℕ)) _ _
          (bEps R ((m.succ : Fin (n + 2)) : ℕ) • A.stairTuple hrow (n + 1) a h m.succ))
      + ((-1 : R) ^ (m : ℕ)) •
        A.δ (m : ℕ) (n - (m : ℕ))
          (transp A (m.castSucc : ℕ) (m : ℕ) (n + 1 - (m.castSucc : ℕ)) ((n - (m : ℕ)) + 1) _ _
            (bEps R ((m.castSucc : Fin (n + 2)) : ℕ) • A.stairTuple hrow (n + 1) a h
                m.castSucc))
      = 0
  simp only [map_smul]
  rw [stairTuple_step n A hrow a h m]
  exact bEps_succ_smul_add_castSucc_smul m _

-- Without this option, `rw` does not find its pattern in this proof.
set_option backward.isDefEq.respectTransparency false in
/-- `cmpRfwd` is surjective: every `R`-cycle class is the image of the `Hthird` class of the
sign-adjusted staircase tuple. -/
theorem cmpRfwd_surjective (A : DoubleCx R) (hrow : A.RowResolution) (i : ℕ) :
    Function.Surjective (cmpRfwd A i) := by
  cases i with
  | zero =>
      intro y
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      obtain ⟨a₀, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.range (A.d 0 0)) z
      refine ⟨Submodule.Quotient.mk
        (Fin.cases (motive := fun k : Fin 1 => A.A (k : ℕ) (0 - (k : ℕ))) a₀
          (fun j => j.elim0) : TotChain A 0), ?_⟩
      show homologyMap (cmpRChainHom A) 0 (Submodule.Quotient.mk _) = _
      simp only [homologyMap]
      rfl
  | succ j =>
      intro y
      obtain ⟨zc, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      obtain ⟨z, hz⟩ := zc
      obtain ⟨a₀, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.range (A.d 0 (j + 1))) z
      rw [LinearMap.mem_ker, DoubleCx.RDiff_mk, Submodule.Quotient.mk_eq_zero] at hz
      have hcyc : A.StairCycle (j + 1) a₀ := hz
      refine ⟨Submodule.Quotient.mk ⟨stairCycleTuple A hrow j a₀ hcyc, ?_⟩, ?_⟩
      · rw [LinearMap.mem_ker]; exact stairTuple_cycle A hrow j a₀ hcyc
      · show homologyMap (cmpRChainHom A) (j + 1) (Submodule.Quotient.mk _) = _
        erw [homologyMap, Submodule.mapQ_apply]
        congr 1
        apply Subtype.ext
        show ((cmpRChainHom A).f (j + 1)) (stairCycleTuple A hrow j a₀ hcyc) = _
        show (A.d 0 (j + 1)).range.mkQ (stairCycleTuple A hrow j a₀ hcyc (0 : Fin (j + 2))) = _
        rw [stairCycleTuple_zero]
        rfl

/-- The forward edge comparison as a linear equivalence (via bijectivity). -/
noncomputable def cmpRfwdEquiv (A : DoubleCx R) (hrow : A.RowResolution) (i : ℕ) :
    Hthird A i ≃ₗ[R] A.RHom i :=
  LinearEquiv.ofBijective (cmpRfwd A i)
    ⟨cmpRfwd_injective A hrow i, cmpRfwd_surjective A hrow i⟩

/-- The underlying linear map of `cmpRfwdEquiv` is `cmpRfwd`. -/
theorem cmpRfwdEquiv_toLinearMap (A : DoubleCx R) (hrow : A.RowResolution) (i : ℕ) :
    (cmpRfwdEquiv A hrow i : Hthird A i →ₗ[R] A.RHom i) = cmpRfwd A i :=
  rfl

/-- The inverse of the forward edge comparison, `H_i(R(A)_•) → H_i(Tot A)`. -/
noncomputable def cmpRinv (A : DoubleCx R) (hrow : A.RowResolution) (i : ℕ) :
    A.RHom i →ₗ[R] Hthird A i :=
  (cmpRfwdEquiv A hrow i).symm.toLinearMap

/-- `cmpRfwd` after `cmpRinv` is the identity on `H_i(R(A)_•)`. -/
theorem cmpR_right_inv (A : DoubleCx R) (hrow : A.RowResolution) (i : ℕ) :
    (cmpRfwd A i).comp (cmpRinv A hrow i) = LinearMap.id := by
  ext x
  exact (cmpRfwdEquiv A hrow i).apply_symm_apply x

/-- `cmpRinv` after `cmpRfwd` is the identity on `H_i(Tot A)`. -/
theorem cmpR_left_inv (A : DoubleCx R) (hrow : A.RowResolution) (i : ℕ) :
    (cmpRinv A hrow i).comp (cmpRfwd A i) = LinearMap.id := by
  ext x
  exact (cmpRfwdEquiv A hrow i).symm_apply_apply x

/-- The edge comparison isomorphism `H_i(Tot A) ≃ H_i(R(A)_•)`, for a double
complex whose rows are exact in positive degree. -/
noncomputable def cmpR (A : DoubleCx R) (hrow : A.RowResolution) (i : ℕ) :
    Hthird A i ≃ₗ[R] A.RHom i :=
  LinearEquiv.ofLinearMap (cmpRfwd A i) (cmpRinv A hrow i)
    (cmpR_right_inv A hrow i) (cmpR_left_inv A hrow i)

end Stacks.Tor.DoubleComplex
