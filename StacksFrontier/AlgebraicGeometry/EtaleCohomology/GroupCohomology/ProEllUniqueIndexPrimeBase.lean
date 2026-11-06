module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.ProcyclicCochainVanishing
public import StacksFrontier.Topology.Algebra.Group.ProPGroup
import Mathlib.Topology.Algebra.ClopenNhdofOne

/-!
# A pro-`ℓ` group with a unique open subgroup of index `ℓ` is procyclic

Let `ℓ` be a prime and `G` a compact, totally disconnected topological group which is pro-`ℓ`.
Assume that `G` has at most one open subgroup of index `ℓ`, and that for every `e` it has an open
normal subgroup of index `ℓ ^ e`. Then `G` is procyclic and torsion free: any element `σ` outside
the open subgroup of index `ℓ` generates every finite quotient of `G` (a proper subgroup of a
finite `ℓ`-group lies in a subgroup of index `ℓ`), so `G` is commutative, and the quotients of
order `ℓ ^ e` are cyclic with generator the image of `σ`. In particular `G` satisfies
`Stacks.GroupCohomology.HasPrimeBase` (`Stacks.GroupCohomology.hasPrimeBase_of_procyclic`), so its
continuous cohomology with torsion coefficients vanishes in degrees `≥ 2`.

This is the group-theoretic half of the computation of the cohomological dimension of the
fraction field of a strictly henselian discrete valuation ring: there a maximal pro-`ℓ` subgroup
of the absolute Galois group is `ℤ_ℓ(1)`.

## Main results

* `Stacks.GroupCohomology.exists_le_index_eq_of_isPGroup`: a proper subgroup of a finite
  `p`-group is contained in a subgroup of index `p`.
* `Stacks.GroupCohomology.zpowers_eq_top_quotient_of_unique_index`: an element outside the
  unique open subgroup of index `ℓ` generates every finite quotient.
* `Stacks.GroupCohomology.mul_comm_of_forall_zpowers_eq_top`: a group generated at every finite
  level by one element is commutative.
* `Stacks.GroupCohomology.hasPrimeBase_of_isProPGroup_of_unique_index_eq`: the prime base.

## References

* J.-P. Serre, *Corps locaux*, IV §2, and *Cohomologie galoisienne*, II §3.3.
-/

@[expose] public section

universe u

namespace Stacks.GroupCohomology

open Subgroup Stacks.GroupHomology.Procyclic

/-- **A proper subgroup of a finite `p`-group is contained in a subgroup of index `p`.** -/
theorem exists_le_index_eq_of_isPGroup {Q : Type*} [Group Q] [Finite Q] {p : ℕ} [hp : Fact p.Prime]
    (hQ : IsPGroup p Q) {H : Subgroup Q} (hH : H ≠ ⊤) : ∃ M : Subgroup Q, H ≤ M ∧ M.index = p := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQ
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (hQ.to_subgroup H)
  have hkn : k < n := by
    by_contra! h
    refine hH (Subgroup.eq_top_of_le_card _ ?_)
    rw [hn, hk]
    exact Nat.pow_le_pow_right hp.out.pos h
  have key : ∀ d, k + d ≤ n - 1 → ∃ M : Subgroup Q, H ≤ M ∧ Nat.card M = p ^ (k + d) := by
    intro d
    induction d with
    | zero => intro _; exact ⟨H, le_rfl, hk⟩
    | succ d ih =>
      intro hd
      obtain ⟨M, hHM, hM⟩ := ih (by omega)
      obtain ⟨M', hM', hMM'⟩ := Sylow.exists_subgroup_card_pow_succ (G := Q) (n := k + d)
        (by rw [hn]; exact pow_dvd_pow p (by omega)) hM
      exact ⟨M', hHM.trans hMM', by rw [hM', add_assoc]⟩
  obtain ⟨M, hHM, hM⟩ := key (n - 1 - k) (by omega)
  refine ⟨M, hHM, ?_⟩
  have h2 : p ^ n = p ^ (n - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n)]
  have h1 := M.card_mul_index
  rw [hM, hn, show k + (n - 1 - k) = n - 1 by omega, h2] at h1
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.out.pos _) h1

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {ℓ : ℕ}

omit [TotallyDisconnectedSpace G] in
/-- **An element outside the unique open subgroup of index `ℓ` generates every finite quotient**
of a pro-`ℓ` group. -/
theorem zpowers_eq_top_quotient_of_unique_index (hℓ : ℓ.Prime) (hG : IsProPGroup ℓ G)
    (huniq : ∀ U V : OpenSubgroup G, (U : Subgroup G).index = ℓ → (V : Subgroup G).index = ℓ →
      U = V)
    (N₁ : OpenSubgroup G) (hN₁ : (N₁ : Subgroup G).index = ℓ) {σ : G} (hσ : σ ∉ N₁)
    (U : OpenNormalSubgroup G) :
    zpowers (σ : G ⧸ (U : Subgroup G)) = ⊤ := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite (G ⧸ (U : Subgroup G)) := Subgroup.quotient_finite_of_isOpen _ U.isOpen'
  by_contra hne
  obtain ⟨M, hle, hM⟩ := exists_le_index_eq_of_isPGroup (hG U) hne
  let f := QuotientGroup.mk' (U : Subgroup G)
  let M' : OpenSubgroup G :=
    { toSubgroup := M.comap f
      isOpen' := Subgroup.isOpen_mono (H₁ := (U : Subgroup G))
        (fun x hx => by
          change f x ∈ M
          rw [show f x = 1 from (QuotientGroup.eq_one_iff x).2 hx]
          exact M.one_mem) U.isOpen' }
  have hM' : (M' : Subgroup G).index = ℓ := by
    change (M.comap f).index = ℓ
    rw [Subgroup.index_comap_of_surjective M (QuotientGroup.mk'_surjective _), hM]
  have hσM' : σ ∈ M' := hle (Subgroup.mem_zpowers _)
  exact hσ (huniq M' N₁ hM' hN₁ ▸ hσM')

/-- **A group generated at every finite level by one element is commutative**, for a compact
totally disconnected group. -/
theorem mul_comm_of_forall_zpowers_eq_top {σ : G}
    (h : ∀ U : OpenNormalSubgroup G, zpowers (σ : G ⧸ (U : Subgroup G)) = ⊤) (a b : G) :
    a * b = b * a := by
  by_contra hab
  have hx : a * b * (b * a)⁻¹ ≠ 1 := fun h1 => hab (mul_inv_eq_one.1 h1)
  have : T2Space G := IsTopologicalGroup.t2Space_iff_one_closed.mpr <| by
    rw [← totallyDisconnectedSpace_iff_connectedComponent_singleton.mp ‹_› 1]
    exact isClosed_connectedComponent
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (isOpen_compl_singleton (x := a * b * (b * a)⁻¹)) (Ne.symm hx)
  have hmem : ∀ g : G, (g : G ⧸ (U : Subgroup G)) ∈ zpowers (σ : G ⧸ (U : Subgroup G)) :=
    fun g => (h U).symm ▸ Subgroup.mem_top _
  have hcomm : (a : G ⧸ (U : Subgroup G)) * b = b * a := by
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hmem a)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hmem b)
    rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
  have hin : a * b * (b * a)⁻¹ ∈ (U : Subgroup G) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_mul, QuotientGroup.mk_mul, hcomm, mul_inv_cancel]
  exact hU hin rfl

/-- **The prime base of a pro-`ℓ` group with a unique open subgroup of index `ℓ`** and open normal
subgroups of every index `ℓ ^ e`: such a group is procyclic, isomorphic to `ℤ_ℓ`, and
`Stacks.GroupCohomology.hasPrimeBase_of_procyclic` applies. -/
theorem hasPrimeBase_of_isProPGroup_of_unique_index_eq (hℓ : ℓ.Prime) (hG : IsProPGroup ℓ G)
    (huniq : ∀ U V : OpenSubgroup G, (U : Subgroup G).index = ℓ → (V : Subgroup G).index = ℓ →
      U = V)
    (hquot : ∀ e : ℕ, ∃ N : OpenNormalSubgroup G, (N : Subgroup G).index = ℓ ^ e) :
    HasPrimeBase G := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨N₁, hN₁⟩ := hquot 1
  rw [pow_one] at hN₁
  obtain ⟨σ, hσ⟩ : ∃ σ : G, σ ∉ (N₁ : Subgroup G) := by
    by_contra! h
    have htop : (N₁ : Subgroup G) = ⊤ := eq_top_iff.2 fun x _ => h x
    rw [htop, Subgroup.index_top] at hN₁
    exact hℓ.one_lt.ne hN₁
  have hgen' := zpowers_eq_top_quotient_of_unique_index hℓ hG huniq N₁.toOpenSubgroup hN₁ hσ
  have hcomm := mul_comm_of_forall_zpowers_eq_top hgen'
  have hgen : GeneratesQuotients σ := fun U g => by
    have : Finite (G ⧸ (U : Subgroup G)) := Subgroup.quotient_finite_of_isOpen _ U.isOpen'
    obtain ⟨j, hj⟩ : (g : G ⧸ (U : Subgroup G)) ∈ Submonoid.powers (σ : G ⧸ (U : Subgroup G)) :=
      mem_powers_iff_mem_zpowers.2 ((hgen' U).symm ▸ Subgroup.mem_top _)
    exact ⟨j, hj.symm⟩
  refine hasPrimeBase_of_procyclic hcomm hgen fun p hp => ?_
  by_cases hpℓ : p = ℓ
  · subst hpℓ
    left
    intro e
    obtain ⟨N, hN⟩ := hquot e
    have : Finite (G ⧸ (N : Subgroup G)) := Subgroup.quotient_finite_of_isOpen _ N.isOpen'
    have hcard : Nat.card (G ⧸ (N : Subgroup G)) = p ^ e := hN
    let φ := zmodMulEquivOfGenerator (g := (σ : G ⧸ (N : Subgroup G)))
      (fun x => (hgen' N).symm ▸ Subgroup.mem_top x) hcard
    refine ⟨φ.symm.toMonoidHom.comp (QuotientGroup.mk' (N : Subgroup G)), ?_, ?_⟩
    · have hker : ((φ.symm.toMonoidHom.comp (QuotientGroup.mk' (N : Subgroup G))).ker : Set G) =
          (N : Set G) := by
        ext x
        simp only [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
          Function.comp_apply, QuotientGroup.mk'_apply, map_eq_one_iff _ φ.symm.injective,
          QuotientGroup.eq_one_iff]
        rfl
      exact hker ▸ N.isOpen'
    · simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
        QuotientGroup.mk'_apply]
      rw [MulEquiv.symm_apply_eq]
      exact (zmodMulEquivOfGenerator_apply_ofAdd_one _ _).symm
  · right
    intro N hdvd
    have : Finite (G ⧸ (N : Subgroup G)) := Subgroup.quotient_finite_of_isOpen _ N.isOpen'
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (hG N)
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).1
      (hp.dvd_of_dvd_pow (hk ▸ hdvd.trans (orderOf_dvd_natCard _))))

end Stacks.GroupCohomology

end
