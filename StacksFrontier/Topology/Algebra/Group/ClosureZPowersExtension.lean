module

public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Extending a Frobenius-invariant character across the closure of a Frobenius

Let `Γ` be a profinite group, `H` a closed normal subgroup and `ψ ∈ Γ` an element whose powers
are detected by open subgroups containing `H`: for every `L > 0` there is an open subgroup
`O ⊇ H` such that `ψ ^ j ∈ O` forces `L ∣ j`. (In the application `Γ = π₁(X)`, `H` is the
geometric fundamental group and `ψ` a power of a Frobenius lift; `O` is the stabilizer of a point
of the fibre of `X ×_k k_L`.) Then the procyclic group `C = closure ⟨ψ⟩` meets `H` trivially, so
that for a closed normal subgroup `N ≤ H` the product `N C` is a semidirect product. A character
`χ : N → A` with values in a discrete abelian group which is invariant under conjugation by `ψ`
therefore extends uniquely to a character `χ̃` of `N C` killing `ψ`, and `χ̃` is again locally
constant.

This is the group-theoretic step "a Frobenius-invariant character of `π₁(X_k̄)` comes from a
character of `π₁` of a cover defined over a finite field" in the proof of the geometric input of
Weil II 1.3.4 (Tag 03VH).

## Main results

* `Stacks.LAdic.eq_one_of_mem_topologicalClosure_zpowers_of_mem` — `closure ⟨ψ⟩ ∩ H = 1`.
* `Stacks.LAdic.exists_extension_of_conj_invariant` — the extension `χ̃` of a `ψ`-invariant
  locally constant character of `N` to `N ⊔ closure ⟨ψ⟩`, killing `ψ`.
* `Stacks.LAdic.isOpen_sup_topologicalClosure_zpowers_pow` — `H ⊔ closure ⟨φ ^ n⟩` is open when
  `H ⊔ ⟨φ⟩` is dense.
* `Stacks.LAdic.isOpen_and_exists_extension` and
  `Stacks.LAdic.encard_invariant_le_encard_extension` — for an open normal `U` and
  `ψ = φ ^ [Γ : U]`, `V = (H ⊓ U) ⊔ closure ⟨ψ⟩` is open and the `ψ`-invariant characters of
  `H ⊓ U` are at most as many as the characters of `V` killing `ψ`.
-/

@[expose] public section

open Topology

namespace Stacks.LAdic

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
  [T2Space Γ] [TotallyDisconnectedSpace Γ]

/-- An open subgroup of a compact group has positive index. -/
private theorem index_pos_of_isOpen {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] {K : Subgroup G} (hK : IsOpen (K : Set G)) :
    0 < K.index :=
  have := Subgroup.quotient_finite_of_isOpen K hK
  Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite

omit [T2Space Γ] in
/-- **The closure of the powers of `ψ` meets `H` trivially**, if the powers of `ψ` are detected
by open subgroups containing `H`. -/
theorem eq_one_of_mem_topologicalClosure_zpowers_of_mem {H : Subgroup Γ} {ψ : Γ}
    (hO : ∀ L : ℕ, 0 < L → ∃ O : Subgroup Γ, IsOpen (O : Set Γ) ∧ H ≤ O ∧
      ∀ j : ℤ, ψ ^ j ∈ O → (L : ℤ) ∣ j)
    {z : Γ} (hz : z ∈ (Subgroup.zpowers ψ).topologicalClosure) (hzH : z ∈ H) : z = 1 := by
  by_contra hne
  obtain ⟨W, hW⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (isOpen_compl_singleton (x := z)) (show (1 : Γ) ∈ ({z}ᶜ : Set Γ) from fun h => hne h.symm)
  have hzW : z ∉ (W : Subgroup Γ) := fun h => hW h rfl
  set r := (W : Subgroup Γ).index with hr
  have hr0 : 0 < r := index_pos_of_isOpen W.isOpen'
  have hψr : ψ ^ r ∈ (W : Subgroup Γ) := Subgroup.pow_index_mem _ ψ
  obtain ⟨O, hOo, hHO, hOdiv⟩ := hO r hr0
  -- the open neighbourhood `z (W ∩ O)` of `z` meets the powers of `ψ`
  have hopen : IsOpen {g : Γ | z⁻¹ * g ∈ ((W : Subgroup Γ) ⊓ O : Subgroup Γ)} :=
    ((W.isOpen').inter hOo).preimage (continuous_const.mul continuous_id)
  have hmem : z ∈ {g : Γ | z⁻¹ * g ∈ ((W : Subgroup Γ) ⊓ O : Subgroup Γ)} := by
    simp only [Set.mem_ofPred_eq, inv_mul_cancel]
    exact Subgroup.one_mem _
  obtain ⟨g, hg, hgψ⟩ := mem_closure_iff.1 hz _ hopen hmem
  obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 hgψ
  have hgW : z⁻¹ * ψ ^ a ∈ (W : Subgroup Γ) := (Subgroup.mem_inf.1 hg).1
  have hgO : z⁻¹ * ψ ^ a ∈ O := (Subgroup.mem_inf.1 hg).2
  have hψO : ψ ^ a ∈ O := by simpa using O.mul_mem (hHO hzH) hgO
  obtain ⟨t, rfl⟩ := hOdiv a hψO
  have hψW : ψ ^ ((r : ℤ) * t) ∈ (W : Subgroup Γ) := by
    rw [zpow_mul, zpow_natCast]
    exact Subgroup.zpow_mem _ hψr t
  apply hzW
  have := (W : Subgroup Γ).mul_mem hψW ((W : Subgroup Γ).inv_mem hgW)
  rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at this

section Extension

variable {N : Subgroup Γ} [N.Normal] {ψ : Γ} {A : Type*} [AddCommGroup A]

omit [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [AddCommGroup A] in
/-- A character of `N` invariant under conjugation by `ψ` is invariant under conjugation by every
element of the closure of the powers of `ψ`. -/
theorem conj_invariant_of_mem_topologicalClosure_zpowers {χ : N → A}
    (hχc : IsLocallyConstant χ)
    (hinv : ∀ a b : N, (b : Γ) = ψ * a * ψ⁻¹ → χ b = χ a)
    {c : Γ} (hc : c ∈ (Subgroup.zpowers ψ).topologicalClosure) (a : N) :
    χ ⟨c * a * c⁻¹, Subgroup.Normal.conj_mem inferInstance _ a.2 c⟩ = χ a := by
  -- the set of `c` with this property is closed and contains the powers of `ψ`
  let S : Set Γ :=
    {c | ∀ a : N, χ ⟨c * a * c⁻¹, Subgroup.Normal.conj_mem inferInstance _ a.2 c⟩ = χ a}
  have hS : IsClosed S := by
    simp only [S, Set.ofPred_forall]
    refine isClosed_iInter fun a => ?_
    have hcont : Continuous fun c : Γ =>
        (⟨c * a * c⁻¹, Subgroup.Normal.conj_mem inferInstance _ a.2 c⟩ : N) :=
      Continuous.subtype_mk (((continuous_id (X := Γ)).mul (continuous_const (y := (a : Γ)))).mul
        continuous_inv) _
    exact (hχc.comp_continuous hcont).isClosed_fiber (χ a)
  have hpow : ∀ j : ℤ, ψ ^ j ∈ S := by
    have hstep : ∀ (d : Γ), d ∈ S → ψ * d ∈ S ∧ ψ⁻¹ * d ∈ S := by
      intro d hd
      refine ⟨fun a => ?_, fun a => ?_⟩
      · rw [← hd a]
        exact hinv _ _ (by simp only [mul_inv_rev, mul_assoc])
      · rw [← hd a]
        have h := hinv ⟨ψ⁻¹ * (d * a * d⁻¹) * ψ, ?_⟩ ⟨d * a * d⁻¹, ?_⟩ ?_
        · refine Eq.trans ?_ h.symm
          congr 1
          simp only [mul_inv_rev, inv_inv, mul_assoc]
        · simpa [mul_assoc] using Subgroup.Normal.conj_mem inferInstance _
            (Subgroup.Normal.conj_mem inferInstance _ a.2 d) ψ⁻¹
        · exact Subgroup.Normal.conj_mem inferInstance _ a.2 d
        · simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
    intro j
    induction j using Int.induction_on with
    | zero => intro a; simp
    | succ i ih =>
      rw [zpow_add_one, ← (Commute.self_zpow ψ (i : ℤ)).eq]
      exact (hstep _ ih).1
    | pred i ih =>
      rw [zpow_sub_one, ← (Commute.self_zpow ψ (-(i : ℤ))).inv_left.eq]
      exact (hstep _ ih).2
  have hsub : ((Subgroup.zpowers ψ : Subgroup Γ) : Set Γ) ⊆ S := by
    rintro _ ⟨j, rfl⟩
    exact hpow j
  exact (closure_minimal hsub hS) hc a

variable (N ψ) in
/-- Multiplication `N × closure ⟨ψ⟩ → N ⊔ closure ⟨ψ⟩`, a bijection when the two factors meet
trivially. -/
noncomputable def mulClosureZPowersEquiv
    (hNC : ∀ z ∈ (Subgroup.zpowers ψ).topologicalClosure, z ∈ N → z = 1) :
    N × (Subgroup.zpowers ψ).topologicalClosure ≃ ↥(N ⊔ (Subgroup.zpowers ψ).topologicalClosure) :=
  Equiv.ofBijective
    (fun p => ⟨p.1 * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩)
    ⟨by
      rintro ⟨n, c⟩ ⟨n', c'⟩ h
      have h' : (n : Γ) * c = n' * c' := congrArg Subtype.val h
      have hz : (n' : Γ)⁻¹ * n = c' * (c : Γ)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h', mul_inv_cancel_right]
      have h1 := hNC _ (Subgroup.mul_mem _ c'.2 (Subgroup.inv_mem _ c.2))
        (hz ▸ N.mul_mem (N.inv_mem n'.2) n.2)
      rw [← hz, inv_mul_eq_one] at h1
      have h2 : (c : Γ) = c' := by
        rw [h1] at h'
        exact mul_left_cancel h'
      exact Prod.ext (Subtype.ext h1.symm) (Subtype.ext h2),
    by
      rintro ⟨m, hm⟩
      have hm' : m ∈ ((N ⊔ (Subgroup.zpowers ψ).topologicalClosure : Subgroup Γ) : Set Γ) := hm
      rw [Subgroup.normal_mul] at hm'
      obtain ⟨n, hn, c, hc, rfl⟩ := hm'
      exact ⟨(⟨n, hn⟩, ⟨c, hc⟩), rfl⟩⟩

omit [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] in
/-- The underlying element of `mulClosureZPowersEquiv N ψ hNC p` is the product `p.1 * p.2`. -/
@[simp]
theorem mulClosureZPowersEquiv_apply_coe
    (hNC : ∀ z ∈ (Subgroup.zpowers ψ).topologicalClosure, z ∈ N → z = 1)
    (p : N × (Subgroup.zpowers ψ).topologicalClosure) :
    ((mulClosureZPowersEquiv N ψ hNC p : ↥(N ⊔ (Subgroup.zpowers ψ).topologicalClosure)) : Γ) =
      p.1 * p.2 := rfl

omit [TotallyDisconnectedSpace Γ] in
/-- **Extension of a `ψ`-invariant character across `closure ⟨ψ⟩`.** Let `N` be a closed normal
subgroup meeting `closure ⟨ψ⟩` trivially and `χ : N → A` a locally constant additive map
invariant under conjugation by `ψ`. Then `χ` extends to a locally constant additive map on
`N ⊔ closure ⟨ψ⟩` killing `ψ`. -/
theorem exists_extension_of_conj_invariant (hN : IsClosed (N : Set Γ))
    (hNC : ∀ z ∈ (Subgroup.zpowers ψ).topologicalClosure, z ∈ N → z = 1)
    (χ : N → A) (hadd : ∀ a b, χ (a * b) = χ a + χ b) (hχc : IsLocallyConstant χ)
    (hinv : ∀ a b : N, (b : Γ) = ψ * a * ψ⁻¹ → χ b = χ a) :
    ∃ χ' : ↥(N ⊔ (Subgroup.zpowers ψ).topologicalClosure) → A,
      (∀ a b, χ' (a * b) = χ' a + χ' b) ∧ IsLocallyConstant χ' ∧
      (∀ n : N, χ' ⟨n, Subgroup.mem_sup_left n.2⟩ = χ n) ∧
      χ' ⟨ψ, Subgroup.mem_sup_right
        (Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers ψ))⟩ = 0 := by
  set C := (Subgroup.zpowers ψ).topologicalClosure
  have : CompactSpace N := isCompact_iff_compactSpace.1 hN.isCompact
  have : CompactSpace C :=
    isCompact_iff_compactSpace.1 (Subgroup.isClosed_topologicalClosure _).isCompact
  set e := mulClosureZPowersEquiv N ψ hNC
  have he_apply : ∀ p, ((e p : ↥(N ⊔ C)) : Γ) = p.1 * p.2 := fun p => rfl
  have he : Continuous e :=
    Continuous.subtype_mk ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)) _
  let h := Continuous.homeoOfEquivCompactToT2 he
  have hχ0 : χ 1 = 0 := by simpa using hadd 1 1
  have hfst : ∀ p, (h.symm (e p)).1 = p.1 := fun p => congrArg Prod.fst (h.symm_apply_apply p)
  refine ⟨fun m => χ (h.symm m).1, ?_, hχc.comp_continuous (continuous_fst.comp h.symm.continuous),
    ?_, ?_⟩
  · intro m m'
    obtain ⟨⟨n, c⟩, rfl⟩ := e.surjective m
    obtain ⟨⟨n', c'⟩, rfl⟩ := e.surjective m'
    have hconj : (c : Γ) * n' * (c : Γ)⁻¹ ∈ N := Subgroup.Normal.conj_mem inferInstance _ n'.2 c
    have hprod : e (⟨n, c⟩) * e (⟨n', c'⟩) =
        e (⟨n * ⟨(c : Γ) * n' * (c : Γ)⁻¹, hconj⟩, c * c'⟩) := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, he_apply, mul_assoc, inv_mul_cancel_left]
    have hs : ∀ p, h.symm (e p) = p := fun p => h.symm_apply_apply p
    simp only [hprod, hs]
    rw [hadd]
    congr 1
    exact conj_invariant_of_mem_topologicalClosure_zpowers hχc hinv c.2 n'
  · intro n
    have : (⟨n, Subgroup.mem_sup_left n.2⟩ : ↥(N ⊔ C)) = e (n, 1) := by
      apply Subtype.ext
      simp [he_apply]
    simp only [this, hfst]
  · have : (⟨ψ, Subgroup.mem_sup_right
        (Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers ψ))⟩ : ↥(N ⊔ C)) =
        e (1, ⟨ψ, Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers ψ)⟩) := by
      apply Subtype.ext
      simp [he_apply]
    simp only [this, hfst]
    exact hχ0

omit [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] in
/-- `(H ⊓ U) ⊔ closure ⟨ψ⟩ = U ⊓ (H ⊔ closure ⟨ψ⟩)` for an open subgroup `U ∋ ψ` and a normal
subgroup `H`; in particular it is open when `H ⊔ closure ⟨ψ⟩` is. -/
theorem inf_sup_topologicalClosure_zpowers_eq {H U : Subgroup Γ} [H.Normal]
    (hUo : IsOpen (U : Set Γ)) (hψU : ψ ∈ U) :
    H ⊓ U ⊔ (Subgroup.zpowers ψ).topologicalClosure =
      U ⊓ (H ⊔ (Subgroup.zpowers ψ).topologicalClosure) := by
  have hCU : (Subgroup.zpowers ψ).topologicalClosure ≤ U :=
    Subgroup.topologicalClosure_minimal _ ((Subgroup.zpowers_le).2 hψU)
      (U.isClosed_of_isOpen hUo)
  apply le_antisymm
  · exact sup_le (le_inf inf_le_right (inf_le_left.trans le_sup_left))
      (le_inf hCU le_sup_right)
  · rintro x ⟨hxU, hx⟩
    have hx' : x ∈ ((H ⊔ (Subgroup.zpowers ψ).topologicalClosure : Subgroup Γ) : Set Γ) := hx
    rw [Subgroup.normal_mul] at hx'
    obtain ⟨n, hn, c, hc, rfl⟩ := hx'
    have hnU : n ∈ U := by simpa using U.mul_mem hxU (U.inv_mem (hCU hc))
    exact Subgroup.mul_mem_sup (Subgroup.mem_inf.2 ⟨hn, hnU⟩) hc

omit [TotallyDisconnectedSpace Γ] in
/-- For a closed normal subgroup `H`, the subgroup `H ⊔ closure ⟨ψ⟩` is closed: as a set it is
the product `H · closure ⟨ψ⟩` of two compact sets. -/
theorem isClosed_sup_topologicalClosure_zpowers {H : Subgroup Γ} [H.Normal]
    (hH : IsClosed (H : Set Γ)) (ψ : Γ) :
    IsClosed ((H ⊔ (Subgroup.zpowers ψ).topologicalClosure : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.normal_mul]
  exact (hH.isCompact.mul (Subgroup.isClosed_topologicalClosure _).isCompact).isClosed

omit [TotallyDisconnectedSpace Γ] in
/-- **`H ⊔ closure ⟨φ ^ n⟩` is open** for `n > 0` when `H ⊔ ⟨φ⟩` is dense: it is closed, and its
translates by `φ ^ i`, `i < n`, cover the dense subgroup `H ⊔ ⟨φ⟩`, so it has finite index. -/
theorem isOpen_sup_topologicalClosure_zpowers_pow {H : Subgroup Γ} [H.Normal]
    (hH : IsClosed (H : Set Γ)) {φ : Γ}
    (hdense : Dense ((H ⊔ Subgroup.zpowers φ : Subgroup Γ) : Set Γ)) {n : ℕ} (hn : 0 < n) :
    IsOpen ((H ⊔ (Subgroup.zpowers (φ ^ n)).topologicalClosure : Subgroup Γ) : Set Γ) := by
  set S := H ⊔ (Subgroup.zpowers (φ ^ n)).topologicalClosure
  have hS : IsClosed (S : Set Γ) := isClosed_sup_topologicalClosure_zpowers hH _
  have hcover : ((H ⊔ Subgroup.zpowers φ : Subgroup Γ) : Set Γ) ⊆
      ⋃ i : Fin n, {g | (φ ^ (i : ℕ))⁻¹ * g ∈ S} := by
    intro g hg
    rw [Subgroup.normal_mul] at hg
    obtain ⟨h, hh, _, ⟨j, rfl⟩, rfl⟩ := hg
    have hn' : (0 : ℤ) < n := by exact_mod_cast hn
    set r := j % n
    set t := j / n
    have hr0 : 0 ≤ r := Int.emod_nonneg _ hn'.ne'
    have hrn : r < n := Int.emod_lt_of_pos _ hn'
    lift r to ℕ using hr0 with r' hr'
    refine Set.mem_iUnion.2 ⟨⟨r', by exact_mod_cast hrn⟩, ?_⟩
    have hj : j = r' + n * t := by
      rw [hr', mul_comm]; exact (Int.emod_add_ediv_mul j n).symm
    show (φ ^ r')⁻¹ * (h * (fun x => φ ^ x) j) ∈ S
    simp only
    rw [hj, zpow_add, zpow_natCast, ← mul_assoc, ← mul_assoc]
    refine S.mul_mem ?_ (Subgroup.mem_sup_right (Subgroup.le_topologicalClosure _ ?_))
    · refine Subgroup.mem_sup_left ?_
      have := Subgroup.Normal.conj_mem inferInstance h hh (φ ^ r')⁻¹
      rwa [inv_inv] at this
    · rw [zpow_mul, zpow_natCast]
      exact Subgroup.zpow_mem_zpowers _ _
  have hclosed : IsClosed (⋃ i : Fin n, {g | (φ ^ (i : ℕ))⁻¹ * g ∈ S}) :=
    isClosed_iUnion_of_finite fun i => hS.preimage (continuous_const.mul continuous_id)
  have huniv : (⋃ i : Fin n, {g | (φ ^ (i : ℕ))⁻¹ * g ∈ S}) = Set.univ :=
    Set.eq_univ_of_univ_subset (hdense.closure_eq ▸ closure_minimal hcover hclosed)
  have : Finite (Γ ⧸ S) := by
    refine Finite.of_surjective (fun i : Fin n => (QuotientGroup.mk (φ ^ (i : ℕ)) : Γ ⧸ S)) ?_
    rintro ⟨g⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (huniv.symm ▸ Set.mem_univ g)
    exact ⟨i, QuotientGroup.eq.2 hi⟩
  have := Subgroup.finiteIndex_of_finite_quotient (H := S)
  exact S.isOpen_of_isClosed_of_finiteIndex hS

/-- **The open subgroup through which a Frobenius-invariant character extends.** Let `H` be a
closed normal subgroup of `Γ` and `φ ∈ Γ` such that `H ⊔ ⟨φ⟩` is dense and the powers of `φ`
are detected by open subgroups containing `H`. For an open normal subgroup `U` put
`ψ = φ ^ [Γ : U] ∈ U`. Then `V = (H ⊓ U) ⊔ closure ⟨ψ⟩` is open, and every locally constant
additive `χ : H ⊓ U → A` invariant under conjugation by `ψ` is the restriction of a locally
constant additive map on `V` killing `ψ`. -/
theorem isOpen_and_exists_extension {H : Subgroup Γ} [H.Normal] (hH : IsClosed (H : Set Γ))
    {φ : Γ} (hdense : Dense ((H ⊔ Subgroup.zpowers φ : Subgroup Γ) : Set Γ))
    (hO : ∀ L : ℕ, 0 < L → ∃ O : Subgroup Γ, IsOpen (O : Set Γ) ∧ H ≤ O ∧
      ∀ j : ℤ, φ ^ j ∈ O → (L : ℤ) ∣ j)
    {U : Subgroup Γ} [U.Normal] (hUo : IsOpen (U : Set Γ)) :
    IsOpen ((H ⊓ U ⊔ (Subgroup.zpowers (φ ^ U.index)).topologicalClosure : Subgroup Γ) :
        Set Γ) ∧
      ∀ (χ : ↥(H ⊓ U) → A), (∀ a b, χ (a * b) = χ a + χ b) → IsLocallyConstant χ →
        (∀ a b : ↥(H ⊓ U), (b : Γ) = φ ^ U.index * a * (φ ^ U.index)⁻¹ → χ b = χ a) →
        ∃ χ' : ↥(H ⊓ U ⊔ (Subgroup.zpowers (φ ^ U.index)).topologicalClosure) → A,
          (∀ a b, χ' (a * b) = χ' a + χ' b) ∧ IsLocallyConstant χ' ∧
          (∀ n : ↥(H ⊓ U), χ' ⟨n, Subgroup.mem_sup_left n.2⟩ = χ n) ∧
          χ' ⟨φ ^ U.index, Subgroup.mem_sup_right
            (Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers _))⟩ = 0 := by
  have hidx : 0 < U.index := index_pos_of_isOpen hUo
  have hψU : φ ^ U.index ∈ U := Subgroup.pow_index_mem U φ
  refine ⟨?_, fun χ hadd hχc hinv => ?_⟩
  · rw [inf_sup_topologicalClosure_zpowers_eq hUo hψU]
    exact hUo.inter (isOpen_sup_topologicalClosure_zpowers_pow hH hdense hidx)
  · have hNC : ∀ z ∈ (Subgroup.zpowers (φ ^ U.index)).topologicalClosure, z ∈ H ⊓ U → z = 1 := by
      intro z hz hzN
      refine eq_one_of_mem_topologicalClosure_zpowers_of_mem (H := H) (fun L hL => ?_) hz
        (Subgroup.mem_inf.1 hzN).1
      obtain ⟨O, hOo, hHO, hdiv⟩ := hO (L * U.index) (Nat.mul_pos hL hidx)
      refine ⟨O, hOo, hHO, fun j hj => ?_⟩
      rw [← zpow_natCast, ← zpow_mul] at hj
      have := hdiv _ hj
      push_cast at this
      rw [mul_comm (L : ℤ)] at this
      exact (Int.dvd_of_mul_dvd_mul_left (by exact_mod_cast hidx.ne') this)
    exact exists_extension_of_conj_invariant (hH.inter (U.isClosed_of_isOpen hUo)) hNC χ hadd
      hχc hinv

/-- **Counting invariant characters through their extensions**: in the situation of
`Stacks.LAdic.isOpen_and_exists_extension`, there are at most as many locally constant additive
`χ : H ⊓ U → A` invariant under conjugation by `ψ = φ ^ [Γ : U]` as there are locally constant
additive maps on `V = (H ⊓ U) ⊔ closure ⟨ψ⟩` killing `ψ`. -/
theorem encard_invariant_le_encard_extension {H : Subgroup Γ} [H.Normal]
    (hH : IsClosed (H : Set Γ)) {φ : Γ}
    (hdense : Dense ((H ⊔ Subgroup.zpowers φ : Subgroup Γ) : Set Γ))
    (hO : ∀ L : ℕ, 0 < L → ∃ O : Subgroup Γ, IsOpen (O : Set Γ) ∧ H ≤ O ∧
      ∀ j : ℤ, φ ^ j ∈ O → (L : ℤ) ∣ j)
    {U : Subgroup Γ} [U.Normal] (hUo : IsOpen (U : Set Γ)) :
    {χ : ↥(H ⊓ U) → A | (∀ a b, χ (a * b) = χ a + χ b) ∧ IsLocallyConstant χ ∧
        ∀ a b : ↥(H ⊓ U), (b : Γ) = φ ^ U.index * a * (φ ^ U.index)⁻¹ → χ b = χ a}.encard ≤
      {χ' : ↥(H ⊓ U ⊔ (Subgroup.zpowers (φ ^ U.index)).topologicalClosure) → A |
        (∀ a b, χ' (a * b) = χ' a + χ' b) ∧ IsLocallyConstant χ' ∧
        χ' ⟨φ ^ U.index, Subgroup.mem_sup_right
          (Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers _))⟩ = 0}.encard := by
  set r : (↥(H ⊓ U ⊔ (Subgroup.zpowers (φ ^ U.index)).topologicalClosure) → A) →
      (↥(H ⊓ U) → A) := fun χ' n => χ' ⟨n, Subgroup.mem_sup_left n.2⟩
  refine le_trans (Set.encard_le_encard ?_) (Set.encard_image_le r _)
  rintro χ ⟨hadd, hχc, hinv⟩
  obtain ⟨χ', hadd', hχc', hext, hψ⟩ :=
    (isOpen_and_exists_extension (A := A) hH hdense hO hUo).2 χ hadd hχc hinv
  exact ⟨χ', ⟨hadd', hχc', hψ⟩, funext hext⟩

end Extension

end Stacks.LAdic
