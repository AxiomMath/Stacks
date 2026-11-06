module

public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.Basic
public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.Completion

/-!
# Riemann–Roch for a global function field, in cardinality form

Let `K` be a function field over a finite field `k`, with adele ring `A`. For a divisor `D` of `K`
(a finitely supported function from the places of `K` to `ℤ`) let
`A(D) = {a ∈ A | ord_v (a_v) ≥ -D(v) for all v}`, `L(D) = K ∩ A(D)` and
`h¹(D) = [A : K + A(D)]`, and `N(D) = ∏_v q_v ^ D(v)`.

We prove that `L(D)` and `A / (K + A(D))` are finite and that
`#L(D) / h¹(D) = N(D) · #L(0) / h¹(0)` (Riemann–Roch, without duality). Finiteness of
`A / (K + O)` comes from Riemann's inequality `N(D) ≤ B · #L(D)` for `D ≥ 0`, which is proved
with a basis of the integral closure of `k[t]` and the fundamental inequality.

## Main definitions

* `Stacks.Adeles.GlobalFunctionField.diag` — the diagonal embedding `K → A`.
* `Stacks.Adeles.GlobalFunctionField.adeleLattice` — `A(D)`.
* `Stacks.Adeles.GlobalFunctionField.principal` — the subgroup `K ⊆ A`.
* `Stacks.Adeles.GlobalFunctionField.divNorm` — `N(D)`.
-/

@[expose] public noncomputable section

open Polynomial IntermediateField WithZero

universe u

/-- For subgroups `H ⊓ B ≤ H ⊓ B'`: `#(H ⊓ B') = #(H ⊓ B) · [H ⊓ B' : H ⊓ B]`. -/
public theorem AddSubgroup.card_inf_eq_card_inf_mul_relIndex {G : Type*} [AddGroup G]
    (H : AddSubgroup G) {B B' : AddSubgroup G} (hB : B ≤ B') :
    Nat.card ↥(H ⊓ B') = Nat.card ↥(H ⊓ B) * (H ⊓ B).relIndex (H ⊓ B') := by
  have hHB : H ⊓ B ≤ H ⊓ B' := inf_le_inf_left _ hB
  rw [AddSubgroup.relIndex, ← Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hHB).toEquiv,
    AddSubgroup.card_mul_index]

/-- For subgroups `H` and `B ≤ B'` of an abelian group:
`[B' : B] = [H ⊓ B' : H ⊓ B] · [H ⊔ B' : H ⊔ B]`. -/
public theorem AddSubgroup.relIndex_eq_relIndex_inf_mul_relIndex_sup {G : Type*} [AddCommGroup G]
    (H : AddSubgroup G) {B B' : AddSubgroup G} (hB : B ≤ B') :
    B.relIndex B' = (H ⊓ B).relIndex (H ⊓ B') * (H ⊔ B).relIndex (H ⊔ B') := by
  set C := H ⊓ B'
  have hmod : (H ⊔ B) ⊓ B' = B ⊔ C := by
    ext x
    simp only [AddSubgroup.mem_inf, AddSubgroup.mem_sup, C]
    constructor
    · rintro ⟨⟨h, hh, b, hb, rfl⟩, hx⟩
      refine ⟨b, hb, h, ⟨hh, ?_⟩, add_comm _ _⟩
      simpa using B'.sub_mem hx (hB hb)
    · rintro ⟨b, hb, h, ⟨hh, hh'⟩, rfl⟩
      exact ⟨⟨h, hh, b, hb, add_comm _ _⟩, B'.add_mem (hB hb) hh'⟩
  rw [← AddSubgroup.relIndex_mul_relIndex B (B ⊔ C) B' le_sup_left (sup_le hB inf_le_right)]
  congr 1
  · rw [AddSubgroup.relIndex_sup_left, ← AddSubgroup.inf_relIndex_right B C]
    congr 1
    simp only [C]
    rw [inf_comm H B', ← inf_assoc, inf_eq_left.2 hB, inf_comm]
  · rw [← hmod, AddSubgroup.inf_relIndex_right, ← AddSubgroup.relIndex_sup_right B' (H ⊔ B)]
    congr 1
    rw [sup_comm, sup_assoc, sup_eq_right.2 hB]

/-- An index identity for subgroups `H` and `B ≤ B'` of an abelian group:
`#(H ⊓ B') · [G : H ⊔ B] = [B' : B] · #(H ⊓ B) · [G : H ⊔ B']`. -/
public theorem AddSubgroup.card_inf_mul_index_sup {G : Type*} [AddCommGroup G]
    (H : AddSubgroup G) {B B' : AddSubgroup G} (hB : B ≤ B') :
    Nat.card ↥(H ⊓ B') * (H ⊔ B).index = B.relIndex B' * Nat.card ↥(H ⊓ B) * (H ⊔ B').index := by
  rw [AddSubgroup.card_inf_eq_card_inf_mul_relIndex H hB,
    ← AddSubgroup.relIndex_mul_index (sup_le_sup_left hB _),
    AddSubgroup.relIndex_eq_relIndex_inf_mul_relIndex_sup H hB]
  ring

/-- If `G` is the directed union of subgroups `X ⊇ C` with `[X : C] ≤ M` (and finite), then
`[G : C] ≤ M`. -/
public theorem AddSubgroup.index_le_of_forall_finset {G : Type*} [AddGroup G] (C : AddSubgroup G)
    (M : ℕ) (hdir : ∀ s : Finset G, ∃ X : AddSubgroup G, C ≤ X ∧ (∀ g ∈ s, g ∈ X) ∧
      C.relIndex X ≠ 0 ∧ C.relIndex X ≤ M) :
    C.index ≠ 0 ∧ C.index ≤ M := by
  classical
  -- every finite set of cosets has at most `M` elements
  have hbound : ∀ S : Finset (G ⧸ C), S.card ≤ M := by
    intro S
    obtain ⟨X, hCX, hX, hne, hle⟩ := hdir (S.image Quotient.out)
    have : Finite (X ⧸ C.addSubgroupOf X) := by
      rw [AddSubgroup.relIndex, AddSubgroup.index] at hne
      exact Nat.finite_of_card_ne_zero hne
    let f : S → X ⧸ C.addSubgroupOf X := fun z =>
      (⟨Quotient.out (z : G ⧸ C), hX _ (Finset.mem_image_of_mem _ z.2)⟩ : X)
    have hf : Function.Injective f := by
      intro z w h
      have := QuotientAddGroup.eq.1 h
      rw [AddSubgroup.mem_addSubgroupOf] at this
      apply Subtype.ext
      rw [← Quotient.out_eq (z : G ⧸ C), ← Quotient.out_eq (w : G ⧸ C)]
      exact QuotientAddGroup.eq.2 (by simpa using this)
    calc S.card = Nat.card S := by simp
      _ ≤ Nat.card (X ⧸ C.addSubgroupOf X) := Nat.card_le_card_of_injective f hf
      _ = C.relIndex X := rfl
      _ ≤ M := hle
  have hfin : Finite (G ⧸ C) := by
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    obtain ⟨S, hS⟩ := Infinite.exists_subset_card_eq (G ⧸ C) (M + 1)
    exact absurd (hbound S) (by omega)
  let := Fintype.ofFinite (G ⧸ C)
  refine ⟨?_, ?_⟩
  · rw [AddSubgroup.index]
    exact Nat.card_ne_zero.2 ⟨inferInstance, hfin⟩
  · rw [AddSubgroup.index, Nat.card_eq_fintype_card, ← Finset.card_univ]
    exact hbound _

namespace Stacks.Adeles.GlobalFunctionField

section KFree

variable {K : Type u} [Field K]

variable (K) in
/-- The lattice `A(D) = {a ∈ A | a_v ∈ ϖ_v^(-D(v)) O_v for all v}` of a divisor `D`. -/
public def adeleLattice (D : Place K →₀ ℤ) : AddSubgroup (AdeleRing K) where
  carrier := {a | ∀ v, a v ∈ v.ball (-D v)}
  zero_mem' v := (v.ball (-D v)).zero_mem
  add_mem' ha hb v := (v.ball (-D v)).add_mem (ha v) (hb v)
  neg_mem' ha v := (v.ball (-D v)).neg_mem (ha v)

public theorem mem_adeleLattice {D : Place K →₀ ℤ} {a : AdeleRing K} :
    a ∈ adeleLattice K D ↔ ∀ v, a v ∈ v.ball (-D v) := Iff.rfl

variable (K) in
/-- `N(D) = ∏_v q_v ^ D(v)`. -/
public def divNorm (D : Place K →₀ ℤ) : ℚ := D.prod fun v n => (v.resCard : ℚ) ^ n

public theorem divNorm_zero : divNorm K 0 = 1 := Finsupp.prod_zero_index

public theorem divNorm_single (v : Place K) (n : ℤ) :
    divNorm K (Finsupp.single v n) = (v.resCard : ℚ) ^ n :=
  Finsupp.prod_single_index (zpow_zero _)

open scoped Classical in
/-- The adele with component `y` at `v` and `0` elsewhere. -/
public def singleAdele (v : Place K) (y : v.completion) : AdeleRing K :=
  ⟨Pi.single v y, (Set.finite_singleton v).subset fun w hw => by
    by_contra h
    apply hw
    change Pi.single v y w ∈ (w.integers : Set w.completion)
    rw [Pi.single_eq_of_ne (by simpa using h)]
    exact w.integers.zero_mem⟩

open scoped Classical in
public theorem singleAdele_apply_self (v : Place K) (y : v.completion) :
    singleAdele v y v = y :=
  Pi.single_eq_same v y

open scoped Classical in
public theorem singleAdele_apply_ne {v w : Place K} (h : w ≠ v) (y : v.completion) :
    singleAdele v y w = 0 :=
  Pi.single_eq_of_ne h y

/-- A value of `D` at a place of `S` is bounded by `∑_{w ∈ S} (D w).toNat`. -/
private theorem le_sum_toNat {D : Place K →₀ ℤ} {S : Finset (Place K)} {v : Place K}
    (hv : v ∈ S) : D v ≤ ∑ w ∈ S, (D w).toNat := by
  have : (D v).toNat ≤ ∑ w ∈ S, (D w).toNat :=
    Finset.single_le_sum (f := fun w => (D w).toNat) (fun _ _ => Nat.zero_le _) hv
  have := Int.self_le_toNat (D v)
  omega

/-- A nonzero polynomial evaluated at a transcendental element is nonzero. -/
private theorem aeval_ne_zero_of_transcendental {k : Type*} [Field k] [Algebra k K] {x : K}
    (hx : Transcendental k x) {f : k[X]} (hf : f ≠ 0) : aeval x f ≠ 0 := fun h =>
  hf (transcendental_iff_injective.1 hx (h.trans (map_zero _).symm))

end KFree

variable (k : Type u) [Field k] [Finite k] {K : Type u} [Field K] [Algebra k K]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]

include k

/-- An element of `K` is integral at all but finitely many places. -/
public theorem eventually_coeRingHom_mem_integers (κ : K) :
    ∀ᶠ v in Filter.cofinite, (v : Place K).coeRingHom κ ∈ v.integers := by
  rcases eq_or_ne κ 0 with rfl | hκ
  · exact Filter.Eventually.of_forall fun v => by simp
  refine (finite_setOf_ord_ne_zero k hκ).eventually_cofinite_notMem.mono fun v hv => ?_
  rw [Set.mem_ofPred_eq, not_not] at hv
  rw [← Place.mem_ball_zero_iff, Place.coeRingHom_mem_ball_iff (isDiscrete k v)]
  exact Or.inr hv.ge

variable (K) in
/-- The diagonal embedding `K → A`. -/
public def diag : K →+* AdeleRing K where
  toFun κ := ⟨fun v => v.coeRingHom κ, eventually_coeRingHom_mem_integers k κ⟩
  map_one' := RestrictedProduct.ext _ _ fun v => map_one v.coeRingHom
  map_mul' a b := RestrictedProduct.ext _ _ fun v => map_mul v.coeRingHom a b
  map_zero' := RestrictedProduct.ext _ _ fun v => map_zero v.coeRingHom
  map_add' a b := RestrictedProduct.ext _ _ fun v => map_add v.coeRingHom a b

@[simp]
public theorem diag_apply (κ : K) (v : Place K) : diag k K κ v = v.coeRingHom κ := rfl

public theorem diag_injective : Function.Injective (diag k K) := by
  obtain ⟨v⟩ := nonempty_place k (K := K)
  intro a b h
  exact v.coeRingHom.injective (congrArg (fun x : AdeleRing K => x v) h)

/-- The image of the diagonal embedding is the subring of principal adeles. -/
public theorem range_diag : (diag k K).range = principalAdeles K := by
  ext x
  simp only [RingHom.mem_range, mem_principalAdeles]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, fun v => rfl⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, RestrictedProduct.ext _ _ fun v => (hc v).symm⟩

variable (K) in
/-- The subgroup `K ⊆ A` of principal adeles. -/
public abbrev principal : AddSubgroup (AdeleRing K) := (diag k K).range.toAddSubgroup

public theorem adeleLattice_mono {D D' : Place K →₀ ℤ} (h : D ≤ D') :
    adeleLattice K D ≤ adeleLattice K D' := fun _ ha v =>
  Place.ball_anti (isDiscrete k v) (neg_le_neg (h v)) (ha v)

/-- A principal adele lies in `A(D)` exactly when its orders are at least `-D`. -/
public theorem diag_mem_adeleLattice_iff {D : Place K →₀ ℤ} {κ : K} :
    diag k K κ ∈ adeleLattice K D ↔ κ = 0 ∨ ∀ v, -D v ≤ v.ord κ := by
  rw [mem_adeleLattice]
  simp only [diag_apply, Place.coeRingHom_mem_ball_iff (isDiscrete k _)]
  rcases eq_or_ne κ 0 with rfl | hκ
  · simp
  · simp [hκ]

/-- Every adele lies in some `A(D)` with `D ≥ 0`. -/
public theorem exists_mem_adeleLattice (a : AdeleRing K) :
    ∃ D : Place K →₀ ℤ, 0 ≤ D ∧ a ∈ adeleLattice K D := by
  classical
  have hfin : {v : Place K | a v ∉ v.integers}.Finite := a.2
  choose m hm using fun v : Place K => Place.exists_mem_ball (isDiscrete k v) (a v)
  let D : Place K →₀ ℤ := Finsupp.ofSupportFinite (fun v => if a v ∈ v.integers then 0
    else max 0 (-m v)) (hfin.subset fun v hv => by
      by_contra h
      exact hv (ite_eq_left (not_not.1 h)))
  refine ⟨D, fun v => ?_, fun v => ?_⟩
  · simp only [D, Finsupp.coe_zero, Pi.zero_apply, Finsupp.ofSupportFinite_coe]
    split_ifs <;> simp
  · simp only [D, Finsupp.ofSupportFinite_coe]
    split_ifs with h
    · simpa [Place.mem_ball_zero_iff] using h
    · exact Place.ball_anti (isDiscrete k v) (by omega) (hm v)

public theorem divNorm_add (D E : Place K →₀ ℤ) :
    divNorm K (D + E) = divNorm K D * divNorm K E :=
  Finsupp.prod_add_index' (fun v => zpow_zero _) fun v a b =>
    zpow_add₀ (by exact_mod_cast (resCard_pos k v).ne') a b

public theorem divNorm_neg (D : Place K →₀ ℤ) : divNorm K (-D) = (divNorm K D)⁻¹ := by
  have h := divNorm_add k D (-D)
  rw [add_neg_cancel, divNorm_zero] at h
  exact eq_inv_of_mul_eq_one_right h.symm

public theorem divNorm_sub (D E : Place K →₀ ℤ) :
    divNorm K (D - E) = divNorm K D / divNorm K E := by
  rw [sub_eq_add_neg, divNorm_add k, divNorm_neg k, div_eq_mul_inv]

public theorem divNorm_pos (D : Place K →₀ ℤ) : 0 < divNorm K D :=
  Finset.prod_pos fun v _ => zpow_pos (by exact_mod_cast resCard_pos k v) _

/-- `[A(D + v) : A(D)] = q_v`. -/
public theorem relIndex_adeleLattice_single (D : Place K →₀ ℤ) (v : Place K) :
    (adeleLattice K D).relIndex (adeleLattice K (D + Finsupp.single v 1)) = v.resCard := by
  classical
  set D' := D + Finsupp.single v 1
  have hD' : D' v = D v + 1 := by simp [D']
  have hDw : ∀ w, w ≠ v → D' w = D w := fun w hw => by simp [D', hw.symm]
  set m := -D v - 1
  have hm : -D' v = m := by rw [hD']; ring
  -- evaluation at `v`, into `ϖ^m O_v`
  let ev : adeleLattice K D' →+ v.ball m :=
    { toFun := fun a => ⟨a.1 v, hm ▸ a.2 v⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let q : v.ball m →+ v.ball m ⧸ (v.ball (m + 1)).addSubgroupOf (v.ball m) :=
    QuotientAddGroup.mk' _
  let φ := q.comp ev
  have hsurj : Function.Surjective φ := by
    intro z
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective z
    have hmem : singleAdele v (y : v.completion) ∈ adeleLattice K D' := by
      intro w
      by_cases hw : w = v
      · subst hw
        rw [singleAdele_apply_self, hm]
        exact y.2
      · rw [singleAdele_apply_ne hw]
        exact (w.ball _).zero_mem
    refine ⟨⟨_, hmem⟩, ?_⟩
    show q ⟨singleAdele v (y : v.completion) v, _⟩ = q y
    congr 1
    exact Subtype.ext (singleAdele_apply_self v _)
  have hker : φ.ker = (adeleLattice K D).addSubgroupOf (adeleLattice K D') := by
    ext a
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
    show ((ev a : v.ball m) : v.ball m ⧸ (v.ball (m + 1)).addSubgroupOf (v.ball m)) = 0 ↔ _
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, mem_adeleLattice]
    show a.1 v ∈ v.ball (m + 1) ↔ _
    have hm1 : m + 1 = -D v := by ring
    rw [hm1]
    refine ⟨fun h w => ?_, fun h => h v⟩
    by_cases hw : w = v
    · subst hw
      exact h
    · have := a.2 w
      rwa [hDw w hw] at this
  rw [AddSubgroup.relIndex, ← hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj,
    AddSubgroup.card_top, ← AddSubgroup.index_eq_card, ← AddSubgroup.relIndex,
    Place.relIndex_ball (isDiscrete k v), Place.residueCard_eq_resCard]

/-- `[A(D + b·v) : A(D)] = q_v ^ b`. -/
public theorem relIndex_adeleLattice_single_nat (D : Place K →₀ ℤ) (v : Place K) (b : ℕ) :
    (adeleLattice K D).relIndex (adeleLattice K (D + Finsupp.single v (b : ℤ))) =
      v.resCard ^ b := by
  induction b with
  | zero => simp
  | succ b ih =>
    have hle1 : adeleLattice K D ≤ adeleLattice K (D + Finsupp.single v (b : ℤ)) :=
      adeleLattice_mono k (le_add_of_nonneg_right (by simp))
    have hle2 : adeleLattice K (D + Finsupp.single v (b : ℤ)) ≤
        adeleLattice K (D + Finsupp.single v (b : ℤ) + Finsupp.single v 1) :=
      adeleLattice_mono k (le_add_of_nonneg_right (by simp))
    have heq : D + Finsupp.single v ((b + 1 : ℕ) : ℤ) =
        D + Finsupp.single v (b : ℤ) + Finsupp.single v 1 := by
      rw [add_assoc, ← Finsupp.single_add]; push_cast; rfl
    rw [heq, ← AddSubgroup.relIndex_mul_relIndex _ _ _ hle1 hle2, ih,
      relIndex_adeleLattice_single k, pow_succ]

/-- `[A(D + E) : A(D)] = N(E)` for `E ≥ 0`. -/
public theorem relIndex_adeleLattice_add (D E : Place K →₀ ℤ) (hE : 0 ≤ E) :
    ((adeleLattice K D).relIndex (adeleLattice K (D + E)) : ℚ) = divNorm K E := by
  induction E using Finsupp.induction generalizing D with
  | zero => simp [divNorm_zero]
  | single_add a b f ha hb ih =>
    have hfa : f a = 0 := Finsupp.notMem_support_iff.1 ha
    have hb0 : 0 ≤ b := by simpa [hfa] using hE a
    have hf0 : 0 ≤ f := fun x => by
      by_cases hx : x = a
      · subst hx; simp [hfa]
      · simpa [Finsupp.single_apply, Ne.symm hx] using hE x
    have hle1 : adeleLattice K D ≤ adeleLattice K (D + f) :=
      adeleLattice_mono k (le_add_of_nonneg_right hf0)
    have hle2 : adeleLattice K (D + f) ≤ adeleLattice K (D + f + Finsupp.single a b) :=
      adeleLattice_mono k (le_add_of_nonneg_right (by simpa using hb0))
    have heq : D + (Finsupp.single a b + f) = D + f + Finsupp.single a b := by abel
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hb0
    rw [heq, ← AddSubgroup.relIndex_mul_relIndex _ _ _ hle1 hle2, Nat.cast_mul, ih D hf0,
      relIndex_adeleLattice_single_nat k, divNorm_add k, divNorm_single, mul_comm]
    push_cast
    rfl

/-- `[A(D') : A(D)] = N(D' - D)` for `D ≤ D'`. -/
public theorem relIndex_adeleLattice_of_le {D D' : Place K →₀ ℤ} (h : D ≤ D') :
    ((adeleLattice K D).relIndex (adeleLattice K D') : ℚ) = divNorm K (D' - D) := by
  have := relIndex_adeleLattice_add k D (D' - D) (sub_nonneg.2 h)
  rwa [add_sub_cancel] at this

public theorem relIndex_adeleLattice_ne_zero {D D' : Place K →₀ ℤ} (h : D ≤ D') :
    (adeleLattice K D).relIndex (adeleLattice K D') ≠ 0 := by
  have h1 := relIndex_adeleLattice_of_le k h
  have h2 := divNorm_pos k (D' - D)
  intro h0
  rw [h0, Nat.cast_zero] at h1
  linarith

variable (K) in
/-- `ℓ(D) = #L(D) = #(K ∩ A(D))`. -/
public abbrev ell (D : Place K →₀ ℤ) : ℕ := Nat.card ↥(principal k K ⊓ adeleLattice K D)

variable (K) in
/-- `h¹(D) = [A : K + A(D)]`. -/
public abbrev hOne (D : Place K →₀ ℤ) : ℕ := (principal k K ⊔ adeleLattice K D).index

public theorem mem_principal {x : AdeleRing K} : x ∈ principal k K ↔ ∃ κ, diag k K κ = x :=
  RingHom.mem_range

/-- `L(0)` is finite: its elements lie in every place. -/
public theorem finite_principal_inf_adeleLattice_zero :
    Finite ↥(principal k K ⊓ adeleLattice K 0) := by
  have hfin := (finite_setOf_forall_mem k (K := K)).image (diag k K)
  refine Set.Finite.to_subtype (hfin.subset ?_)
  rintro x ⟨hxH, hx⟩
  obtain ⟨κ, rfl⟩ := (mem_principal k).1 hxH
  refine ⟨κ, fun v => ?_, rfl⟩
  rcases (diag_mem_adeleLattice_iff k).1 hx with rfl | h
  · exact v.1.zero_mem
  · rcases eq_or_ne κ 0 with rfl | hκ
    · exact v.1.zero_mem
    · exact (Place.ord_nonneg_iff (isDiscrete k v) hκ).1 (by simpa using h v)

/-- For `D ≤ D'`: `ℓ(D') = ℓ(D) · a` with `a · b = [A(D') : A(D)]`. -/
public theorem ell_eq_mul {D D' : Place K →₀ ℤ} (h : D ≤ D') :
    ell k K D' = ell k K D * (principal k K ⊓ adeleLattice K D).relIndex
      (principal k K ⊓ adeleLattice K D') :=
  AddSubgroup.card_inf_eq_card_inf_mul_relIndex _ (adeleLattice_mono k h)

public theorem relIndex_inf_ne_zero {D D' : Place K →₀ ℤ} (h : D ≤ D') :
    (principal k K ⊓ adeleLattice K D).relIndex (principal k K ⊓ adeleLattice K D') ≠ 0 := by
  have := relIndex_adeleLattice_ne_zero k h
  rw [AddSubgroup.relIndex_eq_relIndex_inf_mul_relIndex_sup (principal k K)
    (adeleLattice_mono k h)] at this
  exact left_ne_zero_of_mul this

public theorem relIndex_sup_ne_zero {D D' : Place K →₀ ℤ} (h : D ≤ D') :
    (principal k K ⊔ adeleLattice K D).relIndex (principal k K ⊔ adeleLattice K D') ≠ 0 := by
  have := relIndex_adeleLattice_ne_zero k h
  rw [AddSubgroup.relIndex_eq_relIndex_inf_mul_relIndex_sup (principal k K)
    (adeleLattice_mono k h)] at this
  exact right_ne_zero_of_mul this

/-- `ℓ(D) ≥ 1` for every `D`: `L(D)` is finite. -/
public theorem ell_pos (D : Place K →₀ ℤ) : 0 < ell k K D := by
  have h0 : 0 < ell k K 0 := by
    have := finite_principal_inf_adeleLattice_zero k (K := K)
    exact Nat.card_pos
  have h2 : 0 < ell k K (D ⊔ 0) := by
    rw [ell_eq_mul k (le_sup_right : (0 : Place K →₀ ℤ) ≤ D ⊔ 0)]
    exact Nat.mul_pos h0 (Nat.pos_of_ne_zero (relIndex_inf_ne_zero k le_sup_right))
  have hfin : Finite ↥(principal k K ⊓ adeleLattice K (D ⊔ 0)) := Nat.finite_of_card_ne_zero h2.ne'
  have hle : principal k K ⊓ adeleLattice K D ≤ principal k K ⊓ adeleLattice K (D ⊔ 0) :=
    inf_le_inf_left _ (adeleLattice_mono k le_sup_left)
  have : Finite ↥(principal k K ⊓ adeleLattice K D) :=
    Finite.of_injective _ (AddSubgroup.inclusion_injective hle)
  exact Nat.card_pos

/-- For `D ≤ D'`: `ℓ(D') ≤ ℓ(D) · N(D' - D)`. -/
public theorem ell_le_mul_divNorm {D D' : Place K →₀ ℤ} (h : D ≤ D') :
    (ell k K D' : ℚ) ≤ ell k K D * divNorm K (D' - D) := by
  rw [ell_eq_mul k h, ← relIndex_adeleLattice_of_le k h,
    AddSubgroup.relIndex_eq_relIndex_inf_mul_relIndex_sup (principal k K) (adeleLattice_mono k h)]
  push_cast
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact le_mul_of_one_le_right (by positivity)
    (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (relIndex_sup_ne_zero k h))

/-- The Riemann–Roch identity between `D ≤ D'`:
`ℓ(D') · h¹(D) = N(D' - D) · ℓ(D) · h¹(D')`. -/
public theorem ell_mul_hOne {D D' : Place K →₀ ℤ} (h : D ≤ D') :
    (ell k K D' : ℚ) * hOne k K D = divNorm K (D' - D) * ell k K D * hOne k K D' := by
  rw [← relIndex_adeleLattice_of_le k h]
  exact_mod_cast AddSubgroup.card_inf_mul_index_sup (principal k K) (adeleLattice_mono k h)

variable (K) in
/-- The principal divisor of `y ∈ K`: `v ↦ ord_v y`. -/
public def principalDivisor (y : K) : Place K →₀ ℤ :=
  Finsupp.ofSupportFinite (fun v => v.ord y) (by
    rcases eq_or_ne y 0 with rfl | hy
    · convert Set.finite_empty
      ext v
      simp [Place.ord]
    · exact finite_setOf_ord_ne_zero k hy)

@[simp]
public theorem principalDivisor_apply (y : K) (v : Place K) :
    principalDivisor k K y v = v.ord y := rfl

/-- Multiplication by the principal adele of `y ≠ 0`. -/
public def mulDiag {y : K} (hy : y ≠ 0) : AdeleRing K ≃+ AdeleRing K where
  toFun a := diag k K y * a
  invFun a := diag k K y⁻¹ * a
  left_inv a := by
    simp only
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hy, map_one, one_mul]
  right_inv a := by
    simp only
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hy, map_one, one_mul]
  map_add' a b := mul_add _ a b

public theorem mulDiag_apply {y : K} (hy : y ≠ 0) (a : AdeleRing K) :
    mulDiag k hy a = diag k K y * a := rfl

public theorem mulDiag_symm_apply {y : K} (hy : y ≠ 0) (a : AdeleRing K) :
    (mulDiag k hy).symm a = diag k K y⁻¹ * a := rfl

/-- `y · A(D) = A(D - div y)`. -/
public theorem mul_mem_adeleLattice_iff {y : K} (hy : y ≠ 0) {D : Place K →₀ ℤ}
    {a : AdeleRing K} :
    diag k K y * a ∈ adeleLattice K (D - principalDivisor k K y) ↔ a ∈ adeleLattice K D := by
  simp only [mem_adeleLattice]
  refine forall_congr' fun v => ?_
  have : -(D - principalDivisor k K y) v = -D v + v.ord y := by
    simp only [Finsupp.coe_sub, Pi.sub_apply, principalDivisor_apply]; ring
  rw [this]
  exact Place.coeRingHom_mul_mem_ball_iff (isDiscrete k v) hy

public theorem map_mulDiag_adeleLattice {y : K} (hy : y ≠ 0) (D : Place K →₀ ℤ) :
    (adeleLattice K D).map (mulDiag k hy).toAddMonoidHom =
      adeleLattice K (D - principalDivisor k K y) := by
  ext x
  rw [AddSubgroup.mem_map_equiv, mulDiag_symm_apply, ← mul_mem_adeleLattice_iff k hy,
    ← mul_assoc, ← map_mul, mul_inv_cancel₀ hy, map_one, one_mul]

public theorem map_mulDiag_principal {y : K} (hy : y ≠ 0) :
    (principal k K).map (mulDiag k hy).toAddMonoidHom = principal k K := by
  ext x
  rw [AddSubgroup.mem_map_equiv, mulDiag_symm_apply, mem_principal, mem_principal]
  constructor
  · rintro ⟨κ, hκ⟩
    refine ⟨y * κ, ?_⟩
    rw [map_mul, hκ, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hy, map_one, one_mul]
  · rintro ⟨κ, rfl⟩
    exact ⟨y⁻¹ * κ, map_mul _ _ _⟩

/-- `ℓ(D - div y) = ℓ(D)`. -/
public theorem ell_sub_principalDivisor {y : K} (hy : y ≠ 0) (D : Place K →₀ ℤ) :
    ell k K (D - principalDivisor k K y) = ell k K D := by
  have hinj : Function.Injective (mulDiag k hy).toAddMonoidHom := (mulDiag k hy).injective
  have h1 : principal k K ⊓ adeleLattice K (D - principalDivisor k K y) =
      (principal k K ⊓ adeleLattice K D).map (mulDiag k hy).toAddMonoidHom := by
    rw [AddSubgroup.map_inf_eq _ _ _ hinj, map_mulDiag_adeleLattice, map_mulDiag_principal]
  rw [ell, ell, h1]
  exact Nat.card_congr ((principal k K ⊓ adeleLattice K D).equivMapOfInjective _
    hinj).symm.toEquiv

/-- `h¹(D - div y) = h¹(D)`. -/
public theorem hOne_sub_principalDivisor {y : K} (hy : y ≠ 0) (D : Place K →₀ ℤ) :
    hOne k K (D - principalDivisor k K y) = hOne k K D := by
  have h1 : principal k K ⊔ adeleLattice K (D - principalDivisor k K y) =
      (principal k K ⊔ adeleLattice K D).map (mulDiag k hy).toAddMonoidHom := by
    rw [AddSubgroup.map_sup, map_mulDiag_adeleLattice, map_mulDiag_principal]
  rw [hOne, hOne, h1]
  exact AddSubgroup.index_map_of_bijective (f := (mulDiag k hy).toAddMonoidHom)
    (mulDiag k hy).bijective _

section Riemann

variable (K) in
open scoped Classical in
/-- The pole divisor of `t`: `v ↦ -ord_v t` at the places not containing `t`. -/
public def poleDivisor : Place K →₀ ℤ :=
  Finsupp.ofSupportFinite (fun v => if gen k K ∈ v.1 then 0 else -v.ord (gen k K)) (by
    refine (finite_setOf_gen_notMem k).subset fun v hv => ?_
    by_contra h
    exact hv (ite_eq_left (not_not.1 h)))

public theorem poleDivisor_apply_of_mem {v : Place K} (h : gen k K ∈ v.1) :
    poleDivisor k K v = 0 := by
  simp [poleDivisor, Finsupp.ofSupportFinite_coe, h]

public theorem poleDivisor_apply_of_notMem {v : Place K} (h : gen k K ∉ v.1) :
    poleDivisor k K v = -v.ord (gen k K) := by
  simp [poleDivisor, Finsupp.ofSupportFinite_coe, h]

public theorem ord_gen_neg_of_notMem {v : Place K} (h : gen k K ∉ v.1) : v.ord (gen k K) < 0 := by
  by_contra hle
  exact h ((Place.ord_nonneg_iff (isDiscrete k v) (gen_ne_zero k K)).1 (not_lt.1 hle))

public theorem one_le_poleDivisor_of_notMem {v : Place K} (h : gen k K ∉ v.1) :
    1 ≤ poleDivisor k K v := by
  rw [poleDivisor_apply_of_notMem k h]
  have := ord_gen_neg_of_notMem k h
  omega

public theorem poleDivisor_nonneg : 0 ≤ poleDivisor k K := fun v => by
  by_cases h : gen k K ∈ v.1
  · simp [poleDivisor_apply_of_mem k h]
  · exact (zero_lt_one.trans_le (one_le_poleDivisor_of_notMem k h)).le

omit [Finite k] [FunctionField k K] in
public theorem ord_gen_inv (v : Place K) : v.ord (gen k K)⁻¹ = -v.ord (gen k K) := by
  have h0 := gen_ne_zero k K
  have := Place.ord_mul v h0 (inv_ne_zero h0)
  rw [mul_inv_cancel₀ h0, Place.ord, map_one, log_one, neg_zero] at this
  omega

omit [Field k] [Finite k] [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
  [FunctionField k K] in
/-- `N(D)` of a nonnegative divisor as a natural number. -/
public theorem divNorm_eq_prod_toNat {D : Place K →₀ ℤ} (hD : 0 ≤ D) :
    divNorm K D = ((∏ v ∈ D.support, v.resCard ^ (D v).toNat : ℕ) : ℚ) := by
  rw [divNorm, Finsupp.prod, Nat.cast_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Nat.cast_pow, ← zpow_natCast, Int.toNat_of_nonneg (hD v)]

/-- The pole divisor of `t` has norm at most `#k ^ [K : k(t)]`. -/
public theorem divNorm_poleDivisor_le :
    divNorm K (poleDivisor k K) ≤ (Nat.card k : ℚ) ^ degree k K := by
  rw [divNorm_eq_prod_toNat k (poleDivisor_nonneg k)]
  have hs : ∀ v ∈ (poleDivisor k K).support, (gen k K)⁻¹ ∈ v.1 := by
    intro v hv
    have h : gen k K ∉ v.1 := fun h => (Finsupp.mem_support_iff.1 hv)
      (poleDivisor_apply_of_mem k h)
    exact ((gen_notMem_iff k v).1 h).1
  have key := prod_resCard_pow_ord_le k (gen k K)⁻¹ (gen_inv_transcendental k K) X_ne_zero
    (poleDivisor k K).support hs
  rw [aeval_X, natDegree_X, mul_one, finrank_adjoin_gen_inv] at key
  have heq : ∀ v ∈ (poleDivisor k K).support, (poleDivisor k K v).toNat =
      (v.ord (gen k K)⁻¹).toNat := by
    intro v hv
    have h : gen k K ∉ v.1 := fun h => (Finsupp.mem_support_iff.1 hv)
      (poleDivisor_apply_of_mem k h)
    rw [poleDivisor_apply_of_notMem k h, ord_gen_inv]
  rw [Finset.prod_congr rfl fun v hv => by rw [heq v hv]]
  exact_mod_cast key

public theorem divNorm_nsmul (D : Place K →₀ ℤ) (m : ℕ) :
    divNorm K (m • D) = divNorm K D ^ m := by
  induction m with
  | zero => simp [divNorm_zero]
  | succ m ih => rw [succ_nsmul, divNorm_add k, ih, pow_succ]

end Riemann

section LowerBound

set_option synthInstance.maxHeartbeats 200000 in
/-- With a basis `b` of the integral closure of `k[t]`, the elements `∑ a_{ij} t^j b_i`,
`j ≤ m - c`, give `ℓ(m · D_∞) ≥ #k ^ ([K : k(t)] · (m - c + 1))`. -/
public theorem exists_ell_poleDivisor_lower_bound : ∃ c : ℕ, ∀ m : ℕ, c ≤ m →
    Nat.card k ^ (degree k K * (m - c + 1)) ≤ ell k K (m • poleDivisor k K) := by
  classical
  set t := gen k K
  let b := Module.Free.chooseBasis (polySubalg k t) (intClosure k t)
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex (polySubalg k t) (intClosure k t)) =
      degree k K := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, finrank_intClosure k t]
  set S := (finite_setOf_gen_notMem k (K := K)).toFinset
  set c : ℕ := ∑ i, ∑ v ∈ S, (-(v.ord (b i : K))).toNat
  refine ⟨c, fun m hm => ?_⟩
  set N := m - c + 1
  have hb0 : ∀ i, (b i : K) ≠ 0 := fun i h => b.ne_zero i (Subtype.ext h)
  have hbord : ∀ i (v : Place K), t ∉ v.1 → -(c : ℤ) ≤ v.ord (b i : K) := by
    intro i v hv
    have hvS : v ∈ S := by simpa [S] using hv
    have : (-(v.ord (b i : K))).toNat ≤ c :=
      le_trans (Finset.single_le_sum (f := fun w => (-(w.ord (b i : K))).toNat)
        (fun w _ => Nat.zero_le _) hvS)
        (Finset.single_le_sum (f := fun j => ∑ v ∈ S, (-(v.ord (b j : K))).toNat)
          (fun j _ => Nat.zero_le _) (Finset.mem_univ i))
    omega
  -- the elements `y a = ∑ a_{ij} t^j b_i`
  let y : (Module.Free.ChooseBasisIndex (polySubalg k t) (intClosure k t) × Fin N → k) → K :=
    fun a => ∑ p, algebraMap k K (a p) * t ^ (p.2 : ℕ) * (b p.1 : K)
  have hterm : ∀ (a : Module.Free.ChooseBasisIndex (polySubalg k t) (intClosure k t) × Fin N → k) p,
      diag k K (algebraMap k K (a p) * t ^ (p.2 : ℕ) * (b p.1 : K)) ∈
        adeleLattice K (m • poleDivisor k K) := by
    intro a p
    rw [diag_mem_adeleLattice_iff k]
    by_cases hap : a p = 0
    · left; simp [hap]
    right
    intro v
    have hc0 : algebraMap k K (a p) ≠ 0 := by simpa using hap
    have ht0 : t ^ (p.2 : ℕ) ≠ 0 := pow_ne_zero _ (gen_ne_zero k K)
    rw [Place.ord_mul v (mul_ne_zero hc0 ht0) (hb0 p.1), Place.ord_mul v hc0 ht0,
      ord_algebraMap k v hap, Place.ord_pow, zero_add]
    simp only [Finsupp.smul_apply, nsmul_eq_mul]
    have hp2 : (p.2 : ℕ) + c ≤ m := by have := p.2.2; omega
    by_cases ht : t ∈ v.1
    · rw [poleDivisor_apply_of_mem k ht]
      have h1 := (Place.ord_nonneg_iff (isDiscrete k v) (gen_ne_zero k K)).2 ht
      have h2 := (Place.ord_nonneg_iff (isDiscrete k v) (hb0 p.1)).2
        (intClosure_le_place v ht (b p.1))
      have : (0 : ℤ) ≤ ((p.2 : ℕ) : ℤ) * v.ord t := mul_nonneg (by positivity) h1
      simp only [mul_zero, neg_zero]
      omega
    · rw [poleDivisor_apply_of_notMem k ht]
      have h1 := hbord p.1 v ht
      have h2 := ord_gen_neg_of_notMem k ht
      have hp2' : ((p.2 : ℕ) : ℤ) + c ≤ m := by exact_mod_cast hp2
      have h3 : (m : ℤ) * v.ord t ≤ (((p.2 : ℕ) : ℤ) + c) * v.ord t :=
        mul_le_mul_of_nonpos_right hp2' h2.le
      have h4 : (c : ℤ) * v.ord t ≤ -(c : ℤ) := by nlinarith
      nlinarith
  have hmem : ∀ a, diag k K (y a) ∈ principal k K ⊓ adeleLattice K (m • poleDivisor k K) := by
    intro a
    refine AddSubgroup.mem_inf.2 ⟨(mem_principal k).2 ⟨_, rfl⟩, ?_⟩
    have : y a ∈ (adeleLattice K (m • poleDivisor k K)).comap (diag k K).toAddMonoidHom :=
      AddSubgroup.sum_mem _ fun p _ => hterm a p
    exact this
  -- injectivity
  have hinj : Function.Injective fun a => (⟨diag k K (y a), hmem a⟩ :
      ↥(principal k K ⊓ adeleLattice K (m • poleDivisor k K))) := by
    intro a a' h
    have hyy : y a = y a' := diag_injective k (congrArg Subtype.val h)
    have hsub : y (a - a') = 0 := by
      have : y (a - a') = y a - y a' := by
        simp only [y, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]
      rw [this, hyy, sub_self]
    suffices hz : ∀ d, y d = 0 → d = 0 from sub_eq_zero.1 (hz _ hsub)
    intro d hd
    -- regroup as `∑_i p_i(t) • b_i`
    let α : Module.Free.ChooseBasisIndex (polySubalg k t) (intClosure k t) → polySubalg k t :=
      fun i => polySubalgMap (k := k) t (∑ j : Fin N, C (d (i, j)) * X ^ (j : ℕ))
    have hsum : (∑ i, α i • b i : intClosure k t) = 0 := by
      apply Subtype.ext
      rw [ZeroMemClass.coe_zero, ← hd]
      simp only [y, Fintype.sum_prod_type, AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun i _ => ?_
      show (α i : K) * (b i : K) = _
      rw [coe_polySubalgMap, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, aeval_C, map_pow, aeval_X]
    have hα := (Fintype.linearIndependent_iff.1 b.linearIndependent) α hsum
    funext p
    obtain ⟨i, j⟩ := p
    have hpi : (∑ j : Fin N, C (d (i, j)) * X ^ (j : ℕ) : k[X]) = 0 :=
      polySubalgMap_injective (gen_transcendental k K) ((hα i).trans (map_zero _).symm)
    have := congrArg (fun q : k[X] => q.coeff j) hpi
    simp only [finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at this
    rw [Finset.sum_eq_single j (fun j' _ hj' => ite_eq_right (fun h => hj' (Fin.ext h.symm)))
      (by simp)] at this
    simpa using this
  have hfin : Finite ↥(principal k K ⊓ adeleLattice K (m • poleDivisor k K)) :=
    Nat.finite_of_card_ne_zero (ell_pos k _).ne'
  calc Nat.card k ^ (degree k K * (m - c + 1))
      = Nat.card (Module.Free.ChooseBasisIndex (polySubalg k t) (intClosure k t) × Fin N → k) := by
        rw [Nat.card_fun, Nat.card_prod,
          Nat.card_eq_fintype_card (α := Module.Free.ChooseBasisIndex _ _), hcard, Nat.card_fin]
    _ ≤ ell k K (m • poleDivisor k K) := Nat.card_le_card_of_injective _ hinj

end LowerBound

section RiemannInequality

/-- For `D ≥ 0` there is a nonzero polynomial `f` with `ord_v f(t) ≥ D(v)` at every place
containing `t`. -/
public theorem exists_poly_ord_ge {D : Place K →₀ ℤ} (hD : 0 ≤ D) :
    ∃ f : k[X], f ≠ 0 ∧ ∀ v : Place K, gen k K ∈ v.1 → D v ≤ v.ord (aeval (gen k K) f) := by
  classical
  set t := gen k K
  have hne : ∀ g : k[X], g ≠ 0 → aeval t g ≠ 0 :=
    fun g => aeval_ne_zero_of_transcendental (gen_transcendental k K)
  set S := D.support.filter fun v => t ∈ v.1
  have hP : ∀ v ∈ S, ∃ P : k[X], P ≠ 0 ∧ 1 ≤ v.ord (aeval t P) := fun v hv =>
    exists_poly_ord_pos k (Finset.mem_filter.1 hv).2
  choose! P hP0 hP1 using hP
  set M : ℕ := ∑ v ∈ S, (D v).toNat
  set g : k[X] := ∏ v ∈ S, P v
  have hg0 : g ≠ 0 := Finset.prod_ne_zero_iff.2 fun v hv => hP0 v hv
  refine ⟨g ^ M, pow_ne_zero _ hg0, fun v hv => ?_⟩
  have hgt := ord_aeval_nonneg k t hv (hne g hg0)
  rw [map_pow, Place.ord_pow]
  by_cases hvS : v ∈ S
  · -- the factor at `v` has positive order
    have hge : 1 ≤ v.ord (aeval t g) := by
      have hsplit : g = P v * ∏ w ∈ S.erase v, P w := (Finset.mul_prod_erase S P hvS).symm
      have hrest0 : (∏ w ∈ S.erase v, P w) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun w hw => hP0 w (Finset.mem_of_mem_erase hw)
      have hrest := ord_aeval_nonneg k t hv (hne _ hrest0)
      rw [hsplit, map_mul, Place.ord_mul v (hne _ (hP0 v hvS)) (hne _ hrest0)]
      have := hP1 v hvS
      omega
    have hDM : D v ≤ M := le_sum_toNat hvS
    nlinarith
  · have hDv : D v = 0 := by
      by_contra h
      exact hvS (Finset.mem_filter.2 ⟨Finsupp.mem_support_iff.2 h, hv⟩)
    rw [hDv]
    positivity

/-- `N(div y) · N(D_∞)^(deg f) ≤ #k ^ ([K : k(t)] · deg f)` for `y = f(t)`. -/
public theorem divNorm_principalDivisor_mul_le {f : k[X]} (hf : f ≠ 0) :
    divNorm K (principalDivisor k K (aeval (gen k K) f)) * divNorm K (poleDivisor k K) ^ f.natDegree
      ≤ (Nat.card k : ℚ) ^ (degree k K * f.natDegree) := by
  classical
  set t := gen k K
  set Z := principalDivisor k K (aeval t f) + f.natDegree • poleDivisor k K
  have hZv : ∀ v : Place K, Z v = if t ∈ v.1 then v.ord (aeval t f) else 0 := by
    intro v
    simp only [Z, Finsupp.coe_add, Pi.add_apply, principalDivisor_apply, Finsupp.smul_apply,
      nsmul_eq_mul]
    split_ifs with ht
    · rw [poleDivisor_apply_of_mem k ht, mul_zero, add_zero]
    · rw [poleDivisor_apply_of_notMem k ht, ord_aeval_gen_of_notMem k ht hf]
      ring
  have hZ0 : 0 ≤ Z := fun v => by
    rw [hZv]
    split_ifs with ht
    · exact ord_aeval_nonneg k t ht (aeval_ne_zero_of_transcendental (gen_transcendental k K) hf)
    · exact le_rfl
  have hs : ∀ v ∈ Z.support, t ∈ v.1 := by
    intro v hv
    by_contra ht
    exact Finsupp.mem_support_iff.1 hv (by rw [hZv, ite_eq_right ht])
  have key := prod_resCard_pow_ord_le k t (gen_transcendental k K) hf Z.support hs
  have hNZ : divNorm K Z = divNorm K (principalDivisor k K (aeval t f)) *
      divNorm K (poleDivisor k K) ^ f.natDegree := by
    rw [divNorm_add k, divNorm_nsmul k]
  rw [← hNZ, divNorm_eq_prod_toNat k hZ0]
  rw [Finset.prod_congr rfl fun v hv => by rw [hZv, ite_eq_left (hs v hv)]]
  exact_mod_cast key

/-- **Riemann's inequality**: there is `B > 0` with `N(D) ≤ B · ℓ(D)` for every `D ≥ 0`. -/
public theorem exists_divNorm_le_mul_ell :
    ∃ B : ℚ, 0 < B ∧ ∀ D : Place K →₀ ℤ, 0 ≤ D → divNorm K D ≤ B * ell k K D := by
  classical
  obtain ⟨c, hc⟩ := exists_ell_poleDivisor_lower_bound k (K := K)
  set q : ℚ := (Nat.card k : ℚ)
  set n := degree k K
  have hq1 : 1 ≤ q := by
    have : 1 ≤ Nat.card k := Nat.card_pos
    show (1 : ℚ) ≤ (Nat.card k : ℚ)
    exact_mod_cast this
  have hq0 : 0 < q := zero_lt_one.trans_le hq1
  refine ⟨q ^ (n * c), by positivity, fun D hD => ?_⟩
  set t := gen k K
  obtain ⟨f, hf0, hf⟩ := exists_poly_ord_ge k hD
  set y := aeval t f
  have hy0 : y ≠ 0 := aeval_ne_zero_of_transcendental (gen_transcendental k K) hf0
  set Sinf := (finite_setOf_gen_notMem k (K := K)).toFinset
  set M' : ℕ := ∑ v ∈ Sinf, (D v).toNat
  set m : ℕ := c + f.natDegree + M'
  set E := D - principalDivisor k K y
  have hE : E ≤ m • poleDivisor k K := by
    intro v
    simp only [E, Finsupp.coe_sub, Pi.sub_apply, principalDivisor_apply, Finsupp.smul_apply,
      nsmul_eq_mul]
    by_cases ht : t ∈ v.1
    · rw [poleDivisor_apply_of_mem k ht, mul_zero]
      have := hf v ht
      omega
    · rw [poleDivisor_apply_of_notMem k ht, ord_aeval_gen_of_notMem k ht hf0]
      have hvS : v ∈ Sinf := by simpa [Sinf] using ht
      have h1 : D v ≤ M' := le_sum_toNat hvS
      have h2 := ord_gen_neg_of_notMem k ht
      have hm : (m : ℤ) = c + f.natDegree + M' := by push_cast [m]; ring
      rw [hm]
      nlinarith
  have hlow := hc m (by omega)
  have hup := ell_le_mul_divNorm k hE
  rw [ell_sub_principalDivisor k hy0] at hup
  have hN1 : divNorm K (m • poleDivisor k K - E) * divNorm K D =
      divNorm K (poleDivisor k K) ^ m * divNorm K (principalDivisor k K y) := by
    rw [divNorm_sub k, divNorm_nsmul k, divNorm_sub k]
    field_simp [(divNorm_pos k D).ne', (divNorm_pos k (principalDivisor k K y)).ne']
  have hZ := divNorm_principalDivisor_mul_le k (K := K) hf0
  have hDinf := divNorm_poleDivisor_le k (K := K)
  set A := divNorm K (poleDivisor k K)
  set Ny := divNorm K (principalDivisor k K y)
  set ND := divNorm K D
  have hA0 : 0 < A := divNorm_pos k _
  have hND0 : 0 < ND := divNorm_pos k _
  have hNy0 : 0 < Ny := divNorm_pos k _
  -- `A^m · Ny ≤ q^(n m)`
  have hAm : A ^ m * Ny ≤ q ^ (n * m) := by
    have hsplit : A ^ m * Ny = A ^ (c + M') * (Ny * A ^ f.natDegree) := by
      rw [show m = c + M' + f.natDegree by omega, pow_add]; ring
    rw [hsplit]
    calc A ^ (c + M') * (Ny * A ^ f.natDegree) ≤ (q ^ n) ^ (c + M') * q ^ (n * f.natDegree) :=
          mul_le_mul (pow_le_pow_left₀ hA0.le hDinf _) hZ (by positivity) (by positivity)
      _ = q ^ (n * m) := by
          rw [← pow_mul, ← pow_add]
          congr 1
          simp only [m]
          ring
  have hmain : ND * q ^ (n * (m - c + 1)) ≤ ell k K D * q ^ (n * m) := by
    have h1 : (q ^ (n * (m - c + 1)) : ℚ) ≤ ell k K (m • poleDivisor k K) := by
      show ((Nat.card k : ℚ)) ^ (n * (m - c + 1)) ≤ _
      exact_mod_cast hlow
    calc ND * q ^ (n * (m - c + 1)) ≤ ND * ell k K (m • poleDivisor k K) :=
          mul_le_mul_of_nonneg_left h1 hND0.le
      _ ≤ ND * (ell k K D * divNorm K (m • poleDivisor k K - E)) :=
          mul_le_mul_of_nonneg_left hup hND0.le
      _ = ell k K D * (A ^ m * Ny) := by rw [← hN1]; ring
      _ ≤ ell k K D * q ^ (n * m) := mul_le_mul_of_nonneg_left hAm (by positivity)
  have hpow : q ^ (n * m) ≤ q ^ (n * c) * q ^ (n * (m - c + 1)) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hq1 (by
      rw [← mul_add]
      exact Nat.mul_le_mul_left _ (by omega))
  have hpos : 0 < q ^ (n * (m - c + 1)) := by positivity
  have := hmain.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
  rw [show ell k K D * (q ^ (n * c) * q ^ (n * (m - c + 1))) =
    q ^ (n * c) * ell k K D * q ^ (n * (m - c + 1)) by ring] at this
  exact le_of_mul_le_mul_right this hpos

end RiemannInequality

section RiemannRochFormula

/-- `h¹(0) = [A : K + O]` is finite: the genus of `K` is finite. -/
public theorem hOne_zero_ne_zero : hOne k K 0 ≠ 0 := by
  classical
  obtain ⟨B, -, hB⟩ := exists_divNorm_le_mul_ell k (K := K)
  obtain ⟨M, hM⟩ : ∃ M : ℕ, B * ell k K 0 ≤ M := exists_nat_ge _
  refine (AddSubgroup.index_le_of_forall_finset (principal k K ⊔ adeleLattice K 0) M ?_).1
  intro s
  choose D hD0 hDmem using fun a : AdeleRing K => exists_mem_adeleLattice k a
  set Ds := ∑ a ∈ s, D a
  have hDs0 : 0 ≤ Ds := Finset.sum_nonneg fun a _ => hD0 a
  refine ⟨principal k K ⊔ adeleLattice K Ds, sup_le_sup_left (adeleLattice_mono k hDs0) _,
    fun g hg => ?_, relIndex_sup_ne_zero k hDs0, ?_⟩
  · exact AddSubgroup.mem_sup_right
      (adeleLattice_mono k (Finset.single_le_sum (fun a _ => hD0 a) hg) (hDmem g))
  · have hid := AddSubgroup.relIndex_eq_relIndex_inf_mul_relIndex_sup (principal k K)
      (adeleLattice_mono k hDs0)
    have hN := relIndex_adeleLattice_of_le k hDs0
    rw [sub_zero] at hN
    have hell := ell_eq_mul k hDs0
    have hR := hB Ds hDs0
    set a := (principal k K ⊓ adeleLattice K 0).relIndex (principal k K ⊓ adeleLattice K Ds)
    set b := (principal k K ⊔ adeleLattice K 0).relIndex (principal k K ⊔ adeleLattice K Ds)
    have h1 : (b : ℚ) * ell k K Ds = divNorm K Ds * ell k K 0 := by
      rw [hell, ← hN, hid]; push_cast; ring
    have hpos : (0 : ℚ) < ell k K Ds := by exact_mod_cast ell_pos k Ds
    have h2 : (b : ℚ) * ell k K Ds ≤ (B * ell k K 0) * ell k K Ds := by
      rw [h1]
      have h0 : (0 : ℚ) ≤ ell k K 0 := by positivity
      nlinarith
    have h3 : (b : ℚ) ≤ B * ell k K 0 := le_of_mul_le_mul_right h2 hpos
    exact_mod_cast h3.trans hM

/-- `h¹(D)` is finite for every divisor `D`. -/
public theorem hOne_ne_zero (D : Place K →₀ ℤ) : hOne k K D ≠ 0 := by
  set D₁ := D ⊓ 0
  have h1 : D₁ ≤ 0 := inf_le_right
  have h2 : D₁ ≤ D := inf_le_left
  have hD₁ : hOne k K D₁ ≠ 0 := by
    intro h0
    have hid := AddSubgroup.card_inf_mul_index_sup (principal k K) (adeleLattice_mono k h1)
    change ell k K 0 * hOne k K D₁ = _ * ell k K D₁ * hOne k K 0 at hid
    rw [h0, mul_zero] at hid
    have := Nat.mul_pos (Nat.mul_pos (Nat.pos_of_ne_zero (relIndex_adeleLattice_ne_zero k h1))
      (ell_pos k D₁)) (Nat.pos_of_ne_zero (hOne_zero_ne_zero k (K := K)))
    omega
  intro h0
  have := AddSubgroup.relIndex_mul_index
    (sup_le_sup_left (adeleLattice_mono k h2) (principal k K))
  change _ * hOne k K D = hOne k K D₁ at this
  rw [h0, mul_zero] at this
  exact hD₁ this.symm

/-- **Riemann–Roch** (without duality): `ℓ(D) / h¹(D) = N(D) · ℓ(0) / h¹(0)`. -/
public theorem ell_div_hOne (D : Place K →₀ ℤ) :
    (ell k K D : ℚ) / hOne k K D = divNorm K D * (ell k K 0 / hOne k K 0) := by
  have step : ∀ {D D' : Place K →₀ ℤ}, D ≤ D' →
      (ell k K D' : ℚ) / hOne k K D' = divNorm K (D' - D) * (ell k K D / hOne k K D) := by
    intro D D' h
    have hid := ell_mul_hOne k h
    have h1 : (hOne k K D : ℚ) ≠ 0 := by exact_mod_cast hOne_ne_zero k D
    have h2 : (hOne k K D' : ℚ) ≠ 0 := by exact_mod_cast hOne_ne_zero k D'
    rw [div_eq_iff h2, mul_comm (divNorm K _), mul_assoc, div_mul_eq_mul_div, eq_div_iff h1]
    linarith [hid]
  set D₁ := D ⊓ 0
  have hA := step (inf_le_left : D₁ ≤ D)
  have hB := step (inf_le_right : D₁ ≤ 0)
  rw [hA, hB, divNorm_sub k, divNorm_sub k, divNorm_zero]
  field_simp [(divNorm_pos k D₁).ne']

/-- The Euler characteristic `χ(0) = ℓ(0) / h¹(0)` is positive. -/
public theorem chi_zero_pos : (0 : ℚ) < ell k K 0 / hOne k K 0 := by
  have h1 : (0 : ℚ) < ell k K 0 := by exact_mod_cast ell_pos k 0
  have h2 : (0 : ℚ) < hOne k K 0 := by exact_mod_cast Nat.pos_of_ne_zero (hOne_zero_ne_zero k)
  positivity

/-- **Product formula**: `N(div y) = 1` for `y ≠ 0`. -/
public theorem divNorm_principalDivisor {y : K} (hy : y ≠ 0) :
    divNorm K (principalDivisor k K y) = 1 := by
  have h := ell_div_hOne k (0 - principalDivisor k K y)
  rw [ell_sub_principalDivisor k hy, hOne_sub_principalDivisor k hy, divNorm_sub k,
    divNorm_zero] at h
  have hχ := chi_zero_pos k (K := K)
  have : 1 / divNorm K (principalDivisor k K y) = 1 :=
    mul_right_cancel₀ hχ.ne' (h.symm.trans (one_mul _).symm)
  have hpos := divNorm_pos k (principalDivisor k K y)
  field_simp at this
  linarith

/-- `N(D) ≥ 1` for `D ≥ 0`. -/
public theorem one_le_divNorm {D : Place K →₀ ℤ} (hD : 0 ≤ D) : 1 ≤ divNorm K D := by
  rw [divNorm, Finsupp.prod]
  refine Finset.prod_induction _ (fun x : ℚ => 1 ≤ x)
    (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl fun v _ => ?_
  exact one_le_zpow₀ (by exact_mod_cast (resCard_pos k v)) (hD v)

/-- `L(D) = 0` when `N(D) < 1`. -/
public theorem eq_zero_of_mem_of_divNorm_lt_one {D : Place K →₀ ℤ} (hD : divNorm K D < 1)
    {κ : K} (hκ : diag k K κ ∈ adeleLattice K D) : κ = 0 := by
  by_contra hκ0
  rcases (diag_mem_adeleLattice_iff k).1 hκ with h | h
  · exact hκ0 h
  have hnn : 0 ≤ D + principalDivisor k K κ := fun v => by
    have := h v
    simp only [Finsupp.coe_add, Pi.add_apply, principalDivisor_apply, Finsupp.coe_zero,
      Pi.zero_apply]
    omega
  have := one_le_divNorm k hnn
  rw [divNorm_add k, divNorm_principalDivisor k hκ0, mul_one] at this
  linarith

public theorem finite_principal_inf_adeleLattice (D : Place K →₀ ℤ) :
    Finite ↥(principal k K ⊓ adeleLattice K D) :=
  Nat.finite_of_card_ne_zero (ell_pos k D).ne'

public theorem finite_quotient_principal_sup_adeleLattice (D : Place K →₀ ℤ) :
    Finite (AdeleRing K ⧸ (principal k K ⊔ adeleLattice K D)) :=
  Nat.finite_of_card_ne_zero (hOne_ne_zero k D)

end RiemannRochFormula

section Consequences

/-- `ℓ(D) ≥ N(D) · χ(0)`. -/
public theorem divNorm_mul_chi_le_ell (D : Place K →₀ ℤ) :
    divNorm K D * (ell k K 0 / hOne k K 0) ≤ ell k K D := by
  rw [← ell_div_hOne k D]
  have h1 : (1 : ℚ) ≤ hOne k K D := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (hOne_ne_zero k D)
  exact div_le_self (by positivity) h1

/-- If `ℓ(D) ≥ 2`, `L(D)` has a nonzero element. -/
public theorem exists_ne_zero_of_one_lt_ell {D : Place K →₀ ℤ} (h : 1 < ell k K D) :
    ∃ κ : K, κ ≠ 0 ∧ diag k K κ ∈ adeleLattice K D := by
  have hne : principal k K ⊓ adeleLattice K D ≠ ⊥ := by
    intro hbot
    rw [ell, hbot, AddSubgroup.card_bot] at h
    exact lt_irrefl _ h
  obtain ⟨⟨x, hx⟩, hx0⟩ := (AddSubgroup.ne_bot_iff_exists_ne_zero).1 hne
  obtain ⟨κ, rfl⟩ := (mem_principal k).1 (AddSubgroup.mem_inf.1 hx).1
  refine ⟨κ, fun h0 => hx0 ?_, (AddSubgroup.mem_inf.1 hx).2⟩
  ext1
  simp [h0]

public theorem principalDivisor_inv {κ : K} (hκ : κ ≠ 0) :
    principalDivisor k K κ⁻¹ = -principalDivisor k K κ := by
  ext v
  have := Place.ord_mul v hκ (inv_ne_zero hκ)
  rw [mul_inv_cancel₀ hκ, Place.ord, map_one, log_one, neg_zero] at this
  simp only [principalDivisor_apply, Finsupp.coe_neg, Pi.neg_apply]
  omega

/-- If `κ ≠ 0` lies in `L(D - D₁)`, then `D₁ ≤ D + div κ`. -/
public theorem le_add_principalDivisor_of_mem {D E : Place K →₀ ℤ} {κ : K} (hκ : κ ≠ 0)
    (h : diag k K κ ∈ adeleLattice K (D - E)) : E ≤ D + principalDivisor k K κ := by
  intro v
  rcases (diag_mem_adeleLattice_iff k).1 h with h0 | h
  · exact absurd h0 hκ
  · have := h v
    simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply,
      principalDivisor_apply] at this ⊢
    omega

/-- `A = K + A(D)` once `N(D)` is large. -/
public theorem exists_sup_adeleLattice_eq_top :
    ∃ M₀ : ℚ, ∀ D : Place K →₀ ℤ, M₀ ≤ divNorm K D → principal k K ⊔ adeleLattice K D = ⊤ := by
  classical
  -- a divisor `D₁` with `A = K + A(D₁)`
  have hfin : Finite (AdeleRing K ⧸ (principal k K ⊔ adeleLattice K 0)) :=
    Nat.finite_of_card_ne_zero (hOne_zero_ne_zero k)
  let := Fintype.ofFinite (AdeleRing K ⧸ (principal k K ⊔ adeleLattice K 0))
  choose Dg hDg0 hDgmem using fun a : AdeleRing K => exists_mem_adeleLattice k a
  set S := (Finset.univ : Finset (AdeleRing K ⧸ (principal k K ⊔ adeleLattice K 0))).image
    Quotient.out
  set D₁ := ∑ g ∈ S, Dg g
  have hD₁0 : 0 ≤ D₁ := Finset.sum_nonneg fun g _ => hDg0 g
  have htop : principal k K ⊔ adeleLattice K D₁ = ⊤ := by
    rw [eq_top_iff]
    intro a _
    set g := Quotient.out (QuotientAddGroup.mk a : AdeleRing K ⧸ (principal k K ⊔ adeleLattice K 0))
    have hgS : g ∈ S := Finset.mem_image_of_mem _ (Finset.mem_univ _)
    have hg : g ∈ adeleLattice K D₁ :=
      adeleLattice_mono k (Finset.single_le_sum (fun g _ => hDg0 g) hgS) (hDgmem g)
    have hdiff : a - g ∈ principal k K ⊔ adeleLattice K D₁ := by
      have : -g + a ∈ principal k K ⊔ adeleLattice K 0 := by
        rw [← QuotientAddGroup.eq]
        exact Quotient.out_eq _
      have h2 := sup_le_sup_left (adeleLattice_mono k hD₁0) (principal k K) this
      simpa [sub_eq_neg_add] using h2
    have := (principal k K ⊔ adeleLattice K D₁).add_mem hdiff (AddSubgroup.mem_sup_right hg)
    simpa using this
  set χ := (ell k K 0 : ℚ) / hOne k K 0
  have hχ := chi_zero_pos k (K := K)
  refine ⟨divNorm K D₁ * (2 / χ), fun D hD => ?_⟩
  have hN : 2 / χ ≤ divNorm K (D - D₁) := by
    rw [divNorm_sub k, le_div_iff₀ (divNorm_pos k D₁)]
    linarith
  have hell : 1 < ell k K (D - D₁) := by
    have h1 := divNorm_mul_chi_le_ell k (D - D₁)
    have h2 : (2 : ℚ) ≤ divNorm K (D - D₁) * χ := by
      rwa [div_le_iff₀ hχ] at hN
    have : (1 : ℚ) < ell k K (D - D₁) := by linarith
    exact_mod_cast this
  obtain ⟨κ, hκ, hmem⟩ := exists_ne_zero_of_one_lt_ell k hell
  have hle := le_add_principalDivisor_of_mem k hκ hmem
  have hidx : hOne k K D = 1 := by
    rw [← hOne_sub_principalDivisor k (inv_ne_zero hκ) D, principalDivisor_inv k hκ,
      sub_neg_eq_add, hOne]
    have : principal k K ⊔ adeleLattice K (D + principalDivisor k K κ) = ⊤ := by
      rw [eq_top_iff, ← htop]
      exact sup_le_sup_left (adeleLattice_mono k hle) _
    rw [this, AddSubgroup.index_top]
  exact AddSubgroup.index_eq_one.1 hidx

/-- The effective divisors of bounded norm are finitely many. -/
public theorem finite_setOf_nonneg_divNorm_le (M : ℚ) :
    {E : Place K →₀ ℤ | 0 ≤ E ∧ divNorm K E ≤ M}.Finite := by
  classical
  -- supports lie in the finite set of places with `q_v ≤ M`
  obtain ⟨M', hM'⟩ : ∃ M' : ℕ, M ≤ M' := exists_nat_ge M
  set T := (finite_setOf_resCard_le k (K := K) M').toFinset
  have hsub : ∀ E ∈ {E : Place K →₀ ℤ | 0 ≤ E ∧ divNorm K E ≤ M},
      E.support ⊆ T ∧ ∀ v, E v ≤ M' := by
    rintro E ⟨hE0, hEM⟩
    have hsingle : ∀ v, (v.resCard : ℚ) ^ E v ≤ M' := by
      intro v
      have hsplit : E = Finsupp.single v (E v) + (E - Finsupp.single v (E v)) := by abel
      have hrest : 0 ≤ E - Finsupp.single v (E v) := fun w => by
        by_cases hw : w = v
        · subst hw; simp
        · simpa [Finsupp.single_apply, Ne.symm hw] using hE0 w
      have := one_le_divNorm k hrest
      have h2 : divNorm K E = (v.resCard : ℚ) ^ E v * divNorm K (E - Finsupp.single v (E v)) := by
        conv_lhs => rw [hsplit]
        rw [divNorm_add k, divNorm_single]
      have hq : (0 : ℚ) ≤ (v.resCard : ℚ) ^ E v := by positivity
      nlinarith
    refine ⟨fun v hv => ?_, fun v => ?_⟩
    · have hEv : 1 ≤ E v := by
        have := Finsupp.mem_support_iff.1 hv
        have := hE0 v
        simp at *; omega
      have hq1 : (1 : ℚ) ≤ v.resCard := by exact_mod_cast (resCard_pos k v)
      have : (v.resCard : ℚ) ≤ M' :=
        le_trans (by simpa using zpow_le_zpow_right₀ hq1 hEv) (hsingle v)
      simp only [T, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      exact_mod_cast this
    · have hq2 : (2 : ℚ) ≤ v.resCard := by exact_mod_cast one_lt_resCard k v
      have h := hsingle v
      by_contra hlt
      push Not at hlt
      have hE : (E v).toNat = E v := Int.toNat_of_nonneg (hE0 v)
      have : (M' : ℚ) < (v.resCard : ℚ) ^ E v := by
        rw [← hE, zpow_natCast]
        calc (M' : ℚ) < 2 ^ (E v).toNat := by
              have h1 : M' < (E v).toNat := by omega
              have h2 : (E v).toNat < 2 ^ (E v).toNat := Nat.lt_two_pow_self
              exact_mod_cast h1.trans h2
          _ ≤ (v.resCard : ℚ) ^ (E v).toNat := pow_le_pow_left₀ (by norm_num) hq2 _
      linarith
  -- injection into functions `T → Fin (M' + 1)`
  refine Set.Finite.of_finite_image (f := fun E : Place K →₀ ℤ => fun v : T => E v) ?_ ?_
  · refine (Set.finite_range fun g : T → Fin (M' + 1) => fun v => ((g v : ℕ) : ℤ)).subset ?_
    rintro _ ⟨E, hE, rfl⟩
    obtain ⟨-, hbound⟩ := hsub E hE
    refine ⟨fun v => ⟨(E v).toNat, by have := hbound v; omega⟩, ?_⟩
    funext v
    simp [Int.toNat_of_nonneg (hE.1 v)]
  · intro E hE E' hE' h
    ext v
    by_cases hv : v ∈ T
    · exact congrFun h ⟨v, hv⟩
    · rw [Finsupp.notMem_support_iff.1 fun h => hv ((hsub E hE).1 h),
        Finsupp.notMem_support_iff.1 fun h => hv ((hsub E' hE').1 h)]

/-- **Finiteness of the class number**: the divisors `D` with `B⁻¹ ≤ N(D) ≤ B` lie in finitely
many classes modulo principal divisors. -/
public theorem exists_finset_divisor_classes (B : ℚ) :
    ∃ F : Finset (Place K →₀ ℤ), ∀ D : Place K →₀ ℤ, B⁻¹ ≤ divNorm K D → divNorm K D ≤ B →
      ∃ D' ∈ F, ∃ κ : K, κ ≠ 0 ∧ D = D' - principalDivisor k K κ := by
  classical
  obtain ⟨v₀⟩ := nonempty_place k (K := K)
  set χ := (ell k K 0 : ℚ) / hOne k K 0
  have hχ := chi_zero_pos k (K := K)
  have hq : (1 : ℚ) < v₀.resCard := by exact_mod_cast one_lt_resCard k v₀
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (2 * |B| / χ + 1) hq
  set E₀ : Place K →₀ ℤ := Finsupp.single v₀ (j : ℤ)
  have hE₀ : divNorm K E₀ = (v₀.resCard : ℚ) ^ j := by
    rw [divNorm_single, zpow_natCast]
  set M := B * divNorm K E₀
  obtain ⟨F₀, hF₀⟩ := (finite_setOf_nonneg_divNorm_le k (K := K) M).exists_finset_coe
  refine ⟨F₀.image fun E => E - E₀, fun D hDl hDu => ?_⟩
  have hBpos : 0 < B := by
    have := divNorm_pos k D
    by_contra h
    push Not at h
    have : B⁻¹ ≤ 0 := inv_nonpos.2 h
    linarith
  -- `ℓ(D + E₀) ≥ 2`
  have hN : 2 ≤ divNorm K (D + E₀) * χ := by
    rw [divNorm_add k, hE₀]
    have h1 : 2 * B / χ < (v₀.resCard : ℚ) ^ j := by
      rw [abs_of_pos hBpos] at hj; linarith
    have hD0 : 0 ≤ divNorm K D := (divNorm_pos k D).le
    calc (2 : ℚ) = B⁻¹ * (2 * B / χ) * χ := by
          rw [mul_assoc, div_mul_cancel₀ _ hχ.ne', ← mul_assoc, mul_comm B⁻¹, mul_assoc,
            inv_mul_cancel₀ hBpos.ne', mul_one]
      _ ≤ divNorm K D * (v₀.resCard : ℚ) ^ j * χ := by gcongr
  have hell : 1 < ell k K (D + E₀) := by
    exact_mod_cast (show (1 : ℚ) < ell k K (D + E₀) by
      linarith [divNorm_mul_chi_le_ell k (D + E₀)])
  obtain ⟨κ, hκ, hmem⟩ := exists_ne_zero_of_one_lt_ell k hell
  have hle := le_add_principalDivisor_of_mem k hκ (E := 0) (by rwa [sub_zero])
  set E := D + E₀ + principalDivisor k K κ
  have hEM : divNorm K E ≤ M := by
    rw [divNorm_add k, divNorm_principalDivisor k hκ, mul_one, divNorm_add k]
    exact mul_le_mul_of_nonneg_right hDu (divNorm_pos k E₀).le
  have hEF : E ∈ F₀ := by
    rw [← Finset.mem_coe, hF₀]
    exact ⟨hle, hEM⟩
  refine ⟨E - E₀, Finset.mem_image_of_mem _ hEF, κ, hκ, ?_⟩
  simp only [E]
  abel

end Consequences

end Stacks.Adeles.GlobalFunctionField

end
