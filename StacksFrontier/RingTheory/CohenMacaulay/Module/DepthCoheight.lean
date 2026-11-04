module

public import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
public import StacksFrontier.RingTheory.RegularLocalRing.Criteria
public import StacksFrontier.RingTheory.Serre.Reduced
import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Good elements: definitions, and the depth-coheight bound

Throughout, `R` is a Noetherian local ring with maximal ideal `m` and `M` is a finite, i.e.
finitely generated, `R`-module. We write `Supp M` for the support of `M`, `dim X` for the Krull
dimension of a subset `X ⊆ Spec R`, `depth M` for the `m`-depth of `M`, and
`V(a₁, …, aₙ) = {p ∈ Spec R | a₁, …, aₙ ∈ p}`.

## Definitions

* A finite `R`-module `M` over a Noetherian local ring `R` is *Cohen-Macaulay* if
  `dim (Supp M) = depth M` (Stacks 00N3). This is `IsCohenMacaulayModule R M`, defined as
  `depth M = krullDim (Supp M)`, with `Module.supportDim R M = krullDim (Supp M)`.
* A sequence `f₁, …, f_d ∈ m` is an *`M`-regular sequence* if for each `i` multiplication by
  `fᵢ` on `M / (f₁, …, f_{i-1}) M` is injective and `M / (f₁, …, f_d) M` is nonzero; this is
  `RingTheory.Sequence.IsRegular M f`.
* *Setup* (Stacks 00N2): `M` is a Cohen-Macaulay finite `R`-module and `f₁, …, f_d ∈ m` is an
  `M`-regular sequence with `d = dim (Supp M)`.
* *Good element* (Stacks 00N2): under the setup, `g ∈ m` is *good* for `(M, f₁, …, f_d)` if
  `dim (Supp M ∩ V(g, f₁, …, fᵢ)) = d - i - 1` for all `i = 0, …, d-1`.

## Main results

* `supportDim_le_coheight_of_isCohenMacaulayModule` : for a Cohen-Macaulay `M` and `p ∈ Ass M`,
  `dim (Supp M) ≤ dim (R/p)`; this is Stacks 0AUJ (`depthSup_le_coheight_of_mem_associatedPrimes`)
  combined with the Cohen-Macaulay equality `depth M = dim (Supp M)`.
* `isSMulRegular_of_supportDim_inter_lt` : the avoidance argument showing that an element cutting
  the support dimension of a Cohen-Macaulay module is a nonzerodivisor on it.
* `isCohenMacaulay_quotSMulTop_of_isSMulRegular` : the quotient of a Cohen-Macaulay module by a
  regular element of `m` is Cohen-Macaulay.

The main theorem on good elements, Stacks 00N4, is
`isCohenMacaulayModule_quotient_of_isGoodElement` in
`StacksFrontier.RingTheory.CohenMacaulay.Module.GoodElement`.
-/

@[expose] public section

/-- A finite module `M` over a Noetherian local ring `R` is *Cohen-Macaulay* if the
dimension of its support equals its depth (with respect to the maximal ideal).
(Stacks tag 00N3, Definition 5.) -/
def IsCohenMacaulayPropForm (R : Type*) [CommRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] : Prop :=
  Order.krullDim (Module.support R M) =
    ((Module.depthSup R (IsLocalRing.maximalIdeal R) M : ℕ∞) : WithBot ℕ∞)

/-- `V(g, l_1, ..., l_k)`, the set of primes containing `g` and every entry of the
list `l`, as a closed subset of `Spec(R)`. With `l = f.take i` this is
`V(g, f_1, ..., f_i)`. -/
noncomputable def zeroLocusCons {R : Type*} [CommRing R] (g : R) (l : List R) :
    Set (PrimeSpectrum R) :=
  PrimeSpectrum.zeroLocus (insert g {x | x ∈ l})

/-- (Stacks 00N2, Definition of a good element.) Under the standing assumptions,
`g ∈ m` is good with respect to `(M, f_1, ..., f_d)` (with `d = f.length`) if for
all `i = 0, ..., d-1` we have `dim(Supp(M) ∩ V(g, f_1, ..., f_i)) = d - i - 1`. -/
def IsGoodElement {R : Type*} [CommRing R] [IsLocalRing R] (M : Type*) [AddCommGroup M]
    [Module R M] (f : List R) (g : R) : Prop :=
  ∀ i : ℕ,
    i < f.length →
      Order.krullDim (↑(Module.support R M ∩ zeroLocusCons g (f.take i)) : Set (PrimeSpectrum R)) =
        ((f.length - i - 1 : ℕ) : WithBot ℕ∞)

/-! ### Regularity of a good element -/

open Module in
/-- If `S ⊆ Spec R` is closed under specialization (i.e. upward closed under `≤`, equivalently
under specialization), then for any `P ∈ S` the coheight of `P` is at most `krullDim S`: a chain of
primes above `P` stays inside `S`. -/
theorem coheight_le_krullDim_of_specializationClosed {R : Type*} [CommRing R]
    (S : Set (PrimeSpectrum R)) (hS : ∀ x ∈ S, ∀ y, x ≤ y → y ∈ S) (P : PrimeSpectrum R)
    (hP : P ∈ S) : (Order.coheight P : WithBot ℕ∞) ≤ Order.krullDim S := by
  rw [Order.coheight_eq_krullDim_Ici]
  have hsub : Set.Ici P ⊆ S := fun y hy => hS P hP y hy
  exact Order.krullDim_le_of_strictMono (Set.inclusion hsub) fun _ _ hab => hab

/-- A zero locus `V(I) = zeroLocus I` is closed under specialization. -/
theorem zeroLocus_specializationClosed {R : Type*} [CommRing R] (I : Ideal R) :
    ∀ x ∈ PrimeSpectrum.zeroLocus (↑I : Set R),
      ∀ y, x ≤ y → y ∈ PrimeSpectrum.zeroLocus (↑I : Set R) := by
  intro x hx y hxy
  rw [PrimeSpectrum.mem_zeroLocus] at hx ⊢
  rw [PrimeSpectrum.le_iff_specializes, ← PrimeSpectrum.le_iff_specializes] at hxy
  exact le_trans hx hxy

-- ===========================================================================
-- Stacks 0AUJ and Cohen–Macaulay equidimensionality:
-- `supportDim_le_coheight_of_isCohenMacaulayModule`.
--
-- This is the input for conjunct (a): Stacks 0AUJ, `depth M ≤ dim(R/p)` for `p ∈ Ass M`,
-- proved by induction on `depth M` along an `M`-regular element and combined with the CM
-- equality `depth M = supportDim M`.
--
-- The induction is `depthSup_le_coheight_of_depthSup_le`, its assembly into 0AUJ is
-- `depthSup_le_coheight_of_mem_associatedPrimes`, and the CM form is
-- `supportDim_le_coheight_of_isCohenMacaulayModule`. The induction uses:
--
--   (A) `depth_quotient_succ_of_isSMulRegular`  (depth drops by 1: Stacks 00LF/Rees)
--   (B) `exists_isSMulRegular_of_depth_pos`      (depth > 0 ⟹ ∃ M-regular x ∈ m)
--   (D) `exists_associatedPrime_quotient_gt`     (Ass-of-quotient strict containment)
--   (F) `depth_ne_top`                           (depth is finite for finite M)
--
-- The depth recursion is built off the
-- `sSup`-over-`RingTheory.Sequence.IsRegular` definition of `Module.depthSup`
-- (bridge `RingTheory.Sequence.isRegular_cons_iff`); `Order.coheight_add_one_le`
-- supplies the strict drop of coheight.
-- ===========================================================================

open Module RingTheory.Sequence in
/-- (A, easy half of Stacks 00LF / Rees) `depth(M/xM) + 1 ≤ depth(M)` for an `M`-regular
`x ∈ m`. Proof: prepend `x` to any `M/xM`-regular sequence (in `m`) to get an
`M`-regular sequence one longer, via `isRegular_cons_iff`, then take suprema (`ENat.sSup_add`).
The reverse inequality (`depth M ≤ depth(M/xM) + 1`) is the hard half (Rees exchange). -/
@[ega "0 16.4.6" "(ii)", sga "2 III 2.5" "partial", sga "2 XII 3.4" "partial"]
theorem depth_quotient_succ_le_of_isSMulRegular {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Nontrivial M] (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) (hreg : IsSMulRegular M x) :
    Module.depthSup R (IsLocalRing.maximalIdeal R) (QuotSMulTop x M) + 1 ≤
      Module.depthSup R (IsLocalRing.maximalIdeal R) M := by
  set m := IsLocalRing.maximalIdeal R with hm
  have hNT : Nontrivial (QuotSMulTop x M) := nontrivial_quotSMulTop_of_mem_maximalIdeal M hx
  set SN :=
    {n : ℕ∞ |
      ∃ rs : List R, ↑rs.length = n ∧ (∀ r ∈ rs, r ∈ m) ∧ IsRegular (QuotSMulTop x M) rs} with
    hSN
  have hdepthN : Module.depthSup R m (QuotSMulTop x M) = sSup SN := rfl
  rw [hdepthN]
  have h0 : (0 : ℕ∞) ∈ SN := ⟨[], by simp, by simp, IsRegular.nil R (QuotSMulTop x M)⟩
  have hne : SN.Nonempty := ⟨0, h0⟩
  rw [ENat.sSup_add hne]
  apply iSup_le; intro a; apply iSup_le; intro ha
  obtain ⟨rs, hlen, hmem, hrsreg⟩ := ha
  have hcons : IsRegular M (x :: rs) := by
    rw [isRegular_cons_iff]; exact ⟨hreg, hrsreg⟩
  have hle : ((x :: rs).length : ℕ∞) ≤ Module.depthSup R m M :=
    le_sSup ⟨x :: rs, rfl, List.forall_mem_cons.2 ⟨hx, hmem⟩, hcons⟩
  simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hle
  rw [← hlen]; exact hle

-- ===========================================================================
-- Infrastructure for the Rees exchange lemma (prime avoidance + strong induction).
-- ===========================================================================

open Module RingTheory.Sequence in
/-- An `N`-regular element `y ∈ m` certifies `m ∉ Ass(N)` (regular elements avoid
the union of associated primes, `biUnion_associatedPrimes_eq_compl_regular`). -/
theorem maximalIdeal_notMem_associatedPrimes_of_isSMulRegular {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] {N : Type*}
    [AddCommGroup N] [Module R N] [Module.Finite R N] (y : R) (hy : y ∈ IsLocalRing.maximalIdeal R)
    (hyreg : IsSMulRegular N y) : (IsLocalRing.maximalIdeal R) ∉ associatedPrimes R N := by
  intro hm
  have key := biUnion_associatedPrimes_eq_compl_regular R N
  have : y ∈ ⋃ p ∈ associatedPrimes R N, (p : Set R) := by
    rw [Set.mem_iUnion₂]; exact ⟨_, hm, hy⟩
  rw [key] at this; exact this hyreg

/-- An element outside every associated prime of a finite module is regular on it. -/
private theorem isSMulRegular_of_forall_notMem_associatedPrimes {R : Type*} [CommRing R]
    [IsNoetherianRing R] {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N] {z : R}
    (h : ∀ p ∈ associatedPrimes R N, z ∉ (p : Set R)) : IsSMulRegular N z := by
  have hz : z ∉ ⋃ p ∈ associatedPrimes R N, (p : Set R) := by
    simpa only [Set.mem_iUnion, not_exists] using h
  rw [biUnion_associatedPrimes_eq_compl_regular] at hz; simpa using hz

open Module RingTheory.Sequence in
/-- Simultaneous prime avoidance over three finite modules: if `m ∉ Ass(Nᵢ)` for
`i = 1,2,3`, there is a single `z ∈ m` regular on all three. The finite union
`Ass N₁ ∪ Ass N₂ ∪ Ass N₃` cannot cover `m` (each associated prime is `⊊ m`), via
`Ideal.subset_union_prime`. -/
theorem exists_isSMulRegular_three {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {N₁ N₂ N₃ : Type*} [AddCommGroup N₁] [Module R N₁] [Module.Finite R N₁] [AddCommGroup N₂]
    [Module R N₂] [Module.Finite R N₂] [AddCommGroup N₃] [Module R N₃] [Module.Finite R N₃]
    (h₁ : (IsLocalRing.maximalIdeal R) ∉ associatedPrimes R N₁)
    (h₂ : (IsLocalRing.maximalIdeal R) ∉ associatedPrimes R N₂)
    (h₃ : (IsLocalRing.maximalIdeal R) ∉ associatedPrimes R N₃) :
    ∃ z ∈ IsLocalRing.maximalIdeal R,
      IsSMulRegular N₁ z ∧ IsSMulRegular N₂ z ∧ IsSMulRegular N₃ z := by
  classical
  set m := IsLocalRing.maximalIdeal R with hm
  set A : Set (Ideal R) :=
    associatedPrimes R N₁ ∪ associatedPrimes R N₂ ∪ associatedPrimes R N₃ with hA
  have hAfin : A.Finite :=
    ((associatedPrimes.finite R N₁).union (associatedPrimes.finite R N₂)).union
      (associatedPrimes.finite R N₃)
  set s : Finset (Ideal R) := hAfin.toFinset with hs
  have hmem : ∀ p, p ∈ s ↔ p ∈ A := by
    intro p; rw [hs, Set.Finite.mem_toFinset]
  have hnotsub : ¬((m : Set R) ⊆ ⋃ p ∈ (s : Set (Ideal R)), (↑(id p) : Set R)) := by
    intro hsub
    rw [Ideal.subset_union_prime (a := default) (b := default) ?_] at hsub
    · obtain ⟨p, hps, hle⟩ := hsub
      have hpA : p ∈ A := (hmem p).mp hps
      have hpprime : p.IsPrime := by rcases hpA with (hp | hp) | hp <;> exact hp.isPrime
      have heq : m = p := (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hpprime.ne_top hle
      rcases hpA with (hp | hp) | hp
      · exact h₁ (heq ▸ hp)
      · exact h₂ (heq ▸ hp)
      · exact h₃ (heq ▸ hp)
    · intro i hi _ _
      have hiA : i ∈ A := (hmem i).mp hi
      rcases hiA with (hp | hp) | hp <;> exact hp.isPrime
  rw [Set.not_subset] at hnotsub
  obtain ⟨z, hzm, hznot⟩ := hnotsub
  have znotA : ∀ p ∈ A, z ∉ (p : Set R) := by
    intro p hp hzp; apply hznot; simp only [Set.mem_iUnion, id_eq]; exact ⟨p, (hmem p).mpr hp, hzp⟩
  refine ⟨z, hzm, ?_, ?_, ?_⟩ <;> apply isSMulRegular_of_forall_notMem_associatedPrimes <;>
    intro p hp <;> apply znotA p
  exacts [.inl (.inl hp), .inl (.inr hp), .inr hp]

open Module RingTheory.Sequence in
/-- The length-2 prefix of an `N`-regular sequence (entries in `m`) is `N`-regular.
Properness of the truncated quotient is automatic by Nakayama. -/
theorem isRegular_prefix_two {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N] (b c : R) (rest : List R)
    (hc : c ∈ IsLocalRing.maximalIdeal R) (h : IsRegular N (b :: c :: rest)) :
    IsRegular N [b, c] := by
  rw [isRegular_cons_iff] at h ⊢
  obtain ⟨hbreg, hrest⟩ := h
  refine ⟨hbreg, ?_⟩
  have hNb : Nontrivial (QuotSMulTop b N) := hrest.nontrivial
  rw [isRegular_cons_iff] at hrest
  obtain ⟨hcreg, _⟩ := hrest
  rw [show ([c] : List R) = c :: [] from rfl, isRegular_cons_iff]
  refine ⟨hcreg, ?_⟩
  have : Nontrivial (QuotSMulTop c (QuotSMulTop b N)) :=
    nontrivial_quotSMulTop_of_mem_maximalIdeal (QuotSMulTop b N) hc
  exact IsRegular.nil R _

open Module RingTheory.Sequence in
/-- A single `N`-regular element `a ∈ m` forms an `N`-regular sequence `[a]`
(properness of `N/aN` by Nakayama). -/
theorem isRegular_singleton {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N] [Nontrivial N] (a : R)
    (ha : a ∈ IsLocalRing.maximalIdeal R) (hareg : IsSMulRegular N a) : IsRegular N [a] := by
  rw [show ([a] : List R) = a :: [] from rfl, isRegular_cons_iff]
  have : Nontrivial (QuotSMulTop a N) := nontrivial_quotSMulTop_of_mem_maximalIdeal N ha
  exact ⟨hareg, IsRegular.nil R _⟩

open Module RingTheory.Sequence Pointwise in
/-- (Base case of the Rees exchange.)
If `N` admits an `N`-regular sequence `[b, c]` of length 2 in `m` (so `depth N ≥ 2`)
and `y ∈ m` is `N`-regular, then `N/yN` has positive depth, i.e. `m ∉ Ass(N/yN)`.
Mathematically this is the depth-1 instance of `depth(N/yN) ≥ depth(N) - 1`; proved by
the η-lifting argument: were `m ∈ Ass(N/yN)`, there is `0 ≠ η̄` with `Ann(η̄) = m`,
i.e. `m·η ⊆ yN`, `η ∉ yN`; combined with `y` being `N`-regular and the length-2
witness `[b,c]` this forces a contradiction (cf. `exists_associatedPrime_quotient_gt`
and Bruns–Herzog 1.2.x / Stacks 00LF). -/
theorem maximalIdeal_notMem_associatedPrimes_quotSMulTop {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N] (b c : R)
    (hbc : RingTheory.Sequence.IsRegular N [b, c]) (hb : b ∈ IsLocalRing.maximalIdeal R)
    (hc : c ∈ IsLocalRing.maximalIdeal R) (y : R) (hyreg : IsSMulRegular N y) :
    (IsLocalRing.maximalIdeal R) ∉ associatedPrimes R (QuotSMulTop y N) := by
  classical
  intro hmAss
  rw [show ([b, c] : List R) = b :: [c] from rfl, RingTheory.Sequence.isRegular_cons_iff] at hbc
  obtain ⟨hbreg, hbc'⟩ := hbc
  rw [show ([c] : List R) = c :: [] from rfl, RingTheory.Sequence.isRegular_cons_iff] at hbc'
  obtain ⟨hcreg_quot, _⟩ := hbc'
  have := (isAssociatedPrime_iff (I := IsLocalRing.maximalIdeal R) (M := QuotSMulTop y N)).mp hmAss
  obtain ⟨hmP, ηbar, hη⟩ := this
  have hηbar0 : ηbar ≠ 0 := by
    intro h0
    apply hmP.ne_top
    rw [hη, h0]
    ext r
    simp [Submodule.mem_colon_singleton]
  have hkill : ∀ r ∈ IsLocalRing.maximalIdeal R, r • ηbar = 0 := by
    intro r hr
    have : r ∈ (⊥ : Submodule R (QuotSMulTop y N)).colon {ηbar} := hη ▸ hr
    rw [Submodule.mem_colon_singleton] at this
    simpa using this
  obtain ⟨η, rfl⟩ := Submodule.Quotient.mk_surjective _ ηbar
  have memQ : ∀ (a : R) (z : N), (Submodule.Quotient.mk z : QuotSMulTop a N) = 0 ↔
      ∃ w, a • w = z := by
    intro a z
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists]
    simp
  have memY := memQ y
  have hηnotin : ¬∃ w, y • w = η := by
    rwa [← memY]
  have hmem : ∀ r ∈ IsLocalRing.maximalIdeal R, ∃ w, y • w = r • η := fun r hr => by
    rw [← memY, Submodule.Quotient.mk_smul]; exact hkill r hr
  obtain ⟨w₁, hw₁⟩ := hmem b hb
  obtain ⟨w₂, hw₂⟩ := hmem c hc
  have hkey : y • (c • w₁) = y • (b • w₂) := by
    rw [smul_comm y c w₁, smul_comm y b w₂, hw₁, hw₂, smul_comm c b η]
  have hcw₁bw₂ : c • w₁ = b • w₂ := hyreg hkey
  have memB := memQ b
  have hcw₁zero : c • (Submodule.Quotient.mk w₁ : QuotSMulTop b N) = 0 := by
    rw [← Submodule.Quotient.mk_smul, hcw₁bw₂, memB]
    exact ⟨w₂, rfl⟩
  have hw₁zero : (Submodule.Quotient.mk w₁ : QuotSMulTop b N) = 0 :=
    hcreg_quot
      (show c • (Submodule.Quotient.mk w₁ : QuotSMulTop b N) = c • 0 by rw [smul_zero, hcw₁zero])
  rw [memB] at hw₁zero
  obtain ⟨u, hu⟩ := hw₁zero
  have hbηeq : b • η = b • (y • u) := by rw [← hw₁, ← hu, smul_comm y b u]
  have hηyu : η = y • u := hbreg hbηeq
  exact hηnotin ⟨u, hηyu.symm⟩

open Module RingTheory.Sequence in
/-- (Rees exchange engine.) Strong induction on `n`: from an `N`-regular sequence `bs`
in `m` of length `n+1` and an `N`-regular `y ∈ m`, produce an `N`-regular sequence
`y :: cs` in `m` of the same length with head `y`. The module `N` is an implicit
`∀`-binder so the inductive hypothesis applies to the quotients `N/bN` and `N/zN`.
The step picks (by simultaneous prime avoidance, `exists_isSMulRegular_three`) an
element `z` regular on `N`, `N/bN`, `N/yN` (the last via the base lemma), reorders
length-2 sequences over the local ring (`IsLocalRing.isRegular_of_perm`), and applies
the IH twice at the smaller index `n-1` (to `N/bN`, then to `N/zN`). -/
theorem rees_exchange_aux {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (n : ℕ) :
    ∀ {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N] (y : R),
      y ∈ IsLocalRing.maximalIdeal R →
        IsSMulRegular N y →
        (bs : List R) →
          (∀ r ∈ bs, r ∈ IsLocalRing.maximalIdeal R) →
            RingTheory.Sequence.IsRegular N bs →
            bs.length = n + 1 →
            ∃ cs : List R,
              cs.length = n ∧
                (∀ r ∈ cs, r ∈ IsLocalRing.maximalIdeal R) ∧
                RingTheory.Sequence.IsRegular N (y :: cs) := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro N _ _ _ y hy hyreg bs hbsmem hbsreg hlen
    have hNT : Nontrivial N := hbsreg.nontrivial
    match bs, hlen, hbsmem, hbsreg with
    | b :: bs', hlen, hbsmem, hbsreg =>
      have hbreg_full := hbsreg
      rw [isRegular_cons_iff] at hbsreg
      obtain ⟨hbreg, hbs'reg⟩ := hbsreg
      have hbmem : b ∈ IsLocalRing.maximalIdeal R := hbsmem b (List.mem_cons_self ..)
      have hbs'mem : ∀ r ∈ bs', r ∈ IsLocalRing.maximalIdeal R := fun r hr =>
        hbsmem r (List.mem_cons_of_mem b hr)
      have hbs'len : bs'.length = n := by simpa using hlen
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · subst hn0
        refine ⟨[], rfl, by simp, ?_⟩
        exact isRegular_singleton y hy hyreg
      · -- n ≥ 1, so bs' is nonempty
        rcases bs' with _ | ⟨c, rest⟩
        · exact
            absurd hbs'len
              (by
                simp; omega)
        · have hcmem : c ∈ IsLocalRing.maximalIdeal R := hbs'mem c (List.mem_cons_self ..)
          have hcreg : IsSMulRegular (QuotSMulTop b N) c :=
            (isRegular_cons_iff _ _ _ |>.mp hbs'reg).left
          have hAssN : (IsLocalRing.maximalIdeal R) ∉ associatedPrimes R N :=
            maximalIdeal_notMem_associatedPrimes_of_isSMulRegular y hy hyreg
          have hAssNb : (IsLocalRing.maximalIdeal R) ∉ associatedPrimes R (QuotSMulTop b N) :=
            maximalIdeal_notMem_associatedPrimes_of_isSMulRegular c hcmem hcreg
          have hbc : IsRegular N [b, c] := isRegular_prefix_two b c rest hcmem hbreg_full
          have hAssNy : (IsLocalRing.maximalIdeal R) ∉ associatedPrimes R (QuotSMulTop y N) :=
            maximalIdeal_notMem_associatedPrimes_quotSMulTop b c hbc hbmem hcmem y hyreg
          obtain ⟨z, hzm, hzN, hzNb, hzNy⟩ :=
            exists_isSMulRegular_three (N₁ := N) (N₂ := QuotSMulTop b N) (N₃ := QuotSMulTop y N)
              hAssN hAssNb hAssNy
          have hNyNT : Nontrivial (QuotSMulTop y N) :=
            nontrivial_quotSMulTop_of_mem_maximalIdeal N hy
          -- y is (N/zN)-regular (via [y,z] ↦ [z,y])
          have hyz : IsRegular N [y, z] := by
            rw [show ([y, z] : List R) = y :: [z] from rfl, isRegular_cons_iff]
            exact ⟨hyreg, isRegular_singleton (N := QuotSMulTop y N) z hzm hzNy⟩
          have hzy : IsRegular N [z, y] :=
            IsLocalRing.isRegular_of_perm hyz (List.Perm.swap z y [])
          have hyNz : IsSMulRegular (QuotSMulTop z N) y :=
            ((isRegular_cons_iff _ _ _).mp ((isRegular_cons_iff _ _ _).mp hzy).right).left
          have hn1 : n - 1 < n := by omega
          have hbs'len' : (c :: rest).length = (n - 1) + 1 := by
            rw [hbs'len]; omega
          -- IH on N/bN with z: produces ds (length n-1) with (N/bN)-regular z :: ds
          obtain ⟨ds, hdslen, hdsmem, hdsreg⟩ :=
            IH (n - 1) hn1 (N := QuotSMulTop b N) z hzm hzNb (c :: rest) hbs'mem hbs'reg hbs'len'
          -- transfer to: N/zN has regular sequence b :: ds (length n)
          have hbzds : IsRegular N (b :: z :: ds) := by
            rw [isRegular_cons_iff]; exact ⟨hbreg, hdsreg⟩
          have hzbds : IsRegular N (z :: b :: ds) :=
            IsLocalRing.isRegular_of_perm hbzds (List.Perm.swap z b ds)
          have hNzbds : IsRegular (QuotSMulTop z N) (b :: ds) :=
            ((isRegular_cons_iff _ _ _).mp hzbds).right
          have hbdslen : (b :: ds).length = (n - 1) + 1 := by simp only [List.length_cons, hdslen]
          -- IH on N/zN with y: produces es (length n-1) with (N/zN)-regular y :: es
          obtain ⟨es, heslen, hesmem, hesreg⟩ :=
            IH (n - 1) hn1 (N := QuotSMulTop z N) y hy hyNz (b :: ds)
              (List.forall_mem_cons.2 ⟨hbmem, hdsmem⟩) hNzbds hbdslen
          -- transfer to N: y :: z :: es is N-regular
          have hzyes : IsRegular N (z :: y :: es) := by
            rw [isRegular_cons_iff]; exact ⟨hzN, hesreg⟩
          have hyzes : IsRegular N (y :: z :: es) :=
            IsLocalRing.isRegular_of_perm hzyes (List.Perm.swap y z es)
          refine ⟨z :: es, ?_, ?_, hyzes⟩
          · simp only [List.length_cons, heslen]; omega
          · exact List.forall_mem_cons.2 ⟨hzm, hesmem⟩

open Module RingTheory.Sequence in
/-- (A-exchange, the Rees exchange property; Bruns–Herzog 1.2.x / Stacks 00LH core.)
Given an `M`-regular sequence `rs` in `m` of length `≥ 1`, and an `M`-regular element
`x ∈ m`, there is an `M`-regular sequence `ss` in `m` of the same length whose head is
`x`. This is the substantive content of the hard half of depth-drop: it lets us peel
`x` off (via `isRegular_cons_iff`) to get an `(M/xM)`-regular sequence one shorter.
Proved by prime avoidance: build `ss` element by element, choosing each next entry in
`m` avoiding the finitely many associated primes of `M / (chosen-so-far)·M` (possible
because that quotient still has a regular element, i.e. positive depth, so
`m ⊄ ⋃ Ass`), starting the choice with `x` itself. -/
theorem exists_isRegular_head_eq_of_isSMulRegular {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Nontrivial M] (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) (hreg : IsSMulRegular M x)
    (rs : List R) (hrsmem : ∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R) (hrsreg : IsRegular M rs)
    (hpos : 1 ≤ rs.length) :
    ∃ ss : List R,
      ss.length = rs.length ∧
        (∀ r ∈ ss, r ∈ IsLocalRing.maximalIdeal R) ∧ IsRegular M ss ∧ ss.head? = some x := by
  -- Reduce to the strong-induction engine `rees_exchange_aux`: set `n = rs.length - 1`
  -- so `rs.length = n + 1` (using `hpos`), obtain `cs` with `IsRegular M (x :: cs)`,
  -- then `ss = x :: cs` has the right length, entries in `m`, and head `x`.
  set n := rs.length - 1 with hn
  have hrslen : rs.length = n + 1 := by omega
  obtain ⟨cs, hcslen, hcsmem, hcsreg⟩ := rees_exchange_aux n x hx hreg rs hrsmem hrsreg hrslen
  refine ⟨x :: cs, ?_, ?_, hcsreg, by simp⟩
  · simp only [List.length_cons, hcslen]; omega
  · exact List.forall_mem_cons.2 ⟨hx, hcsmem⟩

open Module RingTheory.Sequence in
/-- (A, Stacks 00LF / Rees) Depth drops by exactly one along an `M`-regular element:
for `x ∈ m` that is `M`-regular, `depth(M/xM) + 1 = depth(M)`. Here `QuotSMulTop x M`
is the canonical `M/xM`. Built from the `sSup`-over-regular-sequences definition of
`Module.depthSup` via `RingTheory.Sequence.isRegular_cons_iff` (a regular sequence on
`M` starting with `x` ↔ `x` `M`-regular together with a regular sequence on `M/xM`). -/
@[ega "0 16.4.6",
  sga "2 III 2.5" "special case",
  sga "2 X 2.1" "more general",
  sga "2 XII 3.4" "more general"]
theorem depth_quotient_succ_of_isSMulRegular {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Nontrivial M] (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) (hreg : IsSMulRegular M x) :
    Module.depthSup R (IsLocalRing.maximalIdeal R) (QuotSMulTop x M) + 1 =
      Module.depthSup R (IsLocalRing.maximalIdeal R) M := by
  apply le_antisymm (depth_quotient_succ_le_of_isSMulRegular x hx hreg)
  -- Hard half (Stacks 00LF / Rees): depth M ≤ depth(M/xM) + 1. This reduces to the exchange lemma
  -- `exists_isRegular_head_eq_of_isSMulRegular`: it suffices (`sSup_le`) to bound every
  -- `M`-regular sequence `rs` in `m` of length `n`; for `n ≥ 1`, exchange produces an `M`-regular
  -- sequence of length `n` with head `x`, then `isRegular_cons_iff` peels `x` to give an
  -- `(M/xM)`-regular tail of length `n-1`, whence `n ≤ depth(M/xM)+1`.
  set m := IsLocalRing.maximalIdeal R with hm
  rw [show
      Module.depthSup R m M =
        sSup {n : ℕ∞ | ∃ rs : List R, ↑rs.length = n ∧ (∀ r ∈ rs, r ∈ m) ∧ IsRegular M rs}
      from rfl]
  apply sSup_le
  rintro n ⟨rs, hlen, hmem, hrsreg⟩
  rcases Nat.eq_zero_or_pos rs.length with h0 | hpos
  · rw [← hlen, h0]; simp
  · obtain ⟨ss, hsslen, hssmem, hssreg, hsshead⟩ :=
      exists_isRegular_head_eq_of_isSMulRegular x hx hreg rs hmem hrsreg hpos
    obtain ⟨tl, htl⟩ : ∃ tl, ss = x :: tl := by
      cases ss with
      | nil => simp at hsshead
      | cons a tl =>
        simp only [List.head?_cons, Option.some.injEq] at hsshead; exact ⟨tl, by rw [hsshead]⟩
    rw [htl] at hssreg hssmem hsslen
    rw [isRegular_cons_iff] at hssreg
    have htlreg : IsRegular (QuotSMulTop x M) tl := hssreg.right
    have htlmem : ∀ r ∈ tl, r ∈ m := fun r hr => hssmem r (List.mem_cons_of_mem x hr)
    have htllen : (tl.length : ℕ∞) ≤ Module.depthSup R m (QuotSMulTop x M) :=
      le_sSup ⟨tl, rfl, htlmem, htlreg⟩
    have hsum : (rs.length : ℕ∞) = tl.length + 1 := by
      rw [List.length_cons] at hsslen; rw [← hsslen]; push_cast; ring
    rw [← hlen, hsum]
    gcongr

open Module in
/-- (B, Stacks 00LK direction) If `depth(M) > 0` then there is an `M`-regular
element `x ∈ m`. Equivalently `depth M = 0 ↔ m ∈ Ass M`; here we only need the
direction giving a regular element. -/
theorem exists_isSMulRegular_of_depth_pos {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hpos : 0 < Module.depthSup R (IsLocalRing.maximalIdeal R) M) :
    ∃ x ∈ IsLocalRing.maximalIdeal R, IsSMulRegular M x := by
  -- A length-≥1 regular sequence realizing the positive depth gives its head as an
  -- `M`-regular element in `m` (unfold `Module.depthSup` `sSup`; the positivity forces a
  -- nonempty regular sequence with all entries in `m`). Alternatively, `m ⊄ ⋃ Ass M` by prime
  -- avoidance (`biUnion_associatedPrimes_eq_compl_regular`, `Ideal.subset_union_prime`,
  -- `associatedPrimes.finite`), so some `x ∈ m` is `M`-regular.
  set m := IsLocalRing.maximalIdeal R with hm
  rw [show
      Module.depthSup R m M =
        sSup
          {n : ℕ∞ |
            ∃ rs : List R, ↑rs.length = n ∧ (∀ r ∈ rs, r ∈ m) ∧ RingTheory.Sequence.IsRegular M rs}
      from rfl] at hpos
  -- positivity of the sSup forces some member to be positive
  have hmem :
    ∃
      n ∈
        {n : ℕ∞ |
          ∃ rs : List R, ↑rs.length = n ∧ (∀ r ∈ rs, r ∈ m) ∧ RingTheory.Sequence.IsRegular M rs},
      0 < n := by
    by_contra hcon
    push Not at hcon
    have :
      sSup
          {n : ℕ∞ |
            ∃ rs : List R,
              ↑rs.length = n ∧ (∀ r ∈ rs, r ∈ m) ∧ RingTheory.Sequence.IsRegular M rs} ≤
        0 :=
      sSup_le fun n hn => hcon n hn
    exact absurd (lt_of_lt_of_le hpos this) (lt_irrefl 0)
  obtain ⟨n, ⟨rs, hlen, hrsmem, hrsreg⟩, hnpos⟩ := hmem
  -- rs has positive length, hence is nonempty
  obtain ⟨a, tl, htl⟩ : ∃ a tl, rs = a :: tl := by
    cases rs with
    | nil =>
      simp only [List.length_nil, CharP.cast_eq_zero] at hlen
      rw [← hlen] at hnpos; exact absurd hnpos (lt_irrefl 0)
    | cons a tl => exact ⟨a, tl, rfl⟩
  subst htl
  rw [RingTheory.Sequence.isRegular_cons_iff] at hrsreg
  refine ⟨a, hrsmem a List.mem_cons_self, hrsreg.left⟩

open Pointwise in
/-- Nakayama: a nonzero finitely generated submodule `T` is not contained in `x • T`
for `x` in the maximal ideal. -/
theorem exists_mem_notMem_smul_of_ne_bot {R : Type*} [CommRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] {T : Submodule R M} (hTfg : T.FG) (hTne : T ≠ ⊥)
    {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R) : ∃ y ∈ T, y ∉ x • T := by
  have hxTle : x • T ≤ T := by
    rintro z hz
    rw [Submodule.mem_smul_pointwise_iff_exists] at hz
    obtain ⟨c, hc, rfl⟩ := hz
    exact T.smul_mem x hc
  have hnotle : ¬(T ≤ x • T) := fun hle => hTne
    (Submodule.eq_bot_of_eq_pointwise_smul_of_mem_jacobson_annihilator hTfg
      (le_antisymm hle hxTle)
      (Ideal.jacobson_mono bot_le (IsLocalRing.maximalIdeal_le_jacobson ⊥ hx)))
  obtain ⟨y, hyT, hyx⟩ := Set.not_subset.mp hnotle
  exact ⟨y, hyT, hyx⟩

/-- Membership in `torsionBySet R M p` for an ideal `p`, with the quantifier over `a ∈ p`. -/
private theorem mem_torsionBySet_iff_forall_mem {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] {p : Ideal R} (m : M) :
    m ∈ Submodule.torsionBySet R M (p : Set R) ↔ ∀ a ∈ p, a • m = 0 := by
  rw [Submodule.mem_torsionBySet_iff, Subtype.forall]
  rfl

open Pointwise in
/-- For `x` `M`-regular, an element of `torsionBySet p` outside `x • torsionBySet p` has
nonzero image in `M ⧸ xM`. -/
theorem quotSMulTop_mk_ne_zero_of_mem_torsionBySet {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] {x : R} (hreg : IsSMulRegular M x) {p : Ideal R} {y : M}
    (hy : y ∈ Submodule.torsionBySet R M (p : Set R))
    (hyx : y ∉ x • Submodule.torsionBySet R M (p : Set R)) :
    (Submodule.Quotient.mk y : QuotSMulTop x M) ≠ 0 := by
  rw [Ne, Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists]
  rintro ⟨m, -, hm⟩
  apply hyx
  have hmT : m ∈ Submodule.torsionBySet R M (p : Set R) := by
    refine (mem_torsionBySet_iff_forall_mem m).mpr fun a ha => hreg ?_
    change x • (a • m) = x • 0
    rw [smul_zero, smul_comm, hm]
    exact (mem_torsionBySet_iff_forall_mem y).mp hy a ha
  rw [Submodule.mem_smul_pointwise_iff_exists]
  exact ⟨m, hmT, hm⟩

open Module Pointwise in
/-- (D, the crux associated-prime construction) For `x ∈ m` that is `M`-regular and
`p ∈ Ass(M)`, there is `q ∈ Ass(M/xM)` with `p ⊊ q` (as primes). Since `x` kills
`M/xM` we have `x ∈ q`, while `x ∉ p` (an `M`-regular element avoids `Ass M`), so the
containment `p ≤ q` is strict. -/
theorem exists_associatedPrime_quotient_gt {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] (x : R)
    (hx : x ∈ IsLocalRing.maximalIdeal R) (hreg : IsSMulRegular M x) (p : Ideal R)
    (hp : p ∈ associatedPrimes R M) :
    ∃ q : Ideal R,
      ∃ hq : q ∈ associatedPrimes R (QuotSMulTop x M),
        (⟨p, hp.1⟩ : PrimeSpectrum R) < (⟨q, hq.1⟩ : PrimeSpectrum R) := by
  -- Take a witness `y` with `Ann y = p`. Let `T` be the `p`-torsion submodule of `M`;
  -- `T ≠ 0` (it contains `y`) and `T` is finite, so by Nakayama `x • T ⊊ T`. Pick
  -- `y₀ ∈ T \ x • T`. Its image `ȳ₀` in `N = M/xM` is nonzero: if `y₀ = x • m`, then
  -- `p`-torsion of `y₀` forces (by `x`-regularity) `m ∈ T`, so `y₀ ∈ x • T`, contradiction.
  -- Now `p ≤ Ann(ȳ₀)`, so any `q ∈ Ass(N)` containing `Ann(ȳ₀)` satisfies `p ≤ q`; and
  -- `x ∈ Ann N ≤ q` while `x ∉ p` (regular element avoids `Ass M`), giving `p < q`.
  classical
  have hpP : p.IsPrime := hp.isPrime
  obtain ⟨hpP', y, hy⟩ := (isAssociatedPrime_iff (I := p) (M := M)).mp hp
  have hmemAnn : ∀ (r : R) (z : M), r ∈ (⊥ : Submodule R M).colon {z} ↔ r • z = 0 := by
    intro r z; rw [Submodule.mem_colon_singleton]; simp
  set T : Submodule R M := Submodule.torsionBySet R M (p : Set R) with hT
  have hmemT : ∀ m : M, m ∈ T ↔ ∀ a ∈ p, a • m = 0 := mem_torsionBySet_iff_forall_mem
  have hyT : y ∈ T := by
    rw [hmemT]; intro a ha
    rw [hy] at ha; exact (hmemAnn a y).mp ha
  have hy0 : y ≠ 0 := by
    rintro rfl
    apply hpP.ne_top
    rw [hy]; ext r; simp [Submodule.mem_colon_singleton]
  have hTne : T ≠ ⊥ := by
    intro hTbot; rw [hTbot] at hyT; exact hy0 (by simpa using hyT)
  obtain ⟨y0, hy0T, hy0notx⟩ :=
    exists_mem_notMem_smul_of_ne_bot (IsNoetherian.noetherian T) hTne hx
  set N := QuotSMulTop x M with hN
  set ybar : N := Submodule.Quotient.mk y0 with hybar
  have hybar0 : ybar ≠ 0 := quotSMulTop_mk_ne_zero_of_mem_torsionBySet hreg hy0T hy0notx
  have hpAnn : p ≤ (⊥ : Submodule R N).colon {ybar} := by
    intro a ha
    rw [Submodule.mem_colon_singleton]
    simp only [Submodule.mem_bot]
    rw [hybar, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    rw [(hmemT y0).mp hy0T a ha]
    exact zero_mem _
  obtain ⟨q, hqAss, hqle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R ybar hybar0
  refine ⟨q, hqAss, ?_⟩
  have hxq : x ∈ q := by
    have hxAnnN : x ∈ Module.annihilator R N := QuotSMulTop.mem_annihilator M x
    have hle := hqAss.annihilator_le
    rw [Submodule.annihilator_top] at hle
    exact hle hxAnnN
  have hxnp : x ∉ p := by
    intro hxp
    have hxin : x ∈ ⋃ p ∈ associatedPrimes R M, (p : Set R) := Set.mem_iUnion₂.mpr ⟨p, hp, hxp⟩
    rw [biUnion_associatedPrimes_eq_compl_regular] at hxin
    exact hxin hreg
  exact (lt_of_le_of_ne (hpAnn.trans hqle) fun h => hxnp (h ▸ hxq) : p < q)

open Module in
/-- (F) `depth(M)` is finite for a finite module `M` over a Noetherian local ring
(`depth M ≤ supportDim M < ⊤`). Needed to extract a natural-number bound for the
induction in `depthSup_le_coheight_of_depthSup_le`. -/
@[ega "0 16.4.5" "partial", sga "2 III 2.7" "special case"]
theorem depth_ne_top {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {M : Type*}
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.depthSup R (IsLocalRing.maximalIdeal R) M ≠ ⊤ := by
  -- Inputs: every `m`-regular sequence has length ≤ `supportDim M` (each
  -- regular element strictly drops the support dimension; cf.
  -- `Module.supportDim_add_length_eq_supportDim_of_isRegular`), and `supportDim M`
  -- is finite (Noetherian). Hence the `sSup` defining `depth` is finite.
  -- Extract a natural-number bound N from the (finite) Krull dimension of R.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ringKrullDim R = ((N : ℕ∞) : WithBot ℕ∞) := by
    have hbot : ringKrullDim R ≠ ⊥ := ringKrullDim_ne_bot
    have htop : ringKrullDim R ≠ ⊤ := ringKrullDim_ne_top
    obtain ⟨x, hx⟩ := WithBot.ne_bot_iff_exists.mp hbot
    rw [← hx] at htop ⊢
    have hxtop : x ≠ ⊤ := by
      intro h; apply htop; rw [h]; rfl
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hxtop
    exact ⟨n, by rw [← hn]⟩
  -- It suffices to show depth ≤ N, since N < ⊤.
  suffices h : Module.depthSup R (IsLocalRing.maximalIdeal R) M ≤ (N : ℕ∞) by
    intro htop; rw [htop] at h; exact (not_le.mpr (ENat.natCast_lt_top N)) h
  rw [Module.depthSup]
  apply sSup_le
  rintro n ⟨rs, hlen, hmem, hreg⟩
  subst hlen
  -- Key bound in WithBot ℕ∞: ↑rs.length ≤ supportDim M ≤ ringKrullDim R = ↑↑N
  have hquot_nt : Nontrivial (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)) :=
    (Submodule.Quotient.nontrivial_iff).mpr (Ne.symm hreg.top_ne_smul)
  have hsd_ne_bot : Module.supportDim R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)) ≠ ⊥ :=
    (Module.supportDim_ne_bot_iff_nontrivial R _).mpr hquot_nt
  have heq := Module.supportDim_add_length_eq_supportDim_of_isRegular rs hreg
  have hle1 : (↑rs.length : WithBot ℕ∞) ≤ Module.supportDim R M := by
    rw [← heq]
    exact WithBot.le_add_self hsd_ne_bot _
  have hle2 : Module.supportDim R M ≤ ringKrullDim R := Module.supportDim_le_ringKrullDim R M
  have hle3 : (↑rs.length : WithBot ℕ∞) ≤ ((N : ℕ∞) : WithBot ℕ∞) := by
    rw [← hN]; exact le_trans hle1 hle2
  exact_mod_cast hle3

open Module RingTheory.Sequence in
/-- (Induction core of Stacks 0AUJ.) For every natural bound `n`, any finite module
`M` with `depth(M) ≤ n` and any `p ∈ Ass(M)` satisfies `depth(M) ≤ coheight p`.
Proved by induction on `n` using (A) depth-drop, (B) existence of a regular element,
(D) the associated-prime strict containment, and the library coheight strict drop
`Order.coheight_add_one_le`. The module `M` is an implicit `∀`-binder so the IH can
be applied to the strictly smaller `QuotSMulTop x M`. -/
@[ega "0 16.4.6" "(iii)"]
theorem depthSup_le_coheight_of_depthSup_le {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (n : ℕ) :
    ∀ {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M],
      Module.depthSup R (IsLocalRing.maximalIdeal R) M ≤ (n : ℕ∞) →
        ∀ (p : Ideal R) (hp : p ∈ associatedPrimes R M),
          (↑(Module.depthSup R (IsLocalRing.maximalIdeal R) M) : WithBot ℕ∞) ≤
            (Order.coheight (⟨p, hp.1⟩ : PrimeSpectrum R) : WithBot ℕ∞) := by
  induction n with
  | zero =>
    intro M _ _ _ hdepth p hp
    have h0 : Module.depthSup R (IsLocalRing.maximalIdeal R) M = 0 :=
      le_antisymm hdepth (by positivity)
    rw [h0]; simp
  | succ k IH =>
    intro M _ _ _ hdepth p hp
    by_cases hz : Module.depthSup R (IsLocalRing.maximalIdeal R) M = 0
    · rw [hz]; simp
    · have hpos : 0 < Module.depthSup R (IsLocalRing.maximalIdeal R) M := pos_iff_ne_zero.mpr hz
      obtain ⟨x, hxm, hxreg⟩ := exists_isSMulRegular_of_depth_pos hpos
      -- Positive depth forces `M` nontrivial: a subsingleton module has empty
      -- depth set (no regular sequence, since `IsRegular` requires `⊤ ≠ I • ⊤`),
      -- hence depth `0`, contradicting `hpos`.
      have hNT : Nontrivial M := by
        rw [← not_subsingleton_iff_nontrivial]
        intro hSub
        have hd0 : Module.depthSup R (IsLocalRing.maximalIdeal R) M = 0 := by
          rw [Module.depthSup]
          refine le_antisymm (sSup_le ?_) (by positivity)
          rintro n ⟨rs, -, -, hreg⟩
          exact (hreg.top_ne_smul (Subsingleton.elim _ _)).elim
        exact lt_irrefl _ (hd0 ▸ hpos)
      have hdrop := depth_quotient_succ_of_isSMulRegular x hxm hxreg
      obtain ⟨q, hq, hpq⟩ := exists_associatedPrime_quotient_gt x hxm hxreg p hp
      have hcoh :
        Order.coheight (⟨q, hq.isPrime⟩ : PrimeSpectrum R) + 1 ≤
          Order.coheight (⟨p, hp.isPrime⟩ : PrimeSpectrum R) :=
        Order.coheight_add_one_le hpq
      have hQdepth :
        Module.depthSup R (IsLocalRing.maximalIdeal R) (QuotSMulTop x M) ≤ (k : ℕ∞) := by
        have hle :
          Module.depthSup R (IsLocalRing.maximalIdeal R) (QuotSMulTop x M) + 1 ≤ (k : ℕ∞) + 1 := by
          rw [hdrop]; exact_mod_cast hdepth
        exact (WithTop.add_le_add_iff_right (WithTop.one_ne_top)).mp hle
      have hIH := IH hQdepth q hq
      have hcast :
        (↑(Module.depthSup R (IsLocalRing.maximalIdeal R) M) : WithBot ℕ∞) =
          (↑(Module.depthSup R (IsLocalRing.maximalIdeal R) (QuotSMulTop x M)) : WithBot ℕ∞) +
            1 := by
        rw [← hdrop]; push_cast; ring
      rw [hcast]
      have hcoh' :
        (↑(Order.coheight (⟨q, hq.isPrime⟩ : PrimeSpectrum R)) : WithBot ℕ∞) + 1 ≤
          (↑(Order.coheight (⟨p, hp.isPrime⟩ : PrimeSpectrum R)) : WithBot ℕ∞) := by
        exact_mod_cast hcoh
      calc
        (↑(Module.depthSup R (IsLocalRing.maximalIdeal R) (QuotSMulTop x M)) : WithBot ℕ∞) + 1 ≤
            (↑(Order.coheight (⟨q, hq.isPrime⟩ : PrimeSpectrum R)) : WithBot ℕ∞) + 1 :=
          by gcongr
        _ ≤ _ := hcoh'

open Module in
/-- (Stacks 0AUJ.) For a finite module `M` over a Noetherian local ring and
`p ∈ Ass(M)`, `depth(M) ≤ dim(R/p) = coheight p`. Reduces to
`depthSup_le_coheight_of_depthSup_le` by
extracting a natural bound `n` with `depth M ≤ n` (finiteness from `depth_ne_top`). -/
theorem depthSup_le_coheight_of_mem_associatedPrimes {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] (p : Ideal R)
    (hp : p ∈ associatedPrimes R M) :
    (↑(Module.depthSup R (IsLocalRing.maximalIdeal R) M) : WithBot ℕ∞) ≤
      (Order.coheight (⟨p, hp.1⟩ : PrimeSpectrum R) : WithBot ℕ∞) := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (depth_ne_top (R := R) (M := M))
  exact depthSup_le_coheight_of_depthSup_le n (le_of_eq hn.symm) p hp

/-- The Cohen–Macaulay equality `depth M = supportDim M`, as an equality in `WithBot ℕ∞`. -/
private theorem depthSup_eq_supportDim_of_isCohenMacaulayModule {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] (hCM : IsCohenMacaulayModule R M) :
    (↑(Module.depthSup R (IsLocalRing.maximalIdeal R) M) : WithBot ℕ∞) =
      Module.supportDim R M := by
  unfold IsCohenMacaulayModule at hCM
  rw [Module.supportDim]; exact hCM

open Module in
/-- (Stacks 0AUJ + Cohen–Macaulay equidimensionality.) For a Cohen–Macaulay finite module `M` over
a Noetherian local ring, every associated prime `p ∈ Ass(M)` has `supportDim M ≤ coheight p` (in
fact equality holds, giving equidimensionality). This is the substantive input to conjunct (a) of
Stacks 00N4. The CM equality `depth M = supportDim M` (`hCM`) reduces it to Stacks 0AUJ
(`depthSup_le_coheight_of_mem_associatedPrimes`). -/
theorem supportDim_le_coheight_of_isCohenMacaulayModule {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] (hCM : IsCohenMacaulayModule R M)
    (p : Ideal R) (hp : p ∈ associatedPrimes R M) :
    Module.supportDim R M ≤ (Order.coheight (⟨p, hp.1⟩ : PrimeSpectrum R) : WithBot ℕ∞) := by
  rw [← depthSup_eq_supportDim_of_isCohenMacaulayModule hCM]
  exact depthSup_le_coheight_of_mem_associatedPrimes p hp

-- ===========================================================================
-- Helper infrastructure for conjunct (b2): CM-quotient by a regular sequence,
-- LinearEquiv transport of depth/supportDim/regularity, and quotient algebra.
-- ===========================================================================

open Module in
/-- Abstract form of the conjunct-(a) avoidance argument: if `Q` is Cohen–Macaulay and
`krullDim(Supp Q ∩ V(g)) < supportDim Q`, then `g` is `Q`-regular. (Specialization-closed
sets + equidimensionality `supportDim_le_coheight_of_isCohenMacaulayModule`.) -/
@[ega "0 16.5.5" "Implication b) ⇒ a)"]
theorem isSMulRegular_of_supportDim_inter_lt {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {Q : Type*} [AddCommGroup Q] [Module R Q] [Module.Finite R Q]
    (hQCM : IsCohenMacaulayModule R Q) (g : R)
    (hlt :
      Order.krullDim
          (↑(Module.support R Q ∩ PrimeSpectrum.zeroLocus (↑(Ideal.span {g}) : Set R)) :
            Set (PrimeSpectrum R)) <
        Module.supportDim R Q) :
    IsSMulRegular Q g := by
  have key := biUnion_associatedPrimes_eq_compl_regular R Q
  rw [show IsSMulRegular Q g ↔ g ∈ {r | IsSMulRegular Q r} from Iff.rfl, ←
    compl_compl {r | IsSMulRegular Q r}, ← key, Set.mem_compl_iff]
  simp only [Set.mem_iUnion, not_exists]
  intro p hp hgp
  set P : PrimeSpectrum R := ⟨p, hp.isPrime⟩ with hPdef
  have hPsupp : P ∈ Module.support R Q := by
    rw [Module.support_eq_zeroLocus, PrimeSpectrum.mem_zeroLocus]
    have := hp.annihilator_le
    rw [Submodule.annihilator_top] at this
    exact this
  have hPVg : P ∈ PrimeSpectrum.zeroLocus (↑(Ideal.span {g}) : Set R) := by
    rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.span_le,
      Set.singleton_subset_iff]
    exact hgp
  have hPS : P ∈ Module.support R Q ∩ PrimeSpectrum.zeroLocus (↑(Ideal.span {g}) : Set R) :=
    ⟨hPsupp, hPVg⟩
  have hSspec :
    ∀ x ∈ Module.support R Q ∩ PrimeSpectrum.zeroLocus (↑(Ideal.span {g}) : Set R),
      ∀ y,
        x ≤ y → y ∈ Module.support R Q ∩ PrimeSpectrum.zeroLocus (↑(Ideal.span {g}) : Set R) := by
    intro x hx y hxy
    refine ⟨?_, ?_⟩
    · rw [Module.support_eq_zeroLocus] at hx ⊢
      exact zeroLocus_specializationClosed _ x hx.left y hxy
    · exact zeroLocus_specializationClosed _ x hx.right y hxy
  have hcoh := coheight_le_krullDim_of_specializationClosed _ hSspec P hPS
  have hL2P := supportDim_le_coheight_of_isCohenMacaulayModule hQCM p hp
  exact absurd (lt_of_le_of_lt (le_trans hL2P hcoh) hlt) (lt_irrefl _)

open Module RingTheory.Sequence in
/-- The quotient `M ⧸ I•⊤` is functorial in `M` along a linear equivalence. -/
noncomputable def quotEquivOfEquiv {R : Type*} [CommRing R] {M M' : Type*} [AddCommGroup M]
    [Module R M] [AddCommGroup M'] [Module R M'] (e : M ≃ₗ[R] M') (I : Ideal R) :
    (M ⧸ I • (⊤ : Submodule R M)) ≃ₗ[R] (M' ⧸ I • (⊤ : Submodule R M')) := by
  apply Submodule.Quotient.equiv (I • ⊤) (I • ⊤) e
  rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]

open Module RingTheory.Sequence in
/-- Regularity of a sequence transports along a linear equivalence. -/
theorem isRegular_of_linearEquiv {R : Type*} [CommRing R] {M M' : Type*} [AddCommGroup M]
    [Module R M] [AddCommGroup M'] [Module R M'] (e : M ≃ₗ[R] M') (rs : List R)
    (h : IsRegular M rs) : IsRegular M' rs := by
  rw [isRegular_iff] at h ⊢
  obtain ⟨hw, hprop⟩ := h
  refine ⟨⟨fun i hi => ?_⟩, ?_⟩
  · exact
      ((hw.regular_mod_prev i hi).of_injective
        (quotEquivOfEquiv e (Ideal.ofList (List.take i rs))).symm.toLinearMap
        (quotEquivOfEquiv e (Ideal.ofList (List.take i rs))).symm.injective)
  · intro heq
    apply hprop
    have hntM' : ¬Nontrivial (M' ⧸ Ideal.ofList rs • (⊤ : Submodule R M')) := by
      rw [Submodule.Quotient.nontrivial_iff]; push Not; exact heq.symm
    have : ¬Nontrivial (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)) := fun hc =>
      hntM' ((quotEquivOfEquiv e (Ideal.ofList rs)).symm.toEquiv.nontrivial)
    rw [Submodule.Quotient.nontrivial_iff] at this; push Not at this; exact this.symm

open Module in
/-- Depth is invariant under a linear equivalence. -/
theorem depth_eq_of_linearEquiv {R : Type*} [CommRing R] {M M' : Type*} [AddCommGroup M]
    [Module R M] [AddCommGroup M'] [Module R M'] (I : Ideal R) (e : M ≃ₗ[R] M') :
    Module.depthSup R I M = Module.depthSup R I M' := by
  unfold Module.depthSup
  congr 1
  ext n
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨rs, hlen, hmem, hreg⟩; exact ⟨rs, hlen, hmem, isRegular_of_linearEquiv e rs hreg⟩
  · rintro ⟨rs, hlen, hmem, hreg⟩; exact ⟨rs, hlen, hmem, isRegular_of_linearEquiv e.symm rs hreg⟩

open Module in
/-- Support dimension is invariant under a linear equivalence. -/
theorem supportDim_eq_of_linearEquiv {R : Type*} [CommRing R] {M M' : Type*} [AddCommGroup M]
    [Module R M] [AddCommGroup M'] [Module R M'] [Module.Finite R M] [Module.Finite R M']
    (e : M ≃ₗ[R] M') : Module.supportDim R M = Module.supportDim R M' := by
  unfold Module.supportDim
  rw [Module.support_eq_zeroLocus, Module.support_eq_zeroLocus, e.annihilator_eq]

open Module in
/-- Cohen–Macaulayness transports along a linear equivalence. -/
theorem isCohenMacaulay_of_linearEquiv {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {M M' : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup M'] [Module R M'] [Module.Finite R M'] (e : M ≃ₗ[R] M')
    (h : IsCohenMacaulayModule R M) : IsCohenMacaulayModule R M' := by
  unfold IsCohenMacaulayModule at h ⊢
  rw [show Order.krullDim ↑(Module.support R M') = Module.supportDim R M' from rfl, ←
    supportDim_eq_of_linearEquiv e,
    ← _root_.depth_eq_of_linearEquiv (IsLocalRing.maximalIdeal R) e]
  exact h

open Module RingTheory.Sequence in
/-- (Stacks 00N4 inductive step.) The quotient of a Cohen–Macaulay module by a single
`M`-regular element `x ∈ m` is Cohen–Macaulay: depth and support dimension both drop by one. -/
@[ega "0 16.4.10" "(i), special case", ega "0 16.5.5", ega "0 16.5.6" "special case"]
theorem isCohenMacaulay_quotSMulTop_of_isSMulRegular {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Nontrivial M] (hCM : IsCohenMacaulayModule R M) (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hreg : IsSMulRegular M x) : IsCohenMacaulayModule R (QuotSMulTop x M) := by
  have heqM := depthSup_eq_supportDim_of_isCohenMacaulayModule hCM
  have hNTQ : Nontrivial (QuotSMulTop x M) := nontrivial_quotSMulTop_of_mem_maximalIdeal M hx
  have hreg1 : IsRegular M [x] := isRegular_singleton x hx hreg
  have hsdQ : Module.supportDim R (QuotSMulTop x M) + 1 = Module.supportDim R M := by
    have hsd := Module.supportDim_add_length_eq_supportDim_of_isRegular [x] hreg1
    simp only [List.length_singleton, Nat.cast_one] at hsd
    have hsupp1 :
      Module.support R (QuotSMulTop x M) =
        Module.support R M ∩ PrimeSpectrum.zeroLocus (↑(Ideal.span {x}) : Set R) := by
      unfold QuotSMulTop
      rw [← Submodule.ideal_span_singleton_smul x ⊤, Module.support_quotient]
    have hsupp2 :
      Module.support R (M ⧸ Ideal.ofList [x] • (⊤ : Submodule R M)) =
        Module.support R M ∩ PrimeSpectrum.zeroLocus (↑(Ideal.span {x}) : Set R) := by
      rw [Module.support_quotient, show Ideal.ofList [x] = Ideal.span {x} by simp [Ideal.ofList]]
    have heqd :
      Module.supportDim R (QuotSMulTop x M) =
        Module.supportDim R (M ⧸ Ideal.ofList [x] • (⊤ : Submodule R M)) := by
      unfold Module.supportDim; rw [hsupp1, hsupp2]
    rw [heqd]; exact hsd
  have hdrop := depth_quotient_succ_of_isSMulRegular x hx hreg
  unfold IsCohenMacaulayModule
  rw [show
      Order.krullDim ↑(Module.support R (QuotSMulTop x M)) = Module.supportDim R (QuotSMulTop x M)
      from rfl]
  have hdropW :
    (↑(Module.depthSup R (IsLocalRing.maximalIdeal R) (QuotSMulTop x M)) : WithBot ℕ∞) + 1 =
      (↑(Module.depthSup R (IsLocalRing.maximalIdeal R) M) : WithBot ℕ∞) := by
    rw [← hdrop]; push_cast; ring
  rw [heqM, ← hsdQ] at hdropW
  exact ENat.WithBot.add_natCast_cancel (c := 1).mp hdropW
end
