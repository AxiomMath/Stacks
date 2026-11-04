module

public import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
public import StacksFrontier.RingTheory.CohenMacaulay.Module.DimensionDrop
public import StacksFrontier.RingTheory.RegularLocalRing.Criteria
public import StacksFrontier.RingTheory.Serre.Reduced
import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extending a dimension-dropping family to a maximal regular sequence

Throughout, `R` is a Noetherian local ring with maximal ideal `m` and `M` is a finite, i.e.
finitely generated, `R`-module. We write `Supp M` for the support of `M` as a closed subset of
`Spec R` and `dim (Supp M)` for its Krull dimension as a topological space.

## Main result

Let `M` be a Cohen-Macaulay `R`-module whose support has dimension `d = dim (Supp M)` and let
`g₁, …, g_c ∈ m` satisfy `dim (Supp (M / (g₁, …, g_c) M)) = d - c`. Then `g₁, …, g_c` is an
`M`-regular sequence, and it extends to a maximal `M`-regular sequence: there are
`g_{c+1}, …, g_d ∈ m` such that `g₁, …, g_d` is a maximal `M`-regular sequence, of length
`d = depth M`. This is Stacks Proposition 10.103.4, tag 00N6.

## Conventions

* An element `g ∈ R` is a *nonzerodivisor* on `M`, equivalently `M`-*regular*, if
  `g • (-) : M → M` is injective; in Mathlib, `IsSMulRegular M g`.
* An `M`-*regular sequence* is a sequence `g₁, …, g_c` such that each `g_{i+1}` is a
  nonzerodivisor on `M / (g₁, …, gᵢ) M` and `(g₁, …, g_c) M ≠ M`; in Mathlib,
  `RingTheory.Sequence.IsRegular M gs`, which packages the nonzerodivisor conditions
  (`regular_mod_prev`) together with the proper-submodule condition
  `⊤ ≠ Ideal.ofList gs • ⊤` (`top_ne_smul`).
* `Module.depthSup R m M` is the supremum of the lengths of `M`-regular sequences with all entries
  in `m`.
* `dim (Supp M)` is `Module.supportDim R M = Order.krullDim (Module.support R M)`, the Krull
  dimension of the support as a subspace of `Spec R`. For `M = 0` this is `⊥ = -∞`, so the
  hypothesis `dim (Supp M) = d` with `d : ℕ` forces `M ≠ 0`; this is also reflected by the
  `[Nontrivial M]` assumption.
* The quotient `M / (g₁, …, g_c) M` is `M ⧸ (Ideal.ofList gs • ⊤)`, where
  `Ideal.ofList gs = (g₁, …, g_c)`.
* `d - c` is truncated natural subtraction. The mathematical hypothesis
  `dim (Supp (M / (g₁, …, g_c) M)) = d - c` forces `c ≤ d`, since dimensions here are
  nonnegative integers, so `hcd : c ≤ d` is included explicitly and `(d - c : ℕ)` faithfully
  represents the intended difference.

Cited antecedents available in Mathlib: Stacks 00KW is
`ringKrullDim_le_ringKrullDim_quotSMulTop_succ`, Stacks 00DS is `Ideal.subset_union_prime`
(prime avoidance), and Stacks 00LJ is `IsLocalRing.isRegular_of_perm`.

## Further contents

After the proof of Stacks 00N6 this file contains the basic API of `IsCohenMacaulayModule`
(Stacks 00N3, 00N5, 0C6G, 0BUS, 00NF, 0AAH) and the invariance of Cohen-Macaulayness under
restriction of scalars along a surjection of Noetherian local rings (Stacks 0AAD); each of these
has its own section docstring below.
-/

@[expose] public section

open IsLocalRing RingTheory.Sequence

open scoped Pointwise in
/-- **Existence of a dimension-dropping regular element (system-of-parameters step).**
For a CM module `N` of positive support dimension `e`, there is `g ∈ m`, regular on `N`,
with `supportDim(QuotSMulTop g N) = e - 1`. The element is produced by prime avoidance
over the (finitely many) associated primes of `N`. -/
theorem exists_mem_maximalIdeal_dimDrop
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N] [Nontrivial N]
    (hCM : IsCohenMacaulay R N)
    (e : ℕ) (he : Module.supportDim R N = (e : WithBot ℕ∞)) (hpos : 1 ≤ e) :
    ∃ g ∈ maximalIdeal R, IsSMulRegular N g ∧
      Module.supportDim R (QuotSMulTop g N) = ((e - 1 : ℕ) : WithBot ℕ∞) := by
  have hne : ∀ p ∈ associatedPrimes R N, ¬ maximalIdeal R ≤ p := fun _ hp =>
    not_maximalIdeal_le_of_mem_associatedPrimes_of_isCohenMacaulay hCM he hpos hp
  have hne_min : ∀ p ∈ (Module.annihilator R N).minimalPrimes, ¬ maximalIdeal R ≤ p :=
    fun _ hp => not_maximalIdeal_le_of_mem_minimalPrimes_annihilator he hpos hp
  -- Prime avoidance over `Ass(N) ∪ minimalPrimes(Ann N)`: pick `g ∈ m` outside all of them.
  have hfin : (associatedPrimes R N).Finite := associatedPrimes.finite R N
  have hfinm : (Module.annihilator R N).minimalPrimes.Finite :=
    Ideal.finite_minimalPrimes_of_isNoetherianRing R _
  set s : Finset (Ideal R) := hfin.toFinset ∪ hfinm.toFinset with hs
  have hmem_s : ∀ p, p ∈ s ↔ p ∈ associatedPrimes R N ∨ p ∈ (Module.annihilator R
      N).minimalPrimes := by
    intro p
    rw [hs, Finset.mem_union, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
  have hprime_s : ∀ p ∈ s, p.IsPrime := by
    intro p hp
    rcases (hmem_s p).mp hp with h | h
    · exact h.isPrime
    · exact h.isPrime
  -- not contained in the union
  have hnsub : ¬ (maximalIdeal R : Set R) ⊆ ⋃ p ∈ (s : Set (Ideal R)), (p : Set R) := by
    rw [Ideal.subset_union_prime (maximalIdeal R) (maximalIdeal R)
      (fun p hp _ _ => hprime_s p hp)]
    rintro ⟨p, hps, hple⟩
    rcases (hmem_s p).mp hps with h | h
    · exact hne p h hple
    · exact hne_min p h hple
  -- extract the avoiding element
  rw [Set.not_subset] at hnsub
  obtain ⟨g, hgm, hgnotin⟩ := hnsub
  simp only [Set.mem_iUnion, not_exists, Finset.mem_coe] at hgnotin
  have hgm' : g ∈ maximalIdeal R := hgm
  -- `g` avoids all associated primes and all minimal primes of `Ann N`.
  have hgnotin_ass : ∀ p ∈ associatedPrimes R N, g ∉ p := fun p hp =>
    hgnotin p ((hmem_s p).mpr (Or.inl hp))
  have hgmin : ∀ p ∈ (Module.annihilator R N).minimalPrimes, g ∉ p := fun p hp =>
    hgnotin p ((hmem_s p).mpr (Or.inr hp))
  -- `g` is regular on `N`: it avoids every associated prime.
  have hgreg : IsSMulRegular N g := by
    have hkey := biUnion_associatedPrimes_eq_compl_regular R N
    by_contra hng
    have hmemc : g ∈ ({r | IsSMulRegular N r}ᶜ) := hng
    rw [← hkey] at hmemc
    simp only [Set.mem_iUnion] at hmemc
    obtain ⟨p, hp, hgp⟩ := hmemc
    exact hgnotin_ass p hp hgp
  -- The dimension drops by exactly one.
  refine ⟨g, hgm', hgreg, ?_⟩
  exact supportDim_quotSMulTop_eq_sub_one_of_le he hpos hgm'
    (supportDim_quotSMulTop_le_of_avoid_minimalPrimes g e he hpos hgmin)

/-- Quotienting by the empty list of elements does not change the module. -/
private theorem quotOfList_nil_nonempty_linearEquiv
    {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N] :
    Nonempty ((N ⧸ (Ideal.ofList ([] : List R) • (⊤ : Submodule R N))) ≃ₗ[R] N) := by
  rw [Ideal.ofList_nil, Submodule.bot_smul]
  exact ⟨Submodule.quotEquivOfEqBot ⊥ rfl⟩

open scoped Pointwise in
/-- **CM propagation down the dim-drop tower.**
`N ⧸ ofList gs • ⊤` is itself nonzero and Cohen–Macaulay (of support dimension `e - |gs|`).
Same inductive structure: per-step exact drop via the 00KW telescoping bound, head
regularity / nontriviality via `stacks00N5_step`, CM-propagation via
`cohenMacaulay_quotSMulTop_of_dimDrop`. -/
@[ega "0 16.5.6" "(x)"]
theorem cohenMacaulay_quotOfList_of_dimDrop
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (e : ℕ) :
    ∀ {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N] [Nontrivial N],
      Module.supportDim R N = (e : WithBot ℕ∞) → IsCohenMacaulay R N →
      ∀ (gs : List R), gs.length ≤ e → (∀ g ∈ gs, g ∈ maximalIdeal R) →
      Module.supportDim R (N ⧸ (Ideal.ofList gs • (⊤ : Submodule R N)))
        = ((e - gs.length : ℕ) : WithBot ℕ∞) →
      Nontrivial (N ⧸ (Ideal.ofList gs • (⊤ : Submodule R N))) ∧
        Module.supportDim R (N ⧸ (Ideal.ofList gs • (⊤ : Submodule R N)))
          = (Module.depthSup R (maximalIdeal R)
              (N ⧸ (Ideal.ofList gs • (⊤ : Submodule R N))) : WithBot ℕ∞) := by
  intro N _ _ _ _ he hCM gs
  induction gs generalizing e N with
  | nil =>
    intro _ _ _
    obtain ⟨heq⟩ := quotOfList_nil_nonempty_linearEquiv (R := R) (N := N)
    refine ⟨heq.toEquiv.nontrivial, ?_⟩
    rw [Module.supportDim_eq_of_equiv heq, depth_eq_of_linearEquiv (maximalIdeal R) heq]
    exact hCM
  | cons g gs' ih =>
    intro hlen hmem hdim
    have hg : g ∈ maximalIdeal R := hmem g (by simp)
    have hlen₁ : gs'.length + 1 ≤ e := hlen
    have hmemtail : ∀ x ∈ gs', x ∈ maximalIdeal R := fun x hx => hmem x (by simp [hx])
    have hbridgeN := quotOfList_cons_supportDim_eq (N := N) g gs'
    -- supportDim((QuotSMulTop g N) ⧸ ofList gs' • ⊤) = e - (|gs'|+1)
    have hdimQ : Module.supportDim R
          ((QuotSMulTop g N) ⧸ (Ideal.ofList gs' • (⊤ : Submodule R (QuotSMulTop g N))))
        = ((e - (gs'.length + 1) : ℕ) : WithBot ℕ∞) := by
      rw [hbridgeN, hdim]; simp only [List.length_cons]
    have hdrop : Module.supportDim R (QuotSMulTop g N) = ((e - 1 : ℕ) : WithBot ℕ∞) :=
      supportDim_quotSMulTop_eq_sub_one_of_dimDrop he hg hmemtail
        hlen₁ hdimQ
    have : Nontrivial (QuotSMulTop g N) :=
      nontrivial_quotSMulTop_of_mem_maximalIdeal N hg
    have hCMQ : IsCohenMacaulay R (QuotSMulTop g N) :=
      cohenMacaulay_quotSMulTop_of_dimDrop hCM e he (by omega) g hg hdrop
    have hdimtail : Module.supportDim R
          ((QuotSMulTop g N) ⧸ (Ideal.ofList gs' • (⊤ : Submodule R (QuotSMulTop g N))))
        = (((e - 1) - gs'.length : ℕ) : WithBot ℕ∞) := by
      rw [hdimQ]; congr 1; omega
    -- recursion gives Nontrivial + CM of (QuotSMulTop g N) ⧸ ofList gs' • ⊤.
    obtain ⟨hnt2, hCM2⟩ := ih (e - 1) (N := QuotSMulTop g N) hdrop hCMQ (by omega) hmemtail hdimtail
    -- transport along the cons bridge LinearEquiv.
    obtain ⟨hequiv⟩ := nonempty_quotSMulTop_quotient_ofList_linearEquiv (N := N) g gs'
    have : Nontrivial ((QuotSMulTop g N) ⧸
        (Ideal.ofList gs' • (⊤ : Submodule R (QuotSMulTop g N)))) := hnt2
    refine ⟨hequiv.toEquiv.symm.nontrivial, ?_⟩
    show Module.supportDim R (N ⧸ (Ideal.ofList (g :: gs') • (⊤ : Submodule R N)))
      = (Module.depthSup R (maximalIdeal R)
          (N ⧸ (Ideal.ofList (g :: gs') • (⊤ : Submodule R N))) : WithBot ℕ∞)
    rw [← Module.supportDim_eq_of_equiv hequiv, ← depth_eq_of_linearEquiv (maximalIdeal R)
        hequiv]
    exact hCM2

open scoped Pointwise in
/-- **Append bridge.** `(N ⧸ ofList gs • ⊤) ⧸ ofList l • ⊤` and `N ⧸ ofList (gs ++ l) • ⊤`
have the same support dimension. -/
theorem quotOfList_append_supportDim_eq
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N]
    (gs l : List R) :
    Module.supportDim R ((N ⧸ (Ideal.ofList gs • (⊤ : Submodule R N))) ⧸
      (Ideal.ofList l • (⊤ : Submodule R (N ⧸ (Ideal.ofList gs • (⊤ : Submodule R N))))))
      = Module.supportDim R (N ⧸ (Ideal.ofList (gs ++ l) • (⊤ : Submodule R N))) := by
  set S : Submodule R N := Ideal.ofList gs • ⊤ with hS
  set T : Submodule R N := Ideal.ofList (gs ++ l) • ⊤ with hT
  have hST : S ≤ T := by
    rw [hS, hT, Ideal.ofList_append, Submodule.sup_smul]
    exact le_sup_left
  have hmap : Submodule.map S.mkQ T
      = Ideal.ofList l • (⊤ : Submodule R (N ⧸ (Ideal.ofList gs • (⊤ : Submodule R N)))) := by
    rw [hT, Ideal.ofList_append, Submodule.sup_smul, Submodule.map_sup]
    have h1 : Submodule.map S.mkQ (Ideal.ofList gs • (⊤ : Submodule R N)) = ⊥ := by
      rw [← hS]; exact Submodule.mkQ_map_self S
    have h2 : Submodule.map S.mkQ (Ideal.ofList l • (⊤ : Submodule R N))
        = Ideal.ofList l • (⊤ : Submodule R (N ⧸ (Ideal.ofList gs • (⊤ : Submodule R N)))) := by
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
    rw [h1, h2, bot_sup_eq]
  have ee := Submodule.quotientQuotientEquivQuotient S T hST
  rw [hmap] at ee
  exact Module.supportDim_eq_of_equiv ee

open scoped Pointwise in
/-- **Inner extension lemma (system of parameters for a CM module).**
A CM module `N` of support dimension `k` admits a list `es` of length `k`, with entries in
`m`, cutting the support dimension all the way down to `0`. -/
theorem cm_exists_dimDrop_list
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (k : ℕ) :
    ∀ {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N] [Nontrivial N],
      IsCohenMacaulay R N → Module.supportDim R N = (k : WithBot ℕ∞) →
      ∃ es : List R, es.length = k ∧ (∀ g ∈ es, g ∈ maximalIdeal R) ∧
        Module.supportDim R (N ⧸ (Ideal.ofList es • (⊤ : Submodule R N))) = (0 : WithBot ℕ∞) := by
  induction k with
  | zero =>
    intro N _ _ _ _ hCM hdim
    refine ⟨[], rfl, by simp, ?_⟩
    obtain ⟨heq⟩ := quotOfList_nil_nonempty_linearEquiv (R := R) (N := N)
    rw [Module.supportDim_eq_of_equiv heq, hdim]; simp
  | succ k ih =>
    intro N _ _ _ _ hCM hdim
    have hpos : 1 ≤ k + 1 := by omega
    have he : Module.supportDim R N = ((k + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hdim
    obtain ⟨g, hgm, hgreg, hgdrop⟩ :=
      exists_mem_maximalIdeal_dimDrop hCM (k + 1) he hpos
    have hgdrop' : Module.supportDim R (QuotSMulTop g N) = (k : WithBot ℕ∞) := by
      rw [hgdrop]; norm_num
    have : Nontrivial (QuotSMulTop g N) :=
      nontrivial_quotSMulTop_of_mem_maximalIdeal N hgm
    have hCMQ : IsCohenMacaulay R (QuotSMulTop g N) :=
      cohenMacaulay_quotSMulTop_of_dimDrop hCM (k + 1) he hpos g hgm hgdrop
    obtain ⟨es', hlen', hmem', hdrop'⟩ := ih hCMQ hgdrop'
    refine ⟨g :: es', by simp [hlen'], ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with h | h
      · exact h ▸ hgm
      · exact hmem' x h
    · rw [← quotOfList_cons_supportDim_eq g es']
      exact hdrop'

/-- **Part (2) — extension to a maximal regular sequence.**
Under the hypotheses of 00N6, `gs` extends to a maximal `M`-regular sequence of
length `d`.

The argument.
By part (1) (`cohenMacaulay_dimDrop_isRegular`) `gs` is `M`-regular, and the inductive
argument also shows `N_c = M/(gs)M` is Cohen–Macaulay of support dimension `d - c`.
We now extend, choosing `g_{c+1},…,g_d ∈ m` one at a time, maintaining the invariant
"`N_j = M/(g_1,…,g_j)M` is CM of support dimension `d - j`":
• If `d - j > 0` then `Supp(N_j)` has dimension `> 0`, so none of its (finitely many,
  by Noetherianness — `minimalPrimes.finite_of_isNoetherianRing`) minimal primes equals
  `m` (a minimal prime equal to `m` would force support dimension `0`). By prime
  avoidance (Stacks 00DS, `Ideal.subset_union_prime`) pick `g_{j+1} ∈ m` lying in **none**
  of those minimal primes; then `Supp(N_j) ∩ V(g_{j+1})` drops dimension by exactly one,
  i.e. `dim Supp(N_{j+1}) = (d - j) - 1`. Apply `stacks00N5_step` to get `g_{j+1}` a
  nonzerodivisor on `N_j` and `N_{j+1}` CM of dim `d - (j+1)`.
Iterating from `j = c` to `j = d` produces `gs' = [g_{c+1},…,g_d] ⊆ m` with
`(gs ++ gs').length = d` and `gs ++ gs'` an `M`-regular sequence (the appended
nonzerodivisor conditions extend `IsWeaklyRegular`; `top_ne_smul` holds since `N_d` has
support dimension `0 ≠ ⊥`, so is nonzero).
Finally, Cohen–Macaulayness of `M` gives `depth M = dim Supp M = d` (and this is finite),
so by `maximal_of_length_eq_depth` the length-`d` regular sequence `gs ++ gs'` is maximal.
-/
@[ega "0 16.5.5" "Implication b) ⇒ a)"]
theorem cohenMacaulay_dimDrop_extends
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (d c : ℕ) (hcd : c ≤ d) (hd : Module.supportDim R M = (d : WithBot ℕ∞))
    (hCM : IsCohenMacaulay R M)
    (gs : List R) (hgs_len : gs.length = c)
    (hgs_mem : ∀ g ∈ gs, g ∈ maximalIdeal R)
    (hdim : Module.supportDim R (M ⧸ (Ideal.ofList gs • (⊤ : Submodule R M)))
      = ((d - c : ℕ) : WithBot ℕ∞)) :
    ∃ gs' : List R, (∀ g ∈ gs', g ∈ maximalIdeal R) ∧
      (gs ++ gs').length = d ∧
      IsMaximalRegularSequence R M (gs ++ gs') := by
  -- `N_c = M ⧸ (gs)M` is CM of support dimension `d - c` (from part (1)'s engine context).
  -- First: `M`-regularity of `gs` shows `N_c` is nonzero; we get CM via the propagation.
  -- We extend `N_c` to drop dim to 0 using `cm_exists_dimDrop_list`.
  -- Build `N_c` as the quotient module.
  set Nc : Type _ := M ⧸ (Ideal.ofList gs • (⊤ : Submodule R M)) with hNc
  -- `N_c` is nonzero (support dimension `d - c ≥ 0 ≠ ⊥`).
  have hNcnt : Nontrivial Nc := nontrivial_of_supportDim_eq_natCast hdim
  -- `N_c` is CM (Cohen–Macaulayness propagates down the dim-drop tower).
  have hNcCM : IsCohenMacaulay R Nc :=
    (cohenMacaulay_quotOfList_of_dimDrop d hd hCM gs (hgs_len ▸ hcd) hgs_mem
      (by rw [hgs_len]; exact hdim)).right
  -- Apply the inner extension lemma to `N_c` (supportDim `d - c`).
  obtain ⟨es, hlen_es, hmem_es, hdrop_es⟩ :=
    cm_exists_dimDrop_list (d - c) hNcCM hdim
  refine ⟨es, hmem_es, ?_, ?_⟩
  · -- length: c + (d - c) = d
    rw [List.length_append, hgs_len, hlen_es]; omega
  · -- maximality of `gs ++ es`
    -- supportDim of the assembled quotient is 0 = d - d.
    have hassembled : Module.supportDim R (M ⧸ (Ideal.ofList (gs ++ es) • (⊤ : Submodule R M)))
        = ((d - d : ℕ) : WithBot ℕ∞) := by
      rw [← quotOfList_append_supportDim_eq gs es]
      simp only [Nat.sub_self, Nat.cast_zero]
      exact hdrop_es
    -- regularity via the engine (e = d, list gs ++ es of length d).
    have hlen_total : (gs ++ es).length = d := by
      rw [List.length_append, hgs_len, hlen_es]; omega
    have hmem_total : ∀ g ∈ gs ++ es, g ∈ maximalIdeal R :=
      List.forall_mem_append.mpr ⟨hgs_mem, hmem_es⟩
    have hreg : IsRegular M (gs ++ es) :=
      isRegular_of_cm_dimDrop_engine d hd hCM (gs ++ es) (by rw [hlen_total]) hmem_total
        (by rw [hlen_total]; exact hassembled)
    -- depth M = d (CM) and finite.
    have hdepthM : Module.depthSup R (maximalIdeal R) M = (d : ℕ∞) := by
      have : (Module.depthSup R (maximalIdeal R) M : WithBot ℕ∞) = (d : WithBot ℕ∞) := by
        rw [← hCM]; exact hd
      exact_mod_cast this
    refine maximal_of_length_eq_depth (gs ++ es) hmem_total hreg ?_ ?_
    · rw [hlen_total, hdepthM]
    · rw [hdepthM]; exact ENat.natCast_ne_top d

-- Main Statement(s)

/-- **Stacks Tag 00N6 (Proposition 10.103.4).**
Let `R` be a Noetherian local ring with maximal ideal `m`, and let `M` be a finite,
nonzero, Cohen-Macaulay `R`-module with `dim(Supp(M)) = d`. If `g_1, ..., g_c ∈ m`
(here `gs`, with `gs.length = c` and `c ≤ d`) satisfy
`dim(Supp(M/(g_1,...,g_c)M)) = d - c`, then:
1. `gs` is an `M`-regular sequence, and
2. `gs` extends to a maximal `M`-regular sequence of length `d` (`= depth M`): there is
   a list `gs'` of elements of `m` with `(gs ++ gs').length = d` such that `gs ++ gs'`
   is a maximal `M`-regular sequence.

The hypothesis `dim(Supp(M)) = d` with `d : ℕ` already forces `M ≠ 0` (since
`dim(Supp(0)) = ⊥`); this is recorded by `[Nontrivial M]`. The hypothesis `hcd : c ≤ d`
ensures the truncated subtraction `(d - c : ℕ)` agrees with the intended integer `d - c`,
which is forced to be nonnegative by the mathematical hypothesis on dimensions. -/
@[stacks 00N6,
  ega "0 16.5.6" "b) ⇒ a)",
  ega "0 16.5.5" "b) ⇒ a)",
  ega "0 16.5.7" "CM: sop ⇒ max reg seq", sga "2 III 2.6" "CM local, dim condition"]
theorem cohenMacaulay_regularSequence_extend
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (d c : ℕ) (hcd : c ≤ d) (hd : Module.supportDim R M = (d : WithBot ℕ∞))
    (hCM : IsCohenMacaulay R M)
    (gs : List R) (hgs_len : gs.length = c)
    (hgs_mem : ∀ g ∈ gs, g ∈ maximalIdeal R)
    (hdim : Module.supportDim R (M ⧸ (Ideal.ofList gs • (⊤ : Submodule R M)))
      = ((d - c : ℕ) : WithBot ℕ∞)) :
    IsRegular M gs ∧
    ∃ gs' : List R, (∀ g ∈ gs', g ∈ maximalIdeal R) ∧
      (gs ++ gs').length = d ∧
      IsMaximalRegularSequence R M (gs ++ gs') := by
  -- Assemble the two parts. Conjunct (1) is `cohenMacaulay_dimDrop_isRegular`;
  -- conjunct (2) is `cohenMacaulay_dimDrop_extends`. Both take exactly these hypotheses.
  refine ⟨cohenMacaulay_dimDrop_isRegular d c hcd hd hCM gs hgs_len hgs_mem hdim,
    cohenMacaulay_dimDrop_extends d c hcd hd hCM gs hgs_len hgs_mem hdim⟩

end

/-!
# Cohen-Macaulay modules

This file develops Stacks project section 10.103 (`00N2`), *Cohen-Macaulay modules*.

Throughout the local part, `R` is a Noetherian local ring with maximal ideal `m` and `M` is a
finite (i.e. finitely generated) `R`-module. We write `Supp M` for `Module.support R M`,
`dim (Supp M)` for `Module.supportDim R M = krullDim (Supp M)`, and `depth M` for
`Module.depthSup R m M`.

## Definitions

The defining notion of the section, Stacks `00N3` (`M` is Cohen-Macaulay if
`dim (Supp M) = depth M`), is `IsCohenMacaulayModule`, from
`StacksFrontier.RingTheory.CohenMacaulay.Defs` (with `Module.depthSup` from
`StacksFrontier.RingTheory.Depth.Defs.Defs`).

* `IsMaximalCohenMacaulayModule` : Stacks `00NF`, `depth M = dim R`.
* `IsLocallyCohenMacaulayModule` : Stacks `0AAH`, the notion for a Noetherian ring that need not
  be local: `M_p` is a Cohen-Macaulay `R_p`-module for every prime `p` in `Supp M`. The source
  says "for all primes"; see the declaration's docstring for why that wording is an erratum.

## Main results

* `isCohenMacaulayModule_iff_supportDim_eq_depth` and `IsCohenMacaulayModule.supportDim_eq_depth`
  : the `dim (Supp M) = depth M` orientation of the definition, together with
  `IsCohenMacaulayModule.nontrivial` and the bridge `IsCohenMacaulayModule.isCohenMacaulay` to
  the local-ring spelling `IsCohenMacaulay` of Stacks Tag 00N6, which carries `[Nontrivial M]`
  as an instance hypothesis.
* `depthSup_le_supportDim` : `depthSup M ≤ dim (Supp M)` for a Noetherian local ring, the
  `Module.depthSup` reading of Stacks `00LK`. The `Module.depth` reading, in full generality,
  is `Module.depth_le_supportDim` in `StacksFrontier.RingTheory.Depth.Dimension`.
* `isSMulRegular_and_isCohenMacaulayModule_quotSMulTop_of_supportDim_drop` : Stacks `00N5`.
* `isCohenMacaulayModule_iff_isCohenMacaulayModule_quotSMulTop` : Stacks `0C6G`.
* `coheight_eq_supportDim_of_mem_associatedPrimes_of_isCohenMacaulayModule` : Stacks `0BUS`.

## Implementation notes

* `dim (Supp M ∩ V(g))` of the Stacks text is rendered as `Module.supportDim R (QuotSMulTop g M)`.
  These agree because `Supp (M/gM) = Supp M ∩ V(g)` for finite `M` (`Module.support_quotSMulTop`),
  and the quotient form is the one all the ambient draft lemmas are stated in.
* `dim (R/p)` of the Stacks text is rendered as `Order.coheight p` in `PrimeSpectrum R`.
* Support dimensions live in `WithBot ℕ∞` and depths in `ℕ∞`. Because every finite module over
  a Noetherian local ring has finite support dimension and depth, the arguments below extract
  natural numbers (via `exists_supportDim_eq_natCast` and `depth_ne_top`) before doing arithmetic,
  which avoids reasoning about `⊥` and `⊤`.

## References

Stacks project, tags `00N3`, `00N5`, `0C6G`, `0BUS`, `00NF`, `0AAH`.
-/

@[expose] public section

open IsLocalRing RingTheory.Sequence

add_to_stacks 00N3 "the definition of a Cohen-Macaulay module" IsCohenMacaulayModule

/-- The annihilator of a module is contained in each of its associated primes. -/
private theorem annihilator_le_of_mem_associatedPrimes {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M] {p : Ideal R} (hp : p ∈ associatedPrimes R M) :
    Module.annihilator R M ≤ p := by
  rw [← Submodule.annihilator_top]
  exact IsAssociatedPrime.annihilator_le hp

section Local

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
  {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- The two orientations of Stacks `00N3`. `IsCohenMacaulayModule`
(`StacksFrontier.RingTheory.CohenMacaulay.Defs`) is stated as `depth M = dim (Supp M)`;
the reverse reading `dim (Supp M) = depth M` is the one the draft lemmas of Stacks
section 10.103 are phrased in, and is also the body of `IsCohenMacaulay` (earlier in
this file). -/
theorem isCohenMacaulayModule_iff_supportDim_eq_depth :
    IsCohenMacaulayModule R M ↔
      Module.supportDim R M = (Module.depthSup R (maximalIdeal R) M : WithBot ℕ∞) := by
  unfold IsCohenMacaulayModule
  rw [Module.supportDim]
  exact eq_comm

/-- The `dim (Supp M) = depth M` reading of Cohen-Macaulayness. -/
theorem IsCohenMacaulayModule.supportDim_eq_depth (h : IsCohenMacaulayModule R M) :
    Module.supportDim R M = (Module.depthSup R (maximalIdeal R) M : WithBot ℕ∞) :=
  isCohenMacaulayModule_iff_supportDim_eq_depth.mp h

/-- A Cohen-Macaulay module is nonzero. The support of the zero module is empty, so
`dim (Supp M) = ⊥`, while `depth M` is a genuine element of `ℕ∞` whose image in `WithBot ℕ∞` is
never `⊥`. -/
theorem IsCohenMacaulayModule.nontrivial (h : IsCohenMacaulayModule R M) : Nontrivial M := by
  refine (Module.supportDim_ne_bot_iff_nontrivial R M).mp ?_
  rw [h.supportDim_eq_depth]
  exact WithBot.coe_ne_bot

/-- `IsCohenMacaulay` (earlier in this file) is the same condition, stated with
`[Nontrivial M]` as an instance hypothesis and the equation the other way round. This is what
lets the section 10.103 lemmas be applied to an `IsCohenMacaulayModule` hypothesis. -/
theorem IsCohenMacaulayModule.isCohenMacaulay [Nontrivial M] (h : IsCohenMacaulayModule R M) :
    IsCohenMacaulay R M := h.supportDim_eq_depth

/-- The converse of `IsCohenMacaulayModule.isCohenMacaulay`. -/
theorem IsCohenMacaulay.isCohenMacaulayModule [Nontrivial M] (h : IsCohenMacaulay R M) :
    IsCohenMacaulayModule R M :=
  isCohenMacaulayModule_iff_supportDim_eq_depth.mpr h

/-- The zero module is not Cohen-Macaulay: this is `IsCohenMacaulayModule.nontrivial` read
contrapositively. -/
private theorem not_isCohenMacaulayModule_of_subsingleton [Subsingleton M] :
    ¬ IsCohenMacaulayModule R M := fun h =>
  not_subsingleton_iff_nontrivial.mpr h.nontrivial inferInstance

/-- A finite nonzero module over a Noetherian local ring has support dimension a natural number:
it is not `⊥` because the module is nonzero, and not `⊤` because it is bounded by
`ringKrullDim R`, which is finite. -/
theorem exists_supportDim_eq_natCast (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M] :
    ∃ e : ℕ, Module.supportDim R M = ((e : ℕ∞) : WithBot ℕ∞) := by
  have hbot : Module.supportDim R M ≠ ⊥ := Module.supportDim_ne_bot_of_nontrivial R M
  have htop : Module.supportDim R M ≠ ⊤ := by
    intro h
    exact ringKrullDim_ne_top (R := R)
      (top_le_iff.mp (h ▸ Module.supportDim_le_ringKrullDim R M))
  obtain ⟨x, hx⟩ := WithBot.ne_bot_iff_exists.mp hbot
  rw [← hx] at htop ⊢
  have hxtop : x ≠ ⊤ := by intro h; exact htop (by rw [h]; rfl)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hxtop
  exact ⟨n, by rw [← hn]⟩

/-- **Stacks 00LK.** The depth of a finite nonzero module over a Noetherian local ring is at most
the dimension of its support. Indeed `M` has an associated prime `p`, and
`depth M ≤ dim (R/p) = dim V(p) ≤ dim (Supp M)` because `V(p) ⊆ Supp M`. -/
theorem depth_le_supportDim [Nontrivial M] :
    (Module.depthSup R (maximalIdeal R) M : WithBot ℕ∞) ≤ Module.supportDim R M := by
  obtain ⟨p, hp⟩ := associatedPrimes.nonempty R M
  refine le_trans (depth_le_krullDim_zeroLocus_of_mem_associatedPrimes p hp) ?_
  have hsub : PrimeSpectrum.zeroLocus (p : Set R) ⊆ Module.support R M := by
    intro q hq
    rw [PrimeSpectrum.mem_zeroLocus] at hq
    rw [Module.mem_support_iff_of_finite]
    exact (annihilator_le_of_mem_associatedPrimes hp).trans hq
  exact Order.krullDim_le_of_strictMono (Set.inclusion hsub) (Subtype.strictMono_coe _)

/-- **Stacks 00LK.** The depth of a finite nonzero module over a Noetherian local ring is at most
the dimension of its support. Indeed `M` has an associated prime `p`, and
`depth M ≤ dim (R/p) = dim V(p) ≤ dim (Supp M)` because `V(p) ⊆ Supp M`. -/
alias depthSup_le_supportDim := depth_le_supportDim

/-- **Stacks 00N5.** Let `M` be a Cohen-Macaulay module over a Noetherian local ring `R`, of
support dimension `e ≥ 1`, and let `g ∈ m` be such that
`dim (Supp M ∩ V(g)) = dim (Supp M) - 1`, i.e. `dim (Supp (M/gM)) = e - 1`. Then

* (a) `g` is a nonzerodivisor on `M`, and
* (b) `M/gM` is Cohen-Macaulay, of depth one less than the depth of `M`.

The hypothesis `1 ≤ e` is the Stacks hypothesis that the dimension actually drops: `e - 1` is
truncated subtraction in `ℕ`, and for `e = 0` the displayed condition of the source has no
solutions. -/
@[stacks 00N5, ega "0 16.5.5" "b) ⇒ a), last part"]
theorem isSMulRegular_and_isCohenMacaulayModule_quotSMulTop_of_supportDim_drop
    (hCM : IsCohenMacaulayModule R M)
    (e : ℕ) (he : Module.supportDim R M = ((e : ℕ∞) : WithBot ℕ∞)) (hpos : 1 ≤ e)
    {g : R} (hg : g ∈ maximalIdeal R)
    (hdrop : Module.supportDim R (QuotSMulTop g M) = (((e - 1 : ℕ) : ℕ∞) : WithBot ℕ∞)) :
    IsSMulRegular M g ∧ IsCohenMacaulayModule R (QuotSMulTop g M) ∧
      Module.depthSup R (maximalIdeal R) (QuotSMulTop g M) + 1
        = Module.depthSup R (maximalIdeal R) M := by
  -- `M ≠ 0` because it is Cohen-Macaulay.
  have : Nontrivial M := hCM.nontrivial
  -- The quotient is nonzero because its support dimension is a natural number, not `⊥`.
  have hQ : Nontrivial (QuotSMulTop g M) :=
    (Module.supportDim_ne_bot_iff_nontrivial R _).mp (by rw [hdrop]; exact WithBot.coe_ne_bot)
  -- (a) Regularity: this is the kernel of the Stacks induction, `stacks00N5_step`, applied
  -- after translating `QuotSMulTop g M` into the `Ideal.span {g} • ⊤` form.
  have hdrop' : Module.supportDim R (M ⧸ (Ideal.span {g} • (⊤ : Submodule R M)))
      = (((e - 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    rw [Submodule.ideal_span_singleton_smul]; exact hdrop
  obtain ⟨hreg, -⟩ := stacks00N5_step hCM.isCohenMacaulay e he hpos g hdrop'
  refine ⟨hreg, ?_, ?_⟩
  · -- (b) Cohen-Macaulayness of the quotient: `cohenMacaulay_quotSMulTop_of_dimDrop`.
    exact (cohenMacaulay_quotSMulTop_of_dimDrop hCM.isCohenMacaulay e he hpos g hg
      hdrop).isCohenMacaulayModule
  · -- The depth drops by exactly one along a nonzerodivisor (Stacks 090R).
    exact depth_quotient_succ_of_isSMulRegular g hg hreg

/-- **Stacks 0C6G.** Let `R` be a Noetherian local ring, `M` a finite `R`-module and `x ∈ m` a
nonzerodivisor on `M`. Then `M` is Cohen-Macaulay if and only if `M/xM` is.

Both the depth and the dimension of the support drop by exactly one along `x`: the first by
Stacks `090R` (`depth_quotient_succ_of_isSMulRegular`) and the second by Stacks `0B52`
(`Module.supportDim_quotSMulTop_succ_eq_supportDim`). -/
@[stacks 0C6G]
theorem isCohenMacaulayModule_iff_isCohenMacaulayModule_quotSMulTop
    {x : R} (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular M x) :
    IsCohenMacaulayModule R M ↔ IsCohenMacaulayModule R (QuotSMulTop x M) := by
  rcases subsingleton_or_nontrivial M with hM | hM
  · -- Both sides are false: the zero module is not Cohen-Macaulay, and neither is its quotient.
    have : Subsingleton (QuotSMulTop x M) :=
      Function.Surjective.subsingleton (Submodule.mkQ_surjective _)
    exact iff_of_false not_isCohenMacaulayModule_of_subsingleton
      not_isCohenMacaulayModule_of_subsingleton
  have hQ : Nontrivial (QuotSMulTop x M) := nontrivial_quotSMulTop_of_mem_maximalIdeal M hx
  have hdepth : Module.depthSup R (maximalIdeal R) (QuotSMulTop x M) + 1
      = Module.depthSup R (maximalIdeal R) M := depth_quotient_succ_of_isSMulRegular x hx hreg
  have hdim : Module.supportDim R (QuotSMulTop x M) + 1 = Module.supportDim R M :=
    Module.supportDim_quotSMulTop_succ_eq_supportDim hreg hx
  -- Replace both invariants of the quotient by natural numbers, then cancel the `+ 1`.
  obtain ⟨e, he⟩ := exists_supportDim_eq_natCast R (QuotSMulTop x M)
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp
    (depth_ne_top (R := R) (M := QuotSMulTop x M))
  rw [isCohenMacaulayModule_iff_supportDim_eq_depth,
    isCohenMacaulayModule_iff_supportDim_eq_depth, ← hdim, ← hdepth, he, ← hd]
  norm_cast
  omega

/-- **Stacks 0BUS** (EGA Ch. 0, Proposition 16.5.4). Let `M` be a finite Cohen-Macaulay module
over a Noetherian local ring `R` and let `p ∈ Ass(M)`. Then `dim (R/p) = dim (Supp M)`, and `p`
is a minimal prime of the support of `M`. In particular `M` has no embedded associated primes.

Here `dim (R/p)` is `Order.coheight p` in `PrimeSpectrum R`, and minimality of `p` in the support
is spelled out as: no prime of `Supp M` is strictly below `p`.

The dimension equality holds because `dim (Supp M) = depth M ≤ dim (R/p)` (Stacks `0AUJ`, the
Cohen-Macaulay form of which is `supportDim_le_coheight_of_isCohenMacaulayModule`) while
`dim (R/p) ≤ dim (Supp M)`
since `Supp M` is closed under specialization and contains `p`. Minimality then follows: a prime
`q ∈ Supp M` with `q < p` would give `dim (R/p) + 1 ≤ dim (R/q) ≤ dim (Supp M) = dim (R/p)`.
-/
@[stacks 0BUS, ega "0 16.5.4", ega "IV 7.2.1.1" "more general"]
theorem coheight_eq_supportDim_of_mem_associatedPrimes_of_isCohenMacaulayModule
    (hCM : IsCohenMacaulayModule R M) {p : Ideal R} (hp : p ∈ associatedPrimes R M) :
    (Order.coheight (⟨p, hp.1⟩ : PrimeSpectrum R) : WithBot ℕ∞) = Module.supportDim R M ∧
      ∀ q ∈ Module.support R M, q ≤ (⟨p, hp.1⟩ : PrimeSpectrum R) →
        q = (⟨p, hp.1⟩ : PrimeSpectrum R) := by
  set P : PrimeSpectrum R := ⟨p, hp.1⟩ with hP
  -- `Supp M` is closed under specialization, being the zero locus of the annihilator.
  have hspec : ∀ x ∈ Module.support R M, ∀ y, x ≤ y → y ∈ Module.support R M := by
    intro x hx y hxy
    rw [Module.support_eq_zeroLocus] at hx ⊢
    exact zeroLocus_specializationClosed _ x hx y hxy
  have hPsupp : P ∈ Module.support R M := by
    exact Module.mem_support_iff_of_finite.mpr (annihilator_le_of_mem_associatedPrimes hp)
  -- `dim (R/q) ≤ dim (Supp M)` for every `q` in the support.
  have hcoh : ∀ q ∈ Module.support R M,
      (Order.coheight q : WithBot ℕ∞) ≤ Module.supportDim R M := fun q hq =>
    coheight_le_krullDim_of_specializationClosed _ hspec q hq
  have heq : (Order.coheight P : WithBot ℕ∞) = Module.supportDim R M :=
    le_antisymm (hcoh P hPsupp) (supportDim_le_coheight_of_isCohenMacaulayModule hCM p hp)
  refine ⟨heq, fun q hq hqP => ?_⟩
  by_contra hne
  -- A strictly smaller prime in the support would make `dim (R/P)` exceed itself.
  have hlt : q < P := lt_of_le_of_ne hqP hne
  have hstep : Order.coheight P + 1 ≤ Order.coheight q := Order.coheight_add_one_le hlt
  have hback : Order.coheight q ≤ Order.coheight P := by
    have := (hcoh q hq).trans_eq heq.symm
    exact_mod_cast this
  have htop : Order.coheight P ≠ ⊤ := by
    intro h
    refine ringKrullDim_ne_top (R := R) (top_le_iff.mp ?_)
    calc (⊤ : WithBot ℕ∞) = (Order.coheight P : WithBot ℕ∞) := by rw [h]; rfl
      _ = Module.supportDim R M := heq
      _ ≤ ringKrullDim R := Module.supportDim_le_ringKrullDim R M
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  rw [← hn] at hstep hback
  have : (n : ℕ∞) + 1 ≤ (n : ℕ∞) := hstep.trans hback
  exact absurd this (by exact_mod_cast Nat.not_succ_le_self n)

/-- **Stacks 00NF.** A finite module `M` over a Noetherian local ring `R` is *maximal
Cohen-Macaulay* if `depth M = dim R`, i.e. if its depth is as large as it can possibly be. -/
@[stacks 00NF]
def IsMaximalCohenMacaulayModule (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] : Prop :=
  (Module.depthSup R (maximalIdeal R) M : WithBot ℕ∞) = ringKrullDim R

/-- A Cohen-Macaulay module whose support is all of `Spec R` is maximal Cohen-Macaulay, since
then `dim (Supp M) = dim R`. This is the remark following Stacks `00NF`. -/
theorem IsCohenMacaulayModule.isMaximalCohenMacaulayModule_of_support_eq_univ
    (hCM : IsCohenMacaulayModule R M) (hsupp : Module.support R M = Set.univ) :
    IsMaximalCohenMacaulayModule R M := by
  rw [IsMaximalCohenMacaulayModule, ← hCM.supportDim_eq_depth]
  refine le_antisymm (Module.supportDim_le_ringKrullDim R M) ?_
  rw [ringKrullDim, Module.supportDim]
  exact Order.krullDim_le_of_strictMono
    (fun p => (⟨p, by rw [hsupp]; exact Set.mem_univ p⟩ : Module.support R M))
    fun _ _ h => h

end Local

/-- **Stacks 0AAH.** Let `R` be a Noetherian ring, not necessarily local, and let `M` be a finite
`R`-module. Then `M` is *Cohen-Macaulay* if `M_p` is a Cohen-Macaulay `R_p`-module for every prime
`p` in the support of `M`. The name records that this is a condition imposed at the points of
`Spec R`; the Stacks project calls it simply "Cohen-Macaulay", which in this repository is already
the name of the local notion `IsCohenMacaulayModule`.

**Erratum in the source.** Stacks 0AAH literally reads "for all primes `p` of `R`". Taken
literally that wording is mathematically inconsistent, because at a prime `p ∉ Supp M` the
localization `M_p` is the zero module, and the zero module is *not* Cohen-Macaulay: with

  `IsCohenMacaulayModule R M ↔ depthSup R 𝔪 M = (krullDim (Module.support R M) : WithBot ℕ∞)`,

the right-hand side is `⊥` for the zero module (its support is empty) while the left-hand side is
a coercion from `ℕ∞` and so is never `⊥`. A literal all-primes reading would therefore be
satisfied by no module except those of full support, which is plainly not the notion 0AAH intends.

This definition quantifies over `Module.support R M` deliberately, which is the intended content
of 0AAH. The restriction is a correction of the source's wording, not a narrowing of the
formalization: the class of modules defined here is exactly the class 0AAH describes. -/
@[stacks 0AAH "Quantified over Supp M. The source's literal all-primes wording is inconsistent \
when M_p = 0, since the zero module is not Cohen-Macaulay here; this is a source erratum, and the \
definition captures 0AAH in full.", ega "0 16.5.13"]
def IsLocallyCohenMacaulayModule (R : Type*) [CommRing R] [IsNoetherianRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] : Prop :=
  ∀ p : PrimeSpectrum R, p ∈ Module.support R M →
    IsCohenMacaulayModule (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl M)

end

/-!
# Cohen-Macaulayness is insensitive to restriction of scalars along a surjection

Let `φ : R → S` be a surjective homomorphism of Noetherian local rings and let `N` be a finite
`S`-module. Then `N` is Cohen-Macaulay as an `S`-module if and only if it is Cohen-Macaulay as
an `R`-module via restriction of scalars along `φ`. This is Stacks Lemma 10.103.6, tag 0AAD,
from the section "Cohen-Macaulay modules".

All rings are commutative with `1`. A *Noetherian local ring* `(R, 𝔪)` is a Noetherian ring
with a unique maximal ideal `𝔪`. If `φ : R → S` is a ring homomorphism and `N` an `S`-module,
then `N` becomes an `R`-module by *restriction of scalars*, `a • n := φ a • n`, which in Lean
is `Module.compHom N φ`.

## Conventions

* A sequence `f₁, …, f_r ∈ R` is *`M`-regular* if each `fᵢ` is a nonzerodivisor on
  `M / (f₁, …, f_{i-1}) M` and `M / (f₁, …, f_r) M ≠ 0` (Stacks tag 00LF).
* For an ideal `I` and a finite module `M`, the `I`-*depth* `depth_I M ∈ ℕ∞` is the supremum
  of the lengths of `M`-regular sequences contained in `I`, with `depth_I M = ∞` when
  `I M = M` (tag 00LI); in Lean, `Module.depthSup R I M`. Over a local ring the depth of `M` is
  `depth_𝔪 M`.
* `Supp M = {𝔭 | M_𝔭 ≠ 0} ⊆ Spec R` is `Module.support R M`.
* For `Z ⊆ Spec R`, `dim Z` is the supremum of the lengths of chains of primes in `Z`, with
  `dim ∅ = -∞`; in Lean it is `Order.krullDim` on the subtype `↑(Module.support R M)`, valued
  in `WithBot ℕ∞`.
* A finite module `M` over a Noetherian local ring `R` is *Cohen-Macaulay* if
  `dim (Supp M) = depth M` (tag 00N3).

## Implementation notes

`Order.krullDim (Module.support R M)` lives in `WithBot ℕ∞` while `Module.depthSup R I M` lives
in `ℕ∞`, so the depth is coerced into `WithBot ℕ∞` for the comparison. Under that coercion the
zero module has support of dimension `⊥ = -∞` and depth `⊤ = ∞`, hence is not Cohen-Macaulay;
the convention is applied identically on the `R`- and `S`-sides, so the biconditional below is
unaffected by the treatment of the zero module.
-/

@[expose] public section

section RestrictScalars

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  {N : Type*} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- Restriction of scalars along a surjection `R → S` preserves the dimension of the support. -/
@[ega "0 16.1.9" "special case"]
theorem krullDim_support_eq_of_surjective_algebraMap
    (hφ : Function.Surjective (algebraMap R S)) [Module.Finite S N] :
    Order.krullDim (Module.support R N) = Order.krullDim (Module.support S N) := by
  have : Module.Finite R S := Module.Finite.of_surjective (Algebra.linearMap R S) hφ
  have : Module.Finite R N := Module.Finite.trans S N
  have hann : Module.annihilator R N = (Module.annihilator S N).comap (algebraMap R S) := by
    ext r
    simp only [Module.mem_annihilator, Ideal.mem_comap, algebraMap_smul]
  have hmem (p : PrimeSpectrum S) :
      PrimeSpectrum.comap (algebraMap R S) p ∈ Module.support R N ↔ p ∈ Module.support S N := by
    rw [Module.support_eq_zeroLocus, Module.support_eq_zeroLocus, PrimeSpectrum.mem_zeroLocus,
      PrimeSpectrum.mem_zeroLocus, PrimeSpectrum.comap_asIdeal, hann]
    exact Ideal.comap_le_comap_iff_of_surjective _ hφ _ _
  have hsurj (q : PrimeSpectrum R) (hq : q ∈ Module.support R N) :
      ∃ p, PrimeSpectrum.comap (algebraMap R S) p = q := by
    rw [Module.support_eq_zeroLocus, PrimeSpectrum.mem_zeroLocus, hann] at hq
    rw [← Set.mem_range, range_comap_of_surjective S _ hφ, PrimeSpectrum.mem_zeroLocus]
    exact (Ideal.comap_mono bot_le).trans hq
  let e : Module.support S N ≃o Module.support R N :=
    { toFun p := ⟨PrimeSpectrum.comap (algebraMap R S) p, (hmem p).2 p.2⟩
      invFun q := ⟨(hsurj q q.2).choose, (hmem _).1 <| by
        rw [(hsurj q q.2).choose_spec]
        exact q.2⟩
      left_inv p := Subtype.ext (PrimeSpectrum.comap_injective_of_surjective _ hφ
        (hsurj _ ((hmem p).2 p.2)).choose_spec)
      right_inv q := Subtype.ext (hsurj q q.2).choose_spec
      map_rel_iff' {a b} := Ideal.comap_le_comap_iff_of_surjective _ hφ a.1.asIdeal b.1.asIdeal }
  exact (Order.krullDim_eq_of_orderIso e).symm

/-- Along a surjection `R → S`, the submodule `(l) N` agrees with `(φ l) N`. -/
theorem ideal_ofList_smul_top_eq_restrictScalars (hφ : Function.Surjective (algebraMap R S))
    (l : List R) :
    Ideal.ofList l • (⊤ : Submodule R N) =
      (Ideal.ofList (l.map (algebraMap R S)) • (⊤ : Submodule S N)).restrictScalars R := by
  have hmap : (Ideal.ofList l).map (algebraMap R S) = Ideal.ofList (l.map (algebraMap R S)) := by
    rw [Ideal.ofList, Ideal.map_span]
    congr 1
    ext x
    simp
  apply le_antisymm
  · rw [Submodule.smul_le]
    intro r hr n _
    rw [Submodule.restrictScalars_mem, ← algebraMap_smul S r n]
    exact Submodule.smul_mem_smul (hmap ▸ Ideal.mem_map_of_mem _ hr) Submodule.mem_top
  · intro x hx
    rw [Submodule.restrictScalars_mem] at hx
    refine Submodule.smul_induction_on hx (fun s hs n _ => ?_) fun _ _ => Submodule.add_mem _
    obtain ⟨r, hr, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ hφ).mp (hmap ▸ hs)
    rw [algebraMap_smul]
    exact Submodule.smul_mem_smul hr Submodule.mem_top

/-- Along a surjection `R → S`, `r` is regular on `N / (l) N` iff `φ r` is regular on
`N / (φ l) N`. -/
theorem isSMulRegular_quotient_ofList_smul_top_iff (hφ : Function.Surjective (algebraMap R S))
    (l : List R) (r : R) :
    IsSMulRegular (N ⧸ Ideal.ofList l • (⊤ : Submodule R N)) r ↔
      IsSMulRegular (N ⧸ Ideal.ofList (l.map (algebraMap R S)) • (⊤ : Submodule S N))
        (algebraMap R S r) := by
  let e := (Submodule.quotEquivOfEq _ _ (ideal_ofList_smul_top_eq_restrictScalars hφ l)).trans
    (Submodule.Quotient.restrictScalarsEquiv R
      (Ideal.ofList (l.map (algebraMap R S)) • (⊤ : Submodule S N)))
  rw [e.isSMulRegular_congr r]
  simp only [IsSMulRegular, algebraMap_smul]

/-- Along a surjection `R → S`, a sequence is `N`-regular iff its image in `S` is. -/
theorem isRegular_iff_map_algebraMap (hφ : Function.Surjective (algebraMap R S)) (rs : List R) :
    RingTheory.Sequence.IsRegular N rs ↔
      RingTheory.Sequence.IsRegular N (rs.map (algebraMap R S)) := by
  rw [RingTheory.Sequence.isRegular_iff, RingTheory.Sequence.isRegular_iff,
    RingTheory.Sequence.isWeaklyRegular_iff, RingTheory.Sequence.isWeaklyRegular_iff,
    ne_comm, ne_comm (a := (⊤ : Submodule S N)), ne_eq, ne_eq,
    ideal_ofList_smul_top_eq_restrictScalars hφ rs, Submodule.restrictScalars_eq_top_iff R S N]
  refine and_congr ⟨fun hw i hi => ?_, fun hw i hi => ?_⟩ Iff.rfl
  · rw [List.getElem_map, ← List.map_take]
    exact (isSMulRegular_quotient_ofList_smul_top_iff hφ _ _).1 (hw i (by simpa using hi))
  · have := hw i (by simpa using hi)
    rw [List.getElem_map, ← List.map_take] at this
    exact (isSMulRegular_quotient_ofList_smul_top_iff hφ _ _).2 this

/-- Restriction of scalars along a surjection of local rings preserves the depth. -/
theorem depthSup_maximalIdeal_eq_of_surjective_algebraMap [IsLocalRing R] [IsLocalRing S]
    (hφ : Function.Surjective (algebraMap R S)) :
    Module.depthSup R (IsLocalRing.maximalIdeal R) N =
      Module.depthSup S (IsLocalRing.maximalIdeal S) N := by
  have := Function.Surjective.isLocalHom (algebraMap R S) hφ
  have hmem (r : R) :
      r ∈ IsLocalRing.maximalIdeal R ↔ algebraMap R S r ∈ IsLocalRing.maximalIdeal S :=
    (map_mem_nonunits_iff _ r).symm
  unfold Module.depthSup
  congr 1
  ext n
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨rs, hlen, hrs, hreg⟩
    refine ⟨rs.map (algebraMap R S), by rwa [List.length_map], fun s hs => ?_,
      (isRegular_iff_map_algebraMap hφ rs).1 hreg⟩
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hs
    exact (hmem r).1 (hrs r hr)
  · rintro ⟨ss, hlen, hss, hreg⟩
    refine ⟨ss.map (Function.surjInv hφ), by rwa [List.length_map], fun r hr => ?_, ?_⟩
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hr
      rw [hmem, Function.surjInv_eq hφ s]
      exact hss s hs
    · rwa [isRegular_iff_map_algebraMap hφ, List.map_map,
        (Function.rightInverse_surjInv hφ).comp_eq_id, List.map_id]

end RestrictScalars

/-- **Stacks 10.103.6 (tag 0AAD).**
Let `φ : R →+* S` be a surjective homomorphism of Noetherian local rings, and let `N`
be a finite `S`-module.  Then `N` is Cohen-Macaulay as an `S`-module if and only if `N`
is Cohen-Macaulay as an `R`-module, where the `R`-module structure on `N` is obtained by
restriction of scalars along `φ` (`Module.compHom N φ`).

Here Noetherianity of `R` is encoded by `IsNoetherianRing R` (and `S` is then automatically
Noetherian as a quotient, but we also assume it for convenience). -/
@[stacks 0AAD, ega "0 16.5.3" "surjective ρ", ega "IV 5.7.10" "special case"]
theorem isCohenMacaulay_iff_of_surjective
    (R S : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (φ : R →+* S) (hφ : Function.Surjective φ)
    (N : Type*) [AddCommGroup N] [Module S N] [Module.Finite S N] :
    IsCohenMacaulayPropForm S N ↔
      (letI : Module R N := Module.compHom N φ; IsCohenMacaulayPropForm R N) := by
  let := φ.toAlgebra
  let : Module R N := Module.compHom N φ
  have : IsScalarTower R S N := ⟨fun r s n => mul_smul (φ r) s n⟩
  unfold IsCohenMacaulayPropForm
  rw [krullDim_support_eq_of_surjective_algebraMap hφ,
    depthSup_maximalIdeal_eq_of_surjective_algebraMap hφ]

/-- **Stacks 10.103.6 (tag 0AAD).**
Let `φ : R →+* S` be a surjective homomorphism of Noetherian local rings, and let `N`
be a finite `S`-module.  Then `N` is Cohen-Macaulay as an `S`-module if and only if `N`
is Cohen-Macaulay as an `R`-module, where the `R`-module structure on `N` is obtained by
restriction of scalars along `φ` (`Module.compHom N φ`).

Here Noetherianity of `R` is encoded by `IsNoetherianRing R` (and `S` is then automatically
Noetherian as a quotient, but we also assume it for convenience). -/
@[stacks 0AAD, ega "0 16.5.3" "surjective ρ"]
theorem isCohenMacaulay_iff_of_surjective'
    (R S : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (φ : R →+* S) (hφ : Function.Surjective φ)
    (N : Type*) [AddCommGroup N] [Module S N] [Module.Finite S N] :
    IsCohenMacaulayModule S N ↔
      (letI : Algebra R S := φ.toAlgebra
       letI : Module R N := Module.compHom N φ
       haveI : IsScalarTower R S N := ⟨fun r s n => mul_smul (φ r) s n⟩
       haveI : Module.Finite R S := Module.Finite.of_surjective (Algebra.linearMap R S) hφ
       haveI : Module.Finite R N := Module.Finite.trans S N
       IsCohenMacaulayModule R N) := by
  let : Algebra R S := φ.toAlgebra
  let : Module R N := Module.compHom N φ
  have : IsScalarTower R S N := ⟨fun r s n => mul_smul (φ r) s n⟩
  have : Module.Finite R S := Module.Finite.of_surjective (Algebra.linearMap R S) hφ
  have : Module.Finite R N := Module.Finite.trans S N
  unfold IsCohenMacaulayModule
  rw [krullDim_support_eq_of_surjective_algebraMap hφ,
    depthSup_maximalIdeal_eq_of_surjective_algebraMap hφ]

/-- A field is a maximal Cohen-Macaulay module over itself: its maximal ideal is `⊥`, so both
the depth and the Krull dimension are `0`. -/
theorem isMaximalCohenMacaulay_self_of_isField (A : Type*) [CommRing A] [IsLocalRing A]
    (h : IsField A) : Module.IsMaximalCohenMacaulay A A := by
  rw [Module.IsMaximalCohenMacaulay, IsLocalRing.isField_iff_maximalIdeal_eq.mp h,
    Module.depth_bot_eq_zero A, ringKrullDim_eq_zero_of_isField h]
  rfl

end
