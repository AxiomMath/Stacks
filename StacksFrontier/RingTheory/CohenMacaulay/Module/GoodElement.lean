module

public import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
public import StacksFrontier.RingTheory.CohenMacaulay.Module.DepthCoheight
public import StacksFrontier.RingTheory.RegularLocalRing.Criteria
public import StacksFrontier.RingTheory.Serre.Reduced
import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quotients of Cohen-Macaulay modules by good elements

We keep the notation of `StacksFrontier.RingTheory.CohenMacaulay.Module.DepthCoheight`, where the
setup and the notion of a good element (Stacks 00N2) are defined.

## Main result

With the setup above, assume `d ≥ 1` and that `g` is good. Then `g` is a nonzerodivisor on `M`,
and `M / gM` is Cohen-Macaulay with the images of `f₁, …, f_{d-1}` forming a maximal
`(M / gM)`-regular sequence; concretely they form an `(M / gM)`-regular sequence and
`dim (Supp (M / gM)) = depth (M / gM) = d - 1`. This is Stacks Lemma 10.103.2, tag 00N4.

## Implementation notes

* The hypothesis `d ≥ 1` is essential: when `d = 0` the goodness condition is vacuous, so every
  `g` would be good, while the conclusion would falsely assert that an arbitrary `g ∈ m` is a
  nonzerodivisor on a nonzero dimension-zero Cohen-Macaulay module. It is therefore an explicit
  hypothesis.
* Part (b) bundles two claims: `M / gM` is Cohen-Macaulay, and `f₁, …, f_{d-1}` is a maximal
  `(M / gM)`-regular sequence. Since `M / gM` is Cohen-Macaulay, a regular sequence is maximal
  exactly when its length equals `depth (M / gM) = dim (Supp (M / gM))`, here `d - 1`; this is
  captured by additionally requiring `Module.supportDim R (M / gM) = d - 1` alongside
  Cohen-Macaulayness.
* Permutation invariance of regular sequences (Stacks 00LJ) is
  `IsLocalRing.isRegular_of_perm`.

## Also in this file

* `IsCohenMacaulay` and `IsMaximalRegularSequence` : the local-ring spelling of Stacks 00N3 used
  by Stacks 00N6, carrying `[Nontrivial M]` as an instance hypothesis, and maximal regular
  sequences in `m`.
* `depth_le_krullDim_zeroLocus_of_mem_associatedPrimes` : the depth-coheight bound Stacks 00LK,
  `depth M ≤ dim (R/p)` for every associated prime `p` of a finite nonzero module `M`.
-/

@[expose] public section

open Module RingTheory.Sequence Pointwise in
/-- `(M ⧸ ⟨a⟩•⊤) ⧸ ofList l•⊤` has the `ofList l` part as the image of `ofList(a::l)•⊤`. -/
theorem map_ofList_cons {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] (a : R)
    (l : List R) :
    Submodule.map (Ideal.span {a} • (⊤ : Submodule R M)).mkQ (Ideal.ofList (a :: l) • ⊤) =
      Ideal.ofList l • (⊤ : Submodule R (M ⧸ Ideal.span {a} • (⊤ : Submodule R M))) := by
  have hofl : Ideal.ofList (a :: l) = Ideal.span {a} ⊔ Ideal.ofList l := by
    unfold Ideal.ofList
    rw [show {r | r ∈ a :: l} = insert a {r | r ∈ l} by
        ext x; simp [List.mem_cons]]
    rw [Ideal.span_insert]
  have hbot :
    Ideal.span {a} • (⊤ : Submodule R (M ⧸ Ideal.span {a} • (⊤ : Submodule R M))) = ⊥ := by
    simp only [Submodule.ideal_span_singleton_smul]
    rw [eq_bot_iff]; rintro x hx
    rw [Submodule.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨c, -, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    rw [Submodule.mem_bot, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a) trivial
  rw [hofl, Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ, Submodule.sup_smul, hbot,
    bot_sup_eq]

open Pointwise in
/-- The submodule cut out by a list of ring elements grows when an element is prepended. -/
theorem span_singleton_smul_top_le_ofList_cons {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] (a : R) (l : List R) :
    Ideal.span {a} • (⊤ : Submodule R M) ≤ Ideal.ofList (a :: l) • (⊤ : Submodule R M) := by
  apply Submodule.smul_mono_left
  rw [Ideal.span_le, Set.singleton_subset_iff]
  apply Ideal.subset_span
  simp [List.mem_cons]

open Pointwise in
/-- `((M ⧸ ⟨a⟩•⊤) ⧸ ofList l•⊤) ≃ₗ M ⧸ ofList(a::l)•⊤`. -/
noncomputable def consQuotEquiv {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (a : R) (l : List R) :
    ((M ⧸ Ideal.span {a} • (⊤ : Submodule R M)) ⧸
        Ideal.ofList l • (⊤ : Submodule R (M ⧸ Ideal.span {a} • (⊤ : Submodule R M)))) ≃ₗ[R]
      (M ⧸ Ideal.ofList (a :: l) • (⊤ : Submodule R M)) :=
  (Submodule.quotEquivOfEq _ _ (map_ofList_cons a l).symm).trans
    (Submodule.quotientQuotientEquivQuotient _ _ (span_singleton_smul_top_le_ofList_cons a l))

open Module RingTheory.Sequence in
/-- (Stacks 00N4.) The quotient of a Cohen–Macaulay module by an `M`-regular sequence
`rs ⊆ m` is Cohen–Macaulay, by induction on `rs` via
`isCohenMacaulay_quotSMulTop_of_isSMulRegular`. -/
@[ega "0 16.4.10" "(i), special case", ega "0 16.5.5" "more general", ega "0 16.5.6" "(x)"]
theorem isCohenMacaulay_quotient_ofList {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (rs : List R) :
    ∀ {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M],
      IsCohenMacaulayModule R M →
        IsRegular M rs →
        (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R) →
        IsCohenMacaulayModule R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)) := by
  induction rs with
  | nil =>
    intro M _ _ _ hCM hreg hmem
    have he : (M ⧸ Ideal.ofList ([] : List R) • (⊤ : Submodule R M)) ≃ₗ[R] M := by
      have hb : Ideal.ofList ([] : List R) • (⊤ : Submodule R M) = ⊥ := by simp [Ideal.ofList]
      exact Submodule.quotEquivOfEqBot _ hb
    exact isCohenMacaulay_of_linearEquiv he.symm hCM
  | cons a l IH =>
    intro M _ _ _ hCM hreg hmem
    have hNT : Nontrivial M := hreg.nontrivial
    rw [isRegular_cons_iff] at hreg
    obtain ⟨hareg, hlreg⟩ := hreg
    have hamem : a ∈ IsLocalRing.maximalIdeal R := hmem a (List.mem_cons_self ..)
    have hlmem : ∀ r ∈ l, r ∈ IsLocalRing.maximalIdeal R := fun r hr =>
      hmem r (List.mem_cons_of_mem a hr)
    have hCMq : IsCohenMacaulayModule R (QuotSMulTop a M) :=
      isCohenMacaulay_quotSMulTop_of_isSMulRegular hCM a hamem hareg
    set Mq := M ⧸ Ideal.span {a} • (⊤ : Submodule R M) with hMq
    have heqv : QuotSMulTop a M ≃ₗ[R] Mq :=
      Submodule.quotEquivOfEq _ _ (Submodule.ideal_span_singleton_smul a ⊤).symm
    have hCMq' : IsCohenMacaulayModule R Mq := isCohenMacaulay_of_linearEquiv heqv hCMq
    have hlreg' : IsRegular Mq l := isRegular_of_linearEquiv heqv l hlreg
    have hIH : IsCohenMacaulayModule R (Mq ⧸ Ideal.ofList l • (⊤ : Submodule R Mq)) :=
      IH hCMq' hlreg' hlmem
    exact isCohenMacaulay_of_linearEquiv (consQuotEquiv a l) hIH

open Pointwise in
/-- The ideal generated by `p` acts as zero on `M ⧸ (p) • ⊤`. -/
theorem ofList_smul_top_quotient_eq_bot {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] (p : List R) :
    Ideal.ofList p • (⊤ : Submodule R (M ⧸ Ideal.ofList p • (⊤ : Submodule R M))) = ⊥ := by
  rw [eq_bot_iff, Submodule.smul_le]
  intro r hr x _
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Submodule.mem_bot, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul hr trivial

open Pointwise in
/-- The image of `(p ++ rest) • ⊤` in `M ⧸ (p) • ⊤` is `(rest) • ⊤`. -/
theorem map_ofList_append {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (p rest : List R) :
    Submodule.map (Ideal.ofList p • (⊤ : Submodule R M)).mkQ (Ideal.ofList (p ++ rest) • ⊤) =
      Ideal.ofList rest • (⊤ : Submodule R (M ⧸ Ideal.ofList p • (⊤ : Submodule R M))) := by
  have hofl : Ideal.ofList (p ++ rest) = Ideal.ofList p ⊔ Ideal.ofList rest := by
    rw [Ideal.ofList, Ideal.ofList, Ideal.ofList, ← Ideal.span_union]
    congr 1; ext x; simp [List.mem_append, Set.mem_union]
  rw [hofl, Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ, Submodule.sup_smul,
    ofList_smul_top_quotient_eq_bot, bot_sup_eq]

open Pointwise in
/-- The submodule cut out by a list of ring elements grows when the list is extended. -/
theorem ofList_smul_top_le_ofList_append {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] (p rest : List R) :
    Ideal.ofList p • (⊤ : Submodule R M) ≤ Ideal.ofList (p ++ rest) • (⊤ : Submodule R M) := by
  apply Submodule.smul_mono_left
  rw [Ideal.ofList, Ideal.ofList, Ideal.span_le]
  intro x hx; apply Ideal.subset_span
  simp only [Set.mem_ofPred_eq, List.mem_append]; exact Or.inl hx

open Pointwise in
/-- `((M ⧸ ofList p•⊤) ⧸ ofList rest•⊤) ≃ₗ M ⧸ ofList(p++rest)•⊤`. -/
noncomputable def appendQuotEquiv {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] (p rest : List R) :
    ((M ⧸ Ideal.ofList p • (⊤ : Submodule R M)) ⧸
        Ideal.ofList rest • (⊤ : Submodule R (M ⧸ Ideal.ofList p • (⊤ : Submodule R M)))) ≃ₗ[R]
      (M ⧸ Ideal.ofList (p ++ rest) • (⊤ : Submodule R M)) :=
  (Submodule.quotEquivOfEq _ _ (map_ofList_append p rest).symm).trans
    (Submodule.quotientQuotientEquivQuotient _ _ (ofList_smul_top_le_ofList_append p rest))

open Module RingTheory.Sequence in
/-- A prefix of an `M`-regular sequence is `M`-regular (properness from full sequence). -/
theorem isRegular_prefix_append {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (p rest : List R) (hf : IsRegular M (p ++ rest)) : IsRegular M p := by
  rw [isRegular_iff] at hf ⊢
  obtain ⟨hw, hprop⟩ := hf
  rw [isWeaklyRegular_append_iff] at hw
  refine ⟨hw.left, ?_⟩
  intro hpeq
  apply hprop
  have hle : Ideal.ofList p ≤ Ideal.ofList (p ++ rest) := by
    rw [Ideal.ofList, Ideal.ofList, Ideal.span_le]
    intro x hx; apply Ideal.subset_span
    simp only [Set.mem_ofPred_eq, List.mem_append]; exact Or.inl hx
  exact le_antisymm (hpeq.trans_le (Submodule.smul_mono_left hle)) le_top

open Module in
/-- `Supp(M ⧸ ofList p•⊤) ∩ V(g) = Supp(M) ∩ zeroLocusCons g p`. -/
@[ega "0 1.7.5" "partial",
  ega "III 2.6.2.5" "special case",
  ega "IV 3.4.1" "Supp(F/tF) = Supp(F) ∩ Y"]
theorem support_quotient_inter_eq {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] [Module.Finite R M] (g : R) (p : List R) :
    Module.support R (M ⧸ Ideal.ofList p • (⊤ : Submodule R M)) ∩
        PrimeSpectrum.zeroLocus (↑(Ideal.span {g}) : Set R) =
      Module.support R M ∩ zeroLocusCons g p := by
  rw [Module.support_quotient]
  unfold zeroLocusCons
  rw [Set.inter_assoc]
  congr 1
  rw [Ideal.ofList, PrimeSpectrum.zeroLocus_span, PrimeSpectrum.zeroLocus_span, ←
    PrimeSpectrum.zeroLocus_union, Set.union_comm,
    show (insert g {x | x ∈ p} : Set R) = {g} ∪ {x | x ∈ p} from rfl]

open Module RingTheory.Sequence Pointwise in
/-- (Reordering bridge for (b2).) If `p` is `M`-regular (entries in `m`) and `g ∈ m` is
regular on `M ⧸ ofList p•⊤`, then `p` is regular on `M ⧸ ⟨g⟩•⊤`. Proof: `p ++ [g]` is
`M`-regular (append + properness), reorder to `g :: p` (Stacks 00LJ), peel `g`. -/
@[ega "IV 19.5.3" "c) ⇒ a), special case"]
theorem isRegular_quotient_span_of_isSMulRegular_quotient {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] (g : R)
    (hg : g ∈ IsLocalRing.maximalIdeal R) (p : List R) (hpreg : IsRegular M p)
    (hQreg : IsSMulRegular (M ⧸ Ideal.ofList p • (⊤ : Submodule R M)) g) :
    IsRegular (M ⧸ Ideal.span {g} • (⊤ : Submodule R M)) p := by
  have hNTQ : Nontrivial (M ⧸ Ideal.ofList p • (⊤ : Submodule R M)) :=
    (Submodule.Quotient.nontrivial_iff).mpr (Ne.symm hpreg.top_ne_smul)
  have hQg : IsRegular (M ⧸ Ideal.ofList p • (⊤ : Submodule R M)) [g] := by
    rw [show ([g] : List R) = g :: [] from rfl, RingTheory.Sequence.isRegular_cons_iff]
    have : Nontrivial (QuotSMulTop g (M ⧸ Ideal.ofList p • (⊤ : Submodule R M))) :=
      nontrivial_quotSMulTop_of_mem_maximalIdeal _ hg
    exact ⟨hQreg, IsRegular.nil R _⟩
  have hpg : IsRegular M (p ++ [g]) := by
    rw [RingTheory.Sequence.isRegular_iff]
    refine ⟨?_, ?_⟩
    · rw [isWeaklyRegular_append_iff]
      exact ⟨hpreg.toIsWeaklyRegular, hQg.toIsWeaklyRegular⟩
    · have hNTpg :
        Nontrivial
          ((M ⧸ Ideal.ofList p • (⊤ : Submodule R M)) ⧸
            Ideal.ofList [g] • (⊤ : Submodule R (M ⧸ Ideal.ofList p • (⊤ : Submodule R M)))) :=
        (Submodule.Quotient.nontrivial_iff).mpr (Ne.symm hQg.top_ne_smul)
      have hNTfinal : Nontrivial (M ⧸ Ideal.ofList (p ++ [g]) • (⊤ : Submodule R M)) :=
        (appendQuotEquiv p [g]).symm.toEquiv.nontrivial
      exact Ne.symm ((Submodule.Quotient.nontrivial_iff).mp hNTfinal)
  have hperm : (p ++ [g]).Perm (g :: p) := by simp
  have hgp : IsRegular M (g :: p) := IsLocalRing.isRegular_of_perm hpg hperm
  rw [RingTheory.Sequence.isRegular_cons_iff] at hgp
  have heqv : QuotSMulTop g M ≃ₗ[R] (M ⧸ Ideal.span {g} • (⊤ : Submodule R M)) :=
    Submodule.quotEquivOfEq _ _ (Submodule.ideal_span_singleton_smul g ⊤).symm
  exact isRegular_of_linearEquiv heqv p hgp.right

/-- (Stacks 00N4, Lemma 10.103.2.) Let `R` be a Noetherian local ring with maximal
ideal `m`, let `M` be a Cohen-Macaulay finite `R`-module, and let `f_1, ..., f_d ∈ m`
(here `d = f.length`) be an `M`-regular sequence with `d = dim(Supp(M))`. Assume
`d ≥ 1` and let `g ∈ m` be good with respect to `(M, f_1, ..., f_d)`. Then:
(a) `g` is a nonzerodivisor on `M`;
(b) `M/gM` is Cohen-Macaulay, the images of `f_1, ..., f_{d-1}` form an
    `(M/gM)`-regular sequence, and this sequence is maximal, equivalently
    `dim(Supp(M/gM)) = depth(M/gM) = d - 1`. -/
@[stacks 00N4]
theorem isCohenMacaulayModule_quotient_of_isGoodElement {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {M : Type*}
    [AddCommGroup M] [Module R M] [Module.Finite R M] (hCM : IsCohenMacaulayModule R M)
    (f : List R) (hf : RingTheory.Sequence.IsRegular M f)
    (hfm : ∀ x ∈ f, x ∈ IsLocalRing.maximalIdeal R)
    (hd : (f.length : WithBot ℕ∞) = Module.supportDim R M) (hd1 : 1 ≤ f.length) (g : R)
    (hg : g ∈ IsLocalRing.maximalIdeal R) (hgood : IsGoodElement M f g) :
    -- (a) g is a nonzerodivisor on M
    IsSMulRegular M g ∧
      -- (b) M/gM is Cohen-Macaulay
      IsCohenMacaulayModule R (M ⧸ (Ideal.span {g}) • (⊤ : Submodule R M)) ∧
      -- the images of f_1, ..., f_{d-1} form an (M/gM)-regular sequence
      RingTheory.Sequence.IsRegular (M ⧸ (Ideal.span {g}) • (⊤ : Submodule R M))
        (f.take (f.length - 1)) ∧
      -- maximality: dim(Supp(M/gM)) = depth(M/gM) = d - 1 (the depth equality is the
      -- Cohen-Macaulay conclusion above; here we record the common value is d - 1)
      Module.supportDim R (M ⧸ (Ideal.span {g}) • (⊤ : Submodule R M)) =
        ((f.length - 1 : ℕ) : WithBot ℕ∞) := by
  -- Mathematical proof outline (Stacks 00N4, Lemma 10.103.2).
  --
  -- Write `d = f.length ≥ 1` and `N = M ⧸ (g) • ⊤ = M/gM`.
  --
  -- The four conjuncts depend on each other as follows: (b3) supportDim(N) = d-1 is proved
  -- directly from goodness at i = 0; (a) g M-regular is proved directly from goodness at i = 0 +
  -- CM; (b1) M/gM CM uses (a) (depth drops by 1) together with (b3); (b2) the (M/gM)-regular
  -- sequence uses (a) and goodness at i = 1, ..., d-1.
  have hg0 : Order.krullDim (↑(Module.support R M ∩
      PrimeSpectrum.zeroLocus (↑(Ideal.span {g}) : Set R)) : Set (PrimeSpectrum R)) =
        ((f.length - 1 : ℕ) : WithBot ℕ∞) := by
    have h := hgood 0 (by omega)
    have hset :
        zeroLocusCons g (f.take 0) = PrimeSpectrum.zeroLocus (↑(Ideal.span {g}) : Set R) := by
      unfold zeroLocusCons
      rw [List.take_zero, PrimeSpectrum.zeroLocus_span]
      simp
    rwa [hset] at h
  have hgreg : IsSMulRegular M g := by
    refine isSMulRegular_of_supportDim_inter_lt hCM g ?_
    rw [hg0, ← hd]
    exact_mod_cast (by omega : f.length - 1 < f.length)
  refine ⟨hgreg, ?_, ?_, ?_⟩
  · -- (b1) `M/gM` is Cohen–Macaulay: `IsCohenMacaulayModule R N`.
    --
    -- By definition `IsCohenMacaulayModule R N` means
    -- `depth N = supportDim N` (= `krullDim (Supp N)`). We compute both sides
    -- and equate them to `d - 1`.
    --   • `supportDim N = d - 1`: this is exactly conjunct (b3), proved below.
    --   • `depth N = d - 1`: by conjunct (a), `g` is `M`-regular; depth drops by
    --     exactly one along a regular element (Stacks 00LF / Rees: for `x`
    --     `M`-regular with `x ∈ m`, `depth(M/xM) = depth M - 1`). Here
    --     `depth M = supportDim M = d` because `M` is CM (`hCM`) and `hd`. With
    --     `d ≥ 1` (`hd1`), `depth N = d - 1`.
    -- Therefore `depth N = d - 1 = supportDim N`, i.e. `N` is CM.
    --
    -- Inputs: conjunct (a), conjunct (b3), `hCM`, `hd`, `hd1`, the depth drop
    -- `depth(M/xM) = depth M - 1` for an `M`-regular `x ∈ m`
    -- (`depth_quotient_succ_of_isSMulRegular`), and the unfolding of
    -- `IsCohenMacaulayModule` as `depth = supportDim`. This conjunct is logically
    -- downstream of (a) and (b3), so both are re-derived here.
    -- `M` is nontrivial since `supportDim M = f.length ≥ 1 ≠ ⊥`.
    have hNT : Nontrivial M := by
      rw [← Module.supportDim_ne_bot_iff_nontrivial R M, ← hd]
      simp
    -- CM equality for `M`: `↑(depth M) = supportDim M`.
    have heqM :
      (↑(Module.depthSup R (IsLocalRing.maximalIdeal R) M) : WithBot ℕ∞) =
        Module.supportDim R M := by
      unfold IsCohenMacaulayModule at hCM
      rw [Module.supportDim]; exact hCM
    -- Hence `depth M = f.length` in `ℕ∞`.
    have hdepthM : Module.depthSup R (IsLocalRing.maximalIdeal R) M = (f.length : ℕ∞) := by
      rw [← hd] at heqM; exact_mod_cast heqM
    -- Depth drops by one along the `M`-regular element `g`.
    have hdrop := depth_quotient_succ_of_isSMulRegular (M := M) g hg hgreg
    -- Therefore `depth (QuotSMulTop g M) = f.length - 1` in `ℕ∞`.
    have hdQ :
      Module.depthSup R (IsLocalRing.maximalIdeal R) (QuotSMulTop g M) =
        ((f.length - 1 : ℕ) : ℕ∞) := by
      rw [hdepthM] at hdrop
      have hfe : f.length = (f.length - 1) + 1 := by omega
      rw [hfe, Nat.cast_add, Nat.cast_one] at hdrop
      exact WithTop.add_right_cancel (ENat.one_ne_top) hdrop
    -- `N = M ⧸ (g)•⊤` and `QuotSMulTop g M = M ⧸ g•⊤` have equal depth (submodules agree).
    have hdepthN :
      Module.depthSup R (IsLocalRing.maximalIdeal R) (M ⧸ (Ideal.span {g}) • (⊤ : Submodule R M)) =
        Module.depthSup R (IsLocalRing.maximalIdeal R) (QuotSMulTop g M) := by
      unfold QuotSMulTop
      rw [Submodule.ideal_span_singleton_smul]
    -- `supportDim N = f.length - 1` (this is exactly conjunct (b3), re-derived locally).
    have hsuppN :
      Module.supportDim R (M ⧸ (Ideal.span {g}) • (⊤ : Submodule R M)) =
        ((f.length - 1 : ℕ) : WithBot ℕ∞) := by
      rw [Module.supportDim, Module.support_quotient, hg0]
    -- Assemble: `↑(depth N) = supportDim N` (both equal `f.length - 1`).
    unfold IsCohenMacaulayModule
    rw [show
        Order.krullDim ↑(Module.support R (M ⧸ (Ideal.span {g}) • (⊤ : Submodule R M))) =
          Module.supportDim R (M ⧸ (Ideal.span {g}) • (⊤ : Submodule R M))
        from rfl]
    rw [hsuppN, hdepthN, hdQ]
    norm_cast
  · -- (b2) the images of `f_1, ..., f_{d-1}` form an `(M/gM)`-regular sequence:
    -- `RingTheory.Sequence.IsRegular N (f.take (d-1))`.
    --
    -- We must show, with `N = M/gM`, that
    -- `f_1, ..., f_{d-1}` is `N`-regular, i.e. each `f_i` is a nonzerodivisor on
    -- `N/(f_1,...,f_{i-1})N` and `N/(f_1,...,f_{d-1})N ≠ 0`.
    -- Note `N/(f_1,...,f_{i-1})N = M/(g, f_1,...,f_{i-1})M`. The sequence
    -- `g, f_1, ..., f_{i-1}` is an `M`-regular sequence: `g` is `M`-regular by
    -- (a), and `f_1, ..., f_{i-1}` is `M`-regular (initial segment of the given
    -- regular sequence `f`, `hf`); to interleave we use that `f_1, ..., f_{i-1},
    -- g` is `M`-regular and apply `IsLocalRing.isRegular_of_perm` (Stacks 00LJ)
    -- to reorder it to `g, f_1, ..., f_{i-1}`. That `f_1, ..., f_{i-1}, g` is
    -- `M`-regular follows because `g` is good ⟹ `g` is a nonzerodivisor on
    -- `M/(f_1,...,f_{i-1})M` (goodness at index `i`:
    -- `dim(Supp(M/(f_1..f_{i-1})M) ∩ V(g)) = d - i < d - (i-1) = dim Supp(M/(f_1..f_{i-1})M)`,
    -- so by the same Ass-avoidance argument as (a) applied to the CM module
    -- `M/(f_1,...,f_{i-1})M`, `g` avoids its associated primes). Injectivity of
    -- `f_i` on `N/(f_1,...,f_{i-1})N = M/(g,f_1,...,f_{i-1})M` then follows since
    -- `f_i` is a nonzerodivisor on `M/(f_1,...,f_i)M` (from `hf`) and, `g` being
    -- a nonzerodivisor commuting through, on the quotient by the regular
    -- sequence `g,f_1,...,f_{i-1}` (regular sequences are unchanged under the
    -- reordering by 00LJ). Nonvanishing of `N/(f_1,...,f_{d-1})N` holds because
    -- its support has dimension `d - 1 - (d-1) = 0 ≥ 0` (it is nonempty: `m`
    -- itself is in the support, as the sequence is maximal).
    --
    -- Inputs: (a), `hf`, `hfm`, `hgood` at indices `1..d-1`,
    -- `IsLocalRing.isRegular_of_perm` (00LJ), the Ass-avoidance lemma
    -- (same as (a)) for the CM modules `M/(f_1,...,f_{i-1})M`, and the fact that
    -- quotienting by `(g)•⊤` then by `f.take(d-1)` agrees with quotienting `M`
    -- by the combined sequence.
    --
    -- Concretely, set `p = f.take (d-1)`. Then `p` is `M`-regular (prefix of `f`,
    -- `isRegular_prefix_append`), `Q' := M ⧸ ofList p • ⊤` is Cohen–Macaulay
    -- (`isCohenMacaulay_quotient_ofList`) of support dimension `1`
    -- (`supportDim_add_length_eq_supportDim_of_isRegular`). Goodness at `i = d-1`
    -- gives `krullDim(Supp Q' ∩ V(g)) = 0 < 1`, so `g` is `Q'`-regular
    -- (`isSMulRegular_of_supportDim_inter_lt`). Finally
    -- `isRegular_quotient_span_of_isSMulRegular_quotient` reorders `p ++ [g] ↦ g :: p`
    -- (Stacks 00LJ) to conclude `p` is `(M ⧸ ⟨g⟩•⊤)`-regular.
    set p := f.take (f.length - 1) with hp
    have hpf : f = p ++ f.drop (f.length - 1) := by rw [hp, List.take_append_drop]
    have hpreg : RingTheory.Sequence.IsRegular M p :=
      isRegular_prefix_append p (f.drop (f.length - 1))
        (by
          rw [← hpf]; exact hf)
    have hpmem : ∀ r ∈ p, r ∈ IsLocalRing.maximalIdeal R := fun r hr =>
      hfm r (List.mem_of_mem_take hr)
    have hplen : p.length = f.length - 1 := by
      rw [hp, List.length_take]; omega
    have hQCM : IsCohenMacaulayModule R (M ⧸ Ideal.ofList p • (⊤ : Submodule R M)) :=
      isCohenMacaulay_quotient_ofList p hCM hpreg hpmem
    have hsdQ :
      Module.supportDim R (M ⧸ Ideal.ofList p • (⊤ : Submodule R M)) = ((1 : ℕ) : WithBot ℕ∞) := by
      have hadd := Module.supportDim_add_length_eq_supportDim_of_isRegular p hpreg
      rw [hplen, ← hd] at hadd
      have hfe :
        (f.length : WithBot ℕ∞) = ((1 : ℕ) : WithBot ℕ∞) + ((f.length - 1 : ℕ) : WithBot ℕ∞) := by
        rw [← Nat.cast_add]; congr 1; omega
      rw [hfe] at hadd
      exact ENat.WithBot.add_natCast_cancel.mp hadd
    have hQreg : IsSMulRegular (M ⧸ Ideal.ofList p • (⊤ : Submodule R M)) g := by
      apply isSMulRegular_of_supportDim_inter_lt hQCM g
      rw [support_quotient_inter_eq, hsdQ]
      have hg' := hgood (f.length - 1) (by omega)
      rw [← hp] at hg'
      rw [hg']
      have hz : (f.length - (f.length - 1) - 1 : ℕ) = 0 := by omega
      rw [hz]
      norm_num
    exact isRegular_quotient_span_of_isSMulRegular_quotient g hg p hpreg hQreg
  · rw [Module.supportDim, Module.support_quotient, hg0]

end

@[expose] public section

open IsLocalRing RingTheory.Sequence

/-- **Cohen-Macaulay module** (Stacks 00N3).
A finite, nonzero `R`-module `M` over a Noetherian local ring is *Cohen-Macaulay* if the
dimension of its support equals its depth (with respect to the maximal ideal):
`dim(Supp(M)) = depth(M)`. Here `Module.supportDim R M : WithBot ℕ∞` and
`Module.depthSup R (maximalIdeal R) M : ℕ∞` (coerced into `WithBot ℕ∞`).
We require `[Module.Finite R M]` and `[Nontrivial M]` (`M ≠ 0`), matching the prose
convention that Cohen-Macaulayness is defined for finite, nonzero modules. -/
@[ega "0 16.5.1" "nonzero-module clause", ega "IV 5.7.1" "F is Cohen–Macaulay at x", ega "IV 7.5.3"]
def IsCohenMacaulay (R : Type*) [CommRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M] : Prop :=
  Module.supportDim R M = (Module.depthSup R (maximalIdeal R) M : WithBot ℕ∞)

/-- **Maximal `M`-regular sequence.**
A sequence `gs` is a *maximal `M`-regular sequence* (in the maximal ideal `m`) if all of
its entries lie in `m`, it is an `M`-regular sequence (`RingTheory.Sequence.IsRegular`),
and it cannot be extended: there is no `g ∈ m` such that `gs ++ [g]` is again an
`M`-regular sequence. -/
def IsMaximalRegularSequence (R : Type*) [CommRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (gs : List R) : Prop :=
  (∀ g ∈ gs, g ∈ maximalIdeal R) ∧ IsRegular M gs ∧
    ¬ ∃ g ∈ maximalIdeal R, IsRegular M (gs ++ [g])

/-! ### Supporting lemmas -/

/- **Depth–coheight bound — Stacks 00LK (the analytic heart of unmixedness 00N4).**
(The formal statement is
`depth_le_krullDim_zeroLocus_of_mem_associatedPrimes`, proved from the four lemmas
`nontrivial_of_mem_associatedPrimes`, `associatedPrime_lift_of_regular`,
`krullDim_zeroLocus_succ_le_of_lt`, and the engine `reg_seq_len_le_krullDim_zeroLocus`.)
For any finite, nonzero module `M` over a Noetherian local ring and any associated
prime `p ∈ Ass(M)`, the depth of `M` is bounded by the coheight of `p`, i.e. by the
Krull dimension `dim(R/p) = krullDim (V(p))` of the closed set cut out by `p`.

This is the general fact, about any finite module and with no Cohen–Macaulay hypothesis, on
which the unmixedness consequence rests.

The argument (Stacks 00LK). Let `d = depth M` and let `x₁,…,x_d ∈ m` be a maximal
`M`-regular sequence (the depth is the supremum of lengths of such sequences). Starting
from `p₀ = p ∈ Ass(M)`, iterate the **lifting step**:

* **(A) Lifting an associated prime along a regular element.** If `x ∈ m` is regular on a
  finite module `M'` and `p' ∈ Ass(M')`, then there is `p'' ∈ Ass(M'/xM')` with
  `p' ⊊ p''`. Proof: pick `m' ≠ 0` with `Ann(m') = p'`; since `x` is regular, `x ∉ p'`,
  and using **Krull's intersection theorem** (`⋂ₙ xⁿM' = 0` for finite `M'` over
  Noetherian local `R`, `x ∈ m`) one may assume the image `m̄` of `m'` is nonzero in
  `M'/xM'`; then `p' + (x) ⊆ Ann(m̄) ⊊ R`, and any associated prime `p''` of `R·m̄ ⊆ M'/xM'`
  contains `p' + (x) ⊋ p'`, so `p' ⊊ p''`.

Applying (A) to `M_{i} = M/(x₁,…,x_i)M` (with `x_{i+1}` regular on `M_i` since
`x₁,…,x_d` is `M`-regular) yields a strict chain `p = p₀ ⊊ p₁ ⊊ ⋯ ⊊ p_d` of primes all
containing `p`. This chain lives in `V(p) ≅ Spec(R/p)`, so `dim(R/p) = krullDim V(p) ≥ d
= depth M`.
-/
/-- A module possessing an associated prime is nonzero.
A `p ∈ Ass(M)` provides `x : M` with `p = (⊥ : Submodule R M).colon {x}` (radical); if `M`
were subsingleton then `x = 0`, `(⊥).colon {0} = ⊤`, and `p = ⊤.radical = ⊤`, contradicting
`p.IsPrime` (`p ≠ ⊤`). Formally: destruct `hp` to `⟨hpr, x, hx⟩`; by contradiction,
`Subsingleton` forces `x = 0`; compute `(⊥).colon {0} = ⊤` (`Submodule.mem_colon_singleton`)
and use `Ideal.radical_top`, contradicting `hpr.ne_top`. -/
theorem nontrivial_of_mem_associatedPrimes
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {p : Ideal R} (hp : p ∈ associatedPrimes R M) : Nontrivial M := by
  obtain ⟨hpr, x, hx⟩ := hp
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have hx0 : x = 0 := Subsingleton.elim x 0
  subst hx0
  have htop : (⊥ : Submodule R M).colon {(0:M)} = ⊤ := by
    ext r
    simp [Submodule.mem_colon_singleton]
  rw [htop, Ideal.radical_top] at hx
  exact hpr.ne_top hx

/- **Lifting step (A) — Stacks 00LK core.** If `x ∈ m` is `M`-regular and `p ∈ Ass(M)`,
then there is `q ∈ Ass(M/xM)` with `p ⊊ q` (strict).
The argument: pick
`0 ≠ m'` with `Ann(m') = p`. Since `x` is `M`-regular, `x ∉ p`. Using **Krull's intersection
theorem** for finite modules (`⋂ₙ xⁿ·M = 0`, `Ideal.iInf_pow_smul_eq_bot_of_isLocalRing`)
one reduces to `m' ∉ xM`, so the image `m̄` of `m'` in `M/xM` is nonzero.
Then `p + (x) ⊆ Ann(m̄) ⊊ R`, and `R·m̄ ≅ R/Ann(m̄) ↪ M/xM` is nonzero, hence has an
associated prime `q` (`associatedPrimes.nonempty`); `q ⊇ Ann(m̄) ⊇ p + (x) ⊋ p`
(strict because `x ∈ q` but `x ∉ p`). Push `q ∈ Ass(R·m̄) ⊆ Ass(M/xM)` via
`associatedPrimes.subset_of_injective`. Here `QuotSMulTop x M = M ⧸ (x • ⊤)`. -/
open scoped Pointwise in
/-- If `x` is `M`-regular, then the annihilator (`⊥.colon`) of `x • w` equals that
of `w`. (`r • (x • w) = 0 ↔ x • (r • w) = 0 ↔ r • w = 0` using regularity of `x`.) -/
theorem ann_smul_regular {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {x : R} (hxreg : IsSMulRegular M x) (w : M) :
    (⊥ : Submodule R M).colon {x • w} = (⊥ : Submodule R M).colon {w} := by
  ext r
  rw [Submodule.mem_colon_singleton, Submodule.mem_colon_singleton]
  simp only [Submodule.mem_bot]
  constructor
  · intro h; apply hxreg; simp only [smul_zero]; rw [smul_comm]; exact h
  · intro h; rw [smul_comm, h, smul_zero]

open scoped Pointwise in
/-- `m ∈ (span {a})^k • ⊤ ↔ ∃ z, m = a^k • z`. -/
theorem mem_span_pow_smul {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (a : R) (m : M) (k : ℕ) :
    m ∈ ((Ideal.span {a})^k • (⊤ : Submodule R M)) ↔ ∃ z, m = a^k • z := by
  rw [Ideal.span_singleton_pow]
  rw [show (Ideal.span {a^k} • (⊤ : Submodule R M)) = a^k • ⊤ from
      (Submodule.ideal_span_singleton_smul (a^k) ⊤),
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨z, _, rfl⟩; exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩; exact ⟨z, trivial, rfl⟩

open scoped Pointwise in
/-- **Krull-intersection descent.** If `x ∈ m` is `M`-regular and `p = Ann(m')` with
`m' ≠ 0`, then there is `n` with `Ann(n) = p` and `n ∉ x • M` (its image in `M/xM` is
nonzero). The deepest external input here is the module form of **Krull's intersection
theorem** `Ideal.iInf_pow_smul_eq_bot_of_isLocalRing` (`⨅ i, (span x)^i • ⊤ = ⊥` for
finite `M` over a Noetherian local ring, applied to the proper ideal `(x)`). The descent
iterates `ann_smul_regular`: if every element with annihilator `p` lay in `x • M`, then
`m'` would lie in `(x)^k • M` for all `k`, hence in `⨅ = ⊥`, contradicting `m' ≠ 0`. -/
theorem descent_of_regular {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {x : R} (hx : x ∈ maximalIdeal R) (hxreg : IsSMulRegular M x)
    {p : Ideal R} (m' : M) (hm' : p = (⊥ : Submodule R M).colon {m'})
    (hm'ne : m' ≠ 0) :
    ∃ n : M, p = (⊥ : Submodule R M).colon {n} ∧ n ∉ x • (⊤ : Submodule R M) := by
  by_contra hcon
  push Not at hcon
  have hxtop : Ideal.span {x} ≠ (⊤ : Ideal R) := by
    intro h
    rw [Ideal.span_singleton_eq_top] at h
    exact (maximalIdeal.isMaximal R).ne_top
      ((maximalIdeal R).eq_top_of_isUnit_mem hx h)
  have hkrull := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := M) (Ideal.span {x}) hxtop
  have key : ∀ k : ℕ, ∃ z : M, m' = x^k • z ∧ p = (⊥ : Submodule R M).colon {z} := by
    intro k
    induction k with
    | zero => exact ⟨m', by simp, hm'⟩
    | succ k ih =>
      obtain ⟨z, hz, hpz⟩ := ih
      have hzin : z ∈ x • (⊤ : Submodule R M) := hcon z hpz
      rw [Submodule.mem_smul_pointwise_iff_exists] at hzin
      obtain ⟨w, _, hw⟩ := hzin
      refine ⟨w, ?_, ?_⟩
      · rw [hz, ← hw, pow_succ, mul_smul]
      · rw [hpz, ← hw, ann_smul_regular hxreg w]
  have hmem : m' ∈ ⨅ i : ℕ, (Ideal.span {x})^i • (⊤ : Submodule R M) := by
    rw [Submodule.mem_iInf]
    intro k
    rw [mem_span_pow_smul]
    obtain ⟨z, hz, _⟩ := key k
    exact ⟨z, hz⟩
  rw [hkrull, Submodule.mem_bot] at hmem
  exact hm'ne hmem

open scoped Pointwise in
/-- Lifting an associated prime along a regular element: if `x ∈ m` is regular on a finite
module `M` and `p ∈ Ass M`, then some `q ∈ Ass (M / xM)` strictly contains `p`. -/
theorem associatedPrime_lift_of_regular
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {x : R} (hx : x ∈ maximalIdeal R) (hxreg : IsSMulRegular M x)
    {p : Ideal R} (hp : p ∈ associatedPrimes R M) :
    ∃ q ∈ associatedPrimes R (QuotSMulTop x M), p < q := by
  -- `x ∉ p`, since `x` is `M`-regular and the union of associated primes is the
  -- complement of the regular elements.
  have hxnp : x ∉ p := by
    have hkey := biUnion_associatedPrimes_eq_compl_regular R M
    intro hxp
    have : x ∈ ⋃ q ∈ associatedPrimes R M, (q : Set R) := by
      rw [Set.mem_iUnion₂]; exact ⟨p, hp, hxp⟩
    rw [hkey] at this
    exact this hxreg
  -- Over a Noetherian ring, an associated prime is the *exact* annihilator of some `m'`.
  have hp' : IsAssociatedPrime p M := hp
  rw [isAssociatedPrime_iff] at hp'
  obtain ⟨_, m', hm'⟩ := hp'
  -- `m' ≠ 0` (else `p = ⊥.colon {0} = ⊤`, contradicting primality).
  have hm'ne : m' ≠ 0 := by
    intro h
    apply hp.isPrime.ne_top
    rw [hm', h]
    ext r
    simp [Submodule.mem_colon_singleton]
  -- Krull-intersection descent: find `n` with `Ann(n) = p` whose image in `M/xM` is nonzero.
  obtain ⟨n, hpn, hnx⟩ := descent_of_regular hx hxreg m' hm' hm'ne
  set N : Submodule R M := x • (⊤ : Submodule R M) with hN
  have hnbar : N.mkQ n ≠ 0 := by
    rwa [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  -- Pick an associated prime `q` of `M/xM` lying above `Ann(n̄)` (Noetherian).
  obtain ⟨q, hqass, hqle⟩ :=
    exists_le_isAssociatedPrime_of_isNoetherianRing R (M := QuotSMulTop x M) (N.mkQ n) hnbar
  refine ⟨q, hqass, ?_⟩
  -- `p ≤ q`: every `r ∈ p = Ann(n)` kills `n̄`, hence lies in `Ann(n̄) ≤ q`.
  have hpq_le : p ≤ q := by
    intro r hr
    apply hqle
    rw [Submodule.mem_colon_singleton]
    simp only [Submodule.mem_bot]
    have hrn : r • n = 0 := by
      rwa [hpn, Submodule.mem_colon_singleton, Submodule.mem_bot] at hr
    change r • (N.mkQ n) = 0
    rw [← LinearMap.map_smul, hrn, map_zero]
  -- `x ∈ q`: `x` kills `n̄` (as `x • n ∈ x • ⊤`), so `x ∈ Ann(n̄) ≤ q`.
  have hxq : x ∈ q := by
    apply hqle
    rw [Submodule.mem_colon_singleton]
    simp only [Submodule.mem_bot]
    change x • (N.mkQ n) = 0
    rw [← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hN,
      Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨n, trivial, rfl⟩
  -- `p ≤ q` and `x ∈ q \ p` give the strict containment `p < q`.
  exact lt_of_le_of_ne hpq_le (fun heq => hxnp (heq ▸ hxq))

/-- **Chain-to-krullDim step.** A strict containment `p ⊊ q` of primes bumps the Krull dimension of
the zero locus by at least one: `krullDim V(q) + 1 ≤ krullDim V(p)`. Informally,
`V(q) = zeroLocus q ⊆ zeroLocus p = V(p)` (since `p ≤ q`); prepending the point `⟨p, _⟩` (which
lies in `V(p)` and is strictly below every point of `V(q) ⊆ V(p)`, as `p < q ≤ r` for `r ∈ V(q)`)
to any `LTSeries` in `V(q)` lengthens it by one inside `V(p)`. The inclusion `V(q) ⊆ V(p)` is
`PrimeSpectrum.zeroLocus_anti_mono` of `p ≤ q` (i.e. `hpq.le`). The `+1` comes from `p` being a
strict lower bound for all of `V(q)`. -/
theorem krullDim_zeroLocus_succ_le_of_lt
    {R : Type*} [CommRing R]
    {p q : Ideal R} (hp : p.IsPrime) (hq : q.IsPrime) (hpq : p < q) :
    Order.krullDim (PrimeSpectrum.zeroLocus (q : Set R)) + 1 ≤
      Order.krullDim (PrimeSpectrum.zeroLocus (p : Set R)) := by
  have hsub : PrimeSpectrum.zeroLocus (q : Set R) ⊆ PrimeSpectrum.zeroLocus (p : Set R) :=
    PrimeSpectrum.zeroLocus_anti_mono hpq.le
  have hincl : StrictMono (Set.inclusion hsub) := Subtype.strictMono_coe _
  have hppt : (⟨p, hp⟩ : PrimeSpectrum R) ∈ PrimeSpectrum.zeroLocus (p : Set R) := by
    rw [PrimeSpectrum.mem_zeroLocus]
  -- nonemptiness of V(q)
  have hne : Nonempty ↥(PrimeSpectrum.zeroLocus (q : Set R)) := by
    refine ⟨⟨⟨q, hq⟩, ?_⟩⟩
    rw [PrimeSpectrum.mem_zeroLocus]
  -- key: each chain in V(q) gives a chain of length +1 in V(p)
  have key : ∀ l : LTSeries ↥(PrimeSpectrum.zeroLocus (q : Set R)),
      ((l.length : WithBot ℕ∞) + 1) ≤ Order.krullDim ↥(PrimeSpectrum.zeroLocus (p : Set R)) := by
    intro l
    let l' : LTSeries ↥(PrimeSpectrum.zeroLocus (p : Set R)) := l.map (Set.inclusion hsub) hincl
    let b : ↥(PrimeSpectrum.zeroLocus (p : Set R)) := ⟨⟨p, hp⟩, hppt⟩
    have hbhead : (b, l'.head) ∈
      {x : ↥(PrimeSpectrum.zeroLocus (p : Set R)) × _ | x.fst < x.snd} := by
      change b < l'.head
      have hh : (l.head : PrimeSpectrum R) ∈ PrimeSpectrum.zeroLocus (q : Set R) := l.head.property
      simp only [PrimeSpectrum.mem_zeroLocus] at hh
      change (⟨⟨p, hp⟩, hppt⟩ : ↥(PrimeSpectrum.zeroLocus (p : Set R))) < l'.head
      rw [Subtype.mk_lt_mk]
      change (⟨p, hp⟩ : PrimeSpectrum R) < (l.head : PrimeSpectrum R)
      rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
      calc p < q := hpq
        _ ≤ (l.head : PrimeSpectrum R).asIdeal := hh
    let l'' : LTSeries ↥(PrimeSpectrum.zeroLocus (p : Set R)) := l'.cons b hbhead
    have hlen : l''.length = l.length + 1 := by
      rw [RelSeries.cons_length]; rfl
    have hkd := Order.LTSeries.length_le_krullDim l''
    rw [hlen] at hkd
    push_cast at hkd
    exact hkd
  -- assemble: krullDim V(q) + 1 ≤ krullDim V(p)
  rw [Order.krullDim_eq_iSup_length (α := ↥(PrimeSpectrum.zeroLocus (q : Set R)))]
  rw [← WithBot.coe_one, ← WithBot.coe_add, ENat.iSup_add, WithBot.coe_iSup (OrderTop.bddAbove _)]
  refine iSup_le fun l => ?_
  have hkl := key l
  push_cast at hkl ⊢
  exact hkl

/-- **Engine for Stacks 00LK.** For `p ∈ Ass(M)` and any `M`-regular sequence `rs` in `m`,
the length of `rs` is at most `krullDim V(p)`. Proven by induction on `rs`: the empty
sequence gives `0 ≤ krullDim V(p)` (nonneg, as `p ∈ V(p)` makes it nonempty); the cons step
`x :: rs` uses `isRegular_cons_iff` (`x` is `M`-regular and `rs` is `QuotSMulTop x M`-regular),
lifts `p` to `q ∈ Ass(QuotSMulTop x M)` with `p < q` via `associatedPrime_lift_of_regular`,
applies the IH to `(QuotSMulTop x M, q, rs)`, and combines with
`krullDim_zeroLocus_succ_le_of_lt`. (No `[Nontrivial M]` needed: `hp` already witnesses it.) -/
theorem reg_seq_len_le_krullDim_zeroLocus
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (p : Ideal R) (hp : p ∈ associatedPrimes R M)
    (rs : List R) (hmem : ∀ r ∈ rs, r ∈ maximalIdeal R) (hreg : IsRegular M rs) :
    (rs.length : WithBot ℕ∞) ≤ Order.krullDim (PrimeSpectrum.zeroLocus (p : Set R)) := by
  induction rs generalizing M p with
  | nil =>
      simp only [List.length_nil, Nat.cast_zero]
      have hpprime : p.IsPrime := hp.isPrime
      have : Nonempty (PrimeSpectrum.zeroLocus (p : Set R)) :=
        ⟨⟨⟨p, hpprime⟩, by rw [PrimeSpectrum.mem_zeroLocus]⟩⟩
      exact Order.krullDim_nonneg_iff.mpr inferInstance
  | cons x rs ih =>
      rw [isRegular_cons_iff] at hreg
      obtain ⟨hxreg, hrsreg⟩ := hreg
      have hxmem : x ∈ maximalIdeal R := hmem x (by simp)
      have hmem' : ∀ r ∈ rs, r ∈ maximalIdeal R := fun r hr => hmem r (List.mem_cons_of_mem x hr)
      obtain ⟨q, hq, hpq⟩ := associatedPrime_lift_of_regular hxmem hxreg hp
      have : Nontrivial (QuotSMulTop x M) := nontrivial_of_mem_associatedPrimes hq
      have hih := ih (M := QuotSMulTop x M) q hq hmem' hrsreg
      calc ((x :: rs).length : WithBot ℕ∞)
          = (rs.length : WithBot ℕ∞) + 1 := by push_cast [List.length_cons]; ring
        _ ≤ Order.krullDim (PrimeSpectrum.zeroLocus (q : Set R)) + 1 := by gcongr
        _ ≤ Order.krullDim (PrimeSpectrum.zeroLocus (p : Set R)) :=
          krullDim_zeroLocus_succ_le_of_lt hp.isPrime hq.isPrime hpq

/-- The depth-coheight bound (Stacks 00LK): for an associated prime `p` of a finite nonzero
module `M`, `depth M ≤ krullDim (V p) = dim (R / p)`. -/
@[ega "0 16.4.6" "(iii)", ega "IV 21.1.10" "partial"]
theorem depth_le_krullDim_zeroLocus_of_mem_associatedPrimes
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (p : Ideal R) (hp : p ∈ associatedPrimes R M) :
    (Module.depthSup R (maximalIdeal R) M : WithBot ℕ∞) ≤
      Order.krullDim (PrimeSpectrum.zeroLocus (p : Set R)) := by
  -- Reduce `depth = sSup {regular-seq lengths}` to the per-sequence bound
  -- `reg_seq_len_le_krullDim_zeroLocus`, pushing the `ℕ∞ → WithBot ℕ∞` coercion through `sSup`.
  have hpprime : p.IsPrime := hp.isPrime
  have hne : Order.krullDim (PrimeSpectrum.zeroLocus (p : Set R)) ≠ ⊥ := by
    rw [Order.krullDim_ne_bot_iff]
    exact ⟨⟨⟨p, hpprime⟩, by rw [PrimeSpectrum.mem_zeroLocus]⟩⟩
  obtain ⟨k, hk⟩ := WithBot.ne_bot_iff_exists.mp hne
  rw [← hk]
  rw [show Module.depthSup R (maximalIdeal R) M
      = sSup {n : ℕ∞ | ∃ rs : List R, (rs.length : ℕ∞) = n ∧ (∀ r ∈ rs, r ∈ maximalIdeal R)
          ∧ RingTheory.Sequence.IsRegular M rs} from rfl]
  rw [WithBot.coe_le_coe]
  apply sSup_le
  rintro n ⟨rs, rfl, hmem, hreg⟩
  have h := reg_seq_len_le_krullDim_zeroLocus p hp rs hmem hreg
  rw [← hk] at h
  exact_mod_cast h

end
