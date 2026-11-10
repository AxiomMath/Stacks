module

public import Mathlib.Order.Int.LeastGreatest
public import StacksCore.Algebra.Homology.SpectralSequence.EdgeStep

/-!
# The infinity page of a spectral sequence

Port of `Mathlib/Algebra/Homology/SpectralSequence/PageInfinity.lean` from mathlib#25848
(Joël Riou, head 2f4d873c95, not yet merged; Copyright (c) 2024 Joël Riou, released under the
Apache 2.0 license); delete when the pin includes it. Names, statements and namespace are
upstream's; proofs may differ (the upstream `set_option` workarounds are not used).
**Everything in this file is temporary and is expected to be deleted** when the pin includes
mathlib#25848.

For `E : SpectralSequence C c r₀` and a position `pq`, `E.HasPageInfinityAt pq` says that from
some page on all differentials into `pq` vanish and from some page on all differentials out of
`pq` vanish; `E.rToMin pq`, `E.rFromMin pq` are the least such pages and `E.rMin pq` their
maximum, from which the object at `pq` is constant. The infinity page `E.pageInfinity pq : C` is
`(E.page (E.rMin pq)).X pq` in that case and `0` otherwise, and
`E.pageInfinityIso pq r : E.pageInfinity pq ≅ (E.page r).X pq` for every page `r` with
`E.HasEdgeMonoAtFrom pq r` and `E.HasEdgeEpiAtFrom pq r` (`rToMin pq ≤ r`, `rFromMin pq ≤ r`),
through the composites `edgeMonoSteps`/`edgeEpiSteps` of the one-step edge maps of `EdgeStep`;
`edgeMono pq r : E_∞ ⟶ E_r` and `edgeEpi pq r : E_r ⟶ E_∞` are the edge maps to and from the
infinity page, `Hom.mapPageInfinity` the functoriality, and the last section gives the edge
classes of a first quadrant cohomological spectral sequence.

In Stacks' terms (011O, `StacksCore.Algebra.Homology.SpectralSequence.Tower`): `pageInfinity pq` is
the limit `E_∞ = Z_∞/B_∞` whenever the towers `B_r ⊆ Z_r` at `pq` stabilise, and is `0`
otherwise, where Stacks' `E_∞` may still exist; the general `Z_∞/B_∞` without stabilisation is
not given a separate definition.

Everything in upstream's file is ported except the root-level `Set.has_min_of_ℤ`, replaced by
Mathlib's `Int.exists_least_of_bdd` (hence the import `Mathlib.Data.Int.LeastGreatest`).
Other divergences: `attribute [local instance] epi_comp` is dropped (`epi_comp` is an instance
at the pin); the deprecated `dif_pos`/`dif_neg` become `dite_eq_left`/`dite_eq_right`; the lemma
`rMin_LE` is new (it gives the proof stored in `pageInfinityIso` the syntactic type
`E.rMin pq ≤ r`, which `simp` needs to apply the `edgeIsoSteps` projections); the four lemmas
upstream proves under `set_option backward.defeqAttrib.useBackward true`
(`edgeMono_edgeMonoSteps`, `pageInfinityIso_hom_edgeMonoSteps'` and their duals) are re-proved
by a case split, with `edgeMono_eq_pageInfinityIso_hom`/`edgeEpi_eq_pageInfinityIso_inv` proved
directly and placed before the primed lemmas; the two `change`-based `2 → 3` instances use
`hasEdgeMonoAtFrom_of_GE`/`hasEdgeEpiAtFrom_of_GE`, and the `change`-based `have` in
`Hom.isIso_mapPageInfinity_of_isIso_hom` is dropped (`IsIso (φ.f i)` is an instance at the pin).
-/

@[expose] public section

namespace CategoryTheory

open Category ZeroObject

variable {C : Type*} [Category* C] [Abelian C]
  {ι : Type*} {c : ℤ → ComplexShape ι} {r₀ : ℤ}

namespace SpectralSequence

variable (E : SpectralSequence C c r₀)

/-- A spectral sequence `E` has an infinity page at the position `pq` if, from some page on,
all the differentials into `pq` vanish and, from some (possibly different) page on, all the
differentials out of `pq` vanish. Upstream: mathlib#25848. -/
class HasPageInfinityAt (pq : ι) : Prop where
  /-- from some page on, all the differentials into `pq` vanish -/
  nonempty_hasEdgeMonoSet : (E.hasEdgeMonoSet pq).Nonempty
  /-- from some page on, all the differentials out of `pq` vanish -/
  nonempty_hasEdgeEpiSet : (E.hasEdgeEpiSet pq).Nonempty

section

variable (pq : ι) [E.HasPageInfinityAt pq]

/-- The set of pages from which all differentials into `pq` vanish is nonempty. -/
lemma nonempty_hasEdgeMonoSet :
    (E.hasEdgeMonoSet pq).Nonempty :=
  HasPageInfinityAt.nonempty_hasEdgeMonoSet

/-- The set of pages from which all differentials out of `pq` vanish is nonempty. -/
lemma nonempty_hasEdgeEpiSet :
    (E.hasEdgeEpiSet pq).Nonempty :=
  HasPageInfinityAt.nonempty_hasEdgeEpiSet

/-- The page chosen by `Int.exists_least_of_bdd` in a nonempty set bounded below by `r₀` is the
least element of the set. -/
private lemma choose_least_spec (S : Set ℤ) (hS : ∀ r ∈ S, r₀ ≤ r) (h : S.Nonempty) :
    (Int.exists_least_of_bdd (P := (· ∈ S)) ⟨r₀, hS⟩ h).choose ∈ S ∧
      ∀ r ∈ S, (Int.exists_least_of_bdd (P := (· ∈ S)) ⟨r₀, hS⟩ h).choose ≤ r :=
  (Int.exists_least_of_bdd (P := (· ∈ S)) ⟨r₀, hS⟩ h).choose_spec

/-- The least page from which all the differentials into `pq` vanish. -/
noncomputable def rToMin : ℤ :=
  (Int.exists_least_of_bdd (P := (· ∈ E.hasEdgeMonoSet pq)) ⟨r₀, fun _ hx ↦ hx.1⟩
    (E.nonempty_hasEdgeMonoSet pq)).choose

/-- `E.rToMin pq` belongs to `E.hasEdgeMonoSet pq`. -/
lemma rToMin_mem : E.rToMin pq ∈ E.hasEdgeMonoSet pq :=
  (choose_least_spec _ (fun _ hx ↦ hx.1) (E.nonempty_hasEdgeMonoSet pq)).1

/-- `E.rToMin pq` is the least element of `E.hasEdgeMonoSet pq`. -/
lemma rToMin_LE (r : ℤ) (hr : r ∈ E.hasEdgeMonoSet pq) :
    E.rToMin pq ≤ r :=
  (choose_least_spec _ (fun _ hx ↦ hx.1) (E.nonempty_hasEdgeMonoSet pq)).2 r hr

/-- `E.rToMin pq` is at least the starting page `r₀`. -/
lemma LE_rToMin :
    r₀ ≤ E.rToMin pq :=
  (E.rToMin_mem pq).1

/-- The least page from which all the differentials out of `pq` vanish. -/
noncomputable def rFromMin : ℤ :=
  (Int.exists_least_of_bdd (P := (· ∈ E.hasEdgeEpiSet pq)) ⟨r₀, fun _ hx ↦ hx.1⟩
    (E.nonempty_hasEdgeEpiSet pq)).choose

/-- `E.rFromMin pq` belongs to `E.hasEdgeEpiSet pq`. -/
lemma rFromMin_mem : E.rFromMin pq ∈ E.hasEdgeEpiSet pq :=
  (choose_least_spec _ (fun _ hx ↦ hx.1) (E.nonempty_hasEdgeEpiSet pq)).1

/-- `E.rFromMin pq` is the least element of `E.hasEdgeEpiSet pq`. -/
lemma rFromMin_LE (r : ℤ) (hr : r ∈ E.hasEdgeEpiSet pq) :
    E.rFromMin pq ≤ r :=
  (choose_least_spec _ (fun _ hx ↦ hx.1) (E.nonempty_hasEdgeEpiSet pq)).2 r hr

/-- `E.rFromMin pq` is at least the starting page `r₀`. -/
lemma LE_rFromMin :
    r₀ ≤ E.rFromMin pq :=
  (E.rFromMin_mem pq).1

/-- The least page from which the object at `pq` is stable: all differentials into and out
of `pq` vanish from `E.rMin pq` on. -/
noncomputable def rMin : ℤ := max (E.rToMin pq) (E.rFromMin pq)

/-- `E.rFromMin pq ≤ E.rMin pq`. -/
lemma rFromMin_LE_rMin : E.rFromMin pq ≤ E.rMin pq := le_max_right _ _

/-- `E.rToMin pq ≤ E.rMin pq`. -/
lemma rToMin_LE_rMin : E.rToMin pq ≤ E.rMin pq := le_max_left _ _

/-- `E.rMin pq` is at least the starting page `r₀`. -/
lemma LE_rMin :
    r₀ ≤ E.rMin pq :=
  (E.LE_rFromMin pq).trans (E.rFromMin_LE_rMin pq)

end

/-- The differentials into `pq'` vanish on every page `r ≥ E.rToMin pq'`. -/
lemma d_to_eq_zero (r : ℤ) (pq pq' : ι) [E.HasPageInfinityAt pq']
    (hr : E.rToMin pq' ≤ r) :
    (E.page r (by have := E.LE_rToMin pq'; lia)).d pq pq' = 0 := by
  have := (E.rToMin_mem pq').2 _ hr
  simp

/-- The differentials out of `pq` vanish on every page `r ≥ E.rFromMin pq`. -/
lemma d_from_eq_zero (r : ℤ) (pq pq' : ι) [E.HasPageInfinityAt pq]
    (hr : E.rFromMin pq ≤ r) :
    (E.page r (by have := E.LE_rFromMin pq; lia)).d pq pq' = 0 := by
  have := (E.rFromMin_mem pq).2 _ hr
  simp

/-- `E.HasEdgeMonoAt pq r` holds for every page `r ≥ E.rToMin pq`. -/
lemma hasEdgeMonoAt_of_rToMin_LE (pq : ι) [E.HasPageInfinityAt pq] (r : ℤ)
    (hr : E.rToMin pq ≤ r) :
    E.HasEdgeMonoAt pq r where
  le := (E.LE_rToMin pq).trans hr
  zero pq' := E.d_to_eq_zero r pq' pq hr

/-- `E.HasEdgeEpiAt pq r` holds for every page `r ≥ E.rFromMin pq`. -/
lemma hasEdgeEpiAt_of_rFromMin_LE (pq : ι) [E.HasPageInfinityAt pq] (r : ℤ)
    (hr : E.rFromMin pq ≤ r) :
    E.HasEdgeEpiAt pq r where
  le := (E.LE_rFromMin pq).trans hr
  zero pq' := E.d_from_eq_zero r pq pq' hr

section

variable (pq : ι) (r : ℤ) [E.HasPageInfinityAt pq]

/-- All the differentials into `pq` vanish from the page `r` on, i.e. `E.rToMin pq ≤ r`. -/
class HasEdgeMonoAtFrom : Prop where
  /-- `E.rToMin pq ≤ r` -/
  le : E.rToMin pq ≤ r

/-- `E.HasEdgeMonoAtFrom pq (E.rToMin pq)`. -/
instance : E.HasEdgeMonoAtFrom pq (E.rToMin pq) where
  le := by rfl

/-- `E.HasEdgeMonoAtFrom pq (E.rMin pq)`. -/
instance : E.HasEdgeMonoAtFrom pq (E.rMin pq) where
  le := E.rToMin_LE_rMin pq

/-- Constructor for `HasEdgeMonoAtFrom`. -/
lemma HasEdgeMonoAtFrom.mk' (h : ∀ (k : ℕ), E.HasEdgeMonoAt pq (r + k))
    (hr : r₀ ≤ r := by lia) :
    E.HasEdgeMonoAtFrom pq r where
  le := E.rToMin_LE _ _ ⟨hr, fun r' hr' ↦ by
    obtain ⟨k, rfl⟩ := Int.le.dest hr'
    infer_instance⟩

variable [E.HasEdgeMonoAtFrom pq r]

/-- `E.rToMin pq ≤ r` when `E.HasEdgeMonoAtFrom pq r`. -/
lemma LE_of_hasEdgeMonoAtFrom : E.rToMin pq ≤ r := by apply HasEdgeMonoAtFrom.le

include E pq in
/-- `r₀ ≤ r` when `E.HasEdgeMonoAtFrom pq r`. -/
lemma le₀_of_hasEdgeMonoAtFrom : r₀ ≤ r :=
  (E.LE_rToMin pq).trans (E.LE_of_hasEdgeMonoAtFrom pq r)

/-- `r ∈ E.hasEdgeMonoSet pq` when `E.HasEdgeMonoAtFrom pq r`. -/
lemma mem_hasEdgeMonoSet : r ∈ E.hasEdgeMonoSet pq :=
  ⟨(E.LE_rToMin pq).trans HasEdgeMonoAtFrom.le, fun _ hrr' ↦
    ⟨(E.le₀_of_hasEdgeMonoAtFrom pq r).trans hrr',
      fun _ ↦  E.d_to_eq_zero _ _ _ ((E.LE_of_hasEdgeMonoAtFrom pq r).trans hrr')⟩⟩

/-- `HasEdgeMonoAtFrom` is stable under increasing the page. -/
lemma hasEdgeMonoAtFrom_of_GE (r' : ℤ) (_ : r ≤ r' := by lia) :
    E.HasEdgeMonoAtFrom pq r' where
  le := by have := E.LE_of_hasEdgeMonoAtFrom pq r; lia

/-- `E.HasEdgeMonoAtFrom pq (max r r')` when `E.HasEdgeMonoAtFrom pq r`. -/
instance (r' : ℤ) :
    E.HasEdgeMonoAtFrom pq (max r r') :=
  E.hasEdgeMonoAtFrom_of_GE pq r _ (le_max_left _ _)

/-- `E.HasEdgeMonoAtFrom pq (max r' r)` when `E.HasEdgeMonoAtFrom pq r`. -/
instance (r' : ℤ) :
    E.HasEdgeMonoAtFrom pq (max r' r) :=
  E.hasEdgeMonoAtFrom_of_GE pq r _ (le_max_right _ _)

/-- `E.HasEdgeMonoAt pq r` when `E.HasEdgeMonoAtFrom pq r`. -/
instance : E.HasEdgeMonoAt pq r where
  le := E.le₀_of_hasEdgeMonoAtFrom pq r
  zero pq' := E.d_to_eq_zero r pq' pq (E.LE_of_hasEdgeMonoAtFrom pq r)

/-- `E.HasEdgeMonoAtFrom pq (r + k)` when `E.HasEdgeMonoAtFrom pq r`. -/
instance (k : ℕ) : E.HasEdgeMonoAtFrom pq (r + k) where
  le := by have := E.LE_of_hasEdgeMonoAtFrom pq r; lia

/-- `E.HasEdgeMonoAtFrom pq 3` when `E.HasEdgeMonoAtFrom pq 2`. -/
instance [E.HasEdgeMonoAtFrom pq 2] : E.HasEdgeMonoAtFrom pq 3 :=
  E.hasEdgeMonoAtFrom_of_GE pq 2 3

/-- Auxiliary definition for `edgeMonoSteps`. -/
noncomputable def edgeMonoSteps' (k : ℕ) :
    (E.page (r + k) (by have := E.le₀_of_hasEdgeMonoAtFrom pq r; lia)).X pq ⟶
      (E.page r (E.le₀_of_hasEdgeMonoAtFrom pq r)).X pq := by
  induction k with
  | zero => exact (E.pageXIsoOfEq pq _ _ (by simp)
      (by have := E.le₀_of_hasEdgeMonoAtFrom pq r; lia)).hom
  | succ k hk => exact E.edgeMonoStep pq (r + k) (r + ((k + 1) : ℕ)) ≫ hk

/-- `edgeMonoSteps'` at `k = 0`. -/
@[simp]
lemma edgeMonoSteps'_zero :
    E.edgeMonoSteps' pq r 0 = (E.pageXIsoOfEq pq _ _ (by simp)
      (by have := E.le₀_of_hasEdgeMonoAtFrom pq r; lia)).hom := rfl

/-- `edgeMonoSteps'` at `k + 1`. -/
@[simp]
lemma edgeMonoSteps'_succ (k : ℕ) :
    E.edgeMonoSteps' pq r (k + 1) =
      E.edgeMonoStep pq (r + k) (r + ((k + 1) : ℕ)) ≫ E.edgeMonoSteps' pq r k := rfl

/-- `edgeMonoSteps'` is a monomorphism. -/
instance (k : ℕ) : Mono (E.edgeMonoSteps' pq r k) := by
  induction k with
  | zero => rw [edgeMonoSteps'_zero]; infer_instance
  | succ => rw [edgeMonoSteps'_succ]; infer_instance

/-- The composition of the edge monomorphisms `E_{r'} ⟶ E_{r'-1} ⟶ ⋯ ⟶ E_r` at `pq`, for
`r ≤ r'` and `E.HasEdgeMonoAtFrom pq r`. -/
noncomputable def edgeMonoSteps (r' : ℤ) (h : r ≤ r' := by lia) :
    (E.page r' (by have := E.le₀_of_hasEdgeMonoAtFrom pq r; lia)).X pq ⟶
      (E.page r (E.le₀_of_hasEdgeMonoAtFrom pq r)).X pq :=
  (E.pageXIsoOfEq pq _ _ (by
    obtain ⟨k, rfl⟩ := Int.le.dest h
    simp) (by have := E.le₀_of_hasEdgeMonoAtFrom pq r; lia)).inv ≫
      E.edgeMonoSteps' pq r (Int.toNat (r' - r))

/-- `edgeMonoSteps` is a monomorphism. -/
instance (r' : ℤ) (h : r ≤ r') :
    Mono (E.edgeMonoSteps pq r r' h) := by
  dsimp [edgeMonoSteps]
  infer_instance

/-- `edgeMonoSteps` in terms of `edgeMonoSteps'`, for `r' = r + k`. -/
lemma edgeMonoSteps_eq (r' : ℤ) (k : ℕ) (h : r + k = r' := by lia) :
    E.edgeMonoSteps pq r r' (by lia) =
      (E.pageXIsoOfEq pq _ _ h (by
        have := E.le₀_of_hasEdgeMonoAtFrom pq r; lia)).inv ≫ E.edgeMonoSteps' pq r k := by
  obtain rfl : k = Int.toNat (r' - r) := by lia
  rfl

/-- `edgeMonoSteps` identifies to `edgeMonoSteps'`. -/
lemma edgeMonoSteps_eq_edgeMonoSteps' (k : ℕ) :
    E.edgeMonoSteps pq r (r + k) (by lia) =
      E.edgeMonoSteps' pq r k := by
  simp [E.edgeMonoSteps_eq pq r (r + k) k rfl, pageXIsoOfEq]

/-- `edgeMonoSteps` from `r` to `r` is the identity. -/
@[simp]
lemma edgeMonoSteps_eq_id :
    E.edgeMonoSteps pq r r (by rfl) = 𝟙 _ := by
  rw [E.edgeMonoSteps_eq pq r r 0 (by simp), edgeMonoSteps'_zero, Iso.inv_hom_id]

/-- `edgeMonoSteps` from `r` to `r' = r` is `pageXIsoOfEq`. -/
lemma edgeMonoSteps_eq_of_eq (r' : ℤ) (h : r = r' := by lia) :
    E.edgeMonoSteps pq r r' (by lia) =
    (E.pageXIsoOfEq pq r r' h (E.le₀_of_hasEdgeMonoAtFrom pq r)).inv := by
  subst h
  simp [pageXIsoOfEq]

/-- Reindexing `edgeMonoSteps` along an equality `r' = r''`. -/
lemma edgeMonoSteps_eq_pageXIsoOfEq_inv_comp_edgeMonoSteps
    (r' r'' : ℤ) (h₁ : r ≤ r' := by lia) (h₂ : r' = r'' := by lia) :
    E.edgeMonoSteps pq r r'' (by lia) =
      (E.pageXIsoOfEq pq r' r'' h₂ (by
        have := E.le₀_of_hasEdgeMonoAtFrom pq r
        lia)).inv ≫ E.edgeMonoSteps pq r r' h₁ := by
  subst h₂
  simp [pageXIsoOfEq]

/-- `edgeMonoSteps` splits off its last `edgeMonoStep`. -/
@[reassoc]
lemma edgeMonoSteps_eq_edgeMonoStep_comp_edgeMonoSteps
    (r' r'' : ℤ) (h₁ : r ≤ r' := by lia) (h₂ : r' + 1 = r'' := by lia)
    [E.HasEdgeMonoAt pq r'] :
    E.edgeMonoSteps pq r r'' (by lia) =
      E.edgeMonoStep pq r' r'' h₂ ≫ E.edgeMonoSteps pq r r' h₁ := by
  obtain ⟨k, rfl⟩ := Int.le.dest h₁
  obtain rfl : r'' = r + ((k + 1) : ℕ) := by lia
  rw [E.edgeMonoSteps_eq_edgeMonoSteps',
    E.edgeMonoSteps_eq_edgeMonoSteps', E.edgeMonoSteps'_succ]

/-- `edgeMonoSteps` from `r` to `r + 1` is `edgeMonoStep`. -/
lemma edgeMonoSteps_eq_edgeMonoStep
    (r' : ℤ) (h : r + 1 = r' := by lia) :
    E.edgeMonoSteps pq r r' (by lia) =
    E.edgeMonoStep pq r r' h := by
  rw [E.edgeMonoSteps_eq_edgeMonoStep_comp_edgeMonoSteps pq r r r' (by rfl) h,
    E.edgeMonoSteps_eq_id, comp_id]

/-- `edgeMonoSteps` is transitive. -/
@[reassoc (attr := simp)]
lemma edgeMonoSteps_comp (r' r'' : ℤ) [E.HasEdgeMonoAtFrom pq r']
    (hr' : r ≤ r' := by lia) (hr'' : r' ≤ r'' := by lia) :
    E.edgeMonoSteps pq r' r'' hr'' ≫ E.edgeMonoSteps pq r r' hr' =
      E.edgeMonoSteps pq r r'' (hr'.trans hr'') := by
  suffices ∀ (k : ℕ), E.edgeMonoSteps pq r' (r' + k) (by lia) ≫
      E.edgeMonoSteps pq r r' hr' =
        E.edgeMonoSteps pq r (r' + k) (by lia) by
    obtain ⟨k, rfl⟩ := Int.le.dest hr''
    apply this
  intro k
  induction k with
  | zero => rw [E.edgeMonoSteps_eq_of_eq pq r' (r' + Nat.zero) (by simp),
      E.edgeMonoSteps_eq_pageXIsoOfEq_inv_comp_edgeMonoSteps pq r r' (r' + Nat.zero) hr' (by simp)]
  | succ k hk =>
    rw [E.edgeMonoSteps_eq_edgeMonoStep_comp_edgeMonoSteps pq r' (r' + k) (r' + k.succ)
      (by simp) (by lia), assoc, hk,
      E.edgeMonoSteps_eq_edgeMonoStep_comp_edgeMonoSteps pq r (r' + k) (r' + k.succ) (by lia)
      (by lia)]

end

section

variable (pq : ι) (r : ℤ) [E.HasPageInfinityAt pq]

/-- All the differentials out of `pq` vanish from the page `r` on, i.e. `E.rFromMin pq ≤ r`. -/
class HasEdgeEpiAtFrom : Prop where
  /-- `E.rFromMin pq ≤ r` -/
  le : E.rFromMin pq ≤ r

/-- `E.HasEdgeEpiAtFrom pq (E.rFromMin pq)`. -/
instance : E.HasEdgeEpiAtFrom pq (E.rFromMin pq) where
  le := by rfl

/-- `E.HasEdgeEpiAtFrom pq (E.rMin pq)`. -/
instance : E.HasEdgeEpiAtFrom pq (E.rMin pq) where
  le := E.rFromMin_LE_rMin pq

/-- Constructor for `HasEdgeEpiAtFrom`. -/
lemma HasEdgeEpiAtFrom.mk' (hr : ∀ (k : ℕ), E.HasEdgeEpiAt pq (r + k))
    (hr : r₀ ≤ r := by lia) :
    E.HasEdgeEpiAtFrom pq r where
  le := E.rFromMin_LE _ _ ⟨hr, fun r' hr' ↦ by
    obtain ⟨k, rfl⟩ := Int.le.dest hr'
    infer_instance⟩

variable [E.HasEdgeEpiAtFrom pq r]

/-- `E.rFromMin pq ≤ r` when `E.HasEdgeEpiAtFrom pq r`. -/
lemma LE_of_hasEdgeEpiAtFrom : E.rFromMin pq ≤ r := by apply HasEdgeEpiAtFrom.le

include E pq in
/-- `r₀ ≤ r` when `E.HasEdgeEpiAtFrom pq r`. -/
lemma le₀_of_hasEdgeEpiAtFrom : r₀ ≤ r :=
  (E.LE_rFromMin pq).trans (E.LE_of_hasEdgeEpiAtFrom pq r)

/-- `r ∈ E.hasEdgeEpiSet pq` when `E.HasEdgeEpiAtFrom pq r`. -/
lemma mem_hasEdgeEpiSet : r ∈ E.hasEdgeEpiSet pq :=
  ⟨(E.LE_rFromMin pq).trans HasEdgeEpiAtFrom.le, fun _ hrr' ↦
    ⟨(E.le₀_of_hasEdgeEpiAtFrom pq r).trans hrr',
      fun _ ↦ E.d_from_eq_zero _ _ _ ((E.LE_of_hasEdgeEpiAtFrom pq r).trans hrr')⟩⟩

/-- `HasEdgeEpiAtFrom` is stable under increasing the page. -/
lemma hasEdgeEpiAtFrom_of_GE (r' : ℤ) (_ : r ≤ r' := by lia) :
    E.HasEdgeEpiAtFrom pq r' where
  le := by have := E.LE_of_hasEdgeEpiAtFrom pq r; lia

/-- `E.HasEdgeEpiAtFrom pq (max r r')` when `E.HasEdgeEpiAtFrom pq r`. -/
instance (r' : ℤ) :
    E.HasEdgeEpiAtFrom pq (max r r') :=
  E.hasEdgeEpiAtFrom_of_GE pq r _ (le_max_left _ _)

/-- `E.HasEdgeEpiAtFrom pq (max r' r)` when `E.HasEdgeEpiAtFrom pq r`. -/
instance (r' : ℤ) :
    E.HasEdgeEpiAtFrom pq (max r' r) :=
  E.hasEdgeEpiAtFrom_of_GE pq r _ (le_max_right _ _)

/-- `E.HasEdgeEpiAt pq r` when `E.HasEdgeEpiAtFrom pq r`. -/
instance : E.HasEdgeEpiAt pq r where
  le := E.le₀_of_hasEdgeEpiAtFrom pq r
  zero pq' := E.d_from_eq_zero r pq pq' (E.LE_of_hasEdgeEpiAtFrom pq r)

/-- `E.HasEdgeEpiAtFrom pq (r + k)` when `E.HasEdgeEpiAtFrom pq r`. -/
instance (k : ℕ) : E.HasEdgeEpiAtFrom pq (r + k) where
  le := by have := E.LE_of_hasEdgeEpiAtFrom pq r; lia

/-- `E.HasEdgeEpiAtFrom pq 3` when `E.HasEdgeEpiAtFrom pq 2`. -/
instance [E.HasEdgeEpiAtFrom pq 2] : E.HasEdgeEpiAtFrom pq 3 :=
  E.hasEdgeEpiAtFrom_of_GE pq 2 3

/-- Auxiliary definition for `edgeEpiSteps`. -/
noncomputable def edgeEpiSteps' (k : ℕ) :
    (E.page r (E.le₀_of_hasEdgeEpiAtFrom pq r)).X pq ⟶ (E.page (r + k) (by
      have := E.le₀_of_hasEdgeEpiAtFrom pq r
      lia)).X pq := by
  have := E.le₀_of_hasEdgeEpiAtFrom pq r
  induction k with
  | zero => exact (E.pageXIsoOfEq pq _ _ (by simp)).inv
  | succ k hk =>
    exact hk ≫ E.edgeEpiStep pq (r + k) (r + ((k + 1) : ℕ))

/-- `edgeEpiSteps'` at `k = 0`. -/
@[simp]
lemma edgeEpiSteps'_zero :
    E.edgeEpiSteps' pq r 0 = (E.pageXIsoOfEq pq _ _ (by simp) (by
      have := E.le₀_of_hasEdgeEpiAtFrom pq r
      lia)).inv := rfl

/-- `edgeEpiSteps'` at `k + 1`. -/
@[simp]
lemma edgeEpiSteps'_succ (k : ℕ) :
    E.edgeEpiSteps' pq r (k + 1) = E.edgeEpiSteps' pq r k ≫
      E.edgeEpiStep pq (r + k) (r + ((k + 1) : ℕ)) := rfl

/-- `edgeEpiSteps'` is an epimorphism. -/
instance (k : ℕ) : Epi (E.edgeEpiSteps' pq r k) := by
  induction k with
  | zero => rw [edgeEpiSteps'_zero]; infer_instance
  | succ => rw [edgeEpiSteps'_succ]; infer_instance

/-- The composition of the edge epimorphisms `E_r ⟶ E_{r+1} ⟶ ⋯ ⟶ E_{r'}` at `pq`, for
`r ≤ r'` and `E.HasEdgeEpiAtFrom pq r`. -/
noncomputable def edgeEpiSteps (r' : ℤ) (h : r ≤ r' := by lia) :
    (E.page r (E.le₀_of_hasEdgeEpiAtFrom pq r)).X pq ⟶
      (E.page r' (by have := E.le₀_of_hasEdgeEpiAtFrom pq r; lia)).X pq :=
  E.edgeEpiSteps' pq r (Int.toNat (r' - r)) ≫ (E.pageXIsoOfEq pq _ _ (by
    obtain ⟨k, rfl⟩ := Int.le.dest h
    simp) (by have := E.le₀_of_hasEdgeEpiAtFrom pq r; lia)).hom

/-- `edgeEpiSteps` is an epimorphism. -/
instance (r' : ℤ) (h : r ≤ r') :
    Epi (E.edgeEpiSteps pq r r' h) := by
  dsimp [edgeEpiSteps]
  infer_instance

/-- `edgeEpiSteps` in terms of `edgeEpiSteps'`, for `r' = r + k`. -/
lemma edgeEpiSteps_eq (r' : ℤ) (k : ℕ) (h : r + k = r' := by lia) :
    E.edgeEpiSteps pq r r' (by lia) =
      E.edgeEpiSteps' pq r k ≫ (E.pageXIsoOfEq pq _ _ h (by
        have := E.le₀_of_hasEdgeEpiAtFrom pq r
        lia)).hom := by
  obtain rfl : k = Int.toNat (r' - r) := by lia
  rfl

/-- `edgeEpiSteps` identifies to `edgeEpiSteps'`. -/
lemma edgeEpiSteps_eq_edgeEpiSteps' (k : ℕ) :
    E.edgeEpiSteps pq r (r + k) =
      E.edgeEpiSteps' pq r k := by
  simp [E.edgeEpiSteps_eq pq r (r + k) k rfl, pageXIsoOfEq]

/-- `edgeEpiSteps` from `r` to `r` is the identity. -/
@[simp]
lemma edgeEpiSteps_eq_id :
    E.edgeEpiSteps pq r r (by rfl) = 𝟙 _ := by
  rw [E.edgeEpiSteps_eq pq r r 0, edgeEpiSteps'_zero, Iso.inv_hom_id]

/-- `edgeEpiSteps` from `r` to `r' = r` is `pageXIsoOfEq`. -/
lemma edgeEpiSteps_eq_of_eq (r' : ℤ) (h : r = r' := by lia) :
    E.edgeEpiSteps pq r r' (by lia) =
    (E.pageXIsoOfEq pq r r' h (E.le₀_of_hasEdgeEpiAtFrom pq r)).hom := by
  subst h
  simp [pageXIsoOfEq]

/-- Reindexing `edgeEpiSteps` along an equality `r' = r''`. -/
@[reassoc]
lemma edgeEpiSteps_eq_edgeEpiSteps_comp_pageXIsoOfEq_hom
    (r' r'' : ℤ) (h₁ : r ≤ r' := by lia) (h₂ : r' = r'' := by lia) :
    E.edgeEpiSteps pq r r'' (by lia) =
    E.edgeEpiSteps pq r r' h₁ ≫ (E.pageXIsoOfEq pq r' r'' h₂ (by
      have := E.le₀_of_hasEdgeEpiAtFrom pq r
      lia)).hom := by
  subst h₂
  simp [pageXIsoOfEq]

/-- `edgeEpiSteps` splits off its last `edgeEpiStep`. -/
lemma edgeEpiSteps_eq_edgeEpiSteps_comp_edgeEpiStep
    (r' r'' : ℤ) (h₁ : r ≤ r' := by lia) (h₂ : r' + 1 = r'' := by lia)
    [E.HasEdgeEpiAt pq r'] :
    E.edgeEpiSteps pq r r'' (by lia) =
      E.edgeEpiSteps pq r r' h₁ ≫ E.edgeEpiStep pq r' r'' h₂ := by
  obtain ⟨k, rfl⟩ := Int.le.dest h₁
  obtain rfl : r'' = r + ((k + 1) : ℕ) := by lia
  rw [E.edgeEpiSteps_eq_edgeEpiSteps', E.edgeEpiSteps_eq_edgeEpiSteps',
    E.edgeEpiSteps'_succ]

/-- `edgeEpiSteps` from `r` to `r + 1` is `edgeEpiStep`. -/
lemma edgeEpiSteps_eq_edgeEpiStep (r' : ℤ) (h : r + 1 = r' := by lia) :
    E.edgeEpiSteps pq r r' (by lia) =
      E.edgeEpiStep pq r r' h := by
  rw [E.edgeEpiSteps_eq_edgeEpiSteps_comp_edgeEpiStep pq r r r' (by rfl) h,
    E.edgeEpiSteps_eq_id, id_comp]

/-- `edgeEpiSteps` is transitive. -/
@[reassoc (attr := simp)]
lemma edgeEpiSteps_comp (r' r'' : ℤ) [E.HasEdgeEpiAtFrom pq r']
    (hr' : r ≤ r' := by lia) (hr'' : r' ≤ r'' := by lia) :
    E.edgeEpiSteps pq r r' hr' ≫ E.edgeEpiSteps pq r' r'' hr'' =
      E.edgeEpiSteps pq r r'' (hr'.trans hr'') := by
  suffices ∀ (k : ℕ), E.edgeEpiSteps pq r r' hr' ≫
      E.edgeEpiSteps pq r' (r' + k) = E.edgeEpiSteps pq r (r' + k) by
    obtain ⟨k, rfl⟩ := Int.le.dest hr''
    apply this
  intro k
  induction k with
  | zero =>
    rw [E.edgeEpiSteps_eq_of_eq pq r' (r' + Nat.zero),
      E.edgeEpiSteps_eq_edgeEpiSteps_comp_pageXIsoOfEq_hom pq r r' (r' + Nat.zero)]
  | succ k hk =>
    rw [E.edgeEpiSteps_eq_edgeEpiSteps_comp_edgeEpiStep pq r' (r' + k) (r' + k.succ)
      (by simp) (by lia), reassoc_of% hk,
      E.edgeEpiSteps_eq_edgeEpiSteps_comp_edgeEpiStep pq r (r' + k) (r' + k.succ)]

end

/-- `edgeEpiSteps` followed by `edgeMonoSteps` is the identity. -/
@[reassoc (attr := simp)]
lemma edgeEpiSteps_edgeMonoSteps (pq : ι) (r r' : ℤ)
    [E.HasPageInfinityAt pq] [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r]
    (hrr' : r ≤ r' := by lia) :
    E.edgeEpiSteps pq r r' hrr' ≫ E.edgeMonoSteps pq r r' hrr' = 𝟙 _ := by
  suffices ∀ (k : ℕ), E.edgeEpiSteps pq r (r + k) ≫
      E.edgeMonoSteps pq r (r + k) = 𝟙 _ by
    obtain ⟨k, rfl⟩ := Int.le.dest hrr'
    apply this
  intro k
  induction k with
  | zero =>
    rw [E.edgeEpiSteps_eq_of_eq pq r (r + Nat.zero),
      E.edgeMonoSteps_eq_of_eq pq r (r + Nat.zero), Iso.hom_inv_id]
  | succ k hk =>
    rw [E.edgeEpiSteps_eq_edgeEpiSteps_comp_edgeEpiStep pq r (r + k) (r + k.succ),
      E.edgeMonoSteps_eq_edgeMonoStep_comp_edgeMonoSteps pq r (r + k) (r + k.succ),
      assoc, E.edgeEpiStep_edgeMonoStep_assoc pq (r + k) (r + k.succ) (by lia), hk]

/-- `edgeMonoSteps` followed by `edgeEpiSteps` is the identity. -/
@[reassoc (attr := simp)]
lemma edgeMonoSteps_edgeEpiSteps (pq : ι) (r r' : ℤ)
    [E.HasPageInfinityAt pq] [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r]
    (hrr' : r ≤ r' := by lia) :
    E.edgeMonoSteps pq r r' hrr' ≫ E.edgeEpiSteps pq r r' hrr' = 𝟙 _ := by
  rw [← cancel_mono (E.edgeMonoSteps pq r r' hrr'), assoc,
    E.edgeEpiSteps_edgeMonoSteps pq r r' hrr', comp_id, id_comp]

/-- When both `E.HasEdgeMonoAtFrom pq r` and `E.HasEdgeEpiAtFrom pq r` hold, the pages
`E_r` and `E_{r'}` at `pq` are isomorphic for `r ≤ r'`, via `edgeEpiSteps`/`edgeMonoSteps`. -/
@[simps]
noncomputable def edgeIsoSteps (pq : ι) (r r' : ℤ)
    [E.HasPageInfinityAt pq] [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r]
    (hrr' : r ≤ r' := by lia) :
    (E.page r (E.le₀_of_hasEdgeMonoAtFrom pq r)).X pq ≅ (E.page r' (by
      have := E.le₀_of_hasEdgeMonoAtFrom pq r
      lia)).X pq where
  hom := E.edgeEpiSteps pq r r' hrr'
  inv := E.edgeMonoSteps pq r r' hrr'

/-- The infinity page `E_∞^{pq}` of a spectral sequence at the position `pq`: the (stable) object
`(E.page (E.rMin pq)).X pq` when `E.HasPageInfinityAt pq`, and `0` otherwise. In the stabilising
case this is Stacks 011O's limit `E_∞ = Z_∞/B_∞`. -/
noncomputable def pageInfinity (pq : ι) : C := by
  by_cases E.HasPageInfinityAt pq
  · exact (E.page (E.rMin pq) (E.LE_rMin pq)).X pq
  · exact 0

section

variable (pq : ι) [E.HasPageInfinityAt pq]

/-- Auxiliary definition for `pageInfinityIso`. -/
noncomputable def pageInfinityIso' :
    E.pageInfinity pq ≅ (E.page (E.rMin pq) (E.LE_rMin pq)).X pq :=
  eqToIso (dite_eq_left (by infer_instance))

/-- `E.rMin pq ≤ r` when both `E.HasEdgeMonoAtFrom pq r` and `E.HasEdgeEpiAtFrom pq r` hold.
Not in upstream (which inlines `max_le` in `pageInfinityIso`): stating it separately gives the
proof stored in `pageInfinityIso` the syntactic type `E.rMin pq ≤ r`, which `simp` needs to apply
the `edgeIsoSteps` projection lemmas. -/
lemma rMin_LE (r : ℤ) [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r] :
    E.rMin pq ≤ r :=
  max_le (E.LE_of_hasEdgeMonoAtFrom pq r) (E.LE_of_hasEdgeEpiAtFrom pq r)

/-- The infinity page at `pq` is isomorphic to `(E.page r).X pq` for every page `r` from which
all the differentials into and out of `pq` vanish. -/
noncomputable def pageInfinityIso
    (r : ℤ) [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r] :
    E.pageInfinity pq ≅ (E.page r (E.le₀_of_hasEdgeEpiAtFrom pq r)).X pq :=
  E.pageInfinityIso' pq ≪≫ E.edgeIsoSteps pq (E.rMin pq) r (E.rMin_LE pq r)

/-- `pageInfinityIso` is compatible with `edgeEpiSteps`. -/
@[reassoc (attr := simp)]
lemma pageInfinityIso_hom_edgeEpiSteps
    (r r' : ℤ) (h : r ≤ r') [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r]
    [E.HasEdgeMonoAtFrom pq r'] [E.HasEdgeEpiAtFrom pq r'] :
    (E.pageInfinityIso pq r).hom ≫ E.edgeEpiSteps pq r r' h =
      (E.pageInfinityIso pq r').hom := by
  simp [pageInfinityIso]

/-- `pageInfinityIso` is compatible with `edgeEpiStep`. -/
lemma pageInfinityIso_hom_edgeEpiStep
    (r r' : ℤ) (h : r + 1 = r') [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r]
    [E.HasEdgeMonoAtFrom pq r'] [E.HasEdgeEpiAtFrom pq r'] :
    (E.pageInfinityIso pq r).hom ≫ E.edgeEpiStep pq r r' h =
      (E.pageInfinityIso pq r').hom := by
  rw [← E.edgeEpiSteps_eq_edgeEpiStep pq r r' h, pageInfinityIso_hom_edgeEpiSteps]

/-- `edgeEpiSteps` is compatible with `pageInfinityIso`. -/
@[reassoc (attr := simp)]
lemma edgeEpiSteps_pageInfinityIso_inv
    (r r' : ℤ) (h : r ≤ r') [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r]
    [E.HasEdgeMonoAtFrom pq r'] [E.HasEdgeEpiAtFrom pq r'] :
    E.edgeEpiSteps pq r r' h ≫ (E.pageInfinityIso pq r').inv =
      (E.pageInfinityIso pq r).inv := by
  simp [← cancel_epi (E.pageInfinityIso pq r).hom,
    pageInfinityIso_hom_edgeEpiSteps_assoc, Iso.hom_inv_id]

/-- `edgeEpiStep` is compatible with `pageInfinityIso`. -/
@[reassoc (attr := simp)]
lemma edgeEpiStep_pageInfinityIso_inv
    (r r' : ℤ) (h : r + 1 = r') [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r]
    [E.HasEdgeMonoAtFrom pq r'] [E.HasEdgeEpiAtFrom pq r'] :
    E.edgeEpiStep pq r r' h ≫ (E.pageInfinityIso pq r').inv =
      (E.pageInfinityIso pq r).inv := by
  rw [← E.edgeEpiSteps_eq_edgeEpiStep pq r r' h,
    edgeEpiSteps_pageInfinityIso_inv]

/-- `edgeMonoSteps` is compatible with `pageInfinityIso`. -/
@[reassoc (attr := simp)]
lemma edgeMonoSteps_pageInfinityIso_inv
    (r r' : ℤ) (h : r ≤ r') [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r]
    [E.HasEdgeMonoAtFrom pq r'] [E.HasEdgeEpiAtFrom pq r'] :
    E.edgeMonoSteps pq r r' h ≫ (E.pageInfinityIso pq r).inv =
      (E.pageInfinityIso pq r').inv := by
  simp [pageInfinityIso]

/-- `edgeMonoStep` is compatible with `pageInfinityIso`. -/
@[reassoc (attr := simp)]
lemma edgeMonoStep_pageInfinityIso_inv
    (r r' : ℤ) (h : r + 1 = r') [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r]
    [E.HasEdgeMonoAtFrom pq r'] [E.HasEdgeEpiAtFrom pq r'] :
    E.edgeMonoStep pq r r' h ≫ (E.pageInfinityIso pq r).inv =
      (E.pageInfinityIso pq r').inv := by
  rw [← E.edgeMonoSteps_eq_edgeMonoStep pq r r' h,
    edgeMonoSteps_pageInfinityIso_inv]

/-- `pageInfinityIso` is compatible with `edgeMonoSteps`. -/
@[reassoc (attr := simp)]
lemma pageInfinityIso_hom_edgeMonoSteps
    (r r' : ℤ) (h : r ≤ r') [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r]
    [E.HasEdgeMonoAtFrom pq r'] [E.HasEdgeEpiAtFrom pq r'] :
    (E.pageInfinityIso pq r').hom ≫ E.edgeMonoSteps pq r r' h =
      (E.pageInfinityIso pq r).hom := by
  simp [← cancel_mono (E.pageInfinityIso pq r).inv,
    assoc, edgeMonoSteps_pageInfinityIso_inv, Iso.hom_inv_id]

/-- `pageInfinityIso` is compatible with `edgeMonoStep`. -/
@[reassoc (attr := simp)]
lemma pageInfinityIso_hom_edgeMonoStep
    (r r' : ℤ) (h : r + 1 = r') [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r]
    [E.HasEdgeMonoAtFrom pq r'] [E.HasEdgeEpiAtFrom pq r'] :
    (E.pageInfinityIso pq r').hom ≫ E.edgeMonoStep pq r r' h =
      (E.pageInfinityIso pq r).hom := by
  rw [← E.edgeMonoSteps_eq_edgeMonoStep pq r r' h,
    pageInfinityIso_hom_edgeMonoSteps]

/-- Every page from `E.rMin pq` on has all differentials out of `pq` vanishing. -/
private lemma hasEdgeEpiAtFrom_of_rMin_LE (r : ℤ) (h : E.rMin pq ≤ r) :
    E.HasEdgeEpiAtFrom pq r :=
  ⟨(E.rFromMin_LE_rMin pq).trans h⟩

/-- Every page from `E.rMin pq` on has all differentials into `pq` vanishing. -/
private lemma hasEdgeMonoAtFrom_of_rMin_LE (r : ℤ) (h : E.rMin pq ≤ r) :
    E.HasEdgeMonoAtFrom pq r :=
  ⟨(E.rToMin_LE_rMin pq).trans h⟩

/-- The edge monomorphism `E_∞^{pq} ⟶ E_r^{pq}`, for `E.HasEdgeMonoAtFrom pq r`. -/
noncomputable def edgeMono (r : ℤ) [E.HasEdgeMonoAtFrom pq r] :
    E.pageInfinity pq ⟶ (E.page r (E.le₀_of_hasEdgeMonoAtFrom pq r)).X pq :=
  if h : r ≤ E.rMin pq
    then
      (E.pageInfinityIso' pq).hom ≫ E.edgeMonoSteps pq r _ h
    else
      have : E.HasEdgeEpiAtFrom pq r := ⟨by
        have := E.rFromMin_LE_rMin pq
        lia⟩
      (E.pageInfinityIso pq r).hom

/-- `edgeMono` is a monomorphism. -/
instance (r : ℤ) [E.HasEdgeMonoAtFrom pq r] :
    Mono (E.edgeMono pq r) := by
  dsimp [edgeMono]
  split_ifs <;> infer_instance

/-- `edgeMono` is compatible with `edgeMonoSteps`. -/
@[reassoc (attr := simp)]
lemma edgeMono_edgeMonoSteps (r r' : ℤ) (h : r ≤ r' := by lia)
    [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeMonoAtFrom pq r'] :
    E.edgeMono pq r' ≫ E.edgeMonoSteps pq r r' h =
      E.edgeMono pq r := by
  by_cases hr : r ≤ E.rMin pq
  · by_cases hr' : r' ≤ E.rMin pq
    · simp [edgeMono, dite_eq_left hr, dite_eq_left hr', assoc, edgeMonoSteps_comp]
    · have := E.hasEdgeEpiAtFrom_of_rMin_LE pq r' (by lia)
      simp only [edgeMono, dite_eq_left hr, dite_eq_right hr', pageInfinityIso, Iso.trans_hom,
        edgeIsoSteps_hom, assoc]
      rw [← E.edgeMonoSteps_comp pq r (E.rMin pq) r' hr (by lia),
        E.edgeEpiSteps_edgeMonoSteps_assoc pq (E.rMin pq) r' (by lia)]
  · have := E.hasEdgeEpiAtFrom_of_rMin_LE pq r (by lia)
    have := E.hasEdgeEpiAtFrom_of_rMin_LE pq r' (by lia)
    simp only [edgeMono, dite_eq_right hr, dite_eq_right (show ¬ r' ≤ E.rMin pq by lia)]
    exact E.pageInfinityIso_hom_edgeMonoSteps pq r r' h

/-- `edgeMono` is `pageInfinityIso` when both edge classes hold. -/
lemma edgeMono_eq_pageInfinityIso_hom (r : ℤ)
    [E.HasEdgeEpiAtFrom pq r] [E.HasEdgeMonoAtFrom pq r] :
    E.edgeMono pq r = (E.pageInfinityIso pq r).hom := by
  by_cases h : r ≤ E.rMin pq
  · rw [← E.pageInfinityIso_hom_edgeMonoSteps pq r (E.rMin pq) h]
    simp [edgeMono, dite_eq_left h, pageInfinityIso, Iso.trans_hom, edgeIsoSteps_hom,
      edgeEpiSteps_eq_id, comp_id]
  · simp [edgeMono, dite_eq_right h]

-- priority less than that of pageInfinityIso_hom_edgeMonoSteps
/-- `(E.pageInfinityIso pq r').hom ≫ E.edgeMonoSteps pq r r' h = E.edgeMono pq r`. -/
@[reassoc (attr := simp 900)]
lemma pageInfinityIso_hom_edgeMonoSteps' (r r' : ℤ) (h : r ≤ r' := by lia)
    [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeMonoAtFrom pq r'] [E.HasEdgeEpiAtFrom pq r'] :
    (E.pageInfinityIso pq r').hom ≫ E.edgeMonoSteps pq r r' h = E.edgeMono pq r := by
  rw [← E.edgeMono_edgeMonoSteps pq r r' h, E.edgeMono_eq_pageInfinityIso_hom pq r']

/-- `(E.pageInfinityIso pq r').hom ≫ E.edgeMonoStep pq r r' h = E.edgeMono pq r`. -/
@[reassoc (attr := simp 900)]
lemma pageInfinityIso_hom_edgeMonoStep' (r r' : ℤ) (h : r + 1 = r' := by lia)
    [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeMonoAtFrom pq r'] [E.HasEdgeEpiAtFrom pq r'] :
    (E.pageInfinityIso pq r').hom ≫ E.edgeMonoStep pq r r' h = E.edgeMono pq r := by
  have := E.le₀_of_hasEdgeMonoAtFrom pq r
  rw [← E.edgeMonoSteps_eq_edgeMonoStep _ _ _, E.pageInfinityIso_hom_edgeMonoSteps' _ _ _]

/-- The edge epimorphism `E_r^{pq} ⟶ E_∞^{pq}`, for `E.HasEdgeEpiAtFrom pq r`. -/
noncomputable def edgeEpi (r : ℤ) [E.HasEdgeEpiAtFrom pq r] :
    (E.page r (E.le₀_of_hasEdgeEpiAtFrom pq r)).X pq ⟶ E.pageInfinity pq :=
  if h : r ≤ E.rMin pq
    then
      E.edgeEpiSteps pq r _ h ≫ (E.pageInfinityIso' pq).inv
    else
      have : E.HasEdgeMonoAtFrom pq r := ⟨by
        have := E.rToMin_LE_rMin pq
        lia⟩
      (E.pageInfinityIso pq r).inv

/-- `edgeEpi` is an epimorphism. -/
instance (r : ℤ) [E.HasEdgeEpiAtFrom pq r] :
    Epi (E.edgeEpi pq r) := by
  dsimp [edgeEpi]
  split_ifs <;> infer_instance

/-- `edgeEpiSteps` is compatible with `edgeEpi`. -/
@[reassoc (attr := simp)]
lemma edgeEpiSteps_edgeEpi (r r' : ℤ) (h : r ≤ r')
    [E.HasEdgeEpiAtFrom pq r] [E.HasEdgeEpiAtFrom pq r'] :
    E.edgeEpiSteps pq r r' h ≫ E.edgeEpi pq r' = E.edgeEpi pq r := by
  by_cases hr : r ≤ E.rMin pq
  · by_cases hr' : r' ≤ E.rMin pq
    · simp [edgeEpi, dite_eq_left hr, dite_eq_left hr', edgeEpiSteps_comp_assoc]
    · have := E.hasEdgeMonoAtFrom_of_rMin_LE pq r' (by lia)
      simp only [edgeEpi, dite_eq_left hr, dite_eq_right hr', pageInfinityIso, Iso.trans_inv,
        edgeIsoSteps_inv]
      rw [← E.edgeEpiSteps_comp pq r (E.rMin pq) r' hr (by lia), assoc,
        E.edgeEpiSteps_edgeMonoSteps_assoc pq (E.rMin pq) r' (by lia)]
  · have := E.hasEdgeMonoAtFrom_of_rMin_LE pq r (by lia)
    have := E.hasEdgeMonoAtFrom_of_rMin_LE pq r' (by lia)
    simp only [edgeEpi, dite_eq_right hr, dite_eq_right (show ¬ r' ≤ E.rMin pq by lia)]
    exact E.edgeEpiSteps_pageInfinityIso_inv pq r r' h

/-- `edgeEpi` is `pageInfinityIso` when both edge classes hold. -/
lemma edgeEpi_eq_pageInfinityIso_inv (r : ℤ)
    [E.HasEdgeEpiAtFrom pq r] [E.HasEdgeMonoAtFrom pq r] :
    E.edgeEpi pq r = (E.pageInfinityIso pq r).inv := by
  by_cases h : r ≤ E.rMin pq
  · rw [← E.edgeEpiSteps_pageInfinityIso_inv pq r (E.rMin pq) h]
    simp [edgeEpi, dite_eq_left h, pageInfinityIso, Iso.trans_inv, edgeIsoSteps_inv,
      edgeMonoSteps_eq_id, id_comp]
  · simp [edgeEpi, dite_eq_right h]

-- priority less than that of edgeEpiSteps_pageInfinityIso_inv
/-- `E.edgeEpiSteps pq r r' h ≫ (E.pageInfinityIso pq r').inv = E.edgeEpi pq r`. -/
@[reassoc (attr := simp 900)]
lemma edgeEpiSteps_pageInfinityIso_inv' (r r' : ℤ) (h : r ≤ r')
    [E.HasEdgeEpiAtFrom pq r] [E.HasEdgeMonoAtFrom pq r'] [E.HasEdgeEpiAtFrom pq r'] :
    E.edgeEpiSteps pq r r' h ≫ (E.pageInfinityIso pq r').inv = E.edgeEpi pq r := by
  rw [← E.edgeEpiSteps_edgeEpi pq r r' h, E.edgeEpi_eq_pageInfinityIso_inv pq r']

/-- `E.edgeEpiStep pq r r' h ≫ (E.pageInfinityIso pq r').inv = E.edgeEpi pq r`. -/
@[reassoc (attr := simp 900)]
lemma edgeEpiStep_pageInfinityIso_inv' (r r' : ℤ) (h : r + 1 = r')
    [E.HasEdgeEpiAtFrom pq r] [E.HasEdgeMonoAtFrom pq r'] [E.HasEdgeEpiAtFrom pq r'] :
    E.edgeEpiStep pq r r' h ≫ (E.pageInfinityIso pq r').inv =
    E.edgeEpi pq r := by
  rw [← E.edgeEpiSteps_eq_edgeEpiStep _ _ _ h, edgeEpiSteps_pageInfinityIso_inv']

end

namespace Hom

variable {E}
variable {E' : SpectralSequence C c r₀} (f : E ⟶ E')

/-- The morphism induced on the infinity pages by a morphism of spectral sequences (zero when
either side has no infinity page at `pq`). -/
noncomputable def mapPageInfinity (pq : ι) :
    E.pageInfinity pq ⟶ E'.pageInfinity pq := by
  by_cases E.HasPageInfinityAt pq
  · by_cases E'.HasPageInfinityAt pq
    · exact (E.pageInfinityIso pq _).hom ≫ (f.hom (max (E.rMin pq) (E'.rMin pq))
        ((E.LE_rMin pq).trans (le_max_left _ _))).f pq ≫
        (E'.pageInfinityIso pq _).inv
    · exact 0
  · exact 0

-- TODO: naturality of edgeEpiStep(s)

/-- Naturality of `edgeMonoStep`. -/
@[reassoc]
lemma edgeMonoStep_naturality (pq : ι) (r r' : ℤ) [E.HasEdgeMonoAt pq r] [E'.HasEdgeMonoAt pq r]
    (hrr' : r + 1 = r' := by lia) (hr : r₀ ≤ r := by lia) :
    E.edgeMonoStep pq r r' hrr' ≫ (f.hom r).f pq =
      (f.hom r').f pq ≫ E'.edgeMonoStep pq r r' hrr' := by
  rw [← cancel_epi (E.iso r r' pq hrr').hom, iso_hom_comp_edgeMonoStep_assoc _ _ _ _,
    ← cancel_epi ((E.page r).isoHomologyπ _ pq rfl (by simp)).hom,
    HomologicalComplex.isoHomologyπ_hom, HomologicalComplex.isoHomologyπ_hom_inv_id_assoc,
    ← Hom.comm_assoc f r r' pq hrr', iso_hom_comp_edgeMonoStep _ _ _ _,
    HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.isoHomologyπ_hom_inv_id_assoc, HomologicalComplex.cyclesMap_i]

/-- Naturality of `edgeMonoSteps`. -/
@[reassoc]
lemma edgeMonoSteps_naturality (pq : ι) (r r' : ℤ)
    (hrr' : r ≤ r' := by lia) (hr₀ : r₀ ≤ r := by lia)
    [E.HasPageInfinityAt pq] [E'.HasPageInfinityAt pq]
    [E.HasEdgeMonoAtFrom pq r] [E'.HasEdgeMonoAtFrom pq r] :
    E.edgeMonoSteps pq r r' hrr' ≫ (f.hom r).f pq =
      (f.hom r').f pq ≫ E'.edgeMonoSteps pq r r' hrr' := by
  obtain ⟨k, hk⟩ := Int.le.dest hrr'
  revert r'
  induction k with
  | zero =>
    intro r' hrr' hr₀
    obtain rfl : r = r' := by omega
    simp
  | succ k hk =>
    intro r' hrr' hr₀
    rw [E.edgeMonoSteps_eq_edgeMonoStep_comp_edgeMonoSteps pq r (r + k) r',
      assoc, hk (r + k) (by lia) rfl, edgeMonoStep_naturality_assoc _ _ _ _ _ (by lia),
      E'.edgeMonoSteps_eq_edgeMonoStep_comp_edgeMonoSteps pq r (r + k) r']

/-- `mapPageInfinity` computed on any page `r` where both infinity pages are reached. -/
lemma mapPageInfinity_eq (pq : ι) (r : ℤ)
    [E.HasPageInfinityAt pq] [E'.HasPageInfinityAt pq]
    [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r]
    [E'.HasEdgeMonoAtFrom pq r] [E'.HasEdgeEpiAtFrom pq r] (hr : r₀ ≤ r := by lia) :
    mapPageInfinity f pq =
      (E.pageInfinityIso pq r).hom ≫ (f.hom r).f pq ≫ (E'.pageInfinityIso pq r).inv := by
  set r' := max (E.rMin pq) (E'.rMin pq)
  have hrr' : r' ≤ r := max_le
    (max_le (E.LE_of_hasEdgeMonoAtFrom pq r) (E.LE_of_hasEdgeEpiAtFrom pq r))
    (max_le (E'.LE_of_hasEdgeMonoAtFrom pq r) (E'.LE_of_hasEdgeEpiAtFrom pq r))
  have : r₀ ≤ r' := (E.LE_rMin pq).trans (le_max_left _ _)
  dsimp [mapPageInfinity]
  rw [dite_eq_left (by infer_instance), dite_eq_left (by infer_instance),
    ← E.pageInfinityIso_hom_edgeEpiSteps pq r' r hrr',
    ← E'.edgeMonoSteps_pageInfinityIso_inv pq r' r hrr', assoc,
    ← edgeMonoSteps_naturality_assoc _ _ _ _ ,
    edgeEpiSteps_edgeMonoSteps_assoc _ _ _ _]

/-- `mapPageInfinity f` is an isomorphism as soon as `f` is an isomorphism on some page. -/
lemma isIso_mapPageInfinity_of_isIso_hom (r : ℤ) (pq : ι) {hr : r₀ ≤ r}
    (hf : IsIso (f.hom r hr)) [E.HasPageInfinityAt pq] [E'.HasPageInfinityAt pq] :
    IsIso (mapPageInfinity f pq) := by
  let r' := max r (max (E.rMin pq) (E'.rMin pq))
  have hr' : r₀ ≤ r' := hr.trans (le_max_left _ _)
  rw [mapPageInfinity_eq f pq r']
  have := isIso_hom_of_GE f r r' (le_max_left _ _) hf
  infer_instance

end Hom

end SpectralSequence

namespace CohomologicalSpectralSequenceNat

section

variable (E : CohomologicalSpectralSequenceNat C r₀)

/-- In a first quadrant cohomological spectral sequence, the differentials out of `pq` vanish
on the page `r` as soon as `pq.2 + 2 ≤ r`. -/
lemma hasEdgeEpiAt
    (pq : ℕ × ℕ) (r : ℤ) (hpq : pq.2 + 2 ≤ r := by lia) (hr₀ : r₀ ≤ r := by lia) :
    E.HasEdgeEpiAt pq r where
  zero pq' := by
    apply HomologicalComplex.shape
    intro h
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at h
    lia

/-- In a first quadrant cohomological spectral sequence, the differentials into `pq` vanish
on the page `r` as soon as `pq.1 + 1 ≤ r`. -/
lemma hasEdgeMonoAt
    (pq : ℕ × ℕ) (r : ℤ) (hpq : pq.1 + 1 ≤ r := by lia) (hr₀ : r₀ ≤ r := by lia) :
    E.HasEdgeMonoAt pq r where
  zero pq' := by
    apply HomologicalComplex.shape
    intro h
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at h
    lia

/-- A first quadrant cohomological spectral sequence has an infinity page everywhere. -/
instance (pq : ℕ × ℕ) : E.HasPageInfinityAt pq where
  nonempty_hasEdgeEpiSet :=
    ⟨max r₀ (pq.2 + 2), ⟨le_max_left _ _, fun _ hr ↦
      E.hasEdgeEpiAt _ _ ((le_max_right _ _).trans hr) ((le_max_left _ _).trans hr)⟩⟩
  nonempty_hasEdgeMonoSet :=
    ⟨max r₀ (pq.1 + 1), ⟨le_max_left _ _, fun _ hr ↦
      E.hasEdgeMonoAt _ _ ((le_max_right _ _).trans hr) ((le_max_left _ _).trans hr)⟩⟩

/-- `E.HasEdgeEpiAtFrom pq r` as soon as `pq.2 + 2 ≤ r`, in the first quadrant case. -/
lemma hasEdgeEpiAtFrom
    (pq : ℕ × ℕ) (r : ℤ) (hpq : pq.2 + 2 ≤ r := by lia) (hr₀ : r₀ ≤ r := by lia) :
    E.HasEdgeEpiAtFrom pq r where
  le := E.rFromMin_LE _ _ ⟨hr₀, fun r' hrr' ↦ hasEdgeEpiAt _ _ _⟩

/-- `E.HasEdgeMonoAtFrom pq r` as soon as `pq.1 + 1 ≤ r`, in the first quadrant case. -/
lemma hasEdgeMonoAtFrom
    (pq : ℕ × ℕ) (r : ℤ) (hpq : pq.1 + 1 ≤ r := by lia) (hr₀ : r₀ ≤ r := by lia) :
    E.HasEdgeMonoAtFrom pq r where
  le := E.rToMin_LE _ _ ⟨hr₀, fun _ _ ↦ hasEdgeMonoAt _ _ _⟩

end

section

variable (E : CohomologicalSpectralSequenceNat C 2)

/-- Edge epimorphisms from the bottom row of a first quadrant `E₂`-spectral sequence. -/
instance (p : ℕ) : E.HasEdgeEpiAtFrom ⟨p, 0⟩ 2 :=
  hasEdgeEpiAtFrom _ _ _

/-- Edge epimorphisms from the second row of a first quadrant `E₂`-spectral sequence. -/
instance (p : ℕ) : E.HasEdgeEpiAtFrom ⟨p, 1⟩ 3 :=
  hasEdgeEpiAtFrom _ _ _

/-- Edge monomorphisms into the first column of a first quadrant `E₂`-spectral sequence. -/
instance (q : ℕ) : E.HasEdgeMonoAtFrom ⟨0, q⟩ 2 :=
  hasEdgeMonoAtFrom _ _ _

/-- Edge monomorphisms into the second column of a first quadrant `E₂`-spectral sequence. -/
instance (q : ℕ) : E.HasEdgeMonoAtFrom ⟨1, q⟩ 2 :=
  hasEdgeMonoAtFrom _ _ _

/-- Edge monomorphisms into the third column of a first quadrant `E₂`-spectral sequence. -/
instance (q : ℕ) : E.HasEdgeMonoAtFrom ⟨2, q⟩ 3 :=
  hasEdgeMonoAtFrom _ _ _

end

section

variable (E : CohomologicalSpectralSequenceNat C 1)

/-- Edge epimorphisms from the bottom row of a first quadrant `E₁`-spectral sequence. -/
instance (p : ℕ) : E.HasEdgeEpiAtFrom ⟨p, 0⟩ 2 :=
  hasEdgeEpiAtFrom _ _ _

/-- Edge epimorphisms from the second row of a first quadrant `E₁`-spectral sequence. -/
instance (p : ℕ) : E.HasEdgeEpiAtFrom ⟨p, 1⟩ 3 :=
  hasEdgeEpiAtFrom _ _ _

/-- Edge monomorphisms into the first column of a first quadrant `E₁`-spectral sequence,
from the first page on. -/
instance (q : ℕ) : E.HasEdgeMonoAtFrom ⟨0, q⟩ 1 :=
  hasEdgeMonoAtFrom _ _ _

/-- Edge monomorphisms into the first column of a first quadrant `E₁`-spectral sequence. -/
instance (q : ℕ) : E.HasEdgeMonoAtFrom ⟨0, q⟩ 2 :=
  hasEdgeMonoAtFrom _ _ _

/-- Edge monomorphisms into the second column of a first quadrant `E₁`-spectral sequence. -/
instance (q : ℕ) : E.HasEdgeMonoAtFrom ⟨1, q⟩ 2 :=
  hasEdgeMonoAtFrom _ _ _

/-- Edge monomorphisms into the third column of a first quadrant `E₁`-spectral sequence. -/
instance (q : ℕ) : E.HasEdgeMonoAtFrom ⟨2, q⟩ 3 :=
  hasEdgeMonoAtFrom _ _ _

end

end CohomologicalSpectralSequenceNat

end CategoryTheory
