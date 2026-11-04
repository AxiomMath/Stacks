module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsTo
public import StacksFrontier.Algebra.Homology.SpectralSequence.Boundedness

/-!
# Degeneration of a spectral sequence detected by lengths

Let `ℓ` be a function on the objects of an abelian category `C` with values in `ℕ∞` which is
additive on short exact sequences and vanishes exactly on the zero objects: for instance the
length of modules over a ring, or, on modules over an algebra over a field `k`, the dimension
over `k` (with value `⊤` on infinite-dimensional modules).

Every page of a spectral sequence is a subquotient of the previous one, so
`ℓ(E_{r + 1}^{p, q}) ≤ ℓ(E_r^{p, q})`, and if `E` abuts to `H` then `ℓ(H^n)` is the sum of the
`ℓ(E_∞^{p, n - p})`. Hence `ℓ(H^n) ≤ ∑_{p + q = n} ℓ(E_r^{p, q})` for every page `r`, and the
main result of this file says that, for a bounded spectral sequence whose page `r₁` has finite
lengths, equality for every `n` holds exactly when the spectral sequence *degenerates at `E_{r₁}`*,
i.e. all the differentials `d_r` with `r ≥ r₁` vanish.

This is the argument by which the equality of the Betti numbers of de Rham and of Hodge
cohomology forces the Hodge-to-de Rham spectral sequence to degenerate at `E_1`
([Stacks, Tag 0FWE]).

## Main results

* `CategoryTheory.SpectralSequence.length_page_le_of_additive`:
  `ℓ(E_{r'}^{p, q}) ≤ ℓ(E_r^{p, q})` for `r ≤ r'`.
* `CategoryTheory.SpectralSequence.AbutsTo.length_eq_finsum`: if `E` abuts to `H`, then
  `ℓ(H^n) = ∑_p ℓ(E_∞^{p, n - p})`.
* `CategoryTheory.SpectralSequence.degeneratesFrom_iff_length_eq_finsum`: a bounded spectral
  sequence abutting to `H`, with finite lengths on page `r₁`, degenerates at `E_{r₁}` if and only
  if `ℓ(H^n) = ∑_{p + q = n} ℓ(E_{r₁}^{p, q})` for every `n`.

## References

* [Stacks Project, Tag 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type*} [Category* C] [Abelian C] {ℓ : C → ℕ∞}

/-- In `ℕ∞`, `a = a + b` with `a` finite forces `b = 0`. -/
lemma _root_.ENat.eq_zero_of_eq_add_right {a b : ℕ∞} (ha : a ≠ ⊤) (h : a = a + b) : b = 0 := by
  lift a to ℕ using ha
  induction b using ENat.recTopCoe with
  | top => simp at h
  | coe b =>
    norm_cast at h ⊢
    omega

namespace Abelian

section Length

variable (hℓ : ∀ S : ShortComplex C, S.ShortExact → ℓ S.X₂ = ℓ S.X₁ + ℓ S.X₃)
  (hℓ0 : ∀ X : C, ℓ X = 0 ↔ IsZero X)

include hℓ

/-- An additive function on short exact sequences, applied to `X ⟶ Y ⟶ coker f` for a
monomorphism `f`. -/
lemma length_eq_add_length_cokernel {X Y : C} (f : X ⟶ Y) [Mono f] :
    ℓ Y = ℓ X + ℓ (cokernel f) :=
  hℓ _ (ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact f)
    (inferInstanceAs (Mono f)) inferInstance)

/-- An additive function on short exact sequences, applied to `ker g ⟶ X ⟶ Y` for an
epimorphism `g`. -/
lemma length_eq_length_kernel_add {X Y : C} (g : X ⟶ Y) [Epi g] :
    ℓ X = ℓ (kernel g) + ℓ Y :=
  hℓ _ (ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact g)
    inferInstance (inferInstanceAs (Epi g)))

include hℓ0

omit hℓ [Abelian C] in
/-- A length function vanishes on zero objects. -/
lemma length_eq_zero_of_isZero {X : C} (hX : IsZero X) : ℓ X = 0 :=
  (hℓ0 X).2 hX

/-- A length function is invariant under isomorphism. -/
lemma length_eq_of_iso {X Y : C} (e : X ≅ Y) : ℓ X = ℓ Y := by
  rw [length_eq_add_length_cokernel hℓ e.hom,
    length_eq_zero_of_isZero hℓ0 (isZero_cokernel_of_epi e.hom), add_zero]

omit hℓ0 in
/-- A length function does not decrease along monomorphisms. -/
lemma length_le_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] : ℓ X ≤ ℓ Y := by
  rw [length_eq_add_length_cokernel hℓ f]
  exact le_self_add

omit hℓ0 in
/-- A length function does not increase along epimorphisms. -/
lemma length_le_of_epi {X Y : C} (g : X ⟶ Y) [Epi g] : ℓ Y ≤ ℓ X := by
  rw [length_eq_length_kernel_add hℓ g]
  exact le_add_self

/-- A monomorphism between objects of the same finite length is an isomorphism. -/
lemma isIso_of_mono_of_length_eq {X Y : C} (f : X ⟶ Y) [Mono f] (hY : ℓ Y ≠ ⊤)
    (h : ℓ X = ℓ Y) : IsIso f := by
  have hc : ℓ (cokernel f) = 0 := by
    have e := length_eq_add_length_cokernel hℓ f
    rw [h] at e
    exact ENat.eq_zero_of_eq_add_right hY e
  have := Preadditive.epi_of_isZero_cokernel f ((hℓ0 _).1 hc)
  exact isIso_of_mono_of_epi f

/-- An epimorphism between objects of the same finite length is an isomorphism. -/
lemma isIso_of_epi_of_length_eq {X Y : C} (g : X ⟶ Y) [Epi g] (hX : ℓ X ≠ ⊤)
    (h : ℓ X = ℓ Y) : IsIso g := by
  have hk : ℓ (kernel g) = 0 := by
    have e := length_eq_length_kernel_add hℓ g
    rw [← h, add_comm] at e
    exact ENat.eq_zero_of_eq_add_right hX e
  have := Preadditive.mono_of_isZero_kernel g ((hℓ0 _).1 hk)
  exact isIso_of_mono_of_epi g

omit hℓ0 in
/-- The length of the homology of a complex at `i` is at most the length of its term at `i`. -/
lemma length_homology_le {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex C c) (i : ι) :
    ℓ (K.homology i) ≤ ℓ (K.X i) :=
  (length_le_of_epi hℓ (K.homologyπ i)).trans (length_le_of_mono hℓ (K.iCycles i))

/-- If the homology of a complex at `i` has the same finite length as its term at `i`, then the
differentials out of and into `i` vanish. -/
lemma d_eq_zero_of_length_homology_eq {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex C c) (i : ι) (hfin : ℓ (K.X i) ≠ ⊤)
    (h : ℓ (K.homology i) = ℓ (K.X i)) :
    (∀ j, K.d i j = 0) ∧ ∀ j, K.d j i = 0 := by
  have h₁ := length_le_of_epi hℓ (K.homologyπ i)
  have h₂ := length_le_of_mono hℓ (K.iCycles i)
  have hc : ℓ (K.cycles i) = ℓ (K.X i) := le_antisymm h₂ (h ▸ h₁)
  have hh : ℓ (K.cycles i) = ℓ (K.homology i) := by rw [hc, h]
  have := isIso_of_mono_of_length_eq hℓ hℓ0 (K.iCycles i) hfin hc
  have := isIso_of_epi_of_length_eq hℓ hℓ0 (K.homologyπ i) (hc ▸ hfin) hh
  refine ⟨fun j => ?_, fun j => ?_⟩
  · rw [← cancel_epi (K.iCycles i), K.iCycles_d, comp_zero]
  · have : K.toCycles j i = 0 := by
      rw [← cancel_mono (K.homologyπ i), K.toCycles_comp_homologyπ, zero_comp]
    rw [← K.toCycles_i, this, zero_comp]

/-- If the differentials out of and into `i` vanish, the homology at `i` has the length of the
term at `i`. -/
lemma length_homology_eq_of_d_eq_zero {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex C c) (i : ι) (h₁ : ∀ j, K.d i j = 0) (h₂ : ∀ j, K.d j i = 0) :
    ℓ (K.homology i) = ℓ (K.X i) := by
  have := K.isIso_iCycles i (c.next i) rfl (h₁ _)
  have := K.isIso_homologyπ (c.prev i) i rfl (h₂ _)
  exact (length_eq_of_iso hℓ hℓ0 (asIso (K.homologyπ i))).symm.trans
    (length_eq_of_iso hℓ hℓ0 (asIso (K.iCycles i)))

omit hℓ0 in
/-- For subobjects `S ≤ T` of an object, `ℓ(T) = ℓ(S) + ℓ(T/S)`. -/
lemma length_subobject_eq_add {Y : C} (S T : Subobject Y) (h : S ≤ T) :
    ℓ (T : C) = ℓ (S : C) + ℓ (cokernel (Subobject.ofLE S T h)) :=
  length_eq_add_length_cokernel hℓ _

/-- **Lengths are additive along a finite filtration.** If `F` is a decreasing filtration of `Y`
by subobjects with `F a = ⊤` and `F b = ⊥`, then `ℓ(Y)` is the sum over `p` of the lengths of the
graded pieces `F p / F (p + 1)`. -/
lemma length_eq_finsum_of_antitone {Y : C} (F : ℤ → Subobject Y) (hF : Antitone F) {a b : ℤ}
    (hab : a ≤ b) (ha : F a = ⊤) (hb : F b = ⊥) :
    ℓ Y = ∑ᶠ p : ℤ, ℓ (cokernel (Subobject.ofLE (F (p + 1)) (F p) (hF (by omega)))) := by
  set g : ℤ → ℕ∞ := fun p => ℓ (cokernel (Subobject.ofLE (F (p + 1)) (F p) (hF (by omega))))
    with hg
  have hzero : ∀ p, F (p + 1) = F p → g p = 0 := by
    intro p hp
    have key : ∀ (S T : Subobject Y) (h : S ≤ T), S = T →
        ℓ (cokernel (Subobject.ofLE S T h)) = 0 := by
      rintro S T h rfl
      rw [Subobject.ofLE_refl]
      exact length_eq_zero_of_isZero hℓ0 (isZero_cokernel_of_epi _)
    exact key _ _ _ hp
  have hsupp : Function.support g ⊆ (Finset.Ico a b : Set ℤ) := by
    intro p hp
    simp only [Finset.coe_Ico, Set.mem_Ico]
    by_contra hlt
    apply hp
    apply hzero
    rcases not_and_or.1 hlt with h | h
    · have h1 : F (p + 1) = ⊤ := top_le_iff.1 (ha ▸ hF (by omega))
      have h2 : F p = ⊤ := top_le_iff.1 (ha ▸ hF (by omega))
      rw [h1, h2]
    · have h1 : F (p + 1) = ⊥ := le_bot_iff.1 (hb ▸ hF (by omega))
      have h2 : F p = ⊥ := le_bot_iff.1 (hb ▸ hF (by omega))
      rw [h1, h2]
  have htel : ∀ k : ℕ, ℓ (F a : C) = (∑ i ∈ Finset.range k, g (a + i)) + ℓ (F (a + k) : C) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [ih, Finset.sum_range_succ, add_assoc]
      congr 1
      rw [length_subobject_eq_add hℓ (F (a + k + 1)) (F (a + k)) (hF (by omega)), add_comm]
      push_cast
      rw [← add_assoc]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, b = a + k := ⟨(b - a).toNat, by omega⟩
  have hY : ℓ Y = ℓ (F a : C) := by
    rw [ha]
    exact (length_eq_of_iso hℓ hℓ0 (asIso (⊤ : Subobject Y).arrow)).symm
  have hbot : ℓ (F (a + k) : C) = 0 := by
    rw [← hk, hb]
    exact length_eq_zero_of_isZero hℓ0 (Subobject.botCoeIsoZero.isZero_iff.2 (isZero_zero C))
  rw [hY, htel k, hbot, add_zero, finsum_eq_sum_of_support_subset g hsupp]
  have hmap : Finset.Ico a b =
      (Finset.range k).map (Nat.castEmbedding.trans (addLeftEmbedding a)) := by
    ext p
    simp only [Finset.mem_Ico, Finset.mem_map, Finset.mem_range, Function.Embedding.trans_apply,
      Nat.castEmbedding_apply, addLeftEmbedding_apply]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(p - a).toNat, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      omega
  rw [hmap, Finset.sum_map]
  rfl

end Length

/-- If `f ≤ g` pointwise on a finite set, `g` takes finite values there and the sums agree, then
`f = g` on that set. -/
lemma _root_.ENat.eq_of_sum_eq_sum_of_le {ι : Type*} {s : Finset ι} {f g : ι → ℕ∞}
    (hle : ∀ i ∈ s, f i ≤ g i) (hfin : ∀ i ∈ s, g i ≠ ⊤)
    (hsum : ∑ i ∈ s, f i = ∑ i ∈ s, g i) : ∀ i ∈ s, f i = g i := by
  have hf : ∀ i ∈ s, f i = ((f i).toNat : ℕ∞) := fun i hi =>
    (ENat.coe_toNat (ne_top_of_le_ne_top (hfin i hi) (hle i hi))).symm
  have hg : ∀ i ∈ s, g i = ((g i).toNat : ℕ∞) := fun i hi => (ENat.coe_toNat (hfin i hi)).symm
  rw [Finset.sum_congr rfl hf, Finset.sum_congr rfl hg, ← Nat.cast_sum, ← Nat.cast_sum,
    Nat.cast_inj] at hsum
  have hle' : ∀ i ∈ s, (f i).toNat ≤ (g i).toNat := fun i hi =>
    ENat.toNat_le_toNat (hle i hi) (hfin i hi)
  intro i hi
  rw [hf i hi, hg i hi, (Finset.sum_eq_sum_iff_of_le hle').1 hsum i hi]

end Abelian

namespace SpectralSequence

open Abelian

variable {r₀ : ℤ} (E : CohomologicalSpectralSequence C r₀)
  (hℓ : ∀ S : ShortComplex C, S.ShortExact → ℓ S.X₂ = ℓ S.X₁ + ℓ S.X₃)
  (hℓ0 : ∀ X : C, ℓ X = 0 ↔ IsZero X)

include hℓ hℓ0

/-- Each page of a spectral sequence is a subquotient of the previous one, so lengths do not
increase from one page to the next. -/
lemma length_page_succ_le_of_additive (r : ℤ) (hr : r₀ ≤ r) (pq : ℤ × ℤ) :
    ℓ ((E.page (r + 1)).X pq) ≤ ℓ ((E.page r).X pq) := by
  rw [← length_eq_of_iso hℓ hℓ0 (E.iso r (r + 1) pq)]
  exact length_homology_le hℓ _ _

/-- Lengths do not increase along the pages of a spectral sequence. -/
lemma length_page_le_of_additive (r r' : ℤ) (hr : r₀ ≤ r) (hrr' : r ≤ r') (pq : ℤ × ℤ) :
    ℓ ((E.page r' (by omega)).X pq) ≤ ℓ ((E.page r).X pq) := by
  induction r', hrr' using Int.le_induction with
  | base => exact le_rfl
  | succ r' hr' ih => exact (E.length_page_succ_le_of_additive hℓ hℓ0 r' (by omega) pq).trans ih

/-- The infinity page has the length of the page `max r (rMin pq)`, from which it is reached. -/
private lemma length_pageInfinity_eq_page_max (pq : ℤ × ℤ) [E.HasPageInfinityAt pq] (r : ℤ)
    (hr : r₀ ≤ r) :
    ℓ (E.pageInfinity pq) = ℓ ((E.page (max r (E.rMin pq)) (by omega)).X pq) := by
  have := E.hasEdgeMonoAtFrom_of_GE pq (E.rMin pq) (max r (E.rMin pq)) (le_max_right _ _)
  have := E.hasEdgeEpiAtFrom_of_GE pq (E.rMin pq) (max r (E.rMin pq)) (le_max_right _ _)
  exact length_eq_of_iso hℓ hℓ0 (E.pageInfinityIso pq (max r (E.rMin pq)))

/-- The length of the infinity page is at most the length of any page. -/
lemma length_pageInfinity_le_of_additive (pq : ℤ × ℤ) [E.HasPageInfinityAt pq] (r : ℤ)
    (hr : r₀ ≤ r) :
    ℓ (E.pageInfinity pq) ≤ ℓ ((E.page r).X pq) := by
  rw [E.length_pageInfinity_eq_page_max hℓ hℓ0 pq r hr]
  exact E.length_page_le_of_additive hℓ hℓ0 r _ hr (le_max_left _ _) pq

/-- The infinity page has the length of every page from which it is reached. -/
lemma length_pageInfinity_eq (pq : ℤ × ℤ) [E.HasPageInfinityAt pq] (r : ℤ)
    [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r] :
    ℓ (E.pageInfinity pq) = ℓ ((E.page r (E.le₀_of_hasEdgeEpiAtFrom pq r)).X pq) :=
  length_eq_of_iso hℓ hℓ0 (E.pageInfinityIso pq r)

omit hℓ hℓ0 in
include hℓ hℓ0 in
/-- **The length of the abutment is the sum of the lengths of the infinity page.** If `E` abuts
to `H`, then `ℓ(H^n) = ∑_p ℓ(E_∞^{p, n - p})`. -/
lemma AbutsTo.length_eq_finsum {H : ℤ → C} (hE : E.AbutsTo H) (n : ℤ) :
    ℓ (H n) = ∑ᶠ p : ℤ, ℓ (E.pageInfinity (p, n - p)) := by
  obtain ⟨hinf, F, hF, hbounds, hgr⟩ := hE
  obtain ⟨a, b, hab, ha, hb⟩ := hbounds n
  rw [length_eq_finsum_of_antitone hℓ hℓ0 (F n) (hF n) hab ha hb]
  refine finsum_congr fun p => ?_
  have : E.HasPageInfinityAt (p, n - p) := hinf p (n - p)
  have key : ∀ m : ℤ, m = n → ∀ e : E.pageInfinity (p, n - p) ≅
      cokernel (Subobject.ofLE (F m (p + 1)) (F m p) (hF m (by omega))),
      ℓ (cokernel (Subobject.ofLE (F n (p + 1)) (F n p) (hF n (by omega)))) =
        ℓ (E.pageInfinity (p, n - p)) := by
    rintro m rfl e
    exact (length_eq_of_iso hℓ hℓ0 e).symm
  exact key (p + (n - p)) (by omega) (hgr p (n - p)).some

/-- **Degeneration detected by lengths.** Let `ℓ` be additive on short exact sequences and vanish
exactly on zero objects. Let `E` be a bounded spectral sequence abutting to `H`, and let `r₁` be a
page all of whose terms have finite length. Then all the differentials `d_r` with `r ≥ r₁` vanish
(the spectral sequence degenerates at `E_{r₁}`) if and only if for every `n`
$$\ell(H^n) = \sum_{p + q = n} \ell(E_{r_1}^{p, q}).$$ -/
theorem degeneratesFrom_iff_length_eq_finsum {H : ℤ → C} (hE : E.AbutsTo H)
    (hb : IsBounded E) (r₁ : ℤ) (hr₁ : r₀ ≤ r₁) (hfin : ∀ pq, ℓ ((E.page r₁).X pq) ≠ ⊤) :
    (∀ (r : ℤ) (hr : r₁ ≤ r) (pq pq' : ℤ × ℤ), (E.page r (by omega)).d pq pq' = 0) ↔
      ∀ n : ℤ, ℓ (H n) = ∑ᶠ p : ℤ, ℓ ((E.page r₁).X (p, n - p)) := by
  refine ⟨fun hd n => ?_, fun hsum r hr pq pq' => ?_⟩
  · rw [AbutsTo.length_eq_finsum E hℓ hℓ0 hE n]
    refine finsum_congr fun p => ?_
    have : E.HasPageInfinityAt (p, n - p) := hE.1 p (n - p)
    -- all pages from `r₁` on have the same length at `(p, n - p)`
    have hconst : ∀ r (hr : r₁ ≤ r),
        ℓ ((E.page r (by omega)).X (p, n - p)) = ℓ ((E.page r₁).X (p, n - p)) := by
      intro r hr
      induction r, hr using Int.le_induction with
      | base => rfl
      | succ r hr ih =>
        rw [← ih, ← length_eq_of_iso hℓ hℓ0 (E.iso r (r + 1) (p, n - p))]
        exact length_homology_eq_of_d_eq_zero hℓ hℓ0 _ _ (hd r hr _) (fun j => hd r hr j _)
    rw [E.length_pageInfinity_eq_page_max hℓ hℓ0 (p, n - p) r₁ hr₁]
    exact hconst _ (le_max_left _ _)
  · obtain ⟨p, q⟩ := pq
    set n := p + q with hn
    have hq : n - p = q := by omega
    -- the terms of page `r₀` in total degree `n` vanish outside a finite set `T`
    obtain ⟨T, hT⟩ := (hb n).exists_finset_coe
    have hvan : ∀ p', p' ∉ T → ∀ r (hr : r₀ ≤ r), ℓ ((E.page r hr).X (p', n - p')) = 0 := by
      intro p' hp' r hr
      have h0 : ℓ ((E.page r₀).X (p', n - p')) = 0 := by
        refine length_eq_zero_of_isZero hℓ0 ?_
        by_contra hz
        exact hp' (by rw [← Finset.mem_coe, hT]; exact hz)
      exact le_antisymm (h0 ▸ E.length_page_le_of_additive hℓ hℓ0 r₀ r le_rfl hr _) bot_le
    have hinf : ∀ p', E.HasPageInfinityAt (p', n - p') := fun p' => hE.1 p' (n - p')
    have hle : ∀ p', ℓ (E.pageInfinity (p', n - p')) ≤ ℓ ((E.page r₁).X (p', n - p')) :=
      fun p' => by
        have := hinf p'
        exact E.length_pageInfinity_le_of_additive hℓ hℓ0 _ r₁ hr₁
    have hsuppE : Function.support (fun p' => ℓ ((E.page r₁).X (p', n - p'))) ⊆ (T : Set ℤ) :=
      Function.support_subset_iff'.2 fun p' h => hvan p' h r₁ hr₁
    have hsuppI : Function.support (fun p' => ℓ (E.pageInfinity (p', n - p'))) ⊆ (T : Set ℤ) :=
      Function.support_subset_iff'.2 fun p' h =>
        le_antisymm ((hle p').trans (hvan p' h r₁ hr₁).le) bot_le
    have heq := (AbutsTo.length_eq_finsum E hℓ hℓ0 hE n).symm.trans (hsum n)
    rw [finsum_eq_sum_of_support_subset _ hsuppI, finsum_eq_sum_of_support_subset _ hsuppE] at heq
    have hpt : ℓ (E.pageInfinity (p, n - p)) = ℓ ((E.page r₁).X (p, n - p)) := by
      by_cases hpT : p ∈ T
      · exact ENat.eq_of_sum_eq_sum_of_le (fun i _ => hle i) (fun i _ => hfin _) heq p hpT
      · exact le_antisymm (hle p) ((hvan p hpT r₁ hr₁).le.trans bot_le)
    rw [hq] at hpt
    have hfin' : ℓ ((E.page r (by omega)).X (p, q)) ≠ ⊤ :=
      ne_top_of_le_ne_top (hfin _) (E.length_page_le_of_additive hℓ hℓ0 r₁ r hr₁ hr _)
    have h1 : ℓ ((E.page (r + 1) (by omega)).X (p, q)) = ℓ ((E.page r (by omega)).X (p, q)) := by
      have : E.HasPageInfinityAt (p, q) := hE.1 p q
      have hI := hpt ▸ E.length_pageInfinity_le_of_additive hℓ hℓ0 (p, q) (r + 1) (by omega)
      exact le_antisymm (E.length_page_succ_le_of_additive hℓ hℓ0 r (by omega) _)
        ((E.length_page_le_of_additive hℓ hℓ0 r₁ r hr₁ hr _).trans hI)
    rw [← length_eq_of_iso hℓ hℓ0 (E.iso r (r + 1) (p, q))] at h1
    exact (d_eq_zero_of_length_homology_eq hℓ hℓ0 _ _ hfin' h1).1 pq'

end SpectralSequence

end CategoryTheory
