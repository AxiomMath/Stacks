module

public import Mathlib.Algebra.Homology.ShortComplex.Homology
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.Ring
public import StacksCore.Algebra.Homology.SpectralSequence.Tower
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Regular, coregular and bounded spectral sequences

Stacks, Homological Algebra, Section 12.24: regular, coregular and bounded spectral sequences
(0BDU) and the relations between these conditions (0BDV), for Mathlib's
`CohomologicalSpectralSequence` and the towers `Z_r`, `B_r` of
`StacksCore.Algebra.Homology.SpectralSequence.Tower`.

Also recorded here are two consequences of a vanishing term: it stays zero on every later page
(`CategoryTheory.SpectralSequence.isZero_page_of_le`), and a spectral sequence with only finitely
many nonzero terms in each total degree on some page has an infinity page at every bidegree
(`CategoryTheory.SpectralSequence.hasPageInfinityAt_of_finite_page`).
-/

@[expose] public section

section

/-
## Stacks Tag 0BDU — Boundedness conditions on spectral sequences

Let `A` be an abelian category and `(E_r, d_r)_{r ≥ r₀}` a cohomological spectral
sequence of bigraded objects with `d_r` of bidegree `(r, -r + 1) = (r, 1 - r)`.
We define when such a spectral sequence is regular, coregular, bounded, bounded
below, and bounded above.
-/

open CategoryTheory CategoryTheory.Limits

variable {C : Type*} [Category C] [Abelian C] {r₀ : ℤ}

/-- A cohomological spectral sequence `E` (with `d_r` of bidegree `(r, 1 - r)`) is
*regular* if for every `(p, q) : ℤ × ℤ` there exists `b : ℤ` such that the
differential `d_r^{p,q} : E_r^{p,q} → E_r^{p + r, q - r + 1}` is zero for all
`r ≥ b` (with `r₀ ≤ r`). -/
@[stacks 0BDU "regular"]
def IsRegularChainComplex (E : CohomologicalSpectralSequence C r₀) : Prop :=
  ∀ p q : ℤ, ∃ b : ℤ, ∀ r : ℤ, ∀ hr : r₀ ≤ r, b ≤ r →
    (E.page r hr).d (p, q) (p + r, q + (1 - r)) = 0

/-- A cohomological spectral sequence `E` (with `d_r` of bidegree `(r, 1 - r)`)
is *coregular* if for every `(p, q) : ℤ × ℤ` there exists `b : ℤ` such that the
differential `d_r^{p - r, q + r - 1} : E_r^{p-r, q+r-1} → E_r^{p, q}` is zero for
all `r ≥ b` (with `r₀ ≤ r`). -/
@[stacks 0BDU "coregular"]
def IsCoregular (E : CohomologicalSpectralSequence C r₀) : Prop :=
  ∀ p q : ℤ, ∃ b : ℤ, ∀ r : ℤ, ∀ hr : r₀ ≤ r, b ≤ r →
    (E.page r hr).d (p - r, q + r - 1) (p, q) = 0

/-- A cohomological spectral sequence `E` is *bounded* if for every total degree
`n : ℤ` there are only finitely many pairs `p : ℤ` such that
`E_{r₀}^{p, n - p}` is nonzero. -/
@[stacks 0BDU "bounded", ega "0 11.1.1" "partial"]
def IsBounded (E : CohomologicalSpectralSequence C r₀) : Prop :=
  ∀ n : ℤ, { p : ℤ | ¬ IsZero ((E.page r₀).X (p, n - p)) }.Finite

/-- A cohomological spectral sequence `E` is *bounded below* if for every total
degree `n : ℤ` there exists `b : ℤ` such that `E_{r₀}^{p, n - p} = 0` for all
`p ≥ b`. -/
@[stacks 0BDU "bounded below"]
def IsBoundedBelow (E : CohomologicalSpectralSequence C r₀) : Prop :=
  ∀ n : ℤ, ∃ b : ℤ, ∀ p : ℤ, b ≤ p → IsZero ((E.page r₀).X (p, n - p))

/-- A cohomological spectral sequence `E` is *bounded above* if for every total
degree `n : ℤ` there exists `b : ℤ` such that `E_{r₀}^{p, n - p} = 0` for all
`p ≤ b`. -/
@[stacks 0BDU "bounded above"]
def IsBoundedAbove (E : CohomologicalSpectralSequence C r₀) : Prop :=
  ∀ n : ℤ, ∃ b : ℤ, ∀ p : ℤ, p ≤ b → IsZero ((E.page r₀).X (p, n - p))

end

section

/-!
## Stacks Tag 0BDV

For a spectral sequence `(E_r, d_r)_{r ≥ r₀}` with its towers of cycles `Z_r^{p,q}` and
boundaries `B_r^{p,q}` inside `E_{r₀}^{p,q}` (Stacks 011N, `SpectralSequence.Z` and
`SpectralSequence.B`):

1. the spectral sequence is regular iff for all `p, q` there is an `r = r(p,q)`
   with `Z_r^{p,q} = Z_{r+1}^{p,q} = …`;
2. it is coregular iff for all `p, q` there is an `r = r(p,q)` with
   `B_r^{p,q} = B_{r+1}^{p,q} = …`;
3. it is bounded iff it is both bounded below and bounded above;
4. if it is bounded below, then it is regular;
5. if it is bounded above, then it is coregular.

The first two rest on `Z_add_one_eq_iff` and `B_add_one_eq_iff`, valid for any spectral sequence:
`Z_{r+1} = Z_r` exactly when the differential of `E_r` out of the position vanishes, and
`B_{r+1} = B_r` exactly when the differential into it does.
-/

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SpectralSequence

variable {C : Type*} [Category C] [Abelian C] {ι : Type*} {c : ℤ → ComplexShape ι} {r₀ : ℤ}
  (E : SpectralSequence C c r₀) (pq : ι)

/-- `Z_{r+1} = Z_r` if and only if the differential of `E_r` out of `pq` vanishes. -/
lemma Z_add_one_eq_iff (r : ℤ) (hr : r₀ ≤ r) :
    E.Z pq (r + 1) = E.Z pq r ↔ (E.page r).d pq ((c r).next pq) = 0 := by
  constructor
  · intro h
    rw [E.Z_add_one pq r hr, Subobject.pullback_kernelSubobject] at h
    have htop : kernelSubobject (E.q pq r hr ≫ (E.page r).d pq ((c r).next pq)) = ⊤ :=
      Subobject.map_obj_injective (E.Z pq r).arrow
        (by rw [h, Subobject.map_top, Subobject.mk_arrow])
    have hzero : E.q pq r hr ≫ (E.page r).d pq ((c r).next pq) = 0 := by
      rw [← cancel_epi (⊤ : Subobject (E.Z pq r : C)).arrow, comp_zero, ← htop,
        kernelSubobject_arrow_comp]
    exact (cancel_epi (E.q pq r hr)).1 (by rw [hzero, comp_zero])
  · intro h
    have : E.HasEdgeEpiAt pq r := ⟨hr, fun pq' => by
      by_cases hrel : (c r).Rel pq pq'
      · rwa [← (c r).next_eq' hrel]
      · exact (E.page r).shape _ _ hrel⟩
    exact E.Z_add_one_of_hasEdgeEpiAt pq r

/-- `B_{r+1} = B_r` if and only if the differential of `E_r` into `pq` vanishes. -/
lemma B_add_one_eq_iff (r : ℤ) (hr : r₀ ≤ r) :
    E.B pq (r + 1) = E.B pq r ↔ (E.page r).d ((c r).prev pq) pq = 0 := by
  constructor
  · intro h
    rw [E.B_add_one pq r hr, ← E.map_kernelSubobject_q pq r hr] at h
    have h' := Abelian.Subobject.pullback_obj_injective_of_epi (E.q pq r hr)
      ((Subobject.map_obj_injective (E.Z pq r).arrow h).trans (Subobject.pullback_bot _).symm)
    rw [← Subobject.bot_factors_iff_zero, ← h']
    simpa using imageSubobject_factors_comp_self ((E.page r).d ((c r).prev pq) pq) (𝟙 _)
  · intro h
    have : E.HasEdgeMonoAt pq r := ⟨hr, fun pq' => by
      by_cases hrel : (c r).Rel pq' pq
      · rwa [← (c r).prev_eq' hrel]
      · exact (E.page r).shape _ _ hrel⟩
    exact E.B_add_one_of_hasEdgeMonoAt pq r

/-- A position that vanishes on the page `E_{r₀}` vanishes on every later page. -/
private lemma isZero_page_X_of_isZero (r : ℤ) (hr : r₀ ≤ r) (h : IsZero ((E.page r₀).X pq)) :
    IsZero ((E.page r).X pq) :=
  (IsZero.of_epi (cokernel.π _) (IsZero.of_mono (E.Z pq r).arrow h)).of_iso
    (E.pageIsoSubquotient pq r hr)

end CategoryTheory.SpectralSequence

namespace CohomologicalSpectralSequence

open SpectralSequence

variable {C : Type*} [Category C] [Abelian C] {r₀ : ℤ} (E : CohomologicalSpectralSequence C r₀)

private lemma prev_eq (r p q : ℤ) :
    (ComplexShape.up' ((r, 1 - r) : ℤ × ℤ)).prev (p, q) = (p - r, q + r - 1) :=
  ComplexShape.prev_eq' _ (Prod.ext (by simp) (by simp))

/-- If `f (r + 1) = f r` for every `r ≥ b`, then `f r = f b` for every `r ≥ b`. -/
private lemma eq_of_succ_eq_above {α : Type*} (b : ℤ) (f : ℤ → α)
    (hsucc : ∀ r, b ≤ r → f (r + 1) = f r) (r : ℤ) (hr : b ≤ r) : f r = f b := by
  induction r, hr using Int.leInduction with
  | base => rfl
  | succ r hbr ih => rw [hsucc r hbr, ih]

/-- Part (1): the spectral sequence is regular iff for all `p, q` the cycles `Z_r^{p,q}` are
eventually constant. -/
@[stacks 0BDV "(1)"]
theorem isRegularChainComplex_iff_Z_eventually_constant :
    IsRegularChainComplex E ↔ ∀ p q : ℤ, ∃ b : ℤ, ∀ r, b ≤ r → E.Z (p, q) r = E.Z (p, q) b := by
  refine ⟨fun hReg p q ↦ ?_, fun hZ p q ↦ ?_⟩
  · obtain ⟨b, hb⟩ := hReg p q
    refine ⟨max r₀ b, eq_of_succ_eq_above _ _ fun r hr ↦ ?_⟩
    rw [E.Z_add_one_eq_iff (p, q) r (le_of_max_le_left hr),
      ComplexShape.next_eq' _ (j := (p + r, q + (1 - r))) rfl]
    exact hb r (le_of_max_le_left hr) (le_of_max_le_right hr)
  · obtain ⟨b, hb⟩ := hZ p q
    refine ⟨b, fun r hr hbr ↦ ?_⟩
    rw [← ComplexShape.next_eq' (ComplexShape.up' ((r, 1 - r) : ℤ × ℤ)) (i := (p, q))
        (j := (p + r, q + (1 - r))) rfl, ← E.Z_add_one_eq_iff (p, q) r hr, hb r hbr,
      hb (r + 1) (by lia)]

/-- Part (2): the spectral sequence is coregular iff for all `p, q` the boundaries `B_r^{p,q}`
are eventually constant. -/
@[stacks 0BDV "(2)"]
theorem isCoregular_iff_B_eventually_constant :
    IsCoregular E ↔ ∀ p q : ℤ, ∃ b : ℤ, ∀ r, b ≤ r → E.B (p, q) r = E.B (p, q) b := by
  refine ⟨fun hCo p q ↦ ?_, fun hB p q ↦ ?_⟩
  · obtain ⟨b, hb⟩ := hCo p q
    refine ⟨max r₀ b, eq_of_succ_eq_above _ _ fun r hr ↦ ?_⟩
    rw [E.B_add_one_eq_iff (p, q) r (le_of_max_le_left hr), prev_eq]
    exact hb r (le_of_max_le_left hr) (le_of_max_le_right hr)
  · obtain ⟨b, hb⟩ := hB p q
    refine ⟨b, fun r hr hbr ↦ ?_⟩
    rw [← prev_eq, ← E.B_add_one_eq_iff (p, q) r hr, hb r hbr, hb (r + 1) (by lia)]

/-- Part (3): the spectral sequence is bounded iff it is both bounded below and bounded
above. -/
@[stacks 0BDV "(3)"]
theorem isBounded_iff_isBoundedBelow_and_isBoundedAbove :
    IsBounded E ↔ IsBoundedBelow E ∧ IsBoundedAbove E := by
  refine ⟨fun hB ↦ ⟨fun n ↦ ?_, fun n ↦ ?_⟩, ?_⟩
  · obtain ⟨a, ha⟩ := (hB n).bddAbove
    exact ⟨a + 1, fun p hp ↦ by by_contra hns; have := ha hns; lia⟩
  · obtain ⟨a, ha⟩ := (hB n).bddBelow
    exact ⟨a - 1, fun p hp ↦ by by_contra hns; have := ha hns; lia⟩
  · rintro ⟨hBelow, hAbove⟩ n
    obtain ⟨b₁, hb₁⟩ := hBelow n
    obtain ⟨b₂, hb₂⟩ := hAbove n
    refine (Set.finite_Icc (b₂ + 1) (b₁ - 1)).subset (fun p hp ↦ Set.mem_Icc.mpr ⟨?_, ?_⟩)
    · by_contra hc
      exact hp (hb₂ p (by lia))
    · by_contra hc
      exact hp (hb₁ p (by lia))

/-- Part (4): if the spectral sequence is bounded below, then it is regular. -/
@[stacks 0BDV "(4)"]
theorem isRegularChainComplex_of_isBoundedBelow (h : IsBoundedBelow E) :
    IsRegularChainComplex E := by
  intro p q
  obtain ⟨b, hb⟩ := h (p + q + 1)
  refine ⟨b - p, fun r hr hbr ↦ ?_⟩
  refine IsZero.eq_of_tgt (E.isZero_page_X_of_isZero _ r hr ?_) _ _
  simpa [show p + q + 1 - (p + r) = q + (1 - r) by ring] using hb (p + r) (by lia)

/-- Part (5): if the spectral sequence is bounded above, then it is coregular. -/
@[stacks 0BDV "(5)"]
theorem isCoregular_of_isBoundedAbove (h : IsBoundedAbove E) : IsCoregular E := by
  intro p q
  obtain ⟨b, hb⟩ := h (p + q - 1)
  refine ⟨p - b, fun r hr hbr ↦ ?_⟩
  refine IsZero.eq_of_src (E.isZero_page_X_of_isZero _ r hr ?_) _ _
  simpa [show p + q - 1 - (p - r) = q + r - 1 by ring] using hb (p - r) (by lia)

end CohomologicalSpectralSequence

/-- A zero term stays zero on all later pages of a spectral sequence. -/
@[ega "0 11.1.6" "partial"]
public lemma CategoryTheory.SpectralSequence.isZero_page_of_le
    {A : Type*} [Category* A] [Abelian A]
    {ι : Type*} {c : ℤ → ComplexShape ι} {r₀ : ℤ}
    (E : SpectralSequence A c r₀) {r : ℤ} (hr : r₀ ≤ r) (i : ι)
    (h : IsZero ((E.page r hr).X i)) :
    ∀ r' : ℤ, r ≤ r' → ∀ hr' : r₀ ≤ r', IsZero ((E.page r' hr').X i) := by
  intro r' hle
  induction r', hle using Int.leInduction with
  | base => exact fun _ => h
  | succ m hm ih =>
    have hm0 : r₀ ≤ m := hr.trans hm
    exact fun _ => IsZero.of_iso
      (ShortComplex.isZero_homology_of_isZero_X₂ _ (ih hm0))
      (E.iso m (m + 1) i rfl hm0).symm

/-- **A spectral sequence with finitely many nonzero terms in each total degree has an infinity
page everywhere.** It suffices that some one page `r₁` have, in each total degree, only finitely
many nonzero terms: a term that vanishes on page `r₁` vanishes on every later page, so from some
page on all the differentials into, and all the differentials out of, a given bidegree vanish. -/
public lemma CategoryTheory.SpectralSequence.hasPageInfinityAt_of_finite_page
    {A : Type*} [Category* A] [Abelian A]
    {r₀ : ℤ} (E : CohomologicalSpectralSequence A r₀) (r₁ : ℤ) (hr₁ : r₀ ≤ r₁)
    (h : ∀ n : ℤ, {p : ℤ | ¬ IsZero ((E.page r₁ hr₁).X (p, n - p))}.Finite)
    (pq : ℤ × ℤ) : E.HasPageInfinityAt pq := by
  obtain ⟨p, q⟩ := pq
  obtain ⟨b₀, hb₀⟩ := (h (p + q - 1)).bddBelow
  obtain ⟨b₁, hb₁⟩ := (h (p + q + 1)).bddAbove
  have hrel : ∀ (r p q p' q' : ℤ),
      (ComplexShape.up' ((r, 1 - r) : ℤ × ℤ)).Rel (p, q) (p', q') → p' = p + r ∧ q' = q + (1 - r) :=
    fun r p q p' q' h ↦ ⟨by simpa using congrArg _root_.Prod.fst h.symm,
      by simpa using congrArg _root_.Prod.snd h.symm⟩
  have hmem : ∀ n p' q' : ℤ, p' + q' = n → ¬ IsZero ((E.page r₁ hr₁).X (p', q')) →
      p' ∈ {i : ℤ | ¬ IsZero ((E.page r₁ hr₁).X (i, n - i))} := by
    rintro n p' q' rfl hn
    simpa using hn
  refine ⟨⟨max r₁ (p - b₀ + 1), hr₁.trans (le_max_left _ _), ?_⟩,
    ⟨max r₁ (b₁ - p + 1), hr₁.trans (le_max_left _ _), ?_⟩⟩
  · intro r hr
    have hrr₁ : r₁ ≤ r := (le_max_left _ _).trans hr
    have hbr : p - b₀ + 1 ≤ r := (le_max_right _ _).trans hr
    exact
      { le := hr₁.trans hrr₁
        zero := by
          rintro ⟨p', q'⟩
          by_cases hr' : (ComplexShape.up' ((r, 1 - r) : ℤ × ℤ)).Rel (p', q') (p, q)
          · obtain ⟨h1, h2⟩ := hrel r _ _ _ _ hr'
            have hz : IsZero ((E.page r₁ hr₁).X (p', q')) := by
              by_contra hn
              have := hb₀ (hmem (p + q - 1) p' q' (by omega) hn)
              omega
            exact (SpectralSequence.isZero_page_of_le E hr₁ _ hz r hrr₁
              (hr₁.trans hrr₁)).eq_of_src _ _
          · exact (E.page r).shape _ _ hr' }
  · intro r hr
    have hrr₁ : r₁ ≤ r := (le_max_left _ _).trans hr
    have hbr : b₁ - p + 1 ≤ r := (le_max_right _ _).trans hr
    exact
      { le := hr₁.trans hrr₁
        zero := by
          rintro ⟨p', q'⟩
          by_cases hr' : (ComplexShape.up' ((r, 1 - r) : ℤ × ℤ)).Rel (p, q) (p', q')
          · obtain ⟨h1, h2⟩ := hrel r _ _ _ _ hr'
            have hz : IsZero ((E.page r₁ hr₁).X (p', q')) := by
              by_contra hn
              have := hb₁ (hmem (p + q + 1) p' q' (by omega) hn)
              omega
            exact (SpectralSequence.isZero_page_of_le E hr₁ _ hz r hrr₁
              (hr₁.trans hrr₁)).eq_of_tgt _ _
          · exact (E.page r).shape _ _ hr' }

end
