module

public import StacksFrontier.AlgebraicGeometry.RegularImmersion.Sequence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Spreading out a regular sequence on the fibre

Let `A → B` be flat and of finite presentation, let `q` be a prime of `B` with `p = A ∩ q`, and let
`f₁, …, f_r ∈ q`.  Stacks 062Y (3) for a sequence says that if `f₁, …, f_r` is a regular sequence
on the fibre `B_q/pB_q` then there is a `g ∉ q` such that `f₁, …, f_r` is a weakly regular sequence
in `B_g` and `B_g/(f₁, …, f_r)B_g` is flat over `A` — that is, `V(f₁, …, f_r) ⊂ Spec(B_g)` is a
relative quasi-regular immersion over `Spec(A)`.  This file proves that statement, with no
Noetherian hypothesis.

Only the single-element case was available, as
`Stacks.RingTheory.SpreadingOut.exists_notMem_isSMulRegular_and_flat_quotient_away`.  The sequence
case is the one input Stacks 063W needs that the tree did not have.

## Main results

* `Stacks.RingTheory.SpreadingOut.isRegular_atPrime_and_flat_quotients_of_isRegular_fibre`: the
  stalk step.  A sequence regular on the fibre `B_q/pB_q` is regular in `B_q`, and every partial
  quotient `B_q/(f₁, …, f_k)` is flat over `A`.
* `Stacks.RingTheory.SpreadingOut.exists_notMem_isWeaklyRegular_and_flat_quotient_away`: **Stacks
  062Y (3) for a sequence.**

## Implementation notes

The two steps are already in the tree in the shapes needed, and the work here is to join them.

* The stalk step is Stacks 0470,
  `Module.Flat.isRegular_and_flat_quotient_ofList_smul_of_isRegular_maximalIdeal`, applied to the
  flat local homomorphism `A_p → B_q`, which is essentially of finite presentation because
  `A → B` is of finite presentation.  This is the sequence analogue of
  `Stacks.RingTheory.SpreadingOut.isSMulRegular_and_flat_quotient_atPrime`, and the same
  non-Noetherian criterion serves: the Noetherian descent of Stacks 02JO is not used.
* The spreading out is
  `Stacks.RingTheory.SpreadingOut.exists_notMem_isWeaklyRegular_away_of_isRegular_atPrime`, whose
  hypotheses are exactly the two conclusions of the stalk step, and whose conclusion is weak
  regularity in `B_{g₁}` for some `g₁ ∉ q`.  Flatness of the full quotient is spread out
  separately, over a basic open `D(g₂)`, by the openness of the flat locus (Stacks 00RC).

Those produce two different elements of `q.primeCompl`, and the conclusion is asserted at their
product.  Both halves survive the further localization: flatness because
`B_{g₁g₂}/(f)B_{g₁g₂}` is a localization of `B_{g₂}/(f)B_{g₂}`, which is how
`flat_quotient_away_of_forall_of_fg` already states it; and weak regularity by
`isWeaklyRegular_away_of_mul_right`, proved here from the elementary reading of a nonzerodivisor
modulo an ideal in a localization, `isSMulRegular_quotientMap_iff`.

## References

* [Stacks Project, Tag 062Y](https://stacks.math.columbia.edu/tag/062Y)
* [Stacks Project, Tag 0470](https://stacks.math.columbia.edu/tag/0470)
* [Stacks Project, Tag 00RC](https://stacks.math.columbia.edu/tag/00RC)
* [Stacks Project, Lemma 31.22.8 (Tag 063W)](https://stacks.math.columbia.edu/tag/063W)
-/

@[expose] public section

namespace Stacks.RingTheory.SpreadingOut

open RingTheory.Sequence

section Elementary

variable {B : Type*} [CommRing B]

/-- An ideal acts on `⊤ : Submodule B B` as the ideal itself. -/
private lemma ideal_smul_top_self (J : Ideal B) : J • (⊤ : Submodule B B) = J :=
  (Ideal.smul_eq_mul J ⊤).trans (Ideal.mul_top J)

/-- **Weak regularity in a localization away from an element, read in `B`.**  The images of
`f₁, …, f_r` form a weakly regular sequence in `B_g` exactly when, for every `k` and every
`x ∈ B`, a power of `g` carrying `f_k x` into `(f₁, …, f_{k-1})` forces a power of `g` carrying
`x` there. -/
private lemma isWeaklyRegular_away_iff {r : ℕ} (f : Fin r → B) (g : B) :
    IsWeaklyRegular (Localization.Away g)
        (List.ofFn fun i => algebraMap B (Localization.Away g) (f i)) ↔
      ∀ k : Fin r, ∀ x : B, (∃ u ∈ Submonoid.powers g, u * (f k * x) ∈ partialIdeal f k.val) →
        ∃ u ∈ Submonoid.powers g, u * x ∈ partialIdeal f k.val := by
  have key (k : Fin r) :
      IsSMulRegular (Localization.Away g ⧸ Ideal.ofList
          ((List.ofFn fun j => algebraMap B (Localization.Away g) (f j)).take k.val) •
            (⊤ : Submodule (Localization.Away g) (Localization.Away g)))
        (algebraMap B (Localization.Away g) (f k)) ↔
      ∀ x : B, (∃ u ∈ Submonoid.powers g, u * (f k * x) ∈ partialIdeal f k.val) →
        ∃ u ∈ Submonoid.powers g, u * x ∈ partialIdeal f k.val := by
    rw [ideal_smul_top_self, ← map_partialIdeal]
    exact isSMulRegular_quotientMap_iff (partialIdeal f k.val) (Submonoid.powers g)
      (Localization.Away g) (f k)
  constructor
  · intro h k
    exact (key k).mp (by simpa using h.regular_mod_prev k.val (by simp))
  · intro h
    refine (isWeaklyRegular_iff_Fin _ _).mpr fun i => ?_
    have hilt : i.val < r := by simpa using i.isLt
    simpa using (key ⟨i.val, hilt⟩).mpr (h ⟨i.val, hilt⟩)

/-- Weak regularity of a sequence in `B_g` passes to the further localization `B_{gc}`. -/
private lemma isWeaklyRegular_away_of_mul_right {r : ℕ} (f : Fin r → B) (g c : B)
    (h : IsWeaklyRegular (Localization.Away g)
      (List.ofFn fun i => algebraMap B (Localization.Away g) (f i))) :
    IsWeaklyRegular (Localization.Away (g * c))
      (List.ofFn fun i => algebraMap B (Localization.Away (g * c)) (f i)) := by
  rw [isWeaklyRegular_away_iff] at h ⊢
  intro k x hx
  obtain ⟨-, ⟨m, rfl⟩, hmem⟩ := hx
  obtain ⟨-, ⟨n, rfl⟩, hmem'⟩ := h k (c ^ m * x) ⟨g ^ m, ⟨m, rfl⟩, by
    rw [show g ^ m * (f k * (c ^ m * x)) = (g * c) ^ m * (f k * x) by rw [mul_pow]; ring]
    exact hmem⟩
  refine ⟨(g * c) ^ max n m, ⟨max n m, rfl⟩, ?_⟩
  rw [show (g * c) ^ max n m * x
      = g ^ (max n m - n) * c ^ (max n m - m) * (g ^ n * (c ^ m * x)) by
    rw [mul_pow, show g ^ max n m = g ^ (max n m - n) * g ^ n by rw [← pow_add]; congr 1; omega,
      show c ^ max n m = c ^ (max n m - m) * c ^ m by rw [← pow_add]; congr 1; omega]
    ring]
  exact Ideal.mul_mem_left _ _ hmem'

end Elementary

section Spreading

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- **The stalk step of Stacks 062Y, for a sequence.**  Let `A → B` be flat and of finite
presentation, let `q` be a prime of `B` and let `p = A ∩ q`.  If `f₁, …, f_r` have regular image in
the fibre `B_q/pB_q`, then their images form a regular sequence in `B_q` and every partial quotient
`B_q/(f₁, …, f_k)` is flat over `A`.

This is the source's appeal to Algebra, Lemma 00MF, but through the non-Noetherian local criterion
of Stacks 0470: `A_p → B_q` is a flat local homomorphism which is essentially of finite
presentation, so no Noetherian hypothesis is needed. -/
theorem isRegular_atPrime_and_flat_quotients_of_isRegular_fibre
    [Module.Flat A B] [Algebra.FinitePresentation A B]
    (q : Ideal B) [q.IsPrime] {r : ℕ} (f : Fin r → B)
    (hfib : IsRegular
      (Localization.AtPrime q ⧸
        (q.comap (algebraMap A B)).map (algebraMap A (Localization.AtPrime q)))
      (List.ofFn fun i => algebraMap B (Localization.AtPrime q) (f i))) :
    IsRegular (Localization.AtPrime q)
        (List.ofFn fun i => algebraMap B (Localization.AtPrime q) (f i)) ∧
      ∀ k : ℕ, Module.Flat A (Localization.AtPrime q ⧸
        Ideal.ofList
          ((List.ofFn fun j => algebraMap B (Localization.AtPrime q) (f j)).take k)) := by
  classical
  let T := Localization.AtPrime q
  let p := q.comap (algebraMap A B)
  have : p.IsPrime := Ideal.comap_isPrime _ _
  have : q.LiesOver p := ⟨rfl⟩
  let P := Localization.AtPrime p
  let : Algebra P T := Localization.AtPrime.algebraOfLiesOver p q
  have : IsLocalHom (algebraMap P T) :=
    Localization.isLocalHom_localRingHom p q (algebraMap A B) rfl
  have : Module.Flat P T :=
    (Module.flat_iff_of_isLocalization P p.primeCompl T).mpr inferInstance
  have hess : (algebraMap P T).EssentiallyOfFinitePresentation :=
    Koszul.essentiallyOfFinitePresentation_localization (S := B) p.primeCompl q.primeCompl
      (by rintro _ ⟨x, hx, rfl⟩; exact hx)
  have hmax : (IsLocalRing.maximalIdeal P).map (algebraMap P T) = p.map (algebraMap A T) :=
    map_maximalIdeal_eq_map_of_isLocalization p
  have hfib' : IsRegular
      (T ⧸ ((IsLocalRing.maximalIdeal P).map (algebraMap P T) • (⊤ : Submodule T T)))
      (List.ofFn fun i => algebraMap B T (f i)) := by
    rwa [ideal_smul_top_self, hmax]
  obtain ⟨h1, h2⟩ := Module.Flat.isRegular_and_flat_quotient_ofList_smul_of_isRegular_maximalIdeal
    (R := P) (S := T) (M := T) hess _ hfib'
  refine ⟨h1, fun k => ?_⟩
  have h3 := h2 k
  rw [ideal_smul_top_self] at h3
  exact Module.Flat.trans A P _

/-- **Stacks 062Y (3), for a sequence.**  Let `A → B` be flat and of finite presentation, let `q`
be a prime of `B`, let `p = A ∩ q` and let `f₁, …, f_r ∈ q`.  If `f₁, …, f_r` have regular image in
the fibre `B_q/pB_q`, then there is a `g ∉ q` such that `f₁, …, f_r` is a weakly regular sequence
in `B_g` and `B_g/(f₁, …, f_r)B_g` is flat over `A`;  that is, `V(f₁, …, f_r) ⊂ Spec(B_g)` is a
relative quasi-regular immersion over `Spec(A)`.

No Noetherian hypothesis is needed.  This is the sequence form of
`exists_notMem_isSMulRegular_and_flat_quotient_away`, and it is the input required by the
fibrewise criterion of Stacks 063W. -/
@[ega "IV 11.3.8" "(c), special case"]
theorem exists_notMem_isWeaklyRegular_and_flat_quotient_away
    [Module.Flat A B] [Algebra.FinitePresentation A B]
    (q : Ideal B) [q.IsPrime] {r : ℕ} (f : Fin r → B) (hq : ∀ i, f i ∈ q)
    (hfib : IsRegular
      (Localization.AtPrime q ⧸
        (q.comap (algebraMap A B)).map (algebraMap A (Localization.AtPrime q)))
      (List.ofFn fun i => algebraMap B (Localization.AtPrime q) (f i))) :
    ∃ g ∉ q,
      IsWeaklyRegular (Localization.Away g)
          (List.ofFn fun i => algebraMap B (Localization.Away g) (f i)) ∧
        Module.Flat A (Localization.Away g ⧸
          (Ideal.span (Set.range f)).map (algebraMap B (Localization.Away g))) := by
  classical
  obtain ⟨hregT, hflatT⟩ := isRegular_atPrime_and_flat_quotients_of_isRegular_fibre q f hfib
  obtain ⟨g₁, hg₁, hwr⟩ :=
    exists_notMem_isWeaklyRegular_away_of_isRegular_atPrime q f hq hregT hflatT
  obtain ⟨g₂, hg₂, hg₂forall⟩ := exists_notMem_forall_flat_atPrime_quotient_of_fg q
    (Ideal.span (Set.range f)) (Submodule.fg_span (Set.finite_range f))
    (Ideal.span_le.mpr (Set.range_subset_iff.mpr hq))
    (by rw [← partialIdeal_length f, map_partialIdeal]; exact hflatT r)
  refine ⟨g₁ * g₂, fun hmem => (‹q.IsPrime›.mem_or_mem hmem).elim hg₁ hg₂,
    isWeaklyRegular_away_of_mul_right f g₁ g₂ hwr, ?_⟩
  refine flat_quotient_away_of_forall_of_fg (Ideal.span (Set.range f)) (g₁ * g₂) fun Q' hQ' => ?_
  refine hg₂forall Q' fun hmem => hQ' ?_
  rw [map_mul]
  exact Ideal.mul_mem_left _ _ hmem

end Spreading

end Stacks.RingTheory.SpreadingOut

end
