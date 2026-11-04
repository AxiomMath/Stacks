module

public import Mathlib.Algebra.Polynomial.Div
public import StacksCore.LinearAlgebra.Matrix.CommSemiring
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Polynomial.ScaleRoots
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

@[expose] public section

/-!
# Absolutely integrally closed rings

A commutative ring `A` is absolutely integrally closed if every monic polynomial in `A[X]` is a
product of linear factors `X - C a` with `a ∈ A`. This file proves that this holds if and only if
every monic polynomial of positive degree has a root in `A`, that the property passes to quotients
and localizations, and that it descends from a localization at nonzerodivisors to a ring which is
integrally closed in it.

## Main definitions

* `IsAbsolutelyIntegrallyClosed`: every monic polynomial is a product of linear factors.

## Main results

* `isAbsolutelyIntegrallyClosed_iff_exists_root`: `A` is absolutely integrally closed if and only
  if every monic polynomial of positive degree has a root in `A`.
* `isAbsolutelyIntegrallyClosed_iff_fin_prod`: the same property with the linear factors indexed
  by `Fin d`.
* `isAbsolutelyIntegrallyClosed_of_surjective`: the property passes along a surjective ring
  homomorphism.
* `isAbsolutelyIntegrallyClosed_quotient`: quotients of absolutely integrally closed rings are
  absolutely integrally closed.
* `isAbsolutelyIntegrallyClosed_localization`: localizations of absolutely integrally closed rings
  are absolutely integrally closed.
* `isAbsolutelyIntegrallyClosed_of_localization`: if `S` consists of nonzerodivisors, `S⁻¹A` is
  absolutely integrally closed and `A` is integrally closed in `S⁻¹A`, then `A` is absolutely
  integrally closed.
* `isAbsolutelyIntegrallyClosed_iff_isAlgClosed_fractionRing`: a normal domain is absolutely
  integrally closed if and only if its fraction field is algebraically closed.

## Implementation notes

The linear factors are encoded by a `Multiset` of roots, so the degree-`0` case `f = 1` is the
empty product.

## References

* [Stacks: Tag 0DCK](https://stacks.math.columbia.edu/tag/0DCK)
-/

open Polynomial

/-- **Stacks 0DCL.**
A ring `A` is *absolutely integrally closed* if every monic polynomial in `A[X]` is the product
of the linear factors `X - C a` over some multiset `s` of elements of `A`. -/
@[stacks 0DCL]
def IsAbsolutelyIntegrallyClosed (A : Type*) [CommRing A] : Prop :=
  ∀ f : A[X], f.Monic → ∃ s : Multiset A, f = (s.map fun a => X - C a).prod

/-- A product of linear factors `X - C a` over a multiset equals a product of linear factors
indexed by some `Fin d`-family. -/
theorem Polynomial.exists_fin_prod_eq_multiset_prod_X_sub_C {A : Type*} [CommRing A]
    (s : Multiset A) :
    ∃ (d : ℕ) (a : Fin d → A), (s.map fun a => X - C a).prod = ∏ i, (X - C (a i)) := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨0, Fin.elim0, by simp⟩
  | cons b s ih =>
    obtain ⟨d, a, ha⟩ := ih
    refine ⟨d + 1, Fin.cons b a, ?_⟩
    rw [Multiset.map_cons, Multiset.prod_cons, ha, Fin.prod_univ_succ]
    simp

/-- A multiset all of whose elements lie in the range of `g` is the image under `g` of a
multiset. -/
theorem Multiset.exists_map_eq_of_forall_mem_range {A B : Type*} (g : A → B) (m : Multiset B)
    (hm : ∀ b ∈ m, ∃ a, g a = b) : ∃ m' : Multiset A, m'.map g = m := by
  induction m using Multiset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | cons b s ih =>
    obtain ⟨a, ha⟩ := hm b (Multiset.mem_cons_self b s)
    obtain ⟨s', hs'⟩ := ih fun x hx => hm x (Multiset.mem_cons_of_mem hx)
    exact ⟨a ::ₘ s', by rw [Multiset.map_cons, ha, hs']⟩

/-- In an absolutely integrally closed ring, every monic polynomial of positive degree has a
root. -/
theorem IsAbsolutelyIntegrallyClosed.exists_root {A : Type*} [CommRing A]
    (h : IsAbsolutelyIntegrallyClosed A) (f : A[X]) (hf : f.Monic) (hdeg : 1 ≤ f.natDegree) :
    ∃ a : A, f.eval a = 0 := by
  obtain ⟨s, hs⟩ := h f hf
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero (s := s) (by rintro rfl; simp_all)
  refine ⟨a, ?_⟩
  rw [hs, eval_multiset_prod, Multiset.map_map]
  exact Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨a, ha, by simp⟩)

/-- A ring in which every monic polynomial of positive degree has a root is absolutely integrally
closed. -/
theorem isAbsolutelyIntegrallyClosed_of_exists_root {A : Type*} [CommRing A]
    (h : ∀ f : A[X], f.Monic → 1 ≤ f.natDegree → ∃ a : A, f.eval a = 0) :
    IsAbsolutelyIntegrallyClosed A := by
  suffices H : ∀ n : ℕ, ∀ f : A[X], f.Monic → f.natDegree = n →
      ∃ s : Multiset A, f = (Multiset.map (fun a => X - C a) s).prod from
    fun f hf => H _ f hf rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f hf hdeg
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, by simpa using hf.natDegree_eq_zero.mp hdeg⟩
    have hd1 : 1 ≤ f.natDegree := by omega
    have : Nontrivial A := by
      rcases subsingleton_or_nontrivial A with _ | h
      · simp [Subsingleton.elim f 0] at hd1
      · exact h
    obtain ⟨a, ha⟩ := h f hf hd1
    obtain ⟨g, hg⟩ := dvd_iff_isRoot.mpr ha
    have hXmonic : (X - C a).Monic := monic_X_sub_C a
    have hgmonic : g.Monic := hXmonic.of_mul_monic_left (hg ▸ hf)
    have hgdeg : g.natDegree < n := by
      have := hXmonic.natDegree_mul hgmonic
      rw [← hg, natDegree_X_sub_C] at this
      omega
    obtain ⟨s, hs⟩ := ih g.natDegree hgdeg g hgmonic rfl
    exact ⟨a ::ₘ s, by rw [Multiset.map_cons, Multiset.prod_cons, ← hs, ← hg]⟩

/-- **Stacks 0DCM**.
A ring `A` is absolutely integrally closed if and only if every monic polynomial of degree at least
`1` has a root in `A`. -/
@[stacks 0DCM]
theorem isAbsolutelyIntegrallyClosed_iff_exists_root (A : Type*) [CommRing A] :
    IsAbsolutelyIntegrallyClosed A ↔
      ∀ f : A[X], f.Monic → 1 ≤ f.natDegree → ∃ a : A, f.eval a = 0 :=
  ⟨fun h => h.exists_root, isAbsolutelyIntegrallyClosed_of_exists_root⟩

/-- A ring `A` is absolutely integrally closed if and only if every monic `f : A[X]` can be
written as `∏ i : Fin d, (X - C (a i))` for some `d` and some family `a : Fin d → A`. -/
theorem isAbsolutelyIntegrallyClosed_iff_fin_prod (A : Type*) [CommRing A] :
    IsAbsolutelyIntegrallyClosed A ↔
      ∀ f : A[X], f.Monic → ∃ (d : ℕ) (a : Fin d → A), f = ∏ i, (X - C (a i)) := by
  refine ⟨fun h f hf => ?_, fun h f hf => ?_⟩
  · obtain ⟨s, hs⟩ := h f hf
    obtain ⟨d, a, ha⟩ := exists_fin_prod_eq_multiset_prod_X_sub_C s
    exact ⟨d, a, hs.trans ha⟩
  · obtain ⟨d, a, ha⟩ := h f hf
    refine ⟨(List.ofFn a : Multiset A), ?_⟩
    rw [ha, Multiset.map_coe, Multiset.prod_coe, List.map_ofFn, List.prod_ofFn]
    rfl

/-- Mapping a product of linear factors `X - C a` along `φ` gives the product of the images. -/
private theorem map_multiset_prod_X_sub_C {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (s : Multiset A) :
    ((s.map fun a => (X : A[X]) - C a).prod).map φ =
      ((s.map φ).map fun b => (X : B[X]) - C b).prod := by
  rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
  exact congrArg _ (Multiset.map_congr rfl fun a _ => by simp)

/-- The target of a surjective ring homomorphism out of an absolutely integrally closed ring is
absolutely integrally closed. -/
theorem isAbsolutelyIntegrallyClosed_of_surjective {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) (hsurj : Function.Surjective φ) (hA : IsAbsolutelyIntegrallyClosed A) :
    IsAbsolutelyIntegrallyClosed B := by
  intro g hg
  have hmem : g ∈ lifts φ := (lifts_iff_coeff_lifts g).mpr fun n => hsurj (g.coeff n)
  obtain ⟨f, hmap, -, hfmonic⟩ := lifts_and_natDegree_eq_and_monic hmem hg
  obtain ⟨s, hs⟩ := hA f hfmonic
  refine ⟨s.map φ, ?_⟩
  rw [← hmap, hs, map_multiset_prod_X_sub_C]

/-- **Stacks 0DCN** (part 1).
If `A` is absolutely integrally closed, then so is the quotient `A ⧸ I` for every ideal `I`. -/
@[stacks 0DCN "(1)"]
theorem isAbsolutelyIntegrallyClosed_quotient (A : Type*) [CommRing A] (I : Ideal A)
    (hA : IsAbsolutelyIntegrallyClosed A) : IsAbsolutelyIntegrallyClosed (A ⧸ I) :=
  isAbsolutelyIntegrallyClosed_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective hA

/-- Clearing denominators: if `B` is a localization of `A` at `S`, every monic `g : B[X]` becomes a
polynomial with coefficients in (the image of) `A` after scaling its roots by some `b ∈ S`. -/
theorem IsLocalization.exists_scaleRoots_mem_lifts {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (S : Submonoid A) [IsLocalization S B] {g : B[X]} (hg : g.Monic) :
    ∃ b : S, g.scaleRoots (algebraMap A B b) ∈ lifts (algebraMap A B) :=
  ⟨IsLocalization.commonDenom S g.support g.coeff,
    IsLocalization.scaleRoots_commonDenom_mem_lifts S g (by rw [hg.leadingCoeff]; exact one_mem _)⟩

/-- **Stacks 0DCN** (part 2).
If `A` is absolutely integrally closed, then so is every localization `B` of `A` at a submonoid
`S`. -/
@[stacks 0DCN "(2)"]
theorem isAbsolutelyIntegrallyClosed_localization (A : Type*) [CommRing A] (S : Submonoid A)
    (B : Type*) [CommRing B] [Algebra A B] [IsLocalization S B]
    (hA : IsAbsolutelyIntegrallyClosed A) : IsAbsolutelyIntegrallyClosed B := by
  rw [isAbsolutelyIntegrallyClosed_iff_exists_root] at hA ⊢
  intro g hg hdeg
  rcases subsingleton_or_nontrivial B with hsub | hnt
  · simp [Subsingleton.elim g 0] at hdeg
  set n := g.natDegree with hn
  obtain ⟨b, hgslifts⟩ := IsLocalization.exists_scaleRoots_mem_lifts S hg
  set s : B := algebraMap A B (b : A) with hs
  have hsunit : IsUnit s := IsLocalization.map_units B b
  set gs : B[X] := g.scaleRoots s with hgs
  have hgsdeg : gs.natDegree = n := by rw [hgs, natDegree_scaleRoots]
  have hgsmonic : gs.Monic := by
    rw [Monic, leadingCoeff, hgsdeg, hgs, coeff_scaleRoots, ← hn, hg.coeff_natDegree]
    simp
  obtain ⟨F, hFmap, hFdeg, hFmonic⟩ := lifts_and_degree_eq_and_monic hgslifts hgsmonic
  have hFnatdeg : F.natDegree = n := (natDegree_eq_natDegree hFdeg).trans hgsdeg
  have hFposdeg : 1 ≤ F.natDegree := hFnatdeg ▸ hdeg
  obtain ⟨c, hc⟩ := hA F hFmonic hFposdeg
  obtain ⟨u, hu⟩ := hsunit
  refine ⟨(↑u⁻¹ : B) * algebraMap A B c, ?_⟩
  have hsr : s * ((↑u⁻¹ : B) * algebraMap A B c) = algebraMap A B c := by
    rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]
  have hgseval : gs.eval (algebraMap A B c) = 0 := by
    have : gs.eval (algebraMap A B c) = algebraMap A B (F.eval c) := by
      rw [← hFmap, eval_map, eval₂_at_apply]
    rw [this, hc, map_zero]
  have hkey := scaleRoots_eval₂_mul (p := g) (RingHom.id B) ((↑u⁻¹ : B) * algebraMap A B c) s
  rw [eval₂_id, eval₂_id, RingHom.id_apply, ← hn, ← hgs, hsr, hgseval] at hkey
  have hsv : s ^ n = (↑(u ^ n) : B) := by rw [← hu, Units.val_pow_eq_pow_val]
  rw [hsv] at hkey
  exact (Units.mul_right_eq_zero (u ^ n)).mp hkey.symm

/-- **Stacks 0DCP**.
Let `B = S⁻¹A` be the localization of `A` at a submonoid `S` of nonzerodivisors. If `B` is
absolutely integrally closed and `A` is integrally closed in `B`, then `A` is absolutely integrally
closed. -/
@[stacks 0DCP]
theorem isAbsolutelyIntegrallyClosed_of_localization (A : Type*) [CommRing A] (B : Type*)
    [CommRing B] [Algebra A B] (S : Submonoid A) [IsLocalization S B] (hS : S ≤ nonZeroDivisors A)
    (hB : IsAbsolutelyIntegrallyClosed B) (hAB : IsIntegrallyClosedIn A B) :
    IsAbsolutelyIntegrallyClosed A := by
  intro f hf
  set φ : A →+* B := algebraMap A B
  obtain ⟨rts, hrts⟩ := hB (f.map φ) (hf.map φ)
  have hroot : ∀ b ∈ rts, IsIntegral A b := by
    intro b hb
    refine ⟨f, hf, ?_⟩
    rw [← eval_map]
    have hdvd : ((X : B[X]) - C b) ∣ f.map φ := by
      rw [hrts]
      exact Multiset.dvd_prod (Multiset.mem_map.mpr ⟨b, hb, rfl⟩)
    exact dvd_iff_isRoot.mp hdvd
  have hmem : ∀ b ∈ rts, ∃ a, φ a = b := fun b hb =>
    IsIntegrallyClosedIn.isIntegral_iff.mp (hroot b hb)
  obtain ⟨rts', hrts'⟩ := Multiset.exists_map_eq_of_forall_mem_range (φ : A → B) rts hmem
  refine ⟨rts', ?_⟩
  have key : f.map φ = ((rts'.map fun a => (X : A[X]) - C a).prod).map φ := by
    rw [hrts, ← hrts', map_multiset_prod_X_sub_C]
  exact Polynomial.map_injective φ (IsLocalization.injective B hS) key

/-- A field is absolutely integrally closed if and only if it is algebraically closed. -/
theorem isAbsolutelyIntegrallyClosed_iff_isAlgClosed (K : Type*) [Field K] :
    IsAbsolutelyIntegrallyClosed K ↔ IsAlgClosed K := by
  rw [isAbsolutelyIntegrallyClosed_iff_exists_root]
  exact ⟨fun h => IsAlgClosed.of_exists_root K fun p hp hirr => h p hp hirr.natDegree_pos,
    fun _ p _ hp => IsAlgClosed.exists_root p (Polynomial.natDegree_pos_iff_degree_pos.mp hp).ne'⟩

/-- **Stacks 0DCQ**.
A normal domain is absolutely integrally closed if and only if its fraction field is
algebraically closed. -/
@[stacks 0DCQ]
theorem isAbsolutelyIntegrallyClosed_iff_isAlgClosed_fractionRing
    (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K] :
    IsAbsolutelyIntegrallyClosed A ↔ IsAlgClosed K := by
  rw [← isAbsolutelyIntegrallyClosed_iff_isAlgClosed]
  exact ⟨isAbsolutelyIntegrallyClosed_localization A (nonZeroDivisors A) K,
    fun h => isAbsolutelyIntegrallyClosed_of_localization A K (nonZeroDivisors A) le_rfl h
      inferInstance⟩
