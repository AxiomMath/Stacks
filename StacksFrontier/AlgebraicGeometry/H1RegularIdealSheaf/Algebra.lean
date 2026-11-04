module

public import Mathlib.RingTheory.Localization.Integer
public import StacksFrontier.RingTheory.Koszul.Relations

/-!
# `H₁`-regularity of a sequence is local on the base

Let `A` be a commutative ring and `f : Fin r → A` a finite sequence.  By
`Koszul.isH1Regular_iff_forall`, `H₁`-regularity of `f` says that every *relation*
`∑ i, a i * f i = 0` lies in the submodule `Koszul.relSpan f ⊆ Aʳ` spanned by the trivial
relations `fᵢ eⱼ - fⱼ eᵢ`.  Written that way the condition is a containment of submodules of
`Aʳ`, and this file supplies the two halves of its local-global principle over the maximal
ideals of `A`.

Both halves are elementary, and neither goes through the Koszul complex.  Clearing denominators
turns a trivial-relation expansion over a localization into one over `A` after multiplying by an
element of the localizing submonoid, and the resulting membership statement is local because the
*conductor* `{t ∈ A | t • a ∈ relSpan f}` is an ideal, so it is the unit ideal as soon as it
escapes every maximal ideal.

This is the commutative-algebra input to the affine-local characterization of `H₁`-regular ideal
sheaves, Stacks tag 063G, for which the localizations are the stalks of the structure sheaf on an
affine open.

## Main results

* `trivRel_map`, `map_mem_relSpan`: the trivial relations and the submodule they span are
  carried into their counterparts by any ring homomorphism.
* `mem_of_forall_maximal_smul`: membership in a submodule is local on the base, in the form in
  which clearing denominators produces it.
* `exists_smul_mem_relSpan`: clearing denominators in a trivial-relation expansion over a
  localization.
* `isH1Regular_localization`: `H₁`-regularity passes to any localization.
* `not_isH1Regular_zero`: `H₁`-regularity is a genuine condition — the sequence `(0)` over a
  nontrivial ring fails it.

## Implementation notes

The localizations are left abstract — an arbitrary `S` with `[IsLocalization T S]` — rather than
taken to be `Localization.AtPrime`, because the intended instances are the stalks of the
structure sheaf of an affine scheme, which are localizations only up to the canonical
isomorphism.

## References

* [Stacks Project, Definition 31.20.1 (Tag 063D)](https://stacks.math.columbia.edu/tag/063D)
* [Stacks Project, Lemma 31.20.4 (Tag 063G)](https://stacks.math.columbia.edu/tag/063G)
-/

@[expose] public section

namespace Stacks.RingTheory.H1RegularIdealSheaf

open Koszul

section Map

variable {A S : Type*} [CommRing A] [CommRing S] {r : ℕ}

/-- A ring homomorphism carries the trivial Koszul relations of a sequence to the trivial Koszul
relations of its image. -/
theorem trivRel_map (ρ : A →+* S) (f : Fin r → A) (i j : Fin r) :
    trivRel (fun k => ρ (f k)) i j = fun k => ρ (trivRel f i j k) := by
  funext k
  rw [trivRel_apply, trivRel_apply, map_sub, apply_ite ρ, apply_ite ρ, map_zero]

/-- A ring homomorphism carries the span of the trivial Koszul relations of a sequence into the
span of the trivial Koszul relations of its image. -/
theorem map_mem_relSpan (ρ : A →+* S) (f : Fin r → A) {w : Fin r → A} (hw : w ∈ relSpan f) :
    (fun k => ρ (w k)) ∈ relSpan (fun k => ρ (f k)) := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    refine Submodule.subset_span (Set.mem_range.mpr ⟨p, ?_⟩)
    exact trivRel_map ρ f p.1 p.2
  | zero => simp [← Pi.zero_def]
  | add x y _ _ hx hy => simpa [Pi.add_def] using Submodule.add_mem _ hx hy
  | smul c x _ hx => simpa [Pi.smul_def] using Submodule.smul_mem _ (ρ c) hx

end Map

section LocalGlobal

/-- **Membership in a submodule is local on the base.** If at every maximal ideal some element
outside it multiplies `a` into `N`, then `a ∈ N`.  The conductor `{t | t • a ∈ N}` is an ideal,
and the hypothesis says it is contained in no maximal ideal. -/
theorem mem_of_forall_maximal_smul {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M]
    [Module A M] (N : Submodule A M) (a : M)
    (h : ∀ m : Ideal A, m.IsMaximal → ∃ t : A, t ∉ m ∧ t • a ∈ N) : a ∈ N := by
  by_contra hna
  set K : Ideal A := N.comap (LinearMap.toSpanSingleton A M a) with hKdef
  have hmemK : ∀ t : A, t ∈ K ↔ t • a ∈ N := fun _ => Iff.rfl
  have hKne : K ≠ ⊤ := by
    intro htop
    have h1 : (1 : A) ∈ K := by rw [htop]; exact Submodule.mem_top
    have h2 : (1 : A) • a ∈ N := (hmemK 1).mp h1
    rw [one_smul] at h2
    exact hna h2
  obtain ⟨m, hm, hKm⟩ := Ideal.exists_le_maximal K hKne
  obtain ⟨t, htm, hta⟩ := h m hm
  exact htm (hKm ((hmemK t).mpr hta))

end LocalGlobal

section Localization

/-- Two vectors over `A` with the same image in a localization are made equal by multiplying by
a single element of the localizing submonoid. -/
theorem exists_smul_eq_of_algebraMap_eq {A : Type*} [CommRing A] (T : Submonoid A) (S : Type*)
    [CommRing S] [Algebra A S] [IsLocalization T S] {n : ℕ} (x y : Fin n → A)
    (h : ∀ k, algebraMap A S (x k) = algebraMap A S (y k)) : ∃ u ∈ T, u • x = u • y := by
  choose s hs using fun k => (IsLocalization.eq_iff_exists T S).mp (h k)
  refine ⟨∏ k, ((s k : A)), prod_mem fun k _ => (s k).2, ?_⟩
  funext k
  have hsplit : (∏ j, ((s j : A))) = (s k : A) * ∏ j ∈ Finset.univ.erase k, ((s j : A)) :=
    (Finset.mul_prod_erase Finset.univ (fun j => ((s j : A))) (Finset.mem_univ k)).symm
  simp only [Pi.smul_apply, smul_eq_mul]
  calc (∏ j, ((s j : A))) * x k
      = (∏ j ∈ Finset.univ.erase k, ((s j : A))) * ((s k : A) * x k) := by rw [hsplit]; ring
    _ = (∏ j ∈ Finset.univ.erase k, ((s j : A))) * ((s k : A) * y k) := by rw [hs k]
    _ = (∏ j, ((s j : A))) * y k := by rw [hsplit]; ring

/-- **Clearing denominators in a trivial-relation expansion.** If the image of `a` in a
localization lies in the span of the trivial relations of the image of `f`, then some element of
the localizing submonoid multiplies `a` into the span of the trivial relations of `f`. -/
theorem exists_smul_mem_relSpan {A : Type*} [CommRing A] (T : Submonoid A) (S : Type*)
    [CommRing S] [Algebra A S] [IsLocalization T S] {r : ℕ} (f a : Fin r → A)
    (h : (fun i => algebraMap A S (a i)) ∈ relSpan fun i => algebraMap A S (f i)) :
    ∃ t ∈ T, t • a ∈ relSpan f := by
  rw [relSpan, Submodule.mem_span_range_iff_exists_fun] at h
  obtain ⟨c, hc⟩ := h
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples T Finset.univ c
  choose d hd using fun p => hb p (Finset.mem_univ p)
  set w : Fin r → A := ∑ p : Fin r × Fin r, d p • trivRel f p.1 p.2 with hwdef
  have hwmem : w ∈ relSpan f :=
    Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (trivRel_mem_relSpan f p.1 p.2)
  have key : (fun k => algebraMap A S (w k))
      = algebraMap A S (b : A) • fun k => algebraMap A S (a k) := by
    funext k
    have hak : algebraMap A S (a k)
        = ∑ p : Fin r × Fin r, c p * trivRel (fun i => algebraMap A S (f i)) p.1 p.2 k := by
      conv_lhs => rw [← congrFun hc k]
      simp [Finset.sum_apply, smul_eq_mul]
    have hwk : algebraMap A S (w k)
        = ∑ p : Fin r × Fin r, algebraMap A S (b : A) *
            (c p * trivRel (fun i => algebraMap A S (f i)) p.1 p.2 k) := by
      rw [hwdef]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [hd p, Algebra.smul_def, ← congrFun (trivRel_map (algebraMap A S) f p.1 p.2) k,
        mul_assoc]
    rw [hwk, Pi.smul_apply, hak, smul_eq_mul, Finset.mul_sum]
  have hmapw : ∀ k, algebraMap A S (((b : A) • a) k) = algebraMap A S (w k) := by
    intro k
    rw [congrFun key k]
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  obtain ⟨u, huT, hu⟩ := exists_smul_eq_of_algebraMap_eq T S ((b : A) • a) w hmapw
  refine ⟨u * (b : A), mul_mem huT b.2, ?_⟩
  rw [mul_smul, hu]
  exact Submodule.smul_mem _ _ hwmem

/-- **`H₁`-regularity passes to a localization.** -/
theorem isH1Regular_localization {A : Type*} [CommRing A] (T : Submonoid A) (S : Type*)
    [CommRing S] [Algebra A S] [IsLocalization T S] {r : ℕ} (f : Fin r → A)
    (hf : IsH1Regular f) : IsH1Regular fun i => algebraMap A S (f i) := by
  rw [isH1Regular_iff_forall] at hf ⊢
  intro α hα
  obtain ⟨t, ht⟩ := IsLocalization.exist_integer_multiples T Finset.univ α
  choose a ha using fun k => ht k (Finset.mem_univ k)
  have hrel : algebraMap A S (∑ k, a k * f k) = 0 := by
    rw [map_sum]
    have hterm : ∀ k, algebraMap A S (a k * f k)
        = (t : A) • (α k * algebraMap A S (f k)) := by
      intro k
      rw [map_mul, ha k, Algebra.smul_def, Algebra.smul_def]
      ring
    rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => hterm k, ← Finset.smul_sum, hα,
      smul_zero]
  have hrel0 : algebraMap A S (∑ k, a k * f k) = algebraMap A S 0 := by rw [hrel, map_zero]
  obtain ⟨t', ht'⟩ := (IsLocalization.eq_iff_exists T S).mp hrel0
  have hzero : ∑ k, ((t' : A) * a k) * f k = 0 := by
    have hre : ∑ k, ((t' : A) * a k) * f k = (t' : A) * ∑ k, a k * f k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hre, ht', mul_zero]
  have hmem := map_mem_relSpan (algebraMap A S) f (hf _ hzero)
  have hval : (fun k => algebraMap A S ((t' : A) * a k))
      = algebraMap A S ((t' : A) * (t : A)) • α := by
    funext k
    have h1 : algebraMap A S ((t' : A) * a k)
        = algebraMap A S (t' : A) * (algebraMap A S (t : A) * α k) := by
      rw [map_mul, ha k, Algebra.smul_def]
    rw [h1, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]
  rw [hval] at hmem
  obtain ⟨v, hv⟩ := IsLocalization.map_units S (⟨(t' : A) * (t : A), mul_mem t'.2 t.2⟩ : T)
  rw [← hv] at hmem
  have hα' : α = ((v⁻¹ : Sˣ) : S) • (((v : Sˣ) : S) • α) := by
    rw [smul_smul, Units.inv_mul, one_smul]
  rw [hα']
  exact Submodule.smul_mem _ _ hmem

end Localization

section Nondegeneracy

/-- **`H₁`-regularity is a genuine condition.** The one-term sequence `(0)` over a nontrivial
ring is not `H₁`-regular: its only trivial relation is `0`, so the span of the trivial relations
is `⊥`, while every element of the ring is a relation.  Recorded because the affine criterion of
Stacks tag 063G identifies the sheaf-theoretic condition with this one, and an identification
with a condition that always held would say nothing. -/
theorem not_isH1Regular_zero {A : Type*} [CommRing A] [Nontrivial A] :
    ¬ IsH1Regular (fun _ : Fin 1 => (0 : A)) := by
  rw [isH1Regular_iff_forall]
  intro h
  have hbot : relSpan (fun _ : Fin 1 => (0 : A)) = ⊥ := by
    rw [relSpan, Submodule.span_eq_bot]
    rintro x ⟨p, rfl⟩
    funext k
    simp [trivRel]
  have hmem := h (fun _ : Fin 1 => (1 : A)) (by simp)
  rw [hbot, Submodule.mem_bot] at hmem
  exact one_ne_zero (congrFun hmem 0)

end Nondegeneracy

end Stacks.RingTheory.H1RegularIdealSheaf

end
