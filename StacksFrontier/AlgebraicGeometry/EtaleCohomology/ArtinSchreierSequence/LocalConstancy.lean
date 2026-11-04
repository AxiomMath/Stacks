module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Artin–Schreier roots of zero are locally constant

Let `A` be a commutative ring in which a prime `p` vanishes and let `x` be an element of `A` with
`x ^ p = x`. Then `x` is locally constant with values in `𝐅_p`: for every prime `𝔭` of `A` there
is an `i < p` and an `f` outside `𝔭` such that `x = i` in the localization `A_f`. Equivalently,
the standard opens on which `x` takes each of the `p` constant values cover `Spec A`.

This is the only non-formal input to the identification of the kernel of the Artin–Schreier map
`x ↦ x ^ p - x` on `𝐆_a` with the constant sheaf `𝐙/p𝐙`.

## Main results

* `Stacks.ArtinSchreier.prod_X_pow_sub_X`: `X ^ p - X = ∏_{i ∈ 𝐅_p} (X - i)` over `𝐅_p`.
* `Stacks.ArtinSchreier.prod_sub_castHom`: the same identity evaluated in a ring of
  characteristic `p`.
* `Stacks.ArtinSchreier.exists_castHom_eq_of_pow_eq`: in a domain of characteristic `p`, an
  element with `x ^ p = x` lies in the prime field.
* `Stacks.ArtinSchreier.exists_notMem_and_algebraMap_eq`: the local constancy statement.

## Implementation notes

The factorization of `X ^ p - X` over `𝐅_p` comes from `FiniteField.roots_X_pow_card_sub_X`,
which says that every element of a finite field is a root, together with the degree count: a
monic polynomial whose multiset of roots has as many elements as its degree is the product of the
corresponding linear factors.

The passage from a domain to a general ring is by localization rather than by the Chinese
remainder theorem. Given `𝔭`, the residue class of `x` is some `i` in the prime field; the
element `f = ∏_{j ≠ i} (x - j)` is then outside `𝔭`, because modulo `𝔭` it is the image of the
nonzero scalar `∏_{j ≠ i} (i - j)`, and `(x - i) * f = x ^ p - x = 0`, so inverting `f` forces
`x = i`. No nontriviality hypothesis is needed on `A`: the presence of a prime ideal supplies it.

## References

* [Stacks Project, Tag 0A3J](https://stacks.math.columbia.edu/tag/0A3J): the Artin–Schreier
  sequence, whose left term is the constant sheaf identified by this statement.
-/

@[expose] public section

open Polynomial

universe u

namespace Stacks.ArtinSchreier

/-- **`X ^ p - X` splits into distinct linear factors over `𝐅_p`**: every element of `𝐅_p` is a
root, and there are as many of them as the degree. -/
theorem prod_X_pow_sub_X (p : ℕ) [Fact p.Prime] :
    (X ^ p - X : (ZMod p)[X]) = ∏ i : ZMod p, (X - C i) := by
  have hp1 : (1 : ℕ) < p := (Fact.out (p := p.Prime)).one_lt
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have hmonic : (X ^ p - X : (ZMod p)[X]).Monic :=
    monic_X_pow_sub (lt_of_le_of_lt degree_X_le (by exact_mod_cast hp1))
  have hroots : (X ^ p - X : (ZMod p)[X]).roots = Finset.univ.val := by
    simpa [hcard] using FiniteField.roots_X_pow_card_sub_X (ZMod p)
  have key := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic
    (by rw [hroots, FiniteField.X_pow_card_sub_X_natDegree_eq _ hp1]; simp [hcard])
  rw [hroots] at key
  exact key.symm

/-- **The Artin–Schreier polynomial factors into scalars in characteristic `p`**:
`∏_{i ∈ 𝐅_p} (x - i) = x ^ p - x` for every element `x` of a ring of characteristic `p`. -/
theorem prod_sub_castHom {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime] [CharP A p] (x : A) :
    ∏ i : ZMod p, (x - (ZMod.castHom (dvd_refl p) A) i) = x ^ p - x := by
  have hmap := congrArg (Polynomial.map (ZMod.castHom (dvd_refl p) A)) (prod_X_pow_sub_X p)
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_prod,
    Polynomial.map_C] at hmap
  simpa [Polynomial.eval_prod] using (congrArg (fun q => Polynomial.eval x q) hmap).symm

/-- **In a domain of characteristic `p`, a solution of `x ^ p = x` lies in the prime field.** -/
theorem exists_castHom_eq_of_pow_eq {A : Type u} [CommRing A] [IsDomain A] {p : ℕ}
    (hp : p.Prime) (hA : (p : A) = 0) (x : A) (hx : x ^ p = x) :
    ∃ i : ℕ, i < p ∧ x = (i : A) := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have : CharP A p := (CharP.charP_iff_prime_eq_zero hp).mpr hA
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp
    (show ∏ j : ZMod p, (x - (ZMod.castHom (dvd_refl p) A) j) = 0 by
      rw [prod_sub_castHom, hx, sub_self])
  refine ⟨i.val, ZMod.val_lt i, ?_⟩
  rw [ZMod.natCast_val]
  exact sub_eq_zero.mp hi

/-- **A solution of `x ^ p = x` is locally constant.** For `A` a commutative ring in which the
prime `p` vanishes, `x` an element with `x ^ p = x`, and `𝔭` a prime of `A`, there are an `i < p`
and an `f` outside `𝔭` with `x = i` in `A_f`.

The residue class of `x` modulo `𝔭` is one of the `p` scalars, say `i`; then
`f = ∏_{j ≠ i} (x - j)` avoids `𝔭` and kills `x - i`. -/
theorem exists_notMem_and_algebraMap_eq {A : Type u} [CommRing A] {p : ℕ} (hp : p.Prime)
    (hA : (p : A) = 0) (x : A) (hx : x ^ p = x) (𝔭 : Ideal A) [𝔭.IsPrime] :
    ∃ (i : ℕ) (f : A), i < p ∧ f ∉ 𝔭 ∧
      algebraMap A (Localization.Away f) x = (i : Localization.Away f) := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Nontrivial A := by
    refine ⟨0, 1, fun h => (Ideal.IsPrime.ne_top ‹𝔭.IsPrime›) ?_⟩
    exact (Ideal.eq_top_iff_one _).2 (h ▸ 𝔭.zero_mem)
  have : CharP A p := (CharP.charP_iff_prime_eq_zero hp).mpr hA
  have : IsDomain (A ⧸ 𝔭) := inferInstance
  have : CharP (A ⧸ 𝔭) p := (CharP.charP_iff_prime_eq_zero hp).mpr (by
    have h := congrArg (Ideal.Quotient.mk 𝔭) hA
    rwa [map_natCast, map_zero] at h)
  set c : ZMod p → A := fun j => (ZMod.castHom (dvd_refl p) A) j with hc
  have hmkc (j : ZMod p) :
      (Ideal.Quotient.mk 𝔭) (c j) = (ZMod.castHom (dvd_refl p) (A ⧸ 𝔭)) j :=
    congrFun (congrArg (fun (g : ZMod p →+* A ⧸ 𝔭) => (g : ZMod p → A ⧸ 𝔭))
      (RingHom.ext_zmod ((Ideal.Quotient.mk 𝔭).comp (ZMod.castHom (dvd_refl p) A))
        (ZMod.castHom (dvd_refl p) (A ⧸ 𝔭)))) j
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp
    (show ∏ j : ZMod p,
        ((Ideal.Quotient.mk 𝔭) x - (ZMod.castHom (dvd_refl p) (A ⧸ 𝔭)) j) = 0 by
      rw [prod_sub_castHom, ← map_pow, ← map_sub, hx, sub_self, map_zero])
  rw [sub_eq_zero] at hi
  set f : A := ∏ j ∈ Finset.univ.erase i, (x - c j) with hf
  have hfactor : (x - c i) * f = 0 := by
    rw [hf, Finset.mul_prod_erase Finset.univ (fun j => x - c j) (Finset.mem_univ i),
      prod_sub_castHom, hx, sub_self]
  have hfp : f ∉ 𝔭 := by
    intro hmem
    have hzero : (Ideal.Quotient.mk 𝔭) f = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hmem
    rw [hf, map_prod] at hzero
    simp only [map_sub, hi, hmkc] at hzero
    obtain ⟨j, hj, hj0⟩ := Finset.prod_eq_zero_iff.mp hzero
    rw [sub_eq_zero] at hj0
    exact (Finset.mem_erase.mp hj).1
      ((ZMod.castHom (dvd_refl p) (A ⧸ 𝔭)).injective hj0).symm
  refine ⟨i.val, f, ZMod.val_lt i, hfp, ?_⟩
  have h0 : (algebraMap A (Localization.Away f)) x = (algebraMap A (Localization.Away f)) (c i) :=
    sub_eq_zero.mp (by
      rw [← map_sub]
      exact (IsLocalization.Away.algebraMap_isUnit f).mul_left_eq_zero.mp
        (by rw [← map_mul, hfactor, map_zero]))
  have hci : c i = ((i.val : ℕ) : A) := by simp [hc, ZMod.castHom_apply, ZMod.natCast_val]
  rw [h0, hci, map_natCast]

end Stacks.ArtinSchreier

end
