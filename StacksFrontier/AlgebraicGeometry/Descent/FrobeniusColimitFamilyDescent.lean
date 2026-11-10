module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitRingSections

/-!
# Descending finitely many sections of `colim_F 𝒪_X` at once

Let `p` be a prime and let `X` be a quasi-separated scheme in characteristic `p`. Over a
quasi-compact open, every section of `colim_F 𝒪_X` is the image of a section of `𝒪_X` at some
finite stage, and two sections of `𝒪_X` with the same image agree after enough Frobenius twists
(`AlgebraicGeometry.exists_frobeniusStructureSheafι_app_eq` and
`AlgebraicGeometry.exists_pow_eq_of_frobeniusStructureSheafι_app_eq`). A descent argument needs
both statements for a *finite family* of sections at once, with one stage and one exponent
serving the whole family: that is what this file provides, by taking the supremum of the finitely
many stages, resp. exponents, and raising each member to the appropriate power.

The device that makes raising harmless is that on a scheme in characteristic `p` the `p ^ k`-th
power map is a ring endomorphism of the sections over every open — `Stacks.Frobenius`'s
`primePowerEndomorphism` iterated — so a relation among sections built from sums and products
survives being raised, and `AlgebraicGeometry.frobeniusStructureSheafι_pow_app` says the raised
section has the same image one stage further along.

## Main definitions

* `Stacks.Frobenius.primePowerIterate`: the `k`-fold iterate of the `p`-th power endomorphism,
  as a ring homomorphism.

## Main results

* `Stacks.Frobenius.sum_pow_prime_pow`: **raising a finite sum to the `p ^ k`-th power raises
  each summand**, in a commutative ring in which `p` vanishes.
* `Stacks.Frobenius.pow_prime_pow_eq_of_le`: an equality of `p ^ k`-th powers persists at every
  larger exponent.
* `AlgebraicGeometry.exists_frobeniusStructureSheafι_app_eq_family`: **a finite family of
  sections of `colim_F 𝒪_X` over quasi-compact opens comes from one finite stage.**
* `AlgebraicGeometry.exists_pow_eq_of_frobeniusStructureSheafι_app_eq_family`: **a finite family
  of pairs of sections of `𝒪_X` with equal images in `colim_F 𝒪_X` agrees after one common
  Frobenius twist.**

## References

* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Frobenius TopologicalSpace

universe u

namespace Stacks.Frobenius

/-- The `k`-fold iterate of the `p`-th power endomorphism of a commutative ring in which the
prime `p` vanishes. -/
noncomputable def primePowerIterate (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hp : (p : R) = 0) : ℕ → (R →+* R)
  | 0 => RingHom.id R
  | k + 1 => (primePowerEndomorphism R p hp).comp (primePowerIterate R p hp k)

/-- The `k`-fold iterate of the `p`-th power endomorphism raises to the `p ^ k`-th power. -/
lemma primePowerIterate_apply (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hp : (p : R) = 0) (k : ℕ) (x : R) : primePowerIterate R p hp k x = x ^ p ^ k := by
  induction k with
  | zero => simp [primePowerIterate]
  | succ k ih =>
      change (primePowerEndomorphism R p hp) (primePowerIterate R p hp k x) = _
      rw [ih, primePowerEndomorphism_apply, ← pow_mul, ← pow_succ]

/-- **Raising a finite sum to the `p ^ k`-th power raises each summand**, in a commutative ring
in which the prime `p` vanishes. -/
lemma sum_pow_prime_pow {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] (hp : (p : R) = 0)
    (k : ℕ) {ι : Type*} (s : Finset ι) (f : ι → R) :
    (∑ i ∈ s, f i) ^ p ^ k = ∑ i ∈ s, f i ^ p ^ k := by
  simpa only [primePowerIterate_apply] using map_sum (primePowerIterate R p hp k) f s

/-- An equality of `p ^ k`-th powers persists at every larger exponent. -/
lemma pow_prime_pow_eq_of_le {R : Type*} [Monoid R] {p : ℕ} {x y : R} {k K : ℕ} (hk : k ≤ K)
    (h : x ^ p ^ k = y ^ p ^ k) : x ^ p ^ K = y ^ p ^ K := by
  have hK : p ^ K = p ^ k * p ^ (K - k) := by
    rw [← pow_add]; congr 1; omega
  rw [hK, pow_mul, pow_mul, h]

end Stacks.Frobenius

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)

include hX in
/-- Raising a finite sum of sections of the structure sheaf to the `p ^ k`-th power raises each
summand: the scheme is in characteristic `p`. -/
lemma sum_pow_prime_pow_sections (V : X.Opens) (k : ℕ) {ι : Type*} (s : Finset ι)
    (f : ι → Γ(X, V)) : (∑ i ∈ s, f i) ^ p ^ k = ∑ i ∈ s, f i ^ p ^ k :=
  Stacks.Frobenius.sum_pow_prime_pow (cast_eq_zero_of_isInCharacteristic hX V) k s f

/-- **A finite family of sections of `colim_F 𝒪_X` over quasi-compact opens comes from one
finite stage.** -/
theorem exists_frobeniusStructureSheafι_app_eq_family [QuasiSeparatedSpace X] {T : Type*}
    [Finite T] (U : T → X.Opens) (hU : ∀ i, IsCompact (U i : Set X))
    (s : ∀ i, ToType ((frobeniusColimitRingSheaf X p hX).obj.obj (op (U i)))) :
    ∃ (n : ℕ) (a : ∀ i, Γ(X, U i)),
      ∀ i, (frobeniusStructureSheafι X p hX n).hom.app (op (U i)) (a i) = s i := by
  classical
  have := Fintype.ofFinite T
  choose nn aa haa using fun i =>
    exists_frobeniusStructureSheafι_app_eq X p hX (U i) (hU i) (s i)
  refine ⟨Finset.univ.sup nn, fun i => aa i ^ p ^ (Finset.univ.sup nn - nn i), fun i => ?_⟩
  have hle : nn i ≤ Finset.univ.sup nn := Finset.le_sup (Finset.mem_univ i)
  have he : nn i + (Finset.univ.sup nn - nn i) = Finset.univ.sup nn := by omega
  rw [show (frobeniusStructureSheafι X p hX (Finset.univ.sup nn)).hom.app (op (U i))
        (aa i ^ p ^ (Finset.univ.sup nn - nn i))
      = (frobeniusStructureSheafι X p hX (nn i + (Finset.univ.sup nn - nn i))).hom.app
        (op (U i)) (aa i ^ p ^ (Finset.univ.sup nn - nn i)) by rw [he],
    frobeniusStructureSheafι_pow_app, haa i]

/-- **A finite family of pairs of sections of `𝒪_X` over quasi-compact opens with equal images
in `colim_F 𝒪_X` agrees after one common Frobenius twist.** -/
theorem exists_pow_eq_of_frobeniusStructureSheafι_app_eq_family {T : Type*} [Finite T]
    (U : T → X.Opens) (hU : ∀ i, IsCompact (U i : Set X)) (n : ℕ) (a b : ∀ i, Γ(X, U i))
    (h : ∀ i, (frobeniusStructureSheafι X p hX n).hom.app (op (U i)) (a i)
      = (frobeniusStructureSheafι X p hX n).hom.app (op (U i)) (b i)) :
    ∃ k : ℕ, ∀ i, a i ^ p ^ k = b i ^ p ^ k := by
  classical
  have := Fintype.ofFinite T
  choose kk hkk using fun i =>
    exists_pow_eq_of_frobeniusStructureSheafι_app_eq X p hX (U i) (hU i) n (a i) (b i) (h i)
  exact ⟨Finset.univ.sup kk, fun i =>
    Stacks.Frobenius.pow_prime_pow_eq_of_le (Finset.le_sup (Finset.mem_univ i)) (hkk i)⟩

end AlgebraicGeometry

end
