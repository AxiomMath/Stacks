module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.WittVector.Teichmuller
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.RootExtraction
public import StacksFrontier.RingTheory.Henselian.Pair.LocalRing
public import StacksFrontier.RingTheory.Henselian.Pair.Nilpotent
public import StacksFrontier.RingTheory.Henselian.Pair.Operations
public import StacksFrontier.RingTheory.WittVector.Approximation

/-!
# Surjectivity of `F - 1` on Witt vectors

Let `p` be a prime. For a henselian local ring `R` of characteristic `p` with separably closed
residue field and a finite `R`-algebra `T`, the Artin–Schreier map `x ↦ x ^ p - x` is surjective
on `T`, and the map `F - 1` is surjective on the ring `W(T)` of (big `p`-typical) Witt vectors,
where `F` is the Witt vector Frobenius.

## Main results

* `Stacks.ArtinSchreier.exists_pow_sub_self_eq_of_henselianPair`: if `(B, J)` is a henselian pair
  in characteristic `p` and `x ↦ x ^ p - x` is surjective on `B ⧸ J`, then it is surjective on `B`.
* `Stacks.ArtinSchreier.exists_pow_sub_self_eq_of_finite_of_isSepClosed`: `x ↦ x ^ p - x` is
  surjective on a finite algebra over a separably closed field of characteristic `p`.
* `Stacks.ArtinSchreier.exists_pow_sub_self_eq_of_henselianLocalRing`: `x ↦ x ^ p - x` is
  surjective on a finite algebra over a henselian local ring of characteristic `p` with separably
  closed residue field.
* `Stacks.ArtinSchreier.exists_frobenius_sub_self_eq`: if `x ↦ x ^ p - x` is surjective on a ring
  `R` in which `p = 0`, then `F - 1` is surjective on `W(R)`.
* `Stacks.ArtinSchreier.exists_frobenius_sub_self_eq_of_henselianLocalRing`: the combination.

## Implementation notes

The polynomial `X ^ p - X - a` has derivative `-1`, so `T[X]/(X ^ p - X - a)` is étale over `T`
and a root modulo an ideal `J` lifts along any henselian pair `(T, J)`. Over a henselian local
ring `R`, the pair `(T, 𝔪_R T)` is henselian; the quotient `T ⧸ 𝔪_R T` is a finite algebra over
the residue field, henselian along its nilradical, and reduced modulo it to a finite product of
fields, each algebraic over the separably closed residue field and hence separably closed.

On Witt vectors, a solution of `F b - b = a` is built coefficient by coefficient: if
`F b - b - a = V^n z`, then adding `V^n t` with `t` the Teichmüller lift of a root of
`X ^ p - X + z₀` kills the coefficient of index `n`, because `F` commutes with `V` in
characteristic `p`. The successive approximations converge coefficientwise to
`WittVector.truncLimit`, and the limit is detected on truncations.
-/

@[expose] public section

open Polynomial IsLocalRing WittVector

universe u v

namespace Stacks.ArtinSchreier

variable {p : ℕ}

/-- If `(B, J)` is a henselian pair in which `p = 0`, and every element of `B ⧸ J` has the form
`d ^ p - d`, then every element of `B` has the form `b ^ p - b`. -/
theorem exists_pow_sub_self_eq_of_henselianPair {B : Type u} [CommRing B] {J : Ideal B}
    (hJ : HenselianPair B J) (hp : 1 < p) (hchar : (p : B) = 0)
    (h : ∀ c : B ⧸ J, ∃ d, d ^ p - d = c) (a : B) : ∃ b, b ^ p - b = a := by
  obtain ⟨c, hc⟩ := h (Ideal.Quotient.mk J a)
  have := etale_adjoinRootAS a hp hchar
  have hroot : (X ^ p - X - C a).eval₂ (Algebra.ofId B (B ⧸ J) : B →+* B ⧸ J) c = 0 := by
    simp [hc]
  have hlift := ((henselianPair_tfae.{u, u} B J).out 1 2).mp hJ
  obtain ⟨τ, -⟩ := hlift (AdjoinRoot (X ^ p - X - C a))
    (AdjoinRoot.liftAlgHom _ (Algebra.ofId B (B ⧸ J)) c hroot)
  refine ⟨τ (AdjoinRoot.root _), ?_⟩
  rw [← map_pow, ← map_sub, root_pow_sub_root, AlgHom.commutes, Algebra.algebraMap_self,
    RingHom.id_apply]

/-- In a separably closed field in which `p = 0`, every element has the form `b ^ p - b`. -/
theorem exists_pow_sub_self_eq_of_isSepClosed {L : Type*} [Field L] [IsSepClosed L]
    (hp : 1 < p) (hchar : (p : L) = 0) (a : L) : ∃ b, b ^ p - b = a := by
  obtain ⟨x, hx⟩ := IsSepClosed.exists_root_C_mul_X_pow_add_C_mul_X_add_C (1 : L) (-1) (-a)
    hchar hp (by simp)
  exact ⟨x, by linear_combination hx⟩

/-- In a finite algebra over a separably closed field, in which `p = 0`, every element has the
form `b ^ p - b`. -/
theorem exists_pow_sub_self_eq_of_finite_of_isSepClosed {k : Type v} {B : Type u} [Field k]
    [IsSepClosed k] [CommRing B] [Algebra k B] [Module.Finite k B] (hp : 1 < p)
    (hchar : (p : B) = 0) (a : B) : ∃ b, b ^ p - b = a := by
  have : IsArtinianRing B := IsArtinianRing.of_finite k B
  have hnil : HenselianPair B (nilradical B) :=
    have := (etaleBaseChange_isEquivalence_and_henselianRing_of_le_nilradical (nilradical B)
      le_rfl).2
    henselianPair_of_henselianRing B (nilradical B)
  refine exists_pow_sub_self_eq_of_henselianPair hnil hp hchar (fun c ↦ ?_) a
  let e := IsArtinianRing.quotNilradicalEquivPi B
  have hm (m : MaximalSpectrum B) : ∃ d : B ⧸ m.asIdeal, d ^ p - d = e c m := by
    let : Field (B ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
    have : Module.Finite k (B ⧸ m.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ k m.asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    have : IsSepClosed (B ⧸ m.asIdeal) := Algebra.IsAlgebraic.isSepClosed (F := k)
    exact exists_pow_sub_self_eq_of_isSepClosed hp
      (by simpa using congrArg (Ideal.Quotient.mk m.asIdeal) hchar) _
  choose d hd using hm
  refine ⟨e.symm d, e.injective ?_⟩
  rw [map_sub, map_pow, e.apply_symm_apply]
  exact funext hd

/-- Let `R` be a henselian local ring of characteristic `p` whose residue field is separably
closed. Then every element of a finite `R`-algebra `T` has the form `b ^ p - b`. -/
theorem exists_pow_sub_self_eq_of_henselianLocalRing (p : ℕ) [Fact p.Prime]
    (R : Type u) [CommRing R] [HenselianLocalRing R] [IsSepClosed (ResidueField R)] [CharP R p]
    {T : Type v} [CommRing T] [Algebra R T] [Module.Finite R T] (a : T) :
    ∃ b : T, b ^ p - b = a := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hcharT : (p : T) = 0 := by
    rw [← map_natCast (algebraMap R T), CharP.cast_eq_zero, map_zero]
  set I := (maximalIdeal R).map (algebraMap R T)
  have hI : HenselianPair T I := henselianPair_map_of_isIntegral _ (henselianPair_maximalIdeal R)
  refine exists_pow_sub_self_eq_of_henselianPair hI hp hcharT (fun c ↦ ?_) a
  let : Algebra (ResidueField R) (T ⧸ I) :=
    (Ideal.quotientMap I (algebraMap R T) Ideal.le_comap_map).toAlgebra
  have : IsScalarTower R (ResidueField R) (T ⧸ I) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Module.Finite R (T ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ R I).toLinearMap Ideal.Quotient.mk_surjective
  have : Module.Finite (ResidueField R) (T ⧸ I) :=
    Module.Finite.of_restrictScalars_finite R _ _
  exact exists_pow_sub_self_eq_of_finite_of_isSepClosed (k := ResidueField R) hp
    (by simpa using congrArg (Ideal.Quotient.mk I) hcharT) c

section WittVector

variable [Fact p.Prime] {R : Type u} [CommRing R]

/-- Let `R` be a ring in which `p = 0` and every element has the form `d ^ p - d`. Then every
Witt vector `a` over `R` has the form `F b - b`, where `F` is the Witt vector Frobenius. -/
theorem exists_frobenius_sub_self_eq (hchar : (p : R) = 0)
    (h : ∀ c : R, ∃ d, d ^ p - d = c) (a : WittVector p R) :
    ∃ b : WittVector p R, frobenius b - b = a := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨0, WittVector.ext fun _ ↦ Subsingleton.elim _ _⟩
  have : CharP R p := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hchar
  choose s hs using h
  let D : WittVector p R → WittVector p R := fun x ↦ frobenius x - x - a
  let t : WittVector p R → ℕ → WittVector p R := fun x n ↦ teichmuller p (s (-(D x).coeff n))
  let b : ℕ → WittVector p R := fun n ↦
    Nat.rec 0 (fun n x ↦ x + verschiebung^[n] (t x n)) n
  have hb (n : ℕ) : b (n + 1) = b n + verschiebung^[n] (t (b n) n) := rfl
  have hD (n : ℕ) : ∀ i < n, (D (b n)).coeff i = 0 := by
    induction n with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
    | succ n ih =>
      set z := (D (b n)).shift n
      set w := z + (frobenius (t (b n) n) - t (b n) n)
      have hcomm : frobenius (verschiebung^[n] (t (b n) n)) =
          verschiebung^[n] (frobenius (t (b n) n)) :=
        ((verschiebung_frobenius_comm (p := p) (R := R)).iterate_left n _).symm
      have hDn : D (b (n + 1)) = verschiebung^[n] w := by
        rw [iterate_map_add, ← eq_iterate_verschiebung ih, iterate_map_sub, ← hcomm]
        simp only [D, hb, map_add]
        abel
      have hw : w.coeff 0 = 0 := by
        have h0 := hs (-(D (b n)).coeff n)
        simp only [w, z, add_coeff_zero, shift_coeff, add_zero]
        rw [← WittVector.constantCoeff_apply, map_sub, WittVector.constantCoeff_apply,
          WittVector.constantCoeff_apply, coeff_frobenius_charP]
        simp only [t, teichmuller_coeff_zero, h0, add_neg_cancel]
      intro i hi
      rw [hDn]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact iterate_verschiebung_coeff_eq_zero _ hi
      · simpa using (iterate_verschiebung_coeff w i 0).trans hw
  have hB := truncate_truncLimit (p := p) (x := b) fun n ↦ by
    rw [hb, map_add, truncate_iterate_verschiebung, add_zero]
  refine ⟨truncLimit p b, sub_eq_zero.mp (WittVector.ext fun n ↦ ?_)⟩
  have hDB : truncate (n + 1) (D (truncLimit p b)) = truncate (n + 1) (D (b (n + 1))) := by
    simp only [D, map_sub, truncate_frobenius_eq_of_truncate_eq (hB (n + 1)), hB (n + 1)]
  rw [zero_coeff]
  exact (truncate_eq_truncate_iff.1 hDB n (Nat.lt_succ_self n)).trans
    (hD (n + 1) n (Nat.lt_succ_self n))

/-- Let `R` be a henselian local ring of characteristic `p` whose residue field is separably
closed, and let `T` be a finite `R`-algebra. Then every Witt vector `a` over `T` has the form
`F b - b`, where `F` is the Witt vector Frobenius. -/
theorem exists_frobenius_sub_self_eq_of_henselianLocalRing
    (R : Type u) [CommRing R] [HenselianLocalRing R] [IsSepClosed (ResidueField R)] [CharP R p]
    {T : Type v} [CommRing T] [Algebra R T] [Module.Finite R T] (a : WittVector p T) :
    ∃ b : WittVector p T, frobenius b - b = a :=
  exists_frobenius_sub_self_eq
    (by rw [← map_natCast (algebraMap R T), CharP.cast_eq_zero, map_zero])
    (exists_pow_sub_self_eq_of_henselianLocalRing p R) a

end WittVector

end Stacks.ArtinSchreier
