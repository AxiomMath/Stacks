module

public import Mathlib.Algebra.Homology.Embedding.Extend

/-!
# An `ℕ`-indexed complex extended by zero, identified with a `ℤ`-indexed one

A cochain complex indexed by `ℤ` which vanishes in negative degrees is the extension by zero
along `ComplexShape.embeddingUpNat` of its restriction to the nonnegative degrees. This file
proves this in the following form: given a cochain complex `K` indexed by `ℕ`, a cochain complex
`L` indexed by `ℤ` vanishing in negative degrees, and isomorphisms `K^n ≅ L^n` commuting with the
differentials, the extension of `K` is isomorphic to `L`.

## Main definitions

* `HomologicalComplex.extendUpNatXIso`: the comparison in a single degree, which is the
  identification `(K.extend e)^{(n)} ≅ K^n` of `HomologicalComplex.extendXIso` followed by the
  given isomorphism in nonnegative degrees, and the unique map between two zero objects in
  negative degrees.
* `HomologicalComplex.extendUpNatIso`: **the isomorphism `K.extend e ≅ L` of complexes.**

## Main results

* `HomologicalComplex.isZero_extend_X_of_neg`: the extension by zero along
  `ComplexShape.embeddingUpNat` vanishes in negative degrees.
* `HomologicalComplex.extendUpNatXIso_natCast`: in a nonnegative degree the comparison is the
  given isomorphism, after the identification of the extended term.

## Implementation notes

The hypothesis supplying the degreewise isomorphisms is stated as
`∀ (n : ℕ) (p : ℤ), (n : ℤ) = p → K.X n ≅ L.X p` rather than as `∀ n : ℕ, K.X n ≅ L.X (n : ℤ)`,
and likewise for its compatibility with the differentials. The reason is that the degree in
which the comparison is formed is `p.toNat` for a nonnegative `p`, and the second form would
then have to be transported along `Int.toNat_of_nonneg` by an `eqToIso`; with the first form the
transport is absorbed into the proof argument, which is irrelevant, and the comparison in degree
`(n : ℤ)` is the given isomorphism on the nose.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex

variable {V : Type u} [Category.{v} V] [HasZeroMorphisms V] [HasZeroObject V]
  (K : CochainComplex V ℕ) (L : CochainComplex V ℤ)

/-- **The extension by zero of an `ℕ`-indexed complex vanishes in negative degrees**, those
being the degrees outside the image of `ComplexShape.embeddingUpNat`. -/
theorem isZero_extend_X_of_neg {p : ℤ} (hp : p < 0) :
    IsZero ((K.extend ComplexShape.embeddingUpNat).X p) :=
  K.isZero_extend_X ComplexShape.embeddingUpNat p fun n ↦ by
    simp only [ComplexShape.embeddingUpNat_f]
    omega

variable (hL : ∀ p : ℤ, p < 0 → IsZero (L.X p))
  (e : ∀ (n : ℕ) (p : ℤ), (n : ℤ) = p → (K.X n ≅ L.X p))

/-- **The comparison of the extension by zero with a `ℤ`-indexed complex, in a single degree**:
the identification of the extended term with the term of `K` followed by the given isomorphism
in a nonnegative degree, and the unique isomorphism of zero objects in a negative one. -/
def extendUpNatXIso (p : ℤ) : (K.extend ComplexShape.embeddingUpNat).X p ≅ L.X p :=
  if hp : 0 ≤ p then
    K.extendXIso ComplexShape.embeddingUpNat
        (show ComplexShape.embeddingUpNat.f p.toNat = p from Int.toNat_of_nonneg hp) ≪≫
      e p.toNat p (Int.toNat_of_nonneg hp)
  else
    (isZero_extend_X_of_neg K (not_le.mp hp)).iso (hL p (not_le.mp hp))

/-- In a nonnegative degree the comparison is the given isomorphism, after the identification
of the extended term with the term of `K`. -/
theorem extendUpNatXIso_natCast (n : ℕ) :
    extendUpNatXIso K L hL e (n : ℤ) =
      K.extendXIso ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ)) rfl ≪≫
        e n (n : ℤ) rfl :=
  dite_eq_left (Int.natCast_nonneg n)

/-- **An `ℕ`-indexed complex extended by zero is isomorphic to a `ℤ`-indexed complex vanishing
in negative degrees**, as soon as their terms are isomorphic compatibly with the
differentials. -/
def extendUpNatIso
    (he : ∀ (n : ℕ) (p q : ℤ) (hp : (n : ℤ) = p) (hq : ((n + 1 : ℕ) : ℤ) = q),
      (e n p hp).hom ≫ L.d p q = K.d n (n + 1) ≫ (e (n + 1) q hq).hom) :
    K.extend ComplexShape.embeddingUpNat ≅ L :=
  Hom.isoOfComponents (extendUpNatXIso K L hL e) fun i j hij ↦ by
    by_cases hi : 0 ≤ i
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, (n : ℤ) = i := ⟨i.toNat, Int.toNat_of_nonneg hi⟩
      obtain rfl : ((n + 1 : ℕ) : ℤ) = j := by push_cast; exact hij
      rw [extendUpNatXIso_natCast, extendUpNatXIso_natCast, Iso.trans_hom, Iso.trans_hom,
        K.extend_d_eq ComplexShape.embeddingUpNat (i := n) (j := n + 1) (i' := (n : ℤ))
          (j' := ((n + 1 : ℕ) : ℤ)) rfl rfl]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, he n _ _ rfl rfl]
    · exact (isZero_extend_X_of_neg K (not_le.mp hi)).eq_of_src _ _

end HomologicalComplex

end
