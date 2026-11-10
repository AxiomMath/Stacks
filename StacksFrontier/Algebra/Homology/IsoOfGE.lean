module

public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Two cochain complexes concentrated in degrees `≥ k`, compared above the cutoff

Two `ℤ`-indexed cochain complexes that both vanish in degrees `< k` are isomorphic as soon as
their terms are isomorphic in the degrees `≥ k`, compatibly with the differentials: below the
cutoff both terms are zero objects, so there is exactly one morphism between them and every
square commutes. This file builds that isomorphism.

It is the two-sided analogue of `HomologicalComplex.extendUpNatIso`, which compares the
extension by zero of an `ℕ`-indexed complex with a `ℤ`-indexed one vanishing in negative
degrees: there one side is an extension and the cutoff is `0`, here both sides are arbitrary and
the cutoff is arbitrary.

## Main definitions

* `CochainComplex.isoXOfGE`: the comparison in a single degree, which is the given isomorphism
  above the cutoff and the unique map between two zero objects below it.
* `CochainComplex.isoOfGE`: **the isomorphism `K ≅ L` of complexes.**

## Main results

* `CochainComplex.isoXOfGE_eq`: in degree `k + m` the comparison is the given isomorphism.

## Implementation notes

The hypothesis supplying the degreewise isomorphisms is stated as
`∀ (m : ℕ) (p : ℤ), k + m = p → (K.X p ≅ L.X p)` rather than as
`∀ m : ℕ, K.X (k + m) ≅ L.X (k + m)`, for the same reason
`HomologicalComplex.extendUpNatIso` states its hypothesis with a degree binder and an equation:
the degree in which the comparison is formed is `k + (p - k).toNat` for `k ≤ p`, and the second
form would have to be transported to `p` along `Int.toNat_of_nonneg` by an `eqToIso`. With a
degree binder the transport is absorbed into the proof argument, which is irrelevant, so the
comparison in degree `k + m` is the given isomorphism on the nose, and no `eqToHom` appears in
the squares of the hypothesis of `CochainComplex.isoOfGE`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex

variable {V : Type u} [Category.{v} V] [HasZeroMorphisms V]
  (K L : CochainComplex V ℤ) (k : ℤ)
  (hK : ∀ p : ℤ, p < k → IsZero (K.X p)) (hL : ∀ p : ℤ, p < k → IsZero (L.X p))
  (e : ∀ (m : ℕ) (p : ℤ), k + (m : ℤ) = p → (K.X p ≅ L.X p))

/-- **The comparison of two complexes concentrated in degrees `≥ k`, in a single degree**: the
given isomorphism above the cutoff, and the unique isomorphism of zero objects below it. -/
def isoXOfGE (p : ℤ) : K.X p ≅ L.X p :=
  if hp : k ≤ p then e (p - k).toNat p (by omega)
  else (hK p (not_le.mp hp)).iso (hL p (not_le.mp hp))

/-- In degree `k + m` the comparison is the given isomorphism. -/
theorem isoXOfGE_eq (m : ℕ) (p : ℤ) (hp : k + (m : ℤ) = p) :
    isoXOfGE K L k hK hL e p = e m p hp := by
  have hk : k ≤ p := by omega
  rw [isoXOfGE, dite_eq_left hk]
  obtain rfl : (p - k).toNat = m := by omega
  rfl

/-- **Two cochain complexes vanishing in degrees `< k` are isomorphic** as soon as their terms
are isomorphic in the degrees `≥ k` compatibly with the differentials. -/
def isoOfGE
    (he : ∀ (m : ℕ) (p q : ℤ) (hp : k + (m : ℤ) = p) (hq : k + ((m + 1 : ℕ) : ℤ) = q),
      (e m p hp).hom ≫ L.d p q = K.d p q ≫ (e (m + 1) q hq).hom) :
    K ≅ L :=
  HomologicalComplex.Hom.isoOfComponents (isoXOfGE K L k hK hL e) fun i j hij => by
    by_cases hi : k ≤ i
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, k + (m : ℤ) = i := ⟨(i - k).toNat, by omega⟩
      have hj : k + ((m + 1 : ℕ) : ℤ) = j := by
        have h : k + (m : ℤ) + 1 = j := hij
        push_cast
        omega
      rw [isoXOfGE_eq K L k hK hL e m _ rfl, isoXOfGE_eq K L k hK hL e (m + 1) _ hj]
      exact he m _ _ rfl hj
    · exact (hK i (not_le.mp hi)).eq_of_src _ _

end CochainComplex

end
