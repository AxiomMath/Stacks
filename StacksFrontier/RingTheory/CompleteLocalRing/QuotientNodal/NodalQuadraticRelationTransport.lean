module

public import StacksFrontier.RingTheory.CompleteLocalRing.QuotientNodal.NodalQuadraticRelation
public import StacksFrontier.RingTheory.LocalRing.CotangentQuotient

/-!
# A nodal quadratic relation is carried along a quotient inside the square of the maximal ideal

The predicate `Stacks.Curves.HasNodalQuadraticRelation` passes along a surjective local
homomorphism whose kernel lies in `𝔪 ^ 2`, and descends along one whose kernel lies in `𝔪 ^ 3`.
It is invariant under an isomorphism of local rings, and it forces the embedding dimension to be
`2`.

## Main results

* `Stacks.Curves.hasNodalQuadraticRelation_of_ker_le_sq` — the predicate passes along a
  surjective local homomorphism with kernel inside `𝔪 ^ 2`.
* `Stacks.Curves.hasNodalQuadraticRelation_of_ker_le_cube` — conversely the predicate descends
  along such a homomorphism when the kernel lies inside `𝔪 ^ 3`, so
  `Stacks.Curves.hasNodalQuadraticRelation_iff_of_ker_le_cube` and
  `Stacks.Curves.hasNodalQuadraticRelation_iff_of_surjective_of_ker_le_cube` read the predicate
  off the quotient by `𝔪 ^ 3`.
* `Stacks.Curves.hasNodalQuadraticRelation_congr` — hence it is invariant under an isomorphism
  of local rings.
* `Stacks.Curves.finrank_cotangentSpace_eq_two_of_hasNodalQuadraticRelation` — a ring carrying a
  nodal quadratic relation has a two-dimensional cotangent space.

## References

* [Stacks Project, Tag 0C49](https://stacks.math.columbia.edu/tag/0C49)
-/

@[expose] public section

open IsLocalRing

universe u

namespace Stacks.Curves

/-- A local ring carrying a nodal quadratic relation has a two-dimensional cotangent space. -/
theorem finrank_cotangentSpace_eq_two_of_hasNodalQuadraticRelation {A : Type*} [CommRing A]
    [IsLocalRing A] (h : HasNodalQuadraticRelation A) :
    Module.finrank (ResidueField A) (CotangentSpace A) = 2 := by
  obtain ⟨_, _, e, _, _, _, _, _, _, _⟩ := (hasNodalQuadraticRelation_iff_exists_basis A).1 h
  rw [Module.finrank_eq_card_basis e]
  simp

/-- A ring homomorphism carries `4 * a * c - b ^ 2` to the same expression in the images. -/
private theorem map_four_mul_mul_sub_sq {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (a b c : R) : f (4 * a * c - b ^ 2) = 4 * f a * f c - f b ^ 2 := by
  rw [map_sub, map_mul, map_mul, map_pow, map_ofNat]

section Surjective

variable {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)]

/-- If `A → B` is a surjective local homomorphism whose kernel lies in `𝔪_A ^ 2`, then a nodal
quadratic relation on `A` gives one on `B`. -/
theorem hasNodalQuadraticRelation_of_ker_le_sq
    (hsurj : Function.Surjective (algebraMap A B))
    (hker : RingHom.ker (algebraMap A B) ≤ maximalIdeal A ^ 2)
    (h : HasNodalQuadraticRelation A) : HasNodalQuadraticRelation B := by
  obtain ⟨x, y, e, a, b, c, hx, hy, hnd, hm⟩ := (hasNodalQuadraticRelation_iff_exists_basis A).1 h
  have hmem : ∀ z : maximalIdeal A, algebraMap A B z ∈ maximalIdeal B :=
    fun z => le_of_eq (maximalIdeal_comap (algebraMap A B)).symm z.2
  refine (hasNodalQuadraticRelation_iff_exists_basis B).2
    ⟨⟨algebraMap A B x, hmem x⟩, ⟨algebraMap A B y, hmem y⟩,
      basisCotangentSpaceOfKerLeSq hsurj hker e,
      algebraMap A B a, algebraMap A B b, algebraMap A B c, ?_, ?_, ?_, ?_⟩
  · rw [basisCotangentSpaceOfKerLeSq_apply, hx, cotangentSpaceEquivOfKerLeSq_toCotangent]
  · rw [basisCotangentSpaceOfKerLeSq_apply, hy, cotangentSpaceEquivOfKerLeSq_toCotangent]
  · rw [← map_four_mul_mul_sub_sq, ← ResidueField.map_residue (algebraMap A B)]
    exact fun hzero => hnd
      ((ResidueField.map (algebraMap A B)).injective (by rw [hzero, map_zero]))
  · have hmap : Ideal.map (algebraMap A B) (maximalIdeal A ^ 3) ≤ maximalIdeal B ^ 3 := by
      rw [Ideal.map_pow]
      exact pow_le_pow_left' (Ideal.map_le_iff_le_comap.2
        (le_of_eq (maximalIdeal_comap (algebraMap A B)).symm)) 3
    refine hmap ?_
    simpa using Ideal.mem_map_of_mem (algebraMap A B) hm

/-- If `A → B` is a surjective local homomorphism whose kernel lies in `𝔪_A ^ 3`, then a nodal
quadratic relation on `B` is the image of one on `A`. -/
theorem hasNodalQuadraticRelation_of_ker_le_cube
    (hsurj : Function.Surjective (algebraMap A B))
    (hker : RingHom.ker (algebraMap A B) ≤ maximalIdeal A ^ 3)
    (h : HasNodalQuadraticRelation B) : HasNodalQuadraticRelation A := by
  have hker2 : RingHom.ker (algebraMap A B) ≤ maximalIdeal A ^ 2 :=
    hker.trans (Ideal.pow_le_pow_right (by norm_num))
  obtain ⟨x, y, e, a, b, c, hx, hy, hnd, hm⟩ := (hasNodalQuadraticRelation_iff_exists_basis B).1 h
  obtain ⟨xA, hxA⟩ := hsurj x.1
  obtain ⟨yA, hyA⟩ := hsurj y.1
  obtain ⟨aA, haA⟩ := hsurj a
  obtain ⟨bA, hbA⟩ := hsurj b
  obtain ⟨cA, hcA⟩ := hsurj c
  have hmemA : ∀ z : A, algebraMap A B z ∈ maximalIdeal B → z ∈ maximalIdeal A := fun z hz =>
    (maximalIdeal_comap (algebraMap A B)).le (Ideal.mem_comap.2 hz)
  have hx' : xA ∈ maximalIdeal A := hmemA xA (by rw [hxA]; exact x.2)
  have hy' : yA ∈ maximalIdeal A := hmemA yA (by rw [hyA]; exact y.2)
  refine (hasNodalQuadraticRelation_iff_exists_basis A).2
    ⟨⟨xA, hx'⟩, ⟨yA, hy'⟩, basisCotangentSpaceSymmOfKerLeSq hsurj hker2 e, aA, bA, cA, ?_, ?_,
      ?_, ?_⟩
  · rw [basisCotangentSpaceSymmOfKerLeSq_apply, LinearEquiv.symm_apply_eq, hx,
      cotangentSpaceEquivOfKerLeSq_toCotangent]
    congr 1
    exact Subtype.ext hxA.symm
  · rw [basisCotangentSpaceSymmOfKerLeSq_apply, LinearEquiv.symm_apply_eq, hy,
      cotangentSpaceEquivOfKerLeSq_toCotangent]
    congr 1
    exact Subtype.ext hyA.symm
  · refine fun hzero => hnd ?_
    have hmapeq : ResidueField.map (algebraMap A B) (residue A (4 * aA * cA - bA ^ 2)) =
        residue B (4 * a * c - b ^ 2) := by
      rw [ResidueField.map_residue]
      congr 1
      rw [map_four_mul_mul_sub_sq, haA, hbA, hcA]
    rw [← hmapeq, hzero, map_zero]
  · have hcomap : Ideal.comap (algebraMap A B) (maximalIdeal B ^ 3) = maximalIdeal A ^ 3 := by
      rw [← IsLocalRing.map_maximalIdeal_of_surjective (algebraMap A B) hsurj, ← Ideal.map_pow,
        Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot,
        sup_eq_left.2 hker]
    rw [← hcomap, Ideal.mem_comap, map_add, map_add, map_mul, map_mul, map_mul, map_mul, map_pow,
      map_pow, haA, hbA, hcA, hxA, hyA]
    exact hm

/-- A surjective local homomorphism whose kernel lies in `𝔪_A ^ 3` neither creates nor destroys
a nodal quadratic relation. -/
theorem hasNodalQuadraticRelation_iff_of_ker_le_cube
    (hsurj : Function.Surjective (algebraMap A B))
    (hker : RingHom.ker (algebraMap A B) ≤ maximalIdeal A ^ 3) :
    HasNodalQuadraticRelation A ↔ HasNodalQuadraticRelation B :=
  ⟨hasNodalQuadraticRelation_of_ker_le_sq hsurj
      (hker.trans (Ideal.pow_le_pow_right (by norm_num))),
    hasNodalQuadraticRelation_of_ker_le_cube hsurj hker⟩

end Surjective

/-- A nodal quadratic relation is invariant under an isomorphism of local rings. -/
theorem hasNodalQuadraticRelation_congr {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] (φ : A ≃+* B) :
    HasNodalQuadraticRelation A ↔ HasNodalQuadraticRelation B := by
  have key : ∀ (C D : Type u) (_ : CommRing C) (_ : CommRing D) (_ : IsLocalRing C)
      (_ : IsLocalRing D) (ψ : C ≃+* D), HasNodalQuadraticRelation C →
        HasNodalQuadraticRelation D := by
    intro C D _ _ _ _ ψ hC
    let : Algebra C D := ψ.toRingHom.toAlgebra
    have hmapeq : (algebraMap C D) = ψ.toRingHom := rfl
    have hsurj : Function.Surjective (algebraMap C D) := ψ.surjective
    let : IsLocalHom (algebraMap C D) := by
      refine ⟨fun z hz => ?_⟩
      rw [hmapeq] at hz
      simpa using (hz.map ψ.symm.toRingHom)
    refine hasNodalQuadraticRelation_of_ker_le_sq hsurj ?_ hC
    have hbot : RingHom.ker (algebraMap C D) = ⊥ := by
      rw [hmapeq, RingHom.ker_eq_bot_iff_eq_zero]
      exact fun z hz => ψ.injective (by simpa using hz)
    exact hbot ▸ bot_le
  exact ⟨key A B _ _ _ _ φ, key B A _ _ _ _ φ.symm⟩

/-- A surjective ring homomorphism of local rings whose kernel lies in `𝔪_A ^ 3` neither creates
nor destroys a nodal quadratic relation. -/
theorem hasNodalQuadraticRelation_iff_of_surjective_of_ker_le_cube {A B : Type u} [CommRing A]
    [CommRing B] [IsLocalRing A] [IsLocalRing B] (φ : A →+* B) (hsurj : Function.Surjective φ)
    (hker : RingHom.ker φ ≤ maximalIdeal A ^ 3) :
    HasNodalQuadraticRelation A ↔ HasNodalQuadraticRelation B := by
  let : Algebra A B := φ.toAlgebra
  have hmap : (algebraMap A B) = φ := rfl
  let : IsLocalHom (algebraMap A B) := IsLocalHom.of_surjective _ (hmap ▸ hsurj)
  exact hasNodalQuadraticRelation_iff_of_ker_le_cube (hmap ▸ hsurj) (hmap ▸ hker)

end Stacks.Curves

end
