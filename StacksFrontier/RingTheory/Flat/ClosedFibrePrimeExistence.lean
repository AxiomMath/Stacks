module

public import StacksFrontier.RingTheory.Flat.HenselianFlattening

/-!
# The closed fibre of a local base change is nonempty

Let `A → B` be a local homomorphism of local rings and let `R` be a local `A`-algebra with local
structure homomorphism. The flatness condition of Stacks Tag 05ML quantifies over the primes of
`B' = B ⊗[A] R` containing `𝔪_R B' + 𝔪_B B'`, i.e. over the points of the closed fibre of
`Spec(B') → Spec(B) ×_{Spec(A)} Spec(R)` above the pair of closed points. This file proves that
there is at least one such prime.

The set is nonempty because `B' ⧸ (𝔪_R B' + 𝔪_B B')` is a quotient of
`κ(𝔪_B) ⊗_{κ(𝔪_A)} κ(𝔪_R)`, which is nonzero: both factors are nonzero vector spaces over the
residue field of `A`, and a vector space over a field is faithfully flat. So the ideal
`𝔪_R B' + 𝔪_B B'` is proper and is contained in a maximal ideal.

Without this the universally quantified flatness condition of Stacks Tag 05ML carries no
information, and in particular the implication from the condition to flatness of a localization of
the base change — the direction used in the proof of Stacks Tag 05PG — has nothing to feed on.

## Main results

* `Module.exists_isPrime_closedFiber`: the ideal `𝔪_R B' + 𝔪_B B'` of `B ⊗[A] R` is contained in a
  prime ideal.
* `Module.FlatAtPointSituation.exists_isPrime_closedFiber`: the same, in the vocabulary of
  Stacks Tag 05MK, so that it applies directly to
  `Module.FlatAtPointSituation.ConditionOn`.

## References

* [Stacks Project, Tag 05MK](https://stacks.math.columbia.edu/tag/05MK)
* [Stacks Project, Tag 05ML](https://stacks.math.columbia.edu/tag/05ML)
* [Stacks Project, Tag 05PG](https://stacks.math.columbia.edu/tag/05PG)
-/

@[expose] public section

open IsLocalRing

open scoped TensorProduct

universe u v w x

namespace Module

section

variable (A : Type u) [CommRing A] [IsLocalRing A] (B : Type v) [CommRing B] [IsLocalRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)] (R : Type x) [CommRing R] [IsLocalRing R]
  [Algebra A R] [IsLocalHom (algebraMap A R)]

/-- The ideal cutting out the closed fibre of `Spec(B ⊗[A] R)`: the sum of the extensions of the
maximal ideals of `R` and of `B`. This is the ideal the flatness condition of Stacks Tag 05ML
requires its test primes to contain. -/
def closedFibreIdeal : Ideal (B ⊗[A] R) :=
  Ideal.map (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := R)).toRingHom
      (maximalIdeal R) +
    Ideal.map (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := R))
      (maximalIdeal B)

/-- The residue field of `B` tensored over the residue field of `A` with the residue field of `R`:
the ring of functions on the closed fibre. -/
private abbrev residueFibre : Type max v x :=
  ResidueField B ⊗[ResidueField A] ResidueField R

/-- The extension of the maximal ideal of a local ring `X` lies in the kernel of `ψ` when `ψ ∘ φ`
factors through the residue map of `X`. -/
private theorem map_maximalIdeal_le_ker {X S T : Type*} [CommRing X] [IsLocalRing X] [CommRing S]
    [CommRing T] (φ : X →+* S) (ψ : S →+* T) (k : ResidueField X →+* T)
    (h : ∀ x, ψ (φ x) = k (residue X x)) : (maximalIdeal X).map φ ≤ RingHom.ker ψ := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  simp [RingHom.mem_ker, h, (residue_eq_zero_iff x).2 hx]

/-- **The closed fibre of a local base change is nonempty.** For a local homomorphism `A → B` of
local rings and a local `A`-algebra `R` with local structure homomorphism there is a prime of
`B ⊗[A] R` containing the extensions of the maximal ideals of `R` and of `B`.

The two residue maps assemble into an `A`-algebra homomorphism
`B ⊗[A] R → κ(𝔪_B) ⊗_{κ(𝔪_A)} κ(𝔪_R)` killing both extended maximal ideals, and the target is
nonzero because a tensor product of two nonzero vector spaces over a field is nonzero. So the
ideal is proper, and a proper ideal lies in a maximal one. -/
theorem exists_isPrime_closedFiber :
    ∃ q : Ideal (B ⊗[A] R), q.IsPrime ∧ closedFibreIdeal A B R ≤ q := by
  have htower : ∀ a : A, algebraMap A (residueFibre A B R) a =
      algebraMap (ResidueField A) (residueFibre A B R) (residue A a) := fun a ↦ by
    change (Algebra.TensorProduct.includeLeft (R := ResidueField A) (A := ResidueField B)
      (B := ResidueField R) (S := ResidueField A)) (algebraMap A (ResidueField B) a) = _
    rw [IsScalarTower.algebraMap_apply A (ResidueField A) (ResidueField B)]
    exact Algebra.TensorProduct.includeLeft.commutes (residue A a)
  -- The left-hand residue map, as an `A`-algebra homomorphism to the closed fibre.
  let f : B →ₐ[A] residueFibre A B R :=
    { __ := (algebraMap (ResidueField B) (residueFibre A B R)).comp (residue B)
      commutes' := fun a ↦ by
        rw [htower a, IsScalarTower.algebraMap_apply (ResidueField A) (ResidueField B)
          (residueFibre A B R)]
        rfl }
  -- The right-hand residue map, as an `A`-algebra homomorphism to the closed fibre.
  let g : R →ₐ[A] residueFibre A B R :=
    { __ := (Algebra.TensorProduct.includeRight
        (R := ResidueField A) (A := ResidueField B) (B := ResidueField R)).toRingHom.comp
          (residue R)
      commutes' := fun a ↦ by
        rw [htower a]
        exact (Algebra.TensorProduct.includeRight (R := ResidueField A)
          (A := ResidueField B) (B := ResidueField R)).commutes (residue A a) }
  have hcomm : ∀ (x : B) (y : R), Commute (f x) (g y) := fun _ _ ↦ Commute.all _ _
  -- The two generators of the closed-fibre ideal die under the lift.
  have hgr : ∀ r : R, Algebra.TensorProduct.lift f g hcomm
      (Algebra.TensorProduct.includeRight r) = g r := fun r ↦ by
    change Algebra.TensorProduct.lift f g hcomm ((1 : B) ⊗ₜ[A] r) = g r
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  have hfb : ∀ b : B, Algebra.TensorProduct.lift f g hcomm
      (Algebra.TensorProduct.includeLeftRingHom b) = f b := fun b ↦ by
    change Algebra.TensorProduct.lift f g hcomm (b ⊗ₜ[A] (1 : R)) = f b
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  have hker : closedFibreIdeal A B R ≤
      RingHom.ker (Algebra.TensorProduct.lift f g hcomm).toRingHom := by
    refine sup_le (map_maximalIdeal_le_ker _ _
      (Algebra.TensorProduct.includeRight (R := ResidueField A) (A := ResidueField B)
        (B := ResidueField R)).toRingHom fun r ↦ (hgr r).trans rfl)
      (map_maximalIdeal_le_ker _ _ (algebraMap (ResidueField B) (residueFibre A B R))
        fun b ↦ (hfb b).trans rfl)
  -- The closed fibre is a nonzero ring, so the ideal is proper.
  have hne : closedFibreIdeal A B R ≠ ⊤ := fun h ↦ by
    have h1 : Algebra.TensorProduct.lift f g hcomm (1 : B ⊗[A] R) = 0 :=
      hker (h ▸ Submodule.mem_top : (1 : B ⊗[A] R) ∈ closedFibreIdeal A B R)
    rw [map_one] at h1
    exact one_ne_zero h1
  obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal _ hne
  exact ⟨q, hq.isPrime, hle⟩

end

namespace FlatAtPointSituation

/-- **The closed fibre tested by the flatness condition of Stacks Tag 05ML is nonempty.** In the
situation of Stacks Tag 05MK, for every local `A`-algebra `R` with local structure homomorphism
there is a prime of `B ⊗[A] R` containing the extensions of the maximal ideals of `R` and of `B`,
so the condition of Stacks Tag 05ML is a nonvacuous requirement. -/
theorem exists_isPrime_closedFiber (S : FlatAtPointSituation.{u, v, w}) (R : Type x) [CommRing R]
    [IsLocalRing R] [Algebra S.A R] [IsLocalHom (algebraMap S.A R)] :
    ∃ q : Ideal (S.B ⊗[S.A] R), q.IsPrime ∧
      Ideal.map (Algebra.TensorProduct.includeRight (R := S.A) (A := S.B) (B := R)).toRingHom
          (maximalIdeal R) +
        Ideal.map (Algebra.TensorProduct.includeLeftRingHom (R := S.A) (A := S.B) (B := R))
          (maximalIdeal S.B) ≤ q :=
  Module.exists_isPrime_closedFiber S.A S.B R

end FlatAtPointSituation

end Module

end
