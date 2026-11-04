module

public import StacksFrontier.LinearAlgebra.Matrix.AlternatingTensorPower

/-!
# Right multiplication by the alternating projector splits

Let `R` be a commutative ring and `n` a finite type with `d` elements. `Matrix.altProj`, the
projector of [Stacks, Tag 0A2L], is the rank-one matrix `a · aᵗ` over the index type `n → n` of
the `d`-fold tensor power of `R ^ n`, where `a = Matrix.altVec` is the alternating vector. This
file records the factorisation of right multiplication by it,
$$
M \mapsto M \cdot p = (M a)\, a^{t},
$$
through the free module of rank `d ^ d`, and the two one-sided inverses that make the two halves
a split epimorphism and a split monomorphism.

This is the local calculation of Tag 0A2L. There the module `𝓗 = Im(f ↦ f p)` has to be shown
finite locally free, and left multiplication `A^{⊗ d} → 𝓗om(𝓗, 𝓗)` an isomorphism; both are read
off a trivialisation, where `A^{⊗ d}` becomes the matrices on `n → n` and `p` becomes `altProj`.
The content is that `altVec` has a coordinate equal to `1` (`Matrix.altVec_id`), so both
`M ↦ M a` and `v ↦ v aᵗ` split, and hence the image of `M ↦ M p` is the free module on `n → n`
with its standard left action — which is the statement that the trivialised `𝓗` is free of rank
`d ^ d` and that the trivialised left multiplication is the standard representation.

## Main definitions

* `Matrix.altCoordVec`: the standard basis vector of `(n → n) → R` at the identity index, which
  is the one-sided inverse both halves of the factorisation use.

## Main results

* `Matrix.altProj_eq_vecMulVec`: `altProj` is `a · aᵗ` in the spelling `Matrix.vecMulVec`.
* `Matrix.mul_altProj_eq_vecMulVec`: **right multiplication by `altProj` is `M ↦ (M a) aᵗ`**, so
  it factors through `(n → n) → R`.
* `Matrix.mulVec_altVec_vecMulVec_altCoordVec`: **the first half is a split epimorphism** — every
  vector is `M a` for some `M`, linearly in the vector.
* `Matrix.mulVec_altCoordVec_vecMulVec`: **the second half is a split monomorphism** — `v aᵗ`
  determines `v`, linearly.
* `Matrix.vecMulVec_altVec_injective` and `Matrix.mulVec_altVec_surjective`: the two consequences,
  stated as injectivity and surjectivity.
* `Matrix.mul_vecMulVec_altVec`: left multiplication acts on the image through the standard
  action on `(n → n) → R`, which is what makes the trivialised left multiplication the standard
  representation.
* `Matrix.altProj_mul_eq_vecMulVec`, `Matrix.vecMulVec_altVec_mul`,
  `Matrix.vecMul_altVec_vecMulVec_altCoordVec`, `Matrix.vecMul_altCoordVec_vecMulVec`: the mirror
  statements for LEFT multiplication by the projector, which is the side
  `CategoryTheory.Mon.imageRep` represents a monoid object on.

## References

* [Stacks Project, Tag 0A2L](https://stacks.math.columbia.edu/tag/0A2L)
-/

@[expose] public section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- `Matrix.altProj` is the rank-one matrix `a · aᵗ` built from the alternating vector. -/
theorem altProj_eq_vecMulVec : altProj R = vecMulVec (altVec R) (altVec R (n := n)) := by
  ext f g
  rw [altProj_apply]
  rfl

/-- **Right multiplication by the alternating projector factors through the free module on the
index type**: `M · p = (M a) aᵗ`. -/
theorem mul_altProj_eq_vecMulVec (M : Matrix (n → n) (n → n) R) :
    M * altProj R = vecMulVec (M *ᵥ altVec R) (altVec R) := by
  rw [altProj_eq_vecMulVec, mul_vecMulVec]

/-- **Left multiplication acts on the image of the projector through the standard action on
`(n → n) → R`**: `M (v aᵗ) = (M v) aᵗ`. This is the statement that, after a trivialisation, left
multiplication on `𝓗 = Im(f ↦ f p)` is the standard representation of the matrix algebra on the
free module. -/
theorem mul_vecMulVec_altVec (M : Matrix (n → n) (n → n) R) (v : (n → n) → R) :
    M * vecMulVec v (altVec R (n := n)) = vecMulVec (M *ᵥ v) (altVec R (n := n)) :=
  mul_vecMulVec ..

/-- The standard basis vector of `(n → n) → R` at the identity index. It pairs to `1` with the
alternating vector, by `Matrix.altVec_id`, and that is the whole content of the splitting. -/
def altCoordVec (R : Type*) [CommRing R] (n : Type*) [Fintype n] [DecidableEq n] :
    (n → n) → R :=
  Pi.single id 1

/-- The pairing `∑ i, altCoordVec R n i * altVec R i` of the standard basis vector at the identity
index with the alternating vector equals `1`. -/
@[simp]
theorem sum_altCoordVec_mul_altVec :
    ∑ i, altCoordVec R n i * altVec R i = 1 := by
  rw [Finset.sum_eq_single_of_mem (id : n → n) (Finset.mem_univ _)
    (fun b _ hb ↦ by rw [altCoordVec, Pi.single_eq_of_ne hb, zero_mul])]
  rw [altCoordVec, Pi.single_eq_same, altVec_id, mul_one]

/-- The pairing `∑ i, altVec R i * altCoordVec R n i` of the alternating vector with the standard
basis vector at the identity index equals `1`. -/
@[simp]
theorem sum_altVec_mul_altCoordVec :
    ∑ i, altVec R i * altCoordVec R n i = 1 := by
  simpa only [mul_comm] using sum_altCoordVec_mul_altVec (R := R) (n := n)

/-- **The first half of the factorisation is a split epimorphism**: the vector `v` is recovered
from `vecMulVec v (altCoordVec R n)` by multiplying with the alternating vector. -/
theorem mulVec_altVec_vecMulVec_altCoordVec (v : (n → n) → R) :
    vecMulVec v (altCoordVec R n) *ᵥ altVec R = v := by
  ext f
  simp only [mulVec, dotProduct, vecMulVec_apply, mul_assoc, ← Finset.mul_sum,
    sum_altCoordVec_mul_altVec, mul_one]

/-- **The second half of the factorisation is a split monomorphism**: the vector `v` is recovered
from `vecMulVec v (altVec R)` by multiplying with the standard basis vector. -/
theorem mulVec_altCoordVec_vecMulVec (v : (n → n) → R) :
    vecMulVec v (altVec R (n := n)) *ᵥ altCoordVec R n = v := by
  ext f
  simp only [mulVec, dotProduct, vecMulVec_apply, mul_assoc, ← Finset.mul_sum,
    sum_altVec_mul_altCoordVec, mul_one]

/-- `v ↦ v aᵗ` is injective. -/
theorem vecMulVec_altVec_injective :
    Function.Injective fun v : (n → n) → R ↦ vecMulVec v (altVec R (n := n)) := by
  intro v w h
  rw [← mulVec_altCoordVec_vecMulVec v, ← mulVec_altCoordVec_vecMulVec w]
  exact congrArg (· *ᵥ altCoordVec R n) h

/-- `M ↦ M a` is surjective. -/
theorem mulVec_altVec_surjective :
    Function.Surjective fun M : Matrix (n → n) (n → n) R ↦ M *ᵥ altVec R :=
  fun v ↦ ⟨vecMulVec v (altCoordVec R n), mulVec_altVec_vecMulVec_altCoordVec v⟩

/-! ### The mirror statements, for left multiplication

`CategoryTheory.Mon.imageRep` represents a monoid object on the image of LEFT multiplication by a
point, because `CategoryTheory.MonoidalClosed.comp` applies its first factor first and so
`internalEnd` is the opposite of composition. The mirror image of each statement above is what
that consumer needs; `Matrix.altProj` is symmetric, so each is the same computation on the other
side. -/

/-- **Left multiplication by the alternating projector factors through the free module on the
index type**: `p · M = a (aᵗ M)`. -/
theorem altProj_mul_eq_vecMulVec (M : Matrix (n → n) (n → n) R) :
    altProj R * M = vecMulVec (altVec R (n := n)) (altVec R ᵥ* M) := by
  rw [altProj_eq_vecMulVec, vecMulVec_mul]

/-- **Right multiplication acts on the image of the projector through the standard right action
on `(n → n) → R`.** -/
theorem vecMulVec_altVec_mul (M : Matrix (n → n) (n → n) R) (v : (n → n) → R) :
    vecMulVec (altVec R (n := n)) v * M = vecMulVec (altVec R (n := n)) (v ᵥ* M) :=
  vecMulVec_mul ..

/-- **The first half of the mirror factorisation is a split epimorphism**: the covector `v` is
recovered from `vecMulVec (altCoordVec R n) v` by multiplying with the alternating vector. -/
theorem vecMul_altVec_vecMulVec_altCoordVec (v : (n → n) → R) :
    altVec R ᵥ* vecMulVec (altCoordVec R n) v = v := by
  ext g
  simp only [vecMul, dotProduct, vecMulVec_apply, ← mul_assoc, ← Finset.sum_mul,
    sum_altVec_mul_altCoordVec, one_mul]

/-- **The second half of the mirror factorisation is a split monomorphism**: the covector `v` is
recovered from `vecMulVec (altVec R) v` by multiplying with the standard basis vector. -/
theorem vecMul_altCoordVec_vecMulVec (v : (n → n) → R) :
    altCoordVec R n ᵥ* vecMulVec (altVec R (n := n)) v = v := by
  ext g
  simp only [vecMul, dotProduct, vecMulVec_apply, ← mul_assoc, ← Finset.sum_mul,
    sum_altCoordVec_mul_altVec, one_mul]

/-- `v ↦ a v` is injective. -/
theorem vecMulVec_altVec_left_injective :
    Function.Injective fun v : (n → n) → R ↦ vecMulVec (altVec R (n := n)) v := by
  intro v w h
  rw [← vecMul_altCoordVec_vecMulVec v, ← vecMul_altCoordVec_vecMulVec w]
  exact congrArg (altCoordVec R n ᵥ* ·) h

/-- `M ↦ aᵗ M` is surjective. -/
theorem vecMul_altVec_surjective :
    Function.Surjective fun M : Matrix (n → n) (n → n) R ↦ altVec R ᵥ* M :=
  fun v ↦ ⟨vecMulVec (altCoordVec R n) v, vecMul_altVec_vecMulVec_altCoordVec v⟩

end Matrix

end
