module

public import StacksFrontier.RingTheory.Koszul.Functoriality
public import StacksFrontier.RingTheory.Koszul.TorComparison.Determinant
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import StacksCore.Tactic.StacksAttribute

/-!
# The Koszul comparison map of a relation between two sequences

Let `R` be a commutative ring and let `f₁, …, f_n` and `g₁, …, g_n` be two sequences in `R`
related by a coefficient matrix,
`fᵢ = ∑ⱼ gᵢⱼ gⱼ`.
Then `Koszul.seqDual f` factors as `Koszul.seqDual g` composed with the linear endomorphism
`ψ` of `Rⁿ` whose matrix is the transpose of `(gᵢⱼ)`, and the functoriality of the Koszul
complex ([Stacks, Tag 0624], `Koszul.koszul_map_comm`) therefore produces a map of chain
complexes

`K_•(f₁, …, f_n) ⟶ K_•(g₁, …, g_n)`

whose component in degree `k` is `⋀ᵏ ψ`. In degree `1` this is the matrix `(gᵢⱼ)` and in the
top degree `n` it is multiplication by `det (gᵢⱼ)`, by
`exteriorPower.map_top_eq_det_smul`.

This is the comparison map used in the proof of Tate's lemma on the annihilator of the diagonal
ideal ([Stacks, Tag 0BWC]): the two Koszul complexes there are flat resolutions of the same
module, and the comparison, being a quasi-isomorphism of K-flat complexes, survives tensoring —
see `StacksFrontier.RingTheory.Koszul.TorComparison.Independence`.

Note that `Koszul.koszul_map_comm` by itself only states the commutation of `⋀(ψ)` with the two
Koszul differentials. It says nothing about determinants; the degree-`n` identification is the
separate statement `exteriorPower.map_top_eq_det_smul`, and assembling the degreewise maps into
a morphism of chain complexes is the content of `Koszul.relComparison` below.

## Main definitions

* `Koszul.relMap`: the endomorphism of `Rⁿ` attached to the coefficient matrix.
* `Koszul.relComparison`: the resulting map of Koszul complexes `K_•(f) ⟶ K_•(g)`.

## Main results

* `Koszul.seqDual_comp_relMap`: the factorisation `Koszul.seqDual g ∘ ψ = Koszul.seqDual f`.
* `Koszul.relComparison_f`: the degreewise description of the comparison map.
* `Koszul.relComparison_f_top_apply`: in top degree the comparison map is multiplication by
  `det (gᵢⱼ)`.

## References

* [Stacks Project, Tag 0624](https://stacks.math.columbia.edu/tag/0624)
* [Stacks Project, Tag 0BWC](https://stacks.math.columbia.edu/tag/0BWC)
-/

@[expose] public noncomputable section

open CategoryTheory Matrix
open scoped ExteriorAlgebra

universe u

namespace Koszul

variable {R : Type u} [CommRing R] {n : ℕ}

/-- The endomorphism of `Rⁿ` attached to a coefficient matrix `(gᵢⱼ)`, namely the linear map of
the transposed matrix: `v ↦ (j ↦ ∑ᵢ vᵢ gᵢⱼ)`. It is the degree-one component of the Koszul
comparison map of a relation `fᵢ = ∑ⱼ gᵢⱼ gⱼ`. -/
def relMap (gij : Matrix (Fin n) (Fin n) R) : (Fin n → R) →ₗ[R] (Fin n → R) :=
  Matrix.toLin' gij.transpose

/-- The `j`-th coordinate of `Koszul.relMap gij v` is `∑ᵢ gᵢⱼ vᵢ`. -/
theorem relMap_apply (gij : Matrix (Fin n) (Fin n) R) (v : Fin n → R) (j : Fin n) :
    relMap gij v j = ∑ i, gij i j * v i := by
  simp [relMap, Matrix.toLin'_apply, Matrix.mulVec, Matrix.transpose_apply, dotProduct]

/-- A relation `fᵢ = ∑ⱼ gᵢⱼ gⱼ` is exactly a factorisation of the functional `Koszul.seqDual f`
through `Koszul.seqDual g` along `Koszul.relMap gij`. -/
theorem seqDual_comp_relMap (f g : Fin n → R) (gij : Matrix (Fin n) (Fin n) R)
    (h : ∀ i, f i = ∑ j, gij i j * g j) :
    (Koszul.seqDual g).comp (relMap gij) = Koszul.seqDual f := by
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.comp_apply, Koszul.seqDual_apply, Koszul.seqDual_apply]
  calc ∑ j, relMap gij v j * g j
      = ∑ j, ∑ i, v i * (gij i j * g j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [relMap_apply, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i, ∑ j, v i * (gij i j * g j) := Finset.sum_comm
    _ = ∑ i, v i * f i :=
        Finset.sum_congr rfl fun i _ => by rw [← Finset.mul_sum, h i]

/-- **The Koszul comparison map of a relation.** If `fᵢ = ∑ⱼ gᵢⱼ gⱼ` then the exterior powers of
`Koszul.relMap gij` assemble into a map of chain complexes
`K_•(f₁, …, f_n) ⟶ K_•(g₁, …, g_n)`.

Tag 0624 itself is carried by `Koszul.koszul_map_comm`; this is its assembly into a morphism of
chain complexes for the particular `ψ` coming from a coefficient matrix. -/
def relComparison (f g : Fin n → R) (gij : Matrix (Fin n) (Fin n) R)
    (h : ∀ i, f i = ∑ j, gij i j * g j) :
    Koszul.seqComplex f ⟶ Koszul.seqComplex g where
  f k := ModuleCat.ofHom (exteriorPower.map k (relMap gij))
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    rw [Koszul.seqComplex_d, Koszul.seqComplex_d]
    apply ModuleCat.hom_ext
    ext z
    change (⋀[R]^(j + 1) (Fin n → R)) at z
    change Koszul.d (Koszul.seqDual g) j (exteriorPower.map (j + 1) (relMap gij) z) =
      exteriorPower.map j (relMap gij) (Koszul.d (Koszul.seqDual f) j z)
    apply Subtype.ext
    simp only [exteriorPower.coe_map, Koszul.d_apply_coe]
    exact (koszul_map_comm _ _ _ (seqDual_comp_relMap f g gij h)
      (z : ExteriorAlgebra R (Fin n → R))).symm

/-- The degree-`k` component of `Koszul.relComparison f g gij h` is the `k`-th exterior power
`⋀ᵏ (Koszul.relMap gij)`. -/
theorem relComparison_f (f g : Fin n → R) (gij : Matrix (Fin n) (Fin n) R)
    (h : ∀ i, f i = ∑ j, gij i j * g j) (k : ℕ) :
    (relComparison f g gij h).f k = ModuleCat.ofHom (exteriorPower.map k (relMap gij)) :=
  rfl

/-- **In top degree the Koszul comparison map is multiplication by the determinant of the
coefficient matrix.** For a relation `fᵢ = ∑ⱼ gᵢⱼ gⱼ` between two sequences of length `n`, the
degree-`n` component of `Koszul.relComparison` acts on `⋀ⁿ(Rⁿ)` as `det (gᵢⱼ) • id`. -/
theorem relComparison_f_top_apply (f g : Fin n → R) (gij : Matrix (Fin n) (Fin n) R)
    (h : ∀ i, f i = ∑ j, gij i j * g j) (x : ⋀[R]^n (Fin n → R)) :
    ((relComparison f g gij h).f n).hom x = gij.det • x := by
  show exteriorPower.map n (relMap gij) x = gij.det • x
  exact (exteriorPower.map_top_pi_eq_det_smul gij.transpose x).trans
    (by rw [Matrix.det_transpose])

end Koszul

end
