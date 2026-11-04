module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import StacksFrontier.RingTheory.Koszul.Defs
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Functoriality of the Koszul complex

For an `R`-module `E` and `φ : E → R`, the Koszul complex `K_•(φ)` is the exterior algebra
`∧(E)` with the differential `d = Koszul.contraction φ`, the unique degree `-1` antiderivation
with `d(e) = φ(e)` for `e ∈ E`.

## Main results

* `koszul_map_comm`: if `φ' ∘ ψ = φ` for `ψ : E → E'`, then `∧(ψ)` commutes with the Koszul
  differentials, so it is a map of differential graded algebras `K_•(φ) → K_•(φ')`.
* `koszul_scalar_eq_homotopy`: for `e ∈ E` and `f = φ(e)`, multiplication by `f` on `K_•(φ)`
  is `d ∘ e + e ∘ d`, hence null-homotopic.
* `Koszul.seqComplex_mulVec_iso`: the Koszul complexes of a finite sequence `f` and of its image
  `x *ᵥ f` under an invertible matrix `x` are isomorphic.

## Implementation notes

The exterior algebra is `ExteriorAlgebra R E`, the Clifford algebra of the zero quadratic form,
and `∧(ψ)` is `ExteriorAlgebra.map ψ`. The Koszul differential is the left contraction
`CliffordAlgebra.contractLeft φ`, which satisfies
`contractLeft φ (ι a * b) = φ a • b - ι a * contractLeft φ b`
(`CliffordAlgebra.contractLeft_ι_mul`).

A sequence of length `r` is a function `Fin r → R`, and the sequence whose `i`-th entry is
`∑ j, x i j * f j` is `x *ᵥ f`. The isomorphism of Koszul complexes is stated as `Nonempty`.

## References

* [Stacks Project, Tag 0624](https://stacks.math.columbia.edu/tag/0624)
* [Stacks Project, Tag 0625](https://stacks.math.columbia.edu/tag/0625)
* [Stacks Project, Tag 0626](https://stacks.math.columbia.edu/tag/0626)
-/

open scoped TensorProduct

variable {R : Type*} [CommRing R]
variable {E E' : Type*} [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R E']

/-- The graded-algebra homomorphism `∧(ψ) : ∧(E) → ∧(E')` induced by `ψ : E → E'`. -/
noncomputable abbrev exteriorMap (ψ : E →ₗ[R] E') :
    ExteriorAlgebra R E →ₐ[R] ExteriorAlgebra R E' :=
  ExteriorAlgebra.map ψ

/-- **Functoriality of the Koszul complex.**

Let `φ : E → R` and `φ' : E' → R` be `R`-module maps and let `ψ : E → E'` be an `R`-module
map with `φ' ∘ ψ = φ`. Then the induced graded-algebra homomorphism `∧(ψ)` commutes with the
Koszul differentials, i.e. `∧(ψ) ∘ d = d' ∘ ∧(ψ)`, where `d = Koszul.contraction φ` and
`d' = Koszul.contraction φ'`. Together with the fact that `∧(ψ) = ExteriorAlgebra.map ψ` is
automatically a unital graded `R`-algebra homomorphism, this exhibits `∧(ψ)` as a homomorphism
of differential graded `R`-algebras `K_•(φ) → K_•(φ')`. -/
@[stacks 0624, ega "III 1.1.5"]
theorem koszul_map_comm (φ : Module.Dual R E) (φ' : Module.Dual R E') (ψ : E →ₗ[R] E')
    (h : φ'.comp ψ = φ) (x : ExteriorAlgebra R E) :
    exteriorMap ψ (Koszul.contraction φ x) = Koszul.contraction φ' (exteriorMap ψ x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [CliffordAlgebra.contractLeft_algebraMap, AlgHom.commutes,
      CliffordAlgebra.contractLeft_algebraMap]
    simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x m ih =>
    rw [CliffordAlgebra.contractLeft_ι_mul]
    have hmap : exteriorMap ψ (ExteriorAlgebra.ι R m * x)
        = ExteriorAlgebra.ι R (ψ m) * exteriorMap ψ x := by
      rw [map_mul, ExteriorAlgebra.map_apply_ι]
    rw [hmap, CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul, map_mul,
      ExteriorAlgebra.map_apply_ι, ih, ← h]
    rfl

section Koszul

variable {R : Type*} [CommRing R]
variable {E : Type*} [AddCommGroup E] [Module R E]

/-- **Multiplication by `φ e` is null-homotopic on the Koszul complex.** Let `φ : E → R` be an
`R`-module map, let `e ∈ E`, and set `f = φ e`. As `R`-linear endomorphisms of
`K_•(φ) = ∧(E)`, `f = d ∘ e + e ∘ d`, i.e. for every `a`, `f • a = d (e ∧ a) + e ∧ d a`, where
`e ∧ -` is left multiplication by `ι R e` in the exterior algebra. -/
@[stacks 0626, ega "III 1.1.7" "more general"]
theorem koszul_scalar_eq_homotopy (φ : Module.Dual R E) (e : E)
    (a : ExteriorAlgebra R E) :
    φ e • a =
      Koszul.contraction φ (ExteriorAlgebra.ι R e * a)
        + ExteriorAlgebra.ι R e * Koszul.contraction φ a := by
  rw [CliffordAlgebra.contractLeft_ι_mul]
  abel

end Koszul

section MulVec

open CategoryTheory
open scoped ExteriorAlgebra

universe u

namespace Koszul

/-- **Change of basis for a Koszul complex.** If `x` is an invertible `r × r` matrix over `R`, then
the Koszul complex of `f` is isomorphic to the Koszul complex of the sequence
`i ↦ ∑ j, x i j * f j`. -/
@[stacks 0625]
public theorem seqComplex_mulVec_iso {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (x : Matrix (Fin r) (Fin r) R)
    (hx : IsUnit x) :
    Nonempty (Koszul.seqComplex f ≅ Koszul.seqComplex (Matrix.mulVec x f)) := by
  let : Invertible x := hx.invertible
  let e : (Fin r → R) ≃ₗ[R] (Fin r → R) :=
    x.transpose.toLinearEquiv' (Matrix.invertibleTranspose x)
  have he (v : Fin r → R) : e v = x.transpose.mulVec v := rfl
  have hdual : (Koszul.seqDual f).comp e.toLinearMap =
      Koszul.seqDual (Matrix.mulVec x f) := by
    apply LinearMap.ext
    intro v
    show Koszul.seqDual f (e v) = Koszul.seqDual (Matrix.mulVec x f) v
    rw [he]
    simp only [Koszul.seqDual_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1 with i
    congr 1 with j
    ac_rfl
  let en (n : ℕ) : (⋀[R]^n (Fin r → R)) ≃ₗ[R] (⋀[R]^n (Fin r → R)) :=
    LinearEquiv.ofBijective (exteriorPower.map n e.toLinearMap) ⟨
      exteriorPower.map_injective e.symm.toLinearMap (by ext; simp),
      exteriorPower.map_surjective e.surjective⟩
  refine ⟨(HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ LinearEquiv.toModuleIso (en n)) ?_).symm⟩
  intro i j hij
  obtain rfl : j + 1 = i := hij
  rw [Koszul.seqComplex_d, Koszul.seqComplex_d]
  apply ModuleCat.hom_ext
  ext z
  change (⋀[R]^(j + 1) (Fin r → R)) at z
  show Koszul.d (Koszul.seqDual f) j (exteriorPower.map (j + 1) e.toLinearMap z) =
    exteriorPower.map j e.toLinearMap (Koszul.d (Koszul.seqDual (Matrix.mulVec x f)) j z)
  apply Subtype.ext
  simp only [exteriorPower.coe_map, Koszul.d_apply_coe]
  exact (koszul_map_comm _ _ _ hdual (z : ExteriorAlgebra R (Fin r → R))).symm

end Koszul

end MulVec
