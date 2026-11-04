module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.MatrixAlgebraSections

/-!
# A point of the matrix algebra sheaf is a combination of the matrix units

Let `S` be a scheme and `I` a finite index type. A point of the matrix algebra sheaf
`Mat_I(𝒪_S) = 𝓗om(𝒪_S^{(I)}, 𝒪_S^{(I)})` is an endomorphism of the free sheaf of modules
(`CategoryTheory.MonoidalClosed.curry'`), and
`Stacks.EtaleCohomology.BrauerScheme.freeDualMatrix` reads off its matrix over the ring
`R₀ S = End (𝒪_S)`. This file records the resulting expansion: **the point attached to an
endomorphism is the combination of the matrix units with its matrix entries as coefficients,**
$$
\mathrm{curry}'(f) = \sum_{(a,b)} f_{ab} \cdot e_{ab}.
$$

This is the point-level counterpart of `Stacks.Matrix.unitCombination`, and it is what lets a
computation with a specific endomorphism — Saltman's projector `altProjFree` of
[Stacks, Tag 0A2L], whose matrix is `Matrix.altProj` — be carried out one matrix unit at a time.
The matrix units are the objects whose behaviour under the tensor-power identifications is known
(`Stacks.EtaleCohomology.BrauerScheme.conj_natTensorPowFreeIso_uncurry'_matIncl`: a matrix unit of
the algebra of size `d ^ m` is a tensor of matrix units of the algebra of size `d`), so an
expansion into matrix units is what reduces a statement about the projector to statements about
them.

The proof is the dual-basis identity
`Stacks.EtaleCohomology.BrauerScheme.sum_matCoord_comp_matIncl` — the matrix units and the matrix
coordinates compose to the identity of the algebra sheaf — together with
`Stacks.EtaleCohomology.BrauerScheme.curry'_comp_matCoord`, which says that the coordinates of the
point of `f` are the matrix entries of `f`.

## Main results

* `Stacks.EtaleCohomology.BrauerScheme.curry'_eq_sum_matIncl`: **the point of the matrix algebra
  sheaf attached to an endomorphism of the free sheaf of modules is the combination of the matrix
  units with the entries of its matrix as coefficients.**

## References

* [Stacks Project, Tag 0A2L](https://stacks.math.columbia.edu/tag/0A2L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry TopologicalSpace
open Stacks.SheafOfModules

universe u

noncomputable section

namespace Stacks.EtaleCohomology.BrauerScheme

attribute [local instance] hasFiniteBiproductsModuleSheaf monoidalPreadditiveModuleSheaf

variable {S : Scheme.{u}} {I : Type u} [Fintype I] [DecidableEq I]

/-- **The point of the matrix algebra sheaf attached to an endomorphism of the free sheaf of
`𝒪_S`-modules is the combination of the matrix units with the entries of its matrix as
coefficients.** The coefficients are elements of `R₀ S = End (𝒪_S)`, i.e. endomorphisms of the
monoidal unit, so the scalar multiplication is composition. -/
theorem curry'_eq_sum_matIncl (f : freeModule S I ⟶ freeModule S I) :
    MonoidalClosed.curry' f
      = ∑ k : I × I, freeDualMatrix f k.1 k.2 ≫ matIncl (S := S) k := by
  have h : MonoidalClosed.curry' f
      = ∑ k : I × I, MonoidalClosed.curry' f ≫ matCoord (S := S) k ≫ matIncl k := by
    rw [← Preadditive.comp_sum, sum_matCoord_comp_matIncl, Category.comp_id]
  refine h.trans (Finset.sum_congr rfl fun k _ => ?_)
  obtain ⟨a, b⟩ := k
  rw [← Category.assoc, curry'_comp_matCoord]

end Stacks.EtaleCohomology.BrauerScheme

end

end
