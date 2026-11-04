module

public import StacksFrontier.Cotangent.ConormalLowDegree

/-!
# `H^{-1}(L_{B/A})` is `Algebra.H1Cotangent A B`

Let `A → B` be an arbitrary ring map. The degree `-1` cohomology of the cotangent complex
`L_{B/A}` of Tag 08PN is isomorphic to Mathlib's presentation-independent
`Algebra.H1Cotangent A B`, that is to `H¹` of the naive cotangent complex `NL_{B/A}`.

Write `d` for the morphism `𝒥/𝒥² ⟶ Ω` of simplicial `B`-modules on the standard resolution and
factor it as `𝒥/𝒥² ↠ Coim(d) ≅ Im(d) ↪ Ω`. The isomorphism is the composite of
`H₁(Ω) ≅ H₁(Im d)`, the connecting homomorphism `H₁(Coim d) ≅ H₀(Ker d)` of the short exact
sequence `0 → Ker(d) → 𝒥/𝒥² → Coim(d) → 0`, and `H₀(Ker d) ≅ Algebra.H1Cotangent A B`.

## Main definitions

* `Stacks.Cotangent.kernelConormalToCotangentMooreHomologyZeroIso`:
  `H₀(Ker d) ≅ Algebra.H1Cotangent A B`.
* `Stacks.Cotangent.coimageConormalToCotangentMooreHomologyOneIso`: the connecting homomorphism
  `H₁(Coim d) ≅ H₀(Ker d)`.
* `Stacks.Cotangent.cotangentMooreComplexHomologyOneIso`: `H₁` of the Moore complex of the
  cotangent simplicial module is isomorphic to `Algebra.H1Cotangent A B`.
* `Stacks.Cotangent.cotangentComplexHomologyNegOneIsoH1Cotangent`:
  `H^{-1}(L_{B/A}) ≅ Algebra.H1Cotangent A B`.

## Main results

* `Stacks.Cotangent.shortExact_kernelConormalToCotangentMoore`,
  `Stacks.Cotangent.shortExact_imageConormalToCotangentMoore`: the short exact sequences
  `0 → Ker(d) → 𝒥/𝒥² → Coim(d) → 0` and `0 → Im(d) → Ω → Coker(d) → 0`.
* `Stacks.Cotangent.isIso_homologyMap_image_ι_conormalToCotangentMoore`: the inclusion
  `Im(d) ↪ Ω` induces an isomorphism `H₁(Im d) ≅ H₁(Ω)`.

## References

* [Stacks Project, Tag 09D5](https://stacks.math.columbia.edu/tag/09D5)
* [Stacks Project, Tag 08R7](https://stacks.math.columbia.edu/tag/08R7)
* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u v

namespace Stacks.Cotangent

open CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A)

/-- The isomorphism `H₀(Ker d) ≅ Algebra.H1Cotangent A B`, for `d : 𝒥/𝒥² ⟶ Ω` on the standard
resolution. -/
def kernelConormalToCotangentMooreHomologyZeroIso :
    (kernel (conormalToCotangentMoore A B)).homology 0 ≅
      ModuleCat.of ↥B (Algebra.H1Cotangent A ↥B) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{max u v} B) (ComplexShape.down ℕ) 0).mapIso
      (kernelConormalToCotangentMooreIso A B) ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{max u v} B) (ComplexShape.down ℕ) 0).mapIso
      (AlgebraicTopology.alternatingFaceMapComplexConst.app
        (ModuleCat.of ↥B (Algebra.H1Cotangent A ↥B))) ≪≫
    ChainComplex.alternatingConstHomologyZero _

/-- The short exact sequence `0 → Ker(d) → 𝒥/𝒥² → Coim(d) → 0` of complexes. -/
theorem shortExact_kernelConormalToCotangentMoore :
    ((ShortComplex.mk (kernel.ι (conormalToCotangentMoore A B))
        (cokernel.π (kernel.ι (conormalToCotangentMoore A B)))
        (cokernel.condition _) :
      ShortComplex (ChainComplex (ModuleCat.{max u v} B) ℕ))).ShortExact :=
  { exact := ShortComplex.exact_cokernel (kernel.ι (conormalToCotangentMoore A B)) }

/-- The short exact sequence `0 → Im(d) → Ω → Coker(d) → 0` of complexes. -/
theorem shortExact_imageConormalToCotangentMoore :
    ((ShortComplex.mk (kernel.ι (cokernel.π (conormalToCotangentMoore A B)))
        (cokernel.π (conormalToCotangentMoore A B)) (kernel.condition _) :
      ShortComplex (ChainComplex (ModuleCat.{max u v} B) ℕ))).ShortExact :=
  { exact := ShortComplex.exact_kernel (cokernel.π (conormalToCotangentMoore A B)) }

/-- The connecting homomorphism `H₁(Coim d) ≅ H₀(Ker d)` of the short exact sequence
`0 → Ker(d) → 𝒥/𝒥² → Coim(d) → 0`. -/
def coimageConormalToCotangentMooreHomologyOneIso :
    (Abelian.coimage (conormalToCotangentMoore A B)).homology 1 ≅
      (kernel (conormalToCotangentMoore A B)).homology 0 :=
  (shortExact_kernelConormalToCotangentMoore A B).δIso 1 0 rfl
    (isZero_conormalMooreComplex_homology_one A B)
    (isZero_conormalMooreComplex_homology_zero A B)

/-- The inclusion `Im(d) ↪ Ω` induces an isomorphism `H₁(Im d) ≅ H₁(Ω)`. -/
theorem isIso_homologyMap_image_ι_conormalToCotangentMoore :
    IsIso (HomologicalComplex.homologyMap
      (Abelian.image.ι (conormalToCotangentMoore A B)) 1) :=
  isIso_homologyMap_f_of_isZero (shortExact_imageConormalToCotangentMoore A B) 1 2 rfl
    (isZero_homology_cokernel_conormalToCotangentMoore A B 1 one_pos)
    (isZero_homology_cokernel_conormalToCotangentMoore A B 2 two_pos)

/-- The isomorphism `H₁(L_{B/A}) ≅ Algebra.H1Cotangent A B`, on the Moore complex of the
cotangent simplicial module. -/
def cotangentMooreComplexHomologyOneIso :
    (cotangentMooreComplex A B).homology 1 ≅ ModuleCat.of ↥B (Algebra.H1Cotangent A ↥B) :=
  haveI := isIso_homologyMap_image_ι_conormalToCotangentMoore A B
  (asIso (HomologicalComplex.homologyMap
      (Abelian.image.ι (conormalToCotangentMoore A B)) 1)).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{max u v} B) (ComplexShape.down ℕ) 1).mapIso
      (asIso (Abelian.coimageImageComparison (conormalToCotangentMoore A B))).symm ≪≫
    coimageConormalToCotangentMooreHomologyOneIso A B ≪≫
    kernelConormalToCotangentMooreHomologyZeroIso A B

/-- The degree `-1` cohomology of the cotangent complex `L_{B/A}` is isomorphic to
`Algebra.H1Cotangent A B`, that is to `H¹` of the naive cotangent complex, for an arbitrary ring
map `A → B`. -/
def cotangentComplexHomologyNegOneIsoH1Cotangent :
    (cotangentComplex A B).homology (-1) ≅ ModuleCat.of ↥B (Algebra.H1Cotangent A ↥B) :=
  HomologicalComplex.extendHomologyIso (cotangentMooreComplex A B)
      (ComplexShape.embeddingUpIntLE 0) (j := 1) (j' := -1) (by simp) ≪≫
    cotangentMooreComplexHomologyOneIso A B

end Stacks.Cotangent

end
