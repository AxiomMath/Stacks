module

public import StacksFrontier.Homology.PseudoCoherent.Products
import all StacksFrontier.Homology.PseudoCoherent.Products

/-!
# Pseudo-coherence of a projective complex from the products of its tensor homology

Let `S` be a commutative ring and `E` a bounded above complex of projective `S`-modules. Stacks
0CYB characterizes pseudo-coherence by the commutation of the derived tensor product with
products. This file states the complex-level core of that characterization in a form that does
not mention any chosen derived tensor product on `D(S)`: if for every degree `i` and every
index type `A` the functor `N ↦ Hⁱ(E ⊗ N[0])` carries the power `∏_A S` to a product, then `E`
is pseudo-coherent.

This is the form in which the criterion is consumed when `Hⁱ(E ⊗ N[0])` is only known through a
natural identification with another functor of `N` (for instance maps out of a perfect object
on an algebraic space), since preservation of a product is invariant under natural isomorphism.

## Main results

* `StacksDraft.PseudoCoherence.preservesLimitsOfShape_homologyFunctor_moduleCat`: homology of
  cochain complexes of modules commutes with products.
* `StacksDraft.PseudoCoherence.isPseudoCoherent_of_preservesLimit_homology_tensor`: the criterion.

## References

* [Stacks Project, Tag 0CYB](https://stacks.math.columbia.edu/tag/0CYB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe v

namespace StacksDraft.PseudoCoherence

attribute [local instance] HasDerivedCategory.standard

variable {S : Type v} [CommRing S]

/-- **Homology of complexes of modules commutes with products.** Products of modules are exact,
so the homology of a short complex commutes with them, and the short complex in a degree of a
product of complexes is the product of the short complexes. -/
theorem preservesLimitsOfShape_homologyFunctor_moduleCat (A : Type v) (i : ℤ) :
    PreservesLimitsOfShape (Discrete A)
      (HomologicalComplex.homologyFunctor (ModuleCat.{v} S) (ComplexShape.up ℤ) i) := by
  have : PreservesLimitsOfShape (Discrete A)
      (HomologicalComplex.shortComplexFunctor (ModuleCat.{v} S) (ComplexShape.up ℤ) i) := by
    exact ⟨⟨fun hE => ⟨ShortComplex.isLimitOfIsLimitπ _
      (isLimitOfPreserves (HomologicalComplex.eval _ (ComplexShape.up ℤ) _) hE)
      (isLimitOfPreserves (HomologicalComplex.eval _ (ComplexShape.up ℤ) i) hE)
      (isLimitOfPreserves (HomologicalComplex.eval _ (ComplexShape.up ℤ) _) hE)⟩⟩⟩
  have := Stacks.DerivedProducts.preservesLimitsOfShape_shortComplexHomologyFunctor
    (A := ModuleCat.{v} S) (I := A)
  show PreservesLimitsOfShape (Discrete A)
    (HomologicalComplex.shortComplexFunctor (ModuleCat.{v} S) (ComplexShape.up ℤ) i ⋙
      ShortComplex.homologyFunctor (ModuleCat.{v} S))
  infer_instance

/-- **The complex-level core of Stacks 0CYB.** Let `E` be a bounded above complex of projective
`S`-modules. If for every degree `i` and every index type `A` the functor `N ↦ Hⁱ(E ⊗ N[0])`
preserves the power `∏_A S`, then `E` is pseudo-coherent. -/
theorem isPseudoCoherent_of_preservesLimit_homology_tensor
    (E : CochainComplex (ModuleCat.{v} S) ℤ) (b : ℤ) [E.IsStrictlyLE b]
    (hp : ∀ i, Projective (E.X i))
    (h : ∀ (A : Type v) (i : ℤ),
      PreservesLimit (Discrete.functor fun _ : A => ModuleCat.of S S)
        (HomologicalComplex.single (ModuleCat.{v} S) (ComplexShape.up ℤ) 0 ⋙
          (curriedTensor (ModuleCat.{v} S)).map₂CochainComplex.obj E ⋙
            HomologicalComplex.homologyFunctor (ModuleCat.{v} S) (ComplexShape.up ℤ) i)) :
    IsPseudoCoherent (DerivedCategory.Q.obj E) := by
  have hiso (A : Type v) (i : ℤ) : IsIso (HomologicalComplex.homologyMap
      (((moduleTensorRingPowerComparison S A).mapHomologicalComplex
        (ComplexShape.up ℤ)).app E) i) := by
    apply (isIso_homology_moduleTensorRingPowerComparison_iff S A E i).mpr
    let H := HomologicalComplex.homologyFunctor (ModuleCat.{v} S) (ComplexShape.up ℤ) i
    have := preservesLimitsOfShape_homologyFunctor_moduleCat (S := S) A i
    have : PreservesLimit (Discrete.functor fun _ : A => ModuleCat.of S S)
        (tensorWithCochainComplex E ⋙ H) := h A i
    have hc : IsIso (piComparison (tensorWithCochainComplex E ⋙ H)
        (fun _ : A => ModuleCat.of S S)) := inferInstance
    rw [Stacks.DerivedProducts.piComparison_comp_eq] at hc
    exact IsIso.of_isIso_comp_right (H.map (piComparison (tensorWithCochainComplex E)
      (fun _ : A => ModuleCat.of S S)))
      (piComparison H fun _ : A => (tensorWithCochainComplex E).obj (ModuleCat.of S S))
  refine (pseudoCoherent_iff_all _).mpr fun m => ?_
  have hE : RingPowerHomologyRange E m := fun A =>
    ⟨fun i _ => hiso A i, by have := hiso A m; infer_instance⟩
  let n := (b - m + 1).toNat
  have hbound : E.IsStrictlyLE (m + n - 1) := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact CochainComplex.isZero_of_isStrictlyLE E b i (by dsimp [n] at hi; omega)
  exact isPseudoCoherentFrom_of_ringPowerHomologyRange_aux m n E hbound hp hE

end StacksDraft.PseudoCoherence
