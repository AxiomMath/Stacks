module

public import StacksFrontier.Cotangent.FlatTowerDescent
public import StacksFrontier.Cotangent.TensorProductNineDiagramCanonical

/-!
# The cone of the right column of Equation 92.15.0.1 along a weakly étale base change

Let `R` be a ring, let `A`, `B` be `R`-algebras and let `A ⊗_R B → C` be a weakly étale ring
map. The right column of the nine diagram of [Stacks, Tag 09D9] starts with the canonical map
`L_{B/R} ⊗^𝐋_B (A ⊗_R B) ⟶ L_{A ⊗_R B/A}`; its cone is the object `E` of Equation 92.15.0.1.
This file proves that a cone of the corresponding map `L_{B/R} ⊗^𝐋_B C ⟶ L_{C/A}` over `C` has
cohomology `H^i(E) ⊗_{A ⊗_R B} C`.

This is the ring-theoretic half of the proof of [Stacks, Tag 09DM]: for a geometric point of a
fibre product of algebraic spaces, the étale local ring `C` of the fibre product is weakly étale
over the tensor product `A ⊗_R B` of the other étale local rings
(`AlgebraicGeometry.Space.cartesian_etaleStalk_tensor_weaklyEtale`), and the stalk of the object
`E` of Equation 92.28.0.1 is a cone of `L_{B/R} ⊗^𝐋_B C ⟶ L_{C/A}`.

## Main results

* `CommAlgCat.nonempty_homology_cone_iso_extendScalars_tensorProduct`: for weakly étale
  `A ⊗_R B → C`, `H^i(E_C) ≅ H^i(E) ⊗_{A ⊗_R B} C` for any cone `E_C` of
  `L_{B/R} ⊗^𝐋_B C ⟶ L_{C/A}` and any cone `E` of
  `CommAlgCat.cotangentTensorProductBaseChangeMapRight R A B`.

## References

* [Stacks Project, Tag 09D9](https://stacks.math.columbia.edu/tag/09D9)
* [Stacks Project, Tag 09DM](https://stacks.math.columbia.edu/tag/09DM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped TensorProduct

universe u

namespace CommAlgCat

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] HasDerivedCategory.standard

variable (R : Type u) [CommRing R] (A B : Type u) [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  (C : Type u) [CommRing C] [Algebra (A ⊗[R] B) C] [Algebra R C] [Algebra A C] [Algebra B C]
  [IsScalarTower R (A ⊗[R] B) C] [IsScalarTower A (A ⊗[R] B) C] [IsScalarTower B (A ⊗[R] B) C]
  [IsScalarTower R A C] [IsScalarTower R B C] [Algebra.WeaklyEtale (A ⊗[R] B) C]

/-- **The cone of the right column along a weakly étale base change.** If `A ⊗_R B → C` is
weakly étale, any cone `E_C` of `L_{B/R} ⊗^𝐋_B C ⟶ L_{C/A}` (the first displayed morphism of
`R → B → C` followed by the second displayed morphism of `R → A → C`) has
`H^i(E_C) ≅ H^i(E) ⊗_{A ⊗_R B} C`, for any cone `E` of the first map
`CommAlgCat.cotangentTensorProductBaseChangeMapRight R A B` of the right column of
Equation 92.15.0.1. -/
theorem nonempty_homology_cone_iso_extendScalars_tensorProduct
    {E : DerivedCategory (ModuleCat.{u} (A ⊗[R] B))}
    {b : cotangentComplexDerived.{u, u} A (CommAlgCat.of A (A ⊗[R] B)) ⟶ E}
    {e : E ⟶ (cotangentComplexDerivedBaseChange R (CommAlgCat.of R B) (A ⊗[R] B))⟦(1 : ℤ)⟧}
    (hE : Triangle.mk (cotangentTensorProductBaseChangeMapRight R A B) b e ∈ distTriang _)
    {EC : DerivedCategory (ModuleCat.{u} C)}
    {b' : cotangentComplexDerived.{u, u} A (CommAlgCat.of A C) ⟶ EC}
    {e' : EC ⟶ (fundamentalVertex₁.{u, u, u + 1, u + 1} R B C)⟦(1 : ℤ)⟧}
    (hC : Triangle.mk (fundamentalMor₁.{u} R B C ≫ fundamentalMor₂.{u} R A C) b' e' ∈
      distTriang (DerivedCategory (ModuleCat.{u} C))) (i : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} C) i).obj EC ≅
      (ModuleCat.extendScalars.{u, u, u} (algebraMap (A ⊗[R] B) C)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] B)) i).obj E)) := by
  rw [← fundamentalMor₁_comp_fundamentalMor₂_includeRight R A B] at hE
  exact nonempty_homology_cone_iso_extendScalars_of_weaklyEtale R A B (A ⊗[R] B) C hE hC i

end CommAlgCat

end
