module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.CanonicalCupProductLawsReduction
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.GradedCommutativity

/-!
# The wedge product satisfies the monoidal identities of complexes

Let `Ω^•` be the relative de Rham complex of `φ : A ⟶ 𝒪_X` and let
`∧ : Tot(Ω^• ⊗_A Ω^•) ⟶ Ω^•` be the wedge product of Tag 0FM2. Read on the extension by zero
`Ω' = (deRhamComplex B D).extend embeddingUpNat` of the de Rham complex to a `ℤ`-indexed
complex (which is `AlgebraicGeometry.SheafOfModules.deRhamComplexInt B D`, read over the ring sheaf
`Stacks.SheafOfModules.Tensor.ringSheaf A` that the monoidal structure is stated over), the
extended wedge product
`m = AlgebraicGeometry.SheafOfModules.multiplicationInt (wedgeProduct B D)` is associative and
commutative for the symmetric monoidal structure of complexes of Stacks 0FPQ:

`(m ⊗ 𝟙) ≫ m = α ≫ (𝟙 ⊗ m) ≫ m`  and  `β ≫ m = m`,

the second with the Koszul symmetry, whose sign `(-1)^{pq}` is the sign of the graded
commutativity of `∧`. These are the hypotheses of Cohomology, Lemmas 0FP4 and 0FP5 for the cup
product on de Rham cohomology (Tag 0FM3).

## Main results

* `AlgebraicGeometry.SheafOfModules.wedgeProductInt_assoc`: **the extended wedge product is
  associative.**
* `AlgebraicGeometry.SheafOfModules.wedgeProductInt_braiding`: **the extended wedge product is
  commutative for the Koszul symmetry.**

## Implementation notes

Both are the reductions `AlgebraicGeometry.SheafOfModules.multiplicationInt_assoc` and
`AlgebraicGeometry.SheafOfModules.multiplicationInt_braiding` of the identities to local pure
tensors, applied to the laws `AlgebraicGeometry.SheafOfModules.wedgeProduct_summand_assoc` and
`AlgebraicGeometry.SheafOfModules.wedgeProduct_summand_comm` of the wedge product on the summands
of the total complex.

## References

* [Stacks Project, Tag 0FM2](https://stacks.math.columbia.edu/tag/0FM2)
* [Stacks Project, Tag 0FM3](https://stacks.math.columbia.edu/tag/0FM3)
* [Stacks Project, Tag 0FPQ](https://stacks.math.columbia.edu/tag/0FPQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory ComplexShape
open TopologicalSpace
open scoped Stacks.Topology.SheafTensorAdditiveOnOpens

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] abelianModules hasSheafifyOpens wEqualsLocallyBijectiveOpens

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

section Monoidal

attribute [local instance] _root_.SheafOfModules.monoidalCategorySheafTensor
  _root_.SheafOfModules.symmetricCategorySheafTensor
  _root_.SheafOfModules.monoidalPreadditiveSheafTensor
  Stacks.Cohomology.MonoidalComplexesOfModules.cochainComplexMonoidalCategory

/-- **The extended wedge product is associative**: `(m ⊗ 𝟙) ≫ m = α ≫ (𝟙 ⊗ m) ≫ m` for
`m = multiplicationInt (wedgeProduct B D)` on the extension by zero of the de Rham complex, in
the symmetric monoidal category of complexes of Stacks 0FPQ. -/
theorem wedgeProductInt_assoc :
    (multiplicationInt (wedgeProduct B D) ⊗ₘ 𝟙 ((deRhamComplex B D).extend embeddingUpNat)) ≫
        multiplicationInt (wedgeProduct B D) =
      (α_ ((deRhamComplex B D).extend embeddingUpNat) ((deRhamComplex B D).extend embeddingUpNat)
        ((deRhamComplex B D).extend embeddingUpNat)).hom ≫
        (𝟙 ((deRhamComplex B D).extend embeddingUpNat) ⊗ₘ multiplicationInt (wedgeProduct B D)) ≫
          multiplicationInt (wedgeProduct B D) :=
  multiplicationInt_assoc (wedgeProduct B D) (wedgeProduct B D) (wedgeProduct B D)
    (wedgeProduct B D) fun a b c U x y z => wedgeProduct_summand_assoc B D a b c U x y z

end Monoidal

section Symmetric

attribute [local instance] _root_.SheafOfModules.monoidalCategorySheafTensor
  _root_.SheafOfModules.symmetricCategorySheafTensor
  _root_.SheafOfModules.monoidalPreadditiveSheafTensor
  _root_.SheafOfModules.monoidalClosedSheafTensor
  _root_.SheafOfModules.preservesColimit_tensorRight_sheafTensor
  Stacks.Cohomology.MonoidalComplexesOfModules.cochainComplexMonoidalCategory
  Stacks.Cohomology.MonoidalComplexesOfModules.cochainComplexSymmetricCategory

/-- **The extended wedge product is commutative for the Koszul symmetry**: `β ≫ m = m` for
`m = multiplicationInt (wedgeProduct B D)` on the extension by zero of the de Rham complex, the
symmetry being the Koszul symmetry of complexes of Stacks 0FPQ. -/
theorem wedgeProductInt_braiding :
    (β_ ((deRhamComplex B D).extend embeddingUpNat)
        ((deRhamComplex B D).extend embeddingUpNat)).hom ≫
        multiplicationInt (wedgeProduct B D) =
      multiplicationInt (wedgeProduct B D) :=
  multiplicationInt_braiding (wedgeProduct B D) (wedgeProduct B D)
    fun a b U x y => wedgeProduct_summand_comm B D a b U x y

end Symmetric

end AlgebraicGeometry.SheafOfModules

end
