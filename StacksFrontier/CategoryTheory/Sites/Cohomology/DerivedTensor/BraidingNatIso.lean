module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ConstraintNaturality

/-!
# The commutativity constraint of a derived tensor product as an isomorphism of bifunctors

Let `(C, O)` be a ringed site and `T` a derived tensor product on it in the sense of
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct`. The commutativity constraint of
[Stacks, Tag 0FPT] is available in two shapes:
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingIso`, an isomorphism
`A ⊗^𝐋_O B ≅ B ⊗^𝐋_O A` at a fixed pair of objects, and
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingTrans`, a morphism of bifunctors
`- ⊗^𝐋_O - ⟶ (- ⊗^𝐋_O -)ᶠˡⁱᵖ`, which is where the naturality in the pair lives.

The second carried no invertibility. This file supplies it: the two shapes agree at every pair
of objects, by
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingIso_hom_eq`, so `braidingTrans`
is invertible componentwise and therefore invertible as a morphism of bifunctors.

The reason to want this is that an isomorphism of bifunctors can be evaluated at one object to
give an isomorphism of *functors* `B ⊗^𝐋_O - ≅ - ⊗^𝐋_O B`, which is what transports an
adjunction with one of these as left adjoint to an adjunction with the other, by
`CategoryTheory.Adjunction.ofNatIsoLeft`. The componentwise constraint does not do this: a
family of isomorphisms indexed by objects is not an isomorphism of functors.

## Main definitions

* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingNatIso`: the commutativity
  constraint as an isomorphism of bifunctors `- ⊗^𝐋_O - ≅ (- ⊗^𝐋_O -)ᶠˡⁱᵖ`.
* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.tensorFlipSlotIso`: its value at an
  object `B`, an isomorphism of functors `B ⊗^𝐋_O - ≅ - ⊗^𝐋_O B`.

## Main results

* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.isIso_braidingTrans`: the commutativity
  constraint of a derived tensor product is invertible as a morphism of bifunctors.
* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingNatIso_hom_app_app`: its value
  at a pair of objects is `braidingIso` there, so it is the constraint of [Stacks, Tag 0FPT] and
  not some other isomorphism between the two bifunctors.

## Implementation notes

No tag is placed here. [Stacks, Tag 0FPT] is registered on the constraints themselves, in
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/DerivedSymmetryAndUnit.lean`; this
file only records that one of them is invertible in a functor category, which is not a further
part of that tag. In particular nothing below assumes any coherence of the constraints, which
this development does not have.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] _root_.SheafOfModules.monoidalCategorySheafTensor
  _root_.SheafOfModules.symmetricCategorySheafTensor
  _root_.SheafOfModules.monoidalPreadditiveSheafTensor
  _root_.SheafOfModules.monoidalClosedSheafTensor
  _root_.SheafOfModules.preservesColimit_tensorRight_sheafTensor

namespace Stacks.DerivedTensor.RingedSite

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K L : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

namespace DerivedTensorProduct

variable (T : DerivedTensorProduct X.O)

/-- At a pair of objects the commutativity constraint of a derived tensor product, read as a
morphism of bifunctors, is invertible: it is the isomorphism `braidingIso` there. -/
theorem isIso_braidingTrans_app_app (A B : DerivedModules X.O) :
    IsIso (((braidingTrans X T).app A).app B) := by
  rw [← braidingIso_hom_eq]
  infer_instance

/-- At an object the commutativity constraint of a derived tensor product is invertible as a
morphism of functors, because it is invertible at every object of the remaining variable. -/
theorem isIso_braidingTrans_app (A : DerivedModules X.O) :
    IsIso ((braidingTrans X T).app A) :=
  have := isIso_braidingTrans_app_app X T A
  NatIso.isIso_of_isIso_app _

/-- **The commutativity constraint of a derived tensor product is invertible as a morphism of
bifunctors.** Each of its values is the isomorphism of [Stacks, Tag 0FPT] at that pair of
objects. -/
theorem isIso_braidingTrans : IsIso (braidingTrans X T) :=
  have := isIso_braidingTrans_app X T
  NatIso.isIso_of_isIso_app _

/-- **The commutativity constraint of a derived tensor product as an isomorphism of
bifunctors**: `- ⊗^𝐋_O - ≅ (- ⊗^𝐋_O -)ᶠˡⁱᵖ`. This is
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingTrans`, which is invertible by
`isIso_braidingTrans`. -/
def braidingNatIso : T.tensor ≅ T.tensor.flip :=
  haveI := isIso_braidingTrans X T
  asIso (braidingTrans X T)

/-- The isomorphism of bifunctors is the commutativity constraint of [Stacks, Tag 0FPT] at each
pair of objects. -/
theorem braidingNatIso_hom_app_app (A B : DerivedModules X.O) :
    ((braidingNatIso X T).hom.app A).app B = (T.braidingIso X A B).hom :=
  (braidingIso_hom_eq X T A B).symm

/-- **The commutativity constraint read at one object**: an isomorphism of functors
`B ⊗^𝐋_O - ≅ - ⊗^𝐋_O B`. This is the isomorphism along which an adjunction whose left adjoint
tensors on one side is transported to one whose left adjoint tensors on the other. -/
def tensorFlipSlotIso (B : DerivedModules X.O) : T.tensor.obj B ≅ T.tensor.flip.obj B :=
  (braidingNatIso X T).app B

/-- The isomorphism of functors `tensorFlipSlotIso` is the commutativity constraint of
[Stacks, Tag 0FPT] at each object of the remaining variable. -/
theorem tensorFlipSlotIso_hom_app (B A : DerivedModules X.O) :
    (tensorFlipSlotIso X T B).hom.app A = (T.braidingIso X B A).hom :=
  braidingNatIso_hom_app_app X T B A

end DerivedTensorProduct

end Stacks.DerivedTensor.RingedSite

end
