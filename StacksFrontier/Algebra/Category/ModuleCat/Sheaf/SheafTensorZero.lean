module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingSheafProductFactorOrthogonal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafifiedDirectSum

/-!
# A zero sheaf of modules tensored with anything is zero

The tensor product of sheaves of modules is the sheafification of the objectwise tensor product
of the underlying presheaves, so a zero factor kills it: over every object of the site one of the
two modules of sections is trivial, hence so is their tensor product, and the sheafification of a
presheaf with trivial sections is a zero object.

## Main results

* `Stacks.SheafOfModules.subsingleton_tensorProduct_of_subsingleton_left` and
  `...._right`: the tensor product of modules with a trivial factor is trivial.
* `Stacks.SheafOfModules.isZero_presheafTensor_of_isZero_left`: the **presheaf** tensor product
  with a zero factor is a zero object.
* `Stacks.SheafOfModules.isZero_sheafTensor_of_isZero_left` and
  `Stacks.SheafOfModules.isZero_tensorObj_of_isZero_left`: the same for the tensor product
  **sheaf**, at the `Tensor.sheafTensor` spelling and at the `⊗` of
  `SheafOfModules.monoidalCategorySheafTensor`, which has the former as its tensor product on the
  nose.

## Implementation notes

This generalizes the two steps by which
`Stacks.SheafOfModules.RingSheafProductFactor.isZero_sheafTensor_restrictScalars` proves the
orthogonality of two distinct factors of a product decomposition off `factorModule`: there the
objectwise vanishing comes from the idempotent cutting out one factor acting as the identity on
one side and as zero on the other, here from one side having no sections at all. The second step
— that sheafification carries the resulting zero presheaf to a zero object — is already general
there (`Tensor.sheafifyMod R |>.map_isZero`) and is reused unchanged.

Note that `Stacks.Cohomology.MonoidalDerived.isZero_tensorObj_of_isZero_left` of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorKFlatOneSided` is **not** this
statement: it is about `DerivedModules` and the derived tensor product of Stacks 0FPB. The
present one is about sheaves of modules and the tensor product of Tag 01CA.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w t

namespace Stacks.SheafOfModules

/-- The tensor product of modules one of which is trivial is trivial: every element is a sum of
pure tensors and each of those has a vanishing left factor. -/
public theorem subsingleton_tensorProduct_of_subsingleton_left {A : Type*} [CommRing A]
    {M : Type*} [AddCommGroup M] [Module A M] {N : Type*} [AddCommGroup N] [Module A N]
    (hM : Subsingleton M) : Subsingleton (TensorProduct A M N) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | tmul a b => rw [hM.elim a 0, TensorProduct.zero_tmul]
  | add x y hx hy => rw [hx, hy, add_zero]

/-- The tensor product of modules one of which is trivial is trivial. -/
public theorem subsingleton_tensorProduct_of_subsingleton_right {A : Type*} [CommRing A]
    {M : Type*} [AddCommGroup M] [Module A M] {N : Type*} [AddCommGroup N] [Module A N]
    (hN : Subsingleton N) : Subsingleton (TensorProduct A M N) := by
  have := subsingleton_tensorProduct_of_subsingleton_left (A := A) (M := N) (N := M) hN
  exact (TensorProduct.comm A M N).injective.subsingleton

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{max u v}}

/-- **The presheaf tensor product with a zero factor is a zero object.** Over every object of the
site the left module of sections is trivial, so the tensor product of sections is. -/
public theorem isZero_presheafTensor_of_isZero_left
    (A B : _root_.SheafOfModules.{max u v} (Tensor.ringSheaf R)) (hA : IsZero A) :
    IsZero ((((PresheafOfModules.tensorBifunctor (R).obj)).obj A.val).obj B.val) :=
  RingSheafProductFactor.isZero_presheaf_of_forall_subsingleton_sections _ fun U =>
    subsingleton_tensorProduct_of_subsingleton_left (Stacks.subsingleton_of_isZero hA U)

variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]

/-- **The tensor product sheaf with a zero factor is a zero object.** The presheaf tensor product
is already zero and sheafification preserves zero objects. -/
public theorem isZero_sheafTensor_of_isZero_left
    (A B : _root_.SheafOfModules.{max u v} (Tensor.ringSheaf R)) (hA : IsZero A) :
    IsZero (((Tensor.sheafTensor R).obj A).obj B) :=
  ((PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf (R))
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (R)).obj))).map_isZero
    (isZero_presheafTensor_of_isZero_left A B hA)

variable [HasBinaryBiproducts (_root_.SheafOfModules (Tensor.ringSheaf R))]

omit [HasBinaryBiproducts (_root_.SheafOfModules (Tensor.ringSheaf R))] in
/-- **A zero sheaf of modules tensored with anything is a zero object**, at the monoidal
spelling: `SheafOfModules.monoidalCategorySheafTensor` has `Tensor.sheafTensor` as its tensor
product on the nose. -/
public theorem isZero_tensorObj_of_isZero_left
    (A B : _root_.SheafOfModules.{max u v} (Tensor.ringSheaf R)) (hA : IsZero A) :
    letI := _root_.SheafOfModules.monoidalCategorySheafTensor R
    IsZero (MonoidalCategory.tensorObj A B) :=
  isZero_sheafTensor_of_isZero_left A B hA

end Stacks.SheafOfModules

end
