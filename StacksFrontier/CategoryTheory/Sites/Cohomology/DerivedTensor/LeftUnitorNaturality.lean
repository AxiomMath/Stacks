module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ConstraintNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DerivedUnitorCoherence
import StacksCore.Tactic.StacksAttribute

/-!
# The left unit constraint of the derived tensor product on a ringed site is natural

Let `(C, 𝒪)` be a ringed site and `T` a derived tensor product on it in the sense of
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct`, that is [Stacks, Tag 06YU]. The left
unit constraint `𝒪[0] ⊗^𝐋_𝒪 A ≅ A` of [Stacks, Tag 0FPT] is constructed one object at a time,
as `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitIso`, and nothing is proved
there about how it varies with `A`. This file supplies that, so that the left unit constraint is
available as an isomorphism of *functors* `𝒪[0] ⊗^𝐋_𝒪 - ≅ 𝟭 D(𝒪)`.

## Main results

* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitIso_naturality`: the naturality
  square of the left unit constraint.
* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitNatIso`: the left unit
  constraint as an isomorphism of functors.

## The proof

The left unit constraint is *defined* as the right one read through the commutativity
constraint, `leftUnitIso_eq`, and both of those carry their naturality:
`braidingIso_hom_naturality` is natural in both objects, and `rightUnitIso_hom_naturality` is the
naturality of the right constraint. Taking the identity of `𝒪[0]` for the first variable of the
braiding turns the first into the square that moves `𝒪[0] ⊗ -` past the braiding, and the two
squares paste.

The counterpart on the right is
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitorNatIso` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RightUnitorNaturality`. It is the
same type of statement but not the same construction: that one is a localization lift through
the K-flat comparison and is *not* identified with the pointwise `rightUnitIso`, whereas
`leftUnitNatIso` below has the pointwise `leftUnitIso` as its components by `rfl`
(`leftUnitNatIso_app`).

Like it, this is strictly more than the family of isomorphisms the construction supplies and
strictly less than the monoidal structure: the associativity constraint, the pentagon, the
hexagon, the unit triangles and the involutivity of the braiding are still not proved, so
[Stacks, Tag 0FPT] is not discharged here.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.DerivedTensor.RingedSite.DerivedTensorProduct

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  (T :
    letI : HasSheafify X.J AddCommGrpCat.{u} := inferInstance
    letI : X.J.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
    letI := Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u} X.O
    DerivedTensorProduct X.O)

/-- **The left unit constraint of [Stacks, Tag 0FPT] is natural in the object**: for
`a : A ⟶ B` in `D(𝒪)` the square

`(𝟙 ⊗ a) ≫ λ_B = λ_A ≫ a`

commutes. The construction of `leftUnitIso` is object by object and proves nothing about how it
varies; this is that missing statement. -/
theorem leftUnitIso_naturality {A B : DerivedModules X.O} (a : A ⟶ B) :
    letI : HasSheafify X.J AddCommGrpCat.{u} := inferInstance
    letI : X.J.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
    letI := Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u} X.O
    (T.tensor.obj (unitObject X)).map a ≫ (T.leftUnitIso X B).hom =
      (T.leftUnitIso X A).hom ≫ a := by
  let : HasSheafify X.J AddCommGrpCat.{u} := inferInstance
  let : X.J.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  let := Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u} X.O
  have hb := braidingIso_hom_naturality X T (𝟙 (unitObject X)) a
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
    Category.comp_id] at hb
  rw [leftUnitIso_eq, leftUnitIso_eq]
  simp only [Iso.trans_hom, Category.assoc]
  have hr : (T.tensor.map a).app (unitObject X) ≫ (T.rightUnitIso X B).hom =
      (T.rightUnitIso X A).hom ≫ a :=
    rightUnitIso_hom_naturality X T a
  rw [← Category.assoc, hb, Category.assoc, hr]

/-- **[Stacks, Tag 0FPT], the unit constraint on the left as an isomorphism of functors:**
`𝒪[0] ⊗^𝐋_𝒪 - ≅ 𝟭 D(𝒪)`. Its components are
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitIso` and its naturality is
`leftUnitIso_naturality`. -/
def leftUnitNatIso :
    letI : HasSheafify X.J AddCommGrpCat.{u} := inferInstance
    letI : X.J.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
    letI := Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u} X.O
    T.tensor.obj (unitObject X) ≅ 𝟭 (DerivedModules X.O) :=
  letI : HasSheafify X.J AddCommGrpCat.{u} := inferInstance
  letI : X.J.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  letI := Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u} X.O
  NatIso.ofComponents (fun A => T.leftUnitIso X A) (fun {_ _} a => leftUnitIso_naturality X T a)

/-- The components of `leftUnitNatIso` are the left unit constraints. -/
lemma leftUnitNatIso_app (A : DerivedModules X.O) :
    letI : HasSheafify X.J AddCommGrpCat.{u} := inferInstance
    letI : X.J.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
    letI := Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u} X.O
    (leftUnitNatIso X T).app A = T.leftUnitIso X A :=
  rfl

end Stacks.DerivedTensor.RingedSite.DerivedTensorProduct

end
