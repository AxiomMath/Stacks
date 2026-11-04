module

public import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityPullbackComparisonCanonical
public import StacksFrontier.CategoryTheory.Monoidal.Reseat
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.AssociativityGeneral

/-!
# The monoidal structure of `D_QCoh(𝒪_X)` for an algebraic space

For an algebraic space `X` the derived category `D(𝒪_X)` is monoidal with tensor product
`- ⊗^L_{𝒪_X} -` and unit `𝒪_X` in degree zero (Stacks 0FPT, re-seated onto the derived tensor
product). By Stacks 08F5 the full subcategory `D_QCoh(𝒪_X)` is closed under it, and it contains
the unit, so `D_QCoh(𝒪_X)` is monoidal, with tensor product `quasicoherentDerivedTensor` and unit
`derivedStructureSheaf` on the nose. A dual in `D(𝒪_X)` of two objects of `D_QCoh(𝒪_X)` is a
dual in `D_QCoh(𝒪_X)`.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDerivedMonoidal`: the monoidal structure on `D(𝒪_X)`.
* `AlgebraicGeometry.Space.quasicoherentDerivedMonoidal`: the monoidal structure on
  `D_QCoh(𝒪_X)`, with tensor product `AlgebraicGeometry.Space.quasicoherentDerivedTensor`.
* `AlgebraicGeometry.Space.quasicoherentDerivedExactPairing`: an exact pairing in `D(𝒪_X)` of
  objects of `D_QCoh(𝒪_X)` is one in `D_QCoh(𝒪_X)`.

## Main results

* `AlgebraicGeometry.Space.quasicoherentDerivedMonoidal_associator_hom_hom` and the two unitor
  analogues: the constraints of `D_QCoh(𝒪_X)` are those of the derived tensor product.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 08F5](https://stacks.math.columbia.edu/tag/08F5)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory CategoryTheory.Pretriangulated.K0

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (X : AlgebraicSpaces B S hS)

/-- The monoidal structure of Stacks 0FPT on `D(𝒪_X)`, with tensor product the derived tensor
product `- ⊗^L_{𝒪_X} -` and unit `𝒪_X` in degree zero. -/
abbrev smallEtaleDerivedMonoidal :
    MonoidalCategory (DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :=
  (smallEtaleDerivedTensorProduct B S hS X).monoidal

/-- The tensor product of `smallEtaleDerivedMonoidal` is the derived tensor product. -/
theorem curriedTensor_smallEtaleDerivedMonoidal :
    @curriedTensor _ _ (smallEtaleDerivedMonoidal X) = smallEtaleDerivedTensor B S hS X :=
  rfl

/-- `D_QCoh(𝒪_X)` is a monoidal subcategory of `D(𝒪_X)`: it contains `𝒪_X` and is closed under
the derived tensor product (Stacks 08F5). -/
theorem qcohDerived_isMonoidal :
    @ObjectProperty.IsMonoidal _ _ (smallEtaleDerivedMonoidal X) (QcohDerived B S hS X) :=
  let := smallEtaleDerivedMonoidal X
  { prop_unit := (derivedStructureSheaf B S hS X.1 X.2).property
    prop_tensor := fun K L hK hL => qcohDerived_smallEtaleDerivedTensor X K L hK hL }

/-- The tensor product of the full monoidal subcategory `D_QCoh(𝒪_X)` is
`quasicoherentDerivedTensor`. -/
def quasicoherentDerivedTensorIso :
    letI := smallEtaleDerivedMonoidal X
    haveI := qcohDerived_isMonoidal X
    curriedTensor (QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) ≅
      quasicoherentDerivedTensor B S hS X :=
  letI := smallEtaleDerivedMonoidal X
  haveI := qcohDerived_isMonoidal X
  NatIso.ofComponents (fun K => NatIso.ofComponents (fun L => Iso.refl _) (fun g => by
      ext; simp [quasicoherentDerivedTensor, liftBifunctor]; rfl)) (fun f => by
      ext L; simp [quasicoherentDerivedTensor, liftBifunctor]; rfl)

/-- **`D_QCoh(𝒪_X)` is monoidal**, with tensor product `quasicoherentDerivedTensor` and unit
`derivedStructureSheaf` on the nose: the full monoidal subcategory of `smallEtaleDerivedMonoidal`
re-seated onto them. -/
@[instance_reducible]
def quasicoherentDerivedMonoidal :
    MonoidalCategory (QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) :=
  letI := smallEtaleDerivedMonoidal X
  haveI := qcohDerived_isMonoidal X
  reseat (quasicoherentDerivedTensorIso X) (U := derivedStructureSheaf B S hS X.1 X.2) (Iso.refl _)

/-- The tensor product of `quasicoherentDerivedMonoidal` is `quasicoherentDerivedTensor`. -/
theorem curriedTensor_quasicoherentDerivedMonoidal :
    @curriedTensor _ _ (quasicoherentDerivedMonoidal X) = quasicoherentDerivedTensor B S hS X :=
  rfl

/-- The unit of `quasicoherentDerivedMonoidal` is `derivedStructureSheaf`. -/
theorem tensorUnit_quasicoherentDerivedMonoidal :
    @MonoidalCategoryStruct.tensorUnit _ _
        (quasicoherentDerivedMonoidal X).toMonoidalCategoryStruct =
      derivedStructureSheaf B S hS X.1 X.2 :=
  rfl

/-- The components of `quasicoherentDerivedTensorIso` are identities. -/
theorem quasicoherentDerivedTensorIso_hom_app_app
    (K L : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) :
    letI := smallEtaleDerivedMonoidal X
    haveI := qcohDerived_isMonoidal X
    ((quasicoherentDerivedTensorIso X).hom.app K).app L = 𝟙 _ :=
  rfl

/-- The components of the inverse of `quasicoherentDerivedTensorIso` are identities. -/
theorem quasicoherentDerivedTensorIso_inv_app_app
    (K L : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) :
    letI := smallEtaleDerivedMonoidal X
    haveI := qcohDerived_isMonoidal X
    ((quasicoherentDerivedTensorIso X).inv.app K).app L = 𝟙 _ :=
  rfl

/-- The associator of `D_QCoh(𝒪_X)` is the associator of the derived tensor product. -/
theorem quasicoherentDerivedMonoidal_associator_hom_hom
    (K L M : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) :
    (@MonoidalCategoryStruct.associator _ _
      (quasicoherentDerivedMonoidal X).toMonoidalCategoryStruct K L M).hom.hom =
      ((smallEtaleDerivedTensorProduct B S hS X).associatorGeneral K.obj L.obj M.obj).hom := by
  let := smallEtaleDerivedMonoidal X
  have := qcohDerived_isMonoidal X
  have h := congrArg (fun g => g.hom) (reseat_associator (quasicoherentDerivedTensorIso X)
    (U := derivedStructureSheaf B S hS X.1 X.2) (Iso.refl _) K L M)
  refine h.trans ?_
  simp only [reseatIso, Iso.app_hom, Iso.app_inv, quasicoherentDerivedTensorIso_hom_app_app,
    quasicoherentDerivedTensorIso_inv_app_app]
  dsimp only [quasicoherentDerivedTensor, liftBifunctor, curriedTensor_obj_obj,
    ObjectProperty.lift_obj_obj, Functor.comp_obj, ObjectProperty.ι_obj]
  simp
  rfl

/-- The left unitor of `D_QCoh(𝒪_X)` is the left unit law of the derived tensor product. -/
theorem quasicoherentDerivedMonoidal_leftUnitor_hom_hom
    (K : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) :
    (@MonoidalCategoryStruct.leftUnitor _ _
      (quasicoherentDerivedMonoidal X).toMonoidalCategoryStruct K).hom.hom =
      ((smallEtaleDerivedTensorProduct B S hS X).leftUnitor.app K.obj).hom := by
  let := smallEtaleDerivedMonoidal X
  have := qcohDerived_isMonoidal X
  have h : (@MonoidalCategoryStruct.leftUnitor _ _
      (quasicoherentDerivedMonoidal X).toMonoidalCategoryStruct K).hom =
      ((reseatIso (quasicoherentDerivedTensorIso X) (derivedStructureSheaf B S hS X.1 X.2) K).inv ≫
        ((Iso.refl (derivedStructureSheaf B S hS X.1 X.2)).inv ⊗ₘ 𝟙 K)) ≫ (λ_ K).hom := by
    rfl
  refine (congrArg (fun g => g.hom) h).trans ?_
  simp only [reseatIso, Iso.app_inv, quasicoherentDerivedTensorIso_inv_app_app, Iso.refl_inv,
    id_tensorHom_id]
  erw [Category.id_comp]
  rfl

/-- The right unitor of `D_QCoh(𝒪_X)` is the right unitor of `smallEtaleDerivedMonoidal`. -/
theorem quasicoherentDerivedMonoidal_rightUnitor_hom_hom
    (K : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) :
    (@MonoidalCategoryStruct.rightUnitor _ _
      (quasicoherentDerivedMonoidal X).toMonoidalCategoryStruct K).hom.hom =
      (@MonoidalCategoryStruct.rightUnitor _ _
        (smallEtaleDerivedMonoidal X).toMonoidalCategoryStruct K.obj).hom := by
  let := smallEtaleDerivedMonoidal X
  have := qcohDerived_isMonoidal X
  have h : (@MonoidalCategoryStruct.rightUnitor _ _
      (quasicoherentDerivedMonoidal X).toMonoidalCategoryStruct K).hom =
      ((reseatIso (quasicoherentDerivedTensorIso X) K (derivedStructureSheaf B S hS X.1 X.2)).inv ≫
        (𝟙 K ⊗ₘ (Iso.refl (derivedStructureSheaf B S hS X.1 X.2)).inv)) ≫ (ρ_ K).hom := by
    rfl
  refine (congrArg (fun g => g.hom) h).trans ?_
  simp only [reseatIso, Iso.app_inv, quasicoherentDerivedTensorIso_inv_app_app, Iso.refl_inv,
    id_tensorHom_id]
  erw [Category.id_comp]
  rfl

/-- **An exact pairing in `D(𝒪_X)` of objects of `D_QCoh(𝒪_X)` is one in `D_QCoh(𝒪_X)`**: the
inclusion is fully faithful and monoidal. -/
@[instance_reducible]
def quasicoherentDerivedExactPairing (K K' : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (p : @ExactPairing _ _ (smallEtaleDerivedMonoidal X) K.obj K'.obj) :
    @ExactPairing _ _ (quasicoherentDerivedMonoidal X) K K' :=
  letI := smallEtaleDerivedMonoidal X
  haveI := qcohDerived_isMonoidal X
  letI p₁ : ExactPairing K K' :=
    @ExactPairing.ofFullyFaithful _ _ _ _ _ _ (QcohDerived B S hS X).ι _ _ _ K K' p
  @ExactPairing.ofFullyFaithful _ _ _ _ (quasicoherentDerivedMonoidal X)
    (ObjectProperty.fullMonoidalSubcategory _) (𝟭 _)
    (reseatMonoidal (quasicoherentDerivedTensorIso X) (U := derivedStructureSheaf B S hS X.1 X.2)
      (Iso.refl _)) _ _ K K' p₁

end AlgebraicGeometry.Space

end
