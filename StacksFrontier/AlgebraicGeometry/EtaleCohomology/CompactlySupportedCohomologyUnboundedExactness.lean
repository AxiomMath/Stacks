module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralCohomologicalDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.BoundedBelowComparison
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution

/-!
# Exactness of the unbounded derived functors entering `Rf_!`

The derived lower shriek `Rf_! = R(fbar)_* ∘ Rj_!` on the unbounded derived category
`D(X_étale, Λ)` is built from total right derived functors along the localization
`DerivedCategory.Q` of cochain complexes. This file records what is needed to move
distinguished triangles through it: such a right derived functor is triangulated, the derived
extension by zero is extension by zero applied degreewise, and the derived direct image along a
composite whose first factor has exact direct image is the composite of that direct image with
the derived direct image along the second factor.

## Main definitions

* `Stacks.Injectives.KInjectiveResolution.homotopyCategoryUnit`: the transformation on the
  homotopy category induced by the unit of a right derived functor along `DerivedCategory.Q`.
* `Stacks.Injectives.KInjectiveResolution.commShiftOfIsRightDerivedFunctor`: the commutation with
  the shift of such a right derived functor.
* `Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroUnboundedIso`: `Rj_! ≅ j_!`.
* `Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnboundedCompIso`:
  `R(a ≫ b)_* ≅ a_* ⋙ Rb_*` when `a_*` is exact.

## Main results

* `Stacks.Injectives.KInjectiveResolution.isTriangulated_of_isRightDerivedFunctor`: a right
  derived functor along `DerivedCategory.Q` out of the derived category of a Grothendieck
  abelian category is triangulated.
* `Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnbounded_isTriangulated`: the unbounded
  derived direct image is triangulated.

## Implementation notes

A right derived functor along `DerivedCategory.Q` is also a right derived functor of the induced
functor on the homotopy category along `DerivedCategory.Qh`: by
`Stacks.Injectives.KInjectiveResolution.isRightDerivedFunctor_of_isIso_app_quotient_isKInjective`
it suffices that the induced unit be invertible at K-injective complexes, where the original unit
is. On the homotopy category, which is triangulated, the criterion
`Stacks.DerivedAcyclic.isTriangulated_of_isRightDerivedFunctor` applies. The commutation with the
shift is the one of the universal property on the homotopy category; it is a definition rather
than a global instance, because Mathlib's instance for total right derived functors along
`DerivedCategory.Q` gives a second one.

For the composite, `a_*` carries K-injective complexes to K-injective complexes because its left
adjoint `a^{-1}` is exact, [Stacks, Tag 08BJ], so the unit of `a_* ⋙ Rb_*` is invertible at
K-injective complexes.

## References

* [Stacks Project, Tag 0F7H](https://stacks.math.columbia.edu/tag/0F7H)
* [Stacks Project, Tag 03S5](https://stacks.math.columbia.edu/tag/03S5)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u r

namespace Stacks.Injectives.KInjectiveResolution

section General

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
  (F : A ⥤ B) [F.Additive] (RF : DerivedCategory A ⥤ DerivedCategory B)
  (α : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ RF)

/-- The transformation `quotient ⋙ (F ⋙ Qh) ⟶ quotient ⋙ (Qh ⋙ RF)` on cochain complexes
from which `homotopyCategoryUnit` is lifted. -/
def homotopyCategoryUnitAux :
    HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙
        (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⟶
      HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙ (DerivedCategory.Qh ⋙ RF) :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom
      DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (DerivedCategory.quotientCompQhIso B).hom ≫ α ≫
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso A).inv RF ≫
    (Functor.associator _ _ _).hom

/-- The component of `homotopyCategoryUnitAux F RF α` at a cochain complex `K`. -/
lemma homotopyCategoryUnitAux_app (K : CochainComplex A ℤ) :
    (homotopyCategoryUnitAux F RF α).app K =
      DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K) ≫
        (DerivedCategory.quotientCompQhIso B).hom.app _ ≫ α.app K ≫
          RF.map ((DerivedCategory.quotientCompQhIso A).inv.app K) := by
  simp [homotopyCategoryUnitAux]

/-- The transformation on the homotopy category induced by a transformation
`α : F ⋙ Q ⟶ Q ⋙ RF` on cochain complexes, through the factorization of `DerivedCategory.Q`
through the homotopy category. -/
def homotopyCategoryUnit :
    F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF :=
  CategoryTheory.Quotient.natTransLift _ (homotopyCategoryUnitAux F RF α)

/-- The component of `homotopyCategoryUnit F RF α` at the image of a cochain complex `K` in the
homotopy category. -/
lemma homotopyCategoryUnit_app_quotient (K : CochainComplex A ℤ) :
    (homotopyCategoryUnit F RF α).app ((HomotopyCategory.quotient _ _).obj K) =
      DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K) ≫
        (DerivedCategory.quotientCompQhIso B).hom.app _ ≫ α.app K ≫
          RF.map ((DerivedCategory.quotientCompQhIso A).inv.app K) :=
  homotopyCategoryUnitAux_app F RF α K

/-- If `α.app K` is an isomorphism, then so is the component of `homotopyCategoryUnit F RF α` at
the image of `K` in the homotopy category. -/
lemma isIso_homotopyCategoryUnit_app_quotient (K : CochainComplex A ℤ) [IsIso (α.app K)] :
    IsIso ((homotopyCategoryUnit F RF α).app ((HomotopyCategory.quotient _ _).obj K)) := by
  rw [homotopyCategoryUnit_app_quotient]
  infer_instance

variable [IsGrothendieckAbelian.{w} A]
  [RF.IsRightDerivedFunctor α (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))]

/-- A right derived functor of `F` along `DerivedCategory.Q` is a right derived functor of the
induced functor on the homotopy category along `DerivedCategory.Qh`. -/
instance isRightDerivedFunctor_homotopyCategoryUnit :
    RF.IsRightDerivedFunctor (homotopyCategoryUnit F RF α)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_of_isIso_app_quotient_isKInjective
    (Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian A) _ RF _
    fun I hI => by
      have := isIso_app_of_isKInjective DerivedCategory.Q RF α
        (invertsQuasiIso_mapHomologicalComplex_comp_Q F) I hI
      exact isIso_homotopyCategoryUnit_app_quotient F RF α I

/-- The commutation with the shift of a right derived functor on the unbounded derived category,
obtained from its universal property on the homotopy category. -/
@[instance_reducible]
def commShiftOfIsRightDerivedFunctor : RF.CommShift ℤ :=
  Functor.IsRightDerivedFunctor.commShift RF (homotopyCategoryUnit F RF α)
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ℤ

/-- A right derived functor on the unbounded derived category of a Grothendieck abelian category
is triangulated, for the commutation with the shift given by its universal property. -/
theorem isTriangulated_of_isRightDerivedFunctor :
    letI := commShiftOfIsRightDerivedFunctor F RF α
    RF.IsTriangulated :=
  Stacks.DerivedAcyclic.isTriangulated_of_isRightDerivedFunctor F RF (homotopyCategoryUnit F RF α)

end General

section Exact

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The functor induced on unbounded derived categories by an exact functor is a right derived
functor of `F` along `DerivedCategory.Q`. -/
instance isRightDerivedFunctor_mapDerivedCategory_Q :
    F.mapDerivedCategory.IsRightDerivedFunctor F.mapDerivedCategoryFactors.inv
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts _ _ F.mapDerivedCategoryFactors

/-- A right derived functor of an exact functor along `DerivedCategory.Q` is the functor it
induces on unbounded derived categories. -/
def isoMapDerivedCategoryOfIsRightDerivedFunctor (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))] :
    RF ≅ F.mapDerivedCategory :=
  Functor.rightDerivedUnique RF F.mapDerivedCategory α F.mapDerivedCategoryFactors.inv
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))

end Exact

end Stacks.Injectives.KInjectiveResolution

namespace Stacks.EtaleCohomology

open AlgebraicGeometry Stacks.Injectives.KInjectiveResolution

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type r) [Ring Λ]

/-! ### Extension by zero -/

/-- The unbounded derived extension by zero `Rj_!` is extension by zero applied degreewise,
extension by zero being exact, [Stacks, Tag 03S5]. -/
def etaleModuleDerivedExtensionByZeroUnboundedIso {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j ≅
      (etaleModuleExtensionByZero.{u, r} Λ j).mapDerivedCategory :=
  isoMapDerivedCategoryOfIsRightDerivedFunctor _ _
    (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, r} Λ j)

/-! ### The derived direct image is triangulated -/

/-- The commutation with the shift of the unbounded derived direct image `Rf_*`, given by its
universal property. -/
@[instance_reducible]
def etaleModuleDerivedDirectImageUnboundedCommShift {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f).CommShift ℤ :=
  commShiftOfIsRightDerivedFunctor (etaleModuleDirectImage.{u, r} Λ f) _
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f)

/-- The unbounded derived direct image `Rf_*` is a triangulated functor. -/
theorem etaleModuleDerivedDirectImageUnbounded_isTriangulated {X Y : Scheme.{u}} (f : X ⟶ Y) :
    letI := etaleModuleDerivedDirectImageUnboundedCommShift.{u, r} Λ f
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f).IsTriangulated :=
  isTriangulated_of_isRightDerivedFunctor (etaleModuleDirectImage.{u, r} Λ f) _
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f)

/-! ### Direct image along a composite with an exact first factor -/

/-- Direct image of sheaves of modules along an integral morphism preserves finite colimits: it
is exact, by `Stacks.EtaleCohomology.etaleModuleDirectImage_exact_of_isIntegralHom`. -/
instance etaleModuleDirectImage_preservesFiniteColimits_of_isIntegralHom {X Y : Scheme.{u}}
    (a : X ⟶ Y) [IsIntegralHom a] :
    PreservesFiniteColimits (etaleModuleDirectImage.{u, r} Λ a) :=
  ((exactFunctor_iff _).mp (etaleModuleDirectImage_exact_of_isIntegralHom Λ a)).2

section Comp

variable {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
  [PreservesFiniteColimits (etaleModuleDirectImage.{u, r} Λ a)]

/-- The comparison `(a ≫ b)_* ⋙ Q ⟶ Q ⋙ a_* ⋙ Rb_*` making `a_* ⋙ Rb_*` a derived direct image
along `a ≫ b`. -/
def etaleModuleDerivedDirectImageUnboundedCompUnit :
    (etaleModuleDirectImage.{u, r} Λ (a ≫ b)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ ((etaleModuleDirectImage.{u, r} Λ a).mapDerivedCategory ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, r} Λ b) :=
  Functor.whiskerRight (Functor.mapHomologicalComplexCompIso
      (etaleModuleDirectImageComp.{u, r} Λ a b (a ≫ b) rfl) (ComplexShape.up ℤ)).inv
      DerivedCategory.Q ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ b) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (etaleModuleDirectImage.{u, r} Λ a).mapDerivedCategoryFactors.inv _ ≫
    (Functor.associator _ _ _).hom

/-- `a_* ⋙ Rb_*` is a right derived functor of the direct image along `a ≫ b`. -/
instance etaleModuleDerivedDirectImageUnboundedComp_isRightDerivedFunctor :
    ((etaleModuleDirectImage.{u, r} Λ a).mapDerivedCategory ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, r} Λ b).IsRightDerivedFunctor
      (etaleModuleDerivedDirectImageUnboundedCompUnit.{u, r} Λ a b)
      (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ)) := by
  have := etaleModuleInverseImage_preservesFiniteLimits.{u, r} Λ a
  have := etaleModuleInverseImage_preservesFiniteColimits.{u, r} Λ a
  rw [isRightDerivedFunctor_iff_isIso_app_of_isKInjective DerivedCategory.Q _ _
    (invertsQuasiIso_mapHomologicalComplex_comp_Q _)]
  intro I hI
  have : CochainComplex.IsKInjective
      (((etaleModuleDirectImage.{u, r} Λ a).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    CochainComplex.isKInjective_mapHomologicalComplex_of_exact _ _
      (etaleModuleInverseImageAdj.{u, r} Λ a) I
  have := isIso_etaleModuleDerivedDirectImageUnboundedUnit_app.{u, r} Λ b _ this
  simp only [etaleModuleDerivedDirectImageUnboundedCompUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  infer_instance

/-- The unbounded derived direct image along `a ≫ b` when the direct image along `a` is exact:
`R(a ≫ b)_* ≅ a_* ⋙ Rb_*`. -/
def etaleModuleDerivedDirectImageUnboundedCompIso :
    etaleModuleDerivedDirectImageUnbounded.{u, r} Λ (a ≫ b) ≅
      (etaleModuleDirectImage.{u, r} Λ a).mapDerivedCategory ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, r} Λ b :=
  Functor.rightDerivedUnique _ _ (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ (a ≫ b))
    (etaleModuleDerivedDirectImageUnboundedCompUnit.{u, r} Λ a b)
    (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ))

end Comp

end Stacks.EtaleCohomology
