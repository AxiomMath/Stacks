module

public import StacksFrontier.AlgebraicGeometry.DeRham.BoxKunnethFlat.Relative
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyBoundedInvertibility
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated

/-!
# Dévissage of the relative box map

The relative map `Stacks.Cohomology.BoxKunnethFlat.relativeBoxMap` of two complexes of
differential operators is natural in each variable, and in each variable both its source and its
target are exact functors of the homotopy category: the source is `Ra_*` (respectively `Rb_*`)
followed by the derived tensor product with a fixed object, the target is the total complex of
the box product with a fixed complex, followed by `Rf_*`.  So, by
`Stacks.CategoryTheory.HomotopyBoundedInvertibility.isIso_app_quotient_of_finite`, the relative
map is invertible at a pair of bounded complexes as soon as it is invertible at every pair of
complexes concentrated in a single degree.  This is the dévissage of the proof of
[Stacks, Tag 0FLT].

## Main results

* `Stacks.Cohomology.BoxKunnethFlat.isIso_relativeBoxMap_of_finite`: the reduction to single
  complexes.

## References

* [Stacks Project, Tag 0FLT](https://stacks.math.columbia.edu/tag/0FLT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DeRhamDirectImage
open Stacks.DerivedTensor.RingedSite
open AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory
open Stacks.Cohomology.BoxKunneth
open Stacks.SheafOfModules.Tensor.Reduction
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.BoxKunnethFlat

attribute [local instance 2000] HasDerivedCategory.standard

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- Modules on an inverse-image ringed space have binary biproducts, at this spelling. -/
local instance hasBinaryBiproducts_modules_inverseImageBase {Z : Scheme.{u}} (g : Z ⟶ S) :
    HasBinaryBiproducts (Modules (inverseImageBase g)) :=
  @hasBinaryBiproducts_of_finite_biproducts _ _ _ (HasFiniteBiproducts.of_hasFiniteProducts)

/-- Modules on an inverse-image ringed space have a zero object, at this spelling. -/
local instance hasZeroObject_modules_inverseImageBase {Z : Scheme.{u}} (g : Z ⟶ S) :
    HasZeroObject (Modules (inverseImageBase g)) :=
  inferInstance

/-- The category of finite-order differential operators has a zero object. -/
instance hasZeroObject_finiteOrder : HasZeroObject (FiniteOrderDifferentialOperatorCategory a) :=
  hasZeroObject_of_hasFiniteBiproducts _

/-- The total complexes of the box-product double complexes exist, for all pairs of complexes at
once, which is the form the descended functors of the homotopy categories ask for. -/
instance hasMapBifunctor_boxProductRelativeCurried :
    ∀ (K₁ : HomologicalComplex (FiniteOrderDifferentialOperatorCategory a) (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex (FiniteOrderDifferentialOperatorCategory b) (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ (boxProductRelativeCurried a b) (ComplexShape.up ℤ) :=
  fun _ _ => inferInstance


/-! ### The first variable -/

/-- The derived direct image along the projection of an inverse-image ringed space is exact. -/
private theorem derivedPushforward_isTriangulated {Z : Scheme.{u}} (g : Z ⟶ S) :
    letI : (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection g)).CommShift ℤ :=
      (derivedAdjunction (inverseImageBaseProjection g)).rightAdjointCommShift ℤ
    (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection g)).IsTriangulated := by
  let : (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection g)).CommShift ℤ :=
    (derivedAdjunction (inverseImageBaseProjection g)).rightAdjointCommShift ℤ
  let : (derivedAdjunction (inverseImageBaseProjection g)).CommShift ℤ :=
    (derivedAdjunction (inverseImageBaseProjection g)).commShift_of_leftAdjoint ℤ
  exact (derivedAdjunction (inverseImageBaseProjection g)).isTriangulated_rightAdjoint

section Left

variable (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ)

/-- The source of the relative map, as a functor of the complex on `X`. -/
abbrev sourceLeft :
    HomotopyCategory (FiniteOrderDifferentialOperatorCategory a) (ComplexShape.up ℤ) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) :=
  (toInverseImageModules a).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⋙
    derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a) ⋙
      (derivedTensorProductFunctor.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)).flip.obj
        ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).obj
          (DerivedCategory.Q.obj (rightComplex b L)))

/-- The target of the relative map, as a functor of the complex on `X`. -/
abbrev targetLeft :
    HomotopyCategory (FiniteOrderDifferentialOperatorCategory a) (ComplexShape.up ℤ) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) :=
  bifunctorPhiR (boxProductRelativeCurried a b) L ⋙ DerivedCategory.Qh ⋙
    derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection (pullback.fst a b ≫ a))

/-- The source functor in the first variable commutes with the shift. -/
@[instance_reducible]
def sourceLeftCommShift : (sourceLeft a b L).CommShift ℤ :=
  letI : (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a)).CommShift ℤ :=
    (derivedAdjunction (inverseImageBaseProjection a)).rightAdjointCommShift ℤ
  letI : ((derivedTensorProductFunctor.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)).flip.obj
      ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).obj
        (DerivedCategory.Q.obj (rightComplex b L)))).CommShift ℤ :=
    (canonicalDerivedTensorProduct (SheafedSpace.sheaf S.toRingedSpace)).commShift_left _
  letI : (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a) ⋙
      (derivedTensorProductFunctor.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)).flip.obj
        ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).obj
          (DerivedCategory.Q.obj (rightComplex b L)))).CommShift ℤ :=
    Functor.CommShift.comp _ _
  letI : (DerivedCategory.Qh ⋙
      derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a) ⋙
      (derivedTensorProductFunctor.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)).flip.obj
        ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).obj
          (DerivedCategory.Q.obj (rightComplex b L)))).CommShift ℤ :=
    Functor.CommShift.comp _ _
  Functor.CommShift.comp _ _

/-- The source functor in the first variable is exact. -/
theorem sourceLeft_isTriangulated :
    letI := sourceLeftCommShift a b L
    (sourceLeft a b L).IsTriangulated := by
  let : (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a)).CommShift ℤ :=
    (derivedAdjunction (inverseImageBaseProjection a)).rightAdjointCommShift ℤ
  have := derivedPushforward_isTriangulated a
  let : ((derivedTensorProductFunctor.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)).flip.obj
      ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).obj
        (DerivedCategory.Q.obj (rightComplex b L)))).CommShift ℤ :=
    (canonicalDerivedTensorProduct (SheafedSpace.sheaf S.toRingedSpace)).commShift_left _
  have : ((derivedTensorProductFunctor.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)).flip.obj
      ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).obj
        (DerivedCategory.Q.obj (rightComplex b L)))).IsTriangulated :=
    (canonicalDerivedTensorProduct (SheafedSpace.sheaf S.toRingedSpace)).exact_left _
  let : (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a) ⋙
      (derivedTensorProductFunctor.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)).flip.obj
        ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).obj
          (DerivedCategory.Q.obj (rightComplex b L)))).CommShift ℤ :=
    Functor.CommShift.comp _ _
  let : (DerivedCategory.Qh ⋙
      derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a) ⋙
      (derivedTensorProductFunctor.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)).flip.obj
        ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).obj
          (DerivedCategory.Q.obj (rightComplex b L)))).CommShift ℤ :=
    Functor.CommShift.comp _ _
  exact inferInstance

/-- The target functor in the first variable commutes with the shift. -/
@[instance_reducible]
def targetLeftCommShift : (targetLeft a b L).CommShift ℤ :=
  letI := bifunctorXiR (boxProductRelativeCurried a b) L
  letI : (derivedPushforward.{u, u + 1, u + 1}
      (inverseImageBaseProjection (pullback.fst a b ≫ a))).CommShift ℤ :=
    (derivedAdjunction (inverseImageBaseProjection (pullback.fst a b ≫ a))).rightAdjointCommShift ℤ
  letI : (DerivedCategory.Qh ⋙ derivedPushforward.{u, u + 1, u + 1}
      (inverseImageBaseProjection (pullback.fst a b ≫ a))).CommShift ℤ :=
    Functor.CommShift.comp _ _
  Functor.CommShift.comp _ _

/-- The target functor in the first variable is exact. -/
theorem targetLeft_isTriangulated :
    letI := targetLeftCommShift a b L
    (targetLeft a b L).IsTriangulated := by
  let := bifunctorXiR (boxProductRelativeCurried a b) L
  have := bifunctorPhiR_isTriangulated (boxProductRelativeCurried a b) L
  let : (derivedPushforward.{u, u + 1, u + 1}
      (inverseImageBaseProjection (pullback.fst a b ≫ a))).CommShift ℤ :=
    (derivedAdjunction (inverseImageBaseProjection (pullback.fst a b ≫ a))).rightAdjointCommShift ℤ
  have := derivedPushforward_isTriangulated (pullback.fst a b ≫ a)
  let : (DerivedCategory.Qh ⋙ derivedPushforward.{u, u + 1, u + 1}
      (inverseImageBaseProjection (pullback.fst a b ≫ a))).CommShift ℤ :=
    Functor.CommShift.comp _ _
  exact inferInstance

/-- The source of the relative map, as a functor of complexes on `X`. -/
abbrev sourceLeftComplex :
    CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) :=
  (toInverseImageModules a).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⋙
    derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a) ⋙
      (derivedTensorProductFunctor.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)).flip.obj
        ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).obj
          (DerivedCategory.Q.obj (rightComplex b L)))

/-- The target of the relative map, as a functor of complexes on `X`. -/
abbrev targetLeftComplex :
    CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) :=
  ((boxProductRelativeCurried a b).map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)).flip.obj L ⋙ DerivedCategory.Q ⋙
    derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection (pullback.fst a b ≫ a))

/-- **The relative map as a natural transformation of complexes on `X`.** -/
def relativeBoxMapLeftComplex : sourceLeftComplex a b L ⟶ targetLeftComplex a b L where
  app K := relativeBoxMap a b K L
  naturality _ _ φ := relativeBoxMap_natural_left a b φ L

/-- The source functor in the first variable, read on complexes. -/
def sourceLeftIso :
    HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙ sourceLeft a b L ≅
      sourceLeftComplex a b L :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((toInverseImageModules a).mapHomotopyCategoryFactors (ComplexShape.up ℤ)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso _) _)

/-- The target functor in the first variable, read on complexes. -/
def targetLeftIso :
    HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙ targetLeft a b L ≅
      targetLeftComplex a b L :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (bifunctorPhiRFactors (boxProductRelativeCurried a b) L) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso _) _)

/-- **The relative map as a natural transformation in the first variable.** -/
def relativeBoxMapLeft : sourceLeft a b L ⟶ targetLeft a b L :=
  CategoryTheory.Quotient.natTransLift _
    ((sourceLeftIso a b L).hom ≫ relativeBoxMapLeftComplex a b L ≫ (targetLeftIso a b L).inv)

/-- Composing with isomorphisms on both sides does not change invertibility. -/
private theorem isIso_comp_three_iff {E : Type*} [Category E] {w x y z : E}
    (e : w ≅ x) (f : x ⟶ y) (g : y ≅ z) :
    IsIso (e.hom ≫ f ≫ g.hom) ↔ IsIso f := by
  rw [isIso_comp_left_iff, isIso_comp_right_iff]

/-- The relative map in the first variable is invertible at the class of `K` exactly when the
relative map at `K` is. -/
theorem isIso_relativeBoxMapLeft_app_iff
    (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ) :
    IsIso ((relativeBoxMapLeft a b L).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
      ↔ IsIso (relativeBoxMap a b K L) :=
  (isIso_comp_three_iff ((sourceLeftIso a b L).app K) ((relativeBoxMapLeftComplex a b L).app K)
    ((targetLeftIso a b L).app K).symm)

/-- **Dévissage in the first variable.** -/
theorem isIso_relativeBoxMap_of_finite_left (P : FiniteOrderDifferentialOperatorCategory a → Prop)
    (hsingle : ∀ (i : ℤ) (E : FiniteOrderDifferentialOperatorCategory a), P E →
      IsIso (relativeBoxMap a b ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj E) L))
    (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ) (hP : ∀ n, P (K.X n))
    (hK : {i : ℤ | ¬ IsZero (K.X i)}.Finite) :
    IsIso (relativeBoxMap a b K L) := by
  let := sourceLeftCommShift a b L
  let := targetLeftCommShift a b L
  have := sourceLeft_isTriangulated a b L
  have := targetLeft_isTriangulated a b L
  rw [← isIso_relativeBoxMapLeft_app_iff]
  exact Stacks.CategoryTheory.HomotopyBoundedInvertibility.isIso_app_quotient_of_finite
    (sourceLeft a b L) (targetLeft a b L) (relativeBoxMapLeft a b L) P
    (fun i E hE => (isIso_relativeBoxMapLeft_app_iff a b L _).2 (hsingle i E hE)) K hP hK

end Left

/-! ### The second variable -/

section Right

variable (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)

/-- The source of the relative map, as a functor of the complex on `Y`. -/
abbrev sourceRight :
    HomotopyCategory (FiniteOrderDifferentialOperatorCategory b) (ComplexShape.up ℤ) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) :=
  (toInverseImageModules b).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⋙
    derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b) ⋙
      (derivedTensorProductFunctor.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)).obj
        ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a)).obj
          (DerivedCategory.Q.obj (leftComplex a K)))

/-- The target of the relative map, as a functor of the complex on `Y`. -/
abbrev targetRight :
    HomotopyCategory (FiniteOrderDifferentialOperatorCategory b) (ComplexShape.up ℤ) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) :=
  bifunctorPhi (boxProductRelativeCurried a b) K ⋙ DerivedCategory.Qh ⋙
    derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection (pullback.fst a b ≫ a))

/-- The source functor in the second variable commutes with the shift. -/
@[instance_reducible]
def sourceRightCommShift : (sourceRight a b K).CommShift ℤ :=
  letI : (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).CommShift ℤ :=
    (derivedAdjunction (inverseImageBaseProjection b)).rightAdjointCommShift ℤ
  letI : ((derivedTensorProductFunctor.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)).obj
      ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a)).obj
        (DerivedCategory.Q.obj (leftComplex a K)))).CommShift ℤ :=
    (canonicalDerivedTensorProduct (SheafedSpace.sheaf S.toRingedSpace)).commShift_right _
  letI : (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b) ⋙
      (derivedTensorProductFunctor.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)).obj
        ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a)).obj
          (DerivedCategory.Q.obj (leftComplex a K)))).CommShift ℤ :=
    Functor.CommShift.comp _ _
  letI : (DerivedCategory.Qh ⋙
      derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b) ⋙
      (derivedTensorProductFunctor.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)).obj
        ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a)).obj
          (DerivedCategory.Q.obj (leftComplex a K)))).CommShift ℤ :=
    Functor.CommShift.comp _ _
  Functor.CommShift.comp _ _

/-- The source functor in the second variable is exact. -/
theorem sourceRight_isTriangulated :
    letI := sourceRightCommShift a b K
    (sourceRight a b K).IsTriangulated := by
  let : (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).CommShift ℤ :=
    (derivedAdjunction (inverseImageBaseProjection b)).rightAdjointCommShift ℤ
  have := derivedPushforward_isTriangulated b
  let : ((derivedTensorProductFunctor.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)).obj
      ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a)).obj
        (DerivedCategory.Q.obj (leftComplex a K)))).CommShift ℤ :=
    (canonicalDerivedTensorProduct (SheafedSpace.sheaf S.toRingedSpace)).commShift_right _
  have : ((derivedTensorProductFunctor.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)).obj
      ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a)).obj
        (DerivedCategory.Q.obj (leftComplex a K)))).IsTriangulated :=
    (canonicalDerivedTensorProduct (SheafedSpace.sheaf S.toRingedSpace)).exact_right _
  let : (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b) ⋙
      (derivedTensorProductFunctor.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)).obj
        ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a)).obj
          (DerivedCategory.Q.obj (leftComplex a K)))).CommShift ℤ :=
    Functor.CommShift.comp _ _
  let : (DerivedCategory.Qh ⋙
      derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b) ⋙
      (derivedTensorProductFunctor.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)).obj
        ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a)).obj
          (DerivedCategory.Q.obj (leftComplex a K)))).CommShift ℤ :=
    Functor.CommShift.comp _ _
  exact inferInstance

/-- The target functor in the second variable commutes with the shift. -/
@[instance_reducible]
def targetRightCommShift : (targetRight a b K).CommShift ℤ :=
  letI := bifunctorXi (boxProductRelativeCurried a b) K
  letI : (derivedPushforward.{u, u + 1, u + 1}
      (inverseImageBaseProjection (pullback.fst a b ≫ a))).CommShift ℤ :=
    (derivedAdjunction (inverseImageBaseProjection (pullback.fst a b ≫ a))).rightAdjointCommShift ℤ
  letI : (DerivedCategory.Qh ⋙ derivedPushforward.{u, u + 1, u + 1}
      (inverseImageBaseProjection (pullback.fst a b ≫ a))).CommShift ℤ :=
    Functor.CommShift.comp _ _
  Functor.CommShift.comp _ _

/-- The target functor in the second variable is exact. -/
theorem targetRight_isTriangulated :
    letI := targetRightCommShift a b K
    (targetRight a b K).IsTriangulated := by
  let := bifunctorXi (boxProductRelativeCurried a b) K
  have := bifunctorPhi_isTriangulated (boxProductRelativeCurried a b) K
  let : (derivedPushforward.{u, u + 1, u + 1}
      (inverseImageBaseProjection (pullback.fst a b ≫ a))).CommShift ℤ :=
    (derivedAdjunction (inverseImageBaseProjection (pullback.fst a b ≫ a))).rightAdjointCommShift ℤ
  have := derivedPushforward_isTriangulated (pullback.fst a b ≫ a)
  let : (DerivedCategory.Qh ⋙ derivedPushforward.{u, u + 1, u + 1}
      (inverseImageBaseProjection (pullback.fst a b ≫ a))).CommShift ℤ :=
    Functor.CommShift.comp _ _
  exact inferInstance

/-- The source of the relative map, as a functor of complexes on `Y`. -/
abbrev sourceRightComplex :
    CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) :=
  (toInverseImageModules b).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⋙
    derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b) ⋙
      (derivedTensorProductFunctor.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)).obj
        ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a)).obj
          (DerivedCategory.Q.obj (leftComplex a K)))

/-- The target of the relative map, as a functor of complexes on `Y`. -/
abbrev targetRightComplex :
    CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) :=
  ((boxProductRelativeCurried a b).map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)).obj K ⋙ DerivedCategory.Q ⋙
    derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection (pullback.fst a b ≫ a))

/-- **The relative map as a natural transformation of complexes on `Y`.** -/
def relativeBoxMapRightComplex : sourceRightComplex a b K ⟶ targetRightComplex a b K where
  app L := relativeBoxMap a b K L
  naturality _ _ ψ := relativeBoxMap_natural_right a b K ψ

/-- The source functor in the second variable, read on complexes. -/
def sourceRightIso :
    HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙ sourceRight a b K ≅
      sourceRightComplex a b K :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((toInverseImageModules b).mapHomotopyCategoryFactors (ComplexShape.up ℤ)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso _) _)

/-- The target functor in the second variable, read on complexes. -/
def targetRightIso :
    HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙ targetRight a b K ≅
      targetRightComplex a b K :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (bifunctorPhiFactors (boxProductRelativeCurried a b) K) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso _) _)

/-- **The relative map as a natural transformation in the second variable.** -/
def relativeBoxMapRight : sourceRight a b K ⟶ targetRight a b K :=
  CategoryTheory.Quotient.natTransLift _
    ((sourceRightIso a b K).hom ≫ relativeBoxMapRightComplex a b K ≫ (targetRightIso a b K).inv)

/-- The relative map in the second variable is invertible at the class of `L` exactly when the
relative map at `L` is. -/
theorem isIso_relativeBoxMapRight_app_iff
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ) :
    IsIso ((relativeBoxMapRight a b K).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L)) ↔
      IsIso (relativeBoxMap a b K L) :=
  (isIso_comp_three_iff ((sourceRightIso a b K).app L) ((relativeBoxMapRightComplex a b K).app L)
    ((targetRightIso a b K).app L).symm)

/-- **Dévissage in the second variable.** -/
theorem isIso_relativeBoxMap_of_finite_right (Q : FiniteOrderDifferentialOperatorCategory b → Prop)
    (hsingle : ∀ (j : ℤ) (G : FiniteOrderDifferentialOperatorCategory b), Q G →
      IsIso (relativeBoxMap a b K ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G)))
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ) (hQ : ∀ n, Q (L.X n))
    (hL : {j : ℤ | ¬ IsZero (L.X j)}.Finite) :
    IsIso (relativeBoxMap a b K L) := by
  let := sourceRightCommShift a b K
  let := targetRightCommShift a b K
  have := sourceRight_isTriangulated a b K
  have := targetRight_isTriangulated a b K
  rw [← isIso_relativeBoxMapRight_app_iff]
  exact Stacks.CategoryTheory.HomotopyBoundedInvertibility.isIso_app_quotient_of_finite
    (sourceRight a b K) (targetRight a b K) (relativeBoxMapRight a b K) Q
    (fun j G hG => (isIso_relativeBoxMapRight_app_iff a b K _).2 (hsingle j G hG)) L hQ hL

end Right

/-- **Dévissage of the relative map to single complexes.**  If the relative map is invertible
at every pair of complexes concentrated in a single degree on objects with properties `P` and
`Q`, it is invertible at every pair of complexes with finitely many nonzero terms, all with `P`,
respectively `Q`. -/
theorem isIso_relativeBoxMap_of_finite (P : FiniteOrderDifferentialOperatorCategory a → Prop)
    (Q : FiniteOrderDifferentialOperatorCategory b → Prop)
    (hsingle : ∀ (i j : ℤ) (F : FiniteOrderDifferentialOperatorCategory a)
      (G : FiniteOrderDifferentialOperatorCategory b), P F → Q G →
      IsIso (relativeBoxMap a b ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F)
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G)))
    (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ) (hP : ∀ n, P (K.X n))
    (hK : {i : ℤ | ¬ IsZero (K.X i)}.Finite)
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ) (hQ : ∀ n, Q (L.X n))
    (hL : {j : ℤ | ¬ IsZero (L.X j)}.Finite) :
    IsIso (relativeBoxMap a b K L) :=
  isIso_relativeBoxMap_of_finite_left a b L P
    (fun i F hF => isIso_relativeBoxMap_of_finite_right a b _ Q
      (fun j G hG => hsingle i j F G hF hG) L hQ hL) K hP hK

end Stacks.Cohomology.BoxKunnethFlat

end
