module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift
public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedTriangulated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedFunctorCriterion
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomFunctor
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomOrthogonal
public import StacksFrontier.Algebra.DifferentialGraded.Module.DistinguishedTriangle
public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHomExact
public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHomShiftFunctor
public import StacksFrontier.Algebra.DifferentialGraded.Module.Pretriangulated
public import StacksFrontier.Algebra.DifferentialGraded.Module.PropertyIResolutionExists
public import StacksFrontier.CategoryTheory.Localization.LiftNatTransCommShift
public import StacksFrontier.CategoryTheory.Shift.QuotientNatTransCommShift

/-! # The internal hom functor commutes with the shift, is exact, and so is derived hom

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R` and let `N`
be a differential graded `(A, B)`-bimodule. Tag 0FQR gives a sign-free comparison
`Hom^•_B(N, P)[k] ≅ Hom^•_B(N, P[k])`, natural in `P`
(`DifferentialGradedModule.homModuleFunctorShiftIso`). This file upgrades that family of
isomorphisms to a `CategoryTheory.Functor.CommShift` structure — the two coherences with the
zero shift and with a sum of shifts — on the internal hom functor of Tag 0FQQ, both on
differential graded modules and on the homotopy categories, and then proves the two exactness
statements that the commutation makes meaningful:

* Tag 09LH, that `Hom^•_B(N, -) : K(B, d) ⥤ K(A, d)` is exact;
* that `R Hom(N, -) : D(B, d) ⥤ D(A, d)` of Tag 09LI is exact.

## Main definitions

* `DifferentialGradedModule.homHomotopyLift`: internal hom on the homotopy categories, presented
  as the descent of the functor on differential graded modules.

## Main results

* `DifferentialGradedModule.homModuleFunctorCommShift` and
  `DifferentialGradedModule.homHomotopyCategoryFunctorCommShift`: the internal hom functor
  commutes with the shift, with the comparisons of Tag 0FQR.
* `DifferentialGradedModule.homHomotopyDescent_commShift`: the descent isomorphism of Tag 0FQQ
  is compatible with those commutations.
* `DifferentialGradedModule.homPostcomp_connectingHom`: the connecting homomorphism of the image
  of an admissible short exact sequence is the image of the connecting homomorphism, read
  through the comparison of Tag 0FQR.
* `DifferentialGradedModule.homHomotopyCategoryFunctor_isTriangulated`: **Stacks 09LH**.
* `DifferentialGradedModule.derivedHomComparisonCommShift`: the comparison of Tag 09LI commutes
  with the shift.
* `DifferentialGradedModule.derivedHomFunctor_isTriangulated`: `R Hom(N, -)` is exact.

## Implementation notes

*Why the coherences are cheap.* The comparison of Tag 0FQR is not given by a formula but
characterized: `DifferentialGradedModule.HomModuleData.IsShiftComparison` says that corresponding
elements have homogeneous maps taking the same values, and
`DifferentialGradedModule.HomModuleData.shiftComparison_unique` says at most one homomorphism has
that property. Each coherence is therefore proved by checking that the composite of structural
identifications built from `CategoryTheory.Functor.CommShift.isoZero` and
`CategoryTheory.Functor.CommShift.isoAdd` has the characterizing property; all the structural
maps are the identity on underlying modules, so this is a computation with degrees only.

*Why the homotopy category goes through a lift.* The functor
`DifferentialGradedModule.homHomotopyCategoryFunctor`
is not defined as a `CategoryTheory.Quotient.lift`, so Mathlib's
`CategoryTheory.Quotient.liftCommShift` does not apply to it directly. It is isomorphic to the
lift of internal hom followed by the passage to homotopy classes, by Tag 0FQQ's
`DifferentialGradedModule.homHomotopyDescent`, and `CategoryTheory.Functor.CommShift.ofIso`
transports the structure along that isomorphism;
`CategoryTheory.Functor.CommShift.ofIso_compatibility`
is what makes the descent isomorphism itself compatible with the shift, which is what a consumer
comparing transformations on the two levels needs.

*Exactness.* The proof of Tag 09LH is the one of Tag 09LR for the tensor functor: every
distinguished triangle of `K(B, d)` is isomorphic to the triangle of an admissible short exact
sequence, the internal hom functor carries such a sequence to one of the same kind
(`DifferentialGradedModule.isAdmissibleShortExact_homPostcomp`, Tag 0FQF), and the connecting
homomorphism of the image is the image of the connecting homomorphism. The last point is the only
one that needs an argument and it is `DifferentialGradedModule.homPostcomp_connectingHom`.
Exactness of `R Hom(N, -)` is then Mathlib's
`CategoryTheory.Functor.isTriangulated_of_leftExtension`, whose resolution hypothesis is supplied
by the property (I) resolutions of Tag 09KU together with Tag 0BYW's invertibility of the
comparison at a module orthogonal on the right to the acyclic ones.

## References

* [Stacks Project, Tag 0FQR](https://stacks.math.columbia.edu/tag/0FQR)
* [Stacks Project, Tag 0FQQ](https://stacks.math.columbia.edu/tag/0FQQ)
* [Stacks Project, Tag 09LH](https://stacks.math.columbia.edu/tag/09LH)
* [Stacks Project, Tag 09LI](https://stacks.math.columbia.edu/tag/09LI)
* [Stacks Project, Tag 0FQF](https://stacks.math.columbia.edu/tag/0FQF)
* [Stacks Project, Tag 0BYW](https://stacks.math.columbia.edu/tag/0BYW)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

universe u

namespace DifferentialGradedModule

section ShiftHelpers

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, u} R}

-- Transport of membership along an equality of degrees is
-- `DifferentialGradedModule.mem_grading_congr`, StacksFrontier/Algebra/DGA/Abelian.lean:188.

/-- The comparison with the zero shift is the identity on underlying modules. -/
theorem shiftFunctorZero_hom_toFun' (M : DifferentialGradedModule.{u, u, u} A) (x : M.M) :
    ((shiftFunctorZero (DifferentialGradedModule A) ℤ).hom.app M).toFun x = x := by
  rw [ShiftMkCore.shiftFunctorZero_eq]
  rfl

/-- The inverse comparison with the zero shift is the identity on underlying modules. -/
theorem shiftFunctorZero_inv_toFun' (M : DifferentialGradedModule.{u, u, u} A) (x : M.M) :
    ((shiftFunctorZero (DifferentialGradedModule A) ℤ).inv.app M).toFun x = x := by
  rw [ShiftMkCore.shiftFunctorZero_eq]
  rfl

/-- The comparison of a sum of shifts is the identity on underlying modules. -/
theorem shiftFunctorAdd_hom_toFun' (M : DifferentialGradedModule.{u, u, u} A) (a b : ℤ)
    (x : M.M) :
    ((shiftFunctorAdd (DifferentialGradedModule A) a b).hom.app M).toFun x = x := by
  rw [ShiftMkCore.shiftFunctorAdd_eq]
  rfl

/-- The inverse comparison of a sum of shifts is the identity on underlying modules. -/
theorem shiftFunctorAdd_inv_toFun' (M : DifferentialGradedModule.{u, u, u} A) (a b : ℤ)
    (x : M.M) :
    ((shiftFunctorAdd (DifferentialGradedModule A) a b).inv.app M).toFun x = x := by
  rw [ShiftMkCore.shiftFunctorAdd_eq]
  rfl

end ShiftHelpers

variable {R : Type u} [CommRing R] (A B : DifferentialGradedAlgebra.{u, u} R)
  (N : DifferentialGradedModule.{u, u, u} B) (L : BimoduleStructure A B N)

/-- The candidate comparison for the zero shift: the structural identifications. -/
def shiftZeroCompare (P : DifferentialGradedModule.{u, u, u} B) :
    shift ((homModuleFunctor A B N L).obj P) 0 ⟶
      (homModuleFunctor A B N L).obj (shift P 0) :=
  (shiftFunctorZero (DifferentialGradedModule A) ℤ).hom.app
      ((homModuleFunctor A B N L).obj P) ≫
    (homModuleFunctor A B N L).map
      ((shiftFunctorZero (DifferentialGradedModule B) ℤ).inv.app P)

/-- The candidate comparison for the zero shift has the characterizing property of the
comparison of Tag 0FQR. -/
theorem isShiftComparison_shiftZeroCompare (P : DifferentialGradedModule.{u, u, u} B) :
    HomModuleData.IsShiftComparison 0 (homModulePresentation A B N L P)
      (homModulePresentation A B N L (shift P 0)) (shiftZeroCompare A B N L P) := by
  intro n p f x
  let v : ((homModuleFunctor A B N L).obj P).grading n :=
    ⟨f.1, mem_grading_congr (show n + 0 = n by omega) f.property⟩
  let h := (shiftFunctorZero (DifferentialGradedModule B) ℤ).inv.app P
  have hval : (shiftZeroCompare A B N L P).toFun f.1 =
      (((homModuleFunctor A B N L).map h).gradedMap n v).1 :=
    congrArg ((homModuleFunctor A B N L).map h).toFun
      (shiftFunctorZero_hom_toFun' ((homModuleFunctor A B N L).obj P) f.1)
  refine Eq.trans (homogeneousEquiv_val_apply_congr
    (homModulePresentation A B N L (shift P 0)) (rfl : n = n) _
    (((homModuleFunctor A B N L).map h).gradedMap n v) hval x) ?_
  refine Eq.trans (homModuleFunctor_map_homogeneousEquiv_apply A B N L h n v x) ?_
  refine Eq.trans (shiftFunctorZero_inv_toFun' P _) ?_
  exact homogeneousEquiv_val_apply_congr (homModulePresentation A B N L P)
    (show n = n + 0 by omega) v f rfl x

/-- The candidate comparison for a sum of two shifts: the two comparisons composed with the
structural identifications. -/
def shiftAddCompare (P : DifferentialGradedModule.{u, u, u} B) (a b : ℤ) :
    shift ((homModuleFunctor A B N L).obj P) (a + b) ⟶
      (homModuleFunctor A B N L).obj (shift P (a + b)) :=
  (shiftFunctorAdd (DifferentialGradedModule A) a b).hom.app
      ((homModuleFunctor A B N L).obj P) ≫
    (CategoryTheory.shiftFunctor (DifferentialGradedModule A) b).map
      (homPresentationShiftIso A B N L P a).hom ≫
    (homPresentationShiftIso A B N L (shift P a) b).hom ≫
    (homModuleFunctor A B N L).map
      ((shiftFunctorAdd (DifferentialGradedModule B) a b).inv.app P)

/-- The candidate comparison for a sum of shifts has the characterizing property of the
comparison of Tag 0FQR. -/
theorem isShiftComparison_shiftAddCompare (P : DifferentialGradedModule.{u, u, u} B) (a b : ℤ) :
    HomModuleData.IsShiftComparison (a + b) (homModulePresentation A B N L P)
      (homModulePresentation A B N L (shift P (a + b))) (shiftAddCompare A B N L P a b) := by
  intro n p f x
  set F := homModuleFunctor A B N L
  set φ₁ := (homPresentationShiftIso A B N L P a).hom
  set φ₂ := (homPresentationShiftIso A B N L (shift P a) b).hom
  let addInv := (shiftFunctorAdd (DifferentialGradedModule B) a b).inv.app P
  let f1 : (homModulePresentation A B N L P).module.grading (n + b + a) :=
    ⟨f.1, mem_grading_congr (show n + (a + b) = n + b + a by omega) f.property⟩
  let f2 : (homModulePresentation A B N L (shift P a)).module.grading (n + b) :=
    ⟨φ₁.toFun f1.1, φ₁.map_grading (n + b) f1.1 f1.property⟩
  let w : (homModulePresentation A B N L (shift (shift P a) b)).module.grading n :=
    ⟨φ₂.toFun f2.1, φ₂.map_grading n f2.1 f2.property⟩
  have hval : (shiftAddCompare A B N L P a b).toFun f.1 = ((F.map addInv).gradedMap n w).1 :=
    congrArg (fun z => (F.map addInv).toFun (φ₂.toFun (φ₁.toFun z)))
      (shiftFunctorAdd_hom_toFun' (F.obj P) a b f.1)
  refine Eq.trans (homogeneousEquiv_val_apply_congr
    (homModulePresentation A B N L (shift P (a + b))) (rfl : n = n) _
    ((F.map addInv).gradedMap n w) hval x) ?_
  refine Eq.trans (homModuleFunctor_map_homogeneousEquiv_apply A B N L addInv n w x) ?_
  refine Eq.trans (shiftFunctorAdd_inv_toFun' P a b _) ?_
  refine Eq.trans (HomModuleData.isShiftComparison_shiftComparison b
    (homModulePresentation A B N L (shift P a))
    (homModulePresentation A B N L (shift (shift P a) b)) n p f2 x) ?_
  refine Eq.trans (HomModuleData.isShiftComparison_shiftComparison a
    (homModulePresentation A B N L P) (homModulePresentation A B N L (shift P a))
    (n + b) p f1 x) ?_
  exact homogeneousEquiv_val_apply_congr (homModulePresentation A B N L P)
    (show n + b + a = n + (a + b) by omega) f1 f rfl x

/-- The inverse of the zero-shift coherence isomorphism is the candidate comparison
`shiftZeroCompare`. -/
theorem commShiftIsoZero_inv_app_eq (P : DifferentialGradedModule.{u, u, u} B) :
    (Functor.CommShift.isoZero (homModuleFunctor A B N L) ℤ).inv.app P =
      shiftZeroCompare A B N L P := by
  simp [Functor.CommShift.isoZero, shiftZeroCompare]

/-- The inverse of the coherence isomorphism for a sum of shifts is the candidate comparison
`shiftAddCompare`. -/
theorem commShiftIsoAdd_inv_app_eq (P : DifferentialGradedModule.{u, u, u} B) (a b : ℤ) :
    (Functor.CommShift.isoAdd (homModuleFunctorShiftIso A B N L a).symm
        (homModuleFunctorShiftIso A B N L b).symm).inv.app P =
      shiftAddCompare A B N L P a b := by
  rw [Functor.CommShift.isoAdd_inv_app]
  rfl

/-- **The internal hom functor on differential graded modules commutes with the shift**, with the
comparison isomorphisms of Tag 0FQR. -/
instance homModuleFunctorCommShift : (homModuleFunctor A B N L).CommShift ℤ where
  commShiftIso k := (homModuleFunctorShiftIso A B N L k).symm
  commShiftIso_zero := by
    ext P
    refine Iso.inv_eq_hom_of_hom_eq_inv
      (z := (Functor.CommShift.isoZero (homModuleFunctor A B N L) ℤ).app P) ?_
    refine HomModuleData.shiftComparison_unique (homPresentationShiftIso_apply A B N L P 0) ?_
    rw [show ((Functor.CommShift.isoZero (homModuleFunctor A B N L) ℤ).app P).inv =
        shiftZeroCompare A B N L P from commShiftIsoZero_inv_app_eq A B N L P]
    exact isShiftComparison_shiftZeroCompare A B N L P
  commShiftIso_add a b := by
    ext P
    refine Iso.inv_eq_hom_of_hom_eq_inv
      (z := (Functor.CommShift.isoAdd (homModuleFunctorShiftIso A B N L a).symm
        (homModuleFunctorShiftIso A B N L b).symm).app P) ?_
    refine HomModuleData.shiftComparison_unique
      (homPresentationShiftIso_apply A B N L P (a + b)) ?_
    rw [show ((Functor.CommShift.isoAdd (homModuleFunctorShiftIso A B N L a).symm
          (homModuleFunctorShiftIso A B N L b).symm).app P).inv =
        shiftAddCompare A B N L P a b from commShiftIsoAdd_inv_app_eq A B N L P a b]
    exact isShiftComparison_shiftAddCompare A B N L P a b

/-! ### The internal hom functor on the homotopy categories commutes with the shift -/

/-- Internal hom followed by passage to homotopy classes identifies homotopic morphisms: it
factors through the homotopy category by Tag 0FQQ. -/
theorem homModuleFunctor_toHomotopy_respects_homotopy
    (X Y : DifferentialGradedModule.{u, u, u} B) (f₁ f₂ : X ⟶ Y) (h : homotopyRel B f₁ f₂) :
    (homModuleFunctor A B N L ⋙ toHomotopyCategory A).map f₁ =
      (homModuleFunctor A B N L ⋙ toHomotopyCategory A).map f₂ := by
  have key : ∀ f : X ⟶ Y, (homModuleFunctor A B N L ⋙ toHomotopyCategory A).map f =
      (homHomotopyDescent N L).inv.app X ≫
        (toHomotopyCategory B ⋙ homHomotopyCategoryFunctor A B N L).map f ≫
          (homHomotopyDescent N L).hom.app Y := by
    intro f
    rw [(homHomotopyDescent N L).hom.naturality f]
    simp
  rw [key f₁, key f₂]
  congr 2
  exact congrArg (homHomotopyCategoryFunctor A B N L).map
    (CategoryTheory.Quotient.sound (homotopyRel B) h)

/-- Internal hom on the homotopy categories, presented as a descent of the functor on
differential graded modules. -/
abbrev homHomotopyLift : HomotopyCategory B ⥤ HomotopyCategory A :=
  CategoryTheory.Quotient.lift (homotopyRel B) (homModuleFunctor A B N L ⋙ toHomotopyCategory A)
    (homModuleFunctor_toHomotopy_respects_homotopy A B N L)

/-- The descent of internal hom is the internal hom functor on homotopy categories. -/
def homHomotopyLiftIso :
    homHomotopyLift A B N L ≅ homHomotopyCategoryFunctor A B N L :=
  CategoryTheory.Quotient.natIsoLift _
    (CategoryTheory.Quotient.lift.isLift _ _
        (homModuleFunctor_toHomotopy_respects_homotopy A B N L) ≪≫
      (homHomotopyDescent N L).symm)

/-- **The internal hom functor on homotopy categories commutes with the shift.** -/
instance homHomotopyCategoryFunctorCommShift :
    (homHomotopyCategoryFunctor A B N L).CommShift ℤ :=
  Functor.CommShift.ofIso (homHomotopyLiftIso A B N L) ℤ

/-- The identification of the descended internal hom with the internal hom functor on homotopy
categories commutes with the shift. -/
instance homHomotopyLiftIso_commShift :
    NatTrans.CommShift (homHomotopyLiftIso A B N L).hom ℤ :=
  Functor.CommShift.ofIso_compatibility (homHomotopyLiftIso A B N L) ℤ

/-- The descent isomorphism of Tag 0FQQ commutes with the shift. -/
instance homHomotopyDescent_commShift : NatTrans.CommShift (homHomotopyDescent N L).hom ℤ := by
  have h1 : Functor.whiskerLeft (toHomotopyCategory B) (homHomotopyLiftIso A B N L).inv =
      (homHomotopyDescent N L).hom ≫ (CategoryTheory.Quotient.lift.isLift (homotopyRel B)
        (homModuleFunctor A B N L ⋙ toHomotopyCategory A)
        (homModuleFunctor_toHomotopy_respects_homotopy A B N L)).inv :=
    CategoryTheory.whiskerLeft_natTransLift _
  have h2 : (homHomotopyDescent N L).hom =
      Functor.whiskerLeft (toHomotopyCategory B) (homHomotopyLiftIso A B N L).inv ≫
        (CategoryTheory.Quotient.lift.isLift (homotopyRel B)
          (homModuleFunctor A B N L ⋙ toHomotopyCategory A)
          (homModuleFunctor_toHomotopy_respects_homotopy A B N L)).hom := by
    rw [h1]
    simp
  rw [h2]
  infer_instance

/-! ### The comparison of the derived Hom functor commutes with the shift -/

/-- Internal hom followed by localization of the target commutes with the shift. -/
instance homToDerivedCategoryCommShift : (homToDerivedCategory A B N L).CommShift ℤ :=
  inferInstanceAs
    ((homHomotopyCategoryFunctor A B N L ⋙ (quasiIsomorphisms' A).Q).CommShift ℤ)

/-- `RHom(N, -)` commutes with the shift, for the structure of a right derived functor. -/
instance derivedHomFunctorCommShift : (derivedHomData A B N L).functor.CommShift ℤ :=
  haveI := (derivedHomData A B N L).isRightDerived
  Functor.IsRightDerivedFunctor.commShift (derivedHomData A B N L).functor
    (derivedHomData A B N L).comparison (quasiIsomorphisms' B) ℤ

/-- **The comparison of Tag 09LI commutes with the shift.** -/
instance derivedHomComparisonCommShift :
    NatTrans.CommShift (derivedHomData A B N L).comparison ℤ :=
  haveI := (derivedHomData A B N L).isRightDerived
  Functor.IsRightDerivedFunctor.natTrans_commShift (derivedHomData A B N L).functor
    (derivedHomData A B N L).comparison (quasiIsomorphisms' B) ℤ

/-! ### The connecting homomorphism of the image sequence -/

section Connecting

variable {X Y Z : DifferentialGradedModule.{u, u, u} B} {f : Hom X Y} {g : Hom Y Z}

/-- The degree-one homogeneous map `π ∘ d_Y ∘ s` of the differential graded category: the
connecting homomorphism of an admissible short exact sequence written so that a differential
graded functor can be applied to it. -/
def connectingHomogeneous (c : CompatibleSplittings B f g) : HomogeneousMap B Z X 1 :=
  homogeneousMapComp B (show (0 : ℤ) + 1 = 1 from rfl) c.π.toHomogeneousMap
    ((dgCategory B).d c.s.toHomogeneousMap)

/-- Its underlying linear map is the connecting homomorphism. -/
theorem connectingHomogeneous_val (hfg : IsAdmissibleShortExact f g)
    (c : CompatibleSplittings B f g) (x : Z.M) :
    (connectingHomogeneous B c).1 x =
      (connectingHom f g hfg c.s c.π c.hs c.hπ c.hker).val.toFun x := by
  refine Eq.trans ?_ ((connectingHom f g hfg c.s c.π c.hs c.hπ c.hker).property x).symm
  show c.π.toFun (((dgCategory B).d c.s.toHomogeneousMap).1 x) = _
  rw [dgCategory_d_val]
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, DifferentialGraded.gradedSign_zero,
    one_smul, map_sub]
  show c.π.toFun (Y.d (c.s.toFun x)) - c.π.toFun (c.s.toFun (Z.d x)) = _
  rw [c.comp_eq_zero, sub_zero]

end Connecting

/-- The internal hom functor sends a morphism to postcomposition with it. -/
theorem homModuleFunctor_map_eq (X Y : DifferentialGradedModule.{u, u, u} B) (h : X ⟶ Y) :
    (homModuleFunctor A B N L).map h = homPostcompHom A B N L h := rfl

/-- The internal hom functor commutes with the differential of the differential graded
category, read on the underlying linear maps. -/
theorem homPostcompMap_d {X Y : DifferentialGradedModule.{u, u, u} B} {n : ℤ}
    (u : HomogeneousMap B X Y n) :
    homPostcompMap A B N L ((dgCategory B).d u) =
      ((dgCategory A).d ((homDGFunctor A B N L).map u)).1 :=
  congrArg Subtype.val ((homDGFunctor A B N L).map_d u)

section Connecting2

variable {X Y Z : DifferentialGradedModule.{u, u, u} B} {f : Hom X Y} {g : Hom Y Z}

/-- The connecting homomorphism of the image sequence is the image of `π ∘ d_Y ∘ s`. -/
theorem homPostcomp_connectingHom_toFun (hfg : IsAdmissibleShortExact f g)
    (c : CompatibleSplittings B f g) (z : (homModulePresentation A B N L Z).module.M) :
    (connectingHom (homPostcompHom A B N L f) (homPostcompHom A B N L g)
        (isAdmissibleShortExact_homPostcomp A B N L c hfg)
        (compatibleSplittings_homPostcomp A B N L c hfg).s
        (compatibleSplittings_homPostcomp A B N L c hfg).π
        (compatibleSplittings_homPostcomp A B N L c hfg).hs
        (compatibleSplittings_homPostcomp A B N L c hfg).hπ
        (compatibleSplittings_homPostcomp A B N L c hfg).hker).val.toFun z =
      homPostcompMap A B N L (connectingHomogeneous B c) z := by
  set c' := compatibleSplittings_homPostcomp A B N L c hfg
  refine ((connectingHom _ _ _ c'.s c'.π c'.hs c'.hπ c'.hker).property z).trans ?_
  rw [connectingHomogeneous, homPostcompMap_comp, homPostcompMap_d, dgCategory_d_val]
  simp only [DifferentialGraded.gradedSign_zero, one_smul]
  show c'.π.toFun ((homModulePresentation A B N L Y).module.d (c'.s.toFun z)) =
    homPostcompMap A B N L c.π.toHomogeneousMap
      (((homDGFunctor A B N L).obj Y).d
          (((homDGFunctor A B N L).map c.s.toHomogeneousMap).1 z) -
        ((homDGFunctor A B N L).map c.s.toHomogeneousMap).1
          (((homDGFunctor A B N L).obj Z).d z))
  have hz : homPostcompMap A B N L c.π.toHomogeneousMap
      (((homDGFunctor A B N L).map c.s.toHomogeneousMap).1
        (((homDGFunctor A B N L).obj Z).d z)) = 0 :=
    homPostcomp_retraction_section A B N L c _
  exact ((LinearMap.map_sub (homPostcompMap A B N L c.π.toHomogeneousMap) _ _).trans
    (sub_eq_self.mpr hz)).symm

/-- **The connecting homomorphism of the image sequence is the image of the connecting
homomorphism**, read through the shift comparison of Tag 0FQR. -/
theorem homPostcomp_connectingHom (hfg : IsAdmissibleShortExact f g)
    (c : CompatibleSplittings B f g) :
    (connectingHom (homPostcompHom A B N L f) (homPostcompHom A B N L g)
        (isAdmissibleShortExact_homPostcomp A B N L c hfg)
        (compatibleSplittings_homPostcomp A B N L c hfg).s
        (compatibleSplittings_homPostcomp A B N L c hfg).π
        (compatibleSplittings_homPostcomp A B N L c hfg).hs
        (compatibleSplittings_homPostcomp A B N L c hfg).hπ
        (compatibleSplittings_homPostcomp A B N L c hfg).hker).val =
      (homModuleFunctor A B N L).map
          (connectingHom f g hfg c.s c.π c.hs c.hπ c.hker).val ≫
        (homPresentationShiftIso A B N L X 1).inv := by
  refine Hom.ext_of_grading fun p u => ?_
  set δ := (connectingHom f g hfg c.s c.π c.hs c.hπ c.hker).val
  set e := homPresentationShiftIso A B N L X 1
  have hid : ∀ w, e.inv.toFun (e.hom.toFun w) = w := fun w =>
    LinearMap.congr_fun (congrArg DifferentialGradedModule.Hom.toFun e.hom_inv_id) w
  set w1 : (homModulePresentation A B N L X).module.grading (p + 1) :=
    ⟨homPostcompMap A B N L (connectingHomogeneous B c) u.1,
      ((homDGFunctor A B N L).map (connectingHomogeneous B c)).2.1 p u.1 u.property⟩
  have hEq : (⟨e.hom.toFun w1.1, e.hom.map_grading p w1.1 w1.property⟩ :
      (homModulePresentation A B N L (shift X 1)).module.grading p) =
      ((homModuleFunctor A B N L).map δ).gradedMap p u := by
    refine ((homModulePresentation A B N L (shift X 1)).homogeneousEquiv p).injective
      (homogeneousMap_ext fun q y => ?_)
    refine Eq.trans (homPresentationShiftIso_apply A B N L X 1 p q w1 y) ?_
    refine Eq.trans ?_ (homModuleFunctor_map_homogeneousEquiv_apply A B N L δ p u y).symm
    set g0 := homogeneousMapComp B (rfl : 1 + p = 1 + p) (connectingHomogeneous B c)
      ((homModulePresentation A B N L Z).homogeneousEquiv p u)
    set v0 := ((homModulePresentation A B N L X).homogeneousEquiv (1 + p)).symm g0 with hv0
    have hval : w1.1 = v0.1 :=
      homPostcompHomogeneousMap_apply A B N L (homModulePresentation A B N L Z)
        (homModulePresentation A B N L X) 1 p (connectingHomogeneous B c) u
    refine Eq.trans (homogeneousEquiv_val_apply_congr (homModulePresentation A B N L X)
      (show p + 1 = 1 + p by omega) w1 v0 hval y) ?_
    rw [hv0, LinearEquiv.apply_symm_apply]
    exact connectingHomogeneous_val B hfg c _
  exact (homPostcomp_connectingHom_toFun A B N L hfg c u.1).trans
    ((hid w1.1).symm.trans (congrArg e.inv.toFun (congrArg Subtype.val hEq)))

end Connecting2

/-- The commutation isomorphism of the internal hom functor with the shift `k`, at `P`, is the
inverse of the comparison of Tag 0FQR. -/
theorem homModuleFunctor_commShiftIso_hom_app (P : DifferentialGradedModule.{u, u, u} B)
    (k : ℤ) :
    ((homModuleFunctor A B N L).commShiftIso k).hom.app P =
      (homPresentationShiftIso A B N L P k).inv := rfl

/-! ### Exactness of the internal hom functor on the homotopy categories -/

section Exact

variable {X Y Z : DifferentialGradedModule.{u, u, u} B} {f : Hom X Y} {g : Hom Y Z}

unseal CategoryTheory.HasShift.quotient CategoryTheory.Quotient.functor_commShift

/-- The image of the triangle of an admissible short exact sequence is the triangle of the image
sequence. All three vertices agree on the nose; only the connecting arrow needs an argument, and
that is `DifferentialGradedModule.homPostcomp_connectingHom`. -/
def homMapTriangleIso (hfg : IsAdmissibleShortExact f g) (c : CompatibleSplittings B f g) :
    (homHomotopyLift A B N L).mapTriangle.obj (associatedTriangleOfSplittings B f g hfg c) ≅
      associatedTriangleOfSplittings A (homPostcompHom A B N L f) (homPostcompHom A B N L g)
        (isAdmissibleShortExact_homPostcomp A B N L c hfg)
        (compatibleSplittings_homPostcomp A B N L c hfg) := by
  refine Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · set ι := (homPresentationShiftIso A B N L X 1).inv with hιdef
    set δ := (connectingHom f g hfg c.s c.π c.hs c.hπ c.hker).val with hδdef
    have hmap : (toHomotopyCategory A).map
          (connectingHom (homPostcompHom A B N L f) (homPostcompHom A B N L g)
            (isAdmissibleShortExact_homPostcomp A B N L c hfg)
            (compatibleSplittings_homPostcomp A B N L c hfg).s
            (compatibleSplittings_homPostcomp A B N L c hfg).π
            (compatibleSplittings_homPostcomp A B N L c hfg).hs
            (compatibleSplittings_homPostcomp A B N L c hfg).hπ
            (compatibleSplittings_homPostcomp A B N L c hfg).hker).val =
        (toHomotopyCategory A).map ((homModuleFunctor A B N L).map δ) ≫
          (toHomotopyCategory A).map ι := by
      rw [homPostcomp_connectingHom A B N L hfg c]
      exact (toHomotopyCategory A).map_comp _ _
    have hC : (Functor.commShiftIso (homModuleFunctor A B N L ⋙ toHomotopyCategory A)
        (1 : ℤ)).hom.app X = (toHomotopyCategory A).map ι := by
      rw [Functor.commShiftIso_comp_hom_app]
      refine Eq.trans (congrArg (fun w => (toHomotopyCategory A).map
          ((Functor.commShiftIso (homModuleFunctor A B N L) (1 : ℤ)).hom.app X) ≫ w)
        (toHomotopyCategory_commShiftIso_hom_app_eq_id A
          ((homModuleFunctor A B N L).obj X) 1)) ?_
      exact Category.comp_id _
    have hcs : ((homHomotopyLift A B N L).commShiftIso (1 : ℤ)).hom.app
        ((toHomotopyCategory B).obj X) = (toHomotopyCategory A).map ι := by
      have hid : (CategoryTheory.Quotient.lift (homotopyRel B)
            (homModuleFunctor A B N L ⋙ toHomotopyCategory A)
            (homModuleFunctor_toHomotopy_respects_homotopy A B N L)).map
          (𝟙 ((toHomotopyCategory B ⋙
            CategoryTheory.shiftFunctor (HomotopyCategory B) (1 : ℤ)).obj X)) = 𝟙 _ :=
        (CategoryTheory.Quotient.lift (homotopyRel B)
          (homModuleFunctor A B N L ⋙ toHomotopyCategory A)
          (homModuleFunctor_toHomotopy_respects_homotopy A B N L)).map_id _
      rw [CategoryTheory.Quotient.liftCommShift_commShiftIso,
        CategoryTheory.Quotient.LiftCommShift.iso_hom_app,
        toHomotopyCategory_commShiftIso_inv_app_eq_id, hC]
      exact (congrArg (fun w => w ≫ (toHomotopyCategory A).map ι) hid).trans
        (Category.id_comp _)
    have h1 : (toHomotopyCategory B).map δ ≫
        eqToHom (CategoryTheory.Quotient.functor_obj_shift (homotopyRel B) ℤ X 1).symm =
        (toHomotopyCategory B).map δ :=
      (congrArg (fun w => (toHomotopyCategory B).map δ ≫ w)
        (quotient_shift_eqToHom_eq_id B X 1)).trans (Category.comp_id _)
    have h2 : ((toHomotopyCategory A).map ((homModuleFunctor A B N L).map δ) ≫
          (toHomotopyCategory A).map ι) ≫
        eqToHom (CategoryTheory.Quotient.functor_obj_shift (homotopyRel A) ℤ
          ((homModuleFunctor A B N L).obj X) 1).symm =
        (toHomotopyCategory A).map ((homModuleFunctor A B N L).map δ) ≫
          (toHomotopyCategory A).map ι :=
      (congrArg (fun w => ((toHomotopyCategory A).map ((homModuleFunctor A B N L).map δ) ≫
          (toHomotopyCategory A).map ι) ≫ w)
        (quotient_shift_eqToHom_eq_id A ((homModuleFunctor A B N L).obj X) 1)).trans
        (Category.comp_id _)
    simp only [Iso.refl_hom]
    refine Eq.trans (congrArg (fun w =>
      ((homHomotopyLift A B N L).mapTriangle.obj
        (associatedTriangleOfSplittings B f g hfg c)).mor₃ ≫ w)
      ((CategoryTheory.shiftFunctor (HomotopyCategory A) (1 : ℤ)).map_id _)) ?_
    refine (Category.comp_id _).trans (Eq.trans ?_ (Category.id_comp _).symm)
    change (homHomotopyLift A B N L).map
          ((toHomotopyCategory B).map δ ≫
            eqToHom (CategoryTheory.Quotient.functor_obj_shift (homotopyRel B) ℤ X 1).symm) ≫
          ((homHomotopyLift A B N L).commShiftIso (1 : ℤ)).hom.app
            ((toHomotopyCategory B).obj X) =
        (toHomotopyCategory A).map
            (connectingHom (homPostcompHom A B N L f) (homPostcompHom A B N L g)
              (isAdmissibleShortExact_homPostcomp A B N L c hfg)
              (compatibleSplittings_homPostcomp A B N L c hfg).s
              (compatibleSplittings_homPostcomp A B N L c hfg).π
              (compatibleSplittings_homPostcomp A B N L c hfg).hs
              (compatibleSplittings_homPostcomp A B N L c hfg).hπ
              (compatibleSplittings_homPostcomp A B N L c hfg).hker).val ≫
          eqToHom (CategoryTheory.Quotient.functor_obj_shift (homotopyRel A) ℤ
            ((homModuleFunctor A B N L).obj X) 1).symm
    rw [h1, hcs, hmap]
    exact h2.symm

end Exact

/-- The descent of the internal hom functor to the homotopy category is triangulated. -/
instance homHomotopyLift_isTriangulated : (homHomotopyLift A B N L).IsTriangulated where
  map_distinguished T hT := by
    rw [distinguishedTriangles_eq B] at hT
    rw [distinguishedTriangles_eq A]
    obtain ⟨X, Y, Z, f, g, hfg, ⟨e⟩⟩ := hT
    let c := Classical.choice (nonempty_compatibleSplittings B f g hfg)
    have hT' : T ≅ associatedTriangleOfSplittings B f g hfg c :=
      e ≪≫ (eqToIso (associatedTriangleOfSplittings_eq B f g hfg c)).symm
    exact isDistinguishedTriangle_of_iso A
      (((homHomotopyLift A B N L).mapTriangle.mapIso hT' ≪≫
        homMapTriangleIso A B N L hfg c).symm)
      (isDistinguishedTriangle_associatedTriangleOfSplittings A _ _ _ _)

/-- **Stacks 09LH.** The internal hom functor out of a differential graded bimodule is an exact
functor of the homotopy categories, for the commutation with the translation of Tag 0FQR. -/
@[stacks 09LH]
instance homHomotopyCategoryFunctor_isTriangulated :
    (homHomotopyCategoryFunctor A B N L).IsTriangulated :=
  Functor.isTriangulated_of_iso (homHomotopyLiftIso A B N L)

/-! ### Exactness of the derived Hom functor -/

/-- Internal hom out of `N`, followed by localization of the target, is exact. -/
instance homToDerivedCategory_isTriangulated : (homToDerivedCategory A B N L).IsTriangulated :=
  inferInstanceAs
    ((homHomotopyCategoryFunctor A B N L ⋙ (quasiIsomorphisms' A).Q).IsTriangulated)

variable {A B} in
/-- Resolutions by modules orthogonal on the right to the acyclic ones, from the property (I)
resolutions of Tag 09KU. -/
theorem exists_quasiIso_rightOrthogonal_acyclic
    (B : DifferentialGradedAlgebra.{u, u} R) (M : DifferentialGradedModule.{u, u, u} B) :
    ∃ (I : DifferentialGradedModule.{u, u, u} B) (f : M ⟶ I),
      QuasiIso ((forgetToCochainComplex B).map f) ∧
        (acyclic' B).rightOrthogonal ((toHomotopyCategory B).obj I) :=
  exists_quasiIso_rightOrthogonal_acyclic_of_propertyI_resolutions B
    (exists_propertyI_resolution B) M

variable {A B} in
/-- Every object of `D(B, d)` is isomorphic to the image of an object of `K(B, d)` orthogonal on
the right to the acyclic modules. -/
theorem exists_rightOrthogonal_resolution (B : DifferentialGradedAlgebra.{u, u} R)
    (X : (quasiIsomorphisms' B).Localization) :
    ∃ I : HomotopyCategory B, (acyclic' B).rightOrthogonal I ∧
      Nonempty ((quasiIsomorphisms' B).Q.obj I ≅ X) := by
  obtain ⟨I, s, hs, hI⟩ := exists_trW_rightOrthogonal_of_exists_quasiIso_rightOrthogonal B
    (exists_quasiIso_rightOrthogonal_acyclic B) ((quasiIsomorphisms' B).Q.objPreimage X)
  rw [acyclic_trW_eq_quasiIsomorphisms' B] at hs
  have hqs : IsIso ((quasiIsomorphisms' B).Q.map s) :=
    Localization.inverts (quasiIsomorphisms' B).Q (quasiIsomorphisms' B) s hs
  exact ⟨I, hI, ⟨(asIso ((quasiIsomorphisms' B).Q.map s)).symm ≪≫
    (quasiIsomorphisms' B).Q.objObjPreimageIso X⟩⟩

/-- **The derived Hom functor `R Hom(N, -) : D(B, d) ⥤ D(A, d)` is exact**, for the commutation
with the translation for which the comparison of Tag 09LI is compatible.

Every object of `D(B, d)` is the image of a module orthogonal on the right to the acyclic ones,
a distinguished triangle may be completed inside those modules — their class is a triangulated
subcategory — and there the comparison of Tag 09LI is invertible. That is the hypothesis of
`CategoryTheory.Functor.isTriangulated_of_leftExtension`, whose other input is the exactness of
ordinary internal hom on the homotopy categories, Tag 09LH. -/
instance derivedHomFunctor_isTriangulated :
    (derivedHomData A B N L).functor.IsTriangulated := by
  have hres := (derivedHomData A B N L).isRightDerived
  refine Functor.isTriangulated_of_leftExtension (derivedHomData A B N L).functor
    (derivedHomData A B N L).comparison fun X Y φ => ?_
  obtain ⟨I, hI, ⟨eI⟩⟩ := exists_rightOrthogonal_resolution B X
  obtain ⟨J, hJ, ⟨eJ⟩⟩ := exists_rightOrthogonal_resolution B Y
  obtain ⟨g, hg⟩ := (quasiIsomorphismsQ_map_bijective_of_rightOrthogonal B hJ I).surjective
    (eI.hom ≫ φ ≫ eJ.inv)
  obtain ⟨Z, k, δ, hT⟩ := Pretriangulated.distinguished_cocone_triangle g
  have hZ : (acyclic' B).rightOrthogonal Z :=
    (acyclic' B).rightOrthogonal.ext_of_isTriangulatedClosed₃ _ hT hI hJ
  refine ⟨Pretriangulated.Triangle.mk g k δ, hT,
    DerivedHomData.isIso_comparison_app_of_rightOrthogonal A B L (derivedHomData A B N L)
      (exists_quasiIso_rightOrthogonal_acyclic B) hI,
    DerivedHomData.isIso_comparison_app_of_rightOrthogonal A B L (derivedHomData A B N L)
      (exists_quasiIso_rightOrthogonal_acyclic B) hJ,
    DerivedHomData.isIso_comparison_app_of_rightOrthogonal A B L (derivedHomData A B N L)
      (exists_quasiIso_rightOrthogonal_acyclic B) hZ, ⟨Arrow.isoMk eI eJ ?_⟩⟩
  simp [hg]

end DifferentialGradedModule

end
