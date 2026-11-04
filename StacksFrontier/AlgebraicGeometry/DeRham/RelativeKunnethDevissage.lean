module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativeKunnethBoundedComparison
public import StacksFrontier.Algebra.Homology.HomotopyCategory.BoundedStupidDevissage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FiniteOrderBiproducts
import StacksCore.Tactic.StacksAttribute

/-!
# Dévissage of the relative Künneth map of the box product

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes, and let `Pa`, `Pb` be predicates on
finite-order differential operators on `X/S` and on `Y/S`. This file proves that the relative
Künneth map of [Stacks, Tag 0G4B]

`Ra_*𝓕^• ⊗^𝐋_{𝒪_S} Rb_*𝓖^• ⟶ Rf_*Tot(𝓕^• ⊠ 𝓖^•)`

is invertible at every pair of strictly bounded complexes whose terms satisfy `Pa` and `Pb`, as
soon as it is invertible at every pair of complexes concentrated in one degree. This is the
dévissage step of the proof of [Stacks, Tag 0FLT].

## Main results

* `Stacks.Cohomology.BoxKunneth.isIso_relativeBoxKunnethMap_of_isIso_single`: **the
  dévissage**, for `relativeBoxKunnethMap`.
* `Stacks.Cohomology.BoxKunneth.isIso_relativeBoxKunnethMapUnbounded_of_isIso_single`: the same
  for the map with the target total complex formed over `f^{-1}𝒪_S`, together with its two
  one-variable halves `..._left` and `..._right`.
* `Stacks.Cohomology.BoxKunneth.kunnethLeftNatTrans` and `kunnethRightNatTrans`: the Künneth map
  as a natural transformation of triangulated functors of one complex, on the homotopy category.

## Implementation notes

*Where the total complex is formed.* `Tot(𝓕^• ⊠ 𝓖^•)` exists in the category of finite-order
differential operators only for bounded-below complexes, so it is not a functor on the homotopy
category. Over `f^{-1}𝒪_S`, where all direct sums exist, it is. With the other complex fixed, it
is a triangulated functor of either complex: `Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR`
and `bifunctorPhi`, the reduction of [Stacks, Tag 0G6E]. So the dévissage runs over
`relativeBoxKunnethMapUnbounded`, and `isIso_relativeBoxKunnethMap_iff` transfers it to
`relativeBoxKunnethMap`. The naturality of the Künneth map in each complex
(`relativeBoxKunnethMapUnbounded_natural_left` and `_right`) makes it a natural transformation on
the category of complexes. It descends to the homotopy category along
`CategoryTheory.Quotient.natTransLift`. The induction itself is the generic
`Stacks.HomotopyDevissage.isIso_app_quotient_obj_of_isStrictlyLE`.

*Two preadditive structures.* The category of `f^{-1}𝒪_S`-modules carries two preadditive
structures that agree only after unfolding: Mathlib's, and the one underlying its abelian
structure. `DerivedCategory.Qh` is formed at the second, so the homotopy categories feeding it are
formed at the second as well. That is the `Abelian.toPreadditive` argument of
`kunnethSourceFirst` and of `kunnethTargetSecond`. The shift- and triangulation data of the
composite functors are assembled with their factors passed explicitly, because instance search
does not cross the two spellings.

*The derived category model.* As in `StacksFrontier.AlgebraicGeometry.DeRham.BoxTotalKunnethMap`, the
model `CategoryTheory.HasDerivedCategory.standard` is given priority, `relativeBoxKunnethMap` and
the maps it is built from being stated at it.

## References

* [Stacks Project, Tag 0FLT](https://stacks.math.columbia.edu/tag/0FLT)
* [Stacks Project, Tag 0G4B](https://stacks.math.columbia.edu/tag/0G4B)
* [Stacks Project, Tag 0G6E](https://stacks.math.columbia.edu/tag/0G6E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DeRhamDirectImage
open Stacks.DerivedTensor.RingedSite
open AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory
open Stacks.Cohomology.GlobalKunneth
open Stacks.SheafOfModules.Tensor.Reduction

universe u

namespace Stacks.Cohomology.BoxKunneth

attribute [local instance 2000] HasDerivedCategory.standard

attribute [local instance] derivedPushforwardCommShift

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- The derived pushforward along a morphism of ringed spaces is a triangulated functor. -/
local instance derivedPushforwardIsTriangulated {Z Z' : RingedSpace.{u, u}} (f : Z ⟶ Z') :
    (derivedPushforward.{u, u + 1, u + 1} f).IsTriangulated :=
  derivedPushforward_isTriangulated f

/-- The box product read over `f^{-1}𝒪_S` is additive in the first operator. -/
instance boxProductRelativeCurried_additive : (boxProductRelativeCurried a b).Additive where
  map_add {F F'} {f g} := by
    refine NatTrans.ext (funext fun G => ?_)
    refine ((boxProductRelative_map a b (f + g) (𝟙 G)).trans ?_).trans
      (congrArg₂ (· + ·) (boxProductRelative_map a b f (𝟙 G))
        (boxProductRelative_map a b g (𝟙 G))).symm
    rw [boxHom_add_left, Functor.map_add]
    exact rfl

/-- The box product read over `f^{-1}𝒪_S` is additive in the second operator. -/
instance boxProductRelativeCurried_obj_additive (F : FiniteOrderDifferentialOperatorCategory a) :
    ((boxProductRelativeCurried a b).obj F).Additive where
  map_add {G G'} {f g} := by
    refine ((boxProductRelative_map a b (𝟙 F) (f + g)).trans ?_).trans
      (congrArg₂ (· + ·) (boxProductRelative_map a b (𝟙 F) f)
        (boxProductRelative_map a b (𝟙 F) g)).symm
    rw [boxHom_add_right, Functor.map_add]
    exact rfl

/-- The category of finite-order differential operators relative to `c` has binary biproducts. -/
local instance hasBinaryBiproducts_finiteOrder {Z T : Scheme.{u}} (c : Z ⟶ T) :
    HasBinaryBiproducts (FiniteOrderDifferentialOperatorCategory c) :=
  hasBinaryBiproducts_of_finite_biproducts _

/-- The category of modules over a ringed space has binary biproducts. -/
local instance hasBinaryBiproducts_modules (Z : RingedSpace.{u, u}) :
    HasBinaryBiproducts (_root_.Modules Z) :=
  inferInstanceAs (HasBinaryBiproducts (SheafOfModules.{u} (structureSheafRing Z)))

/-- Two complexes of finite-order differential operators on `X/S` and on `Y/S` have a total
complex of their box product over `f^{-1}𝒪_S`. -/
local instance hasMapBifunctor_boxProductRelativeCurried
    (K₁ : HomologicalComplex (FiniteOrderDifferentialOperatorCategory a) (ComplexShape.up ℤ))
    (K₂ : HomologicalComplex (FiniteOrderDifferentialOperatorCategory b) (ComplexShape.up ℤ)) :
    K₁.HasMapBifunctor K₂ (boxProductRelativeCurried a b) (ComplexShape.up ℤ) :=
  inferInstance

/-- The total complex of the box product with a fixed second complex commutes with shifts. -/
local instance commShift_bifunctorPhiR
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ) :
    (bifunctorPhiR (boxProductRelativeCurried a b) L).CommShift ℤ :=
  bifunctorXiR (boxProductRelativeCurried a b) L

/-- The total complex of the box product with a fixed second complex is a triangulated functor. -/
local instance isTriangulated_bifunctorPhiR
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ) :
    (bifunctorPhiR (boxProductRelativeCurried a b) L).IsTriangulated :=
  bifunctorPhiR_isTriangulated (boxProductRelativeCurried a b) L

/-- The total complex of the box product with a fixed first complex commutes with shifts. -/
local instance commShift_bifunctorPhi
    (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ) :
    (bifunctorPhi (boxProductRelativeCurried a b) K).CommShift ℤ :=
  bifunctorXi (boxProductRelativeCurried a b) K

/-- The total complex of the box product with a fixed first complex is a triangulated functor. -/
local instance isTriangulated_bifunctorPhi
    (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ) :
    (bifunctorPhi (boxProductRelativeCurried a b) K).IsTriangulated :=
  bifunctorPhi_isTriangulated (boxProductRelativeCurried a b) K

/-- The shift functors of the homotopy category of modules over a ringed space, formed at the
preadditive structure underlying its abelian structure, are additive. -/
local instance homotopyCategory_modules_shiftFunctor_additive (Z : RingedSpace.{u, u}) (n : ℤ) :
    (shiftFunctor (@HomotopyCategory _ (_root_.Modules Z) _ Abelian.toPreadditive
      (ComplexShape.up ℤ)) n).Additive :=
  inferInstance

/-! ### The Künneth map as a natural transformation in the first complex -/

/-- The first half of the two source functors: `𝓕^• ↦ 𝓕^•` read over `a^{-1}𝒪_S`, in
`D(a^{-1}𝒪_S)`. -/
abbrev kunnethSourceFirst :
    HomotopyCategory (FiniteOrderDifferentialOperatorCategory a) (ComplexShape.up ℤ) ⥤
      DerivedCategory (_root_.Modules (inverseImageBase a)) :=
  @Functor.mapHomotopyCategory _ _ _ _ _ _ Abelian.toPreadditive (toInverseImageModules a)
    ⟨fun {_ _ _ _} => Functor.map_add (toInverseImageModules a)⟩ (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh

/-- `kunnethSourceFirst a` commutes with shifts. -/
local instance commShift_kunnethSourceFirst : (kunnethSourceFirst a).CommShift ℤ :=
  Functor.CommShift.comp _ _

/-- `kunnethSourceFirst a` is a triangulated functor. -/
local instance isTriangulated_kunnethSourceFirst :
    (kunnethSourceFirst a).IsTriangulated :=
  Functor.IsTriangulated.instComp _ _

/-- The second half of the target functor: `M ↦ Rf_*M`. -/
abbrev kunnethTargetSecond :
    @HomotopyCategory _ (_root_.Modules (inverseImageBase (pullback.fst a b ≫ a))) _
        Abelian.toPreadditive (ComplexShape.up ℤ) ⥤
      DerivedModules (SheafedSpace.sheaf S.toRingedSpace) :=
  DerivedCategory.Qh ⋙
    derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection (pullback.fst a b ≫ a))

/-- `kunnethTargetSecond a b` commutes with shifts. -/
local instance commShift_kunnethTargetSecond : (kunnethTargetSecond a b).CommShift ℤ :=
  @Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _
    (inferInstance : (DerivedCategory.Qh
      (C := _root_.Modules (inverseImageBase (pullback.fst a b ≫ a)))).CommShift ℤ)
    (derivedPushforwardCommShift (inverseImageBaseProjection (pullback.fst a b ≫ a)))

/-- `kunnethTargetSecond a b` is a triangulated functor. -/
local instance isTriangulated_kunnethTargetSecond :
    (kunnethTargetSecond a b).IsTriangulated :=
  @Functor.IsTriangulated.instComp _ _ _ _ _ _ _ _ _ _
    (inferInstance : (DerivedCategory.Qh
      (C := _root_.Modules (inverseImageBase (pullback.fst a b ≫ a)))).CommShift ℤ) _
    (derivedPushforwardCommShift (inverseImageBaseProjection (pullback.fst a b ≫ a)))
    _ _ _ _ _ _ _ _ _ _ _ _
    (inferInstance : (DerivedCategory.Qh
      (C := _root_.Modules (inverseImageBase (pullback.fst a b ≫ a)))).IsTriangulated)
    (derivedPushforwardIsTriangulated (inverseImageBaseProjection (pullback.fst a b ≫ a)))

section Left

variable (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ)

/-- The functor `M ↦ M ⊗^𝐋_{𝒪_S} Rb_*𝓖^•` commutes with shifts. -/
local instance commShift_tensorRightPushforward :
    ((derivedTensorProductFunctor.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)).flip.obj
        ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).obj
          (DerivedCategory.Q.obj (rightComplex b L)))).CommShift ℤ :=
  (canonicalDerivedTensorProduct (SheafedSpace.sheaf S.toRingedSpace)).commShift_left _

/-- The functor `M ↦ M ⊗^𝐋_{𝒪_S} Rb_*𝓖^•` is a triangulated functor. -/
local instance isTriangulated_tensorRightPushforward :
    ((derivedTensorProductFunctor.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)).flip.obj
        ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).obj
          (DerivedCategory.Q.obj (rightComplex b L)))).IsTriangulated :=
  (canonicalDerivedTensorProduct (SheafedSpace.sheaf S.toRingedSpace)).exact_left _

/-- The second half of the source functor: `M ↦ Ra_*M ⊗^𝐋_{𝒪_S} Rb_*𝓖^•`. -/
abbrev kunnethSourceLeftSecond :
    DerivedCategory (_root_.Modules (inverseImageBase a)) ⥤
      DerivedModules (SheafedSpace.sheaf S.toRingedSpace) :=
  derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a) ⋙
    (derivedTensorProductFunctor.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)).flip.obj
        ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).obj
          (DerivedCategory.Q.obj (rightComplex b L)))

/-- The source of the Künneth map as a triangulated functor of the first complex, on the homotopy
category: `𝓕^• ↦ Ra_*𝓕^• ⊗^𝐋_{𝒪_S} Rb_*𝓖^•`. -/
abbrev kunnethSourceLeft :
    HomotopyCategory (FiniteOrderDifferentialOperatorCategory a) (ComplexShape.up ℤ) ⥤
      DerivedModules (SheafedSpace.sheaf S.toRingedSpace) :=
  kunnethSourceFirst a ⋙ kunnethSourceLeftSecond a b L

/-- The target of the Künneth map as a triangulated functor of the first complex, on the homotopy
category: `𝓕^• ↦ Rf_*Tot(𝓕^• ⊠ 𝓖^•)`. -/
abbrev kunnethTargetLeft :
    HomotopyCategory (FiniteOrderDifferentialOperatorCategory a) (ComplexShape.up ℤ) ⥤
      DerivedModules (SheafedSpace.sheaf S.toRingedSpace) :=
  bifunctorPhiR (boxProductRelativeCurried a b) L ⋙ kunnethTargetSecond a b

/-- `kunnethSourceLeftSecond a b L` commutes with shifts. -/
local instance commShift_kunnethSourceLeftSecond :
    (kunnethSourceLeftSecond a b L).CommShift ℤ :=
  @Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _
    (derivedPushforwardCommShift (inverseImageBaseProjection a))
    (commShift_tensorRightPushforward (L := L))

/-- `kunnethSourceLeftSecond a b L` is a triangulated functor. -/
local instance isTriangulated_kunnethSourceLeftSecond :
    (kunnethSourceLeftSecond a b L).IsTriangulated :=
  @Functor.IsTriangulated.instComp _ _ _ _ _ _ _ _ _ _
    (derivedPushforwardCommShift (inverseImageBaseProjection a)) _
    (commShift_tensorRightPushforward (L := L)) _ _ _ _ _ _ _ _ _ _ _ _
    (derivedPushforwardIsTriangulated (inverseImageBaseProjection a))
    (isTriangulated_tensorRightPushforward (L := L))

/-- `kunnethSourceLeft a b L` commutes with shifts. -/
local instance commShift_kunnethSourceLeft : (kunnethSourceLeft a b L).CommShift ℤ :=
  @Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _
    (commShift_kunnethSourceFirst a) (commShift_kunnethSourceLeftSecond a b L)

/-- `kunnethSourceLeft a b L` is a triangulated functor. -/
local instance isTriangulated_kunnethSourceLeft : (kunnethSourceLeft a b L).IsTriangulated :=
  @Functor.IsTriangulated.instComp _ _ _ _ _ _ _ _ _ _
    (commShift_kunnethSourceFirst a) _ (commShift_kunnethSourceLeftSecond a b L)
    _ _ _ _ _ _ _ _ _ _ _ _
    (isTriangulated_kunnethSourceFirst a) (isTriangulated_kunnethSourceLeftSecond a b L)

/-- `kunnethTargetLeft a b L` commutes with shifts. -/
local instance commShift_kunnethTargetLeft : (kunnethTargetLeft a b L).CommShift ℤ :=
  @Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _
    (commShift_bifunctorPhiR a b L) (commShift_kunnethTargetSecond a b)

/-- `kunnethTargetLeft a b L` is a triangulated functor. -/
local instance isTriangulated_kunnethTargetLeft : (kunnethTargetLeft a b L).IsTriangulated :=
  @Functor.IsTriangulated.instComp _ _ _ _ _ _ _ _ _ _
    (commShift_bifunctorPhiR a b L) _ (commShift_kunnethTargetSecond a b)
    _ _ _ _ _ _ _ _ _ _ _ _
    (isTriangulated_bifunctorPhiR a b L) (isTriangulated_kunnethTargetSecond a b)

/-- The target of the Künneth map as a functor of the first complex on the category of complexes:
`𝓕^• ↦ Rf_*Tot(𝓕^• ⊠ 𝓖^•)`, the total complex formed over `f^{-1}𝒪_S`. -/
abbrev kunnethTargetLeftComplex :
    CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ ⥤
      DerivedModules (SheafedSpace.sheaf S.toRingedSpace) :=
  ((boxProductRelativeCurried a b).map₂HomologicalComplex (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).flip.obj L ⋙ DerivedCategory.Q ⋙
    derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection (pullback.fst a b ≫ a))

/-- The Künneth map, as a natural transformation of functors of the first complex on the category
of complexes. Its naturality is `relativeBoxKunnethMapUnbounded_natural_left`. -/
def relativeBoxKunnethLeftTrans :
    (toInverseImageModules a).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⋙
        kunnethSourceLeftSecond a b L ⟶
      kunnethTargetLeftComplex a b L where
  app K := relativeBoxKunnethMapUnbounded a b K L
  naturality _ _ φ := relativeBoxKunnethMapUnbounded_natural_left a b φ L

/-- The source functor, precomposed with the quotient, is the source of the Künneth map on the
category of complexes. -/
def kunnethSourceLeftIso :
    HomotopyCategory.quotient _ _ ⋙ kunnethSourceLeft a b L ≅
      (toInverseImageModules a).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⋙
        kunnethSourceLeftSecond a b L :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (@Functor.mapHomotopyCategoryFactors _ _ _ _ _ _ Abelian.toPreadditive
          (toInverseImageModules a) ⟨fun {_ _ _ _} => Functor.map_add (toInverseImageModules a)⟩
          (ComplexShape.up ℤ)) DerivedCategory.Qh ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso _)) _ ≪≫
    Functor.associator _ _ _

/-- The target functor, precomposed with the quotient, is the target of the Künneth map on the
category of complexes. -/
def kunnethTargetLeftIso :
    kunnethTargetLeftComplex a b L ≅
      HomotopyCategory.quotient _ _ ⋙ kunnethTargetLeft a b L :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso _).symm _ ≪≫
      Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (bifunctorPhiRFactors (boxProductRelativeCurried a b) L).symm _ ≪≫
    Functor.associator _ _ _

/-- **The Künneth map as a natural transformation of triangulated functors of the first complex,
on the homotopy category.** -/
def kunnethLeftNatTrans : kunnethSourceLeft a b L ⟶ kunnethTargetLeft a b L :=
  CategoryTheory.Quotient.natTransLift _
    ((kunnethSourceLeftIso a b L).hom ≫ relativeBoxKunnethLeftTrans a b L ≫
      (kunnethTargetLeftIso a b L).hom)

/-- A composite with isomorphisms on both sides is invertible exactly when its middle factor is. -/
private theorem isIso_comp_comp_iff_of_isIso {C : Type*} [Category C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) [IsIso f] [IsIso h] : IsIso (f ≫ g ≫ h) ↔ IsIso g := by
  rw [isIso_comp_left_iff, isIso_comp_right_iff]

/-- The natural transformation is invertible at a complex exactly when the Künneth map is. -/
theorem isIso_kunnethLeftNatTrans_app_iff
    (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ) :
    IsIso ((kunnethLeftNatTrans a b L).app ((HomotopyCategory.quotient _ _).obj K)) ↔
      IsIso (relativeBoxKunnethMapUnbounded a b K L) := by
  have h₁ := ((kunnethSourceLeftIso a b L).app K).isIso_hom
  have h₂ := ((kunnethTargetLeftIso a b L).app K).isIso_hom
  show IsIso ((kunnethSourceLeftIso a b L).hom.app K ≫ relativeBoxKunnethMapUnbounded a b K L ≫
    (kunnethTargetLeftIso a b L).hom.app K) ↔ _
  exact @isIso_comp_comp_iff_of_isIso _ _ _ _ _ _ _ _ _ h₁ h₂

/-- **Dévissage of the unbounded Künneth map in the first complex.** If the Künneth map is
invertible at every pair `(E[-i], 𝓖^•)` with `Pa E`, it is invertible at every pair `(𝓕^•, 𝓖^•)`
with `𝓕^•` strictly concentrated in degrees `[n, m]` and `Pa` holding at its terms there. -/
theorem isIso_relativeBoxKunnethMapUnbounded_of_isIso_single_left
    (Pa : FiniteOrderDifferentialOperatorCategory a → Prop)
    (hsingle : ∀ (i : ℤ) (E : FiniteOrderDifferentialOperatorCategory a), Pa E →
      IsIso (relativeBoxKunnethMapUnbounded a b
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj E) L))
    (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ) (n m : ℤ)
    [K.IsStrictlyGE n] [K.IsStrictlyLE m] (hK : ∀ i, n ≤ i → i ≤ m → Pa (K.X i)) :
    IsIso (relativeBoxKunnethMapUnbounded a b K L) :=
  (isIso_kunnethLeftNatTrans_app_iff a b L K).1
    (Stacks.HomotopyDevissage.isIso_app_quotient_obj_of_isStrictlyLE _ _
      (kunnethLeftNatTrans a b L) Pa
      (fun i E hE => (isIso_kunnethLeftNatTrans_app_iff a b L _).2 (hsingle i E hE)) K n m hK)

end Left

section Right

variable (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)

/-- The functor `M ↦ Ra_*𝓕^• ⊗^𝐋_{𝒪_S} M` commutes with shifts. -/
local instance commShift_tensorLeftPushforward :
    ((derivedTensorProductFunctor.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)).obj
        ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a)).obj
          (DerivedCategory.Q.obj (leftComplex a K)))).CommShift ℤ :=
  (canonicalDerivedTensorProduct (SheafedSpace.sheaf S.toRingedSpace)).commShift_right _

/-- The functor `M ↦ Ra_*𝓕^• ⊗^𝐋_{𝒪_S} M` is a triangulated functor. -/
local instance isTriangulated_tensorLeftPushforward :
    ((derivedTensorProductFunctor.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)).obj
        ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a)).obj
          (DerivedCategory.Q.obj (leftComplex a K)))).IsTriangulated :=
  (canonicalDerivedTensorProduct (SheafedSpace.sheaf S.toRingedSpace)).exact_right _

/-- The second half of the source functor of the second complex:
`M ↦ Ra_*𝓕^• ⊗^𝐋_{𝒪_S} Rb_*M`. -/
abbrev kunnethSourceRightSecond :
    DerivedCategory (_root_.Modules (inverseImageBase b)) ⥤
      DerivedModules (SheafedSpace.sheaf S.toRingedSpace) :=
  derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b) ⋙
    (derivedTensorProductFunctor.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)).obj
        ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a)).obj
          (DerivedCategory.Q.obj (leftComplex a K)))

/-- The source of the Künneth map as a triangulated functor of the second complex, on the
homotopy category: `𝓖^• ↦ Ra_*𝓕^• ⊗^𝐋_{𝒪_S} Rb_*𝓖^•`. -/
abbrev kunnethSourceRight :
    HomotopyCategory (FiniteOrderDifferentialOperatorCategory b) (ComplexShape.up ℤ) ⥤
      DerivedModules (SheafedSpace.sheaf S.toRingedSpace) :=
  kunnethSourceFirst b ⋙ kunnethSourceRightSecond a b K

/-- The target of the Künneth map as a triangulated functor of the second complex, on the
homotopy category: `𝓖^• ↦ Rf_*Tot(𝓕^• ⊠ 𝓖^•)`. -/
abbrev kunnethTargetRight :
    HomotopyCategory (FiniteOrderDifferentialOperatorCategory b) (ComplexShape.up ℤ) ⥤
      DerivedModules (SheafedSpace.sheaf S.toRingedSpace) :=
  bifunctorPhi (boxProductRelativeCurried a b) K ⋙ kunnethTargetSecond a b

/-- `kunnethSourceRightSecond a b K` commutes with shifts. -/
local instance commShift_kunnethSourceRightSecond :
    (kunnethSourceRightSecond a b K).CommShift ℤ :=
  @Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _
    (derivedPushforwardCommShift (inverseImageBaseProjection b))
    (commShift_tensorLeftPushforward (K := K))

/-- `kunnethSourceRightSecond a b K` is a triangulated functor. -/
local instance isTriangulated_kunnethSourceRightSecond :
    (kunnethSourceRightSecond a b K).IsTriangulated :=
  @Functor.IsTriangulated.instComp _ _ _ _ _ _ _ _ _ _
    (derivedPushforwardCommShift (inverseImageBaseProjection b)) _
    (commShift_tensorLeftPushforward (K := K)) _ _ _ _ _ _ _ _ _ _ _ _
    (derivedPushforwardIsTriangulated (inverseImageBaseProjection b))
    (isTriangulated_tensorLeftPushforward (K := K))

/-- `kunnethSourceRight a b K` commutes with shifts. -/
local instance commShift_kunnethSourceRight : (kunnethSourceRight a b K).CommShift ℤ :=
  @Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _
    (commShift_kunnethSourceFirst b) (commShift_kunnethSourceRightSecond a b K)

/-- `kunnethSourceRight a b K` is a triangulated functor. -/
local instance isTriangulated_kunnethSourceRight : (kunnethSourceRight a b K).IsTriangulated :=
  @Functor.IsTriangulated.instComp _ _ _ _ _ _ _ _ _ _
    (commShift_kunnethSourceFirst b) _ (commShift_kunnethSourceRightSecond a b K)
    _ _ _ _ _ _ _ _ _ _ _ _
    (isTriangulated_kunnethSourceFirst b) (isTriangulated_kunnethSourceRightSecond a b K)

/-- `kunnethTargetRight a b K` commutes with shifts. -/
local instance commShift_kunnethTargetRight : (kunnethTargetRight a b K).CommShift ℤ :=
  @Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _
    (commShift_bifunctorPhi a b K) (commShift_kunnethTargetSecond a b)

/-- `kunnethTargetRight a b K` is a triangulated functor. -/
local instance isTriangulated_kunnethTargetRight : (kunnethTargetRight a b K).IsTriangulated :=
  @Functor.IsTriangulated.instComp _ _ _ _ _ _ _ _ _ _
    (commShift_bifunctorPhi a b K) _ (commShift_kunnethTargetSecond a b)
    _ _ _ _ _ _ _ _ _ _ _ _
    (isTriangulated_bifunctorPhi a b K) (isTriangulated_kunnethTargetSecond a b)

/-- The target of the Künneth map as a functor of the second complex on the category of
complexes: `𝓖^• ↦ Rf_*Tot(𝓕^• ⊠ 𝓖^•)`, the total complex formed over `f^{-1}𝒪_S`. -/
abbrev kunnethTargetRightComplex :
    CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ ⥤
      DerivedModules (SheafedSpace.sheaf S.toRingedSpace) :=
  ((boxProductRelativeCurried a b).map₂HomologicalComplex (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K ⋙ DerivedCategory.Q ⋙
    derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection (pullback.fst a b ≫ a))

/-- The Künneth map, as a natural transformation of functors of the second complex on the
category of complexes. Its naturality is `relativeBoxKunnethMapUnbounded_natural_right`. -/
def relativeBoxKunnethRightTrans :
    (toInverseImageModules b).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⋙
        kunnethSourceRightSecond a b K ⟶
      kunnethTargetRightComplex a b K where
  app L := relativeBoxKunnethMapUnbounded a b K L
  naturality _ _ φ := relativeBoxKunnethMapUnbounded_natural_right a b K φ

/-- The source functor, precomposed with the quotient, is the source of the Künneth map on the
category of complexes. -/
def kunnethSourceRightIso :
    HomotopyCategory.quotient _ _ ⋙ kunnethSourceRight a b K ≅
      (toInverseImageModules b).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⋙
        kunnethSourceRightSecond a b K :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (@Functor.mapHomotopyCategoryFactors _ _ _ _ _ _ Abelian.toPreadditive
          (toInverseImageModules b) ⟨fun {_ _ _ _} => Functor.map_add (toInverseImageModules b)⟩
          (ComplexShape.up ℤ)) DerivedCategory.Qh ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso _)) _ ≪≫
    Functor.associator _ _ _

/-- The target functor, precomposed with the quotient, is the target of the Künneth map on the
category of complexes. -/
def kunnethTargetRightIso :
    kunnethTargetRightComplex a b K ≅
      HomotopyCategory.quotient _ _ ⋙ kunnethTargetRight a b K :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso _).symm _ ≪≫
      Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (bifunctorPhiFactors (boxProductRelativeCurried a b) K).symm _ ≪≫
    Functor.associator _ _ _

/-- **The Künneth map as a natural transformation of triangulated functors of the second
complex, on the homotopy category.** -/
def kunnethRightNatTrans : kunnethSourceRight a b K ⟶ kunnethTargetRight a b K :=
  CategoryTheory.Quotient.natTransLift _
    ((kunnethSourceRightIso a b K).hom ≫ relativeBoxKunnethRightTrans a b K ≫
      (kunnethTargetRightIso a b K).hom)

/-- The natural transformation is invertible at a complex exactly when the Künneth map is. -/
theorem isIso_kunnethRightNatTrans_app_iff
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ) :
    IsIso ((kunnethRightNatTrans a b K).app ((HomotopyCategory.quotient _ _).obj L)) ↔
      IsIso (relativeBoxKunnethMapUnbounded a b K L) := by
  have h₁ := ((kunnethSourceRightIso a b K).app L).isIso_hom
  have h₂ := ((kunnethTargetRightIso a b K).app L).isIso_hom
  show IsIso ((kunnethSourceRightIso a b K).hom.app L ≫ relativeBoxKunnethMapUnbounded a b K L ≫
    (kunnethTargetRightIso a b K).hom.app L) ↔ _
  exact @isIso_comp_comp_iff_of_isIso _ _ _ _ _ _ _ _ _ h₁ h₂

/-- **Dévissage of the unbounded Künneth map in the second complex.** If the Künneth map is
invertible at every pair `(𝓕^•, E'[-j])` with `Pb E'`, it is invertible at every pair
`(𝓕^•, 𝓖^•)` with `𝓖^•` strictly concentrated in degrees `[n, m]` and `Pb` holding at its terms
there. -/
theorem isIso_relativeBoxKunnethMapUnbounded_of_isIso_single_right
    (Pb : FiniteOrderDifferentialOperatorCategory b → Prop)
    (hsingle : ∀ (j : ℤ) (E' : FiniteOrderDifferentialOperatorCategory b), Pb E' →
      IsIso (relativeBoxKunnethMapUnbounded a b K
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj E')))
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ) (n m : ℤ)
    [L.IsStrictlyGE n] [L.IsStrictlyLE m] (hL : ∀ j, n ≤ j → j ≤ m → Pb (L.X j)) :
    IsIso (relativeBoxKunnethMapUnbounded a b K L) :=
  (isIso_kunnethRightNatTrans_app_iff a b K L).1
    (Stacks.HomotopyDevissage.isIso_app_quotient_obj_of_isStrictlyLE _ _
      (kunnethRightNatTrans a b K) Pb
      (fun j E' hE' => (isIso_kunnethRightNatTrans_app_iff a b K _).2 (hsingle j E' hE')) L n m hL)

end Right

/-! ### The dévissage in both complexes -/

/-- **Dévissage of the unbounded Künneth map in both complexes.** If the Künneth map is
invertible at every pair `(E[-i], E'[-j])` of complexes concentrated in one degree with `Pa E` and
`Pb E'`, it is invertible at every pair `(𝓕^•, 𝓖^•)` of strictly bounded complexes whose terms in
their ranges satisfy `Pa` and `Pb`. The induction runs first in `𝓕^•` at a single `E'[-j]`, then
in `𝓖^•`. -/
theorem isIso_relativeBoxKunnethMapUnbounded_of_isIso_single
    (Pa : FiniteOrderDifferentialOperatorCategory a → Prop)
    (Pb : FiniteOrderDifferentialOperatorCategory b → Prop)
    (hsingle : ∀ (i j : ℤ) (E : FiniteOrderDifferentialOperatorCategory a)
      (E' : FiniteOrderDifferentialOperatorCategory b), Pa E → Pb E' →
      IsIso (relativeBoxKunnethMapUnbounded a b
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj E)
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj E')))
    (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ)
    (n₁ m₁ n₂ m₂ : ℤ) [K.IsStrictlyGE n₁] [K.IsStrictlyLE m₁] [L.IsStrictlyGE n₂]
    [L.IsStrictlyLE m₂] (hK : ∀ i, n₁ ≤ i → i ≤ m₁ → Pa (K.X i))
    (hL : ∀ j, n₂ ≤ j → j ≤ m₂ → Pb (L.X j)) :
    IsIso (relativeBoxKunnethMapUnbounded a b K L) :=
  isIso_relativeBoxKunnethMapUnbounded_of_isIso_single_right a b K Pb
    (fun j E' hE' => isIso_relativeBoxKunnethMapUnbounded_of_isIso_single_left a b
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj E') Pa
      (fun i E hE => hsingle i j E E' hE hE') K n₁ m₁ hK) L n₂ m₂ hL

/-- **Dévissage of the relative Künneth map of [Stacks, Tag 0G4B].** Let `Pa` and `Pb` be
predicates on finite-order differential operators on `X/S` and on `Y/S`. If the relative Künneth
map is invertible at every pair `(E[-i], E'[-j])` of complexes concentrated in one degree with
`Pa E` and `Pb E'`, then it is invertible at every pair `(𝓕^•, 𝓖^•)` with `𝓕^•` strictly
concentrated in degrees `[n₁, m₁]`, `𝓖^•` strictly concentrated in degrees `[n₂, m₂]`, and the
terms in those degrees satisfying `Pa` and `Pb`.

This is the dévissage of the proof of [Stacks, Tag 0FLT], along the stupid truncations: by
`isIso_relativeBoxKunnethMap_iff` the map is invertible exactly when the Künneth map with the
target total complex formed over `f^{-1}𝒪_S` is. That map is a natural transformation of
triangulated functors of each complex on the homotopy category, and
`Stacks.HomotopyDevissage.isIso_app_quotient_obj_of_isStrictlyLE` runs the induction. -/
theorem isIso_relativeBoxKunnethMap_of_isIso_single
    (Pa : FiniteOrderDifferentialOperatorCategory a → Prop)
    (Pb : FiniteOrderDifferentialOperatorCategory b → Prop)
    (hsingle : ∀ (i j : ℤ) (E : FiniteOrderDifferentialOperatorCategory a)
      (E' : FiniteOrderDifferentialOperatorCategory b), Pa E → Pb E' →
      IsIso (relativeBoxKunnethMap a b ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj E)
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj E') i j))
    (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ)
    (n₁ m₁ n₂ m₂ : ℤ) [K.IsStrictlyGE n₁] [K.IsStrictlyLE m₁] [L.IsStrictlyGE n₂]
    [L.IsStrictlyLE m₂] (hK : ∀ i, n₁ ≤ i → i ≤ m₁ → Pa (K.X i))
    (hL : ∀ j, n₂ ≤ j → j ≤ m₂ → Pb (L.X j)) :
    IsIso (relativeBoxKunnethMap a b K L n₁ n₂) :=
  (isIso_relativeBoxKunnethMap_iff a b K L n₁ n₂).2
    (isIso_relativeBoxKunnethMapUnbounded_of_isIso_single a b Pa Pb
      (fun i j E E' hE hE' => (isIso_relativeBoxKunnethMap_iff a b _ _ i j).1
        (hsingle i j E E' hE hE')) K L n₁ m₁ n₂ m₂ hK hL)

end Stacks.Cohomology.BoxKunneth
