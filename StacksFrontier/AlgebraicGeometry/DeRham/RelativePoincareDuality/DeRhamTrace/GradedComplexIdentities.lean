module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.NaiveCupProductInverseImageBase
public import StacksFrontier.Algebra.Homology.TruncatedTotalProduct
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.ToTensorShiftedPairing
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.GradedComplexNaiveShift
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.GradedToTensorShift
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.GradedComplexSingleProduct
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.GradedShiftClass
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.HodgeCupProduct
public import StacksFrontier.AlgebraicGeometry.DeRham.WedgeComponentRestrictScalars

/-!
# The graded pieces of the de Rham multiplication, through `(X, 𝒪_X)`

Let `ι : (X, 𝒪_X) ⟶ (X, f⁻¹𝒪_S)` be the morphism of ringed spaces whose direct image is
restriction of scalars. The product of the graded pieces `Ω^p[-p] ⊗ Ω^q[-q] ⟶ Ω^•_{X/S}` of the de
Rham complex (`StacksDraft.StupidTruncation.gradedMul`) is, through `ι_*`, the naive cup product
of `Ω^p[-p]` and `Ω^q[-q]` (as complexes of `𝒪_X`-modules) followed by `ι_*` of the wedge product
`Ω^p ⊗_{𝒪_X} Ω^q ⟶ Ω^n` and by the inclusion of the top piece. Pairings in the derived category of
`f⁻¹𝒪_S`-modules induced in this way by pairings of complexes of `𝒪_X`-modules are stable under
shifting, and their commutation with the shift of the second variable and of the target is the
pairing induced into the shifted target.

## Main definitions

* `AlgebraicGeometry.RelativeDualitySituation.topComplexX`: `Ω^n` placed in degree `n`.
* `AlgebraicGeometry.RelativeDualitySituation.topComplexToDeRham`: the inclusion of the top piece
  `ι_*(Ω^n[-n]) ⟶ Ω^•_{X/S}`.
* `AlgebraicGeometry.RelativeDualitySituation.topComplexToDeRhamShift`: its shift by `2n`.
* `AlgebraicGeometry.RelativeDualitySituation.gradedWedgeX`: the wedge product
  `Tot(Ω^p[-p] ⊗ Ω^q[-q]) ⟶ Ω^n[-n]` of complexes of `𝒪_X`-modules.
* `AlgebraicGeometry.RelativeDualitySituation.rightShiftedPairingX`: the shift of a pairing of
  complexes in its second variable.
* `AlgebraicGeometry.RelativeDualitySituation.inducedDeRhamPairing`,
  `AlgebraicGeometry.RelativeDualitySituation.inducedShiftedDeRhamPairing`: the pairings in the
  derived category of `f⁻¹𝒪_S`-modules induced by a pairing of complexes of `𝒪_X`-modules.
* `AlgebraicGeometry.RelativeDualitySituation.formsSingleIso`: `Ω^p[-p] ≅ ι_*(Ω^p[-p])`.

## Main results

* `RelativeDualitySituation.pairingCompatible_shiftedPairing_inducedDeRhamPairing`
* `RelativeDualitySituation.pairingCompatible_commShift_inducedDeRhamPairing`
* `RelativeDualitySituation.pairingCompatible_gradedMul_inducedDeRhamPairing`

## Implementation notes

The three compatibilities are first proved for complexes and then read in the derived category
through the naturality of the canonical map to the total tensor complex and its compatibility
with the shifts. For complexes they are instances of statements about an arbitrary family of
maps `F'(GX, GY) ⟶ G F(X, Y)`
(`CochainComplex.mapBifunctorMap_commShiftIso_shiftedPairing_eq_of_lax`,
`CochainComplex.mapBifunctorMap_commShiftIso_rightShift_eq_of_lax`,
`StacksDraft.StupidTruncation.mapBifunctorMap_comp_comp_map_comp_eq_gradedMul`), applied to the
lax comparison of restriction of scalars along `f⁻¹𝒪_S ⟶ 𝒪_X`. On the summand `Ω^p ⊗ Ω^q` the
multiplication of `Ω^•_{X/S}` is that lax comparison followed by the wedge product over `𝒪_X`
(`AlgebraicGeometry.SheafOfModules.laxComparison_comp_restrictScalars_mulSheaf`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Stacks.StandardDerivedModel
open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback renaming Modules → ModulesOn
open Stacks.DeRhamDirectImage (inverseImageBase toInverseImageBase pushedCupMap)
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces (pushforwardComplex naiveCupProduct)
open Stacks.Cohomology.DerivedPullbackTensor (tensorComplexBifunctorOn)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor canonicalDerivedTensorProduct)

universe u

namespace AlgebraicGeometry.RelativeDualitySituation

attribute [local implicit_reducible] TopCat.Sheaf StacksDraft.KFlat.modulePullback
  StacksDraft.KFlat.modulePushforward CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

variable (D : RelativeDualitySituation.{u})

/-- `Ω^k_{X/S}` placed in degree `a`, as a complex of `𝒪_X`-modules. -/
abbrev formsComplexX (k a : ℤ) : CochainComplex (ModulesOn D.X.toRingedSpace) ℤ :=
  (HomologicalComplex.single _ (ComplexShape.up ℤ) a).obj
    (Scheme.Hom.relativeDifferentialForms D.f k)

/-- `Ω^n_{X/S}` placed in degree `n`. -/
abbrev topComplexX : CochainComplex (ModulesOn D.X.toRingedSpace) ℤ :=
  D.formsComplexX D.n D.n

/-- **The inclusion of the top piece**, `ι_*(Ω^n[-n]) ⟶ Ω^•_{X/S}`. -/
def topComplexToDeRham :
    (pushforwardComplex (toInverseImageBase D.f)).obj D.topComplexX ⟶
      D.deRhamCx.extend ComplexShape.embeddingUpNat :=
  (HomologicalComplex.singleMapHomologicalComplex (StacksDraft.KFlat.modulePushforward
    (toInverseImageBase D.f)) (ComplexShape.up ℤ) D.n).hom.app
      (Scheme.Hom.relativeDifferentialForms D.f D.n) ≫ D.topFormsToDeRham

/-- The inclusion of the top piece, shifted by `2n`: `ι_*(Ω^n[-n][2n]) ⟶ Ω^•_{X/S}[2n]`. -/
def topComplexToDeRhamShift :
    (pushforwardComplex (toInverseImageBase D.f)).obj (D.topComplexX⟦(2 * D.n : ℤ)⟧) ⟶
      (D.deRhamCx.extend ComplexShape.embeddingUpNat)⟦(2 * D.n : ℤ)⟧ :=
  ((pushforwardComplex (toInverseImageBase D.f)).commShiftIso (2 * D.n : ℤ)).hom.app
      D.topComplexX ≫ D.topComplexToDeRham⟦(2 * D.n : ℤ)⟧'

/-- **The wedge product `Tot(Ω^p[-p] ⊗ Ω^q[-q]) ⟶ Ω^n[-n]`** of complexes of `𝒪_X`-modules, for
`p + q = n`. -/
def gradedWedgeX (p q : ℤ) (hpq : p + q = D.n) :
    ((tensorComplexBifunctorOn D.X.toRingedSpace).obj (D.formsComplexX p p)).obj
      (D.formsComplexX q q) ⟶ D.topComplexX :=
  (HomologicalComplex.mapBifunctorSingleSingleIso
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} D.X.toRingedSpace.sheaf)
        _ _ p q).hom ≫
    (HomologicalComplex.single _ (ComplexShape.up ℤ) (p + q)).map
      ((Scheme.Hom.relativeDifferentialFormsAlgebra D.f).mulSheaf p q) ≫
    eqToHom (by rw [hpq])

/-- The shift `Tot(A ⊗ B[m]) ≅ Tot(A ⊗ B)[m] ⟶ W[m]` of a pairing of complexes of `𝒪_X`-modules in
its second variable. -/
def rightShiftedPairingX {A B W : CochainComplex (ModulesOn D.X.toRingedSpace) ℤ}
    (h : ((tensorComplexBifunctorOn D.X.toRingedSpace).obj A).obj B ⟶ W) (m : ℤ) :
    ((tensorComplexBifunctorOn D.X.toRingedSpace).obj A).obj (B⟦m⟧) ⟶ W⟦m⟧ :=
  (((tensorComplexBifunctorOn D.X.toRingedSpace).obj A).commShiftIso m).hom.app B ≫ h⟦m⟧'

/-- **The pairing induced by a pairing of complexes of `𝒪_X`-modules into `Ω^n[-n]`**:
`Q(ι_*A) ⊗^L Q(ι_*B) ⟶ Q(Tot(ι_*A ⊗ ι_*B)) ⟶ Q(ι_*Tot(A ⊗ B)) ⟶ Q(ι_*(Ω^n[-n])) ⟶ Q(Ω^•)`, the
canonical map to the total tensor complex followed by the naive cup product, `ι_*h` and the
inclusion of the top piece. -/
def inducedDeRhamPairing {A B : CochainComplex (ModulesOn D.X.toRingedSpace) ℤ}
    (h : ((tensorComplexBifunctorOn D.X.toRingedSpace).obj A).obj B ⟶ D.topComplexX) :
    ((derivedTensorProductFunctor (inverseImageBase D.f).sheaf).obj
        (DerivedCategory.Q.obj ((pushforwardComplex (toInverseImageBase D.f)).obj A))).obj
        (DerivedCategory.Q.obj ((pushforwardComplex (toInverseImageBase D.f)).obj B)) ⟶
      DerivedCategory.Q.obj (D.deRhamCx.extend ComplexShape.embeddingUpNat) :=
  (canonicalDerivedTensorProduct (inverseImageBase D.f).sheaf).toTensor _ _ ≫
    DerivedCategory.Q.map (naiveCupProduct (toInverseImageBase D.f) A B ≫
      (pushforwardComplex (toInverseImageBase D.f)).map h ≫ D.topComplexToDeRham)

/-- **The induced pairing into the shifted target** `Q(ι_*A) ⊗^L Q(ι_*(B[2n])) ⟶ Q(Ω^•)[2n]` of the
shift `Tot(A ⊗ B[2n]) ⟶ Ω^n[-n][2n]` of `h` in its second variable. -/
def inducedShiftedDeRhamPairing {A B : CochainComplex (ModulesOn D.X.toRingedSpace) ℤ}
    (h : ((tensorComplexBifunctorOn D.X.toRingedSpace).obj A).obj B ⟶ D.topComplexX) :
    ((derivedTensorProductFunctor (inverseImageBase D.f).sheaf).obj
        (DerivedCategory.Q.obj ((pushforwardComplex (toInverseImageBase D.f)).obj A))).obj
        (DerivedCategory.Q.obj ((pushforwardComplex (toInverseImageBase D.f)).obj
          (B⟦(2 * D.n : ℤ)⟧))) ⟶
      (DerivedCategory.Q.obj (D.deRhamCx.extend ComplexShape.embeddingUpNat))⟦(2 * D.n : ℤ)⟧ :=
  (canonicalDerivedTensorProduct (inverseImageBase D.f).sheaf).toTensor _ _ ≫
    DerivedCategory.Q.map (naiveCupProduct (toInverseImageBase D.f) A (B⟦(2 * D.n : ℤ)⟧) ≫
      (pushforwardComplex (toInverseImageBase D.f)).map (D.rightShiftedPairingX h (2 * D.n : ℤ)) ≫
      D.topComplexToDeRhamShift) ≫
    (DerivedCategory.Q.commShiftIso (2 * D.n : ℤ)).hom.app
      (D.deRhamCx.extend ComplexShape.embeddingUpNat)

/-- The induced pairing written with `Stacks.DeRhamDirectImage.pushedCupMap`. -/
theorem inducedDeRhamPairing_eq_pushedCupMap {A B : CochainComplex (ModulesOn D.X.toRingedSpace) ℤ}
    (h : ((tensorComplexBifunctorOn D.X.toRingedSpace).obj A).obj B ⟶ D.topComplexX) :
    D.inducedDeRhamPairing h =
      (canonicalDerivedTensorProduct (inverseImageBase D.f).sheaf).toTensor _ _ ≫
        DerivedCategory.Q.map (pushedCupMap D.f h ≫ D.topComplexToDeRham) :=
  congrArg (fun x => _ ≫ DerivedCategory.Q.map x) (Category.assoc _ _ _).symm

/-- The induced pairing into the shifted target written with
`Stacks.DeRhamDirectImage.pushedCupMap`. -/
theorem inducedShiftedDeRhamPairing_eq_pushedCupMap
    {A B : CochainComplex (ModulesOn D.X.toRingedSpace) ℤ}
    (h : ((tensorComplexBifunctorOn D.X.toRingedSpace).obj A).obj B ⟶ D.topComplexX) :
    D.inducedShiftedDeRhamPairing h =
      (canonicalDerivedTensorProduct (inverseImageBase D.f).sheaf).toTensor _ _ ≫
        DerivedCategory.Q.map (pushedCupMap D.f (D.rightShiftedPairingX h (2 * D.n : ℤ)) ≫
          D.topComplexToDeRhamShift) ≫
        (DerivedCategory.Q.commShiftIso (2 * D.n : ℤ)).hom.app
          (D.deRhamCx.extend ComplexShape.embeddingUpNat) :=
  congrArg (fun x => _ ≫ DerivedCategory.Q.map x ≫ _) (Category.assoc _ _ _).symm

/-- **The shift of an induced pairing, through `Q(ι_*(A[a])) ≅ Q(ι_*A)[a]` and
`Q(ι_*(B[b])) ≅ Q(ι_*B)[b]`, is the pairing induced by the shift.** -/
theorem toTensor_shiftedPairing_inducedDeRhamPairing
    {A B : CochainComplex (ModulesOn D.X.toRingedSpace) ℤ}
    (h : ((tensorComplexBifunctorOn D.X.toRingedSpace).obj A).obj B ⟶ D.topComplexX) (a b : ℤ)
    (hab : a + b = 0) :
    letI := (canonicalDerivedTensorProduct (inverseImageBase D.f).sheaf).commShift₂
    ((derivedTensorProductFunctor (inverseImageBase D.f).sheaf).map
        (DerivedCategory.Q.map
            (((pushforwardComplex (toInverseImageBase D.f)).commShiftIso a).hom.app A) ≫
          (DerivedCategory.Q.commShiftIso a).hom.app
            ((pushforwardComplex (toInverseImageBase D.f)).obj A))).app
        (DerivedCategory.Q.obj ((pushforwardComplex (toInverseImageBase D.f)).obj (B⟦b⟧))) ≫
      ((derivedTensorProductFunctor (inverseImageBase D.f).sheaf).obj
          ((DerivedCategory.Q.obj ((pushforwardComplex (toInverseImageBase D.f)).obj A))⟦a⟧)).map
        (DerivedCategory.Q.map
            (((pushforwardComplex (toInverseImageBase D.f)).commShiftIso b).hom.app B) ≫
          (DerivedCategory.Q.commShiftIso b).hom.app
            ((pushforwardComplex (toInverseImageBase D.f)).obj B)) ≫
      (derivedTensorProductFunctor (inverseImageBase D.f).sheaf).shiftedPairing
        (D.inducedDeRhamPairing h) a b hab =
    D.inducedDeRhamPairing ((tensorComplexBifunctorOn D.X.toRingedSpace).shiftedPairing h a b
      hab) := by
  let := (canonicalDerivedTensorProduct (inverseImageBase D.f).sheaf).commShift₂
  have k1 := Stacks.Cohomology.DerivedPullbackTensor.shiftedPairing_toTensor_comp
    (inverseImageBase D.f) (pushedCupMap D.f h ≫ D.topComplexToDeRham) a b hab
  have k2 := (canonicalDerivedTensorProduct (inverseImageBase D.f).sheaf).toTensor_naturality
    (((pushforwardComplex (toInverseImageBase D.f)).commShiftIso a).hom.app A)
    (((pushforwardComplex (toInverseImageBase D.f)).commShiftIso b).hom.app B)
  have k3 := Stacks.DeRhamDirectImage.mapBifunctorMap_commShiftIso_shiftedPairing_pushedCupMap
    D.f h a b hab
  have k4 := Functor.shiftedPairing_comp (tensorComplexBifunctorOn (inverseImageBase D.f))
    (pushedCupMap D.f h) D.topComplexToDeRham a b hab
  refine Functor.map_comp_app_map_comp_eq
    (derivedTensorProductFunctor (inverseImageBase D.f).sheaf) _ _ _ _ _ _ _ (Eq.trans ?_ k1) ?_
  · exact congrArg (_ ≫ _ ≫ ·) (congrArg
      (fun φ => (derivedTensorProductFunctor (inverseImageBase D.f).sheaf).shiftedPairing φ a b hab)
      (inducedDeRhamPairing_eq_pushedCupMap D h))
  refine ((reassoc_of% k2) _).trans ?_
  refine Eq.trans ?_ (inducedDeRhamPairing_eq_pushedCupMap D _).symm
  refine (Category.assoc _ _ _).trans ?_
  exact Functor.comp_map_comp_map_eq DerivedCategory.Q _ _ _ _ ((congrArg (_ ≫ ·) k4).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ D.topComplexToDeRham) k3)))

/-- **The shift of an induced pairing is induced**, by the shift of the pairing of complexes of
`𝒪_X`-modules, up to isomorphisms of the paired objects. This is the compatibility of the
canonical map to the total tensor complex with the shifts
(`Stacks.Cohomology.DerivedPullbackTensor.shiftedPairing_toTensor_comp`) together with that of the
naive cup product along `ι`, which on each summand of the total complex is the lax comparison of
restriction of scalars. -/
theorem pairingCompatible_shiftedPairing_inducedDeRhamPairing
    {A B : CochainComplex (ModulesOn D.X.toRingedSpace) ℤ}
    (h : ((tensorComplexBifunctorOn D.X.toRingedSpace).obj A).obj B ⟶ D.topComplexX) (a b : ℤ)
    (hab : a + b = 0) :
    letI := (canonicalDerivedTensorProduct (inverseImageBase D.f).sheaf).commShift₂
    ∃ (e : (DerivedCategory.Q.obj ((pushforwardComplex (toInverseImageBase D.f)).obj A))⟦a⟧ ⟶
        DerivedCategory.Q.obj ((pushforwardComplex (toInverseImageBase D.f)).obj (A⟦a⟧)))
      (e' : DerivedCategory.Q.obj ((pushforwardComplex (toInverseImageBase D.f)).obj (B⟦b⟧)) ⟶
        (DerivedCategory.Q.obj ((pushforwardComplex (toInverseImageBase D.f)).obj B))⟦b⟧)
      (_ : IsIso e) (_ : IsIso e'),
      (derivedTensorProductFunctor (inverseImageBase D.f).sheaf).PairingCompatible
        ((derivedTensorProductFunctor (inverseImageBase D.f).sheaf).shiftedPairing
          (D.inducedDeRhamPairing h) a b hab)
        (D.inducedDeRhamPairing ((tensorComplexBifunctorOn D.X.toRingedSpace).shiftedPairing h a b
          hab)) e e' := by
  let := (canonicalDerivedTensorProduct (inverseImageBase D.f).sheaf).commShift₂
  exact ⟨_, _, inferInstance, inferInstance,
    Functor.pairingCompatible_inv_of_eq _ _
      (D.toTensor_shiftedPairing_inducedDeRhamPairing h a b hab)⟩

/-- The complex-level identity behind `toTensor_commShift_inducedDeRhamPairing`: the naive cup
product along `ι`, followed by `ι_*h` and the inclusion of the top piece, commutes with the shift
of the second variable and of the target. -/
theorem mapBifunctorMap_commShiftIso_rightShift_deRhamCup
    {A B : CochainComplex (ModulesOn D.X.toRingedSpace) ℤ}
    (h : ((tensorComplexBifunctorOn D.X.toRingedSpace).obj A).obj B ⟶ D.topComplexX) :
    HomologicalComplex.mapBifunctorMap (𝟙 ((pushforwardComplex (toInverseImageBase D.f)).obj A))
        (((pushforwardComplex (toInverseImageBase D.f)).commShiftIso (2 * D.n : ℤ)).hom.app B)
        (Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase D.f).sheaf)
          (ComplexShape.up ℤ) ≫
      (((tensorComplexBifunctorOn (inverseImageBase D.f)).obj
          ((pushforwardComplex (toInverseImageBase D.f)).obj A)).commShiftIso (2 * D.n : ℤ)).hom.app
        ((pushforwardComplex (toInverseImageBase D.f)).obj B) ≫
      (pushedCupMap D.f h ≫ D.topComplexToDeRham)⟦(2 * D.n : ℤ)⟧' =
    pushedCupMap D.f (D.rightShiftedPairingX h (2 * D.n : ℤ)) ≫ D.topComplexToDeRhamShift := by
  have k3 := Stacks.DeRhamDirectImage.mapBifunctorMap_commShiftIso_rightShift_pushedCupMap
    D.f h (2 * D.n : ℤ)
  have k3' := (reassoc_of% k3) (D.topComplexToDeRham⟦(2 * D.n : ℤ)⟧')
  have k5 := Functor.map_comp (shiftFunctor (CochainComplex (ModulesOn (inverseImageBase D.f)) ℤ)
    (2 * D.n : ℤ)) (pushedCupMap D.f h) D.topComplexToDeRham
  exact (congrArg (_ ≫ _ ≫ ·) k5).trans k3'

/-- **The commutation of an induced pairing with the shift of its second variable and target,
through `Q(ι_*(B[2n])) ≅ Q(ι_*B)[2n]`, is the induced pairing into the shifted target.** -/
theorem toTensor_commShift_inducedDeRhamPairing
    {A B : CochainComplex (ModulesOn D.X.toRingedSpace) ℤ}
    (h : ((tensorComplexBifunctorOn D.X.toRingedSpace).obj A).obj B ⟶ D.topComplexX) :
    letI := (canonicalDerivedTensorProduct (inverseImageBase D.f).sheaf).commShift₂
    ((derivedTensorProductFunctor (inverseImageBase D.f).sheaf).obj
        (DerivedCategory.Q.obj ((pushforwardComplex (toInverseImageBase D.f)).obj A))).map
        (DerivedCategory.Q.map
            (((pushforwardComplex (toInverseImageBase D.f)).commShiftIso (2 * D.n : ℤ)).hom.app B) ≫
          (DerivedCategory.Q.commShiftIso (2 * D.n : ℤ)).hom.app
            ((pushforwardComplex (toInverseImageBase D.f)).obj B)) ≫
      (((derivedTensorProductFunctor (inverseImageBase D.f).sheaf).obj
          (DerivedCategory.Q.obj
            ((pushforwardComplex (toInverseImageBase D.f)).obj A))).commShiftIso
            (2 * D.n : ℤ)).hom.app
          (DerivedCategory.Q.obj ((pushforwardComplex (toInverseImageBase D.f)).obj B)) ≫
        (D.inducedDeRhamPairing h)⟦(2 * D.n : ℤ)⟧' =
    D.inducedShiftedDeRhamPairing h := by
  let := (canonicalDerivedTensorProduct (inverseImageBase D.f).sheaf).commShift₂
  have k1 := Stacks.Cohomology.DerivedPullbackTensor.toTensor_shift_right (inverseImageBase D.f)
    ((pushforwardComplex (toInverseImageBase D.f)).obj A)
    ((pushforwardComplex (toInverseImageBase D.f)).obj B) (2 * D.n : ℤ)
  have k2 := (canonicalDerivedTensorProduct (inverseImageBase D.f).sheaf).toTensor_naturality
    (𝟙 ((pushforwardComplex (toInverseImageBase D.f)).obj A))
    (((pushforwardComplex (toInverseImageBase D.f)).commShiftIso (2 * D.n : ℤ)).hom.app B)
  have k4 := (DerivedCategory.Q.commShiftIso (2 * D.n : ℤ)).hom.naturality
    (pushedCupMap D.f h ≫ D.topComplexToDeRham)
  refine Eq.trans ?_ (D.inducedShiftedDeRhamPairing_eq_pushedCupMap h).symm
  refine (congrArg (fun φ => _ ≫ _ ≫ φ⟦(2 * D.n : ℤ)⟧')
    (D.inducedDeRhamPairing_eq_pushedCupMap h)).trans ?_
  refine Functor.map_comp_comp_shift_map_comp_eq _ (2 * D.n : ℤ) _ _ _ _ _ _ _ k1 ?_
  exact Functor.comp_comp_map_comp_eq DerivedCategory.Q _ _ _ _ _ _ _ _ _ _
    ((Functor.map_map_id_app_comp _ _ _ _).symm.trans k2) k4.symm
    (D.mapBifunctorMap_commShiftIso_rightShift_deRhamCup h)

/-- **The commutation of an induced pairing with the shift of its second variable and target is
induced**, up to an isomorphism of the second paired object: it is the induced pairing into the
shifted target. This is the compatibility of the canonical map to the total tensor complex with
the shift in the second variable (`Stacks.Cohomology.DerivedPullbackTensor.toTensor_shift_right`)
together with that of the naive cup product along `ι`. -/
theorem pairingCompatible_commShift_inducedDeRhamPairing
    {A B : CochainComplex (ModulesOn D.X.toRingedSpace) ℤ}
    (h : ((tensorComplexBifunctorOn D.X.toRingedSpace).obj A).obj B ⟶ D.topComplexX) :
    letI := (canonicalDerivedTensorProduct (inverseImageBase D.f).sheaf).commShift₂
    ∃ (e' : (DerivedCategory.Q.obj ((pushforwardComplex (toInverseImageBase D.f)).obj B))⟦(2 * D.n
          : ℤ)⟧ ⟶
        DerivedCategory.Q.obj ((pushforwardComplex (toInverseImageBase D.f)).obj
          (B⟦(2 * D.n : ℤ)⟧))) (_ : IsIso e'),
      (derivedTensorProductFunctor (inverseImageBase D.f).sheaf).PairingCompatible
        (D.inducedShiftedDeRhamPairing h)
        ((((derivedTensorProductFunctor (inverseImageBase D.f).sheaf).obj
            (DerivedCategory.Q.obj
              ((pushforwardComplex (toInverseImageBase D.f)).obj A))).commShiftIso
              (2 * D.n : ℤ)).hom.app
            (DerivedCategory.Q.obj ((pushforwardComplex (toInverseImageBase D.f)).obj B)) ≫
          (D.inducedDeRhamPairing h)⟦(2 * D.n : ℤ)⟧') (𝟙 _) e' := by
  let := (canonicalDerivedTensorProduct (inverseImageBase D.f).sheaf).commShift₂
  exact ⟨_, inferInstance,
    Functor.pairingCompatible_id_inv_of_eq _ (D.toTensor_commShift_inducedDeRhamPairing h)⟩

section GradedMul

attribute [local implicit_reducible] structureSheafRing TopCat.Presheaf.IsSheaf

/-- **The multiplication of `Ω^•_{X/S}` on the summand `Ω^p ⊗_{f⁻¹𝒪_S} Ω^q`** of degree
`n = p + q` is the lax comparison of restriction of scalars followed by `ι_*` of the wedge product
`Ω^p ⊗_{𝒪_X} Ω^q ⟶ Ω^n`, through the identifications of the terms of the extension by zero. -/
theorem ι_multiplicationInt_wedgeProduct_f (p q : ℕ) (hpq : (p : ℤ) + q = D.n) :
    HomologicalComplex.ιMapBifunctor (D.deRhamCx.extend ComplexShape.embeddingUpNat)
        (D.deRhamCx.extend ComplexShape.embeddingUpNat)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ((TopCat.Sheaf.pullback CommRingCat.{u} D.f.base).obj D.S.sheaf))
        (ComplexShape.up ℤ) p q D.n hpq ≫
      (SheafOfModules.multiplicationInt
        (SheafOfModules.wedgeProduct (Scheme.Hom.deRhamAlgebras D.f)
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f)))).f D.n =
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ((TopCat.Sheaf.pullback CommRingCat.{u} D.f.base).obj D.S.sheaf)).map
        (D.deRhamCx.extendXIso ComplexShape.embeddingUpNat (i' := (p : ℤ)) (i := p)
          (by simp)).hom).app _ ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ((TopCat.Sheaf.pullback CommRingCat.{u} D.f.base).obj D.S.sheaf)).obj _).map
        (D.deRhamCx.extendXIso ComplexShape.embeddingUpNat (i' := (q : ℤ)) (i := q)
          (by simp)).hom ≫
      Stacks.DeRhamDirectImage.inverseImageTensorLax D.f
        (Scheme.Hom.relativeDifferentialForms D.f p) (Scheme.Hom.relativeDifferentialForms D.f q) ≫
      (StacksDraft.KFlat.modulePushforward (toInverseImageBase D.f)).map
        ((Scheme.Hom.relativeDifferentialFormsAlgebra D.f).mulSheaf p q ≫
          eqToHom (congrArg (Scheme.Hom.relativeDifferentialForms D.f) hpq)) ≫
      (D.deRhamCx.extendXIso ComplexShape.embeddingUpNat (i' := (D.n : ℤ)) (i := D.n)
        (by simp)).inv := by
  refine (SheafOfModules.ι_multiplicationInt_f _ D.n p q hpq).trans ?_
  refine congrArg (_ ≫ _ ≫ ·) ?_
  have hn : p + q = D.n := by omega
  refine (SheafOfModules.ι_wedgeProductDesc_assoc (Scheme.Hom.deRhamAlgebras D.f)
    (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f)) p q D.n hn _).trans ?_
  rw [← SheafOfModules.laxComparison_comp_restrictScalars_mulSheaf]
  refine (congrArg (· ≫ _) (Category.assoc _ _ _)).trans ((Category.assoc _ _ _).trans ?_)
  refine congrArg (_ ≫ ·) ?_
  refine congrArg (· ≫ _) ?_
  refine Eq.trans ?_
    ((StacksDraft.KFlat.modulePushforward (toInverseImageBase D.f)).map_comp _ _).symm
  refine congrArg (_ ≫ ·) ?_
  simp only [HomologicalComplex.XIsoOfEq, eqToIso.hom]
  exact (eqToHom_map (StacksDraft.KFlat.modulePushforward (toInverseImageBase D.f)) _).symm

/-- The inclusion of the top piece in its degree `n`. -/
theorem topComplexToDeRham_f_self :
    D.topComplexToDeRham.f D.n =
      (StacksDraft.KFlat.modulePushforward (toInverseImageBase D.f)).map
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (D.n : ℤ)
          (Scheme.Hom.relativeDifferentialForms D.f D.n)).hom ≫
      (D.deRhamCx.extendXIso ComplexShape.embeddingUpNat (i' := (D.n : ℤ)) (i := D.n)
        (by simp)).inv := by
  refine (HomologicalComplex.comp_f _ _ _).trans ?_
  refine (congrArg₂ (· ≫ ·) (HomologicalComplex.singleMapHomologicalComplex_hom_app_self _ _ _ _)
    (HomologicalComplex.mkHomFromSingle_f _ _)).trans ?_
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Iso.inv_hom_id_assoc _ _))

/-- **The graded piece `Ω^p_{X/S}[-p]` of the de Rham complex is `ι_*(Ω^p_{X/S}[-p])`**: the
identification of the term of the extension by zero with `Ω^p_{X/S}`, read over `f⁻¹𝒪_S`, followed
by the commutation of `ι_*` with single complexes. -/
def formsSingleIso (p : ℕ) :
    (HomologicalComplex.single (ModulesOn (inverseImageBase D.f)) (ComplexShape.up ℤ) p).obj
        ((D.deRhamCx.extend ComplexShape.embeddingUpNat).X p) ≅
      (pushforwardComplex (toInverseImageBase D.f)).obj (D.formsComplexX p p) :=
  (HomologicalComplex.single _ (ComplexShape.up ℤ) p).mapIso
      (D.deRhamCx.extendXIso ComplexShape.embeddingUpNat (i' := (p : ℤ)) (i := p) (by simp)) ≪≫
    ((HomologicalComplex.singleMapHomologicalComplex
      (StacksDraft.KFlat.modulePushforward (toInverseImageBase D.f)) (ComplexShape.up ℤ) p).app
        (Scheme.Hom.relativeDifferentialForms D.f p)).symm

/-- `ι_multiplicationInt_wedgeProduct_f` in the form of
`StacksDraft.StupidTruncation.IsLaxProductOnSummand`. -/
theorem isLaxProductOnSummand_deRham (p q : ℕ) (hpq : (p : ℤ) + q = D.n) :
    StacksDraft.StupidTruncation.IsLaxProductOnSummand
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} D.X.sheaf)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (inverseImageBase D.f).sheaf)
      (StacksDraft.KFlat.modulePushforward (toInverseImageBase D.f))
      (Stacks.DeRhamDirectImage.inverseImageTensorLax D.f)
      (additive_F' := RingedSpace.KFlatDerivedPullback.sheafTensor_additive (inverseImageBase D.f))
      (additive_F'_obj :=
        RingedSpace.KFlatDerivedPullback.sheafTensor_obj_additive (inverseImageBase D.f))
      (fun k => Scheme.Hom.relativeDifferentialForms D.f k) p q D.n hpq
      ((Scheme.Hom.relativeDifferentialFormsAlgebra D.f).mulSheaf p q)
      (D.deRhamCx.extend ComplexShape.embeddingUpNat)
      (SheafOfModules.multiplicationInt
        (SheafOfModules.wedgeProduct (Scheme.Hom.deRhamAlgebras D.f)
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f))))
      (D.deRhamCx.extendXIso ComplexShape.embeddingUpNat (i' := (p : ℤ)) (i := p) (by simp))
      (D.deRhamCx.extendXIso ComplexShape.embeddingUpNat (i' := (q : ℤ)) (i := q) (by simp))
      (D.deRhamCx.extendXIso ComplexShape.embeddingUpNat (i' := (D.n : ℤ)) (i := D.n)
        (by simp)).inv := by
  unfold StacksDraft.StupidTruncation.IsLaxProductOnSummand
  have e := D.ι_multiplicationInt_wedgeProduct_f p q hpq
  refine Eq.trans ?_ (e.trans ?_)
  · rfl
  · rfl

/-- **The naive cup product along `ι` is the lax comparison on the summands**
(`Stacks.DeRhamDirectImage.ιMapBifunctor_naiveCupProduct_f_toInverseImageBase`). -/
theorem isLaxOnSummands_naiveCupProduct (A B : CochainComplex (ModulesOn D.X.toRingedSpace) ℤ) :
    StacksDraft.StupidTruncation.IsLaxOnSummands
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} D.X.sheaf)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (inverseImageBase D.f).sheaf)
      (StacksDraft.KFlat.modulePushforward (toInverseImageBase D.f))
      (Stacks.DeRhamDirectImage.inverseImageTensorLax D.f)
      (additive_F' := RingedSpace.KFlatDerivedPullback.sheafTensor_additive (inverseImageBase D.f))
      (additive_F'_obj :=
        RingedSpace.KFlatDerivedPullback.sheafTensor_obj_additive (inverseImageBase D.f))
      (naiveCupProduct (toInverseImageBase D.f) A B) :=
  fun i j k h =>
    Stacks.DeRhamDirectImage.ιMapBifunctor_naiveCupProduct_f_toInverseImageBase D.f A B i j k h

/-- **The product of the graded pieces of the de Rham complex, at the level of complexes**: through
`Ω^k[-k] ≅ ι_*(Ω^k[-k])`, the naive cup product along `ι` followed by `ι_*` of the wedge product
and by the inclusion of the top piece is `StacksDraft.StupidTruncation.gradedMul`. -/
theorem mapBifunctorMap_formsSingleIso_naiveCupProduct_gradedWedgeX
    (hM : ∀ k, (D.n : ℤ) < k → IsZero ((D.deRhamCx.extend ComplexShape.embeddingUpNat).X k))
    (p q : ℕ) (hpq : (p : ℤ) + q = D.n) :
    HomologicalComplex.mapBifunctorMap (D.formsSingleIso p).hom (D.formsSingleIso q).hom
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (inverseImageBase D.f).sheaf)
        (ComplexShape.up ℤ) ≫
      naiveCupProduct (toInverseImageBase D.f) (D.formsComplexX p p) (D.formsComplexX q q) ≫
      (pushforwardComplex (toInverseImageBase D.f)).map (D.gradedWedgeX p q hpq) ≫
      D.topComplexToDeRham =
    StacksDraft.StupidTruncation.gradedMul
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (inverseImageBase D.f).sheaf)
      (SheafOfModules.multiplicationInt
        (SheafOfModules.wedgeProduct (Scheme.Hom.deRhamAlgebras D.f)
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f))))
      hM p q hpq := by
  have key := StacksDraft.StupidTruncation.mapBifunctorMap_comp_comp_map_comp_eq_gradedMul
    (C := ModulesOn D.X.toRingedSpace) (C' := ModulesOn (inverseImageBase D.f))
    (additive_F' := RingedSpace.KFlatDerivedPullback.sheafTensor_additive (inverseImageBase D.f))
    (additive_F'_obj :=
      RingedSpace.KFlatDerivedPullback.sheafTensor_obj_additive (inverseImageBase D.f))
    (additive_G := StacksDraft.KFlat.modulePushforward_additive (toInverseImageBase D.f))
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} D.X.sheaf)
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (inverseImageBase D.f).sheaf)
    (StacksDraft.KFlat.modulePushforward (toInverseImageBase D.f))
    (Stacks.DeRhamDirectImage.inverseImageTensorLax D.f)
    (fun k => Scheme.Hom.relativeDifferentialForms D.f k) p q D.n hpq
    ((Scheme.Hom.relativeDifferentialFormsAlgebra D.f).mulSheaf p q)
    (D.deRhamCx.extend ComplexShape.embeddingUpNat)
    (SheafOfModules.multiplicationInt
        (SheafOfModules.wedgeProduct (Scheme.Hom.deRhamAlgebras D.f)
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f)))) hM
    (D.deRhamCx.extendXIso ComplexShape.embeddingUpNat (i' := (p : ℤ)) (i := p) (by simp))
    (D.deRhamCx.extendXIso ComplexShape.embeddingUpNat (i' := (q : ℤ)) (i := q) (by simp))
    (D.deRhamCx.extendXIso ComplexShape.embeddingUpNat (i' := (D.n : ℤ)) (i := D.n) (by simp)).inv
  refine key ?_ D.topComplexToDeRham ?_ _ ?_
  · exact D.isLaxProductOnSummand_deRham p q hpq
  · exact D.topComplexToDeRham_f_self
  · exact D.isLaxOnSummands_naiveCupProduct _ _

/-- **The products of the graded pieces are induced pairings**: the pairing
`Q(Ω^p[-p]) ⊗^L Q(Ω^q[-q]) ⟶ Q(Ω^•)` of `StacksDraft.StupidTruncation.gradedMul` is, up to the
identifications `Ω^k[-k] ≅ ι_*(Ω^k[-k])`, the pairing induced by the wedge product. On the one
nonzero summand of the total complex both are the wedge product of forms, read over `f⁻¹𝒪_S`
through the lax comparison of restriction of scalars. -/
theorem pairingCompatible_gradedMul_inducedDeRhamPairing
    (hM : ∀ k, (D.n : ℤ) < k → IsZero ((D.deRhamCx.extend ComplexShape.embeddingUpNat).X k))
    (p q : ℕ) (hpq : (p : ℤ) + q = D.n) :
    ∃ (e : DerivedCategory.Q.obj ((HomologicalComplex.single (ModulesOn (inverseImageBase D.f))
          (ComplexShape.up ℤ) p).obj ((D.deRhamCx.extend ComplexShape.embeddingUpNat).X p)) ⟶
        DerivedCategory.Q.obj ((pushforwardComplex (toInverseImageBase D.f)).obj
          (D.formsComplexX p p)))
      (e' : DerivedCategory.Q.obj ((pushforwardComplex (toInverseImageBase D.f)).obj
          (D.formsComplexX q q)) ⟶
        DerivedCategory.Q.obj ((HomologicalComplex.single (ModulesOn (inverseImageBase D.f))
          (ComplexShape.up ℤ) q).obj ((D.deRhamCx.extend ComplexShape.embeddingUpNat).X q)))
      (_ : IsIso e) (_ : IsIso e'),
      (derivedTensorProductFunctor (inverseImageBase D.f).sheaf).PairingCompatible
        ((canonicalDerivedTensorProduct (inverseImageBase D.f).sheaf).toTensor
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) p).obj
              ((D.deRhamCx.extend ComplexShape.embeddingUpNat).X p))
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) q).obj
              ((D.deRhamCx.extend ComplexShape.embeddingUpNat).X q)) ≫
          DerivedCategory.Q.map (StacksDraft.StupidTruncation.gradedMul
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (inverseImageBase D.f).sheaf)
            (SheafOfModules.multiplicationInt
              (SheafOfModules.wedgeProduct (Scheme.Hom.deRhamAlgebras D.f)
                (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f))))
            hM p q hpq))
        (D.inducedDeRhamPairing (D.gradedWedgeX p q hpq)) e e' := by
  have k1 := (canonicalDerivedTensorProduct (inverseImageBase D.f).sheaf).toTensor_naturality
    (D.formsSingleIso p).hom (D.formsSingleIso q).hom
  refine ⟨DerivedCategory.Q.map (D.formsSingleIso p).hom,
    CategoryTheory.inv (DerivedCategory.Q.map (D.formsSingleIso q).hom), inferInstance,
    inferInstance, Functor.pairingCompatible_of_eq _ _ ?_⟩
  refine ((reassoc_of% k1) _).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact Functor.comp_map_comp_map_eq DerivedCategory.Q _ _ _ _
    (D.mapBifunctorMap_formsSingleIso_naiveCupProduct_gradedWedgeX hM p q hpq)

end GradedMul

end AlgebraicGeometry.RelativeDualitySituation
