module

public import StacksFrontier.CategoryTheory.Shift.CommShiftTwoInv
public import StacksFrontier.CategoryTheory.Shift.CommShiftTwoWhisker
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ModelComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.CanonicalDerivedTensorCommShiftTwo
public import StacksFrontier.Homology.DerivedCategory.DerivedPullbackModelIsoCommShift
public import StacksFrontier.Homology.KFlat.BifunctorModelComparisonCommShift

/-!
# The derived tensor product at the two models commutes with the shifts

`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorModelIso` compares the derived tensor
product of a ringed site at the standard model of `D(Mod(O))` and at the locally small model of
Tag 079Q, through the comparison equivalence `G = Stacks.Injectives.grothendieckModelEquiv`:
`T_ls(G K, G L) ≅ G(T_std(K, L))`. At each model the derived tensor product commutes with the
shifts in both variables (`Stacks.SheafOfModules.DerivedMonoidal.canonicalTensor_commShift₂Int`,
with Mathlib's sign `(-1) ^ (p * q)`), and `G` commutes with the shift
(`Stacks.Injectives.grothendieckModelEquivCommShift`). This file shows that the comparison is
compatible with all of these.

## Main results

All in the namespace `Stacks.DerivedTensor.RingedSite`:

* `derivedTensorProductFunctorIsoDerivedBifunctor_hom_eq`: the identification of the derived tensor
  product with the derived bifunctor of the total tensor complex is the inverse of
  `Stacks.SheafOfModules.DerivedMonoidal.canonicalTensorIso`.
* `derivedTensorProductFunctorIsoDerivedBifunctor_hom_commShift₂Int`: hence it commutes with the
  shifts in both variables, at any model.
* `derivedTensorProductFunctorModelIso_hom_commShift₂Int`: **the comparison of the two models
  commutes with the shifts in both variables.**
* `derivedTensorProductFunctorModelIso_hom_flipApp_commShift`: its half in the first variable, for
  a fixed second argument.

## Implementation notes

The comparison is the composite of the identifications of the derived tensor product with the
derived bifunctor at the two models and of
`CochainComplex.KFlatBifunctor.derivedBifunctorModelIso`, whose compatibility with the shifts is
`CochainComplex.KFlatBifunctor.derivedBifunctorModelIso_hom_commShift₂Int`, fed with
`StacksDraft.DerivedModel.shrinkComparisonQhIso_hom_commShift`.

The structure `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct` carries a `commShift₂` field,
registered as an instance, and the canonical derived tensor product is made opaque with
`irreducible_def`, so that field is not definitionally the transported structure
`canonicalTensor_commShift₂Int`. The statements below therefore name the latter explicitly.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.DerivedTensor.RingedSite

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The comparison `derivedBifunctorTensorIso` at a derived tensor product equal to the
construction `derivedTensorProductConstruction`, followed by the identification of the two, is
the identity. -/
private theorem derivedBifunctorTensorIso_hom_comp_eqToHom [HasDerivedCategory (Modules R)]
    (T : DerivedTensorProduct R) (hT : T = derivedTensorProductConstruction R) :
    (Stacks.SheafOfModules.DerivedMonoidal.derivedBifunctorTensorIso R T).hom ≫
      eqToHom (congrArg DerivedTensorProduct.tensor hT) = 𝟙 _ := by
  subst hT
  rw [eqToHom_refl, Category.comp_id]
  refine Localization.natTrans₂_ext (Stacks.SheafOfModules.DerivedMonoidal.kFlatComplexQ R)
    (Stacks.SheafOfModules.DerivedMonoidal.kFlatComplexQ R)
    (Stacks.SheafOfModules.DerivedMonoidal.kFlatComplexQuasiIso R)
    (Stacks.SheafOfModules.DerivedMonoidal.kFlatComplexQuasiIso R) (fun X Y => ?_)
  refine (Stacks.SheafOfModules.DerivedMonoidal.derivedBifunctorTensorIso_hom_app_app R _
    X.1 Y.1 X.2 Y.2).trans ?_
  exact Iso.hom_inv_id _

variable [(Stacks.SheafOfModules.Tensor.sheafTensor R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj M).Additive]
  [∀ (K L : CochainComplex (Modules R) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]

/-- The identification of the derived tensor product with the derived bifunctor of the total
tensor complex is the inverse of `Stacks.SheafOfModules.DerivedMonoidal.canonicalTensorIso`. -/
theorem derivedTensorProductFunctorIsoDerivedBifunctor_hom_eq
    [h : HasDerivedCategory (Modules R)] :
    (derivedTensorProductFunctorIsoDerivedBifunctor R).hom =
      (Stacks.SheafOfModules.DerivedMonoidal.canonicalTensorIso R).inv :=
  (Iso.inv_ext
    (derivedBifunctorTensorIso_hom_comp_eqToHom R _ (canonicalDerivedTensorProduct_eq R))).symm

/-- **The identification of the derived tensor product with the derived bifunctor of the total
tensor complex commutes with the shifts in both variables**, at any model of `D(Mod(O))`. The
shifts of the derived tensor product are transported from the derived bifunctor along
`Stacks.SheafOfModules.DerivedMonoidal.canonicalTensorIso`, of which this identification is the
inverse. -/
theorem derivedTensorProductFunctorIsoDerivedBifunctor_hom_commShift₂Int
    [h : HasDerivedCategory (Modules R)] :
    letI := @Stacks.SheafOfModules.DerivedMonoidal.canonicalTensor_commShift₂Int _ _ _ R _ _ h
    NatTrans.CommShift₂Int (derivedTensorProductFunctorIsoDerivedBifunctor R).hom := by
  let := @Stacks.SheafOfModules.DerivedMonoidal.canonicalTensor_commShift₂Int _ _ _ R _ _ h
  have := Functor.CommShift₂.ofIsoInt_commShift₂
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalTensorIso R)
  rw [derivedTensorProductFunctorIsoDerivedBifunctor_hom_eq]
  exact NatTrans.CommShift₂.of_iso_invInt
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalTensorIso R)

variable [IsGrothendieckAbelian.{u} (Modules R)]

/-- **The comparison of the derived tensor product at the two models commutes with the shifts in
both variables.** For the comparison equivalence `G` from the standard model of `D(Mod(O))` to
the locally small one of Tag 079Q, carrying
`Stacks.Injectives.grothendieckModelEquivCommShift`, the isomorphism
`T_ls(G K, G L) ≅ G(T_std(K, L))` is compatible with the shifts of `K` and of `L`; each derived
tensor product carries `Stacks.SheafOfModules.DerivedMonoidal.canonicalTensor_commShift₂Int`. -/
theorem derivedTensorProductFunctorModelIso_hom_commShift₂Int :
    letI := Stacks.Injectives.grothendieckModelEquivCommShift.{u} (Modules R)
    letI := Stacks.Injectives.grothendieckModelEquiv_functor_additive.{u} (Modules R)
    letI : ∀ n : ℤ, (CategoryTheory.shiftFunctor
        (@DerivedCategory (Modules R) _ _ (HasDerivedCategory.standard (Modules R))) n).Additive :=
      fun _ => inferInstance
    letI : ∀ n : ℤ, (CategoryTheory.shiftFunctor (@DerivedCategory (Modules R) _ _
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (Modules R)))
          n).Additive :=
      fun _ => inferInstance
    letI := @Stacks.SheafOfModules.DerivedMonoidal.canonicalTensor_commShift₂Int _ _ _ R _ _
      (HasDerivedCategory.standard (Modules R))
    letI := @Stacks.SheafOfModules.DerivedMonoidal.canonicalTensor_commShift₂Int _ _ _ R _ _
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (Modules R))
    NatTrans.CommShift₂Int (derivedTensorProductFunctorModelIso R).hom := by
  let := Stacks.Injectives.grothendieckModelEquivCommShift.{u} (Modules R)
  let := Stacks.Injectives.grothendieckModelEquiv_functor_additive.{u} (Modules R)
  let : ∀ n : ℤ, (CategoryTheory.shiftFunctor
      (@DerivedCategory (Modules R) _ _ (HasDerivedCategory.standard (Modules R))) n).Additive :=
    fun n => inferInstance
  let : ∀ n : ℤ, (CategoryTheory.shiftFunctor (@DerivedCategory (Modules R) _ _
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (Modules R)))
        n).Additive :=
    fun n => inferInstance
  let := @Stacks.SheafOfModules.DerivedMonoidal.canonicalTensor_commShift₂Int _ _ _ R _ _
    (HasDerivedCategory.standard (Modules R))
  let := @Stacks.SheafOfModules.DerivedMonoidal.canonicalTensor_commShift₂Int _ _ _ R _ _
    (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (Modules R))
  -- the comparison of the two `Qh` commutes with the shift
  have hE : NatTrans.CommShift
      (StacksDraft.DerivedModel.shrinkComparisonQhIso (Modules R)).hom ℤ :=
    StacksDraft.DerivedModel.shrinkComparisonQhIso_hom_commShift (Modules R)
  -- the three factors of `derivedTensorProductFunctorModelIso`
  have hA := derivedTensorProductFunctorIsoDerivedBifunctor_hom_commShift₂Int R
    (h := Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (Modules R))
  have hC := derivedTensorProductFunctorIsoDerivedBifunctor_hom_commShift₂Int R
    (h := HasDerivedCategory.standard (Modules R))
  have hB := CochainComplex.KFlatBifunctor.derivedBifunctorModelIso_hom_commShift₂Int
    (Stacks.SheafOfModules.Tensor.sheafTensor R) _ _ _ _ _ _
    (exists_kFlatLeft_quasiIso R) (exists_kFlat_quasiIso R) _ _ _
    (StacksDraft.DerivedModel.shrinkComparisonQhIso (Modules R)).symm
    (StacksDraft.DerivedModel.shrinkComparisonQhIso (Modules R)).symm
    (StacksDraft.DerivedModel.shrinkComparisonQhIso (Modules R)).symm
  have hC' := NatTrans.CommShift₂.of_iso_invInt
    (derivedTensorProductFunctorIsoDerivedBifunctor R
      (h := HasDerivedCategory.standard (Modules R)))
  dsimp only [derivedTensorProductFunctorModelIso, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Iso.symm_hom]
  infer_instance

/-- **The comparison of the derived tensor product at the two models commutes with the shift in
the first variable**: for every fixed second argument `L`, the transformation
`K ↦ (T_ls(G K, G L) ≅ G(T_std(K, L)))` commutes with the shift. This is the `commShift_flipApp`
half of `derivedTensorProductFunctorModelIso_hom_commShift₂Int`. -/
theorem derivedTensorProductFunctorModelIso_hom_flipApp_commShift
    (L : @DerivedCategory (Modules R) _ _ (HasDerivedCategory.standard (Modules R))) :
    letI := Stacks.Injectives.grothendieckModelEquivCommShift.{u} (Modules R)
    letI := Stacks.Injectives.grothendieckModelEquiv_functor_additive.{u} (Modules R)
    letI : ∀ n : ℤ, (CategoryTheory.shiftFunctor
        (@DerivedCategory (Modules R) _ _ (HasDerivedCategory.standard (Modules R))) n).Additive :=
      fun _ => inferInstance
    letI : ∀ n : ℤ, (CategoryTheory.shiftFunctor (@DerivedCategory (Modules R) _ _
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (Modules R)))
          n).Additive :=
      fun _ => inferInstance
    letI := @Stacks.SheafOfModules.DerivedMonoidal.canonicalTensor_commShift₂Int _ _ _ R _ _
      (HasDerivedCategory.standard (Modules R))
    letI := @Stacks.SheafOfModules.DerivedMonoidal.canonicalTensor_commShift₂Int _ _ _ R _ _
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (Modules R))
    NatTrans.CommShift ((derivedTensorProductFunctorModelIso R).hom.flipApp L) ℤ :=
  (derivedTensorProductFunctorModelIso_hom_commShift₂Int R).commShift_flipApp L

end Stacks.DerivedTensor.RingedSite

end
