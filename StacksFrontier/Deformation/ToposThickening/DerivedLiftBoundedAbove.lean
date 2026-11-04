module

public import StacksFrontier.Deformation.ToposThickening.CurvatureClassDerivedTensor
public import StacksFrontier.Deformation.ToposThickening.TrivialSquareZeroReduction
public import StacksFrontier.Deformation.ToposThickening.DerivedExtensionOfScalarsMinus

/-!
# A complex whose derived base change along a square-zero extension is bounded above is so too

Let `f : O ⟶ O₀` be a surjection of sheaves of commutative rings with square-zero ideal `I`,
recorded by a `Deformation.ComplexLift.DerivedReduction` with its reduction triangle
`K ⊗^L I ⟶ K ⟶ K ⊗^L O₀ ⟶ (K ⊗^L I)⟦1⟧`. If the derived tensor product with `I` and the
restriction of scalars preserve `D^{≤ n}`, then `K ∈ D^{≤ n}` as soon as `K ⊗^L O₀ ∈ D^{≤ n}`
(`Deformation.ComplexLift.DerivedReduction.isLE_of_isLE_baseChange`), by the two-out-of-three
property of `D^{≤ n}` in a distinguished triangle. Both hypotheses hold: restriction of scalars
is exact (`Deformation.ComplexLift.isLE_restrictionOnDerived_obj`), and the derived tensor product
with a module is computed on a bounded above complex of flat modules
(`Deformation.ComplexLift.isLE_derivedTensorRight_obj`). So for a trivial square-zero extension
`O₀[M] ⟶ O₀` the bound holds unconditionally
(`Deformation.ComplexLift.isLE_of_isLE_baseChange_sqZeroExt`).

This is what makes a complex `K` of `O₀[M]`-modules whose reduction is a bounded above `K₀` a lift
of `K₀` in the sense of Stacks 0DIZ, which asks `K` to be bounded above.

## References

* [Stacks Project, Tag 0DIZ](https://stacks.math.columbia.edu/tag/0DIZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe d d₀ v' u u'

namespace Deformation.ComplexLift

section General

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O O₀ : Sheaf J CommRingCat.{u}} (f : O ⟶ O₀)
variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
variable [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]

/-- Applying a zero-preserving functor degreewise to a strictly `≤ n` complex gives an object of
`D^{≤ n}`. -/
private theorem isLE_Q_obj_mapHomologicalComplex {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] [HasDerivedCategory B] (F : A ⥤ B) [F.PreservesZeroMorphisms]
    (K : CochainComplex A ℤ) (n : ℤ) [K.IsStrictlyLE n] :
    (DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).IsLE n :=
  have : CochainComplex.IsStrictlyLE ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n :=
    (CochainComplex.isStrictlyLE_iff _ n).2 fun i hi =>
      F.map_isZero (K.isZero_of_isStrictlyLE n i hi)
  inferInstance

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **Restriction of scalars preserves `D^{≤ n}`.** An object of `D^{≤ n}(O₀)` is represented by
a complex vanishing in degrees `> n`, and restriction of scalars, which needs no deriving, is
computed on it degreewise. -/
theorem isLE_restrictionOnDerived_obj
    (Y : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)))
    (n : ℤ) [Y.IsLE n] : ((restrictionOnDerived.{d, d₀} f).obj Y).IsLE n := by
  obtain ⟨K, hK, ⟨e⟩⟩ := Y.exists_iso_Q_obj_of_isLE n
  let F := SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)
  have : DerivedCategory.TStructure.t.IsLE
      ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).obj K) n :=
    isLE_Q_obj_mapHomologicalComplex F K n
  exact DerivedCategory.TStructure.t.isLE_of_iso
    ((restrictionOnDerived.{d, d₀} f).mapIso e ≪≫ F.mapDerivedCategoryFactors.app K).symm n

/-- **The derived tensor product with a module preserves `D^{≤ n}`**: an object of `D^{≤ n}` is
represented by a complex of flat modules vanishing in degrees `> n`
(`Deformation.ComplexLift.exists_isFlat_representative_of_isLE`), on which the derived tensor
product is the degreewise one
(`Deformation.ComplexLift.isIso_derivedTensorRightCounit_app_of_isFlat`). -/
theorem isLE_derivedTensorRight_obj
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
    (Y : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)))
    (n : ℤ) [Y.IsLE n] : ((derivedTensorRight.{d₀} M).obj Y).IsLE n := by
  obtain ⟨P, hflat, hLE, ⟨e⟩⟩ := exists_isFlat_representative_of_isLE O₀ n Y
  have := isIso_derivedTensorRightCounit_app_of_isFlat O₀ M P hflat n
  have : DerivedCategory.TStructure.t.IsLE
      (((tensorRight O₀ M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).obj P)
      n :=
    isLE_Q_obj_mapHomologicalComplex (tensorRight O₀ M) P n
  exact DerivedCategory.TStructure.t.isLE_of_iso
    ((derivedTensorRight.{d₀} M).mapIso e.symm ≪≫
      asIso ((derivedTensorRightCounit.{d₀} M).app P)).symm n

variable {f}

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **An object whose derived base change is in `D^{≤ n}` is in `D^{≤ n}`**, for a square-zero
extension whose derived tensor product with the ideal and restriction of scalars preserve
`D^{≤ n}`: the first and third terms of the reduction triangle
`K ⊗^L I ⟶ K ⟶ K ⊗^L O₀ ⟶ (K ⊗^L I)⟦1⟧` are in `D^{≤ n}`, hence so is the second. -/
theorem DerivedReduction.isLE_of_isLE_baseChange {T : DerivedExtensionOfScalars.{d, d₀} f}
    {idealTensor : DerivedCategory (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))}
    (R : DerivedReduction T idealTensor) (n : ℤ)
    (hI : ∀ Y : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)),
      Y.IsLE n → (idealTensor.obj Y).IsLE n)
    (hR : ∀ Y : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)),
      Y.IsLE n → (R.restriction.obj Y).IsLE n)
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)))
    (hK : (T.baseChange.obj K).IsLE n) : K.IsLE n :=
  DerivedCategory.TStructure.t.isLE₂ _ (R.distinguished K) n
    (hR _ (hI _ hK)) (hR _ hK)

end General

section SqZeroExt

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O₀ : Sheaf J CommRingCat.{u}}
  (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
variable [HasDerivedCategory.{d} (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (sqZeroExtSheafAnySite O₀ M)))]
variable [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]

/-- **An object of `D(O₀[M])` whose derived base change to `O₀` is in `D^{≤ n}` is in
`D^{≤ n}`**: `Deformation.ComplexLift.DerivedReduction.isLE_of_isLE_baseChange` for the reduction
`Deformation.ComplexLift.sqZeroExtReduction` of the trivial square-zero extension. -/
theorem isLE_of_isLE_baseChange_sqZeroExt (n : ℤ)
    (K : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (sqZeroExtSheafAnySite O₀ M))))
    (hK : ((derivedExtensionOfScalarsData.{d, d₀} (sqZeroExtSheafAnySiteProj M)).baseChange.obj
      K).IsLE n) : K.IsLE n :=
  (sqZeroExtReduction.{d, d₀} M).isLE_of_isLE_baseChange n
    (fun Y _ => isLE_derivedTensorRight_obj M Y n)
    (fun Y _ => isLE_restrictionOnDerived_obj _ Y n) K hK

end SqZeroExt

end Deformation.ComplexLift

end
