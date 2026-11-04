module

public import StacksFrontier.Deformation.ToposThickening.DerivedReductionExists
public import StacksFrontier.Deformation.ToposThickening.DerivedReductionTransport
public import StacksFrontier.Deformation.ToposThickening.DerivedReductionUnit

/-!
# The matching of the reduction triangle's second morphism with the unit of the adjunction

`Deformation.ComplexLift.derivedReductionOfTriangle` transports the triangle obtained by
tensoring the square-zero ideal sequence with an object of `D(O)` onto the data a
`Deformation.ComplexLift.DerivedReduction` asks for, given the one identification that is not
transport: that the second morphism of that triangle *is* the unit of the adjunction between
derived base change and derived restriction of scalars. This file turns that identification,
stated for the derived base change constructed by Stacks 0794, into the hypothesis
`derivedReductionOfTriangle` consumes for an arbitrary derived base change.

The two steps are independent of each other. Reading the triangle's second morphism through the
two vertex identifications is an equality of natural transformations
`- ⊗^L_O O ⟶ - ⊗^L_O O₀|_O`; replacing the constructed derived base change by an arbitrary one
moves the unit and moves the identification of derived base change with the derived tensor
product, and the two moves cancel by
`Deformation.ComplexLift.derivedAdjunctionOf_unit_comp_derivedRestrictExtensionIsoOf`.

## Main results

* `Deformation.ComplexLift.tensorMap_comp_quotientVertexIso`: the matching of the triangle's
  second morphism with the unit, for an arbitrary derived base change, as an equality of natural
  transformations.
* `Deformation.ComplexLift.tensorMap_comp_quotientVertexIso_app`: the same read at an object,
  which is the hypothesis `Deformation.ComplexLift.derivedReductionOfTriangle` takes.

## References

* [Stacks Project, Tag 0DIY](https://stacks.math.columbia.edu/tag/0DIY)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe d d₀ v' u u'

namespace Deformation.ComplexLift

open AlgebraicGeometry.RingedSite Stacks.SheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O O₀ : Sheaf J CommRingCat.{u}} (f : O ⟶ O₀)
variable [HasDerivedCategory.{d} (Modules.{u', v', u} (ringedSiteOf J O))]

attribute [local instance] hasDerivedCategoryRingSheafOf

variable [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]
variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} (ringedSiteOf J O).O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u}
    (ringedSiteOf J O).O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules.{u', v', u} (ringedSiteOf J O)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (ringedSiteOf J O).O) (ComplexShape.up ℤ)]
variable (T : DerivedExtensionOfScalars.{d, d₀} f)
variable (Tt : Stacks.SheafOfModules.DerivedTensorProduct.{u', v', u, d} (ringedSiteOf J O))

/-- **The second morphism of the reduction triangle is the unit of the adjunction.** Read
through the identification of the middle vertex with the identity functor and of the third
vertex with `(- ⊗^L_O O₀)|_O`, the derived tensor product of the surjection `O ⟶ O₀|_O` with an
object of `D(O)` is the unit of the adjunction between derived base change and derived
restriction of scalars.

The hypothesis is the same statement for the derived base change constructed by Stacks 0794;
passing to an arbitrary one is
`Deformation.ComplexLift.derivedAdjunctionOf_unit_comp_derivedRestrictExtensionIsoOf`. -/
theorem tensorMap_comp_quotientVertexIso
    (hiso : (singleTensorIsoDerivedTensorRight Tt
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))).inv ≫
          Tt.tensor.flip.map (DerivedCategory.Q.map
            ((CochainComplex.singleFunctor (Modules.{u', v', u} (ringedSiteOf J O)) 0).map
              (Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit
                (ringSheafMapOf J f)))) ≫
            (singleTensorIsoDerivedTensorRight Tt (restrictUnitOf f)).hom =
        (derivedTensorRightUnitIso.{d} O).hom ≫
          ((derivedAdjunction.{d, d₀} f).unit ≫
            (derivedRestrictExtensionIso.{d, d₀} f).hom)) :
    Tt.tensor.flip.map (DerivedCategory.Q.map
          ((CochainComplex.singleFunctor (Modules.{u', v', u} (ringedSiteOf J O)) 0).map
            (Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit
              (ringSheafMapOf J f)))) ≫
        (quotientVertexIso f T Tt).hom =
      (unitVertexIso Tt).hom ≫ (derivedAdjunctionOf.{d, d₀} f T).unit := by
  have hm := ((singleTensorIsoDerivedTensorRight Tt
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))).inv_comp_eq).mp hiso
  rw [← derivedAdjunctionOf_unit_comp_derivedRestrictExtensionIsoOf f T] at hm
  simp only [unitVertexIso, quotientVertexIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← Category.assoc, hm]
  simp

/-- The matching above read at an object of `D(O)`: the hypothesis
`Deformation.ComplexLift.derivedReductionOfTriangle` takes. -/
theorem tensorMap_comp_quotientVertexIso_app
    (hiso : (singleTensorIsoDerivedTensorRight Tt
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))).inv ≫
          Tt.tensor.flip.map (DerivedCategory.Q.map
            ((CochainComplex.singleFunctor (Modules.{u', v', u} (ringedSiteOf J O)) 0).map
              (Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit
                (ringSheafMapOf J f)))) ≫
            (singleTensorIsoDerivedTensorRight Tt (restrictUnitOf f)).hom =
        (derivedTensorRightUnitIso.{d} O).hom ≫
          ((derivedAdjunction.{d, d₀} f).unit ≫
            (derivedRestrictExtensionIso.{d, d₀} f).hom))
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))) :
    (Tt.tensor.obj K).map ((DerivedCategory.singleFunctor
          (Modules.{u', v', u} (ringedSiteOf J O)) 0).map
        (Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit
          (ringSheafMapOf J f))) ≫
        (quotientVertexIso f T Tt).hom.app K =
      (unitVertexIso Tt).hom.app K ≫ (derivedAdjunctionOf.{d, d₀} f T).unit.app K :=
  NatTrans.congr_app (tensorMap_comp_quotientVertexIso f T Tt hiso) K

/-- **The `DerivedReduction` of a square-zero ideal sequence**, for an arbitrary derived base
change along `f` and an arbitrary derived tensor product of the ringed site: the reduction
triangle of step (2) of the proof of [Stacks, Tag 0DIY], transported onto the data Tags 0DIY and
0DIZ are stated relative to. -/
def derivedReductionOfIdealSequence
  (I₀ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
    {ι : restrictIdeal f I₀ ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    {hι : ι ≫ Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit
      (ringSheafMapOf J f) = 0}
    (hS : (idealSequenceOf f I₀ ι hι).ShortExact) :
    DerivedReduction T (derivedTensorRight.{d₀} I₀) :=
  derivedReductionOfTriangle f I₀ T Tt hS
    (tensorMap_comp_quotientVertexIso_app f T Tt (singleTensorIso_comp_quotientMap f Tt))

end Deformation.ComplexLift

namespace Deformation.ComplexLift

open AlgebraicGeometry.RingedSite Stacks.SheafOfModules

variable {C : Type u'} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O O₀ : Sheaf J CommRingCat.{u}} (f : O ⟶ O₀)
variable [HasDerivedCategory.{d} (Modules.{u', u, u} (ringedSiteOf J O))]

attribute [local instance] hasDerivedCategoryRingSheafOf

variable [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]
variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u', u, u, u, u} (ringedSiteOf J O).O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', u, u, u, u}
    (ringedSiteOf J O).O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules.{u', u, u} (ringedSiteOf J O)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (ringedSiteOf J O).O) (ComplexShape.up ℤ)]
variable (T : DerivedExtensionOfScalars.{d, d₀} f)

/-- **The reduction triangle of a square-zero extension exists**: step (2) of the proof of
[Stacks, Tag 0DIY] as a `Deformation.ComplexLift.DerivedReduction`.

Let `f : O ⟶ O₀` be a morphism of sheaves of commutative rings on a site whose kernel is an
ideal sheaf of square zero, so that the ideal is the restriction `I₀|_O` of a sheaf of
`O₀`-modules `I₀`, and let the sequence `0 ⟶ I₀|_O ⟶ O ⟶ O₀|_O ⟶ 0` of sheaves of `O`-modules
be short exact. Then for every derived base change `T` along `f` there is a
`Deformation.ComplexLift.DerivedReduction` relative to `T` and the derived tensor product with
`I₀`: a derived restriction of scalars right adjoint to `T.baseChange`, and for every object `K`
of `D(O)` a distinguished triangle

`(K ⊗^L_O O₀ ⊗^L_{O₀} I₀)|_O ⟶ K ⟶ (K ⊗^L_O O₀)|_O ⟶ ((K ⊗^L_O O₀ ⊗^L_{O₀} I₀)|_O)⟦1⟧`

whose second morphism is the unit of that adjunction.

So the `Deformation.ComplexLift.DerivedReduction` that Tags 0DIY and 0DIZ are stated relative to
is never vacuous. The derived tensor product of the ringed site that the triangle is formed with
is `Deformation.ComplexLift.derivedTensorProductRingedSiteOf`, the one Stacks 06YU constructs,
which is stated for a site whose morphisms lie in the universe of the sections of `O`. -/
theorem nonempty_derivedReduction
  (I₀ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
    {ι : restrictIdeal f I₀ ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    {hι : ι ≫ Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit
      (ringSheafMapOf J f) = 0}
    (hS : (idealSequenceOf f I₀ ι hι).ShortExact) :
    Nonempty (DerivedReduction T (derivedTensorRight.{d₀} I₀)) :=
  ⟨derivedReductionOfIdealSequence f T (derivedTensorProductRingedSiteOf.{d} O) I₀ hS⟩

end Deformation.ComplexLift

end
