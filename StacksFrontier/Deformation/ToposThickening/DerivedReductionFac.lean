module

public import StacksFrontier.Deformation.ToposThickening.DerivedIdealTensorIdentification
public import StacksFrontier.Deformation.ToposThickening.DerivedTensorBridge
public import StacksFrontier.Deformation.ToposThickening.DerivedTensorUnit
public import StacksFrontier.Homology.TensorComplex.BifunctorSingleRightSecond

/-!
# The comparisons of the identifications a reduction triangle is assembled from

Every identification of two derived functors used in the construction of a
`Deformation.ComplexLift.DerivedReduction` is an instance of uniqueness of left derived
functors, and so comes with a *factorization*: whiskered with the localization and composed
with the target's comparison it gives back the source's comparison. That property, not the
isomorphism itself, is what a computation with the triangle needs, and this file records it for
each of them.

Each factorization is
`CategoryTheory.Functor.leftDerivedNatTrans_fac` at the identity isomorphism, read at the
functors in question. They are collected in one place because the names of the two comparisons
being related are long and because the identity isomorphism has to be cancelled by hand each
time.

The file also proves that the comparison of the ringed site's derived tensor product with the
degreewise one is natural in the fixed tensor factor, which is what carries the second morphism
of a reduction triangle — the image of the surjection `O ⟶ O₀` — from one of these
identifications to another.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.singleTensorIsoOfLeftDerived_fac`: for the
  identification of `- ⊗^L_O M[0]` with an arbitrary left derived functor of `- ⊗_O M`.
* `Stacks.SheafOfModules.DerivedTensorProduct.singleTensorComparison_naturality`: the comparison
  of `- ⊗^L_O M[0]` with `- ⊗_O M` is natural in `M`.
* `Deformation.ComplexLift.baseChangeIso_fac`: for two derived base changes along `f`.
* `Deformation.ComplexLift.singleTensorIsoDerivedTensorRight_fac`: for the identification of the
  ringed site's derived tensor product with the one built from flat resolutions.
* `Deformation.ComplexLift.derivedRestrictExtensionIso_fac`: for derived base change read over
  `O`.
* `Deformation.ComplexLift.derivedIdealTensorIso_fac`: for the ideal part of a derived base
  change.

## References

* [Stacks Project, Tag 0DIY](https://stacks.math.columbia.edu/tag/0DIY)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe d d₀ v' u u'

/-- The map between left derived functors induced by the identity of `F` is compatible with the
two comparisons. -/
private theorem whiskerLeft_leftDerivedNatTrans_id_comp {A B E : Type*} [Category A] [Category B]
    [Category E] {L : A ⥤ E} {F : A ⥤ B} {LF LF' : E ⥤ B} (α : L ⋙ LF ⟶ F) (α' : L ⋙ LF' ⟶ F)
    (W : MorphismProperty A) [L.IsLocalization W] [LF.IsLeftDerivedFunctor α W]
    [LF'.IsLeftDerivedFunctor α' W] :
    Functor.whiskerLeft L (Functor.leftDerivedNatTrans LF LF' α α' W (𝟙 F)) ≫ α' = α :=
  (Functor.leftDerivedNatTrans_fac LF LF' α α' W (𝟙 F)).trans (Category.comp_id _)

namespace Deformation.ComplexLift

open AlgebraicGeometry.RingedSite Stacks.SheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O O₀ : Sheaf J CommRingCat.{u}} (f : O ⟶ O₀)
variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
variable [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The identification of two derived base changes is compatible with their comparisons.** -/
theorem baseChangeIso_fac (T T' : DerivedExtensionOfScalars.{d, d₀} f) :
    Functor.whiskerLeft DerivedCategory.Q
          (DerivedExtensionOfScalars.baseChangeIso T T').hom ≫
        T'.comparison =
      T.comparison :=
  whiskerLeft_leftDerivedNatTrans_id_comp T.comparison T'.comparison
    (HomologicalComplex.quasiIso _ _)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The identifications of two derived base changes in the two directions are inverse.** Both
are instances of uniqueness of left derived functors at the identity isomorphism of degreewise
extension of scalars, so their composite is the identity. This is what lets the transport of a
reduction triangle from the constructed derived base change to an arbitrary one be undone. -/
theorem baseChangeIso_trans (T T' : DerivedExtensionOfScalars.{d, d₀} f) :
    (DerivedExtensionOfScalars.baseChangeIso T T').hom ≫
        (DerivedExtensionOfScalars.baseChangeIso T' T).hom = 𝟙 T.baseChange := by
  refine Functor.leftDerived_ext T.baseChange T.comparison
    (HomologicalComplex.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (ComplexShape.up ℤ)) _ _ _ ?_
  rw [Functor.whiskerLeft_comp, Category.assoc, baseChangeIso_fac f T' T,
    baseChangeIso_fac f T T']
  simp

/-- **Derived base change read over `O` is the derived tensor product with `O₀`, compatibly
with the two comparisons.** -/
theorem derivedRestrictExtensionIso_fac :
    Functor.whiskerLeft DerivedCategory.Qh (derivedRestrictExtensionIso.{d, d₀} f).hom ≫
        derivedTensorRightCounitHomotopy.{d} (restrictUnitOf f) =
      restrictExtensionCounitHomotopy.{d, d₀} f :=
  whiskerLeft_leftDerivedNatTrans_id_comp _ _ (HomotopyCategory.quasiIso _ _)

/-- **The unit of the derived adjunction, read as a morphism into the derived tensor product
with `O₀`, does not depend on the choice of derived base change.** Transporting the adjunction
from the constructed derived base change to an arbitrary one and transporting the identification
of derived base change with the derived tensor product back again cancel, by
`Deformation.ComplexLift.baseChangeIso_trans`. -/
theorem derivedAdjunctionOf_unit_comp_derivedRestrictExtensionIsoOf
    (T : DerivedExtensionOfScalars.{d, d₀} f) :
    (derivedAdjunctionOf.{d, d₀} f T).unit ≫ (derivedRestrictExtensionIsoOf.{d, d₀} f T).hom =
      (derivedAdjunction.{d, d₀} f).unit ≫ (derivedRestrictExtensionIso.{d, d₀} f).hom := by
  have h₁ : (derivedAdjunctionOf.{d, d₀} f T).unit =
      (derivedAdjunction.{d, d₀} f).unit ≫
        Functor.whiskerRight (DerivedExtensionOfScalars.baseChangeIso
            (derivedExtensionOfScalarsData.{d, d₀} f) T).hom
          (restrictionOnDerived.{d, d₀} f) := rfl
  have h₂ : (derivedRestrictExtensionIsoOf.{d, d₀} f T).hom =
      Functor.whiskerRight (DerivedExtensionOfScalars.baseChangeIso T
          (derivedExtensionOfScalarsData.{d, d₀} f)).hom (restrictionOnDerived.{d, d₀} f) ≫
        (derivedRestrictExtensionIso.{d, d₀} f).hom := rfl
  have h₃ : Functor.whiskerRight (DerivedExtensionOfScalars.baseChangeIso
          (derivedExtensionOfScalarsData.{d, d₀} f) T).hom (restrictionOnDerived.{d, d₀} f) ≫
        Functor.whiskerRight (DerivedExtensionOfScalars.baseChangeIso T
          (derivedExtensionOfScalarsData.{d, d₀} f)).hom (restrictionOnDerived.{d, d₀} f) =
      𝟙 _ := by
    rw [← Functor.whiskerRight_comp, baseChangeIso_trans]
    simp
  rw [h₁, h₂]
  exact (Category.assoc _ _ _).trans
    (congrArg (fun k ↦ (derivedAdjunction.{d, d₀} f).unit ≫ k)
      (((Category.assoc _ _ (derivedRestrictExtensionIso.{d, d₀} f).hom).symm.trans
          (congrArg (fun k ↦ k ≫ (derivedRestrictExtensionIso.{d, d₀} f).hom) h₃)).trans
        (Category.id_comp _)))

/-- **The ideal part of a derived base change is the derived tensor product with the ideal,
compatibly with the two comparisons.** -/
theorem derivedIdealTensorIso_fac
  (I₀ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) :
    Functor.whiskerLeft DerivedCategory.Qh (derivedIdealTensorIso.{d, d₀} f I₀).hom ≫
        derivedTensorRightCounitHomotopy.{d} (restrictIdeal f I₀) =
      idealTensorCounitHomotopy.{d, d₀} f I₀ :=
  whiskerLeft_leftDerivedNatTrans_id_comp _ _ (HomotopyCategory.quasiIso _ _)

end Deformation.ComplexLift

namespace Stacks.SheafOfModules.DerivedTensorProduct

open AlgebraicGeometry.RingedSite

variable {X : RingedSite.{u', v', u}}

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules.{u', v', u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)]
  [HasDerivedCategory.{d} (Modules.{u', v', u} X)]

/-- **The identification of a derived tensor product with a left derived functor of the
degreewise tensor product is compatible with the two comparisons.** This is the factorization
property of `CategoryTheory.Functor.leftDerivedUnique`, read at
`Stacks.SheafOfModules.DerivedTensorProduct.singleTensorIsoOfLeftDerived`; everything in sight
is written in the ringed-site spelling, which is what lets the statement be elaborated. -/
theorem singleTensorIsoOfLeftDerived_fac (T : DerivedTensorProduct.{u', v', u, d} X)
    (M : Modules.{u', v', u} X)
    (G : DerivedCategory (Modules.{u', v', u} X) ⥤ DerivedCategory (Modules.{u', v', u} X))
    (γ : DerivedCategory.Q ⋙ G ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj M).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (hG : G.IsLeftDerivedFunctor γ
      (HomologicalComplex.quasiIso (Modules.{u', v', u} X) (ComplexShape.up ℤ))) :
    Functor.whiskerLeft DerivedCategory.Q (T.singleTensorIsoOfLeftDerived M G γ hG).hom ≫ γ =
      T.singleTensorComparison M := by
  have := hG
  have := T.isLeftDerivedFunctor_singleTensorComparison M
  exact whiskerLeft_leftDerivedNatTrans_id_comp (T.singleTensorComparison M) γ
    (HomologicalComplex.quasiIso _ _)

/-- **The comparison of `- ⊗^L_O M[0]` with `- ⊗_O M` is natural in `M`.** Both the canonical
map to the total tensor complex and the degreewise identification of that complex with
`- ⊗_O M` are natural in the fixed tensor factor; this composes the two naturalities. -/
theorem singleTensorComparison_naturality (T : DerivedTensorProduct.{u', v', u, d} X)
    {M N : Modules.{u', v', u} X} (g : M ⟶ N) :
    Functor.whiskerLeft DerivedCategory.Q
          (T.tensor.flip.map (DerivedCategory.Q.map
            ((CochainComplex.singleFunctor (Modules.{u', v', u} X) 0).map g))) ≫
        T.singleTensorComparison N =
      T.singleTensorComparison M ≫
        Functor.whiskerRight
          (NatTrans.mapHomologicalComplex
            ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.map g) (ComplexShape.up ℤ))
          DerivedCategory.Q := by
  have hm := HomologicalComplex.map₂SingleRightNatIso_naturality_snd
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} X.O) g
  have hdef : ∀ M' : Modules.{u', v', u} X, T.singleTensorComparison M' =
      T.toTensorSingle M' ≫ (totalTensorSingleIso M').hom := fun _ ↦ rfl
  have hA : Functor.whiskerLeft DerivedCategory.Q
          (T.tensor.flip.map (DerivedCategory.Q.map
            ((CochainComplex.singleFunctor (Modules.{u', v', u} X) 0).map g))) ≫
        T.toTensorSingle N =
      T.toTensorSingle M ≫
        Functor.whiskerRight
          ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map₂CochainComplex.flip.map
            ((CochainComplex.singleFunctor (Modules.{u', v', u} X) 0).map g))
          DerivedCategory.Q := by
    refine NatTrans.ext (funext fun P ↦ ?_)
    have hnat := T.toTensor_naturality (𝟙 P)
      ((CochainComplex.singleFunctor (Modules.{u', v', u} X) 0).map g)
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.id_comp] at hnat
    exact hnat
  have hinv : (Stacks.SheafOfModules.Tensor.sheafTensor X.O).map₂CochainComplex.flip.map
          ((CochainComplex.singleFunctor (Modules.{u', v', u} X) 0).map g) ≫
        (HomologicalComplex.map₂SingleRightNatIso
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} X.O) N).inv =
      (HomologicalComplex.map₂SingleRightNatIso
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} X.O) M).inv ≫
        NatTrans.mapHomologicalComplex
          ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.map g) (ComplexShape.up ℤ) := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact hm.symm
  have hB : Functor.whiskerRight
          ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map₂CochainComplex.flip.map
            ((CochainComplex.singleFunctor (Modules.{u', v', u} X) 0).map g))
          DerivedCategory.Q ≫
        (totalTensorSingleIso N).hom =
      (totalTensorSingleIso M).hom ≫
        Functor.whiskerRight
          (NatTrans.mapHomologicalComplex
            ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.map g) (ComplexShape.up ℤ))
          DerivedCategory.Q := by
    have hts : ∀ M' : Modules.{u', v', u} X, (totalTensorSingleIso M').hom =
        Functor.whiskerRight (HomologicalComplex.map₂SingleRightNatIso
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} X.O) M').inv
          DerivedCategory.Q := fun _ ↦ rfl
    rw [hts M, hts N, ← Functor.whiskerRight_comp, ← Functor.whiskerRight_comp]
    exact congrArg (fun k ↦ Functor.whiskerRight k DerivedCategory.Q) hinv
  rw [hdef M, hdef N, ← Category.assoc, hA, Category.assoc, hB, ← Category.assoc]

end Stacks.SheafOfModules.DerivedTensorProduct

namespace Deformation.ComplexLift

open AlgebraicGeometry.RingedSite Stacks.SheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O : Sheaf J CommRingCat.{u}}
variable [HasDerivedCategory.{d} (Modules.{u', v', u} (ringedSiteOf J O))]

attribute [local instance] hasDerivedCategoryRingSheafOf

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} (ringedSiteOf J O).O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u}
    (ringedSiteOf J O).O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules.{u', v', u} (ringedSiteOf J O)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (ringedSiteOf J O).O) (ComplexShape.up ℤ)]

/-- **The two derived tensor products with a fixed sheaf of modules agree compatibly with their
comparisons.** -/
theorem singleTensorIsoDerivedTensorRight_fac
    (T : DerivedTensorProduct.{u', v', u, d} (ringedSiteOf J O))
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    Functor.whiskerLeft DerivedCategory.Q (singleTensorIsoDerivedTensorRight T M).hom ≫
        derivedTensorRightCounit.{d} M =
      T.singleTensorComparison M := by
  exact T.singleTensorIsoOfLeftDerived_fac M (derivedTensorRight.{d} M)
    (derivedTensorRightCounit.{d} M) (isLeftDerivedFunctor_derivedTensorRightCounit.{d} M)

end Deformation.ComplexLift

end
