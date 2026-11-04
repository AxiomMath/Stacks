module

public import StacksFrontier.Algebra.Homology.DoubleMappingConeNaturality
public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionPresentationClass

/-!
# The class of a presented square-zero extension does not depend on the presentation

Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` be a morphism of ringed spaces and `𝒢` an `𝒪_X`-module. A
`PresentedSquareZeroExtension` over a family of generators `α : ℰ ⟶ 𝒪_X` is a square-zero
extension `0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` of `f⁻¹𝒪_S`-algebras with a lift `α' : ℰ ⟶ 𝒪_{X'}` of
`α`; it has a class `extClass ∈ Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)`, the class of its homomorphism
`𝒥/𝒥² ⟶ 𝒢` read through the quasi-isomorphism `𝖭𝖫(α) ⟶ 𝖭𝖫_{X/S}` of **Stacks 08TL**.

This file proves that the class is invariant under morphisms: given a morphism of families of
generators `h : ℰ ⟶ ℰ'` over `𝒪_X` and a morphism of extensions `N : 𝒪_{X'} ⟶ 𝒪_{X'_1}` (over
`f⁻¹𝒪_S`, over `𝒪_X`, and the identity on `𝒢`) carrying the first lift to the second, the two
classes agree. In particular the class of a square-zero extension does not depend on the family
of generators used to present it, and it is unchanged by isomorphisms of extensions.

## Main results

* `PresentedSquareZeroExtension.lift_comp_eq`: `N` intertwines the two maps out of the free
  algebras.
* `PresentedSquareZeroExtension.conormalToIdeal_eq_comp`: the homomorphism `𝒥/𝒥² ⟶ 𝒢` of the
  first extension is that of the second precomposed with the map of conormal sheaves.
* `PresentedSquareZeroExtension.Q_map_comp_conormalExtClass`: the classes of conormal
  homomorphisms are natural in the presentation.
* `PresentedSquareZeroExtension.extClass_eq_of_hom`: the two classes in
  `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)` agree.

## References

* [Stacks Project, Tag 0GPZ](https://stacks.math.columbia.edu/tag/0GPZ)
* [Stacks Project, Tag 0GQ0](https://stacks.math.columbia.edu/tag/0GQ0)
* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite TopologicalSpace
open Stacks.Sites.Conormal (IdealRestriction conormalDesc conormalSheaf conormalPresheaf
  conormal_hom_ext conormalDesc_toAssociatedModule kernelIdeal kernelIdeal_le_comap
  hom_of_comp_eq)
open Stacks.Sites.FreeAlgebra (underlyingPresheaf freeAlgebraSheaf freeAlgebraSheafDesc
  freeAlgebraSheafVariable freeAlgebraSheaf_hom_ext freeAlgebraSheafCoefficientMap
  freeAlgebraSheafCoefficientMap_comp_desc freeAlgebraSheafVariable_comp_desc)

universe u

namespace AlgebraicGeometry.RingedSpaceThickening.PresentedSquareZeroExtension

variable {X S : RingedSpace.{u, u}} {f : X ⟶ S}
  {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)}
  {E E' : Functor (Opens X.carrier)ᵒᵖ (Type u)}
  {α : E ⟶ underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf}
  {α' : E' ⟶ underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf}
  (P : PresentedSquareZeroExtension f G E α) (P' : PresentedSquareZeroExtension f G E' α')
  (h : E ⟶ E') (hα : h ≫ α' = α) (N : P.sheaf ⟶ P'.sheaf)
  (hred : N ≫ P'.reduction = P.reduction) (hbase : P.base ≫ N = P'.base)
  (hgen : P.liftGen ≫ Functor.whiskerRight
      ((sheafToPresheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}).map N)
      (forget CommRingCat.{u}) = h ≫ P'.liftGen)

include hred in
/-- A morphism of sheaves of rings over `𝒪_X` carries the square-zero ideal into the square-zero
ideal. -/
theorem map_mem_kernelIdeal (U : (Opens X.carrier)ᵒᵖ) (y : kernelIdeal P.reduction.hom U) :
    (N.hom.app U).hom y.1 ∈ kernelIdeal P'.reduction.hom U :=
  kernelIdeal_le_comap P.reduction.hom P'.reduction.hom N.hom (hom_of_comp_eq hred) U y.2

/-- The map `f⁻¹𝒪_S[ℰ] ⟶ f⁻¹𝒪_S[ℰ']` induced by a morphism of families of generators. -/
abbrev generatorsMap : freeAlgebraSheaf (Opens.grothendieckTopology X.carrier)
      (inverseImageBaseRing f) E ⟶
    freeAlgebraSheaf (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) E' :=
  Stacks.SheafOfModules.freeAlgebraMap (Opens.grothendieckTopology X.carrier)
    (inverseImageBaseRing f) E E' h

include hbase hgen in
/-- **A morphism of presented extensions intertwines the maps out of the free algebras.** -/
theorem lift_comp_eq : P.lift ≫ N = generatorsMap h ≫ P'.lift := by
  refine freeAlgebraSheaf_hom_ext (Opens.grothendieckTopology X.carrier)
    (inverseImageBaseRing f) P'.sheaf E ?_ ?_
  · refine ((Category.assoc _ _ _).symm.trans ?_).trans (Category.assoc _ _ _)
    refine (congrArg (· ≫ N) (freeAlgebraSheafCoefficientMap_comp_desc
      (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) P.sheaf E P.base
      P.liftGen)).trans (hbase.trans ?_)
    refine (freeAlgebraSheafCoefficientMap_comp_desc (Opens.grothendieckTopology X.carrier)
      (inverseImageBaseRing f) P'.sheaf E' P'.base P'.liftGen).symm.trans ?_
    exact congrArg (· ≫ P'.lift)
      (Stacks.SheafOfModules.freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap
        (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) E E' h).symm
  · rw [Functor.map_comp, Functor.map_comp, Functor.whiskerRight_comp,
      Functor.whiskerRight_comp, ← Category.assoc, ← Category.assoc,
      freeAlgebraSheafVariable_comp_desc, hgen,
      Stacks.SheafOfModules.freeAlgebraSheafVariable_comp_freeAlgebraMap, Category.assoc,
      freeAlgebraSheafVariable_comp_desc]

variable [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
    (generatorsPresentation f E α).hom]
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
    (generatorsPresentation f E' α').hom]

/-- The map `𝒥/𝒥² ⟶ 𝒥'/𝒥'²` of conormal sheaves induced by a morphism of families of
generators. -/
abbrev conormalMap :=
  Stacks.SheafOfModules.presentationConormalMap.{u, u, u, u}
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) E E' h X.sheaf
    (structureRingMap f) α α' hα

include hα hbase hgen in
/-- **The homomorphism `𝒥/𝒥² ⟶ 𝒢` is natural.** Under a morphism of presented extensions the
homomorphism of the first is that of the second precomposed with the map of conormal
sheaves. -/
theorem conormalToIdeal_eq_comp
    (hideal : ∀ (U : (Opens X.carrier)ᵒᵖ) (y : kernelIdeal P.reduction.hom U),
      P'.ideal.app U ⟨(N.hom.app U).hom y.1, map_mem_kernelIdeal P P' N hred U y⟩ =
        P.ideal.app U y) :
    P.conormalToIdeal = conormalMap h hα ≫ P'.conormalToIdeal := by
  refine conormal_hom_ext.{u, u, u, u} (generatorsPresentation f E α) G (fun U x ↦ ?_)
  refine (conormalDesc_toAssociatedModule.{u, u, u, u} _ G P.idealRestriction U x).trans ?_
  show _ = P'.conormalToIdeal.val.app U ((conormalMap h hα).val.app U _)
  refine Eq.trans ?_ (congrArg (P'.conormalToIdeal.val.app U)
    (Stacks.Sites.Conormal.conormalSheafMapOfFac_toAssociatedModule.{u, u, u, u}
      (Opens.grothendieckTopology X.carrier) X.sheaf _ _ _ _ _ _ U _)).symm
  refine Eq.trans ?_ (conormalDesc_toAssociatedModule.{u, u, u, u} _ G
    P'.idealRestriction U _).symm
  refine (hideal U ⟨_, P.lift_mem_kernelIdeal U x⟩).symm.trans ?_
  refine congrArg (P'.ideal.app U) (Subtype.ext ?_)
  exact congrArg (fun t ↦ (t.hom.app U).hom x.1) (lift_comp_eq P P' h N hbase hgen)

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- The chain map `𝖭𝖫(α) ⟶ 𝖭𝖫(α')` induced by a morphism of families of generators. -/
abbrev complexMap : presentationComplex f E α ⟶ presentationComplex f E' α' :=
  Stacks.SheafOfModules.presentationNaiveCotangentComplexMap.{u, u, u, u}
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) E E' h X.sheaf
    (structureRingMap f) α α' hα

/-- **The classes of conormal homomorphisms are natural in the presentation.** -/
theorem Q_map_comp_conormalExtClass
    (δ : (twoTerm f E' α').conormal ⟶ G) :
    DerivedCategory.Q.map (complexMap h hα) ≫ (twoTerm f E' α').conormalExtClass G δ =
      (twoTerm f E α).conormalExtClass G (conormalMap h hα ≫ δ) := by
  have h₀ := Stacks.SheafOfModules.presentationNaiveCotangentComplexMap_f_negOne.{u, u, u, u}
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) E E' h X.sheaf
    (structureRingMap f) α α' hα
  have h₁ := Stacks.SheafOfModules.presentationNaiveCotangentComplexMap_f_zero.{u, u, u, u}
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) E E' h X.sheaf
    (structureRingMap f) α α' hα
  have key := CochainComplex.doubleProjQ_naturality _ _ ComplexShape.upIntRelNegOneZero
    (by decide) (conormalMap h hα)
    (Stacks.SheafOfModules.presentationTensorMap.{u, u, u, u}
      (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) E E' h X.sheaf
      (structureRingMap f) α α' hα) (complexMap h hα) (by
      refine h₀.trans ?_
      simp only [HomologicalComplex.doubleXIso₀]
      rfl) (by
      refine h₁.trans ?_
      simp only [HomologicalComplex.doubleXIso₁, eqToIso.hom, eqToIso.inv]
      rfl)
  have key' : DerivedCategory.Q.map (complexMap h hα) ≫ (twoTerm f E' α').proj =
      (twoTerm f E α).proj ≫ ((DerivedCategory.singleFunctor _ 0).map
        (conormalMap h hα))⟦(1 : ℤ)⟧' := key
  have e3 : ((DerivedCategory.singleFunctor _ 0).map (conormalMap h hα))⟦(1 : ℤ)⟧' ≫
      ((DerivedCategory.singleFunctor _ 0).map δ)⟦(1 : ℤ)⟧' =
      ((DerivedCategory.singleFunctor _ 0).map (conormalMap h hα ≫ δ))⟦(1 : ℤ)⟧' :=
    (Functor.map_comp (shiftFunctor _ (1 : ℤ)) _ _).symm.trans
      (congrArg (shiftFunctor _ (1 : ℤ)).map (Functor.map_comp _ _ _).symm)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ ((DerivedCategory.singleFunctor _ 0).map δ)⟦(1 : ℤ)⟧') key').trans
      ((Category.assoc _ _ _).trans (congrArg ((twoTerm f E α).proj ≫ ·) e3)))

include hα hbase hgen in
/-- **The class of a presented square-zero extension is invariant under morphisms.** Given a
morphism of families of generators `h : ℰ ⟶ ℰ'` over `𝒪_X` and a morphism of square-zero
extensions carrying the lift of `ℰ` to the lift of `ℰ'`, the two classes in
`Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)` agree. -/
theorem extClass_eq_of_hom
    (hideal : ∀ (U : (Opens X.carrier)ᵒᵖ) (y : kernelIdeal P.reduction.hom U),
      P'.ideal.app U ⟨(N.hom.app U).hom y.1, map_mem_kernelIdeal P P' N hred U y⟩ =
        P.ideal.app U y) :
    P.extClass = P'.extClass := by
  have hnat := Stacks.SheafOfModules.naiveCotangentComplexComparison_naturality.{u, u, u, u}
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf
    (structureRingMap f) E E' h α α' hα
  have hinv : (naiveCotangentIso f E α).inv ≫ DerivedCategory.Q.map (complexMap h hα) =
      (naiveCotangentIso f E' α').inv := by
    refine (Iso.inv_comp_eq _).2 ((Iso.eq_comp_inv _).2 ?_)
    exact (DerivedCategory.Q.map_comp _ _).symm.trans (congrArg DerivedCategory.Q.map hnat)
  refine (congrArg ((naiveCotangentIso f E α).inv ≫ (twoTerm f E α).conormalExtClass G ·)
    (conormalToIdeal_eq_comp P P' h hα N hred hbase hgen hideal)).trans ?_
  refine (congrArg ((naiveCotangentIso f E α).inv ≫ ·)
    (Q_map_comp_conormalExtClass h hα P'.conormalToIdeal).symm).trans ?_
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hinv)

end Derived

end AlgebraicGeometry.RingedSpaceThickening.PresentedSquareZeroExtension

end
