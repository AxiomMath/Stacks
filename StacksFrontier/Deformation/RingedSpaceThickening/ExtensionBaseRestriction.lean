module

public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentSquare
public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionClassInjective
public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionFromPushout
public import StacksFrontier.Deformation.RingedSpaceThickening.ThickeningBaseDescent

/-!
# Extensions over the base, read over a thickening of the base (towards Stacks 08UC)

Let `t : (S, 𝒪_S) ⟶ (S', 𝒪_{S'})` be a thickening of ringed spaces and `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)`
a morphism. A square-zero extension `0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` of `f⁻¹𝒪_S`-algebras is also
one of `(f ≫ t)⁻¹𝒪_{S'}`-algebras, through `(f ≫ t)⁻¹𝒪_{S'} ⟶ f⁻¹𝒪_S`
(`AlgebraicGeometry.RingedSpaceThickening.AlgebraSquareZeroExtension.restrictBase`). This file
shows that this passage induces an injective homomorphism of groups

`Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢) ⟶ Ext¹_{𝒪_X}(𝖭𝖫_{X/S'}, 𝒢)`

on the classes of **Stacks 0GPZ**. In the proof of **Stacks 08UC** this is how the difference of
two solutions of the deformation problem, which is an extension of `f⁻¹𝒪_S`-algebras, is
compared with the two solutions themselves, which are extensions of `(f ≫ t)⁻¹𝒪_{S'}`-algebras.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.restrictBaseExtClass`: the map on classes.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.extensionOfConormalHom_ideal_bijective`: the
  square-zero pushout identifies its ideal with `𝒢` bijectively.
* `AlgebraicGeometry.RingedSpaceThickening.restrictBaseExtClass_extClass`: the map sends the class
  of an extension to the class of the same extension read over `S'`; so it does not depend on the
  extension chosen to represent a class.
* `AlgebraicGeometry.RingedSpaceThickening.restrictBaseExtClass_injective`: it is injective,
  because a morphism of extensions over `(f ≫ t)⁻¹𝒪_{S'}` between two extensions of
  `f⁻¹𝒪_S`-algebras is automatically one over `f⁻¹𝒪_S`, `(f ≫ t)⁻¹𝒪_{S'} ⟶ f⁻¹𝒪_S` being an
  epimorphism for a thickening.

## References

* [Stacks Project, Tag 08UC](https://stacks.math.columbia.edu/tag/08UC)
* [Stacks Project, Tag 0GPZ](https://stacks.math.columbia.edu/tag/0GPZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Sites.SqZeroPushout
open Stacks.Sites.Conormal (IdealRestriction kernelIdeal kernelIdeal_le_comap hom_of_comp_eq
  conormalSheaf conormal_hom_ext conormalDesc_toAssociatedModule toAssociatedModule
  conormalPresheaf)
open Stacks.Sites.FreeAlgebra (underlyingPresheaf freeAlgebraSheaf
  freeAlgebraSheafCoefficientMap freeAlgebraSheafVariable freeAlgebraSheafDesc
  freeAlgebraSheaf_hom_ext freeAlgebraSheafCoefficientMap_comp_desc
  freeAlgebraSheafVariable_comp_desc)
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X S S' : RingedSpace.{u, u}} {f : X ⟶ S}
  {G : SheafOfModules.{u} (ringSheaf (J := Opens.grothendieckTopology X.carrier) X.sheaf)}

/-! ### The square-zero pushout identifies its ideal bijectively -/

section Pushout

variable {E : Functor (Opens X.carrier)ᵒᵖ (Type u)}
  {α : E ⟶ underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf}
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
    (generatorsPresentation f E α).hom]
  (δ : conormalSheaf.{u, u, u, u} (Opens.grothendieckTopology X.carrier)
      (freeAlgebraSheaf (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) E)
      X.sheaf (generatorsPresentation f E α) ⟶ G)

/-- A local section of the ideal of the pushout is the image of its value in `𝒢`. -/
theorem extensionOfConormalHom_ideal_app_eq (U : (Opens X.carrier)ᵒᵖ)
    (y : ↥(kernelIdeal (extensionOfConormalHom δ).reduction.hom U)) :
    (y : (extensionOfConormalHom δ).sheaf.obj.obj U) =
      pushoutInr.{u} (generatorsPresentation f E α)
        (restrictAlong.{u} (generatorsPresentation f E α) G) (conormalPushoutData δ) U
        ((extensionOfConormalHom δ).ideal.app U y) := by
  obtain ⟨n, hn⟩ := (pushoutProj_app_eq_zero_iff.{u} (generatorsPresentation f E α)
    (restrictAlong.{u} (generatorsPresentation f E α) G) (conormalPushoutData δ) U y.1).1 y.2
  have h : (extensionOfConormalHom δ).ideal.app U y = n :=
    idealRestriction_app_eq_of_val.{u} (generatorsPresentation f E α) G
      (conormalPushoutData δ) U y n hn.symm
  rw [h]
  exact hn.symm

/-- **The square-zero pushout identifies its ideal with `𝒢` bijectively.** -/
theorem extensionOfConormalHom_ideal_bijective (U : (Opens X.carrier)ᵒᵖ) :
    Function.Bijective ((extensionOfConormalHom δ).ideal.app U) := by
  refine ⟨fun y₁ y₂ h => Subtype.ext ?_, fun n => ?_⟩
  · rw [extensionOfConormalHom_ideal_app_eq δ U y₁, extensionOfConormalHom_ideal_app_eq δ U y₂, h]
  · exact ⟨⟨pushoutInr.{u} (generatorsPresentation f E α)
        (restrictAlong.{u} (generatorsPresentation f E α) G) (conormalPushoutData δ) U n,
        pushoutProj_pushoutInr.{u} (generatorsPresentation f E α)
          (restrictAlong.{u} (generatorsPresentation f E α) G) (conormalPushoutData δ) U n⟩,
      idealRestriction_app_pushoutInr.{u} (generatorsPresentation f E α) G
        (conormalPushoutData δ) U n⟩

end Pushout

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **Every class of `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)` is the class of a square-zero extension whose
ideal is identified with `𝒢` bijectively**: the square-zero pushout of
`exists_extension_extClass_eq` is one. -/
theorem exists_ideal_bijective_extClass_eq
    (ζ : PresentedSquareZeroExtension.relativeObj f ⟶
      PresentedSquareZeroExtension.shiftedSingleObj G) :
    ∃ P : AlgebraSquareZeroExtension f G,
      (∀ U, Function.Bijective (P.ideal.app U)) ∧ P.toPresented.extClass = ζ := by
  obtain ⟨E', α', hsurj, δ', hδ'⟩ := exists_conormalRepresentative (f := f) (G := G) ζ
  let : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
    (generatorsPresentation f E' α').hom := hsurj
  exact ⟨extensionOfConormalHom δ', extensionOfConormalHom_ideal_bijective δ',
    (extClass_extensionOfConormalHom δ').trans hδ'⟩

end Derived

/-! ### Presented extensions over the thickened base -/

namespace PresentedSquareZeroExtension

variable {E : Functor (Opens X.carrier)ᵒᵖ (Type u)}
  {α : E ⟶ underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf}

/-- **A presented extension of `f⁻¹𝒪_S`-algebras, read over `(f ≫ t)⁻¹𝒪_{S'}`** with the same
family of generators and the same lift. -/
def restrictBase (t : S ⟶ S') (P : PresentedSquareZeroExtension f G E α) :
    PresentedSquareZeroExtension (f ≫ t) G E α where
  sheaf := P.sheaf
  base := baseInverseImageRingMap f t ≫ P.base
  reduction := P.reduction
  base_comp_reduction := (Category.assoc _ _ _).trans
    ((congrArg (baseInverseImageRingMap f t ≫ ·) P.base_comp_reduction).trans
      (baseInverseImageRingMap_comp f t))
  liftGen := P.liftGen
  liftGen_comp := P.liftGen_comp
  ideal := P.ideal

/-- The map `(f ≫ t)⁻¹𝒪_{S'}[ℰ] ⟶ f⁻¹𝒪_S[ℰ]` of polynomial algebras on the same variables. -/
abbrev freeAlgebraBaseMap (f : X ⟶ S) (t : S ⟶ S') (E : Functor (Opens X.carrier)ᵒᵖ (Type u)) :
    freeAlgebraSheaf (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing (f ≫ t)) E ⟶
      freeAlgebraSheaf (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) E :=
  Stacks.SheafOfModules.freeAlgebraMapOfSquare (Opens.grothendieckTopology X.carrier)
    (inverseImageBaseRing (f ≫ t)) (inverseImageBaseRing f) E E (baseInverseImageRingMap f t)
    (𝟙 E)

/-- On coefficients, the map of polynomial algebras followed by `g` is the base map followed by
the coefficients followed by `g`. -/
theorem coefficientMap_comp_freeAlgebraBaseMap_comp (t : S ⟶ S')
    {B : Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}}
    (g : freeAlgebraSheaf (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) E ⟶ B) :
    freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
        (inverseImageBaseRing (f ≫ t)) E ≫ freeAlgebraBaseMap f t E ≫ g =
      baseInverseImageRingMap f t ≫ freeAlgebraSheafCoefficientMap
        (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) E ≫ g :=
  (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ g)
    (Stacks.SheafOfModules.freeAlgebraSheafCoefficientMap_comp_freeAlgebraMapOfSquare
      (Opens.grothendieckTopology X.carrier) _ _ E E (baseInverseImageRingMap f t) (𝟙 E))).trans
    (Category.assoc _ _ _))

/-- On variables, the map of polynomial algebras followed by `g` is `g`. -/
theorem variable_comp_freeAlgebraBaseMap_comp (t : S ⟶ S')
    {B : Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}}
    (g : freeAlgebraSheaf (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) E ⟶ B) :
    freeAlgebraSheafVariable (Opens.grothendieckTopology X.carrier)
        (inverseImageBaseRing (f ≫ t)) E ≫ Functor.whiskerRight
          ((sheafToPresheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}).map
            (freeAlgebraBaseMap f t E ≫ g)) (forget CommRingCat.{u}) =
      freeAlgebraSheafVariable (Opens.grothendieckTopology X.carrier)
        (inverseImageBaseRing f) E ≫ Functor.whiskerRight
          ((sheafToPresheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}).map g)
          (forget CommRingCat.{u}) := by
  refine (congrArg (fun k => freeAlgebraSheafVariable (Opens.grothendieckTopology X.carrier)
      (inverseImageBaseRing (f ≫ t)) E ≫ Functor.whiskerRight k (forget CommRingCat.{u}))
    ((sheafToPresheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}).map_comp
      (freeAlgebraBaseMap f t E) g)).trans ?_
  refine (congrArg (freeAlgebraSheafVariable (Opens.grothendieckTopology X.carrier)
      (inverseImageBaseRing (f ≫ t)) E ≫ ·) (Functor.whiskerRight_comp _ _ _)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ Functor.whiskerRight
      ((sheafToPresheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}).map g)
      (forget CommRingCat.{u}))
    (Stacks.SheafOfModules.freeAlgebraSheafVariable_comp_freeAlgebraMapOfSquare
      (Opens.grothendieckTopology X.carrier) _ _ E E (baseInverseImageRingMap f t) (𝟙 E))).trans ?_
  exact (Category.assoc _ _ _).trans (Category.id_comp _)

/-- The map of polynomial algebras lies over `𝒪_X`. -/
theorem freeAlgebraBaseMap_comp_generatorsPresentation (t : S ⟶ S') :
    freeAlgebraBaseMap f t E ≫ generatorsPresentation f E α = generatorsPresentation (f ≫ t) E α :=
  freeAlgebraSheaf_hom_ext (Opens.grothendieckTopology X.carrier)
    (inverseImageBaseRing (f ≫ t)) X.sheaf E
    ((coefficientMap_comp_freeAlgebraBaseMap_comp t _).trans
      (((congrArg (baseInverseImageRingMap f t ≫ ·)
        (freeAlgebraSheafCoefficientMap_comp_desc (Opens.grothendieckTopology X.carrier)
          (inverseImageBaseRing f) X.sheaf E (structureRingMap f) α)).trans
        (baseInverseImageRingMap_comp f t)).trans
        (freeAlgebraSheafCoefficientMap_comp_desc (Opens.grothendieckTopology X.carrier)
          (inverseImageBaseRing (f ≫ t)) X.sheaf E (structureRingMap (f ≫ t)) α).symm))
    ((variable_comp_freeAlgebraBaseMap_comp t _).trans
      ((freeAlgebraSheafVariable_comp_desc (Opens.grothendieckTopology X.carrier)
          (inverseImageBaseRing f) X.sheaf E (structureRingMap f) α).trans
        (freeAlgebraSheafVariable_comp_desc (Opens.grothendieckTopology X.carrier)
          (inverseImageBaseRing (f ≫ t)) X.sheaf E (structureRingMap (f ≫ t)) α).symm))

/-- **The lift of the restricted extension is the lift of the given one, precomposed with the map
of polynomial algebras.** -/
theorem lift_restrictBase (t : S ⟶ S') (P : PresentedSquareZeroExtension f G E α) :
    (P.restrictBase t).lift = freeAlgebraBaseMap f t E ≫ P.lift :=
  freeAlgebraSheaf_hom_ext (Opens.grothendieckTopology X.carrier)
    (inverseImageBaseRing (f ≫ t)) P.sheaf E
    ((freeAlgebraSheafCoefficientMap_comp_desc (Opens.grothendieckTopology X.carrier)
        (inverseImageBaseRing (f ≫ t)) P.sheaf E (baseInverseImageRingMap f t ≫ P.base)
        P.liftGen).trans
      ((congrArg (baseInverseImageRingMap f t ≫ ·)
        (freeAlgebraSheafCoefficientMap_comp_desc (Opens.grothendieckTopology X.carrier)
          (inverseImageBaseRing f) P.sheaf E P.base P.liftGen)).symm.trans
        (coefficientMap_comp_freeAlgebraBaseMap_comp t P.lift).symm))
    ((freeAlgebraSheafVariable_comp_desc (Opens.grothendieckTopology X.carrier)
        (inverseImageBaseRing (f ≫ t)) P.sheaf E (baseInverseImageRingMap f t ≫ P.base)
        P.liftGen).trans
      ((freeAlgebraSheafVariable_comp_desc (Opens.grothendieckTopology X.carrier)
        (inverseImageBaseRing f) P.sheaf E P.base P.liftGen).symm.trans
        (variable_comp_freeAlgebraBaseMap_comp t P.lift).symm))

variable [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
    (generatorsPresentation f E α).hom]
  (t : S ⟶ S')
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
    (generatorsPresentation (f ≫ t) E α).hom]

omit [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
    (generatorsPresentation f E α).hom]
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
    (generatorsPresentation (f ≫ t) E α).hom] in
/-- A local relation over `(f ≫ t)⁻¹𝒪_{S'}` maps to a local relation over `f⁻¹𝒪_S`. -/
theorem freeAlgebraBaseMap_mem_kernelIdeal (U : (Opens X.carrier)ᵒᵖ)
    (g : ↥(kernelIdeal (generatorsPresentation (f ≫ t) E α).hom U)) :
    ((freeAlgebraBaseMap f t E).hom.app U).hom g.1 ∈
      kernelIdeal (generatorsPresentation f E α).hom U :=
  kernelIdeal_le_comap (generatorsPresentation (f ≫ t) E α).hom
    (generatorsPresentation f E α).hom (freeAlgebraBaseMap f t E).hom
    (hom_of_comp_eq (freeAlgebraBaseMap_comp_generatorsPresentation t)) U g.2

omit [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
    (generatorsPresentation f E α).hom]
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
    (generatorsPresentation (f ≫ t) E α).hom] in
/-- **The restriction datum of the restricted extension** is the restriction datum of the given
one, read on the image of a local relation in `f⁻¹𝒪_S[ℰ]`. -/
theorem idealRestriction_restrictBase_app (P : PresentedSquareZeroExtension f G E α)
    (U : (Opens X.carrier)ᵒᵖ)
    (g : ↥(kernelIdeal (generatorsPresentation (f ≫ t) E α).hom U)) :
    (P.restrictBase t).idealRestriction.app U g =
      P.idealRestriction.app U ⟨_, freeAlgebraBaseMap_mem_kernelIdeal t U g⟩ :=
  ((P.restrictBase t).idealRestriction_app U g).trans
    ((congrArg (P.ideal.app U) (Subtype.ext
      (congrArg (fun k => (k.hom.app U).hom g.1) (lift_restrictBase t P)))).trans
      (P.idealRestriction_app U _).symm)

omit [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
    (generatorsPresentation f E α).hom] in
/-- **A restriction datum which is a difference of two stays one after restriction to the
thickened base**, read on the conormal sheaves: the homomorphism `𝒥'/𝒥'² ⟶ 𝒢` of the restricted
extension is the difference homomorphism of the two restricted extensions. -/
theorem conormalToIdeal_restrictBase_eq_obstruction (P Q₁ Q₂ : PresentedSquareZeroExtension f G E α)
    (h : ∀ (U : (Opens X.carrier)ᵒᵖ) (g : ↥(kernelIdeal (generatorsPresentation f E α).hom U)),
      P.idealRestriction.app U g = Q₁.idealRestriction.app U g - Q₂.idealRestriction.app U g) :
    (P.restrictBase t).conormalToIdeal = obstruction (Q₁.restrictBase t) (Q₂.restrictBase t) :=
  conormal_hom_ext.{u, u, u, u} (generatorsPresentation (f ≫ t) E α) G fun U g ↦
    (conormalDesc_toAssociatedModule.{u, u, u, u} (generatorsPresentation (f ≫ t) E α) G
      (P.restrictBase t).idealRestriction U g).trans
      ((idealRestriction_restrictBase_app t P U g).trans
        ((h U _).trans
          ((congrArg₂ (· - ·) (idealRestriction_restrictBase_app t Q₁ U g).symm
            (idealRestriction_restrictBase_app t Q₂ U g).symm).trans
            (Stacks.Sites.Conormal.conormalDifference_toAssociatedModule.{u, u, u, u}
              (generatorsPresentation (f ≫ t) E α) G (Q₁.restrictBase t).idealRestriction
              (Q₂.restrictBase t).idealRestriction U g).symm)))

end PresentedSquareZeroExtension

/-! ### The map on classes -/

section Derived

attribute [local instance] HasDerivedCategory.standard

variable (t : S ⟶ S')

/-- **The class of an extension of `f⁻¹𝒪_S`-algebras, read over `(f ≫ t)⁻¹𝒪_{S'}`**: the class
in `Ext¹_{𝒪_X}(𝖭𝖫_{X/S'}, 𝒢)` of an extension representing the given class, read over `S'`. By
`restrictBaseExtClass_extClass` it is the same for every representing extension. -/
def restrictBaseExtClass
    (ζ : PresentedSquareZeroExtension.relativeObj f ⟶
      PresentedSquareZeroExtension.shiftedSingleObj G) :
    PresentedSquareZeroExtension.relativeObj (f ≫ t) ⟶
      PresentedSquareZeroExtension.shiftedSingleObj G :=
  ((exists_ideal_bijective_extClass_eq ζ).choose.restrictBase t).toPresented.extClass

/-- A morphism of extensions of `f⁻¹𝒪_S`-algebras is one of the extensions read over `S'`. -/
theorem restrictBase_extClass_eq_of_hom (P₁ P₂ : AlgebraSquareZeroExtension f G)
    (θ : P₁.sheaf ⟶ P₂.sheaf) (hbase : P₁.base ≫ θ = P₂.base)
    (hred : θ ≫ P₂.reduction = P₁.reduction)
    (hideal : ∀ (V : (Opens X.carrier)ᵒᵖ) (y : ↥(kernelIdeal P₁.reduction.hom V)),
      P₂.ideal.app V ⟨θ.hom.app V y, kernelIdeal_le_comap P₁.reduction.hom P₂.reduction.hom
        θ.hom (hom_of_comp_eq hred) V y.2⟩ = P₁.ideal.app V y) :
    (P₁.restrictBase t).toPresented.extClass = (P₂.restrictBase t).toPresented.extClass :=
  AlgebraSquareZeroExtension.extClass_eq_extClass_of_hom (P₁.restrictBase t) (P₂.restrictBase t)
    θ ((Category.assoc _ _ _).trans (congrArg (baseInverseImageRingMap f t ≫ ·) hbase)) hred
    hideal

/-- **The map on classes sends the class of an extension to the class of the same extension
read over `S'`.** -/
theorem restrictBaseExtClass_extClass (P : AlgebraSquareZeroExtension f G) :
    restrictBaseExtClass t P.toPresented.extClass = (P.restrictBase t).toPresented.extClass := by
  obtain ⟨hbij, hcl⟩ := (exists_ideal_bijective_extClass_eq P.toPresented.extClass).choose_spec
  obtain ⟨θ, hbase, hred, hideal⟩ := AlgebraSquareZeroExtension.exists_hom_of_extClass_eq P _
    hbij hcl.symm
  exact (restrictBase_extClass_eq_of_hom t _ _ θ hbase hred hideal).symm

/-- **The map on classes is injective.** For a thickening, `(f ≫ t)⁻¹𝒪_{S'} ⟶ f⁻¹𝒪_S` is an
epimorphism, so a morphism of the two extensions read over `S'` is a morphism of the extensions
themselves. -/
theorem restrictBaseExtClass_injective (ht : IsThickening t) :
    Function.Injective (restrictBaseExtClass (f := f) (G := G) t) := by
  intro ζ₁ ζ₂ h
  have key (ζ : PresentedSquareZeroExtension.relativeObj f ⟶
      PresentedSquareZeroExtension.shiftedSingleObj G) :
      ∃ P : AlgebraSquareZeroExtension f G, (∀ U, Function.Bijective (P.ideal.app U)) ∧
        P.toPresented.extClass = ζ ∧
        restrictBaseExtClass t ζ = (P.restrictBase t).toPresented.extClass :=
    ⟨_, (exists_ideal_bijective_extClass_eq ζ).choose_spec.1,
      (exists_ideal_bijective_extClass_eq ζ).choose_spec.2, rfl⟩
  obtain ⟨P₁, -, hcl₁, h₁⟩ := key ζ₁
  obtain ⟨P₂, hbij₂, hcl₂, h₂⟩ := key ζ₂
  rw [h₁, h₂] at h
  obtain ⟨θ, hbase, hred, hideal⟩ :=
    AlgebraSquareZeroExtension.exists_hom_of_extClass_eq (P₁.restrictBase t)
      (P₂.restrictBase t) hbij₂ h
  exact hcl₁.symm.trans ((AlgebraSquareZeroExtension.extClass_eq_extClass_of_hom P₁ P₂ θ
    (baseInverseImageRingMap_comp_injective t ht f ((Category.assoc _ _ _).symm.trans hbase))
    hred hideal).trans hcl₂)

/-- **The map on classes is additive.** The difference of two classes is the class of the
square-zero pushout along the difference homomorphism over the common refinement of two
representing extensions, and that pushout read over `S'` has, over the same refinement, the
difference homomorphism of the two representing extensions read over `S'`. -/
theorem restrictBaseExtClass_sub
    (ζ₁ ζ₂ : PresentedSquareZeroExtension.relativeObj f ⟶
      PresentedSquareZeroExtension.shiftedSingleObj G) :
    restrictBaseExtClass t (ζ₁ - ζ₂) = restrictBaseExtClass t ζ₁ - restrictBaseExtClass t ζ₂ := by
  obtain ⟨P₁, rfl⟩ := exists_extension_extClass_eq (f := f) (G := G) ζ₁
  obtain ⟨P₂, rfl⟩ := exists_extension_extClass_eq (f := f) (G := G) ζ₂
  let W := PresentedSquareZeroExtension.obstruction (pairRefinementFst P₁ P₂)
    (pairRefinementSnd P₁ P₂)
  have hW : (extensionOfConormalHom W).toPresented.extClass =
      P₁.toPresented.extClass - P₂.toPresented.extClass :=
    (extClass_extensionOfConormalHom _).trans (extClass_sub_extClass_pairRefinement P₁ P₂).symm
  have h₁ : ((extensionOfConormalHom W).restrictBase t).toPresented.extClass =
      ((presentedOfPushout W).restrictBase t).extClass :=
    (AlgebraSquareZeroExtension.presentedBy_extClass
      ((extensionOfConormalHom W).restrictBase t) (liftGenOfPushout W)
      (liftGenOfPushout_comp W)).symm
  have h₂ : ((presentedOfPushout W).restrictBase t).conormalToIdeal =
      PresentedSquareZeroExtension.obstruction ((pairRefinementFst P₁ P₂).restrictBase t)
        ((pairRefinementSnd P₁ P₂).restrictBase t) :=
    PresentedSquareZeroExtension.conormalToIdeal_restrictBase_eq_obstruction t
      (presentedOfPushout _) (pairRefinementFst P₁ P₂) (pairRefinementSnd P₁ P₂) fun U g ↦
      (presentedOfPushout_idealRestriction_app _ U g).trans
        (Stacks.Sites.Conormal.conormalDifference_toAssociatedModule.{u, u, u, u}
          (generatorsPresentation f (pairRefinementGenerators P₁ P₂) (pairRefinementMap P₁ P₂)) G
          _ _ U g)
  have h₃ : (P₁.restrictBase t).toPresented.extClass - (P₂.restrictBase t).toPresented.extClass =
      ((pairRefinementFst P₁ P₂).restrictBase t).extClass -
        ((pairRefinementSnd P₁ P₂).restrictBase t).extClass :=
    extClass_sub_extClass_pairRefinement (P₁.restrictBase t) (P₂.restrictBase t) |>.trans
      (PresentedSquareZeroExtension.extClass_sub_extClass _ _).symm
  have h₄ : ((presentedOfPushout W).restrictBase t).extClass =
      ((pairRefinementFst P₁ P₂).restrictBase t).extClass -
        ((pairRefinementSnd P₁ P₂).restrictBase t).extClass :=
    (congrArg (fun k => (PresentedSquareZeroExtension.naiveCotangentIso (f ≫ t)
      (pairRefinementGenerators P₁ P₂) (pairRefinementMap P₁ P₂)).inv ≫
        (PresentedSquareZeroExtension.twoTerm (f ≫ t) (pairRefinementGenerators P₁ P₂)
          (pairRefinementMap P₁ P₂)).conormalExtClass G k) h₂).trans
      (PresentedSquareZeroExtension.extClass_sub_extClass _ _).symm
  exact ((congrArg (restrictBaseExtClass t) hW.symm).trans
      (restrictBaseExtClass_extClass t _)).trans
    (h₁.trans (h₄.trans (h₃.symm.trans (congrArg₂ (· - ·) (restrictBaseExtClass_extClass t P₁).symm
      (restrictBaseExtClass_extClass t P₂).symm))))

/-- The map on classes as a homomorphism of groups
`Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢) ⟶ Ext¹_{𝒪_X}(𝖭𝖫_{X/S'}, 𝒢)`. -/
def restrictBaseExtClassHom :
    (PresentedSquareZeroExtension.relativeObj f ⟶
      PresentedSquareZeroExtension.shiftedSingleObj G) →+
    (PresentedSquareZeroExtension.relativeObj (f ≫ t) ⟶
      PresentedSquareZeroExtension.shiftedSingleObj G) :=
  AddMonoidHom.mk' (restrictBaseExtClass t) fun ζ₁ ζ₂ =>
    eq_add_of_sub_eq ((restrictBaseExtClass_sub t (ζ₁ + ζ₂) ζ₂).symm.trans
      (congrArg (restrictBaseExtClass t) (add_sub_cancel_right ζ₁ ζ₂)))

/-- The homomorphism `restrictBaseExtClassHom t` agrees with `restrictBaseExtClass t`. -/
@[simp]
theorem restrictBaseExtClassHom_apply
    (ζ : PresentedSquareZeroExtension.relativeObj f ⟶
      PresentedSquareZeroExtension.shiftedSingleObj G) :
    restrictBaseExtClassHom t ζ = restrictBaseExtClass t ζ :=
  rfl

end Derived

end AlgebraicGeometry.RingedSpaceThickening

end
