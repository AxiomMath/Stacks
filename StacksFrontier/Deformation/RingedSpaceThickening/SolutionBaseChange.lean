module

public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionBaseChangeAlgebra

/-!
# Base change of solutions along a morphism of thickenings of the base

Let `t₁ : (S, 𝒪_S) ⟶ (S'₁, 𝒪_{S'₁})` and `t₂ : (S, 𝒪_S) ⟶ (S'₂, 𝒪_{S'₂})` be first order
thickenings, `h' : S'₂ ⟶ S'₁` with `t₂ ≫ h' = t₁`, and `f : X ⟶ S`. Let `𝒢₁`, `𝒢₂` be
`𝒪_X`-modules with prescribed maps `c₁ : f^*t₁^*𝒥₁ ⟶ 𝒢₁` and `c₂ : f^*t₂^*𝒥₂ ⟶ 𝒢₂`, and
`ν : 𝒢₁ ⟶ 𝒢₂` with `(f^*t₁^*𝒥₁ ⟶ f^*t₂^*𝒥₂) ≫ c₂ = c₁ ≫ ν`, the left map being
`baseChangeIdealMap`. This is the situation of the diagrams of **Stacks 08U9** and **08UA**.

A solution `X'` of the deformation problem of **Stacks 08U7** over `t₁` is carried to a solution
over `t₂`: its structure sheaf is the square-zero pushout `𝒪_{X'} ⊔_{𝒢₁} 𝒢₂` of `𝒪_{X'}` along `ν`,
made an `(f ∘ t₂)⁻¹𝒪_{S'₂}`-algebra by the descent of
`StacksFrontier/Deformation/RingedSpaceThickening/SolutionBaseChangeAlgebra.lean`, and it receives
from `𝒪_{X'}` a morphism of extensions compatible with `h'` inducing `ν` on ideals.

The difference class of **Stacks 08UC** is natural for this base change: the difference of the
base changes of two solutions is the image under `ν` of their difference.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.DeformationSolution.baseChange`: the base change of a
  solution over `t₁` to a solution over `t₂`.
* `AlgebraicGeometry.RingedSpaceThickening.DeformationSolution.baseChangeHom`: the morphism
  `𝒪_{X'} ⟶ 𝒪_{X'_2}` of extended structure sheaves on `X`.

## Main results

* `...DeformationSolution.baseChangeHom_comp_reduction`,
  `...DeformationSolution.baseChange_ideal_baseChangeHom` and
  `...DeformationSolution.adjointBase_comp_baseChangeHom`: the morphism is compatible with the
  reductions, induces `ν` on ideals, and is compatible with the algebra structures through `h'`.
* `AlgebraicGeometry.RingedSpaceThickening.differenceClass_baseChange`: the difference class of
  two base changes is the difference class of the solutions followed by `ν`.

## References

* [Stacks Project, Tag 08U7](https://stacks.math.columbia.edu/tag/08U7)
* [Stacks Project, Tag 08U9](https://stacks.math.columbia.edu/tag/08U9)
* [Stacks Project, Tag 08UA](https://stacks.math.columbia.edu/tag/08UA)
* [Stacks Project, Tag 08UC](https://stacks.math.columbia.edu/tag/08UC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Sites.Conormal (IdealRestriction kernelIdeal kernelIdeal_le_comap hom_of_comp_eq
  presentationScalar)

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

/-! ### Restriction of classes along a composite and along a coefficient map -/

section Restrict

variable {X S S₁ S₂ : RingedSpace.{u, u}}

/-- `(f ∘ t₂ ∘ h')⁻¹𝒪_{S'₁} ⟶ f⁻¹𝒪_S` factors through `(f ∘ t₂)⁻¹𝒪_{S'₂}`. -/
theorem baseInverseImageRingMap_comp_comp (f : X ⟶ S) (t₂ : S ⟶ S₂) (h' : S₂ ⟶ S₁) :
    baseInverseImageRingMap f (t₂ ≫ h') =
      baseInverseImageRingMap (f ≫ t₂) h' ≫ baseInverseImageRingMap f t₂ := by
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    (f ≫ (t₂ ≫ h')).hom.base).homEquiv _ _).injective
  have key : ∀ {S' : RingedSpace.{u, u}} (t : S ⟶ S'),
      adjointBaseHom f (inverseImageBaseRing f) (t := t) (baseInverseImageRingMap f t) = _ :=
    fun t => (congrArg (adjointBaseHom f (inverseImageBaseRing f) (t := t))
      (Category.comp_id (baseInverseImageRingMap f t))).symm.trans
      (adjointBaseHom_baseInverseImageRingMap_comp t f (inverseImageBaseRing f) (𝟙 _))
  have e2 := adjointBaseHom_baseInverseImageRingMap_comp h' (f ≫ t₂) (inverseImageBaseRing f)
    (baseInverseImageRingMap f t₂)
  refine (key (t₂ ≫ h')).trans (Eq.trans ?_ e2.symm)
  change _ = thickeningSharp h' ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} h'.hom.base).map
    (adjointBaseHom f (inverseImageBaseRing f) (t := t₂) (baseInverseImageRingMap f t₂))
  rw [key t₂]
  refine Eq.trans ?_ (congrArg (thickeningSharp h' ≫ ·) ((TopCat.Sheaf.pushforward CommRingCat.{u}
    h'.hom.base).map_comp _ _).symm)
  exact Category.assoc (thickeningSharp h')
    ((TopCat.Sheaf.pushforward CommRingCat.{u} h'.hom.base).map (thickeningSharp t₂)) _

attribute [local instance] HasDerivedCategory.standard

variable {f : X ⟶ S}
  {G G' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)}

/-- **Restricting a class along a composite of base maps is restricting in two steps.** -/
theorem restrictBaseExtClass_comp (t₂ : S ⟶ S₂) (h' : S₂ ⟶ S₁)
    (ζ : PresentedSquareZeroExtension.relativeObj f ⟶
      PresentedSquareZeroExtension.shiftedSingleObj G) :
    restrictBaseExtClass (t₂ ≫ h') ζ = restrictBaseExtClass h' (restrictBaseExtClass t₂ ζ) := by
  obtain ⟨P, rfl⟩ := exists_extension_extClass_eq (f := f) (G := G) ζ
  rw [restrictBaseExtClass_extClass, restrictBaseExtClass_extClass,
    restrictBaseExtClass_extClass (f := f ≫ t₂)]
  exact AlgebraSquareZeroExtension.extClass_eq_extClass_of_hom (P.restrictBase (t₂ ≫ h'))
    ((P.restrictBase t₂).restrictBase h') (𝟙 _)
    ((Category.comp_id _).trans ((congrArg (· ≫ P.base)
      (baseInverseImageRingMap_comp_comp f t₂ h')).trans (Category.assoc _ _ _)))
    (Category.id_comp _) (fun _ _ => rfl)

/-- **Restriction of classes along a base map commutes with pushing forward along a map of
coefficient modules.** -/
theorem restrictBaseExtClass_comp_coeff {S' : RingedSpace.{u, u}} (t : S ⟶ S') (ν : G ⟶ G')
    (ζ : PresentedSquareZeroExtension.relativeObj f ⟶
      PresentedSquareZeroExtension.shiftedSingleObj G) :
    restrictBaseExtClass t (ζ ≫ ((DerivedCategory.singleFunctor _ 0).map ν)⟦(1 : ℤ)⟧') =
      restrictBaseExtClass t ζ ≫ ((DerivedCategory.singleFunctor _ 0).map ν)⟦(1 : ℤ)⟧' := by
  obtain ⟨P, rfl⟩ := exists_extension_extClass_eq (f := f) (G := G) ζ
  rw [AlgebraSquareZeroExtension.extClass_pushCoeff P ν, restrictBaseExtClass_extClass,
    restrictBaseExtClass_extClass]
  exact (AlgebraSquareZeroExtension.extClass_comp_eq_extClass_of_hom (P.restrictBase t)
    ((P.pushCoeff ν).restrictBase t) ν (P.pushCoeffInl ν) (Category.assoc _ _ _)
    (P.pushCoeffInl_comp_reduction ν) (P.pushCoeff_ideal_pushCoeffInl ν)).symm

end Restrict

namespace DeformationSolution

variable {X S S₁ S₂ : RingedSpace.{u, u}} {t₂ : S ⟶ S₂} {h' : S₂ ⟶ S₁} {f : X ⟶ S}
  {G₁ G₂ : SheafOfModules.{u} (structureSheafRing X)}

/-! ### The construction, over `t₁ = t₂ ≫ h'` -/

section Core

variable {ht₁ : IsFirstOrderThickening (t₂ ≫ h')}
  {c₁ : (modulePullback f).obj ((modulePullback (t₂ ≫ h')).obj
    (AlgebraicGeometry.SheafOfModules.idealSheaf (t₂ ≫ h'))) ⟶ G₁}
  (c₂ : (modulePullback f).obj ((modulePullback t₂).obj
    (AlgebraicGeometry.SheafOfModules.idealSheaf t₂)) ⟶ G₂)
  (ν : G₁ ⟶ G₂) (hν : baseChangeIdealMap f h' rfl ≫ c₂ = c₁ ≫ ν)
  (Q : DeformationSolution (t₂ ≫ h') ht₁ f G₁ c₁)

include hν in
/-- The pushout of the extension of a solution along `ν` carries a section `a` of `𝒥₁` to the
value of `c₂` at `h'^♯ a`. -/
theorem pushCoeff_ideal_adjointBase (V : (Opens S₁.carrier)ᵒᵖ) (a : S₁.presheaf.obj V)
    (ha : ((t₂ ≫ h').hom.c.app V).hom a = 0) :
    (Q.toAlgebraExtension.pushCoeff ν).ideal.app _
        ⟨BaseChange.adj (Q.toAlgebraExtension.pushCoeff ν) V a,
          (Q.toAlgebraExtension.pushCoeff ν).adjointBase_mem_kernelIdeal V a ha⟩ =
      BaseChange.presH c₂ V a ha := by
  have hadj : (Q.toAlgebraExtension.pushCoeff ν).adjointBase =
      Q.toAlgebraExtension.adjointBase ≫ (TopCat.Sheaf.pushforward CommRingCat.{u}
        (f ≫ (t₂ ≫ h')).hom.base).map (Q.toAlgebraExtension.pushCoeffInl ν) :=
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
      (f ≫ (t₂ ≫ h')).hom.base).homEquiv_naturality_right _ _
  have hval : BaseChange.adj (Q.toAlgebraExtension.pushCoeff ν) V a =
      ((Q.toAlgebraExtension.pushCoeffInl ν).hom.app _).hom
        ((Q.toAlgebraExtension.adjointBase.hom.app V).hom a) :=
    congrArg (fun k => (k.hom.app V).hom a) hadj
  have h2 := Q.toAlgebraExtension.pushCoeff_ideal_pushCoeffInl ν _
    ⟨_, Q.toAlgebraExtension.adjointBase_mem_kernelIdeal V a ha⟩
  refine Eq.trans ?_ (h2.trans ?_)
  · exact congrArg ((Q.toAlgebraExtension.pushCoeff ν).ideal.app _) (Subtype.ext hval)
  refine (congrArg (ν.val.app _).hom (Q.toAlgebraExtension_ideal_adjointBase V a ha)).trans ?_
  refine (prescribedIdealSection_comp c₁ ν V a ha).symm.trans ?_
  refine Eq.trans ?_ (prescribedIdealSection_baseChangeIdealMap_comp f h' c₂ V a ha)
  exact prescribedIdealSection_congr' _ hν.symm V a ha

variable (ht₂ : IsFirstOrderThickening t₂)

/-- The extension of the base change, over `t₁ = t₂ ≫ h'`. -/
abbrev coreExtension : AlgebraSquareZeroExtension (f ≫ t₂) G₂ :=
  BaseChange.extension c₂ (Q.toAlgebraExtension.pushCoeff ν)
    (Q.toAlgebraExtension.pushCoeff_idealBijective ν)
    (pushCoeff_ideal_adjointBase c₂ ν hν Q) ht₂.1 ht₁.1

/-- The ideal of the extension of the base change, over `t₁ = t₂ ≫ h'`, is identified with `G₂`. -/
theorem coreExtension_idealBijective : (Q.coreExtension c₂ ν hν ht₂).IdealBijective :=
  BaseChange.extension_idealBijective c₂ (Q.toAlgebraExtension.pushCoeff ν)
    (Q.toAlgebraExtension.pushCoeff_idealBijective ν)
    (pushCoeff_ideal_adjointBase c₂ ν hν Q) ht₂.1 ht₁.1

/-- The identification of the ideal of `coreExtension` with `G₂` carries the image of a section `s`
of `𝒥₂` to the value of `c₂` at `s`. -/
theorem coreExtension_ideal_adjointBase (W : (Opens S₂.carrier)ᵒᵖ) (s : S₂.presheaf.obj W)
    (hs : (t₂.hom.c.app W).hom s = 0) :
    (Q.coreExtension c₂ ν hν ht₂).ideal.app _
        ⟨((Q.coreExtension c₂ ν hν ht₂).adjointBase.hom.app W).hom s,
          (Q.coreExtension c₂ ν hν ht₂).adjointBase_mem_kernelIdeal W s hs⟩ =
      prescribedIdealSection c₂ W s hs :=
  BaseChange.extension_ideal_adjointBase c₂ (Q.toAlgebraExtension.pushCoeff ν)
    (Q.toAlgebraExtension.pushCoeff_idealBijective ν)
    (pushCoeff_ideal_adjointBase c₂ ν hν Q) ht₂.1 ht₁.1 W s hs

/-- The base change of a solution, over `t₁ = t₂ ≫ h'`. -/
def baseChangeCore : DeformationSolution t₂ ht₂ f G₂ c₂ :=
  AlgebraSquareZeroExtension.toDeformationSolution (Q.coreExtension_idealBijective c₂ ν hν ht₂) ht₂
    (Q.coreExtension_ideal_adjointBase c₂ ν hν ht₂)

/-- The morphism `𝒪_{X'} ⟶ 𝒪_{X'_2}` of the base change, over `t₁ = t₂ ≫ h'`. -/
def baseChangeCoreHom :
    Q.toAlgebraExtension.sheaf ⟶ (Q.baseChangeCore c₂ ν hν ht₂).toAlgebraExtension.sheaf :=
  Q.toAlgebraExtension.pushCoeffInl ν ≫
    AlgebraSquareZeroExtension.toAlgebraExtensionComparison
      (Q.coreExtension_idealBijective c₂ ν hν ht₂) ht₂
      (Q.coreExtension_ideal_adjointBase c₂ ν hν ht₂)

/-- The morphism of the base change commutes with the reductions to `𝒪_X`. -/
theorem baseChangeCoreHom_comp_reduction :
    Q.baseChangeCoreHom c₂ ν hν ht₂ ≫ (Q.baseChangeCore c₂ ν hν ht₂).toAlgebraExtension.reduction =
      Q.toAlgebraExtension.reduction :=
  (Category.assoc _ _ _).trans
    ((congrArg (Q.toAlgebraExtension.pushCoeffInl ν ≫ ·)
      (AlgebraSquareZeroExtension.toAlgebraExtensionComparison_comp_reduction
        (Q.coreExtension_idealBijective c₂ ν hν ht₂) ht₂
        (Q.coreExtension_ideal_adjointBase c₂ ν hν ht₂))).trans
      (Q.toAlgebraExtension.pushCoeffInl_comp_reduction ν))

/-- On ideals, the morphism of the base change is `ν` under the identifications with `G₁` and
`G₂`. -/
theorem baseChangeCore_ideal_baseChangeCoreHom (V : (Opens X.carrier)ᵒᵖ)
    (y : ↥(kernelIdeal Q.toAlgebraExtension.reduction.hom V)) :
    (Q.baseChangeCore c₂ ν hν ht₂).toAlgebraExtension.ideal.app V
        ⟨(Q.baseChangeCoreHom c₂ ν hν ht₂).hom.app V y,
          kernelIdeal_le_comap _ _ _
            (hom_of_comp_eq (Q.baseChangeCoreHom_comp_reduction c₂ ν hν ht₂)) V y.2⟩ =
      ν.val.app V (Q.toAlgebraExtension.ideal.app V y) :=
  (AlgebraSquareZeroExtension.ideal_toAlgebraExtensionComparison
      (Q.coreExtension_idealBijective c₂ ν hν ht₂) ht₂
      (Q.coreExtension_ideal_adjointBase c₂ ν hν ht₂) V
    ⟨_, kernelIdeal_le_comap _ _ _
      (hom_of_comp_eq (Q.toAlgebraExtension.pushCoeffInl_comp_reduction ν)) V y.2⟩).trans
    (Q.toAlgebraExtension.pushCoeff_ideal_pushCoeffInl ν V y)

/-- The morphism of the base change is compatible with the algebra structures through `h'`. -/
theorem base_comp_baseChangeCoreHom :
    Q.toAlgebraExtension.base ≫ Q.baseChangeCoreHom c₂ ν hν ht₂ =
      baseInverseImageRingMap (f ≫ t₂) h' ≫
        (Q.baseChangeCore c₂ ν hν ht₂).toAlgebraExtension.base := by
  refine (Category.assoc _ _ _).symm.trans ?_
  refine Eq.trans ?_ (congrArg (baseInverseImageRingMap (f ≫ t₂) h' ≫ ·)
    (AlgebraSquareZeroExtension.base_comp_toAlgebraExtensionComparison
      (Q.coreExtension_idealBijective c₂ ν hν ht₂) ht₂
      (Q.coreExtension_ideal_adjointBase c₂ ν hν ht₂)))
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine congrArg (· ≫ _) ?_
  exact (BaseChange.baseInverseImageRingMap_comp_base₂ c₂ (Q.toAlgebraExtension.pushCoeff ν)
    (Q.toAlgebraExtension.pushCoeff_idealBijective ν)
    (pushCoeff_ideal_adjointBase c₂ ν hν Q) ht₂.1 ht₁.1).symm

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- The class over `S'₂` of the base change of a solution, read over `S'₁`, is the class of the
solution pushed forward along `ν`. -/
theorem restrictBaseExtClass_extClass_baseChangeCore :
    restrictBaseExtClass h' (Q.baseChangeCore c₂ ν hν ht₂).extClass =
      Q.extClass ≫ ((DerivedCategory.singleFunctor _ 0).map ν)⟦(1 : ℤ)⟧' := by
  refine (restrictBaseExtClass_extClass h' _).trans ?_
  refine Eq.trans ?_ (AlgebraSquareZeroExtension.extClass_pushCoeff Q.toAlgebraExtension ν).symm
  exact (AlgebraSquareZeroExtension.extClass_eq_extClass_of_hom (Q.toAlgebraExtension.pushCoeff ν)
    ((Q.baseChangeCore c₂ ν hν ht₂).toAlgebraExtension.restrictBase h')
    (AlgebraSquareZeroExtension.toAlgebraExtensionComparison
      (Q.coreExtension_idealBijective c₂ ν hν ht₂) ht₂
      (Q.coreExtension_ideal_adjointBase c₂ ν hν ht₂))
    ((Category.assoc _ _ _).symm.trans (Q.base_comp_baseChangeCoreHom c₂ ν hν ht₂))
    (AlgebraSquareZeroExtension.toAlgebraExtensionComparison_comp_reduction _ ht₂ _)
    (AlgebraSquareZeroExtension.ideal_toAlgebraExtensionComparison
      (Q.coreExtension_idealBijective c₂ ν hν ht₂) ht₂
      (Q.coreExtension_ideal_adjointBase c₂ ν hν ht₂))).symm

omit Q in
/-- **The difference class of two base changes**, over `t₁ = t₂ ≫ h'`. -/
theorem differenceClass_baseChangeCore (Q₁ Q₂ : DeformationSolution (t₂ ≫ h') ht₁ f G₁ c₁) :
    differenceClass (Q₁.baseChangeCore c₂ ν hν ht₂) (Q₂.baseChangeCore c₂ ν hν ht₂) =
      differenceClass Q₁ Q₂ ≫ ((DerivedCategory.singleFunctor _ 0).map ν)⟦(1 : ℤ)⟧' := by
  refine restrictBaseExtClass_injective (t₂ ≫ h') ht₁.1 ?_
  refine (restrictBaseExtClass_comp t₂ h' _).trans ?_
  refine (congrArg (restrictBaseExtClass h')
    (restrictBaseExtClass_differenceClass (Q₁.baseChangeCore c₂ ν hν ht₂)
      (Q₂.baseChangeCore c₂ ν hν ht₂))).trans ?_
  refine (restrictBaseExtClass_sub h' _ _).trans ?_
  refine (congrArg₂ (· - ·) (restrictBaseExtClass_extClass_baseChangeCore c₂ ν hν Q₁ ht₂)
    (restrictBaseExtClass_extClass_baseChangeCore c₂ ν hν Q₂ ht₂)).trans ?_
  refine (Preadditive.sub_comp _ _ _).symm.trans ?_
  refine (congrArg (· ≫ ((DerivedCategory.singleFunctor _ 0).map ν)⟦(1 : ℤ)⟧')
    (restrictBaseExtClass_differenceClass Q₁ Q₂).symm).trans ?_
  exact (restrictBaseExtClass_comp_coeff (t₂ ≫ h') ν _).symm

end Derived

end Core

/-! ### The base change -/

variable {t₁ : S ⟶ S₁} {ht₁ : IsFirstOrderThickening t₁}
  {c₁ : (modulePullback f).obj ((modulePullback t₁).obj
    (AlgebraicGeometry.SheafOfModules.idealSheaf t₁)) ⟶ G₁}

/-- **The base change of a solution along `h'`.** For first order thickenings `t₁`, `t₂` of `S`
with `t₂ ≫ h' = t₁`, and `ν : 𝒢₁ ⟶ 𝒢₂` compatible with the prescribed maps
(`baseChangeIdealMap f h' comm ≫ c₂ = c₁ ≫ ν`), a solution over `t₁` with ideal `𝒢₁` gives a
solution over `t₂` with ideal `𝒢₂`: its structure sheaf is the square-zero pushout
`𝒪_{X'} ⊔_{𝒢₁} 𝒢₂`, with the algebra structure over `𝒪_{S'₂}` descended along `h'`. -/
def baseChange (Q : DeformationSolution t₁ ht₁ f G₁ c₁) (ht₂ : IsFirstOrderThickening t₂)
    (c₂ : (modulePullback f).obj ((modulePullback t₂).obj
      (AlgebraicGeometry.SheafOfModules.idealSheaf t₂)) ⟶ G₂)
    (h' : S₂ ⟶ S₁) (comm : t₂ ≫ h' = t₁) (ν : G₁ ⟶ G₂)
    (hν : baseChangeIdealMap f h' comm ≫ c₂ = c₁ ≫ ν) : DeformationSolution t₂ ht₂ f G₂ c₂ := by
  subst comm
  exact Q.baseChangeCore c₂ ν hν ht₂

/-- **The morphism `𝒪_{X'} ⟶ 𝒪_{X'_2}` of extended structure sheaves on `X`** attached to the base
change of a solution: the inclusion into the square-zero pushout along `ν`. -/
def baseChangeHom (Q : DeformationSolution t₁ ht₁ f G₁ c₁) (ht₂ : IsFirstOrderThickening t₂)
    (c₂ : (modulePullback f).obj ((modulePullback t₂).obj
      (AlgebraicGeometry.SheafOfModules.idealSheaf t₂)) ⟶ G₂)
    (h' : S₂ ⟶ S₁) (comm : t₂ ≫ h' = t₁) (ν : G₁ ⟶ G₂)
    (hν : baseChangeIdealMap f h' comm ≫ c₂ = c₁ ≫ ν) :
    Q.toAlgebraExtension.sheaf ⟶ (Q.baseChange ht₂ c₂ h' comm ν hν).toAlgebraExtension.sheaf := by
  subst comm
  exact Q.baseChangeCoreHom c₂ ν hν ht₂

variable (Q : DeformationSolution t₁ ht₁ f G₁ c₁) (ht₂ : IsFirstOrderThickening t₂)
  (c₂ : (modulePullback f).obj ((modulePullback t₂).obj
    (AlgebraicGeometry.SheafOfModules.idealSheaf t₂)) ⟶ G₂)
  (h' : S₂ ⟶ S₁) (comm : t₂ ≫ h' = t₁) (ν : G₁ ⟶ G₂)
  (hν : baseChangeIdealMap f h' comm ≫ c₂ = c₁ ≫ ν)

/-- The morphism of the base change is compatible with the reductions. -/
theorem baseChangeHom_comp_reduction :
    Q.baseChangeHom ht₂ c₂ h' comm ν hν ≫
        (Q.baseChange ht₂ c₂ h' comm ν hν).toAlgebraExtension.reduction =
      Q.toAlgebraExtension.reduction := by
  subst comm
  exact Q.baseChangeCoreHom_comp_reduction c₂ ν hν ht₂

/-- **The morphism of the base change induces `ν` on the square-zero ideals.** -/
theorem baseChange_ideal_baseChangeHom (V : (Opens X.carrier)ᵒᵖ)
    (y : ↥(kernelIdeal Q.toAlgebraExtension.reduction.hom V)) :
    (Q.baseChange ht₂ c₂ h' comm ν hν).toAlgebraExtension.ideal.app V
        ⟨(Q.baseChangeHom ht₂ c₂ h' comm ν hν).hom.app V y,
          kernelIdeal_le_comap _ _ _
            (hom_of_comp_eq (Q.baseChangeHom_comp_reduction ht₂ c₂ h' comm ν hν)) V y.2⟩ =
      ν.val.app V (Q.toAlgebraExtension.ideal.app V y) := by
  subst comm
  exact Q.baseChangeCore_ideal_baseChangeCoreHom c₂ ν hν ht₂ V y

/-- **The morphism of the base change is compatible with the algebra structures through `h'`**,
in adjoint form: the algebra structure `𝒪_{S'₁} ⟶ (f ∘ t₁)_*𝒪_{X'}` followed by the morphism is
`h'^♯ : 𝒪_{S'₁} ⟶ h'_*𝒪_{S'₂}` followed by `h'_*` of the algebra structure of the base change. -/
theorem adjointBase_comp_baseChangeHom :
    Q.toAlgebraExtension.adjointBase ≫ (TopCat.Sheaf.pushforward CommRingCat.{u}
        (f ≫ t₁).hom.base).map (Q.baseChangeHom ht₂ c₂ h' comm ν hν) =
      thickeningSharp h' ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} h'.hom.base).map
          (Q.baseChange ht₂ c₂ h' comm ν hν).toAlgebraExtension.adjointBase ≫
        eqToHom (by subst comm; rfl) := by
  subst comm
  refine ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    (f ≫ (t₂ ≫ h')).hom.base).homEquiv_naturality_right _ _).symm.trans ?_
  refine (congrArg ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    (f ≫ (t₂ ≫ h')).hom.base).homEquiv _ _)
      (Q.base_comp_baseChangeCoreHom c₂ ν hν ht₂)).trans ?_
  refine (adjointBaseHom_baseInverseImageRingMap_comp h' (f ≫ t₂) _ _).trans ?_
  exact (Category.comp_id _).symm

section Derived

attribute [local instance] HasDerivedCategory.standard

omit Q in
/-- **Stacks 08UC is natural for base change of solutions along `h'`.** The difference class
`o(X'₁ ⊗ S'₂, X'₂ ⊗ S'₂) ∈ Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢₂)` of the base changes of two solutions is the
difference class `o(X'₁, X'₂) ∈ Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢₁)` followed by `ν`. -/
theorem differenceClass_baseChange (Q₁ Q₂ : DeformationSolution t₁ ht₁ f G₁ c₁) :
    differenceClass (Q₁.baseChange ht₂ c₂ h' comm ν hν) (Q₂.baseChange ht₂ c₂ h' comm ν hν) =
      differenceClass Q₁ Q₂ ≫ ((DerivedCategory.singleFunctor _ 0).map ν)⟦(1 : ℤ)⟧' := by
  subst comm
  exact differenceClass_baseChangeCore c₂ ν hν ht₂ Q₁ Q₂

end Derived

end DeformationSolution

end AlgebraicGeometry.RingedSpaceThickening

end
