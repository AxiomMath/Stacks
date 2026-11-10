module

public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionCommonRefinement

/-!
# The class of a square-zero extension is natural in the coefficient module

Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` be a morphism of ringed spaces. A square-zero extension
`0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` of `f⁻¹𝒪_S`-algebras has a class in `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)`
(`AlgebraicGeometry.RingedSpaceThickening.PresentedSquareZeroExtension.extClass`). This class is
natural in the coefficient module: if `θ : 𝒪_{X'} ⟶ 𝒪_{X''}` is a morphism of `f⁻¹𝒪_S`-algebras
over `𝒪_X` from an extension by `𝒢` to an extension by `𝒢'`, inducing `g : 𝒢 ⟶ 𝒢'` on the
square-zero ideals, then the class of the second extension is the class of the first pushed
forward along `g`.

## Main definitions

* `Stacks.Sites.Conormal.IdealRestriction.mapCoeff`: a restriction datum pushed forward along a
  morphism of coefficient modules.

## Main results

* `Stacks.Sites.Conormal.conormalDesc_mapCoeff`: the descent of a restriction datum pushed
  forward along `g` is the descent followed by `g`.
* `RingedSpaceThickening.PresentedSquareZeroExtension.extClass_comp_eq_extClass`: the class of a
  presented extension pushed forward along `g` is the class of the second one.
* `RingedSpaceThickening.AlgebraSquareZeroExtension.extClass_comp_eq_extClass_of_hom`: the same
  for two square-zero extensions related by a morphism of extended structure sheaves inducing `g`.

## References

* [Stacks Project, Tag 0GQ0](https://stacks.math.columbia.edu/tag/0GQ0)
* [Stacks Project, Tag 0GPZ](https://stacks.math.columbia.edu/tag/0GPZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite TopologicalSpace
open Stacks.Sites.Conormal (IdealRestriction conormalDesc conormalSheaf
  conormal_hom_ext conormalDesc_toAssociatedModule conormalDesc_conormalClass
  conormalSheafMapOfFac conormalSheafMapOfFac_conormalClass kernelIdeal kernelIdeal_le_comap
  hom_of_comp_eq)
open Stacks.Sites.FreeAlgebra (underlyingPresheaf freeAlgebraSheaf)
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.SheafOfModules (freeAlgebraMap freeAlgebraMap_comp_presentation
  presentationNaiveCotangentComplexMap presentationConormalExtClass_eq
  naiveCotangentComplexComparison_naturality)

universe u

/-! ### Restriction data pushed forward along a coefficient map -/

namespace Stacks.Sites.Conormal

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {A B : Sheaf J CommRingCat.{u}} {φ : A ⟶ B}
  {G G' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B)}

/-- A restriction datum with values in `𝒢`, pushed forward along a morphism `g : 𝒢 ⟶ 𝒢'`. -/
noncomputable def IdealRestriction.mapCoeff (ρ : IdealRestriction.{u, u, u, u} φ G)
    (g : G ⟶ G') : IdealRestriction.{u, u, u, u} φ G' where
  app X := (g.val.app X).hom.toAddMonoidHom.comp (ρ.app X)
  app_smul X r m := by
    change g.val.app X (ρ.app X (r • m)) = presentationScalar φ X r • g.val.app X (ρ.app X m)
    rw [ρ.app_smul]
    exact (g.val.app X).hom.map_smul _ _
  app_map {X Y} f m := by
    change g.val.app Y (ρ.app Y _) = G'.val.map f (g.val.app X (ρ.app X m))
    rw [ρ.app_map]
    exact PresheafOfModules.naturality_apply g.val f _

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The pushed-forward restriction datum is the restriction datum followed by `g`. -/
@[simp] theorem IdealRestriction.mapCoeff_app (ρ : IdealRestriction.{u, u, u, u} φ G)
    (g : G ⟶ G') (X : Cᵒᵖ) (m : ↥(kernelIdeal φ.hom X)) :
    (ρ.mapCoeff g).app X m = g.val.app X (ρ.app X m) :=
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The descent of a pushed-forward restriction datum is the descent followed by `g`. -/
theorem conormalDesc_mapCoeff [Presheaf.IsLocallySurjective J φ.hom]
    (ρ : IdealRestriction.{u, u, u, u} φ G) (g : G ⟶ G') :
    conormalDesc.{u, u, u, u} φ G' (ρ.mapCoeff g) = conormalDesc.{u, u, u, u} φ G ρ ≫ g := by
  refine conormal_hom_ext φ G' (fun X x ↦ ?_)
  refine (conormalDesc_toAssociatedModule φ G' (ρ.mapCoeff g) X x).trans ?_
  exact (congrArg (g.val.app X) (conormalDesc_toAssociatedModule φ G ρ X x)).symm

end Stacks.Sites.Conormal

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X S : RingedSpace.{u, u}}

/-! ### The class of a conormal homomorphism pushed forward -/

section TwoTerm

variable {M : Type*} [Category M] {D : Type*} [Category D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] {single : M ⥤ D}

/-- The class of a conormal homomorphism is natural in the coefficients: for `ξ : ℐ/ℐ² ⟶ 𝒢` and
`g : 𝒢 ⟶ 𝒢'`, the class of `ξ ≫ g` in `Ext¹(NL(α), 𝒢')` is the class of `ξ` pushed forward along
`g`. -/
theorem NaiveCotangentTwoTerm.conormalExtClass_comp (P : NaiveCotangentTwoTerm single)
    {G G' : M} (ξ : P.conormal ⟶ G) (g : G ⟶ G') :
    P.conormalExtClass G' (ξ ≫ g) =
      P.conormalExtClass G ξ ≫ (single.map g)⟦(1 : ℤ)⟧' := by
  simp only [NaiveCotangentTwoTerm.conormalExtClass, Functor.map_comp, Category.assoc]

end TwoTerm

namespace PresentedSquareZeroExtension

variable {f : X ⟶ S}
  {G G' : SheafOfModules.{u} (ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)}
  {E₁ E₂ : Functor (Opens X.carrier)ᵒᵖ (Type u)}
  {α₁ : E₁ ⟶ underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf}
  {α₂ : E₂ ⟶ underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf}
  (P₁ : PresentedSquareZeroExtension f G E₁ α₁)
  (P₂ : PresentedSquareZeroExtension f G' E₂ α₂)
  (u : E₁ ⟶ E₂) (θ : P₁.sheaf ⟶ P₂.sheaf) (g : G ⟶ G')

section Derived

attribute [local instance] HasDerivedCategory.standard

variable [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
    (generatorsPresentation f E₁ α₁).hom]
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
    (generatorsPresentation f E₂ α₂).hom]

/-- The class of the first presented extension pushed forward along `g` is the class of the second
one read through the chain map `𝖭𝖫(α₁) ⟶ 𝖭𝖫(α₂)` of the refinement. -/
theorem presentedExtClass_comp_eq (hu : u ≫ α₂ = α₁)
    (hred : θ ≫ P₂.reduction = P₁.reduction)
    (hlift : freeAlgebraMap (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f)
      E₁ E₂ u ≫ P₂.lift = P₁.lift ≫ θ)
    (hideal : ∀ (V : (Opens X.carrier)ᵒᵖ) (y : ↥(kernelIdeal P₁.reduction.hom V)),
      P₂.ideal.app V ⟨θ.hom.app V y, kernelIdeal_le_comap P₁.reduction.hom P₂.reduction.hom
        θ.hom (hom_of_comp_eq hred) V y.2⟩ = g.val.app V (P₁.ideal.app V y)) :
    P₁.presentedExtClass ≫ ((DerivedCategory.singleFunctor _ 0).map g)⟦(1 : ℤ)⟧' =
      DerivedCategory.Q.map (presentationNaiveCotangentComplexMap.{u, u, u, u}
          (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) E₁ E₂ u X.sheaf
          (structureRingMap f) α₁ α₂ hu) ≫
        P₂.presentedExtClass := by
  refine ((twoTerm f E₁ α₁).conormalExtClass_comp P₁.conormalToIdeal g).symm.trans ?_
  refine (congrArg (fun ξ ↦ (twoTerm f E₁ α₁).conormalExtClass G' ξ)
    (Stacks.Sites.Conormal.conormalDesc_mapCoeff P₁.idealRestriction g).symm).trans ?_
  exact presentationConormalExtClass_eq (inverseImageBaseRing f) X.sheaf (structureRingMap f)
    E₁ E₂ α₁ α₂ G' u hu _ P₂.conormalToIdeal
    (Stacks.Sites.Conormal.conormalSheafMapOfFac_comp_conormalDesc.{u, u, u, u}
      (generatorsPresentation f E₁ α₁) (generatorsPresentation f E₂ α₂)
      (freeAlgebraMap (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) E₁ E₂ u)
      (freeAlgebraMap_comp_presentation (Opens.grothendieckTopology X.carrier)
        (inverseImageBaseRing f) E₁ E₂ u X.sheaf (structureRingMap f) α₁ α₂ hu)
      G' (P₁.idealRestriction.mapCoeff g) P₂.idealRestriction (fun V h ↦
        (P₂.idealRestriction_app V _).trans
          ((congrArg (P₂.ideal.app V) (Subtype.ext
            (congrArg (fun t : freeAlgebraSheaf (Opens.grothendieckTopology X.carrier)
              (inverseImageBaseRing f) E₁ ⟶ P₂.sheaf ↦ (t.hom.app V).hom h.1) hlift))).trans
            (hideal V ⟨(P₁.lift.hom.app V).hom h.1, P₁.lift_mem_kernelIdeal V h⟩))))

/-- The class of a presented square-zero extension is natural in the coefficient module. Let
`u : ℰ₁ ⟶ ℰ₂` be a morphism of families of generators with `u ≫ α₂ = α₁`, and let
`θ : 𝒪_{X'₁} ⟶ 𝒪_{X'₂}` be a morphism of the two extended structure sheaves over `𝒪_X`,
compatible with the two maps `f⁻¹𝒪_S[ℰ] ⟶ 𝒪_{X'}`, which on the square-zero ideals is
`g : 𝒢 ⟶ 𝒢'` under the two identifications. Then the class of the second extension in
`Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢')` is the class of the first pushed forward along `g`. -/
theorem extClass_comp_eq_extClass (hu : u ≫ α₂ = α₁)
    (hred : θ ≫ P₂.reduction = P₁.reduction)
    (hlift : freeAlgebraMap (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f)
      E₁ E₂ u ≫ P₂.lift = P₁.lift ≫ θ)
    (hideal : ∀ (V : (Opens X.carrier)ᵒᵖ) (y : ↥(kernelIdeal P₁.reduction.hom V)),
      P₂.ideal.app V ⟨θ.hom.app V y, kernelIdeal_le_comap P₁.reduction.hom P₂.reduction.hom
        θ.hom (hom_of_comp_eq hred) V y.2⟩ = g.val.app V (P₁.ideal.app V y)) :
    P₁.extClass ≫ ((DerivedCategory.singleFunctor _ 0).map g)⟦(1 : ℤ)⟧' = P₂.extClass := by
  have hcomp : DerivedCategory.Q.map (presentationNaiveCotangentComplexMap.{u, u, u, u}
          (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) E₁ E₂ u X.sheaf
          (structureRingMap f) α₁ α₂ hu) ≫ (naiveCotangentIso f E₂ α₂).hom =
      (naiveCotangentIso f E₁ α₁).hom :=
    (DerivedCategory.Q.map_comp _ _).symm.trans (congrArg DerivedCategory.Q.map
      (naiveCotangentComplexComparison_naturality.{u, u, u, u}
        (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf
        (structureRingMap f) E₁ E₂ u α₁ α₂ hu))
  have hinv : (naiveCotangentIso f E₁ α₁).inv ≫
      DerivedCategory.Q.map (presentationNaiveCotangentComplexMap.{u, u, u, u}
        (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) E₁ E₂ u X.sheaf
        (structureRingMap f) α₁ α₂ hu) = (naiveCotangentIso f E₂ α₂).inv := by
    rw [← Category.comp_id ((naiveCotangentIso f E₁ α₁).inv ≫ _),
      ← (naiveCotangentIso f E₂ α₂).hom_inv_id, Category.assoc,
      ← Category.assoc _ _ (naiveCotangentIso f E₂ α₂).inv, hcomp,
      (naiveCotangentIso f E₁ α₁).inv_hom_id_assoc]
  change ((naiveCotangentIso f E₁ α₁).inv ≫ P₁.presentedExtClass) ≫ _ =
    (naiveCotangentIso f E₂ α₂).inv ≫ P₂.presentedExtClass
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun t ↦ (naiveCotangentIso f E₁ α₁).inv ≫ t)
    (presentedExtClass_comp_eq P₁ P₂ u θ g hu hred hlift hideal)).trans ?_
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun t ↦ t ≫ P₂.presentedExtClass) hinv)

end Derived

end PresentedSquareZeroExtension

namespace AlgebraSquareZeroExtension

variable {f : X ⟶ S}
  {G G' : SheafOfModules.{u} (ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)}

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- The class of a square-zero extension is natural in the coefficient module. Let `P` be a
square-zero extension of `f⁻¹𝒪_S`-algebras by `𝒢` and `P'` one by `𝒢'`, and let
`θ : 𝒪_{X'} ⟶ 𝒪_{X''}` be a morphism of `f⁻¹𝒪_S`-algebras over `𝒪_X` which on the square-zero
ideals is `g : 𝒢 ⟶ 𝒢'` under the two identifications. Then the class of `P'` in
`Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢')` is the class of `P` pushed forward along `g`. -/
theorem extClass_comp_eq_extClass_of_hom (P : AlgebraSquareZeroExtension f G)
    (P' : AlgebraSquareZeroExtension f G') (g : G ⟶ G')
    (θ : P.sheaf ⟶ P'.sheaf) (hbase : P.base ≫ θ = P'.base)
    (hred : θ ≫ P'.reduction = P.reduction)
    (hideal : ∀ (V : (Opens X.carrier)ᵒᵖ) (y : ↥(kernelIdeal P.reduction.hom V)),
      P'.ideal.app V ⟨θ.hom.app V y, kernelIdeal_le_comap P.reduction.hom P'.reduction.hom
        θ.hom (hom_of_comp_eq hred) V y.2⟩ = g.val.app V (P.ideal.app V y)) :
    P.toPresented.extClass ≫ ((DerivedCategory.singleFunctor _ 0).map g)⟦(1 : ℤ)⟧' =
      P'.toPresented.extClass := by
  have hlift : Functor.whiskerRight θ.hom (forget CommRingCat.{u}) ≫
      Functor.whiskerRight
        ((sheafToPresheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}).map
          P'.reduction) (forget CommRingCat.{u}) = P.generatorsMap := by
    rw [← Functor.whiskerRight_comp]
    exact congrArg
      (fun t : P.sheaf ⟶ X.sheaf ↦ Functor.whiskerRight t.hom (forget CommRingCat.{u})) hred
  refine Eq.trans ?_
    (P'.presentedBy_extClass (Functor.whiskerRight θ.hom (forget CommRingCat.{u})) hlift)
  refine PresentedSquareZeroExtension.extClass_comp_eq_extClass P.toPresented
    (P'.presentedBy (Functor.whiskerRight θ.hom (forget CommRingCat.{u})) hlift)
    (𝟙 _) θ g (Category.id_comp _) hred ?_ hideal
  exact PresentedSquareZeroExtension.freeAlgebraMap_comp_lift P.toPresented
    (P'.presentedBy (Functor.whiskerRight θ.hom (forget CommRingCat.{u})) hlift)
    (𝟙 _) θ hbase (by simp [toPresented, presentedBy])

end Derived

end AlgebraSquareZeroExtension

end AlgebraicGeometry.RingedSpaceThickening

end
