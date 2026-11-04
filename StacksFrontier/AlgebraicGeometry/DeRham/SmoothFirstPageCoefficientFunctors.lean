module

public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothFirstPageIdentification
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothFirstPageFlat
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatCohomologyNaturality
public import StacksFrontier.Homology.TensorComplex.BifunctorSingleLeftComplexNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.TotalComplexFlip

/-!
# The first page of 0FMM with an arbitrary coefficient module

Let `f : X ⟶ Y` be a morphism of schemes over a base `g : Y ⟶ S`. The first page of the spectral
sequence of [Stacks, Tag 0FMM] is computed from the graded pieces
`gr^kΩ^•_{X/S} = f^{-1}Ω^k_{Y/S}[-k] ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y}` of Section 0FMK by the projection
formula and, in the flat case of [Stacks, Tag 0FMN], by a "tiny argument". To compare the action of
local forms on the two sides one needs these identifications **natural in the coefficient
module**, with `Ω^k_{Y/S}` replaced by an arbitrary `𝒪_Y`-module `M`. This file sets up the
objects and the naturality of the parts that do not involve the projection formula.

## Main definitions

* `Stacks.DeRhamSmooth.coefficientTargetTensor`: `M ↦ f^{-1}M ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y}`.
* `Stacks.DeRhamSmooth.coefficientTargetComplex`: `M ↦ f^{-1}M[-k] ⊗ Ω^•_{X/Y}`, read over
  `(f ∘ g)^{-1}𝒪_S`; at `Ω^k_{Y/S}` it is `gradedTargetComplex f g k`.
* `Stacks.DeRhamSmooth.coefficientFirstPageSource`: `M ↦ R^{k + q}f_*(f^{-1}M[-k] ⊗ Ω^•_{X/Y})`.
* `Stacks.DeRhamSmooth.coefficientFirstPageFlat`: `M ↦ M ⊗_{𝒪_Y} ℋ^q_dR(X/Y)`; at `Ω^k_{Y/S}` it
  is `deRhamFirstPageFlat f g k q`.
* `Stacks.DeRhamSmooth.coefficientTargetTensorIsoTensorComplex`: `f^{-1}M ⊗ Ω^•_{X/Y}` as a total
  tensor complex, natural in `M`.

## Main results

* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.homology_derivedPushforward_square_naturality`
  and `Stacks.DeRhamSmooth.higherDirectImageCoefficientRestrictionIso_hom_naturality`: the change
  of coefficients of the higher direct images is natural in the complex.
* `Stacks.Intersection.Diagonal.derivedPullbackSingleIsoOfFlat_hom_naturality`.
* `Stacks.DeRhamSmooth.coefficientTargetTensorIsoTensorComplex_hom_naturality`.

## References

* [Stacks Project, Tag 0FMM](https://stacks.math.columbia.edu/tag/0FMM)
* [Stacks Project, Tag 0FMN](https://stacks.math.columbia.edu/tag/0FMN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.FilteredComplex (higherDirectImage)

universe u

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf

namespace Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes

/-- `derivedPushforwardQIso` is natural in the complex. -/
theorem derivedPushforwardQIso_hom_naturality {A B : RingedSpace.{u, u}} (φ : A ⟶ B)
    [PreservesFiniteColimits (modulePushforward φ)]
    {C C' : CochainComplex (SheafOfModules.{u} (structureSheafRing A)) ℤ} (c : C ⟶ C') :
    (derivedPushforward φ).map (DerivedCategory.Q.map c) ≫ (derivedPushforwardQIso φ C').hom =
      (derivedPushforwardQIso φ C).hom ≫ DerivedCategory.Q.map
        (((modulePushforward φ).mapHomologicalComplex (ComplexShape.up ℤ)).map c) := by
  simp only [derivedPushforwardQIso, Iso.trans_hom, Iso.app_hom, Category.assoc]
  rw [NatTrans.naturality_assoc]
  exact congrArg _ ((modulePushforward φ).mapDerivedCategoryFactors.hom.naturality c)

end Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes

namespace Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

/-- Transport along an equality of morphisms of ringed spaces is natural for the derived
pushforwards along them. -/
theorem derivedPushforward_map_eqToHom {A B : RingedSpace.{u, u}} {φ ψ : A ⟶ B}
    (h : φ = ψ) {K K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing A))}
    (c : K ⟶ K') :
    (derivedPushforward φ).map c ≫
        eqToHom (congrArg (fun φ => (derivedPushforward.{u} φ).obj K') h) =
      eqToHom (congrArg (fun φ => (derivedPushforward.{u} φ).obj K) h) ≫
        (derivedPushforward ψ).map c := by
  subst h
  simp

open Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes in
/-- **Naturality of the comparison of two composites of direct images, one of them exact on
each side.** For a commutative square `a ≫ b = c ≫ d` of morphisms of ringed spaces with `a_*`
right exact and `d_*` exact, the isomorphism
`H^n(Rb_*(a_*K)) ≅ H^n(R(a ≫ b)_*K) = H^n(R(c ≫ d)_*K) ≅ d_*H^n(Rc_*K)` is natural in the complex
`K`. This is the shape of `Stacks.DeRhamSmooth.higherDirectImageCoefficientRestrictionIso`. -/
theorem homology_derivedPushforward_square_naturality {A B C D : RingedSpace.{u, u}}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ C) (d : C ⟶ D) (h : a ≫ b = c ≫ d)
    [PreservesFiniteColimits (modulePushforward a)]
    [PreservesFiniteLimits (modulePushforward d)] [PreservesFiniteColimits (modulePushforward d)]
    {K K' : CochainComplex (SheafOfModules.{u} (structureSheafRing A)) ℤ} (k : K ⟶ K') (n : ℤ) :
    (DerivedCategory.homologyFunctor _ n).map ((derivedPushforward b).map
        (DerivedCategory.Q.map
          (((modulePushforward a).mapHomologicalComplex (ComplexShape.up ℤ)).map k))) ≫
        ((DerivedCategory.homologyFunctor _ n).mapIso
          ((derivedPushforward b).mapIso (derivedPushforwardQIso a K').symm ≪≫
            (derivedPushforwardCompIso a b).app _ ≪≫
            eqToIso (congrArg
              (fun φ => (derivedPushforward.{u} φ).obj (DerivedCategory.Q.obj K')) h) ≪≫
            ((derivedPushforwardCompIso c d).app _).symm) ≪≫
          derivedPushforwardHomologyFunctorObjIso d n _).hom =
      ((DerivedCategory.homologyFunctor _ n).mapIso
          ((derivedPushforward b).mapIso (derivedPushforwardQIso a K).symm ≪≫
            (derivedPushforwardCompIso a b).app _ ≪≫
            eqToIso (congrArg
              (fun φ => (derivedPushforward.{u} φ).obj (DerivedCategory.Q.obj K)) h) ≪≫
            ((derivedPushforwardCompIso c d).app _).symm) ≪≫
          derivedPushforwardHomologyFunctorObjIso d n _).hom ≫
        (modulePushforward d).map ((DerivedCategory.homologyFunctor _ n).map
          ((derivedPushforward c).map (DerivedCategory.Q.map k))) := by
  have i₁ : DerivedCategory.Q.map
        (((modulePushforward a).mapHomologicalComplex (ComplexShape.up ℤ)).map k) ≫
        (derivedPushforwardQIso a K').inv =
      (derivedPushforwardQIso a K).inv ≫ (derivedPushforward a).map (DerivedCategory.Q.map k) := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact (derivedPushforwardQIso_hom_naturality a k).symm
  have h₂ := (derivedPushforwardCompIso a b).hom.naturality (DerivedCategory.Q.map k)
  have h₃ := derivedPushforward_map_eqToHom h (DerivedCategory.Q.map k)
  have h₄ := (derivedPushforwardCompIso c d).inv.naturality (DerivedCategory.Q.map k)
  have h₅ := (derivedPushforwardHomologyFunctorIso d n).hom.naturality
    ((derivedPushforward c).map (DerivedCategory.Q.map k))
  dsimp at h₂ h₄ h₅
  have inner : (derivedPushforward b).map (DerivedCategory.Q.map
        (((modulePushforward a).mapHomologicalComplex (ComplexShape.up ℤ)).map k)) ≫
        (derivedPushforward b).map (derivedPushforwardQIso a K').inv ≫
        (derivedPushforwardCompIso a b).hom.app (DerivedCategory.Q.obj K') ≫
        eqToHom (congrArg (fun φ => (derivedPushforward.{u} φ).obj (DerivedCategory.Q.obj K')) h) ≫
        (derivedPushforwardCompIso c d).inv.app (DerivedCategory.Q.obj K') =
      ((derivedPushforward b).map (derivedPushforwardQIso a K).inv ≫
        (derivedPushforwardCompIso a b).hom.app (DerivedCategory.Q.obj K) ≫
        eqToHom (congrArg (fun φ => (derivedPushforward.{u} φ).obj (DerivedCategory.Q.obj K)) h) ≫
        (derivedPushforwardCompIso c d).inv.app (DerivedCategory.Q.obj K)) ≫
        (derivedPushforward d).map ((derivedPushforward c).map (DerivedCategory.Q.map k)) := by
    have j₁ := congrArg (derivedPushforward b).map i₁
    simp only [Functor.map_comp] at j₁
    simp only [reassoc_of% j₁, reassoc_of% h₂, reassoc_of% h₃, h₄, Category.assoc]
  have inner' := congrArg (DerivedCategory.homologyFunctor _ n).map inner
  simp only [Functor.map_comp, Category.assoc] at inner'
  simp only [derivedPushforwardHomologyFunctorObjIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_hom, eqToIso.hom, Iso.app_inv, Category.assoc, Functor.map_comp]
  simp only [reassoc_of% inner', h₅]

end Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

namespace Stacks.Intersection.Diagonal

/-- `derivedPullbackSingleIsoOfFlat` is natural in the module. -/
theorem derivedPullbackSingleIsoOfFlat_hom_naturality {Y W : RingedSpace.{u, u}} (g : W ⟶ Y)
    [PreservesFiniteLimits (modulePullback g)]
    {M M' : SheafOfModules.{u} (structureSheafRing Y)} (φ : M ⟶ M') :
    (derivedPullback g).map ((DerivedCategory.singleFunctor _ 0).map φ) ≫
        (derivedPullbackSingleIsoOfFlat g M').hom =
      (derivedPullbackSingleIsoOfFlat g M).hom ≫
        (DerivedCategory.singleFunctor _ 0).map ((modulePullback g).map φ) := by
  have : PreservesFiniteColimits (modulePullback g) :=
    RingedSpaceModuleAdjunction.preservesFiniteColimits_modulePullback g
  have h₁ := (AlgebraicGeometry.SpecField.derivedPullbackMapDerivedIso g).hom.naturality
    ((DerivedCategory.singleFunctor _ 0).map φ)
  have h₂ := ((modulePullback g).mapDerivedCategorySingleFunctor 0).hom.naturality φ
  dsimp only [Functor.comp_map] at h₂
  simp only [derivedPullbackSingleIsoOfFlat, Iso.trans_hom, Iso.app_hom, reassoc_of% h₁, h₂,
    Category.assoc]

end Stacks.Intersection.Diagonal

namespace Stacks.DeRhamSmooth


open Stacks.DeRhamDirectImage

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

attribute [local instance] Stacks.DeRhamDirectImage.abelian_modules

/-- **`higherDirectImageCoefficientRestrictionIso` is natural in the complex.** -/
theorem higherDirectImageCoefficientRestrictionIso_hom_naturality
    {C C' : CochainComplex (Modules (inverseImageBase f)) ℤ} (c : C ⟶ C') (n : ℤ) :
    (DerivedCategory.homologyFunctor _ n).map ((derivedRelativePushforward f g).map
        (DerivedCategory.Q.map
          (((coefficientRestriction f g).mapHomologicalComplex (ComplexShape.up ℤ)).map c))) ≫
        (higherDirectImageCoefficientRestrictionIso f g C' n).hom =
      (higherDirectImageCoefficientRestrictionIso f g C n).hom ≫
        (pushforward (toInverseImageBase g)).map
          ((DerivedCategory.homologyFunctor (Modules Y.toRingedSpace) n).map
            ((derivedPushforward (inverseImageBaseProjection f)).map (DerivedCategory.Q.map c))) :=
  let : PreservesFiniteLimits (modulePushforward (toInverseImageBase g)) :=
    inferInstanceAs (PreservesFiniteLimits (pushforward (toInverseImageBase g)))
  let : PreservesFiniteColimits (modulePushforward (toInverseImageBase g)) :=
    inferInstanceAs (PreservesFiniteColimits (pushforward (toInverseImageBase g)))
  let : PreservesFiniteColimits (modulePushforward (coefficientRingChange f g)) :=
    preservesFiniteColimits_coefficientRestriction f g
  homology_derivedPushforward_square_naturality (coefficientRingChange f g) (relativeBase f g)
    (inverseImageBaseProjection f) (toInverseImageBase g)
    (coefficientRingChange_comp_relativeBase f g) c n

/-! ### The first page with a general coefficient module -/

/-- **`f^{-1}M ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y}`**, functorially in the `𝒪_Y`-module `M`: the relative de
Rham complex of `f` tensored degreewise with the inverse image of `M`. At `M = Ω^k_{Y/S}` it is
`gradedTargetTensor f g k`. -/
def coefficientTargetTensor :
    Modules Y.toRingedSpace ⥤ CochainComplex (Modules (inverseImageBase f)) ℤ where
  obj M := ((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase f).sheaf).obj
      ((_root_.pullback (inverseImageBaseProjection f)).obj M)).mapHomologicalComplex
        (ComplexShape.up ℤ) |>.obj (deRhamCochainComplex f)
  map φ := (NatTrans.mapHomologicalComplex
      ((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase f).sheaf).map
        ((_root_.pullback (inverseImageBaseProjection f)).map φ)) (ComplexShape.up ℤ)).app _
  map_id M := by
    simp only [CategoryTheory.Functor.map_id, NatTrans.mapHomologicalComplex_id]
    rfl
  map_comp φ ψ := by
    simp only [CategoryTheory.Functor.map_comp, NatTrans.mapHomologicalComplex_comp]
    rfl

/-- **`f^{-1}M[-k] ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y}`, read over `(f ∘ g)^{-1}𝒪_S`**, functorially in the
`𝒪_Y`-module `M`. At `M = Ω^k_{Y/S}` it is `gradedTargetComplex f g k`. -/
abbrev coefficientTargetComplex (k : ℕ) :
    Modules Y.toRingedSpace ⥤ CochainComplex (Modules (inverseImageBase (f ≫ g))) ℤ :=
  coefficientTargetTensor f ⋙
    CategoryTheory.shiftFunctor (CochainComplex (Modules (inverseImageBase f)) ℤ) (-(k : ℤ)) ⋙
    (coefficientRestriction f g).mapHomologicalComplex (ComplexShape.up ℤ)

/-- `coefficientTargetComplex` at `Ω^k_{Y/S}` is the target of Section 0FMK. -/
theorem coefficientTargetComplex_obj_relativeDifferentialForms (k : ℕ) :
    (coefficientTargetComplex f g k).obj
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)) =
      gradedTargetComplex f g k :=
  rfl

/-- **`R^{k + q}f_*(f^{-1}M[-k] ⊗ Ω^•_{X/Y})`**, functorially in the `𝒪_Y`-module `M`. -/
abbrev coefficientFirstPageSource (k : ℕ) (q : ℤ) :
    Modules Y.toRingedSpace ⥤ Modules (inverseImageBase g) :=
  coefficientTargetComplex f g k ⋙ DerivedCategory.Q ⋙ derivedRelativePushforward f g ⋙
    DerivedCategory.homologyFunctor _ ((k : ℤ) + q)

/-- **`M ⊗_{𝒪_Y} ℋ^q_dR(X/Y)`, read over `g^{-1}𝒪_S`**, functorially in the `𝒪_Y`-module `M`. At
`M = Ω^k_{Y/S}` it is `deRhamFirstPageFlat f g k q`. -/
abbrev coefficientFirstPageFlat (q : ℤ) :
    Modules Y.toRingedSpace ⥤ Modules (inverseImageBase g) :=
  (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).flip.obj (deRhamCohomologySheaf f q) ⋙
    pushforward (toInverseImageBase g)

/-- `coefficientFirstPageSource` at `Ω^k_{Y/S}` is the higher direct image of the target of
Section 0FMK. -/
theorem coefficientFirstPageSource_obj_relativeDifferentialForms (k : ℕ) (q : ℤ) :
    (coefficientFirstPageSource f g k q).obj
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)) =
      higherDirectImage (derivedRelativePushforward f g) (gradedTargetComplex f g k)
        ((k : ℤ) + q) := rfl

/-- `coefficientFirstPageFlat` at `Ω^k_{Y/S}` is `deRhamFirstPageFlat f g k q`. -/
theorem coefficientFirstPageFlat_obj_relativeDifferentialForms (k : ℕ) (q : ℤ) :
    (coefficientFirstPageFlat f g q).obj
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)) =
      deRhamFirstPageFlat f g (k : ℤ) q := rfl


/-- **`f^{-1}M ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y}` is the total tensor complex of `Ω^•_{X/Y}` with `f^*M` in
degree zero**, for an arbitrary `𝒪_Y`-module `M`. At `M = Ω^k_{Y/S}` this is
`gradedTargetTensorIsoTensorComplex f g k`. -/
def coefficientTargetTensorIsoTensorComplex (M : Modules Y.toRingedSpace) :
    (coefficientTargetTensor f).obj M ≅
      ((Stacks.SheafOfModules.Tensor.tensorComplex (inverseImageBase f).sheaf).obj
          (deRhamCochainComplex f)).obj
        ((CochainComplex.singleFunctor (Modules (inverseImageBase f)) 0).obj
          ((modulePullback (inverseImageBaseProjection f)).obj M)) :=
  HomologicalComplex.singleLeftIsoMapBifunctor
      (Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase f).sheaf)
      ((_root_.pullback (inverseImageBaseProjection f)).obj M) (deRhamCochainComplex f) ≪≫
    Stacks.SheafOfModules.Tensor.tensorComplexFlipIso (inverseImageBase f).sheaf _ _

/-- At `Ω^k_{Y/S}`, `coefficientTargetTensorIsoTensorComplex` is
`gradedTargetTensorIsoTensorComplex f g k`. -/
theorem coefficientTargetTensorIsoTensorComplex_relativeDifferentialForms (k : ℕ) :
    coefficientTargetTensorIsoTensorComplex f
    (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)) =
      gradedTargetTensorIsoTensorComplex f g k := rfl

/-- **`coefficientTargetTensorIsoTensorComplex` is natural in the module.** -/
theorem coefficientTargetTensorIsoTensorComplex_hom_naturality {M M' : Modules Y.toRingedSpace}
    (φ : M ⟶ M') :
    (coefficientTargetTensor f).map φ ≫ (coefficientTargetTensorIsoTensorComplex f M').hom =
      (coefficientTargetTensorIsoTensorComplex f M).hom ≫
        ((Stacks.SheafOfModules.Tensor.tensorComplex (inverseImageBase f).sheaf).obj
            (deRhamCochainComplex f)).map
          ((CochainComplex.singleFunctor (Modules (inverseImageBase f)) 0).map
            ((modulePullback (inverseImageBaseProjection f)).map φ)) := by
  have h₁ := HomologicalComplex.singleLeftIsoMapBifunctor_hom_naturality_single
    (Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase f).sheaf)
    ((_root_.pullback (inverseImageBaseProjection f)).map φ) (deRhamCochainComplex f)
  have h₂ := Stacks.SheafOfModules.Tensor.tensorComplexFlipIso_hom_naturality
    (inverseImageBase f).sheaf
    ((CochainComplex.singleFunctor (Modules (inverseImageBase f)) 0).map
      ((_root_.pullback (inverseImageBaseProjection f)).map φ)) (𝟙 (deRhamCochainComplex f))
  dsimp only [coefficientTargetTensorIsoTensorComplex, Iso.trans_hom]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₁).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₂).trans (Category.assoc _ _ _).symm)))

end Stacks.DeRhamSmooth

end
