module

public import StacksFrontier.AlgebraicGeometry.Perfect.LimitHomDescent.System
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.MayerVietorisTriangle
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.ExtSequenceRestrictions
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.ExtensionByZeroBaseChangeDerived
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZero
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology

/-!
# Extension by zero and derived pullback along open immersions

For the inclusion `j : U ⟶ X` of an open subspace of a ringed space, extension by zero `j_!` is
left adjoint to restriction `j^*` and `j^* j_! ≅ id`; on unbounded derived categories the same
holds for the induced functors (Stacks 08BT). This file records the following consequences:

* restriction to `U` is bijective on morphisms out of `j_{U!}(E|_U)`;
* derived pullback along an open immersion with range `U` is bijective on morphisms out of an
  object isomorphic to `j_{U!}(E|_U)`, and carries `j_{U!}(E|_U)` to the pullback of `E`;
* derived pullback carries `j_{U!}(E|_U)` to `j_{U'!}((Lf^*E)|_{U'})` with `U' = f^{-1}U`;
* the Mayer--Vietoris triangle of Stacks 08BU at the concrete derived functors.

## Main results

* `Stacks.LimitHomDescent.bijective_pb_map_of_iso_extensionRestriction`: derived pullback along
  an open immersion is bijective on morphisms out of an extension by zero from its range.
* `Stacks.LimitHomDescent.pbExtensionRestrictionIso`: base change of extension by zero.
* `Stacks.LimitHomDescent.pbOpenImmersionExtensionRestrictionIso`: the pullback of
  `j_{U!}(E|_U)` along an open immersion with range `U` is the pullback of `E`.
* `Stacks.LimitHomDescent.exists_distTriang_extensionRestriction`: Stacks 08BU at the concrete
  functors.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace
open AlgebraicGeometry RingedSpaceModuleAdjunction ExtensionByZeroModules
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.ExtensionByZero (derivedRestriction derivedExtensionRestriction)
open Stacks.Cohomology.PerfectComplexTriangles (mapDerivedCategoryCompIso
  mapDerivedCategoryIsoOfNatIso)
open Stacks.DerivedPullback (schemeFactorIso schemeFactorHom)

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] preservesFiniteLimits_jStar preservesFiniteColimits_jStar

universe u

namespace Stacks.LimitHomDescent

section Instances

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X)

/-- Restriction `j^*` to an open `U` is an additive functor. -/
instance jStar_additive' : (jStar U O).Additive :=
  (Stacks.ExtensionByZero.jStar_additive_and_exact O U).1

/-- Extension by zero `j_!` from an open `U` is an additive functor. -/
instance jShriek_additive' : (jShriek U O).Additive :=
  (Stacks.ExtensionByZero.jShriek_additive_and_exact O U).1

attribute [instance] Stacks.ExtensionByZero.jStarPFL Stacks.ExtensionByZero.jStarPFC
  Stacks.ExtensionByZero.jShriekPFL Stacks.ExtensionByZero.jShriekPFC

end Instances

/-- Precomposition with an isomorphism is bijective. -/
theorem bijective_precomp {C : Type*} [Category* C] {A A' Z : C} (i : A ≅ A') :
    Function.Bijective (fun ψ : A' ⟶ Z => i.hom ≫ ψ) :=
  Function.bijective_iff_has_inverse.2
    ⟨fun ψ => i.inv ≫ ψ, i.inv_hom_id_assoc, i.hom_inv_id_assoc⟩

/-- A functor naturally isomorphic to one bijective on a morphism set is bijective on it. -/
theorem bijective_map_of_natIso {C D : Type*} [Category* C] [Category* D] {P Q : C ⥤ D}
    (β : P ≅ Q) {A A' : C} (h : Function.Bijective (fun φ : A ⟶ A' => Q.map φ)) :
    Function.Bijective (fun φ : A ⟶ A' => P.map φ) := by
  have key : (fun φ : A ⟶ A' => P.map φ) =
      (Iso.homCongr (β.app A).symm (β.app A').symm) ∘ (fun φ : A ⟶ A' => Q.map φ) := by
    funext φ
    simp only [Function.comp_apply, Iso.homCongr_apply, Iso.symm_inv, Iso.app_hom,
      Iso.symm_hom, Iso.app_inv]
    rw [← NatTrans.naturality_assoc, Iso.hom_inv_id_app, Category.comp_id]
  rw [key]
  exact (Equiv.bijective _).comp h

section Space

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X)

/-- `D(j_!) ⋙ D(j^*) ≅ 𝟭`, induced by the unit `𝟭 ≅ j_! ⋙ j^*`. -/
def restrictionExtensionIso :
    (jShriek U O).mapDerivedCategory ⋙ derivedRestriction O U ≅
      𝟭 (DerivedCategory (SheafOfModules.{u} (resRing U O))) :=
  have := isIso_jShriekAdjunction_unit U O
  (mapDerivedCategoryCompIso (jShriek U O) (jStar U O)).symm ≪≫
    mapDerivedCategoryIsoOfNatIso _ _ (asIso (jShriekAdjunction U O).unit).symm ≪≫
    Stacks.Homology.mapDerivedCategoryIdIso

/-- Restriction to `U` is bijective on morphisms out of an extension by zero `D(j_!)N`. -/
theorem bijective_restriction_map_extension
    (N : DerivedCategory (SheafOfModules.{u} (resRing U O)))
    (F : DerivedCategory (SheafOfModules.{u} O)) :
    Function.Bijective
      (fun φ : (jShriek U O).mapDerivedCategory.obj N ⟶ F => (derivedRestriction O U).map φ) := by
  let adj := (jShriekAdjunction U O).mapDerivedCategory
  have : IsIso adj.unit := adj.isIso_unit_of_iso (restrictionExtensionIso O U)
  have key : (fun φ : (jShriek U O).mapDerivedCategory.obj N ⟶ F =>
      (derivedRestriction O U).map φ) =
      (fun ψ => (asIso (adj.unit.app N)).symm.hom ≫ ψ) ∘ adj.homEquiv N F := by
    funext φ
    simp only [Function.comp_apply, Adjunction.homEquiv_unit, Iso.symm_hom, asIso_inv,
      IsIso.inv_hom_id_assoc]
  rw [key]
  exact (bijective_precomp (asIso (adj.unit.app N)).symm).comp (Equiv.bijective _)

/-- Restriction to `U` is bijective on morphisms out of an object isomorphic to
`D(j_!)D(j^*)E'`. -/
theorem bijective_restriction_map_of_iso {E E' : DerivedCategory (SheafOfModules.{u} O)}
    (e : E ≅ (derivedExtensionRestriction O U).obj E')
    (F : DerivedCategory (SheafOfModules.{u} O)) :
    Function.Bijective (fun φ : E ⟶ F => (derivedRestriction O U).map φ) := by
  have key : (fun φ : E ⟶ F => (derivedRestriction O U).map φ) =
      (fun ψ => ((derivedRestriction O U).mapIso e).hom ≫ ψ) ∘
        (fun φ : (derivedExtensionRestriction O U).obj E' ⟶ F =>
          (derivedRestriction O U).map φ) ∘ (fun φ : E ⟶ F => e.symm.hom ≫ φ) := by
    funext φ
    simp only [Function.comp_apply, Functor.mapIso_hom, Iso.symm_hom, Functor.map_comp,
      Iso.map_hom_inv_id_assoc]
  rw [key]
  exact (bijective_precomp ((derivedRestriction O U).mapIso e)).comp
    ((bijective_restriction_map_extension O U _ F).comp (bijective_precomp e.symm))

/-- `D(j^*)` of `D(j_!)D(j^*)E` is `D(j^*)E`. -/
def restrictionExtensionRestrictionIso (E : DerivedCategory (SheafOfModules.{u} O)) :
    (derivedRestriction O U).obj ((derivedExtensionRestriction O U).obj E) ≅
      (derivedRestriction O U).obj E :=
  (restrictionExtensionIso O U).app ((derivedRestriction O U).obj E)

/-- **Stacks 08BU at the concrete derived functors of extension by zero of a restriction.** -/
theorem exists_distTriang_extensionRestriction (V W : Opens X) (hVW : V ⊔ W = ⊤)
    (E : DerivedCategory (SheafOfModules.{u} O)) :
    ∃ (f : (derivedExtensionRestriction O (V ⊓ W)).obj E ⟶
        (derivedExtensionRestriction O V).obj E ⊞ (derivedExtensionRestriction O W).obj E)
      (g : (derivedExtensionRestriction O V).obj E ⊞ (derivedExtensionRestriction O W).obj E ⟶
        E)
      (h : E ⟶ ((derivedExtensionRestriction O (V ⊓ W)).obj E)⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang (DerivedCategory (SheafOfModules.{u} O)) := by
  obtain ⟨iV, iW, δ, -, -, hT⟩ := Stacks.ExtensionByZero.distinguished_extensionRestriction_triangle
    O V W hVW (derivedExtensionRestriction O V) (derivedExtensionRestriction O W)
    (derivedExtensionRestriction O (V ⊓ W))
    (Stacks.ExtensionByZero.derivedExtensionRestrictionFactorsh O V).inv
    (Stacks.ExtensionByZero.derivedExtensionRestrictionFactorsh O W).inv
    (Stacks.ExtensionByZero.derivedExtensionRestrictionFactorsh O (V ⊓ W)).inv
  exact ⟨_, _, _, hT E⟩

end Space

/-! ### Open immersions of schemes -/

section Schemes

variable {X Y Z : Scheme.{u}}

/-- Derived pullback along the inclusion of an open subscheme is derived restriction. -/
def pbOpensιIso (V : Y.Opens) :
    (derivedPullback V.ι.toLRSHom.toShHom :
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) ⥤
        DerivedCategory (SheafOfModules.{u} (resRing V (structureSheafRing Y.toRingedSpace)))) ≅
      derivedRestriction (structureSheafRing Y.toRingedSpace) V :=
  Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenRestrictionIso Y.toRingedSpace V

/-- **Derived pullback along an open immersion `ι` is bijective on morphisms out of an object
isomorphic to an extension by zero from the range of `ι`.** -/
theorem bijective_pb_map_of_iso_extensionRestriction (ι : Z ⟶ Y) [IsOpenImmersion ι]
    {E E' : DMod Y}
    (e : E ≅ (derivedExtensionRestriction (structureSheafRing Y.toRingedSpace) ι.opensRange).obj E')
    (F : DMod Y) :
    Function.Bijective (fun φ : E ⟶ F => (pb ι).map φ) := by
  have h1 : Function.Bijective (fun φ : E ⟶ F => (pb ι.opensRange.ι).map φ) :=
    bijective_map_of_natIso (pbOpensιIso ι.opensRange)
      (bijective_restriction_map_of_iso _ ι.opensRange e F)
  have h2 := Stacks.DerivedPullback.bijective_derivedPullback_map
    ι.isoOpensRange.hom.toLRSHom.toShHom ι.isoOpensRange.inv.toLRSHom.toShHom
    (congrArg (fun m => m.toLRSHom.toShHom) ι.isoOpensRange.hom_inv_id)
    (congrArg (fun m => m.toLRSHom.toShHom) ι.isoOpensRange.inv_hom_id)
    ((pb ι.opensRange.ι).obj E) ((pb ι.opensRange.ι).obj F)
  exact bijective_map_of_natIso
    (schemeFactorIso ι.isoOpensRange.hom ι.opensRange.ι ι ι.isoOpensRange_hom_ι).symm
    (h2.comp h1)

/-- **Extension by zero of a restriction commutes with derived pullback**, objectwise:
`Lf^*(j_{U!}j_U^*M) ≅ j_{U'!}j_{U'}^*(Lf^*M)` with `U' = f⁻¹U`. -/
def pbExtensionRestrictionIso (f : X ⟶ Y) (U : Y.Opens) (M : DMod Y) :
    (pb f).obj ((derivedExtensionRestriction (structureSheafRing Y.toRingedSpace) U).obj M) ≅
      (derivedExtensionRestriction (structureSheafRing X.toRingedSpace) (f ⁻¹ᵁ U)).obj
        ((pb f).obj M) :=
  (pb f).mapIso
      ((mapDerivedCategoryCompIso (jStar U (structureSheafRing Y.toRingedSpace))
        (jShriek U (structureSheafRing Y.toRingedSpace))).symm.app M) ≪≫
    (Stacks.Cohomology.ExtensionByZeroBaseChangeDerived.derivedPullbackExtensionRestrictionIso
      f.toLRSHom.toShHom U).app M ≪≫
    (mapDerivedCategoryCompIso (jStar (f ⁻¹ᵁ U) (structureSheafRing X.toRingedSpace))
      (jShriek (f ⁻¹ᵁ U) (structureSheafRing X.toRingedSpace))).app ((pb f).obj M)

/-- **Derived pullback along an open immersion is bijective on morphisms out of the derived
pullback of an extension by zero**, when the range of the immersion is the preimage of the
open. -/
theorem bijective_pb_map_of_extensionRestriction (f : X ⟶ Y) (ι : Z ⟶ X) [IsOpenImmersion ι]
    (U : Y.Opens) (hU : ι.opensRange = f ⁻¹ᵁ U) (M : DMod Y) (F : DMod X) :
    Function.Bijective (fun φ : (pb f).obj
        ((derivedExtensionRestriction (structureSheafRing Y.toRingedSpace) U).obj M) ⟶ F =>
      (pb ι).map φ) :=
  bijective_pb_map_of_iso_extensionRestriction ι
    (pbExtensionRestrictionIso f U M ≪≫ eqToIso (by rw [hU])) F

/-- **The pullback of `j_{U!}(E|_U)` along an open immersion with range `U` is the pullback of
`E`.** -/
def pbOpenImmersionExtensionRestrictionIso (ι : Z ⟶ Y) [IsOpenImmersion ι] (E : DMod Y) :
    (pb ι).obj ((derivedExtensionRestriction (structureSheafRing Y.toRingedSpace)
        ι.opensRange).obj E) ≅ (pb ι).obj E :=
  ((schemeFactorIso ι.isoOpensRange.hom ι.opensRange.ι ι ι.isoOpensRange_hom_ι).app _).symm ≪≫
    (pb ι.isoOpensRange.hom).mapIso
      ((pbOpensιIso ι.opensRange).app _ ≪≫
        restrictionExtensionRestrictionIso _ ι.opensRange E ≪≫
        ((pbOpensιIso ι.opensRange).app E).symm) ≪≫
    (schemeFactorIso ι.isoOpensRange.hom ι.opensRange.ι ι ι.isoOpensRange_hom_ι).app E

end Schemes

end Stacks.LimitHomDescent

end
