module

public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunctionAcyclic
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedHigherDirectImageComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraExtensionPushoutEquivalence

/-!
# `Ext` groups of quasi-coherent modules on a represented algebraic space

Let `U` be an object of the big fppf site over `S`, with underlying scheme `T`, and let
`h_U = yoneda.obj U` be the algebraic space it represents. The associated-module functor
`(-)^a : Mod(𝒪_T) ⥤ Mod(𝒪_{h_U})` of Stacks 03DU (4) is exact and left adjoint to the direct image
`ε_*` to the Zariski site. For `𝓖` quasi-coherent the unit `𝓖 ⟶ ε_*(𝓖^a)` is an isomorphism
(Stacks 0GN7) and `𝓖^a` is `ε_*`-acyclic (Stacks 03DW), so `(-)^a` is bijective on
`Ext^n(𝓕, 𝓖)` for every `𝓕`. The same holds for the restriction of modules to the `Type u` model
of the small étale site of an algebraic space, an equivalence of categories.

## Main results

* `AlgebraicGeometry.Space.isIso_representedAssociatedModuleZariskiAdjunction_unit_app`: the unit
  of `(-)^a ⊣ ε_*` is an isomorphism at a quasi-coherent module.
* `AlgebraicGeometry.Space.bijective_mapExtAddHom_representedAssociatedModule`:
  `Ext^n(𝓕, 𝓖) ≃ Ext^n(𝓕^a, 𝓖^a)` for `𝓖` quasi-coherent.
* `AlgebraicGeometry.Space.bijective_mapExtAddHom_modelModulesEquiv`: restriction of
  modules to the model of the small étale site is bijective on `Ext` groups.

## References

* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 015D](https://stacks.math.columbia.edu/tag/015D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

attribute [local instance 5000] SheafOfModules.instAbelian

universe w w' u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- **The unit of `(-)^a ⊣ ε_*` is an isomorphism at a quasi-coherent module** (Stacks 0GN7): it
is the unit of the associated-module adjunction of the small étale site of the scheme, followed
by the image of the unit of an equivalence. -/
theorem isIso_representedAssociatedModuleZariskiAdjunction_unit_app
    (F : ((BigFppfOver.toScheme B S hS).obj U).Modules) (hF : F.IsQuasicoherent) :
    IsIso ((representedAssociatedModuleZariskiAdjunction B S hS U).unit.app F) := by
  have := _root_.AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⟨F, hF⟩
  rw [show representedAssociatedModuleZariskiAdjunction B S hS U =
      (_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).comp
        (representedModuleEquivalence.{u, u} B S hS U).toAdjunction from rfl,
    Adjunction.comp_unit_app]
  have : IsIso ((representedModuleEquivalence.{u, u} B S hS U).toAdjunction.unit.app
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj F)) := by
    rw [Equivalence.toAdjunction_unit]
    infer_instance
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance (Functor.map_isIso _ _)

/-- **`(-)^a` is bijective on `Ext^n(𝓕, 𝓖)` for `𝓖` quasi-coherent.** The unit of
`(-)^a ⊣ ε_*` is invertible at `𝓖` and `𝓖^a`, being quasi-coherent, is `ε_*`-acyclic, so
`Stacks.ExtAdjunction.mapExtAddHom_bijective_of_isZero_rightDerived` applies. -/
theorem bijective_mapExtAddHom_representedAssociatedModule
    [HasExt.{w} ((BigFppfOver.toScheme B S hS).obj U).Modules]
    [HasExt.{w'} (Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))]
    (F G : ((BigFppfOver.toScheme B S hS).obj U).Modules) (hG : G.IsQuasicoherent) (n : ℕ) :
    Function.Bijective
      ((representedAssociatedModule B S hS U (isAlgebraicSpace_yoneda B S hS U)).mapExtAddHom
        F G n) := by
  let _ := HasDerivedCategory.standard ((BigFppfOver.toScheme B S hS).obj U).Modules
  let _ := HasDerivedCategory.standard
    (Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
  have := enoughInjectives_modules B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
  have := hasInjectiveResolutions_modules B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
  have := (representedAssociatedModuleZariskiAdjunction B S hS U).isRightAdjoint
  exact Stacks.ExtAdjunction.mapExtAddHom_bijective_of_isZero_rightDerived
    (representedAssociatedModuleZariskiAdjunction B S hS U) F G
    (isIso_representedAssociatedModuleZariskiAdjunction_unit_app B S hS U G hG)
    (fun p hp => isZero_rightDerived_representedZariskiDirectImage_of_isQuasicoherentOnSite
      B S hS U _ (isQuasicoherentOnSite_representedAssociatedModule B S hS U _ G hG) p hp) n

/-- **Restriction of modules to the model of the small étale site is bijective on `Ext`
groups**: it is the functor of an equivalence of abelian categories, the Comparison Lemma
`AlgebraicGeometry.Space.modelModulesEquiv`. -/
theorem bijective_mapExtAddHom_modelModulesEquiv (X : AlgebraicSpaces B S hS)
    [HasExt.{w} (Modules.{u, u} B S hS X.1 X.2)] [HasExt.{w'} (RestrictedModelModules B S hS X)]
    (M N : Modules.{u, u} B S hS X.1 X.2) (n : ℕ) :
    Function.Bijective ((modelModulesEquiv B S hS X).functor.mapExtAddHom M N n) :=
  Stacks.ExtAdjunction.mapExtAddHom_bijective (modelModulesEquiv B S hS X).toAdjunction
    M N n

/-- **`Ext^n(𝓕, 𝓖) = 0` gives `Ext^n(𝓕^a, 𝓖^a) = 0` on the model** of the small étale site of the
represented algebraic space, for `𝓖` quasi-coherent: the associated-module functor and the
restriction to the model are both bijective on `Ext` groups. -/
theorem subsingleton_ext_modelModulesEquiv_representedAssociatedModule
    [HasExt.{w} ((BigFppfOver.toScheme B S hS).obj U).Modules]
    [HasExt.{w'} (RestrictedModelModules B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)]
    (F G : ((BigFppfOver.toScheme B S hS).obj U).Modules) (hG : G.IsQuasicoherent) (n : ℕ)
    (h : Subsingleton (Ext.{w} F G n)) :
    Subsingleton (Ext.{w'}
      ((modelModulesEquiv B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).functor.obj
        ((representedAssociatedModule B S hS U (isAlgebraicSpace_yoneda B S hS U)).obj F))
      ((modelModulesEquiv B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).functor.obj
        ((representedAssociatedModule B S hS U (isAlgebraicSpace_yoneda B S hS U)).obj G)) n) := by
  let _ := HasExt.standard
    (Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
  have : Subsingleton (Ext.{u + 1}
      ((representedAssociatedModule B S hS U (isAlgebraicSpace_yoneda B S hS U)).obj F)
      ((representedAssociatedModule B S hS U (isAlgebraicSpace_yoneda B S hS U)).obj G) n) :=
    (bijective_mapExtAddHom_representedAssociatedModule.{w, u + 1} B S hS U F G hG n).2.subsingleton
  exact (bijective_mapExtAddHom_modelModulesEquiv.{u + 1, w'} B S hS
    ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ _ _ n).2.subsingleton

end AlgebraicGeometry.Space

end
