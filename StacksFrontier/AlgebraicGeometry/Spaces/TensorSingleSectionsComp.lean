module

public import
  StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffineBaseDerivedSectionsPushforwardIsoComp
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedModulePushforwardSingle
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.CategoryTheory.Functor.TensorSectionsPasting
public import StacksFrontier.Homology.DerivedCategory.StandardModuleCatModel

/-!
# `RΓ(X, E ⊗^𝐋 (i_*F)[0]) ⟶ RΓ(X₀, Li^*E ⊗^𝐋 F[0])` along a factorization `i = t ≫ i'`

Let `X₀ --t--> X₁ --i'--> X` be affine morphisms of algebraic spaces with composite `i`, lying over
morphisms `U₀ ⟶ U₁ ⟶ U` of affine objects of the big fppf site, with rings `R → R₁ → R₀`. For a
quasi-coherent `𝒪_{X₀}`-module `F` the identification

`ψ_i : RΓ_R(X, E ⊗^𝐋 (i_*F)[0]) ⟶ RΓ_{R₀}(X₀, Li^*E ⊗^𝐋 F[0])`

is the comparison `(i_*F)[0] ≅ Ri_*(F[0])`, the projection formula of `i` and the identification
`RΓ(X, Ri_* -) ≅ RΓ(X₀, -)` (`affineBaseDerivedSectionsPushforwardIso`). This file proves that, for
a map `a : F₁ ⟶ t_*F` of `𝒪_{X₁}`-modules with `F₁` quasi-coherent, `ψ_i` after
`RΓ(X, E ⊗^𝐋 (i'_*a ≫ (i'_*t_*F ≅ i_*F))[0])` is `ψ_{i'}` at `F₁` followed by the analogous map
along `t` and the comparison of restrictions of scalars `R → R₁ → R₀`, given the compatibility of
the comparisons `(f_*F)[0] ⟶ Rf_*(F[0])` with the composition `i = t ≫ i'`.

Everything is stated over variable spaces, so that its instances in a fixed situation are checked
by instantiation.

## Main results

* `AlgebraicGeometry.Space.tensorSingleSectionsNatTrans`: `ψ_i`.
* `AlgebraicGeometry.Space.tensorSingleSectionsTransitionNatTrans`: the map along `t`.
* `AlgebraicGeometry.Space.tensorSingleSectionsNatTrans_comp`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U U₁ U₀ : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U₁)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U₀)]
  {X X₁ X₀ : AlgebraicSpaces B S hS}
  (h : X ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
  (h₁ : X₁ ⟶ ⟨yoneda.obj U₁, isAlgebraicSpace_yoneda B S hS U₁⟩)
  (h₀ : X₀ ⟶ ⟨yoneda.obj U₀, isAlgebraicSpace_yoneda B S hS U₀⟩)
  (g₁ : U₁ ⟶ U) (gt : U₀ ⟶ U₁) (g₀ : U₀ ⟶ U) (hg : gt ≫ g₁ = g₀)
  (i₁ : X₁ ⟶ X) (t : X₀ ⟶ X₁) (i₀ : X₀ ⟶ X) (hi : t ≫ i₁ = i₀)
  (w₁ : i₁ ≫ h = h₁ ≫ representedSpaceMap B S hS g₁)
  (wt : t ≫ h₁ = h₀ ≫ representedSpaceMap B S hS gt)
  (w₀ : i₀ ≫ h = h₀ ≫ representedSpaceMap B S hS g₀)
  (hc : (representedAffineCommRingCatHom B S hS g₀).hom =
    (representedAffineCommRingCatHom B S hS gt).hom.comp
      (representedAffineCommRingCatHom B S hS g₁).hom)
  (hi₁ : IsAffineHom B S hS i₁.hom) (hi₀ : IsAffineHom B S hS i₀.hom)
  (F : Modules.{u, u} B S hS X₀.1 X₀.2) (hF : F.IsQuasicoherentOnSite)
  (F₁ : Modules.{u, u} B S hS X₁.1 X₁.2) (hF₁ : F₁.IsQuasicoherentOnSite)
  (a : F₁ ⟶ (modulePushforward B S hS t).obj F)

/-- **`ψ_i : RΓ_R(X, E ⊗^𝐋 (i_*F)[0]) ⟶ RΓ_{R₀}(X₀, Li^*E ⊗^𝐋 F[0])`**, natural in `E`, for an
affine morphism `i` and a quasi-coherent `F`: the comparison `(i_*F)[0] ≅ Ri_*(F[0])`, the
projection formula of `i` and `affineBaseDerivedSectionsPushforwardIso`. -/
def tensorSingleSectionsNatTrans :
    (smallEtaleDerivedTensor B S hS X).flip.obj
        ((DerivedCategory.singleFunctor _ 0).obj ((modulePushforward B S hS i₀).obj F)) ⋙
      (derivedModulePushforward B S hS h ⋙ representedAffineDerivedSections B S hS U) ⟶
    smallEtaleDerivedModulePullback B S hS i₀ ⋙
      (smallEtaleDerivedTensor B S hS X₀).flip.obj ((DerivedCategory.singleFunctor _ 0).obj F) ⋙
      (derivedModulePushforward B S hS h₀ ⋙ representedAffineDerivedSections B S hS U₀) ⋙
      StacksDraft.ringRestrictScalars (representedAffineCommRingCatHom B S hS g₀).hom :=
  Functor.whiskerRight ((smallEtaleDerivedTensor B S hS X).flip.map
          (derivedModulePushforwardSingleIsoOfIsAffineHom B S hS i₀ hi₀ F hF).inv)
          (derivedModulePushforward B S hS h ⋙ representedAffineDerivedSections B S hS U) ≫
        Functor.whiskerRight (smallEtaleProjectionFormulaSndNatTrans i₀
            ((DerivedCategory.singleFunctor _ 0).obj F))
          (derivedModulePushforward B S hS h ⋙ representedAffineDerivedSections B S hS U) ≫
        Functor.whiskerLeft (smallEtaleDerivedModulePullback B S hS i₀ ⋙
            (smallEtaleDerivedTensor B S hS X₀).flip.obj
              ((DerivedCategory.singleFunctor _ 0).obj F))
          (affineBaseDerivedSectionsPushforwardIso B S hS g₀ h h₀ i₀ w₀).hom

/-- The map along `t` in `tensorSingleSectionsNatTrans_comp`: `RΓ(X₁, Li'^*E ⊗^𝐋 -)` of
`a[0] ≫ ((t_*F)[0] ⟶ Rt_*(F[0]))`, the projection formula of `t`, the identification of
`RΓ(X₁, Rt_* -)` with `RΓ(X₀, -)`, `Lt^*Li'^* ≅ Li^*`, and the comparison of restrictions of scalars
along `R → R₁ → R₀`. -/
def tensorSingleSectionsTransitionNatTrans :
    smallEtaleDerivedModulePullback B S hS i₁ ⋙
      (smallEtaleDerivedTensor B S hS X₁).flip.obj ((DerivedCategory.singleFunctor _ 0).obj F₁) ⋙
      (derivedModulePushforward B S hS h₁ ⋙ representedAffineDerivedSections B S hS U₁) ⋙
      StacksDraft.ringRestrictScalars (representedAffineCommRingCatHom B S hS g₁).hom ⟶
    smallEtaleDerivedModulePullback B S hS i₀ ⋙
      (smallEtaleDerivedTensor B S hS X₀).flip.obj ((DerivedCategory.singleFunctor _ 0).obj F) ⋙
      (derivedModulePushforward B S hS h₀ ⋙ representedAffineDerivedSections B S hS U₀) ⋙
      StacksDraft.ringRestrictScalars (representedAffineCommRingCatHom B S hS g₀).hom :=
      Functor.whiskerRight
        (Functor.whiskerLeft (smallEtaleDerivedModulePullback B S hS i₁)
            (Functor.whiskerRight
              ((smallEtaleDerivedTensor B S hS X₁).flip.map
                  ((DerivedCategory.singleFunctor _ 0).map a ≫
                    (modulePushforwardSingleToDerived B S hS t).app F) ≫
                smallEtaleProjectionFormulaSndNatTrans t
                  ((DerivedCategory.singleFunctor _ 0).obj F))
              (derivedModulePushforward B S hS h₁ ⋙ representedAffineDerivedSections B S hS U₁) ≫
            Functor.whiskerLeft (smallEtaleDerivedModulePullback B S hS t ⋙
                (smallEtaleDerivedTensor B S hS X₀).flip.obj
                  ((DerivedCategory.singleFunctor _ 0).obj F))
              (affineBaseDerivedSectionsPushforwardIso B S hS gt h₁ h₀ t wt).hom) ≫
          Functor.whiskerRight (smallEtaleDerivedModulePullbackCompIso B S hS t i₁ ≪≫
              smallEtaleDerivedModulePullbackCongr B S hS hi).hom
            ((smallEtaleDerivedTensor B S hS X₀).flip.obj
                ((DerivedCategory.singleFunctor _ 0).obj F) ⋙
              (derivedModulePushforward B S hS h₀ ⋙ representedAffineDerivedSections B S hS U₀) ⋙
              StacksDraft.ringRestrictScalars (representedAffineCommRingCatHom B S hS gt).hom))
        (StacksDraft.ringRestrictScalars (representedAffineCommRingCatHom B S hS g₁).hom) ≫
      Functor.whiskerLeft (smallEtaleDerivedModulePullback B S hS i₀ ⋙
          (smallEtaleDerivedTensor B S hS X₀).flip.obj ((DerivedCategory.singleFunctor _ 0).obj F) ⋙
          (derivedModulePushforward B S hS h₀ ⋙ representedAffineDerivedSections B S hS U₀))
        (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u}
          (representedAffineCommRingCatHom B S hS g₁).hom
          (representedAffineCommRingCatHom B S hS gt).hom
          (representedAffineCommRingCatHom B S hS g₀).hom hc).hom

include hg in
/-- **`ψ_i` along `i = t ≫ i'`.** For `m = i'_*a ≫ cI` with `cI : i'_*t_*F ≅ i_*F` the composition
isomorphism, `ψ_i` after `RΓ(X, E ⊗^𝐋 m[0])` is `ψ_{i'}` at `F₁` followed by
`tensorSingleSectionsTransitionNatTrans`; `ha` is the compatibility of the comparisons
`(f_*F)[0] ⟶ Rf_*(F[0])` with the composition. -/
theorem tensorSingleSectionsNatTrans_comp
    (cI : (modulePushforward B S hS i₁).obj ((modulePushforward B S hS t).obj F) ≅
      (modulePushforward B S hS i₀).obj F)
    (hcI : cI = (modulePushforwardCompIso B S hS t i₁).app F ≪≫
      eqToIso (congrArg (fun φ => (modulePushforward B S hS φ).obj F) hi))
    (m : (modulePushforward B S hS i₁).obj F₁ ⟶ (modulePushforward B S hS i₀).obj F)
    (hm : m = (modulePushforward B S hS i₁).map a ≫ cI.hom)
    (ha : (DerivedCategory.singleFunctor _ 0).map
        ((modulePushforwardCompIso B S hS t i₁).app F ≪≫
          eqToIso (congrArg (fun φ => (modulePushforward B S hS φ).obj F) hi)).hom ≫
        (modulePushforwardSingleToDerived B S hS i₀).app F =
      (modulePushforwardSingleToDerived B S hS i₁).app ((modulePushforward B S hS t).obj F) ≫
        (derivedModulePushforward B S hS i₁).map
          ((modulePushforwardSingleToDerived B S hS t).app F) ≫
        (conjugateEquiv ((smallEtaleDerivedModuleAdjunction B S hS i₁).comp
            (smallEtaleDerivedModuleAdjunction B S hS t))
          (smallEtaleDerivedModuleAdjunction B S hS i₀)
          (smallEtaleDerivedModulePullbackCompIso B S hS t i₁ ≪≫
            smallEtaleDerivedModulePullbackCongr B S hS hi).inv).app
          ((DerivedCategory.singleFunctor _ 0).obj F)) :
    Functor.whiskerRight ((smallEtaleDerivedTensor B S hS X).flip.map
        ((DerivedCategory.singleFunctor _ 0).map m))
        (derivedModulePushforward B S hS h ⋙ representedAffineDerivedSections B S hS U) ≫
      tensorSingleSectionsNatTrans B S hS h h₀ g₀ i₀ w₀ hi₀ F hF =
    tensorSingleSectionsNatTrans B S hS h h₁ g₁ i₁ w₁ hi₁ F₁ hF₁ ≫
      tensorSingleSectionsTransitionNatTrans B S hS h₁ h₀ g₁ gt g₀ i₁ t i₀ hi wt hc F F₁ a := by
  subst hcI hm
  exact
    tensorSectionsPasting (W := (DerivedCategory.singleFunctor _ 0).obj F)
      (S0 := (DerivedCategory.singleFunctor _ 0).obj ((modulePushforward B S hS i₀).obj F))
      (S1 := (DerivedCategory.singleFunctor _ 0).obj
        ((modulePushforward B S hS i₁).obj ((modulePushforward B S hS t).obj F)))
      (S2 := (DerivedCategory.singleFunctor _ 0).obj ((modulePushforward B S hS i₁).obj F₁))
      (S1' := (DerivedCategory.singleFunctor _ 0).obj ((modulePushforward B S hS t).obj F))
      (S2' := (DerivedCategory.singleFunctor _ 0).obj F₁)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (smallEtaleProjectionFormulaSndNatTrans i₁) (smallEtaleProjectionFormulaSndNatTrans t)
      (smallEtaleProjectionFormulaSndNatTrans i₀)
      (affineBaseDerivedSectionsPushforwardIso B S hS g₁ h h₁ i₁ w₁).hom
      (affineBaseDerivedSectionsPushforwardIso B S hS gt h₁ h₀ t wt).hom
      (affineBaseDerivedSectionsPushforwardIso B S hS g₀ h h₀ i₀ w₀).hom
      (conjugateEquiv ((smallEtaleDerivedModuleAdjunction B S hS i₁).comp
          (smallEtaleDerivedModuleAdjunction B S hS t))
        (smallEtaleDerivedModuleAdjunction B S hS i₀)
        (smallEtaleDerivedModulePullbackCompIso B S hS t i₁ ≪≫
          smallEtaleDerivedModulePullbackCongr B S hS hi).inv)
      (smallEtaleDerivedModulePullbackCompIso B S hS t i₁ ≪≫
        smallEtaleDerivedModulePullbackCongr B S hS hi).hom
      (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u}
        (representedAffineCommRingCatHom B S hS g₁).hom
        (representedAffineCommRingCatHom B S hS gt).hom
        (representedAffineCommRingCatHom B S hS g₀).hom hc).hom
      (derivedModulePushforwardSingleIsoOfIsAffineHom B S hS i₀ hi₀ F hF).inv
      ((modulePushforwardSingleToDerived B S hS i₁).app ((modulePushforward B S hS t).obj F))
      (derivedModulePushforwardSingleIsoOfIsAffineHom B S hS i₁ hi₁ F₁ hF₁).inv
      ((modulePushforwardSingleToDerived B S hS t).app F)
      ((DerivedCategory.singleFunctor _ 0).map ((modulePushforward B S hS i₁).map a))
      ((DerivedCategory.singleFunctor _ 0).map a)
      ((DerivedCategory.singleFunctor _ 0).map ((modulePushforwardCompIso B S hS t i₁).app F ≪≫
        eqToIso (congrArg (fun φ => (modulePushforward B S hS φ).obj F) hi)).hom)
      _ (Functor.map_comp _ _ _)
      ((modulePushforwardSingleToDerived B S hS i₁).naturality a) ha
      (smallEtaleProjectionFormulaSndNatTrans_comp_of_eq t i₁ i₀ hi _)
      (affineBaseDerivedSectionsPushforwardIso_hom_comp_of_eq B S hS g₁ gt h h₁ h₀ i₁ t w₁ wt g₀ hg
        i₀ hi w₀ hc)
      (smallEtaleProjectionFormulaSndNatTrans_naturality i₁)


end AlgebraicGeometry.Space

end
