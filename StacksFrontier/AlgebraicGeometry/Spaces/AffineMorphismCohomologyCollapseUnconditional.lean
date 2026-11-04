module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyIso
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyCollapse
public import StacksFrontier.AlgebraicGeometry.Spaces.InjectivePushforwardAcyclicity
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesGlobalSections
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.Homology.CompositeCollapse
import StacksCore.Tactic.StacksAttribute

/-!
# The cohomology of a quasi-coherent module along an affine morphism is natural

`AlgebraicGeometry.Space.cohomologyIsoOfIsAffineHom` is Stacks 0D2U: for an affine morphism
`f : X ⟶ Y` of algebraic spaces and a quasi-coherent `𝒪_X`-module `𝓕`,
`H^i(X, 𝓕) ≅ H^i(Y, f_*𝓕)` for every `i`, built from the Leray collapse
`AlgebraicGeometry.Space.cohomologyCollapseIsoOfIsAffineHom` with its two hypotheses discharged
by Stacks 073H and Stacks 072Z.  This file proves that both isomorphisms are natural in `𝓕`, and
registers the isomorphism for Stacks 0D2U.

## Main results

* `AlgebraicGeometry.Space.cohomologyCollapseIsoOfIsAffineHom_hom_naturality`: the Leray collapse
  along an affine morphism, with its hypotheses discharged, is natural in the module.
* `AlgebraicGeometry.Space.cohomologyIsoOfIsAffineHom_hom_naturality`: Stacks 0D2U is natural in
  the module.

## References

* [Stacks Project, Tag 0D2U](https://stacks.math.columbia.edu/tag/0D2U)
* [Stacks Project, Tag 073H](https://stacks.math.columbia.edu/tag/073H)
* [Stacks Project, Tag 072Z](https://stacks.math.columbia.edu/tag/072Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

noncomputable section

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **The Leray collapse along an affine morphism is natural** in the quasi-coherent module. -/
theorem cohomologyCollapseIsoOfIsAffineHom_hom_naturality (f : X ⟶ Y)
    (hf : IsAffineHom B S hS f.hom) {F F' : Modules.{u, u} B S hS X.1 X.2} (e : F ⟶ F')
    (hF : F.IsQuasicoherentOnSite) (hF' : F'.IsQuasicoherentOnSite) (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    have := enoughInjectives_modules B S hS Y.1 Y.2
    ((modulePushforward B S hS f ⋙ globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Y.1 Y.2).O))).rightDerived i).map e ≫
        (cohomologyCollapseIsoOfIsAffineHom B S hS f hf F'
          (fun n hn => chartwiseIsZeroHigherDirectImage_of_isAffineHom B S hS f hf _ F' hF' n hn)
          (acyclicPushforwardOfInjective B S hS f) i).hom =
      (cohomologyCollapseIsoOfIsAffineHom B S hS f hf F
          (fun n hn => chartwiseIsZeroHigherDirectImage_of_isAffineHom B S hS f hf _ F hF n hn)
          (acyclicPushforwardOfInjective B S hS f) i).hom ≫
        ((globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Y.1 Y.2).O))).rightDerived i).map
            ((modulePushforward B S hS f).map e) :=
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := enoughInjectives_modules B S hS Y.1 Y.2
  have := preservesFiniteLimits_globalSectionsFunctor_structureRingSheaf B S hS Y.1 Y.2
  Stacks.RightDerivedComp.objIsoOfAcyclicImage_hom_naturality _ _ e
    (fun n hn => isZero_rightDerived_modulePushforward_of_isAffineHom_of_isQuasicoherentOnSite
      B S hS f hf F hF n hn)
    (fun n hn => isZero_rightDerived_modulePushforward_of_isAffineHom_of_isQuasicoherentOnSite
      B S hS f hf F' hF' n hn)
    (acyclicPushforwardOfInjective B S hS f) i


private theorem comp_four_eq {C : Type*} [Category C] {P₀ P₁ P₂ P₃ P₄ Q₀ Q₁ Q₂ Q₃ Q₄ : C}
    {a : P₀ ⟶ Q₀} {b' : Q₀ ⟶ Q₁} {c' : Q₁ ⟶ Q₂} {d' : Q₂ ⟶ Q₃} {k' : Q₃ ⟶ Q₄}
    {b : P₀ ⟶ P₁} {x : P₁ ⟶ Q₁} {c : P₁ ⟶ P₂} {y : P₂ ⟶ Q₂} {d : P₂ ⟶ P₃} {z : P₃ ⟶ Q₃}
    {k : P₃ ⟶ P₄} {m : P₄ ⟶ Q₄}
    (h1 : a ≫ b' = b ≫ x) (h2 : x ≫ c' = c ≫ y) (h3 : y ≫ d' = d ≫ z)
    (h4 : z ≫ k' = k ≫ m) :
    a ≫ b' ≫ c' ≫ d' ≫ k' = b ≫ c ≫ d ≫ k ≫ m := by
  rw [reassoc_of% h1, reassoc_of% h2, reassoc_of% h3, h4]

/-- **Stacks 0D2U is natural** in the quasi-coherent module. -/
theorem cohomologyIsoOfIsAffineHom_hom_naturality (f : X ⟶ Y)
    (hf : IsAffineHom B S hS f.hom) {F F' : Modules.{u, u} B S hS X.1 X.2} (e : F ⟶ F')
    (hF : F.IsQuasicoherentOnSite) (hF' : F'.IsQuasicoherentOnSite) (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    have := hasInjectiveResolutions_modules B S hS Y.1 Y.2
    (forget₂ _ AddCommGrpCat.{u + 1}).map (((globalSectionsFunctor.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O))).rightDerived i).map e) ≫
        (cohomologyIsoOfIsAffineHom B S hS f hf F' hF' i).hom =
      (cohomologyIsoOfIsAffineHom B S hS f hf F hF i).hom ≫
        (forget₂ _ AddCommGrpCat.{u + 1}).map (((globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Y.1 Y.2).O))).rightDerived i).map
            ((modulePushforward B S hS f).map e)) := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := hasInjectiveResolutions_modules B S hS Y.1 Y.2
  have := modulePushforward_additive B S hS f
  have h4 := congrArg (forget₂ _ AddCommGrpCat.{u + 1}).map
    (cohomologyCollapseIsoOfIsAffineHom_hom_naturality B S hS f hf e hF hF' i)
  simp only [Functor.map_comp] at h4
  have h1 := ((Functor.rightDerivedCompIso (globalSectionsFunctor.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)))
      (forget₂ _ AddCommGrpCat.{u + 1}) i).inv.naturality e)
  have h2 := ((Functor.rightDerivedIsoOfNatIso
    (globalSectionsModulePushforwardIso B S hS f).symm i).hom.naturality e)
  have h3 := ((Functor.rightDerivedCompIso (modulePushforward B S hS f ⋙
      globalSectionsFunctor.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)))
      (forget₂ _ AddCommGrpCat.{u + 1}) i).hom.naturality e)
  simp only [Functor.comp_map] at h1 h3
  simp only [cohomologyIsoOfIsAffineHom, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, Category.assoc]
  exact comp_four_eq h1 h2 h3 h4

end AlgebraicGeometry.Space

add_to_stacks 0D2U AlgebraicGeometry.Space.cohomologyIsoOfIsAffineHom

end

end
