module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeGlobalSectionsSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsSquareComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackPresentationComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardCompIsoSheafTransfer

/-!
# Global sections along a composite of morphisms of algebraic spaces

Let `k : Z' ⟶ Z` and `g : Z ⟶ W` be morphisms of algebraic spaces over a scheme `S` of a big
fppf site.  This file proves that the two constructions on global sections attached to a
morphism are compatible with composition:

* the identification `Γ(W, g_*𝓜) = Γ(Z, 𝓜)` of Stacks 0732, applied twice, is the one for the
  composite read through the comparison `g_* ∘ k_* ≅ (k ≫ g)_*`;
* the inverse image of global sections `Γ(W, 𝓝) ⟶ Γ(Z', (k ≫ g)^*𝓝)` is the iterated one read
  through the comparison `k^* ∘ g^* ≅ (k ≫ g)^*` of Stacks 03LU.

## Main results

* `AlgebraicGeometry.Space.globalSectionsPushforwardIsoSite_modulePushforwardCompIso`: the first.
* `AlgebraicGeometry.Space.modulePullbackCompIso_globalSectionsPullbackMap`: the second, for
  arbitrary morphisms of algebraic spaces (the case of a morphism of schemes followed by a scheme
  point is `AlgebraicGeometry.Space.modulePullbackCompIso_globalSectionsPullbackMap_represented`).
* `AlgebraicGeometry.Space.globalSectionsPullbackMap_naturality_apply`: the inverse image of
  global sections is natural in the module.

## Implementation notes

The first statement is the compatibility of the geometric comparison of global sections with a
natural transformation between direct images
(`MorphismOfTopoi.pushforwardTerminalHomEquiv_natTrans`), the comparison of composite direct
images of modules being that of sheaves of sets
(`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardCompIso_hom_app`).  The second
follows from the first and the decomposition of the unit of `(k ≫ g)^* ⊣ (k ≫ g)_*`
(`AlgebraicGeometry.Space.modulePullbackAdjunction_unit_comp_app`).

## References

* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open Stacks.Cohomology.SiteModules (globalSectionsFunctor)
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Z' Z W : AlgebraicSpaces B S hS}

/-- The pinned forgetful functor carries the comparison of composite direct images of modules to
the comparison of composite direct images of sheaves of sets. -/
theorem moduleSetSheafFunctor_map_modulePushforwardCompIso_hom_app (k : Z' ⟶ Z) (g : Z ⟶ W)
    (N : Modules.{u, u} B S hS Z'.1 Z'.2) :
    (moduleSetSheafFunctor B S hS W).map ((modulePushforwardCompIso B S hS k g).hom.app N) =
      (smallEtaleDirectImageCompIso B S hS k g).hom.app ((moduleSetSheafFunctor B S hS Z').obj N) :=
  ((moduleSetSheafFunctor_map B S hS W ((modulePushforwardCompIso B S hS k g).hom.app N)).trans
      (moduleSheafFunctor_map_modulePushforwardCompIso_hom_app B S hS k g N)).trans
    (natTrans_app_moduleSetSheafFunctor_obj B S hS (smallEtaleDirectImageCompIso B S hS k g).hom
      N).symm

/-- **Stacks 0732 along a composite.**  A global section of `g_*k_*𝓜` over `W`, read on `Z'`
through the comparison `g_* ∘ k_* ≅ (k ≫ g)_*` and Stacks 0732 for `k ≫ g`, is the section read
through Stacks 0732 for `g` and then for `k`. -/
theorem globalSectionsPushforwardIsoSite_modulePushforwardCompIso (k : Z' ⟶ Z) (g : Z ⟶ W)
    (N : Modules.{u, u} B S hS Z'.1 Z'.2)
    (s : ((modulePushforward B S hS g).obj ((modulePushforward B S hS k).obj N)).sections) :
    ((globalSectionsPushforwardIsoSite B S hS (k ≫ g)).hom.app N).hom
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).map
            ((modulePushforwardCompIso B S hS k g).hom.app N)).hom s) =
      ((globalSectionsPushforwardIsoSite B S hS k).hom.app N).hom
        (((globalSectionsPushforwardIsoSite B S hS g).hom.app
          ((modulePushforward B S hS k).obj N)).hom s) := by
  refine (globalSectionsPushforwardIsoSite_hom_app_apply_set (k ≫ g) N _).trans ?_
  refine Eq.trans ?_ (globalSectionsPushforwardIsoSite_squareComparison_right g k N s).symm
  have h₁ := terminalHomEquivSections_symm_globalSectionsFunctor_map (k ≫ g) N
    ((modulePushforwardCompIso B S hS k g).hom.app N) s
  rw [moduleSetSheafFunctor_map_modulePushforwardCompIso_hom_app] at h₁
  refine congrArg (terminalHomEquivSections ((moduleSetSheafFunctor B S hS Z').obj N)) ?_
  refine (congrArg (fun z =>
      (smallEtaleRingedToposModulesHom B S hS (k ≫ g)).toToposHom.pushforwardTerminalHomEquiv
        ((moduleSetSheafFunctor B S hS Z').obj N) z) h₁).trans ?_
  exact MorphismOfTopoi.pushforwardTerminalHomEquiv_natTrans
    (smallEtaleRingedToposModulesHom B S hS k).toToposHom
    (smallEtaleRingedToposModulesHom B S hS g).toToposHom
    (smallEtaleRingedToposModulesHom B S hS (k ≫ g)).toToposHom
    (smallEtaleDirectImageCompIso B S hS k g).hom ((moduleSetSheafFunctor B S hS Z').obj N) _

/-- **The inverse image of global sections is natural in the module.** -/
theorem globalSectionsPullbackMap_naturality_apply (k : Z' ⟶ Z)
    {M N : Modules.{u, u} B S hS Z.1 Z.2} (φ : M ⟶ N)
    (σ : (globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)).obj M) :
    (globalSectionsPullbackMap B S hS k N).hom
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)).map φ).hom σ) =
      ((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS Z'.1 Z'.2).O)).map
            ((modulePullback B S hS k).map φ)).hom
        ((globalSectionsPullbackMap B S hS k M).hom σ) := by
  have e1 := globalSectionsFunctor_map_comp_apply φ
    ((modulePullbackAdjunction B S hS k).unit.app N) σ
  have e2 := globalSectionsFunctor_map_comp_apply ((modulePullbackAdjunction B S hS k).unit.app M)
    ((modulePushforward B S hS k).map ((modulePullback B S hS k).map φ)) σ
  have e4 := congrArg (fun m => ((globalSectionsFunctor.{u + 1, u, u, u}
    (ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)).map m).hom σ)
      ((modulePullbackAdjunction B S hS k).unit_naturality φ).symm
  refine (globalSectionsPullbackMap_apply k N _).trans ?_
  refine Eq.trans ?_ (congrArg ((globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS Z'.1 Z'.2).O)).map
        ((modulePullback B S hS k).map φ)).hom (globalSectionsPullbackMap_apply k M σ)).symm
  refine Eq.trans ?_ (globalSectionsPushforwardIsoSite_hom_app_naturality_apply k
    ((modulePullback B S hS k).map φ) _)
  exact congrArg ((globalSectionsPushforwardIsoSite B S hS k).hom.app
    ((modulePullback B S hS k).obj N)).hom ((e1.symm.trans e4).trans e2)

/-- A morphism out of an inverse image, applied to the inverse image of a global section, read
through the unit of `g^* ⊣ g_*` and Stacks 0732. -/
theorem globalSectionsFunctor_map_globalSectionsPullbackMap (g : Z ⟶ W)
    (N : Modules.{u, u} B S hS W.1 W.2) {K : Modules.{u, u} B S hS Z.1 Z.2}
    (φ : (modulePullback B S hS g).obj N ⟶ K)
    (σ : (globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).obj N) :
    ((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)).map φ).hom
        ((globalSectionsPullbackMap B S hS g N).hom σ) =
      ((globalSectionsPushforwardIsoSite B S hS g).hom.app K).hom
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).map
            ((modulePushforward B S hS g).map φ)).hom
          (((globalSectionsFunctor.{u + 1, u, u, u}
            (ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).map
              ((modulePullbackAdjunction B S hS g).unit.app N)).hom σ)) :=
  (congrArg ((globalSectionsFunctor.{u + 1, u, u, u}
    (ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)).map φ).hom
      (globalSectionsPullbackMap_apply g N σ)).trans
    (globalSectionsPushforwardIsoSite_hom_app_naturality_apply g φ _).symm

/-- **The inverse image of global sections along a composite.**  For morphisms `k : Z' ⟶ Z` and
`g : Z ⟶ W` of algebraic spaces and a global section `σ` of an `𝒪_W`-module `𝓝`, the comparison
`k^*g^*𝓝 ≅ (k ≫ g)^*𝓝` of Stacks 03LU carries `k^*(g^*σ)` to `(k ≫ g)^*σ`. -/
theorem modulePullbackCompIso_globalSectionsPullbackMap (k : Z' ⟶ Z) (g : Z ⟶ W)
    (N : Modules.{u, u} B S hS W.1 W.2)
    (σ : (globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).obj N) :
    ((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS Z'.1 Z'.2).O)).map
          ((modulePullbackCompIso B S hS k g).hom.app N)).hom
        ((globalSectionsPullbackMap B S hS k ((modulePullback B S hS g).obj N)).hom
          ((globalSectionsPullbackMap B S hS g N).hom σ)) =
      (globalSectionsPullbackMap B S hS (k ≫ g) N).hom σ := by
  have hunit : ((modulePullbackAdjunction B S hS g).unit.app N) ≫
      (modulePushforward B S hS g).map
        ((modulePullbackAdjunction B S hS k).unit.app ((modulePullback B S hS g).obj N)) ≫
      ((modulePushforwardCompIso B S hS k g).hom.app
        ((modulePullback B S hS k).obj ((modulePullback B S hS g).obj N))) ≫
      (modulePushforward B S hS (k ≫ g)).map ((modulePullbackCompIso B S hS k g).hom.app N) =
      (modulePullbackAdjunction B S hS (k ≫ g)).unit.app N :=
    modulePullbackAdjunction_unit_comp_app B S hS k g N
  have e1 : ((globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).map
        ((modulePullbackAdjunction B S hS (k ≫ g)).unit.app N)).hom σ =
      ((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).map
          ((modulePushforward B S hS (k ≫ g)).map
            ((modulePullbackCompIso B S hS k g).hom.app N))).hom
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).map
            ((modulePushforwardCompIso B S hS k g).hom.app
              ((modulePullback B S hS k).obj ((modulePullback B S hS g).obj N)))).hom
          (((globalSectionsFunctor.{u + 1, u, u, u}
            (ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).map
              ((modulePushforward B S hS g).map
                ((modulePullbackAdjunction B S hS k).unit.app
                  ((modulePullback B S hS g).obj N)))).hom
            (((globalSectionsFunctor.{u + 1, u, u, u}
              (ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).map
                ((modulePullbackAdjunction B S hS g).unit.app N)).hom σ))) := by
    refine (congrArg (fun m => ((globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).map m).hom σ) hunit.symm).trans ?_
    refine (globalSectionsFunctor_map_comp_apply
      ((modulePullbackAdjunction B S hS g).unit.app N) _ σ).trans ?_
    refine (globalSectionsFunctor_map_comp_apply ((modulePushforward B S hS g).map
      ((modulePullbackAdjunction B S hS k).unit.app ((modulePullback B S hS g).obj N)))
      _ _).trans ?_
    exact globalSectionsFunctor_map_comp_apply ((modulePushforwardCompIso B S hS k g).hom.app
      ((modulePullback B S hS k).obj ((modulePullback B S hS g).obj N)))
      ((modulePushforward B S hS (k ≫ g)).map ((modulePullbackCompIso B S hS k g).hom.app N)) _
  have e2 := globalSectionsPushforwardIsoSite_hom_app_naturality_apply (k ≫ g)
    ((modulePullbackCompIso B S hS k g).hom.app N)
    (((globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).map
        ((modulePushforwardCompIso B S hS k g).hom.app
          ((modulePullback B S hS k).obj ((modulePullback B S hS g).obj N)))).hom
      (((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).map
          ((modulePushforward B S hS g).map
            ((modulePullbackAdjunction B S hS k).unit.app ((modulePullback B S hS g).obj N)))).hom
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).map
            ((modulePullbackAdjunction B S hS g).unit.app N)).hom σ)))
  have e3 := globalSectionsPushforwardIsoSite_modulePushforwardCompIso k g
    ((modulePullback B S hS k).obj ((modulePullback B S hS g).obj N))
    (((globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).map
        ((modulePushforward B S hS g).map
          ((modulePullbackAdjunction B S hS k).unit.app ((modulePullback B S hS g).obj N)))).hom
      (((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).map
          ((modulePullbackAdjunction B S hS g).unit.app N)).hom σ))
  refine Eq.trans ?_ (globalSectionsPullbackMap_apply (k ≫ g) N σ).symm
  refine Eq.trans ?_ (congrArg ((globalSectionsPushforwardIsoSite B S hS (k ≫ g)).hom.app
    ((modulePullback B S hS (k ≫ g)).obj N)).hom e1).symm
  refine Eq.trans ?_ e2.symm
  refine congrArg ((globalSectionsFunctor.{u + 1, u, u, u}
    (ringSheaf (smallEtaleRingedSite B S hS Z'.1 Z'.2).O)).map
      ((modulePullbackCompIso B S hS k g).hom.app N)).hom ?_
  refine Eq.trans ?_ e3.symm
  refine (globalSectionsPullbackMap_apply k ((modulePullback B S hS g).obj N) _).trans ?_
  refine congrArg (fun z : (globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)).obj ((modulePushforward B S hS k).obj
        ((modulePullback B S hS k).obj ((modulePullback B S hS g).obj N))) =>
    ((globalSectionsPushforwardIsoSite B S hS k).hom.app
      ((modulePullback B S hS k).obj ((modulePullback B S hS g).obj N))).hom z) ?_
  exact globalSectionsFunctor_map_globalSectionsPullbackMap g N
    (K := (modulePushforward B S hS k).obj ((modulePullback B S hS k).obj
      ((modulePullback B S hS g).obj N)))
    ((modulePullbackAdjunction B S hS k).unit.app ((modulePullback B S hS g).obj N)) σ

end AlgebraicGeometry.Space

end
