module

public import StacksFrontier.AlgebraicGeometry.Spaces.AmpleSchemeFibreTwist
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsPullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCompIsoAssoc

/-!
# Restricting pulled-back sections to a scheme over an algebraic space

Let `p_W : X_W ⟶ X` be a morphism of algebraic spaces and `𝒢` an `𝒪_X`-module.  A global section
`σ` of `p_W^*𝒢` pulls back along any `k : V ⟶ X_W` to a global section of `(k ≫ p_W)^*𝒢`, through
the comparison `k^*p_W^*𝒢 ≅ (k ≫ p_W)^*𝒢` of Stacks 03LU
(`AlgebraicGeometry.Space.modulePullbackCompIsoHomApp`).  This file proves that restricting such a
section further to a scheme `U` lying over `V` (`AlgebraicGeometry.Space.restrictSectionAlong`)
is pulling `σ` back along the composite.

## Main definitions

* `AlgebraicGeometry.Space.modulePullbackCompIsoHomApp`: the component of the comparison of
  Stacks 03LU at a module, with its source spelled as an iterated inverse image.

## Main results

* `AlgebraicGeometry.Space.restrictSectionAlong_eq`: the restriction, spelled through
  `AlgebraicGeometry.Space.modulePullbackCompIsoHomApp`.
* `AlgebraicGeometry.Space.restrictSectionAlong_modulePullbackCompIsoHomApp`: the restriction of a
  section read on `(k ≫ p_W)^*𝒢` is its pullback along `j`, read on `((j ≫ k) ≫ p_W)^*𝒢`.

## Implementation notes

The comparison of Stacks 03LU at a module has its source spelled `(p^* ⋙ k^*).obj 𝒢`; applied to
the inverse image of a section, whose type is spelled `k^*(p^*𝒢)`, the two spellings meet inside
large terms, which the elaborator compares slowly.  Every computation is therefore made at the
spelling `AlgebraicGeometry.Space.modulePullbackCompIsoHomApp`, and the definition of
`AlgebraicGeometry.Space.restrictSectionAlong` is converted to it once
(`AlgebraicGeometry.Space.restrictSectionAlong_eq`).

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SiteModules (globalSectionsFunctor)
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Pulling a module back along two equal morphisms identifies global sections by the identity
when the two morphisms are the same. -/
theorem spaceModuleSectionsPullbackCongr_rfl_apply {Z Z' : AlgebraicSpaces B S hS} (g : Z' ⟶ Z)
    (G : Modules.{u, u} B S hS Z.1 Z.2)
    (s : spaceModuleSections Z' ((modulePullback B S hS g).obj G)) :
    (spaceModuleSectionsPullbackCongr (rfl : g = g) G).hom s = s := by
  simp [spaceModuleSectionsPullbackCongr]

/-- The component at `𝒢` of the comparison `k^*p^*𝒢 ≅ (k ≫ p)^*𝒢` of Stacks 03LU. -/
def modulePullbackCompIsoHomApp {X Y Z : AlgebraicSpaces B S hS} (k : Z ⟶ Y) (p : Y ⟶ X)
    (G : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullback B S hS k).obj ((modulePullback B S hS p).obj G) ⟶
      (modulePullback B S hS (k ≫ p)).obj G :=
  (modulePullbackCompIso B S hS k p).hom.app G

/-- Applying `AlgebraicGeometry.Space.modulePullbackCompIsoHomApp` on global sections to the
inverse image of a section is applying the comparison of Stacks 03LU. -/
theorem globalSectionsFunctor_map_modulePullbackCompIsoHomApp_apply {X Y Z : AlgebraicSpaces B S hS}
    (k : Z ⟶ Y) (p : Y ⟶ X) (G : Modules.{u, u} B S hS X.1 X.2)
    (s : spaceModuleSections Y ((modulePullback B S hS p).obj G)) :
    ((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)).map
          ((modulePullbackCompIso B S hS k p).hom.app G))
        ((globalSectionsPullbackMap B S hS k ((modulePullback B S hS p).obj G)).hom s) =
      ((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)).map
          (modulePullbackCompIsoHomApp k p G)).hom
        ((globalSectionsPullbackMap B S hS k ((modulePullback B S hS p).obj G)).hom s) :=
  rfl

/-- The associativity coherence of the comparison of Stacks 03LU, at a module. -/
theorem modulePullbackCompIsoHomApp_assoc {X Y Z Z' : AlgebraicSpaces B S hS} (a : Z' ⟶ Z)
    (k : Z ⟶ Y) (p : Y ⟶ X) (G : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullback B S hS a).map (modulePullbackCompIsoHomApp k p G) ≫
        modulePullbackCompIsoHomApp a (k ≫ p) G =
      modulePullbackCompIsoHomApp a k ((modulePullback B S hS p).obj G) ≫
        modulePullbackCompIsoHomApp (a ≫ k) p G :=
  (modulePullbackCompIsoAssoc B S hS).hom_app a k p G

/-- `AlgebraicGeometry.Space.modulePullbackCompIso_globalSectionsPullbackMap` at the spelling
`AlgebraicGeometry.Space.modulePullbackCompIsoHomApp`. -/
theorem modulePullbackCompIsoHomApp_globalSectionsPullbackMap {X Y Z : AlgebraicSpaces B S hS}
    (k : Z ⟶ Y) (p : Y ⟶ X) (N : Modules.{u, u} B S hS X.1 X.2)
    (σ : spaceModuleSections X N) :
    ((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)).map
          (modulePullbackCompIsoHomApp k p N)).hom
        ((globalSectionsPullbackMap B S hS k ((modulePullback B S hS p).obj N)).hom
          ((globalSectionsPullbackMap B S hS p N).hom σ)) =
      (globalSectionsPullbackMap B S hS (k ≫ p) N).hom σ :=
  modulePullbackCompIso_globalSectionsPullbackMap k p N σ

/-- Two identifications of sections along equalities of morphisms agree on elements that
correspond under the identification along `g₁ = g₂`. -/
theorem spaceModuleSectionsPullbackCongr_apply_eq {Z Z' : AlgebraicSpaces B S hS}
    {g₁ g₂ g' : Z' ⟶ Z} (h₁ : g₁ = g') (h₂ : g₂ = g') (e : g₁ = g₂)
    (G : Modules.{u, u} B S hS Z.1 Z.2)
    (x₁ : spaceModuleSections Z' ((modulePullback B S hS g₁).obj G))
    (x₂ : spaceModuleSections Z' ((modulePullback B S hS g₂).obj G))
    (hx : (spaceModuleSectionsPullbackCongr e G).hom x₁ = x₂) :
    (spaceModuleSectionsPullbackCongr h₁ G).hom x₁ =
      (spaceModuleSectionsPullbackCongr h₂ G).hom x₂ := by
  subst e h₂
  rw [spaceModuleSectionsPullbackCongr_rfl_apply] at hx
  rw [hx]

/-- `AlgebraicGeometry.Space.restrictSectionAlong`, spelled through
`AlgebraicGeometry.Space.modulePullbackCompIsoHomApp`. -/
theorem restrictSectionAlong_eq {X XV : AlgebraicSpaces B S hS} (pV : XV ⟶ X)
    (U : BigFppfOver B S hS) (jV : yoneda.obj U ⟶ XV.1) (p : yoneda.obj U ⟶ X.1)
    (h : jV ≫ pV.hom = p) (G : Modules.{u, u} B S hS X.1 X.2)
    (s : spaceModuleSections XV ((modulePullback B S hS pV).obj G)) :
    restrictSectionAlong pV U jV p h G s =
      (spaceModuleSectionsPullbackCongr (ObjectProperty.hom_ext _ h :
        (representedPointHom U jV) ≫ pV =
          ObjectProperty.homMk p) G).hom
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS (representedAlgebraicSpace B S hS U).1
            (representedAlgebraicSpace B S hS U).2).O)).map
            (modulePullbackCompIsoHomApp (representedPointHom U jV) pV G)).hom
          ((globalSectionsPullbackMap B S hS (representedPointHom U jV)
            ((modulePullback B S hS pV).obj G)).hom s)) := by
  have hb :=
    globalSectionsFunctor_map_modulePullbackCompIsoHomApp_apply (representedPointHom U jV) pV G s
  unfold restrictSectionAlong
  rw [hb]

/-- **Iterated pullback of a section of an inverse image**, for an arbitrary section over the
middle space: for `a : Z' ⟶ V`, `k : V ⟶ X_W` and `p_W : X_W ⟶ X`, pulling a section `x` of
`k^*p_W^*𝒢` back along `a` and reading it on `(a ≫ k ≫ p_W)^*𝒢` agrees with reading `a^*x` on
`((a ≫ k) ≫ p_W)^*𝒢` through `a^*k^* ≅ (a ≫ k)^*`. -/
theorem modulePullbackCompIsoHomApp_globalSectionsPullbackMap_assoc
    {X XW V Z' : AlgebraicSpaces B S hS}
    (a : Z' ⟶ V) (k : V ⟶ XW) (pW : XW ⟶ X) (G : Modules.{u, u} B S hS X.1 X.2)
    (x : spaceModuleSections V
      ((modulePullback B S hS k).obj ((modulePullback B S hS pW).obj G))) :
    (spaceModuleSectionsPullbackCongr (Category.assoc a k pW).symm G).hom
      (((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS Z'.1 Z'.2).O)).map
          (modulePullbackCompIsoHomApp a (k ≫ pW) G)).hom
        ((globalSectionsPullbackMap B S hS a ((modulePullback B S hS (k ≫ pW)).obj G)).hom
          (((globalSectionsFunctor.{u + 1, u, u, u}
            (ringSheaf (smallEtaleRingedSite B S hS V.1 V.2).O)).map
              (modulePullbackCompIsoHomApp k pW G)).hom x))) =
    ((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS Z'.1 Z'.2).O)).map
          (modulePullbackCompIsoHomApp (a ≫ k) pW G)).hom
      (((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS Z'.1 Z'.2).O)).map
          (modulePullbackCompIsoHomApp a k ((modulePullback B S hS pW).obj G))).hom
        ((globalSectionsPullbackMap B S hS a
          ((modulePullback B S hS k).obj ((modulePullback B S hS pW).obj G))).hom x)) := by
  refine (spaceModuleSectionsPullbackCongr_rfl_apply (a ≫ k ≫ pW) G _).trans ?_
  refine (congrArg ((globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS Z'.1 Z'.2).O)).map
        (modulePullbackCompIsoHomApp a (k ≫ pW) G)).hom
    (globalSectionsPullbackMap_naturality_apply a (modulePullbackCompIsoHomApp k pW G) x)).trans ?_
  refine (globalSectionsFunctor_map_comp_apply _ _ _).symm.trans ?_
  refine (congrArg (fun φ => ((globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS Z'.1 Z'.2).O)).map φ).hom
      ((globalSectionsPullbackMap B S hS a
        ((modulePullback B S hS k).obj ((modulePullback B S hS pW).obj G))).hom x))
    (modulePullbackCompIsoHomApp_assoc a k pW G)).trans ?_
  exact globalSectionsFunctor_map_comp_apply _ _ _

/-- **The restriction to `U` of a section over `V` read on `(k ≫ p_W)^*𝒢`** is its pullback to
`U`, read on `((j ≫ k) ≫ p_W)^*𝒢`. -/
theorem restrictSectionAlong_modulePullbackCompIsoHomApp {X XW V : AlgebraicSpaces B S hS}
    (k : V ⟶ XW) (pW : XW ⟶ X) (pV : V ⟶ X) (hk : k ≫ pW = pV) (U : BigFppfOver B S hS)
    (j : yoneda.obj U ⟶ V.1) (p : yoneda.obj U ⟶ X.1) (h : j ≫ pV.hom = p)
    (G : Modules.{u, u} B S hS X.1 X.2)
    (x : spaceModuleSections V
      ((modulePullback B S hS k).obj ((modulePullback B S hS pW).obj G)))
    (h' : ((representedPointHom U j) ≫ k) ≫ pW =
      ObjectProperty.homMk p) :
    restrictSectionAlong pV U j p h G ((spaceModuleSectionsPullbackCongr hk G).hom
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS V.1 V.2).O)).map
            (modulePullbackCompIsoHomApp k pW G)).hom x)) =
      (spaceModuleSectionsPullbackCongr h' G).hom
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS (representedAlgebraicSpace B S hS U).1
            (representedAlgebraicSpace B S hS U).2).O)).map
            (modulePullbackCompIsoHomApp
              ((representedPointHom U j) ≫ k) pW G)).hom
          (((globalSectionsFunctor.{u + 1, u, u, u}
            (ringSheaf (smallEtaleRingedSite B S hS (representedAlgebraicSpace B S hS U).1
              (representedAlgebraicSpace B S hS U).2).O)).map
              (modulePullbackCompIsoHomApp (representedPointHom U j) k
                ((modulePullback B S hS pW).obj G))).hom
            ((globalSectionsPullbackMap B S hS (representedPointHom U j)
                ((modulePullback B S hS k).obj ((modulePullback B S hS pW).obj G))).hom x))) := by
  subst hk h
  refine (congrArg (restrictSectionAlong (k ≫ pW) U j _ rfl G)
    (spaceModuleSectionsPullbackCongr_rfl_apply _ G _)).trans ?_
  rw [restrictSectionAlong_eq]
  exact spaceModuleSectionsPullbackCongr_apply_eq _ _ (Category.assoc _ _ _).symm G _ _
    (modulePullbackCompIsoHomApp_globalSectionsPullbackMap_assoc
      (representedPointHom U j) k pW G x)

end AlgebraicGeometry.Space

end
