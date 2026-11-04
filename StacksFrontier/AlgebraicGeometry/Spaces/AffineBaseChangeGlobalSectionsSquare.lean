module

public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsPullbackBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleBaseChangeMapHorizontal
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianBaseChangeMap

/-!
# The degree-zero base change map on global sections, around a square

For a commutative square of algebraic spaces

```
X' --g'--> X
|f'         |f
v           v
Y' --g-->  Y
```

and an `𝒪_X`-module `𝓚`, a global section `s` of `f_*𝓚` can be carried to a global section of
`(g')^*𝓚` on `X'` in two ways:

* pull it back along `g` (`AlgebraicGeometry.Space.globalSectionsPullbackMap`), apply the
  degree-zero base change map `g^*f_*𝓚 ⟶ f'_*(g')^*𝓚` on global sections of `Y'`, and read the
  result on `X'` through **Stacks 0732** for `f'`; or
* read `s` on `X` through **Stacks 0732** for `f`, and pull it back along `g'`.

This file proves the morphism-level identity from which the two routes agree.

## Main results

* `AlgebraicGeometry.Space.unit_comp_map_mate_comp_map`: the mate identity for the degree-zero
  base change map, followed by a morphism.
* `AlgebraicGeometry.Space.globalSectionsPushforwardIsoSite_hom_app_naturality_apply`: naturality
  of **Stacks 0732**, on sections.

## References

* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.SiteModules (globalSectionsFunctor)
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)

/-- The comparison of **Stacks 0732** is natural, on sections. -/
theorem globalSectionsPushforwardIsoSite_hom_app_naturality_apply {Z W : AlgebraicSpaces B S hS}
    (k : Z ⟶ W) {M N : Modules.{u, u} B S hS Z.1 Z.2} (φ : M ⟶ N)
    (s : (globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).obj
        ((modulePushforward B S hS k).obj M)) :
    ((globalSectionsPushforwardIsoSite B S hS k).hom.app N).hom
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).map
            ((modulePushforward B S hS k).map φ)).hom s) =
      ((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)).map φ).hom
        (((globalSectionsPushforwardIsoSite B S hS k).hom.app M).hom s) :=
  congrArg (fun m ↦ m.hom s) ((globalSectionsPushforwardIsoSite B S hS k).hom.naturality φ)

/-- The inverse image of global sections is the unit on global sections followed by
**Stacks 0732**. -/
theorem globalSectionsPullbackMap_apply {Z W : AlgebraicSpaces B S hS} (k : Z ⟶ W)
    (N : Modules.{u, u} B S hS W.1 W.2)
    (s : (globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).obj N) :
    (globalSectionsPullbackMap B S hS k N).hom s =
      ((globalSectionsPushforwardIsoSite B S hS k).hom.app ((modulePullback B S hS k).obj N)).hom
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).map
            ((modulePullbackAdjunction B S hS k).unit.app N)).hom s) :=
  rfl

/-- `Γ` of a composite, evaluated on a section, is the composite of the two maps on sections. -/
theorem globalSectionsFunctor_map_comp_apply {Z : AlgebraicSpaces B S hS}
    {M₁ M₂ M₃ : Modules.{u, u} B S hS Z.1 Z.2} (a : M₁ ⟶ M₂) (b : M₂ ⟶ M₃)
    (s : (globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)).obj M₁) :
    ((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)).map (a ≫ b)).hom s =
      ((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)).map b).hom
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)).map a).hom s) :=
  congrArg (fun m ↦ m.hom s) ((globalSectionsFunctor.{u + 1, u, u, u}
    (ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)).map_comp a b)

/-- **The mate identity for the degree-zero base change map, followed by a morphism.**  For a
morphism `ψ : (g')^*𝓚 ⟶ 𝓛`, the unit of `g^* ⊣ g_*` at `f_*𝓚` followed by `g_*` of the base change
map and of `f'_*ψ` is `f_*` of the unit of `(g')^* ⊣ g'_*` and of `g'_*ψ`, followed by the
comparison of the two composite direct images around the square. -/
theorem unit_comp_map_mate_comp_map (comm : g' ≫ f = f' ≫ g)
    (K : Modules.{u, u} B S hS X.1 X.2) {L : Modules.{u, u} B S hS X'.1 X'.2}
    (ψ : (modulePullback B S hS g').obj K ⟶ L) :
    (modulePullbackAdjunction B S hS g).unit.app ((modulePushforward B S hS f).obj K) ≫
      (modulePushforward B S hS g).map ((Stacks.Cohomology.BaseChange.mate
        (modulePullbackAdjunction B S hS g) (modulePullbackAdjunction B S hS g')
        (modulePushforward B S hS f) (modulePushforward B S hS f')
        (modulePushforwardSquareComparisonIso f g f' g' comm)).app K ≫
          (modulePushforward B S hS f').map ψ) =
      (modulePushforward B S hS f).map ((modulePullbackAdjunction B S hS g').unit.app K ≫
          (modulePushforward B S hS g').map ψ) ≫
        (modulePushforwardSquareComparisonIso f g f' g' comm).hom.app L := by
  have h := Stacks.Cohomology.BaseChange.unit_comp_map_mate (modulePullbackAdjunction B S hS g)
    (modulePullbackAdjunction B S hS g') (modulePushforward B S hS f)
    (modulePushforward B S hS f') (modulePushforwardSquareComparisonIso f g f' g' comm) K
  have hn := (modulePushforwardSquareComparisonIso f g f' g' comm).hom.naturality ψ
  simp only [Functor.comp_map] at hn
  rw [Functor.map_comp, reassoc_of% h, ← hn, Functor.map_comp, Category.assoc]

end AlgebraicGeometry.Space

end
