module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChangeEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceDerivationVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceTargetValues

/-!
# The conormal map of a square whose ambient morphism factors through the lower subspace

Let
```
Z --i--→ X
|        |
f        g
↓        ↓
Z' -i'-→ X'
```
be a commutative square of algebraic spaces over a scheme `S` contained in a big fppf site `B`,
with `Z` a closed subspace of `X` and `Z'` a closed subspace of `X'`.  This file proves that the
map of defining ideal sheaves `g^*𝓘' ⟶ 𝓘` of [Stacks Project, Tag 04CP] and the map of conormal
modules `f^*𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}` of that tag are **zero as soon as `g` factors through `Z'`**,
and deduces that the composite of the conormal maps of two stacked squares vanishes whenever the
ambient morphism of the outer rectangle factors through its lower subspace.

## Main results

* `AlgebraicGeometry.Space.structureSharp_app_eq_zero_of_mem_definingIdealAt`: the comorphism of
  a morphism factoring through a closed subspace kills the defining ideal of that subspace, on
  the sections over every étale chart.
* `modulePullback_definingIdealSheaf_ι_comp_structureModulePullbackMap_eq_zero`:
  consequently the inverse image along `g` of the inclusion `𝓘' ⊆ 𝒪_{X'}`, read in `𝒪_X` through
  the comparison `g^*𝒪_{X'} ⟶ 𝒪_X`, is the zero morphism.
* `AlgebraicGeometry.Space.idealSheafMap_eq_zero_of_factors`: the inverse image along the
  inclusion of `Z` of the map of defining ideal sheaves is zero.
* `AlgebraicGeometry.Space.conormalMap_eq_zero_of_factors`: **the conormal map of the square is
  zero.**
* `AlgebraicGeometry.Space.comp_conormalMap_eq_zero_of_factors`: **the composite of the conormal
  maps of two stacked squares is zero** when the ambient morphism of the outer rectangle factors
  through its lower closed subspace.

## References

* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP), the canonical maps.
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2), part (3), the
  composition law.
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the comorphism.
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB), the defining ideal
  sheaf.
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU), inverse and direct
  images of modules.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' X'' : AlgebraicSpaces B S hS}

/-! ### The comorphism of a morphism factoring through a closed subspace -/

/-- **The comorphism of a morphism factoring through a closed subspace kills the defining ideal
of that subspace.**  Let `Z'` be a closed subspace of `X'` and let `g : X ⟶ X'` factor through
the inclusion of `Z'`.  Then the comorphism `g^♯ : 𝒪_{X'} ⟶ g_*𝒪_X` of [Stacks Project,
Tag 03G8] carries every section of the defining ideal of `Z'` over an étale chart to zero. -/
theorem structureSharp_app_eq_zero_of_mem_definingIdealAt
    (g : X ⟶ X') (Z' : ClosedSubspaces B S hS X'.1)
    (u : X ⟶ (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (hu : g = u ≫ subspaceInclusion B S hS X' Z')
    (U : (SmallEtale B S hS X'.1)ᵒᵖ)
    (a : ToType ((structureRingSheaf B S hS X').obj.obj U))
    (ha : a ∈ definingIdealAt B S hS X' Z' U) :
    ((structureSharp B S hS g).hom.app U).hom a = 0 := by
  subst hu
  exact structureSharp_comp_app_eq_zero B S hS u (subspaceInclusion B S hS X' Z') U a
    ((mem_definingIdealAt_iff B S hS X' Z' U a).1 ha)

/-- **The inverse image of the inclusion of a defining ideal sheaf, read inside the structure
sheaf, is zero when the morphism factors through the subspace.**  For `g : X ⟶ X'` factoring
through the inclusion of a closed subspace `Z'` of `X'`, the inverse image along `g` of the
inclusion `𝓘' ⊆ 𝒪_{X'}` followed by the canonical comparison `g^*𝒪_{X'} ⟶ 𝒪_X` of
`AlgebraicGeometry.Space.structureModulePullbackMap` is the zero morphism. -/
theorem modulePullback_definingIdealSheaf_ι_comp_structureModulePullbackMap_eq_zero
    (g : X ⟶ X') (Z' : ClosedSubspaces B S hS X'.1)
    (u : X ⟶ (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (hu : g = u ≫ subspaceInclusion B S hS X' Z') :
    (modulePullback B S hS g).map (definingIdealSheaf B S hS X' Z').ι ≫
        structureModulePullbackMap B S hS g =
      (0 : (modulePullback B S hS g).obj
          (definingIdealSheaf B S hS X' Z').toSheafOfModules ⟶
        SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O)) := by
  refine ((modulePullbackAdjunction B S hS g).homEquiv _ _).injective ?_
  refine Eq.trans ((modulePullbackAdjunction B S hS g).homEquiv_naturality_left
    (definingIdealSheaf B S hS X' Z').ι (structureModulePullbackMap B S hS g)) ?_
  refine _root_.SheafOfModules.hom_ext (_root_.PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  refine Eq.trans ?_
    (modulePullbackAdjunction_homEquiv_zero_val_app_apply B S hS g _ _ U x).symm
  refine Eq.trans (Sheaf.hom_congr_app_apply
    (moduleSheafFunctor_map_homEquiv_structureModulePullbackMap B S hS g) U
    ((definingIdealSheaf B S hS X' Z').ι.val.app U x)) ?_
  exact structureSharp_app_eq_zero_of_mem_definingIdealAt B S hS g Z' u hu U _ x.2

/-! ### The conormal map of such a square -/

section Square

variable (Z : ClosedSubspaces B S hS X.1) (Z' : ClosedSubspaces B S hS X'.1) (g : X ⟶ X')
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))

/-- **The map of defining ideal sheaves of a square whose ambient morphism factors through the
lower subspace is zero**, read after the inverse image along the inclusion of `Z`. -/
theorem idealSheafMap_eq_zero_of_factors
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z')
    (u : X ⟶ (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (hu : g = u ≫ subspaceInclusion B S hS X' Z') :
    (show (modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
          ((modulePullback B S hS g).obj
            (definingIdealSheaf B S hS X' Z').toSheafOfModules) ⟶
        conormalModule B S hS X Z from
      (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
        (idealSheafMap B S hS Z Z' g f hsq)) = 0 := by
  have hcomp := (idealSheafMap_comp_definingIdealSheaf_ι B S hS Z Z' g f hsq).trans
    (modulePullback_definingIdealSheaf_ι_comp_structureModulePullbackMap_eq_zero
      B S hS g Z' u hu)
  have hphi := Limits.zero_of_comp_mono (definingIdealSheaf B S hS X Z).ι hcomp
  have hla : (modulePullback B S hS (subspaceInclusion B S hS X Z)).IsLeftAdjoint :=
    (modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).isLeftAdjoint
  rw [hphi]
  exact Functor.map_zero _ _ _

/-- **The conormal map of a square whose ambient morphism factors through the lower closed
subspace is zero.**  Let `Z` be a closed subspace of `X`, `Z'` a closed subspace of `X'`, and let
the commutative square be given by `g : X ⟶ X'` and `f : Z ⟶ Z'`.  If `g` factors through the
inclusion `Z' ⟶ X'` then the canonical map `f^*𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}` of [Stacks Project,
Tag 04CP] is the zero morphism. -/
theorem conormalMap_eq_zero_of_factors
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z')
    (u : X ⟶ (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (hu : g = u ≫ subspaceInclusion B S hS X' Z') :
    conormalMap B S hS Z Z' g f hsq = 0 :=
  (conormalMap_eq B S hS Z Z' g f hsq).trans
    ((congrArg (fun m => conormalPullbackComparison B S hS Z Z' g f hsq ≫ m)
      (idealSheafMap_eq_zero_of_factors B S hS Z Z' g f hsq u hu)).trans Limits.comp_zero)

end Square

/-! ### The composite of the conormal maps of two stacked squares -/

/-- **The composite of the conormal maps of two stacked squares is zero when the ambient
morphism of the outer rectangle factors through its lower closed subspace.**  For closed
subspaces `Z ⊆ X`, `Z' ⊆ X'` and `Z'' ⊆ X''`, morphisms `g : X ⟶ X'` and `g' : X' ⟶ X''` of the
ambient spaces and `f : Z ⟶ Z'`, `f' : Z' ⟶ Z''` of the subspaces making both squares commute,
if `g ≫ g'` factors through the inclusion `Z'' ⟶ X''` then
`f^*𝒞_{Z''/X''} ⟶ f^*𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}` is zero. -/
theorem comp_conormalMap_eq_zero_of_factors (g : X ⟶ X') (g' : X' ⟶ X'')
    (Z : ClosedSubspaces B S hS X.1) (Z' : ClosedSubspaces B S hS X'.1)
    (Z'' : ClosedSubspaces B S hS X''.1)
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (f' : (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z''.1.toFunctor, Z''.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z')
    (hsq' : subspaceInclusion B S hS X' Z' ≫ g' = f' ≫ subspaceInclusion B S hS X'' Z'')
    (u : X ⟶ (⟨Z''.1.toFunctor, Z''.2.1⟩ : AlgebraicSpaces B S hS))
    (hu : g ≫ g' = u ≫ subspaceInclusion B S hS X'' Z'') :
    (modulePullback B S hS f).map (conormalMap B S hS Z' Z'' g' f' hsq') ≫
      conormalMap B S hS Z Z' g f hsq = 0 := by
  have hsq'' : subspaceInclusion B S hS X Z ≫ g ≫ g' =
      (f ≫ f') ≫ subspaceInclusion B S hS X'' Z'' := by
    rw [← Category.assoc, hsq, Category.assoc, hsq', Category.assoc]
  have houter := conormalMap_eq_zero_of_factors B S hS Z Z'' (g ≫ g') (f ≫ f') hsq'' u hu
  have hcomp := conormalMap_comp B S hS g g' Z Z' Z'' f f' hsq hsq' hsq''
  have h1 : (modulePullback B S hS f).map (conormalMap B S hS Z' Z'' g' f' hsq') ≫
        conormalMap B S hS Z Z' g f hsq =
      (modulePullbackCompIso B S hS f f').hom.app (conormalModule B S hS X'' Z'') ≫
        conormalMap B S hS Z Z'' (g ≫ g') (f ≫ f') hsq'' := by
    rw [hcomp, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  rw [h1, houter]
  exact Limits.comp_zero

end AlgebraicGeometry.Space

end
