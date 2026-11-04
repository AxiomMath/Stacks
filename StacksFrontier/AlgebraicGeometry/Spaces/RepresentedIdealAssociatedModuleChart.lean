module

public import StacksFrontier.AlgebraicGeometry.Divisors.IdealAssociatedModuleChartImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeSpaceIdealModuleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv

/-!
# The ideal sheaf of a closed subspace of a represented algebraic space, chart by chart

Let `S` be a scheme contained in a big fppf site `B`, let `V` be an object of the big fppf
category over `S` and let `Z ⊆ h_V = yoneda.obj V` be a closed subspace.  Two sheaves of ideals
are attached to `Z`: the defining ideal sheaf `𝓘_Z ⊆ 𝒪_{h_V}` of Stacks 083B on the small étale
site, and the Zariski sheaf of ideals `I ⊆ 𝒪_V` of the scheme that
`AlgebraicGeometry.Space.schemeSpaceIdeal` cuts out.

This file proves that they agree **chart by chart as sheaves of modules**: over an affine étale
chart `A` of `h_V` the image of `ε^*(I ⊆ 𝒪_V)` on sections is exactly the defining ideal
`AlgebraicGeometry.Space.definingIdealAt` of `Z` at `A`, where `ε^*` is
`AlgebraicGeometry.Space.representedAssociatedModule`, the associated-module functor of
Stacks 03DU (4) read on the represented space.

## The route

The whole of the mathematics is
`AlgebraicGeometry.SmallEtale.exists_idealAssociatedMap_app_eq_iff_mem`, the same statement on
the small étale site of the representing *scheme*.  What is added here is the transport along
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence` and the identification of the
inverse-image sheaf of ideals appearing there with the defining ideal:

* the transport is bookkeeping — `AlgebraicGeometry.Space.representedModulePushforward` is a
  direct image along a comparison of structure sheaves which is the *identity*, so it changes
  no sections, and the composite of `ε^*` with the comparison of structure sheaves is the
  transport of `AlgebraicGeometry.SmallEtale.idealAssociatedMap`;
* the identification is `AlgebraicGeometry.Space.ker_rep_snd_eq_comap_schemeSpaceIdeal` together
  with `AlgebraicGeometry.Space.ker_rep_snd_eq_ofIdealTop_definingIdealAt`, which computes the
  ideal sheaf of the base change of `Z` to an affine chart from a single ideal of global
  functions.

**The route recorded in the "What is not proved" section of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleSchemeComparison.lean` is not the one taken.**
That section proposes the base change of `ε^*` along an étale morphism
(`AlgebraicGeometry.Space.representedAssociatedModuleEtalePullbackIso`), flat base change for a
sheaf of ideals and Descent 03DX (2).  None of the three is used: the passage to an arbitrary
étale chart is naturality in the *module* of the Stacks 03DS identification, which is where
`AlgebraicGeometry.SmallEtale.exists_associatedModule_map_idealIota_app_eq_iff_mem` gets it.

## Main results

* `AlgebraicGeometry.Space.comap_schemeSpaceIdeal_eq_ofIdealTop_definingIdealAt` and
  `AlgebraicGeometry.Space.mem_comap_schemeSpaceIdeal_unitSubmodule_top_iff`: the Zariski sheaf
  of ideals, pulled back to an affine étale chart, is cut out by the defining ideal there.
* `Space.exists_representedAssociatedModule_idealIota_app_eq_iff_mem_definingIdealAt`: **the
  chartwise identification.**

## References

* [Stacks Project, Tag 083B](https://stacks.math.columbia.edu/tag/083B), the ideal sheaf of a
  closed subspace.
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB), the correspondence on
  the small étale site.
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R), the comparison `ε`.
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU), part (4), the
  associated module.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (V : BigFppfOver B S hS) (I : ((BigFppfOver.toScheme B S hS).obj V).IdealSheafData)
  (A : SmallEtale B S hS (yoneda.obj V))

/-- **The inverse image along `ε` of the inclusion of a sheaf of ideals of `𝒪_V` into the
structure sheaf, read on the small étale site of `h_V`, is the transport of
`AlgebraicGeometry.SmallEtale.idealAssociatedMap`.**

`AlgebraicGeometry.Space.representedAssociatedModule` is the associated-module functor of the
small étale site of the scheme followed by the transport along the equivalence of sites
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence`, and
`AlgebraicGeometry.Space.representedAssociatedModuleObjUnitIso` is the transport of the
comparison of structure sheaves; so the composite is the transport of the composite, which is
`AlgebraicGeometry.SmallEtale.idealAssociatedMap` by definition. -/
public theorem representedAssociatedModuleIdealIota_comp_objUnitIso :
    (representedAssociatedModule B S hS V (schemeSpace V).property).map
          (Stacks.ClosedSubscheme.idealIota I) ≫
        (representedAssociatedModuleObjUnitIso B S hS V (schemeSpace V).property).hom =
      (representedModulePushforward B S hS V).map
        (_root_.AlgebraicGeometry.SmallEtale.idealAssociatedMap (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj V) V.left.property I) :=
  ((representedModulePushforward B S hS V).map_comp
    ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj V) V.left.property).map
      (Stacks.ClosedSubscheme.idealIota I))
    (SheafOfModules.pullbackObjUnitToUnit
      (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj V) V.left.property))).symm

/-- The structure morphism of the object of the small étale site of the representing *scheme*
corresponding to an étale chart `A` of `h_V` is the morphism of the site whose Yoneda image is
the structure morphism of `A`. -/
public theorem hom_toOver_obj_representedSmallEtaleEquivalence_functor :
    ((_root_.AlgebraicGeometry.SmallEtale.toOver (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj V) V.left.property).obj
      ((representedSmallEtaleEquivalence B S hS V).functor.obj A)).hom =
      (BigFppfOver.toScheme B S hS).map (yonedaEquiv A.1.hom) := rfl

/-- The two spellings of the morphism of the site underlying an étale chart of a represented
algebraic space agree: `CategoryTheory.yonedaEquiv` of the structure morphism is its
`CategoryTheory.Functor.preimage` under Yoneda, both being the unique morphism whose Yoneda
image it is. -/
public theorem yonedaEquiv_chartHom_eq_preimage :
    (yonedaEquiv A.1.hom : A.1.left ⟶ V) = yoneda.preimage A.1.hom :=
  yoneda.map_injective ((yonedaEquiv.injective (by rw [yonedaEquiv_yoneda_map])).trans
    (yoneda.map_preimage A.1.hom).symm)

variable (Z : ClosedSubspaces B S hS (yoneda.obj V))

/-- **On an affine étale chart of `h_V` the inverse image of the Zariski sheaf of ideals cut out
by a closed subspace is the sheaf of ideals of the defining ideal there.**

`AlgebraicGeometry.Space.ker_rep_snd_eq_comap_schemeSpaceIdeal` identifies the inverse image
with the kernel of pullback of regular functions along the base change of the subspace to the
chart, and on an affine chart that kernel is cut out by a single ideal of global functions,
`AlgebraicGeometry.Space.ker_rep_snd_eq_ofIdealTop_definingIdealAt`. -/
public theorem comap_schemeSpaceIdeal_eq_ofIdealTop_definingIdealAt
    [IsAffine ((BigFppfOver.toScheme B S hS).obj A.1.left)] :
    (schemeSpaceIdeal B S hS V Z).comap
        ((BigFppfOver.toScheme B S hS).map (yonedaEquiv A.1.hom)) =
      Scheme.IdealSheafData.ofIdealTop (definingIdealAt B S hS (schemeSpace V) Z (op A)) := by
  rw [yonedaEquiv_chartHom_eq_preimage B S hS V A,
    ← ker_rep_snd_eq_comap_schemeSpaceIdeal B S hS V Z A]
  exact ker_rep_snd_eq_ofIdealTop_definingIdealAt B S hS (schemeSpace V) Z A

/-- **The global sections over an affine étale chart of `h_V` of the inverse image of the
Zariski sheaf of ideals are the defining ideal of the subspace at that chart.**  This is
`AlgebraicGeometry.Space.comap_schemeSpaceIdeal_eq_ofIdealTop_definingIdealAt` read on the
submodule of the structure sheaf, where the sections over an affine open are the ideal there by
`AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule_obj_affine`. -/
public theorem mem_comap_schemeSpaceIdeal_unitSubmodule_top_iff
    [IsAffine ((BigFppfOver.toScheme B S hS).obj A.1.left)]
    (a : ToType ((structureRingSheaf B S hS (schemeSpace V)).obj.obj (op A))) :
    a ∈ (((schemeSpaceIdeal B S hS V Z).comap
          ((BigFppfOver.toScheme B S hS).map
            (yonedaEquiv A.1.hom))).unitSubmodule).toSubmodule.obj (op ⊤) ↔
      a ∈ definingIdealAt B S hS (schemeSpace V) Z (op A) := by
  rw [Scheme.IdealSheafData.unitSubmodule_obj_affine _
    ⟨⊤, isAffineOpen_top ((BigFppfOver.toScheme B S hS).obj A.1.left)⟩]
  refine Iff.of_eq (congrArg (fun J => a ∈ J) ?_)
  refine Eq.trans (congrArg (fun K => Scheme.IdealSheafData.ideal K
    ⟨⊤, isAffineOpen_top ((BigFppfOver.toScheme B S hS).obj A.1.left)⟩)
    (comap_schemeSpaceIdeal_eq_ofIdealTop_definingIdealAt B S hS V A Z)) ?_
  exact Stacks.Divisors.ideal_ofIdealTop_top (isAffineOpen_top _) _

/-- **The chartwise identification of the defining ideal sheaf of a closed subspace of a
represented algebraic space with the inverse image along `ε` of the Zariski sheaf of ideals it
cuts out.**  Over an affine étale chart `A` of `h_V`, a regular function on the chart scheme is
in the image of `ε^*(I ⊆ 𝒪_V)` exactly when it lies in the defining ideal
`AlgebraicGeometry.Space.definingIdealAt` of the subspace at `A`.

This is what the "What is not proved" section of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleSchemeComparison.lean` records as the
missing *chartwise identification*: the left-hand side mentions only the small étale site of
`h_V` and the right-hand side only the defining ideal of the closed subspace.  The route taken
is not the one recorded there — no base change of `ε^*` along an étale morphism is used — but
`AlgebraicGeometry.SmallEtale.exists_idealAssociatedMap_app_eq_iff_mem`, transported along the
equivalence of the small étale site of `h_V` with that of the representing scheme. -/
public theorem exists_representedAssociatedModule_idealIota_app_eq_iff_mem_definingIdealAt
    [IsAffine ((BigFppfOver.toScheme B S hS).obj A.1.left)]
    (a : ToType ((structureRingSheaf B S hS (schemeSpace V)).obj.obj (op A))) :
    (∃ m, ConcreteCategory.hom
        (((representedAssociatedModule B S hS V (schemeSpace V).property).map
            (Stacks.ClosedSubscheme.idealIota (schemeSpaceIdeal B S hS V Z)) ≫
          (representedAssociatedModuleObjUnitIso B S hS V
            (schemeSpace V).property).hom).val.app (op A)) m = a) ↔
      a ∈ definingIdealAt B S hS (schemeSpace V) Z (op A) := by
  have hA : ∀ m, ConcreteCategory.hom
        (((representedAssociatedModule B S hS V (schemeSpace V).property).map
            (Stacks.ClosedSubscheme.idealIota (schemeSpaceIdeal B S hS V Z)) ≫
          (representedAssociatedModuleObjUnitIso B S hS V
            (schemeSpace V).property).hom).val.app (op A)) m =
      ConcreteCategory.hom
        (((representedModulePushforward B S hS V).map
          (_root_.AlgebraicGeometry.SmallEtale.idealAssociatedMap (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj V) V.left.property
            (schemeSpaceIdeal B S hS V Z))).val.app (op A)) m :=
    fun m => congrArg (fun φ => ConcreteCategory.hom
      (SheafOfModules.Hom.val φ |>.app (op A)) m)
      (representedAssociatedModuleIdealIota_comp_objUnitIso B S hS V (schemeSpaceIdeal B S hS V Z))
  refine Iff.trans ?_ (mem_comap_schemeSpaceIdeal_unitSubmodule_top_iff B S hS V A Z a)
  refine (exists_congr fun m => Eq.congr_left (hA m)).trans
    (_root_.AlgebraicGeometry.SmallEtale.exists_idealAssociatedMap_app_eq_iff_mem
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj V) V.left.property
      (schemeSpaceIdeal B S hS V Z)
      (op ((representedSmallEtaleEquivalence B S hS V).functor.obj A)) a)

end AlgebraicGeometry.Space

end
