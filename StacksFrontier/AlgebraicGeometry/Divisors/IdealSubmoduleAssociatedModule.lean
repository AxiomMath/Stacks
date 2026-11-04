module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity
public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSubmoduleFlatPullback

/-!
# The sheaf of ideals of a closed subscheme on the small étale site

Let `T` be a scheme contained in a big étale site `E` and let `I ⊆ 𝒪_T` be a quasi-coherent
sheaf of ideals, read as a submodule of the structure sheaf by
`AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule`.  The associated-module functor `ε^*` of
Stacks 03DU (4) at `τ = étale` carries `I` to an `𝒪`-module on the small étale site of `T`, and
carries the inclusion `I ⊆ 𝒪_T` to a morphism into the structure sheaf of that site, the
structure sheaf being `ε^*𝒪_T` by Stacks 070R.  This file names that morphism and **computes its
image on sections over an open of `T`.**

The computation is the affine-chart half of the comparison of a sheaf of ideals on the small
étale site with a Zariski sheaf of ideals of the scheme.  It is what
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleSchemeComparison.lean` records as the
missing *chartwise identification*, for the charts cut out by the Zariski opens of `T`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.idealAssociatedMap`: the morphism
  `ε^*I ⟶ 𝒪` of `𝒪`-modules on the small étale site of `T`, namely `ε^*` of the inclusion
  `I ⊆ 𝒪_T` followed by Mathlib's structure-sheaf comparison
  `CategoryTheory.SheafOfModules.pullbackObjUnitToUnit`, which is invertible here because the
  small Zariski site is final in the small étale site.

## Main results

* `AlgebraicGeometry.SmallEtale.homEquiv_idealAssociatedMap` and
  `AlgebraicGeometry.SmallEtale.unit_comp_restrictModule_map_idealAssociatedMap`: **the
  transpose of that morphism along the associated-module adjunction is the inclusion
  `I ⊆ 𝒪_T` followed by the comparison of structure sheaves.**  This is the identity the
  computation rests on, and it needs no section of `ε^*` to be named: Mathlib defines
  `pullbackObjUnitToUnit` as the transpose of `unitToPushforwardObjUnit`, so the transpose of the
  composite is computed by naturality of the adjunction alone.
* `AlgebraicGeometry.SmallEtale.exists_restrictModule_map_idealAssociatedMap_app_eq`: **over an
  open `V` of `T` the sections of `ε^*I ⟶ 𝒪` hit exactly the image of the sections of `I` over
  `V`** under the comparison of structure sheaves.  The unit of the adjunction is an isomorphism
  at `I`, the submodule attached to a sheaf of ideals being quasi-coherent
  (`AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule_isQuasicoherent`) and the unit being
  invertible at every quasi-coherent module by
  `AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent`, Stacks 070S (2); so the transpose
  identity determines the image completely.
* `AlgebraicGeometry.SmallEtale.exists_idealAssociatedMap_app_eq_of_isAffineOpen`: the same over
  an **affine** open, where the sections of `I.unitSubmodule` are the ideal `I.ideal V` itself
  by `AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule_obj_affine`.  This is the form a
  consumer uses: the left-hand side mentions only the small étale site, the right-hand side only
  the affine-local data of `I`.
* `AlgebraicGeometry.SmallEtale.structureMap_hom_app_apply`: the comparison of structure sheaves
  over an open `V` of `T` is, on sections, the isomorphism `Γ(T, V) ≅ Γ(V, ⊤)` of
  `AlgebraicGeometry.Scheme.Opens.topIso`.  This is the transport that
  `AlgebraicGeometry.Space.openChartIdeal` performs on the other side of the comparison, so the
  two sides are stated against the same identification.

## What is not proved here

The comparison of a sheaf of ideals on the small étale site of an *algebraic space* with a
Zariski sheaf of ideals of a representing scheme —
`AlgebraicGeometry.Space.SchemeSpaceIdealModuleComparison` — is **not** proved here, but it is
proved: `AlgebraicGeometry.Space.schemeSpaceIdealModuleComparison` of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedIdealModuleComparison.lean`.  What is missing
beyond the results above is the passage from the charts cut out by the Zariski opens of `T`,
which is what the associated-module adjunction sees, to an arbitrary étale chart; that passage
is `AlgebraicGeometry.SmallEtale.exists_idealAssociatedMap_app_eq_iff_mem` of
`StacksFrontier/AlgebraicGeometry/Divisors/IdealAssociatedModuleChartImage.lean`, and it is
naturality in the *module* of the Stacks 03DS identification.  **None of the three inputs this
section used to name for it is used** — the base change of `ε^*` along an étale morphism
(`AlgebraicGeometry.Space.representedAssociatedModuleEtalePullbackIso`), flat base change for a
sheaf of ideals (`Stacks.ClosedSubscheme.pullbackIdealFlatIso`) and the
cartesian-on-affine-charts property of Descent, Proposition 03DX (2)
(`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite`) — although all
three are available in the tree.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU), part (4), the associated
  module.
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R), the comparison `ε`.
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S), part (2), the sections
  of the associated module.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (E : BigEtaleSite.{u}) (T : Scheme.{u}) (hT : E.Contains T) (I : T.IdealSheafData)

/-- **The inverse image along `ε` of the inclusion of a sheaf of ideals into the structure
sheaf.**  The associated-module functor of Stacks 03DU (4) at `τ = étale` applied to the
inclusion `I ⊆ 𝒪_T`, followed by the comparison `ε^*𝒪_T ≅ 𝒪` of Stacks 070R. -/
public noncomputable def idealAssociatedMap :
    (associatedModule E T hT).obj I.unitSubmodule.toSheafOfModules ⟶
      SheafOfModules.unit (structureSheaf E T hT) :=
  (associatedModule E T hT).map (Stacks.ClosedSubscheme.idealIota I) ≫
    SheafOfModules.pullbackObjUnitToUnit (structureMap E T hT)

/-- **The transpose of `AlgebraicGeometry.SmallEtale.idealAssociatedMap` is the inclusion
`I ⊆ 𝒪_T` followed by the comparison of structure sheaves.**

Nothing about the sections of `ε^*I` is used: the transpose of `ε^*(ι) ≫ θ` is `ι` followed by
the transpose of `θ`, and `CategoryTheory.SheafOfModules.pullbackObjUnitToUnit` is *defined* as
the transpose of `CategoryTheory.SheafOfModules.unitToPushforwardObjUnit`. -/
public theorem homEquiv_idealAssociatedMap :
    (associatedModuleAdjunction E T hT).homEquiv _ _ (idealAssociatedMap E T hT I) =
      Stacks.ClosedSubscheme.idealIota I ≫
        SheafOfModules.unitToPushforwardObjUnit (structureMap E T hT) :=
  ((associatedModuleAdjunction E T hT).homEquiv_naturality_left
      (Stacks.ClosedSubscheme.idealIota I)
      (SheafOfModules.pullbackObjUnitToUnit (structureMap E T hT))).trans
    (congrArg (fun t => Stacks.ClosedSubscheme.idealIota I ≫ t)
      (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
        (structureMap E T hT)))

/-- `AlgebraicGeometry.SmallEtale.homEquiv_idealAssociatedMap` with the transpose written out as
the unit of the adjunction followed by restriction along the inclusion of the small Zariski
site.  This is the form that can be read on the sections over an open. -/
public theorem unit_comp_restrictModule_map_idealAssociatedMap :
    (associatedModuleAdjunction E T hT).unit.app I.unitSubmodule.toSheafOfModules ≫
        (restrictModule E T hT).map (idealAssociatedMap E T hT I) =
      Stacks.ClosedSubscheme.idealIota I ≫
        SheafOfModules.unitToPushforwardObjUnit (structureMap E T hT) :=
  Eq.trans
    (Eq.symm (Adjunction.homEquiv_unit (associatedModuleAdjunction E T hT)
      I.unitSubmodule.toSheafOfModules _ (idealAssociatedMap E T hT I)))
    (homEquiv_idealAssociatedMap E T hT I)

/-- **The unit of the associated-module adjunction is invertible at a sheaf of ideals.**  The
submodule of the structure sheaf attached to a sheaf of ideals is quasi-coherent — Stacks 01R8,
`AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule_isQuasicoherent` — and the unit is
invertible at every quasi-coherent module by
`AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent`. -/
public instance isIso_unit_app_unitSubmodule :
    IsIso ((associatedModuleAdjunction E T hT).unit.app
      I.unitSubmodule.toSheafOfModules) :=
  unitIsoOnQuasicoherent E T hT ⟨I.unitSubmodule.toSheafOfModules, inferInstance⟩

/-- `AlgebraicGeometry.SmallEtale.unit_comp_restrictModule_map_idealAssociatedMap` read on the
sections over an open of `T`. -/
public theorem unit_comp_restrictModule_map_idealAssociatedMap_app (V : (T.Opens)ᵒᵖ) :
    ((associatedModuleAdjunction E T hT).unit.app
          I.unitSubmodule.toSheafOfModules).val.app V ≫
        ((restrictModule E T hT).map (idealAssociatedMap E T hT I)).val.app V =
      (Stacks.ClosedSubscheme.idealIota I).val.app V ≫
        (SheafOfModules.unitToPushforwardObjUnit (structureMap E T hT)).val.app V :=
  congrArg (fun k => k.val.app V)
    (unit_comp_restrictModule_map_idealAssociatedMap E T hT I)

/-- The unit of the associated-module adjunction at a sheaf of ideals is surjective on the
sections over an open, being invertible. -/
public theorem surjective_unit_app_unitSubmodule_app (V : (T.Opens)ᵒᵖ) :
    Function.Surjective (ConcreteCategory.hom
      (((associatedModuleAdjunction E T hT).unit.app
        I.unitSubmodule.toSheafOfModules).val.app V)) := fun m =>
  ⟨ConcreteCategory.hom ((inv ((associatedModuleAdjunction E T hT).unit.app
      I.unitSubmodule.toSheafOfModules)).val.app V) m,
    ConcreteCategory.congr_hom (congrArg (fun k => k.val.app V)
      (IsIso.inv_hom_id ((associatedModuleAdjunction E T hT).unit.app
        I.unitSubmodule.toSheafOfModules))) m⟩

/-- **Over an open of `T` the sections of `ε^*I ⟶ 𝒪` hit exactly the sections of `I` there**,
read through the comparison of structure sheaves.

One inclusion is the transpose identity
`AlgebraicGeometry.SmallEtale.unit_comp_restrictModule_map_idealAssociatedMap_app` alone; the
other also uses that the unit is surjective on sections, so that every section of `ε^*I` over
the open is the image of a section of `I`. -/
public theorem exists_restrictModule_map_idealAssociatedMap_app_eq (V : (T.Opens)ᵒᵖ)
    (a : ToType (((restrictModule E T hT).obj
      (SheafOfModules.unit (structureSheaf E T hT))).val.obj V)) :
    (∃ m, ConcreteCategory.hom
        (((restrictModule E T hT).map (idealAssociatedMap E T hT I)).val.app V) m = a) ↔
      ∃ b, b ∈ I.unitSubmodule.obj V ∧
        ConcreteCategory.hom
          ((SheafOfModules.unitToPushforwardObjUnit (structureMap E T hT)).val.app V) b = a := by
  have key := ConcreteCategory.congr_hom
    (unit_comp_restrictModule_map_idealAssociatedMap_app E T hT I V)
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨x, hx⟩ := surjective_unit_app_unitSubmodule_app E T hT I V m
    subst hx
    exact ⟨x.1, x.2, (key x).symm.trans hm⟩
  · rintro ⟨b, hb, hba⟩
    exact ⟨_, (key ⟨b, hb⟩).trans hba⟩

/-- **The comparison of structure sheaves over an open `V` of `T` is, on sections, the
isomorphism `Γ(T, V) ≅ Γ(V, ⊤)`** of `AlgebraicGeometry.Scheme.Opens.topIso`.

The sections of `𝒪` over the étale chart cut out by `V` are the *global* functions on `V`, while
the sections of `𝒪_T` over `V` are functions on `V` read inside `T`; this records that the
comparison of structure sheaves is the canonical identification of the two, which is the same
transport that `AlgebraicGeometry.Space.openChartIdeal` performs. -/
public theorem structureMap_hom_app_apply (V : T.Opens)
    (b : ToType (T.ringCatSheaf.obj.obj (op V))) :
    ConcreteCategory.hom ((structureMap E T hT).hom.app (op V)) b =
      ConcreteCategory.hom V.topIso.inv b := rfl

/-- **The affine-chart identification.**  Over an affine open `V` of `T`, the sections of
`ε^*I ⟶ 𝒪` on the small étale site hit exactly the image of the ideal `I.ideal V` under the
comparison of structure sheaves.

This is `AlgebraicGeometry.SmallEtale.exists_restrictModule_map_idealAssociatedMap_app_eq` with
the sections of `I.unitSubmodule` over the affine open replaced by the ideal itself, which is
`AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule_obj_affine`.  The left-hand side mentions
only the small étale site and the right-hand side only the affine-local data of `I`. -/
public theorem exists_idealAssociatedMap_app_eq_of_isAffineOpen (V : T.affineOpens)
    (a : ToType ((SheafOfModules.unit (structureSheaf E T hT)).val.obj
      (op (opensObj E T hT V.1)))) :
    (∃ m, ConcreteCategory.hom
        ((idealAssociatedMap E T hT I).val.app (op (opensObj E T hT V.1))) m = a) ↔
      ∃ b, b ∈ I.ideal V ∧
        ConcreteCategory.hom ((structureMap E T hT).hom.app (op V.1)) b = a := by
  refine (exists_restrictModule_map_idealAssociatedMap_app_eq E T hT I (op V.1) a).trans
    (exists_congr fun b => and_congr_left' ?_)
  rw [I.unitSubmodule_obj_affine V]
  exact Iff.rfl

end AlgebraicGeometry.SmallEtale

end
