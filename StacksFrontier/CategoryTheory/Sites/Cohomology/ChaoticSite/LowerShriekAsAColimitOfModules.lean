module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.LowerShriekAsAColimit
import StacksCore.Tactic.StacksAttribute

/-!
# Lower shriek to a point as a colimit, with linear coefficients

Let `s` be a ringed-point situation: a category `C` with the chaotic topology, a ring `B`
carried on the point, and `π : (Sh(C), B̲) ⟶ (Sh(*), B)` the induced morphism of ringed topoi.
This file is the linear half of [Stacks, Tag 08PF]: the inverse image `π_!` of a sheaf with
coefficients in `ModuleCat B` is the colimit of the underlying presheaf of `B`-modules.

On the chaotic site a sheaf of `B̲`-modules is exactly a presheaf of `B`-modules, so
`Sheaf (GrothendieckTopology.trivial C) (ModuleCat B)` is the ringed-site category the source
speaks about; `Stacks.ChaoticSite.moduleSheafEquivalence` records that identification on the
`SheafOfModules` side.

## Main definitions

* `Stacks.ChaoticSite.ModuleValued.moduleColimitLowerShriek`: the colimit functor to
  module-valued sheaves on the point.

## Main results

* `Stacks.ChaoticSite.ModuleValued.moduleLowerShriekColimitAdjunction`: the colimit functor is
  left adjoint to restriction along the point functor.
* `Stacks.ChaoticSite.ModuleValued.moduleLowerShriekColimitIso`: the established inverse image
  `Functor.sheafPullback` along the point **is** the colimit functor, naturally in the sheaf.
* `Stacks.ChaoticSite.ModuleValued.moduleLowerShriekColimitIso_unit`: the comparison carries the
  unit of the established lower shriek to the unit of the colimit adjunction.
* `Stacks.ChaoticSite.ModuleValued.moduleLowerShriekColimit_evalIso` and
  `moduleLowerShriekColimit_unit_cocone`: the comparison evaluated at the point is the ordinary
  colimit, and the unit is the canonical colimit cocone.

## Implementation notes

Nothing is reproved here. The abelian half of the tag already states its two load-bearing
pieces at a general coefficient category — `Stacks.ChaoticSite.presheafColimitStarAdjunction`
takes any `A` with `[HasColimitsOfShape Cᵒᵖ A]`, and `Stacks.ChaoticSite.trivialHasSheafify`
supplies sheafification for the chaotic topology at any `A` — so the four clauses below are
those same constructions instantiated at `A := ModuleCat B`. `ModuleCat` has colimits of every
shape, so no size hypothesis is needed.

`moduleLowerShriekColimitIso_unit` is the general uniqueness law
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` read at these two adjunctions; it is
recorded explicitly because the clause asserts it of these particular functors.

The declarations live in the `ModuleValued` namespace because two of the clause's names are
already taken in `Stacks.ChaoticSite` by different statements:
`Stacks.ChaoticSite.moduleColimitLowerShriek` is the `SheafOfModules`-to-`SheafOfModules`
colimit functor, and `Stacks.ChaoticSite.pointModule_isRightAdjoint` is the
`SheafOfModules.pushforward` adjointness instance. The clause here is about sheaves *valued*
in `ModuleCat B`, which is the spelling the colimit formula is stated in.

The universes are the situation's and are independent: `C : Type u` with `Category.{v} C`, the
ring in `CommRingCat.{max w u v}`, and module sections in `max w (u + 1) v`. No universe is
narrowed.

## References

* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
* [Stacks Project, Tag 08PE](https://stacks.math.columbia.edu/tag/08PE)
* [Stacks Project, Tag 09CY](https://stacks.math.columbia.edu/tag/09CY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.ChaoticSite.ModuleValued

universe w v u

variable (s : RingedPointSituation.{w, v, u})

/-- **Stacks 08PF.** The colimit formula with linear coefficients, regarded as a functor to
module-valued sheaves on the point. -/
def moduleColimitLowerShriek :
    Sheaf (GrothendieckTopology.trivial s.C) (ModuleCat.{max w (u + 1) v} s.B) ⥤
      Sheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))
        (ModuleCat.{max w (u + 1) v} s.B) :=
  sheafToPresheaf (GrothendieckTopology.trivial s.C) (ModuleCat.{max w (u + 1) v} s.B) ⋙
    (colim : (s.Cᵒᵖ ⥤ ModuleCat.{max w (u + 1) v} s.B) ⥤
      ModuleCat.{max w (u + 1) v} s.B) ⋙
    (Functor.const (Discrete PUnit.{u + 1})ᵒᵖ) ⋙
    presheafToSheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))
      (ModuleCat.{max w (u + 1) v} s.B)

/-- The colimit formula is the lower shriek of a module-valued sheaf, naturally in the sheaf. -/
def moduleLowerShriekColimitAdjunction :
    moduleColimitLowerShriek s ⊣
      (Functor.star s.C).sheafPushforwardContinuous (ModuleCat.{max w (u + 1) v} s.B)
        (GrothendieckTopology.trivial s.C)
        (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) :=
  ((presheafColimitStarAdjunction (ModuleCat.{max w (u + 1) v} s.B) s.C).comp
      (sheafificationAdjunction (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))
        (ModuleCat.{max w (u + 1) v} s.B))).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf _ _) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

/-- Restriction of module-valued sheaves along the point functor has a left adjoint. -/
instance pointModule_isRightAdjoint :
    ((Functor.star s.C).sheafPushforwardContinuous (ModuleCat.{max w (u + 1) v} s.B)
      (GrothendieckTopology.trivial s.C)
      (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))).IsRightAdjoint :=
  (moduleLowerShriekColimitAdjunction s).isRightAdjoint

/-- **Stacks 08PF.** The established lower shriek on module-valued sheaves is naturally the
colimit functor, rather than merely another left adjoint to point restriction. -/
@[stacks 08PF "lower_shriek_colimit"]
def moduleLowerShriekColimitIso :
    (Functor.star s.C).sheafPullback (ModuleCat.{max w (u + 1) v} s.B)
      (GrothendieckTopology.trivial s.C)
      (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) ≅
      moduleColimitLowerShriek s :=
  Adjunction.leftAdjointUniq
    ((Functor.star s.C).sheafAdjunctionContinuous (ModuleCat.{max w (u + 1) v} s.B)
      (GrothendieckTopology.trivial s.C)
      (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})))
    (moduleLowerShriekColimitAdjunction s)

/-- **Stacks 08PF.** The module comparison preserves the canonical unit. -/
@[stacks 08PF "lower_shriek_colimit"]
theorem moduleLowerShriekColimitIso_unit
    (F : Sheaf (GrothendieckTopology.trivial s.C) (ModuleCat.{max w (u + 1) v} s.B)) :
    ((Functor.star s.C).sheafAdjunctionContinuous (ModuleCat.{max w (u + 1) v} s.B)
      (GrothendieckTopology.trivial s.C)
      (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))).unit.app F ≫
      ((Functor.star s.C).sheafPushforwardContinuous (ModuleCat.{max w (u + 1) v} s.B)
        (GrothendieckTopology.trivial s.C)
        (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))).map
          ((moduleLowerShriekColimitIso s).hom.app F) =
    (moduleLowerShriekColimitAdjunction s).unit.app F :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ F

/-- **Stacks 08PF.** At each object, the colimit presentation evaluated at the point is the
colimit of the underlying presheaf of modules. -/
@[stacks 08PF "lower_shriek_colimit"]
def moduleLowerShriekColimit_evalIso
    (F : Sheaf (GrothendieckTopology.trivial s.C) (ModuleCat.{max w (u + 1) v} s.B)) :
    ((moduleColimitLowerShriek s).obj F).obj.obj
      (op (Discrete.mk PUnit.unit)) ≅ colimit F.obj :=
  ((isoSheafify (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))
      (P := (Functor.const (Discrete PUnit.{u + 1})ᵒᵖ).obj (colimit F.obj))
      (by
        simpa only [GrothendieckTopology.trivial_eq_bot] using
          Presheaf.isSheaf_bot
            ((Functor.const (Discrete PUnit.{u + 1})ᵒᵖ).obj (colimit F.obj)))).app
    (op (Discrete.mk PUnit.unit))).symm

/-- **Stacks 08PF.** At each object, the unit of the colimit presentation is the canonical map
into the colimit of the underlying presheaf of modules. -/
@[stacks 08PF "lower_shriek_colimit"]
theorem moduleLowerShriekColimit_unit_cocone
    (F : Sheaf (GrothendieckTopology.trivial s.C) (ModuleCat.{max w (u + 1) v} s.B)) (U : s.C) :
    ((moduleLowerShriekColimitAdjunction s).unit.app F).hom.app (op U) ≫
      (moduleLowerShriekColimit_evalIso s F).hom =
      colimit.ι F.obj (op U) := by
  have key := Adjunction.map_restrictFullyFaithful_unit_app
    (L := moduleColimitLowerShriek s)
    (R := (Functor.star s.C).sheafPushforwardContinuous (ModuleCat.{max w (u + 1) v} s.B)
      (GrothendieckTopology.trivial s.C)
      (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})))
    ((presheafColimitStarAdjunction (ModuleCat.{max w (u + 1) v} s.B) s.C).comp
      (sheafificationAdjunction (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))
        (ModuleCat.{max w (u + 1) v} s.B)))
    (fullyFaithfulSheafToPresheaf _ _) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _) F
  have h2 : ((moduleLowerShriekColimitAdjunction s).unit.app F).hom
      = ((presheafColimitStarAdjunction (ModuleCat.{max w (u + 1) v} s.B) s.C).comp
          (sheafificationAdjunction (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))
            (ModuleCat.{max w (u + 1) v} s.B))).unit.app F.obj :=
    key.trans (by cat_disch)
  have h3 : ((moduleLowerShriekColimitAdjunction s).unit.app F).hom.app (op U)
      = colimit.ι F.obj (op U) ≫ (moduleLowerShriekColimit_evalIso s F).inv := by
    rw [h2]
    simp only [GrothendieckTopology.trivial_eq_bot, Functor.id_obj, Functor.comp_obj,
      Adjunction.comp_unit_app, colim_obj, Functor.whiskeringLeft_obj_obj, ObjectProperty.ι_obj,
      sheafificationAdjunction_unit_app, Functor.whiskeringLeft_obj_map, NatTrans.comp_app,
      Functor.op_obj, Functor.const_obj_obj, presheafColimitStarAdjunction_unit_app_app,
      Functor.whiskerLeft_app, moduleLowerShriekColimit_evalIso, Iso.symm_inv, Iso.app_hom,
      isoSheafify_hom]
    dsimp only [star_obj_eq]
    rfl
  refine (congrArg (fun g => g ≫ (moduleLowerShriekColimit_evalIso s F).hom) h3).trans ?_
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Stacks.ChaoticSite.ModuleValued

end
