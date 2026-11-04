module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restriction of sheaves of modules to a slice site preserves colimits

Let `R` be a sheaf of rings on a site `(C, J)` and let `V` be an object of `C`.  Restriction
to the slice site, `SheafOfModules.overFunctor R V`, preserves colimits.  Mathlib obtains this
from `SheafOfModules.overPushforwardOverAdj`, which exhibits the restriction as a left adjoint
but needs `Over.star V`, hence `HasBinaryProducts C`: a hypothesis a site need not satisfy.

This file removes that hypothesis.  Restriction of *abelian* sheaves to a slice site is a left
adjoint with no products in sight, because `Over.forget V` is both continuous and cocontinuous
and the right adjoint is the right Kan extension along it
(`CategoryTheory.Functor.sheafAdjunctionCocontinuous`).  Forgetting the module structure of a
sheaf of modules reflects isomorphisms, so once it is known to preserve colimits it reflects
them, and restriction of sheaves of modules preserves colimits because it does so after
forgetting the module structure — where it *is* the restriction of abelian sheaves, on the
nose.

## Main results

* `Stacks.SheafOfModules.preservesColimits_toSheaf`: forgetting the module structure of a sheaf
  of modules preserves colimits.
* `Stacks.SheafOfModules.preservesColimits_overFunctor`: restriction of sheaves of modules to a
  slice site preserves colimits, with no finite limits assumed on the site.
* `Stacks.SheafOfModules.preservesColimits_overFunctor_of_small`: the same for a site whose
  objects and morphisms live in the universe of the sections, which is the shape in which
  [Stacks, Tag 082T] uses it.

## Implementation notes

The only hypothesis of `preservesColimits_overFunctor` beyond those already needed to state
colimits of sheaves of modules is the existence of pointwise right Kan extensions along
`(Over.forget V).op` for presheaves of abelian groups; this is a size condition, and
`preservesColimits_overFunctor_of_small` discharges it for `C : Type u` with
`Category.{u} C`.

These results are deliberately stated as theorems rather than instances: the Kan extension
hypothesis is a universally quantified instance goal, and making it participate in instance
search for every sheaf of modules in the development would be paid for everywhere while being
needed only where a site carries no finite limits.

## References

* [Stacks Project, Tag 082T](https://stacks.math.columbia.edu/tag/082T)
* [Stacks Project, Tag 01BP](https://stacks.math.columbia.edu/tag/01BP)
-/

@[expose] public section

open CategoryTheory Limits SheafOfModules

universe u v₁ u₁

namespace Stacks.SheafOfModules

section ToSheaf

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Forgetting the module structure preserves colimits.**  A colimit of sheaves of modules is
the sheafification of the colimit of the underlying presheaves of modules, and sheafification of
presheaves of modules is compatible with forgetting the module structure on the nose
(`PresheafOfModules.sheafificationCompToSheaf`), so the underlying abelian sheaf of the colimit
is the sheafification of the colimit of the underlying presheaves of abelian groups. -/
theorem preservesColimits_toSheaf :
    PreservesColimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u} R) where
  preservesColimitsOfShape {K} _ :=
    { preservesColimit := fun {D} ↦ by
        have hc : PreservesColimitsOfSize.{u, u}
            (PresheafOfModules.sheafification.{u} (𝟙 R.obj) ⋙ SheafOfModules.toSheaf.{u} R) :=
          preservesColimits_of_natIso
            (PresheafOfModules.sheafificationCompToSheaf (𝟙 R.obj)).symm
        let E := D ⋙ SheafOfModules.forget R
        let L := PresheafOfModules.sheafification.{u} (𝟙 R.obj)
        let e : E ⋙ L ≅ D := Functor.isoWhiskerLeft D
          (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit)
        have h : IsColimit
            ((SheafOfModules.toSheaf.{u} R).mapCocone (L.mapCocone (colimit.cocone E))) :=
          isColimitOfPreserves (L ⋙ SheafOfModules.toSheaf.{u} R) (colimit.isColimit E)
        have := preservesColimit_of_preserves_colimit_cocone
          (isColimitOfPreserves L (colimit.isColimit E)) h
        exact preservesColimit_of_iso_diagram (SheafOfModules.toSheaf.{u} R) e }

/-- **Forgetting the module structure reflects colimits.**  It reflects isomorphisms and, by
`Stacks.SheafOfModules.preservesColimits_toSheaf`, preserves colimits. -/
theorem reflectsColimits_toSheaf :
    ReflectsColimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u} R) :=
  have := preservesColimits_toSheaf.{u} (R := R)
  reflectsColimits_of_reflectsIsomorphisms

end ToSheaf

section Over

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Restriction to a slice site preserves colimits, with no products on the site.**  After
forgetting the module structures, restriction of sheaves of modules to the slice site over `V`
*is* restriction of abelian sheaves along `Over.forget V`, which is a left adjoint because
`Over.forget V` is continuous and cocontinuous; and forgetting the module structure reflects
colimits. -/
theorem preservesColimits_overFunctor (V : C)
    [∀ F : (Over V)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (Over.forget V).op.HasPointwiseRightKanExtension F] :
    PreservesColimitsOfSize.{u, u} (overFunctor.{u} R V) :=
  have _hres : PreservesColimitsOfSize.{u, u}
      ((Over.forget V).sheafPushforwardContinuous AddCommGrpCat.{u} (J.over V) J) :=
    ((Over.forget V).sheafAdjunctionCocontinuous
      AddCommGrpCat.{u} (J.over V) J).leftAdjoint_preservesColimits
  have _hcomp : PreservesColimitsOfSize.{u, u}
      (overFunctor.{u} R V ⋙ SheafOfModules.toSheaf.{u} (R.over V)) :=
    have := preservesColimits_toSheaf.{u} (R := R)
    inferInstanceAs (PreservesColimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u} R ⋙
      (Over.forget V).sheafPushforwardContinuous AddCommGrpCat.{u} (J.over V) J))
  have := reflectsColimits_toSheaf.{u} (R := R.over V)
  preservesColimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf.{u} (R.over V))

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Restriction along a morphism of the site preserves colimits, with no pullbacks on the
site.**  Mathlib gets this from `SheafOfModules.overMapPushforwardAdj`, which needs
`Over.pullback f` and hence `HasPullbacks C`.  But `Over.map f` is continuous and cocontinuous
for the slice topologies with no hypothesis at all, so the same argument as for
`Stacks.SheafOfModules.preservesColimits_overFunctor` applies. -/
@[ega "0 4.3.2" "partial"]
theorem preservesColimits_overMap {V W : C} (f : W ⟶ V)
    [∀ F : (Over W)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (Over.map f).op.HasPointwiseRightKanExtension F] :
    PreservesColimitsOfSize.{u, u} (overMap.{u} R f) :=
  have _hres : PreservesColimitsOfSize.{u, u}
      ((Over.map f).sheafPushforwardContinuous AddCommGrpCat.{u} (J.over W) (J.over V)) :=
    ((Over.map f).sheafAdjunctionCocontinuous
      AddCommGrpCat.{u} (J.over W) (J.over V)).leftAdjoint_preservesColimits
  have _hcomp : PreservesColimitsOfSize.{u, u}
      (overMap.{u} R f ⋙ SheafOfModules.toSheaf.{u} (R.over W)) :=
    have := preservesColimits_toSheaf.{u} (R := R.over V)
    inferInstanceAs (PreservesColimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u} (R.over V) ⋙
      (Over.map f).sheafPushforwardContinuous AddCommGrpCat.{u} (J.over W) (J.over V)))
  have := reflectsColimits_toSheaf.{u} (R := R.over W)
  preservesColimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf.{u} (R.over W))

end Over

section Small

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- `Stacks.SheafOfModules.preservesColimits_overFunctor` for a site whose objects and
morphisms live in the universe of the sections: there the pointwise right Kan extensions along
`(Over.forget V).op` exist because `AddCommGrpCat.{u}` has limits of that size. -/
@[sga "4 IV 11.2.2" "partial"]
theorem preservesColimits_overFunctor_of_small (V : C) :
    PreservesColimitsOfSize.{u, u} (overFunctor.{u} R V) :=
  preservesColimits_overFunctor R V

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `Stacks.SheafOfModules.preservesColimits_overMap` for a site whose objects and morphisms
live in the universe of the sections. -/
theorem preservesColimits_overMap_of_small {V W : C} (f : W ⟶ V) :
    PreservesColimitsOfSize.{u, u} (overMap.{u} R f) :=
  preservesColimits_overMap R f

end Small

end Stacks.SheafOfModules

end
