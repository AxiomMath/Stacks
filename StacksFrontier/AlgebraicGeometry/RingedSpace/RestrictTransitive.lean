module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import StacksFrontier.CategoryTheory.Sites.Modules.OverFunctorExact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.RestrictionOfComplexes
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Transitivity of restriction of sheaves of modules to a slice

Let `R` be a sheaf of rings on a site `(C, J)`. Restricting a sheaf of `R`-modules `M` to an
object `U` of `C` gives `M.over U`, a sheaf of modules over `R.over U` on the slice `Over U`.
This file assembles the data needed to shrink `U`: for `f : U' ⟶ U` the natural isomorphism
`SheafOfModules.overFunctorMap` identifies "restrict to `U` then push to `U'`" with "restrict
to `U'`", and conjugating by it turns a morphism between restrictions to `U` into a morphism
between restrictions to `U'`.

This is the transport that an induction producing data over smaller and smaller `U` needs. In
the `Over U` idiom the two slices live over one and the same site, so the comparison
isomorphism is built from identities; nothing has to be transported along a change of the
underlying space.

## Main definitions

* `SheafOfModules.overRestrict`: a morphism `M.over U ⟶ N.over U` restricted along
  `f : U' ⟶ U` to a morphism `M.over U' ⟶ N.over U'`.
* `SheafOfModules.overSectionsAlong`: a section of `M` over `U` viewed as a global section of
  `M.over U'` for `f : U' ⟶ U`.

## Main results

* `SheafOfModules.overFunctor_preservesFiniteLimits_opens`: on the site of opens of a space,
  restriction to a slice preserves finite limits with no typeclass hypotheses, so it carries a
  kernel to a kernel.
* `SheafOfModules.overRestrict_comp`, `SheafOfModules.overRestrict_map`,
  `SheafOfModules.overRestrict_add`, `SheafOfModules.overRestrict_sub`,
  `SheafOfModules.overRestrict_zero`: `overRestrict` is additive, compatible with composition,
  and takes the restriction of a global morphism to its restriction.
* `SheafOfModules.unitHomEquiv_symm_overSections_comp`: the morphism out of the unit object
  classified by a lifted section is a lift of the restriction of the morphism classified by the
  original section.

## Implementation notes

`overRestrict` is conjugation of `SheafOfModules.overMap` by `SheafOfModules.overFunctorMap`;
it is not the action on morphisms of a functor, because its source and target objects are
pinned to restrictions of fixed objects of `SheafOfModules R`. All of its algebraic properties
come from naturality of `overFunctorMap` together with additivity of `overMap`.

Additivity of `overMap` is `SheafOfModules.overMap_additive` of
`StacksFrontier.CategoryTheory.Sites.Modules.OverFunctorExact`, imported rather than restated.
Preservation of finite limits is checked after composing with
`SheafOfModules.forget ⋙ PresheafOfModules.toPresheaf`, which reflects isomorphisms and
preserves limits; restriction followed by that functor is, by construction of the pushforward,
*equal* to that functor followed by restriction of presheaves of abelian groups along
`Over.forget`, and limits of presheaves are computed pointwise.

Sections of a restriction are indexed by the whole slice `Over U'`, and the value of such a
family at an object `V` of the slice is a section over `V.left`; the structure morphism
`V.hom : V.left ⟶ U'` is what makes the restriction of a section over `U` to all of them
possible. The distinguished index is `Over.mk (𝟙 U)`, the terminal object of `Over U`, whose
value is the section over `U` itself.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

universe v u v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

section Additive

-- Restriction of sheaves of modules to a slice is additive: `SheafOfModules.overFunctor_additive`
-- in `StacksFrontier/CategoryTheory/Sites/Cohomology/Slice/RestrictionOfComplexes.lean`.
-- Additivity of `SheafOfModules.overMap` is `SheafOfModules.overMap_additive` in
-- `StacksFrontier/CategoryTheory/Sites/Modules/OverFunctorExact.lean`, which is imported for it.

/-- Restriction to an open subset of sheaves of modules over a sheaf of rings on a topological
space preserves finite limits.

After composing with the forgetful functor to presheaves of abelian groups, which reflects
isomorphisms and preserves limits, restriction becomes restriction of presheaves along
`Over.forget`, and limits of presheaves are computed pointwise.

`SheafOfModules.overFunctor_preservesFiniteLimits` of
`StacksFrontier.CategoryTheory.Sites.Modules.OverFunctorExact` is the general-site statement, but
it carries `HasSheafify` and `WEqualsLocallyBijective` hypotheses for the slice topology which
instance search does not discharge on the site of opens of a space. This version has no
hypotheses: on that site the sheafification typeclasses — on the space and on each of its
slices — are available unconditionally. -/
@[sga "6 I 1.3" "partial"]
public instance overFunctor_preservesFiniteLimits_opens {T : Type u} [TopologicalSpace T]
    (R : Sheaf (_root_.Opens.grothendieckTopology T) RingCat.{u})
    (U : TopologicalSpace.Opens T) : PreservesFiniteLimits (overFunctor.{u} R U) := by
  have e : overFunctor.{u} R U ⋙
        (forget.{u} (R.over U) ⋙ PresheafOfModules.toPresheaf _) ≅
      (forget.{u} R ⋙ PresheafOfModules.toPresheaf _) ⋙
        (Functor.whiskeringLeft (Over U)ᵒᵖ (TopologicalSpace.Opens T)ᵒᵖ
          AddCommGrpCat.{u}).obj (Over.forget U).op :=
    Iso.refl _
  have : PreservesFiniteLimits (overFunctor.{u} R U ⋙
      (forget.{u} (R.over U) ⋙ PresheafOfModules.toPresheaf _)) :=
    preservesFiniteLimits_of_natIso e.symm
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (forget.{u} (R.over U) ⋙ PresheafOfModules.toPresheaf _)

/-- Restriction of sheaves of modules to a slice has finite biproducts in its target: the
category of sheaves of modules over the restricted sheaf of rings is preadditive and has finite
products. -/
public instance hasFiniteBiproducts_over (R : Sheaf J RingCat.{u}) (U : C) :
    HasFiniteBiproducts (SheafOfModules.{v} (R.over U)) :=
  HasFiniteBiproducts.of_hasFiniteProducts

end Additive

section OverRestrict

variable {U' U : C} (f : U' ⟶ U) {M N P : SheafOfModules.{v} R}

/-- A morphism between the restrictions of `M` and `N` to `U`, restricted along `f : U' ⟶ U` to
a morphism between their restrictions to `U'`.

This is `SheafOfModules.overMap R f` conjugated by the isomorphism
`SheafOfModules.overFunctorMap R f` which identifies restricting to `U` and pushing to `U'`
with restricting to `U'`. -/
public def overRestrict (γ : M.over U ⟶ N.over U) : M.over U' ⟶ N.over U' :=
  (overFunctorMap R f).inv.app M ≫ (overMap R f).map γ ≫ (overFunctorMap R f).hom.app N

/-- Restricting the restriction of a global morphism gives its restriction: this is naturality
of `SheafOfModules.overFunctorMap`. -/
@[simp]
public theorem overRestrict_map (u : M ⟶ N) :
    overRestrict f ((overFunctor R U).map u) = (overFunctor R U').map u := by
  rw [overRestrict, ← Functor.comp_map, (overFunctorMap R f).hom.naturality u,
    ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

/-- Restriction of morphisms along `f` is compatible with composition. -/
public theorem overRestrict_comp (γ : M.over U ⟶ N.over U) (δ : N.over U ⟶ P.over U) :
    overRestrict f (γ ≫ δ) = overRestrict f γ ≫ overRestrict f δ := by
  simp only [overRestrict, Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]

/-- Restriction of morphisms along `f` takes the zero morphism to the zero morphism. -/
@[simp]
public theorem overRestrict_zero : overRestrict f (0 : M.over U ⟶ N.over U) = 0 := by
  simp only [overRestrict, Functor.map_zero, Limits.zero_comp, Limits.comp_zero]

/-- Restriction of morphisms along `f` is additive. -/
public theorem overRestrict_add (γ δ : M.over U ⟶ N.over U) :
    overRestrict f (γ + δ) = overRestrict f γ + overRestrict f δ := by
  simp only [overRestrict, Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]

/-- Restriction of morphisms along `f` commutes with subtraction. -/
public theorem overRestrict_sub (γ δ : M.over U ⟶ N.over U) :
    overRestrict f (γ - δ) = overRestrict f γ - overRestrict f δ := by
  simp only [overRestrict, Functor.map_sub, Preadditive.comp_sub, Preadditive.sub_comp]

end OverRestrict

section Sections

variable {U' U : C} {M N : SheafOfModules.{u} R}

/-- A section of `M` over `U` gives a global section of the restriction of `M` to `U'` along
`f : U' ⟶ U`: the value at an object `V` of the slice `Over U'` is the restriction of the
section along `V.hom ≫ f`. -/
public def overSectionsAlong (f : U' ⟶ U) (a : M.val.obj (op U)) : (M.over U').sections :=
  PresheafOfModules.sectionsMk
    (fun V : (Over U')ᵒᵖ => M.val.map (V.unop.hom ≫ f).op a)
    (fun V V' g => by
      change M.val.map g.unop.left.op (M.val.map (V.unop.hom ≫ f).op a) = _
      rw [← M.val.map_comp_apply]
      exact M.val.congr_map_apply
        (by rw [← op_comp, ← Category.assoc, Over.w g.unop]) a)

/-- The restriction of the unit sheaf of modules to a slice is the unit sheaf of modules over
the restricted sheaf of rings.

The two are definitionally equal; this isomorphism exists so that the two spellings can be
converted into one another inside proofs, where unfolding the definitions of
`SheafOfModules.unit` and `SheafOfModules.overFunctor` is not available. -/
public def overUnitIso (R : Sheaf J RingCat.{u}) (U : C) :
    (unit R).over U ≅ unit (R.over U) :=
  Iso.refl _

/-- The section over `U` classified by a morphism out of the restriction to `U` of the unit
sheaf of modules, namely its value at the terminal object `Over.mk (𝟙 U)` of the slice. -/
public def unitSection (γ : (unit R).over U ⟶ N.over U) : N.val.obj (op U) :=
  ((N.over U).unitHomEquiv ((overUnitIso R U).inv ≫ γ)).val (op (Over.mk (𝟙 U)))

/-- The morphism out of the restriction to `U'` of the unit sheaf of modules classified by the
restriction along `f : U' ⟶ U` of a section of `M` over `U`. -/
public def overUnitHom (f : U' ⟶ U) (a : M.val.obj (op U)) : (unit R).over U' ⟶ M.over U' :=
  (overUnitIso R U').hom ≫ (M.over U').unitHomEquiv.symm (overSectionsAlong f a)

/-- The value, at an object `V` of the slice `Over U'`, of the section classified by the
restriction along `f : U' ⟶ U` of `γ : (unit R).over U ⟶ N.over U`: it is the value of the
section classified by `γ` at `Over.mk (V.hom ≫ f)`. -/
public theorem unitHomEquiv_overRestrict_val (f : U' ⟶ U)
    (γ : (unit R).over U ⟶ N.over U) (V : (Over U')ᵒᵖ) :
    ((N.over U').unitHomEquiv ((overUnitIso R U').inv ≫ overRestrict f γ)).val V =
      ((N.over U).unitHomEquiv ((overUnitIso R U).inv ≫ γ)).val
        (op (Over.mk (V.unop.hom ≫ f))) :=
  rfl

/-- A section classified by a morphism out of the restriction of the unit sheaf of modules is,
at the index `Over.mk h`, the restriction along `h` of the section over `U`. -/
public theorem unitHomEquiv_val_over_mk {V : C} (γ : (unit R).over U ⟶ N.over U) (h : V ⟶ U) :
    ((N.over U).unitHomEquiv ((overUnitIso R U).inv ≫ γ)).val (op (Over.mk h)) =
      N.val.map h.op (unitSection γ) :=
  (((N.over U).unitHomEquiv ((overUnitIso R U).inv ≫ γ)).property
    (Over.homMk h (by simp) : Over.mk h ⟶ Over.mk (𝟙 U)).op).symm

/-- Restricting a morphism out of the restriction of the unit sheaf of modules is classified by
the restriction of the section that classifies it. -/
public theorem overRestrict_eq_overUnitHom (f : U' ⟶ U) (γ : (unit R).over U ⟶ N.over U) :
    overRestrict f γ = overUnitHom f (unitSection γ) := by
  rw [overUnitHom, ← Iso.inv_comp_eq]
  refine (N.over U').unitHomEquiv.injective
    (PresheafOfModules.sections_ext _ _ fun V₀ => ?_)
  rw [Equiv.apply_symm_apply, unitHomEquiv_overRestrict_val, unitHomEquiv_val_over_mk]
  rfl

/-- Let `p : M ⟶ N` be a morphism of sheaves of modules, let `s` be a section of `N` over `U`,
and let `a` be a section of `M` over `V` whose image under `p` is the restriction of `s` along
`f₂ : V ⟶ U`. Then, over any `f₁ : U' ⟶ V`, the morphism out of the unit object classified by
the restriction of `a` is a lift through `p` of the morphism classified by `s`. -/
public theorem overUnitHom_comp (p : M ⟶ N) {V : C} (f₁ : U' ⟶ V) (f₂ : V ⟶ U)
    (a : M.val.obj (op V)) (s : N.val.obj (op U))
    (hag : p.val.app (op V) a = N.val.map f₂.op s) :
    overUnitHom f₁ a ≫ (overFunctor R U').map p = overUnitHom (f₁ ≫ f₂) s := by
  rw [overUnitHom, overUnitHom, Category.assoc, ← Iso.eq_inv_comp, Iso.inv_hom_id_assoc]
  refine (N.over U').unitHomEquiv.injective
    (PresheafOfModules.sections_ext _ _ fun V₀ => ?_)
  rw [unitHomEquiv_comp_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  show p.val.app (op V₀.unop.left) (M.val.map (V₀.unop.hom ≫ f₁).op a) = _
  rw [PresheafOfModules.naturality_apply, hag, ← N.val.map_comp_apply, ← op_comp]
  exact N.val.congr_map_apply (by rw [Category.assoc]) _

end Sections

end SheafOfModules

end
