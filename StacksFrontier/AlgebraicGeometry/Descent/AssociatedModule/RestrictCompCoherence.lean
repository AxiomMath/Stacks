module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.ComparisonCoherence

/-!
# The functoriality of restriction to an object, computed

`AlgebraicGeometry.BigFppfOver.objRestrictComp` compares the two ways of restricting a module on
the big fppf site of `S` to the big fppf site of the scheme of `T'`, for `g : T' ⟶ T`: in two
steps through the site of the scheme of `T`, or in one step.  It is the third factor of the
comparison isomorphism of Stacks 03DV along a morphism of the big fppf site,
`AlgebraicGeometry.BigFppfOver.localAssociatedModuleComparison`, and therefore one of the two
pieces whose coherence the `CategoryTheory.Pseudofunctor.DescentData.pullHom_hom` field of a
descent datum for the transition isomorphisms of Stacks 03DX (1) needs — see the implementation
notes of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/ComparisonCoherence.lean`, which splits
that field's residue into a coherence for `objRestrictComp` and a coherence for
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso`.

**`objRestrictComp` had no usable characterisation.**  It is defined by *rewriting* the goal along
the functor equality `AlgebraicGeometry.BigFppfOver.objRestrict_eq_overMap` and then supplying
`Stacks.SheafOfModules.overMapCompIso`, so its value is a transport of that isomorphism along an
equality of functors, and nothing could be read off it: the two sides of that equality are
definitionally equal, but checking it at the concrete structure sheaf of the big fppf site
exhausts the heartbeat budget — `rfl` does not prove
`objRestrict B S hS T = SheafOfModules.overMap B.structureSheaf T.hom`, which is exactly why
`objRestrict_eq_overMap` is proved by citing a general lemma.  This file supplies the
characterisation, in the one form that needs no such check:
`AlgebraicGeometry.BigFppfOver.objRestrictComp_heq` identifies `objRestrictComp` with a composite
of restriction comparisons *up to `HEq`*, which is provable because the transport is a `cast`, and
`AlgebraicGeometry.BigFppfOver.objRestrictComp_eq` turns that into an equality of isomorphisms
conjugated by the two transports written as `CategoryTheory.eqToIso`.

Both forms speak of restriction along a *single* arrow of the big fppf site,
`SheafOfModules.overMap` of Mathlib, where the comparison isomorphisms are computable: this file
also records the sections
of `Stacks.SheafOfModules.overMapCompIso` and of the congruence isomorphism
`Stacks.SheafOfModules.overMapCongrIso` introduced here, each of which is the action of the module
on a reassociation arrow of the slice category.

## Main definitions

* `Stacks.SheafOfModules.overMapCongrIso`: restriction of sheaves of modules along two *equal*
  arrows of the site agree, by an isomorphism whose sections are computable — unlike
  `CategoryTheory.eqToIso`, which is opaque at the concrete sites of this development.

## Main results

* `Stacks.SheafOfModules.overMapCompIso_hom_app_val_app`,
  `Stacks.SheafOfModules.overMapCongrIso_hom_app_val_app`: **the sections of the two comparison
  isomorphisms of restriction** — each is the action of the module on the corresponding arrow of
  the slice category, `CategoryTheory.Over.mapComp` and `CategoryTheory.Over.mapCongr`.
* `Stacks.SheafOfModules.overMap_eqToIso`: the transport along an equality of arrows *is* the
  congruence isomorphism, which is what makes the latter usable where the former appears.
* `AlgebraicGeometry.BigFppfOver.objRestrictComp_heq` and
  `AlgebraicGeometry.BigFppfOver.objRestrictComp_eq`: **the functoriality of restriction to an
  object of the big fppf site, computed** — `objRestrictComp` is the composition comparison of
  restriction along the structure morphism of `T` and along `g`, followed by the congruence
  isomorphism of `CategoryTheory.Over.w`, transported along `objRestrict_eq_overMap`.

## Implementation notes

Nothing here carries a `stacks` attribute: Stacks 03DX (1) is still a hypothesis, and this file
proves no part of 03DV either — it computes a comparison that the source leaves implicit.

`Stacks.iso_eq_trans_of_heq` is the only way the `HEq` characterisation can be converted into an
equality: the two sides live in types that are definitionally but not cheaply equal, so an
equality of isomorphisms between them has to be stated with explicit `CategoryTheory.eqToIso`
transports, and the general lemma proves exactly that from the `HEq`, by substituting the two
equalities of objects.

The congruence isomorphism `Stacks.SheafOfModules.overMapCongrIso` duplicates, in content,
`CategoryTheory.eqToIso` applied to `congrArg`; it exists because the latter's sections cannot be
computed.  `Stacks.SheafOfModules.overMap_eqToIso` identifies the two, so no generality is lost
and the two spellings never diverge.

`Stacks.SheafOfModules.overMap_map_val_app` and `Stacks.SheafOfModules.overMap_obj_val_map` are
the two further sections computations that a whiskered comparison needs — restriction acting on a
morphism, and the restricted module acting on an arrow — and they are recorded here because they
are the remaining inputs of the pentagon described below, together with
`PresheafOfModules.map_comp_apply` and `PresheafOfModules.congr_map_apply`.

**What is still missing, and exactly where it stops.**  The coherence this file was written for —
the cocycle among `AlgebraicGeometry.BigFppfOver.objRestrictComp` at `g`, at `g₁` and at
`g ≫ g₁`, which is one of the two halves of the residue of
`CategoryTheory.Pseudofunctor.DescentData.pullHom_hom` — is not proved here.  With the
characterisation above it is no longer a statement about the big fppf site at all: it is the
pentagon for restriction along a single arrow on an arbitrary site,

    `overMapCompIso` at `(g, h)` whiskered by `f`, then `overMapCompIso` at `(f, h ≫ g)`, then
      `overMapCongrIso` of `(h ≫ g) ≫ f = h ≫ g ≫ f`
    = `overMapCompIso` at `(f, g)` whiskered by `h`, then `overMapCompIso` at `(g ≫ f, h)`,

together with the congruence isomorphisms of the instances of `CategoryTheory.Over.w` that pin
the three composites in the site, and the transport of that pentagon along
`objRestrict_eq_overMap` by the method of `Stacks.iso_eq_trans_of_heq`.

The pentagon's content is only that every isomorphism in it is the module's action on an arrow of
the slice category whose underlying map is the identity, which is what the four `rfl` lemmas of
the first section say; one congruence isomorphism is unavoidable there, because the two routes
end at restriction along `(h ≫ g) ≫ f` and along `h ≫ (g ≫ f)`, and no substitution removes the
associativity of the site.  Reducing both sides of the pentagon to that form is blocked at one
step: rewriting the right-hand route's outer factor
`overMapCompIso` at `(g ≫ f, h)` requires identifying the ring of sections of the structure
sheaf in its two spellings — `R.over V` at the object `(Over.map h).obj A` and `R.over W` at the
object `A` — and that identification, which is definitional, does not fit in the heartbeat
budget, which this round may not raise.  Every other step of the reduction goes through.

## References

* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace Stacks

/-- **An isomorphism is determined, up to the two transports, by any isomorphism it is `HEq`
to.**  If `A = A'` and `X = X'` are equalities of objects and `i : A ≅ X` is heterogeneously
equal to `j : A' ≅ X'`, then `i` is `j` conjugated by the two transports.  This is how a
construction whose value is a `cast` — the shape produced by `rw` on an equality of functors —
is identified with the isomorphism that was cast. -/
public theorem iso_eq_trans_of_heq {𝒞 : Type*} [Category 𝒞] {A A' X X' : 𝒞}
    (hA : A = A') (hX : X = X') (i : A ≅ X) (j : A' ≅ X') (h : HEq i j) :
    i = eqToIso hA ≪≫ j ≪≫ eqToIso hX.symm := by
  subst hA hX
  rw [eq_of_heq h]
  simp

end Stacks

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
variable {U V W : C}

/-! ### Restriction along equal arrows -/

/-- **The comparison of structure sheaves is compatible with a congruence of arrows.**  For
`a = b` arrows `X ⟶ U` of the site, the identification of the pushforward of `R.over U` along
`Over.map a` with `R.over X` followed by the transport along `CategoryTheory.Over.mapCongr` is
the identification for `b`.  Both are the identity on sections; this is the hypothesis that
`SheafOfModules.pushforwardCongr₂` needs in order to compare the two restrictions. -/
public theorem pushforwardOverMapIso_inv_comp_mapCongr {a b : W ⟶ U} (e : a = b) :
    (Sheaf.pushforwardOverMapIso R a).inv ≫
        (Functor.sheafPushforwardContinuousNatTrans (Over.mapCongr b a e.symm).hom RingCat.{w}
          (J.over W) (J.over U)).app (R.over U) =
      (Sheaf.pushforwardOverMapIso R b).inv := by
  subst e
  ext A : 3
  simp
  rfl

/-- **Restriction of sheaves of modules along equal arrows agrees.**  For `a = b` arrows
`W ⟶ U` of the site the two restriction functors are isomorphic, by the transport of
`CategoryTheory.Over.mapCongr` through `SheafOfModules.pushforwardCongr₂`.

This is `CategoryTheory.eqToIso` of the corresponding congruence of functors — see
`Stacks.SheafOfModules.overMap_eqToIso` — but, unlike it, its sections are the action of the
module on an arrow of the slice category and can be computed. -/
public noncomputable def overMapCongrIso {a b : W ⟶ U} (e : a = b) :
    SheafOfModules.overMap.{w} R a ≅ SheafOfModules.overMap.{w} R b :=
  SheafOfModules.pushforwardCongr₂ (ψ := (Sheaf.pushforwardOverMapIso R b).inv)
    (Sheaf.pushforwardOverMapIso R a).inv (Over.mapCongr b a e.symm)
    (pushforwardOverMapIso_inv_comp_mapCongr R e)

/-- **The sections of the congruence isomorphism of restriction**: the module's action on the
arrow `CategoryTheory.Over.mapCongr` of the slice category, whose underlying map is the
identity. -/
@[simp] public theorem overMapCongrIso_hom_app_val_app {a b : W ⟶ U} (e : a = b)
    (M : SheafOfModules.{w} (R.over U)) (A : (Over W)ᵒᵖ) (x) :
    (ModuleCat.Hom.hom (((overMapCongrIso R e).hom.app M).val.app A)) x =
      (ModuleCat.Hom.hom (M.val.map ((Over.mapCongr b a e.symm).hom.app A.unop).op)) x := rfl

/-- **The transport of restriction along an equality of arrows is the congruence
isomorphism.**  The left-hand side is what `rw` on such an equality produces; the right-hand
side is the isomorphism whose sections `Stacks.SheafOfModules.overMapCongrIso_hom_app_val_app`
computes. -/
public theorem overMap_eqToIso {a b : W ⟶ U} (e : a = b) :
    eqToIso (congrArg (fun k : W ⟶ U => SheafOfModules.overMap.{w} R k) e) =
      overMapCongrIso R e := by
  subst e
  ext M A : 5
  refine ConcreteCategory.ext_apply fun x => ?_
  simp
  rfl

/-! ### The sections of the composition comparison -/

/-- **The sections of the composition comparison of restriction**: the module's action on the
arrow `CategoryTheory.Over.mapComp` of the slice category, whose underlying map is the identity.
Restricting along `f : V ⟶ U` and then along `g : W ⟶ V` reads a section over `A` as the section
over `A ⟶ W ⟶ V ⟶ U` taken with the two composites bracketed the other way. -/
@[simp] public theorem overMapCompIso_hom_app_val_app (f : V ⟶ U) (g : W ⟶ V)
    (M : SheafOfModules.{w} (R.over U)) (A : (Over W)ᵒᵖ) (x) :
    (ModuleCat.Hom.hom (((overMapCompIso R f g).hom.app M).val.app A)) x =
      (ModuleCat.Hom.hom (M.val.map ((Over.mapComp g f).hom.app A.unop).op)) x := rfl

/-- **Restriction acts on a morphism of sheaves of modules by reindexing its components**: the
component of `g^*φ` over `A` is the component of `φ` over the image of `A`. -/
@[simp] public theorem overMap_map_val_app (g : W ⟶ V)
    {M N : SheafOfModules.{w} (R.over V)} (φ : M ⟶ N) (A : (Over W)ᵒᵖ) (x) :
    (ModuleCat.Hom.hom (((SheafOfModules.overMap.{w} R g).map φ).val.app A)) x =
      (ModuleCat.Hom.hom (φ.val.app (Opposite.op ((Over.map g).obj A.unop)))) x := rfl

/-- **The restriction of a sheaf of modules restricts along the image arrow**: the action of
`f^*M` on an arrow of the slice over `V` is the action of `M` on its image in the slice over
`U`. -/
@[simp] public theorem overMap_obj_val_map (f : V ⟶ U) (M : SheafOfModules.{w} (R.over U))
    {A A' : (Over V)ᵒᵖ} (m : A ⟶ A') (x) :
    (ModuleCat.Hom.hom ((((SheafOfModules.overMap.{w} R f).obj M).val.map m)) ) x =
      (ModuleCat.Hom.hom (M.val.map ((Over.map f).map m.unop).op)) x := rfl

end Stacks.SheafOfModules

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The functoriality of restriction to an object, computed -/

/-- **Restricting to the site of the scheme of `T` and then to that of the scheme of `T'` is
restricting along the structure morphism of `T` and then along `g`.**  This is
`AlgebraicGeometry.BigFppfOver.objRestrict_eq_overMap` at the two objects involved; it is the
equality of functors that `AlgebraicGeometry.BigFppfOver.objRestrictComp` is a transport
along. -/
public theorem objRestrict_comp_eq_overMap_comp {T T' : BigFppfOver B S hS} (g : T' ⟶ T) :
    objRestrict B S hS T ⋙
        objRestrict B (objScheme B S hS T) (contains_objScheme B S hS T) (Over.mk g.left) =
      SheafOfModules.overMap.{u} B.structureSheaf T.hom ⋙
        SheafOfModules.overMap.{u} B.structureSheaf g.left := by
  rw [objRestrict_eq_overMap, objRestrict_eq_overMap]
  rfl

/-- **The functoriality of restriction to an object of the big fppf site, up to `HEq`.**
`AlgebraicGeometry.BigFppfOver.objRestrictComp` at `g : T' ⟶ T` is the composition comparison of
restriction along the structure morphism of `T` and along `g`, followed by the congruence
isomorphism of `CategoryTheory.Over.w` for `g` — heterogeneously, because the source and target
are written in the two spellings of restriction.

This is the characterisation the definition does not have: it is built by rewriting along an
equality of functors, so its value is a `cast`, and `HEq` is what a `cast` can be stripped
from. -/
public theorem objRestrictComp_heq {T T' : BigFppfOver B S hS} (g : T' ⟶ T) :
    HEq (objRestrictComp B S hS g)
      (Stacks.SheafOfModules.overMapCompIso.{u} B.structureSheaf T.hom g.left ≪≫
        Stacks.SheafOfModules.overMapCongrIso B.structureSheaf (Over.w g)) := by
  rw [← Stacks.SheafOfModules.overMap_eqToIso]
  unfold objRestrictComp
  simp only [eq_mpr_eq_cast, cast_cast]
  exact cast_heq _ _

/-- **The functoriality of restriction to an object of the big fppf site, computed.**  For
`g : T' ⟶ T` the isomorphism `AlgebraicGeometry.BigFppfOver.objRestrictComp` is, after the two
transports between the two spellings of restriction, the composition comparison
`Stacks.SheafOfModules.overMapCompIso` of restriction along the structure morphism of `T` and
along `g`, followed by the congruence isomorphism of `CategoryTheory.Over.w` for `g`, which
identifies `g.left ≫ T.hom` with the structure morphism of `T'`.

The sections of the two factors on the right are computed by
`Stacks.SheafOfModules.overMapCompIso_hom_app_val_app` and
`Stacks.SheafOfModules.overMapCongrIso_hom_app_val_app`, so this is a complete description of
`objRestrictComp`. -/
public theorem objRestrictComp_eq {T T' : BigFppfOver B S hS} (g : T' ⟶ T) :
    objRestrictComp B S hS g =
      eqToIso (objRestrict_comp_eq_overMap_comp B S hS g) ≪≫
        (Stacks.SheafOfModules.overMapCompIso.{u} B.structureSheaf T.hom g.left ≪≫
            Stacks.SheafOfModules.overMapCongrIso B.structureSheaf (Over.w g)) ≪≫
          eqToIso (objRestrict_eq_overMap B S hS T').symm :=
  Stacks.iso_eq_trans_of_heq (objRestrict_comp_eq_overMap_comp B S hS g)
    (objRestrict_eq_overMap B S hS T') _ _ (objRestrictComp_heq B S hS g)

end AlgebraicGeometry.BigFppfOver

end
