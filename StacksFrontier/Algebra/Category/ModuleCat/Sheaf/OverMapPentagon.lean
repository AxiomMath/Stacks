module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.RestrictCompCoherence

/-!
# The coherence pentagon for restriction along an arrow of a site

For a site `(C, J)` with a sheaf of rings `R`, restriction of sheaves of `R`-modules along an
arrow `f : V ⟶ U` of `C` is `SheafOfModules.overMap R f`, the pushforward along
`CategoryTheory.Over.map f`, and `Stacks.SheafOfModules.overMapCompIso` compares restriction
along `f` followed by restriction along `g : W ⟶ V` with restriction along `g ≫ f`.  That
comparison is not strictly associative: the two ways of bracketing three arrows `h : X ⟶ W`, `g`,
`f` of the site end at restriction along `(h ≫ g) ≫ f` and along `h ≫ g ≫ f`, so the coherence
statement carries one congruence isomorphism and is a *pentagon*,

    `overMapCompIso` at `(g, h)` whiskered by `f`, then `overMapCompIso` at `(f, h ≫ g)`, then
      the congruence of `(h ≫ g) ≫ f = h ≫ g ≫ f`
    = `overMapCompIso` at `(f, g)` whiskered by `h`, then `overMapCompIso` at `(g ≫ f, h)`.

This file reduces that pentagon to its mathematical content and proves the content.  The content is
`Stacks.overMapComp_pentagon`, an identity between five arrows of the slice category `Over U` each
of which is the identity on the underlying object, together with its image
`Stacks.SheafOfModules.overMapComp_pentagon_presheaf` under the module's underlying presheaf of
abelian groups; and `Stacks.SheafOfModules.overMapCompIso_assoc_of_forget₂` shows that the
pentagon follows from the agreement of the two routes after the faithful forgetful functor to
presheaves of abelian groups, which is the form in which all five comparison isomorphisms are
computable (`Stacks.SheafOfModules.forget₂_map_overMapCompIso_hom_app_val_app` and its
companions).

## Main results

* `Stacks.overMapComp_pentagon`: **the pentagon for `CategoryTheory.Over.map`** — the two
  bracketings of `CategoryTheory.Over.mapComp` for three composable arrows agree, after the
  congruence isomorphism of the associativity of the site.  Both composites are the identity on
  underlying objects, so this is an instance of `CategoryTheory.Over.hom_ext`.
* `Stacks.SheafOfModules.overMap_obj_val_presheaf_map`,
  `Stacks.SheafOfModules.forget₂_map_overMapCompIso_hom_app_val_app`,
  `Stacks.SheafOfModules.forget₂_map_overMapCongrIso_hom_app_val_app`,
  `Stacks.SheafOfModules.forget₂_map_overMap_map_val_app`: **the comparison isomorphisms of
  restriction, computed on underlying presheaves of abelian groups** — each is the action of the
  module's underlying presheaf on the corresponding arrow of the slice category.
* `Stacks.SheafOfModules.overMapComp_pentagon_presheaf`: **the pentagon, on the module's
  underlying presheaf of abelian groups** — the composite of the three restriction maps of the one
  route equals the composite of the two of the other.
* `Stacks.SheafOfModules.overMapCompIso_assoc_of_forget₂`: **the pentagon for restriction of
  sheaves of modules, from its image under the forgetful functor to presheaves of abelian
  groups**, which is faithful.

## Implementation notes

This file is general sheaf-of-modules infrastructure: it speaks only of a site, a sheaf of rings
on it, and sheaves of modules over that sheaf of rings, and mentions no scheme and no big site.
It is nonetheless placed downstream of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/RestrictCompCoherence.lean`, because that
is where `Stacks.SheafOfModules.overMapCongrIso` lives; when that is moved to this part of the
library the import should be inverted.

**Why the comparisons are computed on underlying abelian groups.**  Each of the four comparisons
above is `rfl`, and `StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/RestrictCompCoherence.lean` already records them *on individual sections*.
Those forms cannot drive the pentagon: a rewrite that puts `M.val.map` of a slice arrow next to a
section of a *threefold* restriction makes the elaborator identify the ring of sections of `R`
restricted three times with the ring of sections of `R`, and that identification — definitional,
and immediate for the kernel — exhausts the heartbeat budget by itself, because
`CategoryTheory.Sheaf.over` and `CategoryTheory.Functor.sheafPushforwardContinuous` are reducible
and are unfolded afresh at every occurrence (diagnostics: 8149 unfoldings of the latter, 334807
reducible unfoldings of `CategoryTheory.Functor.obj`, for one such step).  The ring is what is
expensive, and on underlying presheaves of abelian groups it is not mentioned: `forget₂` to
`CategoryTheory.Ab` discards the `ModuleCat.restrictScalars` transports through which the rings
enter, so each comparison becomes an equation between restriction maps of a single presheaf.  The
comparisons are stated at that level for exactly this reason, and they determine the morphisms
they compute because `forget₂` is faithful — which is what
`Stacks.SheafOfModules.overMapCompIso_assoc_of_forget₂` uses.

**The one step that is still missing, and exactly where it stops.**  The reduction of the pentagon
runs as follows, and every step of it is cheap:

    ext M A : 5
    apply (forget₂ (ModuleCat.{w} _) Ab).map_injective
    simp only [Iso.trans_hom, NatTrans.comp_app, SheafOfModules.comp_val,
      PresheafOfModules.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom,
      Functor.associator_inv_app, Functor.map_comp, Category.id_comp,
      forget₂_map_overMap_map_val_app, forget₂_map_overMapCompIso_hom_app_val_app,
      forget₂_map_overMapCongrIso_hom_app_val_app, overMap_obj_val_presheaf_map,
      Quiver.Hom.unop_op]

After it the goal *prints identically* to
`Stacks.SheafOfModules.overMapComp_pentagon_presheaf`, and it is not that statement: the ambient
objects of the two composites are inherited from the pentagon's source and target, so they are
spelled `(forget₂ (ModuleCat.{w} _) Ab).obj (((overMap R f ⋙ overMap R g ⋙ overMap R h).obj
M).val.obj A)` where the lemma spells them `M.val.presheaf.obj (Opposite.op ((Over.map f).obj
((Over.map g).obj ((Over.map h).obj A.unop))))`.  Identifying those two is definitional and is a
single `rfl` for the kernel; for the elaborator it costs more than 200000 heartbeats *on its own*,
with nothing else in the declaration.  Both routes away from it are exhausted:

* *Cheap spelling.*  The identification is cheap for one restriction and for two, and only becomes
  unaffordable at three; naming the shifted ring does not help, because the cost is not in the
  ring's name but in `CategoryTheory.Sheaf.over` being reducible, which no name in this file can
  change.  Going through sections first (`ConcreteCategory.ext_apply` and the four `_val_app` `rfl`
  lemmas of `StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/RestrictCompCoherence.lean`, in every order) reduces four of the five factors inside
  budget and leaves the fifth needing the same identification.
* *Making the fifth factor like the other four.*  The three factors that rewrite cheaply are the
  ones whose module argument is `M` itself or whose object argument is a single shift; the
  expensive one is the whiskered factor, where the module argument is `(overMap R f).obj M` and the
  object argument is a double shift.  Restating it with the module argument written out, with the
  object argument written out, at the level of sections, at the level of morphisms of `ModuleCat`,
  and at the level of abelian groups all produce the same identification; the `ModuleCat` form does
  not even typecheck, because the two sides differ by `ModuleCat.restrictScalars` along
  `R.obj.map (𝟙 _)`, which is not the identity ring map but only propositionally equal to it.

So the residue is not a missing mathematical fact — every ingredient is proved here — but a single
definitional identification that the elaborator cannot perform inside the fixed budget.  Closing
it needs either a raised budget, which this round forbids, or a Mathlib-side change making
`CategoryTheory.Sheaf.over` and `SheafOfModules.overMap` irreducible with `obj`/`map` simp lemmas,
so that the layers are peeled by rewriting rather than by `whnf`.

**Relation to the pseudofunctor coherence for `pullHom` and `pullModComp`.**  The coherence that
`CategoryTheory.Pseudofunctor.DescentData.pullHom_hom` needs for the quasi-coherent descent datum
of Stacks 03DX is the same associativity pentagon in different clothing: there the two routes are
built from `pullModComp` and compared by `pullHom`, here from `overMapCompIso` and compared by
`overMapCongrIso`.  `Stacks.overMapComp_pentagon` is the arrow identity underlying both, and is
stated for an arbitrary category so that it can serve both; the `forget₂` reduction above is what
has to be repeated on the `pullMod` side.

Nothing here carries a `stacks` attribute: the coherence is a step that Stacks 03DX (1) leaves
implicit, and the source states no tag for it.

## References

* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory

universe w v u

namespace Stacks

variable {C : Type u} [Category.{v} C] {U V W X : C}

/-- **The pentagon for `CategoryTheory.Over.map`.**  For three composable arrows `h : X ⟶ W`,
`g : W ⟶ V`, `f : V ⟶ U` of a category and an object `A` of the slice over `X`, the two ways of
comparing the triple composite `Over.map h ⋙ Over.map g ⋙ Over.map f` with `Over.map (h ≫ g ≫ f)`
agree: reassociating the inner pair and then the outer one, after the congruence isomorphism of
`(h ≫ g) ≫ f = h ≫ g ≫ f`, is reassociating the outer pair and then the inner one.

Every arrow occurring here is the identity on the underlying object of the slice, so the identity
holds by `CategoryTheory.Over.hom_ext`.  That is also why it is the whole content of the coherence
pentagon for restriction of sheaves of modules: the underlying presheaf maps of the five
comparison isomorphisms there are the module's action on these arrows — see
`Stacks.SheafOfModules.overMapComp_pentagon_presheaf`. -/
public theorem overMapComp_pentagon (f : V ⟶ U) (g : W ⟶ V) (h : X ⟶ W) (A : Over X) :
    (Over.mapCongr (h ≫ g ≫ f) ((h ≫ g) ≫ f) (Category.assoc h g f).symm).hom.app A ≫
        (Over.mapComp (h ≫ g) f).hom.app A ≫
          (Over.map f).map ((Over.mapComp h g).hom.app A) =
      (Over.mapComp h (g ≫ f)).hom.app A ≫
        (Over.mapComp g f).hom.app ((Over.map h).obj A) := by
  ext
  simp

end Stacks

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
variable {U V W X : C}

/-! ### The comparisons of restriction, on underlying presheaves of abelian groups -/

/-- **The restriction of a sheaf of modules restricts along the image arrow.**  The action of the
underlying presheaf of `f^*M` on an arrow of the slice over `V` is the action of the underlying
presheaf of `M` on its image in the slice over `U`.

This is `Stacks.SheafOfModules.overMap_obj_val_map` with the module structures forgotten; the
implementation notes explain why that is the usable form. -/
public theorem overMap_obj_val_presheaf_map (f : V ⟶ U) (M : SheafOfModules.{w} (R.over U))
    {A A' : (Over V)ᵒᵖ} (m : A ⟶ A') :
    ((SheafOfModules.overMap.{w} R f).obj M).val.presheaf.map m =
      M.val.presheaf.map ((Over.map f).map m.unop).op :=
  rfl

/-- **The composition comparison of restriction, on underlying presheaves of abelian groups**: the
module's action on the arrow `CategoryTheory.Over.mapComp` of the slice category.  Restricting
along `f : V ⟶ U` and then along `g : W ⟶ V` reads a section over `A` as the section over
`A ⟶ W ⟶ V ⟶ U` with the two composites bracketed the other way. -/
public theorem forget₂_map_overMapCompIso_hom_app_val_app (f : V ⟶ U) (g : W ⟶ V)
    (M : SheafOfModules.{w} (R.over U)) (A : (Over W)ᵒᵖ) :
    (forget₂ (ModuleCat.{w} _) Ab).map (((overMapCompIso R f g).hom.app M).val.app A) =
      M.val.presheaf.map ((Over.mapComp g f).hom.app A.unop).op :=
  rfl

/-- **The congruence comparison of restriction, on underlying presheaves of abelian groups**: the
module's action on the arrow `CategoryTheory.Over.mapCongr` of the slice category, whose
underlying map is the identity. -/
public theorem forget₂_map_overMapCongrIso_hom_app_val_app {a b : W ⟶ U} (e : a = b)
    (M : SheafOfModules.{w} (R.over U)) (A : (Over W)ᵒᵖ) :
    (forget₂ (ModuleCat.{w} _) Ab).map (((overMapCongrIso R e).hom.app M).val.app A) =
      M.val.presheaf.map ((Over.mapCongr b a e.symm).hom.app A.unop).op :=
  rfl

/-- **Restriction acts on a morphism of sheaves of modules by reindexing its components**, on
underlying presheaves of abelian groups: the component of `g^*φ` over `A` is the component of `φ`
over the image of `A`. -/
public theorem forget₂_map_overMap_map_val_app (g : W ⟶ V)
    {M N : SheafOfModules.{w} (R.over V)} (φ : M ⟶ N) (A : (Over W)ᵒᵖ) :
    (forget₂ (ModuleCat.{w} _) Ab).map (((SheafOfModules.overMap.{w} R g).map φ).val.app A) =
      (forget₂ (ModuleCat.{w} _) Ab).map
        (φ.val.app (Opposite.op ((Over.map g).obj A.unop))) :=
  rfl

/-! ### The pentagon -/

/-- **The coherence pentagon for restriction, on the module's underlying presheaf of abelian
groups.**  For `f : V ⟶ U`, `g : W ⟶ V`, `h : X ⟶ W` and an object `A` of the slice over `X`, the
composite of the three restriction maps of `M`'s underlying presheaf that the one route of the
pentagon contributes equals the composite of the two that the other contributes.

By the four computations above, these five restriction maps are exactly the underlying presheaf
maps of the five comparison isomorphisms in the pentagon, read in the order in which the pentagon
composes them; so this statement is the pentagon's whole content.  It is
`Stacks.overMapComp_pentagon` transported by `M.val.presheaf`. -/
public theorem overMapComp_pentagon_presheaf (f : V ⟶ U) (g : W ⟶ V) (h : X ⟶ W)
    (M : SheafOfModules.{w} (R.over U)) (A : (Over X)ᵒᵖ) :
    M.val.presheaf.map ((Over.map f).map ((Over.mapComp h g).hom.app A.unop)).op ≫
        M.val.presheaf.map ((Over.mapComp (h ≫ g) f).hom.app A.unop).op ≫
          M.val.presheaf.map ((Over.mapCongr (h ≫ g ≫ f) ((h ≫ g) ≫ f)
            (Category.assoc h g f).symm).hom.app A.unop).op =
      M.val.presheaf.map ((Over.mapComp g f).hom.app ((Over.map h).obj A.unop)).op ≫
        M.val.presheaf.map ((Over.mapComp h (g ≫ f)).hom.app A.unop).op := by
  have key := congrArg (fun k : (Over.map (h ≫ g ≫ f)).obj A.unop ⟶
      (Over.map f).obj ((Over.map g).obj ((Over.map h).obj A.unop)) =>
    M.val.presheaf.map (Quiver.Hom.op k)) (Stacks.overMapComp_pentagon f g h A.unop)
  simpa only [op_comp, Functor.map_comp, Category.assoc] using key

/-- **The coherence pentagon for restriction of sheaves of modules along arrows of the site,
from its image on underlying presheaves of abelian groups.**  For `f : V ⟶ U`, `g : W ⟶ V` and
`h : X ⟶ W`, the two ways of identifying the threefold restriction `f^* ⋙ g^* ⋙ h^*` with the
restriction along the composite agree — comparing the inner pair `(g, h)` and then the pair
`(f, h ≫ g)`, followed by the congruence isomorphism of the associativity
`(h ≫ g) ≫ f = h ≫ g ≫ f` of the site, is comparing the outer pair `(f, g)` and then the pair
`(g ≫ f, h)` — as soon as the two agree after the forgetful functor to abelian groups, at every
module and every object of the slice.

The congruence isomorphism is unavoidable: the two routes end at restriction along `(h ≫ g) ≫ f`
and along `h ≫ (g ≫ f)`, and no substitution removes the associativity of the site.

The hypothesis is the pentagon for the underlying presheaves of abelian groups, where the sheaves
of rings and the `ModuleCat.restrictScalars` transports through which they enter have been
discarded; the implementation notes record the reduction that brings it to
`Stacks.SheafOfModules.overMapComp_pentagon_presheaf` and the single definitional identification
of ambient objects that separates the two. -/
public theorem overMapCompIso_assoc_of_forget₂ (f : V ⟶ U) (g : W ⟶ V) (h : X ⟶ W)
    (H : ∀ (M : SheafOfModules.{w} (R.over U)) (A : (Over X)ᵒᵖ),
      (forget₂ (ModuleCat.{w} _) Ab).map
          (((Functor.isoWhiskerLeft (SheafOfModules.overMap.{w} R f) (overMapCompIso R g h) ≪≫
              overMapCompIso R f (h ≫ g) ≪≫
                overMapCongrIso R (Category.assoc h g f)).hom.app M).val.app A) =
        (forget₂ (ModuleCat.{w} _) Ab).map
          ((((Functor.associator (SheafOfModules.overMap.{w} R f)
                (SheafOfModules.overMap.{w} R g) (SheafOfModules.overMap.{w} R h)).symm ≪≫
              Functor.isoWhiskerRight (overMapCompIso R f g)
                  (SheafOfModules.overMap.{w} R h) ≪≫
                overMapCompIso R (g ≫ f) h).hom.app M).val.app A)) :
    Functor.isoWhiskerLeft (SheafOfModules.overMap.{w} R f) (overMapCompIso R g h) ≪≫
        overMapCompIso R f (h ≫ g) ≪≫ overMapCongrIso R (Category.assoc h g f) =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (overMapCompIso R f g) (SheafOfModules.overMap.{w} R h) ≪≫
          overMapCompIso R (g ≫ f) h := by
  ext M A : 5
  exact (forget₂ (ModuleCat.{w} _) Ab).map_injective (H M A)

end Stacks.SheafOfModules

end
