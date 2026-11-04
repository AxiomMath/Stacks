module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OverMapPentagon

/-!
# The coherence pentagon for restriction, unconditionally

`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/OverMapPentagon.lean` proves the coherence pentagon
for restriction of sheaves of modules along arrows of a site from one hypothesis: that the two
routes of the pentagon agree after the faithful forgetful functor
`CategoryTheory.forget₂ (ModuleCat _) CategoryTheory.Ab`.  It also proves the pentagon's whole
mathematical content, `Stacks.SheafOfModules.overMapComp_pentagon_presheaf`.  What separated the
two was not a missing fact but an identification of ambient objects: the two composites of the
pentagon live over the objects
`(forget₂ (ModuleCat _) Ab).obj (((overMap R f ⋙ overMap R g ⋙ overMap R h).obj M).val.obj A)`
inherited from its source and target, whereas the content is stated over
`M.val.presheaf.obj (Opposite.op ((Over.map f).obj ((Over.map g).obj ((Over.map h).obj A.unop))))`.

This file performs that identification and so makes the pentagon unconditional.  It is performed
*one layer of restriction at a time*: `Stacks.SheafOfModules.forget₂_obj_val_obj` and
`Stacks.SheafOfModules.overMap_obj_val_presheaf_obj` each strip a single layer, and are each a
one-step `rfl`, so rewriting with them three times replaces the three-layer definitional
unfolding — which alone exceeds the heartbeat budget — by three cheap ones.

## Main results

* `Stacks.SheafOfModules.forget₂_obj_val_obj`,
  `Stacks.SheafOfModules.overMap_obj_val_presheaf_obj`: **one layer of restriction, on objects**
  — the underlying abelian group of the sections of a sheaf of modules is the value of its
  underlying presheaf, and the sections of the restriction `f^*M` over an object `A` of the slice
  are the sections of `M` over the image of `A`.
* `Stacks.SheafOfModules.forget₂_map_overMapCompIso_assoc`: **the two routes of the pentagon agree
  on underlying presheaves of abelian groups**, at every sheaf of modules and every object of the
  slice.  This is the hypothesis of `Stacks.SheafOfModules.overMapCompIso_assoc_of_forget₂`.
* `Stacks.SheafOfModules.overMapCompIso_assoc`: **the coherence pentagon for restriction of
  sheaves of modules along arrows of the site**, with no hypothesis.

## Implementation notes

The reduction of the pentagon to its content is the `simp only` block recorded in the
implementation notes of `OverMapPentagon.lean`: it rewrites the five comparison isomorphisms into
restriction maps of `M`'s underlying presheaf, by the four `rfl` computations proved there.  That
block rewrites the *maps*; the objects over which the two composites are taken are left in the
spelling inherited from the pentagon's source and target, and are only definitionally the objects
the content speaks of.

Closing the gap needs exactly a `dsimp only` with the two one-layer object lemmas below, together
with `CategoryTheory.Functor.comp_obj` to expose the three layers of
`overMap R f ⋙ overMap R g ⋙ overMap R h` one at a time.  Why that is enough when a single `rfl`
on the three-layer identification is not: `CategoryTheory.Sheaf.over` and
`CategoryTheory.Functor.sheafPushforwardContinuous` are reducible, so `whnf` re-unfolds them at
every occurrence and the cost of the identification grows sharply with the number of layers — it
is cheap for one layer and unaffordable for three.  Rewriting by lemmas whose statements name the
layers therefore never performs the expensive unfolding at all: each rewrite does one layer's
worth of work, and the layers are peeled rather than collapsed.

No transport along `ModuleCat.restrictScalars` is needed.  Working underneath
`forget₂ (ModuleCat _) Ab` is what removes the rings, and with the rings removed the two
spellings differ only by the layers of `CategoryTheory.Over.map`, which the object lemmas strip
directly.

Nothing here carries a `stacks` attribute: the coherence is a step that Stacks 03DX (1) leaves
implicit, and the source states no tag for it.

## References

* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory

universe w v u

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
variable {U V W X : C}

/-! ### Peeling one layer of restriction, on objects -/

/-- **The sections of a sheaf of modules, as an abelian group, are the sections of its underlying
presheaf of abelian groups.**  Applying `CategoryTheory.forget₂` to the module of sections of `M`
over `A` gives the value at `A` of `CategoryTheory.PresheafOfModules.presheaf` of `M`.

This is the object-level counterpart of the four `rfl` computations of `OverMapPentagon.lean`,
and the first of the two rewrites that identify the ambient objects of the pentagon with the
ambient objects of its content. -/
public theorem forget₂_obj_val_obj (M : SheafOfModules.{w} (R.over U)) (A : (Over U)ᵒᵖ) :
    (forget₂ (ModuleCat.{w} _) Ab).obj (M.val.obj A) = M.val.presheaf.obj A :=
  rfl

/-- **One layer of restriction, on objects.**  The abelian group of sections of the restriction
`f^*M` over an object `A` of the slice over `V` is the group of sections of `M` over the image of
`A` in the slice over `U`.

This is the object-level counterpart of `Stacks.SheafOfModules.overMap_obj_val_presheaf_map`, and
strips exactly one layer of restriction.  Stripping the pentagon's three layers by three uses of
this lemma is what makes the identification affordable; the three-layer identification taken in
one step is the same definitional equality and exceeds the heartbeat budget on its own. -/
public theorem overMap_obj_val_presheaf_obj (f : V ⟶ U) (M : SheafOfModules.{w} (R.over U))
    (A : (Over V)ᵒᵖ) :
    ((SheafOfModules.overMap.{w} R f).obj M).val.presheaf.obj A =
      M.val.presheaf.obj (Opposite.op ((Over.map f).obj A.unop)) :=
  rfl

/-! ### The pentagon -/

/-- **The two routes of the coherence pentagon agree on underlying presheaves of abelian
groups.**  For `f : V ⟶ U`, `g : W ⟶ V`, `h : X ⟶ W`, a sheaf of modules `M` over `R.over U` and
an object `A` of the slice over `X`, the component at `M` and `A` of the pentagon's one route —
comparing the inner pair `(g, h)` whiskered by `f`, then the pair `(f, h ≫ g)`, then the
congruence of `(h ≫ g) ≫ f = h ≫ g ≫ f` — becomes, after the forgetful functor to abelian
groups, the same morphism as the component of the other route, which compares the outer pair
`(f, g)` whiskered by `h` and then the pair `(g ≫ f, h)`.

Both components are, by the four computations of `OverMapPentagon.lean`, composites of
restriction maps of `M`'s underlying presheaf of abelian groups, and the resulting identity is
`Stacks.SheafOfModules.overMapComp_pentagon_presheaf`, the image under that presheaf of the arrow
identity `Stacks.overMapComp_pentagon` of the slice category.  This is the hypothesis of
`Stacks.SheafOfModules.overMapCompIso_assoc_of_forget₂`, so with it the coherence pentagon
`Stacks.SheafOfModules.overMapCompIso_assoc` is unconditional. -/
public theorem forget₂_map_overMapCompIso_assoc (f : V ⟶ U) (g : W ⟶ V) (h : X ⟶ W)
    (M : SheafOfModules.{w} (R.over U)) (A : (Over X)ᵒᵖ) :
    (forget₂ (ModuleCat.{w} _) Ab).map
        (((Functor.isoWhiskerLeft (SheafOfModules.overMap.{w} R f) (overMapCompIso R g h) ≪≫
            overMapCompIso R f (h ≫ g) ≪≫
              overMapCongrIso R (Category.assoc h g f)).hom.app M).val.app A) =
      (forget₂ (ModuleCat.{w} _) Ab).map
        ((((Functor.associator (SheafOfModules.overMap.{w} R f)
              (SheafOfModules.overMap.{w} R g) (SheafOfModules.overMap.{w} R h)).symm ≪≫
            Functor.isoWhiskerRight (overMapCompIso R f g)
                (SheafOfModules.overMap.{w} R h) ≪≫
              overMapCompIso R (g ≫ f) h).hom.app M).val.app A) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom,
    Functor.associator_inv_app, Functor.map_comp, Category.id_comp,
    forget₂_map_overMap_map_val_app, forget₂_map_overMapCompIso_hom_app_val_app,
    forget₂_map_overMapCongrIso_hom_app_val_app, overMap_obj_val_presheaf_map,
    Quiver.Hom.unop_op]
  dsimp only [forget₂_obj_val_obj, Functor.comp_obj, overMap_obj_val_presheaf_obj]
  exact overMapComp_pentagon_presheaf R f g h M A

/-- **The coherence pentagon for restriction of sheaves of modules along arrows of the site.**
For `f : V ⟶ U`, `g : W ⟶ V` and `h : X ⟶ W`, the two ways of identifying the threefold
restriction `f^* ⋙ g^* ⋙ h^*` with restriction along the composite agree: comparing the inner
pair `(g, h)` and then the pair `(f, h ≫ g)`, followed by the congruence isomorphism of the
associativity `(h ≫ g) ≫ f = h ≫ g ≫ f` of the site, is comparing the outer pair `(f, g)` and
then the pair `(g ≫ f, h)`.

The congruence isomorphism is unavoidable: the two routes end at restriction along `(h ≫ g) ≫ f`
and along `h ≫ (g ≫ f)`, and no substitution removes the associativity of the site.

This is `Stacks.SheafOfModules.overMapCompIso_assoc_of_forget₂` with its hypothesis discharged by
`Stacks.SheafOfModules.forget₂_map_overMapCompIso_assoc`.  It is the associativity coherence that
the quasi-coherent descent datum of Stacks 03DX (1) needs, and the pseudofunctor coherence for
`pullHom` and `pullModComp` is the same identity in different clothing. -/
public theorem overMapCompIso_assoc (f : V ⟶ U) (g : W ⟶ V) (h : X ⟶ W) :
    Functor.isoWhiskerLeft (SheafOfModules.overMap.{w} R f) (overMapCompIso R g h) ≪≫
        overMapCompIso R f (h ≫ g) ≪≫ overMapCongrIso R (Category.assoc h g f) =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (overMapCompIso R f g) (SheafOfModules.overMap.{w} R h) ≪≫
          overMapCompIso R (g ≫ f) h :=
  overMapCompIso_assoc_of_forget₂ R f g h (forget₂_map_overMapCompIso_assoc R f g h)

end Stacks.SheafOfModules

end
