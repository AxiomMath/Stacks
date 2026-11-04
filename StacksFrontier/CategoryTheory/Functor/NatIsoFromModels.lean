module

public import Mathlib.CategoryTheory.NatIso

/-!
# Extending a comparison on a family of models to a natural isomorphism

Let `F G : C ⥤ D` be functors and let `p : A → C` index a family of *model* objects which
meets every isomorphism class of `C`.  A family of isomorphisms `F (p a) ≅ G (p a)` that is
natural for all morphisms between models extends to a natural isomorphism `F ≅ G`: one
transports the comparison at a chosen model along a chosen isomorphism `p (r x) ≅ x`, and
naturality on models forces the result to be natural on all of `C`.

The choice `r : C → A` of a model for each object is *not* required to be functorial, which
is the point of the construction: a comparison assembled from arbitrarily chosen resolutions
or presentations is still natural, because naturality is tested only on the models.

The same construction works for a family of morphisms in place of a family of isomorphisms,
giving a natural transformation rather than a natural isomorphism.

## Main definitions

* `CategoryTheory.NatIso.ofModels`: the natural isomorphism `F ≅ G` extending a comparison
  given on a family of models.
* `CategoryTheory.NatTrans.ofModels`: the natural transformation `F ⟶ G` extending a family of
  morphisms given on a family of models.

## Main results

* `CategoryTheory.NatIso.ofModels_hom_app_models` and
  `CategoryTheory.NatTrans.ofModels_app_models`: on a model object the extension restores the
  given family, so no information is lost in extending it.
-/

@[expose] public section

namespace CategoryTheory.NatIso

variable {C D : Type*} [Category* C] [Category* D] (F G : C ⥤ D)

/-- A comparison `c` between `F` and `G` on a family of models `p : A → C`, natural for all
morphisms between models, extends to a natural isomorphism `F ≅ G`, given a choice `r` of a
model for every object and isomorphisms `e x : p (r x) ≅ x` realising it.  The choice `r`
need not be functorial. -/
def ofModels {A : Type*} (p : A → C)
    (c : ∀ a, F.obj (p a) ≅ G.obj (p a))
    (hc : ∀ a b (f : p a ⟶ p b), F.map f ≫ (c b).hom = (c a).hom ≫ G.map f)
    (r : C → A) (e : ∀ x, p (r x) ≅ x) : F ≅ G :=
  NatIso.ofComponents (fun x => (F.mapIso (e x)).symm ≪≫ c (r x) ≪≫ G.mapIso (e x))
    (by
      intro x y f
      have h := hc (r x) (r y) ((e x).hom ≫ f ≫ (e y).inv)
      simp only [Functor.map_comp, Category.assoc] at h
      dsimp
      apply (cancel_epi (F.map (e x).hom)).1
      simp only [Category.assoc, ← F.map_comp_assoc, Iso.hom_inv_id, F.map_id,
        Category.id_comp]
      have h' := congrArg (fun z => z ≫ G.map (e y).hom) h
      simp only [Functor.map_comp, Category.assoc]
      simpa only [Category.assoc, ← G.map_comp, Iso.inv_hom_id, G.map_id,
        Category.comp_id] using h')

/-- Transporting along an isomorphism `e` a morphism that is natural for `e.hom` recovers it. -/
private theorem map_inv_comp_comp_map_hom {X Y : C} (e : X ≅ Y) (u : F.obj X ⟶ G.obj X)
    (v : F.obj Y ⟶ G.obj Y) (h : F.map e.hom ≫ v = u ≫ G.map e.hom) :
    F.map e.inv ≫ u ≫ G.map e.hom = v := by
  rw [← h, ← F.map_comp_assoc, e.inv_hom_id, F.map_id, Category.id_comp]

/-- The extension of a comparison given on a family of models agrees with that comparison at
every model object. -/
lemma ofModels_hom_app_models {A : Type*} (p : A → C)
    (c : ∀ a, F.obj (p a) ≅ G.obj (p a))
    (hc : ∀ a b (f : p a ⟶ p b), F.map f ≫ (c b).hom = (c a).hom ≫ G.map f)
    (r : C → A) (e : ∀ x, p (r x) ≅ x) (a : A) :
    (ofModels F G p c hc r e).hom.app (p a) = (c a).hom := by
  exact map_inv_comp_comp_map_hom F G (e (p a)) _ _ (hc _ _ _)

end CategoryTheory.NatIso

namespace CategoryTheory.NatTrans

variable {C D : Type*} [Category* C] [Category* D] (F G : C ⥤ D)

/-- A family of morphisms `F (p a) ⟶ G (p a)` on a family of models `p : A → C`, natural for
all morphisms between models, extends to a natural transformation `F ⟶ G`, given a choice `r`
of a model for every object and isomorphisms `e x : p (r x) ≅ x` realising it.  The choice `r`
need not be functorial. -/
def ofModels {A : Type*} (p : A → C)
    (c : ∀ a, F.obj (p a) ⟶ G.obj (p a))
    (hc : ∀ a b (f : p a ⟶ p b), F.map f ≫ c b = c a ≫ G.map f)
    (r : C → A) (e : ∀ x, p (r x) ≅ x) : F ⟶ G where
  app x := F.map (e x).inv ≫ c (r x) ≫ G.map (e x).hom
  naturality := by
    intro x y f
    have h := hc (r x) (r y) ((e x).hom ≫ f ≫ (e y).inv)
    simp only [Functor.map_comp, Category.assoc] at h
    apply (cancel_epi (F.map (e x).hom)).1
    simp only [Category.assoc, ← F.map_comp_assoc, Iso.hom_inv_id, F.map_id,
      Category.id_comp]
    have h' := congrArg (fun z => z ≫ G.map (e y).hom) h
    simp only [Functor.map_comp, Category.assoc]
    simpa only [Category.assoc, ← G.map_comp, Iso.inv_hom_id, G.map_id,
      Category.comp_id] using h'

/-- The extension of a family of morphisms given on a family of models agrees with that family
at every model object. -/
lemma ofModels_app_models {A : Type*} (p : A → C)
    (c : ∀ a, F.obj (p a) ⟶ G.obj (p a))
    (hc : ∀ a b (f : p a ⟶ p b), F.map f ≫ c b = c a ≫ G.map f)
    (r : C → A) (e : ∀ x, p (r x) ≅ x) (a : A) :
    (ofModels F G p c hc r e).app (p a) = c a := by
  exact NatIso.map_inv_comp_comp_map_hom F G (e (p a)) _ _ (hc _ _ _)

end CategoryTheory.NatTrans

end
