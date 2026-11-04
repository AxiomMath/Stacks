module

public import Mathlib.Algebra.Homology.Bifunctor
import StacksCore.Tactic.StacksAttribute

/-!
# Functoriality of the total complex of a bifunctor, and transport along an isomorphism

Let `F, G : C₁ ⥤ C₂ ⥤ D` be bifunctors and `β : F ≅ G` an isomorphism between them. Then for
cochain complexes `K₁` and `K₂` the bicomplexes `(i₁, i₂) ↦ (F.obj (K₁.X i₁)).obj (K₂.X i₂)`
and `(i₁, i₂) ↦ (G.obj (K₁.X i₁)).obj (K₂.X i₂)` are isomorphic, componentwise by `β`, and so
therefore are their total complexes. Mathlib has the corresponding transports along a shift
(`Mathlib.Algebra.Homology.BifunctorShift`) and along the flip of a bifunctor
(`Mathlib.Algebra.Homology.BifunctorFlip`), but not along an isomorphism of the bifunctor
itself; this file supplies it.

Also collected here is the functoriality of `HomologicalComplex.mapBifunctorMap` in the pair
of morphisms: Mathlib defines that morphism but records neither that it is the identity on a
pair of identities nor that it respects composition, both of which a construction building a
bifunctor out of it needs.

## Main definitions

* `HomologicalComplex.mapBifunctorHomologicalComplexNatIso`: the isomorphism of bicomplexes.
* `HomologicalComplex.mapBifunctorNatIso`: the induced isomorphism of total complexes.

## Main results

* `HomologicalComplex.hasMapBifunctor_of_natIso`: the total complex of one bifunctor exists as
  soon as that of an isomorphic one does.
* `HomologicalComplex.mapBifunctorMap_id` and `HomologicalComplex.mapBifunctorMap_comp`: the
  functoriality of `mapBifunctorMap` in the pair of morphisms.
* `HomologicalComplex.mapBifunctorMap_eq_map₂_comp`: `mapBifunctorMap` is the composite of the
  two one-variable images under `Functor.map₂HomologicalComplex`.

## Implementation notes

The isomorphism of bicomplexes is assembled from its components with
`HomologicalComplex.Hom.isoOfComponents`, twice: the commutation with the differential in the
second variable is the naturality of `β.hom.app (K₁.X i₁)`, and the commutation with the
differential in the first variable is the naturality of `β.hom` itself, evaluated at
`K₂.X i₂`. The passage to total complexes is then Mathlib's
`HomologicalComplex₂.total.mapIso`, and the existence transfer is
`HomologicalComplex₂.hasTotal_of_iso`, exactly as in `BifunctorShift`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {C₁ C₂ D I₁ I₂ J : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂)
  {F G : C₁ ⥤ C₂ ⥤ D}
  [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  [G.PreservesZeroMorphisms] [∀ X₁, (G.obj X₁).PreservesZeroMorphisms]

/-- An isomorphism `β : F ≅ G` of bifunctors induces an isomorphism of the bicomplexes
that `F` and `G` build from a pair of complexes. -/
def mapBifunctorHomologicalComplexNatIso (β : F ≅ G) :
    ((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂ ≅
      ((G.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂ :=
  Hom.isoOfComponents
    (fun i₁ ↦ Hom.isoOfComponents
      (fun i₂ ↦ (β.app (K₁.X i₁)).app (K₂.X i₂))
      (fun i₂ i₂' _ ↦ ((β.hom.app (K₁.X i₁)).naturality (K₂.d i₂ i₂')).symm))
    (fun i₁ i₁' _ ↦ by
      ext i₂
      exact (NatTrans.congr_app (β.hom.naturality (K₁.d i₁ i₁')) (K₂.X i₂)).symm)

/-- The components of `mapBifunctorHomologicalComplexNatIso` are the components of `β`. -/
@[simp]
lemma mapBifunctorHomologicalComplexNatIso_hom_f_f (β : F ≅ G) (i₁ : I₁) (i₂ : I₂) :
    ((mapBifunctorHomologicalComplexNatIso K₁ K₂ β).hom.f i₁).f i₂ =
      (β.hom.app (K₁.X i₁)).app (K₂.X i₂) :=
  rfl

variable (c : ComplexShape J) [TotalComplexShape c₁ c₂ c]

include K₁ K₂ in
/-- If the total complex of the bicomplex built by `F` exists, so does the one built by any
isomorphic bifunctor `G`. -/
lemma hasMapBifunctor_of_natIso (β : F ≅ G) [HasMapBifunctor K₁ K₂ F c] :
    HasMapBifunctor K₁ K₂ G c :=
  HomologicalComplex₂.hasTotal_of_iso (mapBifunctorHomologicalComplexNatIso K₁ K₂ β) c

variable [DecidableEq J] [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor K₁ K₂ G c]

/-- An isomorphism `β : F ≅ G` of bifunctors induces an isomorphism of the total complexes
`Tot(F(K₁, K₂)) ≅ Tot(G(K₁, K₂))`. -/
def mapBifunctorNatIso (β : F ≅ G) :
    mapBifunctor K₁ K₂ F c ≅ mapBifunctor K₁ K₂ G c :=
  HomologicalComplex₂.total.mapIso (mapBifunctorHomologicalComplexNatIso K₁ K₂ β) c

/-- `mapBifunctorNatIso` acts on the summand of bidegree `(i₁, i₂)` by the component of `β`
at that bidegree. -/
@[reassoc (attr := simp)]
lemma ι_mapBifunctorNatIso_hom (β : F ≅ G) (i₁ : I₁) (i₂ : I₂) (j : J)
    (h : ComplexShape.π c₁ c₂ c (i₁, i₂) = j) :
    ιMapBifunctor K₁ K₂ F c i₁ i₂ j h ≫ (mapBifunctorNatIso K₁ K₂ c β).hom.f j =
      (β.hom.app (K₁.X i₁)).app (K₂.X i₂) ≫ ιMapBifunctor K₁ K₂ G c i₁ i₂ j h :=
  HomologicalComplex₂.ιTotal_map _ _ (mapBifunctorHomologicalComplexNatIso K₁ K₂ β).hom c i₁ i₂ j h

/-- **`mapBifunctorNatIso` is natural in both complexes.** On the summand of bidegree
`(i₁, i₂)` both sides are the component of `β` there, composed with the maps induced by `f` and
`g`, in the two orders; they agree because `β` is a natural transformation of bifunctors, which
is naturality of its uncurrying at the pair `(f, g)`. -/
@[reassoc (attr := simp)]
lemma mapBifunctorNatIso_hom_naturality (β : F ≅ G)
    {L₁ : HomologicalComplex C₁ c₁} {L₂ : HomologicalComplex C₂ c₂}
    [HasMapBifunctor L₁ L₂ F c] [HasMapBifunctor L₁ L₂ G c]
    (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂) :
    mapBifunctorMap f g F c ≫ (mapBifunctorNatIso L₁ L₂ c β).hom =
      (mapBifunctorNatIso K₁ K₂ c β).hom ≫ mapBifunctorMap f g G c := by
  ext n i j hij
  simp only [HomologicalComplex.comp_f, HomologicalComplex.ι_mapBifunctorMap,
    ι_mapBifunctorNatIso_hom, reassoc_of% ι_mapBifunctorNatIso_hom,
    HomologicalComplex.ι_mapBifunctorMap_assoc]
  have h := (Functor.uncurry.map β.hom).naturality
    (show ((K₁.X i, K₂.X j) : C₁ × C₂) ⟶ (L₁.X i, L₂.X j) from (f.f i, g.f j))
  simpa only [Functor.uncurry_obj_map, Functor.uncurry_map_app, Category.assoc] using
    congrArg (· ≫ ιMapBifunctor L₁ L₂ G c i j n hij) h

end HomologicalComplex

namespace HomologicalComplex

variable {C₁ C₂ D I₁ I₂ J : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  {K₁ L₁ M₁ : HomologicalComplex C₁ c₁} {K₂ L₂ M₂ : HomologicalComplex C₂ c₂}
  (F : C₁ ⥤ C₂ ⥤ D)
  [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c] [DecidableEq J]

/-- `mapBifunctorMap` of a pair of identities is the identity. -/
@[simp]
lemma mapBifunctorMap_id [HasMapBifunctor K₁ K₂ F c] :
    mapBifunctorMap (𝟙 K₁) (𝟙 K₂) F c = 𝟙 _ := by
  ext
  simp

/-- `mapBifunctorMap` respects composition in both variables at once. -/
@[reassoc (attr := simp)]
lemma mapBifunctorMap_comp [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c]
    [HasMapBifunctor M₁ M₂ F c]
    (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (g₁ : L₁ ⟶ M₁) (g₂ : L₂ ⟶ M₂) :
    mapBifunctorMap f₁ f₂ F c ≫ mapBifunctorMap g₁ g₂ F c =
      mapBifunctorMap (f₁ ≫ g₁) (f₂ ≫ g₂) F c := by
  ext
  simp

/-- `mapBifunctorMap f₁ f₂` is the composite of the two one-variable images of `f₁` and `f₂`
under the induced bifunctor on homological complexes. -/
lemma mapBifunctorMap_eq_map₂_comp [∀ (A : HomologicalComplex C₁ c₁)
      (B : HomologicalComplex C₂ c₂), HasMapBifunctor A B F c]
    (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) :
    ((F.map₂HomologicalComplex c₁ c₂ c).map f₁).app K₂ ≫
        ((F.map₂HomologicalComplex c₁ c₂ c).obj L₁).map f₂ =
      mapBifunctorMap f₁ f₂ F c := by
  have h := mapBifunctorMap_comp F c f₁ (𝟙 K₂) (𝟙 L₁) f₂
  rw [Category.comp_id, Category.id_comp] at h
  rw [Functor.map₂HomologicalComplex_map_app, Functor.map₂HomologicalComplex_obj_map]
  exact h

end HomologicalComplex

end
