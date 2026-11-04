module

public import Mathlib.CategoryTheory.MorphismProperty.Representable

/-!
# Chosen base changes of a relatively representable morphism along a composite

Let `F : C ⥤ D` be a fully faithful functor and let `f : X ⟶ Y`, `g : Y ⟶ Z` be morphisms of
`D` which are relatively representable along `F`, together with a relatively representable
`fg : X ⟶ Z` and an identification `w : f ≫ g = fg`.  For every `p : F.obj a ⟶ Z` the two
objects

`hf.pullback (hg.fst p)` and `hfg.pullback p`

of `C` both represent the fibre product of `p` and `fg`, the first by pasting the two chosen
cartesian squares.  This file builds the canonical isomorphism between them and records its
compatibility with the two projections, in both directions.

Everything here is formal: the only inputs are the universal property of a chosen base change
(`CategoryTheory.Functor.relativelyRepresentable.lift`, with `…lift_fst` and `…lift_snd`) and
the extensionality principle `CategoryTheory.Functor.relativelyRepresentable.hom_ext`.  No
limits in `C` are assumed, and no choice of fibre product in `C` is used: the comparison is
built from the two chosen squares alone.

## Main definitions

* `CategoryTheory.Functor.relativelyRepresentable.pullbackCompIso`: the comparison
  isomorphism `hf.pullback (hg.fst p) ≅ hfg.pullback p`, with `…pullbackCompHom` and
  `…pullbackCompInv` its two directions.

## Main results

* `CategoryTheory.Functor.relativelyRepresentable.map_pullbackCompHom_fst` and
  `CategoryTheory.Functor.relativelyRepresentable.pullbackCompHom_snd`: the comparison is
  compatible with the projection to `X` and with the projection to `a`, the latter being the
  composite of the two projections.  These two pin it down, by `…hom_ext`.
* `CategoryTheory.Functor.relativelyRepresentable.map_pullbackCompInv_fst` and
  `CategoryTheory.Functor.relativelyRepresentable.pullbackCompInv_snd`: the same two
  compatibilities for the inverse direction.

## Implementation notes

The composite `fg` is a *separate* morphism together with an identification `f ≫ g = fg`,
rather than literally `f ≫ g`.  A consumer whose composite is spelled differently — for
instance the underlying morphism of presheaves of a composite of morphisms of algebraic
spaces, where `(f ≫ g).hom` and `f.hom ≫ g.hom` agree only by unfolding the category
structure of a full subcategory — then supplies the identification instead of relying on that
unfolding inside a larger elaboration.

The inverse direction factors through `…pullbackCompMid`, the morphism
`hfg.pullback p ⟶ hg.pullback p` induced by `hfg.fst p ≫ f`; naming it is what keeps every
step below a single application of `…lift_fst` or `…lift_snd`.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.relativelyRepresentable

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D}
  [instFull : F.Full] [instFaithful : F.Faithful] {X Y Z : D} {f : X ⟶ Y} {g : Y ⟶ Z}
  {fg : X ⟶ Z} (hf : F.relativelyRepresentable f) (hg : F.relativelyRepresentable g)
  (hfg : F.relativelyRepresentable fg) (w : f ≫ g = fg) {a : C} (p : F.obj a ⟶ Z)

include w in
omit instFull instFaithful in
/-- The pasted cartesian square: the iterated chosen base change of `f` and `g` along `p` sits
over `fg` and over `p`. -/
theorem pullbackComp_cond :
    hf.fst (hg.fst p) ≫ fg = F.map (hf.snd (hg.fst p) ≫ hg.snd p) ≫ p := by
  rw [← w, ← Category.assoc, hf.w (hg.fst p), Category.assoc, hg.w p, F.map_comp,
    Category.assoc]

/-- The comparison from the iterated chosen base change to the chosen base change along the
composite, obtained from the universal property of the latter applied to the pasted square. -/
noncomputable def pullbackCompHom : hf.pullback (hg.fst p) ⟶ hfg.pullback p :=
  hfg.lift (hf.fst (hg.fst p)) (hf.snd (hg.fst p) ≫ hg.snd p)
    (pullbackComp_cond hf hg w p)

omit instFaithful in
/-- The comparison is compatible with the projection to `X`. -/
@[reassoc]
theorem map_pullbackCompHom_fst :
    F.map (pullbackCompHom hf hg hfg w p) ≫ hfg.fst p = hf.fst (hg.fst p) :=
  hfg.lift_fst _ _ _

include instFaithful in
/-- The comparison carries the projection of the composite base change to the composite of the
two projections. -/
@[reassoc]
theorem pullbackCompHom_snd :
    pullbackCompHom hf hg hfg w p ≫ hfg.snd p = hf.snd (hg.fst p) ≫ hg.snd p :=
  hfg.lift_snd _ _ _

include w in
omit instFull instFaithful in
/-- The projection of the base change along the composite, followed by `f`, sits over `g` and
over `p`. -/
theorem pullbackComp_mid_cond :
    (hfg.fst p ≫ f) ≫ g = F.map (hfg.snd p) ≫ p := by
  rw [Category.assoc, w]
  exact hfg.w p

/-- The middle factor of the inverse comparison: the morphism from the base change along the
composite to the base change along `g`, induced by its projection to `X` followed by `f`. -/
noncomputable def pullbackCompMid : hfg.pullback p ⟶ hg.pullback p :=
  hg.lift (hfg.fst p ≫ f) (hfg.snd p) (pullbackComp_mid_cond hfg w p)

omit instFaithful in
/-- The middle factor is compatible with the projection to `Y`. -/
@[reassoc]
theorem map_pullbackCompMid_fst :
    F.map (pullbackCompMid hg hfg w p) ≫ hg.fst p = hfg.fst p ≫ f :=
  hg.lift_fst _ _ _

include instFaithful in
/-- The middle factor is compatible with the projection to `a`. -/
@[reassoc]
theorem pullbackCompMid_snd :
    pullbackCompMid hg hfg w p ≫ hg.snd p = hfg.snd p :=
  hg.lift_snd _ _ _

/-- The inverse comparison, from the chosen base change along the composite to the iterated
chosen base change. -/
noncomputable def pullbackCompInv : hfg.pullback p ⟶ hf.pullback (hg.fst p) :=
  hf.lift (hfg.fst p) (pullbackCompMid hg hfg w p)
    (map_pullbackCompMid_fst hg hfg w p).symm

omit instFaithful in
/-- The inverse comparison is compatible with the projection to `X`. -/
@[reassoc]
theorem map_pullbackCompInv_fst :
    F.map (pullbackCompInv hf hg hfg w p) ≫ hf.fst (hg.fst p) = hfg.fst p :=
  hf.lift_fst _ _ _

include instFaithful in
/-- The inverse comparison, followed by the projection of the iterated base change to the
base change along `g`, is the middle factor. -/
@[reassoc]
theorem pullbackCompInv_mid :
    pullbackCompInv hf hg hfg w p ≫ hf.snd (hg.fst p) = pullbackCompMid hg hfg w p :=
  hf.lift_snd _ _ _

include instFaithful in
/-- The inverse comparison carries the composite of the two projections to the projection of
the base change along the composite. -/
@[reassoc]
theorem pullbackCompInv_snd :
    pullbackCompInv hf hg hfg w p ≫ hf.snd (hg.fst p) ≫ hg.snd p = hfg.snd p := by
  rw [← Category.assoc, pullbackCompInv_mid hf hg hfg w p, pullbackCompMid_snd hg hfg w p]

include instFaithful in
/-- The comparison followed by the middle factor of its inverse is the projection of the
iterated base change to the base change along `g`. -/
theorem pullbackCompHom_pullbackCompMid :
    pullbackCompHom hf hg hfg w p ≫ pullbackCompMid hg hfg w p = hf.snd (hg.fst p) := by
  refine hg.hom_ext ?_ ?_
  · rw [F.map_comp, Category.assoc, map_pullbackCompMid_fst hg hfg w p, ← Category.assoc,
      map_pullbackCompHom_fst hf hg hfg w p]
    exact hf.w (hg.fst p)
  · rw [Category.assoc, pullbackCompMid_snd hg hfg w p, pullbackCompHom_snd hf hg hfg w p]

include instFaithful in
/-- The comparison and its inverse compose to the identity of the iterated base change. -/
theorem pullbackCompHom_pullbackCompInv :
    pullbackCompHom hf hg hfg w p ≫ pullbackCompInv hf hg hfg w p = 𝟙 _ := by
  refine hf.hom_ext ?_ ?_
  · simp [map_pullbackCompInv_fst, map_pullbackCompHom_fst]
  · simp [pullbackCompInv_mid, pullbackCompHom_pullbackCompMid]

include instFaithful in
/-- The inverse comparison and the comparison compose to the identity of the base change along
the composite. -/
theorem pullbackCompInv_pullbackCompHom :
    pullbackCompInv hf hg hfg w p ≫ pullbackCompHom hf hg hfg w p = 𝟙 _ := by
  refine hfg.hom_ext ?_ ?_
  · simp [map_pullbackCompHom_fst, map_pullbackCompInv_fst]
  · simp [pullbackCompHom_snd, pullbackCompInv_snd]

/-- The chosen base change along a composite agrees with the iterated chosen base change: both
are fibre products of `p` and `fg`, the first by the pasted square. -/
@[simps]
noncomputable def pullbackCompIso : hf.pullback (hg.fst p) ≅ hfg.pullback p where
  hom := pullbackCompHom hf hg hfg w p
  inv := pullbackCompInv hf hg hfg w p
  hom_inv_id := pullbackCompHom_pullbackCompInv hf hg hfg w p
  inv_hom_id := pullbackCompInv_pullbackCompHom hf hg hfg w p

/-! ### Functoriality in the chart, and naturality of the comparison -/

section Map

variable {a a' : C}

/-- The chosen base change of `f` along a morphism of charts: the morphism
`hf.pullback p ⟶ hf.pullback p'` induced by `k : a ⟶ a'` over `p = F.map k ≫ p'`. -/
noncomputable def pullbackMap (p : F.obj a ⟶ Y) (p' : F.obj a' ⟶ Y) (k : a ⟶ a')
    (hk : F.map k ≫ p' = p) : hf.pullback p ⟶ hf.pullback p' :=
  hf.lift (hf.fst p) (hf.snd p ≫ k) (by
    rw [F.map_comp, Category.assoc, hk]
    exact hf.w p)

omit instFaithful in
/-- The chosen base change of a morphism of charts is compatible with the projection to `X`. -/
@[reassoc]
theorem pullbackMap_fst (p : F.obj a ⟶ Y) (p' : F.obj a' ⟶ Y) (k : a ⟶ a')
    (hk : F.map k ≫ p' = p) :
    F.map (pullbackMap hf p p' k hk) ≫ hf.fst p' = hf.fst p :=
  hf.lift_fst _ _ _

include instFaithful in
/-- The chosen base change of a morphism of charts lies over that morphism. -/
@[reassoc]
theorem pullbackMap_snd (p : F.obj a ⟶ Y) (p' : F.obj a' ⟶ Y) (k : a ⟶ a')
    (hk : F.map k ≫ p' = p) :
    pullbackMap hf p p' k hk ≫ hf.snd p' = hf.snd p ≫ k :=
  hf.lift_snd _ _ _

include instFaithful in
/-- The comparison of the iterated chosen base change with the chosen base change along the
composite is natural in the chart. -/
theorem pullbackMap_pullbackCompHom (p : F.obj a ⟶ Z) (p' : F.obj a' ⟶ Z) (k : a ⟶ a')
    (hk : F.map k ≫ p' = p) :
    pullbackMap hf (hg.fst p) (hg.fst p') (pullbackMap hg p p' k hk)
          (pullbackMap_fst hg p p' k hk) ≫
        pullbackCompHom hf hg hfg w p' =
      pullbackCompHom hf hg hfg w p ≫ pullbackMap hfg p p' k hk := by
  refine hfg.hom_ext ?_ ?_
  · rw [F.map_comp, F.map_comp, Category.assoc, Category.assoc,
      map_pullbackCompHom_fst hf hg hfg w p',
      pullbackMap_fst hf (hg.fst p) (hg.fst p') (pullbackMap hg p p' k hk)
        (pullbackMap_fst hg p p' k hk),
      pullbackMap_fst hfg p p' k hk, map_pullbackCompHom_fst hf hg hfg w p]
  · rw [Category.assoc, Category.assoc, pullbackCompHom_snd hf hg hfg w p',
      pullbackMap_snd hfg p p' k hk, ← Category.assoc, ← Category.assoc,
      pullbackMap_snd hf (hg.fst p) (hg.fst p') (pullbackMap hg p p' k hk)
        (pullbackMap_fst hg p p' k hk),
      pullbackCompHom_snd hf hg hfg w p, Category.assoc, Category.assoc,
      pullbackMap_snd hg p p' k hk]

end Map

end CategoryTheory.Functor.relativelyRepresentable

end
