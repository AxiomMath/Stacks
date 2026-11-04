module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Transporting short exactness along isomorphisms of the objects

`CategoryTheory.ShortComplex.shortExact_of_iso` moves short exactness along an isomorphism of
short complexes. In practice one has a short exact sequence `0 ⟶ A ⟶ B ⟶ E ⟶ 0` and wants the
sequence obtained by replacing `B` and `E` by isomorphic objects, the maps being the evident
composites — and then the isomorphism of short complexes has to be assembled by hand each time,
with its two commuting squares. This file does that once.

## Main results

* `Stacks.ShortComplex.shortExact_of_iso₂₃`: short exactness transported along isomorphisms
  `β : B ≅ B'` and `γ : E ≅ E'` of the second and third objects. The new maps are arguments
  rather than the composites `f ≫ β.hom` and `β.inv ≫ g ≫ γ.hom`, with the two commuting
  squares as hypotheses, so that a caller whose maps are built differently does not have to
  rewrite them into that shape first.
* `Stacks.ShortComplex.shortExact_transport₂₃`: the same with the new first map taken to be
  `f ≫ β.hom` and the vanishing of the new composite supplied, so that the one commuting square
  identifying the new third map is all the caller owes.
* `Stacks.ShortComplex.shortExact_comp_iso`: the special case where only the third object moves,
  packaged with the vanishing of the new composite.

Everything is stated in an abstract category with zero morphisms. That is the point: in the
sheaf-of-modules applications the objects carry several definitionally equal spellings of the
sheaf of rings indexing them, and assembling the isomorphism of short complexes in place runs
into those spellings, while the general lemma applies to whatever the caller's terms elaborate
to.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.ShortComplex

/-- **Short exactness transported along isomorphisms of the second and third objects.** If
`0 ⟶ A ⟶ B ⟶ E ⟶ 0` is short exact, `β : B ≅ B'` and `γ : E ≅ E'`, and `f' : A ⟶ B'`,
`g' : B' ⟶ E'` make the two evident squares commute, then `0 ⟶ A ⟶ B' ⟶ E' ⟶ 0` is short
exact. -/
theorem shortExact_of_iso₂₃ {C : Type*} [Category* C] [HasZeroMorphisms C]
    {A B B' E E' : C} {f : A ⟶ B} {g : B ⟶ E} {h : f ≫ g = 0}
    (hse : (CategoryTheory.ShortComplex.mk f g h).ShortExact)
    (β : B ≅ B') (γ : E ≅ E') {f' : A ⟶ B'} {g' : B' ⟶ E'}
    (hf : f ≫ β.hom = f') (hg : β.hom ≫ g' = g ≫ γ.hom) (h' : f' ≫ g' = 0) :
    (CategoryTheory.ShortComplex.mk f' g' h').ShortExact :=
  CategoryTheory.ShortComplex.shortExact_of_iso
    (S₁ := CategoryTheory.ShortComplex.mk f g h)
    (CategoryTheory.ShortComplex.isoMk (Iso.refl _) β γ
      ((Category.id_comp f').trans hf.symm) hg) hse

/-- **Short exactness transported along isomorphisms of the second and third objects**, with the
vanishing of the new composite supplied rather than assumed, and the new first map taken to be
`f ≫ β.hom`. The only input beyond the two isomorphisms is the commuting square
`β.hom ≫ g' = g ≫ γ.hom` identifying the new third map. -/
theorem shortExact_transport₂₃ {C : Type*} [Category* C] [HasZeroMorphisms C]
    {A B B' E E' : C} {f : A ⟶ B} {g : B ⟶ E} {h : f ≫ g = 0}
    (hse : (CategoryTheory.ShortComplex.mk f g h).ShortExact)
    (β : B ≅ B') (γ : E ≅ E') {g' : B' ⟶ E'} (hg : β.hom ≫ g' = g ≫ γ.hom) :
    ∃ h' : (f ≫ β.hom) ≫ g' = 0,
      (CategoryTheory.ShortComplex.mk (f ≫ β.hom) g' h').ShortExact :=
  ⟨by rw [Category.assoc, hg, ← Category.assoc, h, zero_comp],
    shortExact_of_iso₂₃ hse β γ rfl hg _⟩

/-- **Replacing the last object of a short exact sequence by an isomorphic one.** If
`0 ⟶ A ⟶ B ⟶ E ⟶ 0` is short exact and `γ : E ≅ E'`, then `0 ⟶ A ⟶ B ⟶ E' ⟶ 0` is short exact
with the last map postcomposed with `γ`. -/
theorem shortExact_comp_iso {C : Type*} [Category* C] [HasZeroMorphisms C]
    {A B E E' : C} (f : A ⟶ B) (g : B ⟶ E) (h : f ≫ g = 0)
    (hse : (CategoryTheory.ShortComplex.mk f g h).ShortExact) (γ : E ≅ E') :
    ∃ h' : f ≫ g ≫ γ.hom = 0, (CategoryTheory.ShortComplex.mk f (g ≫ γ.hom) h').ShortExact :=
  ⟨(Category.assoc _ _ _).symm.trans (by rw [h, zero_comp]),
    shortExact_of_iso₂₃ hse (Iso.refl _) γ (Category.comp_id _) (Category.id_comp _) _⟩

end Stacks.ShortComplex

end
