module

public import Mathlib.CategoryTheory.NatIso

/-!
# The unit law of a morphism of pseudofunctors, from its composition law

`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePushforwardUnitLaws.lean` proves that the
unit laws of a *pseudofunctor* carry no information beyond the associativity coherence:
`CategoryTheory.Functor.compIso_eq_isoWhiskerRight_idIsoOfCompIso` derives a unit law from the
cocycle law read at a single object.  This file is the same statement for a *morphism of
pseudofunctors*.

A morphism of pseudofunctors between two assignments of a category to each object and of a
functor to each arrow is a comparison functor at each object together with a comparison
isomorphism at each arrow, subject to a composition law.  Read at one arrow and its own composite
with itself, the data is: two endofunctors `P` and `Q` — the values of the two pseudofunctors at
that arrow — a comparison functor `F`, a family of isomorphisms
`t M : Q (F M) ≅ F (P M)`, and the composition comparisons `m : Q ⋙ Q ≅ Q` and `n : P ⋙ P ≅ P`
of the two pseudofunctors at the pair of that arrow with itself.

Suppose the arrow is an identity, so that each pseudofunctor identifies its value with the
identity functor — `u : Q ≅ 𝟭` and `w : P ≅ 𝟭` — each identification obeying its own unit law
against the composition comparison.  Then `t` is the comparison those two identifications force,
and no further datum enters: `t M` is `u` at `F M` followed by the image under `F` of the inverse
of `w` at `M`.

Nothing is computed.  The composition law, with `n` rewritten by the unit law of the second
pseudofunctor and the naturality of `t` applied to the component of `w`, says exactly that `Q`
carries `t M` followed by `F w` to the component of `m`; the unit law of the first pseudofunctor
rewrites that component as a component of `u`, and the naturality of `u` then strips the `Q`.

## Main results

* `Stacks.CategoryTheory.transportApp_of_compLaw_of_idIso`: **the unit law for a morphism of
  pseudofunctors** — a comparison obeying the composition law at an identity is the comparison
  that the two pseudofunctors' own identifications with the identity functor force.
* `Stacks.CategoryTheory.map_transportApp_of_compLaw`: its coherence-free half, asking no unit
  law of the first pseudofunctor.
* `Stacks.CategoryTheory.map_comp_eq_of_cancel` and
  `Stacks.CategoryTheory.eq_app_comp_of_map_comp_eq`: the same two halves with every functor but
  the one whose image is taken replaced by plain objects and morphisms, for use when the two
  categories are two spellings of one category (see the implementation notes).

## Implementation notes

The comparison `t` is taken as a *family* of isomorphisms together with its naturality, rather
than as an isomorphism of functors `F ⋙ Q ≅ P ⋙ F`, so that the comparison and its naturality
can be supplied as two separate statements, with no isomorphism of functors to assemble from them
and project the forward map back out of.

When the two categories are two spellings of one category — a definition and what it unfolds
to — the forms that abstract over the comparison functor do not apply in practice, even with every
functor passed by name and every composition comparison weakened to its components: matching the
two spellings is then a kernel deterministic timeout, and a `rewrite` cannot match across them at
all, since the pattern and the target differ only in the category instance that
`CategoryTheory.CategoryStruct.comp` carries.  `Stacks.CategoryTheory.map_comp_eq_of_cancel` and
`Stacks.CategoryTheory.eq_app_comp_of_map_comp_eq` are the same mathematics with the comparison
functor gone, so that a term application has nothing left to match.

The two unit-law hypotheses are taken in the two *different* shapes in which a pseudofunctor's
left and right unit laws respectively present them — `hm` with the component of `u` at `Q Z`, and
`hn` with `P` applied to the component of `w`.  Both shapes are available for a pseudofunctor that
has either unit law, since the two differ by the naturality of the identification at its own
component, but taking each in the shape its own side already has spares that conversion.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

/-- **The composition law and the naturality of a comparison, cancelled.**  The algebraic
skeleton of `Stacks.CategoryTheory.map_transportApp_of_compLaw`, with every functor but the one
whose image is taken replaced by plain objects and morphisms.

It is stated separately for the case where the two sides of the comparison live in two spellings
of one category — a definition and what it unfolds to: a `rewrite` cannot match across the
category instance those two spellings carry, while a term application of this lemma unifies up to
definitional equality. -/
theorem map_comp_eq_of_cancel {C : Type u₁} [Category* C] (Q : C ⥤ C) {X Y Y' : C}
    (a : Q.obj X ≅ Y) (e : Y ⟶ X) (b : Q.obj Y ⟶ Y') (c : Y' ⟶ Y)
    (m : Q.obj (Q.obj X) ⟶ Q.obj X)
    (hcoc : Q.map a.hom ≫ b ≫ c = m ≫ a.hom) (ht : Q.map e ≫ a.hom = b ≫ c) :
    Q.map (a.hom ≫ e) = m := by
  rw [Q.map_comp]
  refine (cancel_mono a.hom).1 ?_
  rw [Category.assoc, ht]
  exact hcoc

/-- **A comparison determined by the image of one composite.**  If the functor `Q` carries
`a` followed by `e` to the component of an identification `u : Q ≅ 𝟭` at `Q X`, then `a` is that
identification at `X` followed by the inverse of `e`.

The companion of `Stacks.CategoryTheory.map_comp_eq_of_cancel`: that lemma computes the image,
this one reads `a` off it.  Together they are
`Stacks.CategoryTheory.transportApp_of_compLaw_of_idIso` with the comparison functor taken out. -/
theorem eq_app_comp_of_map_comp_eq {C : Type u₁} [Category* C] (Q : C ⥤ C) (u : Q ≅ 𝟭 C)
    {X Y : C} (a : Q.obj X ≅ Y) (e : Y ⟶ X) (einv : X ⟶ Y) (he : e ≫ einv = 𝟙 Y)
    (hkey : Q.map (a.hom ≫ e) = u.hom.app (Q.obj X)) :
    a.hom = u.hom.app X ≫ einv := by
  have hnat := u.hom.naturality (a.hom ≫ e)
  simp only [Functor.id_map] at hnat
  rw [hkey] at hnat
  have hs : a.hom ≫ e = u.hom.app X := ((cancel_epi (u.hom.app (Q.obj X))).1 hnat).symm
  rw [← hs, Category.assoc, he, Category.comp_id]

/-- Two mutually inverse morphisms stay mutually inverse under a composite of two functors,
with the composite written out rather than as a `CategoryTheory.Functor.comp`. -/
theorem map_map_comp_eq_id {A : Type u₂} [Category* A] {A' : Type u₃} [Category* A']
    {C : Type u₁} [Category* C] (F₁ : A ⥤ A') (F₂ : A' ⥤ C) {M N : A} (f : M ⟶ N) (g : N ⟶ M)
    (h : f ≫ g = 𝟙 M) :
    F₂.map (F₁.map f) ≫ F₂.map (F₁.map g) = 𝟙 (F₂.obj (F₁.obj M)) := by
  rw [← F₂.map_comp, ← F₁.map_comp, h, F₁.map_id, F₂.map_id]

/-- **The coherence-free half of the unit law for a morphism of pseudofunctors.**  The
composition law `hcoc`, read at one object, together with the naturality `ht` of the comparison
and the unit law `hn` of the second pseudofunctor, determines the component of the first
pseudofunctor's composition comparison at an object in the image of the comparison functor.

No unit law is asked of the first pseudofunctor; that is the hypothesis `hm` of
`Stacks.CategoryTheory.transportApp_of_compLaw_of_idIso`, which this is the first step of. -/
theorem map_transportApp_of_compLaw {A : Type u₁} [Category* A] {C : Type u₂} [Category* C]
    {A' : Type u₃} [Category* A'] (P : A ⥤ A) (Q : C ⥤ C) (F₁ : A ⥤ A') (F₂ : A' ⥤ C)
    (t : ∀ M : A, Q.obj (F₂.obj (F₁.obj M)) ≅ F₂.obj (F₁.obj (P.obj M)))
    (mapp : ∀ Z : C, Q.obj (Q.obj Z) ⟶ Q.obj Z)
    (napp : ∀ M : A, P.obj (P.obj M) ⟶ P.obj M) (wapp : ∀ M : A, P.obj M ⟶ M)
    (ht : ∀ {M N : A} (f : M ⟶ N),
      Q.map (F₂.map (F₁.map f)) ≫ (t N).hom = (t M).hom ≫ F₂.map (F₁.map (P.map f)))
    (hcoc : ∀ M : A, Q.map (t M).hom ≫ (t (P.obj M)).hom ≫ F₂.map (F₁.map (napp M)) =
      mapp (F₂.obj (F₁.obj M)) ≫ (t M).hom)
    (hn : ∀ M : A, napp M = P.map (wapp M)) (M : A) :
    Q.map ((t M).hom ≫ F₂.map (F₁.map (wapp M))) = mapp (F₂.obj (F₁.obj M)) := by
  have h := hcoc M
  rw [hn M, ← ht (wapp M), ← Category.assoc, ← Q.map_comp] at h
  exact (cancel_mono (t M).hom).1 h

/-- **The unit law for a morphism of pseudofunctors.**

Let `P : A ⥤ A` and `Q : C ⥤ C` be the values at one arrow of two pseudofunctors, with the
components `napp` and `mapp` of their composition comparisons at the pair of that arrow with
itself, and let `F₁ ⋙ F₂ : A ⥤ C` be the comparison functor of a morphism between them, whose
comparison at that arrow is the natural family of isomorphisms `t`.  If the arrow is an identity,
so that `u : Q ≅ 𝟭 C` and the mutually inverse families `wapp`, `winv` identify both values with
the identity functors and obey their own unit laws `hm` and `hn`, and if `t` obeys the composition
law `hcoc` at a single object, then `t` is the comparison they force. -/
theorem transportApp_of_compLaw_of_idIso {A : Type u₁} [Category* A] {C : Type u₂} [Category* C]
    {A' : Type u₃} [Category* A'] (P : A ⥤ A) (Q : C ⥤ C) (F₁ : A ⥤ A') (F₂ : A' ⥤ C)
    (t : ∀ M : A, Q.obj (F₂.obj (F₁.obj M)) ≅ F₂.obj (F₁.obj (P.obj M)))
    (mapp : ∀ Z : C, Q.obj (Q.obj Z) ⟶ Q.obj Z)
    (napp : ∀ M : A, P.obj (P.obj M) ⟶ P.obj M) (u : Q ≅ 𝟭 C)
    (wapp : ∀ M : A, P.obj M ⟶ M) (winv : ∀ M : A, M ⟶ P.obj M)
    (hw : ∀ M : A, wapp M ≫ winv M = 𝟙 (P.obj M))
    (ht : ∀ {M N : A} (f : M ⟶ N),
      Q.map (F₂.map (F₁.map f)) ≫ (t N).hom = (t M).hom ≫ F₂.map (F₁.map (P.map f)))
    (hcoc : ∀ M : A, Q.map (t M).hom ≫ (t (P.obj M)).hom ≫ F₂.map (F₁.map (napp M)) =
      mapp (F₂.obj (F₁.obj M)) ≫ (t M).hom)
    (hm : ∀ Z : C, mapp Z = u.hom.app (Q.obj Z))
    (hn : ∀ M : A, napp M = P.map (wapp M)) (M : A) :
    (t M).hom = u.hom.app (F₂.obj (F₁.obj M)) ≫ F₂.map (F₁.map (winv M)) := by
  have key := map_transportApp_of_compLaw P Q F₁ F₂ t mapp napp wapp ht hcoc hn M
  rw [hm (F₂.obj (F₁.obj M))] at key
  exact eq_app_comp_of_map_comp_eq Q u (t M) (F₂.map (F₁.map (wapp M)))
    (F₂.map (F₁.map (winv M))) (map_map_comp_eq_id F₁ F₂ _ _ (hw M)) key

end Stacks.CategoryTheory

end
