module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerived

/-!
# Uniqueness of right derived descent, and its transport along a comparison of units

Let `L : 𝒞 ⥤ 𝒟` be a localization functor for a class `W` of morphisms of `𝒞`, let `F : 𝒞 ⥤ ℋ`
and let `α : F ⟶ L ⋙ RF` exhibit `RF : 𝒟 ⥤ ℋ` as a right derived functor of `F`. A natural
transformation `β : F ⟶ L ⋙ G` then descends to a unique `RF ⟶ G`,
`CategoryTheory.Functor.rightDerivedDesc`, characterized by
`CategoryTheory.Functor.rightDerived_fac`. This file records the two consequences of that
characterization which a comparison of two such descents needs, and which Mathlib states only
in the one direction that builds a descent.

The first is that the descent determines the transformation it descends: two descents out of the
same right derived functor agree exactly when the transformations they descend agree. The second
is the transport: a comparison `u : RF ⟶ RF'` of two right derived functors of the *same* `F`
which is compatible with the two derivation units absorbs a descent, in the sense that
`u ≫ RF'.rightDerivedDesc α' β` is `RF.rightDerivedDesc α β`.

Combining the two gives `comp_rightDerivedDesc_eq_rightDerivedDesc_iff`, which is the shape in
which an identification of two canonical maps obtained by right derived descent is to be used:
it turns such an identification — a statement about functors on localized categories — into the
corresponding statement about the two underived transformations, where it is a computation with
the data the two descents were built from.

## Main results

* `Stacks.RightDerivedDescent.rightDerivedDesc_eq_iff`: **the descent determines what it
  descends.** Two right derived descents out of the same right derived functor, into the same
  target, are equal exactly when the natural transformations they descend are equal.
* `Stacks.RightDerivedDescent.comp_rightDerivedDesc`: **transport.** A comparison of two right
  derived functors of the same functor which matches the two derivation units absorbs a right
  derived descent.
* `Stacks.RightDerivedDescent.rightDerivedDesc_eq_inv_comp`: the same for an isomorphism of right
  derived functors, read as a conjugation.
* `Stacks.RightDerivedDescent.comp_rightDerivedDesc_eq_rightDerivedDesc_iff`: the combination of
  the two — the reduction of an identity between two transported descents to the identity of the
  two transformations they descend.

## Implementation notes

Everything here is a two-line consequence of `CategoryTheory.Functor.rightDerived_fac` and
`CategoryTheory.Functor.rightDerived_ext`. It is stated at a variable localization and at
variable categories on purpose: the intended instantiations have both `RF` and `G` built as
composites of functors between categories of complexes, homotopy categories and derived
categories, and in a goal mentioning such a composite `rw`, `simp` and `reassoc_of%` all report
that they have nothing to do — a term whose type is written through
`CategoryTheory.Functor.comp` is type-correct only up to unfolding that definition, which is not
the transparency at which a rewrite motive is checked. Proved at a variable category every
rewrite here is immediate, and `exact` instantiates the result up to default transparency.

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace Stacks.RightDerivedDescent

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {H : Type u₃} [Category.{v₃} H] {L : C ⥤ D} {F : C ⥤ H}
  (W : MorphismProperty C) [L.IsLocalization W]
  (RF : D ⥤ H) (α : F ⟶ L ⋙ RF) [RF.IsRightDerivedFunctor α W]

/-- **A right derived descent determines the natural transformation it descends.** The descent of
`β : F ⟶ L ⋙ G` along `α : F ⟶ L ⋙ RF` recovers `β` on composition with `α`, so two descents out
of the same right derived functor into the same target agree exactly when what they descend
agrees. The interesting direction is the forward one; the converse is a congruence. -/
theorem rightDerivedDesc_eq_iff (G : D ⥤ H) (β β' : F ⟶ L ⋙ G) :
    RF.rightDerivedDesc α W G β = RF.rightDerivedDesc α W G β' ↔ β = β' := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  rw [← Functor.rightDerived_fac RF α W G β, ← Functor.rightDerived_fac RF α W G β', h]

variable (RF' : D ⥤ H) (α' : F ⟶ L ⋙ RF') [RF'.IsRightDerivedFunctor α' W]

/-- **A comparison of two right derived functors of the same functor absorbs a right derived
descent.** If `u : RF ⟶ RF'` matches the two derivation units, in the sense that `α` followed by
`u` is `α'`, then composing `u` with the descent of `β` along `α'` is the descent of the same `β`
along `α`. Both sides are transformations out of `RF`, and `rightDerived_ext` compares them by
their composites with `α`, each of which is `β` by `rightDerived_fac`. -/
theorem comp_rightDerivedDesc (u : RF ⟶ RF') (hu : α ≫ Functor.whiskerLeft L u = α')
    (G : D ⥤ H) (β : F ⟶ L ⋙ G) :
    u ≫ RF'.rightDerivedDesc α' W G β = RF.rightDerivedDesc α W G β := by
  refine Functor.rightDerived_ext RF α W G _ _ ?_
  rw [Functor.whiskerLeft_comp, ← Category.assoc, hu, Functor.rightDerived_fac,
    Functor.rightDerived_fac]

/-- The transport of `comp_rightDerivedDesc` for an isomorphism of right derived functors, read as
a conjugation: a descent along `α'` is the inverse comparison followed by the descent along
`α`. -/
theorem rightDerivedDesc_eq_inv_comp (e : RF ≅ RF')
    (he : α ≫ Functor.whiskerLeft L e.hom = α') (G : D ⥤ H) (β : F ⟶ L ⋙ G) :
    RF'.rightDerivedDesc α' W G β = e.inv ≫ RF.rightDerivedDesc α W G β := by
  rw [← comp_rightDerivedDesc W RF α RF' α' e.hom he G β, ← Category.assoc, e.inv_hom_id,
    Category.id_comp]

/-- **The reduction of an identity of two right derived descents to an identity of the two
transformations they descend.** Given a comparison `u : RF ⟶ RF'` matching the two derivation
units, the descent of `β` along `α'` — transported by `u` — is the descent of `β'` along `α`
exactly when `β = β'`.

This is the shape in which two canonical maps built by right derived descent are to be
identified: the left hand side is an identity in the category of natural transformations between
functors on localized categories, about which nothing is computable, and the right hand side is
an identity between two explicit composites of the data the descents were built from. -/
theorem comp_rightDerivedDesc_eq_rightDerivedDesc_iff (u : RF ⟶ RF')
    (hu : α ≫ Functor.whiskerLeft L u = α') (G : D ⥤ H) (β β' : F ⟶ L ⋙ G) :
    u ≫ RF'.rightDerivedDesc α' W G β = RF.rightDerivedDesc α W G β' ↔ β = β' := by
  rw [comp_rightDerivedDesc W RF α RF' α' u hu G β, rightDerivedDesc_eq_iff]

end Stacks.RightDerivedDescent

end
