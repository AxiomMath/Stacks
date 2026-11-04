module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# A square of comparisons of left adjoints, from the mirrored square of right adjoints

Consider four categories `A`, `B`, `C`, `D` and the functors

* endofunctors `P` of `A` and `Q` of `C`,
* `S1, S0 : A ⥤ B` and `U1, U0 : C ⥤ D`,
* `T : B ⥤ D` and `Fs : A ⥤ C`,

each with a chosen adjunction exhibiting it as a left adjoint, together with natural
transformations

* `α : P ⋙ S1 ⟶ S0` and `α' : Q ⋙ U1 ⟶ U0` — the two *stage comparisons*;
* `β1 : S1 ⋙ T ⟶ Fs ⋙ U1` and `β0 : S0 ⋙ T ⟶ Fs ⋙ U0` — the two *bridges*;
* `κ : P ⋙ Fs ⟶ Fs ⋙ Q` — the commutation of the endofunctors with `Fs`.

The coherence this file is about is that the bridge is a morphism of the two systems
`(S0, S1, α)` and `(U0, U1, α')`: the square

```
  (P ⋙ S1) ⋙ T ────→ S0 ⋙ T
        │                 │
        ↓                 ↓
  Fs ⋙ (Q ⋙ U1) ───→ Fs ⋙ U0
```

commutes, the vertical arrows being assembled from `β1` and `κ`.

Such a coherence can essentially never be proved on the left adjoints directly, because a
left adjoint is given by a universal property and not by a construction. It can, however
always be *transported*: `CategoryTheory.conjugateEquiv` is a bijection between natural
transformations of left adjoints and natural transformations of the corresponding right
adjoints, and it turns a pasting of `2`-cells into the mirror-image pasting of their mates.
The right adjoints are the ones given by an explicit construction — restrictions of scalars,
pushforwards — so the mirrored coherence is where the actual mathematics is checkable.

## Main results

* `CategoryTheory.natTrans_square_of_conjugate`: the square of left adjoints commutes as soon
  as the mirrored square of the conjugates commutes.

## Implementation notes

The mirrored square is written out with the conjugates of the five given transformations as
its edges rather than with fresh data, so that the user supplies exactly one equation and no
compatibility between two spellings of a mate. The proof is injectivity of
`CategoryTheory.conjugateEquiv` followed by Mathlib's transfer lemmas
`CategoryTheory.conjugateEquiv_comp`, `conjugateEquiv_whiskerLeft`,
`conjugateEquiv_whiskerRight` and `conjugateEquiv_associator_hom`; the one step those do not
cover is the conjugate of an *inverse* associator, which is derived inline from the forward
one by cancelling the forward associator.
-/

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

open _root_.CategoryTheory.Functor

variable {A : Type u₁} {B : Type u₂} {Cc : Type u₃} {D : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} Cc] [Category.{v₄} D]

/-- **A square of comparisons of left adjoints commutes as soon as the mirrored square of
their mates does.**

The five natural transformations `α`, `α'`, `β1`, `β0` and `κ` relate the left adjoints; the
hypothesis is the same square read on the right adjoints, with each edge replaced by its
`CategoryTheory.conjugateEquiv` mate and the order of composition reversed. -/
lemma natTrans_square_of_conjugate
    {P : A ⥤ A} {P' : A ⥤ A} (aP : P ⊣ P')
    {S1 : A ⥤ B} {S1' : B ⥤ A} (aS1 : S1 ⊣ S1')
    {S0 : A ⥤ B} {S0' : B ⥤ A} (aS0 : S0 ⊣ S0')
    {T : B ⥤ D} {T' : D ⥤ B} (aT : T ⊣ T')
    {Fs : A ⥤ Cc} {Fs' : Cc ⥤ A} (aFs : Fs ⊣ Fs')
    {Q : Cc ⥤ Cc} {Q' : Cc ⥤ Cc} (aQ : Q ⊣ Q')
    {U1 : Cc ⥤ D} {U1' : D ⥤ Cc} (aU1 : U1 ⊣ U1')
    {U0 : Cc ⥤ D} {U0' : D ⥤ Cc} (aU0 : U0 ⊣ U0')
    (α : P ⋙ S1 ⟶ S0) (α' : Q ⋙ U1 ⟶ U0)
    (β1 : S1 ⋙ T ⟶ Fs ⋙ U1) (β0 : S0 ⋙ T ⟶ Fs ⋙ U0)
    (κ : P ⋙ Fs ⟶ Fs ⋙ Q)
    (h : conjugateEquiv (aFs.comp aU0) (aS0.comp aT) β0 ≫
            whiskerLeft T' (conjugateEquiv aS0 (aP.comp aS1) α) =
          whiskerRight (conjugateEquiv aU0 (aQ.comp aU1) α') Fs' ≫
            (associator U1' Q' Fs').hom ≫
              whiskerLeft U1' (conjugateEquiv (aFs.comp aQ) (aP.comp aFs) κ) ≫
                (associator U1' Fs' P').inv ≫
                  whiskerRight (conjugateEquiv (aFs.comp aU1) (aS1.comp aT) β1) P' ≫
                    (associator T' S1' P').hom) :
    whiskerRight α T ≫ β0 =
      (associator P S1 T).hom ≫ whiskerLeft P β1 ≫ (associator P Fs U1).inv ≫
        whiskerRight κ U1 ≫ (associator Fs Q U1).hom ≫ whiskerLeft Fs α' := by
  have hassoc : conjugateEquiv ((aP.comp aFs).comp aU1) (aP.comp (aFs.comp aU1))
      (associator P Fs U1).inv = (associator U1' Fs' P').inv := by
    apply (cancel_epi (associator U1' Fs' P').hom).1
    rw [← conjugateEquiv_associator_hom aP aFs aU1, conjugateEquiv_comp,
      Iso.inv_hom_id, conjugateEquiv_id, conjugateEquiv_associator_hom, Iso.hom_inv_id]
  apply (conjugateEquiv (aFs.comp aU0) ((aP.comp aS1).comp aT)).injective
  rw [← conjugateEquiv_comp _ (aS0.comp aT) _,
    conjugateEquiv_whiskerRight aS0 (aP.comp aS1) aT,
    ← conjugateEquiv_comp _ (aP.comp (aS1.comp aT)) _,
    ← conjugateEquiv_comp _ (aP.comp (aFs.comp aU1)) _,
    ← conjugateEquiv_comp _ ((aP.comp aFs).comp aU1) _,
    ← conjugateEquiv_comp _ ((aFs.comp aQ).comp aU1) _,
    ← conjugateEquiv_comp _ (aFs.comp (aQ.comp aU1)) _,
    conjugateEquiv_whiskerLeft aU0 (aQ.comp aU1) aFs,
    conjugateEquiv_associator_hom aFs aQ aU1,
    conjugateEquiv_whiskerRight (aFs.comp aQ) (aP.comp aFs) aU1, hassoc,
    conjugateEquiv_whiskerLeft (aFs.comp aU1) (aS1.comp aT) aP,
    conjugateEquiv_associator_hom aP aS1 aT, h]
  simp only [Category.assoc]

end CategoryTheory

end
