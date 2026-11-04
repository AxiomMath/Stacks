module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Localization.Adjunction

/-!
# Localization carries mates to mates

Let `adj₁ : L₁ ⊣ R₁` and `adj₂ : L₂ ⊣ R₂` be adjunctions arranged as the horizontal edges of a
square of categories, with vertical functors `G` and `H`:

```
         L₁                  R₁
      C₁ --→ D₁           C₁ ←-- D₁
    G ↓  ↗   ↓ H        G ↓  ↘   ↓ H
      C₂ --→ D₂           C₂ ←-- D₂
         L₂                  R₂
```

`CategoryTheory.mateEquiv` turns a 2-cell `α : G ⋙ L₂ ⟶ L₁ ⋙ H` into its mate
`β : R₁ ⋙ G ⟶ H ⋙ R₂`.  Suppose each of the four corners carries a localization functor, that
each of the six functors descends to the localized categories, and that the two adjunctions
descend by `CategoryTheory.Adjunction.localization`.  This file shows that the mate of the
descended 2-cell is the descended mate.

No property of the localizations is used beyond the defining one.  A mate is pinned down by a
single equation involving the counits — this is `CategoryTheory.eq_mateEquiv_of_counit` below,
the uniqueness half of `CategoryTheory.mateEquiv_counit` — and both sides of that equation are
components of natural transformations between functors out of the localized category `D₁'`, so
`CategoryTheory.Localization.natTrans_ext` reduces it to the objects in the image of the
localization functor, where the descended data is computed by the hypotheses and by
`CategoryTheory.Adjunction.localization_counit_app`.

## Main results

* `CategoryTheory.eq_mateEquiv_of_counit`: a 2-cell satisfying the counit equation of
  `CategoryTheory.mateEquiv_counit` *is* the mate.  Mathlib has that equation but not the
  uniqueness it expresses.
* `CategoryTheory.mateEquiv_localization`: **localization carries mates to mates.**

## Implementation notes

The two descended 2-cells are arguments, with their compatibility with the undescended ones as
hypotheses, rather than being constructed here: a consumer's descended 2-cell is produced by
whatever universal property is at hand — a left derived functor, say — and is only known to agree
with the undescended one on the image of the localization, which is exactly what the hypotheses
ask.  The two descended adjunctions are arguments for the same reason.

The compatibilities are written out in terms of the four relevant `CategoryTheory.CatCommSq.iso`s
rather than through `CategoryTheory.CatCommSq.hComp`: the latter is not an instance, so a
statement phrased through it would have to name the composite square at every use.  Written out,
each hypothesis is the commuting square a consumer has in hand.

Every auxiliary step of the chase is a `have` whose statement spells the objects in normalized
form — `H'.obj (PD₁.obj Y)` rather than `(PD₁ ⋙ H').obj Y` — so that `rewrite` finds its pattern;
the naturality lemmas produce the unnormalized spelling, and the conversion happens in term
position, where it runs at default transparency.

Nothing here is a result of the Stacks project: it is the compatibility of the mates
correspondence with the localization of categories.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Category

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

section Uniqueness

variable {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
  {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}

/-- **A 2-cell satisfying the counit equation of the mates correspondence is the mate.**
`CategoryTheory.mateEquiv_counit` says that the mate `β` of `α` satisfies
`L₂ (β Y) ≫ ε₂ = α (R₁ Y) ≫ H (ε₁ Y)`.  The left-hand side is the image of `β Y` under the
bijection of `adj₂`, so that equation determines `β` component by component. -/
theorem eq_mateEquiv_of_counit (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : TwoSquare G L₁ L₂ H) (β : TwoSquare R₁ H G R₂)
    (h : ∀ Y : D, L₂.map (β.app Y) ≫ adj₂.counit.app (H.obj Y) =
      α.app (R₁.obj Y) ≫ H.map (adj₁.counit.app Y)) :
    β = mateEquiv adj₁ adj₂ α := by
  refine TwoSquare.ext _ _ fun Y => ?_
  show β.app Y = (mateEquiv adj₁ adj₂ α).app Y
  refine (adj₂.homEquiv _ _).symm.injective ?_
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  exact (h Y).trans (mateEquiv_counit adj₁ adj₂ α Y).symm

end Uniqueness

section Localization

variable {C₁ : Type u₁} {C₂ : Type u₂} {D₁ : Type u₃} {D₂ : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} D₁] [Category.{v₄} D₂]
  {C₁' : Type u₅} {C₂' : Type u₆} {D₁' : Type u₇} {D₂' : Type u₈}
  [Category.{v₅} C₁'] [Category.{v₆} C₂'] [Category.{v₇} D₁'] [Category.{v₈} D₂']
  {G : C₁ ⥤ C₂} {H : D₁ ⥤ D₂} {L₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁} {L₂ : C₂ ⥤ D₂} {R₂ : D₂ ⥤ C₂}
  {G' : C₁' ⥤ C₂'} {H' : D₁' ⥤ D₂'} {L₁' : C₁' ⥤ D₁'} {R₁' : D₁' ⥤ C₁'}
  {L₂' : C₂' ⥤ D₂'} {R₂' : D₂' ⥤ C₂'}

/-- The counit of a descended adjunction, precomposed with the comparison isomorphism of the
right adjoints, is the localized counit of the original adjunction. -/
private theorem localization_counit_comp_iso
    (PC₁ : C₁ ⥤ C₁') (WC₁ : MorphismProperty C₁) [PC₁.IsLocalization WC₁]
    (PD₁ : D₁ ⥤ D₁') (WD₁ : MorphismProperty D₁) [PD₁.IsLocalization WD₁]
    [CatCommSq L₁ PC₁ PD₁ L₁'] [CatCommSq R₁ PD₁ PC₁ R₁']
    (adj₁ : L₁ ⊣ R₁) (adj₁' : L₁' ⊣ R₁')
    (h₁ : adj₁' = adj₁.localization PC₁ WC₁ PD₁ WD₁ L₁' R₁') (Y : D₁) :
    L₁'.map ((CatCommSq.iso R₁ PD₁ PC₁ R₁').hom.app Y) ≫ adj₁'.counit.app (PD₁.obj Y) =
      (CatCommSq.iso L₁ PC₁ PD₁ L₁').inv.app (R₁.obj Y) ≫ PD₁.map (adj₁.counit.app Y) := by
  rw [h₁, Adjunction.localization_counit_app, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, Functor.map_id, id_comp]

/-- **Localization carries mates to mates.**  The four corners of the square are localized by
`PC₁`, `PC₂`, `PD₁`, `PD₂`, each of the six functors descends as recorded by a
`CategoryTheory.CatCommSq`, and `adj₁'`, `adj₂'` are the descents of `adj₁`, `adj₂` given by
`CategoryTheory.Adjunction.localization`.  If `α'` descends `α` and `β'` descends the mate of
`α` — each in the sense that the evident square commutes on the image of the localization functor
of its source corner — then `β'` is the mate of `α'`. -/
theorem mateEquiv_localization
    (PC₁ : C₁ ⥤ C₁') (WC₁ : MorphismProperty C₁) [PC₁.IsLocalization WC₁]
    (PC₂ : C₂ ⥤ C₂') (WC₂ : MorphismProperty C₂) [PC₂.IsLocalization WC₂]
    (PD₁ : D₁ ⥤ D₁') (WD₁ : MorphismProperty D₁) [PD₁.IsLocalization WD₁]
    (PD₂ : D₂ ⥤ D₂') (WD₂ : MorphismProperty D₂) [PD₂.IsLocalization WD₂]
    [CatCommSq G PC₁ PC₂ G'] [CatCommSq H PD₁ PD₂ H']
    [CatCommSq L₁ PC₁ PD₁ L₁'] [CatCommSq R₁ PD₁ PC₁ R₁']
    [CatCommSq L₂ PC₂ PD₂ L₂'] [CatCommSq R₂ PD₂ PC₂ R₂']
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₁' : L₁' ⊣ R₁') (adj₂' : L₂' ⊣ R₂')
    (h₁ : adj₁' = adj₁.localization PC₁ WC₁ PD₁ WD₁ L₁' R₁')
    (h₂ : adj₂' = adj₂.localization PC₂ WC₂ PD₂ WD₂ L₂' R₂')
    (α : TwoSquare G L₁ L₂ H) (α' : TwoSquare G' L₁' L₂' H')
    (β' : TwoSquare R₁' H' G' R₂')
    (hα : ∀ X : C₁, (CatCommSq.iso L₂ PC₂ PD₂ L₂').hom.app (G.obj X) ≫
        L₂'.map ((CatCommSq.iso G PC₁ PC₂ G').hom.app X) ≫ α'.app (PC₁.obj X) =
      PD₂.map (α.app X) ≫ (CatCommSq.iso H PD₁ PD₂ H').hom.app (L₁.obj X) ≫
        H'.map ((CatCommSq.iso L₁ PC₁ PD₁ L₁').hom.app X))
    (hβ : ∀ Y : D₁, (CatCommSq.iso G PC₁ PC₂ G').hom.app (R₁.obj Y) ≫
        G'.map ((CatCommSq.iso R₁ PD₁ PC₁ R₁').hom.app Y) ≫ β'.app (PD₁.obj Y) =
      PC₂.map ((mateEquiv adj₁ adj₂ α).app Y) ≫
        (CatCommSq.iso R₂ PD₂ PC₂ R₂').hom.app (H.obj Y) ≫
        R₂'.map ((CatCommSq.iso H PD₁ PD₂ H').hom.app Y)) :
    β' = mateEquiv adj₁' adj₂' α' := by
  refine eq_mateEquiv_of_counit adj₁' adj₂' α' β' ?_
  -- The counit equation on the image of `PD₁`.
  have key : ∀ Y : D₁,
      L₂'.map (β'.app (PD₁.obj Y)) ≫ adj₂'.counit.app (H'.obj (PD₁.obj Y)) =
        α'.app (R₁'.obj (PD₁.obj Y)) ≫ H'.map (adj₁'.counit.app (PD₁.obj Y)) := by
    intro Y
    have hcn : L₂'.map (R₂'.map ((CatCommSq.iso H PD₁ PD₂ H').hom.app Y)) ≫
          adj₂'.counit.app (H'.obj (PD₁.obj Y)) =
        adj₂'.counit.app (PD₂.obj (H.obj Y)) ≫ (CatCommSq.iso H PD₁ PD₂ H').hom.app Y :=
      adj₂'.counit_naturality _
    have hc₂ := reassoc_of%
      localization_counit_comp_iso PC₂ WC₂ PD₂ WD₂ adj₂ adj₂' h₂ (H.obj Y)
    have hnat : L₂'.map (PC₂.map ((mateEquiv adj₁ adj₂ α).app Y)) ≫
          (CatCommSq.iso L₂ PC₂ PD₂ L₂').inv.app (R₂.obj (H.obj Y)) =
        (CatCommSq.iso L₂ PC₂ PD₂ L₂').inv.app (G.obj (R₁.obj Y)) ≫
          PD₂.map (L₂.map ((mateEquiv adj₁ adj₂ α).app Y)) :=
      (CatCommSq.iso L₂ PC₂ PD₂ L₂').inv.naturality _
    have hl := reassoc_of% hnat
    have hnα₀ : L₂'.map (G'.map ((CatCommSq.iso R₁ PD₁ PC₁ R₁').hom.app Y)) ≫
          α'.app (R₁'.obj (PD₁.obj Y)) =
        α'.app (PC₁.obj (R₁.obj Y)) ≫
          H'.map (L₁'.map ((CatCommSq.iso R₁ PD₁ PC₁ R₁').hom.app Y)) :=
      α'.naturality _
    have hnα := reassoc_of% hnα₀
    have hc₁ := localization_counit_comp_iso PC₁ WC₁ PD₁ WD₁ adj₁ adj₁' h₁ Y
    have hH : H'.map (L₁'.map ((CatCommSq.iso R₁ PD₁ PC₁ R₁').hom.app Y)) ≫
          H'.map (adj₁'.counit.app (PD₁.obj Y)) =
        H'.map ((CatCommSq.iso L₁ PC₁ PD₁ L₁').inv.app (R₁.obj Y)) ≫
          H'.map (PD₁.map (adj₁.counit.app Y)) := by
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg _ hc₁
    have hα₀ : L₂'.map ((CatCommSq.iso G PC₁ PC₂ G').hom.app (R₁.obj Y)) ≫
          α'.app (PC₁.obj (R₁.obj Y)) =
        (CatCommSq.iso L₂ PC₂ PD₂ L₂').inv.app (G.obj (R₁.obj Y)) ≫
          PD₂.map (α.app (R₁.obj Y)) ≫
          (CatCommSq.iso H PD₁ PD₂ H').hom.app (L₁.obj (R₁.obj Y)) ≫
          H'.map ((CatCommSq.iso L₁ PC₁ PD₁ L₁').hom.app (R₁.obj Y)) := by
      rw [← cancel_epi ((CatCommSq.iso L₂ PC₂ PD₂ L₂').hom.app (G.obj (R₁.obj Y))),
        hα (R₁.obj Y)]
      simp
    have hα₁ := reassoc_of% hα₀
    have hm₀ : H'.map ((CatCommSq.iso L₁ PC₁ PD₁ L₁').hom.app (R₁.obj Y)) ≫
        H'.map ((CatCommSq.iso L₁ PC₁ PD₁ L₁').inv.app (R₁.obj Y)) = 𝟙 _ := by
      rw [← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]
    have hm := reassoc_of% hm₀
    have hh : PD₂.map (H.map (adj₁.counit.app Y)) ≫
          (CatCommSq.iso H PD₁ PD₂ H').hom.app Y =
        (CatCommSq.iso H PD₁ PD₂ H').hom.app (L₁.obj (R₁.obj Y)) ≫
          H'.map (PD₁.map (adj₁.counit.app Y)) :=
      CatCommSq.iso_hom_naturality H PD₁ PD₂ H' (adj₁.counit.app Y)
    rw [← cancel_epi (L₂'.map ((CatCommSq.iso G PC₁ PC₂ G').hom.app (R₁.obj Y) ≫
      G'.map ((CatCommSq.iso R₁ PD₁ PC₁ R₁').hom.app Y)))]
    have hL : L₂'.map ((CatCommSq.iso G PC₁ PC₂ G').hom.app (R₁.obj Y) ≫
          G'.map ((CatCommSq.iso R₁ PD₁ PC₁ R₁').hom.app Y)) ≫
        L₂'.map (β'.app (PD₁.obj Y)) ≫ adj₂'.counit.app (H'.obj (PD₁.obj Y)) =
      (CatCommSq.iso L₂ PC₂ PD₂ L₂').inv.app (G.obj (R₁.obj Y)) ≫
        PD₂.map (L₂.map ((mateEquiv adj₁ adj₂ α).app Y) ≫ adj₂.counit.app (H.obj Y)) ≫
        (CatCommSq.iso H PD₁ PD₂ H').hom.app Y := by
      rw [← Functor.map_comp_assoc, assoc, hβ Y, Functor.map_comp, Functor.map_comp, assoc,
        assoc, hcn, hc₂, hl, ← Functor.map_comp_assoc]
    have hR : L₂'.map ((CatCommSq.iso G PC₁ PC₂ G').hom.app (R₁.obj Y) ≫
          G'.map ((CatCommSq.iso R₁ PD₁ PC₁ R₁').hom.app Y)) ≫
        α'.app (R₁'.obj (PD₁.obj Y)) ≫ H'.map (adj₁'.counit.app (PD₁.obj Y)) =
      (CatCommSq.iso L₂ PC₂ PD₂ L₂').inv.app (G.obj (R₁.obj Y)) ≫
        PD₂.map (α.app (R₁.obj Y) ≫ H.map (adj₁.counit.app Y)) ≫
        (CatCommSq.iso H PD₁ PD₂ H').hom.app Y := by
      rw [Functor.map_comp, assoc, hnα, hH, hα₁, hm, ← hh, ← Functor.map_comp_assoc]
    rw [hL, hR, mateEquiv_counit adj₁ adj₂ α Y]
  -- Both sides are components of natural transformations out of `D₁'`.
  have knat : (Functor.associator R₁' G' L₂').inv ≫ Functor.whiskerRight β'.natTrans L₂' ≫
        (Functor.associator H' R₂' L₂').hom ≫ Functor.whiskerLeft H' adj₂'.counit ≫
        (Functor.rightUnitor H').hom =
      Functor.whiskerLeft R₁' α'.natTrans ≫ (Functor.associator R₁' L₁' H').inv ≫
        Functor.whiskerRight adj₁'.counit H' ≫ (Functor.leftUnitor H').hom :=
    Localization.natTrans_ext PD₁ WD₁ fun Y => by
      simpa [Functor.whiskerLeft_app, Functor.whiskerRight_app] using key Y
  intro Z
  simpa [Functor.whiskerLeft_app, Functor.whiskerRight_app] using NatTrans.congr_app knat Z

end Localization

end CategoryTheory

end
