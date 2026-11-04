module

public import StacksFrontier.CategoryTheory.Localization.MateLocalization

/-!
# Transporting a mate along isomorphisms of the four functors of its square

Let `adj₁ : L₁ ⊣ R₁` and `adj₂ : L₂ ⊣ R₂` be adjunctions and let `α : TwoSquare G L₁ L₂ H` be a
2-cell, with mate `CategoryTheory.mateEquiv adj₁ adj₂ α : TwoSquare R₁ H G R₂`.  Each of the six
functors involved may be replaced by an isomorphic one: the two adjunctions may be transported
along `CategoryTheory.Adjunction.ofNatIsoLeft` and
`CategoryTheory.Adjunction.ofNatIsoRight`, and the two vertical edges `G` and `H` of the square
may be replaced outright.  This file says what each replacement does to the mate.

The three statements are what lets a mate computed for one presentation of a square of
adjunctions be read off for another — the situation of the derived base change of
[Stacks, Tag 08HY], which is a mate for the derived adjunctions of [Stacks, Tag 079W] while the
mates calculus on derived categories is available for the degreewise adjunctions.

## Main results

* `CategoryTheory.mateEquiv_ofNatIsoLeft`: replacing the **left** adjoints leaves the mate
  unchanged, once the 2-cell is conjugated accordingly.  This is the direction in which nothing
  happens, because the mate lives on the right adjoints.
* `CategoryTheory.mateEquiv_ofNatIsoRight`: replacing the **right** adjoints conjugates the mate
  by the two isomorphisms, and changes nothing else.
* `CategoryTheory.mateEquiv_conj_vertical`: replacing the two **vertical** edges `G` and `H`
  conjugates both the 2-cell and its mate, each by the isomorphism at the edge it meets.

## Implementation notes

Each proof is one application of
`CategoryTheory.eq_mateEquiv_of_counit`: a 2-cell satisfying the counit equation of the mates
correspondence *is* the mate, so it is enough to check that equation for the candidate, and the
counits of `CategoryTheory.Adjunction.ofNatIsoLeft` and
`CategoryTheory.Adjunction.ofNatIsoRight` are given by the `@[simps]` lemmas
`Adjunction.ofNatIsoLeft_counit` and `Adjunction.ofNatIsoRight_counit`.  What is left in each
case is one associativity chase, and each chase is a `private` helper at an arbitrary category
with the objects implicit and the morphisms explicit, applied with `exact`: at the categories
these are used at the two bracketings of a composite are definitionally but not syntactically
equal, and `rw` on `CategoryTheory.Category.assoc` fails on them.

The hypotheses are stated componentwise (`∀ a, α'.app a = …`) rather than as equalities of
natural transformations, so that a caller whose square is built from whiskerings does not have
to normalise them first.

## References

* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Category

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
  {G : A ⥤ C} {H : B ⥤ D}
  {L₁ L₁' : A ⥤ B} {R₁ : B ⥤ A} {L₂ L₂' : C ⥤ D} {R₂ : D ⥤ C}

/-! ### Replacing the left adjoints -/

/-- The chase behind `mateEquiv_ofNatIsoLeft`: one naturality square, the counit equation, and
a pair of mutually inverse morphisms cancelled.  Stated at an arbitrary category with the
objects implicit and the morphisms explicit. -/
private theorem chaseL {E : Type*} [Category* E] {p q r s t w w' : E}
    (m : p ⟶ q) (i₂ : q ⟶ r) (c₂ : r ⟶ t) (i₁ : p ⟶ s) (m' : s ⟶ r)
    (aa : s ⟶ w) (hc : w ⟶ t) (hh : w ⟶ w') (hi : w' ⟶ w)
    (hnat : m ≫ i₂ = i₁ ≫ m') (hcc : m' ≫ c₂ = aa ≫ hc)
    (htri : hh ≫ hi = CategoryStruct.id w) :
    m ≫ i₂ ≫ c₂ = i₁ ≫ aa ≫ hh ≫ hi ≫ hc := by
  rw [reassoc_of% hnat, hcc, reassoc_of% htri]

/-- **Transporting both adjunctions along isomorphisms of their left adjoints does not change
the mate.**  If `e₁ : L₁ ≅ L₁'` and `e₂ : L₂ ≅ L₂'` and the 2-cell `α' : TwoSquare G L₁' L₂' H`
is `α` conjugated by them, then `α'` and `α` have the same mate — which is possible because the
mate is a 2-cell between the right adjoints, and those have not moved. -/
theorem mateEquiv_ofNatIsoLeft (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (e₁ : L₁ ≅ L₁') (e₂ : L₂ ≅ L₂') (α : TwoSquare G L₁ L₂ H) (α' : TwoSquare G L₁' L₂' H)
    (hα : ∀ a : A, α'.app a = e₂.inv.app (G.obj a) ≫ α.app a ≫ H.map (e₁.hom.app a)) :
    mateEquiv (adj₁.ofNatIsoLeft e₁) (adj₂.ofNatIsoLeft e₂) α' = mateEquiv adj₁ adj₂ α := by
  refine (eq_mateEquiv_of_counit (adj₁.ofNatIsoLeft e₁) (adj₂.ofNatIsoLeft e₂) α'
    (mateEquiv adj₁ adj₂ α) fun Y => ?_).symm
  simp only [Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app, Functor.whiskerLeft_app,
    hα, Functor.comp_obj, Functor.map_comp, Category.assoc]
  exact chaseL _ _ _ _ _ _ _ _ _ (e₂.inv.naturality _)
    (mateEquiv_counit adj₁ adj₂ α Y)
    ((H.map_comp _ _).symm.trans
      ((congrArg H.map (e₁.hom_inv_id_app (R₁.obj Y))).trans (H.map_id _)))

/-! ### Replacing the right adjoints -/

/-- **Transporting both adjunctions along isomorphisms of their right adjoints conjugates the
mate by those isomorphisms.**  The 2-cell `α` is untouched — it mentions only the left adjoints
— and the mate acquires `d₁` at its source and `d₂` at its target. -/
theorem mateEquiv_ofNatIsoRight {R₁' : B ⥤ A} {R₂' : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (d₁ : R₁ ≅ R₁') (d₂ : R₂ ≅ R₂') (α : TwoSquare G L₁ L₂ H)
    (β : TwoSquare R₁' H G R₂')
    (hβ : ∀ Y : B, β.app Y =
      G.map (d₁.inv.app Y) ≫ (mateEquiv adj₁ adj₂ α).app Y ≫ d₂.hom.app (H.obj Y)) :
    β = mateEquiv (adj₁.ofNatIsoRight d₁) (adj₂.ofNatIsoRight d₂) α := by
  refine eq_mateEquiv_of_counit (adj₁.ofNatIsoRight d₁) (adj₂.ofNatIsoRight d₂) α β fun Y => ?_
  have hnat := α.naturality (d₁.inv.app Y)
  have hc := mateEquiv_counit adj₁ adj₂ α Y
  simp only [hβ, Adjunction.ofNatIsoRight_counit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.comp_obj, Functor.comp_map, Functor.map_comp,
    Category.assoc] at hnat hc ⊢
  rw [← Category.assoc (L₂.map (d₂.hom.app _)), ← L₂.map_comp, d₂.hom_inv_id_app,
    L₂.map_id, Category.id_comp, hc, ← Category.assoc, hnat, Category.assoc]

/-! ### Replacing the two vertical edges -/

/-- The chase behind `mateEquiv_conj_vertical`: the counit equation followed by one naturality
square.  Stated at an arbitrary category with the objects implicit and the morphisms
explicit. -/
private theorem chaseV {E : Type*} [Category* E] {p q r s t u v : E}
    (g : p ⟶ q) (b : q ⟶ r) (c : r ⟶ s) (e : s ⟶ t) (a : q ⟶ u) (hm : u ⟶ s)
    (eh : u ⟶ v) (hp : v ⟶ t)
    (hc : b ≫ c = a ≫ hm) (hH : hm ≫ e = eh ≫ hp) :
    g ≫ b ≫ c ≫ e = g ≫ a ≫ eh ≫ hp := by
  rw [reassoc_of% hc, hH]

/-- **Conjugating the two vertical edges of a 2-cell conjugates its mate.**  If `eG : G ≅ G'`
and `eH : H ≅ H'` and `α'` is `α` read at the new edges, then the mate of `α'` is the mate of
`α` with `eG` at its source and `eH`, under the right adjoint, at its target. -/
theorem mateEquiv_conj_vertical {G' : A ⥤ C} {H' : B ⥤ D} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (eG : G ≅ G') (eH : H ≅ H') (α : TwoSquare G L₁ L₂ H) (α' : TwoSquare G' L₁ L₂ H')
    (hα : ∀ a : A, α'.app a =
      L₂.map (eG.inv.app a) ≫ α.app a ≫ eH.hom.app (L₁.obj a))
    (β : TwoSquare R₁ H' G' R₂)
    (hβ : ∀ Y : B, β.app Y =
      eG.inv.app (R₁.obj Y) ≫ (mateEquiv adj₁ adj₂ α).app Y ≫ R₂.map (eH.hom.app Y)) :
    β = mateEquiv adj₁ adj₂ α' := by
  refine eq_mateEquiv_of_counit adj₁ adj₂ α' β fun Y => ?_
  have hc := mateEquiv_counit adj₁ adj₂ α Y
  have hε := adj₂.counit.naturality (eH.hom.app Y)
  have hH := eH.hom.naturality (adj₁.counit.app Y)
  simp only [hβ, hα, Functor.map_comp, Category.assoc, Functor.comp_map, Functor.id_map]
    at hc hε hH ⊢
  rw [hε]
  exact chaseV _ _ _ _ _ _ _ _ hc hH

end CategoryTheory

end
