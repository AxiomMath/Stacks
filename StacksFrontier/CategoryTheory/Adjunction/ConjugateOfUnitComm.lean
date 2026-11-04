module

public import StacksFrontier.CategoryTheory.Adjunction.RestrictMates
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Transporting the inverse conjugate along functors compatible with the units

Let `iC : C ⥤ C'` and `iD : D ⥤ D'` be functors, and let two adjunctions `L₁ ⊣ R₁` and
`L₂ ⊣ R₂` between `C` and `D` be accompanied by adjunctions `L₁' ⊣ R₁'` and `L₂' ⊣ R₂'` between
`C'` and `D'`, together with commutation isomorphisms `iC ⋙ Lᵢ' ≅ Lᵢ ⋙ iD` and
`iD ⋙ Rᵢ' ≅ Rᵢ ⋙ iC` through which the units correspond. If transformations `β : R₁ ⟶ R₂` and
`α : R₁' ⟶ R₂'` of the right adjoints correspond, then so do the transformations of left adjoints
of which they are the conjugates.

This is the converse direction of `CategoryTheory.conjugateEquiv_of_counit_comm_app`, stated with
the units instead of the counits.

## Main results

* `CategoryTheory.unit_comm_comp`: the unit correspondence is stable under composition of
  adjunctions.
* `CategoryTheory.conjugateEquiv_symm_of_unit_comm_app`: corresponding transformations of right
  adjoints have corresponding inverse conjugates.
* `CategoryTheory.leftAdjointCompIso_hom_app_comp_leftAdjointUniq_hom_app`: the compositors of two
  triangles of adjunctions with the same right adjoints are carried into each other by the
  comparisons of the left adjoints.
-/

@[expose] public section

namespace CategoryTheory

open Category

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

section Comp

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {C' : Type u₄} [Category.{v₄} C']
  {D' : Type u₅} [Category.{v₅} D'] {E' : Type u₆} [Category.{v₆} E']
  {iC : C ⥤ C'} {iD : D ⥤ D'} {iE : E ⥤ E'}
  {LA : C ⥤ D} {RA : D ⥤ C} {LA' : C' ⥤ D'} {RA' : D' ⥤ C'}
  {LB : D ⥤ E} {RB : E ⥤ D} {LB' : D' ⥤ E'} {RB' : E' ⥤ D'}

/-- **The unit correspondence is stable under composition of adjunctions.** If `aA` and `aB`
correspond on units to `adjA` and `adjB` through the given commutation isomorphisms, then
`aA.comp aB` corresponds on units to `adjA.comp adjB` through the composite commutation
isomorphisms. -/
theorem unit_comm_comp (adjA : LA' ⊣ RA') (adjB : LB' ⊣ RB') (aA : LA ⊣ RA) (aB : LB ⊣ RB)
    (cA : iC ⋙ LA' ≅ LA ⋙ iD) (dA : iD ⋙ RA' ≅ RA ⋙ iC)
    (cB : iD ⋙ LB' ≅ LB ⋙ iE) (dB : iE ⋙ RB' ≅ RB ⋙ iD)
    (hA : ∀ X : C, iC.map (aA.unit.app X) ≫ dA.inv.app (LA.obj X) =
      adjA.unit.app (iC.obj X) ≫ RA'.map (cA.hom.app X))
    (hB : ∀ Y : D, iD.map (aB.unit.app Y) ≫ dB.inv.app (LB.obj Y) =
      adjB.unit.app (iD.obj Y) ≫ RB'.map (cB.hom.app Y))
    (X : C) :
    iC.map ((aA.comp aB).unit.app X) ≫ (commIsoComp dB dA).inv.app ((LA ⋙ LB).obj X) =
      (adjA.comp adjB).unit.app (iC.obj X) ≫
        (RB' ⋙ RA').map ((commIsoComp cA cB).hom.app X) := by
  have nA : iC.map (RA.map (aB.unit.app (LA.obj X))) ≫ dA.inv.app (RB.obj (LB.obj (LA.obj X))) =
      dA.inv.app (LA.obj X) ≫ RA'.map (iD.map (aB.unit.app (LA.obj X))) :=
    dA.inv.naturality (aB.unit.app (LA.obj X))
  have nU : cA.hom.app X ≫ adjB.unit.app (iD.obj (LA.obj X)) =
      adjB.unit.app (LA'.obj (iC.obj X)) ≫ RB'.map (LB'.map (cA.hom.app X)) :=
    adjB.unit.naturality (cA.hom.app X)
  simp only [commIsoComp_hom_app, commIsoComp_inv_app, Adjunction.comp_unit_app,
    Functor.comp_obj, Functor.comp_map, Functor.map_comp, assoc]
  calc iC.map (aA.unit.app X) ≫ iC.map (RA.map (aB.unit.app (LA.obj X))) ≫
        dA.inv.app (RB.obj (LB.obj (LA.obj X))) ≫ RA'.map (dB.inv.app (LB.obj (LA.obj X)))
      = (iC.map (aA.unit.app X) ≫ dA.inv.app (LA.obj X)) ≫
          RA'.map (iD.map (aB.unit.app (LA.obj X)) ≫ dB.inv.app (LB.obj (LA.obj X))) := by
        rw [reassoc_of% nA, Functor.map_comp, assoc]
    _ = adjA.unit.app (iC.obj X) ≫ RA'.map (cA.hom.app X ≫ adjB.unit.app (iD.obj (LA.obj X)) ≫
          RB'.map (cB.hom.app (LA.obj X))) := by
        rw [hA, hB, assoc, ← RA'.map_comp]
    _ = _ := by
        rw [reassoc_of% nU, RA'.map_comp, RA'.map_comp]

end Comp

section Conjugate

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {C' : Type u₃} [Category.{v₃} C'] {D' : Type u₄} [Category.{v₄} D']
  {iC : C ⥤ C'} {iD : D ⥤ D'}
  {L₁' L₂' : C' ⥤ D'} {R₁' R₂' : D' ⥤ C'} {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
  (adj₁ : L₁' ⊣ R₁') (adj₂ : L₂' ⊣ R₂') (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
  (c₁ : iC ⋙ L₁' ≅ L₁ ⋙ iD) (d₁ : iD ⋙ R₁' ≅ R₁ ⋙ iC)
  (c₂ : iC ⋙ L₂' ≅ L₂ ⋙ iD) (d₂ : iD ⋙ R₂' ≅ R₂ ⋙ iC)

/-- **Adjunctions that correspond on units have corresponding inverse conjugates.** If the units
of `a₁` and `a₂`, read through `iC`, are the units of `adj₁` and `adj₂` conjugated by the
commutation isomorphisms, then transformations `α : R₁' ⟶ R₂'` and `β : R₁ ⟶ R₂` which agree
through the commutation isomorphisms of the right adjoints have inverse conjugates which agree
through the commutation isomorphisms of the left adjoints. -/
theorem conjugateEquiv_symm_of_unit_comm_app
    (hu₁ : ∀ X : C, iC.map (a₁.unit.app X) ≫ d₁.inv.app (L₁.obj X) =
      adj₁.unit.app (iC.obj X) ≫ R₁'.map (c₁.hom.app X))
    (hu₂ : ∀ X : C, iC.map (a₂.unit.app X) ≫ d₂.inv.app (L₂.obj X) =
      adj₂.unit.app (iC.obj X) ≫ R₂'.map (c₂.hom.app X))
    (α : R₁' ⟶ R₂') (β : R₁ ⟶ R₂)
    (h : ∀ Y : D, d₁.inv.app Y ≫ α.app (iD.obj Y) = iC.map (β.app Y) ≫ d₂.inv.app Y)
    (X : C) :
    ((conjugateEquiv adj₁ adj₂).symm α).app (iC.obj X) ≫ c₁.hom.app X =
      c₂.hom.app X ≫ iD.map (((conjugateEquiv a₁ a₂).symm β).app X) := by
  apply (adj₂.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [← reassoc_of% (unit_conjugateEquiv_symm adj₁ adj₂ α (iC.obj X))]
  have nα : α.app (L₁'.obj (iC.obj X)) ≫ R₂'.map (c₁.hom.app X) =
      R₁'.map (c₁.hom.app X) ≫ α.app (iD.obj (L₁.obj X)) := (α.naturality (c₁.hom.app X)).symm
  have nd : iC.map (R₂.map (((conjugateEquiv a₁ a₂).symm β).app X)) ≫ d₂.inv.app (L₁.obj X) =
      d₂.inv.app (L₂.obj X) ≫ R₂'.map (iD.map (((conjugateEquiv a₁ a₂).symm β).app X)) :=
    d₂.inv.naturality (((conjugateEquiv a₁ a₂).symm β).app X)
  calc adj₁.unit.app (iC.obj X) ≫ α.app (L₁'.obj (iC.obj X)) ≫ R₂'.map (c₁.hom.app X)
      = (adj₁.unit.app (iC.obj X) ≫ R₁'.map (c₁.hom.app X)) ≫ α.app (iD.obj (L₁.obj X)) := by
        rw [nα, assoc]
    _ = iC.map (a₁.unit.app X) ≫ d₁.inv.app (L₁.obj X) ≫ α.app (iD.obj (L₁.obj X)) := by
        rw [← hu₁, assoc]
    _ = iC.map (a₁.unit.app X ≫ β.app (L₁.obj X)) ≫ d₂.inv.app (L₁.obj X) := by
        rw [h, Functor.map_comp, assoc]
    _ = (iC.map (a₂.unit.app X) ≫ d₂.inv.app (L₂.obj X)) ≫
          R₂'.map (iD.map (((conjugateEquiv a₁ a₂).symm β).app X)) := by
        rw [unit_conjugateEquiv_symm, Functor.map_comp, assoc, nd, assoc]
    _ = _ := by rw [hu₂, assoc]

end Conjugate

section LeftAdjointUniq

variable {C₀ : Type u₁} [Category.{v₁} C₀] {C₁ : Type u₂} [Category.{v₂} C₁]
  {C₂ : Type u₃} [Category.{v₃} C₂]
  {F₀₁ R₀₁ : C₀ ⥤ C₁} {F₁₂ R₁₂ : C₁ ⥤ C₂} {F₀₂ R₀₂ : C₀ ⥤ C₂}
  {G₁₀ : C₁ ⥤ C₀} {G₂₁ : C₂ ⥤ C₁} {G₂₀ : C₂ ⥤ C₀}

/-- The unit of `a₀₂` composed with `e.inv` is the unit of `a₀₁.comp a₁₂` composed with the
compositor `leftAdjointCompIso`. -/
private theorem unit_comp_leftAdjointCompIso_hom_app (a₀₁ : F₀₁ ⊣ G₁₀) (a₁₂ : F₁₂ ⊣ G₂₁)
    (a₀₂ : F₀₂ ⊣ G₂₀) (e : G₂₁ ⋙ G₁₀ ≅ G₂₀) (c : C₀) :
    a₀₂.unit.app c ≫ e.inv.app (F₀₂.obj c) = (a₀₁.comp a₁₂).unit.app c ≫
      (G₂₁ ⋙ G₁₀).map ((Adjunction.leftAdjointCompIso a₀₁ a₁₂ a₀₂ e).hom.app c) :=
  unit_conjugateEquiv_symm a₀₂ (a₀₁.comp a₁₂) e.inv c

/-- **Two triangles of adjunctions with the same right adjoints have compatible compositors.**
If `F₀₁ ⊣ G₁₀`, `F₁₂ ⊣ G₂₁`, `F₀₂ ⊣ G₂₀` and `R₀₁ ⊣ G₁₀`, `R₁₂ ⊣ G₂₁`, `R₀₂ ⊣ G₂₀` share their
right adjoints, the compositors that `CategoryTheory.Adjunction.leftAdjointCompIso` builds from
one comparison `e : G₂₁ ⋙ G₁₀ ≅ G₂₀` of the right adjoints are carried into each other by the
comparisons `CategoryTheory.Adjunction.leftAdjointUniq` of the left adjoints. -/
theorem leftAdjointCompIso_hom_app_comp_leftAdjointUniq_hom_app (a₀₁ : F₀₁ ⊣ G₁₀)
    (a₁₂ : F₁₂ ⊣ G₂₁) (a₀₂ : F₀₂ ⊣ G₂₀) (b₀₁ : R₀₁ ⊣ G₁₀) (b₁₂ : R₁₂ ⊣ G₂₁) (b₀₂ : R₀₂ ⊣ G₂₀)
    (e : G₂₁ ⋙ G₁₀ ≅ G₂₀) (c : C₀) :
    (Adjunction.leftAdjointCompIso a₀₁ a₁₂ a₀₂ e).hom.app c ≫
        (Adjunction.leftAdjointUniq a₀₂ b₀₂).hom.app c =
      F₁₂.map ((Adjunction.leftAdjointUniq a₀₁ b₀₁).hom.app c) ≫
        (Adjunction.leftAdjointUniq a₁₂ b₁₂).hom.app (R₀₁.obj c) ≫
          (Adjunction.leftAdjointCompIso b₀₁ b₁₂ b₀₂ e).hom.app c := by
  have ne : G₂₀.map ((Adjunction.leftAdjointUniq a₀₂ b₀₂).hom.app c) ≫ e.inv.app (R₀₂.obj c) =
      e.inv.app (F₀₂.obj c) ≫
        (G₂₁ ⋙ G₁₀).map ((Adjunction.leftAdjointUniq a₀₂ b₀₂).hom.app c) :=
    e.inv.naturality _
  have nu : (Adjunction.leftAdjointUniq a₀₁ b₀₁).hom.app c ≫ a₁₂.unit.app (R₀₁.obj c) =
      a₁₂.unit.app (F₀₁.obj c) ≫
        G₂₁.map (F₁₂.map ((Adjunction.leftAdjointUniq a₀₁ b₀₁).hom.app c)) :=
    a₁₂.unit.naturality _
  apply ((a₀₁.comp a₁₂).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  calc (a₀₁.comp a₁₂).unit.app c ≫
        (G₂₁ ⋙ G₁₀).map ((Adjunction.leftAdjointCompIso a₀₁ a₁₂ a₀₂ e).hom.app c) ≫
          (G₂₁ ⋙ G₁₀).map ((Adjunction.leftAdjointUniq a₀₂ b₀₂).hom.app c)
      = a₀₂.unit.app c ≫ G₂₀.map ((Adjunction.leftAdjointUniq a₀₂ b₀₂).hom.app c) ≫
          e.inv.app (R₀₂.obj c) := by
        rw [← assoc, ← unit_comp_leftAdjointCompIso_hom_app a₀₁ a₁₂ a₀₂ e c, assoc, ne]
    _ = (b₀₁.comp b₁₂).unit.app c ≫
          (G₂₁ ⋙ G₁₀).map ((Adjunction.leftAdjointCompIso b₀₁ b₁₂ b₀₂ e).hom.app c) := by
        rw [← assoc, Adjunction.unit_leftAdjointUniq_hom_app,
          unit_comp_leftAdjointCompIso_hom_app b₀₁ b₁₂ b₀₂ e c]
    _ = _ := by
        simp only [Adjunction.comp_unit_app, Functor.comp_map, assoc]
        rw [← Adjunction.unit_leftAdjointUniq_hom_app a₀₁ b₀₁ c,
          ← Adjunction.unit_leftAdjointUniq_hom_app a₁₂ b₁₂ (R₀₁.obj c)]
        have nu' := congrArg G₁₀.map nu
        simp only [Functor.map_comp] at nu' ⊢
        simp only [assoc]
        rw [reassoc_of% nu']

end LeftAdjointUniq

end CategoryTheory
