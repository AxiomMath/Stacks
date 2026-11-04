module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Restrict

/-!
# Restricting adjunctions along a pair of functors preserves adjoint mates

Let `iC : C ⥤ C'` and `iD : D ⥤ D'` be functors, and let two adjunctions `L₁' ⊣ R₁'` and
`L₂' ⊣ R₂'` between `C'` and `D'` be accompanied by adjunctions `L₁ ⊣ R₁` and `L₂ ⊣ R₂`
between `C` and `D` together with commutation isomorphisms `iC ⋙ Lᵢ' ≅ Lᵢ ⋙ iD` and
`iD ⋙ Rᵢ' ≅ Rᵢ ⋙ iC` through which the counits correspond. A transformation `α : L₂' ⟶ L₁'`
compatible with a transformation `β : L₂ ⟶ L₁` then has an adjoint mate compatible with the
adjoint mate of `β`.

The counit correspondence is the only property of the smaller adjunctions that is used, and it
holds for `CategoryTheory.Adjunction.restrictFullyFaithful` and for a composite of two
adjunctions each of which has it. Those two facts together cover the composite of two
restricted adjunctions, which is not itself a restricted adjunction on the nose.

## Main definitions

* `CategoryTheory.commIsoComp`: the commutation isomorphism of a composite of two functors,
  built from the commutation isomorphisms of the factors.

## Main results

* `CategoryTheory.conjugateEquiv_of_counit_comm_app` and
  `CategoryTheory.conjugateEquiv_of_counit_comm`: the mate compatibility, componentwise and as
  an equality of natural transformations;
* `CategoryTheory.counit_comm_restrictFullyFaithful`: the counit correspondence holds for an
  adjunction restricted along fully faithful functors;
* `CategoryTheory.counit_comm_comp`: the counit correspondence is stable under composition of
  adjunctions;
* `CategoryTheory.conjugateEquiv_restrictFullyFaithful_app`: the mate compatibility for two
  adjunctions restricted along the same pair of fully faithful functors.

## Implementation notes

The proof of `CategoryTheory.conjugateEquiv_of_counit_comm_app` transposes along the second
ambient adjunction, where the statement becomes an equality of morphisms out of
`L₂'.obj (R₁'.obj (iD.obj Y))`, and then rewrites with the counit correspondence at both
indices. What is left is the naturality of `α` and the compatibility hypothesis.

Only the case of equal vertical functors is treated, which is the case in which mates are
transported by `CategoryTheory.conjugateEquiv`. The variant for a general 2-square, in which
the two adjunctions live between two different pairs of categories and six commutation
isomorphisms appear instead of four, is
`CategoryTheory.mateEquiv_restrictFullyFaithful_app` in
`StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.MateCoherence`; it is stated for
`CategoryTheory.Adjunction.restrictFullyFaithful` itself rather than for the counit
correspondence, so it does not apply to a composite of restricted adjunctions.

Nothing here carries a Stacks attribute: these are general facts about adjunctions and the
source states none of them.
-/

@[expose] public section

namespace CategoryTheory

open Category

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

section CommIsoComp

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {C' : Type u₄} [Category.{v₄} C']
  {D' : Type u₅} [Category.{v₅} D'] {E' : Type u₆} [Category.{v₆} E']
  {iC : C ⥤ C'} {iD : D ⥤ D'} {iE : E ⥤ E'}
  {LA : C ⥤ D} {LA' : C' ⥤ D'} {LB : D ⥤ E} {LB' : D' ⥤ E'}

/-- The commutation isomorphism of a composite: if `iC ⋙ LA' ≅ LA ⋙ iD` and
`iD ⋙ LB' ≅ LB ⋙ iE`, then `iC ⋙ LA' ⋙ LB' ≅ (LA ⋙ LB) ⋙ iE`. -/
@[simps!]
def commIsoComp (cA : iC ⋙ LA' ≅ LA ⋙ iD) (cB : iD ⋙ LB' ≅ LB ⋙ iE) :
    iC ⋙ LA' ⋙ LB' ≅ (LA ⋙ LB) ⋙ iE :=
  NatIso.ofComponents (fun X ↦ LB'.mapIso (cA.app X) ≪≫ cB.app (LA.obj X)) (by
    intro X Y f
    have hA := cA.hom.naturality f
    have hB := cB.hom.naturality (LA.map f)
    dsimp at hA hB ⊢
    rw [assoc, ← hB, ← Functor.map_comp_assoc LB' (cA.hom.app X) (iD.map (LA.map f)), ← hA,
      Functor.map_comp, assoc])

end CommIsoComp

section Conjugate

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {C' : Type u₃} [Category.{v₃} C'] {D' : Type u₄} [Category.{v₄} D']
  {iC : C ⥤ C'} {iD : D ⥤ D'}
  {L₁' L₂' : C' ⥤ D'} {R₁' R₂' : D' ⥤ C'} {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
  (adj₁ : L₁' ⊣ R₁') (adj₂ : L₂' ⊣ R₂') (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
  (c₁ : iC ⋙ L₁' ≅ L₁ ⋙ iD) (d₁ : iD ⋙ R₁' ≅ R₁ ⋙ iC)
  (c₂ : iC ⋙ L₂' ≅ L₂ ⋙ iD) (d₂ : iD ⋙ R₂' ≅ R₂ ⋙ iC)

/-- **Adjunctions that correspond on counits have corresponding mates.** If the counits of
`a₁` and `a₂`, read through `iD`, are the counits of `adj₁` and `adj₂` conjugated by the
commutation isomorphisms, then a transformation `α : L₂' ⟶ L₁'` compatible with
`β : L₂ ⟶ L₁` has a mate compatible with the mate of `β`. -/
theorem conjugateEquiv_of_counit_comm_app
    (hc₁ : ∀ Y : D, c₁.hom.app (R₁.obj Y) ≫ iD.map (a₁.counit.app Y) =
      L₁'.map (d₁.inv.app Y) ≫ adj₁.counit.app (iD.obj Y))
    (hc₂ : ∀ Y : D, c₂.hom.app (R₂.obj Y) ≫ iD.map (a₂.counit.app Y) =
      L₂'.map (d₂.inv.app Y) ≫ adj₂.counit.app (iD.obj Y))
    (α : L₂' ⟶ L₁') (β : L₂ ⟶ L₁)
    (h : ∀ X : C, α.app (iC.obj X) ≫ c₁.hom.app X = c₂.hom.app X ≫ iD.map (β.app X))
    (Y : D) :
    d₁.hom.app Y ≫ iC.map ((conjugateEquiv a₁ a₂ β).app Y) =
      (conjugateEquiv adj₁ adj₂ α).app (iD.obj Y) ≫ d₂.hom.app Y := by
  set γ := conjugateEquiv a₁ a₂ β with hγ
  suffices key : d₁.hom.app Y ≫ iC.map (γ.app Y) ≫ d₂.inv.app Y =
      (conjugateEquiv adj₁ adj₂ α).app (iD.obj Y) by
    rw [← key, assoc, assoc, Iso.inv_hom_id_app]
    simp
  apply (adj₂.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, assoc]
  rw [conjugateEquiv_counit adj₁ adj₂ α (iD.obj Y), ← hc₂ Y]
  have n₂ := c₂.hom.naturality (γ.app Y)
  dsimp at n₂
  rw [reassoc_of% n₂, ← Functor.map_comp iD, hγ, conjugateEquiv_counit a₁ a₂ β Y,
    Functor.map_comp iD, reassoc_of% (h (R₁.obj Y)).symm, hc₁ Y,
    ← reassoc_of% (α.naturality (d₁.inv.app Y)), ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app]
  simp

/-- `CategoryTheory.conjugateEquiv_of_counit_comm_app` as an equality of natural
transformations. -/
theorem conjugateEquiv_of_counit_comm
    (hc₁ : ∀ Y : D, c₁.hom.app (R₁.obj Y) ≫ iD.map (a₁.counit.app Y) =
      L₁'.map (d₁.inv.app Y) ≫ adj₁.counit.app (iD.obj Y))
    (hc₂ : ∀ Y : D, c₂.hom.app (R₂.obj Y) ≫ iD.map (a₂.counit.app Y) =
      L₂'.map (d₂.inv.app Y) ≫ adj₂.counit.app (iD.obj Y))
    (α : L₂' ⟶ L₁') (β : L₂ ⟶ L₁)
    (h : ∀ X : C, α.app (iC.obj X) ≫ c₁.hom.app X = c₂.hom.app X ≫ iD.map (β.app X)) :
    d₁.hom ≫ Functor.whiskerRight (conjugateEquiv a₁ a₂ β) iC =
      Functor.whiskerLeft iD (conjugateEquiv adj₁ adj₂ α) ≫ d₂.hom :=
  NatTrans.ext (funext fun Y ↦
    conjugateEquiv_of_counit_comm_app adj₁ adj₂ a₁ a₂ c₁ d₁ c₂ d₂ hc₁ hc₂ α β h Y)

end Conjugate

section Restrict

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {C' : Type u₃} [Category.{v₃} C'] {D' : Type u₄} [Category.{v₄} D']
  {iC : C ⥤ C'} {iD : D ⥤ D'}
  {L' : C' ⥤ D'} {R' : D' ⥤ C'} {L : C ⥤ D} {R : D ⥤ C}

/-- **The counit correspondence holds for a restricted adjunction.** The counit of
`CategoryTheory.Adjunction.restrictFullyFaithful`, read through `iD`, is the counit of the
ambient adjunction conjugated by the two commutation isomorphisms. -/
theorem counit_comm_restrictFullyFaithful (adj : L' ⊣ R') (hiC : iC.FullyFaithful)
    (hiD : iD.FullyFaithful) (c : iC ⋙ L' ≅ L ⋙ iD) (d : iD ⋙ R' ≅ R ⋙ iC) (Y : D) :
    c.hom.app (R.obj Y) ≫
        iD.map ((adj.restrictFullyFaithful hiC hiD c d).counit.app Y) =
      L'.map (d.inv.app Y) ≫ adj.counit.app (iD.obj Y) := by
  rw [Adjunction.map_restrictFullyFaithful_counit_app]
  simp

end Restrict

section Comp

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {C' : Type u₄} [Category.{v₄} C']
  {D' : Type u₅} [Category.{v₅} D'] {E' : Type u₆} [Category.{v₆} E']
  {iC : C ⥤ C'} {iD : D ⥤ D'} {iE : E ⥤ E'}
  {LA : C ⥤ D} {RA : D ⥤ C} {LA' : C' ⥤ D'} {RA' : D' ⥤ C'}
  {LB : D ⥤ E} {RB : E ⥤ D} {LB' : D' ⥤ E'} {RB' : E' ⥤ D'}

/-- **The counit correspondence is stable under composition of adjunctions.** If `aA` and `aB`
correspond on counits to `adjA` and `adjB` through the given commutation isomorphisms, then
`aA.comp aB` corresponds on counits to `adjA.comp adjB` through the composite commutation
isomorphisms. -/
theorem counit_comm_comp (adjA : LA' ⊣ RA') (adjB : LB' ⊣ RB') (aA : LA ⊣ RA) (aB : LB ⊣ RB)
    (cA : iC ⋙ LA' ≅ LA ⋙ iD) (dA : iD ⋙ RA' ≅ RA ⋙ iC)
    (cB : iD ⋙ LB' ≅ LB ⋙ iE) (dB : iE ⋙ RB' ≅ RB ⋙ iD)
    (hA : ∀ Y : D, cA.hom.app (RA.obj Y) ≫ iD.map (aA.counit.app Y) =
      LA'.map (dA.inv.app Y) ≫ adjA.counit.app (iD.obj Y))
    (hB : ∀ Z : E, cB.hom.app (RB.obj Z) ≫ iE.map (aB.counit.app Z) =
      LB'.map (dB.inv.app Z) ≫ adjB.counit.app (iE.obj Z))
    (Z : E) :
    (commIsoComp cA cB).hom.app ((RB ⋙ RA).obj Z) ≫
        iE.map ((aA.comp aB).counit.app Z) =
      (LA' ⋙ LB').map ((commIsoComp dB dA).inv.app Z) ≫
        (adjA.comp adjB).counit.app (iE.obj Z) := by
  have nB := cB.hom.naturality (aA.counit.app (RB.obj Z))
  dsimp at nB
  simp only [commIsoComp_hom_app, commIsoComp_inv_app, Adjunction.comp_counit_app,
    Functor.comp_obj, Functor.comp_map, Functor.map_comp, assoc]
  rw [← reassoc_of% nB, ← Functor.map_comp_assoc LB', hA (RB.obj Z), Functor.map_comp, assoc,
    hB Z, ← Functor.map_comp_assoc LB', ← Functor.map_comp_assoc LB',
    ← Functor.map_comp_assoc LB', ← Functor.map_comp_assoc LB']
  refine congrArg (fun t ↦ LB'.map t ≫ adjB.counit.app (iE.obj Z)) ?_
  have hn := adjA.counit.naturality (dB.inv.app Z)
  dsimp at hn
  rw [assoc, assoc, ← hn]

end Comp

section RestrictConjugate

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {C' : Type u₃} [Category.{v₃} C'] {D' : Type u₄} [Category.{v₄} D']
  {iC : C ⥤ C'} {iD : D ⥤ D'}
  {L₁' L₂' : C' ⥤ D'} {R₁' R₂' : D' ⥤ C'} {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
  (adj₁ : L₁' ⊣ R₁') (adj₂ : L₂' ⊣ R₂')
  (hiC : iC.FullyFaithful) (hiD : iD.FullyFaithful)
  (c₁ : iC ⋙ L₁' ≅ L₁ ⋙ iD) (d₁ : iD ⋙ R₁' ≅ R₁ ⋙ iC)
  (c₂ : iC ⋙ L₂' ≅ L₂ ⋙ iD) (d₂ : iD ⋙ R₂' ≅ R₂ ⋙ iC)

/-- **Restriction of an adjunction along fully faithful functors preserves adjoint mates.**
If `α : L₂' ⟶ L₁'` and `β : L₂ ⟶ L₁` agree through the commutation isomorphisms of the left
adjoints, then the mate of `α` and the mate of `β` agree through the commutation isomorphisms
of the right adjoints. -/
theorem conjugateEquiv_restrictFullyFaithful_app (α : L₂' ⟶ L₁') (β : L₂ ⟶ L₁)
    (h : ∀ X : C, α.app (iC.obj X) ≫ c₁.hom.app X = c₂.hom.app X ≫ iD.map (β.app X))
    (Y : D) :
    d₁.hom.app Y ≫ iC.map ((conjugateEquiv (adj₁.restrictFullyFaithful hiC hiD c₁ d₁)
        (adj₂.restrictFullyFaithful hiC hiD c₂ d₂) β).app Y) =
      (conjugateEquiv adj₁ adj₂ α).app (iD.obj Y) ≫ d₂.hom.app Y :=
  conjugateEquiv_of_counit_comm_app adj₁ adj₂ _ _ c₁ d₁ c₂ d₂
    (counit_comm_restrictFullyFaithful adj₁ hiC hiD c₁ d₁)
    (counit_comm_restrictFullyFaithful adj₂ hiC hiD c₂ d₂) α β h Y

end RestrictConjugate

end CategoryTheory

end
