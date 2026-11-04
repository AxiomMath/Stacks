module

public import StacksFrontier.CategoryTheory.Adjunction.ConjugateNaturality

/-!
# Transporting adjunctions along equivalences, and the retypings that come with it

An adjunction `L ⊣ R` between two categories can be *conjugated* by equivalences of those
categories: composing with the adjunction of each equivalence gives an adjunction
`(d.inverse ⋙ L) ⋙ e.functor ⊣ e.inverse ⋙ (R ⋙ d.functor)`.  That is how a morphism of
topoi is transported along a comparison equivalence, and how the adjunctions on the small
étale topoi of an algebraic space are obtained from those on the spaces-étale topoi.

Working with such transports means constantly rewriting an adjunction along an isomorphism of
one of its two adjoints — `CategoryTheory.Adjunction.ofNatIsoLeft` and
`CategoryTheory.Adjunction.ofNatIsoRight` — and asking what those retypings do to the adjoint
mate.  This file collects the bookkeeping.

Two neighbouring facts are already in the draft and are not duplicated here: associativity of
`CategoryTheory.Adjunction.comp` is `CategoryTheory.Adjunction.comp_assoc` in
`StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentationForkInverseImage`, and the
effect of retyping the left adjoints on the mate bijection is
`Stacks.CategoryTheory.conjugateEquiv_ofNatIsoLeft` in
`StacksFrontier.CategoryTheory.Sites.SemiRepresentable.PushPullNaturality`.

## Main results

* `CategoryTheory.Adjunction.ofNatIsoLeft_trans`,
  `CategoryTheory.Adjunction.ofNatIsoRight_trans`: two successive retypings are the retyping
  along the composite isomorphism.
* `CategoryTheory.Adjunction.comp_ofNatIsoLeft_left`,
  `CategoryTheory.Adjunction.comp_ofNatIsoLeft_right`,
  `CategoryTheory.Adjunction.comp_ofNatIsoRight_left`,
  `CategoryTheory.Adjunction.comp_ofNatIsoRight_right`: a retyping of one factor of a
  composite of adjunctions is a retyping of the composite along the whiskered isomorphism.
* `CategoryTheory.Adjunction.eq_of_leftAdjointUniq_eq`: two adjunctions with the same left and
  the same right adjoint are equal as soon as their comparisons with one and the same third
  adjunction agree.  This is the form in which a statement about comparison isomorphisms is
  turned back into a statement about adjunctions.
* `CategoryTheory.conjugateEquiv_conj`: **conjugating two adjunctions by one and the same pair
  of equivalences whiskers their mates and does nothing else.**
* `CategoryTheory.conjugateEquiv_comp_equivalence`: **the mate of the unit of an equivalence
  inserted after an adjunction is the inverse unit of that equivalence.**  This is the one
  non-formal ingredient of the transport of a *composite* of adjunctions: the composite of two
  conjugated adjunctions is the conjugate of the composite with an `e.functor ⋙ e.inverse`
  inserted in the middle, and this lemma is what cancels it.
* `CategoryTheory.conjugateEquiv_transport_comp`: **the composite of two conjugated adjunctions
  is the conjugate of the composite**, read on mates: the mate of a transformation of the
  composite left adjoints, conjugated and with the middle equivalence inserted, is the mate
  downstairs, preceded by the inverse unit of that equivalence.
* `CategoryTheory.conjugateEquiv_transport_comp_ofNatIsoLeft`: the same with each conjugated
  adjunction read through an isomorphism of its left adjoint, which is how a transport presents
  a left adjoint that is available in a strict form of its own.

## Implementation notes

`CategoryTheory.conjugateEquiv_transport_comp_ofNatIsoLeft` has to move the three retypings
`CategoryTheory.Adjunction.ofNatIsoLeft` out of a mate.  The general statement that does this
is `Stacks.CategoryTheory.conjugateEquiv_ofNatIsoLeft`, which lives in a file about sites that
this one must not import, so the instance of it needed here is proved in place, by the same
`ext`-and-`simp` on the units and counits.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory.Adjunction

universe v₀ v₁ v₂ v₃ u₀ u₁ u₂ u₃

variable {C₀ : Type u₀} [Category.{v₀} C₀] {C₁ : Type u₁} [Category.{v₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] {C₃ : Type u₃} [Category.{v₃} C₃]

/-- Two adjunctions with the same adjoints are equal as soon as their units agree componentwise. -/
private theorem ext_of_unit_app {F : C₀ ⥤ C₁} {G : C₁ ⥤ C₀} {a b : F ⊣ G}
    (h : ∀ X, a.unit.app X = b.unit.app X) : a = b :=
  Adjunction.ext (NatTrans.ext (funext h))

/-- Two successive retypings of the left adjoint are the retyping along the composite. -/
theorem ofNatIsoLeft_trans {F F' F'' : C₀ ⥤ C₁} {G : C₁ ⥤ C₀} (a : F ⊣ G)
    (i : F ≅ F') (i' : F' ≅ F'') :
    (a.ofNatIsoLeft i).ofNatIsoLeft i' = a.ofNatIsoLeft (i ≪≫ i') := by
  refine ext_of_unit_app fun X => ?_
  simp [Adjunction.ofNatIsoLeft]

/-- Two successive retypings of the right adjoint are the retyping along the composite. -/
theorem ofNatIsoRight_trans {F : C₀ ⥤ C₁} {G G' G'' : C₁ ⥤ C₀} (a : F ⊣ G)
    (i : G ≅ G') (i' : G' ≅ G'') :
    (a.ofNatIsoRight i).ofNatIsoRight i' = a.ofNatIsoRight (i ≪≫ i') := by
  refine ext_of_unit_app fun X => ?_
  simp [Adjunction.ofNatIsoRight]

/-- Retyping the left adjoint of the first factor of a composite of adjunctions. -/
theorem comp_ofNatIsoLeft_left {F F' : C₀ ⥤ C₁} {G : C₁ ⥤ C₀} {H : C₁ ⥤ C₂} {I : C₂ ⥤ C₁}
    (a : F ⊣ G) (b : H ⊣ I) (j : F ≅ F') :
    (a.ofNatIsoLeft j).comp b = (a.comp b).ofNatIsoLeft (Functor.isoWhiskerRight j H) := by
  refine ext_of_unit_app fun X => ?_
  simp only [comp_unit_app, ofNatIsoLeft_unit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.comp_map, Category.assoc, ← Functor.map_comp]
  exact congrArg (fun t => a.unit.app X ≫ G.map t) (b.unit.naturality (j.hom.app X))

/-- Retyping the left adjoint of the second factor of a composite of adjunctions. -/
theorem comp_ofNatIsoLeft_right {F : C₀ ⥤ C₁} {G : C₁ ⥤ C₀} {H H' : C₁ ⥤ C₂} {I : C₂ ⥤ C₁}
    (a : F ⊣ G) (b : H ⊣ I) (i : H ≅ H') :
    a.comp (b.ofNatIsoLeft i) = (a.comp b).ofNatIsoLeft (Functor.isoWhiskerLeft F i) := by
  refine ext_of_unit_app fun X => ?_
  simp [comp_unit_app, Adjunction.ofNatIsoLeft]

/-- Retyping the right adjoint of the first factor of a composite of adjunctions. -/
theorem comp_ofNatIsoRight_left {F : C₀ ⥤ C₁} {G G' : C₁ ⥤ C₀} {H : C₁ ⥤ C₂} {I : C₂ ⥤ C₁}
    (a : F ⊣ G) (b : H ⊣ I) (j : G ≅ G') :
    (a.ofNatIsoRight j).comp b = (a.comp b).ofNatIsoRight (Functor.isoWhiskerLeft I j) := by
  refine ext_of_unit_app fun X => ?_
  simp [comp_unit_app, Adjunction.ofNatIsoRight]

/-- Retyping the right adjoint of the second factor of a composite of adjunctions. -/
theorem comp_ofNatIsoRight_right {F : C₀ ⥤ C₁} {G : C₁ ⥤ C₀} {H : C₁ ⥤ C₂} {I I' : C₂ ⥤ C₁}
    (a : F ⊣ G) (b : H ⊣ I) (i : I ≅ I') :
    a.comp (b.ofNatIsoRight i) = (a.comp b).ofNatIsoRight (Functor.isoWhiskerRight i G) := by
  refine ext_of_unit_app fun X => ?_
  simp [comp_unit_app, Adjunction.ofNatIsoRight]

/-- **An adjunction is determined by its comparison with another left adjoint of its right
adjoint.**  The unit of the second adjunction is the unit of the first followed by the
comparison, so two adjunctions with the same adjoints and the same comparison with a third one
have the same unit. -/
theorem eq_of_leftAdjointUniq_eq {N L : C₀ ⥤ C₁} {R : C₁ ⥤ C₀} (a : N ⊣ R)
    {b b' : L ⊣ R} (h : leftAdjointUniq a b = leftAdjointUniq a b') : b = b' := by
  refine ext_of_unit_app fun X => ?_
  rw [← unit_leftAdjointUniq_hom_app a b, ← unit_leftAdjointUniq_hom_app a b', h]

end CategoryTheory.Adjunction

namespace CategoryTheory

universe v₀ v₁ v₂ v₃ u₀ u₁ u₂ u₃

variable {C₀ : Type u₀} [Category.{v₀} C₀] {C₁ : Type u₁} [Category.{v₁} C₁]

/-- **The mate of the unit of an equivalence inserted after an adjunction is the inverse unit
of that equivalence.**

Composing an adjunction `a : L ⊣ R` with the adjunction `e.functor ⋙ e.inverse ⊣
e.functor ⋙ e.inverse` obtained from an equivalence `e` and its inverse changes neither of the
two adjoints up to the unit isomorphism of `e`, and the comparison on the left side is mated
to the comparison on the right side. -/
theorem conjugateEquiv_comp_equivalence {D : Type u₂} [Category.{v₂} D] (e : C₁ ≌ D)
    {L : C₀ ⥤ C₁} {R : C₁ ⥤ C₀} (a : L ⊣ R) :
    conjugateEquiv (a.comp (e.toAdjunction.comp e.symm.toAdjunction)) a
        (Functor.whiskerLeft L e.unit) =
      Functor.whiskerRight e.unitIso.inv R := by
  ext Y
  simp only [Equivalence.symm_inverse, comp_obj, Equivalence.symm_functor,
    Equivalence.toAdjunction, Equivalence.symm_unit, Equivalence.symm_counit,
    conjugateEquiv_apply_app, whiskerLeft_app, Adjunction.comp_counit_app, Functor.comp_map,
    Equivalence.inv_fun_map, id_obj, Category.assoc, Equivalence.unit_inverse_comp_assoc,
    ← map_comp, Iso.hom_inv_id_app_assoc, whiskerRight_app]
  rw [Functor.map_comp, a.right_triangle_components_assoc]

/-- **Conjugating two adjunctions by one and the same pair of equivalences whiskers their
mates and does nothing else.** -/
theorem conjugateEquiv_conj {DX : Type u₂} [Category.{v₂} DX] {DY : Type u₃} [Category.{v₃} DY]
    (e : C₀ ≌ DX) (d : C₁ ≌ DY) {L₁ L₂ : C₁ ⥤ C₀} {R₁ R₂ : C₀ ⥤ C₁}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (τ : L₂ ⟶ L₁) :
    conjugateEquiv ((d.symm.toAdjunction.comp a₁).comp e.toAdjunction)
        ((d.symm.toAdjunction.comp a₂).comp e.toAdjunction)
        (Functor.whiskerRight (Functor.whiskerLeft d.inverse τ) e.functor) =
      Functor.whiskerLeft e.inverse
        (Functor.whiskerRight (conjugateEquiv a₁ a₂ τ) d.functor) := by
  rw [conjugateEquiv_whiskerRight]
  exact congrArg (Functor.whiskerLeft e.inverse)
    (conjugateEquiv_whiskerLeft a₁ a₂ d.symm.toAdjunction τ)

section TransportComp

variable {A₀ : Type u₀} [Category.{v₀} A₀] {A₁ : Type u₁} [Category.{v₁} A₁]
  {A₂ : Type u₂} [Category.{v₂} A₂] {B₀ : Type*} [Category* B₀] {B₁ : Type*} [Category* B₁]
  {B₂ : Type*} [Category* B₂]

/-- **The composite of two conjugated adjunctions is the conjugate of the composite**, on
mates.

Let `ak`, `al` and `am` be adjunctions between three categories `A₂ ⥤ A₁ ⥤ A₀` and let `τ`
compare the left adjoint of `am` with the composite of those of `al` and `ak`.  Conjugating by
equivalences `e₀`, `e₁`, `e₂` and composing inserts `e₁.functor ⋙ e₁.inverse` in the middle;
the comparison of the two composite left adjoints is therefore `τ`, conjugated, followed by
the unit of `e₁`.  Its mate is the mate of `τ`, conjugated, preceded by the inverse unit of
`e₁` — the composition comparison of the transported right adjoints.

The two inputs are `CategoryTheory.conjugateEquiv_conj`, which peels the two outer
equivalences, and `CategoryTheory.conjugateEquiv_comp_equivalence`, which cancels the inserted
middle one. -/
theorem conjugateEquiv_transport_comp (e₀ : A₀ ≌ B₀) (e₁ : A₁ ≌ B₁) (e₂ : A₂ ≌ B₂)
    {Pk : A₁ ⥤ A₀} {Qk : A₀ ⥤ A₁} {Pl : A₂ ⥤ A₁} {Ql : A₁ ⥤ A₂}
    {Pm : A₂ ⥤ A₀} {Qm : A₀ ⥤ A₂}
    (ak : Pk ⊣ Qk) (al : Pl ⊣ Ql) (am : Pm ⊣ Qm) (τ : Pm ⟶ Pl ⋙ Pk) :
    conjugateEquiv
        (((e₂.symm.toAdjunction.comp al).comp e₁.toAdjunction).comp
          ((e₁.symm.toAdjunction.comp ak).comp e₀.toAdjunction))
        ((e₂.symm.toAdjunction.comp am).comp e₀.toAdjunction)
        (Functor.whiskerRight (Functor.whiskerLeft e₂.inverse τ) e₀.functor ≫
          Functor.whiskerLeft (e₂.inverse ⋙ Pl)
            (Functor.whiskerRight e₁.unit (Pk ⋙ e₀.functor))) =
      Functor.whiskerLeft (e₀.inverse ⋙ Qk)
          (Functor.whiskerRight e₁.unitIso.inv (Ql ⋙ e₂.functor)) ≫
        Functor.whiskerLeft e₀.inverse
          (Functor.whiskerRight (conjugateEquiv (al.comp ak) am τ) e₂.functor) := by
  have hassoc : ((e₂.symm.toAdjunction.comp al).comp e₁.toAdjunction).comp
        ((e₁.symm.toAdjunction.comp ak).comp e₀.toAdjunction) =
      (e₂.symm.toAdjunction.comp
        ((al.comp (e₁.toAdjunction.comp e₁.symm.toAdjunction)).comp ak)).comp
          e₀.toAdjunction := by
    refine Adjunction.ext_of_unit_app fun M => ?_
    simp [Adjunction.comp, Equivalence.toAdjunction]
  have hsplit := conjugateEquiv_comp
    (((e₂.symm.toAdjunction.comp al).comp e₁.toAdjunction).comp
      ((e₁.symm.toAdjunction.comp ak).comp e₀.toAdjunction))
    ((e₂.symm.toAdjunction.comp (al.comp ak)).comp e₀.toAdjunction)
    ((e₂.symm.toAdjunction.comp am).comp e₀.toAdjunction)
    (Functor.whiskerLeft (e₂.inverse ⋙ Pl)
      (Functor.whiskerRight e₁.unit (Pk ⋙ e₀.functor)))
    (Functor.whiskerRight (Functor.whiskerLeft e₂.inverse τ) e₀.functor)
  rw [← hsplit, conjugateEquiv_conj e₀ e₂ (al.comp ak) am τ, hassoc]
  congr 1
  have hrfl : Functor.whiskerLeft (e₂.inverse ⋙ Pl)
        (Functor.whiskerRight e₁.unit (Pk ⋙ e₀.functor)) =
      Functor.whiskerRight (Functor.whiskerLeft e₂.inverse
        (Functor.whiskerRight (Functor.whiskerLeft Pl e₁.unit) Pk)) e₀.functor := rfl
  rw [hrfl,
    conjugateEquiv_conj e₀ e₂ ((al.comp (e₁.toAdjunction.comp e₁.symm.toAdjunction)).comp ak)
      (al.comp ak) (Functor.whiskerRight (Functor.whiskerLeft Pl e₁.unit) Pk),
    conjugateEquiv_whiskerRight (al.comp (e₁.toAdjunction.comp e₁.symm.toAdjunction)) al ak
      (Functor.whiskerLeft Pl e₁.unit),
    conjugateEquiv_comp_equivalence e₁ al]
  rfl

/-- `CategoryTheory.conjugateEquiv_transport_comp` with each of the three conjugated
adjunctions read through an isomorphism `ι` of its left adjoint.

A transport usually presents its left adjoint in a form of its own — here the `Sk`, `Sl`, `Sm`
— and the three retypings then have to be moved out of the mate, which replaces the
transformation `σ` of those forms by the transformation of the conjugated left adjoints that
`hσ` names. -/
theorem conjugateEquiv_transport_comp_ofNatIsoLeft (e₀ : A₀ ≌ B₀) (e₁ : A₁ ≌ B₁) (e₂ : A₂ ≌ B₂)
    {Pk : A₁ ⥤ A₀} {Qk : A₀ ⥤ A₁} {Pl : A₂ ⥤ A₁} {Ql : A₁ ⥤ A₂}
    {Pm : A₂ ⥤ A₀} {Qm : A₀ ⥤ A₂}
    (ak : Pk ⊣ Qk) (al : Pl ⊣ Ql) (am : Pm ⊣ Qm) (τ : Pm ⟶ Pl ⋙ Pk)
    {Sk : B₁ ⥤ B₀} {Sl : B₂ ⥤ B₁} {Sm : B₂ ⥤ B₀}
    (ιk : (e₁.inverse ⋙ Pk) ⋙ e₀.functor ≅ Sk)
    (ιl : (e₂.inverse ⋙ Pl) ⋙ e₁.functor ≅ Sl)
    (ιm : (e₂.inverse ⋙ Pm) ⋙ e₀.functor ≅ Sm)
    (σ : Sm ⟶ Sl ⋙ Sk)
    (hσ : ιm.hom ≫ σ ≫
        (Functor.isoWhiskerLeft ((e₂.inverse ⋙ Pl) ⋙ e₁.functor) ιk ≪≫
          Functor.isoWhiskerRight ιl Sk).inv =
      Functor.whiskerRight (Functor.whiskerLeft e₂.inverse τ) e₀.functor ≫
        Functor.whiskerLeft (e₂.inverse ⋙ Pl)
          (Functor.whiskerRight e₁.unit (Pk ⋙ e₀.functor))) :
    conjugateEquiv
        ((((e₂.symm.toAdjunction.comp al).comp e₁.toAdjunction).ofNatIsoLeft ιl).comp
          (((e₁.symm.toAdjunction.comp ak).comp e₀.toAdjunction).ofNatIsoLeft ιk))
        (((e₂.symm.toAdjunction.comp am).comp e₀.toAdjunction).ofNatIsoLeft ιm) σ =
      Functor.whiskerLeft (e₀.inverse ⋙ Qk)
          (Functor.whiskerRight e₁.unitIso.inv (Ql ⋙ e₂.functor)) ≫
        Functor.whiskerLeft e₀.inverse
          (Functor.whiskerRight (conjugateEquiv (al.comp ak) am τ) e₂.functor) := by
  rw [Adjunction.comp_ofNatIsoLeft_left, Adjunction.comp_ofNatIsoLeft_right,
    Adjunction.ofNatIsoLeft_trans]
  refine Eq.trans ?_ (conjugateEquiv_transport_comp e₀ e₁ e₂ ak al am τ)
  rw [← hσ]
  ext d
  simp only [conjugateEquiv_apply_app, Adjunction.ofNatIsoLeft_unit,
    Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
  rfl

end TransportComp

end CategoryTheory

end
