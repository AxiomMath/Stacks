module

public import StacksFrontier.CategoryTheory.Shift.DetectingCommShift

/-!
# Shift-compatibility of a transformation conjugate to an ambient one

* `CategoryTheory.NatTrans.commShift_of_conj_app` and
  `CategoryTheory.NatTrans.commShift_of_conj_lift`: a transformation between functors into a
  subcategory is shift-compatible when, after the inclusion, its components are those of a
  shift-compatible ambient transformation conjugated by shift-compatible comparison isomorphisms.
  Their instance arguments are named, so that they can be supplied explicitly when the ambient
  functors are spelled in two ways.

Both reduce, through `CategoryTheory.NatTrans.commShift_of_whiskerRight`, to the criteria of
`StacksFrontier.CategoryTheory.Shift.DetectingCommShift`.
-/

@[expose] public section

universe v u v' u' v'' u''

namespace CategoryTheory.NatTrans

/-- **A transformation which, after a faithful functor commuting with the shift, is a
shift-compatible transformation conjugated by shift-compatible isomorphisms, is
shift-compatible.** This is the form in which a transformation between functors into a full
subcategory is compared with one between functors into the ambient category. -/
theorem commShift_of_conj_app {C : Type u} [Category.{v} C] {H : Type u'} [Category.{v'} H]
    {E : Type u''} [Category.{v''} E] {M : Type*} [AddMonoid M]
    [HasShift C M] [HasShift H M] [HasShift E M] (ι : H ⥤ E) [ι.Faithful] [ι.CommShift M]
    {F G : C ⥤ H} [hF : F.CommShift M] [hG : G.CommShift M] {F' G' : C ⥤ E}
    [hF' : F'.CommShift M] [hG' : G'.CommShift M] (eF : F ⋙ ι ≅ F') (eG : G ⋙ ι ≅ G')
    [heF : NatTrans.CommShift eF.hom M] [heG : NatTrans.CommShift eG.hom M] (θ : F' ⟶ G')
    [hθ : NatTrans.CommShift θ M] (τ : F ⟶ G)
    (h : ∀ K, ι.map (τ.app K) = eF.hom.app K ≫ θ.app K ≫ eG.inv.app K) :
    NatTrans.CommShift τ M := by
  refine commShift_of_whiskerRight τ ι ?_
  refine commShift_of_eq_conj eF eG θ ?_
  ext K
  simp [h K]

/-- **The square form of `CategoryTheory.NatTrans.commShift_of_conj_app`**: a transformation
`τ : T₁ ⋙ P ⟶ P ⋙ T₂` between functors into a subcategory, which after the inclusion `ι₂` is a
shift-compatible `β : T₁' ⋙ L ⟶ L ⋙ T₂'` between ambient functors conjugated by the
shift-compatible comparisons of `P`, `T₁`, `T₂` with `L`, `T₁'`, `T₂'`, is shift-compatible. -/
theorem commShift_of_conj_lift {C₁ C₂ D₁ D₂ : Type*}
    [Category C₁] [Category C₂] [Category D₁] [Category D₂] {M : Type*} [AddMonoid M]
    [HasShift C₁ M] [HasShift C₂ M] [HasShift D₁ M] [HasShift D₂ M]
    {ι₁ : C₁ ⥤ D₁} {ι₂ : C₂ ⥤ D₂} [ι₂.Faithful] {T₁ : C₁ ⥤ C₁} {P : C₁ ⥤ C₂} {T₂ : C₂ ⥤ C₂}
    {T₁' : D₁ ⥤ D₁} {L : D₁ ⥤ D₂} {T₂' : D₂ ⥤ D₂}
    [hι₁ : ι₁.CommShift M] [hι₂ : ι₂.CommShift M] [hT₁ : T₁.CommShift M] [hP : P.CommShift M]
    [hT₂ : T₂.CommShift M] [hT₁' : T₁'.CommShift M] [hL : L.CommShift M] [hT₂' : T₂'.CommShift M]
    (eP : P ⋙ ι₂ ≅ ι₁ ⋙ L) (e₁ : T₁ ⋙ ι₁ ≅ ι₁ ⋙ T₁') (e₂ : T₂ ⋙ ι₂ ≅ ι₂ ⋙ T₂')
    [heP : NatTrans.CommShift eP.hom M] [he₁ : NatTrans.CommShift e₁.hom M]
    [he₂ : NatTrans.CommShift e₂.hom M]
    (β : T₁' ⋙ L ⟶ L ⋙ T₂') [hβ : NatTrans.CommShift β M] (τ : T₁ ⋙ P ⟶ P ⋙ T₂)
    (h : ∀ K, ι₂.map (τ.app K) = eP.hom.app (T₁.obj K) ≫ L.map (e₁.hom.app K) ≫
      β.app (ι₁.obj K) ≫ T₂'.map (eP.inv.app K) ≫ e₂.inv.app (P.obj K)) :
    NatTrans.CommShift τ M := by
  refine commShift_of_whiskerRight _ ι₂ ?_
  have e : Functor.whiskerRight τ ι₂ =
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft T₁ eP.hom ≫
        (Functor.associator _ _ _).inv ≫ Functor.whiskerRight e₁.hom L ≫
          (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft ι₁ β ≫
            (Functor.associator _ _ _).inv ≫ Functor.whiskerRight eP.inv T₂' ≫
              (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft P e₂.inv ≫
                (Functor.associator _ _ _).inv := by
    ext K
    simp [h K]
  rw [e]
  infer_instance

end CategoryTheory.NatTrans

end
