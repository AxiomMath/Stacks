module

public import Mathlib.CategoryTheory.Shift.CommShift

/-!
# Detecting the commutation of a natural transformation with the shift

Let `F, G : 𝒞 ⥤ 𝒟` be two functors between categories with a shift by a monoid `M`, each
commuting with the shift, and let `η : F ⟶ G`. The class
`CategoryTheory.NatTrans.CommShift η M` records the single equation

`(F.commShiftIso a).hom ≫ η⟦a⟧ = η_{-⟦a⟧} ≫ (G.commShiftIso a).hom`

for every `a : M`. This file gives criteria reducing that equation to one already known.

## Main results

* `CategoryTheory.NatTrans.commShift_of_whiskerLeft`: the equation may be tested after
  restriction along an essentially surjective functor which commutes with the shift.
* `CategoryTheory.NatTrans.commShift_of_whiskerRight`: the equation may be tested after
  whiskering with a faithful functor which commutes with the shift.
* `CategoryTheory.NatTrans.commShift_of_eq_conj`: a transformation which is the conjugate of a
  shift-compatible one by two shift-compatible isomorphisms is itself shift-compatible.
* `CategoryTheory.NatTrans.commShift_of_eq`: a transformation equal to a shift-compatible one is
  shift-compatible.
* `CategoryTheory.NatTrans.ext_of_essSurj`: an equality of natural transformations is detected
  on the image of an essentially surjective functor.
-/

@[expose] public section

universe v u v' u' v'' u''

namespace CategoryTheory.NatTrans

/-- **An equality of natural transformations is detected on the image of an essentially
surjective functor**. -/
theorem ext_of_essSurj {V : Type u} [Category.{v} V] {H : Type u'} [Category.{v'} H]
    {E : Type u''} [Category.{v''} E] (q : V ⥤ H) [q.EssSurj] {F G : H ⥤ E} {τ τ' : F ⟶ G}
    (h : ∀ X : V, τ.app (q.obj X) = τ'.app (q.obj X)) : τ = τ' := by
  refine NatTrans.ext (funext fun Y ↦ ?_)
  rw [← cancel_epi (F.map (q.objObjPreimageIso Y).hom), τ.naturality, τ'.naturality, h]

/-- **Commutation with the shift is detected after restriction along an essentially surjective
functor which commutes with the shift.** -/
theorem commShift_of_whiskerLeft {V : Type u} [Category.{v} V] {H : Type u'} [Category.{v'} H]
    {E : Type u''} [Category.{v''} E] {M : Type*} [AddMonoid M]
    [HasShift V M] [HasShift H M] [HasShift E M]
    (q : V ⥤ H) [q.EssSurj] [q.CommShift M]
    {F G : H ⥤ E} [F.CommShift M] [G.CommShift M] (η : F ⟶ G)
    (h : NatTrans.CommShift (Functor.whiskerLeft q η) M) :
    NatTrans.CommShift η M := by
  refine NatTrans.CommShift.of_core fun a ↦ ⟨ext_of_essSurj q fun X ↦ ?_⟩
  have hc := NatTrans.shift_app_comm (Functor.whiskerLeft q η) a X
  have hn := η.naturality ((q.commShiftIso a).hom.app X)
  dsimp at hc hn ⊢
  rw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_hom_app] at hc
  rw [← cancel_epi (F.map ((q.commShiftIso a).hom.app X)), ← Category.assoc, hc,
    ← Category.assoc, ← hn, Category.assoc]

/-- **Commutation with the shift is detected after whiskering with a faithful functor which
commutes with the shift.** -/
theorem commShift_of_whiskerRight {H : Type u} [Category.{v} H] {E : Type u'} [Category.{v'} E]
    {E' : Type u''} [Category.{v''} E'] {M : Type*} [AddMonoid M]
    [HasShift H M] [HasShift E M] [HasShift E' M]
    {F G : H ⥤ E} [F.CommShift M] [G.CommShift M] (η : F ⟶ G)
    (ι : E ⥤ E') [ι.Faithful] [ι.CommShift M]
    (h : NatTrans.CommShift (Functor.whiskerRight η ι) M) :
    NatTrans.CommShift η M := by
  refine NatTrans.CommShift.of_core fun a ↦ ⟨NatTrans.ext (funext fun K ↦ ι.map_injective ?_)⟩
  have hc := NatTrans.shift_app_comm (Functor.whiskerRight η ι) a K
  have hn := (ι.commShiftIso a).hom.naturality (η.app K)
  dsimp at hc hn ⊢
  rw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_hom_app] at hc
  rw [ι.map_comp, ι.map_comp, ← cancel_mono ((ι.commShiftIso a).hom.app (G.obj K)),
    Category.assoc, Category.assoc, hn]
  simpa only [Category.assoc] using hc

/-- **The conjugate of a shift-compatible transformation by two shift-compatible isomorphisms is
shift-compatible.** -/
theorem commShift_of_eq_conj {H : Type u} [Category.{v} H] {E : Type u'} [Category.{v'} E]
    {M : Type*} [AddMonoid M] [HasShift H M] [HasShift E M]
    {F₁ F₂ G₁ G₂ : H ⥤ E} [F₁.CommShift M] [F₂.CommShift M] [G₁.CommShift M] [G₂.CommShift M]
    (eF : F₁ ≅ F₂) (eG : G₁ ≅ G₂) [NatTrans.CommShift eF.hom M] [NatTrans.CommShift eG.hom M]
    {η : F₁ ⟶ G₁} (θ : F₂ ⟶ G₂) [NatTrans.CommShift θ M]
    (h : η = eF.hom ≫ θ ≫ eG.inv) : NatTrans.CommShift η M := by
  subst h
  infer_instance

/-- **A transformation equal to a shift-compatible one is shift-compatible.** -/
theorem commShift_of_eq {H : Type u} [Category.{v} H] {E : Type u'} [Category.{v'} E]
    {M : Type*} [AddMonoid M] [HasShift H M] [HasShift E M]
    {F G : H ⥤ E} [F.CommShift M] [G.CommShift M] {η θ : F ⟶ G}
    [NatTrans.CommShift θ M] (h : η = θ) : NatTrans.CommShift η M := by
  subst h
  infer_instance

end CategoryTheory.NatTrans

end
