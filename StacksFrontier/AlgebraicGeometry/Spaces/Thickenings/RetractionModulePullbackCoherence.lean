module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Unique
public import StacksFrontier.CategoryTheory.Adjunction.LeftAdjointUniqPasting

/-!
# The coherence of comparisons of left adjoints, checked on right adjoints

For the module-level coherence `MC` of the proof of `toLift_pullback` in Stacks 0DLL: a comparison
`Lg ⋙ LW ⟶ LV` of left adjoints agrees with a composite of four comparisons of left adjoints
through `Lg ⋙ EW ⋙ Is`, `EV ⋙ Hs ⋙ Is` and `EV ⋙ Js` as soon as the conjugate comparisons of
right adjoints compose correctly
(`AlgebraicGeometry.Space.squareZeroLeftAdjoint_coherence_of_conjugateEquiv`). Every comparison
met there is a `CategoryTheory.Adjunction.leftAdjointUniq` of an adjunction transported along an
isomorphism of right adjoints, whose conjugate is that isomorphism
(`Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom`).

Nothing here is registered.

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Space

variable {A B C MV MW : Type*} [Category* A] [Category* B] [Category* C] [Category* MV]
  [Category* MW]
  {Lg : A ⥤ B} {Rg : B ⥤ A} (ag : Lg ⊣ Rg) {LW : B ⥤ C} {RW : C ⥤ B} (aW : LW ⊣ RW)
  {LV : A ⥤ C} {RV : C ⥤ A} (aV : LV ⊣ RV)
  {EV : A ⥤ MV} {EV' : MV ⥤ A} (eV : EV ⊣ EV') {EW : B ⥤ MW} {EW' : MW ⥤ B} (eW : EW ⊣ EW')
  {Hs : MV ⥤ MW} {Hp : MW ⥤ MV} (h : Hs ⊣ Hp) {Is : MW ⥤ C} {Ip : C ⥤ MW} (iw : Is ⊣ Ip)
  {Js : MV ⥤ C} {Jp : C ⥤ MV} (iv : Js ⊣ Jp)

/-- **The coherence of comparisons of left adjoints is checked on the right adjoints**: a
comparison `cI : Lg ⋙ LW ⟶ LV` equals the composite of comparisons
`Lg ⋙ LW ⟶ Lg ⋙ EW ⋙ Is ⟶ EV ⋙ Hs ⋙ Is ⟶ EV ⋙ Js ⟶ LV` as soon as their conjugates, the
corresponding comparisons of right adjoints, compose correctly. -/
theorem squareZeroLeftAdjoint_coherence_of_conjugateEquiv (cI : Lg ⋙ LW ⟶ LV) (sWi : LW ⟶ EW ⋙ Is)
    (G2i : Lg ⋙ EW ⟶ EV ⋙ Hs) (τ : Hs ⋙ Is ⟶ Js) (sV : EV ⋙ Js ⟶ LV)
    {ρ : RV ⟶ RW ⋙ Rg} {σW : Ip ⋙ EW' ⟶ RW} {γ : Hp ⋙ EV' ⟶ EW' ⋙ Rg} {π : Jp ⟶ Ip ⋙ Hp}
    {σV : RV ⟶ Jp ⋙ EV'}
    (hcI : conjugateEquiv aV (ag.comp aW) cI = ρ)
    (hsW : conjugateEquiv (eW.comp iw) aW sWi = σW)
    (hG2 : conjugateEquiv (eV.comp h) (ag.comp eW) G2i = γ)
    (hτ : conjugateEquiv iv (h.comp iw) τ = π)
    (hsV : conjugateEquiv aV (eV.comp iv) sV = σV)
    (hR : σV ≫ Functor.whiskerRight π EV' ≫ Functor.whiskerLeft Ip γ ≫
      Functor.whiskerRight σW Rg = ρ) :
    cI = Functor.whiskerLeft Lg sWi ≫ Functor.whiskerRight G2i Is ≫
      Functor.whiskerLeft EV τ ≫ sV := by
  apply (conjugateEquiv aV (ag.comp aW)).injective
  have e1 : Functor.whiskerLeft Lg sWi ≫ Functor.whiskerRight G2i Is ≫
      Functor.whiskerLeft EV τ ≫ sV =
    ((((Functor.whiskerLeft Lg sWi ≫ (Functor.associator _ _ _).inv) ≫
      Functor.whiskerRight G2i Is) ≫
      (Functor.associator _ _ _).hom) ≫ Functor.whiskerLeft EV τ) ≫ sV := by
    ext X
    simp
  rw [e1, hcI, ← hR, ← conjugateEquiv_comp aV (eV.comp iv) _ sV,
    ← conjugateEquiv_comp (eV.comp iv) (eV.comp (h.comp iw)) _ (Functor.whiskerLeft EV τ),
    ← conjugateEquiv_comp (eV.comp (h.comp iw)) ((eV.comp h).comp iw) _
      (Functor.associator _ _ _).hom,
    ← conjugateEquiv_comp ((eV.comp h).comp iw) ((ag.comp eW).comp iw) _
      (Functor.whiskerRight G2i Is),
    ← conjugateEquiv_comp ((ag.comp eW).comp iw) (ag.comp (eW.comp iw)) _
      (Functor.associator _ _ _).inv,
    conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight, conjugateEquiv_whiskerLeft,
    conjugateEquiv_associator_hom,
    Stacks.CategoryTheory.LeftAdjointUniqPasting.conjugateEquiv_associator_inv, hsW, hG2, hτ, hsV]
  ext X
  simp

end AlgebraicGeometry.Space
