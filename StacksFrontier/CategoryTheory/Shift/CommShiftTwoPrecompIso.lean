module

public import StacksFrontier.CategoryTheory.Shift.CommShiftTwoWhisker
public import StacksFrontier.CategoryTheory.Shift.DetectingCommShiftTwo
public import StacksFrontier.CategoryTheory.Shift.CommShiftTwoInv
public import StacksFrontier.CategoryTheory.Shift.CommShiftTwoPostcomp

/-!
# Restricting a bifunctor along isomorphic functors respects the shifts

Let `G : D ⥤ D ⥤ E` be a bifunctor commuting with the shifts in both variables, and let
`a ⋙ k` and `b ⋙ l` be two shift-compatible functors `C' ⥤ D`, each written as a composite, with
a shift-compatible isomorphism `e : a ⋙ k ≅ b ⋙ l`. Restricting `G` in both variables along
`a ⋙ k`, one factor at a time, and along `b ⋙ l` gives two bifunctors `C' ⥤ C' ⥤ E`, and `e`
induces an isomorphism between them with components `G(e X₁, e X₂)`. This file shows that this
isomorphism commutes with the shifts in both variables, for the commutation data
`CategoryTheory.Functor.CommShift₂.precomp₁` and `precomp₂` put on the two restrictions.

It is also recorded that `CategoryTheory.NatTrans.CommShift₂` is closed under composition across
a middle bifunctor whose commutation datum is written in two equal ways.

## Main results

* `CategoryTheory.NatTrans.CommShift₂.restrictBoth` and `restrictBothMap`: restriction of a
  bifunctor, and of a transformation of bifunctors, along one functor in both variables.
* `CategoryTheory.NatTrans.CommShift₂.precompPairIso`: the isomorphism induced by `e`.
* `CategoryTheory.NatTrans.CommShift₂.precompPairIso_commShift₂`: it commutes with the shifts
  in both variables.
* `CategoryTheory.NatTrans.CommShift₂.of_restrictBothMap`: a transformation of bifunctors whose
  restriction along an essentially surjective shift-compatible functor in both variables commutes
  with the shifts commutes with them itself.
* `CategoryTheory.NatTrans.CommShift₂.comp_of_eq_data`: composition of shift-compatible
  transformations of bifunctors across two equal data on the middle bifunctor.
-/

@[expose] public section

namespace CategoryTheory.NatTrans.CommShift₂

open Category _root_.CategoryTheory.Functor

variable {C' C C'' D E : Type*} [Category* C'] [Category* C] [Category* C''] [Category* D]
  [Category* E] {M : Type*} [AddCommMonoid M] [HasShift C' M] [HasShift C M] [HasShift C'' M]
  [HasShift D M] [HasShift E M]

/-- **Composition across two equal data on the middle bifunctor.** The class
`CategoryTheory.NatTrans.CommShift₂` receives the commutation data of the source and target as
instance arguments, so two shift-compatible transformations compose as soon as the datum on the
middle bifunctor is the same, even when it is reached by two routes. -/
theorem comp_of_eq_data {C₁ C₂ : Type*} [Category* C₁] [Category* C₂] [HasShift C₁ M]
    [HasShift C₂ M] {h : CommShift₂Setup E M} {G₁ G₂ G₃ : C₁ ⥤ C₂ ⥤ E}
    {d₁ : G₁.CommShift₂ h} {d₂ d₂' : G₂.CommShift₂ h} {d₃ : G₃.CommShift₂ h}
    (τ : G₁ ⟶ G₂) (τ' : G₂ ⟶ G₃)
    (hτ : letI := d₁; letI := d₂; NatTrans.CommShift₂ τ h)
    (hτ' : letI := d₂'; letI := d₃; NatTrans.CommShift₂ τ' h) (hd : d₂ = d₂') :
    letI := d₁; letI := d₃; NatTrans.CommShift₂ (τ ≫ τ') h := by
  subst hd
  infer_instance

/-- The restriction of a bifunctor `H` along `r` in both variables. Its commutation datum is
`CategoryTheory.Functor.CommShift₂.precomp₁` after `precomp₂`. -/
abbrev restrictBoth {A : Type*} [Category* A] (r : C' ⥤ A) (H : A ⥤ A ⥤ E) : C' ⥤ C' ⥤ E :=
  r ⋙ (H ⋙ (whiskeringLeft C' A E).obj r)

/-- The restriction of a transformation of bifunctors along `r` in both variables. It is
shift-compatible by `CategoryTheory.NatTrans.CommShift₂.whiskerLeft_precomp₁` after
`whiskerRight_precomp₂` as soon as the transformation is. -/
abbrev restrictBothMap {A : Type*} [Category* A] (r : C' ⥤ A) {H H' : A ⥤ A ⥤ E} (τ : H ⟶ H') :
    restrictBoth r H ⟶ restrictBoth r H' :=
  whiskerLeft r (whiskerRight τ ((whiskeringLeft C' A E).obj r))

/-- **Detecting shift compatibility after restricting both variables.** If the restriction of
`τ` along an essentially surjective shift-compatible functor `r`, in both variables, commutes with
the shifts, so does `τ`: this is `CategoryTheory.NatTrans.CommShift₂.of_essSurj`, whose two
hypotheses are the two fields of the restricted statement. -/
theorem of_restrictBothMap {h : CommShift₂Setup E M} {G₁ G₂ : D ⥤ D ⥤ E} [G₁.CommShift₂ h]
    [G₂.CommShift₂ h] (τ : G₁ ⟶ G₂) (r : C' ⥤ D) [r.EssSurj] [r.CommShift M]
    (hτ : NatTrans.CommShift₂ (restrictBothMap r τ) h) : NatTrans.CommShift₂ τ h :=
  of_essSurj τ h r r (fun K₁ => hτ.commShift_app K₁) (fun K₂ => hτ.commShift_flipApp K₂)

/-- The inverse of the restriction of a shift-compatible transformation of bifunctors, when that
restriction is invertible, is shift-compatible. -/
theorem restrictBothMap_inv_commShift₂ {A : Type*} [Category* A] [HasShift A M]
    {h : CommShift₂Setup E M} (r : C' ⥤ A) [r.CommShift M] {H H' : A ⥤ A ⥤ E}
    [H.CommShift₂ h] [H'.CommShift₂ h] (τ : H ⟶ H') [IsIso (restrictBothMap r τ)]
    (hτ : NatTrans.CommShift₂ τ h) :
    NatTrans.CommShift₂ (inv (restrictBothMap r τ)) h :=
  have : NatTrans.CommShift₂ (asIso (restrictBothMap r τ)).hom h :=
    inferInstanceAs (NatTrans.CommShift₂ (restrictBothMap r τ) h)
  inferInstanceAs (NatTrans.CommShift₂ (asIso (restrictBothMap r τ)).inv h)

section OneVariable

variable {A : Type*} [Category* A] [HasShift A M] {h : CommShift₂Setup E M} (r : C' ⥤ A)
  [r.CommShift M] {H H' : A ⥤ A ⥤ E} [H.CommShift₂ h] [H'.CommShift₂ h] (τ : H ⟶ H')

/-- The second-variable component of the restriction of a transformation of bifunctors along `r`
is shift-compatible as soon as the component of the transformation at the image is. -/
theorem restrictBothMap_app_commShift (X : C') (hτ : NatTrans.CommShift (τ.app (r.obj X)) M) :
    NatTrans.CommShift ((restrictBothMap r τ).app X) M :=
  inferInstanceAs (NatTrans.CommShift (whiskerLeft r (τ.app (r.obj X))) M)

/-- The first-variable component of the restriction of a transformation of bifunctors along `r`
is shift-compatible as soon as the flipped component of the transformation at the image is. -/
theorem restrictBothMap_flipApp_commShift (X : C')
    (hτ : NatTrans.CommShift (τ.flipApp (r.obj X)) M) :
    NatTrans.CommShift ((restrictBothMap r τ).flipApp X) M :=
  inferInstanceAs (NatTrans.CommShift (whiskerLeft r (τ.flipApp (r.obj X))) M)

/-- The second-variable component of the inverse of an invertible restriction. -/
theorem restrictBothMap_inv_app_commShift [IsIso (restrictBothMap r τ)] (X : C')
    (hτ : NatTrans.CommShift (τ.app (r.obj X)) M) :
    NatTrans.CommShift ((inv (restrictBothMap r τ)).app X) M := by
  have := restrictBothMap_app_commShift r τ X hτ
  rw [NatIso.isIso_inv_app]
  exact NatTrans.CommShift.of_isIso _ _

/-- The first-variable component of the inverse of an invertible restriction. -/
theorem restrictBothMap_inv_flipApp_commShift [IsIso (restrictBothMap r τ)] (X : C')
    (hτ : NatTrans.CommShift (τ.flipApp (r.obj X)) M) :
    NatTrans.CommShift ((inv (restrictBothMap r τ)).flipApp X) M := by
  have := restrictBothMap_flipApp_commShift r τ X hτ
  have : (inv (restrictBothMap r τ)).flipApp X = inv ((restrictBothMap r τ).flipApp X) :=
    by simp only [NatTrans.flipApp, Functor.map_inv, NatIso.isIso_inv_app]
  rw [this]
  exact NatTrans.CommShift.of_isIso _ _

end OneVariable

/-- The component of `restrictBothMap r τ` at `(X, Y)` is the component of `τ` at
`(r X, r Y)`. -/
@[simp]
theorem restrictBothMap_app_app {A : Type*} [Category* A] (r : C' ⥤ A) {H H' : A ⥤ A ⥤ E}
    (τ : H ⟶ H') (X Y : C') :
    ((restrictBothMap r τ).app X).app Y = (τ.app (r.obj X)).app (r.obj Y) :=
  rfl

variable (G : D ⥤ D ⥤ E) (h : CommShift₂Setup E M) [G.CommShift₂ h]

/-- The restriction of a bifunctor `G` along `a ⋙ k` in both variables, one factor at a time:
first along `k` in each variable, then along `a` in each variable. -/
abbrev precompPair (a : C' ⥤ C) (k : C ⥤ D) : C' ⥤ C' ⥤ E :=
  a ⋙ ((k ⋙ (G ⋙ (whiskeringLeft C D E).obj k)) ⋙ (whiskeringLeft C' C E).obj a)

variable {G} {a : C' ⥤ C} {k : C ⥤ D} {b : C' ⥤ C''} {l : C'' ⥤ D}

/-- **The isomorphism of restrictions induced by an isomorphism `e : a ⋙ k ≅ b ⋙ l`**, with
components `G(e X₁, e X₂)`. -/
def precompPairIso (e : a ⋙ k ≅ b ⋙ l) : precompPair G a k ≅ precompPair G b l :=
  NatIso.ofComponents
    (fun X₁ => NatIso.ofComponents
      (fun X₂ => (G.mapIso (e.app X₁)).app _ ≪≫ (G.obj _).mapIso (e.app X₂))
      (fun {X₂ Y₂} g => by
        have h₁ := ((G.map (e.hom.app X₁)).naturality (k.map (a.map g)))
        have h₂ := congrArg (G.obj (l.obj (b.obj X₁))).map (e.hom.naturality g)
        simp only [Functor.comp_map, Functor.map_comp] at h₂
        simp only [precompPair, Functor.comp_obj, whiskeringLeft_obj_obj, Functor.comp_map,
          Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
        rw [← h₂, reassoc_of% h₁]))
    (fun {X₁ Y₁} g => by
      ext X₂
      have h₁ := congrArg (fun t => NatTrans.app t (k.obj (a.obj X₂)))
        (congrArg G.map (e.hom.naturality g))
      have n₁ := (G.map (e.hom.app Y₁)).naturality (e.hom.app X₂)
      have n₂ := (G.map (l.map (b.map g))).naturality (e.hom.app X₂)
      simp only [Functor.comp_map, Functor.map_comp, NatTrans.comp_app, Functor.comp_obj]
        at h₁ n₁ n₂
      simp only [precompPair, Functor.comp_obj, whiskeringLeft_obj_obj, Functor.comp_map,
        whiskeringLeft_obj_map, NatTrans.comp_app, whiskerLeft_app, NatIso.ofComponents_hom_app,
        Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
      rw [reassoc_of% h₁, n₂])

/-- The component of `precompPairIso e` at `(X₁, X₂)` is `G(e X₁, e X₂)`, the composite of
`G.map (e.hom.app X₁)` at the second variable with `G.obj _` applied to `e.hom.app X₂`. -/
@[simp]
theorem precompPairIso_hom_app_app (e : a ⋙ k ≅ b ⋙ l) (X₁ X₂ : C') :
    ((precompPairIso e).hom.app X₁).app X₂ =
      (G.map (e.hom.app X₁)).app _ ≫ (G.obj _).map (e.hom.app X₂) :=
  rfl

variable [a.CommShift M] [k.CommShift M] [b.CommShift M] [l.CommShift M]

/-- The second-variable component of `precompPairIso e`, as a composite of whiskerings. -/
private theorem precompPairIso_hom_app_eq (e : a ⋙ k ≅ b ⋙ l) (X₁ : C') :
    (precompPairIso (G := G) e).hom.app X₁ =
      whiskerLeft a (whiskerLeft k (G.map (e.hom.app X₁))) ≫
        (Functor.associator a k (G.obj (l.obj (b.obj X₁)))).inv ≫
          whiskerRight e.hom (G.obj (l.obj (b.obj X₁))) ≫
            (Functor.associator b l (G.obj (l.obj (b.obj X₁)))).hom := by
  ext X₂
  simp

/-- The first-variable component of `precompPairIso e`, as a composite of whiskerings. -/
private theorem precompPairIso_hom_flipApp_eq (e : a ⋙ k ≅ b ⋙ l) (X₂ : C') :
    (precompPairIso (G := G) e).hom.flipApp X₂ =
      whiskerLeft a (whiskerLeft k (G.flip.map (e.hom.app X₂))) ≫
        (Functor.associator a k (G.flip.obj (l.obj (b.obj X₂)))).inv ≫
          whiskerRight e.hom (G.flip.obj (l.obj (b.obj X₂))) ≫
            (Functor.associator b l (G.flip.obj (l.obj (b.obj X₂)))).hom := by
  ext X₁
  dsimp
  simp only [Category.comp_id, Category.id_comp]
  exact ((G.map (e.hom.app X₁)).naturality (e.hom.app X₂)).symm

/-- **Restricting a bifunctor along two isomorphic functors gives isomorphic bifunctors, and the
isomorphism commutes with the shifts in both variables**, as soon as the isomorphism of functors
does. -/
instance precompPairIso_commShift₂ (e : a ⋙ k ≅ b ⋙ l) [NatTrans.CommShift e.hom M] :
    NatTrans.CommShift₂ (precompPairIso (G := G) e).hom h where
  commShift_app X₁ := by
    rw [precompPairIso_hom_app_eq]
    exact inferInstanceAs (NatTrans.CommShift
      (whiskerLeft a (whiskerLeft k (G.map (e.hom.app X₁))) ≫
        (Functor.associator a k (G.obj (l.obj (b.obj X₁)))).inv ≫
          whiskerRight e.hom (G.obj (l.obj (b.obj X₁))) ≫
            (Functor.associator b l (G.obj (l.obj (b.obj X₁)))).hom) M)
  commShift_flipApp X₂ := by
    rw [precompPairIso_hom_flipApp_eq]
    exact inferInstanceAs (NatTrans.CommShift
      (whiskerLeft a (whiskerLeft k (G.flip.map (e.hom.app X₂))) ≫
        (Functor.associator a k (G.flip.obj (l.obj (b.obj X₂)))).inv ≫
          whiskerRight e.hom (G.flip.obj (l.obj (b.obj X₂))) ≫
            (Functor.associator b l (G.flip.obj (l.obj (b.obj X₂)))).hom) M)

end CategoryTheory.NatTrans.CommShift₂

namespace CategoryTheory.Functor.CommShift₂

/-- The commutation datum that `CategoryTheory.Functor.CommShift₂.postcompInt` puts on
`(G ⋙ H).flip.obj X₂` is `CategoryTheory.Functor.CommShift.comp` of the datum on
`G.flip.obj X₂` and the datum on `H`. -/
theorem postcompInt_commShiftFlipObj {C₁ C₂ D D' : Type*} [Category* C₁] [Category* C₂]
    [Category* D] [Category* D'] [Preadditive D] [Preadditive D'] [HasShift C₁ ℤ]
    [HasShift C₂ ℤ] [HasShift D ℤ] [HasShift D' ℤ] [∀ (n : ℤ), (shiftFunctor D n).Additive]
    [∀ (n : ℤ), (shiftFunctor D' n).Additive] (G : C₁ ⥤ C₂ ⥤ D) (H : D ⥤ D') [H.CommShift ℤ]
    [H.Additive] [G.CommShift₂Int] (X₂ : C₂) :
    (show (G.flip.obj X₂ ⋙ H).CommShift ℤ from
      (postcompInt G H).commShiftFlipObj X₂) =
      CommShift.comp (G.flip.obj X₂) H :=
  rfl

/-- The commutation datum that `CategoryTheory.Functor.CommShift₂.precomp₁` after `precomp₂` puts
on the restriction of `G` along `F` in both variables, read in the first variable, is
`CategoryTheory.Functor.CommShift.comp` of the datum on `F` and the flipped datum of `G`. -/
theorem precomp₁₂_commShiftFlipObj {C' C D : Type*} [Category* C'] [Category* C] [Category* D]
    {M : Type*} [AddCommMonoid M] [HasShift C' M] [HasShift C M] [HasShift D M]
    (F : C' ⥤ C) [F.CommShift M] (G : C ⥤ C ⥤ D) (h : CommShift₂Setup D M) [G.CommShift₂ h]
    (X₂ : C') :
    (show (F ⋙ G.flip.obj (F.obj X₂)).CommShift M from
      (precomp₁ F (G ⋙ (whiskeringLeft C' C D).obj F) h).commShiftFlipObj X₂) =
      CommShift.comp F (G.flip.obj (F.obj X₂)) :=
  rfl

end CategoryTheory.Functor.CommShift₂

end
