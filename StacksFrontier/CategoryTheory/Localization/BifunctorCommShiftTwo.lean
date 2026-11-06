module

public import Mathlib.CategoryTheory.Localization.Bifunctor
public import Mathlib.CategoryTheory.Shift.CommShiftTwo
public import Mathlib.CategoryTheory.Shift.Localization

/-!
# A bifunctor induced through two localizations commutes with the shifts in both variables

Let `L₁ : C₁ ⥤ D₁` be a localization functor for a morphism property `W₁` and `L₂ : C₂ ⥤ D₂` one
for `W₂`, let the five categories `C₁`, `C₂`, `D₁`, `D₂`, `E` carry shifts by an additive
commutative monoid `M` with `L₁` and `L₂` compatible with them, and let a bifunctor
`G : C₁ ⥤ C₂ ⥤ E` factor through `L₁` and `L₂` as `G' : D₁ ⥤ D₂ ⥤ E` in the sense of
`CategoryTheory.Localization.Lifting₂`.  This file proves that if `G` commutes with the shifts in
both variables — `CategoryTheory.Functor.CommShift₂` for a `CategoryTheory.CommShift₂Setup` on
`E`, so including the sign coherence between the two variables — then so does `G'`.

This is the two-variable analogue of Mathlib's one-variable
`CategoryTheory.Functor.commShiftOfLocalization`. No
`CategoryTheory.MorphismProperty.IsCompatibleWithShift` is assumed, only that the two localization
functors commute with the shifts, so the result applies to shifts on `D₁`, `D₂` that were not
obtained by transport along the localizations.

## Main results

* `CategoryTheory.Functor.CommShift.ofConj`: `CategoryTheory.Functor.CommShift.ofIso` with the
  resulting family of commutation isomorphisms prescribed on the nose.
* `CategoryTheory.Localization.Lifting₂.precompSnd`: a bifunctor precomposed in the second
  variable lifts the corresponding precomposite, given an isomorphism `S ⋙ L₂ ≅ L₂ ⋙ S'`.
* `CategoryTheory.Localization.bifunctorCommShiftIso`: **the commutation isomorphism in the
  second variable, descended as a single isomorphism of bifunctors** on `D₁ ⥤ D₂ ⥤ E`.
* `CategoryTheory.Localization.objCommShift` and `CategoryTheory.Localization.map_commShift`:
  the `commShiftObj` and `commShift_map` halves of the conclusion.
* `CategoryTheory.Localization.commShift₂_comm_of_lifting₂`: the sign coherence `comm`.
* `CategoryTheory.Functor.CommShift₂.ofLocalization` and
  `CategoryTheory.Functor.CommShift₂.ofLocalizationInt`: the conclusion, for a general setup and
  for the standard `ℤ` setup `CategoryTheory.CommShift₂Setup.int` with its sign
  `(-1) ^ (p * q)`.

## Implementation notes

For each `n : M`, the commutation isomorphisms of the functors `G'.obj Y₁` with the shift by `n`
are not built object by object from a chosen preimage of `Y₁` under `L₁`: such a choice is not
functorial in `Y₁`, and the fields `commShift_map` and `comm` cannot be proved for it. They are
instead the components of a single isomorphism of bifunctors
`CategoryTheory.Localization.bifunctorCommShiftIso n`, descended by
`CategoryTheory.Localization.lift₂NatIso`, so that their naturality in `Y₁` holds by construction.
A chosen preimage enters only the proofs of the two `Prop` fields of each
`CategoryTheory.Functor.CommShift` structure, through `CategoryTheory.Functor.CommShift.ofConj`.
-/

@[expose] public section

namespace CategoryTheory

open Category CategoryTheory.Functor CategoryTheory.Localization

variable {A B C₁ C₂ D₁ D₂ E : Type*} [Category* A] [Category* B] [Category* C₁] [Category* C₂]
  [Category* D₁] [Category* D₂] [Category* E]

namespace Functor.CommShift

variable {M : Type*} [AddMonoid M] [HasShift A M] [HasShift B M] {F F' : A ⥤ B} [F.CommShift M]

/-- **A functor isomorphic to one which commutes with the shift commutes with the shift, with a
prescribed family of commutation isomorphisms.**  This is
`CategoryTheory.Functor.CommShift.ofIso` with the resulting `commShiftIso` fixed on the nose:
`ofIso` conjugates the given isomorphisms by `α`, and `hκ` says that `κ` *is* that conjugate, so
the structure produced here has `commShiftIso = κ` by `rfl`. -/
@[instance_reducible]
noncomputable def ofConj (α : F ≅ F')
    (κ : ∀ n : M, shiftFunctor A n ⋙ F' ≅ F' ⋙ shiftFunctor B n)
    (hκ : ∀ n : M, (F.commShiftIso n).hom ≫ Functor.whiskerRight α.hom (shiftFunctor B n) =
      Functor.whiskerLeft (shiftFunctor A n) α.hom ≫ (κ n).hom) :
    F'.CommShift M := by
  letI := ofIso α M
  have h : ∀ n : M, κ n = F'.commShiftIso n := by
    intro n
    ext Y
    have key : (F.commShiftIso n).hom.app Y ≫ ((α.hom.app Y)⟦n⟧') =
        α.hom.app (Y⟦n⟧) ≫ (κ n).hom.app Y := by
      simpa using congr_app (hκ n) Y
    rw [ofIso_commShiftIso_hom_app, key]
    simp
  exact
    { commShiftIso := κ
      commShiftIso_zero := by rw [h, F'.commShiftIso_zero]
      commShiftIso_add := fun a b => by rw [h, h, h, F'.commShiftIso_add] }

/-- The commutation isomorphisms of `CategoryTheory.Functor.CommShift.ofConj α κ hκ` are the
isomorphisms `κ n`. -/
theorem ofConj_commShiftIso (α : F ≅ F')
    (κ : ∀ n : M, shiftFunctor A n ⋙ F' ≅ F' ⋙ shiftFunctor B n)
    (hκ : ∀ n : M, (F.commShiftIso n).hom ≫ Functor.whiskerRight α.hom (shiftFunctor B n) =
      Functor.whiskerLeft (shiftFunctor A n) α.hom ≫ (κ n).hom) (n : M) :
    letI := ofConj α κ hκ
    F'.commShiftIso n = κ n :=
  rfl

end Functor.CommShift

namespace Localization

/-! ### Lifting data for a bifunctor precomposed in the second variable -/

section PrecompSnd

variable (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  (F : C₁ ⥤ C₂ ⥤ E) (F' : D₁ ⥤ D₂ ⥤ E) [Lifting₂ L₁ L₂ W₁ W₂ F F']

/-- **A bifunctor precomposed in the second variable lifts the corresponding precomposite**, as
soon as the two precomposing functors are related by an isomorphism `e : S ⋙ L₂ ≅ L₂ ⋙ S'` over
the second localization. -/
@[instance_reducible]
noncomputable def Lifting₂.precompSnd (S : C₂ ⥤ C₂) (S' : D₂ ⥤ D₂) (e : S ⋙ L₂ ≅ L₂ ⋙ S') :
    Lifting₂ L₁ L₂ W₁ W₂ (F ⋙ (whiskeringLeft C₂ C₂ E).obj S)
      (F' ⋙ (whiskeringLeft D₂ D₂ E).obj S') where
  iso := isoWhiskerLeft (L₁ ⋙ F') ((whiskeringLeft C₂ D₂ E).mapIso e.symm) ≪≫
    isoWhiskerRight (Lifting₂.iso L₁ L₂ W₁ W₂ F F') ((whiskeringLeft C₂ C₂ E).obj S)

/-- The components of the isomorphism of `CategoryTheory.Localization.Lifting₂.precompSnd`. -/
theorem Lifting₂.precompSnd_iso_hom_app_app (S : C₂ ⥤ C₂) (S' : D₂ ⥤ D₂)
    (e : S ⋙ L₂ ≅ L₂ ⋙ S') (X₁ : C₁) (X₂ : C₂) :
    letI := Lifting₂.precompSnd L₁ L₂ W₁ W₂ F F' S S' e
    ((Lifting₂.iso L₁ L₂ W₁ W₂ (F ⋙ (whiskeringLeft C₂ C₂ E).obj S)
        (F' ⋙ (whiskeringLeft D₂ D₂ E).obj S')).hom.app X₁).app X₂ =
      (F'.obj (L₁.obj X₁)).map (e.inv.app X₂) ≫
        ((Lifting₂.iso L₁ L₂ W₁ W₂ F F').hom.app X₁).app (S.obj X₂) :=
  rfl

/-- The components of the inverse of the isomorphism of
`CategoryTheory.Localization.Lifting₂.compRight`. -/
theorem Lifting₂.compRight_iso_inv_app_app (T : E ⥤ E) (X₁ : C₁) (X₂ : C₂) :
    ((Lifting₂.iso L₁ L₂ W₁ W₂ (F ⋙ (whiskeringRight C₂ E E).obj T)
        (F' ⋙ (whiskeringRight D₂ E E).obj T)).inv.app X₁).app X₂ =
      T.map (((Lifting₂.iso L₁ L₂ W₁ W₂ F F').inv.app X₁).app X₂) :=
  rfl

end PrecompSnd

/-! ### The descent of the commutation isomorphism in the second variable -/

section OneVariable

variable {M : Type*} [AddMonoid M] [HasShift C₂ M] [HasShift D₂ M] [HasShift E M]
  (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
  [W₁.ContainsIdentities] [W₂.ContainsIdentities] [L₂.CommShift M]
  (F : C₁ ⥤ C₂ ⥤ E) (F' : D₁ ⥤ D₂ ⥤ E) [Lifting₂ L₁ L₂ W₁ W₂ F F']
  [∀ X₁ : C₁, (F.obj X₁).CommShift M]
  [∀ (X₁ Y₁ : C₁) (f : X₁ ⟶ Y₁), NatTrans.CommShift (F.map f) M]

/-- The lifting of `F` precomposed in the second variable with the shift by `n` to `F'` precomposed
in the second variable with the shift by `n`, given by
`CategoryTheory.Localization.Lifting₂.precompSnd` at the commutation isomorphism of `L₂` with the
shift by `n`. -/
noncomputable abbrev liftingShiftSnd (n : M) :
    Lifting₂ L₁ L₂ W₁ W₂ (F ⋙ (whiskeringLeft C₂ C₂ E).obj (shiftFunctor C₂ n))
      (F' ⋙ (whiskeringLeft D₂ D₂ E).obj (shiftFunctor D₂ n)) :=
  Lifting₂.precompSnd L₁ L₂ W₁ W₂ F F' _ _ (L₂.commShiftIso n)

/-- **The commutation isomorphisms of `F.obj X₁` in the second variable, assembled into a single
isomorphism of bifunctors.** -/
noncomputable def bifunctorCommShiftIsoSrc (n : M) :
    F ⋙ (whiskeringLeft C₂ C₂ E).obj (shiftFunctor C₂ n) ≅
      F ⋙ (whiskeringRight C₂ E E).obj (shiftFunctor E n) :=
  NatIso.ofComponents (fun X₁ => (F.obj X₁).commShiftIso n)
    (fun f => (NatTrans.shift_comm (F.map f) n).symm)

/-- The component of `CategoryTheory.Localization.bifunctorCommShiftIsoSrc F n` at `X₁` is the
commutation isomorphism of `F.obj X₁` with the shift by `n`. -/
@[simp]
theorem bifunctorCommShiftIsoSrc_hom_app (n : M) (X₁ : C₁) :
    (bifunctorCommShiftIsoSrc F n).hom.app X₁ = ((F.obj X₁).commShiftIso n).hom :=
  rfl

/-- **The descended commutation isomorphism in the second variable, as a single isomorphism of
bifunctors on the localizations.**

Its component at `Y₁ : D₁` is an isomorphism
`shiftFunctor D₂ n ⋙ F'.obj Y₁ ≅ F'.obj Y₁ ⋙ shiftFunctor E n`; it is descended from
`CategoryTheory.Localization.bifunctorCommShiftIsoSrc` by
`CategoryTheory.Localization.lift₂NatIso`. -/
noncomputable def bifunctorCommShiftIso (n : M) :
    F' ⋙ (whiskeringLeft D₂ D₂ E).obj (shiftFunctor D₂ n) ≅
      F' ⋙ (whiskeringRight D₂ E E).obj (shiftFunctor E n) :=
  letI := liftingShiftSnd L₁ L₂ W₁ W₂ F F' n
  lift₂NatIso L₁ L₂ W₁ W₂ _ _ _ _ (bifunctorCommShiftIsoSrc F n)

/-- The components of `CategoryTheory.Localization.bifunctorCommShiftIso` over the images of the
two localization functors. -/
theorem bifunctorCommShiftIso_hom_app_app (n : M) (X₁ : C₁) (X₂ : C₂) :
    (((bifunctorCommShiftIso L₁ L₂ W₁ W₂ F F' n).hom.app (L₁.obj X₁)).app (L₂.obj X₂)) =
      (F'.obj (L₁.obj X₁)).map ((L₂.commShiftIso n).inv.app X₂) ≫
        ((Lifting₂.iso L₁ L₂ W₁ W₂ F F').hom.app X₁).app (X₂⟦n⟧) ≫
        ((F.obj X₁).commShiftIso n).hom.app X₂ ≫
        (shiftFunctor E n).map (((Lifting₂.iso L₁ L₂ W₁ W₂ F F').inv.app X₁).app X₂) := by
  let _ := liftingShiftSnd L₁ L₂ W₁ W₂ F F' n
  show (((lift₂NatTrans L₁ L₂ W₁ W₂ _ _ _ _
    (bifunctorCommShiftIsoSrc F n).hom).app (L₁.obj X₁)).app (L₂.obj X₂)) = _
  rw [lift₂NatTrans_app_app, Lifting₂.precompSnd_iso_hom_app_app,
    Lifting₂.compRight_iso_inv_app_app, bifunctorCommShiftIsoSrc_hom_app]
  simp only [Category.assoc]

/-- Over the image of the first localization functor, the components of
`CategoryTheory.Localization.bifunctorCommShiftIso` are the one-variable descent
`CategoryTheory.Functor.commShiftOfLocalization` along the second localization functor. -/
theorem bifunctorCommShiftIso_hom_app_image (X₁ : C₁) (n : M) :
    letI := Lifting₂.fst L₁ L₂ W₁ W₂ F F' X₁
    letI := Functor.commShiftOfLocalization L₂ W₂ M (F.obj X₁) (F'.obj (L₁.obj X₁))
    ((F'.obj (L₁.obj X₁)).commShiftIso n).hom =
      (bifunctorCommShiftIso L₁ L₂ W₁ W₂ F F' n).hom.app (L₁.obj X₁) := by
  let _ := Lifting₂.fst L₁ L₂ W₁ W₂ F F' X₁
  let _ := Functor.commShiftOfLocalization L₂ W₂ M (F.obj X₁) (F'.obj (L₁.obj X₁))
  refine natTrans_ext L₂ W₂ fun X₂ => ?_
  rw [Functor.commShiftOfLocalization_iso_hom_app, bifunctorCommShiftIso_hom_app_app]
  rfl

/-- **The second-variable commutation isomorphisms of `F'.obj Y₁`, for an arbitrary object `Y₁`
of the first localization.**  They are the components at `Y₁` of
`CategoryTheory.Localization.bifunctorCommShiftIso`. -/
@[instance_reducible]
noncomputable def objCommShift (Y₁ : D₁) : (F'.obj Y₁).CommShift M :=
  haveI := Localization.essSurj L₁ W₁
  letI := Lifting₂.fst L₁ L₂ W₁ W₂ F F' (L₁.objPreimage Y₁)
  letI := Functor.commShiftOfLocalization L₂ W₂ M (F.obj (L₁.objPreimage Y₁))
    (F'.obj (L₁.obj (L₁.objPreimage Y₁)))
  Functor.CommShift.ofConj (F'.mapIso (L₁.objObjPreimageIso Y₁))
    (fun n => (bifunctorCommShiftIso L₁ L₂ W₁ W₂ F F' n).app Y₁)
    (fun n => by
      rw [bifunctorCommShiftIso_hom_app_image]
      exact ((bifunctorCommShiftIso L₁ L₂ W₁ W₂ F F' n).hom.naturality
        (L₁.objObjPreimageIso Y₁).hom).symm)

/-- The commutation isomorphisms of `CategoryTheory.Localization.objCommShift` are the components
of `CategoryTheory.Localization.bifunctorCommShiftIso`, by construction. -/
theorem objCommShift_commShiftIso (Y₁ : D₁) (n : M) :
    letI : (F'.obj Y₁).CommShift M := objCommShift L₁ L₂ W₁ W₂ F F' Y₁
    (F'.obj Y₁).commShiftIso n =
      (bifunctorCommShiftIso L₁ L₂ W₁ W₂ F F' n).app Y₁ :=
  rfl

/-- **The image under `F'` of a morphism of the first localization commutes with the
second-variable shifts.** -/
theorem map_commShift {Y₁ Z₁ : D₁} (f : Y₁ ⟶ Z₁) :
    letI : (F'.obj Y₁).CommShift M := objCommShift L₁ L₂ W₁ W₂ F F' Y₁
    letI : (F'.obj Z₁).CommShift M := objCommShift L₁ L₂ W₁ W₂ F F' Z₁
    NatTrans.CommShift (F'.map f) M := by
  let _ : (F'.obj Y₁).CommShift M := objCommShift L₁ L₂ W₁ W₂ F F' Y₁
  let _ : (F'.obj Z₁).CommShift M := objCommShift L₁ L₂ W₁ W₂ F F' Z₁
  exact ⟨fun n => ((bifunctorCommShiftIso L₁ L₂ W₁ W₂ F F' n).hom.naturality f).symm⟩


/-- The components of the descended second-variable commutation isomorphisms over the images of
the two localization functors. -/
theorem objCommShift_commShiftIso_hom_app_app (X₁ : C₁) (X₂ : C₂) (n : M) :
    letI : (F'.obj (L₁.obj X₁)).CommShift M := objCommShift L₁ L₂ W₁ W₂ F F' (L₁.obj X₁)
    ((F'.obj (L₁.obj X₁)).commShiftIso n).hom.app (L₂.obj X₂) =
      (F'.obj (L₁.obj X₁)).map ((L₂.commShiftIso n).inv.app X₂) ≫
        ((Lifting₂.iso L₁ L₂ W₁ W₂ F F').hom.app X₁).app (X₂⟦n⟧) ≫
        ((F.obj X₁).commShiftIso n).hom.app X₂ ≫
        (shiftFunctor E n).map (((Lifting₂.iso L₁ L₂ W₁ W₂ F F').inv.app X₁).app X₂) :=
  bifunctorCommShiftIso_hom_app_app L₁ L₂ W₁ W₂ F F' n X₁ X₂

end OneVariable

/-! ### The two-variable descent -/

section TwoVariable

variable {M : Type*} [AddCommMonoid M] [HasShift C₁ M] [HasShift C₂ M] [HasShift D₁ M]
  [HasShift D₂ M] [HasShift E M]
  (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
  [W₁.ContainsIdentities] [W₂.ContainsIdentities] [L₁.CommShift M] [L₂.CommShift M]
  (G : C₁ ⥤ C₂ ⥤ E) (G' : D₁ ⥤ D₂ ⥤ E) [Lifting₂ L₁ L₂ W₁ W₂ G G']
  (h : CommShift₂Setup E M) [G.CommShift₂ h]

/-- **The sign coherence `comm` of `CategoryTheory.Functor.CommShift₂` descends** to the
commutation isomorphisms `CategoryTheory.Localization.objCommShift` of `G'` and of `G'.flip`. -/
theorem commShift₂_comm_of_lifting₂ (m n : M) :
    letI : ∀ Y₁ : D₁, (G'.obj Y₁).CommShift M := objCommShift L₁ L₂ W₁ W₂ G G'
    letI : ∀ Y₂ : D₂, (G'.flip.obj Y₂).CommShift M := objCommShift L₂ L₁ W₂ W₁ G.flip G'.flip
    ∀ (Y₁ : D₁) (Y₂ : D₂),
      ((G'.obj (Y₁⟦m⟧)).commShiftIso n).hom.app Y₂ ≫
          (((G'.flip.obj Y₂).commShiftIso m).hom.app Y₁)⟦n⟧' =
        ((G'.flip.obj (Y₂⟦n⟧)).commShiftIso m).hom.app Y₁ ≫
          (((G'.obj Y₁).commShiftIso n).hom.app Y₂)⟦m⟧' ≫
            (shiftComm ((G'.obj Y₁).obj Y₂) m n).inv ≫
              (h.ε m n).val.app (((G'.obj Y₁).obj Y₂)⟦m⟧⟦n⟧) := by
  let _ : ∀ Y₁ : D₁, (G'.obj Y₁).CommShift M := objCommShift L₁ L₂ W₁ W₂ G G'
  let _ : ∀ Y₂ : D₂, (G'.flip.obj Y₂).CommShift M := objCommShift L₂ L₁ W₂ W₁ G.flip G'.flip
  let _ : ∀ (Y₁ Z₁ : D₁) (f : Y₁ ⟶ Z₁), NatTrans.CommShift (G'.map f) M := fun _ _ f =>
    map_commShift L₁ L₂ W₁ W₂ G G' f
  let _ : ∀ (Y₂ Z₂ : D₂) (g : Y₂ ⟶ Z₂), NatTrans.CommShift (G'.flip.map g) M := fun _ _ g =>
    map_commShift L₂ L₁ W₂ W₁ G.flip G'.flip g
  have hflipHom : ∀ (X₁ : C₁) (X₂ : C₂),
      ((Lifting₂.iso L₂ L₁ W₂ W₁ G.flip G'.flip).hom.app X₂).app X₁ =
        ((Lifting₂.iso L₁ L₂ W₁ W₂ G G').hom.app X₁).app X₂ := fun _ _ => rfl
  have hflipInv : ∀ (X₁ : C₁) (X₂ : C₂),
      ((Lifting₂.iso L₂ L₁ W₂ W₁ G.flip G'.flip).inv.app X₂).app X₁ =
        ((Lifting₂.iso L₁ L₂ W₁ W₂ G G').inv.app X₁).app X₂ := fun _ _ => rfl
  have himage : ∀ (X₁ : C₁) (X₂ : C₂),
      ((G'.obj ((L₁.obj X₁)⟦m⟧)).commShiftIso n).hom.app (L₂.obj X₂) ≫
          (((G'.flip.obj (L₂.obj X₂)).commShiftIso m).hom.app (L₁.obj X₁))⟦n⟧' =
        ((G'.flip.obj ((L₂.obj X₂)⟦n⟧)).commShiftIso m).hom.app (L₁.obj X₁) ≫
          (((G'.obj (L₁.obj X₁)).commShiftIso n).hom.app (L₂.obj X₂))⟦m⟧' ≫
            (shiftComm ((G'.obj (L₁.obj X₁)).obj (L₂.obj X₂)) m n).inv ≫
              (h.ε m n).val.app
                (((G'.obj (L₁.obj X₁)).obj (L₂.obj X₂))⟦m⟧⟦n⟧) := by
    intro X₁ X₂
    have hu := NatTrans.shift_app_comm (G'.map ((L₁.commShiftIso m).hom.app X₁)) n (L₂.obj X₂)
    have hv := NatTrans.shift_app_comm (G'.flip.map ((L₂.commShiftIso n).hom.app X₂)) m
      (L₁.obj X₁)
    have hnat := (G'.map ((L₁.commShiftIso m).hom.app X₁)).naturality
      ((L₂.commShiftIso n).hom.app X₂)
    have hW := objCommShift_commShiftIso_hom_app_app L₁ L₂ W₁ W₂ G G' X₁ X₂ n
    have hWm := objCommShift_commShiftIso_hom_app_app L₁ L₂ W₁ W₂ G G' (X₁⟦m⟧) X₂ n
    have hY := objCommShift_commShiftIso_hom_app_app L₂ L₁ W₂ W₁ G.flip G'.flip X₂ X₁ m
    have hYn := objCommShift_commShiftIso_hom_app_app L₂ L₁ W₂ W₁ G.flip G'.flip (X₂⟦n⟧) X₁ m
    have hcomm := G.commShift₂_comm h X₁ X₂ m n
    have hcu : ∀ Z : D₂, (G'.map ((L₁.commShiftIso m).hom.app X₁)).app Z ≫
        (G'.map ((L₁.commShiftIso m).inv.app X₁)).app Z = 𝟙 _ := fun Z => by
      rw [← NatTrans.comp_app, ← G'.map_comp, Iso.hom_inv_id_app, G'.map_id, NatTrans.id_app]
    have hcv : ∀ Z : D₁, (G'.obj Z).map ((L₂.commShiftIso n).hom.app X₂) ≫
        (G'.obj Z).map ((L₂.commShiftIso n).inv.app X₂) = 𝟙 _ := fun Z => by
      rw [← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]
    have hsc : ∀ {P Q : E} (f : P ⟶ Q), ((f⟦n⟧')⟦m⟧') ≫ (shiftComm Q m n).inv =
        (shiftComm P m n).inv ≫ ((f⟦m⟧')⟦n⟧') := fun f =>
      (shiftFunctorComm E m n).inv.naturality f
    have hcen : ∀ {P Q : E} (f : P ⟶ Q),
        (h.ε m n).val.app P ≫ f = f ≫ (h.ε m n).val.app Q := fun f =>
      ((h.ε m n).val.naturality f).symm
    simp only [Functor.comp_obj, Functor.flip_obj_map, Functor.flip_map_app,
      hflipHom, hflipInv] at hu hv hW hWm hY hYn
    refine (Iso.cancel_iso_hom_left
      ((G'.obj (L₁.obj (X₁⟦m⟧))).mapIso ((L₂.commShiftIso n).app X₂) ≪≫
        Iso.app (G'.mapIso ((L₁.commShiftIso m).app X₁)) ((L₂.obj X₂)⟦n⟧)) _ _).mp ?_
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc]
    rw [← reassoc_of% hu, reassoc_of% hnat, ← reassoc_of% hv, hWm, hY, hYn, hW]
    simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Category.assoc,
      reassoc_of% hcu, reassoc_of% hcv, Iso.inv_hom_id_app_app_assoc]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% hcomm, hcen,
      ← reassoc_of% (hsc (((Lifting₂.iso L₁ L₂ W₁ W₂ G G').inv.app X₁).app X₂))]
    rfl
  have hsnd : ∀ (Y₁ : D₁) (X₂ : C₂),
      ((G'.obj (Y₁⟦m⟧)).commShiftIso n).hom.app (L₂.obj X₂) ≫
          (((G'.flip.obj (L₂.obj X₂)).commShiftIso m).hom.app Y₁)⟦n⟧' =
        ((G'.flip.obj ((L₂.obj X₂)⟦n⟧)).commShiftIso m).hom.app Y₁ ≫
          (((G'.obj Y₁).commShiftIso n).hom.app (L₂.obj X₂))⟦m⟧' ≫
            (shiftComm ((G'.obj Y₁).obj (L₂.obj X₂)) m n).inv ≫
              (h.ε m n).val.app (((G'.obj Y₁).obj (L₂.obj X₂))⟦m⟧⟦n⟧) := by
    intro Y₁ X₂
    exact congr_app (natTrans_ext L₁ W₁
      (τ := Functor.whiskerLeft (shiftFunctor D₁ m)
          (Functor.whiskerRight (bifunctorCommShiftIso L₁ L₂ W₁ W₂ G G' n).hom
            ((evaluation D₂ E).obj (L₂.obj X₂))) ≫
        Functor.whiskerRight ((G'.flip.obj (L₂.obj X₂)).commShiftIso m).hom (shiftFunctor E n))
      (τ' := ((G'.flip.obj ((L₂.obj X₂)⟦n⟧)).commShiftIso m).hom ≫
        Functor.whiskerRight
            (Functor.whiskerRight (bifunctorCommShiftIso L₁ L₂ W₁ W₂ G G' n).hom
              ((evaluation D₂ E).obj (L₂.obj X₂))) (shiftFunctor E m) ≫
          Functor.whiskerLeft (G'.flip.obj (L₂.obj X₂)) (shiftFunctorComm E m n).inv ≫
            Functor.whiskerLeft
              (G'.flip.obj (L₂.obj X₂) ⋙ shiftFunctor E m ⋙ shiftFunctor E n) (h.ε m n).val.asHom)
      (fun X₁ => himage X₁ X₂)) Y₁
  intro Y₁ Y₂
  exact congr_app (natTrans_ext L₂ W₂
    (τ := ((G'.obj (Y₁⟦m⟧)).commShiftIso n).hom ≫
      Functor.whiskerRight
        (Functor.whiskerRight (bifunctorCommShiftIso L₂ L₁ W₂ W₁ G.flip G'.flip m).hom
          ((evaluation D₁ E).obj Y₁)) (shiftFunctor E n))
    (τ' := Functor.whiskerLeft (shiftFunctor D₂ n)
        (Functor.whiskerRight (bifunctorCommShiftIso L₂ L₁ W₂ W₁ G.flip G'.flip m).hom
          ((evaluation D₁ E).obj Y₁)) ≫
      Functor.whiskerRight ((G'.obj Y₁).commShiftIso n).hom (shiftFunctor E m) ≫
        Functor.whiskerLeft (G'.obj Y₁) (shiftFunctorComm E m n).inv ≫
          Functor.whiskerLeft (G'.obj Y₁ ⋙ shiftFunctor E m ⋙ shiftFunctor E n) (h.ε m n).val.asHom)
    (fun X₂ => hsnd Y₁ X₂)) Y₂

end TwoVariable

end Localization

/-! ### A bifunctor induced through two localizations commutes with the shifts -/

namespace Functor.CommShift₂

section

variable {M : Type*} [AddCommMonoid M] [HasShift C₁ M] [HasShift C₂ M] [HasShift D₁ M]
  [HasShift D₂ M] [HasShift E M]
  (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
  [W₁.ContainsIdentities] [W₂.ContainsIdentities] [L₁.CommShift M] [L₂.CommShift M]
  (G : C₁ ⥤ C₂ ⥤ E) (G' : D₁ ⥤ D₂ ⥤ E) [Localization.Lifting₂ L₁ L₂ W₁ W₂ G G']
  (h : CommShift₂Setup E M) [G.CommShift₂ h]

/-- **A bifunctor induced through two localization functors commutes with the shifts in both
variables as soon as the bifunctor it is induced from does.**  This is the two-variable analogue
of `CategoryTheory.Functor.commShiftOfLocalization`. -/
@[instance_reducible]
noncomputable def ofLocalization : G'.CommShift₂ h where
  commShiftObj Y₁ := Localization.objCommShift L₁ L₂ W₁ W₂ G G' Y₁
  commShift_map f := Localization.map_commShift L₁ L₂ W₁ W₂ G G' f
  commShiftFlipObj Y₂ := Localization.objCommShift L₂ L₁ W₂ W₁ G.flip G'.flip Y₂
  commShift_flip_map g := Localization.map_commShift L₂ L₁ W₂ W₁ G.flip G'.flip g
  comm Y₁ Y₂ m n := Localization.commShift₂_comm_of_lifting₂ L₁ L₂ W₁ W₂ G G' h m n Y₁ Y₂

end

section Int

variable [Preadditive E] [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift D₁ ℤ] [HasShift D₂ ℤ]
  [HasShift E ℤ] [∀ n : ℤ, (shiftFunctor E n).Additive]
  (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
  [W₁.ContainsIdentities] [W₂.ContainsIdentities] [L₁.CommShift ℤ] [L₂.CommShift ℤ]
  (G : C₁ ⥤ C₂ ⥤ E) (G' : D₁ ⥤ D₂ ⥤ E) [Localization.Lifting₂ L₁ L₂ W₁ W₂ G G']
  [G.CommShift₂Int]

/-- **A bifunctor induced through two localization functors commutes with the shifts by `ℤ` in
both variables, with the sign `(-1) ^ (p * q)`, as soon as the bifunctor it is induced from
does.**  This is `CategoryTheory.Functor.CommShift₂.ofLocalization` at the standard setup
`CategoryTheory.CommShift₂Setup.int`. -/
@[instance_reducible]
noncomputable def ofLocalizationInt : G'.CommShift₂Int :=
  ofLocalization L₁ L₂ W₁ W₂ G G' CommShift₂Setup.int

end Int

end Functor.CommShift₂

end CategoryTheory

end
