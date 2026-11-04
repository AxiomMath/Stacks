module

public import Mathlib.CategoryTheory.Localization.Bifunctor
public import Mathlib.CategoryTheory.Shift.CommShiftTwo
public import Mathlib.CategoryTheory.Shift.Localization
public import StacksFrontier.CategoryTheory.Shift.CommShiftTwoPostcomp

/-!
# Bifunctors on localized categories commuting with shifts in both variables

Let `L₁ : C₁ ⥤ D₁` and `L₂ : C₂ ⥤ D₂` be localization functors for classes of morphisms `W₁`
and `W₂`, both commuting with a shift by an additive monoid `M`, and let `F' : D₁ ⥤ D₂ ⥤ E` be
induced by a bifunctor `F : C₁ ⥤ C₂ ⥤ E` (`CategoryTheory.Localization.Lifting₂`). If `F`
commutes with the shifts in both variables (`CategoryTheory.Functor.CommShift₂`), then so does
`F'`. This is the two-variable analogue of `CategoryTheory.Functor.commShiftOfLocalization`.

The commutation of `F'.obj Y₁` with the shift in the second variable is obtained, naturally in
`Y₁`, by descending the isomorphism of bifunctors `(X₁, X₂) ↦ F(X₁, X₂[m]) ≅ F(X₁, X₂)[m]`
along the two localizations; its value at `Y₁ = L₁(X₁)` is the commutation descended from
`F.obj X₁` alone. The compatibility between the two variables only has to be checked on objects
`(L₁(X₁), L₂(X₂))`, because both sides are natural and the localization functors are
essentially surjective.

We also record that a bifunctor commuting with the shifts by `ℤ`, followed by an additive functor
commuting with the shift, again commutes with the shifts in both variables.

## Main definitions

* `CategoryTheory.Localization.Lifting₂.commShift₂`: the commutation of `F'` with the shifts in
  both variables.

## Main results

* `CategoryTheory.Localization.Lifting₂.commShift_fst_iso_hom`: the lifting isomorphism
  `L₂ ⋙ F'.obj (L₁.obj X₁) ≅ F.obj X₁` commutes with the shift.
* `CategoryTheory.Functor.CommShift₂.comm_of_essSurj`: the compatibility axiom of
  `Functor.CommShift₂` can be checked on the essential images of essentially surjective functors.
* `CategoryTheory.Functor.CommShift₂.map_int_ε_app`: an additive functor preserves the sign of
  the standard setup; postcomposition itself is `CategoryTheory.Functor.CommShift₂.postcompInt`.
-/

@[expose] public noncomputable section

open CategoryTheory Category Functor

namespace CategoryTheory.Localization.Lifting₂

variable {C₁ C₂ D₁ D₂ E : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
  [Category E]
  (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂] [W₁.ContainsIdentities] [W₂.ContainsIdentities]
  (F : C₁ ⥤ C₂ ⥤ E) (F' : D₁ ⥤ D₂ ⥤ E) [Lifting₂ L₁ L₂ W₁ W₂ F F']
  {M : Type*} [AddMonoid M] [HasShift C₂ M] [HasShift D₂ M] [HasShift E M] [L₂.CommShift M]

section

variable [∀ X₁, (F.obj X₁).CommShift M]

/-- The commutation of the functors `F.obj X₁` with the shift by `m`, as one isomorphism of
bifunctors, natural in `X₁`. -/
def shiftIsoSnd [∀ {X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁), NatTrans.CommShift (F.map f) M] (m : M) :
    F ⋙ (whiskeringLeft C₂ C₂ E).obj (shiftFunctor C₂ m) ≅
      F ⋙ (whiskeringRight C₂ E E).obj (shiftFunctor E m) :=
  NatIso.ofComponents (fun X₁ ↦ (F.obj X₁).commShiftIso m)
    (fun f ↦ (NatTrans.shift_comm (F.map f) m).symm)

omit [∀ X₁, (F.obj X₁).CommShift M] in
/-- If `F'` lifts `F`, then `F'` precomposed in its second variable with the shift by `m` lifts
`F` precomposed in its second variable with the shift by `m`. -/
@[instance_reducible]
def liftingShiftSnd (m : M) :
    Lifting₂ L₁ L₂ W₁ W₂ (F ⋙ (whiskeringLeft C₂ C₂ E).obj (shiftFunctor C₂ m))
      (F' ⋙ (whiskeringLeft D₂ D₂ E).obj (shiftFunctor D₂ m)) where
  iso := NatIso.ofComponents (fun X₁ ↦ NatIso.ofComponents (fun X₂ ↦
      (F'.obj (L₁.obj X₁)).mapIso ((L₂.commShiftIso m).symm.app X₂) ≪≫
        ((Lifting₂.iso L₁ L₂ W₁ W₂ F F').app X₁).app (X₂⟦m⟧)) (fun g ↦ by
      dsimp
      simp only [← Functor.map_comp_assoc, commShiftIso_inv_naturality]
      simp only [Functor.map_comp, assoc]
      congr 1
      exact ((Lifting₂.iso L₁ L₂ W₁ W₂ F F').hom.app X₁).naturality _)) (fun f ↦ by
      ext X₂
      dsimp
      refine (NatTrans.naturality_assoc (F'.map (L₁.map f))
        ((L₂.commShiftIso m).inv.app X₂) _).symm.trans ?_
      have h := NatTrans.congr_app ((Lifting₂.iso L₁ L₂ W₁ W₂ F F').hom.naturality f) (X₂⟦m⟧)
      dsimp at h
      dsimp
      rw [h, assoc])

variable [∀ {X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁), NatTrans.CommShift (F.map f) M]

/-- The commutation of the functors `F'.obj Y₁` with the shift by `m`, natural in `Y₁`: the
descent of `shiftIsoSnd F m`. -/
def shiftIsoSndLift (m : M) :
    F' ⋙ (whiskeringLeft D₂ D₂ E).obj (shiftFunctor D₂ m) ≅
      F' ⋙ (whiskeringRight D₂ E E).obj (shiftFunctor E m) :=
  letI := liftingShiftSnd L₁ L₂ W₁ W₂ F F' m
  lift₂NatIso L₁ L₂ W₁ W₂ _ _ _ _ (shiftIsoSnd F m)

/-- The component of `shiftIsoSndLift` at `(L₁.obj X₁, L₂.obj X₂)`, in terms of the lifting
isomorphism of `F'` and the commutation of `F.obj X₁` with the shift. -/
lemma shiftIsoSndLift_hom_app_app (m : M) (X₁ : C₁) (X₂ : C₂) :
    (((shiftIsoSndLift L₁ L₂ W₁ W₂ F F' m).hom.app (L₁.obj X₁)).app (L₂.obj X₂)) =
      (F'.obj (L₁.obj X₁)).map ((L₂.commShiftIso m).inv.app X₂) ≫
        ((Lifting₂.iso L₁ L₂ W₁ W₂ F F').hom.app X₁).app (X₂⟦m⟧) ≫
          ((F.obj X₁).commShiftIso m).hom.app X₂ ≫
            (((Lifting₂.iso L₁ L₂ W₁ W₂ F F').inv.app X₁).app X₂)⟦m⟧' := by
  let := liftingShiftSnd L₁ L₂ W₁ W₂ F F' m
  simp [shiftIsoSndLift, liftingShiftSnd, shiftIsoSnd]
  rfl

/-- Naturality of `shiftIsoSndLift` in the first variable, evaluated at an object of `D₂`. -/
@[reassoc]
lemma shiftIsoSndLift_hom_naturality_app (m : M) {Y₁ Y₁' : D₁} (g : Y₁ ⟶ Y₁') (Y₂ : D₂) :
    (F'.map g).app (Y₂⟦m⟧) ≫ ((shiftIsoSndLift L₁ L₂ W₁ W₂ F F' m).hom.app Y₁').app Y₂ =
      ((shiftIsoSndLift L₁ L₂ W₁ W₂ F F' m).hom.app Y₁).app Y₂ ≫ ((F'.map g).app Y₂)⟦m⟧' :=
  NatTrans.congr_app ((shiftIsoSndLift L₁ L₂ W₁ W₂ F F' m).hom.naturality g) Y₂

/-- At `L₁.obj X₁`, `shiftIsoSndLift` is the commutation of `F'.obj (L₁.obj X₁)` with the shift
descended from that of `F.obj X₁`. -/
lemma shiftIsoSndLift_app_eq (m : M) (X₁ : C₁) :
    letI := Lifting₂.fst L₁ L₂ W₁ W₂ F F' X₁
    (shiftIsoSndLift L₁ L₂ W₁ W₂ F F' m).app (L₁.obj X₁) =
      Functor.commShiftOfLocalization.iso L₂ W₂ (F.obj X₁) (F'.obj (L₁.obj X₁)) m := by
  let := Lifting₂.fst L₁ L₂ W₁ W₂ F F' X₁
  ext1
  refine natTrans_ext L₂ W₂ (fun X₂ ↦ ?_)
  rw [Iso.app_hom, shiftIsoSndLift_hom_app_app, Functor.commShiftOfLocalization.iso_hom_app]
  rfl

/-- The commutation of `F'.obj Y₁` with the shift, descended from that of the functors
`F.obj X₁`. -/
@[instance_reducible]
def commShiftSnd (Y₁ : D₁) : (F'.obj Y₁).CommShift M where
  commShiftIso m := (shiftIsoSndLift L₁ L₂ W₁ W₂ F F' m).app Y₁
  commShiftIso_zero := by
    let Z : F' ⋙ (whiskeringLeft D₂ D₂ E).obj (shiftFunctor D₂ (0 : M)) ⟶
        F' ⋙ (whiskeringRight D₂ E E).obj (shiftFunctor E (0 : M)) :=
      { app Y := (CommShift.isoZero (F'.obj Y) M).hom
        naturality _ _ g := by
          ext Y₂
          simp only [comp_obj, whiskeringLeft_obj_obj, whiskeringRight_obj_obj,
            NatTrans.comp_app, Functor.comp_map, whiskeringLeft_obj_map, whiskerLeft_app,
            CommShift.isoZero_hom_app, whiskeringRight_obj_map, whiskerRight_app, assoc]
          rw [← NatTrans.naturality_assoc]
          exact congrArg _ ((shiftFunctorZero E M).inv.naturality ((F'.map g).app Y₂)) }
    have h : (shiftIsoSndLift L₁ L₂ W₁ W₂ F F' 0).hom = Z := by
      refine natTrans_ext L₁ W₁ (fun X₁ ↦ ?_)
      let := Lifting₂.fst L₁ L₂ W₁ W₂ F F' X₁
      let := Functor.commShiftOfLocalization L₂ W₂ M (F.obj X₁) (F'.obj (L₁.obj X₁))
      rw [← Iso.app_hom, shiftIsoSndLift_app_eq]
      exact congrArg Iso.hom ((F'.obj (L₁.obj X₁)).commShiftIso_zero M)
    ext1
    exact NatTrans.congr_app h Y₁
  commShiftIso_add a b := by
    let Z : F' ⋙ (whiskeringLeft D₂ D₂ E).obj (shiftFunctor D₂ (a + b)) ⟶
        F' ⋙ (whiskeringRight D₂ E E).obj (shiftFunctor E (a + b)) :=
      { app Y := (CommShift.isoAdd ((shiftIsoSndLift L₁ L₂ W₁ W₂ F F' a).app Y)
            ((shiftIsoSndLift L₁ L₂ W₁ W₂ F F' b).app Y)).hom
        naturality Y Y' g := by
          ext Y₂
          have h1 := (F'.map g).naturality ((shiftFunctorAdd D₂ a b).hom.app Y₂)
          have h2 := shiftIsoSndLift_hom_naturality_app L₁ L₂ W₁ W₂ F F' b g (Y₂⟦a⟧)
          have h3 := shiftIsoSndLift_hom_naturality_app L₁ L₂ W₁ W₂ F F' a g Y₂
          have h4 := (shiftFunctorAdd E a b).inv.naturality ((F'.map g).app Y₂)
          dsimp at h1 h2 h3 h4 ⊢
          simp only [CommShift.isoAdd_hom_app, assoc, Iso.app_hom]
          rw [← reassoc_of% h1, reassoc_of% h2, ← Functor.map_comp_assoc, h3,
            Functor.map_comp_assoc, h4] }
    have h : (shiftIsoSndLift L₁ L₂ W₁ W₂ F F' (a + b)).hom = Z := by
      refine natTrans_ext L₁ W₁ (fun X₁ ↦ ?_)
      let := Lifting₂.fst L₁ L₂ W₁ W₂ F F' X₁
      let := Functor.commShiftOfLocalization L₂ W₂ M (F.obj X₁) (F'.obj (L₁.obj X₁))
      change ((shiftIsoSndLift L₁ L₂ W₁ W₂ F F' (a + b)).app (L₁.obj X₁)).hom =
        (CommShift.isoAdd ((shiftIsoSndLift L₁ L₂ W₁ W₂ F F' a).app (L₁.obj X₁))
            ((shiftIsoSndLift L₁ L₂ W₁ W₂ F F' b).app (L₁.obj X₁))).hom
      rw [shiftIsoSndLift_app_eq, shiftIsoSndLift_app_eq, shiftIsoSndLift_app_eq]
      exact congrArg Iso.hom ((F'.obj (L₁.obj X₁)).commShiftIso_add a b)
    ext1
    exact NatTrans.congr_app h Y₁

/-- The commutation isomorphism of `commShiftSnd` is given by the components of
`shiftIsoSndLift`. -/
lemma commShiftSnd_iso_hom_app (Y₁ : D₁) (m : M) (Y₂ : D₂) :
    letI : (F'.obj Y₁).CommShift M := commShiftSnd L₁ L₂ W₁ W₂ F F' Y₁
    ((F'.obj Y₁).commShiftIso m).hom.app Y₂ =
      ((shiftIsoSndLift L₁ L₂ W₁ W₂ F F' m).hom.app Y₁).app Y₂ := rfl

/-- For the commutations `commShiftSnd`, the natural transformation `F'.map g` commutes with the
shift. -/
lemma commShiftSnd_map {Y₁ Y₁' : D₁} (g : Y₁ ⟶ Y₁') :
    letI : (F'.obj Y₁).CommShift M := commShiftSnd L₁ L₂ W₁ W₂ F F' Y₁
    letI : (F'.obj Y₁').CommShift M := commShiftSnd L₁ L₂ W₁ W₂ F F' Y₁'
    NatTrans.CommShift (F'.map g) M := by
  let : (F'.obj Y₁).CommShift M := commShiftSnd L₁ L₂ W₁ W₂ F F' Y₁
  let : (F'.obj Y₁').CommShift M := commShiftSnd L₁ L₂ W₁ W₂ F F' Y₁'
  refine ⟨fun m ↦ ?_⟩
  ext Y₂
  exact (shiftIsoSndLift_hom_naturality_app L₁ L₂ W₁ W₂ F F' m g Y₂).symm

/-- The isomorphism `L₂ ⋙ F'.obj (L₁.obj X₁) ≅ F.obj X₁` of a lifting commutes with the shift,
for the commutation of `F'.obj (L₁.obj X₁)` with the shift descended from `F`. -/
lemma commShift_fst_iso_hom (X₁ : C₁) :
    letI : (F'.obj (L₁.obj X₁)).CommShift M := commShiftSnd L₁ L₂ W₁ W₂ F F' (L₁.obj X₁)
    letI := Lifting₂.fst L₁ L₂ W₁ W₂ F F' X₁
    NatTrans.CommShift (Lifting.iso L₂ W₂ (F.obj X₁) (F'.obj (L₁.obj X₁))).hom M := by
  let : (F'.obj (L₁.obj X₁)).CommShift M := commShiftSnd L₁ L₂ W₁ W₂ F F' (L₁.obj X₁)
  let := Lifting₂.fst L₁ L₂ W₁ W₂ F F' X₁
  refine ⟨fun a ↦ ?_⟩
  ext X₂
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.commShiftIso_comp_hom_app, commShiftSnd_iso_hom_app, shiftIsoSndLift_hom_app_app]
  have e : ∀ Y₂, (Lifting.iso L₂ W₂ (F.obj X₁) (F'.obj (L₁.obj X₁))).hom.app Y₂ =
      ((Lifting₂.iso L₁ L₂ W₁ W₂ F F').hom.app X₁).app Y₂ := fun _ ↦ rfl
  rw [e, e]
  simp

end

end CategoryTheory.Localization.Lifting₂

namespace CategoryTheory.Functor.CommShift₂

variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]
  {M : Type*} [AddCommMonoid M] [HasShift C₁ M] [HasShift C₂ M] [HasShift D M]
  (G : C₁ ⥤ C₂ ⥤ D) (h : CommShift₂Setup D M)
  [∀ X₁, (G.obj X₁).CommShift M] [∀ X₂, (G.flip.obj X₂).CommShift M]
  [∀ {X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁), NatTrans.CommShift (G.map f) M]
  [∀ {X₂ Y₂ : C₂} (g : X₂ ⟶ Y₂), NatTrans.CommShift (G.flip.map g) M]

omit [∀ {X₂ Y₂ : C₂} (g : X₂ ⟶ Y₂), NatTrans.CommShift (G.flip.map g) M] in
/-- Naturality in the first variable of the left-hand side of the compatibility equation of
`Functor.CommShift₂`. -/
lemma comm_lhs_naturality_fst {Y₁ Y₁' : C₁} (g : Y₁ ⟶ Y₁') (Y₂ : C₂) (m n : M) :
    (G.map (g⟦m⟧')).app (Y₂⟦n⟧) ≫ ((G.obj (Y₁'⟦m⟧)).commShiftIso n).hom.app Y₂ ≫
        (((G.flip.obj Y₂).commShiftIso m).hom.app Y₁')⟦n⟧' =
      (((G.obj (Y₁⟦m⟧)).commShiftIso n).hom.app Y₂ ≫
        (((G.flip.obj Y₂).commShiftIso m).hom.app Y₁)⟦n⟧') ≫ (((G.map g).app Y₂)⟦m⟧')⟦n⟧' := by
  have h₁ : (G.map (g⟦m⟧')).app Y₂ ≫ ((G.flip.obj Y₂).commShiftIso m).hom.app Y₁' =
      ((G.flip.obj Y₂).commShiftIso m).hom.app Y₁ ≫ ((G.map g).app Y₂)⟦m⟧' :=
    (G.flip.obj Y₂).commShiftIso_hom_naturality g m
  rw [← NatTrans.shift_app_comm_assoc (G.map (g⟦m⟧')) n Y₂, ← Functor.map_comp, h₁,
    Functor.map_comp, assoc]

omit [∀ {X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁), NatTrans.CommShift (G.map f) M] in
/-- Naturality in the second variable of the left-hand side of the compatibility equation of
`Functor.CommShift₂`. -/
lemma comm_lhs_naturality_snd (Y₁ : C₁) {Y₂ Y₂' : C₂} (g : Y₂ ⟶ Y₂') (m n : M) :
    (G.obj (Y₁⟦m⟧)).map (g⟦n⟧') ≫ ((G.obj (Y₁⟦m⟧)).commShiftIso n).hom.app Y₂' ≫
        (((G.flip.obj Y₂').commShiftIso m).hom.app Y₁)⟦n⟧' =
      (((G.obj (Y₁⟦m⟧)).commShiftIso n).hom.app Y₂ ≫
        (((G.flip.obj Y₂).commShiftIso m).hom.app Y₁)⟦n⟧') ≫ (((G.obj Y₁).map g)⟦m⟧')⟦n⟧' := by
  have h₁ : (G.obj (Y₁⟦m⟧)).map g ≫ ((G.flip.obj Y₂').commShiftIso m).hom.app Y₁ =
      ((G.flip.obj Y₂).commShiftIso m).hom.app Y₁ ≫ ((G.obj Y₁).map g)⟦m⟧' :=
    (NatTrans.shift_app_comm (G.flip.map g) m Y₁).symm
  rw [(G.obj (Y₁⟦m⟧)).commShiftIso_hom_naturality_assoc g n, ← Functor.map_comp, h₁,
    Functor.map_comp, assoc]

/-- Naturality of the sign-corrected inverse of the commutation of shifts. -/
private lemma shiftComm_inv_ε_naturality {X Y : D} (f : X ⟶ Y) (m n : M) :
    (f⟦n⟧')⟦m⟧' ≫ (shiftComm Y m n).inv ≫ (h.ε m n).val.app _ =
      (shiftComm X m n).inv ≫ (h.ε m n).val.app _ ≫ (f⟦m⟧')⟦n⟧' := by
  have h₃ : (f⟦n⟧')⟦m⟧' ≫ (shiftComm Y m n).inv = (shiftComm X m n).inv ≫ (f⟦m⟧')⟦n⟧' :=
    (shiftFunctorComm D m n).inv.naturality f
  rw [reassoc_of% h₃, CatCenter.naturality]

omit [∀ {X₂ Y₂ : C₂} (g : X₂ ⟶ Y₂), NatTrans.CommShift (G.flip.map g) M] in
/-- Naturality in the first variable of the right-hand side of the compatibility equation of
`Functor.CommShift₂`. -/
lemma comm_rhs_naturality_fst {Y₁ Y₁' : C₁} (g : Y₁ ⟶ Y₁') (Y₂ : C₂) (m n : M) :
    (G.map (g⟦m⟧')).app (Y₂⟦n⟧) ≫ ((G.flip.obj (Y₂⟦n⟧)).commShiftIso m).hom.app Y₁' ≫
        (((G.obj Y₁').commShiftIso n).hom.app Y₂)⟦m⟧' ≫
          (shiftComm ((G.obj Y₁').obj Y₂) m n).inv ≫ (h.ε m n).val.app _ =
      (((G.flip.obj (Y₂⟦n⟧)).commShiftIso m).hom.app Y₁ ≫
        (((G.obj Y₁).commShiftIso n).hom.app Y₂)⟦m⟧' ≫
          (shiftComm ((G.obj Y₁).obj Y₂) m n).inv ≫ (h.ε m n).val.app _) ≫
        (((G.map g).app Y₂)⟦m⟧')⟦n⟧' := by
  have h₁ : (G.map (g⟦m⟧')).app (Y₂⟦n⟧) ≫
      ((G.flip.obj (Y₂⟦n⟧)).commShiftIso m).hom.app Y₁' =
      ((G.flip.obj (Y₂⟦n⟧)).commShiftIso m).hom.app Y₁ ≫ ((G.map g).app (Y₂⟦n⟧))⟦m⟧' :=
    (G.flip.obj (Y₂⟦n⟧)).commShiftIso_hom_naturality g m
  have h₂ : (G.map g).app (Y₂⟦n⟧) ≫ ((G.obj Y₁').commShiftIso n).hom.app Y₂ =
      ((G.obj Y₁).commShiftIso n).hom.app Y₂ ≫ ((G.map g).app Y₂)⟦n⟧' :=
    (NatTrans.shift_app_comm (G.map g) n Y₂).symm
  rw [reassoc_of% h₁, ← Functor.map_comp_assoc, h₂, Functor.map_comp_assoc,
    shiftComm_inv_ε_naturality]
  simp only [assoc]

omit [∀ {X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁), NatTrans.CommShift (G.map f) M] in
/-- Naturality in the second variable of the right-hand side of the compatibility equation of
`Functor.CommShift₂`. -/
lemma comm_rhs_naturality_snd (Y₁ : C₁) {Y₂ Y₂' : C₂} (g : Y₂ ⟶ Y₂') (m n : M) :
    (G.obj (Y₁⟦m⟧)).map (g⟦n⟧') ≫ ((G.flip.obj (Y₂'⟦n⟧)).commShiftIso m).hom.app Y₁ ≫
        (((G.obj Y₁).commShiftIso n).hom.app Y₂')⟦m⟧' ≫
          (shiftComm ((G.obj Y₁).obj Y₂') m n).inv ≫ (h.ε m n).val.app _ =
      (((G.flip.obj (Y₂⟦n⟧)).commShiftIso m).hom.app Y₁ ≫
        (((G.obj Y₁).commShiftIso n).hom.app Y₂)⟦m⟧' ≫
          (shiftComm ((G.obj Y₁).obj Y₂) m n).inv ≫ (h.ε m n).val.app _) ≫
        (((G.obj Y₁).map g)⟦m⟧')⟦n⟧' := by
  have h₁ : (G.obj (Y₁⟦m⟧)).map (g⟦n⟧') ≫
      ((G.flip.obj (Y₂'⟦n⟧)).commShiftIso m).hom.app Y₁ =
      ((G.flip.obj (Y₂⟦n⟧)).commShiftIso m).hom.app Y₁ ≫ ((G.obj Y₁).map (g⟦n⟧'))⟦m⟧' :=
    (NatTrans.shift_app_comm (G.flip.map (g⟦n⟧')) m Y₁).symm
  have h₂ : (G.obj Y₁).map (g⟦n⟧') ≫ ((G.obj Y₁).commShiftIso n).hom.app Y₂' =
      ((G.obj Y₁).commShiftIso n).hom.app Y₂ ≫ ((G.obj Y₁).map g)⟦n⟧' :=
    (G.obj Y₁).commShiftIso_hom_naturality g n
  rw [reassoc_of% h₁, ← Functor.map_comp_assoc, h₂, Functor.map_comp_assoc,
    shiftComm_inv_ε_naturality]
  simp only [assoc]

/-- The equation of `Functor.CommShift₂` holds at all pairs of objects as soon as it holds on
pairs of objects in the essential images of two essentially surjective functors. -/
lemma comm_of_essSurj {C₁' C₂' : Type*} [Category C₁'] [Category C₂'] (L₁ : C₁' ⥤ C₁)
    (L₂ : C₂' ⥤ C₂) [L₁.EssSurj] [L₂.EssSurj] (m n : M)
    (H : ∀ (X₁ : C₁') (X₂ : C₂'),
      ((G.obj ((L₁.obj X₁)⟦m⟧)).commShiftIso n).hom.app (L₂.obj X₂) ≫
        (((G.flip.obj (L₂.obj X₂)).commShiftIso m).hom.app (L₁.obj X₁))⟦n⟧' =
      ((G.flip.obj ((L₂.obj X₂)⟦n⟧)).commShiftIso m).hom.app (L₁.obj X₁) ≫
        (((G.obj (L₁.obj X₁)).commShiftIso n).hom.app (L₂.obj X₂))⟦m⟧' ≫
          (shiftComm ((G.obj (L₁.obj X₁)).obj (L₂.obj X₂)) m n).inv ≫ (h.ε m n).val.app _)
    (Y₁ : C₁) (Y₂ : C₂) :
      ((G.obj (Y₁⟦m⟧)).commShiftIso n).hom.app Y₂ ≫
        (((G.flip.obj Y₂).commShiftIso m).hom.app Y₁)⟦n⟧' =
      ((G.flip.obj (Y₂⟦n⟧)).commShiftIso m).hom.app Y₁ ≫
        (((G.obj Y₁).commShiftIso n).hom.app Y₂)⟦m⟧' ≫
          (shiftComm ((G.obj Y₁).obj Y₂) m n).inv ≫ (h.ε m n).val.app _ := by
  let e₁ := L₁.objObjPreimageIso Y₁
  let e₂ := L₂.objObjPreimageIso Y₂
  have H₁ := H (L₁.objPreimage Y₁) (L₂.objPreimage Y₂)
  have H₂ : ((G.obj ((L₁.obj (L₁.objPreimage Y₁))⟦m⟧)).commShiftIso n).hom.app Y₂ ≫
        (((G.flip.obj Y₂).commShiftIso m).hom.app (L₁.obj (L₁.objPreimage Y₁)))⟦n⟧' =
      ((G.flip.obj (Y₂⟦n⟧)).commShiftIso m).hom.app (L₁.obj (L₁.objPreimage Y₁)) ≫
        (((G.obj (L₁.obj (L₁.objPreimage Y₁))).commShiftIso n).hom.app Y₂)⟦m⟧' ≫
          (shiftComm ((G.obj (L₁.obj (L₁.objPreimage Y₁))).obj Y₂) m n).inv ≫
            (h.ε m n).val.app _ := by
    rw [← cancel_epi ((G.obj ((L₁.obj (L₁.objPreimage Y₁))⟦m⟧)).map (e₂.hom⟦n⟧')),
      comm_lhs_naturality_snd, comm_rhs_naturality_snd, H₁]
  rw [← cancel_epi ((G.map (e₁.hom⟦m⟧')).app (Y₂⟦n⟧)), comm_lhs_naturality_fst,
    comm_rhs_naturality_fst, H₂]

end CategoryTheory.Functor.CommShift₂

namespace CategoryTheory.Localization.Lifting₂

variable {C₁ C₂ D₁ D₂ E : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
  [Category E]
  (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂] [W₁.ContainsIdentities] [W₂.ContainsIdentities]
  (F : C₁ ⥤ C₂ ⥤ E) (F' : D₁ ⥤ D₂ ⥤ E) [Lifting₂ L₁ L₂ W₁ W₂ F F']
  {M : Type*} [AddCommMonoid M] [HasShift C₁ M] [HasShift C₂ M] [HasShift D₁ M] [HasShift D₂ M]
  [HasShift E M] [L₁.CommShift M] [L₂.CommShift M] (h : CommShift₂Setup E M) [F.CommShift₂ h]

omit [L₁.IsLocalization W₁] [L₂.IsLocalization W₂] [W₁.ContainsIdentities]
  [W₂.ContainsIdentities] [AddCommMonoid M] [HasShift C₁ M] [HasShift C₂ M] [HasShift D₁ M]
  [HasShift D₂ M] [HasShift E M] [L₁.CommShift M] [L₂.CommShift M] [F.CommShift₂ h] in
/-- The lifting isomorphism of `F'.flip` has the same components as that of `F'`. -/
lemma flip_iso_hom_app_app (X₁ : C₁) (X₂ : C₂) :
    ((Lifting₂.iso L₂ L₁ W₂ W₁ F.flip F'.flip).hom.app X₂).app X₁ =
      ((Lifting₂.iso L₁ L₂ W₁ W₂ F F').hom.app X₁).app X₂ := rfl

omit [L₁.IsLocalization W₁] [L₂.IsLocalization W₂] [W₁.ContainsIdentities]
  [W₂.ContainsIdentities] [AddCommMonoid M] [HasShift C₁ M] [HasShift C₂ M] [HasShift D₁ M]
  [HasShift D₂ M] [HasShift E M] [L₁.CommShift M] [L₂.CommShift M] [F.CommShift₂ h] in
/-- The inverse of the lifting isomorphism of `F'.flip` has the same components as that of
`F'`. -/
lemma flip_iso_inv_app_app (X₁ : C₁) (X₂ : C₂) :
    ((Lifting₂.iso L₂ L₁ W₂ W₁ F.flip F'.flip).inv.app X₂).app X₁ =
      ((Lifting₂.iso L₁ L₂ W₁ W₂ F F').inv.app X₁).app X₂ := rfl

include h in
/-- The compatibility equation of `Functor.CommShift₂` for `F'`, with the commutations
`commShiftSnd`, at a pair of objects `(L₁.obj X₁, L₂.obj X₂)`. -/
lemma commShift₂_comm_obj (X₁ : C₁) (X₂ : C₂) (m n : M) :
    letI : ∀ Y₁, (F'.obj Y₁).CommShift M := commShiftSnd L₁ L₂ W₁ W₂ F F'
    letI : ∀ Y₂, (F'.flip.obj Y₂).CommShift M := commShiftSnd L₂ L₁ W₂ W₁ F.flip F'.flip
    ((F'.obj ((L₁.obj X₁)⟦m⟧)).commShiftIso n).hom.app (L₂.obj X₂) ≫
        (((F'.flip.obj (L₂.obj X₂)).commShiftIso m).hom.app (L₁.obj X₁))⟦n⟧' =
      ((F'.flip.obj ((L₂.obj X₂)⟦n⟧)).commShiftIso m).hom.app (L₁.obj X₁) ≫
        (((F'.obj (L₁.obj X₁)).commShiftIso n).hom.app (L₂.obj X₂))⟦m⟧' ≫
          (shiftComm ((F'.obj (L₁.obj X₁)).obj (L₂.obj X₂)) m n).inv ≫ (h.ε m n).val.app _ := by
  let : ∀ Y₁, (F'.obj Y₁).CommShift M := commShiftSnd L₁ L₂ W₁ W₂ F F'
  let : ∀ Y₂, (F'.flip.obj Y₂).CommShift M := commShiftSnd L₂ L₁ W₂ W₁ F.flip F'.flip
  have : ∀ {Y₁ Y₁' : D₁} (g : Y₁ ⟶ Y₁'), NatTrans.CommShift (F'.map g) M :=
    fun g ↦ commShiftSnd_map L₁ L₂ W₁ W₂ F F' g
  have : ∀ {Y₂ Y₂' : D₂} (g : Y₂ ⟶ Y₂'), NatTrans.CommShift (F'.flip.map g) M :=
    fun g ↦ commShiftSnd_map L₂ L₁ W₂ W₁ F.flip F'.flip g
  let u := (L₁.commShiftIso m).app X₁
  let v := (L₂.commShiftIso n).app X₂
  have A := (NatTrans.shift_app_comm (F'.map u.hom) n (L₂.obj X₂)).symm
  have B : (F'.obj ((L₁.obj X₁)⟦m⟧)).map v.hom ≫
      ((F'.flip.obj ((L₂.obj X₂)⟦n⟧)).commShiftIso m).hom.app (L₁.obj X₁) =
      ((F'.flip.obj (L₂.obj (X₂⟦n⟧))).commShiftIso m).hom.app (L₁.obj X₁) ≫
        ((F'.obj (L₁.obj X₁)).map v.hom)⟦m⟧' :=
    (NatTrans.shift_app_comm (F'.flip.map v.hom) m (L₁.obj X₁)).symm
  have hφ : (F'.obj (L₁.obj (X₁⟦m⟧))).map v.hom ≫ (F'.map u.hom).app ((L₂.obj X₂)⟦n⟧) =
      (F'.map u.hom).app (L₂.obj (X₂⟦n⟧)) ≫ (F'.obj ((L₁.obj X₁)⟦m⟧)).map v.hom :=
    (F'.map u.hom).naturality v.hom
  rw [← cancel_epi ((F'.obj (L₁.obj (X₁⟦m⟧))).map v.hom ≫
    (F'.map u.hom).app ((L₂.obj X₂)⟦n⟧))]
  conv_lhs => rw [assoc, reassoc_of% A]
  conv_rhs => rw [hφ, assoc]
  rw [reassoc_of% B]
  simp only [commShiftSnd_iso_hom_app, shiftIsoSndLift_hom_app_app, flip_iso_hom_app_app,
    flip_iso_inv_app_app]
  simp only [comp_obj, flip_obj_obj, Iso.app_hom, whiskeringLeft₂_obj_obj_obj_obj_obj, flip_obj_map,
    map_comp, cancelIso, assoc, Iso.app_inv, v, u]
  have h₃ : ((((Lifting₂.iso L₁ L₂ W₁ W₂ F F').inv.app X₁).app X₂)⟦n⟧')⟦m⟧' ≫
      (shiftFunctorComm E m n).inv.app ((F'.obj (L₁.obj X₁)).obj (L₂.obj X₂)) =
      (shiftFunctorComm E m n).inv.app ((F.obj X₁).obj X₂) ≫
        ((((Lifting₂.iso L₁ L₂ W₁ W₂ F F').inv.app X₁).app X₂)⟦m⟧')⟦n⟧' :=
    (shiftFunctorComm E m n).inv.naturality _
  rw [reassoc_of% h₃, CatCenter.naturality, reassoc_of% (F.commShift₂_comm h X₁ X₂ m n)]
  rfl

/-- **A bifunctor induced on localized categories by a bifunctor commuting with the shifts in
both variables commutes with the shifts in both variables.** This is the two-variable analogue
of `Functor.commShiftOfLocalization`. -/
@[instance_reducible]
def commShift₂ : F'.CommShift₂ h where
  commShiftObj := commShiftSnd L₁ L₂ W₁ W₂ F F'
  commShift_map f := commShiftSnd_map L₁ L₂ W₁ W₂ F F' f
  commShiftFlipObj := commShiftSnd L₂ L₁ W₂ W₁ F.flip F'.flip
  commShift_flip_map g := commShiftSnd_map L₂ L₁ W₂ W₁ F.flip F'.flip g
  comm Y₁ Y₂ m n := by
    let : ∀ Y₁, (F'.obj Y₁).CommShift M := commShiftSnd L₁ L₂ W₁ W₂ F F'
    let : ∀ Y₂, (F'.flip.obj Y₂).CommShift M := commShiftSnd L₂ L₁ W₂ W₁ F.flip F'.flip
    have : ∀ {Y₁ Y₁' : D₁} (g : Y₁ ⟶ Y₁'), NatTrans.CommShift (F'.map g) M :=
      fun g ↦ commShiftSnd_map L₁ L₂ W₁ W₂ F F' g
    have : ∀ {Y₂ Y₂' : D₂} (g : Y₂ ⟶ Y₂'), NatTrans.CommShift (F'.flip.map g) M :=
      fun g ↦ commShiftSnd_map L₂ L₁ W₂ W₁ F.flip F'.flip g
    have := Localization.essSurj L₁ W₁
    have := Localization.essSurj L₂ W₂
    exact Functor.CommShift₂.comm_of_essSurj F' h L₁ L₂ m n
      (fun X₁ X₂ ↦ commShift₂_comm_obj L₁ L₂ W₁ W₂ F F' h X₁ X₂ m n) Y₁ Y₂

end CategoryTheory.Localization.Lifting₂

namespace CategoryTheory.Functor.CommShift₂

variable {C₁ C₂ D D' : Type*} [Category C₁] [Category C₂] [Category D] [Category D']
  [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift D ℤ] [HasShift D' ℤ] [Preadditive D] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D n).Additive] [∀ n : ℤ, (shiftFunctor D' n).Additive]

/-- An additive functor carries the sign `(-1)^(pq)` of the standard setup to the sign of the
standard setup. -/
lemma map_int_ε_app (H : D ⥤ D') [H.Additive] (p q : ℤ) (X : D) :
    H.map (((CommShift₂Setup.int (D := D)).ε p q).val.app X) =
      ((CommShift₂Setup.int (D := D')).ε p q).val.app (H.obj X) := by
  simp [Units.smul_def]

end CategoryTheory.Functor.CommShift₂

end
