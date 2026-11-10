module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.GuitartExact.KanExtension
public import Mathlib.CategoryTheory.GuitartExact.Opposite
public import Mathlib.CategoryTheory.Sites.CoverLifting

/-!
# The base change map of sheaves along a 2-commutative square of sites

Let
```
      T
  C₁ ---> C₂
  |        |
 L|   w    |R
  v        v
  C₃ ---> C₄
      B
```
be a square of functors between sites which commutes up to a natural transformation
`w : T ⋙ R ⟶ L ⋙ B`, with `T` and `B` continuous and `L` and `R` both continuous and
cocontinuous. Inverse image of sheaves along a continuous functor is restriction, so `w` induces
a 2-cell `B⁻¹ ⋙ L⁻¹ ⟶ R⁻¹ ⋙ T⁻¹` between the two composite inverse images, and restriction along
`L` and `R` is left adjoint to the direct images `L_*`, `R_*`. The mate of that 2-cell under the
two adjunctions is the **base change map**
`B⁻¹R_* ⟶ L_*T⁻¹`:
at a sheaf `F` on `C₂` it is the composite
`B⁻¹R_*F ⟶ L_*L⁻¹B⁻¹R_*F ⟶ L_*T⁻¹R⁻¹R_*F ⟶ L_*T⁻¹F`
of the unit of `L⁻¹ ⊣ L_*`, the 2-cell, and the counit of `R⁻¹ ⊣ R_*`.

On underlying presheaves the two adjunctions are the right Kan extension adjunctions, so the base
change map is the base change of right Kan extensions of the opposite square,
`CategoryTheory.TwoSquare.ranBaseChange`. In particular it is an isomorphism when the square is
Guitart exact.

## Main definitions

* `CategoryTheory.TwoSquare.presheafInverseImage`: the 2-cell of restrictions of presheaves
  induced by `w`.
* `CategoryTheory.TwoSquare.sheafInverseImage`: the 2-cell `B⁻¹ ⋙ L⁻¹ ⟶ R⁻¹ ⋙ T⁻¹` of inverse
  images of sheaves induced by `w`.
* `CategoryTheory.TwoSquare.sheafBaseChange`: the base change map `R_* ⋙ B⁻¹ ⟶ T⁻¹ ⋙ L_*`.

## Main results

* `CategoryTheory.TwoSquare.mateEquiv_presheafInverseImage`: the base change of right Kan
  extensions of the opposite square is the mate of the 2-cell of restrictions under the right Kan
  extension adjunctions.
* `CategoryTheory.TwoSquare.sheafBaseChange_app_hom`: on underlying presheaves, the base change
  map is `CategoryTheory.TwoSquare.ranBaseChange` of the opposite square.
* `CategoryTheory.TwoSquare.isIso_sheafBaseChange`: it is an isomorphism when the square is
  Guitart exact.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory.TwoSquare

variable {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄} (w : TwoSquare T L R B)
  (A : Type*) [Category* A] (J₁ : GrothendieckTopology C₁) (J₂ : GrothendieckTopology C₂)
  (J₃ : GrothendieckTopology C₃) (J₄ : GrothendieckTopology C₄)

/-- The 2-cell `B⁻¹ ⋙ L⁻¹ ⟶ R⁻¹ ⋙ T⁻¹` between the two composite restrictions of presheaves
induced by `w : T ⋙ R ⟶ L ⋙ B`: on a presheaf `P` on `C₄` it is `P` applied to the opposite of
`w`. -/
@[simps!]
def presheafInverseImage :
    TwoSquare ((whiskeringLeft _ _ A).obj B.op) ((whiskeringLeft _ _ A).obj R.op)
      ((whiskeringLeft _ _ A).obj L.op) ((whiskeringLeft _ _ A).obj T.op) :=
  TwoSquare.mk _ _ _ _
    { app := fun P => Functor.whiskerRight (NatTrans.op w) P
      naturality := fun P P' φ => by
        ext X
        exact (φ.naturality (w.app X.unop).op).symm }

/-- **The base change of right Kan extensions of the opposite square is a mate**: it is the mate,
under the right Kan extension adjunctions of `R.op` and `L.op`, of the 2-cell of restrictions
`CategoryTheory.TwoSquare.presheafInverseImage`. -/
theorem mateEquiv_presheafInverseImage [∀ F : C₁ᵒᵖ ⥤ A, L.op.HasRightKanExtension F]
    [∀ F : C₂ᵒᵖ ⥤ A, R.op.HasRightKanExtension F] :
    (mateEquiv (R.op.ranAdjunction A) (L.op.ranAdjunction A)
      (w.presheafInverseImage A)) = w.op.ranBaseChange := by
  refine NatTrans.ext (funext fun F => ?_)
  rw [TwoSquare.ranBaseChange_app]
  refine ((L.op.ranAdjunction A).homEquiv _ _).symm.injective ?_
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  refine (mateEquiv_counit (R.op.ranAdjunction A) (L.op.ranAdjunction A)
    (w.presheafInverseImage A) F).trans ?_
  rw [Functor.ranAdjunction_counit]
  ext X
  simp

section InverseImage

variable [T.IsContinuous J₁ J₂] [L.IsContinuous J₁ J₃] [R.IsContinuous J₂ J₄]
  [B.IsContinuous J₃ J₄]

/-- The 2-cell `B⁻¹ ⋙ L⁻¹ ⟶ R⁻¹ ⋙ T⁻¹` between the two composite inverse images of sheaves
induced by `w : T ⋙ R ⟶ L ⋙ B`: both composites are restriction along a composite functor, and
on a sheaf `F` on `C₄` it is `F` applied to the opposite of `w`. -/
@[simps!]
def sheafInverseImage :
    TwoSquare (B.sheafPushforwardContinuous A J₃ J₄) (R.sheafPushforwardContinuous A J₂ J₄)
      (L.sheafPushforwardContinuous A J₁ J₃) (T.sheafPushforwardContinuous A J₁ J₂) :=
  TwoSquare.mk _ _ _ _
    { app := fun F => ⟨Functor.whiskerRight (NatTrans.op w) F.obj⟩
      naturality := fun F F' φ => by
        ext X
        exact (φ.hom.naturality (w.app X.unop).op).symm }

end InverseImage

section BaseChange

variable [T.IsContinuous J₁ J₂] [L.IsContinuous J₁ J₃] [L.IsCocontinuous J₁ J₃]
  [R.IsContinuous J₂ J₄] [R.IsCocontinuous J₂ J₄] [B.IsContinuous J₃ J₄]
  [∀ F : C₁ᵒᵖ ⥤ A, L.op.HasPointwiseRightKanExtension F]
  [∀ F : C₂ᵒᵖ ⥤ A, R.op.HasPointwiseRightKanExtension F]

/-- **The base change map** `B⁻¹R_* ⟶ L_*T⁻¹` of sheaves along the square `w`: the mate, under
the adjunctions `R⁻¹ ⊣ R_*` and `L⁻¹ ⊣ L_*`, of the 2-cell of inverse images
`CategoryTheory.TwoSquare.sheafInverseImage`. -/
noncomputable def sheafBaseChange :
    R.sheafPushforwardCocontinuous A J₂ J₄ ⋙ B.sheafPushforwardContinuous A J₃ J₄ ⟶
      T.sheafPushforwardContinuous A J₁ J₂ ⋙ L.sheafPushforwardCocontinuous A J₁ J₃ :=
  (mateEquiv (R.sheafAdjunctionCocontinuous A J₂ J₄) (L.sheafAdjunctionCocontinuous A J₁ J₃)
    (w.sheafInverseImage A J₁ J₂ J₃ J₄))

/-- **The base change map on underlying presheaves.** The underlying transformation of presheaves
of the base change map at a sheaf `F` is the base change of right Kan extensions of the opposite
square at the underlying presheaf of `F`. -/
theorem sheafBaseChange_app_hom (F : Sheaf J₂ A) :
    ((w.sheafBaseChange A J₁ J₂ J₃ J₄).app F).hom = w.op.ranBaseChange.app F.obj := by
  rw [← mateEquiv_presheafInverseImage]
  have hc : (T.sheafPushforwardContinuous A J₁ J₂).map
      ((R.sheafAdjunctionCocontinuous A J₂ J₄).counit.app F) =
        ⟨((whiskeringLeft _ _ A).obj T.op).map ((R.op.ranAdjunction A).counit.app F.obj)⟩ := by
    ext1
    change Functor.whiskerLeft T.op ((R.sheafAdjunctionCocontinuous A J₂ J₄).counit.app F).hom = _
    rw [Functor.sheafAdjunctionCocontinuous_counit_app_hom]
    rfl
  simp only [sheafBaseChange, mateEquiv_apply, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app, Functor.comp_obj, Functor.comp_map,
    Category.id_comp, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.id_hom, Functor.sheafAdjunctionCocontinuous_unit_app_hom,
    hc]
  rfl

/-- **The base change map of a Guitart exact square is an isomorphism**: on underlying presheaves
it is the base change of right Kan extensions of the opposite square, which is invertible for a
Guitart exact square, and `sheafToPresheaf` reflects isomorphisms. -/
instance isIso_sheafBaseChange [w.GuitartExact] : IsIso (w.sheafBaseChange A J₁ J₂ J₃ J₄) := by
  refine (NatTrans.isIso_iff_isIso_app _).2 fun F => ?_
  have : IsIso ((sheafToPresheaf J₃ A).map ((w.sheafBaseChange A J₁ J₂ J₃ J₄).app F)) := by
    change IsIso ((w.sheafBaseChange A J₁ J₂ J₃ J₄).app F).hom
    rw [sheafBaseChange_app_hom]
    exact w.op.isIso_ranBaseChange_app F.obj
  exact isIso_of_reflects_iso _ (sheafToPresheaf J₃ A)

end BaseChange

end CategoryTheory.TwoSquare

end
