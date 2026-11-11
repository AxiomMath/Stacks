module

public import StacksFrontier.CategoryTheory.Localization.RightFraction.Defs

/-!
# The localization functor of a right multiplicative system (Stacks 04VK)

Let `W` be a right multiplicative system on `C` (`W.HasRightCalculusOfFractions`, Stacks 04VC)
and let `RightLocalization W` be the category of right fractions of Stacks 04VH, whose
morphisms `X ⟶ Y` are classes of pairs `(f : X' ⟶ Y, s : X' ⟶ X)` with `s ∈ W`. This file
proves Stacks 04VK:

1. `X ↦ X`, `f ↦ (f, 𝟙 X)` is a functor `RightLocalization.Q W : C ⥤ RightLocalization W`
   (`RightLocalization.Q_obj`, `RightLocalization.Q_map`);
2. `(RightLocalization.Q W).map s` is an isomorphism for `s ∈ W`
   (`RightLocalization.isIso_Q_map`);
3. every functor `G : C ⥤ D` inverting `W` is `RightLocalization.Q W ⋙ H` for a unique
   `H : RightLocalization W ⥤ D` (`RightLocalization.existsUnique_lift`).

Following the Stacks proof ("replace all categories by their opposites"), equalities of
morphisms of `RightLocalization W` are checked after sending a class of right fractions `φ`
to the class of the left fraction `φ.op` in `LeftFraction.Localization W.op`
(`RightLocalization.toOp`, which is injective and reverses composition), and the lift `H` is
the opposite of Mathlib's lift for `(Cᵒᵖ, W.op)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MorphismProperty

namespace CategoryTheory.MorphismProperty.RightLocalization

universe v u v' u'

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
variable {D : Type u'} [Category.{v'} D]

/-- The class `f s⁻¹` of a right fraction `φ = (f, s)`, as a morphism of `RightLocalization W`. -/
def homMk {X Y : C} (φ : W.RightFraction X Y) : of W X ⟶ of W Y :=
  Hom.mk W φ

variable {W} in
lemma homMk_surjective {X Y : C} (f : of W X ⟶ of W Y) : ∃ φ, homMk W φ = f :=
  Quot.exists_rep f

lemma homMk_comp_homMk {X Y Z : C} (φ : W.RightFraction X Y) (ψ : W.RightFraction Y Z) :
    homMk W φ ≫ homMk W ψ = homMk W (RightFraction.comp W φ ψ) :=
  rfl

/-- A morphism of `RightLocalization W`, sent to the opposite left-fraction localization
`LeftFraction.Localization W.op`: the class of `φ` goes to the class of `φ.op`. -/
noncomputable def toOp {X Y : C} (f : of W X ⟶ of W Y) :
    (LeftFraction.Localization.Q W.op).obj (Opposite.op Y) ⟶
      (LeftFraction.Localization.Q W.op).obj (Opposite.op X) :=
  Quot.lift (fun φ : W.RightFraction X Y => LeftFraction.Localization.homMk φ.op)
    (fun φ φ' h => (RightFraction.homMk_op_eq_iff_rightFractionRel W φ φ').2 h) f

lemma toOp_homMk {X Y : C} (φ : W.RightFraction X Y) :
    toOp W (homMk W φ) = LeftFraction.Localization.homMk φ.op :=
  rfl

lemma toOp_injective {X Y : C} : Function.Injective (toOp W (X := X) (Y := Y)) := by
  intro f g h
  obtain ⟨φ, rfl⟩ := homMk_surjective f
  obtain ⟨ψ, rfl⟩ := homMk_surjective g
  exact Quot.sound ((RightFraction.homMk_op_eq_iff_rightFractionRel W φ ψ).1 h)

lemma toOp_comp {X Y Z : C} (f : of W X ⟶ of W Y) (g : of W Y ⟶ of W Z) :
    toOp W (f ≫ g) = toOp W g ≫ toOp W f := by
  obtain ⟨φ, rfl⟩ := homMk_surjective f
  obtain ⟨ψ, rfl⟩ := homMk_surjective g
  exact RightFraction.homMk_op_comp W φ ψ

lemma toOp_id (X : C) : toOp W (𝟙 (of W X)) = 𝟙 _ :=
  RightFraction.homMk_op_id W X

/-- **Stacks 04VK (1)**: the functor `Q : C ⥤ S⁻¹C` into the category of right fractions,
the identity on objects and sending `f : X ⟶ Y` to the class of the pair `(f, 𝟙 X)`. -/
@[stacks 04VK "(1)"]
noncomputable def Q : C ⥤ RightLocalization W where
  obj X := of W X
  map f := homMk W (RightFraction.ofHom W f)
  map_id _ := rfl
  map_comp f g := toOp_injective W (by
    rw [toOp_comp, toOp_homMk, toOp_homMk, toOp_homMk]
    exact (LeftFraction.Localization.Q W.op).map_comp g.op f.op)

/-- Stacks 04VK (1), objects: `Q` is the identity on objects. -/
lemma Q_obj (X : C) : (RightLocalization.Q W).obj X = of W X :=
  rfl

/-- Stacks 04VK (1), morphisms: `Q` sends `f : X ⟶ Y` to the class of the pair `(f, 𝟙 X)`. -/
lemma Q_map {X Y : C} (f : X ⟶ Y) :
    (RightLocalization.Q W).map f = homMk W (RightFraction.mk (𝟙 X) (W.id_mem X) f) :=
  rfl

lemma toOp_Q_map {X Y : C} (f : X ⟶ Y) :
    toOp W ((RightLocalization.Q W).map f) = (LeftFraction.Localization.Q W.op).map f.op :=
  rfl

/-- **Stacks 04VK (2)**: for `s ∈ W`, the morphism `Q s` is an isomorphism of
`RightLocalization W`; its inverse is the class of the pair `(𝟙 X, s)`. -/
@[stacks 04VK "(2)"]
theorem isIso_Q_map {X Y : C} (s : X ⟶ Y) (hs : W s) :
    IsIso ((RightLocalization.Q W).map s) :=
  ⟨homMk W (RightFraction.mk s hs (𝟙 X)),
    toOp_injective W ((toOp_comp W (X := X) (Y := Y) (Z := X) ((RightLocalization.Q W).map s)
      (homMk W (RightFraction.mk s hs (𝟙 X)))).trans
        ((LeftFraction.Localization.Qiso_inv_hom_id (W := W.op) s.op hs).trans
          (toOp_id W X).symm)),
    toOp_injective W ((toOp_comp W (X := Y) (Y := X) (Z := Y)
      (homMk W (RightFraction.mk s hs (𝟙 X))) ((RightLocalization.Q W).map s)).trans
        ((LeftFraction.Localization.Qiso_hom_inv_id (W := W.op) s.op hs).trans
          (toOp_id W Y).symm))⟩

lemma inverts : W.IsInvertedBy (RightLocalization.Q W) :=
  fun _ _ s hs => isIso_Q_map W s hs

instance {X Y : C} (φ : W.RightFraction X Y) : IsIso ((RightLocalization.Q W).map φ.s) :=
  isIso_Q_map W φ.s φ.hs

/-- `Q s ≫ f s⁻¹ = Q f` for the class `f s⁻¹` of a right fraction `(f, s)`. -/
lemma Q_map_s_comp_homMk {X Y : C} (φ : W.RightFraction X Y) :
    (RightLocalization.Q W).map φ.s ≫ homMk W φ = (RightLocalization.Q W).map φ.f := by
  refine toOp_injective W ((toOp_comp W (X := φ.X') (Y := X) (Z := Y)
    ((RightLocalization.Q W).map φ.s) (homMk W φ)).trans ?_)
  change LeftFraction.Localization.homMk φ.op ≫ (LeftFraction.Localization.Q W.op).map φ.s.op =
    (LeftFraction.Localization.Q W.op).map φ.f.op
  have h := LeftFraction.Localization.Q_map_comp_Qinv (W := W.op) φ.f.op φ.s.op φ.hs
  calc _ = ((LeftFraction.Localization.Q W.op).map φ.f.op ≫
          LeftFraction.Localization.Qinv φ.s.op φ.hs) ≫
        (LeftFraction.Localization.Q W.op).map φ.s.op := by rw [h]; rfl
    _ = _ := by
      rw [Category.assoc]
      exact (congrArg (_ ≫ ·) (LeftFraction.Localization.Qiso_inv_hom_id (W := W.op) φ.s.op
        φ.hs)).trans (Category.comp_id _)

/-- The class `f s⁻¹` of a right fraction `(f, s)` is `(Q s)⁻¹ ≫ Q f`. -/
lemma homMk_eq {X Y : C} (φ : W.RightFraction X Y) :
    homMk W φ = inv ((RightLocalization.Q W).map φ.s) ≫ (RightLocalization.Q W).map φ.f :=
  (IsIso.inv_hom_id_assoc ((RightLocalization.Q W).map φ.s) (homMk W φ)).symm.trans
    (congrArg (inv ((RightLocalization.Q W).map φ.s) ≫ ·) (Q_map_s_comp_homMk W φ))

variable {W}

/-- Mathlib's lift of `G.op` through the left-fraction localization of `(Cᵒᵖ, W.op)`. -/
noncomputable abbrev opLift (G : C ⥤ D) (hG : W.IsInvertedBy G) :
    LeftFraction.Localization W.op ⥤ Dᵒᵖ :=
  LeftFraction.Localization.StrictUniversalPropertyFixedTarget.lift G.op hG.op

/-- The functor `H : RightLocalization W ⥤ D` induced by a functor `G : C ⥤ D` inverting `W`:
it sends the class of `(f, s)` to `(G s)⁻¹ ≫ G f`. It is the opposite of Mathlib's lift of
`G.op` through `LeftFraction.Localization W.op`. -/
noncomputable def lift (G : C ⥤ D) (hG : W.IsInvertedBy G) : RightLocalization W ⥤ D where
  obj X := G.obj X.out
  map {X Y} f := ((opLift G hG).map (toOp W (X := X.out) (Y := Y.out) f)).unop
  map_id X :=
    (congrArg (fun g => ((opLift G hG).map g).unop) (toOp_id W X.out)).trans
      (congrArg Quiver.Hom.unop ((opLift G hG).map_id _))
  map_comp {X Y Z} f g :=
    (congrArg (fun g => ((opLift G hG).map g).unop)
      (toOp_comp W (X := X.out) (Y := Y.out) (Z := Z.out) f g)).trans
      (congrArg Quiver.Hom.unop ((opLift G hG).map_comp _ _))

lemma lift_map_homMk (G : C ⥤ D) (hG : W.IsInvertedBy G) {X Y : C}
    (φ : W.RightFraction X Y) :
    (lift G hG).map (homMk W φ) = φ.map G hG :=
  Quiver.Hom.op_inj (RightFraction.op_map φ G hG).symm

lemma fac (G : C ⥤ D) (hG : W.IsInvertedBy G) : RightLocalization.Q W ⋙ lift G hG = G :=
  Functor.hext (fun _ => rfl) (fun _ _ f => heq_of_eq
    ((lift_map_homMk G hG (RightFraction.ofHom W f)).trans (RightFraction.map_ofHom W f G hG)))

lemma eq_lift (H : RightLocalization W ⥤ D) :
    H = lift (RightLocalization.Q W ⋙ H) (fun _ _ s hs => by
      have := isIso_Q_map W s hs
      exact inferInstanceAs (IsIso (H.map ((RightLocalization.Q W).map s)))) := by
  refine Functor.hext (fun _ => rfl) (fun X Y f => heq_of_eq ?_)
  obtain ⟨φ, rfl⟩ := homMk_surjective (W := W) (X := X.out) (Y := Y.out) f
  refine (congrArg H.map (homMk_eq W φ)).trans ((H.map_comp _ _).trans ?_)
  refine (congrArg (fun g : H.obj ((RightLocalization.Q W).obj X.out) ⟶
      H.obj ((RightLocalization.Q W).obj φ.X') => g ≫ H.map ((RightLocalization.Q W).map φ.f))
    (H.map_inv ((RightLocalization.Q W).map φ.s))).trans ?_
  exact (lift_map_homMk (RightLocalization.Q W ⋙ H) _ φ).symm

variable (W)

/-- **Stacks 04VK (3)**: every functor `G : C ⥤ D` inverting the right multiplicative system
`W` factors as `G = Q ⋙ H` for a unique functor `H : RightLocalization W ⥤ D` out of the
category of right fractions. -/
@[stacks 04VK "(3)"]
theorem existsUnique_lift (G : C ⥤ D) (hG : W.IsInvertedBy G) :
    ∃! H : RightLocalization W ⥤ D, RightLocalization.Q W ⋙ H = G :=
  ⟨lift G hG, fac G hG, fun H hH => by
    subst hH
    exact eq_lift H⟩

end CategoryTheory.MorphismProperty.RightLocalization
