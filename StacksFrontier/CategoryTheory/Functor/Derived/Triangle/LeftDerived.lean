module

public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Opposite.Basic
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import StacksFrontier.CategoryTheory.EssentiallyConstant.Cofinal
import StacksFrontier.CategoryTheory.EssentiallyConstant.IndObject
public import StacksFrontier.CategoryTheory.Functor.Derived.DefinedAt
import StacksFrontier.CategoryTheory.Functor.Derived.Morphisms
public import StacksFrontier.CategoryTheory.Localization.Saturated.Defs
import StacksFrontier.CategoryTheory.Triangulated.Localization
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.CategoryTheory.Functor.Derived.Triangle.RightDerived

/-!
# The left derived functor along a distinguished triangle, and computing objects

Saturation and compatibility with the triangulation pass to `W.op`; the left derived functor
by duality with the right derived functor of `Fᵒᵖ`; the statement of
[Stacks, Tag 05SC] for both `RF` and `LF`, and [Stacks, Tag 05SZ]: computing a derived functor
propagates along a distinguished triangle.
-/

section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

open scoped CategoryTheory.Pretriangulated.Opposite

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace DerivedFunctorValues

section Opposite

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {H : Type u₂} [Category.{v₂} H] [HasZeroObject H] [HasShift H ℤ] [Preadditive H]
  [∀ n : ℤ, (shiftFunctor H n).Additive] [Pretriangulated H]

variable {W : MorphismProperty C}

omit [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- Saturation (Stacks 05Q8) passes to the opposite class: the two calculi of fractions are
exchanged and MS4 is self-dual. -/
private lemma isSaturated_op (hW : W.IsSaturated) : W.op.IsSaturated where
  hasLeftCalculusOfFractions := by have := hW.hasRightCalculusOfFractions; infer_instance
  hasRightCalculusOfFractions := by have := hW.hasLeftCalculusOfFractions; infer_instance
  mem_of_comp_mem_comp f g h h₁ h₂ := hW.mem_of_comp_mem_comp h.unop g.unop f.unop h₂ h₁

omit [HasZeroObject C] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- Compatibility with the shift passes to the opposite class: the shift of `Cᵒᵖ` acts on a
morphism as the shift of `C` by the opposite amount, up to the isomorphism
`shiftFunctorOpIso`. -/
private lemma isCompatibleWithShift_op (hW : W.IsSaturated) [W.IsCompatibleWithShift ℤ] :
    W.op.IsCompatibleWithShift ℤ where
  condition a := by
    apply MorphismProperty.ext
    intro X Y f
    show W.op ((shiftFunctor Cᵒᵖ a).map f) ↔ W.op f
    have := respectsIso_of_isSaturated (isSaturated_op hW)
    rw [shiftFunctor_op_map f a (-a) (by lia), W.op.cancel_left_of_respectsIso,
      W.op.cancel_right_of_respectsIso]
    exact MorphismProperty.IsCompatibleWithShift.iff W f.unop (-a)

/-- Compatibility with the triangulation, read on the first vertex instead of the third: given a
morphism of distinguished triangles on the second and third vertices whose two components lie in
`W`, the first component may be chosen in `W` as well.

This is `MorphismProperty.compatible_with_triangulation` applied to the rotated triangles; the
component it produces is a shift `a⟦1⟧'`, and `a` is recovered because `shiftFunctor C 1` is an
equivalence, hence full and faithful. -/
private lemma exists_mem_of_rotate [W.IsCompatibleWithTriangulation]
    (S₁ S₂ : Triangle C) (h₁ : S₁ ∈ distTriang C) (h₂ : S₂ ∈ distTriang C)
    (b : S₁.obj₂ ⟶ S₂.obj₂) (c : S₁.obj₃ ⟶ S₂.obj₃) (hb : W b) (hc : W c)
    (comm : S₁.mor₂ ≫ c = b ≫ S₂.mor₂) :
    ∃ (a : S₁.obj₁ ⟶ S₂.obj₁) (_ : W a), S₁.mor₁ ≫ b = a ≫ S₂.mor₁ ∧
      S₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ S₂.mor₃ := by
  have key : ∀ a₀ : S₁.obj₁⟦(1 : ℤ)⟧ ⟶ S₂.obj₁⟦(1 : ℤ)⟧, W a₀ →
      S₁.mor₃ ≫ a₀ = c ≫ S₂.mor₃ →
      (-(S₁.mor₁⟦(1 : ℤ)⟧')) ≫ b⟦(1 : ℤ)⟧' = a₀ ≫ (-(S₂.mor₁⟦(1 : ℤ)⟧')) →
      ∃ (a : S₁.obj₁ ⟶ S₂.obj₁) (_ : W a), S₁.mor₁ ≫ b = a ≫ S₂.mor₁ ∧
        S₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ S₂.mor₃ := by
    intro a₀ ha₀ e₂ e₃
    rw [Preadditive.neg_comp, Preadditive.comp_neg, neg_inj] at e₃
    have hmap := (shiftFunctor C (1 : ℤ)).map_preimage a₀
    refine ⟨(shiftFunctor C (1 : ℤ)).preimage a₀, ?_, ?_, ?_⟩
    · exact (MorphismProperty.IsCompatibleWithShift.iff W _ (1 : ℤ)).mp (by rwa [hmap])
    · exact (shiftFunctor C (1 : ℤ)).map_injective
        (by rwa [Functor.map_comp, Functor.map_comp, hmap])
    · rwa [hmap]
  obtain ⟨a₀, ha₀, e₂, e₃⟩ := MorphismProperty.compatible_with_triangulation
    S₁.rotate S₂.rotate (rot_of_distTriang _ h₁) (rot_of_distTriang _ h₂) b c hb hc comm
  exact key a₀ ha₀ e₂ e₃

/-- Compatibility with the triangulation passes to the opposite class. A morphism of
distinguished triangles of `Cᵒᵖ` known on the first two vertices becomes, under
`CategoryTheory.Pretriangulated.triangleOpEquivalence`, a morphism of distinguished triangles of
`C` known on the last two, so `exists_mem_of_rotate` supplies the missing component
in `W`; opposing it back is the required component, the third identity being read off through
`CategoryTheory.Pretriangulated.opShiftFunctorEquivalence` exactly as in
`CategoryTheory.Pretriangulated.Opposite.complete_distinguished_triangle_morphism`. -/
private lemma isCompatibleWithTriangulation_op (hW : W.IsSaturated)
    [W.IsCompatibleWithTriangulation] : W.op.IsCompatibleWithTriangulation where
  __ := isCompatibleWithShift_op hW
  compatible_with_triangulation T₁ T₂ hT₁ hT₂ a b ha hb comm := by
    rw [mem_distTriang_op_iff] at hT₁ hT₂
    obtain ⟨c, hc, hc₁, hc₂⟩ := exists_mem_of_rotate (W := W)
      (Triangle.mk T₂.mor₂.unop T₂.mor₁.unop
        (((opShiftFunctorEquivalence C 1).unitIso.inv.app T₂.obj₁).unop ≫
          T₂.mor₃.unop⟦(1 : ℤ)⟧'))
      (Triangle.mk T₁.mor₂.unop T₁.mor₁.unop
        (((opShiftFunctorEquivalence C 1).unitIso.inv.app T₁.obj₁).unop ≫
          T₁.mor₃.unop⟦(1 : ℤ)⟧'))
      hT₂ hT₁ b.unop a.unop hb ha (Quiver.Hom.op_inj comm.symm)
    dsimp only [Triangle.mk_mor₁, Triangle.mk_mor₂, Triangle.mk_mor₃] at hc₁ hc₂
    replace hc₂ := ((opShiftFunctorEquivalence C 1).unitIso.hom.app T₂.obj₁).unop ≫= hc₂
    dsimp at hc₂
    simp only [Category.assoc, Iso.unop_hom_inv_id_app_assoc] at hc₂
    refine ⟨c.op, hc, Quiver.Hom.unop_inj hc₁.symm, Quiver.Hom.unop_inj ?_⟩
    apply (shiftFunctor C (1 : ℤ)).map_injective
    rw [unop_comp, unop_comp, Functor.map_comp, Functor.map_comp,
      Quiver.Hom.unop_op, hc₂, ← unop_comp_assoc, ← unop_comp_assoc,
      ← opShiftFunctorEquivalence_unitIso_inv_naturality]
    simp

end Opposite

section Duality

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {H : Type u₂} [Category.{v₂} H] [HasZeroObject H] [HasShift H ℤ] [Preadditive H]
  [∀ n : ℤ, (shiftFunctor H n).Additive] [Pretriangulated H]

variable {W : MorphismProperty C} {X : C}

/-- The index of the pro-object `W/X` opposite to an index of the ind-object `(op X)/W.op`. -/
private abbrev overOfUnderOp (s : W.op.Under ⊤ (Opposite.op X)) : W.Over ⊤ X :=
  MorphismProperty.Over.mk ⊤ s.hom.unop s.prop

/-- The index of the ind-object `(op X)/W.op` opposite to an index of the pro-object `W/X`. -/
private abbrev underOpOfOver (t : W.Over ⊤ X) : W.op.Under ⊤ (Opposite.op X) :=
  MorphismProperty.Under.mk ⊤ t.hom.op t.prop

/-- The transition morphism of the pro-object `W/X` opposite to a transition morphism of the
ind-object `(op X)/W.op`. -/
private abbrev overOfUnderOpMap {s t : W.op.Under ⊤ (Opposite.op X)} (f : s ⟶ t) :
    overOfUnderOp t ⟶ overOfUnderOp s :=
  MorphismProperty.Over.homMk f.right.unop (Quiver.Hom.op_inj (MorphismProperty.Under.w f))

/-- The transition morphism of the ind-object `(op X)/W.op` opposite to a transition morphism of
the pro-object `W/X`. -/
private abbrev underOpOfOverMap {s t : W.Over ⊤ X} (f : s ⟶ t) :
    underOpOfOver t ⟶ underOpOfOver s :=
  MorphismProperty.Under.homMk f.left.op (Quiver.Hom.unop_inj (MorphismProperty.Over.w f))

variable (F : C ⥤ H)

/-- The cocone on the ind-object of Stacks 05S9 for `F.op`, `W.op` and `Opposite.op X` opposite to
a cone on the pro-object for `F`, `W` and `X`: the same maps read in `Hᵒᵖ`. -/
private def coconeOp (c : Cone (MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F)) :
    Cocone (MorphismProperty.Under.forget W.op ⊤ (Opposite.op X) ⋙
      Under.forget (Opposite.op X) ⋙ F.op) where
  pt := Opposite.op c.pt
  ι :=
    { app s := (c.π.app (overOfUnderOp s)).op
      naturality _ _ f :=
        (congrArg Quiver.Hom.op (c.w (overOfUnderOpMap f))).trans (Category.comp_id _).symm }

/-- The cone on the pro-object of Stacks 05S9 for `F`, `W` and `X` opposite to a cocone on the
ind-object for `F.op`, `W.op` and `Opposite.op X`. It is a section of
`coconeOp`. -/
private def coneUnop (c : Cocone (MorphismProperty.Under.forget W.op ⊤ (Opposite.op X) ⋙
      Under.forget (Opposite.op X) ⋙ F.op)) :
    Cone (MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F) where
  pt := c.pt.unop
  π :=
    { app t := (c.ι.app (underOpOfOver t)).unop
      naturality _ _ f := (Category.id_comp _).trans
        (congrArg Quiver.Hom.unop (c.w (underOpOfOverMap f))).symm }

omit [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [HasZeroObject H] [HasShift H ℤ]
  [Preadditive H] [∀ n : ℤ, (shiftFunctor H n).Additive] [Pretriangulated H] in
/-- Stacks 05S9 read in the opposite category: a cone exhibits its vertex as a value of `LF` at
`X` exactly when the opposite cocone exhibits the opposite vertex as a value of the right derived
functor of `F.op` relative to `W.op` at `Opposite.op X`. Both sides are the essential constancy of
one and the same system, read once on `W.Over ⊤ X` and once on `W.op.Under ⊤ (Opposite.op X)`. -/
private lemma isRightDerivedValueAt_op_coconeOp_iff
    (c : Cone (MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F)) :
    F.op.IsRightDerivedValueAt W.op (Opposite.op X) (coconeOp F c) ↔
      F.IsLeftDerivedValueAt W X c := by
  constructor
  · rintro ⟨s₀, r, hr, hfac⟩
    refine ⟨overOfUnderOp s₀, r.unop, Quiver.Hom.op_inj hr, fun s => ?_⟩
    obtain ⟨t, u, v, huv⟩ := hfac (underOpOfOver s)
    exact ⟨overOfUnderOp t, overOfUnderOpMap u, overOfUnderOpMap v,
      (congrArg Quiver.Hom.unop huv).trans (Category.assoc _ _ _)⟩
  · rintro ⟨s₀, r, hr, hfac⟩
    refine ⟨underOpOfOver s₀, r.op, Quiver.Hom.unop_inj hr, fun s => ?_⟩
    obtain ⟨t, u, v, huv⟩ := hfac (overOfUnderOp s)
    exact ⟨underOpOfOver t, underOpOfOverMap u, underOpOfOverMap v,
      (congrArg Quiver.Hom.op huv).trans
        (Category.assoc ((coconeOp F c).ι.app s) r.op (F.op.map (underOpOfOverMap v).right))⟩


end Duality

section Translate

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {H : Type u₂} [Category.{v₂} H] [HasZeroObject H] [HasShift H ℤ] [Preadditive H]
  [∀ n : ℤ, (shiftFunctor H n).Additive] [Pretriangulated H]

variable (F : C ⥤ H) [F.CommShift ℤ]

omit [HasZeroObject H] [Preadditive H] [∀ n : ℤ, (shiftFunctor H n).Additive]
  [Pretriangulated H] in
/-- `CategoryTheory.shiftFunctorCompIsoId_naturality_1` with the second component of the
counit transposed to the shifted object: for `g : P ⟶ Q⟦1⟧` the composite
`P ⟶ P⟦-1⟧⟦1⟧ ⟶ Q⟦1⟧⟦-1⟧⟦1⟧ ⟶ Q⟦1⟧` is `g` again. -/
private lemma shiftFunctorCompIsoId_naturality_1_shift {P Q : H} (g : P ⟶ Q⟦(1 : ℤ)⟧) :
    (shiftFunctorCompIsoId H (-1) 1 (neg_add_cancel 1)).inv.app P ≫ ((g⟦(-1 : ℤ)⟧')⟦(1 : ℤ)⟧') ≫
        ((shiftFunctorCompIsoId H 1 (-1) (add_neg_cancel 1)).hom.app Q)⟦(1 : ℤ)⟧' = g := by
  rw [shift_shiftFunctorCompIsoId_add_neg_cancel_hom_app]
  exact shiftFunctorCompIsoId_naturality_1 g (-1 : ℤ) 1 (neg_add_cancel 1)

omit [HasZeroObject C] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [HasZeroObject H] [Preadditive H]
  [∀ n : ℤ, (shiftFunctor H n).Additive] [Pretriangulated H] in
/-- The identification, in `H`, of the opposite of the third characterising square of Tag 05SA
for `F.op` with the square characterising `LF(h)`: the shifted projection of the value at `X⟦1⟧`
is the shift of the projection followed by the inverse of the commutation isomorphism of `F`
with the shift, read through `opShiftFunctorEquivalence`. -/
private lemma shift_unop_translate {P : H} {X Y : C} (π : P ⟶ F.obj X) (h' : X ⟶ Y⟦(1 : ℤ)⟧) :
    ((opShiftFunctorEquivalence H 1).unitIso.inv.app (Opposite.op P)).unop ≫
        ((((shiftFunctor Hᵒᵖ (1 : ℤ)).map π.op).unop ≫
          ((F.op.commShiftIso (1 : ℤ)).hom.app (Opposite.op X)).unop ≫
            F.map (((opShiftFunctorEquivalence C 1).counitIso.inv.app (Opposite.op Y) ≫
              h'.op⟦(1 : ℤ)⟧').unop))⟦(1 : ℤ)⟧') =
      π ≫ F.map h' ≫ (F.commShiftIso (1 : ℤ)).hom.app Y := by
  rw [unop_comp, F.map_comp, Functor.map_shift_unop,
    Functor.map_opShiftFunctorEquivalence_counitIso_inv_app_unop]
  simp only [Functor.id_obj, opShiftFunctorEquivalence, Int.reduceNeg, NatIso.op_symm,
    Functor.comp_obj, Functor.op_obj, Iso.trans_inv, Functor.isoWhiskerRight_inv, Iso.symm_inv,
    NatIso.op_inv, NatTrans.comp_app, Functor.whiskerRight_app, Functor.op_map, NatTrans.op_app,
    unop_comp, Quiver.Hom.unop_op, shiftFunctor_op_map (n := (1 : ℤ)) (m := (-1 : ℤ)),
    Category.assoc, NatIso.op_hom, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    Iso.unop_hom_inv_id_app_assoc, Functor.map_comp, cancelIso]
  refine Eq.trans ?_ (shiftFunctorCompIsoId_naturality_1_shift
    (π ≫ F.map h' ≫ (F.commShiftIso (1 : ℤ)).hom.app Y))
  simp only [Functor.map_comp, Category.assoc]

end Translate

section LeftDerived

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {H : Type u₂} [Category.{v₂} H] [HasZeroObject H] [HasShift H ℤ] [Preadditive H]
  [∀ n : ℤ, (shiftFunctor H n).Additive] [Pretriangulated H]

/-- Tag 05SC for the left derived functor: the mirror of `solution_right`, obtained
from it in the opposite categories. -/
private theorem solution_left (F : C ⥤ H) [F.CommShift ℤ] [F.IsTriangulated]
    (W : MorphismProperty C) (hW : W.IsSaturated) [W.IsCompatibleWithTriangulation]
    (T : Triangle C) (hT : T ∈ distTriang C) :
    ((∃ c, F.IsLeftDerivedValueAt W T.obj₁ c) → (∃ c, F.IsLeftDerivedValueAt W T.obj₂ c) →
          ∃ c, F.IsLeftDerivedValueAt W T.obj₃ c) ∧
        ((∃ c, F.IsLeftDerivedValueAt W T.obj₂ c) → (∃ c, F.IsLeftDerivedValueAt W T.obj₃ c) →
          ∃ c, F.IsLeftDerivedValueAt W T.obj₁ c) ∧
        ((∃ c, F.IsLeftDerivedValueAt W T.obj₃ c) → (∃ c, F.IsLeftDerivedValueAt W T.obj₁ c) →
          ∃ c, F.IsLeftDerivedValueAt W T.obj₂ c) ∧
        ∀ (cX : Cone (MorphismProperty.Over.forget W ⊤ T.obj₁ ⋙ Over.forget T.obj₁ ⋙ F))
          (_ : F.IsLeftDerivedValueAt W T.obj₁ cX)
          (cY : Cone (MorphismProperty.Over.forget W ⊤ T.obj₂ ⋙ Over.forget T.obj₂ ⋙ F))
          (_ : F.IsLeftDerivedValueAt W T.obj₂ cY)
          (cZ : Cone (MorphismProperty.Over.forget W ⊤ T.obj₃ ⋙ Over.forget T.obj₃ ⋙ F))
          (_ : F.IsLeftDerivedValueAt W T.obj₃ cZ),
          ∃ (u : cX.pt ⟶ cY.pt) (v : cY.pt ⟶ cZ.pt) (w : cZ.pt ⟶ cX.pt⟦(1 : ℤ)⟧),
            Triangle.mk u v w ∈ distTriang H ∧
            (∀ (s : W.Over ⊤ T.obj₁) (t : W.Over ⊤ T.obj₂) (f' : s.left ⟶ t.left),
              s.hom ≫ T.mor₁ = f' ≫ t.hom → u ≫ cY.π.app t = cX.π.app s ≫ F.map f') ∧
            (∀ (t : W.Over ⊤ T.obj₂) (r : W.Over ⊤ T.obj₃) (g' : t.left ⟶ r.left),
              t.hom ≫ T.mor₂ = g' ≫ r.hom → v ≫ cZ.π.app r = cY.π.app t ≫ F.map g') ∧
            ∀ (r : W.Over ⊤ T.obj₃) (s : W.Over ⊤ T.obj₁) (h' : r.left ⟶ s.left⟦(1 : ℤ)⟧),
              r.hom ≫ T.mor₃ = h' ≫ s.hom⟦(1 : ℤ)⟧' →
                w ≫ (cX.π.app s)⟦(1 : ℤ)⟧' =
                  cZ.π.app r ≫ F.map h' ≫ (F.commShiftIso (1 : ℤ)).hom.app s.left := by
  have hWop := isSaturated_op hW
  have := isCompatibleWithTriangulation_op hW
  have hTop : (triangleOpEquivalence C).functor.obj (Opposite.op T) ∈ distTriang Cᵒᵖ :=
    op_distinguished T hT
  have hR := solution_right F.op W.op hWop _ hTop
  have hiff : ∀ X : C, (∃ c, F.IsLeftDerivedValueAt W X c) ↔
      ∃ c, F.op.IsRightDerivedValueAt W.op (Opposite.op X) c := fun X =>
    ⟨fun ⟨c, hc⟩ => ⟨coconeOp F c, (isRightDerivedValueAt_op_coconeOp_iff F c).2 hc⟩,
      fun ⟨c, hc⟩ => ⟨coneUnop F c, (isRightDerivedValueAt_op_coconeOp_iff F (coneUnop F c)).1 hc⟩⟩
  refine ⟨fun h₁ h₂ => (hiff _).2 (hR.2.1 ((hiff _).1 h₂) ((hiff _).1 h₁)),
    fun h₂ h₃ => (hiff _).2 (hR.1 ((hiff _).1 h₃) ((hiff _).1 h₂)),
    fun h₃ h₁ => (hiff _).2 (hR.2.2.1 ((hiff _).1 h₁) ((hiff _).1 h₃)), ?_⟩
  intro cX hcX cY hcY cZ hcZ
  obtain ⟨u', v', w', hdist, h1, h2, h3⟩ := hR.2.2.2
    (coconeOp F cZ) ((isRightDerivedValueAt_op_coconeOp_iff F cZ).2 hcZ)
    (coconeOp F cY) ((isRightDerivedValueAt_op_coconeOp_iff F cY).2 hcY)
    (coconeOp F cX) ((isRightDerivedValueAt_op_coconeOp_iff F cX).2 hcX)
  rw [mem_distTriang_op_iff] at hdist
  refine ⟨v'.unop, u'.unop,
    ((opShiftFunctorEquivalence H 1).unitIso.inv.app (Opposite.op cZ.pt)).unop ≫
      w'.unop⟦(1 : ℤ)⟧', ?_, ?_, ?_, ?_⟩
  · exact hdist
  · intro s t f' hsq
    exact congrArg Quiver.Hom.unop
      (h2 (underOpOfOver t) (underOpOfOver s) f'.op (Quiver.Hom.unop_inj hsq))
  · intro t r g' hsq
    exact congrArg Quiver.Hom.unop
      (h1 (underOpOfOver r) (underOpOfOver t) g'.op (Quiver.Hom.unop_inj hsq))
  · intro r s h' hsq
    have hsq' : ((opShiftFunctorEquivalence C 1).counitIso.inv.app (Opposite.op T.obj₁) ≫
          T.mor₃.op⟦(1 : ℤ)⟧') ≫ (r.hom.op)⟦(1 : ℤ)⟧' =
        s.hom.op ≫ ((opShiftFunctorEquivalence C 1).counitIso.inv.app (Opposite.op s.left) ≫
          h'.op⟦(1 : ℤ)⟧') := by
      have hnat : s.hom.op ≫
            (opShiftFunctorEquivalence C 1).counitIso.inv.app (Opposite.op s.left) =
          (opShiftFunctorEquivalence C 1).counitIso.inv.app (Opposite.op T.obj₁) ≫
            ((s.hom⟦(1 : ℤ)⟧').op)⟦(1 : ℤ)⟧' :=
        opShiftFunctorEquivalence_counitIso_inv_naturality (C := C) (1 : ℤ) s.hom.op
      calc ((opShiftFunctorEquivalence C 1).counitIso.inv.app (Opposite.op T.obj₁) ≫
              T.mor₃.op⟦(1 : ℤ)⟧') ≫ (r.hom.op)⟦(1 : ℤ)⟧'
          = (opShiftFunctorEquivalence C 1).counitIso.inv.app (Opposite.op T.obj₁) ≫
              ((r.hom ≫ T.mor₃).op)⟦(1 : ℤ)⟧' := by
            rw [Category.assoc, ← Functor.map_comp, op_comp]
        _ = (opShiftFunctorEquivalence C 1).counitIso.inv.app (Opposite.op T.obj₁) ≫
              ((h' ≫ s.hom⟦(1 : ℤ)⟧').op)⟦(1 : ℤ)⟧' := by rw [hsq]
        _ = s.hom.op ≫ ((opShiftFunctorEquivalence C 1).counitIso.inv.app (Opposite.op s.left) ≫
              h'.op⟦(1 : ℤ)⟧') := by
            rw [← Category.assoc, hnat, Category.assoc, ← Functor.map_comp, op_comp]
    have key := congrArg Quiver.Hom.unop (h3 (underOpOfOver s) (underOpOfOver r) _ hsq')
    simp only [coconeOp] at key
    clear hR hiff h1 h2 h3 hdist hsq' hsq hcX hcY hcZ
    -- `w'` was obtained against the triangle `(triangleOpEquivalence C).functor.obj (op T)`, whose
    -- vertices are only definitionally the opposites of those of `T`, so its type is not
    -- type-correct at the transparency `rw` builds motives at; the rest is done in term mode.
    have key' : w'.unop ≫ cX.π.app s =
        ((shiftFunctor Hᵒᵖ (1 : ℤ)).map (cZ.π.app r).op).unop ≫
          ((F.op.commShiftIso (1 : ℤ)).hom.app (Opposite.op r.left)).unop ≫
            F.map (((opShiftFunctorEquivalence C 1).counitIso.inv.app (Opposite.op s.left) ≫
              h'.op⟦(1 : ℤ)⟧').unop) := key.trans (Category.assoc _ _ _)
    refine Eq.trans ?_ (shift_unop_translate F (cZ.π.app r) h')
    refine (Category.assoc _ _ _).trans ?_
    refine congrArg (fun z => ((opShiftFunctorEquivalence H 1).unitIso.inv.app
      (Opposite.op cZ.pt)).unop ≫ z) ?_
    exact (Functor.map_comp (shiftFunctor H (1 : ℤ)) w'.unop (cX.π.app s)).symm.trans
      (congrArg (fun z => (shiftFunctor H (1 : ℤ)).map z) key')


end LeftDerived
end DerivedFunctorValues

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {H : Type u₂} [Category.{v₂} H] [HasZeroObject H] [HasShift H ℤ] [Preadditive H]
  [∀ n : ℤ, (shiftFunctor H n).Additive] [Pretriangulated H]

/-- **Stacks 05SC**. Let `F : C ⥤ H` be an exact functor of pretriangulated categories and let
`W` be a saturated multiplicative system in `C` (Stacks 05Q8) compatible with the triangulation.
Let `T = (X, Y, Z, f, g, h)` be a distinguished triangle of `C`.

If the right derived functor `RF` of `F` with respect to `W` is defined at two of `X`, `Y`, `Z`
— that is, if for two of them the ind-object `(s : X ⟶ X') ↦ F(X')` over `X/W` is essentially
constant — then it is defined at the third; moreover, for any values `RF(X)`, `RF(Y)`, `RF(Z)` at
the three objects there are morphisms `RF(f)`, `RF(g)`, `RF(h)` between them, each characterised
by compatibility with the coprojections as in Stacks 05SA, such that
`(RF(X), RF(Y), RF(Z), RF(f), RF(g), RF(h))` is a distinguished triangle of `H`. That is the first
conjunct.

Similarly for the left derived functor `LF`, the second conjunct: if `LF` is defined at two of
`X`, `Y`, `Z` — if for two of them the pro-object `(s : X' ⟶ X) ↦ F(X')` over `W/X` is essentially
constant — then it is defined at the third, and for any values `LF(X)`, `LF(Y)`, `LF(Z)` there are
morphisms `LF(f)`, `LF(g)`, `LF(h)`, each characterised by compatibility with the projections as
in the dual of Stacks 05SA, such that `(LF(X), LF(Y), LF(Z), LF(f), LF(g), LF(h))` is a
distinguished triangle of `H`. -/
@[stacks 05SC, sga "4 XVII 1.2.2" "(ii)"]
public theorem exists_isRightDerivedValueAt_and_isLeftDerivedValueAt_and_triangle_distinguished
    (F : C ⥤ H) [F.CommShift ℤ] [F.IsTriangulated] (W : MorphismProperty C)
    (hW : W.IsSaturated) [W.IsCompatibleWithTriangulation]
    (T : Triangle C) (hT : T ∈ distTriang C) :
    (((∃ c, F.IsRightDerivedValueAt W T.obj₁ c) → (∃ c, F.IsRightDerivedValueAt W T.obj₂ c) →
          ∃ c, F.IsRightDerivedValueAt W T.obj₃ c) ∧
        ((∃ c, F.IsRightDerivedValueAt W T.obj₂ c) → (∃ c, F.IsRightDerivedValueAt W T.obj₃ c) →
          ∃ c, F.IsRightDerivedValueAt W T.obj₁ c) ∧
        ((∃ c, F.IsRightDerivedValueAt W T.obj₃ c) → (∃ c, F.IsRightDerivedValueAt W T.obj₁ c) →
          ∃ c, F.IsRightDerivedValueAt W T.obj₂ c) ∧
        ∀ (cX : Cocone (MorphismProperty.Under.forget W ⊤ T.obj₁ ⋙ Under.forget T.obj₁ ⋙ F))
          (_ : F.IsRightDerivedValueAt W T.obj₁ cX)
          (cY : Cocone (MorphismProperty.Under.forget W ⊤ T.obj₂ ⋙ Under.forget T.obj₂ ⋙ F))
          (_ : F.IsRightDerivedValueAt W T.obj₂ cY)
          (cZ : Cocone (MorphismProperty.Under.forget W ⊤ T.obj₃ ⋙ Under.forget T.obj₃ ⋙ F))
          (_ : F.IsRightDerivedValueAt W T.obj₃ cZ),
          ∃ (u : cX.pt ⟶ cY.pt) (v : cY.pt ⟶ cZ.pt) (w : cZ.pt ⟶ cX.pt⟦(1 : ℤ)⟧),
            Triangle.mk u v w ∈ distTriang H ∧
            (∀ (s : W.Under ⊤ T.obj₁) (t : W.Under ⊤ T.obj₂) (f' : s.right ⟶ t.right),
              T.mor₁ ≫ t.hom = s.hom ≫ f' → cX.ι.app s ≫ u = F.map f' ≫ cY.ι.app t) ∧
            (∀ (t : W.Under ⊤ T.obj₂) (r : W.Under ⊤ T.obj₃) (g' : t.right ⟶ r.right),
              T.mor₂ ≫ r.hom = t.hom ≫ g' → cY.ι.app t ≫ v = F.map g' ≫ cZ.ι.app r) ∧
            ∀ (r : W.Under ⊤ T.obj₃) (s : W.Under ⊤ T.obj₁) (h' : r.right ⟶ s.right⟦(1 : ℤ)⟧),
              T.mor₃ ≫ s.hom⟦(1 : ℤ)⟧' = r.hom ≫ h' →
                cZ.ι.app r ≫ w =
                  F.map h' ≫ (F.commShiftIso (1 : ℤ)).hom.app s.right ≫
                    (cX.ι.app s)⟦(1 : ℤ)⟧') ∧
      (((∃ c, F.IsLeftDerivedValueAt W T.obj₁ c) → (∃ c, F.IsLeftDerivedValueAt W T.obj₂ c) →
            ∃ c, F.IsLeftDerivedValueAt W T.obj₃ c) ∧
          ((∃ c, F.IsLeftDerivedValueAt W T.obj₂ c) → (∃ c, F.IsLeftDerivedValueAt W T.obj₃ c) →
            ∃ c, F.IsLeftDerivedValueAt W T.obj₁ c) ∧
          ((∃ c, F.IsLeftDerivedValueAt W T.obj₃ c) → (∃ c, F.IsLeftDerivedValueAt W T.obj₁ c) →
            ∃ c, F.IsLeftDerivedValueAt W T.obj₂ c) ∧
          ∀ (cX : Cone (MorphismProperty.Over.forget W ⊤ T.obj₁ ⋙ Over.forget T.obj₁ ⋙ F))
            (_ : F.IsLeftDerivedValueAt W T.obj₁ cX)
            (cY : Cone (MorphismProperty.Over.forget W ⊤ T.obj₂ ⋙ Over.forget T.obj₂ ⋙ F))
            (_ : F.IsLeftDerivedValueAt W T.obj₂ cY)
            (cZ : Cone (MorphismProperty.Over.forget W ⊤ T.obj₃ ⋙ Over.forget T.obj₃ ⋙ F))
            (_ : F.IsLeftDerivedValueAt W T.obj₃ cZ),
            ∃ (u : cX.pt ⟶ cY.pt) (v : cY.pt ⟶ cZ.pt) (w : cZ.pt ⟶ cX.pt⟦(1 : ℤ)⟧),
              Triangle.mk u v w ∈ distTriang H ∧
              (∀ (s : W.Over ⊤ T.obj₁) (t : W.Over ⊤ T.obj₂) (f' : s.left ⟶ t.left),
                s.hom ≫ T.mor₁ = f' ≫ t.hom → u ≫ cY.π.app t = cX.π.app s ≫ F.map f') ∧
              (∀ (t : W.Over ⊤ T.obj₂) (r : W.Over ⊤ T.obj₃) (g' : t.left ⟶ r.left),
                t.hom ≫ T.mor₂ = g' ≫ r.hom → v ≫ cZ.π.app r = cY.π.app t ≫ F.map g') ∧
              ∀ (r : W.Over ⊤ T.obj₃) (s : W.Over ⊤ T.obj₁) (h' : r.left ⟶ s.left⟦(1 : ℤ)⟧),
                r.hom ≫ T.mor₃ = h' ≫ s.hom⟦(1 : ℤ)⟧' →
                  w ≫ (cX.π.app s)⟦(1 : ℤ)⟧' =
                    cZ.π.app r ≫ F.map h' ≫ (F.commShiftIso (1 : ℤ)).hom.app s.left) :=
  ⟨DerivedFunctorValues.solution_right F W hW T hT,
    DerivedFunctorValues.solution_left F W hW T hT⟩

end CategoryTheory.Functor

end

end

section

/-!
# Computing a derived functor propagates along a distinguished triangle

Let `F : 𝒟 ⥤ 𝒟'` be an exact functor of pretriangulated categories and let `W` be a saturated
multiplicative system in `𝒟` compatible with the triangulation. The right derived functor `RF` is
*defined at* an object `X` when the ind-object
$$ X/W ⟶ 𝒟', \qquad (s : X ⟶ X') ⟼ F(X'), $$
is essentially constant, its value being `RF(X)` (Tag 05S9); the identity `𝟙 X` is one of the
indices, so a value carries a canonical map `F(X) ⟶ RF(X)`, and `X` *computes* `RF` when `RF` is
defined at `X` and that canonical map is an isomorphism (Tag 05SX). Dually `LF` is defined at `X`
when the pro-object on `W/X` is essentially constant with value `LF(X)`, and `X` computes `LF`
when the canonical map `LF(X) ⟶ F(X)` is an isomorphism.

Computing a derived functor propagates along a distinguished triangle: if two of the three objects
of a distinguished triangle `(X, Y, Z, f, g, h)` of `𝒟` compute `RF`, then so does the third, and
likewise for `LF`. Indeed `RF` is then defined at the third object and
`(RF(X), RF(Y), RF(Z), RF(f), RF(g), RF(h))` is a distinguished triangle of `𝒟'` (Tag 05SC); the
canonical maps assemble into a morphism from the distinguished triangle `F(T)` to that one, two of
whose three components are isomorphisms, hence so is the third.

## Main results

* `CategoryTheory.Functor.computesRightDerived_and_computesLeftDerived_of_distTriang` (Tag 05SZ):
  along a distinguished triangle, two of the three objects computing `RF` forces the third to
  compute `RF`, in each of the three positions; and the same for `LF`.

## Implementation notes

*All three positions, not only the third.* The source states the assertion in one position — `X`
and `Y` compute `RF`, hence `Z` does — but its own applications use the others: the proof of
Leray's acyclicity lemma (Tag 015E) applies it to the stupid-truncation triangle
`(σ_{≥ a + 1}A, A, σ_{≤ a}A)`, where the two *outer* complexes compute `RF` and the conclusion is
wanted for the *middle* one. All three positions are therefore asserted, as Tag 05SC already does
for definedness and as Mathlib does for the analogous propagation of vanishing and of
invertibility (`CategoryTheory.Pretriangulated.Triangle.isZero₃_of_isZero₁₂` and its two siblings,
`CategoryTheory.Pretriangulated.isIso₂_of_isIso₁₃` and its two siblings). The extra positions cost
the proof nothing: definedness in every position is Tag 05SC, and the triangle-morphism argument
is the same one, closed by the sibling of `isIso₃_of_isIso₁₂` for the position in question. They
are conjuncts of one theorem rather than three lemmas because they share their hypotheses, as in
the statements for Tags 05SC, 05SD and 05T0.

*Faithfulness.* (1) No hypothesis is dead: `hT` is what makes the conclusion hold at all (for a
triangle that is not distinguished, two vertices computing `RF` says nothing about the third), and
exactness of `F`, saturation of `W` and its compatibility with the triangulation are what Tag
05SC — the sole input beyond the two-out-of-three property of isomorphisms — runs on. (2) The data
are the source's: one class `W` of morphisms of the source category of `F`, the index categories
`X/W` of morphisms of `W` out of the object in question with arbitrary morphisms of `𝒟` under it,
the diagram valued in `𝒟'` through `F`, and the shift on either side the `ℤ`-shift of the
respective pretriangulated structure; no localization of `𝒟` and no change of `W`. (3) The
canonical maps are pinned, not merely asserted to exist: "computes" is Tag 05SX as stated in this
project, invertibility of the coprojection, resp. projection, of the value cocone, resp. cone, at
the index `𝟙 X`, so both hypotheses and conclusions are about the source's maps
`F(X) ⟶ RF(X)`, resp. `LF(X) ⟶ F(X)`. (4) The instantiation is not degenerate: for `W` the class
of isomorphisms of `𝒟` — a saturated multiplicative system compatible with the triangulation —
every object computes both `RF` and `LF`, so the hypotheses are satisfiable; non-trivially, for `W`
the quasi-isomorphisms in a homotopy category the K-injective complexes compute `RF` (Tag 070Y),
and the content is that this class of objects is closed under the two-out-of-three property along
distinguished triangles. Each hypothesis is a genuine condition, implying that the derived functor
is defined at the object in question.

*Pretriangulated, not triangulated.* Situation 05S8 asks for triangulated categories, but neither
Tag 05SC (whose index-category input, Tag 05R9, is a statement about pretriangulated categories)
nor the two-out-of-three property of isomorphisms in a morphism of distinguished triangles uses the
octahedron axiom, so it is not assumed. Saturation of `W` (Tag 05Q8, `MorphismProperty.IsSaturated`
in this repository) is not droppable: it is what makes the category of `W`-morphisms of triangles
full over `X/W` in Tag 05R9, and by Tag 05RG non-saturated multiplicative systems compatible with
the triangulation exist. Since `IsSaturated` bundles both calculi of fractions and MS1, neither
`W.HasLeftCalculusOfFractions` nor `W.IsMultiplicative` is imposed separately.

*Why the identities instance.* `ComputesRightDerived` and `ComputesLeftDerived` name the index
`𝟙 X`, which `[W.ContainsIdentities]` provides. It is implied by `hW` (part of MS1) and appears as
an instance argument only so that the two predicates elaborate, exactly as in the statements for Tags
05SX and 05T0; it is not an assumption beyond `hW`.

*Duality.* The assertion for `LF` is given directly, in terms of the pro-object form in which
Tag 05S9 gives `IsLeftDerivedValueAt`, rather than as the assertion for `F.op`, `W.op` and the
opposite triangle; the two agree through the equivalence
`(W.Over ⊤ X)ᵒᵖ ≌ W.op.Under ⊤ (Opposite.op X)` and the pretriangulated structure on the opposite
category, which is a separate lemma. Because all three positions are asserted, the `LF` conjuncts
are stated on the same triangle `T`, no rotation or reversal being needed to match the dual.

*Shifts.* The source's Tag 05SY (`X` computes `RF` if and only if `X⟦n⟧` does) is not used and not
restated: with all three positions available, no rotation of the triangle is needed.

## Proof outline

# Computing a derived functor propagates along a distinguished triangle

Let `F : 𝒟 ⥤ 𝒟'` be an exact functor of pretriangulated categories and let `W` be a saturated
multiplicative system in `𝒟` compatible with the triangulation. The right derived functor `RF` is
*defined at* an object `X` when the ind-object `X/W ⟶ 𝒟'`, `(s : X ⟶ X') ↦ F(X')`, is essentially
constant, its value being `RF(X)` (Tag 05S9); the identity `𝟙 X` is one of the indices, so a value
carries a canonical map `F(X) ⟶ RF(X)`, the coprojection at that index, and `X` *computes* `RF`
when that map is an isomorphism (Tag 05SX). Dually `LF` is defined at `X` when the pro-object
`W/X ⟶ 𝒟'`, `(s : X' ⟶ X) ↦ F(X')`, is essentially constant with value `LF(X)`, and `X` computes
`LF` when the projection `LF(X) ⟶ F(X)` at the index `𝟙 X` is an isomorphism.

Along a distinguished triangle `T = (X, Y, Z, f, g, h)` of `𝒟`, two of the three objects computing
`RF` forces the third to compute `RF`: by Tag 05SC the functor `RF` is then defined at the third
object, and for any values `RF(X)`, `RF(Y)`, `RF(Z)` the induced morphisms `RF(f)`, `RF(g)`,
`RF(h)` make `(RF(X), RF(Y), RF(Z), RF(f), RF(g), RF(h))` a distinguished triangle of `𝒟'`. Those
morphisms are pinned by their compatibility with the coprojections, and at the indices `𝟙 X`,
`𝟙 Y`, `𝟙 Z` that compatibility says precisely that the three canonical maps are the components of
a morphism of triangles
`(F(X), F(Y), F(Z), F(f), F(g), F(h)) ⟶ (RF(X), RF(Y), RF(Z), RF(f), RF(g), RF(h))`.
Both triangles being distinguished, two of the three components being isomorphisms forces the
third (Tag 014A). The argument for `LF` is the mirror of this one: the second half of Tag 05SC
supplies the distinguished triangle of values `(LF(X), LF(Y), LF(Z), LF(f), LF(g), LF(h))` together
with the compatibility of its morphisms with the projections, which at the identity indices
assembles the canonical maps into a morphism of triangles in the other direction, towards `F(T)`.

## Implementation notes

*The two halves are mirror images, neither deduced from the other.* Tag 05SC states both the
ind-side and the pro-side, so each half of this lemma runs on the corresponding half of Tag 05SC,
and no transport along `op` — of exactness of `F`, of saturation of `W` (Tag 05Q8), of compatibility
with the triangulation, nor the identification of `IsLeftDerivedValueAt` with
`F.op.IsRightDerivedValueAt W.op` across `(W.Over ⊤ X)ᵒᵖ ≌ W.op.Under ⊤ (Opposite.op X)` — is
needed. Beyond Tag 05SC, all six conjuncts are the two-out-of-three property of isomorphisms in a
morphism of distinguished triangles (`CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂` and its two
siblings), applied to the morphism of triangles assembled from the canonical maps; the pro-side
differs only in that that morphism points from the triangle of values towards `F(T)`, the direction
in which the canonical map `LF(-) ⟶ F(-)` goes. That property is used through a single statement,
taking the morphism of triangles as three commuting squares between two distinguished triangles and
returning the three implications at once, and the two halves are its two instances — the ind-side
with `F(T)` as source, the pro-side with `F(T)` as target.

*The canonical maps as components of a morphism of triangles.* The compatibility clauses of
Tag 05SC characterise `RF(f)`, `RF(g)`, `RF(h)`, resp. `LF(f)`, `LF(g)`, `LF(h)`, against arbitrary
indices; instantiating them at `s = t = r = 𝟙` — the side conditions becoming
`T.mor₁ ≫ 𝟙 = 𝟙 ≫ T.mor₁` and its analogues — gives exactly the three commuting squares of a
morphism `F.mapTriangle.obj T ⟶ Triangle.mk (RF f) (RF g) (RF h)`, resp.
`Triangle.mk (LF f) (LF g) (LF h) ⟶ F.mapTriangle.obj T`. No cofinality argument and no uniqueness
statement about values is needed for this step.

## References

* [Stacks Project, Tag 05SZ](https://stacks.math.columbia.edu/tag/05SZ), Lemma 13.14.10; the
  situation is Tag 05S8, definedness and values are Tag 05S9, "computes" is Tag 05SX, the
  distinguished triangle of values is Tag 05SC, saturated multiplicative systems are Tag 05Q8,
  and the application to Leray's acyclicity lemma is Tag 015E.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated MorphismProperty

namespace DerivedFunctorDistTriang

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {H : Type u₂} [Category.{v₂} H] [HasZeroObject H] [HasShift H ℤ] [Preadditive H]
  [∀ n : ℤ, (shiftFunctor H n).Additive] [Pretriangulated H]

/-- The index `𝟙 X` of the index category `X/W` of the ind-object whose value is `RF(X)`. -/
private abbrev idUnder (W : MorphismProperty C) [W.ContainsIdentities] (X : C) : W.Under ⊤ X :=
  MorphismProperty.Under.mk ⊤ (𝟙 X) (MorphismProperty.id_mem W X)

/-- The index `𝟙 X` of the index category `W/X` of the pro-object whose value is `LF(X)`. -/
private abbrev idOver (W : MorphismProperty C) [W.ContainsIdentities] (X : C) : W.Over ⊤ X :=
  MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem W X)

omit [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- The identity indices satisfy the side condition of every compatibility clause of Stacks 05SC
on the ind-side: for `f : Z ⟶ G X`, both `f ≫ G 𝟙` and `𝟙 ≫ f` are `f`. The clauses for `T.mor₁`
and `T.mor₂` are the case `G = 𝟭`, the clause for `T.mor₃` the case `G = ⟦1⟧`. -/
private lemma comp_idUnder_hom (W : MorphismProperty C) [W.ContainsIdentities] (G : C ⥤ C)
    {X Z : C} (f : Z ⟶ G.obj X) : f ≫ G.map (idUnder W X).hom = (idUnder W Z).hom ≫ f := by
  simp [idUnder, MorphismProperty.Under.mk]

omit [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- The identity indices satisfy the side condition of every compatibility clause of Stacks 05SC
on the pro-side, the mirror of `comp_idUnder_hom`. -/
private lemma idOver_hom_comp (W : MorphismProperty C) [W.ContainsIdentities] (G : C ⥤ C)
    {X Z : C} (f : Z ⟶ G.obj X) : (idOver W Z).hom ≫ f = f ≫ G.map (idOver W X).hom := by
  simp [idOver, MorphismProperty.Over.mk]

/-- **Two out of three isomorphisms in a morphism of distinguished triangles** (Stacks 014A), in
the form both halves below use it: three commuting squares between distinguished triangles are a
morphism of triangles, so any two of their vertical maps being isomorphisms forces the third. -/
private lemma isIso_two_out_of_three (A B : Triangle H) (hA : A ∈ distTriang H)
    (hB : B ∈ distTriang H) {a : A.obj₁ ⟶ B.obj₁} {b : A.obj₂ ⟶ B.obj₂} {c : A.obj₃ ⟶ B.obj₃}
    (h₁ : A.mor₁ ≫ b = a ≫ B.mor₁) (h₂ : A.mor₂ ≫ c = b ≫ B.mor₂)
    (h₃ : A.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ B.mor₃) :
    (IsIso a → IsIso b → IsIso c) ∧ (IsIso b → IsIso c → IsIso a) ∧
      (IsIso c → IsIso a → IsIso b) :=
  let φ : A ⟶ B := ⟨a, b, c, h₁, h₂, h₃⟩
  ⟨fun ha hb => isIso₃_of_isIso₁₂ φ hA hB ha hb, fun hb hc => isIso₁_of_isIso₂₃ φ hA hB hb hc,
    fun hc ha => isIso₂_of_isIso₁₃ φ hA hB ha hc⟩

/-- The three canonical maps `F(-) ⟶ RF(-)` of Stacks 05SX along a distinguished triangle `T` are
the components of a morphism of triangles from `F(T)` to the distinguished triangle of values
`(RF(X), RF(Y), RF(Z))` of Stacks 05SC: read at the identity indices, the compatibility of
`RF(f)`, `RF(g)`, `RF(h)` with the coprojections is exactly its three commuting squares. Two of
the three canonical maps being isomorphisms therefore forces the third. -/
private lemma isIso_ι_idUnder (F : C ⥤ H) [F.CommShift ℤ] [F.IsTriangulated]
    (W : MorphismProperty C) [W.ContainsIdentities] (hW : W.IsSaturated)
    [W.IsCompatibleWithTriangulation] (T : Triangle C) (hT : T ∈ distTriang C)
    (cX : Cocone (MorphismProperty.Under.forget W ⊤ T.obj₁ ⋙ Under.forget T.obj₁ ⋙ F))
    (hcX : F.IsRightDerivedValueAt W T.obj₁ cX)
    (cY : Cocone (MorphismProperty.Under.forget W ⊤ T.obj₂ ⋙ Under.forget T.obj₂ ⋙ F))
    (hcY : F.IsRightDerivedValueAt W T.obj₂ cY)
    (cZ : Cocone (MorphismProperty.Under.forget W ⊤ T.obj₃ ⋙ Under.forget T.obj₃ ⋙ F))
    (hcZ : F.IsRightDerivedValueAt W T.obj₃ cZ) :
    (IsIso (cX.ι.app (idUnder W T.obj₁)) → IsIso (cY.ι.app (idUnder W T.obj₂)) →
        IsIso (cZ.ι.app (idUnder W T.obj₃))) ∧
      (IsIso (cY.ι.app (idUnder W T.obj₂)) → IsIso (cZ.ι.app (idUnder W T.obj₃)) →
        IsIso (cX.ι.app (idUnder W T.obj₁))) ∧
      (IsIso (cZ.ι.app (idUnder W T.obj₃)) → IsIso (cX.ι.app (idUnder W T.obj₁)) →
        IsIso (cY.ι.app (idUnder W T.obj₂))) := by
  obtain ⟨-, -, -, hval⟩ :=
    (F.exists_isRightDerivedValueAt_and_isLeftDerivedValueAt_and_triangle_distinguished
      W hW T hT).1
  obtain ⟨u, v, w, hdist, hu, hv, hw⟩ := hval cX hcX cY hcY cZ hcZ
  exact isIso_two_out_of_three (F.mapTriangle.obj T) (Triangle.mk u v w)
    (F.map_distinguished T hT) hdist
    (hu (idUnder W T.obj₁) (idUnder W T.obj₂) T.mor₁ (comp_idUnder_hom W (𝟭 C) T.mor₁)).symm
    (hv (idUnder W T.obj₂) (idUnder W T.obj₃) T.mor₂ (comp_idUnder_hom W (𝟭 C) T.mor₂)).symm
    (by
      have h := hw (idUnder W T.obj₃) (idUnder W T.obj₁) T.mor₃
        (comp_idUnder_hom W (shiftFunctor C 1) T.mor₃)
      rw [← Category.assoc] at h
      exact h.symm)

/-- The three canonical maps `LF(-) ⟶ F(-)` of Stacks 05SX along a distinguished triangle `T` are
the components of a morphism of triangles from the distinguished triangle of values
`(LF(X), LF(Y), LF(Z))` of Stacks 05SC to `F(T)` — the direction in which the canonical maps go;
read at the identity indices, the compatibility of `LF(f)`, `LF(g)`, `LF(h)` with the projections
is exactly its three commuting squares. Two of the three canonical maps being isomorphisms
therefore forces the third. -/
private lemma isIso_π_idOver (F : C ⥤ H) [F.CommShift ℤ] [F.IsTriangulated]
    (W : MorphismProperty C) [W.ContainsIdentities] (hW : W.IsSaturated)
    [W.IsCompatibleWithTriangulation] (T : Triangle C) (hT : T ∈ distTriang C)
    (cX : Cone (MorphismProperty.Over.forget W ⊤ T.obj₁ ⋙ Over.forget T.obj₁ ⋙ F))
    (hcX : F.IsLeftDerivedValueAt W T.obj₁ cX)
    (cY : Cone (MorphismProperty.Over.forget W ⊤ T.obj₂ ⋙ Over.forget T.obj₂ ⋙ F))
    (hcY : F.IsLeftDerivedValueAt W T.obj₂ cY)
    (cZ : Cone (MorphismProperty.Over.forget W ⊤ T.obj₃ ⋙ Over.forget T.obj₃ ⋙ F))
    (hcZ : F.IsLeftDerivedValueAt W T.obj₃ cZ) :
    (IsIso (cX.π.app (idOver W T.obj₁)) → IsIso (cY.π.app (idOver W T.obj₂)) →
        IsIso (cZ.π.app (idOver W T.obj₃))) ∧
      (IsIso (cY.π.app (idOver W T.obj₂)) → IsIso (cZ.π.app (idOver W T.obj₃)) →
        IsIso (cX.π.app (idOver W T.obj₁))) ∧
      (IsIso (cZ.π.app (idOver W T.obj₃)) → IsIso (cX.π.app (idOver W T.obj₁)) →
        IsIso (cY.π.app (idOver W T.obj₂))) := by
  obtain ⟨-, -, -, hval⟩ :=
    (F.exists_isRightDerivedValueAt_and_isLeftDerivedValueAt_and_triangle_distinguished
      W hW T hT).2
  obtain ⟨u, v, w, hdist, hu, hv, hw⟩ := hval cX hcX cY hcY cZ hcZ
  exact isIso_two_out_of_three (Triangle.mk u v w) (F.mapTriangle.obj T) hdist
    (F.map_distinguished T hT)
    (hu (idOver W T.obj₁) (idOver W T.obj₂) T.mor₁ (idOver_hom_comp W (𝟭 C) T.mor₁))
    (hv (idOver W T.obj₂) (idOver W T.obj₃) T.mor₂ (idOver_hom_comp W (𝟭 C) T.mor₂))
    (hw (idOver W T.obj₃) (idOver W T.obj₁) T.mor₃
      (idOver_hom_comp W (shiftFunctor C 1) T.mor₃))

/-- Abstract form of the propagation argument of Stacks 05SZ, in the three positions: if the
property `d` (definedness, with its choice of value) propagates along the triangle in every
position, and in every position two of the three canonical maps (`i`) being isomorphisms forces
the third, then `∃ c, d c ∧ i c` propagates in every position. -/
private lemma exists_and_of_two_of_three {A B Z : Sort*} (dA iA : A → Prop) (dB iB : B → Prop)
    (dZ iZ : Z → Prop) (hZ : (∃ a, dA a) → (∃ b, dB b) → ∃ z, dZ z)
    (hX : (∃ b, dB b) → (∃ z, dZ z) → ∃ a, dA a) (hY : (∃ z, dZ z) → (∃ a, dA a) → ∃ b, dB b)
    (h : ∀ a, dA a → ∀ b, dB b → ∀ z, dZ z →
      (iA a → iB b → iZ z) ∧ (iB b → iZ z → iA a) ∧ (iZ z → iA a → iB b)) :
    ((∃ a, dA a ∧ iA a) → (∃ b, dB b ∧ iB b) → ∃ z, dZ z ∧ iZ z) ∧
      ((∃ b, dB b ∧ iB b) → (∃ z, dZ z ∧ iZ z) → ∃ a, dA a ∧ iA a) ∧
      ((∃ z, dZ z ∧ iZ z) → (∃ a, dA a ∧ iA a) → ∃ b, dB b ∧ iB b) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨a, ha, iA⟩ ⟨b, hb, iB⟩
    obtain ⟨z, hz⟩ := hZ ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨z, hz, (h a ha b hb z hz).1 iA iB⟩
  · rintro ⟨b, hb, iB⟩ ⟨z, hz, iZ⟩
    obtain ⟨a, ha⟩ := hX ⟨b, hb⟩ ⟨z, hz⟩
    exact ⟨a, ha, (h a ha b hb z hz).2.1 iB iZ⟩
  · rintro ⟨z, hz, iZ⟩ ⟨a, ha, iA⟩
    obtain ⟨b, hb⟩ := hY ⟨z, hz⟩ ⟨a, ha⟩
    exact ⟨b, hb, (h a ha b hb z hz).2.2 iZ iA⟩

/-- The three `RF` conjuncts of Stacks 05SZ: along a distinguished triangle, two of the three
objects computing `RF` forces the third to compute `RF`. -/
private theorem computesRightDerived_of_distTriang (F : C ⥤ H)
    [F.CommShift ℤ] [F.IsTriangulated] (W : MorphismProperty C) [W.ContainsIdentities]
    (hW : W.IsSaturated) [W.IsCompatibleWithTriangulation]
    (T : Triangle C) (hT : T ∈ distTriang C) :
    (F.ComputesRightDerived W T.obj₁ → F.ComputesRightDerived W T.obj₂ →
        F.ComputesRightDerived W T.obj₃) ∧
      (F.ComputesRightDerived W T.obj₂ → F.ComputesRightDerived W T.obj₃ →
        F.ComputesRightDerived W T.obj₁) ∧
      (F.ComputesRightDerived W T.obj₃ → F.ComputesRightDerived W T.obj₁ →
        F.ComputesRightDerived W T.obj₂) := by
  obtain ⟨hZ, hX, hY, -⟩ :=
    (F.exists_isRightDerivedValueAt_and_isLeftDerivedValueAt_and_triangle_distinguished
      W hW T hT).1
  exact exists_and_of_two_of_three _ _ _ _ _ _ hZ hX hY (isIso_ι_idUnder F W hW T hT)

/-- The three `LF` conjuncts of Stacks 05SZ: along a distinguished triangle, two of the three
objects computing `LF` forces the third to compute `LF`. -/
private theorem computesLeftDerived_of_distTriang (F : C ⥤ H)
    [F.CommShift ℤ] [F.IsTriangulated] (W : MorphismProperty C) [W.ContainsIdentities]
    (hW : W.IsSaturated) [W.IsCompatibleWithTriangulation]
    (T : Triangle C) (hT : T ∈ distTriang C) :
    (F.ComputesLeftDerived W T.obj₁ → F.ComputesLeftDerived W T.obj₂ →
        F.ComputesLeftDerived W T.obj₃) ∧
      (F.ComputesLeftDerived W T.obj₂ → F.ComputesLeftDerived W T.obj₃ →
        F.ComputesLeftDerived W T.obj₁) ∧
      (F.ComputesLeftDerived W T.obj₃ → F.ComputesLeftDerived W T.obj₁ →
        F.ComputesLeftDerived W T.obj₂) := by
  obtain ⟨hZ, hX, hY, -⟩ :=
    (F.exists_isRightDerivedValueAt_and_isLeftDerivedValueAt_and_triangle_distinguished
      W hW T hT).2
  exact exists_and_of_two_of_three _ _ _ _ _ _ hZ hX hY (isIso_π_idOver F W hW T hT)

end DerivedFunctorDistTriang

namespace CategoryTheory.Functor

open DerivedFunctorDistTriang

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {H : Type u₂} [Category.{v₂} H] [HasZeroObject H] [HasShift H ℤ] [Preadditive H]
  [∀ n : ℤ, (shiftFunctor H n).Additive] [Pretriangulated H]

/-- **Stacks 05SZ**. Let `F : 𝒟 ⥤ 𝒟'` be an exact functor of pretriangulated categories and let
`W` be a saturated multiplicative system in `𝒟` (Stacks 05Q8) compatible with the triangulation.
Let `T = (X, Y, Z, f, g, h)` be a distinguished triangle of `𝒟`.

If two of the three objects `X`, `Y`, `Z` compute the right derived functor `RF` — that is, `RF` is
defined at each of them and the canonical map `F(-) ⟶ RF(-)` is an isomorphism there (Stacks 05SX)
— then the third computes `RF` as well. Similarly for the left derived functor `LF`.

The source states only the case where `X` and `Y` are assumed to compute; the other two positions
are asserted as well because its applications use them (see the module docstring). -/
@[stacks 05SZ, sga "4 XVII 1.2.2" "(i), special case"]
public theorem computesRightDerived_and_computesLeftDerived_of_distTriang (F : C ⥤ H)
    [F.CommShift ℤ] [F.IsTriangulated] (W : MorphismProperty C) [W.ContainsIdentities]
    (hW : W.IsSaturated) [W.IsCompatibleWithTriangulation]
    (T : Triangle C) (hT : T ∈ distTriang C) :
    (F.ComputesRightDerived W T.obj₁ → F.ComputesRightDerived W T.obj₂ →
        F.ComputesRightDerived W T.obj₃) ∧
      (F.ComputesRightDerived W T.obj₂ → F.ComputesRightDerived W T.obj₃ →
        F.ComputesRightDerived W T.obj₁) ∧
      (F.ComputesRightDerived W T.obj₃ → F.ComputesRightDerived W T.obj₁ →
        F.ComputesRightDerived W T.obj₂) ∧
      (F.ComputesLeftDerived W T.obj₁ → F.ComputesLeftDerived W T.obj₂ →
        F.ComputesLeftDerived W T.obj₃) ∧
      (F.ComputesLeftDerived W T.obj₂ → F.ComputesLeftDerived W T.obj₃ →
        F.ComputesLeftDerived W T.obj₁) ∧
      (F.ComputesLeftDerived W T.obj₃ → F.ComputesLeftDerived W T.obj₁ →
        F.ComputesLeftDerived W T.obj₂) := by
  obtain ⟨r₁, r₂, r₃⟩ := computesRightDerived_of_distTriang F W hW T hT
  obtain ⟨l₁, l₂, l₃⟩ := computesLeftDerived_of_distTriang F W hW T hT
  exact ⟨r₁, r₂, r₃, l₁, l₂, l₃⟩

end CategoryTheory.Functor

end

end
