module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Limits.Opposites
public import Mathlib.CategoryTheory.Limits.Yoneda
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Representability of set-valued functors on a Grothendieck abelian category

Let `A` be a Grothendieck abelian category and let `F : Aᵒᵖ ⥤ Set` be a functor. Then `F` is
representable if and only if it commutes with colimits, that is, `F (colim_i N_i) = lim_i F (N_i)`
for every diagram `I ⥤ A`; equivalently, `F` preserves limits as a functor out of `Aᵒᵖ`.

One direction holds over any category and for purely formal reasons: a representable presheaf
preserves limits, since the universal property of a colimit says exactly that maps out of it are
compatible families of maps out of the pieces.

The converse is the special adjoint functor theorem. A Grothendieck abelian category is
cocomplete, is well-powered and has a separator, so its opposite is complete, is well-powered
(subobjects of an object of an abelian category correspond to its quotients) and has a
coseparator. A limit-preserving functor `F : Aᵒᵖ ⥤ Set` out of such a category therefore has a
left adjoint `L : Set ⥤ Aᵒᵖ`, and evaluating the adjunction bijection at a one-element set
identifies `F N` with `Hom_A (N, L ∗)` naturally in `N`, so `L ∗` represents `F`.

## Main results

* `Stacks.Injectives.representableByOfIsRightAdjoint`: a presheaf of sets which is a right adjoint
  is represented by the value of its left adjoint at a one-element set.
* `Stacks.Injectives.isRepresentable_iff_preservesLimits`: a set-valued functor on the opposite of
  a Grothendieck abelian category is representable if and only if it preserves limits.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace Stacks.Injectives

variable {C : Type u} [Category.{v} C]

/-- A presheaf of sets which is a right adjoint is represented by the value of its left adjoint
at a one-element set, the adjunction bijection at that set being the required bijection
`(N ⟶ L ∗) ≃ F N`. -/
noncomputable def representableByOfIsRightAdjoint (F : Cᵒᵖ ⥤ Type w) [F.IsRightAdjoint] :
    F.RepresentableBy (F.leftAdjoint.obj PUnit.{w + 1}).unop where
  homEquiv {X} :=
    Equiv.trans
      { toFun g := g.op
        invFun h := h.unop
        left_inv _ := rfl
        right_inv _ := rfl }
      (((Adjunction.ofIsRightAdjoint F).homEquiv PUnit.{w + 1} (op X)).trans
        { toFun h := h PUnit.unit
          invFun y := ↾fun _ ↦ y
          left_inv _ := rfl
          right_inv _ := rfl })
  homEquiv_comp {X X'} f g := by
    dsimp
    rw [Adjunction.homEquiv_naturality_right]
    rfl

variable (C) in
/-- The opposite of a Grothendieck abelian category has a coseparator, is complete and is
well-powered, so the special adjoint functor theorem applies to functors out of it. -/
theorem isRightAdjoint_of_preservesLimits [Abelian C] [IsGrothendieckAbelian.{w} C]
    (F : Cᵒᵖ ⥤ Type w) [PreservesLimitsOfSize.{w, w} F] : F.IsRightAdjoint :=
  isRightAdjoint_of_preservesLimits_of_isCoseparating (isCoseparator_coseparator Cᵒᵖ) F

/-- Let `A` be a Grothendieck abelian category and `F : Aᵒᵖ ⥤ Set` a functor. Then `F` is
representable if and only if it commutes with colimits, that is, `F (colim_i N_i) = lim_i F (N_i)`
for every diagram `I ⥤ A`. -/
@[stacks 07D7, sga "4 I 8.12.7" "Grothendieck abelian"]
theorem isRepresentable_iff_preservesLimits [Abelian C] [IsGrothendieckAbelian.{w} C]
    (F : Cᵒᵖ ⥤ Type w) : F.IsRepresentable ↔ PreservesLimitsOfSize.{w, w} F := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h
    infer_instance
  · have := h
    have := isRightAdjoint_of_preservesLimits C F
    exact (representableByOfIsRightAdjoint F).isRepresentable

end Stacks.Injectives

end
