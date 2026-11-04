module

public import StacksFrontier.CategoryTheory.Sites.Localization.AndMorphisms
public import Mathlib.CategoryTheory.GuitartExact.KanExtension
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# The base change of right Kan extensions of a commutative square, as a mate

For a commutative square of functors `u' ⋙ v = v' ⋙ u`, the base change of right Kan extensions
of the opposite square is the mate of the square of precomposition functors along the right Kan
extension adjunctions of `u` and `u'`. Its mate along those of `v` and `v'` is therefore the
conjugate of an isomorphism, hence invertible.

## Main definitions

* `Stacks.Sites.CocontinuousExchange.precompositionSquare`: the commutative square read on
  precomposition functors.

## Main results

* `Stacks.Sites.CocontinuousExchange.ranBaseChange_eq_mateEquiv`: the base change of right Kan
  extensions is the mate of the square of precomposition functors.
* `Stacks.Sites.CocontinuousExchange.isIso_mateEquiv_ranBaseChange`: the mate of the base change
  of right Kan extensions along the restrictions by `v` and `v'` is invertible.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor

namespace Stacks.Sites.CocontinuousExchange

variable {C' C D' D : Type*} [Category* C'] [Category* C] [Category* D'] [Category* D]
  {u' : C' ⥤ D'} {u : C ⥤ D} {v' : C' ⥤ C} {v : D' ⥤ D} (hsq : u' ⋙ v = v' ⋙ u)
  (H : Type*) [Category* H]

/-- The commutative square read on precomposition functors. -/
def precompositionSquare :
    TwoSquare ((whiskeringLeft _ _ H).obj v.op) ((whiskeringLeft _ _ H).obj u.op)
      ((whiskeringLeft _ _ H).obj u'.op) ((whiskeringLeft _ _ H).obj v'.op) :=
  TwoSquare.mk _ _ _ _
    { app := fun M => Functor.whiskerRight (twoSquare hsq).op.natTrans M
      naturality := fun M M' g => by
        ext X
        exact (g.naturality _).symm }

/-- The natural transformation of the square of precomposition functors is an isomorphism. -/
instance isIso_precompositionSquare : IsIso (precompositionSquare hsq H).natTrans := by
  haveI : IsIso (twoSquare hsq).op.natTrans := inferInstance
  haveI : ∀ M : Dᵒᵖ ⥤ H, IsIso ((precompositionSquare hsq H).natTrans.app M) := fun M =>
    inferInstanceAs (IsIso (Functor.whiskerRight (twoSquare hsq).op.natTrans M))
  exact NatIso.isIso_of_isIso_app _

variable [∀ F : C'ᵒᵖ ⥤ H, u'.op.HasRightKanExtension F] [∀ F : Cᵒᵖ ⥤ H, u.op.HasRightKanExtension F]

/-- **The base change of right Kan extensions of a commutative square is the mate of the square
of precomposition functors.** -/
theorem ranBaseChange_eq_mateEquiv :
    (twoSquare hsq).op.ranBaseChange (D := H) =
      (mateEquiv (u.op.ranAdjunction H) (u'.op.ranAdjunction H)
        (precompositionSquare hsq H)).natTrans := by
  refine NatTrans.ext (funext fun F => ?_)
  rw [TwoSquare.ranBaseChange_app]
  refine ((u'.op.ranAdjunction H).homEquiv _ _).symm.injective ?_
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  refine Eq.trans ?_ (mateEquiv_counit (u.op.ranAdjunction H) (u'.op.ranAdjunction H)
    (precompositionSquare hsq H) F).symm
  rw [Functor.ranAdjunction_counit]
  ext X
  simp [precompositionSquare]

variable [∀ F : C'ᵒᵖ ⥤ H, v'.op.HasRightKanExtension F]
  [∀ F : D'ᵒᵖ ⥤ H, v.op.HasRightKanExtension F]

/-- **The mate of the base change of right Kan extensions along the two restrictions is
invertible.** -/
theorem isIso_mateEquiv_ranBaseChange :
    IsIso (mateEquiv (v'.op.ranAdjunction H) (v.op.ranAdjunction H)
      (TwoSquare.mk _ _ _ _ ((twoSquare hsq).op.ranBaseChange (D := H)))).natTrans := by
  rw [show TwoSquare.mk _ _ _ _ ((twoSquare hsq).op.ranBaseChange (D := H)) =
    mateEquiv (u.op.ranAdjunction H) (u'.op.ranAdjunction H) (precompositionSquare hsq H) from
      ranBaseChange_eq_mateEquiv hsq H, iterated_mateEquiv_conjugateEquiv]
  exact conjugateEquiv_iso _ _ (precompositionSquare hsq H).natTrans

end Stacks.Sites.CocontinuousExchange
