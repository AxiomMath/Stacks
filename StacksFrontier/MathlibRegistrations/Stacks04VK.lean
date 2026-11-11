module

public import Mathlib.CategoryTheory.Localization.Predicate
public import StacksCore.Tactic.StacksAttribute

/-! SGA registrations of `CategoryTheory.Functor.q_isLocalization`: the generic localization
`W.Q : C ⥤ W.Localization` is a localization functor. This is not Stacks 04VK, which concerns
the category of right fractions of a right multiplicative system; that lemma is
`CategoryTheory.MorphismProperty.RightLocalization.Q` / `isIso_Q_map` / `existsUnique_lift` in
`StacksFrontier.CategoryTheory.Localization.RightFraction.UniversalProperty`. -/

@[expose] public section

add_to_sga "4½ Etat_0 2.3.1" "partial" CategoryTheory.Functor.q_isLocalization
add_to_sga "4½ Etat_0 2.3.2" "partial" CategoryTheory.Functor.q_isLocalization
