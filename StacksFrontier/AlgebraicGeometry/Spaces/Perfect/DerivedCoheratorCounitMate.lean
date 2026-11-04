module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Transferring an invertible counit along a square of adjunctions

In a square of adjunctions `L ⊣ R`, `L' ⊣ R'`, `p ⊣ P`, `q ⊣ Q` a 2-cell `θ : L ⋙ q ⟶ p ⋙ L'`
has two successive mates: `α : P ⋙ L ⟶ L' ⋙ Q` over `p ⊣ P`, `q ⊣ Q`, and then
`σ : R' ⋙ P ⟶ Q ⋙ R` over `L ⊣ R`, `L' ⊣ R'`.  The iterated mate is the conjugate of `θ`, so
`σ` is invertible when `θ` is, and the counit square of `σ` then carries invertibility of the
counit of `L' ⊣ R'` at `Y` to invertibility of the counit of `L ⊣ R` at `Q Y`.

## Main results

* `Stacks.CategoryTheory.isIso_mateEquiv_mateEquiv`: the iterated mate of an invertible 2-cell
  is invertible.
* `Stacks.CategoryTheory.isIso_counit_app_obj_of_isIso_mateEquiv_app`: invertibility of a counit
  transfers along the square.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

namespace Stacks.CategoryTheory

variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  {L : A ⥤ B} {R : B ⥤ A} {L' : A' ⥤ B'} {R' : B' ⥤ A'}
  {p : A ⥤ A'} {P : A' ⥤ A} {q : B ⥤ B'} {Q : B' ⥤ B}

/-- **The iterated mate of an invertible 2-cell is invertible.**  For a square of adjunctions
`L ⊣ R`, `L' ⊣ R'`, `p ⊣ P`, `q ⊣ Q` and an invertible `θ : L ⋙ q ⟶ p ⋙ L'`, the mate over
`L ⊣ R`, `L' ⊣ R'` of the mate of `θ` over `p ⊣ P`, `q ⊣ Q` is invertible: it is the conjugate
of `θ` for the two composite adjunctions `L ⋙ q ⊣ Q ⋙ R` and `p ⋙ L' ⊣ R' ⋙ P`. -/
theorem isIso_mateEquiv_mateEquiv (adj : L ⊣ R) (adj' : L' ⊣ R') (adjp : p ⊣ P) (adjq : q ⊣ Q)
    (θ : TwoSquare L p q L') (hθ : IsIso θ.natTrans) :
    IsIso (mateEquiv adj' adj (mateEquiv adjp adjq θ)).natTrans := by
  rw [iterated_mateEquiv_conjugateEquiv adjp adjq adj adj' θ]
  exact conjugateEquiv_iso (adjp.comp adj') (adj.comp adjq) θ.natTrans

/-- **Invertibility of a counit transfers along a square of adjunctions.**  In the situation of
`Stacks.CategoryTheory.isIso_mateEquiv_mateEquiv`, if moreover the mate
`α : P ⋙ L ⟶ L' ⋙ Q` of `θ` is invertible at `R' Y` and the counit of `L' ⊣ R'` is invertible
at `Y`, then the counit of `L ⊣ R` is invertible at `Q Y`.

The counit square `L(σ_Y) ≫ ε_{Q Y} = α_{R' Y} ≫ Q(ε'_Y)` of the mate `σ` of `α` has an
invertible right-hand side and an invertible first factor on the left. -/
theorem isIso_counit_app_obj_of_isIso_mateEquiv_app (adj : L ⊣ R) (adj' : L' ⊣ R')
    (adjp : p ⊣ P) (adjq : q ⊣ Q) (θ : TwoSquare L p q L') (hθ : IsIso θ.natTrans) (Y : B')
    (hα : IsIso ((mateEquiv adjp adjq θ).app (R'.obj Y))) (hY : IsIso (adj'.counit.app Y)) :
    IsIso (adj.counit.app (Q.obj Y)) := by
  have := isIso_mateEquiv_mateEquiv adj adj' adjp adjq θ hθ
  have := NatIso.isIso_app_of_isIso
    (mateEquiv adj' adj (mateEquiv adjp adjq θ)).natTrans Y
  have hsq := mateEquiv_counit adj' adj (mateEquiv adjp adjq θ) Y
  have hrhs : IsIso ((mateEquiv adjp adjq θ).app (R'.obj Y) ≫
      Q.map (adj'.counit.app Y)) := inferInstance
  rw [← hsq] at hrhs
  exact IsIso.of_isIso_comp_left
    (L.map ((mateEquiv adj' adj (mateEquiv adjp adjq θ)).app Y)) _

end Stacks.CategoryTheory

end
