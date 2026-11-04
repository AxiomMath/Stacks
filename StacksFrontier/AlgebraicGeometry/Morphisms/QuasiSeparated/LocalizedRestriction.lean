module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.Sections

/-!
# Restriction maps of a sheaf of modules

Elementary lemmas on the restriction maps of a sheaf of modules on a scheme: that restricting
twice is restricting once, that restricting along `le_rfl` is the identity, and that a section
over an open contained in `⊥` vanishes.

## Main results

* `Stacks.AlgebraicGeometry.QcqsLocalizedRestriction.res_res`, `.resRing_res`: restriction maps
  compose.
* `Stacks.AlgebraicGeometry.QcqsLocalizedRestriction.res_self`, `.resRing_self`: restricting
  along `le_rfl` is the identity.
* `Stacks.AlgebraicGeometry.QcqsLocalizedRestriction.eq_zero_of_le_bot`: a section over an open
  below `⊥` is zero.

## Implementation notes

In `res_res` and `resRing_res` the inequality `C ≤ A` is an explicit argument, so that the
right-hand side is stated with whichever proof of it is given.

## References

* [Stacks Project, Tag 01P7](https://stacks.math.columbia.edu/tag/01P7)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.AlgebraicGeometry.QcqsLocalizedRestriction

variable {X : Scheme.{u}}

/-- Restriction maps of the underlying abelian presheaf of a sheaf of modules compose:
restricting `A → B → C` equals the direct restriction `A → C`. -/
theorem res_res (M : X.Modules) {A B C : X.Opens} (hBA : B ≤ A) (hCB : C ≤ B)
    (hCA : C ≤ A) (x : Γ(M, A)) :
    M.presheaf.map (homOfLE hCB).op (M.presheaf.map (homOfLE hBA).op x)
      = M.presheaf.map (homOfLE hCA).op x := by
  simp [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]

/-- The structure-sheaf case of `res_res`. -/
theorem resRing_res {A B C : X.Opens} (hBA : B ≤ A) (hCB : C ≤ B)
    (hCA : C ≤ A) (g : Γ(X, A)) :
    X.presheaf.map (homOfLE hCB).op (X.presheaf.map (homOfLE hBA).op g)
      = X.presheaf.map (homOfLE hCA).op g := by
  simp [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]

/-- Restricting a section of a sheaf of modules along `A ≤ A` does nothing. -/
theorem res_self (M : X.Modules) {A : X.Opens} (x : Γ(M, A)) :
    M.presheaf.map (homOfLE (le_refl A)).op x = x := by
  simp

/-- The structure-sheaf case of `res_self`. -/
theorem resRing_self {A : X.Opens} (g : Γ(X, A)) :
    X.presheaf.map (homOfLE (le_refl A)).op g = g := by
  simp

/-- A section of a sheaf of modules over an open contained in `⊥` vanishes: it is determined by
its restrictions to the empty cover. -/
theorem eq_zero_of_le_bot (M : X.Modules) {V : X.Opens} (hV : V ≤ ⊥)
    (x : Γ(M, V)) : x = 0 :=
  TopCat.Sheaf.eq_of_locally_eq' (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab X)
    (fun i : PEmpty.{u + 1} => i.elim) V (fun i => i.elim) (hV.trans bot_le) x 0
    (fun i => i.elim)

end Stacks.AlgebraicGeometry.QcqsLocalizedRestriction

end
