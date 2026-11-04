module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.ReesGradedModule
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.Basic

/-!
# The pieces of the graded module `⨁ₙ ℐⁿF`, one degree at a time

`Stacks.Blowup.reesGradedModule I F` is the graded module `⨁ₙ ℐⁿF` over the Rees algebra. Its
pieces in negative degrees are zero objects, and every piece is quasi-coherent when `F` is: in
nonnegative degrees by `Stacks.Blowup.reesMultiple_isQuasicoherent`, and in negative degrees
because a zero object is quasi-coherent.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Algebraization

namespace Stacks.Blowup

universe u

/-- **In negative degrees the pieces of `⨁ₙ ℐⁿF` are zero objects**, because `ℐⁿF` is there the
zero subsheaf of `F` (`Stacks.Blowup.reesMultiple_eq_bot_of_neg`). -/
public lemma isZero_piece_reesGradedModule_of_neg {X : Scheme.{u}} (I : X.IdealSheafData)
    (F : X.Modules) (n : ℤ) (hn : n < 0) : IsZero ((reesGradedModule I F).piece n) :=
  SheafOfModules.Submodule.isZero_toSheafOfModules_of_eq_bot
    (reesMultiple_eq_bot_of_neg I n F hn)

/-- **Every piece of the graded module `⨁ₙ ℐⁿF` over the Rees algebra is quasi-coherent when `F`
is.** In nonnegative degrees this is `Stacks.Blowup.reesMultiple_isQuasicoherent`; in negative
degrees the piece is a zero object. -/
public lemma isQuasicoherent_piece_reesGradedModule {X : Scheme.{u}} (I : X.IdealSheafData)
    (F : X.Modules) [F.IsQuasicoherent] (n : ℤ) :
    ((reesGradedModule I F).piece n).IsQuasicoherent := by
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact reesMultiple_isQuasicoherent I m F
  · exact Stacks.AlgebraicGeometry.HigherDirectImage.isQuasicoherent_of_isZero
      (M := (reesGradedModule I F).piece n) (isZero_piece_reesGradedModule_of_neg I F n hn)

end Stacks.Blowup

end
