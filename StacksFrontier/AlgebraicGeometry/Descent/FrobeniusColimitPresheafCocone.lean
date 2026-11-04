module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitRestrictReduction

/-!
# The presheaf cocone of Stacks Tag 0EXB

After `SheafOfModules.toSheaf` the cocone of Stacks Tag 0EXB is the image under abelian
sheafification of a cocone of presheaves of `𝒪_X`-modules built from the objectwise extensions
of scalars

`j ↦ 𝒪_X ⊗_{φ^j, 𝒪_X} 𝒢`, with apex `(colim_j 𝒪_X) ⊗_{𝒪_X} 𝒢`,

by `AlgebraicGeometry.frobeniusExtendScalarsIterCompToSheafIso` and
`AlgebraicGeometry.frobeniusStageExtendScalarsCompToSheafIso`. This file builds that presheaf
cocone and the arithmetic of the powers of Frobenius which indexes it.

## Main results

* `AlgebraicGeometry.frobeniusRingSheafIter_comp_frobeniusRingSheafHom`: the `j`-th power of
  Frobenius followed by Frobenius is the `j + 1`-st power.
* `AlgebraicGeometry.frobeniusRingSheafHom_hom_comp_frobeniusRingPresheafι_succ`: Frobenius
  followed by the stage-`n + 1` coprojection into `colim_j 𝒪_X` is the stage-`n` coprojection.
* `AlgebraicGeometry.frobeniusRingSheafIter_hom_comp_frobeniusRingPresheafι`: the `j`-th power
  of Frobenius followed by the stage-`n + j` coprojection into `colim_j 𝒪_X` is the stage-`n`
  coprojection.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)

/-- **The `j`-th power of Frobenius followed by Frobenius is the `j + 1`-st power.** -/
lemma frobeniusRingSheafIter_comp_frobeniusRingSheafHom (j : ℕ) :
    frobeniusRingSheafIter X p hX j ≫ frobeniusRingSheafHom X p hX =
      frobeniusRingSheafIter X p hX (j + 1) := by
  induction j with
  | zero => exact (Category.id_comp _).trans (Category.comp_id _).symm
  | succ j ih => exact (Category.assoc _ _ _).trans (congrArg (frobeniusRingSheafHom X p hX ≫ ·) ih)

/-- Frobenius, as an endomorphism of `AlgebraicGeometry.Scheme.ringSheafOnOpens`, followed by the
stage-`n + 1` coprojection into the presheaf colimit `colim_j 𝒪_X` is the stage-`n`
coprojection. -/
lemma frobeniusRingSheafHom_hom_comp_frobeniusRingPresheafι_succ (n : ℕ) :
    (frobeniusRingSheafHom X p hX).hom ≫ frobeniusRingPresheafι X p hX (n + 1) =
      frobeniusRingPresheafι X p hX n :=
  comp_ringPresheafEndoColimitι_succ (frobeniusRingSheafHom X p hX) n

/-- **The `j`-th power of Frobenius followed by the stage-`n + j` coprojection into the presheaf
`colim_j 𝒪_X` is the stage-`n` coprojection.** -/
lemma frobeniusRingSheafIter_hom_comp_frobeniusRingPresheafι (j : ℕ) : ∀ n : ℕ,
    (frobeniusRingSheafIter X p hX j).hom ≫ frobeniusRingPresheafι X p hX (n + j) =
      frobeniusRingPresheafι X p hX n := by
  induction j with
  | zero => exact fun _ ↦ Category.id_comp _
  | succ j ih =>
    intro n
    have hstep : (frobeniusRingSheafIter X p hX (j + 1)).hom =
        (frobeniusRingSheafHom X p hX).hom ≫ (frobeniusRingSheafIter X p hX j).hom :=
      rfl
    rw [hstep, Category.assoc, show n + (j + 1) = n + 1 + j by lia, ih (n + 1),
      frobeniusRingSheafHom_hom_comp_frobeniusRingPresheafι_succ]

end AlgebraicGeometry

end
