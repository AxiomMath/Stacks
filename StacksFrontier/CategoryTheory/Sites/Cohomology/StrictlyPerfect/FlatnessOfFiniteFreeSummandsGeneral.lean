module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.FlatnessOfFiniteFreeSummands

/-!
# Flatness of direct summands of finite free modules, at an arbitrary universe of sections

The three results of
`StacksFrontier/CategoryTheory/Sites/Cohomology/StrictlyPerfect/FlatnessOfFiniteFreeSummands.lean`
at `RingedSite.{u, v, w}`, with the universe of sections free. The unit law, hence the flatness
of the structure sheaf (`Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit`), holds at a
free universe `w` of sections, and so do Stacks 05NG for finite direct sums and the retract
argument. The small étale ringed site of a scheme, a `RingedSite.{u + 1, u, u}`, is the case
that needs them.

## Main results

* `Stacks.SheafOfModules.isFlat_free_general`: a finite free `O`-module is flat.
* `Stacks.SheafOfModules.isFlat_of_isDirectSummandOfFiniteFree_general`: a direct summand of a
  finite free `O`-module is flat.
* `Stacks.SheafOfModules.isFlat_X_of_isStrictlyPerfect_general`: every term of a strictly
  perfect complex of `O`-modules is flat.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w

namespace Stacks.SheafOfModules

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {Y : RingedSite.{u, v, w}}
  [HasSheafify Y.J AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **A finite free `O`-module is flat**, at an arbitrary universe of sections. -/
theorem isFlat_free_general (I : Type w) [Finite I] :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := Y.O)
      (_root_.SheafOfModules.free (R := Stacks.SheafOfModules.Tensor.ringSheaf Y.O) I) :=
  FlatColimits.isFlat_coproduct_finite Y.O
    (fun _ : I => _root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    fun _ => DerivedTensorProduct.isFlat_unit

/-- **A direct summand of a finite free `O`-module is flat**, at an arbitrary universe of
sections. -/
theorem isFlat_of_isDirectSummandOfFiniteFree_general
    (F : AlgebraicGeometry.RingedSite.Modules.{u, v, w} Y)
    (hF : IsDirectSummandOfFiniteFree (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := Y.O) F := by
  obtain ⟨n, i, r, hir⟩ :=
    (isDirectSummandOfFiniteFree_iff_free (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F).1 hF
  exact FlatRetract.isFlat_of_retract Y.O i r hir (isFlat_free_general (ULift.{w} (Fin n)))

/-- **Every term of a strictly perfect complex of `O`-modules is flat**, at an arbitrary
universe of sections. -/
theorem isFlat_X_of_isStrictlyPerfect_general
    {P : CochainComplex (AlgebraicGeometry.RingedSite.Modules.{u, v, w} Y) ℤ}
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) P) (i : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := Y.O) (P.X i) :=
  isFlat_of_isDirectSummandOfFiniteFree_general (P.X i) (hP.termDirectSummand i)

end Stacks.SheafOfModules

end
