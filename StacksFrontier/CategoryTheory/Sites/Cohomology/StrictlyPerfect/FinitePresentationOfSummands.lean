module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFinite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.ConeOfAMorphism
import StacksCore.Tactic.StacksAttribute

/-!
# A direct summand of a finite free sheaf of modules is of finite presentation

Let `(C, O)` be a ringed site. A direct summand of a finite free `O`-module, that is, a retract
of `O^{⊕n}`, is an `O`-module of finite presentation.

## Main results

* `Stacks.SheafOfModules.isFinitePresentation_of_isDirectSummandOfFiniteFree`: a direct summand
  of a finite free `O`-module is of finite presentation.

## References

* [Stacks Project, Tag 08FM](https://stacks.math.columbia.edu/tag/08FM)
* [Stacks Project, Tag 0H98](https://stacks.math.columbia.edu/tag/0H98)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
  [∀ T : C, HasSheafify (J.over T) AddCommGrpCat.{w}]
  [∀ T : C, (J.over T).WEqualsLocallyBijective AddCommGrpCat.{w}]

omit [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})] in
/-- **A direct summand of a finite free `O`-module is of finite presentation.** -/
theorem isFinitePresentation_of_isDirectSummandOfFiniteFree (F : _root_.SheafOfModules.{w} R)
    (hF : IsDirectSummandOfFiniteFree R F) : F.IsFinitePresentation := by
  obtain ⟨n, i, r, hir⟩ := (isDirectSummandOfFiniteFree_iff_free R F).1 hF
  obtain ⟨p, hp⟩ := exists_isFinite_presentation_of_retract i r hir
  let := hp
  exact SliceFinite.isFinitePresentation_of_presentation p

end Stacks.SheafOfModules

end
