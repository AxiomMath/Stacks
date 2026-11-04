module
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Etale.DerivedUpperShriekAdjunction
import all StacksFrontier.AlgebraicGeometry.Etale.DerivedUpperShriekAdjunction

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.LeftExact
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.DerivedAdjunction
public import StacksFrontier.CategoryTheory.Sites.SheafComposeColimits
public import StacksFrontier.AlgebraicGeometry.Etale.UpperShriekQuasiFinite

import StacksCore.Tactic.StacksAttribute

/-!
# DerivedUpperShriekAdjunctionUnconditional

Stronger forms of declarations of
`StacksFrontier.AlgebraicGeometry.Etale.DerivedUpperShriekAdjunction`, stated as separate
declarations beside the ones there: over more general coefficient universes, or with inputs that
are carried there as hypotheses discharged, together with the new results built on them.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w r

namespace AlgebraicGeometry.SmallEtale

section Abelian

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

variable [HasDerivedCategory.{w} (AbelianSheaf.{u, v} B X)]
  [HasDerivedCategory.{w} (AbelianSheaf.{u, v} B Y)]

end Abelian

section Module

variable (B : BigEtaleSite.{u}) (S : B.Scheme) (Λ : Type r) [Ring Λ]

/-- Sheafification is available for presheaves of `Λ`-modules on the localization of the small
étale site at one of its objects, at the same coefficient universe: the slice is again essentially
small in that universe.

This is a theorem and not a global instance: its conclusion is stated at the coefficient universe
`max (u + 1) v r`, and offered to a goal at a universe such as `u + 1` the unifier is left with the
undetermined constraint `u + 1 =?= max (u + 1) ?v`, which is reported as an error rather than as a
failed match. Files that need it at the universe `max (u + 1) v r` enable it with
`attribute [local instance]`. -/
public theorem hasSheafify_moduleSheaf_over (V : SmallEtale B S.obj S.property) :
    HasSheafify ((SmallEtale.topology B S.obj S.property).over V)
      (ModuleCat.{max (u + 1) v r} Λ) := by
  have := preservesFilteredColimits_forgetModuleCat.{max (u + 1) v r} Λ
  have : EssentiallySmall.{max (u + 1) v r} (Over V) := inferInstance
  exact hasSheafifyEssentiallySmallSite.{_, _, _, _, max (u + 1) v r} _ _

section Shriek

variable {X Y : B.Scheme}

variable [HasDerivedCategory.{w} (ModuleSheaf.{u, v, r} B X Λ)]
  [HasDerivedCategory.{w} (ModuleSheaf.{u, v, r} B Y Λ)]

end Shriek

end Module

end AlgebraicGeometry.SmallEtale

end
