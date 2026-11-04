module

public import StacksFrontier.AlgebraicGeometry.Cohomology.ClosedImmersionSections
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Isomorphism
public import StacksFrontier.AlgebraicGeometry.Cohomology.DerivedSections

/-!
# Further results on `ClosedImmersionSections`

Results about the objects of `StacksFrontier.AlgebraicGeometry.Cohomology.ClosedImmersionSections`
that need imports beyond those of that module.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.Cohomology.ClosedImmersion

/-- **Cohomology vanishes across an isomorphism of schemes.** For an isomorphism `f : Y ⟶ Z` and
a sheaf of modules `N` on `Z`, the group `Hⁿ(Z, N)` is zero if and only if `Hⁿ(Y, f^*N)` is. -/
theorem isZero_rightDerived_sectionsFunctor_pullback_iff_of_isIso {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [IsIso f] (N : Z.Modules) (n : ℕ) :
    IsZero (((Stacks.Cohomology.sectionsFunctor Z ⊤).rightDerived n).obj N) ↔
      IsZero (((Stacks.Cohomology.sectionsFunctor Y ⊤).rightDerived n).obj
        ((Scheme.Modules.pullback f).obj N)) :=
  (((Stacks.Cohomology.sectionsFunctor Z ⊤).rightDerived n).mapIso
      (_root_.Stacks.ClosedImmersion.unitIsoOfIsIso f N)).isZero_iff.trans
    (isZero_rightDerived_sectionsFunctor_pushforward_iff f
      ((Scheme.Modules.pullback f).obj N) n)

end Stacks.Cohomology.ClosedImmersion

end
