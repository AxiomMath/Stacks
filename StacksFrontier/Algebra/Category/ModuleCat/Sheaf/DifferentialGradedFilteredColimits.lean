module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedForgetLimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleFilteredColimits

/-!
# Exactness of filtered colimits of differential graded modules

Let `R` be a sheaf of rings on a site `(C, J)` and let `A` be a sheaf of differential graded
`R`-algebras. Filtered colimits in the category of right differential graded `A`-modules are
exact, which is Grothendieck's axiom AB5 for that category.

## Main results

* `SheafOfModules.DifferentialGradedModule.filteredColimits_exact`: right differential graded
  modules satisfy AB5 at every size at which they have filtered colimits.

## Implementation notes

The general size is reduced to shapes small relative to the module universe by
`CategoryTheory.ab5OfSize_of_exactSmallFilteredColimits`, and in that case the statement is
transported from the graded case, `SheafOfModules.GradedModule.filteredColimits_exact`, along the
functor `SheafOfModules.forgetToGradedModule` that forgets the differential. That functor is both
a left and a right adjoint, so it preserves the colimits and the finite limits involved; it is
faithful because a morphism of differential graded modules is its underlying morphism of
complexes; and it reflects isomorphisms, because a morphism whose image is invertible is both a
monomorphism and an epimorphism, hence invertible in an abelian category. Those are exactly the
hypotheses of `CategoryTheory.HasExactColimitsOfShape.domain_of_functor`.

## References

* [Stacks Project, Tag 0FRJ](https://stacks.math.columbia.edu/tag/0FRJ)
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules.DifferentialGradedModule

universe s s' m' a t v u

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  [HasSheafify J AddCommGrpCat.{max u m'}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u m'}]

private theorem exactColimitsOnSmallFilteredShape (A : DifferentialGradedAlgebra.{t, a} R)
    (S : Type s') [Category.{max u m', s'} S] [IsFiltered S] [UnivLE.{s', max u m'}]
    [HasColimitsOfShape S (DifferentialGradedModule.{t, a, max u m'} A)] :
    HasExactColimitsOfShape S (DifferentialGradedModule.{t, a, max u m'} A) := by
  let DG := DifferentialGradedModule.{t, a, max u m'} A
  let GM := GradedModule.{t, a, max u m'} A.toGradedAlgebra
  let F : DG ⥤ GM := forgetToGradedModule.{t, a, max u m'} A
  let : Abelian DG := DifferentialGradedModule.abelian (A := A)
  let : HasFiniteLimits DG := inferInstance
  let : HasColimitsOfSize.{max u m', max u m'} GM := inferInstance
  let : HasFilteredColimitsOfSize.{max u m', s'} GM :=
    hasFilteredColimitsOfSize_of_univLE.{max u m', s', max u m', max u m'}
  let : AB5OfSize.{max u m', s'} GM :=
    GradedModule.filteredColimits_exact A.toGradedAlgebra
  let : PreservesColimitsOfSize.{max u m', max u m'} F := inferInstance
  let : PreservesColimitsOfSize.{max u m', s'} F :=
    preservesColimitsOfSize_of_univLE.{max u m', max u m', max u m', s'} F
  let : PreservesLimits F := inferInstance
  let : F.Faithful :=
    ⟨fun h => DifferentialGradedModule.Hom.ext (fun n => congrArg (fun f => f.app n) h)⟩
  let : F.ReflectsIsomorphisms := ⟨fun f hf => by
    let : IsIso (F.map f) := hf
    let : Mono f := Functor.mono_of_mono_map F inferInstance
    let : Epi f := Functor.epi_of_epi_map F inferInstance
    exact isIso_of_mono_of_epi f⟩
  exact HasExactColimitsOfShape.domain_of_functor S F

/-- **Filtered colimits of right differential graded modules over a sheaf of differential graded
algebras are exact**, at every size at which those colimits exist. -/
instance filteredColimits_exact (A : DifferentialGradedAlgebra.{t, a} R)
    [HasFilteredColimitsOfSize.{s, s'} (DifferentialGradedModule.{t, a, max u m'} A)] :
    AB5OfSize.{s, s'} (DifferentialGradedModule.{t, a, max u m'} A) :=
  have : Abelian (DifferentialGradedModule.{t, a, max u m'} A) :=
    DifferentialGradedModule.abelian (A := A)
  ab5OfSize_of_exactSmallFilteredColimits
    (fun K => exactColimitsOnSmallFilteredShape A K)

end

end SheafOfModules.DifferentialGradedModule

end
