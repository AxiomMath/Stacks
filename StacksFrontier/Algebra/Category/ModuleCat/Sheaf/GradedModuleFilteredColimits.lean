module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedDegreeLimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleAbelian
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import StacksFrontier.CategoryTheory.Abelian.GrothendieckAxioms.AB5SizeReduction

/-!
# Exactness of filtered colimits of graded modules

Let `R` be a sheaf of rings on a site `(C, J)` and let `A` be a sheaf of graded `R`-algebras.
Filtered colimits in the category of right graded `A`-modules are exact, which is Grothendieck's
axiom AB5 for that category.

## Main results

* `SheafOfModules.GradedModule.filteredColimits_exact`: right graded modules satisfy AB5 at every
  size at which they have filtered colimits.
* `SheafOfModules.GradedModule.ab5OfSize`: the same with no size hypothesis, at the module
  universe `max u m'` of a site `C : Type u`, where those colimits are known to exist.

## Implementation notes

Mathlib spells exactness of filtered colimits `CategoryTheory.AB5OfSize`, whose implicit
hypothesis is the existence of those colimits; `filteredColimits_exact` therefore takes the
existence as an instance argument and asserts exactness at the same size. At the module universe
the graded modules have all colimits, so `ab5OfSize` discharges that argument and states Tag
0FR0's exactness assertion outright.

Only the case of a shape small relative to the module universe is proved here; the general size
is `CategoryTheory.ab5OfSize_of_exactSmallFilteredColimits`. In the small case exactness is
transported from abelian sheaves: the forgetful functor to `Sheaf J AddCommGrpCat` preserves
those colimits (Tag 03DB) and reflects monomorphisms, and taking a fixed homogeneous component
preserves both the colimits and the finite limits, so a monomorphism of diagrams has monomorphic
colimit degreewise, hence in the category of graded modules.

## References

* [Stacks Project, Tag 0FR0](https://stacks.math.columbia.edu/tag/0FR0)
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules.GradedModule

universe s s' m' a t v u

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  [HasSheafify J AddCommGrpCat.{max u m'}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u m'}]

/-- A functor preserving colimits of size `a` preserves those of any smaller shape. -/
private theorem preservesColimitsOfShape_of_univLE {C' D' : Type*} [Category C']
    [Category D'] (F : C' ⥤ D') (S : Type s') [Category.{a, s'} S] [UnivLE.{s', a}]
    [PreservesColimitsOfSize.{a, a} F] : PreservesColimitsOfShape S F := by
  have := preservesColimitsOfSize_of_univLE.{a, a, a, s'} F
  infer_instance

private theorem exactColimitsOnSmallFilteredShape (A : GradedAlgebra.{t, a} R)
    (S : Type s') [Category.{max u m', s'} S] [IsFiltered S] [UnivLE.{s', max u m'}]
    [HasColimitsOfShape S (GradedModule.{t, a, max u m'} A)] :
    HasExactColimitsOfShape S (GradedModule.{t, a, max u m'} A) := by
  let GM := GradedModule.{t, a, max u m'} A
  let D := SheafOfModules.{max u m'} R
  let : Abelian GM := GradedModule.abelian (A := A)
  let : HasFilteredColimitsOfSize.{max u m', max u m'} AddCommGrpCat.{max u m'} := inferInstance
  let : AB5OfSize.{max u m', max u m'} AddCommGrpCat.{max u m'} := inferInstance
  let : HasFilteredColimitsOfSize.{max u m', s'} AddCommGrpCat.{max u m'} :=
    hasFilteredColimitsOfSize_of_univLE.{max u m', s', max u m', max u m'}
  let : AB5OfSize.{max u m', s'} AddCommGrpCat.{max u m'} :=
    AB5OfSize_of_univLE.{max u m', s', max u m', max u m'} (C := AddCommGrpCat.{max u m'})
  let : HasColimitsOfShape S AddCommGrpCat.{max u m'} := inferInstance
  let : HasExactColimitsOfShape S AddCommGrpCat.{max u m'} := inferInstance
  let : HasColimitsOfShape S (Cᵒᵖ ⥤ AddCommGrpCat.{max u m'}) := inferInstance
  let : HasExactColimitsOfShape S (Cᵒᵖ ⥤ AddCommGrpCat.{max u m'}) := inferInstance
  let : HasColimitsOfShape S (Sheaf J AddCommGrpCat.{max u m'}) := inferInstance
  let : HasExactColimitsOfShape S (Sheaf J AddCommGrpCat.{max u m'}) := inferInstance
  let E := SheafOfModules.toSheaf.{max u m'} R
  let : HasColimitsOfShape S D := inferInstance
  let : PreservesColimitsOfShape S E := preservesColimitsOfShape_of_univLE.{s', max u m'} E S
  let : PreservesFiniteLimits E := inferInstance
  let : Functor.ReflectsMonomorphisms E :=
    CategoryTheory.Functor.reflectsMonomorphisms_of_faithful E
  let : Functor.PreservesMonomorphisms (colim (J := S) ⋙ E) :=
    Functor.PreservesMonomorphisms.of_iso
      (preservesColimitNatIso (J := S) (C := D)
        (D := Sheaf J AddCommGrpCat.{max u m'}) E).symm
  let : Functor.PreservesMonomorphisms (colim (J := S) (C := D)) :=
    CategoryTheory.Functor.preservesMonomorphisms_of_preserves_of_reflects
      (colim (J := S) (C := D)) E
  let : HasExactColimitsOfShape S D :=
    hasExactColimitsOfShape_of_preservesMono (C := D) S
  let : HasColimitsOfShape S GM := inferInstance
  let : HasFiniteLimits GM := inferInstance
  let : Functor.PreservesMonomorphisms (colim (J := S) (C := GM)) := by
    refine ⟨fun {F G} α hα => ?_⟩
    refine ⟨fun {Z} f g h => ?_⟩
    apply GradedModule.Hom.ext
    intro n
    let E := pieceFunctor.{t, a, max u m'} A n
    let : PreservesColimitsOfShape S E := preservesColimitsOfShape_of_univLE.{s', max u m'} E S
    let : PreservesLimits E := pieceFunctor_preservesLimits A n
    let : Functor.PreservesMonomorphisms E := inferInstance
    let W := (Functor.whiskeringRight S GM D).obj E
    let L := colim (J := S) (C := D)
    let : Functor.PreservesMonomorphisms W := inferInstance
    let : Functor.PreservesMonomorphisms L := inferInstance
    let : Functor.PreservesMonomorphisms (W ⋙ L) := inferInstance
    let : Functor.PreservesMonomorphisms (colim (J := S) (C := GM) ⋙ E) :=
      Functor.PreservesMonomorphisms.of_iso
        (preservesColimitNatIso (J := S) (C := GM) (D := D) E).symm
    let : Mono (((colim (J := S) (C := GM)).map α).app n) := by
      show Mono ((colim (J := S) (C := GM) ⋙ E).map α)
      let : Mono α := hα
      infer_instance
    apply (cancel_mono (((colim (J := S) (C := GM)).map α).app n)).1
    have hh := congrArg
      (fun γ : GradedModule.Hom Z (colim.obj G) => γ.app n) h
    change f.app n ≫ ((colim (J := S) (C := GM)).map α).app n =
      g.app n ≫ ((colim (J := S) (C := GM)).map α).app n at hh
    exact hh
  exact hasExactColimitsOfShape_of_preservesMono (C := GM) S

/-- **Filtered colimits of right graded modules over a sheaf of graded algebras are exact**, at
every size at which those colimits exist. -/
@[stacks 0FR0 "filtered_colimits_exact"]
instance filteredColimits_exact (A : GradedAlgebra.{t, a} R)
    [HasFilteredColimitsOfSize.{s, s'} (GradedModule.{t, a, max u m'} A)] :
    AB5OfSize.{s, s'} (GradedModule.{t, a, max u m'} A) :=
  have : Abelian (GradedModule.{t, a, max u m'} A) := GradedModule.abelian (A := A)
  ab5OfSize_of_exactSmallFilteredColimits
    (fun K => exactColimitsOnSmallFilteredShape A K)

/-- **Filtered colimits of right graded modules are exact**, unconditionally, at the module
universe `max u m'` of a site `C : Type u`.

The graded modules have all colimits of that size, so the size hypothesis of
`filteredColimits_exact` is discharged rather than assumed. -/
@[stacks 0FR0 "filtered_colimits_exact"]
theorem ab5OfSize (A : GradedAlgebra.{t, a} R) :
    AB5OfSize.{max u m', max u m'} (GradedModule.{t, a, max u m'} A) :=
  have : Abelian (GradedModule.{t, a, max u m'} A) := GradedModule.abelian (A := A)
  filteredColimits_exact A

end

end SheafOfModules.GradedModule

end
