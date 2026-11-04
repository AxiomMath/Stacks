module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedModuleAbelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedDegreeLimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetRightAdjoint
public import StacksCore.Tactic.StacksAttribute

/-!
# The cohomology long exact sequence of differential graded modules

Let `R` be a sheaf of rings on a site and let `A` be a sheaf of differential graded
`R`-algebras. A short exact sequence of right differential graded `A`-modules has an underlying
short exact sequence of cochain complexes of sheaves of modules, and therefore induces the
cohomology long exact sequence. This file also records that forgetting the differential detects
exactness. That it computes kernels and cokernels (the comparison maps are isomorphisms) is
found by instance search, from `SheafOfModules.forgetToGradedModule_preservesLimitsOfSize` and
`SheafOfModules.forgetToGradedModule_preservesColimitsOfSize`.

## Main results

* `SheafOfModules.DifferentialGradedModule.exact_iff_forgetToGradedModule_exact`: a short
  complex of differential graded modules is exact exactly when its underlying short complex of
  graded modules is.
* `SheafOfModules.DifferentialGradedModule.toCochainComplex_shortExact`: a short exact sequence
  of differential graded modules has an underlying short exact sequence of cochain complexes.
* `SheafOfModules.DifferentialGradedModule.cohomologyExactAtFirst`,
  `...cohomologyExactAtMiddle` and `...cohomologyExactAtThird`: the three successive exactness
  positions of the resulting cohomology long exact sequence.

## Implementation notes

The connecting homomorphism is Mathlib's canonical
`CategoryTheory.ShortComplex.ShortExact.δ` of the underlying short exact sequence of complexes,
so no choice is made here and no comparison with another construction is needed. Exactness is
stated separately at each of the three cohomology sheaves; the first position uses the
connecting map out of the preceding degree, and the third the connecting map into the next one,
which is why those two are stated as explicit `ShortComplex.mk`s rather than as the image of a
homology functor.

The short exactness of the underlying sequence is proved degreewise, through
`HomologicalComplex.shortExact_of_degreewise_shortExact`. In degree `n` the relevant functor is
`forgetToGradedModule A ⋙ GradedModule.pieceFunctor A.toGradedAlgebra n`, which agrees with
`toCochainComplex A ⋙ HomologicalComplex.eval _ _ n` on the nose; it is additive and exact
because forgetting the differential is both a left and a right adjoint
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedForgetColimits.lean` and
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedForgetRightAdjoint.lean`), and taking a homogeneous component commutes with limits and
colimits (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedDegreeLimits.lean` and `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedModuleAbelian.lean`).

The forgetful functor is `SheafOfModules.toCochainComplex` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedForgetRightAdjoint.lean`, which forgets the
action of a differential graded module and keeps its complex; it is not redefined here. The
abelian structures on differential graded and on graded modules are
`SheafOfModules.DifferentialGradedModule.abelian` and
`SheafOfModules.GradedModule.abelian`.

Both `HasSheafify J AddCommGrpCat.{m}` and `J.WEqualsLocallyBijective AddCommGrpCat.{m}` are
hypotheses: over an arbitrary site they are what make `SheafOfModules.{m} R` abelian, and hence
what makes "short exact" meaningful for differential graded modules. The source states the
tagged results for a ringed site, where they come free from essential smallness, so nothing is weakened by
naming them.

The base is an arbitrary sheaf of rings on an arbitrary site rather than the structure sheaf of
a ringed site, and the universes of the site, the ring, the algebra pieces and the module pieces
are independent; a ringed site `X` is the case `R := X.ringSheaf`.

## References

* [Stacks Project, Tag 0FRK](https://stacks.math.columbia.edu/tag/0FRK)
* [Stacks Project, Tag 0FRJ](https://stacks.math.columbia.edu/tag/0FRJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t a m v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- Forgetting the action of a right differential graded module is additive: the preadditive
structure on differential graded modules is the degreewise one. -/
instance toCochainComplex_additive (A : DifferentialGradedAlgebra.{t, a} R) :
    (toCochainComplex.{t, a, m} A).Additive where
  map_add := rfl

namespace DifferentialGradedModule

/-- Forgetting the differential is faithful. -/
theorem forgetToGradedModule_faithful (A : DifferentialGradedAlgebra.{t, a} R) :
    (forgetToGradedModule.{t, a, m} A).Faithful :=
  ⟨fun {_ _} _ _ e => Hom.ext fun n => congrArg (fun k => k.app n) e⟩

variable [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  (A : DifferentialGradedAlgebra.{t, a} R)

/-- Passing to the underlying cochain complex commutes with colimits of the size of the module
universe: forgetting the differential is a left adjoint and taking a homogeneous component
commutes with colimits by Tag 0FR0. -/
theorem toCochainComplex_preservesColimitsOfSize :
    PreservesColimitsOfSize.{m, m} (toCochainComplex.{t, a, m} A) where
  preservesColimitsOfShape {K} _ := by
    refine HomologicalComplex.preservesColimitsOfShape_of_eval _ fun n => ?_
    have : PreservesColimitsOfShape K
        (GradedModule.pieceFunctor.{t, a, m} A.toGradedAlgebra n) :=
      (GradedModule.pieceFunctor_preservesColimitsOfSize' (A := A.toGradedAlgebra) n
        ).preservesColimitsOfShape
    exact comp_preservesColimitsOfShape (forgetToGradedModule.{t, a, m} A)
      (GradedModule.pieceFunctor A.toGradedAlgebra n)

section Exactness

/-- **A short complex of differential graded modules is exact exactly when its underlying short
complex of graded modules is exact.** -/
theorem exact_iff_forgetToGradedModule_exact
    (S : ShortComplex (DifferentialGradedModule.{t, a, m} A)) :
    S.Exact ↔ (S.map (forgetToGradedModule.{t, a, m} A)).Exact := by
  have := forgetToGradedModule_faithful.{t, a, m} A
  exact (S.exact_map_iff_of_faithful (forgetToGradedModule.{t, a, m} A)).symm

end Exactness

section LongExactSequence

/-- The degree-`n` component functor on differential graded modules: forget the differential,
then take the degree-`n` homogeneous piece. -/
private abbrev pieceComp (n : ℤ) :
    DifferentialGradedModule.{t, a, m} A ⥤ SheafOfModules.{m} R :=
  forgetToGradedModule.{t, a, m} A ⋙ GradedModule.pieceFunctor A.toGradedAlgebra n

/-- **A short exact sequence of differential graded modules has an underlying short exact
sequence of cochain complexes of sheaves of modules.** -/
@[stacks 0FRK "underlying short exact sequence"]
theorem toCochainComplex_shortExact
    (S : ShortComplex (DifferentialGradedModule.{t, a, m} A)) (hS : S.ShortExact) :
    (S.map (toCochainComplex.{t, a, m} A)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  show (S.map (pieceComp.{t, a, m} A n)).ShortExact
  have := (GradedModule.pieceFunctor_preservesLimitsOfSize.{t, a, m}
    (A := A.toGradedAlgebra) n).preservesFiniteLimits
  have := (GradedModule.pieceFunctor_preservesColimitsOfSize'.{t, a, m}
    (A := A.toGradedAlgebra) n).preservesFiniteColimits
  have : PreservesFiniteLimits (pieceComp.{t, a, m} A n) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (pieceComp.{t, a, m} A n) := comp_preservesFiniteColimits _ _
  exact hS.map_of_exact (pieceComp.{t, a, m} A n)

/-- Exactness of the cohomology sequence at the cohomology of the first module, including the
connecting map from the preceding degree. -/
@[stacks 0FRK "exactness at the first cohomology sheaf"]
theorem cohomologyExactAtFirst
    (S : ShortComplex (DifferentialGradedModule.{t, a, m} A)) (hS : S.ShortExact) (n : ℤ) :
    (ShortComplex.mk
      ((toCochainComplex_shortExact A S hS).δ (n - 1) n (by simp))
      (HomologicalComplex.homologyMap S.f.toHomologicalComplex n)
      ((toCochainComplex_shortExact A S hS).δ_comp (n - 1) n (by simp))).Exact :=
  (toCochainComplex_shortExact A S hS).homology_exact₁ (n - 1) n (by simp)

/-- Exactness of the cohomology sequence at the cohomology of the middle module. -/
@[stacks 0FRK "exactness at the middle cohomology sheaf"]
theorem cohomologyExactAtMiddle
    (S : ShortComplex (DifferentialGradedModule.{t, a, m} A)) (hS : S.ShortExact) (n : ℤ) :
    ((S.map (toCochainComplex.{t, a, m} A)).map
      (HomologicalComplex.homologyFunctor (SheafOfModules.{m} R) (ComplexShape.up ℤ) n)).Exact :=
  (toCochainComplex_shortExact A S hS).homology_exact₂ n

/-- Exactness of the cohomology sequence at the cohomology of the third module, before the
canonical connecting map to the next degree. -/
@[stacks 0FRK "exactness at the third cohomology sheaf"]
theorem cohomologyExactAtThird
    (S : ShortComplex (DifferentialGradedModule.{t, a, m} A)) (hS : S.ShortExact) (n : ℤ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap S.g.toHomologicalComplex n)
      ((toCochainComplex_shortExact A S hS).δ n (n + 1) (by simp))
      ((toCochainComplex_shortExact A S hS).comp_δ n (n + 1) (by simp))).Exact :=
  (toCochainComplex_shortExact A S hS).homology_exact₃ n (n + 1) (by simp)

end LongExactSequence

end DifferentialGradedModule

end SheafOfModules
