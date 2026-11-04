module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerivedComparison.CechFunctorAtFourUniverses
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfSheavesOfModules.AugmentationIsAKernel

/-!
# The Čech complex of the covering of [Stacks, Tag 01ES] is the one of [Stacks, Tag 01EP]

For an open covering `𝒰` of `𝒰.U`, the Čech complex
`Stacks.Cohomology.CechSpectral.cechComplexFunctor` of [Stacks, Tag 01EJ], from which the Čech
double complex `K^{i,j}(ℱ) = Č^j(𝒰, I^i(ℱ))` of [Stacks, Tag 01ES] is built, and the Čech complex
`Stacks.Cohomology.CechSheaf.cechComplex` of [Stacks, Tag 01EP] are the same functor on sheaves
of modules: both are `CategoryTheory.cechComplexFunctor` of the family
`fun i ↦ Over.mk (homOfLE (𝒰.le i))` in the slice over `𝒰.U`, applied to the same presheaf of
modules on that slice. Consequently the positive-degree Čech cohomology of an injective sheaf of
modules vanishes for either presentation
(`Stacks.Cohomology.CechSheaf.isZero_cechComplex_homology_of_injective`).

## Main definitions

* `Stacks.Cohomology.CechSpectral.cechSheafComplexFunctor`: the Čech complex of a *sheaf* of
  `O`-modules, as a functor — the Čech complex functor of [Stacks, Tag 01EJ] precomposed with
  `SheafOfModules.forget`.

## Main results

* `Stacks.Cohomology.CechSpectral.cechSheafComplexFunctor_eq`: the two Čech complex functors are
  equal.
* `Stacks.Cohomology.CechSpectral.isZero_cechSheafComplex_homology_of_injective` and
  `Stacks.Cohomology.CechSpectral.cechSheafComplex_exactAt_of_injective`: the positive-degree Čech
  cohomology of an injective sheaf of modules vanishes.

## References

* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
* [Stacks Project, Tag 01EJ](https://stacks.math.columbia.edu/tag/01EJ)
* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
* [Stacks Project, Tag 01ES](https://stacks.math.columbia.edu/tag/01ES)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Stacks.Cohomology.CechSpectral

universe u r v w

variable {X : Type u} [TopologicalSpace X]
  (O : Sheaf (Opens.grothendieckTopology X) RingCat.{r})
  (𝒰 : CechExactFunctor.CechOpenCover.{u, w} (TopCat.of X))

/-- The open covered by `𝒰` is the supremum of the members of `𝒰`. -/
theorem covers' : 𝒰.U = ⨆ i, 𝒰.obj i := 𝒰.covers.symm

/-- **The Čech complex of a sheaf of `O`-modules**, as a functor: the Čech complex functor of
[Stacks, Tag 01EJ] applied to the underlying presheaf of modules. -/
def cechSheafComplexFunctor :
    SheafOfModules.{max u r v w} O ⥤
      CochainComplex (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U))) ℕ :=
  SheafOfModules.forget.{max u r v w} O ⋙ cechComplexFunctor.{u, r, v, w} O 𝒰

/-- **The two presentations of the module-valued Čech complex agree, as functors.** Both are
`CategoryTheory.cechComplexFunctor` of the same family in the slice over `𝒰.U`, applied to the
same presheaf of modules. -/
theorem cechSheafComplexFunctor_eq :
    cechSheafComplexFunctor.{u, r, v, w} O 𝒰 =
      CechSheaf.cechComplexFunctorOfCover 𝒰.U 𝒰.obj (covers' 𝒰) :=
  rfl

/-- The Čech complex of a sheaf of modules is the complex
`Stacks.Cohomology.CechSheaf.cechComplex` of [Stacks, Tag 01EP]. -/
theorem cechSheafComplexFunctor_obj (F : SheafOfModules.{max u r v w} O) :
    (cechSheafComplexFunctor.{u, r, v, w} O 𝒰).obj F =
      CechSheaf.cechComplex 𝒰.U 𝒰.obj (covers' 𝒰) F :=
  rfl

/-- **The positive-degree Čech cohomology of an injective sheaf of modules vanishes**
([Stacks, Tag 01EP]), for the Čech complex `cechSheafComplexFunctor`. -/
theorem isZero_cechSheafComplex_homology_of_injective
    (F : SheafOfModules.{max u r v w} O) [Injective F] (p : ℕ) (hp : 0 < p) :
    IsZero (((cechSheafComplexFunctor.{u, r, v, w} O 𝒰).obj F).homology p) :=
  CechSheaf.isZero_cechComplex_homology_of_injective 𝒰.U 𝒰.obj (covers' 𝒰) F p hp

/-- **The Čech complex of an injective sheaf of modules is exact in every positive degree.** -/
theorem cechSheafComplex_exactAt_of_injective
    (F : SheafOfModules.{max u r v w} O) [Injective F] (p : ℕ) (hp : 0 < p) :
    ((cechSheafComplexFunctor.{u, r, v, w} O 𝒰).obj F).ExactAt p :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ p).2
    (isZero_cechSheafComplex_homology_of_injective.{u, r, v, w} O 𝒰 F p hp)

end Stacks.Cohomology.CechSpectral

end
