module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalk
public import StacksFrontier.Homology.PseudoCoherent.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
# The stalk of a cohomology sheaf is the cohomology of the derived stalk

The stalk functor `Stacks.ModuleSkyscraper.modulesStalkFunctor X x` is exact, and
`AlgebraicGeometry.derivedStalkFunctor x` is the functor it induces on unbounded derived
categories. An exact functor commutes with the homology of the derived category
(`StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso`), so the stalk at `x` of the `n`-th
cohomology sheaf of `K` is the `n`-th cohomology of the derived stalk `K_x`.

The consequence this is wanted for: when `K_x` is a single module `M` in degree `0` — the shape
the Koszul description of [Stacks, Tag 0G0N] produces — the stalk of `H^0(K)` at `x` is `M`, and
in particular its annihilator is the annihilator of `M`.

## Main results

* `AlgebraicGeometry.derivedStalkCompHomologyIso`: the natural isomorphism
  `(−)_x ∘ H^n ≅ H^n ∘ (−)_x` between the stalk of a cohomology sheaf and the cohomology of the
  derived stalk.
* `AlgebraicGeometry.derivedStalkSingleIso`: the derived stalk of a module placed in degree `0`
  is its stalk, placed in degree `0`.
* `AlgebraicGeometry.modulesStalkZeroHomologyIsoOfDerivedStalkIsoSingle`: the stalk of `H^0(K)`
  at `x`, for `K` whose derived stalk at `x` is a module in degree `0`.
* `AlgebraicGeometry.annihilator_modulesStalk_zeroHomology_of_derivedStalk_iso_single`: the
  annihilator of that stalk is the annihilator of the module.

## Implementation notes

`StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso` was stated for exact functors between
module categories; the proof uses nothing of the module structure, so it is stated for exact
functors between abelian categories and applied here to the stalk functor, whose target is a
module category but whose source is a category of sheaves of modules.

`DerivedCategory.singleFunctorCompHomologyFunctorIso` identifies the `n`-th cohomology of an
object concentrated in degree `n` with that object.

## References

* [Stacks Project, Tag 0G0N](https://stacks.math.columbia.edu/tag/0G0N)
* [Stacks Project, Tag 0G0R](https://stacks.math.columbia.edu/tag/0G0R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (x : X) [HasDerivedCategory.{w} X.Modules]
  [HasDerivedCategory.{w} (ModuleCat.{u} (X.presheaf.stalk x))]

/-- **The stalk of a cohomology sheaf is the cohomology of the derived stalk.** -/
def derivedStalkCompHomologyIso (n : ℤ) :
    derivedStalkFunctor x ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} (X.presheaf.stalk x)) n ≅
      DerivedCategory.homologyFunctor X.Modules n ⋙
        Stacks.ModuleSkyscraper.modulesStalkFunctor X x :=
  StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso
    (Stacks.ModuleSkyscraper.modulesStalkFunctor X x) n

/-- **The derived stalk of a module placed in degree zero is its stalk, placed in degree zero.**
This is `CategoryTheory.Functor.mapDerivedCategorySingleFunctor` at the stalk functor; it is what
turns a hypothesis of the shape "`L i^* K` is the sheaf `Δ_{Y_s/k,*}𝒪_{Y_s}`" — a module, not a
complex — into a statement about the derived stalk that the Koszul machinery can read. -/
def derivedStalkSingleIso (F : X.Modules) :
    (derivedStalkFunctor x).obj ((DerivedCategory.singleFunctor X.Modules 0).obj F) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (X.presheaf.stalk x)) 0).obj
        ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj F) :=
  ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapDerivedCategorySingleFunctor 0).app F

/-- **The stalk of `H^0(K)` when the derived stalk of `K` is a module in degree zero.** -/
def modulesStalkZeroHomologyIsoOfDerivedStalkIsoSingle
    (K : DerivedCategory X.Modules) (M : ModuleCat.{u} (X.presheaf.stalk x))
    (e : (derivedStalkFunctor x).obj K ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (X.presheaf.stalk x)) 0).obj M) :
    (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj
        ((DerivedCategory.homologyFunctor X.Modules 0).obj K) ≅ M :=
  ((derivedStalkCompHomologyIso x 0).app K).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (X.presheaf.stalk x)) 0).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{u} (X.presheaf.stalk x)) 0).app M

/-- **The annihilator of the stalk of `H^0(K)`, when the derived stalk of `K` is a module in
degree zero, is the annihilator of that module.** -/
theorem annihilator_modulesStalk_zeroHomology_of_derivedStalk_iso_single
    (K : DerivedCategory X.Modules) (M : ModuleCat.{u} (X.presheaf.stalk x))
    (e : (derivedStalkFunctor x).obj K ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (X.presheaf.stalk x)) 0).obj M) :
    Module.annihilator (X.presheaf.stalk x)
        ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj
          ((DerivedCategory.homologyFunctor X.Modules 0).obj K)) =
      Module.annihilator (X.presheaf.stalk x) M :=
  (modulesStalkZeroHomologyIsoOfDerivedStalkIsoSingle x K M e).toLinearEquiv.annihilator_eq

end AlgebraicGeometry

end
