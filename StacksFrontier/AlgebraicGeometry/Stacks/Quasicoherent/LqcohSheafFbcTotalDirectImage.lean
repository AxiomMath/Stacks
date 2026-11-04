module

public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonIso
public import StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitHelpers
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusComparisons
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyComparison.Basic
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LqcohSheafFbcFppfHigherDirectImage
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# The total direct image of `LQCoh^fbc` in the fppf and the étale topology (Stacks 0771 (4)(a))

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks and `F` an object of
`LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)`. **Stacks 0771** part (4)(a) says that the total direct image `Rf_*F`
can be computed in either the étale or the fppf topology with the same result. The two results
live in different derived categories, and `ε_* : Mod(𝒪_𝒴) ⥤ Mod(𝒴_ét, 𝒪_𝒴)` is only left exact,
so the fppf result is read on the étale site through `Rε_*`:

`Rf_{ét,*}(ε_*F) ≅ Rε_*(Rf_{fppf,*}F)` in `D⁺(Mod(𝒴_ét, 𝒪_𝒴))`.

The total direct images are Mathlib's `CategoryTheory.Functor.rightDerivedFunctorPlus` of the
direct images `AlgebraicGeometry.Stack.stackModuleDirectImage` at the module universe of the
schemes, where the categories of modules have enough injectives
(`AlgebraicGeometry.Stack.enoughInjectives_moduleRingSheaf`).

## Main results

* `AlgebraicGeometry.Stack.totalDirectImageEtaleComparisonIso`:
  `Rε_* ∘ Rf_{fppf,*} ≅ Rf_{ét,*} ∘ Rε_*`, for every module.
* `AlgebraicGeometry.Stack.lqcohSheafFbcTotalDirectImageIso`: **Stacks 0771** part (4)(a) for the
  total direct image.
* `AlgebraicGeometry.Stack.nonempty_homology_totalDirectImage_etale_iso` and
  `AlgebraicGeometry.Stack.nonempty_homology_etaleComparison_totalDirectImage_iso`: for `f`
  quasi-compact and quasi-separated, the cohomology sheaves of both sides are `ε_*Rⁱf_{fppf,*}F`.

## Implementation notes

The statements hold for any choice of derived categories: each of `D(Mod(𝒪_𝒳))`,
`D(Mod(𝒳_ét, 𝒪_𝒳))`, `D(Mod(𝒪_𝒴))` and `D(Mod(𝒴_ét, 𝒪_𝒴))` is given by an arbitrary
`HasDerivedCategory` instance, with its own universe.

## References

* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 075R](https://stacks.math.columbia.edu/tag/075R)
* [Stacks Project, Tag 06WX](https://stacks.math.columbia.edu/tag/06WX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u t d₁ d₂ d₃ d₄

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] enoughInjectives_moduleRingSheaf
attribute [local instance high] abelianStackModules

/-- The direct image of modules along a 1-morphism of algebraic stacks preserves injective objects
(**Stacks 06WX** part (2)): it is right adjoint to the inverse image, which is left exact. -/
instance preservesInjectiveObjects_stackModuleDirectImage {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS}
    (f : 𝒳 ⟶ 𝒴) (τ : SiteKind) : (stackModuleDirectImage B S hS f τ).PreservesInjectiveObjects :=
  preservesInjectiveObjects_of_adjunction_sheafOfModules_pushforward B S hS 𝒳.val.val.p
    𝒴.val.val.p (CatFiberedInGroupoids.homFunctor f.hom) (B.baseTopology τ)
    𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor_comp_p f.hom) (B.baseTopology_le_topology τ) _
    (stackModuleInverseDirectImageAdjunction B S hS f τ)

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS}
  [HasDerivedCategory.{d₁} (StackModules B S hS .fppf 𝒳)]
  [HasDerivedCategory.{d₂} (StackModules B S hS .etale 𝒳)]
  [HasDerivedCategory.{d₃} (StackModules B S hS .fppf 𝒴)]
  [HasDerivedCategory.{d₄} (StackModules B S hS .etale 𝒴)]

/-- **The fppf and étale total direct images, compared through `Rε_*`.** For a 1-morphism
`f : 𝒳 ⟶ 𝒴` of algebraic stacks, `Rε_* ∘ Rf_{fppf,*} ≅ Rf_{ét,*} ∘ Rε_*` as functors
`D⁺(Mod(𝒪_𝒳)) ⥤ D⁺(Mod(𝒴_ét, 𝒪_𝒴))`. Both sides are the right derived functor of
`ε_* ∘ f_{fppf,*} ≅ f_{ét,*} ∘ ε_*`
(`AlgebraicGeometry.Stack.stackModulesDirectImageEtaleComparisonIso`), since `f_{fppf,*}` and
`ε_*` preserve injective objects (`CategoryTheory.Functor.rightDerivedFunctorPlusCompIso`). -/
noncomputable def totalDirectImageEtaleComparisonIso (f : 𝒳 ⟶ 𝒴) :
    (stackModuleDirectImage B S hS f .fppf).rightDerivedFunctorPlus ⋙
        (stackModulesEtaleComparison B S hS 𝒴).rightDerivedFunctorPlus ≅
      (stackModulesEtaleComparison B S hS 𝒳).rightDerivedFunctorPlus ⋙
        (stackModuleDirectImage B S hS f .etale).rightDerivedFunctorPlus :=
  (Functor.rightDerivedFunctorPlusCompIso _ _).symm ≪≫
    Functor.rightDerivedFunctorPlusNatIso (stackModulesDirectImageEtaleComparisonIso B S hS f) ≪≫
    Functor.rightDerivedFunctorPlusCompIso _ _

/-- **Stacks 0771, part (4)(a), for the total direct image.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
algebraic stacks and `F` an object of `LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)`. The total direct image of `F`
computed in the étale topology is the one computed in the fppf topology, read on the étale site:
`Rf_{ét,*}(ε_*F) ≅ Rε_*(Rf_{fppf,*}F)` in `D⁺(Mod(𝒴_ét, 𝒪_𝒴))`.

Here `ε_* : Mod(𝒪_𝒴) ⥤ Mod(𝒴_ét, 𝒪_𝒴)` is only left exact, so the fppf result is compared through
its right derived functor `Rε_*`. The isomorphism is
`AlgebraicGeometry.Stack.totalDirectImageEtaleComparisonIso` together with `Rε_*F ≅ ε_*F`, which
is **Stacks 075R** (1),
`AlgebraicGeometry.Stack.isZero_rightDerived_etaleComparisonPushforward_of_lqcohSheafFbc`.
No quasi-compactness or quasi-separatedness of `f` is needed for this form. When `f` is
quasi-compact and quasi-separated, part (4)(b) and **Stacks 075R** (1) make the cohomology
sheaves `Rⁱf_{fppf,*}F` of `Rf_{fppf,*}F` themselves `ε_*`-acyclic, so that `Rε_*` there is
`ε_*` applied to the cohomology sheaves: that is the form of part (4)(a) for the higher direct
images, `AlgebraicGeometry.Stack.nonempty_etaleComparison_fppfModulesHigherDirectImage_iso`, and
`AlgebraicGeometry.Stack.nonempty_homology_etaleComparison_totalDirectImage_iso` below. -/
@[stacks 0771 "part (4)(a), total direct image Rf_*: Rf_{ét,*}(ε_*F) ≅ Rε_*(Rf_{fppf,*}F) in \
  D⁺(𝒴_ét), for F in LQCoh^fbc and every 1-morphism f, modules at the module universe u of the \
  schemes"]
noncomputable def lqcohSheafFbcTotalDirectImageIso (f : 𝒳 ⟶ 𝒴) (F : StackModules B S hS .fppf 𝒳)
    (hF : lqcohSheafFbcFppfModules.{u, t, u} B E h S hS 𝒳 F) :
    (stackModuleDirectImage B S hS f .etale).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((stackModulesEtaleComparison B S hS 𝒳).obj F)) ≅
      (stackModulesEtaleComparison B S hS 𝒴).rightDerivedFunctorPlus.obj
        ((stackModuleDirectImage B S hS f .fppf).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) :=
  have hac : (stackModulesEtaleComparison B S hS 𝒳).rightAcyclic F :=
    (Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat _ F).2 fun n hn =>
      isZero_rightDerived_etaleComparisonPushforward_of_lqcohSheafFbc B S hS E h 𝒳 F hF n hn
  (stackModuleDirectImage B S hS f .etale).rightDerivedFunctorPlus.mapIso
      (Stacks.Cohomology.AffineComparison.rightDerivedFunctorPlusObjSingleIso _ F hac).symm ≪≫
    ((totalDirectImageEtaleComparisonIso B S hS f).app _).symm

omit [HasDerivedCategory.{d₁} (StackModules B S hS .fppf 𝒳)]
  [HasDerivedCategory.{d₃} (StackModules B S hS .fppf 𝒴)] in
/-- For `f` quasi-compact and quasi-separated and `F` in `LQCoh^fbc(𝒪_𝒳)`, the `i`-th cohomology
sheaf of `Rf_{ét,*}(ε_*F)` is `ε_*Rⁱf_{fppf,*}F`. -/
theorem nonempty_homology_totalDirectImage_etale_iso (f : 𝒳 ⟶ 𝒴)
    (hqc : IsQuasiCompactMorphism B S hS f) (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f)
    (F : StackModules B S hS .fppf 𝒳) (hF : lqcohSheafFbcFppfModules.{u, t, u} B E h S hS 𝒳 F)
    (i : ℕ) :
    Nonempty ((DerivedCategory.Plus.homologyFunctor _ (i : ℤ)).obj
        ((stackModuleDirectImage B S hS f .etale).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((stackModulesEtaleComparison B S hS 𝒳).obj F))) ≅
      (stackModulesEtaleComparison B S hS 𝒴).obj
        ((stackModuleHigherDirectImage B S hS f .fppf i).obj F)) := by
  obtain ⟨e⟩ := nonempty_etaleComparison_fppfModulesHigherDirectImage_iso B E h S hS f hqc hqs F
    hF i
  exact ⟨rightDerivedPlusObjIso (stackModuleDirectImage B S hS f .etale)
    ((stackModulesEtaleComparison B S hS 𝒳).obj F) i ≪≫ e.symm⟩

omit [HasDerivedCategory.{d₂} (StackModules B S hS .etale 𝒳)] in
/-- For `f` quasi-compact and quasi-separated and `F` in `LQCoh^fbc(𝒪_𝒳)`, the `i`-th cohomology
sheaf of `Rε_*(Rf_{fppf,*}F)` is `ε_*Rⁱf_{fppf,*}F`. -/
theorem nonempty_homology_etaleComparison_totalDirectImage_iso (f : 𝒳 ⟶ 𝒴)
    (hqc : IsQuasiCompactMorphism B S hS f) (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f)
    (F : StackModules B S hS .fppf 𝒳) (hF : lqcohSheafFbcFppfModules.{u, t, u} B E h S hS 𝒳 F)
    (i : ℕ) :
    Nonempty ((DerivedCategory.Plus.homologyFunctor _ (i : ℤ)).obj
        ((stackModulesEtaleComparison B S hS 𝒴).rightDerivedFunctorPlus.obj
          ((stackModuleDirectImage B S hS f .fppf).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) ≅
      (stackModulesEtaleComparison B S hS 𝒴).obj
        ((stackModuleHigherDirectImage B S hS f .fppf i).obj F)) := by
  let := HasDerivedCategory.standard (StackModules B S hS .etale 𝒳)
  obtain ⟨e⟩ := nonempty_homology_totalDirectImage_etale_iso B E h S hS f hqc hqs F hF i
  exact ⟨(DerivedCategory.Plus.homologyFunctor _ (i : ℤ)).mapIso
    (lqcohSheafFbcTotalDirectImageIso B E h S hS f F hF).symm ≪≫ e⟩

end AlgebraicGeometry.Stack

end
