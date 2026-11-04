module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseHigherDirectImageAcyclic
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBasePushforwardInjectiveAcyclic
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleSite
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardReduction
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 08EX at an affine étale chart of the target

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of algebraic spaces over a
scheme `S` contained in a big fppf site `B`, let `F` be a quasi-coherent `𝒪_X`-module and let
`V` be an **affine** étale chart of `Y`.  Stacks 08EX asserts

`H^q(V ×_Y X, F) = H^0(V, R^q f_*F)`

in every degree.  This file proves it at exactly those data, with nothing left over.

The isomorphism is `AlgebraicGeometry.Space.cohomologyChartIsoSectionsHigherDirectImage` with its
two named inputs supplied: `h072Z` (Stacks 072Z through part (3) of Stacks 0731) by
`AlgebraicGeometry.Space.acyclicPushforwardOfInjective_of_isAffineSpace`, and `hcoh` (Stacks 0720
together with Stacks 01XB on the small étale site) by
`AlgebraicGeometry.Space.acyclicHigherDirectImages_of_isAffineSpace_of_affineTarget`, both at the
base change `f' : V ×_Y X ⟶ V`, whose target is the affine algebraic space represented by `V`.
The `@[stacks 08EX]` attribute therefore sits here.

## Main results

* `AlgebraicGeometry.Space.isAffineSpace_chartBaseChangeTarget`: the algebraic space represented
  by an affine étale chart is an affine algebraic space.
* `AlgebraicGeometry.Space.cohomologyAffineChartIsoSectionsHigherDirectImage`: **Stacks 08EX**,
  at the source's own data and with no input left open.

## Implementation notes

*No restriction on the degree.*  The source states 08EX for `q ∈ ℤ`; the degree below runs over
`ℕ` in the injective-resolution convention `CategoryTheory.Functor.rightDerived`, in which the
negative degrees are zero on both sides.

*The local priority raise* of `SheafOfModules.instAbelian` is the one carried throughout this
area of the library: instance search for `CategoryTheory.Abelian` on the modules at module
universe `u` otherwise commits to the module-universe-`max u v r w` instances in the import
closure and then fails on the universe constraint.

## References

* [Stacks Project, Lemma 50.6.3 (Tag 08EX)](https://stacks.math.columbia.edu/tag/08EX)
* [Stacks Project, Tag 0720](https://stacks.math.columbia.edu/tag/0720)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 072Z](https://stacks.math.columbia.edu/tag/072Z)
* [Stacks Project, Tag 0731](https://stacks.math.columbia.edu/tag/0731)
* [Stacks Project, Tag 03HF](https://stacks.math.columbia.edu/tag/03HF)
* [Stacks Project, Tag 03KL](https://stacks.math.columbia.edu/tag/03KL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

noncomputable section

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **The algebraic space represented by an affine étale chart is affine.** -/
theorem isAffineSpace_chartBaseChangeTarget (V : SmallEtale B S hS Y.1)
    (hV : IsAffineChart B S hS Y.1 V) :
    IsAffineSpace B S hS (chartBaseChangeTarget B S hS V).1 :=
  isAffineSpace_yoneda B S hS ((SmallEtale.toOver B S hS Y.1).obj V) hV

/-- **Stacks 08EX.** Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of
algebraic spaces over `S`, let `F` be a quasi-coherent `𝒪_X`-module and let `V` be an affine
étale chart of `Y`.  Then the cohomology of `F` over `U = V ×_Y X` agrees with the module of
sections over `V` of the degree-`q` higher direct image `R^q f_*F`, in every degree:

`H^q(V ×_Y X, F) = H^0(V, R^q f_*F)`. -/
@[stacks 08EX "the source's statement and both steps of its proof at the source's own data: f
quasi-compact and quasi-separated, F quasi-coherent, V an affine object of Y_etale. The
cohomology over V times_Y X is read as the right derived functor of the composite
Gamma(V, f'_* -), as in the library's form of Stacks 0D2U"]
def cohomologyAffineChartIsoSectionsHigherDirectImage (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (V : SmallEtale B S hS Y.1) (hV : IsAffineChart B S hS Y.1 V) (q : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    have := hasInjectiveResolutions_modules B S hS (chartBaseChangeSpace B S hS f V).1
      (chartBaseChangeSpace B S hS f V).2
    have := enoughInjectives_modules B S hS (chartBaseChangeTarget B S hS V).1
      (chartBaseChangeTarget B S hS V).2
    ((modulePushforward B S hS (chartBaseChangeProjection B S hS f V) ⋙
            globalSectionsFunctor.{u + 1, u, u, u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
                (chartBaseChangeTarget B S hS V).1
                (chartBaseChangeTarget B S hS V).2).O))).rightDerived q).obj
        ((chartBaseChangeModulePullback B S hS f V).obj F) ≅
      (globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
            (chartBaseChangeTarget B S hS V).1
            (chartBaseChangeTarget B S hS V).2).O))).obj
        ((etaleModulePullback B S hS (chartToSpace B S hS Y V)
            (isEtale_chartToSpace B S hS Y V)).obj
          (((modulePushforward B S hS f).rightDerived q).obj F)) :=
  haveI : ((chartBaseChangeModulePullback B S hS f V).obj F).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_etaleModulePullback B S hS (chartBaseChangeInclusion B S hS f V)
      (isEtale_chartBaseChangeInclusion B S hS f V) F hF
  cohomologyChartIsoSectionsHigherDirectImage B S hS f F V q
    (preservesInjectiveObjects_etaleModulePullback B S hS
      (chartBaseChangeInclusion B S hS f V) (isEtale_chartBaseChangeInclusion B S hS f V))
    (acyclicPushforwardOfInjective_of_isAffineSpace B S hS
      (chartBaseChangeProjection B S hS f V)
      (isAffineSpace_chartBaseChangeTarget B S hS V hV))
    (acyclicHigherDirectImages_of_isAffineSpace_of_affineTarget B S hS
      (chartBaseChangeProjection B S hS f V)
      (isAffineSpace_chartBaseChangeTarget B S hS V hV)
      (isQuasiCompact_chartBaseChangeProjection B S hS f V hfqc)
      (isQuasiSeparated_chartBaseChangeProjection B S hS f V hfqs)
      ((chartBaseChangeModulePullback B S hS f V).obj F))

end AlgebraicGeometry.Space

end

end
