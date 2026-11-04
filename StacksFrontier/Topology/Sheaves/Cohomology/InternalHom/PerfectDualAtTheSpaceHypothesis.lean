module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.LeftDualOnARingedSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectBidual
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDual
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualGlobalSections
public import
  StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RingedSitePerfectnessFromTheSpace
import StacksCore.Tactic.StacksAttribute

/-!
# Duals of perfect objects on a ringed space

Let `(X, O_X)` be a ringed space and let `K` be a perfect object of `D(O_X)`, in the ringed-space
sense `Stacks.Cohomology.PerfectComplexes.IsPerfect` of [Stacks, Tag 08CM]. Then the dual
`K^∨ = RSheafHom(K, O_X)` is perfect; `(K^∨)^∨ ≅ K`; `M ⊗^L_{O_X} K^∨ ≅ RSheafHom(K, M)` for
every `M`; and `H⁰(X, M ⊗^L_{O_X} K^∨) = Hom_{D(O_X)}(K, M)`.

These are deduced from the same assertions for `AlgebraicGeometry.RingedSite.IsPerfect` at the
site of opens, the notion of [Stacks, Tag 08G5], through
`Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect`.

## Main results

* `Stacks.SheafOfModules.isPerfect_derivedDual_of_isPerfectSpace`: the dual of a perfect object
  is perfect.
* `Stacks.SheafOfModules.isIso_derivedBidualMap_of_isPerfectSpace` and
  `Stacks.SheafOfModules.derivedBidualIsoOfIsPerfectSpace`: a perfect object is isomorphic to its
  bidual.
* `Stacks.SheafOfModules.isIso_derivedTensorDualToSheafHom_of_isPerfectSpace`:
  `M ⊗^L_{O_X} K^∨ ≅ RSheafHom(K, M)`.
* `Stacks.SheafOfModules.bijective_derivedTensorDualGlobalSectionsMap_of_isPerfectSpace` and
  `Stacks.SheafOfModules.derivedTensorDualGlobalSectionsAddEquivOfIsPerfectSpace`:
  `H⁰(X, M ⊗^L_{O_X} K^∨) = Hom_{D(O_X)}(K, M)`.

## References

* [Stacks Project, Lemma 20.50.5 (Tag 08DQ)](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Definition 20.46.4 (Tag 08CM)](https://stacks.math.columbia.edu/tag/08CM)
* [Stacks Project, Definition 20.48.1 (Tag 08G5)](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 08I1](https://stacks.math.columbia.edu/tag/08I1)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open StrictlyPerfect
open Stacks.Cohomology.ModuleSections

universe u

namespace Stacks.SheafOfModules

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

variable (X : RingedSpace.{u, u}) (K M : DerivedCategory (OXMod.{u, u} X))

/-- Let `(X, O_X)` be a ringed space and let `K` be a perfect object of `D(O_X)` in the sense of
[Stacks, Tag 08CM]. Then the dual `K^∨ = RSheafHom(K, O_X)` is perfect in that same sense. -/
@[stacks 08DQ "the first assertion with perfectness in the RINGED-SPACE reading of Tag 08CM on \
both sides, rather than the site reading of Tag 08G5 that \
`Stacks.SheafOfModules.isPerfect_derivedDual` uses; the two are equivalent by \
`Stacks.Cohomology.PerfectComplexes.isPerfect_of_ringedSite` and \
`Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect`"]
theorem isPerfect_derivedDual_of_isPerfectSpace
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X) K) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X) (derivedDual X.sheaf K) :=
  Stacks.Cohomology.PerfectComplexes.isPerfect_of_ringedSite X _
    (isPerfect_derivedDual X.sheaf K
      (Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect X K hK))

/-- For a perfect object `K` of `D(O_X)` in the sense of [Stacks, Tag 08CM] the canonical map
`K ⟶ (K^∨)^∨` of `Stacks.SheafOfModules.derivedBidualMap` is an isomorphism. -/
@[stacks 08DQ "the second assertion with perfectness in the RINGED-SPACE reading of Tag 08CM \
rather than the site reading of Tag 08G5 that `Stacks.SheafOfModules.isIso_derivedBidualMap` \
uses", sga "6 I 7.2" "special case"]
theorem isIso_derivedBidualMap_of_isPerfectSpace
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X) K) :
    IsIso (derivedBidualMap X.sheaf K) :=
  isIso_derivedBidualMap X.sheaf K
    (Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect X K hK)

/-- For a perfect object `K` of `D(O_X)` in the sense of [Stacks, Tag 08CM], the isomorphism
`K ≅ (K^∨)^∨`. -/
@[stacks 08DQ "the second assertion as an isomorphism, with perfectness in the RINGED-SPACE \
reading of Tag 08CM rather than the site reading of Tag 08G5 that \
`Stacks.SheafOfModules.derivedBidualIso` uses"]
def derivedBidualIsoOfIsPerfectSpace
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X) K) :
    K ≅ derivedDual X.sheaf (derivedDual X.sheaf K) :=
  derivedBidualIso X.sheaf K
    (Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect X K hK)

/-- For a perfect object `K` of `D(O_X)` in the sense of [Stacks, Tag 08CM] and any object `M`, the
canonical map of [Stacks, Tag 08I1]

`M ⊗^L_{O_X} K^∨ ⟶ RSheafHom(K, M)`

is an isomorphism. -/
@[stacks 08DQ "the third assertion with perfectness in the RINGED-SPACE reading of Tag 08CM \
rather than the site reading of Tag 08G5 that \
`Stacks.SheafOfModules.isIso_derivedTensorDualToSheafHom_of_isPerfect` uses"]
theorem isIso_derivedTensorDualToSheafHom_of_isPerfectSpace
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X) K) :
    IsIso (derivedTensorDualToSheafHom X.sheaf K M) :=
  isIso_derivedTensorDualToSheafHom_of_isPerfect X.sheaf K M
    (Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect X K hK)

/-- For a perfect object `K` of `D(O_X)` in the sense of [Stacks, Tag 08CM] and any object `M`, the
canonical map of [Stacks, Tag 08I1] on degree-zero global hypercohomology

`H⁰(X, M ⊗^L_{O_X} K^∨) ⟶ Hom_{D(O_X)}(K, M)`

is bijective. -/
@[stacks 08DQ "the fourth assertion with perfectness in the RINGED-SPACE reading of Tag 08CM \
rather than the site reading of Tag 08G5 that \
`Stacks.SheafOfModules.bijective_derivedTensorDualGlobalSectionsMap_of_isPerfect` uses"]
theorem bijective_derivedTensorDualGlobalSectionsMap_of_isPerfectSpace
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X) K) :
    Function.Bijective (derivedTensorDualGlobalSectionsMap X.sheaf K M) :=
  bijective_derivedTensorDualGlobalSectionsMap_of_isPerfect X.sheaf K M
    (Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect X K hK)

/-- For a perfect object `K` of `D(O_X)` in the sense of [Stacks, Tag 08CM] and any object `M`,
`H⁰(X, M ⊗^L_{O_X} K^∨) = Hom_{D(O_X)}(K, M)` as abelian groups, the identification being the
canonical map of [Stacks, Tag 08I1]. -/
@[stacks 08DQ "the fourth assertion as an isomorphism of abelian groups, with perfectness in the \
RINGED-SPACE reading of Tag 08CM rather than the site reading of Tag 08G5 that \
`Stacks.SheafOfModules.derivedTensorDualGlobalSectionsAddEquiv` uses; functoriality in `M` is \
`Stacks.SheafOfModules.derivedTensorDualSections_naturality` together with \
`AlgebraicGeometry.RingedSite.derivedTensorDualGlobalSectionsMap_naturality`"]
def derivedTensorDualGlobalSectionsAddEquivOfIsPerfectSpace
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X) K) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
        ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj
          (((derivedTensor X.sheaf).obj M).obj (derivedDual X.sheaf K))) : Type u) ≃+ (K ⟶ M) :=
  derivedTensorDualGlobalSectionsAddEquiv X.sheaf K M
    (Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect X K hK)

end Stacks.SheafOfModules

end
