module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualTensorHom
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDual

/-!
# `H⁰(X, M ⊗^L K^∨) = Hom_{D(O_X)}(K, M)` for a perfect `K`

Let `(X, O_X)` be a ringed space, let `K` be a **perfect** object of `D(O_X)` and let `M` be an
arbitrary object. The fourth assertion of **Stacks 08DQ** is that the canonical map of
Stacks 08I1 on degree-zero global hypercohomology,

`H⁰(X, M ⊗^L_{O_X} K^∨) ⟶ Hom_{D(O_X)}(K, M)`

(`Stacks.SheafOfModules.derivedTensorDualGlobalSectionsMap`), is an isomorphism of abelian
groups. That is what this file proves, with perfectness of `K` as the only hypothesis; nothing is
assumed of `M`.

## Main results

* `Stacks.SheafOfModules.bijective_derivedTensorDualGlobalSectionsMap_of_isPerfect`:
  **Stacks 08DQ, fourth assertion**, as bijectivity of the canonical map.
* `Stacks.SheafOfModules.derivedTensorDualGlobalSectionsAddEquiv`: **Stacks 08DQ, fourth
  assertion**, as the resulting isomorphism of abelian groups
  `H⁰(X, M ⊗^L_{O_X} K^∨) ≃+ Hom_{D(O_X)}(K, M)` — the source's `=`.

## How it is proved

This is the step the source performs with Stacks 08I1: the fourth assertion reduces to the third
one, and the reduction is already in the library, conditionally.

`Stacks.SheafOfModules.derivedTensorDualGlobalSectionsMap` is by construction (its pinning lemma
`Stacks.SheafOfModules.derivedTensorDualGlobalSectionsMap_apply`) the composite of two maps: the
degree-zero global hypercohomology of the canonical map

`Φ : M ⊗^L_{O_X} K^∨ ⟶ RSheafHom(K, M)`

of Stacks 08I1, and the identification
`H⁰(X, RSheafHom(K, M)) ≅ Hom_{D(O_X)}(K, M)` of Stacks 08DK
(`Stacks.SheafOfModules.derivedSheafHomGlobalSectionsEquiv`). The second factor is an
isomorphism unconditionally. The first factor is an isomorphism exactly when `Φ` is, both
`Stacks.SheafOfModules.derivedModuleGlobalSections` and
`CategoryTheory.DerivedCategory.homologyFunctor` being functors.

So the assertion is **equivalent to the third assertion of the tag**, and it genuinely consumes
it: the input is

`Stacks.SheafOfModules.isIso_derivedTensorDualToSheafHom_of_isPerfect` of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualTensorHom`,

that `Φ` is invertible for a perfect `K`. There is no route to the fourth assertion that avoids
it — the source takes the same one, saying "By Lemma 08I1 to see the final statement it suffices
to check that the map (08I2) is an isomorphism".

The first half of the reduction is
`Stacks.SheafOfModules.bijective_derivedTensorDualGlobalSectionsMap` of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDual`, at a general
`X : TopCat.{u}`, matching the universe of the third assertion.

## Functoriality in `M`: not claimed here, but available

Stacks 08DQ calls the isomorphisms of its third and fourth assertions *functorial* in `M`. For
the third assertion that clause is available
(`Stacks.SheafOfModules.derivedTensorDualToSheafHom_naturality`); the statements below do not
claim it for the map of this file, but it **is** in the library. Functoriality of the canonical map on degree-zero global hypercohomology is
`Stacks.SheafOfModules.derivedTensorDualSections_naturality`; the compatibility of the
identification of Stacks 08DK with postcomposition in `M` is
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality_target` (Tag 08JA),
which is precisely the covariant companion of
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality_source`; and the two are assembled as
`AlgebraicGeometry.RingedSite.derivedTensorDualGlobalSectionsMap_naturality`, all three in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsTargetNaturality`. The
0A94 naturality they rest on is
`AlgebraicGeometry.RingedSite.sheafHomGlobalHomologyEquivDerivedCategoryHom_naturality`, in both
variables, off `AlgebraicGeometry.RingedSite.globalSectionsIso_homMap`.

The site-level counterpart of the *bijectivity* proved below — which is what Stacks 09JC
consumes — is
`AlgebraicGeometry.RingedSite.bijective_derivedTensorDualGlobalSectionsMap_of_isPerfect` in
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualSiteGlobalSections`, together
with the natural additive bijection `Hom(L, N) ≃+ Hom(O, N ⊗^L_O L^∨)` it supports. The
statements below are the special case of it at `ringedSite Rc`, reproved directly; they are kept
because they carry the Tag 08DQ registrations.

## References

* [Stacks Project, Lemma 20.50.5 (Tag 08DQ)](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08I1](https://stacks.math.columbia.edu/tag/08I1)
* [Stacks Project, Tag 08DK](https://stacks.math.columbia.edu/tag/08DK)
* [Stacks Project, Definition 20.48.1 (Tag 08G5)](https://stacks.math.columbia.edu/tag/08G5)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.Cohomology.ModuleSections

universe u

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

variable [∀ V : Opens X, HasSheafify ((Opens.grothendieckTopology X).over V) AddCommGrpCat.{u}]
  [∀ V : Opens X, ((Opens.grothendieckTopology X).over V).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [∀ V : Opens X, HasWeakSheafify ((Opens.grothendieckTopology X).over V) AddCommGrpCat.{u}]

/-- **Stacks 08DQ, fourth assertion.** Let `(X, O_X)` be a ringed space, let `K` be a perfect
object of `D(O_X)` and let `M` be any object. The canonical map of Stacks 08I1 on degree-zero
global hypercohomology

`H⁰(X, M ⊗^L_{O_X} K^∨) ⟶ Hom_{D(O_X)}(K, M)`

is bijective.

Perfectness of `K` is in the site-level reading of Stacks 08G5, and `M` is arbitrary. The proof is
the source's: by Stacks 08I1 the assertion reduces to invertibility of the canonical map
`M ⊗^L_{O_X} K^∨ ⟶ RSheafHom(K, M)`, which is the third assertion of the tag,
`isIso_derivedTensorDualToSheafHom_of_isPerfect`. -/
@[stacks 08DQ "the fourth assertion: the canonical map \
`H⁰(X, M ⊗^L K^∨) ⟶ Hom_{D(O_X)}(K, M)` of Stacks 08I1 is bijective for a perfect `K`"]
theorem bijective_derivedTensorDualGlobalSectionsMap_of_isPerfect
    (K M : DerivedCategory (StructureSheafModules Rc))
    (hK : (ringedSite Rc).IsPerfect K) :
    Function.Bijective (derivedTensorDualGlobalSectionsMap Rc K M) :=
  Stacks.SheafOfModules.bijective_derivedTensorDualGlobalSectionsMap Rc K M
    (isIso_derivedTensorDualToSheafHom_of_isPerfect Rc K M hK)

/-- **Stacks 08DQ, fourth assertion**, in the equality form the source states it in: for a
perfect object `K` of `D(O_X)` and any object `M`,

`H⁰(X, M ⊗^L_{O_X} K^∨) = Hom_{D(O_X)}(K, M)`

as abelian groups, the identification being the canonical map of Stacks 08I1.

Functoriality of this identification in `M` is *not* claimed; see the section "What is still
missing" of this file. -/
@[stacks 08DQ "the fourth assertion: `H⁰(X, M ⊗^L K^∨) = Hom_{D(O_X)}(K, M)` for a perfect \
`K`, as an isomorphism of abelian groups along the canonical map of Stacks 08I1; not its \
functoriality in `M`"]
def derivedTensorDualGlobalSectionsAddEquiv
    (K M : DerivedCategory (StructureSheafModules Rc))
    (hK : (ringedSite Rc).IsPerfect K) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
        ((derivedModuleGlobalSections (ringedSite Rc)).obj
          (((derivedTensor Rc).obj M).obj (derivedDual Rc K))) : Type u) ≃+ (K ⟶ M) :=
  AddEquiv.ofBijective (derivedTensorDualGlobalSectionsMap Rc K M)
    (bijective_derivedTensorDualGlobalSectionsMap_of_isPerfect Rc K M hK)

end Stacks.SheafOfModules

end
