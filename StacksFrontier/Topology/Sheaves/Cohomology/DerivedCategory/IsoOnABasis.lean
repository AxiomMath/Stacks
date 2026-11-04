module

public import StacksFrontier.AlgebraicGeometry.HigherDirectImageAffine.BasisVanishing
public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CohomologySheavesOfADerivedPushforward

/-!
# Isomorphisms of the derived category detected on a basis

Let `(Z, 𝒪_Z)` be a ringed space and let `ℬ` be a basis for the topology of `Z`. A morphism
`φ : K ⟶ L` of the unbounded derived category `D(𝒪_Z)` is an isomorphism as soon as the maps it
induces on hypercohomology `H^n(V, K) ⟶ H^n(V, L)` are bijective for every `V ∈ ℬ` and every
`n`.

Indeed the `n`-th cohomology sheaf of an object of `D(𝒪_Z)` is the sheafification of its
cohomology presheaf `V ↦ H^n(V, -)` ([Stacks, Tag 0BKJ]), and a morphism of presheaves of modules
which is bijective on the members of a basis has invertible sheafification: its kernel and its
cokernel vanish on the basis, so their sheafifications vanish, and sheafification is exact.

## Main results

* `Stacks.Topology.BasisVanishing.isIso_sheafification_map_of_bijective_on_basis`: a morphism of
  presheaves of modules bijective on a basis has invertible sheafification.
* `Stacks.Cohomology.DerivedIsoOnABasis.isIso_of_bijective_homology_derivedSectionsOverOpen`:
  **a morphism of `D(𝒪_Z)` inducing bijections on hypercohomology over the members of a basis is
  an isomorphism.**

## References

* [Stacks Project, Tag 0BKJ](https://stacks.math.columbia.edu/tag/0BKJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.DerivedSectionsLeray (derivedSectionsOverOpen)
open scoped Stacks.StandardDerivedModel

universe u

namespace Stacks.Topology.BasisVanishing

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **A morphism of presheaves of modules which is bijective on a basis has invertible
sheafification.** Its kernel and its cokernel vanish on the basis, hence have vanishing
sheafifications, and sheafification preserves kernels and cokernels. -/
theorem isIso_sheafification_map_of_bijective_on_basis {P Q : PresheafOfModules.{u} R.obj}
    (α : P ⟶ Q) {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (hα : ∀ V ∈ B, Function.Bijective (α.app (op V))) :
    IsIso ((PresheafOfModules.sheafification (𝟙 R.obj)).map α) := by
  let S := PresheafOfModules.sheafification.{u} (𝟙 R.obj)
  have hker : IsZero (S.obj (kernel α)) := by
    refine isZero_sheafification_of_isZero_on_basis (kernel α) hB fun V hV => ?_
    have hmono : Mono (α.app (op V)) :=
      (ModuleCat.mono_iff_injective _).2 (hα V hV).1
    exact Functor.map_isZero (forget₂ _ AddCommGrpCat)
      ((isZero_kernel_of_mono (α.app (op V))).of_iso
        (PreservesKernel.iso (PresheafOfModules.evaluation R.obj (op V)) α))
  have hcok : IsZero (S.obj (cokernel α)) := by
    refine isZero_sheafification_of_isZero_on_basis (cokernel α) hB fun V hV => ?_
    have hepi : Epi (α.app (op V)) :=
      (ModuleCat.epi_iff_surjective _).2 (hα V hV).2
    exact Functor.map_isZero (forget₂ _ AddCommGrpCat)
      ((isZero_cokernel_of_epi (α.app (op V))).of_iso
        (PreservesCokernel.iso (PresheafOfModules.evaluation R.obj (op V)) α))
  have hm : Mono (S.map α) :=
    Preadditive.mono_of_isZero_kernel _ (hker.of_iso (PreservesKernel.iso S α).symm)
  have he : Epi (S.map α) :=
    Preadditive.epi_of_isZero_cokernel _ (hcok.of_iso (PreservesCokernel.iso S α).symm)
  exact isIso_of_mono_of_epi _

end Stacks.Topology.BasisVanishing

namespace Stacks.Cohomology.DerivedIsoOnABasis

/-- Sheaves of modules on a ringed space form a Grothendieck abelian category, in the one module
universe available there. -/
local instance isGrothendieckAbelian_moduleSheaves (Y : RingedSpace.{u, u}) :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} (structureSheafRing Y)) :=
  SheafOfModules.isGrothendieckAbelianU.{u, u, u} (structureSheafRing Y)

variable {Z : RingedSpace.{u, u}}

/-- **A morphism of `D(𝒪_Z)` is an isomorphism if it induces bijections on hypercohomology over
the members of a basis.** If `ℬ` is a basis of the topology of `Z` and `φ : K ⟶ L` induces
bijections `H^n(V, K) ⟶ H^n(V, L)` for every `V ∈ ℬ` and every `n`, then `φ` is an
isomorphism: the cohomology sheaves are the sheafifications of the cohomology presheaves
([Stacks, Tag 0BKJ]). -/
theorem isIso_of_bijective_homology_derivedSectionsOverOpen {B : Set (Opens Z.carrier)}
    (hB : Opens.IsBasis B)
    {K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z))} (φ : K ⟶ L)
    (h : ∀ V ∈ B, ∀ n : ℤ, Function.Bijective
      ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((structureSheafRing Z).obj.obj (op V))) n).map
          ((derivedSectionsOverOpen Z V).map φ))) :
    IsIso φ := by
  rw [DerivedCategory.isIso_iff]
  intro n
  let O := structureSheafRing Z
  let P := Stacks.Cohomology.HypercohomologyEdge.derivedSectionsPresheaf O ⋙
    DerivedCategory.homologyFunctor (PresheafOfModules.{u} O.obj) n
  have hP : ∀ V ∈ B, Function.Bijective ((P.map φ).app (op V)) := by
    intro V hV
    have hiso : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} (O.obj.obj (op V))) n).map
        ((derivedSectionsOverOpen Z V).map φ)) :=
      (ConcreteCategory.isIso_iff_bijective _).2 (h V hV n)
    have hiso' : IsIso ((P ⋙ PresheafOfModules.evaluation O.obj (op V)).map φ) :=
      (NatIso.isIso_map_iff
        (Stacks.Cohomology.HypercohomologyEdge.sectionsEvaluationIso O V n) φ).2 hiso
    exact (ConcreteCategory.isIso_iff_bijective _).1 hiso'
  exact (NatIso.isIso_map_iff
    (Stacks.Cohomology.HypercohomologyEdge.sheafificationCohomologyPresheafIso O n) φ).1
    (Stacks.Topology.BasisVanishing.isIso_sheafification_map_of_bijective_on_basis
      (P.map φ) hB hP)

end Stacks.Cohomology.DerivedIsoOnABasis
