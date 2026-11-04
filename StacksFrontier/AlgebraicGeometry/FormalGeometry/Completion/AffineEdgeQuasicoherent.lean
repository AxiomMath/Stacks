module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.AffineCovering
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.HypercohomologyOverAcyclicOpens
public import StacksCore.Tactic.StacksAttribute

/-!
# The hypercohomology edge isomorphism over an affine open, at quasi-coherent cohomology sheaves

Let `X` be a scheme and `L` an object of `D(𝒪_X)` all of whose cohomology sheaves are
quasi-coherent. Over an affine open `U ⊂ X` the hypercohomology edge morphism is invertible:

`H^p(U, L) = Γ(U, H^p(L))`.

This is [Stacks, Tag 0BKT] at the basis of affine opens of a scheme, with its acyclicity
hypothesis discharged by Serre vanishing. The statement was previously available only inside the
proof of `Stacks.Algebraization.finite_homology_derivedSections_of_isPseudoCoherent`, where it is
assembled from three results on every use; it is factored out here because the comparison of a
derived completion with an adic quotient tower needs it at several different objects.

## Main results

* `Stacks.Algebraization.isZero_rightDerived_evaluation_homology_of_isQuasicoherent` — the
  acyclicity hypothesis of [Stacks, Tag 0BKT] on the basis of affine opens, for an object with
  quasi-coherent cohomology sheaves.
* `Stacks.Algebraization.homologyIso_derivedSections_of_isAffineOpen` — the edge isomorphism
  `H^p(U, L) ≅ Γ(U, H^p(L))`.

## References

* [Stacks Project, Tag 0BKT](https://stacks.math.columbia.edu/tag/0BKT)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.Cohomology.HypercohomologyEdge

universe u

namespace Stacks.Algebraization

attribute [local instance] HasDerivedCategory.standard

/-- **Serre vanishing supplies the acyclicity hypothesis of [Stacks, Tag 0BKT] on the basis of
affine opens.** If every cohomology sheaf of `L` is quasi-coherent then each of them has
vanishing higher cohomology over every affine open. -/
public theorem isZero_rightDerived_evaluation_homology_of_isQuasicoherent (X : Scheme.{u})
    (L : DerivedCategory X.Modules)
    (hqc : ∀ q : ℤ, ((DerivedCategory.homologyFunctor X.Modules q).obj L).IsQuasicoherent) :
    ∀ V ∈ X.affineOpens, ∀ r : ℕ, 0 < r → ∀ q : ℤ,
      IsZero (((SheafOfModules.evaluation (structureSheafRing X.toRingedSpace)
          (op V)).rightDerived r).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) q).obj L)) := by
  intro V hV r hr q
  have := hqc q
  exact (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
    X.ringCatSheaf V r ((DerivedCategory.homologyFunctor X.Modules q).obj L)).2
    (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X _ V hV r hr)

/-- **[Stacks, Tag 0BKT] over an affine open of a scheme.** For an object `L` of `D(𝒪_X)` with
quasi-coherent cohomology sheaves and an affine open `U`, the hypercohomology `H^p(U, L)` is the
module of sections over `U` of the cohomology sheaf `H^p(L)`.

The cohomology sheaves are acyclic over the affine opens by Serre vanishing
(`Stacks.Algebraization.isZero_rightDerived_evaluation_homology_of_isQuasicoherent`), and the
affine opens are a basis, so
`Stacks.Cohomology.AcyclicOpen.hypercohomologyIso` applies. -/
@[stacks 0BKT "over an affine open of a scheme, for an object of `D(𝒪_X)` whose cohomology \
sheaves are all quasi-coherent: the acyclicity hypothesis of the tag is Serre vanishing on the \
affine opens, which quasi-coherence supplies, and the affine opens are a basis of the topology",
  ega "III 1.3.1" "more general",
  ega "III 4.1.7.21" "H^i(U"]
public def homologyIso_derivedSections_of_isAffineOpen (X : Scheme.{u})
    (L : DerivedCategory X.Modules)
    (hqc : ∀ q : ℤ, ((DerivedCategory.homologyFunctor X.Modules q).obj L).IsQuasicoherent)
    (U : X.affineOpens) (p : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) p).obj
        ((derivedSections (structureSheafRing X.toRingedSpace) U.1).obj L) ≅
      ModuleCat.of Γ(X, U.1) Γ((DerivedCategory.homologyFunctor X.Modules p).obj L, U.1) :=
  Stacks.Cohomology.AcyclicOpen.hypercohomologyIso X.toRingedSpace L
    X.affineOpens X.isBasis_affineOpens
    (isZero_rightDerived_evaluation_homology_of_isQuasicoherent X L hqc) U.1 U.2 p

end Stacks.Algebraization

end
