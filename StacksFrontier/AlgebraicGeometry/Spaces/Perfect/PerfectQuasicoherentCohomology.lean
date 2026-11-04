module

public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherentCohomologyUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedCategory
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PseudoCoherenceAndTorAmplitude
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PseudoCoherenceAndTorAmplitudeSupplement

/-!
# A perfect object on an algebraic space has quasi-coherent cohomology

Let `S` be a scheme, let `F` be an algebraic space over `S` and let `E` be an object of
`D(𝒪_F)`.  If `E` is perfect then every cohomology sheaf of `E` is quasi-coherent, that is, `E`
lies in `D_QCoh(𝒪_F)`.  This is the inclusion `D_perf(𝒪_F) ⊆ D_QCoh(𝒪_F)`.

## Main results

* `AlgebraicGeometry.Space.derivedCategoryB_isQuasicoherentOnSite_of_isPerfect_of_isAlgebraicSpace`
  states that a perfect object of `D(𝒪_F)` lies in `D_QCoh(𝒪_F)`.

## Implementation notes

The proof is the composition of two results.  A perfect object of `D(O)` on any ringed site is
pseudo-coherent, by `AlgebraicGeometry.RingedSite.isPseudoCoherent_of_isPerfect_univ`, which is
the first clause of the implication (1) ⟹ (2) of Stacks 08G8; and a pseudo-coherent object of
`D(𝒪_F)` on an algebraic space has quasi-coherent cohomology, by
`AlgebraicGeometry.Space.derivedCategoryB_of_isPseudoCoherent_unconditional`, which is the
second assertion of Stacks 08JL.

The conclusion is the object property whose full subcategory is
`AlgebraicGeometry.Space.QuasicoherentDerivedCategory`, the `D_QCoh(𝒪_F)` of Stacks 071X, and
the hypothesis is the `AlgebraicGeometry.RingedSite.IsPerfect` whose full subcategory on the
small étale ringed site is the `D_perf(𝒪_F)` of
`AlgebraicGeometry.Space.PerfectDerivedCategory`.  Unfolding
`CategoryTheory.DerivedCategoryB.derivedCategoryB`, the conclusion is literally
`∀ n, Hⁿ(E)` quasi-coherent.

The two instance hypotheses on the slices of the small étale site, `HasSheafify` and
`WEqualsLocallyBijective`, are the ones `AlgebraicGeometry.RingedSite.IsPerfect` asks for and
that `StacksFrontier/AlgebraicGeometry/Spaces/RingedSite.lean` does not already provide at this
universe.  The remaining sheafification hypotheses of `AlgebraicGeometry.RingedSite.IsPerfect`
— weak sheafification and local bijectivity of the weak equivalences on the slices, and
sheafification on the site itself — are global instances for the small étale ringed site of an
algebraic space.

## References

* [Stacks Project, Tag 08G8](https://stacks.math.columbia.edu/tag/08G8)
* [Stacks Project, Tag 08JL](https://stacks.math.columbia.edu/tag/08JL)
* [Stacks Project, Tag 071X](https://stacks.math.columbia.edu/tag/071X)
* [Stacks Project, Tag 0F8I](https://stacks.math.columbia.edu/tag/0F8I)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    [∀ U : (smallEtaleRingedSite B S hS F hF).C,
      HasSheafify ((smallEtaleRingedSite B S hS F hF).J.over U) AddCommGrpCat.{u}]
    [∀ U : (smallEtaleRingedSite B S hS F hF).C,
      ((smallEtaleRingedSite B S hS F hF).J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ U : (smallEtaleRingedSite B S hS F hF).C,
      ((smallEtaleRingedSite B S hS F hF).J.over U).HasSheafCompose
        (forget₂ RingCat.{u} AddCommGrpCat.{u})]

omit [∀ U : (smallEtaleRingedSite B S hS F hF).C,
  ((smallEtaleRingedSite B S hS F hF).J.over U).HasSheafCompose
    (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- **A perfect object of `D(𝒪_F)` lies in `D_QCoh(𝒪_F)`**, for `F` an algebraic space over the
base: if `E` is perfect then `Hⁿ(E)` is a quasi-coherent `𝒪_F`-module for every `n`.

This is the inclusion `D_perf(𝒪_F) ⊆ D_QCoh(𝒪_F)`, the full subcategories being
`AlgebraicGeometry.Space.PerfectDerivedCategory` and
`AlgebraicGeometry.Space.QuasicoherentDerivedCategory`.

A perfect object is pseudo-coherent, by
`AlgebraicGeometry.RingedSite.isPseudoCoherent_of_isPerfect_univ`, and a pseudo-coherent object of
`D(𝒪_F)` has quasi-coherent cohomology, by
`AlgebraicGeometry.Space.derivedCategoryB_of_isPseudoCoherent_unconditional`. -/
theorem derivedCategoryB_isQuasicoherentOnSite_of_isPerfect_of_isAlgebraicSpace
    (E : DerivedCategory (Modules.{u, u} B S hS F hF))
    (hE : (smallEtaleRingedSite B S hS F hF).IsPerfect E) :
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) E :=
  derivedCategoryB_of_isPseudoCoherent_unconditional B S hS F hF E
    (RingedSite.isPseudoCoherent_of_isPerfect_univ (smallEtaleRingedSite B S hS F hF) hE)

end AlgebraicGeometry.Space

end
