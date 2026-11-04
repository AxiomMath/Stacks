module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.Basic
public import StacksFrontier.Homology.DerivedIndexing.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# The first page of the Hodge-to-de Rham spectral sequence

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a topological space, with
`𝒪_X` the structure sheaf of a ringed space `X`, and let `Ω^•_{𝒪_X/A}` be the relative de Rham
complex. The brutal truncations `σ^{≥p}Ω^•_{𝒪_X/A}` make it a filtered complex, and the spectral
sequence of that filtered complex is the *Hodge-to-de Rham spectral sequence*. Its first page is

`E_1^{p, q} = H^q(X, Ω^p_{𝒪_X/A})`,

the Hodge cohomology of `X` over `A`, and the differential
`d_1^{p, q} : H^q(X, Ω^p) ⟶ H^q(X, Ω^{p + 1})` is the map induced by the de Rham differential
`d : Ω^p ⟶ Ω^{p + 1}`.

This file builds that page, row by row, directly from the de Rham complex.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.hodgeToDeRhamFirstPage`: the `q`-th row `E_1^{•, q}` of the
  first page, as a cochain complex: the term in position `p` is the Hodge cohomology group
  `H^q(X, Ω^p_{𝒪_X/A})` and the differential is the one induced by the de Rham differential.

## Main results

* `AlgebraicGeometry.SheafOfModules.hodgeToDeRhamFirstPage_X` and
  `AlgebraicGeometry.SheafOfModules.hodgeToDeRhamFirstPage_d`: the terms and the differential of
  the first page are the Hodge cohomology groups and the maps the de Rham differential induces
  on them.

## Implementation notes

The spectral sequence itself is not constructed here, only its first page. The construction is
available: the de Rham complex of `AlgebraicGeometry.SheafOfModules.deRhamComplexInt` is
concentrated in nonnegative degrees, so
`Stacks.Cohomology.FilteredComplex.exists_boundedBelowStupidTruncationSpectralSequence`
([Stacks, Tag 0FLK]) applies to it and produces the spectral sequence of its brutal filtration
`CochainComplex.stupidTruncationFiltration` ([Stacks, Tag 0118]), bounded and converging to the
hypercohomology of the de Rham complex, with first page `H^q(X, Ω^p_{𝒪_X/A})`; the filtration it
converges along is the image of the hypercohomology of the brutal truncations, which is the Hodge
filtration of `AlgebraicGeometry.SheafOfModules.hodgeFiltration` ([Stacks, Tag 0FM8]).

The page is formed in the abelian-sheaf realization of the de Rham complex, the one in which
`AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelian` and the Hodge cohomology group
`AlgebraicGeometry.Scheme.Hom.hodgeCohomologyOne` are taken. Each row is the cohomology functor
`H^q(X, -)` applied to the de Rham complex degreewise, so `d_1` is by construction the map
induced by the de Rham differential, and it squares to zero because `d ∘ d = 0`.

## References

* [Stacks Project, Tag 0FM6](https://stacks.math.columbia.edu/tag/0FM6)
* [Stacks Project, Tag 0FM8](https://stacks.math.columbia.edu/tag/0FM8)
* [Stacks Project, Tag 0FLK](https://stacks.math.columbia.edu/tag/0FLK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.Cohomology.Leray (sectionsFunctor)

universe u

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-- Cohomology of abelian sheaves over an open subset is an additive functor. This is the
`additive` field of the cohomological `δ`-functor of [Stacks, Tag 010Q]; Mathlib does not record
it as an instance for `CategoryTheory.Functor.rightDerived`. -/
instance additive_rightDerived_sectionsFunctor (Y : TopCat.{u}) (U : Opens Y) (q : ℕ) :
    ((sectionsFunctor Y U).rightDerived q).Additive :=
  (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (sectionsFunctor Y U)).additive q

variable {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-- **The `q`-th row `E_1^{•, q}` of the first page of the Hodge-to-de Rham spectral sequence of
Stacks Section 0FM6.** The term in position `p` is the Hodge cohomology group
`H^q(X, Ω^p_{𝒪_X/A})` and the differential `d_1^{p, q} : H^q(X, Ω^p) ⟶ H^q(X, Ω^{p + 1})` is the
map induced by the de Rham differential `d : Ω^p ⟶ Ω^{p + 1}`; it squares to zero because the de
Rham differential does. -/
@[stacks 0FM6 "the first page of the Hodge-to-de Rham spectral sequence, E_1^{p,q} = H^q(X, Ω^p)
with d_1 induced by the de Rham differential; the spectral sequence itself and the conjugate
spectral sequence are not constructed", sga "7 XXII 3.3" "First page of (3.3.2)"]
abbrev hodgeToDeRhamFirstPage (q : ℕ) : CochainComplex AddCommGrpCat.{u} ℕ :=
  (((sectionsFunctor X.carrier ⊤).rightDerived q).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (deRhamAbelianComplex B D)

/-- The term of the first page in position `(p, q)` is the Hodge cohomology group
`H^q(X, Ω^p_{𝒪_X/A})`. -/
theorem hodgeToDeRhamFirstPage_X (q p : ℕ) :
    (hodgeToDeRhamFirstPage B D q).X p =
      ((sectionsFunctor X.carrier ⊤).rightDerived q).obj ((deRhamAbelianComplex B D).X p) :=
  rfl

/-- The differential of the first page is the map induced on `H^q(X, -)` by the de Rham
differential `d : Ω^p ⟶ Ω^{p + 1}`. -/
theorem hodgeToDeRhamFirstPage_d (q p : ℕ) :
    (hodgeToDeRhamFirstPage B D q).d p (p + 1) =
      ((sectionsFunctor X.carrier ⊤).rightDerived q).map
        ((deRhamAbelianComplex B D).d p (p + 1)) := by
  simp [hodgeToDeRhamFirstPage]

end AlgebraicGeometry.SheafOfModules

end
