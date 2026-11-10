module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.FormalFunctionsAdicLimitUnconditional
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohomology over a complete Noetherian base is the limit of the cohomology of the adic quotients

Let `A` be a Noetherian ring which is complete with respect to an ideal `I`, let
`f : X ⟶ Spec A` be a proper morphism of algebraic spaces and let `F` be a coherent
`𝒪_X`-module.  [Stacks, Tag 08B0] says that for every `p ≥ 0` the canonical map
`Hᵖ(X, F) ⟶ lim_n Hᵖ(X, F / Iⁿ F)` is an isomorphism.

This is proved in the imported module as
`AlgebraicGeometry.Space.C1573.bijective_cohomologyToIdealQuotientLimit`, whose hypotheses are
section variables of that file.  Here the same statement is recorded with every hypothesis in its
own signature.

## Main results

* `AlgebraicGeometry.Space.cohomologyToIdealQuotientLimit_bijective_of_isAdicComplete`:
  **[Stacks, Tag 08B0]**.

## References

* [Stacks Project, Tag 08B0](https://stacks.math.columbia.edu/tag/08B0)
* [Stacks Project, Tag 08AZ](https://stacks.math.columbia.edu/tag/08AZ)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 08B0.**  Let `A` be a Noetherian ring (`[IsNoetherianRing A]`), `I ⊆ A` an ideal
such that `A` is `I`-adically complete (`[IsAdicComplete I A]`), `f : X ⟶ Spec A` a proper
morphism of algebraic spaces and `F` a coherent `𝒪_X`-module.  Then for every `p ≥ 0` the
canonical map `Hᵖ(X, F) ⟶ lim_n Hᵖ(X, F / Iⁿ F)` is bijective, i.e.
`Hᵖ(X, F) = lim_n Hᵖ(X, F / Iⁿ F)`.

The objects in the statement, with the files that define them:
* `B : BigFppfSite` is a big fppf site and `hA : B.Contains (Spec A)` says that `Spec A` is one of
  its schemes; `AlgebraicSpaces B (Spec A) hA`
  (`StacksFrontier/AlgebraicGeometry/Spaces/Category.lean`) is the category of algebraic spaces over
  `Spec A`.
* `AlgebraicGeometry.Space.baseObject A B hA`
  (`StacksFrontier/AlgebraicGeometry/Spaces/FormalAlgebraization.lean`) is `Spec A` itself as an
  object of the big fppf site over `Spec A` (the identity of `Spec A`), and
  `AlgebraicGeometry.schemeSpace` (`StacksFrontier/AlgebraicGeometry/Spaces/SchemeAsSpace.lean`)
  regards it as an algebraic space, so `f : X ⟶ schemeSpace (baseObject A B hA)` is a morphism
  `X ⟶ Spec A` of algebraic spaces over `Spec A`.
* `AlgebraicGeometry.Space.IsProper`
  (`StacksFrontier/AlgebraicGeometry/Spaces/UniversallyClosed.lean`, Stacks 03ZM) is properness of a
  morphism of algebraic spaces: separated, of finite type and universally closed.
* `AlgebraicGeometry.Space.Modules` (`StacksFrontier/AlgebraicGeometry/Spaces/RingedSite.lean`) is
  the category of `𝒪_X`-modules on the small étale site of `X`, and
  `AlgebraicGeometry.Space.IsCoherent`
  (`StacksFrontier/AlgebraicGeometry/Spaces/CoherentModules.lean`, Stacks 07UA) says that such a
  module is coherent.
* `AlgebraicGeometry.Space.baseRingHom A B hA X.1 X.2`
  (`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleCohomology.lean`) is the canonical ring map
  from `A` to the global functions of `X`, through which `A` acts on cohomology.
* `AlgebraicGeometry.Space.C1573.cohomologyToIdealQuotientLimit φ F I p` (the imported module)
  is the `A`-linear map `Hᵖ(X, F) ⟶ lim_n Hᵖ(X, F / Iⁿ F)` whose `n`-th component is the map on
  `Hᵖ` induced by the projection `F ⟶ F / Iⁿ F`.  Here `Hᵖ(X, -)` is the `p`-th right derived
  functor of global sections on `𝒪_X`-modules, as an `A`-module along `φ`
  (`AlgebraicGeometry.Space.cohomologyRes`,
  `StacksFrontier/AlgebraicGeometry/Spaces/IdealPowerCohomologyReesFinite.lean`); `F / Iⁿ F` is the
  cokernel of the inclusion of the submodule `Iⁿ F ⊆ F`, the image of multiplication by the
  elements of `Iⁿ` (`AlgebraicGeometry.Space.idealQuotient`,
  `StacksFrontier/AlgebraicGeometry/Spaces/IdealMultipleModule.lean`); and the limit is
  `AlgebraicGeometry.Space.C1573.cohomologyIdealQuotientLimit` (same file as the map), the
  `A`-module of compatible families of the tower `n ↦ Hᵖ(X, F / Iⁿ F)` under the maps induced by
  `F / Iⁿ F ⟶ F / Iᵐ F`, `m ≤ n` (`Stacks.IntertwinedFiltration.towerLimit`,
  `StacksFrontier/RingTheory/AdicCompletion/IntertwinedFiltration.lean`).

The proof is `AlgebraicGeometry.Space.C1573.bijective_cohomologyToIdealQuotientLimit`: `Hᵖ(X, F)`
is a finite `A`-module (Stacks 08AS), hence `I`-adically complete, and the theorem on formal
functions (Stacks 08AZ) identifies its completion with the limit. -/
@[stacks 08B0, ega "III 4.1.5" "partial", ega "III 4.1.7" "special case", sga "2 XII 5.8" "partial"]
theorem cohomologyToIdealQuotientLimit_bijective_of_isAdicComplete {B : BigFppfSite.{u}}
    {A : Type u} [CommRing A] [IsNoetherianRing A] {hA : B.Contains (Spec (.of A))}
    {X : AlgebraicSpaces B (Spec (.of A)) hA} (f : X ⟶ schemeSpace (baseObject A B hA))
    (hf : IsProper B (Spec (.of A)) hA f.hom) (F : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2)
    [IsCoherent B (Spec (.of A)) hA X.1 X.2 F] (I : Ideal A) [IsAdicComplete I A] (p : ℕ) :
    Function.Bijective
      (C1573.cohomologyToIdealQuotientLimit (baseRingHom A B hA X.1 X.2) F I p) :=
  C1573.bijective_cohomologyToIdealQuotientLimit f hf F I p

end AlgebraicGeometry.Space

end
