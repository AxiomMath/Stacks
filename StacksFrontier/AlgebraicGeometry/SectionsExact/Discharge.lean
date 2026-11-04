module

public import StacksFrontier.AlgebraicGeometry.AffineVanishing.Basic
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.AlgebraicGeometry.SectionsExact.Basic

/-!
# The long exact cohomology sequence over an open, and [Stacks, Tag 01EW] without it

`StacksFrontier/AlgebraicGeometry/AffineVanishing/Basic.lean` reduces [Stacks, Tag 01EW] to four
named statements, the first of which is `Stacks.CohomologyVanishing.IsCohomologyDeltaFunctor`:
a cohomological δ-functor on `Mod(𝒪_X)` whose degree-zero part is `Γ(U, -)` and whose
positive-degree parts are the cohomology functors `Hⁿ(U, -)`. Equivalently, the long exact
cohomology sequence over the open `U`.

This file discharges it. The δ-functor is
`Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives (secF R U)`, the `ℕ`-indexed
right derived δ-functor of `Γ(U, -)`, and the resulting capstone
`Stacks.CohomologyVanishing.higherCohomology_isZero_of_cechGaps` carries only the three
*remaining* gaps of the tag — [Stacks, Tag 01EP], the degreewise form of [Stacks, Tag 01EU], and
[Stacks, Tag 01EU] itself.

## Main results

* `Stacks.CohomologyVanishing.isCohomologyDeltaFunctor_rightDerived`: the right derived
  δ-functor of `Γ(U, -)` realizes the cohomology over `U`, i.e. the long exact cohomology
  sequence over `U`.
* `Stacks.CohomologyVanishing.higherCohomology_isZero_of_cechGaps`: **[Stacks, Tag 01EW] with
  the long exact sequence no longer a hypothesis.** `Hⁿ(U, F) = 0` for `n > 0` and `U ∈ Bas`,
  from the three Čech statements alone.

No tag attribute is attached. Tag 01EW belongs to the cohomology chapters, and three of its four
inputs are still hypotheses here, so a tag would misreport the tag as formalized.

## Implementation notes

**Why both fields are cheap.** `isoZero` is `CategoryTheory.Functor.rightDerivedZeroIsoSelf`,
whose one side condition is left exactness of `Γ(U, -)`; that is
`Stacks.SectionsExact.preservesFiniteLimits_secF`, and it was the last thing missing.

`isoSucc` is `Iso.refl`. This is worth recording rather than rediscovering:
`Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives_functor` holds by `rfl`, so
the degree-`m+1` part of the δ-functor *is* `(secF R U).rightDerived (m + 1)`, which is the
definition of `Hfunctor R U (m + 1)`. The two sides are the same functor, not merely isomorphic
ones, and no transport along the `ℕ`/`ℤ` indexing comparison is needed in positive degrees — the
comparison is already spent inside `rightDerivedDeltaFunctorOfEnoughInjectives`.

**The derived-category hypotheses.** `[HasDerivedCategory (SheafOfModules.{w} R)]` and
`[HasDerivedCategory AddCommGrpCat.{w}]` are what `rightDerivedDeltaFunctorOfEnoughInjectives`
needs; they are not required by the capstone of `AffineVanishing/Basic.lean` and appear here only
because the δ-functor is built through `D⁺`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u w

namespace Stacks.CohomologyVanishing

variable {X : Type u} [TopologicalSpace X]
  (R : Sheaf (Opens.grothendieckTopology X) RingCat)
  [HasProducts.{u} AddCommGrpCat.{w}]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{w}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EnoughInjectives (SheafOfModules.{w} R)]
  [HasDerivedCategory (SheafOfModules.{w} R)]
  [HasDerivedCategory AddCommGrpCat.{w}]

/-- **The long exact cohomology sequence over an open `U`**, i.e. the first of the four gaps of
[Stacks, Tag 01EW]: the `ℕ`-indexed right derived δ-functor of `Γ(U, -)` has degree-zero part
`Γ(U, -)` and positive-degree parts the cohomology functors `Hⁿ(U, -)`. -/
noncomputable def isCohomologyDeltaFunctor_rightDerived (U : Opens X) :
    IsCohomologyDeltaFunctor R U
      (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives (secF R U)) where
  isoZero := Functor.rightDerivedZeroIsoSelf (secF R U)
  isoSucc _ := Iso.refl _

/-- **[Stacks, Tag 01EW] reduced to its three Čech statements.** Let `F` be an `𝒪_X`-module with
vanishing positive-degree Čech cohomology for every covering in `Cov`. Then `Hⁿ(U, F) = 0` for
every `n > 0` and every `U ∈ Bas`, given

1. Čech acyclicity of injective modules (`CechAcyclicInjectives`, [Stacks, Tag 01EP]);
2. short exactness of the Čech complexes of a short exact sequence (`CechShortExact`,
   [Stacks, Tag 01EU] degreewise);
3. surjectivity on sections over the basis opens ([Stacks, Tag 01EU]).

This is `higherCohomology_isZero_of_gaps` with its first hypothesis supplied by
`isCohomologyDeltaFunctor_rightDerived`: the long exact cohomology sequence over `U` is no longer
assumed. -/
theorem higherCohomology_isZero_of_cechGaps {Bas : Set (Opens X)} {Cov : Set (OpenCover X)}
    {U : Opens X} (hinj : CechAcyclicInjectives R Cov) (hSE : CechShortExact R Cov)
    (hsec : ∀ S : ShortComplex (SheafOfModules.{w} R), S.ShortExact →
      ∀ V ∈ Bas, Epi ((secF R V).map S.g))
    (hU : U ∈ Bas) (F : SheafOfModules.{w} R) (hF : HasVanishingHigherCech R Cov F)
    (n : ℕ) (hn : 0 < n) : IsZero (Hgroup R U n F) :=
  higherCohomology_isZero_of_gaps R (isCohomologyDeltaFunctor_rightDerived R U) hinj hSE hsec
    hU F hF n hn

end Stacks.CohomologyVanishing
