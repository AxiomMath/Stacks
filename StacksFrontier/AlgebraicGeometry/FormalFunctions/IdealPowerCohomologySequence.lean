module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.AffineBase
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.IdealPowerShortExact
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# The long exact cohomology sequence of `0 → I ^ n ℱ → ℱ → ℱ / I ^ n ℱ → 0`

Let `X` be a scheme, `I` a quasi-coherent ideal sheaf on `X` and `ℱ` a sheaf of modules. The
short exact sequence of
`StacksFrontier/AlgebraicGeometry/FormalFunctions/IdealPowerShortExact.lean` has a long exact
cohomology sequence, and this file records the three of its properties that the Artin--Rees step
of the theorem on formal functions uses, all of them in the `Γ(X, ⊤)`-module spelling of
cohomology rather than at abelian sheaves:

* exactness of `H^p(X, I ^ n ℱ) → H^p(X, ℱ) → H^p(X, ℱ / I ^ n ℱ)`, which identifies
  `Ker(H^p(X, ℱ) → H^p(X, ℱ / I ^ n ℱ))` with `Im(H^p(X, I ^ n ℱ) → H^p(X, ℱ))`;
* exactness of `H^p(X, ℱ) → H^p(X, ℱ / I ^ n ℱ) → H^(p+1)(X, I ^ n ℱ)`;
* naturality of the connecting map along the ladder `idealPowerQuotientShortComplexMap`.

## Main definitions

* `Stacks.Cohomology.FormalFunctions.cohomologyDeltaFunctor` — the cohomological `δ`-functor
  `ℱ ↦ H^•(X, ℱ)` on `X.Modules`, valued in `Γ(X, ⊤)`-modules.
* `Stacks.Cohomology.FormalFunctions.idealPowerδ` — the connecting map
  `H^p(X, ℱ / I ^ n ℱ) ⟶ H^(p+1)(X, I ^ n ℱ)`.

## Main results

* `Stacks.Cohomology.FormalFunctions.ker_cohomology_idealPowerQuotient_eq_range` —
  `Ker(H^p(X, ℱ) → H^p(X, ℱ / I ^ n ℱ)) = Im(H^p(X, I ^ n ℱ) → H^p(X, ℱ))`, the identity with
  which [Stacks, Tag 02OB] part (1) begins.
* `Stacks.Cohomology.FormalFunctions.exact_cohomology_idealPowerQuotient_δ` — exactness at
  `H^p(X, ℱ / I ^ n ℱ)`.
* `Stacks.Cohomology.FormalFunctions.idealPowerδ_naturality` — the ladder square relating the
  connecting maps in two consecutive exponents, the diagram chase of [Stacks, Tag 02OB] part (3).

## Implementation notes

The `δ`-functor is `Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives` applied to
`Stacks.Cohomology.AffineBase.moduleGlobalSections X`, which needs nothing beyond additivity of
that functor and enough injectives on `X.Modules`. The same instantiation is made privately in
`StacksFrontier/AlgebraicGeometry/CohomologyFinitenessNoetherian/Basic.lean`, where only one
exactness field is used and the connecting morphisms therefore appear in no statement; here the
connecting map is needed in a statement, so the `δ`-functor is public.

`HasDerivedCategory.standard` is a `local instance`: the generic constructor is built through the
bounded-below derived category and asks for `HasDerivedCategory` on both sides, while the
statements below mention only `Functor.rightDerived`, which does not.

Cohomology is valued in `ModuleCat Γ(X, ⊤)` and not in modules over a base ring; a morphism
`f : X ⟶ Spec A` turns these into `A`-modules by `ModuleCat.restrictScalars`, which changes
neither the carriers nor the maps, so every exactness statement below transports to `A`-modules
by `fun x => h x`.

## References

* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
* [Stacks Project, Tag 02OB](https://stacks.math.columbia.edu/tag/02OB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Cohomology.FormalFunctions

open Stacks.Cohomology.AffineBase Stacks.Algebraization

/-- **The long exact sequence of global-sections cohomology**, valued in `Γ(X, ⊤)`-modules, as
the cohomological `δ`-functor of [Stacks, Tag 010Q]. There is no base and no hypothesis on `X`:
the generic constructor needs only additivity of `moduleGlobalSections X` and enough injectives
on `X.Modules`. -/
public def cohomologyDeltaFunctor (X : Scheme.{u}) :
    CategoryTheory.DeltaFunctor X.Modules (ModuleCat.{u} Γ(X, ⊤)) :=
  Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives (moduleGlobalSections X)

/-- The `p`-th functor of `cohomologyDeltaFunctor X` is the `p`-th right derived functor of
`moduleGlobalSections X`. -/
@[simp]
public lemma cohomologyDeltaFunctor_functor (X : Scheme.{u}) (p : ℕ) :
    (cohomologyDeltaFunctor X).functor p = (moduleGlobalSections X).rightDerived p := rfl

variable {X : Scheme.{u}} (I : X.IdealSheafData) (F : X.Modules) (n p : ℕ)

/-- The connecting map `H^p(X, ℱ / I ^ n ℱ) ⟶ H^(p+1)(X, I ^ n ℱ)` of the short exact sequence
`0 → I ^ n ℱ → ℱ → ℱ / I ^ n ℱ → 0`. -/
public def idealPowerδ :
    ((moduleGlobalSections X).rightDerived p).obj (idealPowerQuotient I n F) ⟶
      ((moduleGlobalSections X).rightDerived (p + 1)).obj
        (idealPowerMultiple I n F).toSheafOfModules :=
  (cohomologyDeltaFunctor X).δ (idealPowerQuotientShortComplex_shortExact I n F) p

/-- **Exactness at `H^p(X, ℱ)`.** The sequence
`H^p(X, I ^ n ℱ) → H^p(X, ℱ) → H^p(X, ℱ / I ^ n ℱ)` is exact. -/
public theorem exact_cohomology_idealPowerMultiple :
    Function.Exact
      (((moduleGlobalSections X).rightDerived p).map (idealPowerMultiple I n F).ι).hom
      (((moduleGlobalSections X).rightDerived p).map
        (cokernel.π (C := X.Modules) (idealPowerMultiple I n F).ι)).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    ((cohomologyDeltaFunctor X).exact_map (idealPowerQuotientShortComplex_shortExact I n F) p)

/-- **`Ker(H^p(X, ℱ) → H^p(X, ℱ / I ^ n ℱ)) = Im(H^p(X, I ^ n ℱ) → H^p(X, ℱ))`.** This is the
identity with which the Artin--Rees step of the theorem on formal functions begins,
[Stacks, Tag 02OB] part (1). -/
public theorem ker_cohomology_idealPowerQuotient_eq_range :
    LinearMap.ker (((moduleGlobalSections X).rightDerived p).map
        (cokernel.π (C := X.Modules) (idealPowerMultiple I n F).ι)).hom =
      LinearMap.range (((moduleGlobalSections X).rightDerived p).map
        (idealPowerMultiple I n F).ι).hom :=
  LinearMap.exact_iff.1 (exact_cohomology_idealPowerMultiple I F n p)

/-- **Exactness at `H^p(X, ℱ / I ^ n ℱ)`.** The sequence
`H^p(X, ℱ) → H^p(X, ℱ / I ^ n ℱ) → H^(p+1)(X, I ^ n ℱ)` is exact. -/
public theorem exact_cohomology_idealPowerQuotient_δ :
    Function.Exact
      (((moduleGlobalSections X).rightDerived p).map
        (cokernel.π (C := X.Modules) (idealPowerMultiple I n F).ι)).hom
      (idealPowerδ I F n p).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    ((cohomologyDeltaFunctor X).exact_δ₁ (idealPowerQuotientShortComplex_shortExact I n F) p)

/-- **Exactness at `H^(p+1)(X, I ^ n ℱ)`.** The sequence
`H^p(X, ℱ / I ^ n ℱ) → H^(p+1)(X, I ^ n ℱ) → H^(p+1)(X, ℱ)` is exact. -/
public theorem exact_δ_cohomology_idealPowerMultiple :
    Function.Exact (idealPowerδ I F n p).hom
      (((moduleGlobalSections X).rightDerived (p + 1)).map
        (idealPowerMultiple I n F).ι).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    ((cohomologyDeltaFunctor X).exact_δ₂ (idealPowerQuotientShortComplex_shortExact I n F) p)

variable {n}

/-- **Naturality of the connecting map along the ladder.** For `n ≤ m`, lowering the exponent on
`H^p(X, ℱ / I ^ m ℱ)` and then taking the connecting map of the exponent-`n` sequence is the
connecting map of the exponent-`m` sequence followed by the inclusion
`I ^ m ℱ ⊆ I ^ n ℱ` in degree `p + 1`. -/
public theorem idealPowerδ_naturality {m : ℕ} (h : n ≤ m) :
    ((moduleGlobalSections X).rightDerived p).map (idealPowerQuotientDrop I h F) ≫
        idealPowerδ I F n p =
      idealPowerδ I F m p ≫ ((moduleGlobalSections X).rightDerived (p + 1)).map
        (submoduleInclusion (idealPowerMultiple_antitone I F h)) :=
  (cohomologyDeltaFunctor X).δ_naturality (idealPowerQuotientShortComplex_shortExact I m F)
    (idealPowerQuotientShortComplex_shortExact I n F) (idealPowerQuotientShortComplexMap I F h) p

end Stacks.Cohomology.FormalFunctions

end
