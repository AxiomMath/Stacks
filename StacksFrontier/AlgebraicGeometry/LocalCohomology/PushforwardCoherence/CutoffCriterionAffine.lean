module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.FiniteLocallyFreeComplementAffine
public import StacksFrontier.RingTheory.LocalCohomology.SerreFormalFibresCriterion

/-!
# Coherence of the higher direct images on a punctured affine spectrum, below the cutoff

Let `A` be a Noetherian ring, `I ⊆ A` an ideal, `X = Spec A`, `Z = V(I)`, `U = X ∖ Z` and
`j : U → X` the inclusion. Let `M` be a finite `A`-module and `ℱ = M̃|_U`. This file assembles
two things.

First, clause (3) of [Stacks, Tag 0BK0] in the form its consumers need: `R^pj_*ℱ` is coherent
if and only if `H^{p+1}_Z(M)` is a finite `A`-module. The tag's (a) ⟺ (b) compares `R^pj_*ℱ`
with `H^p(U, ℱ)` and its (b) ⟺ (c) compares `H^p(U, ℱ)` with `H^{p+1}_Z(M)`; both are already
available, and the composite is what the finiteness theorems for local cohomology plug into.

Second, the affine case of [Stacks, Tag 0BJY]: if `A` is universally catenary and the formal
fibres of its local rings satisfy Serre's condition `(Sₙ)`, then `R^pj_*ℱ` is coherent for all
`0 ≤ p < n` exactly when `n` is below the local cohomology finiteness cutoff `s_{A,I}(M)` of
[Stacks, Tag 0BJR].

## Main results

* `Stacks.LocalCohomologySequence.isCoherent_rightDerived_iff_finite_localCohomology` —
  **clause (3) of [Stacks, Tag 0BK0], the equivalence of (a) and (c)**.
* `Stacks.LocalCohomologySequence.lt_localCohomologyCutoff_iff_forall_isCoherent_rightDerived` —
  the cutoff criterion for coherence of the higher direct images.

## Implementation notes

The second result is the affine case of [Stacks, Tag 0BJY] with that tag's depth–dimension
condition written as the cutoff of [Stacks, Tag 0BJR] rather than as the minimum of the
expressions `depth_{𝒪_{X,x}}(ℱ_x) + dim(𝒪_{closure{x}, z})`. The same equivalence with that
minimum written out, over the pairs of primes of `A`, is
`Stacks.LocalCohomologySequence.forall_lt_depth_add_height_iff_forall_isCoherent_rightDerived`.
The two expressions are read on a scheme by
`AlgebraicGeometry.depth_stalk_eq_depth_localizedModule`, which reads the depth of a stalk on an
affine open as the depth of the localized sections, and by
`topCodim_closureSingleton_eq_height_map_quotientMk`, which reads `dim(𝒪_{closure{p}, q})` on
`Spec A` as the height of the image of `q` in `A ⧸ p`.

Coherence of `R^pj_*ℱ` is local on the base:
`AlgebraicGeometry.CoherentImageLocalBase.isCoherent_rightDerived_of_cover` assumes nothing of
the morphism, the module or the base, being built from [Stacks, Tag 01E5] for schemes,
`AlgebraicGeometry.ProjectiveCoherentImage.higherDirectImageRestrictIsoScheme`, together with
`AlgebraicGeometry.Modules.isCoherent_of_restrict`. Passing from an affine `X` to a locally
Noetherian one additionally requires the identification of an affine open of `X` with a `Spec`
and of its part of the complement with a `zeroLocusCompl`.

Every coherent `𝒪_U`-module is of the form `M̃|_U` for some finite `A`-module `M`, by clause (1)
of [Stacks, Tag 0BK0], available as
`AlgebraicGeometry.exists_finiteModule_tilde_restrict_zeroLocusCompl`; the statements below fix
`M` instead, because the cutoff is a function of `M`.

## References

* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0BJR](https://stacks.math.columbia.edu/tag/0BJR)
* [Stacks Project, Tag 0BJW](https://stacks.math.columbia.edu/tag/0BJW)
* [Stacks Project, Tag 0BJY](https://stacks.math.columbia.edu/tag/0BJY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.LocalCohomologyTilde

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.LocalCohomologySequence

variable {A : CommRingCat.{u}}

/-- **[Stacks, Tag 0BK0] (3), the equivalence of (a) and (c).** Let `A` be a Noetherian ring,
`I ⊆ A` an ideal, `X = Spec A`, `Z = V(I)`, `U = X ∖ Z` and `j : U → X` the inclusion. For a
finite `A`-module `M` and any `p ≥ 0` the higher direct image `R^pj_*(M̃|_U)` is coherent if and
only if the local cohomology `H^{p+1}_Z(M)` is a finite `A`-module.

This is the composite of the tag's (a) ⟺ (b), which is
`moduleFinite_complementCohomologyBase_iff_isCoherent`, with its (b) ⟺ (c), which is
`finite_complementCohomologyBase_iff_finite_localCohomology`; the intermediate module is
`H^p(U, M̃)` in both. -/
@[stacks 0BK0 "(3), (a) ⟺ (c)"]
public theorem isCoherent_rightDerived_iff_finite_localCohomology [IsNoetherianRing A]
    (I : Ideal A) (M : ModuleCat.{u} A) [Module.Finite A M] (p : ℕ) :
    (((Scheme.Modules.pushforward (zeroLocusCompl I).ι).rightDerived p).obj
        ((tilde M).restrict (zeroLocusCompl I).ι)).IsCoherent ↔
      Module.Finite A (Stacks.LocalCohomology.localCohomologyWithSupportIn.{u, u} A
        (PrimeSpectrum.zeroLocus (I : Set A))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ((p + 1 : ℕ) : ℤ)) :=
  (moduleFinite_complementCohomologyBase_iff_isCoherent I M p).symm.trans
    (finite_complementCohomologyBase_iff_finite_localCohomology I M p)

/-- **The affine case of [Stacks, Tag 0BJY].** Let `A` be a universally catenary Noetherian
ring, `I ⊆ A` an ideal, `U = Spec A ∖ V(I)`, `j : U → Spec A` the inclusion and `M` a finite
`A`-module. If the formal fibres of the local rings of `A` satisfy Serre's condition `(Sₙ)`,
then `R^pj_*(M̃|_U)` is coherent for every `0 ≤ p < n` exactly when `n` is strictly below the
local cohomology finiteness cutoff `s_{A,I}(M)` of [Stacks, Tag 0BJR].

The cutoff controls finiteness of `H^{p+1}_Z(M)` by [Stacks, Tag 0BJW], in the form
`Stacks.LocalCohomology.lt_localCohomologyCutoff_iff_forall_finite_succ`, and finiteness of
`H^{p+1}_Z(M)` is coherence of `R^pj_*(M̃|_U)` by clause (3) of [Stacks, Tag 0BK0]. -/
public theorem lt_localCohomologyCutoff_iff_forall_isCoherent_rightDerived [IsNoetherianRing A]
    (I : Ideal A) (M : ModuleCat.{u} A) [Module.Finite A M]
    (hA : Ring.IsUniversallyCatenary (ToType A)) (n : ℕ)
    (hformal : ∀ q : PrimeSpectrum (ToType A),
      Stacks.LocalCohomology.FormalFibersHavePropertySk (Localization.AtPrime q.asIdeal) n) :
    (n : ℕ∞) < Stacks.LocalCohomology.localCohomologyCutoff (ToType A) I M ↔
      ∀ p : ℕ, p < n →
        (((Scheme.Modules.pushforward (zeroLocusCompl I).ι).rightDerived p).obj
          ((tilde M).restrict (zeroLocusCompl I).ι)).IsCoherent :=
  (Stacks.LocalCohomology.lt_localCohomologyCutoff_iff_forall_finite_succ
      (ToType A) I M hA n hformal).trans
    (forall_congr' fun p => forall_congr' fun _ =>
      (isCoherent_rightDerived_iff_finite_localCohomology I M p).symm)

end Stacks.LocalCohomologySequence

end
