module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.ExternalTensor.SingleComparison
public import StacksFrontier.AlgebraicGeometry.Duality.IdentityKernelNaturalPullback
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FibreTensorStalkInstance
import StacksCore.Tactic.StacksAttribute

/-!
# Step 2 of the proof of Tag 0G0E: the kernel has no cohomology outside degree zero

Let `k` be a field, let `X` be a smooth proper `k`-scheme and let `K` be a perfect object of
`D(𝒪_{X ×_k X})` whose Fourier-Mukai functor induces on `D_perf(𝒪_X)` an endofunctor isomorphic
to the identity.  This file proves

`H^i(K) = 0` for every `i ≠ 0`,

which is steps 1 and 2 of the proof of [Stacks, Tag 0G0E] together; what the source's second step
adds to its first is the vanishing in positive degrees, and that is what this file contributes.

## Main definitions

* `AlgebraicGeometry.fibreTransformIsoFourierMukai` — for a flat first projection, the integral
  transform `R pr_{2,*}(pr_1^*𝓕 ⊗^𝐋 K)` of [Stacks, Tag 0FZ9] is the Fourier-Mukai functor of
  [Stacks, Tag 0FYQ] at `𝓕[0]`.

## Main results

* `Stacks.Duality.isZero_homology_of_ne_zero_of_representsIdentityOnPerfect` — **steps 1 and 2 of
  [Stacks, Tag 0G0E]**: `H^i(K) = 0` for `i ≠ 0`.
* `Stacks.Duality.isLE_zero_of_representsIdentityOnPerfect` — **step 2 of [Stacks, Tag 0G0E]**:
  `K.IsLE 0`.

## Implementation notes

*The route is not the source's display.*  The source runs its second step on the displayed
computation of `H^i(X × X, K ⊗^𝐋 (ℰ ⊠ 𝒢))` at the maximal nonvanishing degree, with `ℰ` and `𝒢`
of zero-dimensional support.  Along that display the top-degree hypercohomology edge is not
unconditional, and the identification of `H^i(K ⊗^𝐋 𝒩[0])` with `H^i(K) ⊗ 𝒩` for a `𝒩` that is
not flat is not available in this development.

Instead the vanishing criterion of [Stacks, Tag 0FZ9] is used, which is built on the adic
criterion [Stacks, Tag 0EGV] and consumes exactly the same test modules — the coherent
`𝒪_X`-modules of zero-dimensional support — but reads them through the conservativity of
`R pr_{2,*}` on complexes supported over an affine open of the first factor rather than through
the display.  That criterion is
`AlgebraicGeometry.isZero_homology_of_isZero_homology_fibreTransform`, and it needs no minimality:
it gives the vanishing degree by degree, so the induction that step 1 runs is not needed here and
both halves of the source's argument come out at once.

Its two inputs are discharged as follows.

* The bundle `AlgebraicGeometry.FibreTensorComparisons` is now unconditional,
  `AlgebraicGeometry.fibreTensorComparisonsOfPullback`.
* The hypothesis on the integral transforms is the tag's own hypothesis `Φ_K ≅ 𝟭`.  A coherent
  module `𝓕` on the regular `X` is perfect in degree zero
  (`AlgebraicGeometry.isPerfect_single_of_isCoherent_of_isRegular`, with
  `AlgebraicGeometry.isRegular_of_smooth_over_field`), so
  `Stacks.Duality.nonempty_natIso_fourierMukai_of_representsIdentityOnPerfect` gives
  `Φ_K(𝓕[0]) ≅ 𝓕[0]`, whose cohomology vanishes outside degree zero.  The integral transform of
  [Stacks, Tag 0FZ9] tensors with the *ordinary* pullback `pr_1^*𝓕` placed in degree zero while
  `Φ_K` tensors with the derived pullback of `𝓕[0]`; the two agree because `pr_1` is flat, being
  the base change of a morphism to the spectrum of a field, and that identification is
  `AlgebraicGeometry.fibreTransformIsoFourierMukai` below.

*Why the zero-dimensionality of the support is never used.*  The criterion of [Stacks, Tag 0FZ9]
asks for the vanishing only at the modules of zero-dimensional support, and the hypothesis
discharged here holds at *every* coherent module; the restriction is simply not consumed.

## References

* [Stacks Project, Tag 0G0E](https://stacks.math.columbia.edu/tag/0G0E)
* [Stacks Project, Tag 0FZ9](https://stacks.math.columbia.edu/tag/0FZ9)
* [Stacks Project, Tag 0FYQ](https://stacks.math.columbia.edu/tag/0FYQ)
* [Stacks Project, Tag 0EGV](https://stacks.math.columbia.edu/tag/0EGV)
* [Stacks Project, Tag 0FXU](https://stacks.math.columbia.edu/tag/0FXU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The integral transform of [Stacks, Tag 0FZ9] is the Fourier-Mukai functor of
[Stacks, Tag 0FYQ] at a module placed in degree zero**, when the first projection is flat.

`AlgebraicGeometry.fibreTransform` tensors the kernel with the *ordinary* pullback `pr_1^*𝓕`
placed in degree zero, while `AlgebraicGeometry.fourierMukai` tensors it with the derived
pullback of `𝓕[0]`; for a flat `pr_1` the two agree, by
`AlgebraicGeometry.derivedPullbackSingleIsoOfFlat`. -/
def fibreTransformIsoFourierMukai {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [Flat (Limits.pullback.fst f g)] (K : DerivedCategory (Limits.pullback f g).Modules)
    (F : X.Modules) :
    fibreTransform f g K F ≅
      (fourierMukai f g K).obj ((DerivedCategory.singleFunctor X.Modules 0).obj F) :=
  (fourierMukaiPushforward f g).mapIso ((fourierMukaiTensor f g K).mapIso
    (derivedPullbackSingleIsoOfFlat (Limits.pullback.fst f g) F).symm)

end AlgebraicGeometry

namespace Stacks.Duality

attribute [local instance 10000] HasDerivedCategory.standard

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] [IsProper f]

/-- **Steps 1 and 2 of the proof of [Stacks, Tag 0G0E]**: a perfect object `K` of
`D(𝒪_{X ×_k X})` whose Fourier-Mukai functor induces on `D_perf(𝒪_X)` an endofunctor isomorphic
to the identity has no cohomology outside degree zero.

The vanishing criterion of [Stacks, Tag 0FZ9] reduces this to the vanishing of the cohomology of
the integral transforms of the coherent modules of zero-dimensional support, and those
transforms are `Φ_K(𝓕[0]) ≅ 𝓕[0]`.  See the implementation notes of this file. -/
theorem isZero_homology_of_ne_zero_of_representsIdentityOnPerfect
    (K : DerivedCategory (Limits.pullback f f).Modules)
    (hK : perfectDerivedObjects (Limits.pullback f f) K)
    (hΦ : RepresentsIdentityOnPerfect f K) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (Limits.pullback f f).Modules i).obj K) := by
  have hreg : IsRegular X := isRegular_of_smooth_over_field f
  have : IsNoetherian (Spec (CommRingCat.of k)) :=
    isNoetherian_Spec.mpr (inferInstanceAs (IsNoetherianRing k))
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  have := isNoetherian_pullback_self f
  obtain ⟨b, hb⟩ :=
    (Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect
      (Limits.pullback f f) K hK).1.2
  refine isZero_homology_of_isZero_homology_fibreTransform f f
    (fibreTensorComparisonsOfPullback f f) K hK b (fun j hj => hb j hj) i ?_
  intro F hF _
  have hperf : perfectDerivedObjects X ((DerivedCategory.singleFunctor X.Modules 0).obj F) :=
    perfectDerivedObjects_single_of_coherentObjects hreg ⟨F, hF⟩
  have hzero : IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj F)) := by
    rcases lt_or_gt_of_ne hi with h | h
    · exact DerivedCategory.isZero_of_isGE _ 0 i h
    · exact DerivedCategory.isZero_of_isLE _ 0 i h
  refine (nonempty_natIso_fourierMukai_of_representsIdentityOnPerfect f K hΦ).elim fun e => ?_
  exact hzero.of_iso ((DerivedCategory.homologyFunctor X.Modules i).mapIso
    (fibreTransformIsoFourierMukai f f K F ≪≫ e.app ⟨_, hperf⟩))

/-- **Step 2 of the proof of [Stacks, Tag 0G0E]**: a perfect object `K` of `D(𝒪_{X ×_k X})` whose
Fourier-Mukai functor induces on `D_perf(𝒪_X)` an endofunctor isomorphic to the identity has no
cohomology above degree zero. -/
theorem isLE_zero_of_representsIdentityOnPerfect
    (K : DerivedCategory (Limits.pullback f f).Modules)
    (hK : perfectDerivedObjects (Limits.pullback f f) K)
    (hΦ : RepresentsIdentityOnPerfect f K) :
    K.IsLE 0 :=
  (DerivedCategory.isLE_iff K 0).2 fun j hj =>
    isZero_homology_of_ne_zero_of_representsIdentityOnPerfect f K hK hΦ j hj.ne'

end Stacks.Duality

end
