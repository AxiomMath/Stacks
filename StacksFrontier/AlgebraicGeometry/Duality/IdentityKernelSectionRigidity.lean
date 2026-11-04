module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.ClosedImmersionKernel
public import StacksFrontier.AlgebraicGeometry.Duality.IdentityKernelReduction
public import StacksFrontier.AlgebraicGeometry.Duality.PullbackIdentityRigidity
public import StacksFrontier.AlgebraicGeometry.Perfect.RegularCoherentPerfect
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular

/-!
# A section realising the identity kernel is the diagonal on points

Let `X` be a smooth proper scheme over a field `k`, let `K` be an object of `D(𝒪_{X ×_k X})` whose
Fourier-Mukai functor induces on `D_perf(𝒪_X)` an endofunctor isomorphic to the identity, and
suppose `K ≅ Rs_*𝒪_X` for a morphism `s : X ⟶ X ×_k X` sectioning the second projection.  Then

`pr_1 ∘ s` is the identity on the underlying topological space of `X`.

This is the topological content of the step the proof of [Stacks, Tag 0G0E] leaves implicit, the
one its text disposes of with "and this can happen only if `s` is the diagonal morphism".

## Main results

* `AlgebraicGeometry.base_comp_fst_eq_self_of_representsIdentityOnPerfect` — the statement above.

## Implementation notes

The chain is short because each of its three links is now available.

1. `AlgebraicGeometry.fourierMukaiIsoDerivedPullback_of_comp_snd_eq_id` identifies `Φ_{Rs_*𝒪_X}`
   with `L(pr_1 ∘ s)^*`, for a section of the second projection of a separated `f`.  Composed
   with `K ≅ Rs_*𝒪_X` and with the isomorphism `Φ_K ≅ 𝟭` of
   `Stacks.Duality.RepresentsIdentityOnPerfect`, read at a perfect object, this gives
   `L(pr_1 ∘ s)^* M ≅ M` for every perfect `M`.
2. A coherent module on a regular scheme is perfect in degree zero
   (`AlgebraicGeometry.isPerfect_single_of_isCoherent_of_isRegular`), and `X` smooth over a field
   is regular (`AlgebraicGeometry.isRegular_of_smooth_over_field`), so the previous step applies
   to the single complex of every coherent `𝒪_X`-module.
3. `Stacks.Duality.base_eq_self_of_forall_iso_derivedPullback_single` turns that into the
   conclusion: taking degree-zero cohomology gives `(pr_1 ∘ s)^*ℱ ≅ ℱ` for every coherent `ℱ`,
   whence every closed subset of `X` is its own inverse image and `pr_1 ∘ s` fixes every point.

*Which hypotheses are consumed.*  Perfectness of `K` is not used: the isomorphism `Φ_K ≅ 𝟭` on
`D_perf(𝒪_X)` and the identification of `K` with `Rs_*𝒪_X` are what the argument reads.  Nor is
properness of `f` used for more than separatedness — needed for a section of `pr_2` to be a closed
immersion — and Noetherianness of `X`, needed so that `𝒪_X/ℐ_Z` is coherent.

*What this leaves for `pr_1 ∘ s = 𝟙`, and where it is done.*  Only the comorphism.  The
conclusion here is an equality of continuous maps, and a morphism of schemes inducing the identity
on the underlying space need not be the identity — on `𝔸^1` over `𝔽_p` the Frobenius `t ↦ t^p`
induces the identity map of the spectrum.  What rules that out is the module-level hypothesis
rather than the topological conclusion, and it is proved in
`StacksFrontier/AlgebraicGeometry/Duality/IdentityKernelComorphism.lean`: a *natural* isomorphism
`g^* ≅ 𝟭` on coherent modules forces `g^♯_x` to induce the identity of `κ(x)` at every fixed
closed point.  `Stacks.Duality.comp_fst_eq_id_of_representsIdentityOnPerfect` is the full
conclusion `pr_1 ∘ s = 𝟙 X` under the hypotheses of Tag 0G0E together with `K ≅ Rs_*𝒪_X`.

## References

* [Stacks Project, Tag 0G0E](https://stacks.math.columbia.edu/tag/0G0E)
* [Stacks Project, Tag 0FDC](https://stacks.math.columbia.edu/tag/0FDC)
* [Stacks Project, Tag 056S](https://stacks.math.columbia.edu/tag/056S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.DerivedTensor.RingedSite

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

/-- **A section of the second projection whose direct image represents the identity on perfect
complexes composes with the first projection to the identity on points.**

For `X` smooth and proper over a field `k`, an object `K` of `D(𝒪_{X ×_k X})` whose Fourier-Mukai
functor induces on `D_perf(𝒪_X)` an endofunctor isomorphic to the identity, and a morphism
`s : X ⟶ X ×_k X` with `s ≫ pr_2 = 𝟙` and `K ≅ Rs_*𝒪_X`, the morphism `pr_1 ∘ s` fixes every
point of `X`.

This is the topological half of the second step of step 4 of the proof of [Stacks, Tag 0G0E]; see
the implementation notes of this file for what separates it from `pr_1 ∘ s = 𝟙`. -/
theorem base_comp_fst_eq_self_of_representsIdentityOnPerfect
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] [IsProper f]
    (K : DerivedCategory (Limits.pullback f f).Modules)
    (hΦ : Stacks.Duality.RepresentsIdentityOnPerfect f K)
    (s : X ⟶ Limits.pullback f f) (hsnd : s ≫ Limits.pullback.snd f f = 𝟙 X)
    (eK : K ≅ (dpush s).obj (derivedUnitObject X)) (x : X) :
    (s ≫ Limits.pullback.fst f f).base x = x := by
  obtain ⟨_, ⟨eid⟩⟩ := hΦ
  have hreg : IsRegular X := isRegular_of_smooth_over_field f
  have : IsNoetherian (Spec (CommRingCat.of k)) :=
    isNoetherian_Spec.mpr (inferInstanceAs (IsNoetherianRing k))
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  refine Stacks.Duality.base_eq_self_of_forall_iso_derivedPullback_single
    (s ≫ Limits.pullback.fst f f) (fun F hF => ?_) x
  have := hF
  have hM : Stacks.Duality.perfectDerivedObjects X
      ((DerivedCategory.singleFunctor X.Modules 0).obj F) :=
    isPerfect_single_of_isCoherent_of_isRegular hreg F
  have e1 := (Stacks.Duality.perfectDerivedObjects X).ι.mapIso (eid.app ⟨_, hM⟩)
  have e2 := ((derivedTensorProductFunctor
      (Limits.pullback f f).toRingedSpace.sheaf).flip.mapIso eK).app
    ((fourierMukaiPullback f f).obj ((DerivedCategory.singleFunctor X.Modules 0).obj F))
  have e3 := (fourierMukaiIsoDerivedPullback_of_comp_snd_eq_id f f s hsnd).app
    ((DerivedCategory.singleFunctor X.Modules 0).obj F)
  exact ⟨e3.symm ≪≫ ((fourierMukaiPushforward f f).mapIso e2).symm ≪≫ e1⟩

end AlgebraicGeometry

end
