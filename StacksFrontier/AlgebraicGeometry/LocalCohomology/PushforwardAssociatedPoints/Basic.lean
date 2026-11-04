module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Defs

/-!
# Associated primes as embedded residue rings, and coherence of a direct image

A prime `𝔭` of a ring `R` is the annihilator of an element of an `R`-module `M` exactly when
`R ⧸ 𝔭` admits an injective `R`-linear map into `M`. If a quasi-coherent `𝒪_U`-module embeds in
an `𝒪_U`-module whose direct image along an open immersion into a locally Noetherian scheme is
coherent, then its own direct image is coherent.

## Main results

In the namespace `Stacks.AlgebraicGeometry.PushforwardAssociatedPoints`:

* `isAssociatedPrimeStacks_iff_exists_injective`: the characterisation of an associated prime by
  an embedding of its residue ring.
* `isCoherent_pushforward_of_mono`: the descent of coherence of a direct image along a
  monomorphism of `𝒪_U`-modules.

## References

* [Stacks Project, Tag 0BJZ](https://stacks.math.columbia.edu/tag/0BJZ)
* [Stacks Project, Tag 00LA](https://stacks.math.columbia.edu/tag/00LA)
* [Stacks Project, Tag 01Y1](https://stacks.math.columbia.edu/tag/01Y1)
* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.PushforwardAssociatedPoints

/-- A prime ideal `𝔭` of `R` is associated to the `R`-module `M` if and only if `R ⧸ 𝔭` admits an
injective `R`-linear map into `M`. -/
theorem isAssociatedPrimeStacks_iff_exists_injective {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] {p : Ideal R} :
    IsAssociatedPrimeStacks R M p ↔
      p.IsPrime ∧ ∃ f : (R ⧸ p) →ₗ[R] M, Function.Injective f := by
  refine and_congr_right fun _ =>
    ⟨fun ⟨m, hm⟩ => ?_, fun ⟨f, hf⟩ => ⟨f (Ideal.Quotient.mk p 1), ?_⟩⟩
  · have hker : LinearMap.ker (LinearMap.toSpanSingleton R M m) = p := by
      ext r
      rw [LinearMap.mem_ker, ← hm, Submodule.mem_colon_span_singleton]
      simp [LinearMap.toSpanSingleton_apply]
    refine ⟨Submodule.liftQ p (LinearMap.toSpanSingleton R M m) hker.ge, ?_⟩
    rw [← LinearMap.ker_eq_bot, Submodule.ker_liftQ_eq_bot]
    exact hker.le
  · have key : ∀ r : R, r • f (Ideal.Quotient.mk p 1) = f (Ideal.Quotient.mk p r) := fun r => by
      rw [← map_smul]
      congr 1
      simp [Algebra.smul_def]
    ext r
    rw [Submodule.mem_colon_span_singleton]
    simp only [Submodule.mem_bot, key r]
    rw [← map_zero f, hf.eq_iff, Ideal.Quotient.eq_zero_iff_mem]

/-- If a quasi-coherent `𝒪_U`-module `H` admits a monomorphism into an `𝒪_U`-module `F` whose
direct image along an open immersion `j : U ⟶ X` into a locally Noetherian scheme is coherent,
then the direct image of `H` along `j` is coherent. -/
theorem isCoherent_pushforward_of_mono {U X : Scheme.{u}} [IsLocallyNoetherian X] (j : U ⟶ X)
    [IsOpenImmersion j] {H F : U.Modules} [H.IsQuasicoherent] (φ : H ⟶ F) [Mono φ]
    (hF : ((Scheme.Modules.pushforward j).obj F).IsCoherent) :
    ((Scheme.Modules.pushforward j).obj H).IsCoherent := by
  exact Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_mono
    ((Scheme.Modules.pushforward j).map φ)

end Stacks.AlgebraicGeometry.PushforwardAssociatedPoints

end
