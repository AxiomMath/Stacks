module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import StacksFrontier.RingTheory.AdicCompletion.ShortExact
public import StacksFrontier.RingTheory.Length.Finiteness

/-!
# Completing a quotient of finite length

Let `R` be a commutative local ring with maximal ideal `m` and let `f : M →ₗ[R] N` be an
injective linear map whose cokernel `N / f(M)` has finite length.  Then `m`-adic completion does
not change that cokernel: the canonical map identifies `N / f(M)` with `N^∧ / f^∧(M^∧)`, and it
is the only `R`-linear isomorphism between the two that is compatible with the completion maps.

Finite length is used only through the power of `m` that annihilates the cokernel: that is
exactly the hypothesis of [Stacks, Tag 0BNG](https://stacks.math.columbia.edu/tag/0BNG), which
says that completing `0 → M → N → N/f(M) → 0` keeps it short exact and leaves the third term
alone.  So `N^∧ / f^∧(M^∧)` is the completion of `N/f(M)`, which is `N/f(M)` itself.

## Main results

* `AdicCompletion.existsUnique_linearEquiv_quotientRange_of_isFiniteLength`.

## Implementation notes

The target is written `AdicCompletion m N ⧸ LinearMap.range (AdicCompletion.map m f)` rather
than with an abstractly chosen submodule, and the isomorphism is pinned by its compatibility
with `AdicCompletion.of`, so the conclusion is a `∃!` and not a bare existence statement.  The
isomorphism is `R`-linear; `AdicCompletion.map m f` is `R^∧`-linear, and the equivalence is
obtained by restricting scalars along `R → R^∧`.

The two modules live in independent universes and `R` is not assumed Noetherian, since the
proof uses neither.

## References

* [Stacks Project, Tag 0BNG](https://stacks.math.columbia.edu/tag/0BNG)
* [Stacks Project, Tag 00IW](https://stacks.math.columbia.edu/tag/00IW) for the power of the
  maximal ideal annihilating a module of finite length
-/

@[expose] public noncomputable section

namespace AdicCompletion

/-- A quotient of finite length over a local ring is unchanged by adic completion: there is
exactly one `R`-linear isomorphism `N / f(M) ≅ N^∧ / f^∧(M^∧)` compatible with the canonical
maps to the completions. -/
public theorem existsUnique_linearEquiv_quotientRange_of_isFiniteLength
    {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (hf : Function.Injective f)
    (hFL : IsFiniteLength R (N ⧸ LinearMap.range f)) :
    ∃! e : (N ⧸ LinearMap.range f) ≃ₗ[R]
        (AdicCompletion (IsLocalRing.maximalIdeal R) N ⧸
          LinearMap.range (AdicCompletion.map (IsLocalRing.maximalIdeal R) f)),
      ∀ a : N, e (Submodule.mkQ _ a) =
        Submodule.mkQ _ (AdicCompletion.of (IsLocalRing.maximalIdeal R) N a) := by
  classical
  set I := IsLocalRing.maximalIdeal R
  set g := (LinearMap.range f).mkQ with hg
  obtain ⟨n, hpow⟩ := exists_pow_maximalIdeal_smul_eq_bot_of_isFiniteLength R
    (N ⧸ LinearMap.range f) hFL
  obtain ⟨-, hexact, hsurj, hcomplete⟩ :=
    map_shortExact_and_isAdicComplete_of_pow_smul_top_eq_bot (I := I) (f := f) (g := g) hf
      (LinearMap.exact_map_mkQ_range f) (Submodule.mkQ_surjective _) hpow
  let : IsAdicComplete I (N ⧸ LinearMap.range f) := hcomplete
  -- The completed sequence identifies the target with the completion of the quotient.
  let qc : (AdicCompletion I N ⧸ LinearMap.range (map I f)) ≃ₗ[AdicCompletion I R]
      AdicCompletion I (N ⧸ LinearMap.range f) :=
    (Submodule.quotEquivOfEq _ _ (LinearMap.exact_iff.mp hexact).symm).trans
      ((map I g).quotKerEquivOfSurjective hsurj)
  let e : (N ⧸ LinearMap.range f) ≃ₗ[R]
      (AdicCompletion I N ⧸ LinearMap.range (map I f)) :=
    (ofLinearEquiv I (N ⧸ LinearMap.range f)).trans (qc.restrictScalars R).symm
  have he : ∀ a : N, e (Submodule.mkQ _ a) =
      Submodule.mkQ _ (AdicCompletion.of I N a) := by
    intro a
    apply (qc.restrictScalars R).injective
    simp [e, qc, ofLinearEquiv, AdicCompletion.map_of, hg]
  refine ⟨e, he, fun e' he' => LinearEquiv.ext fun z => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range f) z
  exact (he' a).trans (he a).symm

end AdicCompletion

end
