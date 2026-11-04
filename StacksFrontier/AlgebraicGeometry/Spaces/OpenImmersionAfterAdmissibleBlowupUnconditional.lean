module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismClosedImmersionLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ProperLimitOfFinitePresentationEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionAfterAdmissibleBlowup

/-!
# A finite type separated modification becomes an open immersion after an admissible blowup

Let `f : X ⟶ A` be a morphism of algebraic spaces and let `U ⊆ A` be an open subspace.  Assume
that `A` is quasi-compact and quasi-separated, that `U` is quasi-compact, that `f` is of finite
type and separated, and that `f⁻¹(U) ⟶ U` is an isomorphism.  Then there is a `U`-admissible
blowup `A' ⟶ A` such that `U` is scheme-theoretically dense in `A'` and the strict transform
of `X` maps isomorphically to an open subspace of `A'`.  This is [Stacks, Tag 087F] with the
hypothesis that `f` be separated added: as published, without it, the statement is false.

**The counterexample.**  Let `k` be a field, `A = 𝐀¹_k`, `U = 𝐀¹_k ∖ {0}`, and let `X` be the
affine line with doubled origin, with its morphism to `𝐀¹_k`.  Then `f` is of finite type, and
an isomorphism over `U`.  A `U`-admissible blowup of `𝐀¹_k` is the blowup in a closed subscheme
`V(xⁿ)`, an effective Cartier divisor of a regular curve, hence an isomorphism; and since `X` is
integral, the strict transform of `X` is `X` itself.  But `X ⟶ 𝐀¹_k` is not an open immersion,
not being injective.  The source's proof breaks where it applies Stacks 0879, which assumes `f`
separated.  Every use of Stacks 087F in the source (Stacks 088Q, 0F47, 0F4A) applies it to a
separated morphism.

## Main results

* `AlgebraicGeometry.Space.exists_isBlowupAlong_isOpenImmersion_strictTransformSpaceToBlowUp_unconditional`:
  the corrected statement of Stacks 087F.

## Implementation notes

This is `AlgebraicGeometry.Space.exists_isBlowupAlong_isOpenImmersion_strictTransformSpaceToBlowUp`
with its two inputs supplied by the library: Stacks 07VR is
`AlgebraicGeometry.Space.exists_integralFiniteSystem_isClosedImmersion_of_isFinite` and Stacks
0873 is
`AlgebraicGeometry.Space.exists_isClosedImmersion_isSeparated_isFinitePresentation_of_isFiniteType`.

## References

* [Stacks Project, Tag 087F](https://stacks.math.columbia.edu/tag/087F)
* [Stacks Project, Tag 0879](https://stacks.math.columbia.edu/tag/0879)
* [Stacks Project, Tag 07VR](https://stacks.math.columbia.edu/tag/07VR)
* [Stacks Project, Tag 0873](https://stacks.math.columbia.edu/tag/0873)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 087F, corrected.**  Let `f : X ⟶ A` be a morphism of algebraic spaces over `S` and
let `U ⊆ A` be an open subspace.  Assume that `A` is quasi-compact and quasi-separated, that `U`
is quasi-compact, that `f` is of finite type **and separated**, and that `f⁻¹(U) ⟶ U` is an
isomorphism.  Then there is a `U`-admissible blowup `b : A' ⟶ A`, with centre `Z`, such that
`b⁻¹(U)` is scheme-theoretically dense in `A'` and the strict transform of `X` is an open
immersion into `A'`.

Without separatedness the statement is false; see the module documentation. -/
@[stacks 087F "corrected: f separated; as published the statement is false (the affine line with \
doubled origin over 𝐀¹, with U = 𝐀¹ minus the origin)"]
theorem exists_isBlowupAlong_isOpenImmersion_strictTransformSpaceToBlowUp_unconditional
    (hZ : B.Contains (⊤_ Scheme.{u})) {A X : AlgebraicSpaces B S hS} (f : X ⟶ A)
    (U : OpenSubspaces B S hS A.1)
    (hAqc : IsQuasiCompactSpace B S hS A.1) (hAqs : IsAbsolutelyQuasiSeparated B S hS hZ A.1)
    (hUqc : IsQuasiCompactSpace B S hS U.1.toFunctor)
    (hft : IsFiniteType B S hS f.hom) (hsep : IsSeparated B S hS f.hom)
    (hiso : IsIso (pullback.snd f.hom U.1.ι)) :
    ∃ (A' : AlgebraicSpaces B S hS) (b : A' ⟶ A) (Z : ClosedSubspaces B S hS A.1),
      IsFinitePresentation B S hS Z.1.ι ∧
        Disjoint (subspacePointSet B S hS A.1 U.1) (subspacePointSet B S hS A.1 Z.1) ∧
          IsBlowupAlong B S hS Z b ∧
            IsSchemeTheoreticallyDense B S hS (U.1.preimage b.hom) ∧
              IsOpenImmersion B S hS
                (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)).hom :=
  exists_isBlowupAlong_isOpenImmersion_strictTransformSpaceToBlowUp hZ f U hAqc hAqs hUqc hft hsep
    hiso
    (fun g hX hY hf hqc hqs => exists_integralFiniteSystem_isClosedImmersion_of_isFinite g hX hY hf
      hqc hqs)
    (fun f hX hY hft hsep hqc hqs => by
      obtain ⟨X', i, f', hX', hi, hf'sep, hf'fp, hif⟩ :=
        exists_isClosedImmersion_isSeparated_isFinitePresentation_of_isFiniteType B S hS hX hY f
          hft hsep hqc hqs
      exact ⟨X', f', i, hX', hf'sep, hf'fp, hi, hif⟩)

end AlgebraicGeometry.Space
