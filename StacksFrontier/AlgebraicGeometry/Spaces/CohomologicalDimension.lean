module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModules
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.VeryReasonableImpliesReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ZariskiLocallyQuasiSeparatedVeryReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCohomology

/-!
# Finite cohomological dimension of a quasi-compact quasi-separated algebraic space

A quasi-compact and quasi-separated algebraic space `X` carries a surjective étale morphism
`U ⟶ X` from an affine scheme whose fibres are universally bounded, and there is a single
integer `n = n(X)` beyond which the cohomology of *every* quasi-coherent `𝒪_X`-module vanishes:
`Hᑫ(X, 𝓕) = 0` for `q ≥ n`. This is [Stacks, Tag 072C], and the uniformity in `𝓕` is what makes
the Euler characteristic of a coherent module on a proper algebraic space over a field a finite
alternating sum.

## Main results

* `AlgebraicGeometry.Space.exists_affine_etale_surjective_cover_hasUniversallyBoundedFibers`:
  the choices (1)–(3) of [Stacks, Tag 072C] — an affine scheme `U`, a surjective étale morphism
  `U ⟶ X`, and a universal bound on the degrees of its fibres.
* `AlgebraicGeometry.Space.exists_forall_isZero_cohomologyOverBase_of_isQuasiCompactSpace`: a
  single degree beyond which the cohomology over the base ring of every quasi-coherent
  `𝒪_X`-module vanishes, from such a degree for each affine chart with universally bounded
  fibres. This is a reduction taking the vanishing as a hypothesis, not [Stacks, Tag 072C].
* `AlgebraicGeometry.Space.exists_forall_isZero_cohomologyOverBase_of_isCoherent`: the same
  conditional bound read off for coherent modules, which is the form the additivity of the Euler
  characteristic consumes.

## Implementation notes

**The cohomology used.** `AlgebraicGeometry.Space.cohomologyOverBase` is cohomology of modules
on the small étale ringed site of `X` with scalars restricted to the base ring along
`AlgebraicGeometry.Space.baseRingHom`, so the vanishing is stated for an algebraic space over
`Spec A`; the quasi-coherence of a module is `SheafOfModules.IsQuasicoherentOnSite` on that
site, which is [Stacks, Tag 03DL], and coherence is `AlgebraicGeometry.Space.IsCoherent` of
[Stacks, Tag 07UA], whose parent projection supplies quasi-coherence.

**Where the choices come from.** The affine surjective étale chart is the forward direction of
`AlgebraicGeometry.Space.isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover`, which
is [Stacks, Tag 03H6]. The universal bound on its fibres is the composite
`(η) ⇒ (ζ) ⇒ (ε) ⇒ (δ)` of [Stacks, Tag 03JX] — quasi-separated, Zariski locally
quasi-separated, very reasonable, reasonable — followed by
`AlgebraicGeometry.Space.IsReasonableSpace.hasUniversallyBoundedFibers`; quasi-separatedness is
taken in the absolute form `AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated` of
[Stacks, Tag 03BS](3), which is why the ambient big fppf site must contain the terminal scheme.

**Where the full tag is.** This file only makes the choices (1)–(3), and its vanishing
statement for `cohomologyOverBase` reduces to a vanishing degree for a chart, taken as the
hypothesis `hvanish`.  The complete [Stacks, Tag 072C] — the choices (4)–(5) and the vanishing
`H^q(X, ℱ) = 0` for `q ≥ max (d_p + p)`, over an arbitrary base scheme — is
`AlgebraicGeometry.Space.exists_affine_etale_surjective_cover_diagonalComplementQuotient` and
`AlgebraicGeometry.Space.isZero_sheafH_of_boundsFibreDegrees_of_diagonalComplementQuotient`, under
`StacksDraft.AlgebraicGeometry.Spaces.AlternatingCech`.

## References

* [Stacks Project, Tag 072C](https://stacks.math.columbia.edu/tag/072C)
* [Stacks Project, Tag 072B](https://stacks.math.columbia.edu/tag/072B)
* [Stacks Project, Tag 072A](https://stacks.math.columbia.edu/tag/072A)
* [Stacks Project, Tag 0728](https://stacks.math.columbia.edu/tag/0728)
* [Stacks Project, Tag 0726](https://stacks.math.columbia.edu/tag/0726)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 03JL](https://stacks.math.columbia.edu/tag/03JL)
* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u w

namespace AlgebraicGeometry.Space

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u})
    (hA : B.Contains (Spec (.of A))) (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)

include hX in
/-- **The choices (1)–(3) of Stacks 072C.** A quasi-compact, quasi-separated algebraic space
carries a surjective étale morphism from an affine scheme whose fibres are universally bounded
in the sense of Stacks 03JL. -/
@[stacks 072C "parts (1)-(3): an affine scheme U, a surjective étale morphism U ⟶ X, and an \
integer bounding the degrees of its fibres"]
theorem exists_affine_etale_surjective_cover_hasUniversallyBoundedFibers
    (hqc : IsQuasiCompactSpace B (Spec (.of A)) hA X)
    (hqs : IsAbsolutelyQuasiSeparated B (Spec (.of A)) hA hZ X) :
    ∃ (U : BigFppfOver B (Spec (.of A)) hA) (g : yoneda.obj U ⟶ X),
      IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U) ∧
        (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B (Spec (.of A)) hA)).presheaf g ∧
        IsEtale B (Spec (.of A)) hA g ∧
        HasUniversallyBoundedFibers B (Spec (.of A)) hA U g := by
  obtain ⟨U, g, hU, hsurj, het⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B (Spec (.of A)) hA X hX).1 hqc
  refine ⟨U, g, hU, hsurj, het, ?_⟩
  refine IsReasonableSpace.hasUniversallyBoundedFibers B (Spec (.of A)) hA X
    (isReasonableSpace_of_isVeryReasonableSpace B (Spec (.of A)) hA X hX
      (isVeryReasonableSpace_of_isAbsolutelyZariskiLocallyQuasiSeparated B (Spec (.of A)) hA hZ
        X hX (isAbsolutelyZariskiLocallyQuasiSeparated_of_isAbsolutelyQuasiSeparated
          B (Spec (.of A)) hA X hZ hX hqs))) U hU g ?_
  exact (isEtale_iff_presheaf_of_yoneda B (Spec (.of A)) hA g).1 het

/-- On a quasi-compact, quasi-separated algebraic space over `Spec A`, if every affine étale
surjective chart with universally bounded fibres gives a single degree beyond which the
cohomology over `A` of every quasi-coherent `𝒪_X`-module vanishes, then there is such a degree.
The chart exists by
`AlgebraicGeometry.Space.exists_affine_etale_surjective_cover_hasUniversallyBoundedFibers`. -/
theorem exists_forall_isZero_cohomologyOverBase_of_isQuasiCompactSpace
    (hqc : IsQuasiCompactSpace B (Spec (.of A)) hA X)
    (hqs : IsAbsolutelyQuasiSeparated B (Spec (.of A)) hA hZ X)
    (hvanish : ∀ (U : BigFppfOver B (Spec (.of A)) hA) (g : yoneda.obj U ⟶ X),
      IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U) →
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (Spec (.of A)) hA)).presheaf g →
      IsEtale B (Spec (.of A)) hA g →
      HasUniversallyBoundedFibers B (Spec (.of A)) hA U g →
      ∃ N : ℕ, ∀ F : Modules.{u, max (u + 1) w} B (Spec (.of A)) hA X hX,
        F.IsQuasicoherentOnSite → ∀ q, N ≤ q →
          IsZero (cohomologyOverBase.{u, w} A B hA X hX F q)) :
    ∃ N : ℕ, ∀ F : Modules.{u, max (u + 1) w} B (Spec (.of A)) hA X hX,
      F.IsQuasicoherentOnSite → ∀ q, N ≤ q →
        IsZero (cohomologyOverBase.{u, w} A B hA X hX F q) := by
  obtain ⟨U, g, hU, hsurj, het, hbd⟩ :=
    exists_affine_etale_surjective_cover_hasUniversallyBoundedFibers.{u} A B hA hZ X hX hqc hqs
  exact hvanish U g hU hsurj het hbd

/-- The conditional bound of
`AlgebraicGeometry.Space.exists_forall_isZero_cohomologyOverBase_of_isQuasiCompactSpace`, read off
for coherent modules: a coherent module is quasi-coherent, being an extension of that condition.
Like that statement it takes the vanishing for a chart as the hypothesis `hvanish`, so it is not
[Stacks, Tag 072C] itself; the unconditional vanishing is
`AlgebraicGeometry.Space.isZero_sheafH_of_boundsFibreDegrees_of_diagonalComplementQuotient`. -/
theorem exists_forall_isZero_cohomologyOverBase_of_isCoherent
    (hqc : IsQuasiCompactSpace B (Spec (.of A)) hA X)
    (hqs : IsAbsolutelyQuasiSeparated B (Spec (.of A)) hA hZ X)
    (hvanish : ∀ (U : BigFppfOver B (Spec (.of A)) hA) (g : yoneda.obj U ⟶ X),
      IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U) →
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (Spec (.of A)) hA)).presheaf g →
      IsEtale B (Spec (.of A)) hA g →
      HasUniversallyBoundedFibers B (Spec (.of A)) hA U g →
      ∃ N : ℕ, ∀ F : Modules.{u, max (u + 1) w} B (Spec (.of A)) hA X hX,
        F.IsQuasicoherentOnSite → ∀ q, N ≤ q →
          IsZero (cohomologyOverBase.{u, w} A B hA X hX F q)) :
    ∃ N : ℕ, ∀ F : Modules.{u, max (u + 1) w} B (Spec (.of A)) hA X hX,
      IsCoherent B (Spec (.of A)) hA X hX F → ∀ q, N ≤ q →
        IsZero (cohomologyOverBase.{u, w} A B hA X hX F q) := by
  obtain ⟨N, hN⟩ := exists_forall_isZero_cohomologyOverBase_of_isQuasiCompactSpace.{u, w}
    A B hA hZ X hX hqc hqs hvanish
  exact ⟨N, fun F hF => hN F hF.toIsQuasicoherentOnSite⟩

end AlgebraicGeometry.Space

end
