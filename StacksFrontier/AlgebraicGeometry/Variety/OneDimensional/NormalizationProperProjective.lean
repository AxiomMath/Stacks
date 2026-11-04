module

public import StacksFrontier.AlgebraicGeometry.AmplePullback.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.QuasiProjectiveOverAmpleBase
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.AmpleTwistingSheaf
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationOverField

/-!
# The normalization of a proper scheme over a field is proper, and projective if the scheme is

Let `k` be a field, let `X` be proper over `k` and let `ν : X^ν ⟶ X` be the normalization
morphism. Then `X^ν` is proper over `k`, and if `X` is projective over `k` then so is `X^ν`.

## Main results

* `AlgebraicGeometry.isProper_and_isProjective_normalizationOverField`: **[Stacks, Tag 0GK4]**,
  both assertions of the source in one statement. Projectivity of `X` is an implication inside
  the conclusion, not a hypothesis, so the properness assertion is stated at the source's own
  hypotheses.

## The argument

Properness is `AlgebraicGeometry.isProper_normalizationOverField_comp`: the normalization
morphism is finite, hence proper, and a composition of proper morphisms is proper.

Projectivity goes through an ample invertible module on `X^ν`, which is where the finiteness of
`ν` is used a second time.

* The base `Spec k` is affine, so projectivity of `X` over `k` is H-projectivity
  (`AlgebraicGeometry.isProjective_iff_isProjectiveMorphism_of_isAffine`, [Stacks, Tag 01WB] over
  an affine base): there is a closed immersion `i : X ⟶ ℙⁿ_k` for some `n`.
* `𝒪(1)` is ample on `ℙⁿ_k`, the base being affine
  (`Stacks.ProjectiveSpace.isAmple_projectiveSpaceTwistingSheaf`).
* `ν ≫ i` is an affine morphism — `ν` is finite and `i` is a closed immersion — and ampleness
  pulls back along an affine morphism with no further hypothesis, which is [Stacks, Tag 0B3E] in
  the form `Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom`. So `(ν ≫ i)^* 𝒪(1)` is
  an ample invertible module on `X^ν`.
* `X^ν ⟶ Spec k` is of finite type and quasi-compact, so [Stacks, Tag 01VS] in the form
  `AlgebraicGeometry.isHQuasiProjective_of_exists_isAmple` makes it H-quasi-projective; it is
  proper by the first assertion, so clause (2) of [Stacks, Tag 0BCL],
  `AlgebraicGeometry.isProjectiveMorphism_iff_isHQuasiProjective_and_isProper`, makes it
  H-projective, hence projective by [Stacks, Tag 01W9].

This is the route of
`StacksFrontier/AlgebraicGeometry/Variety/Curve/ProjectiveCompletionDiscreteValuation.lean` rather
than the source's. The source makes `ν` itself a projective morphism over `X` and composes, which
needs [Stacks, Tag 0B3I] over the non-affine base `X`; that tag is available here only on the
hypothesis `Stacks.FiniteMorphismProjective.PushforwardIsRelativeProj`. Embedding `X^ν` directly
into a projective space over `k` avoids it: the base `Spec k` is affine, and that is the only
thing the affine-morphism case of Tag 0B3E needs.

## References

* [Stacks Project, Tag 0GK4](https://stacks.math.columbia.edu/tag/0GK4)
* [Stacks Project, Tag 01WB](https://stacks.math.columbia.edu/tag/01WB)
* [Stacks Project, Tag 0B3E](https://stacks.math.columbia.edu/tag/0B3E)
* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 0BCL](https://stacks.math.columbia.edu/tag/0BCL)
* [Stacks Project, Tag 01W9](https://stacks.math.columbia.edu/tag/01W9)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0GK4.** Let `k` be a field, let `X` be a proper scheme over `k` and let
`ν : X^ν ⟶ X` be the normalization morphism. Then `X^ν` is proper over `k`, and if `X` is
projective over `k` then `X^ν` is projective over `k`.

Projectivity of `X` is an implication inside the conclusion: the properness assertion holds at
the source's own hypotheses, with nothing assumed about projectivity. Over the affine base
`Spec k` projectivity and H-projectivity agree ([Stacks, Tag 01WB]), so the implication may be
read with either notion. -/
@[stacks 0GK4]
public theorem isProper_and_isProjective_normalizationOverField (k : Type u) [Field k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p] :
    IsProper (normalizationOverField k p ≫ p) ∧
      (IsProjective p → IsProjective (normalizationOverField k p ≫ p)) := by
  let : LocallyOfFiniteType p := IsProper.toLocallyOfFiniteType
  let := isFinite_normalizationOverField k p
  have hproper : IsProper (normalizationOverField k p ≫ p) :=
    isProper_normalizationOverField_comp k p
  refine ⟨hproper, fun hproj => ?_⟩
  obtain ⟨n, i, hi, -⟩ := (isProjective_iff_isProjectiveMorphism_of_isAffine p).mp hproj
  have : IsClosedImmersion i := hi
  have hample : ∃ (L : (normalizationSchemeOverField k p).Modules)
      (hL : Stacks.Ample.IsInvertibleModule (normalizationSchemeOverField k p) L),
      let : Stacks.Ample.IsInvertibleModule (normalizationSchemeOverField k p) L := hL
      Stacks.Ample.IsAmple (normalizationSchemeOverField k p) L :=
    ⟨Stacks.AmpleLocallyClosed.pullbackModule (normalizationOverField k p ≫ i)
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n (Spec (.of k))),
      inferInstance,
      Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom _ _
        (Stacks.ProjectiveSpace.isAmple_projectiveSpaceTwistingSheaf n (Spec (.of k)))⟩
  exact (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mpr
    ⟨isHQuasiProjective_of_exists_isAmple _ inferInstance inferInstance hample,
      hproper⟩).isProjective

end AlgebraicGeometry

end
