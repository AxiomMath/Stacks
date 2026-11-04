module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.NaiveCotangent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Finite
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.QuasiFiniteNaiveCotangent
public import StacksCore.Tactic.StacksAttribute

/-!
# The naive cotangent complex of a finite syntomic morphism

A finite morphism of schemes is syntomic exactly when it is flat, locally of finite presentation
and its naive cotangent complex `NL_{Y/X}` has Tor amplitude in `[-1, 0]`, and exactly when
`NL_{Y/X}` is moreover a perfect object of `D(𝒪_Y)` of rank zero.

## Main results

* `AlgebraicGeometry.finite_flat_lfp_and_hasTorAmplitude_of_finite_syntomic` and
  `AlgebraicGeometry.finite_syntomic_of_finite_flat_lfp_of_hasTorAmplitude`: **Stacks 0FKY**, the
  implications (1) ⟹ (5) and (5) ⟹ (1), bundled as
  `AlgebraicGeometry.finite_syntomic_iff_hasTorAmplitude_naiveCotangentComplex`.
* `AlgebraicGeometry.finite_flat_lfp_and_isPerfect_and_hasTorAmplitude_of_finite_syntomic` and
  `AlgebraicGeometry.finite_syntomic_iff_isPerfect_and_hasTorAmplitude_naiveCotangentComplex`:
  **Stacks 0FKY**, the implication (1) ⟹ (6) and the equivalence of (1) and (6).
* `AlgebraicGeometry.hasTorAmplitudeCanonical_naiveCotangentObject_of_hasTorAmplitude`: the
  Tor-amplitude condition on `NL_{X/Y}` read on the sections over an affine open of the source
  lying over an affine open of the target.

## Implementation notes

The predicates are the ones Stacks 0FK3 is stated at in this library,
`Stacks.Cohomology.TorAmplitude.HasTorAmplitude` of Stacks 08CG and
`Stacks.Cohomology.PerfectComplexes.IsPerfect` of Stacks 08CM, read on the class of
`AlgebraicGeometry.Scheme.naiveCotangentComplex` in the standard derived category of the
underlying ringed space of the source.

Rank zero is `AlgebraicGeometry.DeterminantTwoTerm.IsRankZeroScheme`: affine locally, `NL_{Y/X}` is
the derived sheafification of an object of `D(Γ(Y, V))` with a two-term presentation by finite
projective modules of equal rank at every prime, as in More on Algebra, Section 0FJI.

*The forward implications.* A finite syntomic morphism is a local complete intersection
morphism, and perfectness and Tor amplitude of `NL_{Y/X}` hold for any such morphism by Stacks
0FK3; flatness and finite presentation are properties of a syntomic morphism. Rank zero holds
for any locally quasi-finite syntomic morphism
(`AlgebraicGeometry.isRankZeroScheme_naiveCotangentComplex_of_locallyQuasiFinite_syntomic`):
for a presentation `B = A[x_1, …, x_n]/I` of the sections over affine opens, both `I/I²` and
`⨁ᵢ B dxᵢ` have rank `n` at every prime. Only this last conjunct uses finiteness, and only
through quasi-finiteness.

*The converses.* These run through the ring-level equivalence Stacks 0FJV, which for a flat map
of finite presentation makes Tor amplitude in `[-1, 0]` of `NL_{B/A}` equivalent to syntomicity.
Finiteness is what makes the reduction to rings cheap: a finite morphism is affine, so the
preimage of an affine open `U` of the target is a single affine open `V`, and syntomicity of
`f` is exactly syntomicity of `Γ(X, U) → Γ(Y, f⁻¹(U))` for such pairs. Reading the Tor-amplitude
hypothesis there is the converse of
`AlgebraicGeometry.NaiveCotangentLocalCompleteIntersection.isPerfect_and_hasTorAmplitude_restrict`
along the same chain: Tor amplitude restricts to an open
(`Stacks.Cohomology.TorAmplitude.hasTorAmplitude_restrictModules`), `NL_{X/Y}|_V` is the derived
pullback of the derived sheafification of `NL_{Γ(X, V)/Γ(Y, U)}` by Stacks 0D0I, and the pullback
along `V ≅ Spec Γ(X, V)` and the sheafification both *reflect* the condition, by Stacks 08E9.
The last step converts between `StacksDraft.TorAmplitude.HasTorAmplitudeCanonical` and the
three-argument form Stacks 0FJV is stated at, through the flat representative of Stacks 0654,
the definition of the former not being exposed.

The converse (6) ⟹ (1) needs only the Tor-amplitude conjunct of (6); the perfectness and
rank-zero conjuncts are not used there.

## References

* [Stacks Project, Tag 0FKY](https://stacks.math.columbia.edu/tag/0FKY)
* [Stacks Project, Lemma 37.62.17 (0FK3)](https://stacks.math.columbia.edu/tag/0FK3)
* [Stacks Project, Lemma 15.88.5 (0FJV)](https://stacks.math.columbia.edu/tag/0FJV)
* [Stacks Project, Lemma 36.3.5 (0D0I)](https://stacks.math.columbia.edu/tag/0D0I)
* [Stacks Project, Lemma 36.10.4 (08E9)](https://stacks.math.columbia.edu/tag/08E9)
* [Stacks Project, Lemma 15.63.3 (0654)](https://stacks.math.columbia.edu/tag/0654)
* [Stacks Project, Section 15.87 (Tag 0FJI)](https://stacks.math.columbia.edu/tag/0FJI)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks Project, Tag 0FKY, the implication (1) ⟹ (5).** A finite syntomic morphism of
schemes is finite, flat and locally of finite presentation, and `NL_{Y/X}` has Tor amplitude in
`[-1, 0]`. -/
@[stacks 0FKY "the implication (1) ⟹ (5)"]
theorem finite_flat_lfp_and_hasTorAmplitude_of_finite_syntomic {Y X : Scheme.{u}} {f : Y ⟶ X}
    (h : IsFinite f ∧ Syntomic f) :
    ((IsFinite f ∧ Flat f) ∧ LocallyOfFinitePresentation f) ∧
      Stacks.Cohomology.TorAmplitude.HasTorAmplitude Y.toRingedSpace
        (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) (-1) 0 :=
  ⟨⟨⟨h.1, flat h.2⟩, locallyOfFinitePresentation h.2⟩,
    (isPerfect_and_hasTorAmplitude_naiveCotangentComplex f
      (isLocalCompleteIntersectionMorphism_of_syntomic h.2)).2⟩

/-- **Stacks Project, Tag 0FKY, the implication (1) ⟹ (6).** A finite syntomic morphism of schemes
is finite, flat and locally of finite presentation, and `NL_{Y/X}` is a perfect object of
`D(𝒪_Y)` of rank zero with Tor amplitude in `[-1, 0]`. -/
@[stacks 0FKY "the implication (1) ⟹ (6)"]
theorem finite_flat_lfp_and_isPerfect_and_hasTorAmplitude_of_finite_syntomic {Y X : Scheme.{u}}
    {f : Y ⟶ X} (h : IsFinite f ∧ Syntomic f) :
    ((IsFinite f ∧ Flat f) ∧ LocallyOfFinitePresentation f) ∧
      (Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace)
          (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) ∧
        DeterminantTwoTerm.IsRankZeroScheme
          (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) ∧
        Stacks.Cohomology.TorAmplitude.HasTorAmplitude Y.toRingedSpace
          (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) (-1) 0) := by
  have := h.1
  have h5 := finite_flat_lfp_and_hasTorAmplitude_of_finite_syntomic h
  exact ⟨h5.1, (isPerfect_and_hasTorAmplitude_naiveCotangentComplex f
    (isLocalCompleteIntersectionMorphism_of_syntomic h.2)).1,
    isRankZeroScheme_naiveCotangentComplex_of_locallyQuasiFinite_syntomic h.2, h5.2⟩

/-! ### From the Tor-amplitude condition back to syntomicity -/

open NaiveCotangentLocalCompleteIntersection in
/-- **The Tor-amplitude condition on `NL_{X/Y}` read on sections.** If `NL_{X/Y}` has Tor
amplitude in `[-1, 0]`, then so does `NL_{Γ(X, V)/Γ(Y, U)}` in `D(Γ(X, V))`, for `V` an affine
open of `X` lying over an affine open `U` of `Y`.

This is the converse of
`AlgebraicGeometry.NaiveCotangentLocalCompleteIntersection.isPerfect_and_hasTorAmplitude_restrict`
for the Tor-amplitude half, along the same chain of identifications: Tor amplitude restricts to
an open, `NL_{X/Y}|_V` is the derived pullback of the derived sheafification of
`NL_{Γ(X, V)/Γ(Y, U)}` by Stacks 0D0I, and the pullback along the isomorphism
`V ≅ Spec Γ(X, V)` and the sheafification both reflect the condition, by Stacks 08E9. -/
theorem hasTorAmplitudeCanonical_naiveCotangentObject_of_hasTorAmplitude {X Y : Scheme.{u}}
    (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens} (hVU : V ≤ f ⁻¹ᵁ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace
      (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) (-1) 0) :
    letI := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
    StacksDraft.TorAmplitude.HasTorAmplitudeCanonical Γ(X, V)
      (NaiveCotangent.naiveCotangentObject Γ(Y, U) Γ(X, V)) (-1) 0 := by
  let := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
  have h1 := Stacks.Cohomology.TorAmplitude.hasTorAmplitude_restrictModules
    (X := X.toRingedSpace) V (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) (-1) 0
    (by norm_num) h
  have h2 := Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_of_iso.{u, u + 1} h1
    (naiveCotangentComplexRestrictIso f hVU hU hV).symm
  have h3 := (Stacks.Cohomology.TransportAlongIso.hasTorAmplitude_derivedPullback_scheme_iff
    hV.isoSpec _ (-1) 0).1 h2
  have h4 := Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_of_iso.{u, u + 1} h3
    ((tilde.functor Γ(X, V)).mapDerivedCategory.mapIso
      (sectionsNaiveCotangentComplexIso f hVU)).symm
  exact (AlgebraicGeometry.hasTorAmplitude_tilde_iff (R := Γ(X, V)) _ (-1) 0).1 h4

/-- **Stacks Project, Tag 0FKY, the implication (5) ⟹ (1).** A finite flat morphism of schemes
which is locally of finite presentation and whose naive cotangent complex has Tor amplitude in
`[-1, 0]` is syntomic.

A finite morphism is affine, so the preimage of an affine open `U` of the target is an affine
open `V`; there the hypotheses say that `Γ(Y, U) → Γ(X, V)` is flat of finite presentation with
`NL_{Γ(X, V)/Γ(Y, U)}` of Tor amplitude in `[-1, 0]`, and that map is syntomic by Stacks
0FJV. -/
@[stacks 0FKY "the implication (5) ⟹ (1)"]
theorem finite_syntomic_of_finite_flat_lfp_of_hasTorAmplitude {Y X : Scheme.{u}} {f : Y ⟶ X}
    (h : ((IsFinite f ∧ Flat f) ∧ LocallyOfFinitePresentation f) ∧
      Stacks.Cohomology.TorAmplitude.HasTorAmplitude Y.toRingedSpace
        (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) (-1) 0) :
    IsFinite f ∧ Syntomic f := by
  obtain ⟨⟨⟨hfin, hflat⟩, hfp⟩, hamp⟩ := h
  have : IsFinite f := hfin
  refine ⟨hfin, fun y => ?_⟩
  obtain ⟨U, hU, hyU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := f.base y) (U := ⊤) (by simp)
  have hV : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  have hVU : (f ⁻¹ᵁ U) ≤ f ⁻¹ᵁ U := le_rfl
  refine ⟨⟨f ⁻¹ᵁ U, hV⟩, hyU, ⟨U, hU⟩, hVU, ?_⟩
  let := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
  have hflat' : Module.Flat Γ(X, U) Γ(Y, f ⁻¹ᵁ U) :=
    (HasRingHomProperty.iff_appLE (P := @Flat) (Q := @RingHom.Flat)).mp hflat ⟨U, hU⟩
      ⟨f ⁻¹ᵁ U, hV⟩ hVU
  have hfp' : Algebra.FinitePresentation Γ(X, U) Γ(Y, f ⁻¹ᵁ U) :=
    (HasRingHomProperty.iff_appLE (P := @LocallyOfFinitePresentation)
      (Q := @RingHom.FinitePresentation)).mp hfp ⟨U, hU⟩ ⟨f ⁻¹ᵁ U, hV⟩ hVU
  have hA : StacksDraft.TorAmplitude.HasTorAmplitude
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct Γ(Y, f ⁻¹ᵁ U)).tensor
      (StacksDraft.TorAmplitude.canonicalTensorComparison Γ(Y, f ⁻¹ᵁ U))
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived Γ(Y, f ⁻¹ᵁ U))
      (NaiveCotangent.naiveCotangentObject Γ(X, U) Γ(Y, f ⁻¹ᵁ U)) (-1) 0 :=
    (StacksDraft.TorAmplitude.hasTorAmplitude_iff_hasFlatRepresentative
        (StacksDraft.TorAmplitude.canonicalTensorComparison Γ(Y, f ⁻¹ᵁ U))
        (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived Γ(Y, f ⁻¹ᵁ U)) _ (-1) 0).2
      ((StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_hasFlatRepresentative
          Γ(Y, f ⁻¹ᵁ U) _ (-1) 0).1
        (hasTorAmplitudeCanonical_naiveCotangentObject_of_hasTorAmplitude f hVU hU hV hamp))
  exact (NaiveCotangent.hasTorAmplitude_tfae_syntomic Γ(X, U) Γ(Y, f ⁻¹ᵁ U)).out 1 3 |>.mp hA

/-! ### The equivalences -/

/-- **Stacks Project, Tag 0FKY, the equivalence of (1) and (5).** A morphism of schemes is finite
and syntomic if and only if it is finite, flat and locally of finite presentation with `NL_{Y/X}`
of Tor amplitude in `[-1, 0]`. -/
@[stacks 0FKY "the equivalence of (1) and (5)"]
theorem finite_syntomic_iff_hasTorAmplitude_naiveCotangentComplex {Y X : Scheme.{u}}
    (f : Y ⟶ X) :
    (IsFinite f ∧ Syntomic f) ↔
      (((IsFinite f ∧ Flat f) ∧ LocallyOfFinitePresentation f) ∧
        Stacks.Cohomology.TorAmplitude.HasTorAmplitude Y.toRingedSpace
          (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) (-1) 0) :=
  ⟨finite_flat_lfp_and_hasTorAmplitude_of_finite_syntomic,
    finite_syntomic_of_finite_flat_lfp_of_hasTorAmplitude⟩

/-- **Stacks Project, Tag 0FKY, the equivalence of (1) and (6).** A morphism of schemes is finite
and syntomic if and only if it is finite, flat and locally of finite presentation with `NL_{Y/X}`
a perfect object of `D(𝒪_Y)` of rank zero with Tor amplitude in `[-1, 0]`. -/
@[stacks 0FKY "the equivalence of (1) and (6)",
  sga "6 0 4.3" "special case",
  sga "6 VIII 2.4" "Forward direction"]
theorem finite_syntomic_iff_isPerfect_and_hasTorAmplitude_naiveCotangentComplex
    {Y X : Scheme.{u}} (f : Y ⟶ X) :
    (IsFinite f ∧ Syntomic f) ↔
      (((IsFinite f ∧ Flat f) ∧ LocallyOfFinitePresentation f) ∧
        (Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace)
            (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) ∧
          DeterminantTwoTerm.IsRankZeroScheme
            (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) ∧
          Stacks.Cohomology.TorAmplitude.HasTorAmplitude Y.toRingedSpace
            (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) (-1) 0)) :=
  ⟨finite_flat_lfp_and_isPerfect_and_hasTorAmplitude_of_finite_syntomic,
    fun h => finite_syntomic_of_finite_flat_lfp_of_hasTorAmplitude ⟨h.1, h.2.2.2⟩⟩

end AlgebraicGeometry

end
