module

public import Mathlib.AlgebraicGeometry.Normalization
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.GenericPoints
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Normalization of a scheme

Let `X` be a scheme such that every quasi-compact open has finitely many irreducible
components. The spectra of the residue fields at its generic points map canonically to `X`,
and the *normalization* of `X` is the relative normalization of `X` in that morphism.

## Main definitions

* `AlgebraicGeometry.Scheme.normalizationScheme` is the scheme obtained by relatively
  normalizing `X` in the coproduct of its generic-point residue fields.
* `AlgebraicGeometry.Scheme.normalization` is the normalization morphism to `X`.

## Main results

* `AlgebraicGeometry.Scheme.isIntegral_normalizationScheme`: the normalization of an integral
  scheme is integral, part of Tag 035Q.
* `AlgebraicGeometry.Scheme.quasiCompactFromGenericPointResidueFields` and
  `AlgebraicGeometry.Scheme.quasiSeparatedFromGenericPointResidueFields` supply the finiteness
  properties needed to form the relative normalization.

## Implementation notes

The hypothesis on quasi-compact opens makes the generic-point residue-field morphism
quasi-compact: a quasi-compact open of `X` meets only finitely many irreducible components, so
only finitely many summands of the coproduct map into it. The source of that morphism is
quasi-separated because it is a coproduct of affine schemes with pairwise disjoint images.
These two facts supply the hypotheses of relative normalization. The definitions below are
abbreviations exposing that construction directly, so its existing API applies to the
normalization of `X` without a comparison theorem.

## References

* [Stacks Project, Tag 035N](https://stacks.math.columbia.edu/tag/035N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- Only finitely many generic points of `X` lie in a quasi-compact open, when every
quasi-compact open of `X` has finitely many irreducible components. -/
theorem finite_genericPoints_mem (X : Scheme.{u}) (U : X.Opens)
    (hU : IsCompact (U : Set X))
    (hX : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite) :
    { η : genericPoints X | η.1 ∈ U }.Finite := by
  have : Finite (genericPoints (U : Set X)) := (genericPoints.finite (hX U hU)).to_subtype
  have : Finite { η : genericPoints X // η.1 ∈ U } :=
    Finite.of_injective (genericPointsInOpenEquiv X U)
      (genericPointsInOpenEquiv X U).injective
  exact Set.finite_coe_iff.mp this

/-- The canonical morphism from the generic-point residue fields is quasi-compact when every
quasi-compact open of the target has finitely many irreducible components. -/
theorem quasiCompactFromGenericPointResidueFields (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    QuasiCompact (fromGenericPointResidueFields X) := by
  refine ⟨fun U hU hUc ↦ ?_⟩
  unfold fromGenericPointResidueFields genericPointResidueSpectrum
  let e := sigmaMk (fun η : genericPoints X ↦ Spec (.of (X.residueField η.1)))
  apply e.isCompact_preimage.mp
  convert Set.isCompact_sigma
    (finite_genericPoints_mem X ⟨U, hU⟩ hUc hX)
    (fun _ _ ↦ isCompact_univ) using 1
  · ext z
    obtain ⟨η, z⟩ := z
    simp only [Set.mem_preimage, Set.mem_sigma_iff, Set.mem_ofPred_eq, Set.mem_univ, and_true]
    rw [show e ⟨η, z⟩ =
      Sigma.ι (fun η : genericPoints X ↦ Spec (.of (X.residueField η.1))) η z by simp [e],
      ← Scheme.Hom.comp_apply, Sigma.ι_desc, X.fromSpecResidueField_apply]
    rfl
  · intro η _
    infer_instance

/-- The canonical morphism from the generic-point residue fields is quasi-separated. -/
theorem quasiSeparatedFromGenericPointResidueFields (X : Scheme.{u}) :
    QuasiSeparated (fromGenericPointResidueFields X) := by
  have hs : QuasiSeparatedSpace (genericPointResidueSpectrum X) := by
    unfold genericPointResidueSpectrum
    apply quasiSeparatedSpace_of_isOpenCover
      (fun η ↦ (Sigma.ι (fun η : genericPoints X ↦
        Spec (.of (X.residueField η.1))) η).opensRange)
    · exact (sigmaOpenCover (fun η : genericPoints X ↦
        Spec (.of (X.residueField η.1)))).iSup_opensRange
    · exact fun _ ↦ isAffineOpen_opensRange _
    · intro η ξ
      rcases eq_or_ne η ξ with rfl | h
      · simpa using (isAffineOpen_opensRange
          (Sigma.ι (fun η : genericPoints X ↦
            Spec (.of (X.residueField η.1))) η)).isCompact
      · rw [← Opens.coe_inf, disjoint_iff.mp (disjoint_opensRange_sigmaι
          (fun η : genericPoints X ↦ Spec (.of (X.residueField η.1))) η ξ h)]
        exact isCompact_empty
  infer_instance

/-- The normalization scheme of `X`, obtained by normalizing it in the canonical morphism from
the spectra of the residue fields at its generic points. -/
noncomputable abbrev normalizationScheme (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    Scheme.{u} :=
  letI := quasiCompactFromGenericPointResidueFields X hX
  letI := quasiSeparatedFromGenericPointResidueFields X
  (fromGenericPointResidueFields X).normalization

/-- **Stacks Project, Tag 035N.** The normalization morphism of a scheme whose quasi-compact
opens have finitely many irreducible components. -/
@[stacks 035N, ega "II 7.4.6" "special case"]
noncomputable abbrev normalization (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    normalizationScheme X hX ⟶ X :=
  letI := quasiCompactFromGenericPointResidueFields X hX
  letI := quasiSeparatedFromGenericPointResidueFields X
  (fromGenericPointResidueFields X).fromNormalization

/-! ### The normalization of an integral scheme -/

/-- The coproduct of the residue fields at the generic points of an integral scheme is the
spectrum of its function field, hence integral: an integral scheme has exactly one generic
point, so the coproduct has exactly one summand. -/
instance isIntegral_genericPointResidueSpectrum (X : Scheme.{u}) [IsIntegral X] :
    IsIntegral (genericPointResidueSpectrum X) := by
  have : Unique (genericPoints X) := by
    rw [genericPoints_eq_singleton]
    exact Set.uniqueSingleton _
  unfold genericPointResidueSpectrum
  exact IsIntegral.of_isIso (coproductUniqueIso
    (fun η : genericPoints X ↦ Spec (.of (X.residueField η.1)))).inv

/-- **Stacks Project, Tag 035Q (integral case).** The normalization of an integral scheme is
integral: it is the relative normalization of the scheme in the spectrum of its function field. -/
instance isIntegral_normalizationScheme (X : Scheme.{u}) [IsIntegral X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    IsIntegral (X.normalizationScheme hX) :=
  inferInstance

end AlgebraicGeometry.Scheme
