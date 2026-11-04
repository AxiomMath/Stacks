module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Limits.SigmaIrreducibleComponents
public import StacksFrontier.AlgebraicGeometry.MinimalPrimeResidueLocalization.Stalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.PushforwardStalkFibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Scheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Integral
public import StacksFrontier.AlgebraicGeometry.Properties.UnibranchIntegralClosure
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The normalization of a geometrically unibranch scheme is a universal homeomorphism

Let `X` be an irreducible, geometrically unibranch scheme. Its normalization morphism
`ν : X^ν → X` is a universal homeomorphism.

## Main results

* `AlgebraicGeometry.Scheme.surjective_normalization`: the normalization morphism is surjective.
* `AlgebraicGeometry.Scheme.universalHomeomorphism_normalization`: the normalization of an
  irreducible, geometrically unibranch scheme is a universal homeomorphism.

## Implementation notes

A morphism is a universal homeomorphism exactly when it is integral, universally injective and
surjective. Integrality of `ν` holds for any scheme whose quasi-compact opens have finitely many
irreducible components, and surjectivity follows because `ν` is integral, hence closed, and
dominant: it is a factor of the dominant morphism from the spectra of the generic-point residue
fields.

Universal injectivity is checked through its characterization by injectivity together with pure
inseparability of the residue-field extensions. Both come from the stalk
`S = (ν_* 𝒪_{X^ν})_x`, which `AlgebraicGeometry.Scheme.Hom.exists_fibreEquivMaximalSpectrum`
identifies -- with its residue fields -- with the fibre of `ν` over `x`, and which
[Stacks, Tag 0C3B] computes as the integral closure of `𝒪_{X,x}` in the total ring of fractions
of its reduction. Geometric unibranchness of the stalk makes that integral closure a local ring
with purely inseparable residue extension
(`IsGeometricallyUnibranchRing.exists_isLocalRing_of_algEquiv_integralClosure`). A local ring has
one maximal ideal, so the fibre is a single point; and its residue field is the residue field of
`S`, so the extension is purely inseparable.

Irreducibility of `X` enters only through the hypothesis needed to form the normalization at all,
that the quasi-compact opens of `X` have finitely many irreducible components: an open subspace
of an irreducible space has at most one irreducible component. That hypothesis is therefore
supplied in the statement rather than assumed. The condition that the local rings have a unique
minimal prime, which the Stacks proof deduces from irreducibility, is already part of
`IsGeometricallyUnibranchRing`, whose reduction is required to be a domain.

## References

* [Stacks Project, Tag 035Q](https://stacks.math.columbia.edu/tag/035Q)
* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
* [Stacks Project, Tag 0GIQ](https://stacks.math.columbia.edu/tag/0GIQ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open Stacks.NormalizationStalkAmbient

universe u

namespace AlgebraicGeometry.Scheme

/-- Every quasi-compact open of an irreducible scheme has finitely many irreducible components,
so the normalization of an irreducible scheme is defined. -/
public theorem finite_irreducibleComponents_of_irreducibleSpace (X : Scheme.{u})
    [IrreducibleSpace X] (U : X.Opens) (_hU : IsCompact (U : Set X)) :
    (irreducibleComponents U).Finite :=
  finite_irreducibleComponents_isOpen_of_irreducibleSpace U.isOpen

/-- The normalization morphism of a scheme whose quasi-compact opens have finitely many
irreducible components is surjective: it is integral, hence closed, and dominant. -/
public instance surjective_normalization (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    Surjective (normalization X hX) := by
  let : QuasiCompact (fromGenericPointResidueFields X) :=
    quasiCompactFromGenericPointResidueFields X hX
  let : QuasiSeparated (fromGenericPointResidueFields X) :=
    quasiSeparatedFromGenericPointResidueFields X
  let : IsDominant (fromGenericPointResidueFields X).fromNormalization :=
    IsDominant.of_comp (fromGenericPointResidueFields X).toNormalization _ (H := by
      rw [(fromGenericPointResidueFields X).toNormalization_fromNormalization]
      infer_instance)
  infer_instance

/-- **Stacks Project, Tag 0GIQ.** The normalization morphism of an irreducible, geometrically
unibranch scheme is a universal homeomorphism. -/
@[stacks 0GIQ,
  ega "0 23.2.2" "sufficiency + homeo",
  sga "3 X 5.14.0" "univ. homeomorphism",
  sga "4 VIII 1.3" "1.3 c), special case"]
public theorem universalHomeomorphism_normalization (X : Scheme.{u}) [IrreducibleSpace X]
    (hX : IsGeometricallyUnibranch X) :
    UniversalHomeomorphism
      (normalization X (finite_irreducibleComponents_of_irreducibleSpace X)) := by
  let hfin := finite_irreducibleComponents_of_irreducibleSpace X
  let ν := normalization X hfin
  -- The stalk of `ν_* 𝒪_{X^ν}` at a point is a local ring with purely inseparable residue
  -- extension, by geometric unibranchness and [Stacks, Tag 0C3B].
  have hstalk : ∀ x : X,
      let : Algebra (X.presheaf.stalk x) (normalizationPushforwardStalk X hfin x) :=
        normalizationPushforwardStalkAlgebra X hfin x
      ∃ hloc : IsLocalRing (normalizationPushforwardStalk X hfin x),
        ∃ _ : IsLocalHom
          (algebraMap (X.presheaf.stalk x) (normalizationPushforwardStalk X hfin x)),
          let := hloc
          IsPurelyInseparable (IsLocalRing.ResidueField (X.presheaf.stalk x))
            (IsLocalRing.ResidueField (normalizationPushforwardStalk X hfin x)) := by
    intro x
    let : Algebra (X.presheaf.stalk x) (normalizationPushforwardStalk X hfin x) :=
      normalizationPushforwardStalkAlgebra X hfin x
    exact IsGeometricallyUnibranchRing.exists_isLocalRing_of_algEquiv_integralClosure (hX x)
      (normalizationStalkAlgEquivIntegralClosureFractionRing X hfin x)
  rw [universalHomeomorphism_iff_integral_universallyInjective_surjective]
  refine ⟨inferInstance, ?_, surjective_normalization X hfin⟩
  have htfae := (tfae_universallyInjective ν).out 1 3
  refine htfae.mpr ⟨?_, ?_⟩
  · -- `ν` is injective: the fibre over `x` is the maximal spectrum of a local ring.
    intro y₁ y₂ hy
    obtain ⟨e, -⟩ := ν.exists_fibreEquivMaximalSpectrum (ν y₁)
    obtain ⟨hloc, -, -⟩ := hstalk (ν y₁)
    let : IsLocalRing ((ν.base _* (normalizationScheme X hfin).presheaf).stalk (ν y₁)) := hloc
    have hEq : e ⟨y₁, rfl⟩ = e ⟨y₂, hy.symm⟩ := MaximalSpectrum.ext (by
      rw [IsLocalRing.eq_maximalIdeal (e ⟨y₁, rfl⟩).isMaximal,
        IsLocalRing.eq_maximalIdeal (e ⟨y₂, hy.symm⟩).isMaximal])
    exact congrArg Subtype.val (e.injective hEq)
  · -- The residue-field extensions of `ν` are purely inseparable.
    intro y
    obtain ⟨e, hres⟩ := ν.exists_fibreEquivMaximalSpectrum (ν y)
    obtain ⟨hloc, hlh, hpure⟩ := hstalk (ν y)
    let A := X.presheaf.stalk (ν y)
    let S := (ν.base _* (normalizationScheme X hfin).presheaf).stalk (ν y)
    let : Algebra A S := normalizationPushforwardStalkAlgebra X hfin (ν y)
    let : IsLocalRing S := hloc
    let : IsLocalHom (algebraMap A S) := hlh
    obtain ⟨ε, -, hcompat⟩ := hres ⟨y, rfl⟩
    have hM : (e ⟨y, rfl⟩).asIdeal = IsLocalRing.maximalIdeal S :=
      IsLocalRing.eq_maximalIdeal (e ⟨y, rfl⟩).isMaximal
    let eRF : (S ⧸ (e ⟨y, rfl⟩).asIdeal) ≃+* IsLocalRing.ResidueField S :=
      Ideal.quotEquivOfEq hM
    let εRF : (normalizationScheme X hfin).residueField y ≃+* IsLocalRing.ResidueField S :=
      ε.trans eRF
    -- `ε` carries the residue-field map of `ν` to the residue-field map of `A → S`.
    have hres' : εRF.toRingHom.comp (ν.residueFieldMap y).hom =
        algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField S) := by
      refine RingHom.ext fun c => ?_
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := A) c
      change εRF ((ν.residueFieldMap y).hom ((X.residue (ν y)).hom a)) = _
      calc
        εRF ((ν.residueFieldMap y).hom ((X.residue (ν y)).hom a))
            = eRF (Ideal.Quotient.mk (e ⟨y, rfl⟩).asIdeal (algebraMap A S a)) :=
              congrArg eRF (RingHom.congr_fun hcompat a)
        _ = IsLocalRing.residue S (algebraMap A S a) :=
              Ideal.quotEquivOfEq_mk hM (algebraMap A S a)
        _ = _ := (IsLocalRing.ResidueField.algebraMap_residue a).symm
    -- Hence the residue field of `y` is the residue field of `S` over that of `x`.
    let : Algebra (IsLocalRing.ResidueField A)
        ((normalizationScheme X hfin).residueField y) :=
      (ν.residueFieldMap y).hom.toAlgebra
    let εAlg : ((normalizationScheme X hfin).residueField y) ≃ₐ[IsLocalRing.ResidueField A]
        IsLocalRing.ResidueField S :=
      { εRF with commutes' := fun c => RingHom.congr_fun hres' c }
    have hpureY : IsPurelyInseparable (IsLocalRing.ResidueField A)
        ((normalizationScheme X hfin).residueField y) :=
      εAlg.isPurelyInseparable_iff.mpr hpure
    let : Algebra (X.residueField (ν y)) ((normalizationScheme X hfin).residueField y) :=
      (ν.residueFieldMap y).hom.toAlgebra
    rw [show (ν.residueFieldMap y).hom =
      algebraMap (X.residueField (ν y)) ((normalizationScheme X hfin).residueField y) from rfl,
      RingHom.isPurelyInseparable_algebraMap_iff]
    exact hpureY

end AlgebraicGeometry.Scheme

end
