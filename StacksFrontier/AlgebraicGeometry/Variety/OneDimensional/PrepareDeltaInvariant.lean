module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.UniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationBirational.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationQuotient.DirectSum
public import StacksFrontier.AlgebraicGeometry.NormalizationQuotient.StalkLength
public import StacksFrontier.AlgebraicGeometry.NormalizationStalkAmbient.UniqueEmbedding
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Completion
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationStalkCompletion
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.SemilocalDedekind
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The normalization of a one-dimensional reduced Nagata scheme

Let `X` be a reduced Nagata scheme of dimension one, `ν : X^ν ⟶ X` its normalization and
`x ∈ X` a closed point, with `A = 𝒪_{X,x}` and `A' = (ν_* 𝒪_{X^ν})_x`.
[Stacks, Tag 0C1R](https://stacks.math.columbia.edu/tag/0C1R) lists nine properties of this
situation.  This file states each of the parts (1), (2), (4), (5), (6) and (7) as one
declaration; parts (3), (8) and (9) are each already stated whole by a single declaration:

* (3) `AlgebraicGeometry.existsUnique_algHom_normalizationPushforwardStalk_fractionRing`;
* (8) `AlgebraicGeometry.exists_pi_isDiscreteValuationRing_adicCompletion_normalizationStalk`;
* (9) `existsUnique_linearEquiv_quotient_adicCompletion_normalizationPushforwardStalk`, in the
  namespace `Stacks.AlgebraicGeometry.NormalizationQuotient`.

## Main results

* `AlgebraicGeometry.Scheme.isFinite_surjective_isBirational_normalization`: part (1).
* `AlgebraicGeometry.normalizationQuotient_mono_iso_coproduct_skyscraperModule`: part (2).
* `AlgebraicGeometry.normalizationQuotientStalk_finiteLength_eq_deltaInvariant`: part (4).
* `AlgebraicGeometry.normalizationPushforwardStalk_semilocal_finiteProductOfDedekindDomains`:
  part (5).
* `AlgebraicGeometry.adicCompletion_stalk_reduced_noetherian_complete_local_dim_one`: part (6).
* `AlgebraicGeometry.adicCompletion_stalk_reduced_noetherian_complete_local_ringKrullDim_eq`:
  part (6) at every point, with `dim A^∧ = dim A ≤ 1`.
* `exists_injective_range_eq_integralClosure_adicCompletion_normalizationStalk_of_isNagataScheme`:
  part (7), in the namespace `AlgebraicGeometry`.

## Implementation notes

Parts (6) and (8), as printed in the source, are false at a closed point whose local ring has
dimension zero, and such points exist: `X = Spec (k × k[t])` is reduced, Nagata and of dimension
one, and the point `Spec k` is closed with local ring `A = k`.  There `A^∧ = A' = (A')^∧ = k`,
a field, which has dimension zero and is not a product of discrete valuation rings.  Both parts
are therefore stated under the hypothesis `ringKrullDim 𝒪_{X,x} = 1`, the correction the
source already makes in part (8) ("if `dim(𝒪_{X,x}) = 1`").  The remaining parts hold at every
point, including those.

Hypotheses of the source that a part does not use are dropped, so each statement is at least as
general as the corresponding part: the closedness of `x` is used by none of them, and the
dimension of `X` only by parts (2), (4), (5) and (7).  The normalization is formed with the
finiteness of irreducible components that the Nagata hypothesis provides.

The completion `(A')^∧` is the completion of `A'` along `𝔪_A A'`; as `A'` is finite over `A`,
this ideal and the Jacobson radical of `A'` define the same topology.  The total ring of fractions
of a ring `R` is `FractionRing R`, the localization at the non-zero-divisors, and the
`δ`-invariant of `X` at `x` is `Ring.deltaInvariant 𝒪_{X,x}` (Tag 0C3T).

## References

* [Stacks Project, Tag 0C1R](https://stacks.math.columbia.edu/tag/0C1R)
* [Stacks Project, Tag 0C3T](https://stacks.math.columbia.edu/tag/0C3T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing
open Stacks.AlgebraicGeometry.Normalization (finite_irreducibleComponents_of_isNagataScheme)
open Stacks.AlgebraicGeometry.NormalizationQuotient Stacks.NormalizationStalkAmbient

universe u

namespace AlgebraicGeometry

namespace Scheme

/-- **Stacks Project, Tag 0C1R, part (1).** The normalization `ν : X^ν ⟶ X` of a reduced Nagata
scheme is finite, surjective and birational.

The dimension of `X` is not used. -/
@[stacks 0C1R "part (1): ν is finite, surjective and birational", ega "II 6.3.8" "special case"]
public theorem isFinite_surjective_isBirational_normalization (X : Scheme.{u}) [IsReduced X]
    (hX : IsNagataScheme X) :
    IsFinite (X.normalization (finite_irreducibleComponents_of_isNagataScheme X hX)) ∧
      Surjective (X.normalization (finite_irreducibleComponents_of_isNagataScheme X hX)) ∧
      IsBirational (X.normalization (finite_irreducibleComponents_of_isNagataScheme X hX)) :=
  ⟨isFinite_normalization hX _, surjective_normalization X _, X.isBirational_normalization _⟩

end Scheme

/-- The normalization morphism of a reduced scheme is injective on sections over every open. -/
private theorem injective_normalization_app (X : Scheme.{u}) [IsReduced X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (U : X.Opens) : Function.Injective ((X.normalization hX).app U) :=
  let := Scheme.quasiCompactFromGenericPointResidueFields X hX
  let := Scheme.quasiSeparatedFromGenericPointResidueFields X
  Stacks.AlgebraicGeometry.Normalization.injective_fromNormalization_app
    (Scheme.fromGenericPointResidueFields X) U

/-- The module map `𝒪_X ⟶ ν_* 𝒪_{X^ν}` of a reduced scheme is a monomorphism, because the
normalization morphism is injective on sections over every open. -/
public theorem mono_normalizationModuleMap (X : Scheme.{u}) [IsReduced X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    Mono (normalizationModuleMap X hX) := by
  refine (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).mono_of_mono_map ?_
  have (U : X.Opensᵒᵖ) : Mono (((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
      (normalizationModuleMap X hX)).app U) :=
    (AddCommGrpCat.mono_iff_injective _).mpr (injective_normalization_app X hX U.unop)
  exact NatTrans.mono_of_mono_app _

/-- **Stacks Project, Tag 0C1R, part (2).** For a reduced Nagata scheme `X` of dimension one,
`𝒪_X ⊂ ν_* 𝒪_{X^ν}` — the map is a monomorphism both of sheaves of rings and of `𝒪_X`-modules —
and the quotient `ν_* 𝒪_{X^ν} / 𝒪_X` is the direct sum, over the singular points `x` of `X`, of
the skyscraper sheaves at `x` with value `𝒬_x`, the stalk of the quotient at `x`; that stalk is
nonzero exactly at the singular points. -/
@[stacks 0C1R "part (2): O_X ⊂ ν_*O, the quotient a sum of skyscrapers Q_x at singular points"]
public theorem normalizationQuotient_mono_iso_coproduct_skyscraperModule (X : Scheme.{u})
    [IsReduced X] (hX : IsNagataScheme X) (hdim : topologicalKrullDim X = 1) :
    Mono (Scheme.Hom.toRingCatSheafHom
        (X.normalization (finite_irreducibleComponents_of_isNagataScheme X hX))) ∧
      Mono (normalizationModuleMap X (finite_irreducibleComponents_of_isNagataScheme X hX)) ∧
      Nonempty
        (normalizationQuotient X (finite_irreducibleComponents_of_isNagataScheme X hX) ≅
          ∐ fun z : singularLocus X =>
            skyscraperModule X z.1
              (normalizationQuotientStalk X
                (finite_irreducibleComponents_of_isNagataScheme X hX) z.1)) ∧
      ∀ x : X, ¬ IsZero (normalizationQuotientStalk X
          (finite_irreducibleComponents_of_isNagataScheme X hX) x) ↔ x ∈ singularLocus X :=
  ⟨Stacks.AlgebraicGeometry.Normalization.mono_toRingCatSheafHom_of_app_injective _
      (injective_normalization_app X _),
    mono_normalizationModuleMap X (finite_irreducibleComponents_of_isNagataScheme X hX),
    normalizationQuotient_iso_coproduct_skyscraperModule X hX hdim,
    normalizationQuotientStalk_nonzero_iff_mem_singularLocus X hX hdim⟩

/-- **Stacks Project, Tag 0C1R, part (4).** On a reduced Nagata scheme of dimension one, the
stalk `𝒬_x` of `ν_* 𝒪_{X^ν} / 𝒪_X` at `x` is `A' / A`, where `A = 𝒪_{X,x}` and
`A' = (ν_* 𝒪_{X^ν})_x`; it has finite length over `A`, and that length is the `δ`-invariant of
`X` at `x`. -/
@[stacks 0C1R "part (4): Q_x = A'/A has finite length equal to the δ-invariant"]
public theorem normalizationQuotientStalk_finiteLength_eq_deltaInvariant (X : Scheme.{u})
    [IsReduced X] (hX : IsNagataScheme X) (hdim : topologicalKrullDim X = 1) (x : X) :
    letI : Algebra (X.presheaf.stalk x)
        (normalizationPushforwardStalk X (finite_irreducibleComponents_of_isNagataScheme X hX) x) :=
      normalizationPushforwardStalkAlgebra X _ x
    Nonempty (normalizationQuotientStalk X (finite_irreducibleComponents_of_isNagataScheme X hX) x
        ≃ₗ[X.presheaf.stalk x]
        (normalizationPushforwardStalk X (finite_irreducibleComponents_of_isNagataScheme X hX) x ⧸
          LinearMap.range (Algebra.linearMap (X.presheaf.stalk x)
            (normalizationPushforwardStalk X
              (finite_irreducibleComponents_of_isNagataScheme X hX) x)))) ∧
      IsFiniteLength (X.presheaf.stalk x)
        (normalizationQuotientStalk X (finite_irreducibleComponents_of_isNagataScheme X hX) x) ∧
      Module.length (X.presheaf.stalk x)
          (normalizationQuotientStalk X (finite_irreducibleComponents_of_isNagataScheme X hX) x) =
        Ring.deltaInvariant (X.presheaf.stalk x) :=
  ⟨normalizationQuotientStalk_linearEquiv_quotient_range X _ x,
    isFiniteLength_normalizationQuotientStalk X hX hdim _ x,
    length_normalizationQuotientStalk X _ x⟩

/-- **Stacks Project, Tag 0C1R, part (5).** On a Nagata scheme of dimension one, the stalk
`A' = (ν_* 𝒪_{X^ν})_x` is a semi-local ring — it has finitely many maximal ideals — which is a
finite product of Dedekind domains.

Reducedness of `X` is not used. -/
@[stacks 0C1R "part (5): A' is semi-local and a finite product of Dedekind domains"]
public theorem normalizationPushforwardStalk_semilocal_finiteProductOfDedekindDomains
    (X : Scheme.{u}) (hX : IsNagataScheme X) (hdim : topologicalKrullDim X = 1) (x : X) :
    Finite (MaximalSpectrum
        (normalizationPushforwardStalk X (finite_irreducibleComponents_of_isNagataScheme X hX) x)) ∧
      IsDiscreteValuationRing.IsFiniteProductOfDedekindDomains
        (normalizationPushforwardStalk X (finite_irreducibleComponents_of_isNagataScheme X hX) x) :=
  ⟨finite_maximalSpectrum_normalizationPushforwardStalk X hX _ x,
    isFiniteProductOfDedekindDomains_normalizationPushforwardStalk X hX hdim _ x⟩

/-- **Stacks Project, Tag 0C1R, part (6)**, at a point whose local ring has dimension one. For a
reduced Nagata scheme `X` and a point `x` with `dim 𝒪_{X,x} = 1`, the completion `A^∧` of
`A = 𝒪_{X,x}` at its maximal ideal is a reduced Noetherian complete local ring of dimension one.

The hypothesis on `dim 𝒪_{X,x}` corrects the source: at a closed point of a one-dimensional scheme
whose local ring is a field (an isolated point), `A^∧ = A` has dimension zero.  Everything except
the dimension holds without it. -/
@[stacks 0C1R "part (6): A^ is reduced Noetherian complete local of dimension 1 (dim A = 1)",
  ega "IV 7.3.19" "dim(Â)=1"]
public theorem adicCompletion_stalk_reduced_noetherian_complete_local_dim_one (X : Scheme.{u})
    [IsReduced X] (hX : IsNagataScheme X) (x : X)
    (hxdim : ringKrullDim (X.presheaf.stalk x) = 1) :
    _root_.IsReduced (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) ∧
      IsNoetherianRing (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) ∧
      ∃ _ : IsLocalRing
          (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)),
        IsAdicComplete
            (maximalIdeal
              (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)))
            (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) ∧
          ringKrullDim
              (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) = 1 := by
  have hA : IsNagataRing (X.presheaf.stalk x) := stalk_isNagataRing X hX x
  refine ⟨IsLocalRing.isReduced_adicCompletion_maximalIdeal_of_isNagataRing hA, inferInstance,
    inferInstance, inferInstance, ?_⟩
  rw [IsLocalRing.ringKrullDim_adicCompletion_maximalIdeal, hxdim]

/-- **Stacks Project, Tag 0C1R, part (6)**, at every point. Let `X` be a reduced Nagata scheme of
dimension one, `x ∈ X` and `A = 𝒪_{X,x}`.  The completion `A^∧` of `A` at its maximal ideal is a
reduced Noetherian complete local ring with `dim A^∧ = dim A`; moreover `dim A ≤ 1`, with
`dim A = 1` exactly when `A` is not a field.  So the source's "of dimension 1" is precisely the
case `dim A = 1`, the one `adicCompletion_stalk_reduced_noetherian_complete_local_dim_one` states.

Part (6) as printed fails when `A` is a field, which happens at an isolated point: the scheme
`X = Spec (k × k[t])` is reduced, Nagata and of dimension one, its point `Spec k` is closed, and
there `A = A^∧ = k` has dimension zero.  Neither closedness of `x` nor any hypothesis on `dim A` is
used. -/
@[stacks 0C1R "part (6) at every point: A^ reduced Noetherian complete local, dim A^ = dim A ≤ 1",
  ega "IV 7.3.19" "dim(Â)=1"]
public theorem adicCompletion_stalk_reduced_noetherian_complete_local_ringKrullDim_eq
    (X : Scheme.{u}) [IsReduced X] (hX : IsNagataScheme X) (hdim : topologicalKrullDim X = 1)
    (x : X) :
    _root_.IsReduced (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) ∧
      IsNoetherianRing (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) ∧
      (∃ _ : IsLocalRing
          (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)),
        IsAdicComplete
            (maximalIdeal
              (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)))
            (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) ∧
          ringKrullDim
              (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) =
            ringKrullDim (X.presheaf.stalk x)) ∧
      ringKrullDim (X.presheaf.stalk x) ≤ 1 ∧
      (ringKrullDim (X.presheaf.stalk x) = 1 ↔ ¬ IsField (X.presheaf.stalk x)) := by
  have hA : IsNagataRing (X.presheaf.stalk x) := stalk_isNagataRing X hX x
  have hle : ringKrullDim (X.presheaf.stalk x) ≤ 1 :=
    hdim ▸ (le_iSup (fun y : X ↦ ringKrullDim (X.presheaf.stalk y)) x).trans
      (topologicalKrullDim_eq_iSup_krullDimOfRing_stalk X).ge
  refine ⟨IsLocalRing.isReduced_adicCompletion_maximalIdeal_of_isNagataRing hA, inferInstance,
    ⟨inferInstance, inferInstance, IsLocalRing.ringKrullDim_adicCompletion_maximalIdeal⟩, hle,
    ⟨fun h hfield ↦ ?_, fun hnf ↦ ?_⟩⟩
  · exact one_ne_zero (h.symm.trans (ringKrullDim_eq_zero_of_isField hfield))
  · have h0 : ¬ ringKrullDim (X.presheaf.stalk x) ≤ 0 := fun h0 ↦ by
      have : Ring.KrullDimLE 0 (X.presheaf.stalk x) := Ring.krullDimLE_iff.mpr (by simpa using h0)
      exact hnf Ring.KrullDimLE.isField_of_isReduced
    have hnn := ringKrullDim_nonneg_of_nontrivial (R := X.presheaf.stalk x)
    generalize ringKrullDim (X.presheaf.stalk x) = d at hle h0 hnn ⊢
    induction d using WithBot.recBotCoe with
    | bot => exact absurd hnn (by simp)
    | coe e =>
      induction e using ENat.recTopCoe with
      | top => exact absurd hle (by decide)
      | coe n =>
        have hle' : n ≤ 1 := by exact_mod_cast hle
        have h0' : ¬ n ≤ 0 := by exact_mod_cast h0
        obtain rfl : n = 1 := by lia
        rfl

/-- **Stacks Project, Tag 0C1R, part (7).** Let `X` be a reduced Nagata scheme of dimension one,
`A = 𝒪_{X,x}` and `A' = (ν_* 𝒪_{X^ν})_x`.  The completion `(A')^∧` of `A'` along `𝔪_A A'` is the
integral closure of `A^∧` in its total ring of fractions: there is an injective ring map
`(A')^∧ → Frac(A^∧)` extending the structure map of `A^∧`, whose image is the integral closure of
`A^∧` in `Frac(A^∧)`.

Closedness of the point is not needed. -/
@[stacks 0C1R "part (7): (A')^ is the integral closure of A^ in its total ring of fractions"]
public theorem
    exists_injective_range_eq_integralClosure_adicCompletion_normalizationStalk_of_isNagataScheme
    (X : Scheme.{u}) [IsReduced X] (hX : IsNagataScheme X) (hdim : topologicalKrullDim X = 1)
    (x : X) :
    letI : Algebra (X.presheaf.stalk x)
        (normalizationPushforwardStalk X (finite_irreducibleComponents_of_isNagataScheme X hX) x) :=
      normalizationPushforwardStalkAlgebra X _ x
    let A := X.presheaf.stalk x
    let A' :=
      normalizationPushforwardStalk X (finite_irreducibleComponents_of_isNagataScheme X hX) x
    let Ac := AdicCompletion (maximalIdeal A) A
    let J := (maximalIdeal A).map (algebraMap A A')
    let C := AdicCompletion J A'
    let k : Ac →+* C := adicCompletionMap (algebraMap A A') (maximalIdeal A) J le_rfl
    ∃ g : C →+* FractionRing Ac,
      Function.Injective g ∧
        g.range = (integralClosure Ac (FractionRing Ac)).toSubring ∧
        ∀ y : Ac, g (k y) = algebraMap Ac (FractionRing Ac) y := by
  intro A A' Ac J C k
  obtain ⟨f₀, ⟨hf₀, hrange⟩, -⟩ :=
    existsUnique_algHom_normalizationPushforwardStalk_fractionRing X
      (finite_irreducibleComponents_of_isNagataScheme X hX) x
  obtain ⟨-, -, g, hg, hgrange, hgk, -⟩ :=
    exists_injective_range_eq_integralClosure_adicCompletion_normalizationStalk X hX hdim _ x
      f₀ hf₀ hrange
  exact ⟨g, hg, hgrange, hgk⟩

end AlgebraicGeometry

end
