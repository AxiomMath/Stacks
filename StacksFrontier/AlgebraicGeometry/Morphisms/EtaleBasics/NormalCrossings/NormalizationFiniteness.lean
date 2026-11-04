module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.NormalizationCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.FiniteCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.EtaleLocalStructure.DisjointDecomposition
import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.FpqcLocalAtTarget

/-!
# Finiteness of an unramified normalization of a divisor

The normalization `ν : D^ν ⟶ D` of the closed subscheme cut out by a divisor on a locally
Noetherian scheme is an integral morphism. When it is unramified it is therefore finite, and so
is the composition `D^ν ⟶ X` with the closed immersion of the subscheme. Being finite and
unramified, that composition splits étale-locally on `X` into finitely many closed subschemes of
the étale neighbourhood. These are the opening steps of the implication from condition (2) of
Tag 0CBR to condition (1). The scheme `Z_1` of condition (2) is the normalization itself, so the
hypotheses made there on `Z_1` say that `D^ν` is regular and that `D^ν ⟶ X` is a local complete
intersection morphism.

## Main definitions

* `Stacks.Divisors.divisorNormalizationToAmbient` is the composition `D^ν ⟶ X` of the
  normalization with the closed immersion of the subscheme.
* `Stacks.Divisors.normalizationDistinctOneIso` identifies `Z_1` with the normalization.

## Main results

* `Stacks.Divisors.isFinite_divisorNormalization`: an unramified normalization of a divisor is
  finite.
* `Stacks.Divisors.isFinite_divisorNormalizationToAmbient` and
  `Stacks.Divisors.unramified_divisorNormalizationToAmbient`: the morphism `D^ν ⟶ X` is finite
  and unramified.
* `Stacks.Divisors.exists_etaleNeighborhood_disjoint_closed_decomposition_divisorNormalization`:
  étale-locally on `X` the normalization becomes a finite disjoint union of closed subschemes of
  the base.
* `Stacks.Divisors.isRegular_divisorNormalizationScheme` and
  `Stacks.Divisors.isLocalCompleteIntersectionMorphism_divisorNormalizationToAmbient`: condition
  (2) of Tag 0CBR makes `D^ν` regular and `D^ν ⟶ X` a local complete intersection morphism.

## Implementation notes

Integrality of the normalization morphism is the integrality of a relative normalization, but the
quasi-compactness and quasi-separatedness instances that the latter needs are supplied by local
`letI`s inside the definition of the normalization of a scheme, so they are reinstated here
before the library instance can be used.

Finiteness is deduced from integrality by Tag 01WJ: an unramified morphism is locally of finite
type, and an integral morphism locally of finite type is finite. The étale-local splitting is
Tag 04HJ applied to `D^ν ⟶ X`.

That `Z_1` is the normalization uses that a single-factor fibre power has no pair of distinct
coordinates, so its fat diagonal is empty, together with the identification of the one-fold
fibre power with the source of the morphism, which is the pullback along an identity. The two
consequences drawn from `Z_1` transport a property of a scheme and a property of a morphism along
that identification.

## References

* [Stacks Project, Tag 0CBR](https://stacks.math.columbia.edu/tag/0CBR)
* [Stacks Project, Tag 01WJ](https://stacks.math.columbia.edu/tag/01WJ)
* [Stacks Project, Tag 04HJ](https://stacks.math.columbia.edu/tag/04HJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Function

universe u

namespace AlgebraicGeometry

variable {Y S : Scheme.{u}}

/-- The only coordinate of a one-fold fibre power is the second projection of the pullback along
the identity. -/
public theorem fibrePowerLeg_one (f : Y ⟶ S) :
    fibrePowerLeg f 1 0 = pullback.snd (𝟙 S) f := rfl

/-- The one-fold fibre power of a morphism is its source. -/
public instance isIso_fibrePowerLeg_one (f : Y ⟶ S) : IsIso (fibrePowerLeg f 1 0) := by
  rw [fibrePowerLeg_one]
  infer_instance

/-- A one-fold fibre power has no pair of distinct coordinates, so its fat diagonal is empty. -/
public theorem fibrePowerDistinctLocus_one (f : Y ⟶ S) :
    fibrePowerDistinctLocus f 1 = Set.univ :=
  Set.eq_univ_of_forall fun _ i j hij => absurd (Subsingleton.elim i j) hij

end AlgebraicGeometry

namespace Stacks.Divisors

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (D : X.IdealSheafData)

/-- The normalization of the closed subscheme cut out by a divisor on a locally Noetherian scheme
is an integral morphism. -/
@[stacks 0CBR "the proof of (2) to (1), first step: the normalization `ν : D^ν ⟶ D` is \
integral. Neither implication of the equivalence is asserted."]
public instance isIntegralHom_divisorNormalization : IsIntegralHom (divisorNormalization D) := by
  have : IsLocallyNoetherian D.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian D.subschemeι
  have := Scheme.quasiCompactFromGenericPointResidueFields D.subscheme
    (finite_irreducibleComponents_of_isCompact D.subscheme)
  have := Scheme.quasiSeparatedFromGenericPointResidueFields D.subscheme
  exact inferInstanceAs
    (IsIntegralHom (Scheme.Hom.fromNormalization (Scheme.fromGenericPointResidueFields _)))

/-- An unramified normalization of the closed subscheme cut out by a divisor on a locally
Noetherian scheme is finite: it is integral and, being unramified, locally of finite type. -/
@[stacks 0CBR "the proof of (2) to (1), first step: an unramified `ν` is finite, being \
integral and locally of finite type (Tag 01WJ). Neither implication of the equivalence is \
asserted."]
public instance isFinite_divisorNormalization [Unramified (divisorNormalization D)] :
    IsFinite (divisorNormalization D) :=
  IsFinite.of_isIntegralHom_of_locallyOfFiniteType (divisorNormalization D)

/-- The morphism `D^ν ⟶ X` from the normalization of the closed subscheme cut out by a divisor to
the ambient scheme. -/
public noncomputable abbrev divisorNormalizationToAmbient :
    divisorNormalizationScheme D ⟶ X :=
  divisorNormalization D ≫ D.subschemeι

/-- The morphism `D^ν ⟶ X` is finite when the normalization of `D` is unramified: it is the
composition of the finite normalization with a closed immersion. -/
@[stacks 0CBR "the proof of (2) to (1), second step: `D^ν ⟶ X` is finite. Neither \
implication of the equivalence is asserted."]
public instance isFinite_divisorNormalizationToAmbient
    [Unramified (divisorNormalization D)] : IsFinite (divisorNormalizationToAmbient D) :=
  inferInstance

/-- The morphism `D^ν ⟶ X` is unramified when the normalization of `D` is: it is the composition
of the unramified normalization with a closed immersion. -/
@[stacks 0CBR "the proof of (2) to (1), second step: `D^ν ⟶ X` is unramified. Neither \
implication of the equivalence is asserted."]
public theorem unramified_divisorNormalizationToAmbient
    [Unramified (divisorNormalization D)] : Unramified (divisorNormalizationToAmbient D) :=
  MorphismProperty.comp_mem (@Unramified.{u}) _ _ inferInstance inferInstance

/-- Around any point of the ambient scheme the normalization of `D` becomes, after an étale base
change, a finite disjoint union of closed subschemes of the étale neighbourhood: the morphism
`D^ν ⟶ X` is finite and unramified, so Tag 04HJ applies to it. -/
@[stacks 0CBR "the proof of (2) to (1), third step: étale-locally on `X` the normalization is \
a finite disjoint union of closed subschemes of the étale neighbourhood (Tag 04HJ). The \
further shrinking making the chosen point lie on every `D_i` is not asserted, nor is either \
implication of the equivalence."]
public theorem exists_etaleNeighborhood_disjoint_closed_decomposition_divisorNormalization
    [Unramified (divisorNormalization D)] (p : X) :
    ∃ (U : EtaleNeighborhood X p) (n : ℕ)
      (V : Fin n → (pullback (divisorNormalizationToAmbient D) U.toBase).Opens),
      sSup (Set.range V) = ⊤ ∧ Pairwise (Disjoint on V) ∧
        ∀ j, IsClosedImmersion
          ((V j).ι ≫ pullback.snd (divisorNormalizationToAmbient D) U.toBase) :=
  have := unramified_divisorNormalizationToAmbient D
  exists_etaleNeighborhood_disjoint_closed_decomposition_of_finite_unramified
    (divisorNormalizationToAmbient D) p

/-- The scheme `Z_1` is the normalization of `D` itself: a one-fold fibre power has empty fat
diagonal and is the normalization. -/
@[stacks 0CBR "the identification `Z_1 = D^ν` used in the proof of (2) to (1). Neither \
implication of the equivalence is asserted."]
public noncomputable def normalizationDistinctOneIso :
    normalizationDistinct D 1 ≅ divisorNormalizationScheme D :=
  (fibrePower (divisorNormalization D) 1).isoOfEq
      (TopologicalSpace.Opens.ext (fibrePowerDistinctLocus_one (divisorNormalization D))) ≪≫
    (fibrePower (divisorNormalization D) 1).topIso ≪≫
    asIso (fibrePowerLeg (divisorNormalization D) 1 0)

/-- The identification of `Z_1` with the normalization is the inclusion of the complement of the
fat diagonal followed by the unique coordinate of the one-fold fibre power. -/
public theorem normalizationDistinctOneIso_hom :
    (normalizationDistinctOneIso D).hom =
      (normalizationDistinctOpens D 1).ι ≫ fibrePowerLeg (divisorNormalization D) 1 0 := by
  simp [normalizationDistinctOneIso]

/-- The morphism `Z_1 ⟶ X` is the morphism `D^ν ⟶ X` read through the identification of `Z_1`
with the normalization. -/
public theorem normalizationDistinctToAmbient_one :
    normalizationDistinctToAmbient D 1 =
      (normalizationDistinctOneIso D).hom ≫ divisorNormalizationToAmbient D := by
  rw [normalizationDistinctOneIso_hom]
  change (normalizationDistinctOpens D 1).ι ≫
    fibrePowerProj (divisorNormalization D) 1 ≫ D.subschemeι = _
  rw [← fibrePowerLeg_comp (divisorNormalization D) 1 0]
  simp [divisorNormalizationToAmbient]

/-- Condition (2) of Tag 0CBR makes the normalization of `D` a regular scheme: it is the scheme
`Z_1` of that condition. -/
@[stacks 0CBR "the proof of (2) to (1), fourth step, partially: the hypothesis on `Z_1` makes \
`D^ν` regular. The conclusion that each `D_i` is an effective Cartier divisor is not \
asserted."]
public theorem isRegular_divisorNormalizationScheme (h : IsNormalizationCrossingsDivisor D) :
    IsRegular (divisorNormalizationScheme D) := by
  obtain ⟨-, hν, hZ⟩ := h
  have := hν
  have : IsLocallyNoetherian D.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian D.subschemeι
  have : IsLocallyNoetherian (divisorNormalizationScheme D) :=
    LocallyOfFiniteType.isLocallyNoetherian (divisorNormalization D)
  exact isRegular_of_iso (normalizationDistinctOneIso D).symm (hZ 1 le_rfl).1

/-- Condition (2) of Tag 0CBR makes `D^ν ⟶ X` a local complete intersection morphism: it is the
morphism `Z_1 ⟶ X` of that condition, up to the identification of `Z_1` with the
normalization. -/
@[stacks 0CBR "the proof of (2) to (1), fourth step, partially: the hypothesis on `Z_1` makes \
`D^ν ⟶ X` a local complete intersection morphism. The conclusion that each `D_i` is an \
effective Cartier divisor is not asserted."]
public theorem isLocalCompleteIntersectionMorphism_divisorNormalizationToAmbient
    (h : IsNormalizationCrossingsDivisor D) :
    IsLocalCompleteIntersectionMorphism (divisorNormalizationToAmbient D) := by
  obtain ⟨-, hν, hZ⟩ := h
  have := hν
  have hlci := (hZ 1 le_rfl).2.1
  rw [normalizationDistinctToAmbient_one] at hlci
  exact (MorphismProperty.cancel_left_of_respectsIso @IsLocalCompleteIntersectionMorphism
    (normalizationDistinctOneIso D).hom (divisorNormalizationToAmbient D)).mp hlci

end Stacks.Divisors

end
