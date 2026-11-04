module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Blowup.NormalizedBlowUp
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.Basic
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.FiniteType
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.Properties.Nagata

/-!
# Sequences of normalized blowups at closed points

A *sequence of normalized blowups* over a base scheme `S` is a tower
`Xₙ → ⋯ → X₁ → S` in which each step is the normalized blowup of the previous scheme at a
closed point. Over a normal, Nagata, locally Noetherian base every scheme in such a tower is
again normal, Nagata and locally Noetherian, and is proper over `S`.

## Main definitions

* `AlgebraicGeometry.NormalizedBlowUpSeq` is the predicate asserting that a morphism `X ⟶ S`
  is the composite of finitely many normalized blowups at closed points.

## Main results

* `AlgebraicGeometry.isNormal_isNagataScheme_and_isProper_normalizedBlowUp`: one normalized
  blowup of a Nagata scheme is normal, Nagata and proper over that scheme.
* `AlgebraicGeometry.NormalizedBlowUpSeq.properties`: every scheme in a sequence of normalized
  blowups over a normal, Nagata, locally Noetherian base is normal, Nagata and locally
  Noetherian, and is proper over the base.

## Implementation notes

Finiteness of the sequence is expressed by the inductive predicate rather than by an indexed
family, and the morphism carried by the predicate is the composite down to the base, so the
properness statement is about the composite and not only about the individual steps.

A single normalized blowup is the normalization of a blowup, so the step splits into two halves.
Properness of the blowup morphism of a locally Noetherian scheme gives the blowup locally of
finite type over the base, hence Nagata; finiteness of the normalization morphism of a Nagata
scheme then gives the second half, and a finite morphism is proper and locally of finite type.
Being Nagata is equivalent to being locally Noetherian and universally Japanese, which is how
local Noetherianity is recovered at each stage instead of being propagated separately.

Normality of the base is not used in the inductive step: a normalization is normal whatever the
scheme normalized, so the base case is the only place the hypothesis is needed.

## References

* [Stacks Project, Tag 0BBS](https://stacks.math.columbia.edu/tag/0BBS)
* [Stacks Project, Tag 0BFT](https://stacks.math.columbia.edu/tag/0BFT)
* [Stacks Project, Tag 035A](https://stacks.math.columbia.edu/tag/035A)
* [Stacks Project, Tag 035S](https://stacks.math.columbia.edu/tag/035S)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A Nagata scheme is locally Noetherian. -/
private theorem isLocallyNoetherian_of_isNagataScheme {X : Scheme.{u}} (h : IsNagataScheme X) :
    IsLocallyNoetherian X :=
  ((isNagataScheme_iff_isLocallyNoetherian_and_isUniversallyJapaneseScheme X).mp h).1

/-- The normalization of the blowup of a Nagata, locally Noetherian scheme `X` in a
quasi-coherent ideal is normal and Nagata, and is proper over `X`. -/
private theorem isNormal_isNagataScheme_and_isProper_normalization_blowUp {X : Scheme.{u}}
    (I : X.IdealSheafData) (hNagata : IsNagataScheme X) [IsLocallyNoetherian X]
    (hfin : ∀ U : (blowUp I).Opens, IsCompact (U : Set (blowUp I)) →
      (irreducibleComponents U).Finite) :
    IsNormal (Scheme.normalizationScheme (blowUp I) hfin) ∧
      IsNagataScheme (Scheme.normalizationScheme (blowUp I) hfin) ∧
      IsProper (Scheme.normalization (blowUp I) hfin ≫ blowUpToBase I) := by
  have hNagataBlowUp : IsNagataScheme (blowUp I) :=
    isNagataScheme_of_locallyOfFiniteType (blowUpToBase I) hNagata
  have hfinite : IsFinite (Scheme.normalization (blowUp I) hfin) :=
    Scheme.isFinite_normalization hNagataBlowUp hfin
  exact ⟨Scheme.isNormal_normalizationScheme (blowUp I) hfin,
    isNagataScheme_of_locallyOfFiniteType (Scheme.normalization (blowUp I) hfin) hNagataBlowUp,
    inferInstance⟩

/-- **Stacks Project, Tag 0BFT.** The normalized blowup of a Nagata scheme `X` at a closed point
is a normal, Nagata scheme, and its structure morphism is proper over `X`. -/
@[stacks 0BFT]
public theorem isNormal_isNagataScheme_and_isProper_normalizedBlowUp {X : Scheme.{u}}
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) (hx : IsClosed ({x} : Set X)) (hNagata : IsNagataScheme X) :
    IsNormal (Stacks.Blowup.normalizedBlowUpScheme X hX x hx) ∧
      IsNagataScheme (Stacks.Blowup.normalizedBlowUpScheme X hX x hx) ∧
      IsProper (Stacks.Blowup.normalizedBlowUp X hX x hx) := by
  have := isLocallyNoetherian_of_isNagataScheme hNagata
  exact isNormal_isNagataScheme_and_isProper_normalization_blowUp
    (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)) hNagata
    (Stacks.Blowup.finite_irreducibleComponents_blowUp _ hX)

/-- A finite sequence of normalized blowups at closed points over a base `S`:
`Xₙ → ⋯ → X₁ → S`. The indexed morphism is the composite down to `S`. -/
public inductive NormalizedBlowUpSeq (S : Scheme.{u}) : (X : Scheme.{u}) → (X ⟶ S) → Prop where
  | refl : NormalizedBlowUpSeq S S (CategoryTheory.CategoryStruct.id S)
  | blowUp {X : Scheme.{u}} {f : X ⟶ S} (prev : NormalizedBlowUpSeq S X f)
      (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
      (x : X) (hx : IsClosed ({x} : Set X)) :
      NormalizedBlowUpSeq S (Stacks.Blowup.normalizedBlowUpScheme X hX x hx)
        (Stacks.Blowup.normalizedBlowUp X hX x hx ≫ f)

/-- Over a normal, Nagata, locally Noetherian base, every scheme in a sequence of normalized
blowups is again normal, Nagata and locally Noetherian, and is proper over the base. -/
public theorem NormalizedBlowUpSeq.properties {S X : Scheme.{u}} {f : X ⟶ S}
    (hseq : NormalizedBlowUpSeq S X f)
    (hS : IsNagataScheme S) [IsLocallyNoetherian S] [IsNormal S] :
    IsNagataScheme X ∧ IsLocallyNoetherian X ∧ IsNormal X ∧ IsProper f := by
  induction hseq with
  | refl => exact ⟨hS, inferInstance, inferInstance, inferInstance⟩
  | blowUp prev hX x hx ih =>
    obtain ⟨hNagata, -, -, hproper⟩ := ih
    obtain ⟨hnormal, hnagata, hstep⟩ :=
      isNormal_isNagataScheme_and_isProper_normalizedBlowUp hX x hx hNagata
    exact ⟨hnagata, isLocallyNoetherian_of_isNagataScheme hnagata, hnormal, inferInstance⟩

end AlgebraicGeometry

end
