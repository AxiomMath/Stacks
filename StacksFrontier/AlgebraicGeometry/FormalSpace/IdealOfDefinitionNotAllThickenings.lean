module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalScheme.IdealOfDefinition
public import StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealOfDefinitionExample
public import StacksFrontier.Topology.Algebra.AdicTopology.IdealOfDefinition
public import StacksFrontier.Topology.Algebra.AdicTopology.PadicComplexInt

/-!
# Ideals of definition do not classify the thickenings

**Stacks 0AIV** gives, for a formal scheme `𝔛` in the sense of McQuillan, a one-to-one
correspondence between the *weak* ideals of definition of `𝔛` and the thickenings
`Z → h_𝔛`, sending `ℐ` to `Z = (𝔛, 𝒪_𝔛/ℐ)`. **Stacks 0AIW** records that the ideals of
definition of a formal scheme à la EGA do *not* give the same correspondence, and points at
Example **Stacks 0CB8** for the reason: there is a thickening whose weak ideal of definition is
not an ideal of definition, so the restriction of the correspondence of Stacks 0AIV to the
ideals of definition misses that thickening.

This file assembles that negative statement out of the halves of Stacks 0CB8 already proved in
`StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealOfDefinitionExample`, and instantiates it on
the ring of integers of the field `ℂ_[p]` of `p`-adic complex numbers, which satisfies the
hypotheses of Stacks 0CB8 unconditionally
(`StacksFrontier.Topology.Algebra.AdicTopology.PadicComplexInt`).

## Main results

* `AlgebraicGeometry.FormalSpace.WeakIdealOfDefinitionExample`
  `.isThickening_residueField_and_not_isIdealOfDefinition`: for a valuation ring `(A, 𝔪, κ)`
  which is `(π)`-adically complete with `𝔪` the radical of `(π)` and not finitely generated, the
  residue-field stage `Spec κ → Spf A` is a thickening whose weak ideal of definition `𝔪` is not
  an ideal of definition.
* `PadicComplexInt.isWeakIdealOfDefinition_maximalIdeal_and_not_isIdealOfDefinition`: the maximal
  ideal of the ring of integers of `ℂ_[p]` is a weak ideal of definition which is not an ideal of
  definition. This is unconditional, so the failure above is not vacuous.
* `PadicComplexInt.isThickening_residueField_not_from_idealOfDefinition`: the same failure for
  the formal spectrum of the ring of integers of `ℂ_[p]`.
* `PadicComplexInt.exists_isWeakIdealOfDefinitionOn_not_isIdealOfDefinitionOn`: a formal scheme à
  la EGA carrying an ideal sheaf which is a weak ideal of definition over its affine formal open
  subschemes without being an ideal of definition over them. The witness is the
  pseudo-discretisation of `Spec (𝒪_{ℂ_p}/(p))`, whose nilradical is not nilpotent exactly
  because the maximal ideal of `𝒪_{ℂ_p}` is not an ideal of definition.

## Implementation notes

The thickening is the one of Stacks 0CB8, namely the colimit cocone map of the formal spectrum of
`A` at the stage indexed by the weak ideal of definition `𝔪`; being a thickening is phrased, as
in `WeakIdealOfDefinitionExample`, as the relative morphism property of
`Stacks.Thickenings.IsThickening` pulled back along `AlgebraicGeometry.BigFppfOver.toScheme`, and
the presentation `D` of the formal spectrum over a big fppf site is an input, exactly as it is for
the statements of Stacks 0CB8 this file combines.

What is *not* stated here is that the correspondence of Stacks 0AIV is a bijection: that half of
Stacks 0AIV is not carried by this library, only its two definitions and their locality
(`StacksFrontier.AlgebraicGeometry.FormalScheme.WeakIdealOfDefinition`). The negative clause of
Stacks 0AIW is therefore recorded in the form the source's own reason for it takes — a thickening
together with the weak ideal of definition it corresponds to, which is not an ideal of definition
— rather than as the non-surjectivity of a map that has no name here.

## References

* [Stacks Project, Tag 0AIW](https://stacks.math.columbia.edu/tag/0AIW)
* [Stacks Project, Tag 0AIV](https://stacks.math.columbia.edu/tag/0AIV)
* [Stacks Project, Tag 0CB8](https://stacks.math.columbia.edu/tag/0CB8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry.FormalSpace.WeakIdealOfDefinitionExample

variable {A : Type u} [CommRing A] [IsLocalRing A]
  [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
  (π : A)

/-- **Stacks 0AIW**, the failure of the correspondence of Stacks 0AIV for ideals of definition.
For a valuation ring `(A, 𝔪, κ)` which is `(π)`-adically complete for a nonzero `π ∈ 𝔪` whose
radical is `𝔪`, and whose maximal ideal is not finitely generated, the residue-field stage
`Spec κ ⟶ Spf A` of the formal spectrum is a thickening, while the weak ideal of definition `𝔪`
to which the correspondence of Stacks 0AIV attaches it is *not* an ideal of definition. So the
correspondence between weak ideals of definition and thickenings does not restrict to a
correspondence between ideals of definition and thickenings. -/
@[stacks 0AIW "we do NOT get the same correspondence between ideals of definition and \
thickenings as in Stacks 0AIV: the residue-field stage of Spf A is a thickening while the weak \
ideal of definition it corresponds to is not an ideal of definition (Stacks 0CB8); the \
presentation `D` of the formal spectrum over a big fppf site is an input, as it is throughout \
the statements of Stacks 0CB8 combined here"]
theorem isThickening_residueField_and_not_isIdealOfDefinition [IsDomain A]
    (hval : IsValuationRing A) (hπm : π ∈ maximalIdeal A)
    (hadic : IsAdic (Ideal.span ({π} : Set A)))
    (hrad : (Ideal.span ({π} : Set A)).radical = maximalIdeal A)
    (hnotfg : ¬ (maximalIdeal A).FG)
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (D : QuotientSystem B S hS A) :
    let J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I } :=
      ⟨maximalIdeal A, isWeakIdealOfDefinition_maximalIdeal π hadic hrad⟩
    (MorphismProperty.relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)))
      (formalSpectrumInclusion D (OrderDual.toDual J)) ∧
      ¬ TopologicalRing.IsIdealOfDefinition J.1 :=
  ⟨isThickening_residueField π hadic hrad D,
    not_isIdealOfDefinition_maximalIdeal π hval hπm hadic hnotfg⟩

end AlgebraicGeometry.FormalSpace.WeakIdealOfDefinitionExample

namespace PadicComplexInt

open AlgebraicGeometry.FormalSpace AlgebraicGeometry.FormalSpace.WeakIdealOfDefinitionExample

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- **Stacks 0AIW**, the negative clause on the example of Stacks 0CB8. The maximal ideal of the
ring of integers of the field `ℂ_[p]` of `p`-adic complex numbers is a weak ideal of definition
of that admissible topological ring, and it is not an ideal of definition. So the two notions
differ, and the correspondence of Stacks 0AIV between weak ideals of definition and thickenings
cannot restrict to one between ideals of definition and thickenings. -/
@[stacks 0AIW "the negative clause is not vacuous: in the ring of integers of ℂ_[p] the maximal \
ideal is a weak ideal of definition and is not an ideal of definition",
  stacks 0CB8 "a weak ideal of definition that is not an ideal of definition, on the ring of \
integers of ℂ_[p]"]
theorem isWeakIdealOfDefinition_maximalIdeal_and_not_isIdealOfDefinition :
    TopologicalRing.IsWeakIdealOfDefinition (maximalIdeal (PadicComplexInt p)) ∧
      ¬ TopologicalRing.IsIdealOfDefinition (maximalIdeal (PadicComplexInt p)) :=
  ⟨isWeakIdealOfDefinition_maximalIdeal (p : PadicComplexInt p) (isAdic_span_p p)
      (radical_span_p p),
    not_isIdealOfDefinition_maximalIdeal (p : PadicComplexInt p) (isValuationRing p)
      (natCast_mem_maximalIdeal p) (isAdic_span_p p) (not_fg_maximalIdeal p)⟩

/-- **Stacks 0AIW**, the negative clause on the example of Stacks 0CB8, geometrically: the
residue-field stage `Spec ℂ_[p]^- ⟶ Spf 𝒪_{ℂ_p}` of the formal spectrum of the ring of integers
of `ℂ_[p]` is a thickening whose weak ideal of definition, the maximal ideal, is not an ideal of
definition. -/
@[stacks 0AIW "the negative clause on the example of Stacks 0CB8: a thickening of the formal \
spectrum of the ring of integers of ℂ_[p] whose weak ideal of definition is not an ideal of \
definition; the presentation `D` of the formal spectrum over a big fppf site is an input"]
theorem isThickening_residueField_not_from_idealOfDefinition
    {B : BigFppfSite.{0}} {S : Scheme.{0}} {hS : B.Contains S}
    (D : QuotientSystem B S hS (PadicComplexInt p)) :
    let J : { I : Ideal (PadicComplexInt p) // TopologicalRing.IsWeakIdealOfDefinition I } :=
      ⟨maximalIdeal (PadicComplexInt p),
        (isWeakIdealOfDefinition_maximalIdeal_and_not_isIdealOfDefinition p).1⟩
    (MorphismProperty.relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{0})
        (BigFppfOver.toScheme B S hS)))
      (formalSpectrumInclusion D (OrderDual.toDual J)) ∧
      ¬ TopologicalRing.IsIdealOfDefinition J.1 :=
  isThickening_residueField_and_not_isIdealOfDefinition (p : PadicComplexInt p)
    (isValuationRing p) (natCast_mem_maximalIdeal p) (isAdic_span_p p) (radical_span_p p)
    (not_fg_maximalIdeal p) D

/-- **Stacks 0CB8.** The ideal `(p)` is an ideal of definition of the ring of integers of
`ℂ_[p]`: its topology is the `(p)`-adic one. -/
@[stacks 0CB8 "the p-adic complex integers"]
theorem isIdealOfDefinition_span_p :
    TopologicalRing.IsIdealOfDefinition
      (Ideal.span ({(p : PadicComplexInt p)} : Set (PadicComplexInt p))) :=
  ⟨by simpa [pow_one] using (isAdic_iff.mp (isAdic_span_p p)).1 1,
    (isAdic_iff.mp (isAdic_span_p p)).2⟩

/-- No power of the maximal ideal of the ring of integers of `ℂ_[p]` lies inside `(p)`: otherwise
the maximal ideal would be an ideal of definition, which it is not. -/
theorem not_maximalIdeal_pow_le_span_p (n : ℕ) :
    ¬ (maximalIdeal (PadicComplexInt p)) ^ n ≤
      Ideal.span ({(p : PadicComplexInt p)} : Set (PadicComplexInt p)) := by
  intro hle
  refine (isWeakIdealOfDefinition_maximalIdeal_and_not_isIdealOfDefinition p).2
    ⟨(isWeakIdealOfDefinition_maximalIdeal_and_not_isIdealOfDefinition p).1.1, fun V hV => ?_⟩
  obtain ⟨m, hm⟩ := (isIdealOfDefinition_span_p p).2 V hV
  refine ⟨n * m, fun x hx => hm ?_⟩
  rw [pow_mul] at hx
  exact pow_le_pow_left' hle m hx

/-- The quotient of the ring of integers of `ℂ_[p]` by `(p)` is nontrivial: `(p)` lies inside the
maximal ideal. -/
instance nontrivial_quotient_span_p :
    Nontrivial (PadicComplexInt p ⧸
      Ideal.span ({(p : PadicComplexInt p)} : Set (PadicComplexInt p))) :=
  Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (maximalIdeal.isMaximal (PadicComplexInt p)).ne_top
      (Ideal.span_le.mpr (by rintro x rfl; exact natCast_mem_maximalIdeal p)))

/-- The quotient of the ring of integers of `ℂ_[p]` by `(p)` has exactly one prime ideal: a prime
of the quotient pulls back to a prime of the ring containing `(p)`, hence containing the radical
`𝔪` of `(p)`, hence equal to `𝔪`. -/
instance subsingleton_primeSpectrum_quotient_span_p :
    Subsingleton (PrimeSpectrum (PadicComplexInt p ⧸
      Ideal.span ({(p : PadicComplexInt p)} : Set (PadicComplexInt p)))) := by
  have hkey : ∀ q : PrimeSpectrum (PadicComplexInt p ⧸
        Ideal.span ({(p : PadicComplexInt p)} : Set (PadicComplexInt p))),
      Ideal.comap (Ideal.Quotient.mk
          (Ideal.span ({(p : PadicComplexInt p)} : Set (PadicComplexInt p)))) q.asIdeal =
        maximalIdeal (PadicComplexInt p) := by
    intro q
    have hprime := Ideal.comap_isPrime (Ideal.Quotient.mk
      (Ideal.span ({(p : PadicComplexInt p)} : Set (PadicComplexInt p)))) q.asIdeal
    refine ((maximalIdeal.isMaximal (PadicComplexInt p)).eq_of_le hprime.ne_top ?_).symm
    rw [← radical_span_p p]
    exact hprime.radical_le_iff.mpr fun x hx => by
      simp [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  exact ⟨fun q q' => PrimeSpectrum.ext (Ideal.comap_injective_of_surjective _
    Ideal.Quotient.mk_surjective ((hkey q).trans (hkey q').symm))⟩

/-- No power of the nilradical of the quotient of the ring of integers of `ℂ_[p]` by `(p)`
vanishes: the nilradical contains the image of the maximal ideal `𝔪`, because `𝔪` is the radical
of `(p)`, so a vanishing power would put a power of `𝔪` inside `(p)`. -/
theorem nilradical_pow_ne_bot_quotient_span_p (n : ℕ) :
    (nilradical (PadicComplexInt p ⧸
      Ideal.span ({(p : PadicComplexInt p)} : Set (PadicComplexInt p)))) ^ n ≠ ⊥ := by
  set A := PadicComplexInt p
  set J : Ideal A := Ideal.span ({(p : A)} : Set A) with hJ
  intro hbot
  have hmle : Ideal.map (Ideal.Quotient.mk J) (maximalIdeal A) ≤ nilradical (A ⧸ J) := by
    refine Ideal.map_le_iff_le_comap.mpr fun x hx => ?_
    obtain ⟨k, hk⟩ := Ideal.mem_radical_iff.mp (by rw [radical_span_p p]; exact hx)
    exact mem_nilradical.mpr ⟨k, by
      rw [← map_pow]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hk⟩
  refine not_maximalIdeal_pow_le_span_p p n ?_
  have hmapbot : Ideal.map (Ideal.Quotient.mk J) ((maximalIdeal A) ^ n) = ⊥ := by
    rw [Ideal.map_pow]
    exact le_antisymm (hbot ▸ pow_le_pow_left' hmle n) bot_le
  simpa [Ideal.mk_ker] using
    (Ideal.map_eq_bot_iff_le_ker (Ideal.Quotient.mk J)).mp hmapbot

open AlgebraicGeometry.LocallyTopologicallyRingedSpace

/-- **Stacks 0AIW**, the negative clause at the level of ideal sheaves, unconditionally. The
pseudo-discretisation of `Spec (𝒪_{ℂ_p}/(p))` is a formal scheme à la EGA whose nilradical is a
weak ideal of definition over its affine formal open subschemes and is not an ideal of definition
over them: the ring has the single prime `𝔪/(p)`, and no power of its nilradical vanishes because
no power of `𝔪` lies inside `(p)`. -/
@[stacks 0AIW "the negative clause is not vacuous at the level of ideal sheaves: an explicit \
formal scheme à la EGA with a weak ideal of definition that is not an ideal of definition"]
theorem exists_isWeakIdealOfDefinitionOn_not_isIdealOfDefinitionOn
    (q : ℕ) [Fact (Nat.Prime q)] :
    ∃ (X : LTRS.{0}) (_ : IsFormalScheme X) (I : LocallyTopologicallyRingedSpace.IdealSheaf X),
      I.IsWeakIdealOfDefinitionOn (IsAffineFormalOpen X) ∧
        ¬ I.IsIdealOfDefinitionOn (IsAffineFormalOpen X) :=
  exists_isWeakIdealOfDefinitionOn_not_isIdealOfDefinitionOn_of_nilradical
    (PadicComplexInt q ⧸ Ideal.span ({(q : PadicComplexInt q)} : Set (PadicComplexInt q)))
    (nilradical_pow_ne_bot_quotient_span_p q)

end PadicComplexInt

end
