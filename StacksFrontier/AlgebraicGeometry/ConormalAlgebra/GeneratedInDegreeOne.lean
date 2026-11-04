module

public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.Immersion
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.SectionRings

/-!
# The conormal algebra is generated in degree one over an affine chart

Let `i : Z ⟶ X` be an immersion and `U ⊆ X` an affine open over which `i` restricts to a closed
immersion, with kernel ideal `I = ker(Γ(X, U) → Γ(Z, i⁻¹U))`. The degree-`n` sections of the
conormal algebra over `i⁻¹U` are `Iⁿ/Iⁿ⁺¹`, and `Iⁿ⁺¹ = I · Iⁿ`, so each one is a sum of products
of a degree-one section with a section of the preceding degree. That is
`SheafOfModules.GradedAlgebra.IsGeneratedInDegreeOne` for the conormal algebra at the chart.

This is the input that makes the extension of an identification of a conormal algebra from degrees
zero and one to all degrees unique, which is how [Stacks, Tag 0CAY] glues its chartwise
comparisons: with `SheafOfModules.GradedAlgebra.apply_eq_of_isGeneratedInDegreeOne` two
homomorphisms out of the conormal algebra agreeing in degrees zero and one agree on the sections
over every affine closed-immersion chart.

That is agreement over a *basis* of the source, not over every open, and it is all that holds:
a homogeneous section of degree `n` over a general open of `Z` is only locally a sum of products
of a degree-one section with a degree-`(n-1)` one, so `IsGeneratedInDegreeOne` of a conormal
algebra over an arbitrary open is not asserted here and is not expected. Turning the agreement
over the charts into equality of the two homomorphisms is the separatedness of the target sheaf,
and is not proved here; `SheafOfModules.GradedAlgebra.Hom.ext_of_isGeneratedInDegreeOne` asks for
generation in degree one over every object of the site and therefore does not apply directly.

## Main results

* `Stacks.Conormal.ConormalAlgebraData.isGeneratedInDegreeOne`: a graded algebra with the
  canonical local presentations of Tag 0630 is generated in degree one over every affine
  closed-immersion chart.
* `Stacks.Conormal.isGeneratedInDegreeOne_conormalAlgebra`: the conormal algebra of Tag 0630 is.

## Implementation notes

Nothing here uses the identification of the chart sections with the algebraic associated graded
(`AlgebraicGeometry.degreeEquiv`): the three fields `localMap`, `localMap_surjective` and
`localMap_mul` of `Stacks.Conormal.ConormalAlgebraData` already say everything needed, and
working with them directly keeps the statement at the level of the structure rather than of the
particular algebra `Stacks.Conormal.conormalAlgebra`.

The generating set of `I ^ (1 + n)` is handled by `Submodule.mul_induction_on` after
`pow_add` and `pow_one`, transported with `▸` rather than with `rw`: the representative's type
mentions the exponent `1 + n` too, so rewriting it in the membership hypothesis leaves a motive
that does not typecheck. Its additive step quantifies over arbitrary ring elements, with no
membership in `I ^ (1 + n)` available, so the predicate carried through the induction is the
*existential*
`∃ h : r ∈ I ^ (1 + n), localMap ⟨r, h⟩ ∈ P` rather than the universally quantified form; the
two agree by proof irrelevance wherever a membership is at hand.

The degree of the conclusion is `1 + (n : ℤ)` while the local presentations are indexed by `ℕ`,
and the two meet because `Int.ofNat` addition of two `Int.ofNat`s reduces to `Int.ofNat` of the
sum, so `((1 + n : ℕ) : ℤ)` and `1 + (n : ℤ)` are definitionally equal and no transport is
needed.

## References

* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
* [Stacks Project, Tag 0CAY](https://stacks.math.columbia.edu/tag/0CAY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Conormal

/-- **A graded algebra with the canonical local presentations of Tag 0630 is generated in degree
one over every affine closed-immersion chart.** The degree-`1 + n` sections over the chart are the
images of `I ^ (1 + n) = I · Iⁿ`, hence sums of products of a degree-one section with a degree-`n`
one. -/
theorem ConormalAlgebraData.isGeneratedInDegreeOne {Z X : Scheme.{u}} {i : Z ⟶ X}
    (A : ConormalAlgebraData i) (U : X.affineOpens)
    (hU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl)) :
    SheafOfModules.GradedAlgebra.IsGeneratedInDegreeOne A.algebra (op (i ⁻¹ᵁ U.1)) := by
  intro n P hP
  rw [AddSubgroup.eq_top_iff']
  -- Every representative in `I ^ (1 + n)` has its class in `P`.
  have key : ∀ a : ↥(chartIdeal i U ^ (1 + n)), A.localMap U hU (1 + n) a ∈ P := by
    intro a
    have heq : chartIdeal i U ^ (1 + n) = chartIdeal i U * chartIdeal i U ^ n := by
      rw [pow_add, pow_one]
    have hmul : (a : Γ(X, U)) ∈ chartIdeal i U * chartIdeal i U ^ n := heq ▸ a.property
    have hind : ∃ h : (a : Γ(X, U)) ∈ chartIdeal i U ^ (1 + n),
        A.localMap U hU (1 + n) ⟨(a : Γ(X, U)), h⟩ ∈ P := by
      refine Submodule.mul_induction_on hmul ?_ ?_
      · intro b hb c hc
        have hb1 : b ∈ chartIdeal i U ^ 1 := by rwa [pow_one]
        have hbc : b * c ∈ chartIdeal i U ^ (1 + n) := by
          rw [pow_add, pow_one]
          exact Ideal.mul_mem_mul hb hc
        refine ⟨hbc, ?_⟩
        have hval : ((⟨b * c, hbc⟩ : ↥(chartIdeal i U ^ (1 + n))) : Γ(X, U)) =
            ((⟨b, hb1⟩ : ↥(chartIdeal i U ^ 1)) : Γ(X, U)) *
              ((⟨c, hc⟩ : ↥(chartIdeal i U ^ n)) : Γ(X, U)) := rfl
        rw [A.localMap_mul U hU 1 n ⟨b, hb1⟩ ⟨c, hc⟩ ⟨b * c, hbc⟩ hval]
        exact hP _ _
      · rintro x y ⟨hx, hxP⟩ ⟨hy, hyP⟩
        refine ⟨Submodule.add_mem _ hx hy, ?_⟩
        have hsum : (⟨x + y, Submodule.add_mem _ hx hy⟩ :
            ↥(chartIdeal i U ^ (1 + n))) =
            (⟨x, hx⟩ : ↥(chartIdeal i U ^ (1 + n))) + ⟨y, hy⟩ := rfl
        rw [hsum, map_add]
        exact AddSubgroup.add_mem _ hxP hyP
    obtain ⟨h, hmem⟩ := hind
    have : (⟨(a : Γ(X, U)), h⟩ : ↥(chartIdeal i U ^ (1 + n))) = a := Subtype.ext rfl
    rwa [this] at hmem
  intro x
  obtain ⟨a, ha⟩ := A.localMap_surjective U hU (1 + n) x
  rw [← ha]
  exact key a

/-- The conormal algebra of an immersion is generated in degree one over every affine open on
which the immersion restricts to a closed immersion. No `@[stacks]` attribute is attached: this
is not one of the assertions of Tag 0630, it is a consequence of the local presentations that
tag asserts. -/
theorem isGeneratedInDegreeOne_conormalAlgebra {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (U : X.affineOpens) (hU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl)) :
    SheafOfModules.GradedAlgebra.IsGeneratedInDegreeOne
      (conormalAlgebra i).algebra (op (i ⁻¹ᵁ U.1)) :=
  (conormalAlgebra i).isGeneratedInDegreeOne U hU

end Stacks.Conormal

end
