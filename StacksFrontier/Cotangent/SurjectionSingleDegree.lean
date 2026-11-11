module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import StacksFrontier.Cotangent.Surjection
public import StacksFrontier.Cotangent.SurjectivePresentationHigherHomology

/-!
# When the cotangent complex of a surjection is a single module in degree `-1`

Let `A → B` be a surjective ring map with kernel `I`. Its cotangent complex `L_{B/A}` is
concentrated in cohomological degrees `≤ 0`, its degree-zero homology vanishes and its
degree `-1` homology is the conormal module `I/I²`; these are Tag 08RA, available as
`CommAlgCat.cotangentComplex_isZero_homology_zero` and
`CommAlgCat.cotangentComplex_homologyNegOneIso`. Consequently the *only* obstruction to
`L_{B/A}` being quasi-isomorphic to `I/I²[1]` is the vanishing of its homology in the
degrees `≤ -2`.

This file isolates that obstruction. It proves that the vanishing in degrees `≤ -2` is
sufficient — the resulting derived-category isomorphism is read off the `t`-structure — and it
transports the vanishing to the conormal complex, which by Tag 09D5 computes the homology of
`L_{B/A}` in those degrees.

## Main results

* `CommAlgCat.isZero_homology_cotangentComplex_of_isZero_homology_conormalComplex`: in
  cohomological degree `-n` with `n ≥ 2`, the homology of `L_{B/A}` vanishes as soon as that of
  the conormal complex `𝒥•/𝒥•²` of the standard resolution does. This is Tag 09D5, read as an
  implication; it needs no surjectivity.
* `CommAlgCat.isZero_homology_cotangentComplex_of_ne_negOne`: for a surjective `A → B` whose
  cotangent complex has no homology in degrees `≤ -2`, the homology vanishes in every degree
  other than `-1`.
* `CommAlgCat.isGE_Q_obj_cotangentComplex_negOne` and
  `CommAlgCat.isLE_Q_obj_cotangentComplex_negOne`: under the same hypothesis, `L_{B/A}` lies in
  `D^{≥ -1}(B)` and in `D^{≤ -1}(B)`.
* `CommAlgCat.nonempty_cotangentComplex_iso_single_of_isZero_homology_le_negTwo`: under the same
  hypothesis, `L_{B/A}` is isomorphic in `D(B)` to `I/I²` placed in cohomological degree `-1`,
  that is, to `I/I²[1]`.
* `CommAlgCat.nonempty_cotangentComplex_iso_single_of_isZero_homology_conormalComplex`: the same
  conclusion from the acyclicity of the conormal complex in degrees `≤ -2`.

## No `stacks` attribute

The statement of [Stacks, Tag 08SK] is that `L_{B/A}` is quasi-isomorphic to `I/I²[1]` whenever
`I` is a Koszul-regular ideal — `Ideal.IsKoszulRegular`, Tag 07CV (2). The results below do not
state that and no `stacks` attribute is attached to any of them: each carries the vanishing in
degrees `≤ -2` as an explicit hypothesis, and it is exactly that vanishing which the
Koszul-regularity of `I` is supposed to supply. Deriving it from `Ideal.IsKoszulRegular` is
Quillen's theorem; in the Stacks Project it is Tag 08SJ, reduced to the base case Tag 08SI
through the fundamental triangle of Tag 08QX. Both are available, downstream of this file:
Tag 08QX is `CommAlgCat.productFundamentalTriangle_distinguished` of
`StacksFrontier/Cotangent/Triangle/ProductDescent.lean`, Tag 08SI is
`CommAlgCat.nonempty_cotangentComplex_retraction_iso_single_unconditional` of
`StacksFrontier/Cotangent/PolynomialRetractionUnconditional.lean`, and Tag 08SJ is
`CommAlgCat.nonempty_cotangentComplex_iso_single_of_isKoszulRegular_sequence` of
`StacksFrontier/Cotangent/KoszulRegularQuotient.lean` — each of which imports this file and
consumes the results below. What this file contributes is that the whole of Tag 08SK reduces to
that one vanishing, with the `t`-structure bookkeeping and the degree-`-1` identification already
discharged; the vanishing itself is not proved here, so no attribute is placed.

## Implementation notes

The isomorphism is not constructed as data. `L_{B/A}` lying in `D^{≥ -1}(B)` and in
`D^{≤ -1}(B)` produces, through
`DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE`, *some* module with an
isomorphism to the shifted single complex on it; that module is then identified with the
degree `-1` homology, hence with `I/I²`. The module is obtained from an existential, so the
conclusion is `Nonempty` of an isomorphism — which is what "quasi-isomorphic" asserts.

The vanishing in positive degrees is not assumed: the terms of `L_{B/A}` themselves vanish
there (`CommAlgCat.cotangentComplex_isZero_pos`), so the homology does.

## References

* [Stacks Project, Tag 08SK](https://stacks.math.columbia.edu/tag/08SK)
* [Stacks Project, Tag 08RA](https://stacks.math.columbia.edu/tag/08RA)
* [Stacks Project, Tag 09D5](https://stacks.math.columbia.edu/tag/09D5)
* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CommAlgCat

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A)

/-- **Tag 09D5, read as an implication.** In cohomological degree `-n` with `n ≥ 2` the homology
of `L_{B/A}` is the homology of the conormal complex `𝒥•/𝒥•²` of the standard resolution, so it
vanishes as soon as the latter does. No surjectivity is needed. -/
theorem isZero_homology_cotangentComplex_of_isZero_homology_conormalComplex
    (n : ℕ) (hn : 2 ≤ n)
    (hz : IsZero ((Stacks.Cotangent.conormalComplex A B).homology (-(n : ℤ)))) :
    IsZero ((cotangentComplex A B).homology (-(n : ℤ))) := by
  have : IsIso (HomologicalComplex.homologyMap
      (Stacks.Cotangent.conormalToCotangentComplex A B) (-(n : ℤ))) :=
    Stacks.Cotangent.isIso_homologyMap_conormalToCotangentComplex A B n hn
  exact hz.of_iso (asIso (HomologicalComplex.homologyMap
    (Stacks.Cotangent.conormalToCotangentComplex A B) (-(n : ℤ)))).symm

section Surjective

/-- For a surjective `A → B` whose cotangent complex has no homology in the degrees `≤ -2`, the
homology vanishes in every cohomological degree other than `-1`: below `-1` by hypothesis, at `0`
by Tag 08RA, and above `0` because the terms of the complex vanish there. -/
theorem isZero_homology_cotangentComplex_of_ne_negOne
    (h : Function.Surjective (algebraMap A B))
    (hlow : ∀ i : ℤ, i ≤ -2 → IsZero ((cotangentComplex A B).homology i))
    (i : ℤ) (hi : i ≠ -1) :
    IsZero ((cotangentComplex A B).homology i) := by
  rcases lt_trichotomy i 0 with hneg | rfl | hpos
  · exact hlow i (by omega)
  · exact cotangentComplex_isZero_homology_zero A B h
  · exact ShortComplex.isZero_homology_of_isZero_X₂ ((cotangentComplex A B).sc i)
      (cotangentComplex_isZero_pos A B i hpos)

/-- Under the same hypothesis, the derived-category homology of `L_{B/A}` vanishes away from
degree `-1`. -/
private theorem isZero_homologyFunctor_obj_Q_cotangentComplex_of_ne_negOne
    (h : Function.Surjective (algebraMap A B))
    (hlow : ∀ i : ℤ, i ≤ -2 → IsZero ((cotangentComplex A B).homology i))
    (i : ℤ) (hi : i ≠ -1) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) i).obj
      (DerivedCategory.Q.obj (cotangentComplex A B))) :=
  (isZero_homology_cotangentComplex_of_ne_negOne A B h hlow i hi).of_iso
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} B) i).app
      (cotangentComplex A B))

/-- Under the same hypothesis, `L_{B/A}` lies in `D^{≥ -1}(B)`. -/
theorem isGE_Q_obj_cotangentComplex_negOne
    (h : Function.Surjective (algebraMap A B))
    (hlow : ∀ i : ℤ, i ≤ -2 → IsZero ((cotangentComplex A B).homology i)) :
    (DerivedCategory.Q.obj (cotangentComplex A B)).IsGE (-1) :=
  (DerivedCategory.isGE_iff _ (-1)).2 fun i hi =>
    isZero_homologyFunctor_obj_Q_cotangentComplex_of_ne_negOne A B h hlow i (by omega)

/-- Under the same hypothesis, `L_{B/A}` lies in `D^{≤ -1}(B)`. -/
theorem isLE_Q_obj_cotangentComplex_negOne
    (h : Function.Surjective (algebraMap A B))
    (hlow : ∀ i : ℤ, i ≤ -2 → IsZero ((cotangentComplex A B).homology i)) :
    (DerivedCategory.Q.obj (cotangentComplex A B)).IsLE (-1) :=
  (DerivedCategory.isLE_iff _ (-1)).2 fun i hi =>
    isZero_homologyFunctor_obj_Q_cotangentComplex_of_ne_negOne A B h hlow i (by omega)

/-- **The conclusion of [Stacks, Tag 08SK], granted the vanishing of `H^i(L_{B/A})` for
`i ≤ -2`.** For a surjective ring map `A → B` with kernel `I`, if the cotangent complex has no
homology in the degrees `≤ -2`, then it is isomorphic in `D(B)` to the conormal module `I/I²`
placed in cohomological degree `-1`, that is, to `I/I²[1]`.

No `stacks` attribute is attached: the carried hypothesis is the entire content that
Koszul-regularity of `I` is meant to provide. -/
theorem nonempty_cotangentComplex_iso_single_of_isZero_homology_le_negTwo
    (h : Function.Surjective (algebraMap A B))
    (hlow : ∀ i : ℤ, i ≤ -2 → IsZero ((cotangentComplex A B).homology i)) :
    Nonempty (DerivedCategory.Q.obj (cotangentComplex A B) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{max u v} B) (-1)).obj
        (ModuleCat.of B (surjectionExtension A B h).Cotangent)) := by
  have : (DerivedCategory.Q.obj (cotangentComplex A B)).IsGE (-1) :=
    isGE_Q_obj_cotangentComplex_negOne A B h hlow
  have : (DerivedCategory.Q.obj (cotangentComplex A B)).IsLE (-1) :=
    isLE_Q_obj_cotangentComplex_negOne A B h hlow
  obtain ⟨Y, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
    (DerivedCategory.Q.obj (cotangentComplex A B)) (-1)
  refine ⟨e ≪≫ (DerivedCategory.singleFunctor (ModuleCat.{max u v} B) (-1)).mapIso
    (((DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{max u v} B) (-1)).app Y).symm ≪≫
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) (-1)).mapIso e).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} B) (-1)).app
        (cotangentComplex A B) ≪≫
      cotangentComplex_homologyNegOneIso A B h)⟩

/-- The same conclusion from the acyclicity of the conormal complex of the standard resolution in
the degrees `≤ -2`, which by Tag 09D5 is an equivalent hypothesis. -/
theorem nonempty_cotangentComplex_iso_single_of_isZero_homology_conormalComplex
    (h : Function.Surjective (algebraMap A B))
    (hac : ∀ n : ℕ, 2 ≤ n →
      IsZero ((Stacks.Cotangent.conormalComplex A B).homology (-(n : ℤ)))) :
    Nonempty (DerivedCategory.Q.obj (cotangentComplex A B) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{max u v} B) (-1)).obj
        (ModuleCat.of B (surjectionExtension A B h).Cotangent)) := by
  refine nonempty_cotangentComplex_iso_single_of_isZero_homology_le_negTwo A B h ?_
  intro i hi
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = -(n : ℤ) := ⟨(-i).toNat, by omega⟩
  exact isZero_homology_cotangentComplex_of_isZero_homology_conormalComplex A B n (by omega)
    (hac n (by omega))

end Surjective

end CommAlgCat

end
