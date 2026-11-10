module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameCovers.RegularDivisorNormalization
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.RegularPurity
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameRamification.CodimensionOnePullbackRamification
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization

/-!
# The normalization of `X` in a tame cover of `X ∖ D`

Let `X` be a locally Noetherian scheme, `D ⊆ X` an effective Cartier divisor which is a regular
scheme, and `Y ⟶ X ∖ D` finite étale and tamely ramified over `X` in codimension one. Then the
normalization `π : Y' ⟶ X` of `X` in `Y` is finite locally free, restricts to `Y` over `X ∖ D`,
`D' = π⁻¹(D)_red` is an effective Cartier divisor on `Y'` which is a regular scheme, and étale
locally on `X` the morphism `Y' ⟶ X` is a finite disjoint union of standard morphisms
`Spec(A[x]/(x^e - φ)) ⟶ Spec(A)`. This is [Stacks, Tag 0EYH].

## Main results

* `AlgebraicGeometry.TameCovers.normalization_of_isTamelyRamifiedInCodimensionOne_of_isRegular`:
  [Stacks, Tag 0EYH].

## Implementation notes

The proof is `AlgebraicGeometry.TameCovers.normalization_of_isTamelyRamifiedInCodimensionOne`,
which derives every part of the tag from Abhyankar's lemma for a regular divisor
([Stacks, Tag 0EYG]) and smooth base change of normalization ([Stacks, Tag 03GV]), with the
input of Abhyankar's lemma, that tameness pulls back along the étale charts, discharged by
`Stacks.FundamentalGroup.pulledBackCover_isTamelyRamifiedInCodimensionOne` ([Stacks, Tag 0EYD]).

The normalization of `X` in `Y` is Mathlib's relative normalization of `Y ⟶ X ∖ D ⟶ X`, and
`D'` is the closed subscheme cut out by the radical of the pulled-back ideal sheaf
`D.comap π`. "`D` is a regular scheme" and "`D'` is a regular scheme" are
`AlgebraicGeometry.IsRegular` of the closed subschemes ([Stacks, Tag 02IS]).

## References

* [Stacks Project, Tag 0EYH](https://stacks.math.columbia.edu/tag/0EYH)
* [Stacks Project, Tag 0EYG](https://stacks.math.columbia.edu/tag/0EYG)
* [Stacks Project, Tag 03GV](https://stacks.math.columbia.edu/tag/03GV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.TameCovers

/-- **Stacks Project, Tag 0EYH.** Let `X` be a locally Noetherian scheme, let `D ⊆ X` be an
effective Cartier divisor such that `D` is a regular scheme, and let `f : Y ⟶ X ∖ D` be finite
étale and tamely ramified over `X` in codimension one (the situation of [Stacks, Tag 0EYG]).
Then the normalization `π : Y' ⟶ X` of `X` in `Y` is a finite locally free morphism such that
1. the restriction of `Y'` to `X ∖ D` is isomorphic to `Y` (over `X ∖ D`),
2. `D' = π⁻¹(D)_red` is an effective Cartier divisor on `Y'`, and
3. `D'` is a regular scheme.
Moreover, étale locally on `X` the morphism `Y' ⟶ X` is a finite disjoint union of morphisms
`Spec(A[x]/(x^e - φ)) ⟶ Spec(A)` where `A` is a Noetherian ring, `φ ∈ A` is a nonzerodivisor
with `A/φA` regular, and `e ≥ 1` is invertible in `A`: every `x ∈ X` is in the image of an
étale `g : Spec A ⟶ X` over which `Y' ×_X Spec A ≅ ∐ᵢ Spec(A[x]/(x^{eᵢ} - φ))` over `Spec A`.

Here `π` is `(f ≫ ι).fromNormalization` for the inclusion `ι` of `X ∖ D = D.support.compl`,
and `D'` is the closed subscheme of the radical of the ideal sheaf `D.comap π`. -/
@[stacks 0EYH "the normalization of `X` in a tame cover `Y` of `X ∖ D` is finite locally free, \
restricts to `Y`, has `π⁻¹(D)_red` a regular effective Cartier divisor, and is étale locally a \
finite disjoint union of standard `Spec(A[x]/(x^e - f)) ⟶ Spec(A)`"]
public theorem normalization_of_isTamelyRamifiedInCodimensionOne_of_isRegular {X : Scheme.{u}}
    [IsLocallyNoetherian X] (D : X.IdealSheafData)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) (hDreg : IsRegular D.subscheme)
    {Y : Scheme.{u}} (f : Y ⟶ (D.support.compl : X.Opens)) [IsFinite f] [Etale f]
    (hf : Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne
      (Scheme.Opens.ι (D.support.compl : X.Opens)) f) :
    Stacks.Morphisms.IsFiniteLocallyFree
        (f ≫ Scheme.Opens.ι (D.support.compl : X.Opens)).fromNormalization ∧
      (∃ e : pullback (f ≫ Scheme.Opens.ι (D.support.compl : X.Opens)).fromNormalization
          (Scheme.Opens.ι (D.support.compl : X.Opens)) ≅ Y,
        e.hom ≫ f = pullback.snd _ _) ∧
      Stacks.Divisors.IsEffectiveCartierDivisor
        (D.comap (f ≫ Scheme.Opens.ι (D.support.compl : X.Opens)).fromNormalization).radical ∧
      IsRegular (D.comap (f ≫ Scheme.Opens.ι
          (D.support.compl : X.Opens)).fromNormalization).radical.subscheme ∧
      ∀ x : X, ∃ (A : CommRingCat.{u}) (g : Spec A ⟶ X) (_ : Etale g) (a : Spec A)
        (_ : g a = x) (φ : A) (_ : IsNoetherianRing A) (_ : φ ∈ nonZeroDivisors A)
        (_ : IsRegularRing (A ⧸ Ideal.span {φ})) (n : ℕ) (e : Fin n → ℕ)
        (_ : ∀ i, 0 < e i ∧ IsUnit (e i : A)),
        ∃ ι : pullback (f ≫ Scheme.Opens.ι (D.support.compl : X.Opens)).fromNormalization g ≅
            ∐ fun i ↦ Spec (.of (standardTamelyRamifiedAlgebra A φ (e i))),
          ι.hom ≫ Sigma.desc (fun i ↦ standardTamelyRamifiedMorphism A φ (e i)) =
            pullback.snd _ g := by
  have hDreg' := (isRegular_tfae D.subscheme).out 1 2
  obtain ⟨h1, h2, h3, h4, h5⟩ := normalization_of_isTamelyRamifiedInCodimensionOne
    (fun S h ↦ Stacks.FundamentalGroup.pulledBackCover_isTamelyRamifiedInCodimensionOne S h)
    D hD (hDreg'.mp hDreg).2 f hf
  have : IsFinite (f ≫ Scheme.Opens.ι (D.support.compl : X.Opens)).fromNormalization :=
    ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mp
      h1).1
  have : IsLocallyNoetherian (f ≫ Scheme.Opens.ι (D.support.compl : X.Opens)).normalization :=
    LocallyOfFiniteType.isLocallyNoetherian
      (f ≫ Scheme.Opens.ι (D.support.compl : X.Opens)).fromNormalization
  have : IsLocallyNoetherian (D.comap (f ≫ Scheme.Opens.ι
      (D.support.compl : X.Opens)).fromNormalization).radical.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (Scheme.IdealSheafData.subschemeι _)
  have hD'reg := (isRegular_tfae (D.comap (f ≫ Scheme.Opens.ι
    (D.support.compl : X.Opens)).fromNormalization).radical.subscheme).out 1 2
  exact ⟨h1, h2, h3, hD'reg.mpr ⟨inferInstance, h4⟩, h5⟩

end AlgebraicGeometry.TameCovers

end
