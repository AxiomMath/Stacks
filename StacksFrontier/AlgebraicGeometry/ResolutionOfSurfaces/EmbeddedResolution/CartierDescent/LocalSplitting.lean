module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierDescent.Globalization
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierDescent.ResidualSupportAG

/-!
# The local splitting of Tag 0AGT, free of a choice of regular parameters

`CartierDescent.ResidualSupportAG` proves the local splitting of [Stacks, Tag 0AGT] for a
two-dimensional regular local ring together with a chosen pair `x, y` spanning its maximal
ideal — the pair that cuts out the two standard charts of the blowup. The statement that the
globalisation of `CartierDescent.Globalization` consumes,
`Stacks.ResolutionOfSurfaces.CartierDescent.LocalColengthSplitting`, makes no such choice. This
file removes the choice, by producing a regular system of parameters from
`CartierDescent.ResidualSupport`.

The colength drop itself is still carried as a hypothesis here, in the form in which
`CartierDescent.ResidualSupportAG` consumes it, so that the chart computation which supplies it
can be written independently.

## Main results

* `Stacks.ResolutionOfSurfaces.CartierDescent.localColengthSplitting_of_colength` — the local
  splitting, given the colength drop.

## Implementation notes

The pair of regular parameters comes from `isRegular_pair_of_span` applied to the two generators
of the maximal ideal supplied by `Submodule.FG.exists_span_finset_card_eq_spanFinrank` together
with `IsRegularLocalRing.spanFinrank_maximalIdeal`; `CartierDescent.ResidualSupport` packages
that as the regularity of the pair, and the existence of the pair itself is
`CartierDescent.RegularParameters`' `exists_pair_span_eq_maximalIdeal_isRegular`.

## References

* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
* [Stacks Project, Tag 00NQ](https://stacks.math.columbia.edu/tag/00NQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry

universe u

namespace Stacks.ResolutionOfSurfaces.CartierDescent

/-- **The local splitting of [Stacks, Tag 0AGT], given the colength drop.** For every
two-dimensional regular local ring and every ideal `L` with `𝔪 ^ n ≤ L ≤ 𝔪`, one blowup at the
closed point splits the inverse image of `L` as a positive power of the exceptional divisor times
an ideal sheaf supported at finitely many closed points with regular two-dimensional local rings
and of strictly smaller total colength.

The colength drop on the two standard charts is the hypothesis `hcol`; everything else is
discharged. -/
public theorem localColengthSplitting_of_colength
    (hcol : ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A], ringKrullDim A = 2 →
      ∀ (x y : A), Ideal.span ({x, y} : Set A) = IsLocalRing.maximalIdeal A →
      ∀ (L : Ideal A) (n : ℕ), IsLocalRing.maximalIdeal A ^ n ≤ L →
      L ≤ IsLocalRing.maximalIdeal A →
      ∀ (d : ℕ), 0 < d →
      ∀ J'₀ : (Stacks.Blowup.blowUp (centre A)).IdealSheafData,
      Stacks.Blowup.exceptionalIdeal (centre A) ^ d * J'₀ =
          (idealSheafOf A L).comap (Stacks.Blowup.blowUpToBase (centre A)) →
      ¬ ((idealSheafOf A L).comap (Stacks.Blowup.blowUpToBase (centre A)) ≤
          Stacks.Blowup.exceptionalIdeal (centre A) ^ (d + 1)) →
      ∀ T₀ : Finset (Stacks.Blowup.blowUp (centre A)),
      ((J'₀.support : Set (Stacks.Blowup.blowUp (centre A))) ⊆ (T₀ : Set _)) →
      ∑ w ∈ T₀, Module.length ((Stacks.Blowup.blowUp (centre A)).presheaf.stalk w)
          ((Stacks.Blowup.blowUp (centre A)).presheaf.stalk w ⧸
            AlgebraicGeometry.IdealSheafData.stalk J'₀ w) <
        Module.length A (A ⧸ L)) :
    LocalColengthSplitting.{u} := by
  intro A _ _ hdim L n hmn hLm
  obtain ⟨x, y, hspan, -⟩ := exists_pair_span_eq_maximalIdeal_isRegular A hdim
  exact exists_residual_support A hdim hspan L n hmn hLm
    (hcol A hdim x y hspan L n hmn hLm)

end Stacks.ResolutionOfSurfaces.CartierDescent

end
