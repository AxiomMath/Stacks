module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.CohomologySpectralSequenceTagTotal

/-!
# The sections double complex of a complex bounded below in any degree

`StacksFrontier/CategoryTheory/Sites/Simplicial/CohomologySpectralSequence.lean` and
`StacksFrontier/CategoryTheory/Sites/Simplicial/CohomologySpectralSequenceTagTotal.lean` state the
convergence of the spectral sequence of the double complex

```
A^{q,p} = Γ(C_p, Z^q_p)
```

and the comparison `Γ(C_total, Z^•) ≅ Tot(A^{•,•})` of Stacks 0133 for a complex `Z^•` of
abelian sheaves vanishing in the *negative* degrees, which is what the chosen injective
resolution of a single sheaf satisfies. An object of `D^+(C_total)` is represented by a complex
of injectives bounded below in some degree `n₀` that need not be `0`, so this file restates the
two with `0` replaced by an arbitrary `n₀`.

Only one of the hypotheses of Stacks 0133 uses the bound at all -- the finiteness of the
antidiagonals of `A^{•,•}` -- and it only needs *some* bound: the simplicial coordinate is
always non-negative, the complex of Stacks 0D77 being extended by zero, so an antidiagonal of
`A^{•,•}` is contained in `[n₀, n] × [0, n - n₀]`. The exactness of the columns away from
simplicial degree `0` and the kernel clause of the augmentation use only the injectivity of the
terms, and are reused unchanged.

## Main results

* `CategoryTheory.SimplicialSiteSituation.diagonalFinite_sectionsDoubleComplex_of_isZero`
  and `CategoryTheory.SimplicialSiteSituation.diagonalFinite_sections_of_isZero`: the
  antidiagonals of `A^{•,•}` are finite for a complex bounded below in any degree.
* `CategoryTheory.SimplicialSiteSituation.sectionsSpectralSequence_abutsTo_total_of_isZero`:
  **the spectral sequence abuts to `H^n(Tot(A^{•,•}))`** for such a complex.
* `CategoryTheory.SimplicialSiteSituation.sectionsComparisonHomologyIso_of_isZero`:
  **`H^n(Γ(C_total, Z^•)) ≅ H^n(Tot(A^{•,•}))`** for such a complex, with injective terms.

## References

* [Stacks Project, Tag 09WJ](https://stacks.math.columbia.edu/tag/09WJ)
* [Stacks Project, Tag 0D77](https://stacks.math.columbia.edu/tag/0D77)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
* [Stacks Project, Tag 012W](https://stacks.math.columbia.edu/tag/012W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u})
  (Z : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ) (n₀ : ℤ)

/-- **The double complex vanishes outside the quadrant `q ≥ n₀`, `p ≥ 0`**, for a complex of
abelian sheaves vanishing in the degrees below `n₀`. -/
theorem isZero_sectionsDoubleComplex_X_X_of_isZero
    (hZ : ∀ q : ℤ, q < n₀ → IsZero (Z.X q)) (q p : ℤ) (h : q < n₀ ∨ p < 0) :
    IsZero (((S.sectionsDoubleComplex Z).X q).X p) := by
  rcases h with hq | hp
  · exact (HomologicalComplex.eval Ab.{u} (ComplexShape.up ℤ) p).map_isZero
      (S.cechSectionsComplexZ.map_isZero (hZ q hq))
  · exact S.isZero_sectionsDoubleComplex_X_X_of_neg_snd Z q p hp

/-- A nonzero term of the double complex has `q ≥ n₀` and `p ≥ 0`. -/
private theorem le_and_nonneg_of_not_isZero_sectionsDoubleComplex_X_X
    (hZ : ∀ q : ℤ, q < n₀ → IsZero (Z.X q)) (q p : ℤ)
    (hne : ¬ IsZero (((S.sectionsDoubleComplex Z).X q).X p)) : n₀ ≤ q ∧ 0 ≤ p := by
  by_contra h
  exact hne (S.isZero_sectionsDoubleComplex_X_X_of_isZero Z n₀ hZ q p (by omega))

/-- **The diagonals of the double complex are finite**, for a complex of abelian sheaves
vanishing in the degrees below `n₀`: a nonzero term has `q ≥ n₀` and `p ≥ 0`. -/
theorem diagonalFinite_sectionsDoubleComplex_of_isZero
    (hZ : ∀ q : ℤ, q < n₀ → IsZero (Z.X q)) (n : ℤ) :
    {qp : ℤ × ℤ | qp.1 + qp.2 = n ∧
      ¬ IsZero (((S.sectionsDoubleComplex Z).X qp.1).X qp.2)}.Finite := by
  refine Set.Finite.subset (Set.finite_Icc ((n₀ : ℤ), (0 : ℤ)) (n, n - n₀)) ?_
  rintro ⟨q, p⟩ ⟨hsum, hne⟩
  obtain ⟨hq, hp⟩ :=
    S.le_and_nonneg_of_not_isZero_sectionsDoubleComplex_X_X Z n₀ hZ q p hne
  exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

/-- **The spectral sequence abuts to the cohomology of the total complex** of the double complex
`A^{q,p} = Γ(C_p, Z^q_p)`, for a complex of abelian sheaves vanishing in the degrees below `n₀`:
the filtration by the simplicial coordinate is degreewise finite, so Stacks 012W applies. -/
theorem sectionsSpectralSequence_abutsTo_total_of_isZero
    (hZ : ∀ q : ℤ, q < n₀ → IsZero (Z.X q)) :
    SpectralSequence.AbutsTo (S.sectionsSpectralSequence Z)
      (fun n => ((S.sectionsDoubleComplex Z).total (ComplexShape.up ℤ)).homology n) :=
  CochainComplex.Filtered.abutsTo_of_isDegreewiseFinite
    (S.sectionsDoubleComplex Z).totalFiltration₂
    (fun p n => (S.sectionsDoubleComplex Z).stepSubobject (fun (_ : ℤ) j => j) p n)
    (fun _ _ => (Subobject.mk_arrow _).symm) _ (fun _ _ _ => rfl) _ (fun _ _ _ => rfl) _
    (HomologicalComplex₂.pageIso₂ _)
    (HomologicalComplex₂.isDegreewiseFinite_totalFiltration₂ _
      (S.diagonalFinite_sectionsDoubleComplex_of_isZero Z n₀ hZ))

/-- **The antidiagonals of the double complex are finite**, in the shape Stacks 0133 asks for,
for a complex of abelian sheaves vanishing in the degrees below `n₀`. -/
theorem diagonalFinite_sections_of_isZero (hZ : ∀ q : ℤ, q < n₀ → IsZero (Z.X q)) :
    DiagonalFinite (S.sectionsDoubleComplex Z) := by
  intro n
  refine Set.Finite.subset (Set.finite_Icc n₀ n) fun q hq => ?_
  simp only [Set.mem_ofPred_eq] at hq
  obtain ⟨h1, h2⟩ :=
    S.le_and_nonneg_of_not_isZero_sectionsDoubleComplex_X_X Z n₀ hZ q (n - q) hq
  exact ⟨h1, by omega⟩

/-- **The hypotheses of Stacks 0133 for the double complex `A^{q,p} = Γ(C_p, Z^q_p)`** of a
complex `Z^•` of injective abelian sheaves on the total site vanishing in the degrees below
`n₀`. Only the finiteness of the antidiagonals sees the bound. -/
theorem sectionsHypotheses_of_isZero (hZ : ∀ q : ℤ, q < n₀ → IsZero (Z.X q))
    (hinj : ∀ q : ℤ, Injective (Z.X q)) :
    Hypotheses (S.totalSectionsComplex Z) (S.sectionsDoubleComplex Z)
      (S.sectionsAlpha Z) where
  diagonalFinite := S.diagonalFinite_sections_of_isZero Z n₀ hZ
  zero_of_neg q p hp := S.isZero_sectionsDoubleComplex_X_X_of_neg_snd Z q p hp
  exactAt_of_ne_zero := S.exactAt_sectionsDoubleComplex_X Z hinj
  inducesIsoKernel := S.inducesIsoKernel_sectionsAlpha Z

/-- **`H^n(Γ(C_total, Z^•)) ≅ H^n(Tot(A^{•,•}))`.** This is Stacks 0133 for the double complex
`A^{q,p} = Γ(C_p, Z^q_p)` of a complex of injective abelian sheaves vanishing in the degrees
below `n₀`. -/
def sectionsComparisonHomologyIso_of_isZero (hZ : ∀ q : ℤ, q < n₀ → IsZero (Z.X q))
    (hinj : ∀ q : ℤ, Injective (Z.X q)) (n : ℤ) :
    (S.totalSectionsComplex Z).homology n ≅
      ((S.sectionsDoubleComplex Z).total (ComplexShape.up ℤ)).homology n :=
  comparisonHomologyIso _ _ _ (S.sectionsHypotheses_of_isZero Z n₀ hZ hinj) n

end CategoryTheory.SimplicialSiteSituation

end
