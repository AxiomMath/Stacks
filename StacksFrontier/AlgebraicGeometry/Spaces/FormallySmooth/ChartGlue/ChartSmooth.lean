module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartGlue.AlgChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFormallySmooth
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff

/-!
# A spectrum formally smooth over an affine thickening has a formally smooth ring

Let `T'` be an affine object of the big fppf site over `S` with ring `A'`, and let `R` be an
`A'`-algebra whose spectrum belongs to the site. If `Spec R` has the infinitesimal lifting
property relative to `T'` against square-zero closed immersions of affine objects of the site,
then `R` is a formally smooth `A'`-algebra. The site only contains spectra of rings of
cardinality below the cutoff, and that is enough, by
`formallySmooth_of_exists_section_of_mk_lt`.

## Main results

* `AlgebraicGeometry.Space.ChartGlue.formallySmooth_of_relLift`
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space.ChartGlue

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (T' : BigFppfOver B S hS)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]

/-- A ring of cardinality below the cutoff has its spectrum in the site. -/
lemma contains_spec_of_mk_lt {Q : Type u} [CommRing Q] (hQ : #Q < B.cutoff) :
    B.Contains (Spec (CommRingCat.of Q)) := by
  change (Spec (CommRingCat.of Q)).size < B.cutoff
  rw [Scheme.size_Spec]
  exact max_lt B.aleph0_lt_cutoff hQ

/-- A ring whose spectrum is in the site has cardinality below the cutoff. -/
lemma mk_lt_of_contains_spec {Q : Type u} [CommRing Q] (hQ : B.Contains (Spec (CommRingCat.of Q))) :
    #Q < B.cutoff := by
  have h : (Spec (CommRingCat.of Q)).size < B.cutoff := hQ
  rw [Scheme.size_Spec] at h
  exact (le_max_right _ _).trans_lt h

/-- The ring of `T'` has cardinality below the cutoff. -/
lemma mk_ringOf_lt : #(ringOf B S hS T') < B.cutoff :=
  ((BigFppfOver.toScheme B S hS).obj T').mk_sections_le_size
    ⟨⊤, isAffineOpen_top _⟩ |>.trans_lt T'.left.property

/-- **Relative formal smoothness of a spectrum over `T'` makes its ring formally smooth.** -/
theorem formallySmooth_of_relLift (R : Type u) [CommRing R] [Algebra (ringOf B S hS T') R]
    (hR : B.Contains (Spec (CommRingCat.of R)))
    (H : ∀ (C₀ D₀ : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj C₀) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj D₀) → ∀ (j : D₀ ⟶ C₀),
        IsSquareZeroClosedImmersion B S hS j → ∀ (c : C₀ ⟶ T') (e₀ : D₀ ⟶ specObj B S hS T' R hR),
          e₀ ≫ specToT B S hS T' R hR = j ≫ c →
            ∃ e : C₀ ⟶ specObj B S hS T' R hR, j ≫ e = e₀ ∧ e ≫ specToT B S hS T' R hR = c) :
    Algebra.FormallySmooth (ringOf B S hS T') R := by
  refine Stacks.Smooth.formallySmooth_of_exists_section_of_mk_lt B.aleph0_lt_cutoff
    (mk_ringOf_lt B S hS T') (mk_lt_of_contains_spec B hR) ?_
  intro Q _ _ π hπ hsq hQ
  have hQc := contains_spec_of_mk_lt B hQ
  have hj := isSquareZeroClosedImmersion_specMap B S hS T' hQc hR π hπ hsq
  obtain ⟨e, he₁, he₂⟩ := H (specObj B S hS T' Q hQc) (specObj B S hS T' R hR)
    (inferInstanceAs (IsAffine (Spec (CommRingCat.of Q))))
    (inferInstanceAs (IsAffine (Spec (CommRingCat.of R)))) _ hj (specToT B S hS T' Q hQc) (𝟙 _)
    (by rw [Category.id_comp, specMap_specToT])
  obtain ⟨s, hs, -⟩ := existsUnique_specMap_eq B S hS T' hR hQc e he₂
  refine ⟨s, ?_⟩
  have h1 : specMap B S hS T' hR hR (π.comp s) = specMap B S hS T' hR hR (AlgHom.id _ R) := by
    rw [specMap_comp B S hS T' hR hQc hR, hs, he₁, specMap_id]
  exact (existsUnique_specMap_eq B S hS T' hR hR _ (by rw [specMap_specToT])).unique h1 rfl

end AlgebraicGeometry.Space.ChartGlue

end
