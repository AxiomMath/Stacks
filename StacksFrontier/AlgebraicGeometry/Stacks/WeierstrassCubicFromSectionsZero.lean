module

public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassCubicFromSections

/-!
# The zero section of a plane Weierstrass cubic given by three sections

Let `X ⟶ Spec R` carry three sections `s₀, s₁, s₂` of an invertible module whose ratios satisfy
the Weierstrass cubic of `C` and whose nonvanishing opens cover `X`. A section
`σ : Spec R ⟶ X` of `X ⟶ Spec R` landing in the chart `s₁ ≠ 0`, where both ratios `s₀/s₁` and
`s₂/s₁` vanish, is sent by `cubicHomOfSections` to the point `(0 : 1 : 0)` at infinity.

## Main results

* `comp_cubicHomOfSections_eq_zeroOf`: such a section composed with the morphism given by the
  sections is the zero section `zeroOf C`.

## References

* [Stacks: Tag 072T](https://stacks.math.columbia.edu/tag/072T)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

open Stacks.ProjectiveFromSections

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] {C : WeierstrassCurve R} {X : Scheme.{u}}
  {π : X ⟶ Spec (.of R)} {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]
  {s : Fin 3 → Γ(L, ⊤)}

/-- **A section through the point where `s₀/s₁` and `s₂/s₁` vanish goes to the zero section.**
Let `σ : Spec R ⟶ X` be a section of `π` that factors as `σ₁` through the chart `X_{s₁}` and
satisfies `σ₁^*(s₀/s₁) = 0` and `σ₁^*(s₂/s₁) = 0`. Then `σ ≫ cubicHomOfSections hrel hcov` is
the zero section `zeroOf C`, the point `(0 : 1 : 0)`. -/
theorem comp_cubicHomOfSections_eq_zeroOf (hrel : SatisfiesCubic C π s)
    (hcov : IsOpenCover (nvCover s)) (σ : Spec (.of R) ⟶ X) (hσ : σ ≫ π = 𝟙 _)
    (σ₁ : Spec (.of R) ⟶ (nvCover s 1).toScheme) (hσ₁ : σ₁ ≫ (nvCover s 1).ι = σ)
    (h₀ : σ₁.appTop (chartRatio s 1 0) = 0) (h₂ : σ₁.appTop (chartRatio s 1 2) = 0) :
    σ ≫ cubicHomOfSections hrel hcov = zeroOf C := by
  have hring : σ₁.appTop.hom.comp (chartRingHom hrel 1) = evalZeroGlobalOf C := by
    refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun a => ?_) (fun k => ?_))
    · have hbase : σ₁.appTop.hom.comp (openBase π (nvCover s 1)) =
          (Scheme.ΓSpecIso (.of R)).inv.hom := by
        rw [openBase, ← CommRingCat.hom_comp, Category.assoc, ← Scheme.Hom.comp_appTop,
          ← Category.assoc, hσ₁, hσ, Scheme.Hom.id_appTop, Category.comp_id]
      simp only [RingHom.comp_apply, chartRingHom_mk, chartPolyHom, MvPolynomial.eval₂Hom_C]
      rw [← RingHom.comp_apply, hbase]
      simp [evalZeroGlobalOf, evalZeroOf]
    · simp only [RingHom.comp_apply, chartRingHom_mk, chartPolyHom, MvPolynomial.eval₂Hom_X']
      fin_cases k <;> simp [h₀, h₂, evalZeroGlobalOf, evalZeroOf]
  have hirr : (HomogeneousIdeal.irrelevant (gradingOf C)).toIdeal.map
      (σ₁.appTop.hom.comp (chartRingHom hrel 1)) = ⊤ := by
    rw [hring]; exact map_irrelevant_eq_top_of C
  rw [← hσ₁, Category.assoc, ι_cubicHomOfSections, cubicChartHom]
  refine (comp_fromOfGlobalSections (gradingOf C) σ₁ _ _ hirr).trans ?_
  show Proj.fromOfGlobalSections _ _ hirr = Proj.fromOfGlobalSections _ _ _
  congr 1

end AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

end
