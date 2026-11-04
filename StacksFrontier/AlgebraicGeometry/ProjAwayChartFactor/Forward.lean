module

public import StacksFrontier.AlgebraicGeometry.ProjAwayChartFactor.Basic

/-!
# The chart bijection of `Proj`, computed forwards

`Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.chartHomEquiv` is the bijection, for `r` a
homogeneous element of positive degree of a graded ring `𝒜`, between the morphisms
`Y ⟶ Proj 𝒜` landing in `D₊(r)` and the ring homomorphisms out of
`HomogeneousLocalization.Away 𝒜 r`. This file computes it: the homomorphism attached to `g` is
the pullback along `g` of the functions on the standard open, that is,
`AlgebraicGeometry.Proj.awayToSection`, the canonical map `(𝒜_r)₀ ⟶ Γ(Proj 𝒜, D₊(r))`, followed
by `g.appLE (D₊ r) ⊤`. So the class of `a / r^n` goes to the pullback of the function it names.

## Main results

* `Stacks.AlgebraicGeometry.ProjAwayChartFactor.specHomEquiv_apply`: the `Γ`–`Spec` bijection of
  `Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.specHomEquiv`, read forwards, is the action on
  global sections.
* `Stacks.AlgebraicGeometry.ProjAwayChartFactor.chartHomEquiv_apply`: the chart bijection,
  computed: `chartHomEquiv 𝒜 hr hd Y ⟨g, hg⟩` is `Proj.awayToSection 𝒜 r ≫ g.appLE (D₊ r) ⊤`.

## References

* [Stacks Project, Tag 01NA](https://stacks.math.columbia.edu/tag/01NA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace Stacks.AlgebraicGeometry.ProjAwayChartFactor

universe u w

/-- The ring homomorphism attached by `ProjF1DegreeOneChart.specHomEquiv` to a morphism
`h : Z ⟶ Spec R` is its action on global sections, read through the identification of
`Γ(Spec R, ⊤)` with `R`. -/
public theorem specHomEquiv_apply (R : CommRingCat.{u}) (Z : Scheme.{u}) (h : Z ⟶ Spec R) :
    ProjF1DegreeOneChart.specHomEquiv R Z h = (Scheme.ΓSpecIso R).inv ≫ h.appTop := by
  have key : (ΓSpec.adjunction.homEquiv Z (op R))
      (ProjF1DegreeOneChart.specHomEquiv R Z h).op = h :=
    (ΓSpec.adjunction.homEquiv Z (op R)).apply_symm_apply h
  simpa only [key] using (ΓSpecIso_inv_ΓSpec_adjunction_homEquiv
    (X := Z) (B := R) (ProjF1DegreeOneChart.specHomEquiv R Z h)).symm

variable {Y : Scheme.{u}} {σ : Type w} {R : Type u} [CommRing R] [SetLike σ R]
  [AddSubgroupClass σ R] (𝒜 : ℕ → σ) [GradedRing 𝒜] {r : R} {d : ℕ}

/-- The inverse of `U.topIso` is the action `U.ι.appLE U ⊤` of the inclusion of `U` on
sections. -/
public theorem topIso_inv_eq_ι_appLE (U : (Proj 𝒜).Opens) :
    U.topIso.inv = U.ι.appLE U ⊤ U.ι_preimage_self.ge := by
  simp only [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appLE]
  rfl

/-- The ring homomorphism out of `HomogeneousLocalization.Away 𝒜 r` attached by
`ProjF1DegreeOneChart.chartHomEquiv` to a morphism `g` landing in `D₊(r)` is the pullback along
`g` of the functions on `D₊(r)`: `AlgebraicGeometry.Proj.awayToSection`, which names the function
`a / r^n`, followed by `g.appLE`. -/
public theorem chartHomEquiv_apply (hr : r ∈ 𝒜 d) (hd : 0 < d)
    {g : Y ⟶ Proj 𝒜} (hg : g ⁻¹ᵁ Proj.basicOpen 𝒜 r = ⊤) :
    ProjF1DegreeOneChart.chartHomEquiv 𝒜 hr hd Y ⟨g, hg⟩ =
      Proj.awayToSection 𝒜 r ≫ g.appLE (Proj.basicOpen 𝒜 r) ⊤ hg.ge := by
  have hfac : (ProjF1DegreeOneChart.opensHomEquiv (Proj.basicOpen 𝒜 r)) ⟨g, hg⟩ ≫
      (Proj.basicOpen 𝒜 r).ι = g :=
    IsOpenImmersion.lift_fac _ _ _
  have step : ProjF1DegreeOneChart.chartHomEquiv 𝒜 hr hd Y ⟨g, hg⟩ =
      ProjF1DegreeOneChart.specHomEquiv _ Y ((Iso.refl Y).inv ≫
        (ProjF1DegreeOneChart.opensHomEquiv (Proj.basicOpen 𝒜 r)) ⟨g, hg⟩ ≫
          (Proj.basicOpenIsoSpec 𝒜 r hr hd).hom) := rfl
  have hbt : Scheme.Hom.appTop (Proj.basicOpenToSpec 𝒜 r) =
      (Scheme.ΓSpecIso _).hom ≫ Proj.awayToSection 𝒜 r ≫ (Proj.basicOpen 𝒜 r).topIso.inv :=
    Proj.basicOpenToSpec_app_top 𝒜 r
  have happ : Scheme.Hom.appTop
        ((ProjF1DegreeOneChart.opensHomEquiv (Proj.basicOpen 𝒜 r)) ⟨g, hg⟩) =
      Scheme.Hom.appLE ((ProjF1DegreeOneChart.opensHomEquiv (Proj.basicOpen 𝒜 r)) ⟨g, hg⟩) ⊤ ⊤
        (Scheme.Hom.preimage_top
          ((ProjF1DegreeOneChart.opensHomEquiv (Proj.basicOpen 𝒜 r)) ⟨g, hg⟩)).ge :=
    Scheme.Hom.app_eq_appLE _
  rw [step, Iso.refl_inv, Category.id_comp, specHomEquiv_apply, Scheme.Hom.comp_appTop,
    Proj.basicOpenIsoSpec_hom, hbt]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [topIso_inv_eq_ι_appLE, happ, Scheme.Hom.appLE_comp_appLE]
  simp only [hfac]

end Stacks.AlgebraicGeometry.ProjAwayChartFactor

end
