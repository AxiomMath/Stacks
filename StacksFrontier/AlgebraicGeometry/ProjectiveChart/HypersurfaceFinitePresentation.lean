module

public import StacksFrontier.AlgebraicGeometry.ProjectiveChart.HypersurfaceChart
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# A hypersurface of `ℙⁿ_R` is of finite presentation over `R`

The structure morphism of a closed subscheme `Z ⊆ ℙⁿ_R` cut out by one homogeneous equation is
locally of finite presentation: the standard charts cover `Z` by affine opens whose rings are
`R[Y₁, …, Yₙ] ⧸ (F(Tⱼ = 1))`, a quotient of a polynomial ring by a principal — hence finitely
generated — ideal.

This is the hypothesis under which smoothness of a morphism at a point is the formal smoothness
of the localization of its chart ring, and under which a point with finite residue field
extension is closed; both are needed to read [Stacks, Tag 0CCU] on the projective plane.

## Main results

* `Stacks.ProjectiveChart.finitePresentation_chartPresentation_comp_C`: each chart ring is a
  finitely presented `R`-algebra.
* `Stacks.ProjectiveChart.iSup_subschemeChart_eq_top`: the charts cover `Z`.
* `Stacks.ProjectiveChart.locallyOfFinitePresentation_toSpec`: **the structure morphism
  `Z ⟶ Spec R` is locally of finite presentation.**

## Implementation notes

The affine-local criterion used is `AlgebraicGeometry.HasRingHomProperty.of_iSup_eq_top`, whose
base must be affine — it is `Spec R` — and which asks for `RingHom.FinitePresentation` of the
`AlgebraicGeometry.Scheme.Hom.appLE` into each chart.  That ring map is the one
`Stacks.ProjectiveChart.chartPresentation_C` identifies, after the identification of `R` with
`Γ(Spec R, ⊤)`, with the presentation of the chart; so finite presentation of the chart as an
`R`-algebra is exactly what is needed, and `RingHom.finitePresentation_respectsIso` moves it
across the identification of the base.

## References

* [Stacks Project, Tag 0CCU](https://stacks.math.columbia.edu/tag/0CCU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Stacks.ProjectiveChart

universe u

variable {R : Type u} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ} {Z : Scheme.{u}}
  (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) (j : Fin (n + 1))

/-- **The standard charts cover a subscheme of projective space.** -/
theorem iSup_subschemeChart_eq_top : ⨆ j : Fin (n + 1), subschemeChart i j = ⊤ := by
  have h := TopologicalSpace.Opens.map_iSup i.base
    (fun l : Fin (n + 1) => Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (MvPolynomial.X l))
  rw [iSup_basicOpen_X_eq_top R n] at h
  exact h.symm.trans rfl

variable [IsClosedImmersion i] [IsNoetherianRing R] {d : ℕ} (F : MvPolynomial (Fin (n + 1)) R)
  (hF : F ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R (d • 1))
  (hideal : AlgebraicGeometry.ProjectiveSpectrum.Proj.idealOfClosedSubscheme
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) i = Ideal.span {F})

include hF hideal in
/-- The isomorphism `chartQuotientEquiv` sends the class of a polynomial `y` to
`chartPresentation i j y`. -/
theorem chartQuotientEquiv_mk (y : MvPolynomial (Fin n) R) :
    chartQuotientEquiv i j F hF hideal (Ideal.Quotient.mk _ y) = chartPresentation i j y :=
  rfl

include hF hideal in
/-- **Each chart of a hypersurface is a finitely presented `R`-algebra**, for the `R`-algebra
structure coming from the structure morphism. -/
theorem finitePresentation_chartPresentation_comp_C :
    RingHom.FinitePresentation ((chartPresentation i j).comp MvPolynomial.C) := by
  let : Algebra R Γ(Z, subschemeChart i j) :=
    ((chartPresentation i j).comp MvPolynomial.C).toAlgebra
  let e : (MvPolynomial (Fin n) R ⧸ Ideal.span {dehomCoeff R j F}) ≃ₐ[R]
      Γ(Z, subschemeChart i j) :=
    { chartQuotientEquiv i j F hF hideal with
      commutes' := fun r => chartQuotientEquiv_mk i j F hF hideal (MvPolynomial.C r) }
  exact (Algebra.FinitePresentation.quotient
    (Submodule.fg_span_singleton (dehomCoeff R j F))).equiv e

include hF hideal in
/-- **The structure morphism of a hypersurface in projective space is locally of finite
presentation.** -/
theorem locallyOfFinitePresentation_toSpec :
    LocallyOfFinitePresentation
      (i ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff R n) := by
  refine HasRingHomProperty.of_iSup_eq_top
    (P := @LocallyOfFinitePresentation) (Q := RingHom.FinitePresentation)
    (fun l : Fin (n + 1) => ⟨subschemeChart i l, isAffineOpen_subschemeChart i l⟩)
    (iSup_subschemeChart_eq_top i) fun l => ?_
  set ψ := ((i ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff R n).appLE ⊤
    (subschemeChart i l) le_top).hom
  set e : R ≃+* Γ(Spec (CommRingCat.of R), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  have hcomp : ψ.comp e.toRingHom = (chartPresentation i l).comp MvPolynomial.C := by
    ext r
    exact (chartPresentation_C i l r).symm
  have h1 : RingHom.FinitePresentation (ψ.comp e.toRingHom) :=
    hcomp ▸ finitePresentation_chartPresentation_comp_C i l F hF hideal
  have h2 := RingHom.finitePresentation_respectsIso.2 (ψ.comp e.toRingHom) e.symm h1
  rwa [RingHom.comp_assoc, show e.toRingHom.comp e.symm.toRingHom = RingHom.id _ from
    RingHom.ext e.apply_symm_apply, RingHom.comp_id] at h2

end Stacks.ProjectiveChart

end
