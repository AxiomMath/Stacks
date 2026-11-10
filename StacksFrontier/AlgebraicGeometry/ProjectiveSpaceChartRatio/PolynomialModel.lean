module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceChartRatio.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceSections.GradedNaturality

/-!
# The glued morphism to projective space, chartwise, in the polynomial model over the base ring

`Stacks.ProjectiveSpaceChartRatio.toPolynomialModel` is the morphism
`φ_{(ℒ, (s₀, …, sₙ))} : X ⟶ ℙⁿ_k` of [Stacks, Tag 01ND] read in the polynomial model
`Proj k[T₀, …, Tₙ]` rather than in the base-change model `ℙⁿ_k = Spec k ×_{Spec ℤ} ℙⁿ_ℤ`. The
sibling module computes it on the standard chart `D₊(Tᵢ)` *on sections*. This module identifies
its restriction to `X_{sᵢ}` as a *morphism*, with
`AlgebraicGeometry.Proj.fromOfGlobalSections` of the ring homomorphism

`k[T₀, …, Tₙ] → Γ(X_{sᵢ}, 𝒪)`,  `Tⱼ ↦ sⱼ/sᵢ`,  `a ↦ a`

— that is, with the chart morphism of the ratio family taken over `k` instead of over `ℤ`.

That is the step the glued morphism was missing. `Stacks.ProjectiveFromSections` glues the chart
morphisms over the *integral* model `ℙⁿ_ℤ`, where a linear substitution with coefficients in `k`
does not act; the restriction below is a `fromOfGlobalSections` over `k`, where it does
(`AlgebraicGeometry.fromOfGlobalSections_substitution`).

## Main definitions

* `Stacks.ProjectiveSpaceChartRatio.baseRingHom`: the `k`-algebra structure of the global
  sections of a scheme over `Spec k`.

## Main results

* `Stacks.ProjectiveSpaceChartRatio.toSpecΓ_SpecMap_baseRingHom`: a morphism to an affine scheme
  is recovered from its map on global sections.
* `Stacks.ProjectiveSpaceChartRatio.hom_ext_polynomialModel`: **two morphisms into
  `Proj k[T₀, …, Tₙ]` agree as soon as they agree over `Spec k` and over `ℙⁿ_ℤ`**, because the
  polynomial model is the fibre product of the two
  (`Stacks.AlgebraicGeometry.ProjBaseChange.isIso_projCompare`).
* `Stacks.ProjectiveSpaceChartRatio.fromOfGlobalSections_comp_projToSpecCoeff` and
  `…_comp_coordinateProjMap`: the two components of
  `AlgebraicGeometry.Proj.fromOfGlobalSections` of an evaluation homomorphism. The second is
  where `AlgebraicGeometry.Proj.fromOfGlobalSections_comp_map` is used: the projection to the
  integral model is `AlgebraicGeometry.Proj.map` of the coefficient homomorphism, and naturality
  in the graded ring turns the morphism over `k` into the morphism over `ℤ`.
* `Stacks.ProjectiveSpaceChartRatio.ι_toPolynomialModel`: **the chart identification.**

## Implementation notes

`AlgebraicGeometry.projectiveSpaceAtUniverse` is declared `implicit_reducible` locally, for the
reason given in the sibling module: without it `rw` refuses goals mentioning both `ℙⁿ_ℤ` and
`AlgebraicGeometry.Proj` of the integral polynomial ring.

The identification is proved by the universal property of the fibre product rather than by
comparing the two morphisms on the affine chart `D₊(Tᵢ)`. Both routes are available —
`Stacks.ProjectiveSpaceChartRatio.chartPullback_eq` and
`Stacks.ProjGlobalSectionsAppTop.toBasicOpenOfGlobalSections_appTop` compute the two sides on
sections — but the fibre-product route needs no computation at all on the `Away` ring: the
component over `ℙⁿ_ℤ` is naturality in the graded ring together with the identity of ring
homomorphisms `(T ↦ sⱼ/sᵢ over k) ∘ (coefficient change) = (T ↦ sⱼ/sᵢ over ℤ)`, and the
component over `Spec k` is Mathlib's `AlgebraicGeometry.Proj.fromOfGlobalSections_toSpecZero`.

## References

* [Stacks Project, Tag 01ND](https://stacks.math.columbia.edu/tag/01ND)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
* [Stacks Project, Tag 03GL](https://stacks.math.columbia.edu/tag/03GL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjBaseChange Stacks.AlgebraicGeometry.ProjPolyChart

namespace Stacks.ProjectiveSpaceChartRatio

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] AlgebraicGeometry.projectiveSpaceAtUniverse

variable {k : Type u} [CommRing k] {n : ℕ}

/-! ### The base ring structure on global sections -/

/-- The `k`-algebra structure of the global sections of a scheme over `Spec k`. -/
def baseRingHom {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of k)) : k →+* Γ(Y, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ g.appTop).hom

/-- **A morphism to an affine scheme is recovered from its map on global sections.** -/
theorem toSpecΓ_SpecMap_baseRingHom {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of k)) :
    Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (baseRingHom g)) = g := by
  rw [baseRingHom, CommRingCat.ofHom_hom, Spec.map_comp, ← Category.assoc,
    ← Scheme.toSpecΓ_naturality, Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
    Category.comp_id]

/-! ### The two components of the morphism of an evaluation homomorphism -/

variable {Y : Scheme.{u}}

/-- An evaluation homomorphism at a family spanning the unit ideal meets Mathlib's hypothesis on
the irrelevant ideal: the variables are homogeneous of degree one. -/
theorem map_irrelevant_eval₂Hom_eq_top (κ : k →+* Γ(Y, ⊤)) (r : Fin (n + 1) → Γ(Y, ⊤))
    (hr : Ideal.span (Set.range r) = ⊤) :
    (HomogeneousIdeal.irrelevant (polyGrading k n)).toIdeal.map
      (MvPolynomial.eval₂Hom κ r) = ⊤ := by
  rw [eq_top_iff, ← hr, Ideal.span_le]
  rintro - ⟨i, rfl⟩
  rw [SetLike.mem_coe, show r i = MvPolynomial.eval₂Hom κ r (MvPolynomial.X i) from
    (MvPolynomial.eval₂Hom_X' κ r i).symm]
  exact Ideal.mem_map_of_mem _
    (HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.one_pos (X_mem_one k n i))

/-- Evaluating after the inclusion of the constants is the coefficient homomorphism. -/
theorem eval₂Hom_comp_algebraMap (κ : k →+* Γ(Y, ⊤)) (r : Fin (n + 1) → Γ(Y, ⊤)) :
    ((MvPolynomial.eval₂Hom κ r).comp
          (algebraMap ↥(polyGrading k n 0) (MvPolynomial (Fin (n + 1)) k))).comp
        (algebraMap k ↥(polyGrading k n 0)) = κ :=
  RingHom.ext fun a => by
    rw [RingHom.comp_apply, RingHom.comp_apply,
      show (algebraMap ↥(polyGrading k n 0) (MvPolynomial (Fin (n + 1)) k))
          (algebraMap k ↥(polyGrading k n 0) a) = MvPolynomial.C a by
        rw [show (algebraMap ↥(polyGrading k n 0) (MvPolynomial (Fin (n + 1)) k))
            (algebraMap k ↥(polyGrading k n 0) a) =
            ((algebraMap k ↥(polyGrading k n 0) a : ↥(polyGrading k n 0)) :
              MvPolynomial (Fin (n + 1)) k) from rfl,
          SetLike.GradeZero.coe_algebraMap, MvPolynomial.algebraMap_eq],
      MvPolynomial.eval₂Hom_C]

/-- **The morphism of an evaluation homomorphism, over `Spec k`.** -/
theorem fromOfGlobalSections_comp_projToSpecCoeff (κ : k →+* Γ(Y, ⊤))
    (r : Fin (n + 1) → Γ(Y, ⊤)) (hr : Ideal.span (Set.range r) = ⊤) :
    AlgebraicGeometry.Proj.fromOfGlobalSections (polyGrading k n)
          (MvPolynomial.eval₂Hom κ r) (map_irrelevant_eval₂Hom_eq_top κ r hr) ≫
        projToSpecCoeff k n =
      Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom κ) := by
  rw [projToSpecCoeff, ← Category.assoc, AlgebraicGeometry.Proj.fromOfGlobalSections_toSpecZero,
    Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    Stacks.ProjBaseChange.projZeroRingHom'_comp_algebraMap (polyGrading k n),
    eval₂Hom_comp_algebraMap κ r]

/-- Evaluating over `k` after coefficient change from `ℤ` is evaluating over `ℤ`. -/
theorem eval₂Hom_comp_integralGradedHom (κ : k →+* Γ(Y, ⊤)) (r : Fin (n + 1) → Γ(Y, ⊤)) :
    (MvPolynomial.eval₂Hom κ r).comp (integralGradedHom k n).toRingHom =
      Stacks.SectionsToProjectiveSpace.sectionsHom r := by
  refine MvPolynomial.ringHom_ext (fun m => ?_) (fun j => ?_)
  · rw [RingHom.comp_apply, GradedRingHom.coe_toRingHom, integralGradedHom_apply,
      MvPolynomial.map_C, MvPolynomial.eval₂Hom_C,
      Stacks.SectionsToProjectiveSpace.sectionsHom, MvPolynomial.eval₂Hom_C]
    change κ ((m.down : k)) = ((m.down : ℤ) : Γ(Y, ⊤))
    rw [map_intCast]
  · rw [RingHom.comp_apply, GradedRingHom.coe_toRingHom, integralGradedHom_apply,
      MvPolynomial.map_X, MvPolynomial.eval₂Hom_X',
      Stacks.SectionsToProjectiveSpace.sectionsHom_X]

/-- **The morphism of an evaluation homomorphism, over the integral model.** This is where
naturality of `AlgebraicGeometry.Proj.fromOfGlobalSections` in the graded ring is used. -/
theorem fromOfGlobalSections_comp_coordinateProjMap (κ : k →+* Γ(Y, ⊤))
    (r : Fin (n + 1) → Γ(Y, ⊤)) (hr : Ideal.span (Set.range r) = ⊤) :
    AlgebraicGeometry.Proj.fromOfGlobalSections (polyGrading k n)
          (MvPolynomial.eval₂Hom κ r) (map_irrelevant_eval₂Hom_eq_top κ r hr) ≫
        coordinateProjMap k n (integralGradedHom k n)
          (mapDomain_integralGradedHom_eq_top k n) =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse r hr := by
  have h2 : (HomogeneousIdeal.irrelevant (polyGrading (ULift.{u} ℤ) n)).toIdeal.map
      ((MvPolynomial.eval₂Hom κ r).comp (integralGradedHom k n).toRingHom) = ⊤ := by
    rw [eval₂Hom_comp_integralGradedHom κ r]
    exact Stacks.SectionsToProjectiveSpace.map_irrelevant_eq_top r hr
  rw [coordinateProjMap_eq_projMap,
    AlgebraicGeometry.Proj.fromOfGlobalSections_comp_map (integralGradedHom k n)
      (irrelevant_le_map_integralGradedHom k n) (MvPolynomial.eval₂Hom κ r)
      (map_irrelevant_eval₂Hom_eq_top κ r hr) h2]
  exact AlgebraicGeometry.Proj.fromOfGlobalSections_congr
    (eval₂Hom_comp_integralGradedHom κ r) h2 _

/-! ### Two morphisms into the polynomial model -/

/-- **Two morphisms into `Proj k[T₀, …, Tₙ]` agree as soon as they agree over `Spec k` and over
the integral model `ℙⁿ_ℤ`**: the polynomial model is the fibre product of the two. -/
theorem hom_ext_polynomialModel {g g' : Y ⟶ AlgebraicGeometry.Proj (polyGrading k n)}
    (h1 : g ≫ projToSpecCoeff k n = g' ≫ projToSpecCoeff k n)
    (h2 : g ≫ coordinateProjMap k n (integralGradedHom k n)
          (mapDomain_integralGradedHom_eq_top k n) =
        g' ≫ coordinateProjMap k n (integralGradedHom k n)
          (mapDomain_integralGradedHom_eq_top k n)) :
    g = g' := by
  rw [← cancel_mono (projCompare k n)]
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, projCompare_fst, h1]
  · rw [Category.assoc, Category.assoc, projCompare_snd, h2]

/-! ### The chart identification -/

variable {X : Scheme.{u}} {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]
  (s : Fin (n + 1) → Γ(L, ⊤)) (hs : Stacks.ProjectiveFromSections.GeneratesStalks s)
  (f : X ⟶ Spec (CommRingCat.of k))

/-- **The glued morphism of [Stacks, Tag 01ND], restricted to the `i`-th chart and read in the
polynomial model over `k`, is `AlgebraicGeometry.Proj.fromOfGlobalSections` of the evaluation
`Tⱼ ↦ sⱼ/sᵢ`.**

The analogous statement over the integral model is
`Stacks.ProjectiveFromSections.ι_toProjectiveSpaceAtUniverse`, and it is the one the glueing is
performed with; this is the same statement over the base ring `k`, where a linear substitution in
the homogeneous coordinates acts. -/
theorem ι_toPolynomialModel (i : Fin (n + 1)) :
    (Stacks.ProjectiveFromSections.nvCover s i).ι ≫ toPolynomialModel s hs f =
      AlgebraicGeometry.Proj.fromOfGlobalSections (polyGrading k n)
        (MvPolynomial.eval₂Hom
          (baseRingHom ((Stacks.ProjectiveFromSections.nvCover s i).ι ≫ f))
          (Stacks.ProjectiveFromSections.chartRatio s i))
        (map_irrelevant_eval₂Hom_eq_top _ _
          (Stacks.ProjectiveFromSections.span_range_chartRatio s i)) := by
  refine hom_ext_polynomialModel ?_ ?_
  · rw [Category.assoc, toPolynomialModel_comp_projToSpecCoeff,
      fromOfGlobalSections_comp_projToSpecCoeff _ _
        (Stacks.ProjectiveFromSections.span_range_chartRatio s i),
      toSpecΓ_SpecMap_baseRingHom]
  · rw [Category.assoc, toPolynomialModel_comp_coordinateProjMap,
      fromOfGlobalSections_comp_coordinateProjMap _ _
        (Stacks.ProjectiveFromSections.span_range_chartRatio s i),
      Stacks.ProjectiveFromSections.ι_toProjectiveSpaceAtUniverse]

end Stacks.ProjectiveSpaceChartRatio

end
