module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.ProjectiveSpaceImmersion
public import StacksFrontier.AlgebraicGeometry.AmpleImmersionReduction.Charts
public import StacksFrontier.AlgebraicGeometry.Morphisms.PseudoCoherentFrom
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Away

/-!
# The standard affine charts of projective space over a scheme

The `i`-th standard chart `D₊(Tᵢ)` of `ℙⁿ_S` is affine `n`-space over `S`. This file proves that
identification and deduces that an affine scheme locally of finite type over an affine base
admits an immersion into a projective space over the base, over the base.

Both the integral model `ℙⁿ_ℤ = Proj ℤ[T₀, …, Tₙ]` and `𝔸ⁿ_S`
(Mathlib's `AlgebraicGeometry.AffineSpace`) are base changes from the terminal scheme, so the
chart of `ℙⁿ_S` is the base change of the chart of the integral model, and the whole statement
reduces to a statement about the coordinate ring of `D₊(Tᵢ) ⊆ ℙⁿ_ℤ`: it is a polynomial ring in
the `n` affine coordinates `T_j / T_i`, `j ≠ i`. That ring-level identification is
`Stacks.AlgebraicGeometry.ProjPolyChart.chartEquiv`.

## Main definitions

* `AlgebraicGeometry.projectiveSpaceOver.chartRingEquiv`: the coordinate ring of the `i`-th
  standard chart of `ℙⁿ_ℤ` is a polynomial ring in `n` variables over `ULift ℤ`, for any index
  type `σ` in the universe of the base matched with `{j // j ≠ i}`.
* `AlgebraicGeometry.projectiveSpaceOver.chartIsoBasicOpen`: hence `D₊(Tᵢ) ≅ 𝔸ⁿ_ℤ`.
* `AlgebraicGeometry.projectiveSpaceOver.affineChartAtUniverse`: the resulting open immersion
  `𝔸ⁿ_ℤ ⟶ ℙⁿ_ℤ`.
* `AlgebraicGeometry.projectiveSpaceOver.affineChart`: its base change, the open immersion
  `𝔸ⁿ_S ⟶ ℙⁿ_S` onto the `i`-th standard chart.

## Main results

* `AlgebraicGeometry.projectiveSpaceOver.affineChart_over`: `𝔸ⁿ_S ⟶ ℙⁿ_S` lies over `S`.
* `AlgebraicGeometry.projectiveSpaceOver.opensRange_affineChart`: its image is exactly the
  `i`-th standard chart `AlgebraicGeometry.projectiveSpaceOver.standardChart`.
* `AlgebraicGeometry.projectiveSpaceOver.standardChartIso`: **the identification
  `D₊(Tᵢ) ≅ 𝔸ⁿ_S`** of the `i`-th standard chart of `ℙⁿ_S` with affine `n`-space over `S`.
* `AlgebraicGeometry.exists_isImmersion_projectiveSpaceOver_of_isAffine`: an affine scheme
  locally of finite type over an affine base immerses into a projective space over the base,
  over the base; a case of [Stacks, Tag 02O5].

## Implementation notes

The index type of an affine space must live in the universe of the schemes, while the chart's
natural index type is the subtype `{j : Fin (n + 1) // j ≠ i}` of universe zero. Rather than
fixing a universe lift, the declarations here take an arbitrary `σ : Type u` together with an
equivalence `σ ≃ {j : Fin (n + 1) // j ≠ i}`; a caller needing a concrete index type supplies
`ULift (Fin n)` and `Equiv.ulift.trans (finSuccAboveEquiv i)`.

The ring homomorphism underlying `chartRingEquiv` is bound to a named declaration with its type
written out, `chartRingHom`, before `CommRingCat.ofHom` is applied to it. Applying
`CommRingCat.ofHom` directly to `(chartRingEquiv …).symm.toRingHom` fails: `ofHom` leaves its
`CommRing` instance argument to be solved later, so the multiplication of the expected
`RingHom` is `CommRing.toCommSemiring.….toMul ?inst` with `?inst` a metavariable, while the
`RingEquiv` carries `AddMonoidAlgebra.instMul` on the polynomial side and the standalone
`HomogeneousLocalization.instMul` on the chart side. Naming the homomorphism first fixes both
instances by synthesis, after which the two agree. Mathlib works around the same obstruction in
`AlgebraicGeometry.AffineSpace.isoOfIsAffine` with
`backward.isDefEq.respectTransparency.types false`; no option is needed here.

`AlgebraicGeometry.projectiveSpaceAtUniverse` is a `def` whose body is produced by a tactic
block, so it is not unfolded during unification inside a tactic proof; it is made
`implicit_reducible` locally, which is what lets `Proj.basicOpen` and `Proj.awayι` be used
against it in tactic mode.

## References

* [Stacks Project, Tag 01M3](https://stacks.math.columbia.edu/tag/01M3)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open HomogeneousLocalization Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.SectionsToProjectiveSpace

namespace AlgebraicGeometry.projectiveSpaceOver

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] projectiveSpaceAtUniverse AffineSpace

variable {σ : Type u} (n : ℕ) (i : Fin (n + 1)) (e : σ ≃ {j : Fin (n + 1) // j ≠ i})
  (S : Scheme.{u})

/-! ### The coordinate ring of a standard chart of the integral model -/

/-- **The coordinate ring of the `i`-th standard chart of `ℙⁿ_ℤ` is a polynomial ring in `n`
variables.** The degree-zero part of the localization of `ℤ[T₀, …, Tₙ]` away from `Tᵢ` is
generated by the affine coordinates `T_j / T_i` for `j ≠ i`, freely; this is
`Stacks.AlgebraicGeometry.ProjPolyChart.chartEquiv` with its index type transported along `e`. -/
def chartRingEquiv :
    MvPolynomial σ (ULift.{u} ℤ) ≃+* Away (coordGrading.{u} n) (MvPolynomial.X i) :=
  ((MvPolynomial.renameEquiv (ULift.{u} ℤ) e).toRingEquiv).trans (chartEquiv (ULift.{u} ℤ) n i)

/-- The inverse of `AlgebraicGeometry.projectiveSpaceOver.chartRingEquiv` as a ring
homomorphism. -/
def chartRingHom :
    Away (coordGrading.{u} n) (MvPolynomial.X i) →+* MvPolynomial σ (ULift.{u} ℤ) :=
  (chartRingEquiv n i e).symm.toRingHom

/-- The morphism of commutative rings underlying
`AlgebraicGeometry.projectiveSpaceOver.chartRingHom` is an isomorphism. -/
instance isIso_ofHom_chartRingHom : IsIso (CommRingCat.ofHom (chartRingHom n i e)) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact (chartRingEquiv n i e).symm.bijective

/-- **The `i`-th standard chart of `ℙⁿ_ℤ` is `𝔸ⁿ_ℤ`.** The chart is the spectrum of its
coordinate ring by `AlgebraicGeometry.Proj.basicOpenIsoSpec`, the variable `Tᵢ` being
homogeneous of degree one, and that ring is a polynomial ring in `n` variables by
`AlgebraicGeometry.projectiveSpaceOver.chartRingEquiv`. -/
def chartIsoBasicOpen : Spec (CommRingCat.of (MvPolynomial σ (ULift.{u} ℤ))) ≅
    (Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)).toScheme :=
  asIso (Spec.map (CommRingCat.ofHom (chartRingHom n i e))) ≪≫
    (Proj.basicOpenIsoSpec (coordGrading.{u} n) (MvPolynomial.X i)
      (X_mem_one (ULift.{u} ℤ) n i) one_pos).symm

/-- **The `i`-th standard affine chart of the integral model `ℙⁿ_ℤ`**, as an open immersion of
`𝔸ⁿ_ℤ` onto `D₊(Tᵢ)`. -/
def affineChartAtUniverse : Spec (CommRingCat.of (MvPolynomial σ (ULift.{u} ℤ))) ⟶
    projectiveSpaceAtUniverse.{u} n :=
  (chartIsoBasicOpen n i e).hom ≫ (Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)).ι

/-- The `i`-th standard affine chart of `ℙⁿ_ℤ` is an open immersion. -/
instance : IsOpenImmersion (affineChartAtUniverse n i e) := by
  unfold affineChartAtUniverse
  infer_instance

/-- The image of the `i`-th standard affine chart of `ℙⁿ_ℤ` is `D₊(Tᵢ)`. -/
theorem opensRange_affineChartAtUniverse :
    (affineChartAtUniverse n i e).opensRange =
      Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i) := by
  unfold affineChartAtUniverse
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact (Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)).opensRange_ι

/-! ### The standard affine charts of `ℙⁿ_S` -/

/-- **The `i`-th standard affine chart of `ℙⁿ_S`**: the open immersion `𝔸ⁿ_S ⟶ ℙⁿ_S` obtained by
base change along `S ⟶ Spec ℤ` from the `i`-th standard affine chart of the integral model. Both
`𝔸ⁿ_S` and `ℙⁿ_S` are pullbacks over the terminal scheme, so the base change is a
`CategoryTheory.Limits.pullback.map`. -/
def affineChart : 𝔸(σ; S) ⟶ projectiveSpaceOver n S :=
  pullback.map (terminal.from S) (terminal.from _) (terminal.from S) (terminal.from _)
    (𝟙 S) (affineChartAtUniverse n i e) (𝟙 _) (by simp) (by simp)

/-- The `i`-th standard affine chart of `ℙⁿ_S` is an open immersion. -/
instance : IsOpenImmersion (affineChart n i e S) := by
  unfold affineChart
  exact MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance inferInstance
    (by simp) (by simp)

/-- The `i`-th standard affine chart of `ℙⁿ_S` composed with the projection of `ℙⁿ_S` to the
base is the projection of `𝔸ⁿ_S` to the base, both written as pullback projections. -/
theorem affineChart_comp_fst :
    affineChart n i e S ≫ pullback.fst (terminal.from S)
        (terminal.from (projectiveSpaceAtUniverse.{u} n)) =
      pullback.fst (terminal.from S)
        (terminal.from (Spec (CommRingCat.of (MvPolynomial σ (ULift.{u} ℤ))))) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- The `i`-th standard affine chart of `ℙⁿ_S` composed with the projection of `ℙⁿ_S` to the
integral model is the projection of `𝔸ⁿ_S` to `𝔸ⁿ_ℤ` followed by the `i`-th standard affine chart
of `ℙⁿ_ℤ`, written with pullback projections. -/
theorem affineChart_comp_snd :
    affineChart n i e S ≫ pullback.snd (terminal.from S)
        (terminal.from (projectiveSpaceAtUniverse.{u} n)) =
      pullback.snd (terminal.from S)
          (terminal.from (Spec (CommRingCat.of (MvPolynomial σ (ULift.{u} ℤ))))) ≫
        affineChartAtUniverse n i e :=
  pullback.lift_snd _ _ _

/-- The `i`-th standard affine chart of `ℙⁿ_S` lies over `S`. -/
@[reassoc]
theorem affineChart_over :
    affineChart n i e S ≫ (projectiveSpaceOver n S ↘ S) = 𝔸(σ; S) ↘ S :=
  affineChart_comp_fst n i e S

/-- The `i`-th standard affine chart of `ℙⁿ_S` covers the `i`-th standard affine chart of the
integral model. -/
@[reassoc]
theorem affineChart_toIntegralAtUniverse :
    affineChart n i e S ≫ toIntegralAtUniverse n S =
      AffineSpace.toSpecMvPoly σ S ≫ affineChartAtUniverse n i e :=
  affineChart_comp_snd n i e S

/-- The `i`-th standard affine chart of `ℙⁿ_S` is the base change of the `i`-th standard affine
chart of the integral model: `𝔸ⁿ_S` is the fibre product of `ℙⁿ_S` and `𝔸ⁿ_ℤ` over `ℙⁿ_ℤ`. -/
def pullbackIsoAffineSpace :
    𝔸(σ; S) ≅ pullback (toIntegralAtUniverse n S) (affineChartAtUniverse n i e) where
  hom := pullback.lift (affineChart n i e S) (pullback.snd (terminal.from S)
    (terminal.from (Spec (CommRingCat.of (MvPolynomial σ (ULift.{u} ℤ))))))
    (affineChart_comp_snd n i e S)
  inv := pullback.lift (pullback.fst _ _ ≫ pullback.fst (terminal.from S)
    (terminal.from (projectiveSpaceAtUniverse.{u} n))) (pullback.snd _ _)
    (terminal.hom_ext _ _)
  hom_inv_id := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst,
        affineChart_comp_fst, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]
  inv_hom_id := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp]
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, affineChart_comp_fst, pullback.lift_fst]
      · rw [Category.assoc, affineChart_comp_snd, pullback.lift_snd_assoc]
        exact pullback.condition.symm
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]

/-- The identification `AlgebraicGeometry.projectiveSpaceOver.pullbackIsoAffineSpace` followed
by the first projection is the `i`-th standard affine chart of `ℙⁿ_S`. -/
@[reassoc]
theorem pullbackIsoAffineSpace_hom_fst :
    (pullbackIsoAffineSpace n i e S).hom ≫ pullback.fst _ _ = affineChart n i e S :=
  pullback.lift_fst _ _ _

/-- **The image of the `i`-th standard affine chart of `ℙⁿ_S` is the `i`-th standard chart.** -/
theorem range_affineChart :
    Set.range (affineChart n i e S).base = (standardChart n S i : Set _) := by
  have h : ((pullbackIsoAffineSpace n i e S).hom ≫
      pullback.fst (toIntegralAtUniverse n S) (affineChartAtUniverse n i e)).opensRange =
      standardChart n S i := by
    rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_pullbackFst,
      opensRange_affineChartAtUniverse]
    rfl
  rw [← pullbackIsoAffineSpace_hom_fst n i e S, ← h]
  rfl

/-- **The image of the `i`-th standard affine chart of `ℙⁿ_S` is the `i`-th standard chart.** -/
theorem opensRange_affineChart :
    (affineChart n i e S).opensRange = standardChart n S i :=
  TopologicalSpace.Opens.ext (range_affineChart n i e S)

/-- **The `i`-th standard chart of `ℙⁿ_S` is affine `n`-space over `S`**: the identification
`D₊(Tᵢ) ≅ 𝔸ⁿ_S`. -/
def standardChartIso : 𝔸(σ; S) ≅ (standardChart n S i).toScheme :=
  IsOpenImmersion.isoOfRangeEq (affineChart n i e S) (standardChart n S i).ι
    ((range_affineChart n i e S).trans (Scheme.Opens.range_ι _).symm)

/-- The identification `AlgebraicGeometry.projectiveSpaceOver.standardChartIso` followed by the
inclusion of the `i`-th standard chart into `ℙⁿ_S` is the `i`-th standard affine chart. -/
@[reassoc (attr := simp)]
theorem standardChartIso_hom_ι :
    (standardChartIso n i e S).hom ≫ (standardChart n S i).ι = affineChart n i e S :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The identification of the `i`-th standard chart of `ℙⁿ_S` with `𝔸ⁿ_S` is a morphism over
`S`. -/
@[reassoc]
theorem standardChartIso_hom_ι_over :
    (standardChartIso n i e S).hom ≫ (standardChart n S i).ι ≫
      (projectiveSpaceOver n S ↘ S) = 𝔸(σ; S) ↘ S := by
  rw [← Category.assoc, standardChartIso_hom_ι, affineChart_over]

end AlgebraicGeometry.projectiveSpaceOver

namespace AlgebraicGeometry

universe u

/-- **An affine scheme locally of finite type over an affine base immerses into a projective
space over the base.** Its coordinate ring is generated by finitely many elements over that of
the base, which gives a closed immersion into an affine space over the base
(`AlgebraicGeometry.exists_isClosedImmersion_affineSpace`); that affine space is a standard chart
of a projective space over the base
(`AlgebraicGeometry.projectiveSpaceOver.affineChart`), and a closed immersion followed by an
open immersion is an immersion. This is a case of [Stacks, Tag 02O5]. -/
theorem exists_isImmersion_projectiveSpaceOver_of_isAffine {Y S : Scheme.{u}} (g : Y ⟶ S)
    [IsAffine Y] [IsAffine S] [LocallyOfFiniteType g] :
    ∃ (m : ℕ) (j : Y ⟶ projectiveSpaceOver m S),
      IsImmersion j ∧ j ≫ (projectiveSpaceOver m S ↘ S) = g := by
  obtain ⟨m, c, hc, hcS⟩ := exists_isClosedImmersion_affineSpace g
  have := hc
  refine ⟨m, c ≫ projectiveSpaceOver.affineChart m 0
    (Equiv.ulift.{u}.trans (finSuccAboveEquiv (0 : Fin (m + 1)))) S, inferInstance, ?_⟩
  rw [Category.assoc, projectiveSpaceOver.affineChart_over]
  exact hcS

end AlgebraicGeometry

end
