module

public import StacksFrontier.AlgebraicGeometry.Curves.InseparableGenusChangeDominant
public import StacksFrontier.AlgebraicGeometry.ProjTwistChain.Sections

/-!
# The embedding of `k(x)` that the projection of [Stacks, Tag 0CD1] induces is the chart's

`StacksFrontier/AlgebraicGeometry/Curves/InseparableGenusChangeFunctionField.lean` identifies the
function field of the plane cubic `Z = Proj (k[T₀, T₁, T₂] ⧸ (F))` of [Stacks, Tag 0CD1] with
`k(x)[y] ⧸ (y³ - x² - a)`, and so gives an embedding
`Stacks.Curves.InseparableGenus.chartRatFuncAlgebra` of `k(x)` into it — the one for which `x` is
the chart coordinate `T₁/T₀`.
`StacksFrontier/AlgebraicGeometry/Curves/InseparableGenusChangeDominant.lean` proves the coordinate
projection `f : Z ⟶ 𝐏¹_k` dominant and so gives a second embedding,
`Stacks.Curves.InseparableGenus.projectionRatFuncAlgebra`. This file proves that **the two
embeddings are equal**, which is the last clause of the example of [Stacks, Tag 0CD1]: the purely
inseparable degree-three extension of the example is the extension of function fields that `f`
induces.

## Main results

* `Stacks.Curves.InseparableGenus.appLE_mapHom_planeCubicProjection_ratio`: **`f` read on the
  sections of the chart.** The chart coordinate `S₁/S₀` of `𝐏¹_k` pulls back along `f` to the
  chart coordinate `T₁/T₀` of `Z`.
* `Stacks.Curves.InseparableGenus.appLE_planeCubicProjection_C`: a constant pulls back to that
  constant, because `f` is a morphism over `Spec k`.
* `Stacks.Curves.InseparableGenus.projectionRatFuncAlgebra_eq_chartRatFuncAlgebra`: **the two
  embeddings of `k(x)` into the function field of `Z` agree.**
* `Stacks.Curves.InseparableGenus.isPurelyInseparable_and_finrank_projectionFunctionField`:
  **the extension of function fields that `f` induces is purely inseparable of degree three.**

## Implementation notes

**The shape of the argument.** Two ring homomorphisms out of `k(x) = Frac k[x]` agree as soon as
they agree on `k[x]`, and then as soon as they agree on the constants and on `x`; so the equation
of embeddings reduces to two values. Each value is computed by the same route: the square
`AlgebraicGeometry.appLE_germToFunctionField_commutes` turns the map on function fields into the
map on sections over the charts `D₊(S₀) ⊆ 𝐏¹_k` and `Z ∩ D₊(T₀) = f ⁻¹ᵁ D₊(S₀)`, where the
coordinate of `𝐏¹_k` is a germ of a section by
`Stacks.Curves.InseparableGenus.projectiveLineFunctionFieldEquiv_symm_algebraMap` and the
coordinate of `Z` is one by
`Stacks.Curves.InseparableGenus.functionFieldEquivCurveFunctionField_algebraMap`.

**`f` on sections.** The two values on sections are computed differently. The coordinate is
`Stacks.AlgebraicGeometry.ProjTwistChain.appLE_mapHom_awayToSection`: `f` is
`Stacks.AlgebraicGeometry.ProjTwistChain.mapHom` of the substitution `Sⱼ ↦ Tⱼ` restricted along
the curve, and on the standard open that morphism is `Spec` of
`HomogeneousLocalization.Away.map`, which carries `S₁/S₀` to `T₁/T₀`. The constants need no such
computation: `Stacks.ProjectiveChart.sectionsChartEquiv_C` and
`Stacks.ProjectiveChart.chartPresentation_C` express both of them as pullbacks along the
structure morphisms to `Spec k`, and the projection is a morphism over `Spec k`
(`Stacks.Curves.InseparableGenus.planeCubicProjection_comp_projToSpecCoeff`).

**The two names of `T₀`.** The substitution sends `S₀` to `T₀` by a theorem, not by definition,
so `HomogeneousLocalization.Away ℬ (ψ S₀)` and `HomogeneousLocalization.Away ℬ T₀` are different
types with equal indices. Rather than transport between them,
`appLE_mapHom_planeCubicProjection_ratio` takes the images of `S₀` and `S₁` as free variables
together with the equations naming them, so that the specific instance is obtained by
substitution instead of by a rewrite under a dependent type.

## References

* [Stacks Project, Tag 0CD1](https://stacks.math.columbia.edu/tag/0CD1)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 02JU](https://stacks.math.columbia.edu/tag/02JU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open Stacks.ProjectiveChart (subschemeChart chartPresentation sectionsChartEquiv chartRingEquiv
  ratio X_mem_degree_one sectionsChartEquiv_C chartPresentation_C)
open Stacks.AlgebraicGeometry.ProjShared (mapDomain)
open Stacks.AlgebraicGeometry.ProjPolyChart (projToSpecCoeff)
open Stacks.AlgebraicGeometry.ProjTwistChain (mapHom appLE_mapHom_awayToSection
  appLE_awayι_awayToSection appLE_top_top appLE_congr_hom map_isLocalizationElem mem_of_mem)

universe u

namespace Stacks.Curves.InseparableGenus

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### The images of the two coordinates of `𝐏¹_k` -/

/-- The coordinate projection sends the coordinate `S₀` of `𝐏¹_k` to `T₀`. -/
theorem coordProjHom_X_zero (k : Type u) [CommRing k] :
    coordProjHom k (MvPolynomial.X (0 : Fin 2)) = MvPolynomial.X (0 : Fin 3) := by
  rw [coordProjHom_X]; rfl

/-- The coordinate projection sends the coordinate `S₁` of `𝐏¹_k` to `T₁`. -/
theorem coordProjHom_X_one (k : Type u) [CommRing k] :
    coordProjHom k (MvPolynomial.X (1 : Fin 2)) = MvPolynomial.X (1 : Fin 3) := by
  rw [coordProjHom_X]; rfl

/-- The graded coordinate projection sends `S₀` to `T₀`. -/
theorem coordProjGradedHom_X_zero (k : Type u) [CommRing k] :
    (coordProjGradedHom k) (MvPolynomial.X (0 : Fin 2)) = MvPolynomial.X (0 : Fin 3) := by
  change coordProjHom k (MvPolynomial.X (0 : Fin 2)) = _
  exact coordProjHom_X_zero k

/-- The graded coordinate projection sends `S₁` to `T₁`. -/
theorem coordProjGradedHom_X_one (k : Type u) [CommRing k] :
    (coordProjGradedHom k) (MvPolynomial.X (1 : Fin 2)) = MvPolynomial.X (1 : Fin 3) := by
  change coordProjHom k (MvPolynomial.X (1 : Fin 2)) = _
  exact coordProjHom_X_one k

/-! ### The coordinates of `𝐏¹_k` and of `𝐏²_k` as homogeneous elements -/

/-- A coordinate of `k[S₀, S₁]` is homogeneous of degree one. Stated at the index type `Fin 2`
rather than at `Fin (1 + 1)`, which is what `Stacks.ProjectiveChart.X_mem_degree_one` produces
and what instance search cannot match against the curve's `Fin 2`. -/
theorem X_mem_degree_one_two (k : Type u) [CommRing k] (j : Fin 2) :
    MvPolynomial.X j ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k 1 :=
  X_mem_degree_one k j

/-- A coordinate of `k[T₀, T₁, T₂]` is homogeneous of degree one, at the index type `Fin 3`. -/
theorem X_mem_degree_one_three (k : Type u) [CommRing k] (j : Fin 3) :
    MvPolynomial.X j ∈ MvPolynomial.homogeneousSubmodule (Fin 3) k 1 :=
  X_mem_degree_one k j

/-! ### The chart `D₊(S₀)` of `𝐏¹_k` -/

/-- The ring of sections of `𝐏¹_k` over the chart `D₊(S₀)` is nontrivial. -/
instance nontrivial_sections_basicOpen_X_zero_projectiveLine (k : Type u) [Field k] :
    Nontrivial Γ(AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k),
      AlgebraicGeometry.Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k)
        (MvPolynomial.X (0 : Fin 2))) :=
  (sectionsChartEquiv k (0 : Fin 2)).symm.toEquiv.nontrivial

/-- The chart `D₊(S₀)` of `𝐏¹_k` is nonempty. -/
instance nonempty_basicOpen_X_zero_projectiveLine (k : Type u) [Field k] :
    Nonempty (AlgebraicGeometry.Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X (0 : Fin 2))) :=
  (AlgebraicGeometry.Proj.isAffineOpen_basicOpen _ _ (X_mem_degree_one_two k 0)
    Nat.one_pos).nonempty_of_nontrivial

/-- The standard chart of `𝐏¹_k` is the chart isomorphism followed by `awayι`. -/
private theorem lineChart_eq_lineChartIso_comp_awayι (k : Type u) [Field k] :
    lineChart k = (lineChartIso k).hom ≫
      AlgebraicGeometry.Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 2) k)
        (MvPolynomial.X (0 : Fin 2)) (X_mem_degree_one_two k 0) Nat.one_pos := rfl

/-- The inverse image of `D₊(S₀)` under `awayι` at `S₀` is everything. -/
private theorem preimage_basicOpen_awayι_X_zero (k : Type u) [Field k] :
    AlgebraicGeometry.Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 2) k)
      (MvPolynomial.X (0 : Fin 2)) (X_mem_degree_one_two k 0) Nat.one_pos ⁻¹ᵁ
      AlgebraicGeometry.Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k)
        (MvPolynomial.X (0 : Fin 2)) = ⊤ := by
  rw [← AlgebraicGeometry.Proj.opensRange_awayι (MvPolynomial.homogeneousSubmodule (Fin 2) k)
    (MvPolynomial.X (0 : Fin 2)) (X_mem_degree_one_two k 0) Nat.one_pos,
    Scheme.Hom.preimage_opensRange]

/-- The inverse image of `D₊(S₀)` under the standard chart `𝔸¹_k → 𝐏¹_k` is all of `𝔸¹_k`. -/
theorem preimage_basicOpen_lineChart (k : Type u) [Field k] :
    lineChart k ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X (0 : Fin 2)) = ⊤ := by
  rw [lineChart_eq_lineChartIso_comp_awayι, Scheme.Hom.comp_preimage,
    preimage_basicOpen_awayι_X_zero]
  simp

/-- **The standard chart of `𝐏¹_k` is the identity on sections.** A polynomial in the chart
coordinate `S₁/S₀`, read as a function on `D₊(S₀)`, pulls back along the chart to itself. -/
theorem appLE_lineChart_awayToSection (k : Type u) [Field k]
    (h : (⊤ : (Stacks.Chow.specPolynomial k).Opens) ≤ lineChart k ⁻¹ᵁ
      AlgebraicGeometry.Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k)
        (MvPolynomial.X (0 : Fin 2)))
    (p : Polynomial k) :
    ((lineChart k).appLE (AlgebraicGeometry.Proj.basicOpen
          (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X (0 : Fin 2))) ⊤ h).hom
        ((AlgebraicGeometry.Proj.awayToSection
          (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X (0 : Fin 2))).hom
            (lineChartRingEquiv k p)) =
      (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv.hom p := by
  have hawayι := preimage_basicOpen_awayι_X_zero k
  have hiso := lineChart_eq_lineChartIso_comp_awayι k
  have hsplit := Scheme.Hom.appLE_comp_appLE (lineChartIso k).hom
    (AlgebraicGeometry.Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 2) k)
      (MvPolynomial.X (0 : Fin 2)) (X_mem_degree_one_two k 0) Nat.one_pos)
    (AlgebraicGeometry.Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k)
      (MvPolynomial.X (0 : Fin 2))) ⊤ ⊤ hawayι.ge le_top
  rw [appLE_top_top (lineChartIso k).hom le_top] at hsplit
  have hfin := (appLE_congr_hom hiso (AlgebraicGeometry.Proj.basicOpen
    (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X (0 : Fin 2))) ⊤ h
      (by rw [← hiso]; exact h)).trans hsplit.symm
  rw [hfin]
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [appLE_awayι_awayToSection Nat.one_pos (X_mem_degree_one_two k 0) hawayι.ge]
  have hspec : (lineChartIso k).hom =
      Spec.map (CommRingCat.ofHom (lineChartRingEquiv k).symm.toRingHom) := rfl
  rw [hspec]
  have hnat := congrArg (fun m : CommRingCat.of (Stacks.ProjectiveChart.ChartRing k 1 0) ⟶
      Γ(Spec (CommRingCat.of (Polynomial k)), ⊤) => m.hom (lineChartRingEquiv k p))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (lineChartRingEquiv k).symm.toRingHom))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom] at hnat
  rw [← hnat]
  simp

/-- **A rational function on `𝐏¹_k` which is a polynomial in the chart coordinate is the germ of
that polynomial read on the chart.** -/
theorem projectiveLineFunctionFieldEquiv_symm_algebraMap (k : Type u) [Field k]
    (p : Polynomial k) :
    (projectiveLineFunctionFieldEquiv k).symm (algebraMap (Polynomial k) (RatFunc k) p) =
      ((AlgebraicGeometry.Proj
          (MvPolynomial.homogeneousSubmodule (Fin 2) k)).germToFunctionField
          (AlgebraicGeometry.Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k)
            (MvPolynomial.X (0 : Fin 2)))).hom
        ((AlgebraicGeometry.Proj.awayToSection
          (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X (0 : Fin 2))).hom
            (lineChartRingEquiv k p)) := by
  refine (AlgebraicGeometry.dominantFunctionFieldMap (lineChart k)).injective ?_
  rw [dominantFunctionFieldMap_projectiveLineFunctionFieldEquiv_symm]
  have hle : (⊤ : (Stacks.Chow.specPolynomial k).Opens) ≤ lineChart k ⁻¹ᵁ
      AlgebraicGeometry.Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k)
        (MvPolynomial.X (0 : Fin 2)) := (preimage_basicOpen_lineChart k).ge
  obtain ⟨x0⟩ : Nonempty (Stacks.Chow.specPolynomial k) := inferInstance
  rw [AlgebraicGeometry.dominantFunctionFieldMap_germToFunctionField_of_mem (lineChart k) x0 _
      (hle (Set.mem_univ x0)) ⊤ (Set.mem_univ x0) hle,
    appLE_lineChart_awayToSection k hle p]
  rw [RingEquiv.symm_apply_eq]
  exact (Stacks.Chow.specFunctionFieldEquiv_specAlgebraMap (CommRingCat.of (Polynomial k))
    (RatFunc k) p).symm.trans
      (congrArg (Stacks.Chow.specFunctionFieldEquiv (CommRingCat.of (Polynomial k)) (RatFunc k))
        (Stacks.Chow.germToFunctionField_eq_specAlgebraMap (CommRingCat.of (Polynomial k)) p).symm)

/-! ### The projection read on the sections of the chart -/

/-- **The coordinate projection of [Stacks, Tag 0CD1] is a morphism over `Spec k`.** -/
theorem planeCubicProjection_comp_projToSpecCoeff (k : Type u) [Field k] (a : k) :
    planeCubicProjection k a ≫ projToSpecCoeff k 1 =
      planeCubicEmbedding k a ≫ projToSpecCoeff k 2 := by
  rw [planeCubicProjection, Category.assoc,
    mapHom_comp_projToSpecCoeff (coordProjGradedHom k) (coordProjGradedHom_C k),
    ← Category.assoc, IsOpenImmersion.lift_fac]

/-- **The chart `Z ∩ D₊(T₀)` of the curve is the inverse image of the chart `D₊(S₀)` of
`𝐏¹_k`.** -/
theorem preimage_basicOpen_planeCubicProjection (k : Type u) [Field k] (a : k) :
    planeCubicProjection k a ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X (0 : Fin 2)) =
      subschemeChart (planeCubicEmbedding k a) 0 := by
  rw [planeCubicProjection_preimage_basicOpen k a (MvPolynomial.X (0 : Fin 2)) 1
    (X_mem_degree_one_two k 0) Nat.one_pos, coordProjHom_X_zero]

/-- **The chart coordinate `S₁/S₀` of `𝐏¹_k` pulls back along the projection to the chart
coordinate `T₁/T₀` of the curve.** The images of `S₀` and `S₁` are free variables here, named by
the two equations, so that the instance needed is obtained by substitution; see the
implementation notes. -/
theorem appLE_mapHom_planeCubicProjection_ratio (k : Type u) [Field k] (a : k)
    {g₀ g₁ : MvPolynomial (Fin 3) k}
    (hg₀ : (coordProjGradedHom k) (MvPolynomial.X (0 : Fin 2)) = g₀)
    (hg₁ : (coordProjGradedHom k) (MvPolynomial.X (1 : Fin 2)) = g₁)
    (h0 : g₀ ∈ MvPolynomial.homogeneousSubmodule (Fin 3) k 1)
    (h1 : g₁ ∈ MvPolynomial.homogeneousSubmodule (Fin 3) k 1)
    (h : planeCubicEmbedding k a ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
          (MvPolynomial.homogeneousSubmodule (Fin 3) k) g₀ ≤
        planeCubicProjection k a ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
          (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X (0 : Fin 2))) :
    ((planeCubicProjection k a).appLE
          (AlgebraicGeometry.Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k)
            (MvPolynomial.X (0 : Fin 2)))
          (planeCubicEmbedding k a ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
            (MvPolynomial.homogeneousSubmodule (Fin 3) k) g₀) h).hom
        ((AlgebraicGeometry.Proj.awayToSection
            (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X (0 : Fin 2))).hom
          (Away.isLocalizationElem (X_mem_degree_one_two k 0)
            (X_mem_degree_one_two k 1))) =
      ((planeCubicEmbedding k a).appLE
          (AlgebraicGeometry.Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 3) k) g₀)
          (planeCubicEmbedding k a ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
            (MvPolynomial.homogeneousSubmodule (Fin 3) k) g₀) le_rfl).hom
        ((AlgebraicGeometry.Proj.awayToSection
          (MvPolynomial.homogeneousSubmodule (Fin 3) k) g₀).hom
            (Away.isLocalizationElem h0 h1)) := by
  subst hg₀
  subst hg₁
  rw [appLE_mapHom_awayToSection (MvPolynomial.homogeneousSubmodule (Fin 2) k)
    (MvPolynomial.homogeneousSubmodule (Fin 3) k) (coordProjGradedHom k) Nat.one_pos
    (X_mem_degree_one_two k 0) (q := planeCubicProjection k a)
    (IsOpenImmersion.lift _ (planeCubicEmbedding k a)
      (range_base_subset_range_mapDomain k a))
    (IsOpenImmersion.lift_fac _ _ _) rfl h,
    map_isLocalizationElem (MvPolynomial.homogeneousSubmodule (Fin 2) k)
      (MvPolynomial.homogeneousSubmodule (Fin 3) k) (coordProjGradedHom k)
      (X_mem_degree_one_two k 0) (X_mem_degree_one_two k 1)]

/-- **A constant pulls back along the projection to that constant.** Both sides are the pullback
of the constant along a structure morphism to `Spec k`, and the projection is a morphism over
`Spec k`. -/
theorem appLE_planeCubicProjection_C (k : Type u) [Field k] (a : k) (c : k)
    (h : subschemeChart (planeCubicEmbedding k a) 0 ≤
      planeCubicProjection k a ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X (0 : Fin 2))) :
    ((planeCubicProjection k a).appLE
          (AlgebraicGeometry.Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k)
            (MvPolynomial.X (0 : Fin 2))) (subschemeChart (planeCubicEmbedding k a) 0) h).hom
        (sectionsChartEquiv k (0 : Fin 2) (MvPolynomial.C c)) =
      chartPresentation (planeCubicEmbedding k a) 0 (MvPolynomial.C c) := by
  rw [show sectionsChartEquiv k (0 : Fin 2) (MvPolynomial.C c) =
        ((projToSpecCoeff k 1).appLE ⊤ (AlgebraicGeometry.Proj.basicOpen
            (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X (0 : Fin 2)))
          (fun _ _ => trivial)).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)
      from Stacks.ProjectiveChart.sectionsChartEquiv_C k 0 c,
    show chartPresentation (planeCubicEmbedding k a) 0 (MvPolynomial.C c) =
        ((planeCubicEmbedding k a ≫ projToSpecCoeff k 2).appLE ⊤
          (subschemeChart (planeCubicEmbedding k a) 0) (fun _ _ => trivial)).hom
          ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)
      from Stacks.ProjectiveChart.chartPresentation_C (planeCubicEmbedding k a) 0 c]
  have e1 := Scheme.Hom.appLE_comp_appLE (planeCubicProjection k a) (projToSpecCoeff k 1)
    ⊤ (AlgebraicGeometry.Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k)
      (MvPolynomial.X (0 : Fin 2))) (subschemeChart (planeCubicEmbedding k a) 0)
    (fun _ _ => trivial) h
  have e3 := appLE_congr_hom (planeCubicProjection_comp_projToSpecCoeff k a)
    (⊤ : (Spec (CommRingCat.of k)).Opens) (subschemeChart (planeCubicEmbedding k a) 0)
    (fun _ _ => trivial) (fun _ _ => trivial)
  have hcat := congrArg (fun m : Γ(Spec (CommRingCat.of k), ⊤) ⟶
      Γ(planeCubicCurve k a, subschemeChart (planeCubicEmbedding k a) 0) =>
    m.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)) (e1.trans e3)
  simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] using hcat

/-! ### The chart presentation of the curve on germs -/

/-- The chart presentation of the curve sends the class of a polynomial `y` to the section
`chartPresentation (planeCubicEmbedding k a) 0 y`. -/
theorem planeCubicChartEquiv_mk (k : Type u) [Field k] (a : k) (y : MvPolynomial (Fin 2) k) :
    planeCubicChartEquiv k a (Ideal.Quotient.mk _ y) =
      chartPresentation (planeCubicEmbedding k a) 0 y := rfl

/-- The chart presentation of the curve, read as the restriction along the embedding of a
function on the standard chart of `𝐏²_k`. -/
theorem appLE_planeCubicEmbedding_sectionsChartEquiv (k : Type u) [Field k] (a : k)
    (y : MvPolynomial (Fin 2) k) :
    ((planeCubicEmbedding k a).appLE (AlgebraicGeometry.Proj.basicOpen
          (MvPolynomial.homogeneousSubmodule (Fin 3) k) (MvPolynomial.X (0 : Fin 3)))
          (subschemeChart (planeCubicEmbedding k a) 0) le_rfl).hom
        (sectionsChartEquiv k (0 : Fin 3) y) =
      planeCubicChartEquiv k a (Ideal.Quotient.mk _ y) := by
  rw [planeCubicChartEquiv_mk, Scheme.Hom.appLE_eq_app]
  rfl

/-- The chart coordinate `T₁/T₀` of the curve, as a section of the structure sheaf. -/
theorem sectionsChartEquiv_X_zero_eq_awayToSection (k : Type u) [Field k] :
    sectionsChartEquiv k (0 : Fin 3) (MvPolynomial.X (0 : Fin 2)) =
      (AlgebraicGeometry.Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin 3) k)
        (MvPolynomial.X (0 : Fin 3))).hom
          (Away.isLocalizationElem (X_mem_degree_one_three k 0)
            (X_mem_degree_one_three k 1)) := by
  have hX : chartRingEquiv k (0 : Fin 3) (MvPolynomial.X (0 : Fin 2)) =
      ratio k (0 : Fin 3) (1 : Fin 3) := by
    simp [chartRingEquiv, Stacks.ProjectiveChart.chartRingEquivDeg0,
      Stacks.ProjectiveChart.chartHom]
  rw [sectionsChartEquiv, RingEquiv.trans_apply, hX]
  rfl

/-- The chart coordinate of `𝔸¹_k` corresponds to the element `S₁/S₀` of the degree-zero
localization of `k[S₀, S₁]` at `S₀`. -/
theorem sectionsChartEquiv_X_zero_eq_awayToSection_line (k : Type u) [Field k] :
    lineChartRingEquiv k Polynomial.X =
      Away.isLocalizationElem (X_mem_degree_one_two k 0)
        (X_mem_degree_one_two k 1) := by
  rw [lineChartRingEquiv_X]
  rfl

/-- A constant `c` of `k`, read as a section of `𝐏¹_k` over `D₊(S₀)` through the chart, is the
section `sectionsChartEquiv k 0 (C c)`. -/
theorem lineChartRingEquiv_C (k : Type u) [Field k] (c : k) :
    (AlgebraicGeometry.Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin 2) k)
        (MvPolynomial.X (0 : Fin 2))).hom (lineChartRingEquiv k (Polynomial.C c)) =
      sectionsChartEquiv k (0 : Fin 2) (MvPolynomial.C c) := by
  have h : (MvPolynomial.uniqueAlgEquiv k (Fin 1)).toRingEquiv.symm (Polynomial.C c) =
      MvPolynomial.C c := by simp
  rw [lineChartRingEquiv, RingEquiv.trans_apply, h, sectionsChartEquiv, RingEquiv.trans_apply]
  rfl

/-! ### The constant `c` in the function field of the curve -/

/-- The constant `c` of `k`, read in `k(x)[y] ⧸ (y³ - x² - a)` through the chart. -/
@[simp] theorem planeCubicChartToCurveFunctionField_C (k : Type u) [Field k] (a : k) (c : k) :
    planeCubicChartToCurveFunctionField k a (Ideal.Quotient.mk _ (MvPolynomial.C c)) =
      algebraMap (RatFunc k) (curveFunctionField k a) (RatFunc.C c) := by
  rw [planeCubicChartToCurveFunctionField, RingHom.comp_apply, RingEquiv.coe_toRingHom,
    planeCubicChartEquivAdjoinRoot_mk, bivariateEquivSwap_C,
    show (AdjoinRoot.mk (chartCubic k a)) (Polynomial.C (Polynomial.C c)) =
      AdjoinRoot.of (chartCubic k a) (Polynomial.C c) from rfl,
    Stacks.AdjoinRootFraction.toMapAdjoinRoot_of, RatFunc.algebraMap_C,
    AdjoinRoot.algebraMap_eq]

/-! ### The two embeddings of `k(x)` agree -/

/-- **The germ on the chart of the curve, read in `k(x)[y] ⧸ (y³ - x² - a)`.** -/
theorem germToFunctionField_planeCubicChartEquiv (k : Type u) [Field k] [ExpChar k 3] (a : k)
    (ha : ∀ b : k, b ^ 3 ≠ a) (z : planeCubicChart k a) :
    letI := isIntegral_planeCubicCurve k a ha
    ((planeCubicCurve k a).germToFunctionField
        (subschemeChart (planeCubicEmbedding k a) 0)).hom (planeCubicChartEquiv k a z) =
      (functionFieldEquivCurveFunctionField k a ha).symm
        (planeCubicChartToCurveFunctionField k a z) := by
  let := isIntegral_planeCubicCurve k a ha
  have h := functionFieldEquivCurveFunctionField_algebraMap k a ha z
  rw [RingHom.algebraMap_toAlgebra] at h
  exact ((functionFieldEquivCurveFunctionField k a ha).symm_apply_eq.mpr h.symm).symm

/-- **The embedding of `k(x)` which the coordinate projection `f : Z ⟶ 𝐏¹_k` of
[Stacks, Tag 0CD1] induces on function fields is the one which calls `x` the chart coordinate
`T₁/T₀`.** -/
theorem planeCubicProjectionFunctionFieldMap_eq (k : Type u) [Field k] [ExpChar k 3] (a : k)
    (ha : ∀ b : k, b ^ 3 ≠ a) :
    letI := isIntegral_planeCubicCurve k a ha
    (planeCubicProjectionFunctionFieldMap k a ha).comp
        (projectiveLineFunctionFieldEquiv k).symm.toRingHom =
      ((functionFieldEquivCurveFunctionField k a ha).symm :
          curveFunctionField k a →+* (planeCubicCurve k a).functionField).comp
        (algebraMap (RatFunc k) (curveFunctionField k a)) := by
  let := isIntegral_planeCubicCurve k a ha
  let := isDominant_planeCubicProjection k a
  have hV : planeCubicProjection k a ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X (0 : Fin 2)) =
      subschemeChart (planeCubicEmbedding k a) 0 := preimage_basicOpen_planeCubicProjection k a
  have hle : subschemeChart (planeCubicEmbedding k a) 0 ≤
      planeCubicProjection k a ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X (0 : Fin 2)) := hV.ge
  obtain ⟨x0⟩ : Nonempty (subschemeChart (planeCubicEmbedding k a) 0) := inferInstance
  -- the germ square for the projection
  have hgerm : ∀ s : Γ(AlgebraicGeometry.Proj
        (MvPolynomial.homogeneousSubmodule (Fin 2) k),
      AlgebraicGeometry.Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k)
        (MvPolynomial.X (0 : Fin 2))),
      planeCubicProjectionFunctionFieldMap k a ha
          (((AlgebraicGeometry.Proj
            (MvPolynomial.homogeneousSubmodule (Fin 2) k)).germToFunctionField _).hom s) =
        ((planeCubicCurve k a).germToFunctionField
            (subschemeChart (planeCubicEmbedding k a) 0)).hom
          (((planeCubicProjection k a).appLE _ _ hle).hom s) := fun s =>
    AlgebraicGeometry.dominantFunctionFieldMap_germToFunctionField_of_mem
      (planeCubicProjection k a) x0.1 _ (hle x0.2) _ x0.2 hle s
  refine IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial k)) ?_
  refine Polynomial.ringHom_ext (fun c => ?_) ?_
  · simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom]
    rw [projectiveLineFunctionFieldEquiv_symm_algebraMap k (Polynomial.C c),
      lineChartRingEquiv_C, hgerm, appLE_planeCubicProjection_C k a c hle,
      ← planeCubicChartEquiv_mk k a (MvPolynomial.C c),
      germToFunctionField_planeCubicChartEquiv k a ha,
      planeCubicChartToCurveFunctionField_C, RatFunc.algebraMap_C]
  · simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom]
    rw [projectiveLineFunctionFieldEquiv_symm_algebraMap k Polynomial.X,
      sectionsChartEquiv_X_zero_eq_awayToSection_line, hgerm,
      appLE_mapHom_planeCubicProjection_ratio k a (coordProjGradedHom_X_zero k)
        (coordProjGradedHom_X_one k) (X_mem_degree_one_three k 0)
        (X_mem_degree_one_three k 1) hle,
      ← sectionsChartEquiv_X_zero_eq_awayToSection,
      appLE_planeCubicEmbedding_sectionsChartEquiv,
      germToFunctionField_planeCubicChartEquiv k a ha,
      planeCubicChartToCurveFunctionField_X_zero, RatFunc.algebraMap_X]

/-- **The embedding of `k(x)` that the coordinate projection of [Stacks, Tag 0CD1] induces is the
chart's.** This is the last clause of the example: the purely inseparable degree-three extension
of function fields is the one `f` induces. -/
theorem projectionRatFuncAlgebra_eq_chartRatFuncAlgebra (k : Type u) [Field k] [ExpChar k 3]
    (a : k) (ha : ∀ b : k, b ^ 3 ≠ a) :
    projectionRatFuncAlgebra k a ha = chartRatFuncAlgebra k a ha :=
  congrArg RingHom.toAlgebra (planeCubicProjectionFunctionFieldMap_eq k a ha)

/-- **The function field of the curve of [Stacks, Tag 0CD1] is a purely inseparable extension of
`k(x)` of degree three, for the embedding of `k(x)` the coordinate projection
`f : Z ⟶ 𝐏¹_k` induces on function fields.**

This is the extension of the example: `Stacks.Curves.InseparableGenus.projectionRatFuncAlgebra`
is the embedding of `k(x)` the extension of function fields of `f` gives, through the
identification of the function field of `𝐏¹_k` with `k(x)`. -/
theorem isPurelyInseparable_and_finrank_projectionFunctionField (k : Type u) [Field k]
    [ExpChar k 3] (a : k) (ha : ∀ b : k, b ^ 3 ≠ a) :
    letI := isIntegral_planeCubicCurve k a ha
    letI := projectionRatFuncAlgebra k a ha
    IsPurelyInseparable (RatFunc k) (planeCubicCurve k a).functionField ∧
      Module.finrank (RatFunc k) (planeCubicCurve k a).functionField = 3 := by
  let := isIntegral_planeCubicCurve k a ha
  rw [projectionRatFuncAlgebra_eq_chartRatFuncAlgebra k a ha]
  exact isPurelyInseparable_and_finrank_functionField_planeCubicCurve k a ha

end Stacks.Curves.InseparableGenus

end
