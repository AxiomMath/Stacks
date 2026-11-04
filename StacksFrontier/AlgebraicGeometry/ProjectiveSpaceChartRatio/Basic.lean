module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinates
public import StacksFrontier.AlgebraicGeometry.TwistPullbackRatio.Comparison

/-!
# The standard chart of projective space over a ring, and the pulled-back ratios

Let `X` be a scheme over `Spec k`, let `L` be an invertible `𝒪_X`-module and let `s₀, …, sₙ` be
global sections of `L` generating it. [Stacks, Tag 01ND] attaches to this datum a morphism
`φ : X ⟶ ℙⁿ_k`. This file computes `φ` on the standard affine chart: over `X_{sᵢ}` the morphism
lands in `D₊(Tᵢ)`, whose coordinate ring is the polynomial ring `k[Y_j : j ≠ i]` on the affine
coordinates `Y_j = T_j / T_i`, and `φ` pulls `Y_j` back to the ratio `s_j / s_i`.

`Stacks.TwistPullbackPinned.appLE_coordFrac_chart` is the same computation for the *integral*
model `ℙⁿ_ℤ`. The statement over `Spec k` does not follow from it formally, because `X ⟶ ℙⁿ_ℤ`
forgets the `k`-structure; what this file adds is the passage through the comparison of the two
models of `ℙⁿ_k`, `Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison`.

## Main definitions

* `Stacks.ProjectiveSpaceChartRatio.coordFracAt`: the degree-zero fraction `T_j / T_i` in the
  standard chart of `Proj R[T₀, …, Tₙ]`; for `j ≠ i` it is the affine coordinate
  `Stacks.AlgebraicGeometry.ProjPolyChart.chartCoord`.
* `Stacks.ProjectiveSpaceChartRatio.toPolynomialModel`: the morphism `φ : X ⟶ ℙⁿ_k` of
  [Stacks, Tag 01ND], read in the polynomial model `Proj k[T₀, …, Tₙ]`.
* `Stacks.ProjectiveSpaceChartRatio.chartBaseHom`: the structure morphism of `X` over `k`,
  restricted to the chart `X_{sᵢ}`.
* `Stacks.ProjectiveSpaceChartRatio.chartPullback`: the composite
  `k[Y_j : j ≠ i] ≅ Γ(ℙⁿ_k, D₊(Tᵢ)) → Γ(X, X_{sᵢ})`.

## Main results

* `Stacks.ProjectiveSpaceChartRatio.appLE_awayToSection_projMap`: the chart square of
  `AlgebraicGeometry.Proj.map`, read on sections.
* `Stacks.ProjectiveSpaceChartRatio.appLE_awayToSection_coordinateProjMap`: the same for the
  projection `Proj k[T] ⟶ ℙⁿ_ℤ` of the comparison of the two models.
* `Stacks.ProjectiveSpaceChartRatio.appLE_coordFracAt_chart`: **`φ^♯(T_j/T_i) = s_j/s_i` over
  `Spec k`.**
* `Stacks.ProjectiveSpaceChartRatio.appLE_coeffToAway_chart`: `φ` pulls a constant back to the
  constant, i.e. the chart map is a `k`-algebra map.
* `Stacks.ProjectiveSpaceChartRatio.chartPullback_eq`: **the two together** — the composite
  `k[Y_j : j ≠ i] ≅ Γ(D₊(Tᵢ)) → Γ(X, X_{sᵢ})` is the `k`-algebra map sending `Y_j` to
  `s_j / s_i`.
* `Stacks.ProjectiveSpaceChartRatio.toProjectiveSpaceOfModule_comp_eq_toPolynomialModel`: the
  morphism of [Stacks, Tag 0FCY] is the morphism computed here, read through the coordinate
  isomorphism of a basis.

## Implementation notes

`AlgebraicGeometry.projectiveSpaceAtUniverse` is declared `implicit_reducible` locally, as in
`StacksFrontier.AlgebraicGeometry.TwistPullbackRatio.Comparison`: without it `rw` refuses goals that
mention both `ℙⁿ_ℤ` and `Proj (polyGrading (ULift ℤ) n)`, the motive failing to be type-correct
at `implicit` transparency although the two schemes are the same term.

The chart square of `AlgebraicGeometry.Proj.map` is restated here rather than used through
Mathlib's `AlgebraicGeometry.Proj.awayToSection_comp_appLE`: the latter speaks of
`HomogeneousLocalization.Away ℬ (ψ s)`, and `ψ (Tᵢ) = Tᵢ` is not a definitional equality, so the
target type has to be taken as a variable and substituted, as in
`Stacks.AlgebraicGeometry.ProjBaseChange.awayι_comp_projMap`, with the same hypotheses.

## References

* [Stacks Project, Tag 01ND](https://stacks.math.columbia.edu/tag/01ND)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
* [Stacks Project, Tag 01NG](https://stacks.math.columbia.edu/tag/01NG)
* [Stacks Project, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open HomogeneousLocalization
open Stacks.AlgebraicGeometry.ProjBaseChange Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.ProjectiveFromSections Stacks.SectionsToProjectiveSpace

namespace Stacks.ProjectiveSpaceChartRatio

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] AlgebraicGeometry.projectiveSpaceAtUniverse

section Generic

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-- The chart square of `AlgebraicGeometry.Proj.map`, read on sections. -/
theorem appLE_awayToSection_projMap (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ)
    {d : ℕ} {s : A} (hs : s ∈ 𝒜 d) {t : B} (ht : t ∈ ℬ d) (hst : ψ s = t)
    (θ : Away 𝒜 s →+* Away ℬ t)
    (hθ : ∀ (k : ℕ) (a : A) (ha : a ∈ 𝒜 (k • d)) (ha' : ψ a ∈ ℬ (k • d)),
      θ (Away.mk 𝒜 hs k a ha) = Away.mk ℬ ht k (ψ a) ha')
    (e : AlgebraicGeometry.Proj.basicOpen ℬ t ≤
      AlgebraicGeometry.Proj.map ψ hψ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 s)
    (z : Away 𝒜 s) :
    (AlgebraicGeometry.Proj.map ψ hψ).appLE
        (AlgebraicGeometry.Proj.basicOpen 𝒜 s) (AlgebraicGeometry.Proj.basicOpen ℬ t) e
        ((AlgebraicGeometry.Proj.awayToSection 𝒜 s).hom z) =
      (AlgebraicGeometry.Proj.awayToSection ℬ t).hom (θ z) := by
  subst hst
  have hθ' : θ = Away.map ψ s := by
    refine RingHom.ext fun x => ?_
    obtain ⟨k, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hs x
    rw [hθ k a ha (ψ.map_mem ha), Away.map_mk]
  subst hθ'
  exact CategoryTheory.ConcreteCategory.congr_hom
    (AlgebraicGeometry.Proj.awayToSection_comp_appLE ψ hψ hs) z

end Generic

/-- `AlgebraicGeometry.Scheme.Hom.appLE` from `⊤` to `⊤` is the map on global sections. -/
theorem appLE_top_top {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    (e : (⊤ : Y.Opens) ≤ g ⁻¹ᵁ (⊤ : Z.Opens)) (z : Γ(Z, ⊤)) :
    g.appLE ⊤ ⊤ e z = g.appTop z := by
  rw [Scheme.Hom.appLE, CategoryTheory.ConcreteCategory.comp_apply]
  show Y.presheaf.map (eqToHom (show g ⁻¹ᵁ (⊤ : Z.Opens) = ⊤ from rfl)).op _ = _
  exact Functor.map_id_apply _ _ _

section Coefficients

variable (k : Type u) [CommRing k] (n : ℕ)

/-- The degree-zero fraction `T_j / T_i` in the standard chart of `Proj R[T₀, …, Tₙ]`. -/
def coordFracAt (i j : Fin (n + 1)) : Away (polyGrading k n) (MvPolynomial.X i) :=
  Away.mk (polyGrading k n) (X_mem_one k n i) 1 (MvPolynomial.X j) (X_mem_smul k n j)

/-- For `j ≠ i` the fraction `T_j / T_i` is the affine coordinate of the chart. -/
theorem coordFracAt_eq_chartCoord (i : Fin (n + 1)) (j : {j : Fin (n + 1) // j ≠ i}) :
    coordFracAt k n i j.1 = chartCoord k n i j := rfl

/-- The integral fraction `T_j / T_i`. -/
theorem coordFrac_eq_coordFracAt (i j : Fin (n + 1)) :
    Stacks.TwistPullbackPinned.coordFrac.{u} i j = coordFracAt (ULift.{u} ℤ) n i j := rfl

/-- Coefficient change carries `T_j / T_i` to `T_j / T_i`. -/
theorem chartBaseChange_coordFracAt (i j : Fin (n + 1)) :
    chartBaseChange (ULift.{u} ℤ) n (integralCoeffHom k) i (coordFracAt (ULift.{u} ℤ) n i j) =
      coordFracAt k n i j := by
  refine (chartBaseChange_mk (ULift.{u} ℤ) n (integralCoeffHom k) i 1 (MvPolynomial.X j)
    (X_mem_smul (ULift.{u} ℤ) n j) (by simpa using X_mem_smul k n j)).trans ?_
  rw [HomogeneousLocalization.ext_iff_val, coordFracAt]
  simp

/-- Coefficient change carries the integral fraction `T_j / T_i` to `T_j / T_i`. -/
theorem chartBaseChange_coordFrac (i j : Fin (n + 1)) :
    chartBaseChange (ULift.{u} ℤ) n (integralCoeffHom k) i
        (Stacks.TwistPullbackPinned.coordFrac.{u} i j) = coordFracAt k n i j :=
  chartBaseChange_coordFracAt k n i j

/-- The projection to the integral model pulls `D₊(Tᵢ)` back to `D₊(Tᵢ)`. -/
theorem coordinateProjMap_preimage_basicOpen (i : Fin (n + 1)) :
    coordinateProjMap k n (integralGradedHom k n) (mapDomain_integralGradedHom_eq_top k n) ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i) =
      AlgebraicGeometry.Proj.basicOpen (polyGrading k n) (MvPolynomial.X i) := by
  rw [coordinateProjMap_eq_projMap, AlgebraicGeometry.Proj.map_preimage_basicOpen]
  congr 1
  simp

/-- The chart square of the projection to the integral model, read on sections. -/
theorem appLE_awayToSection_coordinateProjMap (i : Fin (n + 1))
    (e : AlgebraicGeometry.Proj.basicOpen (polyGrading k n) (MvPolynomial.X i) ≤
      coordinateProjMap k n (integralGradedHom k n)
          (mapDomain_integralGradedHom_eq_top k n) ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i))
    (z : Away (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i)) :
    (coordinateProjMap k n (integralGradedHom k n)
          (mapDomain_integralGradedHom_eq_top k n)).appLE
        (AlgebraicGeometry.Proj.basicOpen (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i))
        (AlgebraicGeometry.Proj.basicOpen (polyGrading k n) (MvPolynomial.X i)) e
        ((AlgebraicGeometry.Proj.awayToSection (polyGrading (ULift.{u} ℤ) n)
          (MvPolynomial.X i)).hom z) =
      (AlgebraicGeometry.Proj.awayToSection (polyGrading k n) (MvPolynomial.X i)).hom
        (chartBaseChange (ULift.{u} ℤ) n (integralCoeffHom k) i z) := by
  have e' : AlgebraicGeometry.Proj.basicOpen (polyGrading k n) (MvPolynomial.X i) ≤
      AlgebraicGeometry.Proj.map (integralGradedHom k n)
          (irrelevant_le_map_integralGradedHom k n) ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i) := by
    rw [← coordinateProjMap_eq_projMap]
    exact e
  rw [Stacks.TwistPullbackPinned.appLE_congr_hom (coordinateProjMap_eq_projMap k n) _ _ e e']
  exact appLE_awayToSection_projMap (polyGrading (ULift.{u} ℤ) n) (polyGrading k n)
    (integralGradedHom k n) (irrelevant_le_map_integralGradedHom k n)
    (X_mem_one (ULift.{u} ℤ) n i) (X_mem_one k n i) (by simp)
    (chartBaseChange (ULift.{u} ℤ) n (integralCoeffHom k) i)
    (fun m a ha ha' => chartBaseChange_mk (ULift.{u} ℤ) n (integralCoeffHom k) i m a ha ha')
    e' z

/-- **The structure morphism of `Proj k[T₀, …, Tₙ]` on the standard chart `D₊(Tᵢ)`**, read
through the identification of the chart with the spectrum of its coordinate ring. -/
theorem basicOpen_ι_comp_projToSpecCoeff (i : Fin (n + 1)) :
    (AlgebraicGeometry.Proj.basicOpen (polyGrading k n) (MvPolynomial.X i)).ι ≫
        projToSpecCoeff k n =
      (AlgebraicGeometry.Proj.basicOpenIsoSpec (polyGrading k n) (MvPolynomial.X i)
          (X_mem_one k n i) Nat.one_pos).hom ≫
        Spec.map (CommRingCat.ofHom (coeffToAway k n i)) := by
  rw [← awayι_comp_projToSpecCoeff k n i,
    ← AlgebraicGeometry.Proj.basicOpenIsoSpec_inv_ι (polyGrading k n) (MvPolynomial.X i)
      (X_mem_one k n i) Nat.one_pos,
    ← Category.assoc, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- **On the standard chart the structure morphism of `Proj k[T₀, …, Tₙ]` is the coefficient
inclusion `k → k[T]_{(Tᵢ)}`**, read on sections. -/
theorem appLE_coeffToAway_projToSpecCoeff (i : Fin (n + 1))
    (e : AlgebraicGeometry.Proj.basicOpen (polyGrading k n) (MvPolynomial.X i) ≤
      projToSpecCoeff k n ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of k)).Opens)) (r : k) :
    (projToSpecCoeff k n).appLE ⊤
        (AlgebraicGeometry.Proj.basicOpen (polyGrading k n) (MvPolynomial.X i)) e
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r) =
      (AlgebraicGeometry.Proj.awayToSection (polyGrading k n) (MvPolynomial.X i)).hom
        (coeffToAway k n i r) := by
  refine Stacks.TwistPullbackPinned.topIso_inv_injective _ ?_
  rw [← CategoryTheory.ConcreteCategory.comp_apply,
    Stacks.TwistPullbackPinned.appLE_comp_topIso_inv, appLE_top_top,
    basicOpen_ι_comp_projToSpecCoeff k n i, Scheme.Hom.comp_appTop,
    CategoryTheory.ConcreteCategory.comp_apply]
  have hnat := CategoryTheory.ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (coeffToAway k n i))) r
  rw [CategoryTheory.ConcreteCategory.comp_apply,
    CategoryTheory.ConcreteCategory.comp_apply] at hnat
  rw [← hnat]
  have hβ : (AlgebraicGeometry.Proj.basicOpenIsoSpec (polyGrading k n) (MvPolynomial.X i)
        (X_mem_one k n i) Nat.one_pos).hom.appTop =
      (Scheme.ΓSpecIso (CommRingCat.of (Away (polyGrading k n) (MvPolynomial.X i)))).hom ≫
        AlgebraicGeometry.Proj.awayToSection (polyGrading k n) (MvPolynomial.X i) ≫
          (AlgebraicGeometry.Proj.basicOpen (polyGrading k n) (MvPolynomial.X i)).topIso.inv := by
    rw [AlgebraicGeometry.Proj.basicOpenIsoSpec_hom]
    exact AlgebraicGeometry.Proj.basicOpenToSpec_app_top _ _
  rw [hβ, CategoryTheory.ConcreteCategory.comp_apply,
    CategoryTheory.ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
  rfl

end Coefficients

section Chart

open Stacks.AlgebraicGeometry.ProjBaseChange

variable {k : Type u} [CommRing k] {n : ℕ} {X : Scheme.{u}} {L : X.Modules}
  [Stacks.Ample.IsInvertibleModule X L] (s : Fin (n + 1) → Γ(L, ⊤))
  (hs : Stacks.ProjectiveFromSections.GeneratesStalks s) (f : X ⟶ Spec (CommRingCat.of k))

/-- The morphism to the polynomial model of `ℙⁿ_k`. -/
def toPolynomialModel : X ⟶ AlgebraicGeometry.Proj (polyGrading k n) :=
  Stacks.ProjectiveFromSections.toProjectiveSpaceOver s hs f ≫
    (polynomialComparison k n).iso.hom

/-- The comparison isomorphism commutes with the projection to the integral model, spelled with
the canonical coefficient homomorphism. -/
theorem polynomialComparison_iso_hom_comp_coordinateProjMap (k : Type u) [CommRing k] (n : ℕ) :
    (polynomialComparison k n).iso.hom ≫ coordinateProjMap k n (integralGradedHom k n)
        (mapDomain_integralGradedHom_eq_top k n) =
      AlgebraicGeometry.projectiveSpaceOver.toIntegralAtUniverse n (Spec (CommRingCat.of k)) :=
  (polynomialComparison k n).toIntegral

/-- Read on the integral model, the morphism to the polynomial model is the glued morphism. -/
theorem toPolynomialModel_comp_coordinateProjMap :
    toPolynomialModel s hs f ≫ coordinateProjMap k n (integralGradedHom k n)
        (mapDomain_integralGradedHom_eq_top k n) =
      Stacks.ProjectiveFromSections.toProjectiveSpaceAtUniverse s hs := by
  rw [toPolynomialModel, Category.assoc,
    polynomialComparison_iso_hom_comp_coordinateProjMap k n,
    Stacks.ProjectiveFromSections.toProjectiveSpaceOver_snd]

/-- The `i`-th chart of `X` maps into the `i`-th standard chart of the polynomial model. -/
theorem nvCover_le_preimage_basicOpen_toPolynomialModel (i : Fin (n + 1)) :
    Stacks.ProjectiveFromSections.nvCover s i ≤ toPolynomialModel s hs f ⁻¹ᵁ
      AlgebraicGeometry.Proj.basicOpen (polyGrading k n) (MvPolynomial.X i) := by
  have h := Stacks.TwistPullbackPinned.nvCover_le_preimage_basicOpen s
    (Stacks.ProjectiveFromSections.toProjectiveSpaceAtUniverse s hs) i
    (Stacks.ProjectiveFromSections.ι_toProjectiveSpaceAtUniverse s hs i)
  rw [← toPolynomialModel_comp_coordinateProjMap s hs f, Scheme.Hom.comp_preimage,
    coordinateProjMap_preimage_basicOpen k n i] at h
  exact h

/-- Restricting along a factorization `φ ≫ c = g` composes the two `appLE` maps. -/
private theorem appLE_comp_appLE_apply_of_comp_eq {X Y Z : Scheme.{u}} {φ : X ⟶ Y} {c : Y ⟶ Z}
    {g : X ⟶ Z} (h : φ ≫ c = g) {U : Z.Opens} {V : Y.Opens} {W : X.Opens}
    (e₁ : V ≤ c ⁻¹ᵁ U) (e₂ : W ≤ φ ⁻¹ᵁ V) (e₀ : W ≤ g ⁻¹ᵁ U) (z : Γ(Z, U)) :
    φ.appLE V W e₂ (c.appLE U V e₁ z) = g.appLE U W e₀ z := by
  rw [← CategoryTheory.ConcreteCategory.comp_apply, Scheme.Hom.appLE_comp_appLE]
  exact CategoryTheory.ConcreteCategory.congr_hom
    (Stacks.TwistPullbackPinned.appLE_congr_hom h _ _ _ _) z

/-- **The pullback of the affine coordinate `T_j / T_i` along the morphism of a generating
family is the ratio `s_j / s_i`.** -/
theorem appLE_coordFracAt_chart (i j : Fin (n + 1)) :
    (toPolynomialModel s hs f).appLE
        (AlgebraicGeometry.Proj.basicOpen (polyGrading k n) (MvPolynomial.X i))
        (Stacks.ProjectiveFromSections.nvCover s i)
        (nvCover_le_preimage_basicOpen_toPolynomialModel s hs f i)
        ((AlgebraicGeometry.Proj.awayToSection (polyGrading k n) (MvPolynomial.X i)).hom
          (coordFracAt k n i j)) =
      Stacks.ProjectiveFromSections.ratio s i j := by
  have e₀ := Stacks.TwistPullbackPinned.nvCover_le_preimage_basicOpen s
    (Stacks.ProjectiveFromSections.toProjectiveSpaceAtUniverse s hs) i
    (Stacks.ProjectiveFromSections.ι_toProjectiveSpaceAtUniverse s hs i)
  have e₁ := (coordinateProjMap_preimage_basicOpen k n i).ge
  rw [← chartBaseChange_coordFrac k n i j, ← appLE_awayToSection_coordinateProjMap k n i e₁,
    appLE_comp_appLE_apply_of_comp_eq (toPolynomialModel_comp_coordinateProjMap s hs f) _ _ e₀]
  exact Stacks.TwistPullbackPinned.appLE_coordFrac_chart s _ i j
    (Stacks.ProjectiveFromSections.ι_toProjectiveSpaceAtUniverse s hs i)

/-- The comparison isomorphism commutes with the structure morphism to `Spec k`, spelled with
`Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff`. -/
theorem polynomialComparison_iso_hom_comp_projToSpecCoeff (k : Type u) [CommRing k] (n : ℕ) :
    (polynomialComparison k n).iso.hom ≫ projToSpecCoeff k n =
      pullback.fst (terminal.from (Spec (CommRingCat.of k)))
        (terminal.from (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} n)) :=
  (polynomialComparison k n).toBase

/-- **`φ` is a morphism over `Spec k`**, read in the polynomial model. -/
theorem toPolynomialModel_comp_projToSpecCoeff :
    toPolynomialModel s hs f ≫ projToSpecCoeff k n = f := by
  rw [toPolynomialModel, Category.assoc,
    polynomialComparison_iso_hom_comp_projToSpecCoeff k n]
  exact Stacks.ProjectiveFromSections.toProjectiveSpaceOver_fst s hs f

/-- **`φ` pulls a constant back to the constant**: on the chart `X_{sᵢ}` the composite of `φ`
with the coefficient inclusion `k → k[T]_{(Tᵢ)}` is the structure morphism of `X` over `k`. -/
theorem appLE_coeffToAway_chart (i : Fin (n + 1)) (r : k) :
    (toPolynomialModel s hs f).appLE
        (AlgebraicGeometry.Proj.basicOpen (polyGrading k n) (MvPolynomial.X i))
        (Stacks.ProjectiveFromSections.nvCover s i)
        (nvCover_le_preimage_basicOpen_toPolynomialModel s hs f i)
        ((AlgebraicGeometry.Proj.awayToSection (polyGrading k n) (MvPolynomial.X i)).hom
          (coeffToAway k n i r)) =
      f.appLE ⊤ (Stacks.ProjectiveFromSections.nvCover s i) le_top
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r) := by
  rw [← appLE_coeffToAway_projToSpecCoeff k n i le_top r]
  exact appLE_comp_appLE_apply_of_comp_eq (toPolynomialModel_comp_projToSpecCoeff s hs f)
    le_top _ _ _

/-- **The `k`-algebra structure of the chart `X_{sᵢ}` through `φ`**: the structure morphism of
`X` over `k`, restricted to the chart. -/
def chartBaseHom (i : Fin (n + 1)) :
    k →+* Γ(X, Stacks.ProjectiveFromSections.nvCover s i) :=
  (CategoryTheory.ConcreteCategory.hom
      (f.appLE ⊤ (Stacks.ProjectiveFromSections.nvCover s i) le_top)).comp
    (CategoryTheory.ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of k)).inv)

/-- **The chart of `φ`**: the composite of the identification of the standard chart `D₊(Tᵢ)` of
`ℙⁿ_k` with `Spec k[Y_j : j ≠ i]` and the pullback along `φ`, as a ring homomorphism
`k[Y_j : j ≠ i] → Γ(X, X_{sᵢ})`. -/
def chartPullback (i : Fin (n + 1)) :
    MvPolynomial {j : Fin (n + 1) // j ≠ i} k →+*
      Γ(X, Stacks.ProjectiveFromSections.nvCover s i) :=
  RingHom.comp
    (RingHom.comp
      ((toPolynomialModel s hs f).appLE
          (AlgebraicGeometry.Proj.basicOpen (polyGrading k n) (MvPolynomial.X i))
          (Stacks.ProjectiveFromSections.nvCover s i)
          (nvCover_le_preimage_basicOpen_toPolynomialModel s hs f i)).hom
      (AlgebraicGeometry.Proj.awayToSection (polyGrading k n) (MvPolynomial.X i)).hom)
    (Stacks.AlgebraicGeometry.ProjPolyChart.chartHom k n i)

/-- `Stacks.ProjectiveSpaceChartRatio.chartPullback` spelled through the chart isomorphism
`Stacks.AlgebraicGeometry.ProjPolyChart.chartEquiv`, which is the identification of the standard
open `D₊(Tᵢ)` of `ℙⁿ_k` with `Spec k[Y_j : j ≠ i]`. -/
theorem chartPullback_apply (i : Fin (n + 1)) (p : MvPolynomial {j : Fin (n + 1) // j ≠ i} k) :
    chartPullback s hs f i p =
      (toPolynomialModel s hs f).appLE
        (AlgebraicGeometry.Proj.basicOpen (polyGrading k n) (MvPolynomial.X i))
        (Stacks.ProjectiveFromSections.nvCover s i)
        (nvCover_le_preimage_basicOpen_toPolynomialModel s hs f i)
        ((AlgebraicGeometry.Proj.awayToSection (polyGrading k n) (MvPolynomial.X i)).hom
          (Stacks.AlgebraicGeometry.ProjPolyChart.chartEquiv k n i p)) := rfl

/-- **The standard chart of `ℙⁿ_k` through `φ_{(ℒ, (s₀, …, sₙ))}` is the `k`-algebra map sending
`Y_j` to the ratio `s_j / s_i`.**

This is the field analogue of `Stacks.TwistPullbackPinned.appLE_coordFrac_chart`, which states
the same for the integral model `ℙⁿ_ℤ`. -/
theorem chartPullback_eq (i : Fin (n + 1)) :
    chartPullback s hs f i =
      MvPolynomial.eval₂Hom (chartBaseHom s f i)
        (fun j : {j : Fin (n + 1) // j ≠ i} => Stacks.ProjectiveFromSections.ratio s i j.1) := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
  · rw [chartPullback, RingHom.comp_apply, RingHom.comp_apply,
      Stacks.AlgebraicGeometry.ProjPolyChart.chartHom_C, MvPolynomial.eval₂Hom_C]
    exact appLE_coeffToAway_chart s hs f i r
  · rw [chartPullback, RingHom.comp_apply, RingHom.comp_apply,
      Stacks.AlgebraicGeometry.ProjPolyChart.chartHom_X, MvPolynomial.eval₂Hom_X',
      ← coordFracAt_eq_chartCoord k n i j]
    exact appLE_coordFracAt_chart s hs f i j.1

/-- **The morphism `φ_{ℒ,ψ} : X ⟶ 𝐏(V)` of [Stacks, Tag 0FCY], read in the polynomial model.**
A basis of `V` identifies `𝐏(V)` with `ℙⁿ_k`, and `φ_{ℒ,ψ}` read through that identification is
the morphism of this file, so `Stacks.ProjectiveSpaceChartRatio.chartPullback_eq` computes its
standard charts as well. -/
theorem toProjectiveSpaceOfModule_comp_eq_toPolynomialModel {V : Type u} [AddCommGroup V]
    [Module k V] (b : Module.Basis (Fin (n + 1)) k V) :
    AlgebraicGeometry.toProjectiveSpaceOfModule b s hs f ≫
        (AlgebraicGeometry.basisProjectiveSpaceIso b).inv ≫
        (polynomialComparison k n).iso.hom = toPolynomialModel s hs f := by
  rw [toPolynomialModel, ← Category.assoc,
    AlgebraicGeometry.toProjectiveSpaceOfModule_comp_basisProjectiveSpaceIso_inv]

end Chart

end Stacks.ProjectiveSpaceChartRatio

end
