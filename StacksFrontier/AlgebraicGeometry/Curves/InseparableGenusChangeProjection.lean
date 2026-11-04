module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveLineDivisorDegree.Chart
public import StacksFrontier.AlgebraicGeometry.Curves.InseparableGenusChangeExample
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The projection of [Stacks, Tag 0CD1] over `Spec k`, and the function field of `𝐏¹_k`

`StacksFrontier/AlgebraicGeometry/Curves/InseparableGenusChangeExample.lean` constructs the
coordinate projection `f : Z ⟶ 𝐏¹_k` of the example of [Stacks, Tag 0CD1] and pins it down by
the inverse images of the standard opens. Two things that file leaves open are supplied here:
that `f` is a morphism **over `Spec k`**, and the identification of the function field of
`𝐏¹_k = Proj k[S₀, S₁]` with `RatFunc k`, which is the base of the extension of function fields
the example is about.

## Main definitions

* `Stacks.Curves.InseparableGenus.lineChart`: the standard chart `Spec k[T] ⟶ 𝐏¹_k` at `D₊(S₀)`,
  an open immersion whose coordinate `T` is the ratio `S₁ / S₀`.
* `Stacks.Curves.InseparableGenus.projectiveLineFunctionFieldEquiv`: **the function field of
  `𝐏¹_k` is `k(x)`** — the identification of `(Proj k[S₀, S₁]).functionField` with `RatFunc k`
  given by that chart.

## Main results

* `Stacks.Curves.InseparableGenus.mapHom_comp_projToSpecCoeff`: a graded homomorphism of
  polynomial rings which fixes the constants induces, on its domain of definition, a morphism of
  projective spectra **over the coefficient ring**.
* `Stacks.Curves.InseparableGenus.exists_coordProj_hom_over_specCoeff`: the coordinate projection
  `f : Z ⟶ 𝐏¹_k` of the example **is a morphism over `Spec k`**, on top of being pinned down by
  the inverse images of the standard opens.
* `Stacks.Curves.InseparableGenus.lineChartRingEquiv_X` and
  `Stacks.Curves.InseparableGenus.dominantFunctionFieldMap_projectiveLineFunctionFieldEquiv_symm`:
  the identification is the one which calls the ratio `S₁ / S₀` the coordinate `x`.

## Implementation notes

**Over `Spec k`.** The morphism of the example is
`Stacks.AlgebraicGeometry.ProjTwistChain.mapHom` of the substitution `Sⱼ ↦ Tⱼ`, restricted along
the curve, so the compatibility to prove is the one between `mapHom` and
`Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff`. Both sides are compared on the standard
opens `D₊(ψ g)` that cover the domain of definition, by
`Stacks.AlgebraicGeometry.ProjTwistChain.mapDomain_hom_ext`: there `mapHom` is `Spec` of the map
`A_{(g)} → B_{(ψ g)}` of degree-zero localizations, each structure morphism is `Spec` of the
inclusion of the coefficient ring into one of those localizations, and the identity that remains
is that `ψ` carries a constant to that constant. So the geometric statement reduces to
`MvPolynomial.rename_C`, which is what `coordProjGradedHom_C` records.

The computation of the structure morphism on a chart is
`Stacks.AlgebraicGeometry.ProjBaseChange.awayι_comp_projToSpecCoeff` for the chart of a *variable*;
`awayι_comp_projToSpecCoeff_elem` is the same statement for an arbitrary homogeneous element of
positive degree, which is what the cover of the domain of definition supplies, and its proof is
the same.

**The function field.** `Stacks.Chow.chartFunctionFieldEquiv` computes the function field of an
integral, locally Noetherian scheme carrying a dominant open immersion from `Spec k[T]`; all that
is needed is such a chart on `Proj k[S₀, S₁]`. It is the standard open `D₊(S₀)`, whose chart ring
is a polynomial ring in one variable by `Stacks.ProjectiveChart.chartRingEquiv`, read through
`MvPolynomial.uniqueAlgEquiv` to pass from a one-element index type to `Polynomial`. The chart is
dominant because `Proj` of a polynomial ring over a domain is irreducible
(`Stacks.AlgebraicGeometry.ProjPolyChart.isIntegral_proj`). Local Noetherianness is
`isLocallyNoetherian_proj`, read off the standard affine cover and
`Stacks.ProjectiveChart.isNoetherianRing_sections`; it is a statement about `Proj` of a polynomial
ring in general and is proved here only because its natural home,
`StacksFrontier/AlgebraicGeometry/ProjPolyChart/Cover.lean`, is imported by a dozen files.

## Not done here

The identification of the *extension* of function fields.
`Stacks.Curves.InseparableGenus.curveFunctionField` is the extension `k(x) ⊆ k(x)(y)`,
`y³ = x² + a`, and `projectiveLineFunctionFieldEquiv` identifies its base with the function field
of `𝐏¹_k`; that the embedding of `k(x)` the projection induces on function fields is the one that
calls `x` the coordinate `T₁/T₀` takes three further things, all elsewhere:

* `Z.functionField` computed as `curveFunctionField k a` — the fraction field of the chart
  `k[Y₀, Y₁] ⧸ (Y₀² - Y₁³ + a)` of the curve on `D₊(T₀)` — is
  `Stacks.Curves.InseparableGenus.functionFieldEquivCurveFunctionField`, in
  `StacksFrontier/AlgebraicGeometry/Curves/InseparableGenusChangeFunctionField.lean`;
* dominance of the projection is
  `Stacks.Curves.InseparableGenus.isDominant_planeCubicProjection`, in
  `StacksFrontier/AlgebraicGeometry/Curves/InseparableGenusChangeDominant.lean`, which also names
  the projection and the embedding of `k(x)` it induces;
* the equation `Stacks.Curves.InseparableGenus.projectionRatFuncAlgebra =
  Stacks.Curves.InseparableGenus.chartRatFuncAlgebra` itself, which reads `f` on the sections of
  that chart, is
  `Stacks.Curves.InseparableGenus.projectionRatFuncAlgebra_eq_chartRatFuncAlgebra`, in
  `StacksFrontier/AlgebraicGeometry/Curves/InseparableGenusChangeProjectionEmbedding.lean`.

## References

* [Stacks Project, Tag 0CD1](https://stacks.math.columbia.edu/tag/0CD1)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01NG](https://stacks.math.columbia.edu/tag/01NG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open AlgebraicGeometry.ProjectiveSpectrum.Proj (idealOfClosedSubscheme)
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading X_mem_one projToSpecCoeff)
open Stacks.AlgebraicGeometry.ProjShared (mapDomain)
open Stacks.AlgebraicGeometry.ProjTwistChain (mapHom mapAwayHom mapDomain_hom_ext mem_of_mem
  homOfLE_mapHom_assoc basicOpen_le_mapDomain mapHom_preimage_basicOpen)

universe u

namespace Stacks.Curves.InseparableGenus

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### The coefficient ring inside a chart of `Proj` of a polynomial ring -/

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The coefficient ring maps into the degree-zero localization at a homogeneous element, as the
composite of the identification of the coefficient ring with the degree-zero part and the
structure map of the localization. This is
`Stacks.AlgebraicGeometry.ProjPolyChart.coeffToAway` with an arbitrary element in place of a
variable. -/
def coeffToAwayElem (f : MvPolynomial (Fin (n + 1)) R) :
    R →+* Away (polyGrading R n) f :=
  (algebraMap (polyGrading R n 0) (Away (polyGrading R n) f)).comp
    (algebraMap R (polyGrading R n 0))

/-- A constant is homogeneous of degree `0 • d`, the shape `HomogeneousLocalization.Away.mk` asks
for with denominator exponent zero. -/
theorem C_mem_zero_smul (d : ℕ) (r : R) :
    (MvPolynomial.C r : MvPolynomial (Fin (n + 1)) R) ∈ polyGrading R n (0 • d) := by
  simp

/-- On the coefficient ring the chart map is the fraction with denominator `f⁰`. -/
theorem coeffToAwayElem_eq_mk {d : ℕ} {f : MvPolynomial (Fin (n + 1)) R}
    (hf : f ∈ polyGrading R n d) (r : R) :
    coeffToAwayElem R n f r =
      Away.mk (polyGrading R n) hf 0 (MvPolynomial.C r) (C_mem_zero_smul R n d r) := by
  rw [HomogeneousLocalization.ext_iff_val, Away.val_mk]
  have hc : ((algebraMap R (polyGrading R n 0)) r : MvPolynomial (Fin (n + 1)) R) =
      MvPolynomial.C r := by
    rw [SetLike.GradeZero.coe_algebraMap]; simp [MvPolynomial.algebraMap_eq]
  simp only [coeffToAwayElem, RingHom.comp_apply, HomogeneousLocalization.algebraMap_eq]
  rw [show (HomogeneousLocalization.fromZeroRingHom (polyGrading R n)
      (Submonoid.powers f) ((algebraMap R (polyGrading R n 0)) r)).val =
      Localization.mk ((algebraMap R (polyGrading R n 0)) r : MvPolynomial (Fin (n + 1)) R) 1
      from rfl, hc]
  congr 1

/-- **The structure morphism of `Proj R[T₀, …, Tₙ]` on the standard open of a homogeneous element
of positive degree.** It is `Spec` of the inclusion of the coefficient ring. -/
theorem awayι_comp_projToSpecCoeff_elem {d : ℕ} (hd : 0 < d)
    {f : MvPolynomial (Fin (n + 1)) R} (hf : f ∈ polyGrading R n d) :
    AlgebraicGeometry.Proj.awayι (polyGrading R n) f hf hd ≫ projToSpecCoeff R n =
      Spec.map (CommRingCat.ofHom (coeffToAwayElem R n f)) := by
  have hz : ∀ r : R, (GradedRing.projZeroRingHom' (polyGrading R n))
      (algebraMap R (MvPolynomial (Fin (n + 1)) R) r) = algebraMap R (polyGrading R n 0) r :=
    fun r => by
      have h := GradedRing.projZeroRingHom'_apply_coe (polyGrading R n)
        (algebraMap R (polyGrading R n 0) r)
      rwa [SetLike.GradeZero.coe_algebraMap] at h
  have key : (HomogeneousLocalization.fromZeroRingHom (polyGrading R n)
        (Submonoid.powers f)).comp
        ((GradedRing.projZeroRingHom' (polyGrading R n)).comp
          (algebraMap R (MvPolynomial (Fin (n + 1)) R))) = coeffToAwayElem R n f := by
    refine RingHom.ext fun r => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, hz r, coeffToAwayElem, RingHom.comp_apply]
    rfl
  rw [Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff, ← Category.assoc,
    AlgebraicGeometry.Proj.awayι_toSpecZero, ← Spec.map_comp, ← CommRingCat.ofHom_comp, key]

/-! ### A graded homomorphism fixing the constants is a morphism over the coefficient ring -/

variable {R n}

/-- A graded homomorphism of polynomial rings which fixes the constants commutes with the
inclusions of the coefficient ring into the degree-zero localizations. -/
theorem map_coeffToAwayElem {m n : ℕ} (ψ : polyGrading R m →+*ᵍ polyGrading R n)
    (hψ : ∀ r : R, ψ (MvPolynomial.C r) = MvPolynomial.C r) {d : ℕ}
    {f : MvPolynomial (Fin (m + 1)) R} (hf : f ∈ polyGrading R m d) :
    (Away.map ψ f).comp (coeffToAwayElem R m f) = coeffToAwayElem R n (ψ f) := by
  refine RingHom.ext fun r => ?_
  rw [RingHom.comp_apply, coeffToAwayElem_eq_mk R m hf, Away.map_mk,
    HomogeneousLocalization.ext_iff_val, Away.val_mk,
    coeffToAwayElem_eq_mk R n (mem_of_mem _ _ ψ hf), Away.val_mk, hψ]

/-- **A graded homomorphism of polynomial rings which fixes the constants induces a morphism over
the coefficient ring.** On the standard open of a homogeneous element of positive degree both
sides are `Spec` of a map of degree-zero localizations, and the two agree because a constant goes
to that constant. -/
@[ega "II 2.8.5" "special case"]
theorem mapHom_comp_projToSpecCoeff {m n : ℕ} (ψ : polyGrading R m →+*ᵍ polyGrading R n)
    (hψ : ∀ r : R, ψ (MvPolynomial.C r) = MvPolynomial.C r) :
    mapHom (polyGrading R m) (polyGrading R n) ψ ≫ projToSpecCoeff R m =
      (mapDomain (polyGrading R m) (polyGrading R n) ψ).ι ≫ projToSpecCoeff R n := by
  refine mapDomain_hom_ext _ _ ψ _ _ fun d hd f hf => ?_
  have hψf : (ψ f : MvPolynomial (Fin (n + 1)) R) ∈ polyGrading R n d := ψ.map_mem hf
  have hι : (AlgebraicGeometry.Proj.basicOpen (polyGrading R n) (ψ f)).ι =
      AlgebraicGeometry.Proj.basicOpenToSpec (polyGrading R n) (ψ f) ≫
        AlgebraicGeometry.Proj.awayι (polyGrading R n) (ψ f) hψf hd := by
    rw [AlgebraicGeometry.Proj.awayι,
      ← AlgebraicGeometry.Proj.basicOpenIsoSpec_hom (polyGrading R n) (ψ f) hψf hd,
      Iso.hom_inv_id_assoc]
  have hma : mapAwayHom (polyGrading R m) (polyGrading R n) ψ hd hf =
      AlgebraicGeometry.Proj.basicOpenToSpec (polyGrading R n) (ψ f) ≫
        Spec.map (CommRingCat.ofHom (Away.map ψ f)) ≫
          AlgebraicGeometry.Proj.awayι (polyGrading R m) f hf hd := rfl
  rw [homOfLE_mapHom_assoc (polyGrading R m) (polyGrading R n) ψ hd hf,
    Scheme.homOfLE_ι_assoc, hι, Category.assoc,
    awayι_comp_projToSpecCoeff_elem R n hd hψf, hma, Category.assoc, Category.assoc,
    awayι_comp_projToSpecCoeff_elem R m hd hf, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    map_coeffToAwayElem ψ hψ hf]

/-! ### The projection of Tag 0CD1 is a morphism over `Spec k` -/

/-- The coordinate projection `Sⱼ ↦ Tⱼ` fixes the constants. -/
theorem coordProjGradedHom_C (k : Type u) [CommRing k] (r : k) :
    coordProjGradedHom k (MvPolynomial.C r) = MvPolynomial.C r := by
  show coordProjHom k (MvPolynomial.C r) = MvPolynomial.C r
  simp [coordProjHom]

/-- **The morphism `f : Z ⟶ 𝐏¹_k` of [Stacks, Tag 0CD1] is a morphism over `Spec k`**, as well as
being the coordinate projection `(T₀ : T₁ : T₂) ↦ (T₀ : T₁)`.

The morphism is the one of `Stacks.Curves.InseparableGenus.exists_coordProj_hom`; what is added
here is the second conjunct, the compatibility with the two structure morphisms. It holds because
the substitution `Sⱼ ↦ Tⱼ` fixes the constants, so `mapHom_comp_projToSpecCoeff` applies, and
restricting along the lift of the curve into the domain of definition changes neither side. -/
theorem exists_coordProj_hom_over_specCoeff {k : Type u} [Field k] (a : k) {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 3) k)) [IsClosedImmersion i]
    (hI : idealOfClosedSubscheme (MvPolynomial.homogeneousSubmodule (Fin 3) k) i =
      Ideal.span {planeCubic k a}) :
    ∃ f : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k),
      (∀ (G : MvPolynomial (Fin 2) k) (d : ℕ),
        G ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k d → 0 < d →
        f ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
            (MvPolynomial.homogeneousSubmodule (Fin 2) k) G =
          i ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
            (MvPolynomial.homogeneousSubmodule (Fin 3) k) (coordProjHom k G)) ∧
      f ≫ projToSpecCoeff k 1 = i ≫ projToSpecCoeff k 2 := by
  set U := mapDomain (MvPolynomial.homogeneousSubmodule (Fin 2) k)
    (MvPolynomial.homogeneousSubmodule (Fin 3) k) (coordProjGradedHom k) with hU
  have hrange : Set.range i.base ⊆ Set.range U.ι.base := by
    rintro y ⟨x, rfl⟩
    refine ⟨⟨i.base x, ?_⟩, rfl⟩
    exact mem_mapDomain_coordProjGradedHom a (i.base x)
      (planeCubic_mem_asHomogeneousIdeal a i hI x)
  refine ⟨IsOpenImmersion.lift U.ι i hrange ≫ mapHom _ _ (coordProjGradedHom k),
    fun G d hG hd => ?_, ?_⟩
  · rw [Scheme.Hom.comp_preimage, mapHom_preimage_basicOpen _ _ _ G d hG hd,
      ← Scheme.Hom.comp_preimage, IsOpenImmersion.lift_fac]
    rfl
  · rw [Category.assoc,
      mapHom_comp_projToSpecCoeff (coordProjGradedHom k) (coordProjGradedHom_C k),
      ← Category.assoc, IsOpenImmersion.lift_fac]

/-! ### The function field of the projective line -/

/-- The chart ring of the standard open `D₊(S₀)` of `𝐏¹_R` is the one-variable polynomial ring,
with `T` the ratio `S₁ / S₀`. -/
def lineChartRingEquiv (R : Type u) [CommRing R] :
    Polynomial R ≃+* Stacks.ProjectiveChart.ChartRing R 1 0 :=
  (MvPolynomial.uniqueAlgEquiv R (Fin 1)).toRingEquiv.symm.trans
    (Stacks.ProjectiveChart.chartRingEquiv R 0)

/-- **The coordinate of the standard chart is the ratio `S₁ / S₀`.** The identification of the
chart ring of `D₊(S₀)` with `R[T]` carries `T` to `S₁ / S₀`, so the function field identification
built from it below is the one which calls `S₁ / S₀` the coordinate `x`. -/
theorem lineChartRingEquiv_X (R : Type u) [CommRing R] :
    lineChartRingEquiv R Polynomial.X = Stacks.ProjectiveChart.ratio R 0 1 := by
  have hd : (default : Fin 1) = 0 := rfl
  have h0 : (MvPolynomial.uniqueAlgEquiv R (Fin 1)).toRingEquiv.symm Polynomial.X
      = MvPolynomial.X (0 : Fin 1) := by
    simp [hd]
  have h1 : Stacks.ProjectiveChart.chartRingEquiv R (0 : Fin 2) (MvPolynomial.X (0 : Fin 1))
      = Stacks.ProjectiveChart.ratio R 0 1 := by
    rw [Stacks.ProjectiveChart.chartRingEquiv, RingEquiv.trans_apply,
      MvPolynomial.mapEquiv_apply, MvPolynomial.map_X]
    show Stacks.ProjectiveChart.chartHom R (0 : Fin 2) (MvPolynomial.X (0 : Fin 1)) = _
    rw [Stacks.ProjectiveChart.chartHom, MvPolynomial.aeval_X]
    rfl
  rw [lineChartRingEquiv, RingEquiv.trans_apply, h0, h1]

/-- The standard open `D₊(S₀)` of `𝐏¹_R` is the spectrum of a one-variable polynomial ring. -/
def lineChartIso (R : Type u) [CommRing R] :
    Spec (CommRingCat.of (Polynomial R)) ≅
      Spec (CommRingCat.of (Stacks.ProjectiveChart.ChartRing R 1 0)) :=
  Scheme.Spec.mapIso ((lineChartRingEquiv R).symm.toCommRingCatIso).op

/-- **The standard chart of `𝐏¹_k`**: the open immersion `Spec k[T] ⟶ 𝐏¹_k` onto `D₊(S₀)`, whose
coordinate `T` is the ratio `S₁ / S₀`. -/
def lineChart (k : Type u) [Field k] :
    Stacks.Chow.specPolynomial k ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k) :=
  (lineChartIso k).hom ≫
    AlgebraicGeometry.Proj.awayι (polyGrading k 1) (MvPolynomial.X 0) (X_mem_one k 1 0) Nat.one_pos

/-- The standard chart `Spec k[T] ⟶ 𝐏¹_k` is an open immersion. -/
instance isOpenImmersion_lineChart (k : Type u) [Field k] : IsOpenImmersion (lineChart k) := by
  have h : IsOpenImmersion ((lineChartIso k).hom ≫
      AlgebraicGeometry.Proj.awayι (polyGrading k 1) (MvPolynomial.X 0) (X_mem_one k 1 0)
        Nat.one_pos) := inferInstance
  exact h

/-- The standard chart `Spec k[T] ⟶ 𝐏¹_k` is dominant. -/
instance isDominant_lineChart (k : Type u) [Field k] : IsDominant (lineChart k) :=
  Stacks.Chow.isDominant_of_isOpenImmersion _

/-- **`Proj R[T₀, …, Tₙ]` is locally Noetherian when `R` is.** The standard opens cover it and
each has a polynomial ring as its ring of sections. -/
theorem isLocallyNoetherian_proj (R : Type u) [CommRing R] [IsNoetherianRing R] (n : ℕ) :
    IsLocallyNoetherian (Proj (polyGrading R n)) := by
  refine isLocallyNoetherian_of_affine_cover
    (S := fun i : Fin (n + 1) =>
      ⟨AlgebraicGeometry.Proj.basicOpen (polyGrading R n) (MvPolynomial.X i),
        AlgebraicGeometry.Proj.isAffineOpen_basicOpen _ _ (X_mem_one R n i) Nat.one_pos⟩)
    ?_ fun i => Stacks.ProjectiveChart.isNoetherianRing_sections i
  exact Stacks.AlgebraicGeometry.ProjPolyChart.iSup_basicOpen_X_eq_top R n

/-- **The function field of `𝐏¹_k` is the field `k(x)` of rational functions.** The standard open
`D₊(S₀)` is a dominant open immersion from `Spec k[T]`, so the function field of `𝐏¹_k` is that of
`Spec k[T]`, which is `RatFunc k`; the coordinate `T` is the ratio `S₁ / S₀`.

This is the base of the extension of function fields of [Stacks, Tag 0CD1]. -/
def projectiveLineFunctionFieldEquiv (k : Type u) [Field k] :
    (AlgebraicGeometry.Proj
      (MvPolynomial.homogeneousSubmodule (Fin 2) k)).functionField ≃+* RatFunc k :=
  haveI := isLocallyNoetherian_proj k 1
  Stacks.Chow.chartFunctionFieldEquiv k (lineChart k)

/-- A rational function read on `𝐏¹_k` through the identification restricts, on the standard
chart, to that rational function read on `Spec k[T]`. With `lineChartRingEquiv_X` this says that
the coordinate `x` of `RatFunc k` is the ratio `S₁ / S₀`. -/
theorem dominantFunctionFieldMap_projectiveLineFunctionFieldEquiv_symm (k : Type u) [Field k]
    (y : RatFunc k) :
    AlgebraicGeometry.dominantFunctionFieldMap (lineChart k)
        ((projectiveLineFunctionFieldEquiv k).symm y)
      = (Stacks.Chow.ratFuncEquivFunctionField k).symm y := by
  have := isLocallyNoetherian_proj k 1
  exact Stacks.Chow.dominantFunctionFieldMap_chartFunctionFieldEquiv_symm k (lineChart k) y

/-- The identification of the function field of `𝐏¹_k` with `RatFunc k` is: pull back along the
standard chart, then read the result as a rational function. -/
theorem projectiveLineFunctionFieldEquiv_apply (k : Type u) [Field k]
    (h : (AlgebraicGeometry.Proj
      (MvPolynomial.homogeneousSubmodule (Fin 2) k)).functionField) :
    projectiveLineFunctionFieldEquiv k h =
      Stacks.Chow.ratFuncEquivFunctionField k
        (AlgebraicGeometry.dominantFunctionFieldMap (lineChart k) h) := rfl

end Stacks.Curves.InseparableGenus

end
