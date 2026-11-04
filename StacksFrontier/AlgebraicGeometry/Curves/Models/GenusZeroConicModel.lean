module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.SplitConicGenericFibre

/-!
# The split conic as a model of the projective line

Let `R` be a discrete valuation ring with fraction field `K` and uniformizer `π`, and let
`X = V(T₁T₂ - πT₀²) ⊆ ℙ²_R`. Then `X` is a regular proper model of `ℙ¹_K`, its generic fibre being
identified with `ℙ¹_K` by the parametrization `[u : v] ↦ [uv : v² : πu²]`, and its two
projections `[T₀ : T₁]` and `[T₂ : T₀]` to `ℙ¹_R` are morphisms of models, to `ℙ¹_R` with the
canonical identification of its generic fibre and with that identification twisted by the
scaling `[u : v] ↦ [πu : v]`.

## Main definitions

* `Stacks.Models.GenusZero.conicGenericFibreIso`: the identification of the generic fibre of `X`
  with `ℙ¹_K`.

## Main results

* `Stacks.Models.GenusZero.isModel_conic`: `X` is a model of `ℙ¹_K`.
* `Stacks.Models.GenusZero.isModelHom_firstProjection` and
  `Stacks.Models.GenusZero.isModelHom_secondProjection`: the projections are morphisms of models.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial HomogeneousLocalization

universe u

namespace Stacks.Models.GenusZero

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every homomorphism out of the homogeneous coordinate ring of the conic is the evaluation at the
images of the coordinates. -/
theorem eq_conicHom {R : Type u} [CommRing R] (a : R) {L : Type u} [CommRing L]
    (χ : MvPolynomial (Fin 3) R ⧸ conicIdeal a →+* L) :
    χ = conicHom a (χ.comp ((Ideal.Quotient.mk (conicIdeal a)).comp C))
      (fun k => χ (conicCoord a k))
      (by rw [← map_mul, ← map_pow, conic_relation, map_mul, map_pow]; rfl) := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => ?_) (fun k => ?_)) <;>
    simp [conicHom_mk]

/-! ### The scaling on points -/

section Scaling

open Stacks.AlgebraicGeometry.ProjBaseChange

variable {K : Type u} [Field K]

/-- Two morphisms into `ℙ¹` over a base scheme agree if their base components and the
coordinate ring homomorphisms of their integral points agree. -/
private theorem lift_intPointOf_congr {Z : Scheme.{u}} {L : Type u} [CommRing L]
    {g g' : Spec (.of L) ⟶ Z} (hg : g = g')
    {φ φ' : MvPolynomial (Fin (1 + 1)) (ULift.{u} ℤ) →+* L} (hφ : φ = φ') (s : Fin 2)
    (hu : IsUnit (φ (X s))) (hu' : IsUnit (φ' (X s))) :
    pullback.lift (f := terminal.from Z) (g := terminal.from (projectiveSpaceAtUniverse.{u} 1))
        g (intPointOf φ s hu) (terminal.hom_ext _ _) =
      pullback.lift g' (intPointOf φ' s hu') (terminal.hom_ext _ _) := by
  subst hg hφ
  rfl

/-- **The scaling `[u : v] ↦ [a u : v]`, on points with values in a `K`-algebra.** -/
theorem lift_comp_scaling {L : Type u} [CommRing L] (f : K →+* L) (c : L) (a : K) (ha : a ≠ 0) :
    pullback.lift (Spec.map (CommRingCat.ofHom f))
        (intPointOf (vecHom L c 1) 1 (by rw [vecHom_X_one]; exact isUnit_one))
        (terminal.hom_ext _ _) ≫ (scaling a ha).hom =
      pullback.lift (Spec.map (CommRingCat.ofHom f))
        (intPointOf (vecHom L (f a * c) 1) 1 (by rw [vecHom_X_one]; exact isUnit_one))
        (terminal.hom_ext _ _) := by
  have hlift : ∀ c' : L, pullback.lift (Spec.map (CommRingCat.ofHom f))
      (intPointOf (vecHom L c' 1) 1 (by rw [vecHom_X_one]; exact isUnit_one))
      (terminal.hom_ext _ _) =
      ProjPoint.point (lineGrading K) (eval₂Hom f ![c', 1]) (X 1) (X_mem K 1) one_pos
        (by simp) ≫ (polynomialComparison K 1).iso.inv := by
    intro c'
    rw [point_comp_iso_inv]
    refine pullback.hom_ext ?_ ?_
    · simp only [pullback.lift_fst]
      congr 2
      ext r
      simp
    · simp only [pullback.lift_snd]
      unfold intPointOf
      refine ProjPoint.point_congr_ringHom _ ?_ _ _ _ _ _
      rw [comp_coordinateMap_eq_vecHom]
      simp
  have hX : (X 1 : MvPolynomial (Fin (1 + 1)) K) = matrixSubstGradedHom K 1
      (((scalingMatrix a ha)⁻¹⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) (X 1) := by
    rw [inv_inv, matrixSubstGradedHom_X]
    simp [scalingMatrix, Fin.sum_univ_two, Matrix.diagonal_apply]
  have hring : (eval₂Hom f ![c, 1]).comp (matrixSubstGradedHom K 1
      (((scalingMatrix a ha)⁻¹⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) : MvPolynomial (Fin (1 + 1)) K →+* MvPolynomial (Fin (1 + 1)) K) =
      eval₂Hom f ![f a * c, 1] := by
    rw [inv_inv]
    refine MvPolynomial.ringHom_ext (fun n => ?_) (fun i => ?_)
    · change eval₂Hom f ![c, 1] (matrixSubstGradedHom K 1 _ (C n)) = _
      rw [matrixSubstGradedHom_C]
      simp
    · change eval₂Hom f ![c, 1] (matrixSubstGradedHom K 1 _ (X i)) = _
      rw [matrixSubstGradedHom_X]
      fin_cases i <;> simp [scalingMatrix, Fin.sum_univ_two, Matrix.diagonal_apply]
  rw [hlift, hlift, scaling, projectiveSpaceMatrixToAut_hom_eq, Category.assoc,
    Iso.inv_hom_id_assoc, ← Category.assoc]
  congr 1
  rw [ProjPoint.point_congr _ _ hX _ ((matrixSubstGradedHom K 1 _).2 (X_mem _ 1)) _ _
      (by rw [← hX]; simp), ProjPoint.point_comp_map]
  exact ProjPoint.point_congr_ringHom _ hring _ _ _ _ _

end Scaling

/-! ### The generic fibre -/

section Generic

open Stacks.AlgebraicGeometry.ProjBaseChange PlaneCurveModel

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K] {π : R}

/-- **The parametrization `ℙ¹_K ≅ V(T₁T₂ - aT₀²)`**, `[u : v] ↦ [uv : v² : au²]`, with inverse the
projection `[T₀ : T₁ : T₂] ↦ [T₀ : T₁]`. -/
def paramIso {a : K} (ha : a ≠ 0) : projectiveSpaceOverRing 1 (.of K) ≅ conicScheme a where
  hom := (polynomialComparison K 1).iso.hom ≫ parametrizationP ha
  inv := firstProjection a
  hom_inv_id := by rw [Category.assoc, parametrizationP_comp_firstProjection, Iso.hom_inv_id]
  inv_hom_id := firstProjection_comp_parametrizationP ha

/-- The inverse of `paramIso` is the first projection. -/
private theorem paramIso_inv {a : K} (ha : a ≠ 0) : (paramIso ha).inv = firstProjection a := rfl

/-- The parametrization `paramIso` commutes with the structure morphisms to `Spec K`. -/
theorem paramIso_hom_toSpec {a : K} (ha : a ≠ 0) :
    (paramIso ha).hom ≫ conicToSpec a = projectiveSpaceOverRing 1 (.of K) ↘ Spec (.of K) := by
  rw [← firstProjection_comp_structure a, ← paramIso_inv ha, Iso.hom_inv_id_assoc]

/-- The conic over `K` is the generic fibre of the conic over `R`. -/
def genFibreIso (π : R) : conicScheme (algebraMap R K π) ≅
    pullback (conicToSpec π) (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
  asIso (conicChange (algebraMap R K) π) ≪≫
    (isPullback_mapMap (conicEquation π) (isHomogeneous_conicEquation π)
      (algebraMap R K)).isoPullback

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- Composing `genFibreIso` with the first projection gives the base change map `baseConic`. -/
theorem genFibreIso_hom_fst (π : R) :
    (genFibreIso (K := K) π).hom ≫ pullback.fst _ _ = baseConic (algebraMap R K) π := by
  rw [genFibreIso, Iso.trans_hom, Category.assoc, IsPullback.isoPullback_hom_fst, asIso_hom,
    baseConic_eq]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- Composing `genFibreIso` with the second projection gives the structure morphism of the conic
over `K`. -/
theorem genFibreIso_hom_snd (π : R) :
    (genFibreIso (K := K) π).hom ≫ pullback.snd _ _ = conicToSpec (algebraMap R K π) := by
  rw [genFibreIso, Iso.trans_hom, Category.assoc, IsPullback.isoPullback_hom_snd, asIso_hom,
    conicChange_toSpec]

/-- **The identification of the generic fibre of `X = V(T₁T₂ - πT₀²)` with `ℙ¹_K`**: the generic
fibre of `X` is `V(T₁T₂ - πT₀²)` over `K`, which the parametrization `[u : v] ↦ [uv : v² : πu²]`
identifies with `ℙ¹_K`. -/
def conicGenericFibreIso (hπ : Irreducible π) : projectiveSpaceOverRing 1 (.of K) ≅
    pullback (conicToSpec π) (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
  paramIso (algebraMap_ne_zero_of_irreducible hπ) ≪≫ genFibreIso π

omit [IsDiscreteValuationRing R] in
/-- Composing `conicGenericFibreIso` with the first projection gives the parametrization
`paramIso` followed by the base change morphism `baseConic`. -/
theorem conicGenericFibreIso_hom_fst (hπ : Irreducible π) :
    (conicGenericFibreIso (K := K) hπ).hom ≫ pullback.fst _ _ =
      (paramIso (algebraMap_ne_zero_of_irreducible hπ)).hom ≫ baseConic (algebraMap R K) π := by
  rw [conicGenericFibreIso, Iso.trans_hom, Category.assoc, genFibreIso_hom_fst]

/-- **`X = V(T₁T₂ - πT₀²)` is a model of `ℙ¹_K`.** -/
theorem isModel_conic (hπ : Irreducible π) :
    IsModel (projectiveSpaceOverRing 1 (.of K) ↘ Spec (.of K)) (conicToSpec π)
      (conicGenericFibreIso hπ) := by
  have := locallyOfFinitePresentation_toSpec (conicEquation π) (isHomogeneous_conicEquation π) 0
    (not_X_zero_dvd_conicEquation π)
  refine ⟨flat_conicToSpec hπ, inferInstance, inferInstance, ?_⟩
  rw [conicGenericFibreIso, Iso.trans_hom, Category.assoc, genFibreIso_hom_snd,
    paramIso_hom_toSpec]

end Generic

/-! ### The projections are morphisms of models -/

section ModelHom

open Stacks.AlgebraicGeometry.ProjBaseChange PlaneCurveModel

/-- The coordinates of the conic over a field are units in its function field. -/
private theorem isUnit_algebraMap_conicCoord {K : Type u} [Field K] {b : K} (hb : b ≠ 0)
    (i : Fin 3) :
    IsUnit (algebraMap (MvPolynomial (Fin 3) K ⧸ conicIdeal b)
      (FractionRing (MvPolynomial (Fin 3) K ⧸ conicIdeal b)) (conicCoord b i)) :=
  have := isDomain_conicRing hb
  isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
    (conicCoord_ne_zero hb i))

/-- The generic point of the conic over a field, read on the chart `D₊(T₁)`. -/
abbrev conicGenericPoint {K : Type u} [Field K] {b : K} (hb : b ≠ 0) :
    Spec (.of (FractionRing (MvPolynomial (Fin 3) K ⧸ conicIdeal b))) ⟶ conicScheme b :=
  have := isDomain_conicRing hb
  ProjPoint.point (conicGrading b) (algebraMap _ (FractionRing (MvPolynomial (Fin 3) K ⧸
    conicIdeal b))) (conicCoord b 1) (conicCoord_mem b 1) one_pos
    (isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
      (conicCoord_ne_zero hb 1)))

/-- **Morphisms out of the conic over a field are determined by the generic point.** -/
theorem conic_hom_ext {K : Type u} [Field K] {b : K} (hb : b ≠ 0) {Z : Scheme.{u}}
    [IsSeparated (terminal.from Z)] {f g : conicScheme b ⟶ Z}
    (h : conicGenericPoint hb ≫ f = conicGenericPoint hb ≫ g) : f = g := by
  have := isDomain_conicRing hb
  let A := MvPolynomial (Fin 3) K ⧸ conicIdeal b
  let ψ := algebraMap A (FractionRing A)
  have hψ : ∀ i, IsUnit (ψ (conicCoord b i)) := isUnit_algebraMap_conicCoord hb
  refine ProjPoint.hom_ext_of_point (conicGrading b) (terminal.from _) (terminal.hom_ext _ _)
    (conicCoord b) (conicCoord_mem b) (fun _ => one_pos) (irrelevant_le_span_mk_X _) ψ hψ
    (fun _ => ProjPoint.injective_awayEval_algebraMap _ _ _) (fun i => ?_)
  rwa [ProjPoint.point_indep _ ψ (conicCoord_mem b i) (conicCoord_mem b 1) one_pos one_pos
    (hψ i) (hψ 1)]

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K] {π : R}

/-- The projective line `ℙ¹_B` over a commutative ring `B` is a separated scheme. -/
theorem isSeparated_terminal_projectiveLine (B : CommRingCat.{u}) :
    IsSeparated (terminal.from (projectiveSpaceOverRing 1 B)) :=
  have : IsProper (projectiveSpaceOverRing 1 B ↘ Spec B) := isProper_projectiveSpaceOver 1 _
  isSeparated_terminal_from (projectiveSpaceOverRing 1 B ↘ Spec B)

/-- The value of `awayEval` on `T₀/T₁` in a field. -/
theorem awayEval_frac_field {S L : Type u} [CommRing S] [Field L] {b : S}
    (χ : MvPolynomial (Fin 3) S ⧸ conicIdeal b →+* L) (hu : IsUnit (χ (conicCoord b 1))) :
    ProjPoint.awayEval _ χ _ hu (frac b 1 0) = χ (conicCoord b 0) * (χ (conicCoord b 1))⁻¹ := by
  rw [awayEval_frac, Units.val_inv_eq_inv_val, IsUnit.unit_spec]

omit [IsDiscreteValuationRing R] in
/-- **The projections commute with the change of coefficients `R → K`.** -/
theorem baseConic_comp_firstProjection (hπ : Irreducible π) :
    baseConic (algebraMap R K) π ≫ firstProjection π =
      firstProjection (algebraMap R K π) ≫ genericFibreMap (R := R) (K := K) := by
  have := isSeparated_terminal_projectiveLine (.of R)
  have hb := algebraMap_ne_zero_of_irreducible (K := K) hπ
  have := isDomain_conicRing hb
  refine conic_hom_ext hb ?_
  have hψ1 := isUnit_algebraMap_conicCoord hb 1
  rw [conicGenericPoint, ProjPoint.point_congr_ringHom _ (eq_conicHom _ _) _ _ _ hψ1
    (by rwa [conicHom_coord]),
    ← Category.assoc, ← Category.assoc, point_comp_baseConic (algebraMap R K) π _ _ _ 1 hψ1,
    point_comp_firstProjection,
    point_comp_firstProjection, lift_comp_genericFibreMap]
  refine lift_intPointOf_congr ?_ ?_ _ _ _
  · rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    simp [conicHom_mk]
  · simp only [firstA, firstB, map_one, awayEval_frac_field, conicHom_coord]

omit [IsDiscreteValuationRing R] in
/-- **The second projection commutes with the change of coefficients `R → K`.** -/
theorem baseConic_comp_secondProjection (hπ : Irreducible π) :
    baseConic (algebraMap R K) π ≫ secondProjection π =
      secondProjection (algebraMap R K π) ≫ genericFibreMap (R := R) (K := K) := by
  have := isSeparated_terminal_projectiveLine (.of R)
  have hb := algebraMap_ne_zero_of_irreducible (K := K) hπ
  have := isDomain_conicRing hb
  refine conic_hom_ext hb ?_
  have hψ1 := isUnit_algebraMap_conicCoord hb 1
  rw [conicGenericPoint, ProjPoint.point_congr_ringHom _ (eq_conicHom _ _) _ _ _ hψ1
    (by rwa [conicHom_coord]),
    ← Category.assoc, ← Category.assoc, point_comp_baseConic (algebraMap R K) π _ _ _ 1 hψ1,
    point_comp_secondProjection,
    point_comp_secondProjection, lift_comp_genericFibreMap]
  refine lift_intPointOf_congr ?_ ?_ _ _ _
  · rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    simp [conicHom_mk]
  · simp only [secondA, secondB, map_one, map_mul, awayEval_frac_field, awayEval_constEl,
      conicConst, conicHom_mk, eval₂_C, eval₂_X, RingHom.comp_apply]

/-- **Over a field, the second projection is the first followed by the scaling by `a`**:
`[T₂ : T₀] = [aT₀ : T₁]`, and `[T₀ : T₁] ↦ [aT₀ : T₁]` is the scaling. -/
theorem secondProjection_eq {a : K} (ha : a ≠ 0) :
    secondProjection a = firstProjection a ≫ (scaling a ha).hom := by
  have := isSeparated_terminal_projectiveLine (.of K)
  have := isDomain_conicRing ha
  refine conic_hom_ext ha ?_
  let A := MvPolynomial (Fin 3) K ⧸ conicIdeal a
  let ψ := algebraMap A (FractionRing A)
  have hψ1 : IsUnit (ψ (conicCoord a 1)) := isUnit_algebraMap_conicCoord ha 1
  let f := ψ.comp ((Ideal.Quotient.mk (conicIdeal a)).comp C)
  have h1 : conicGenericPoint ha ≫ firstProjection a =
      pullback.lift (Spec.map (CommRingCat.ofHom f))
        (intPointOf (vecHom _ (ProjPoint.awayEval _ ψ _ hψ1 (firstA a 1)) 1) 1
          (by rw [vecHom_X_one]; exact isUnit_one)) (terminal.hom_ext _ _) := by
    rw [conicGenericPoint, point_comp_firstProjection]
    refine lift_intPointOf_congr rfl ?_ _ _ _
    rw [show firstB a 1 = 1 from rfl, map_one]
  have h2 : conicGenericPoint ha ≫ secondProjection a =
      pullback.lift (Spec.map (CommRingCat.ofHom f))
        (intPointOf (vecHom _ (f a * ProjPoint.awayEval _ ψ _ hψ1 (firstA a 1)) 1) 1
          (by rw [vecHom_X_one]; exact isUnit_one)) (terminal.hom_ext _ _) := by
    rw [conicGenericPoint, point_comp_secondProjection]
    refine lift_intPointOf_congr rfl ?_ _ _ _
    rw [show secondB a 1 = 1 from rfl, map_one, show secondA a 1 = constEl a 1 * frac a 1 0
      from rfl, map_mul, awayEval_constEl]
    rfl
  rw [h2, ← Category.assoc, h1, lift_comp_scaling]

/-- **The first projection is a morphism of models**, from `X` with its identification
`conicGenericFibreIso` to `ℙ¹_R` with the canonical identification of its generic fibre. -/
theorem isModelHom_firstProjection (hπ : Irreducible π) :
    IsModelHom (conicToSpec π) (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R))
      (conicGenericFibreIso (K := K) hπ) projectiveLineGenericFibreIso (firstProjection π) := by
  refine IsModelHom.of_genericFiber_fst_comp (firstProjection_comp_structure π)
    ((isModel_conic hπ).2.2.2.trans projectiveLineGenericFibreIso_hom_snd.symm) ?_
  rw [← Category.assoc, conicGenericFibreIso_hom_fst, Category.assoc,
    baseConic_comp_firstProjection hπ, ← paramIso_inv (algebraMap_ne_zero_of_irreducible hπ),
    Iso.hom_inv_id_assoc]

/-- **The second projection is a morphism of models**, from `X` with its identification
`conicGenericFibreIso` to `ℙ¹_R` with the identification twisted by the scaling
`[u : v] ↦ [πu : v]`. -/
theorem isModelHom_secondProjection (hπ : Irreducible π) :
    IsModelHom (conicToSpec π) (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R))
      (conicGenericFibreIso (K := K) hπ) (twistedGenericFibreIso hπ) (secondProjection π) := by
  refine IsModelHom.of_genericFiber_fst_comp (secondProjection_comp_structure π)
    ((isModel_conic hπ).2.2.2.trans (twistedGenericFibreIso_hom_snd hπ).symm) ?_
  rw [← Category.assoc, conicGenericFibreIso_hom_fst, Category.assoc,
    baseConic_comp_secondProjection hπ, secondProjection_eq (algebraMap_ne_zero_of_irreducible hπ),
    ← paramIso_inv (algebraMap_ne_zero_of_irreducible hπ), Category.assoc,
    Iso.hom_inv_id_assoc, twistedGenericFibreIso, Iso.trans_hom, Category.assoc]

end ModelHom

end Stacks.Models.GenusZero

end
