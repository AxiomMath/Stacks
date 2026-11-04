module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.SplitConicComponents
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFibreRadicalComponents
public import StacksFrontier.AlgebraicGeometry.Curves.Models.RegularProperModel
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.Immersions

/-!
# The special fibre of the split conic is reduced, with components the two lines

Let `R` be a discrete valuation ring with uniformizer `π`, fraction field `K` and residue field
`k`, and let `X = V(T₁T₂ - πT₀²) ⊆ ℙ²_R`. Then `X` is a regular proper model of `ℙ¹_K`, its special
fibre `V(T₁T₂) ⊆ ℙ²_k` is reduced, and the irreducible components of the special fibre are the two
lines `C₁ = V(π, T₁)` and `C₂ = V(π, T₂)`. Hence, as sheaves of ideals on `X`, `X_k = C₁ + C₂`.

## Main definitions

* `Stacks.Models.GenusZero.conicSituation`: `X` as a regular proper model of `ℙ¹_K`, in the
  standing situation of [Stacks, Tag 0C61].

## Main results

* `Stacks.Models.GenusZero.range_specialFibre_eq_union`: the special fibre is the union of the
  two lines.
* `Stacks.Models.GenusZero.specialFiberIdeal_eq_mul`: the special fibre is the sum `C₁ + C₂` of
  the two lines.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial HomogeneousLocalization

universe u

namespace Stacks.Models.GenusZero

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### The split conic as a regular proper model -/

section Situation

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (K : Type u)
  [Field K] [Algebra R K] [IsFractionRing R K] {π : R} (hπ : Irreducible π)

attribute [local instance] AlgebraicGeometry.isCurve_projectiveSpaceOver_one

/-- **The split conic `X = V(T₁T₂ - πT₀²)` as a regular proper model of `ℙ¹_K`**, with residue
field the residue field of `R` and the identification `conicGenericFibreIso` of its generic
fibre. -/
def conicSituation : RegularProperModelSituation.{u} where
  R := R
  K := K
  k := IsLocalRing.ResidueField R
  residueEquiv := AlgEquiv.refl
  C := projectiveSpaceOverRing 1 (.of K)
  C_to_K := projectiveSpaceOverRing 1 (.of K) ↘ Spec (.of K)
  X := conicScheme π
  X_to_R := conicToSpec π
  flat := flat_conicToSpec hπ
  locallyOfFiniteType := (isModel_conic (K := K) hπ).2.1
  quasiCompact := (isModel_conic (K := K) hπ).2.2.1
  regular := isRegular_conicScheme hπ
  genericFiberIso := conicGenericFibreIso hπ
  genericFiberIso_over_K := (isModel_conic (K := K) hπ).2.2.2
  π := π
  uniformizer := hπ
  curveProjective := Stacks.HProjective.isHProjective_over 1 _
  isIso_globalSections := isIso_ΓSpecIso_inv_comp_appTop_projectiveSpaceOverRing K 1

end Situation


/-! ### The special fibre is reduced -/

section Reduced

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {π : R}
  (hπ : Irreducible π)
include hπ

local notation "κ" => IsLocalRing.ResidueField R

omit hπ in
/-- `T₁T₂` is squarefree in `k[T₀, T₁, T₂]`. -/
theorem squarefree_X_one_mul_X_two (k : Type u) [Field k] :
    Squarefree (X 1 * X 2 : MvPolynomial (Fin 3) k) := by
  have hX : ∀ i : Fin 3, Irreducible (X i : MvPolynomial (Fin 3) k) :=
    fun i => (MvPolynomial.X_prime (σ := Fin 3) (R := k) (i := i)).irreducible
  rw [squarefree_mul_iff]
  refine ⟨(hX 1).isRelPrime_iff_not_dvd.2 ?_, (hX 1).squarefree, (hX 2).squarefree⟩
  rw [MvPolynomial.X_dvd_X]
  simp

omit hπ in
/-- The homogeneous coordinate ring `k[T₀, T₁, T₂]/(T₁T₂)` of the special fibre is reduced. -/
theorem isReduced_specialFibreRing (hπ' : π ∈ IsLocalRing.maximalIdeal R) :
    IsReduced (MvPolynomial (Fin 3) κ ⧸ (PlaneCurveModel.equationIdeal
      (MvPolynomial.map (algebraMap R κ) (conicEquation π))
      ((isHomogeneous_conicEquation π).map _)).toIdeal) := by
  rw [PlaneCurveModel.toIdeal_equationIdeal, map_conicEquation]
  have h0 : algebraMap R κ π = 0 := residue_eq_zero hπ'
  rw [h0, conicEquation, map_zero, zero_mul, sub_zero]
  exact (Ideal.isRadical_iff_quotient_reduced _).mp
    (isRadical_iff_span_singleton.mp (squarefree_X_one_mul_X_two κ).isRadical)

/-- **The special fibre of `X` is reduced**: it is `Proj k[T₀, T₁, T₂]/(T₁T₂)`. -/
theorem isReduced_specialFibre :
    IsReduced (pullback (conicToSpec π) (residueSpecMap R)) := by
  have h := PlaneCurveModel.isPullback_mapMap (conicEquation π) (isHomogeneous_conicEquation π)
    (algebraMap R κ)
  have := isReduced_specialFibreRing (mem_maximalIdeal_of_irreducible hπ)
  have hred : IsReduced (PlaneCurveModel.scheme (MvPolynomial.map (algebraMap R κ)
      (conicEquation π)) ((isHomogeneous_conicEquation π).map _)) := by
    have hst : ∀ x : PlaneCurveModel.scheme (MvPolynomial.map (algebraMap R κ)
        (conicEquation π)) ((isHomogeneous_conicEquation π).map _),
        _root_.IsReduced ((PlaneCurveModel.scheme _ _).presheaf.stalk x) := by
      intro x
      have := x.isPrime
      have : _root_.IsReduced (HomogeneousLocalization.AtPrime (PlaneCurveModel.grading _
          ((isHomogeneous_conicEquation π).map (algebraMap R κ))) x.1.toIdeal) :=
        isReduced_of_injective (algebraMap _ (Localization x.1.toIdeal.primeCompl))
          (HomogeneousLocalization.val_injective _)
      exact isReduced_of_injective (AlgebraicGeometry.Proj.stalkIso' _ x)
        (AlgebraicGeometry.Proj.stalkIso' _ x).injective
    exact isReduced_of_isReduced_stalk _
  exact isReduced_of_isOpenImmersion h.isoPullback.inv

end Reduced


/-! ### Two closed irreducible sets covering a space -/

section Topology

variable {T : Type*} [TopologicalSpace T] {A B : Set T}

/-- **The irreducible components of a union of two incomparable closed irreducible sets are the
two sets.** -/
theorem eq_or_eq_of_mem_irreducibleComponents (hAc : IsClosed A) (hBc : IsClosed B)
    (hA : IsIrreducible A) (hB : IsIrreducible B) (hcov : A ∪ B = Set.univ)
    {Z : Set T} (hZ : Z ∈ irreducibleComponents T) : Z = A ∨ Z = B := by
  rcases isPreirreducible_iff_isClosed_union_isClosed.mp hZ.1.isPreirreducible A B hAc hBc
    (hcov ▸ Set.subset_univ Z) with h | h
  · exact Or.inl (le_antisymm h (hZ.2 hA h))
  · exact Or.inr (le_antisymm h (hZ.2 hB h))

/-- One of two incomparable closed irreducible sets covering a space is an irreducible
component. -/
theorem mem_irreducibleComponents_of_union (hAc : IsClosed A) (hBc : IsClosed B)
    (hA : IsIrreducible A) (hB : IsIrreducible B) (hcov : A ∪ B = Set.univ) (hAB : ¬ A ⊆ B) :
    A ∈ irreducibleComponents T := by
  obtain ⟨Z, hZ, hAZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible A hA
  rcases eq_or_eq_of_mem_irreducibleComponents hAc hBc hA hB hcov hZ with rfl | rfl
  · exact hZ
  · exact (hAB hAZ).elim

end Topology

/-! ### The two lines are the irreducible components of the special fibre -/

section Components

open Stacks.AlgebraicGeometry.ProjBaseChange

/-- The base change morphism `ℙ¹_T ⟶ ℙ¹_S` lies over `T ⟶ S`. -/
theorem baseChangeLine_comp_structure {S T : Scheme.{u}} (g : T ⟶ S) :
    baseChangeLine g ≫ (projectiveSpaceOver 1 S ↘ S) = (projectiveSpaceOver 1 T ↘ T) ≫ g := by
  rw [baseChangeLine, Category.assoc, pullback.condition, ← Category.assoc,
    ← projectiveSpaceOverBaseChangeIso_hom_over, Iso.inv_hom_id_assoc]

variable {R : Type u} [CommRing R] [IsLocalRing R]

local notation "κ" => IsLocalRing.ResidueField R

/-- The structure morphism `Proj k[S₀, S₁] ⟶ Spec k`. -/
abbrev lineToSpec : AlgebraicGeometry.Proj (lineGrading κ) ⟶ Spec (.of κ) :=
  (polynomialComparison κ 1).iso.inv ≫ (projectiveSpaceOverRing 1 (.of κ) ↘ Spec (.of κ))

variable {π : R} (hπ : π ∈ IsLocalRing.maximalIdeal R)

/-- The line `C₁` lies over the closed point of `Spec R`. -/
theorem firstLine_comp_conicToSpec :
    firstLine hπ ≫ conicToSpec π = lineToSpec ≫ residueSpecMap R := by
  rw [← secondProjection_comp_structure π, ← Category.assoc, firstLine_comp_secondProjection,
    Category.assoc, Category.assoc]
  exact (polynomialComparison κ 1).iso.inv ≫= baseChangeLine_comp_structure (residueSpecMap R)

/-- The line `C₂` lies over the closed point of `Spec R`. -/
theorem secondLine_comp_conicToSpec :
    secondLine hπ ≫ conicToSpec π = lineToSpec ≫ residueSpecMap R := by
  rw [← firstProjection_comp_structure π, ← Category.assoc, secondLine_comp_firstProjection,
    Category.assoc, Category.assoc]
  exact (polynomialComparison κ 1).iso.inv ≫= baseChangeLine_comp_structure (residueSpecMap R)

/-- The line `C₁` as a closed subscheme of the special fibre. -/
abbrev firstLineFibre : AlgebraicGeometry.Proj (lineGrading κ) ⟶
    pullback (conicToSpec π) (residueSpecMap R) :=
  pullback.lift (firstLine hπ) lineToSpec (firstLine_comp_conicToSpec hπ)

/-- The line `C₂` as a closed subscheme of the special fibre. -/
abbrev secondLineFibre : AlgebraicGeometry.Proj (lineGrading κ) ⟶
    pullback (conicToSpec π) (residueSpecMap R) :=
  pullback.lift (secondLine hπ) lineToSpec (secondLine_comp_conicToSpec hπ)

/-- The generic point of `Proj k[S₀, S₁]`, the zero ideal. -/
def lineZeroIdealPoint : ProjectiveSpectrum (lineGrading κ) where
  asHomogeneousIdeal := ⊥
  isPrime := by simpa using (Ideal.isPrime_bot (α := MvPolynomial (Fin (1 + 1)) κ))
  not_irrelevant_le h := by
    have hX : (X 0 : MvPolynomial (Fin (1 + 1)) κ) ∈ HomogeneousIdeal.irrelevant (lineGrading κ) :=
      by
      rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
        DirectSum.decompose_of_mem_ne _ (X_mem κ 0) one_ne_zero]
    exact X_ne_zero (R := κ) (0 : Fin (1 + 1)) (h hX)

/-- The generic point of a line given by `y` is not in the line given by `y'` if the coordinate
`Tᵢ` vanishes on the latter but not on the former. -/
private theorem not_range_map_lineHom_subset
    {y y' : Fin 3 → MvPolynomial (Fin (1 + 1)) κ} {hy hy' hlin hlin'} {h h'} (i : Fin 3)
    (hi : y' i = 0) (hi' : y i ≠ 0) :
    ¬ Set.range (Proj.map (lineHom π y hy hlin) h) ⊆
      Set.range (Proj.map (lineHom π y' hy' hlin') h') := by
  intro hsub
  obtain ⟨x, hx⟩ := hsub ⟨lineZeroIdealPoint, rfl⟩
  have hmem : conicCoord π i ∈
      (Proj.map (lineHom π y hy hlin) h lineZeroIdealPoint).asHomogeneousIdeal := by
    rw [← hx]
    change lineHom π y' hy' hlin' (conicCoord π i) ∈ x.asHomogeneousIdeal
    rw [lineHom_coord, hi]
    exact zero_mem _
  change lineHom π y hy hlin (conicCoord π i) ∈ (⊥ : HomogeneousIdeal (lineGrading κ)) at hmem
  rw [lineHom_coord] at hmem
  exact hi' hmem

/-- The line `C₁` is not contained in the line `C₂`: the generic point of `C₁` does not contain
`T₂`, which vanishes on `C₂`. -/
theorem not_range_firstLine_subset :
    ¬ Set.range (firstLine hπ) ⊆ Set.range (secondLine hπ) :=
  not_range_map_lineHom_subset 2 (by simp) (by simp)

/-- The line `C₂` is not contained in the line `C₁`. -/
theorem not_range_secondLine_subset :
    ¬ Set.range (secondLine hπ) ⊆ Set.range (firstLine hπ) :=
  not_range_map_lineHom_subset 1 (by simp) (by simp)

end Components


/-! ### The special fibre is the sum of the two lines -/

section Decomposition

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {π : R}
  (hπ : Irreducible π)

local notation "κ" => IsLocalRing.ResidueField R

/-- **The special fibre of `X` is the union of the two lines `C₁` and `C₂`.** -/
theorem range_specialFibre_eq_union :
    Set.range (pullback.fst (conicToSpec π) (residueSpecMap R)) =
      Set.range (firstLine (mem_maximalIdeal_of_irreducible hπ)) ∪
        Set.range (secondLine (mem_maximalIdeal_of_irreducible hπ)) := by
  ext x
  refine ⟨mem_range_lines_of_mem_specialFibre hπ x, ?_⟩
  rintro (⟨y, rfl⟩ | ⟨y, rfl⟩)
  · exact ⟨firstLineFibre _ y, by rw [← Scheme.Hom.comp_apply, pullback.lift_fst]⟩
  · exact ⟨secondLineFibre _ y, by rw [← Scheme.Hom.comp_apply, pullback.lift_fst]⟩

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The preimage of the range of `l ≫ ι` under an injective `ι` is the range of `l`. -/
theorem preimage_range_comp {P Y W : Scheme.{u}} (l : P ⟶ Y) (ι : Y ⟶ W)
    (h : Function.Injective ι) : ι ⁻¹' Set.range (l ≫ ι) = Set.range l := by
  ext t
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, h (by rwa [Scheme.Hom.comp_apply] at hy)⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, Scheme.Hom.comp_apply _ _ _⟩

/-- If `l ≫ ι` is a closed immersion from an irreducible space and `ι` is injective, then the range
of `l` is closed and irreducible, is the preimage of the range of `l ≫ ι`, and maps onto it. -/
private theorem isClosed_and_isIrreducible_range_of_comp {P Y W : Scheme.{u}} [IrreducibleSpace P]
    (l : P ⟶ Y) (ι : Y ⟶ W) (f : P ⟶ W) (hf : l ≫ ι = f) [IsClosedImmersion f]
    (hinj : Function.Injective ι) :
    IsClosed (Set.range l) ∧ IsIrreducible (Set.range l) ∧
      ι ⁻¹' Set.range f = Set.range l ∧ ι '' Set.range l = Set.range f := by
  have hpre : ι ⁻¹' Set.range f = Set.range l := hf ▸ preimage_range_comp l ι hinj
  refine ⟨?_, ?_, hpre, ?_⟩
  · rw [← hpre]; exact f.isClosedEmbedding.isClosed_range.preimage ι.continuous
  · rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ l.continuous.continuousOn
  · rw [← hf, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]

/-- The special fibre, as the cover of its two lines: the facts entering
`eq_or_eq_of_mem_irreducibleComponents`. -/
theorem specialFibre_lines :
    IsClosed (Set.range (firstLineFibre (mem_maximalIdeal_of_irreducible hπ))) ∧
    IsClosed (Set.range (secondLineFibre (mem_maximalIdeal_of_irreducible hπ))) ∧
    IsIrreducible (Set.range (firstLineFibre (mem_maximalIdeal_of_irreducible hπ))) ∧
    IsIrreducible (Set.range (secondLineFibre (mem_maximalIdeal_of_irreducible hπ))) ∧
    Set.range (firstLineFibre (mem_maximalIdeal_of_irreducible hπ)) ∪
      Set.range (secondLineFibre (mem_maximalIdeal_of_irreducible hπ)) = Set.univ ∧
    ¬ Set.range (firstLineFibre (mem_maximalIdeal_of_irreducible hπ)) ⊆
      Set.range (secondLineFibre (mem_maximalIdeal_of_irreducible hπ)) ∧
    ¬ Set.range (secondLineFibre (mem_maximalIdeal_of_irreducible hπ)) ⊆
      Set.range (firstLineFibre (mem_maximalIdeal_of_irreducible hπ)) := by
  set hπ' := mem_maximalIdeal_of_irreducible hπ
  have : IsClosedImmersion (residueSpecMap R) :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  set ι := pullback.fst (conicToSpec π) (residueSpecMap R)
  have hinj : Function.Injective ι := ι.isClosedEmbedding.injective
  obtain ⟨hAc, hAi, hA, hiA⟩ := isClosed_and_isIrreducible_range_of_comp (firstLineFibre hπ') ι
    (firstLine hπ') (pullback.lift_fst _ _ _) hinj
  obtain ⟨hBc, hBi, hB, hiB⟩ := isClosed_and_isIrreducible_range_of_comp (secondLineFibre hπ') ι
    (secondLine hπ') (pullback.lift_fst _ _ _) hinj
  refine ⟨hAc, hBc, hAi, hBi, ?_, ?_, ?_⟩
  · rw [← hA, ← hB, ← Set.preimage_union, ← range_specialFibre_eq_union hπ, Set.preimage_range]
  · intro h
    exact not_range_firstLine_subset hπ' (hiA ▸ hiB ▸ Set.image_mono h)
  · intro h
    exact not_range_secondLine_subset hπ' (hiA ▸ hiB ▸ Set.image_mono h)

end Decomposition


/-! ### The special fibre as a sheaf of ideals -/

section Ideal

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (K : Type u)
  [Field K] [Algebra R K] [IsFractionRing R K] {π : R} (hπ : Irreducible π)

local notation "κ" => IsLocalRing.ResidueField R

/-- The reduced ideal of an irreducible component of the special fibre which is the image of a line
`l : ℙ¹_k ⟶ X_k` is the ideal of the closed immersion `ℙ¹_k ⟶ X`. -/
theorem specialFiberComponentIdeal_eq_ker
    (l : AlgebraicGeometry.Proj (lineGrading κ) ⟶ pullback (conicToSpec π) (residueSpecMap R))
    [IsClosedImmersion (l ≫ pullback.fst (conicToSpec π) (residueSpecMap R))]
    (Z : irreducibleComponents (conicSituation K hπ).specialFiber)
    (h : Z.1 = Set.range l) :
    (conicSituation K hπ).specialFiberComponentIdeal Z =
      (l ≫ pullback.fst (conicToSpec π) (residueSpecMap R)).ker := by
  have hset : (pullback.fst (conicToSpec π) (residueSpecMap R)) '' Z.1 =
      Set.range (l ≫ pullback.fst (conicToSpec π) (residueSpecMap R)) := by
    rw [h, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  have hcl : TopologicalSpace.Closeds.closure
      ((pullback.fst (conicToSpec π) (residueSpecMap R)) '' Z.1) =
      (l ≫ pullback.fst (conicToSpec π) (residueSpecMap R)).ker.support := by
    refine SetLike.coe_injective ?_
    rw [Scheme.Hom.support_ker, TopologicalSpace.Closeds.coe_closure, hset]
  refine (congrArg Scheme.IdealSheafData.vanishingIdeal hcl).trans ?_
  exact (ker_eq_vanishingIdeal_of_reduced_closed_immersion
    (l ≫ pullback.fst (conicToSpec π) (residueSpecMap R))).symm

/-- **The special fibre of `X` is the sum `C₁ + C₂` of the two lines**: as sheaves of ideals on
`X`, `X_k = C₁ + C₂`, where `Cᵢ` is the ideal of the closed immersion `ℙ¹_k ⟶ X` onto the line.

The special fibre is reduced, so it is the sum of its irreducible components
(`Stacks.Models.RegularModelSituation.radical_specialFiberIdeal_eq_prod`), and these are the two
lines. -/
theorem specialFiberIdeal_eq_mul :
    (conicSituation K hπ).specialFiberIdeal =
      (firstLine (mem_maximalIdeal_of_irreducible hπ)).ker *
        (secondLine (mem_maximalIdeal_of_irreducible hπ)).ker := by
  set S := conicSituation K hπ
  obtain ⟨hAc, hBc, hA, hB, hcov, hAB, hBA⟩ := specialFibre_lines hπ
  have : IsReduced S.specialFiber := isReduced_specialFibre hπ
  have hrad : S.specialFiberIdeal.radical = S.specialFiberIdeal := by
    rw [← Scheme.IdealSheafData.vanishingIdeal_support]
    exact (ker_eq_vanishingIdeal_of_reduced_closed_immersion S.specialFiberι).symm
  let Z1 : irreducibleComponents S.specialFiber :=
    ⟨_, mem_irreducibleComponents_of_union hAc hBc hA hB hcov hAB⟩
  let Z2 : irreducibleComponents S.specialFiber :=
    ⟨_, mem_irreducibleComponents_of_union hBc hAc hB hA ((Set.union_comm _ _).trans hcov) hBA⟩
  have hne : Z1 ≠ Z2 := fun h => hAB (congrArg Subtype.val h).le
  have huniv : (Finset.univ : Finset (irreducibleComponents S.specialFiber)) = {Z1, Z2} := by
    ext Z
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases eq_or_eq_of_mem_irreducibleComponents hAc hBc hA hB hcov Z.2 with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have h1 : IsClosedImmersion (firstLineFibre (mem_maximalIdeal_of_irreducible hπ) ≫
      pullback.fst (conicToSpec π) (residueSpecMap R)) := by
    rw [pullback.lift_fst]; infer_instance
  have h2 : IsClosedImmersion (secondLineFibre (mem_maximalIdeal_of_irreducible hπ) ≫
      pullback.fst (conicToSpec π) (residueSpecMap R)) := by
    rw [pullback.lift_fst]; infer_instance
  rw [← hrad, S.radical_specialFiberIdeal_eq_prod, huniv, Finset.prod_pair hne,
    specialFiberComponentIdeal_eq_ker K hπ _ Z1 rfl,
    specialFiberComponentIdeal_eq_ker K hπ _ Z2 rfl, pullback.lift_fst, pullback.lift_fst]
  rfl

end Ideal

end Stacks.Models.GenusZero

end
