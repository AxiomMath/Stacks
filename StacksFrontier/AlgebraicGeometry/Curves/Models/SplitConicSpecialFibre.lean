module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.GenusZeroConicModel
public import StacksFrontier.AlgebraicGeometry.Limits.ProjGradedSurjection01N0

/-!
# The special fibre of the split conic and the two contractions

Let `R` be a discrete valuation ring with uniformizer `π` and residue field `k`, and let
`X = V(T₁T₂ - πT₀²) ⊆ ℙ²_R`. Its special fibre is `V(T₁T₂) ⊆ ℙ²_k`, the union of the two lines
`C₁ = V(T₁)` and `C₂ = V(T₂)`, each a copy of `ℙ¹_k`. The first projection `[T₀ : T₁]` contracts
`C₁` to the point `[1 : 0]` and maps `C₂` isomorphically onto the special fibre of `ℙ¹_R`; the
second projection `[T₂ : T₀]` contracts `C₂` to the point `[0 : 1]` and maps `C₁` isomorphically
onto the special fibre of `ℙ¹_R`.

## Main definitions

* `Stacks.Models.GenusZero.firstLine` and `Stacks.Models.GenusZero.secondLine`: the closed
  immersions `ℙ¹_k ⟶ X` onto `C₁` and `C₂`, `[S₀ : S₁] ↦ [S₁ : 0 : S₀]` and
  `[S₀ : S₁] ↦ [S₀ : S₁ : 0]`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial HomogeneousLocalization

universe u

namespace Stacks.Models.GenusZero

attribute [local instance] MvPolynomial.gradedAlgebra

section Lines

variable {R : Type u} [CommRing R] [IsLocalRing R] (π : R)

/-- The residue field. -/
local notation "κ" => IsLocalRing.ResidueField R

/-- The graded homomorphism `R[T₀, T₁, T₂]/(T₁T₂ - πT₀²) → k[S₀, S₁]` sending the coordinates to
linear forms `y` with `y₁y₂ = π̄ y₀²`. -/
def lineHom (y : Fin 3 → MvPolynomial (Fin (1 + 1)) κ)
    (hy : y 1 * y 2 = (C.comp (IsLocalRing.residue R)) π * y 0 ^ 2)
    (hlin : ∀ i, (y i).IsHomogeneous 1) : conicGrading π →+*ᵍ lineGrading κ where
  __ := conicHom π (C.comp (IsLocalRing.residue R)) y hy
  map_mem {n b} hb := by
    obtain ⟨p, hp, rfl⟩ := (Stacks.HomogeneousIdeal.mem_quotientGrading_iff _ b).1 hb
    change conicHom π _ y hy (Ideal.Quotient.mk _ p) ∈ _
    rw [conicHom_mk, mem_homogeneousSubmodule]
    have := ((mem_homogeneousSubmodule _ _).1 hp).eval₂ (C.comp (IsLocalRing.residue R)) y
      (fun r => isHomogeneous_C _ _) hlin
    rwa [one_mul] at this

/-- The homomorphism `lineHom` is the evaluation `conicHom` at the images of the coordinates. -/
theorem lineHom_apply (y : Fin 3 → MvPolynomial (Fin (1 + 1)) κ)
    (hy : y 1 * y 2 = (C.comp (IsLocalRing.residue R)) π * y 0 ^ 2)
    (hlin : ∀ i, (y i).IsHomogeneous 1) (b : MvPolynomial (Fin 3) R ⧸ conicIdeal π) :
    lineHom π y hy hlin b = conicHom π (C.comp (IsLocalRing.residue R)) y hy b := rfl

/-- The homomorphism `lineHom` sends the coordinate `Tᵢ` to `yᵢ`. -/
@[simp] theorem lineHom_coord (y : Fin 3 → MvPolynomial (Fin (1 + 1)) κ)
    (hy : y 1 * y 2 = (C.comp (IsLocalRing.residue R)) π * y 0 ^ 2)
    (hlin : ∀ i, (y i).IsHomogeneous 1) (i : Fin 3) :
    lineHom π y hy hlin (conicCoord π i) = y i := by
  rw [lineHom_apply, conicHom_coord]

/-- The homomorphism `lineHom` sends the class of a constant `r ∈ R` to the constant given by its
residue `r̄ ∈ k`. -/
@[simp] theorem lineHom_C (y : Fin 3 → MvPolynomial (Fin (1 + 1)) κ)
    (hy : y 1 * y 2 = (C.comp (IsLocalRing.residue R)) π * y 0 ^ 2)
    (hlin : ∀ i, (y i).IsHomogeneous 1) (r : R) :
    lineHom π y hy hlin (Ideal.Quotient.mk (conicIdeal π) (C r)) = C (IsLocalRing.residue R r) := by
  rw [lineHom_apply, conicHom_mk, eval₂_C]
  rfl

/-- `lineHom` is surjective when both coordinates of `k[S₀, S₁]` occur among the `yᵢ`. -/
theorem surjective_lineHom (y : Fin 3 → MvPolynomial (Fin (1 + 1)) κ)
    (hy : y 1 * y 2 = (C.comp (IsLocalRing.residue R)) π * y 0 ^ 2)
    (hlin : ∀ i, (y i).IsHomogeneous 1) (i₀ i₁ : Fin 3) (h₀ : y i₀ = X 0) (h₁ : y i₁ = X 1) :
    Function.Surjective (lineHom π y hy hlin) := by
  have hrange : ∀ q : MvPolynomial (Fin (1 + 1)) κ, q ∈ (lineHom π y hy hlin).range := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C c =>
      obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective c
      refine ⟨Ideal.Quotient.mk _ (C r), ?_⟩
      change conicHom π _ y hy (Ideal.Quotient.mk _ (C r)) = _
      rw [conicHom_mk, eval₂_C]
      rfl
    | add p q hp hq => exact add_mem hp hq
    | mul_X p i hp =>
      refine mul_mem hp ?_
      fin_cases i
      · refine ⟨conicCoord π i₀, ?_⟩
        change conicHom π _ y hy (conicCoord π i₀) = X 0
        rw [conicHom_coord, h₀]
      · refine ⟨conicCoord π i₁, ?_⟩
        change conicHom π _ y hy (conicCoord π i₁) = X 1
        rw [conicHom_coord, h₁]
  intro q
  obtain ⟨b, hb⟩ := hrange q
  exact ⟨b, hb⟩

variable {π} (hπ : π ∈ IsLocalRing.maximalIdeal R)

include hπ in
/-- An element of the maximal ideal vanishes in the residue field. -/
theorem residue_eq_zero : IsLocalRing.residue R π = 0 :=
  (IsLocalRing.residue_eq_zero_iff π).2 hπ

include hπ in
/-- The images `(S₁, 0, S₀)` of the coordinates satisfy the equation of `X` modulo `π`. -/
theorem firstLine_rel :
    (![X 1, 0, X 0] : Fin 3 → MvPolynomial (Fin (1 + 1)) κ) 1 *
        (![X 1, 0, X 0] : Fin 3 → MvPolynomial (Fin (1 + 1)) κ) 2 =
      (C.comp (IsLocalRing.residue R)) π *
        (![X 1, 0, X 0] : Fin 3 → MvPolynomial (Fin (1 + 1)) κ) 0 ^ 2 := by
  simp [residue_eq_zero hπ]

include hπ in
/-- The images `(S₀, S₁, 0)` of the coordinates satisfy the equation of `X` modulo `π`. -/
theorem secondLine_rel :
    (![X 0, X 1, 0] : Fin 3 → MvPolynomial (Fin (1 + 1)) κ) 1 *
        (![X 0, X 1, 0] : Fin 3 → MvPolynomial (Fin (1 + 1)) κ) 2 =
      (C.comp (IsLocalRing.residue R)) π *
        (![X 0, X 1, 0] : Fin 3 → MvPolynomial (Fin (1 + 1)) κ) 0 ^ 2 := by
  simp [residue_eq_zero hπ]

/-- The images `(S₁, 0, S₀)` of the coordinates are linear forms. -/
theorem firstLine_lin :
    ∀ i, ((![X 1, 0, X 0] : Fin 3 → MvPolynomial (Fin (1 + 1)) κ) i).IsHomogeneous 1 := by
  intro i; fin_cases i <;> simp [isHomogeneous_X, isHomogeneous_zero]

/-- The images `(S₀, S₁, 0)` of the coordinates are linear forms. -/
theorem secondLine_lin :
    ∀ i, ((![X 0, X 1, 0] : Fin 3 → MvPolynomial (Fin (1 + 1)) κ) i).IsHomogeneous 1 := by
  intro i; fin_cases i <;> simp [isHomogeneous_X, isHomogeneous_zero]

/-- **The line `C₁ = V(T₁)` of the special fibre**, as the closed immersion `ℙ¹_k ⟶ X`,
`[S₀ : S₁] ↦ [S₁ : 0 : S₀]`. -/
def firstLine : AlgebraicGeometry.Proj (lineGrading κ) ⟶ conicScheme π :=
  Proj.map (lineHom π _ (firstLine_rel hπ) firstLine_lin)
    (Proj.irrelevant_le_map_of_surjective _
      (surjective_lineHom π _ _ _ 2 0 rfl rfl))

/-- **The line `C₂ = V(T₂)` of the special fibre**, as the closed immersion `ℙ¹_k ⟶ X`,
`[S₀ : S₁] ↦ [S₀ : S₁ : 0]`. -/
def secondLine : AlgebraicGeometry.Proj (lineGrading κ) ⟶ conicScheme π :=
  Proj.map (lineHom π _ (secondLine_rel hπ) secondLine_lin)
    (Proj.irrelevant_le_map_of_surjective _
      (surjective_lineHom π _ _ _ 0 1 rfl rfl))

/-- The line `C₁` is a closed subscheme of `X`. -/
instance isClosedImmersion_firstLine : IsClosedImmersion (firstLine hπ) :=
  Proj.isClosedImmersion_map_of_surjective' _ (surjective_lineHom π _ _ _ 2 0 rfl rfl)

/-- The line `C₂` is a closed subscheme of `X`. -/
instance isClosedImmersion_secondLine : IsClosedImmersion (secondLine hπ) :=
  Proj.isClosedImmersion_map_of_surjective' _ (surjective_lineHom π _ _ _ 0 1 rfl rfl)

end Lines

/-! ### The two contractions -/

section Contraction

open Stacks.AlgebraicGeometry.ProjBaseChange Stacks.AlgebraicGeometry.ProjPolyChart

variable {R : Type u} [CommRing R] [IsLocalRing R] {π : R} (hπ : π ∈ IsLocalRing.maximalIdeal R)

local notation "κ" => IsLocalRing.ResidueField R

/-- The inclusion of the special fibre `ℙ¹_k ⟶ ℙ¹_R`. -/
abbrev specialFibreMap : projectiveSpaceOverRing 1 (.of κ) ⟶ projectiveSpaceOverRing 1 (.of R) :=
  baseChangeLine (residueSpecMap R)

/-- The `k`-point of `ℙ¹_R` over the closed point determined by `φ`. -/
abbrev pointOver (φ : MvPolynomial (Fin (1 + 1)) (ULift.{u} ℤ) →+* κ) (s : Fin 2)
    (hu : IsUnit (φ (X s))) : Spec (.of κ) ⟶ projectiveSpaceOverRing 1 (.of R) :=
  pullback.lift (residueSpecMap R) (intPointOf φ s hu) (terminal.hom_ext _ _)

/-- The generic point of `ℙ¹_k`, read on the chart `D₊(Sₛ)`. -/
abbrev lineGenericPoint (k : Type u) [Field k] (s : Fin 2) :
    Spec (.of (FractionRing (MvPolynomial (Fin (1 + 1)) k))) ⟶
      AlgebraicGeometry.Proj (lineGrading k) :=
  ProjPoint.point (lineGrading k) (algebraMap _ _) (X s) (X_mem k s) one_pos
    (isUnit_algebraMap_X s)

/-- **Morphisms out of `ℙ¹_k` are determined by the generic point.** -/
theorem line_hom_ext (k : Type u) [Field k] {Z : Scheme.{u}} [IsSeparated (terminal.from Z)]
    {f g : AlgebraicGeometry.Proj (lineGrading k) ⟶ Z} (s : Fin 2)
    (h : lineGenericPoint k s ≫ f = lineGenericPoint k s ≫ g) : f = g := by
  refine ProjPoint.hom_ext_of_point (lineGrading k) (terminal.from _) (terminal.hom_ext _ _)
    (fun i : Fin 2 => (X i : MvPolynomial (Fin (1 + 1)) k)) (X_mem k) (fun _ => one_pos)
    (irrelevant_le_span_X k 1) (algebraMap _ _) (fun i => isUnit_algebraMap_X i)
    (fun i => ProjPoint.injective_awayEval_algebraMap _ _ _) (fun i => ?_)
  rw [ProjPoint.point_indep _ _ (X_mem k i) (X_mem k s) one_pos one_pos
    (isUnit_algebraMap_X i) (isUnit_algebraMap_X s)]
  exact h

/-- A point of `ℙ¹_k` followed by a closed immersion onto a line of the special fibre. -/
theorem point_comp_lineMap (y : Fin 3 → MvPolynomial (Fin (1 + 1)) κ)
    (hy : y 1 * y 2 = (C.comp (IsLocalRing.residue R)) π * y 0 ^ 2)
    (hlin : ∀ i, (y i).IsHomogeneous 1) (hirr) {L : Type u} [CommRing L]
    (φ : MvPolynomial (Fin (1 + 1)) κ →+* L) (s : Fin 2) (t : Fin 3) (ht : y t = X s)
    (hu : IsUnit (φ (X s))) :
    ProjPoint.point (lineGrading κ) φ (X s) (X_mem κ s) one_pos hu ≫
        Proj.map (lineHom π y hy hlin) hirr =
      ProjPoint.point (conicGrading π) (φ.comp (lineHom π y hy hlin :
          MvPolynomial (Fin 3) R ⧸ conicIdeal π →+* MvPolynomial (Fin (1 + 1)) κ))
        (conicCoord π t) (conicCoord_mem π t) one_pos (by
          change IsUnit (φ (conicHom π _ y hy (conicCoord π t)))
          rw [conicHom_coord, ht]; exact hu) := by
  have hX : (X s : MvPolynomial (Fin (1 + 1)) κ) = lineHom π y hy hlin (conicCoord π t) := by
    change _ = conicHom π _ y hy (conicCoord π t)
    rw [conicHom_coord, ht]
  rw [ProjPoint.point_congr _ _ hX _ ((lineHom π y hy hlin).2 (conicCoord_mem π t)) _ _
    (by rw [← hX]; exact hu)]
  exact ProjPoint.point_comp_map _ _ _ _ _ _ _ _

/-- The first and second projections, on the generic point of a line of the special fibre. -/
theorem lineGeneric_values (y : Fin 3 → MvPolynomial (Fin (1 + 1)) κ)
    (hy : y 1 * y 2 = (C.comp (IsLocalRing.residue R)) π * y 0 ^ 2)
    (hlin : ∀ i, (y i).IsHomogeneous 1) (i : Fin 3) :
    ((algebraMap (MvPolynomial (Fin (1 + 1)) κ) (FractionRing (MvPolynomial (Fin (1 + 1)) κ))).comp
      (lineHom π y hy hlin : MvPolynomial (Fin 3) R ⧸ conicIdeal π →+* _)) (conicCoord π i) =
      algebraMap _ _ (y i) := by
  change algebraMap _ _ (conicHom π _ y hy (conicCoord π i)) = _
  rw [conicHom_coord]

/-- The constants of `k[S₀, S₁]`, as degree-zero elements. -/
theorem projZero_C {k : Type u} [Field k] (c : k) :
    algebraMap (lineGrading k 0) (MvPolynomial (Fin (1 + 1)) k)
      (GradedRing.projZeroRingHom' (polyGrading k 1) (algebraMap k _ c)) = C c := by
  change (↑(GradedRing.projZeroRingHom' (polyGrading k 1) (C c)) : MvPolynomial (Fin (1 + 1)) k) =
    C c
  rw [GradedRing.coe_projZeroRingHom'_apply, GradedRing.projZeroRingHom_apply,
    DirectSum.decompose_of_mem_same (polyGrading k 1)
      ((mem_homogeneousSubmodule _ _).2 (isHomogeneous_C _ _))]

/-- **The first projection maps `C₂` isomorphically onto the special fibre of `ℙ¹_R`**: on `C₂` it
is `[S₀ : S₁] ↦ [S₀ : S₁]`. -/
theorem secondLine_comp_firstProjection :
    secondLine hπ ≫ firstProjection π =
      (polynomialComparison κ 1).iso.inv ≫ specialFibreMap := by
  have := isSeparated_terminal_projectiveLine (.of R)
  refine line_hom_ext κ 1 ?_
  rw [lineGenericPoint, ← Category.assoc, secondLine,
    point_comp_lineMap (π := π) ![X 0, X 1, 0] _ _ _ _ 1 1 rfl,
    point_comp_firstProjection, ← Category.assoc, point_comp_iso_inv, lift_comp_baseChangeLine]
  refine pullback.hom_ext ?_ ?_
  · simp only [pullback.lift_fst]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    simp only [RingHom.comp_apply, RingHom.coe_coe, lineHom_C]
    rfl
  · simp only [pullback.lift_snd]
    unfold intPointOf
    rw [ProjPoint.point_congr_ringHom _ (comp_coordinateMap_eq_vecHom _) _ _ _ _
      (by rw [vecHom_X_one]; exact isUnit_algebraMap_X 1)]
    refine point_vecHom_eq_of_mul_eq _ ?_ _ _ _ _
    rw [show firstA π 1 = frac π 1 0 from rfl, show firstB π 1 = 1 from rfl, map_one,
      awayEval_frac_field]
    have h1 := (isUnit_algebraMap_X (K := κ) (σ := Fin (1 + 1)) 1).ne_zero
    simp only [RingHom.comp_apply, RingHom.coe_coe, lineHom_coord, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    field_simp

/-- **The first projection contracts `C₁`** to the point `[1 : 0]` over the closed point. -/
theorem firstLine_comp_firstProjection :
    firstLine hπ ≫ firstProjection π =
      projToSpecCoeff κ 1 ≫
        pointOver (vecHom κ 1 0) 0 (by rw [vecHom_X_zero]; exact isUnit_one) := by
  have := isSeparated_terminal_projectiveLine (.of R)
  refine line_hom_ext κ 0 ?_
  rw [lineGenericPoint, ← Category.assoc, firstLine,
    point_comp_lineMap (π := π) ![X 1, 0, X 0] _ _ _ _ 0 2 rfl,
    point_comp_firstProjection, ← Category.assoc, projToSpecCoeff, ← Category.assoc,
    ProjPoint.point_comp_toSpecZero, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  refine pullback.hom_ext ?_ ?_
  · simp only [pullback.lift_fst, Category.assoc]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    simp only [RingHom.comp_apply, RingHom.coe_coe, lineHom_C, projZero_C]
    rfl
  · simp only [pullback.lift_snd, Category.assoc]
    unfold intPointOf
    refine Eq.trans ?_ (ProjPoint.SpecMap_comp_point _ _ _ _ _ _ _).symm
    refine ProjPoint.point_congr_ringHom _ ?_ _ _ _ _ _
    rw [comp_vecHom, map_one, map_zero, show firstA π 2 = 1 from rfl,
      show firstB π 2 = constEl π 2 * frac π 2 0 from rfl, map_one, map_mul, awayEval_constEl]
    congr 1
    simp only [RingHom.comp_apply, RingHom.coe_coe, conicConst, lineHom_C, residue_eq_zero hπ,
      map_zero, zero_mul]

/-- **The second projection maps `C₁` isomorphically onto the special fibre of `ℙ¹_R`**: on `C₁`
it is `[S₀ : S₁] ↦ [S₀ : S₁]`. -/
theorem firstLine_comp_secondProjection :
    firstLine hπ ≫ secondProjection π =
      (polynomialComparison κ 1).iso.inv ≫ specialFibreMap := by
  have := isSeparated_terminal_projectiveLine (.of R)
  refine line_hom_ext κ 1 ?_
  rw [lineGenericPoint, ← Category.assoc, firstLine,
    point_comp_lineMap (π := π) ![X 1, 0, X 0] _ _ _ _ 1 0 rfl,
    point_comp_secondProjection, ← Category.assoc, point_comp_iso_inv, lift_comp_baseChangeLine]
  refine pullback.hom_ext ?_ ?_
  · simp only [pullback.lift_fst]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    simp only [RingHom.comp_apply, RingHom.coe_coe, lineHom_C]
    rfl
  · simp only [pullback.lift_snd]
    unfold intPointOf
    rw [ProjPoint.point_congr_ringHom _ (comp_coordinateMap_eq_vecHom _) _ _ _ _
      (by rw [vecHom_X_one]; exact isUnit_algebraMap_X 1)]
    refine point_vecHom_eq_of_mul_eq _ ?_ _ _ _ _
    rw [show secondA π 0 = frac π 0 2 from rfl, show secondB π 0 = 1 from rfl, map_one,
      awayEval_frac, Units.val_inv_eq_inv_val, IsUnit.unit_spec]
    have h1 := (isUnit_algebraMap_X (K := κ) (σ := Fin (1 + 1)) 1).ne_zero
    simp only [RingHom.comp_apply, RingHom.coe_coe, lineHom_coord, Matrix.cons_val_zero,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    field_simp

/-- **The second projection contracts `C₂`** to the point `[0 : 1]` over the closed point. -/
theorem secondLine_comp_secondProjection :
    secondLine hπ ≫ secondProjection π =
      projToSpecCoeff κ 1 ≫
        pointOver (vecHom κ 0 1) 1 (by rw [vecHom_X_one]; exact isUnit_one) := by
  have := isSeparated_terminal_projectiveLine (.of R)
  refine line_hom_ext κ 0 ?_
  rw [lineGenericPoint, ← Category.assoc, secondLine,
    point_comp_lineMap (π := π) ![X 0, X 1, 0] _ _ _ _ 0 0 rfl,
    point_comp_secondProjection, ← Category.assoc, projToSpecCoeff, ← Category.assoc,
    ProjPoint.point_comp_toSpecZero, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  refine pullback.hom_ext ?_ ?_
  · simp only [pullback.lift_fst, Category.assoc]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    simp only [RingHom.comp_apply, RingHom.coe_coe, lineHom_C, projZero_C]
    rfl
  · simp only [pullback.lift_snd, Category.assoc]
    unfold intPointOf
    refine Eq.trans ?_ (ProjPoint.SpecMap_comp_point _ _ _ _ _ _ _).symm
    refine ProjPoint.point_congr_ringHom _ ?_ _ _ _ _ _
    rw [comp_vecHom, map_one, map_zero, show secondA π 0 = frac π 0 2 from rfl,
      show secondB π 0 = 1 from rfl, map_one, awayEval_frac]
    simp only [RingHom.comp_apply, RingHom.coe_coe, lineHom_coord, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, map_zero, zero_mul]

end Contraction

end Stacks.Models.GenusZero

end
