module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveLine
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectionFormula
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveLineFibreBasis
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionCycleClass
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.EquidimensionalCorrespondence
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DiagonalDualBasis
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ProjectiveLine
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionGysinFlat
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.NonemptyScheme
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The cohomology of the projective line (Stacks 0FHI)

Let `H^*` be given with the data (D0)–(D3) of Section 0FHA satisfying the axioms (A), (B) and (C),
over a field `k` and with coefficients in a field `F` of characteristic zero
(`Stacks.WeilCohomology.WeilData`). Then `H^*(𝐏¹_k)` is one dimensional in degrees `0` and `2`
and zero in every other degree. Here `𝐏¹_k` is the actual projective line
`Stacks.WeilCohomology.projectiveLineObj k`.

The proof runs as follows:

* `[Δ] = pr₁^![∞] + pr₂^![∞]` in `CH¹(𝐏¹_k × 𝐏¹_k)`: the Gysin pullback of the point `∞` along
  the flat projections is the class of the fibres `∞ × 𝐏¹` and `𝐏¹ × ∞`
  (`codimensionGysin_fst_pointInfinity`, from Stacks 0FF4 and 02RB through
  `Stacks.Chow.codimensionGysin_closedSubschemeClass_of_flat`), and `[Δ] = [∞ × 𝐏¹] + [𝐏¹ × ∞]`
  in `CH₁(𝐏¹_k × 𝐏¹_k)` (`Stacks.WeilCohomology.diagonal_cycle_eq_add_fibres`);
* hence, by axiom (C)(a) and additivity of `γ`, `γ([Δ]) = pr₁^*γ([∞]) + pr₂^*γ([∞])`, whose
  Künneth decomposition is `γ([∞]) ⊗ 1 + 1 ⊗ γ([∞])` (`diagonalClassProjectiveLine_eq`);
* by Lemma 0FHH the `(i, 2 - i)` Künneth component of `γ([Δ])` is `∑_j e_j ⊗ e'_j` for a basis
  `e` of `H^i(𝐏¹_k)` and a linearly independent family `e'`, so `dim H^i(𝐏¹_k) ≤ 1` for
  `i = 0, 2` and `H^i(𝐏¹_k) = 0` otherwise (`finrank_grade_projectiveLineObj_le`);
* `H^0(𝐏¹_k) ≠ 0` by Lemma 0FHF and `dim H^0 = dim H^2` by axiom (A)(b).

## Main results

* `Stacks.WeilCohomology.WeilData.cohomology_projectiveLineObj` — **Stacks 0FHI.**
* `Stacks.WeilCohomology.WeilData.finrank_grade_projectiveLineObj` — the same, degree by degree.
* `Stacks.WeilCohomology.closedSubschemeClass_diagonal_eq_add` — `[Δ] = [x × 𝐏¹] + [𝐏¹ × x]` in
  `CH¹(𝐏¹_k × 𝐏¹_k)` for a rational point `x`.
* `Stacks.WeilCohomology.WeilData.codimensionGysin_fst_pointInfinity`,
  `Stacks.WeilCohomology.WeilData.codimensionGysin_snd_pointInfinity` — `pr₁^![∞] = [∞ × 𝐏¹]`
  and `pr₂^![∞] = [𝐏¹ × ∞]`.

## References

* [Stacks Project, Tag 0FHI](https://stacks.math.columbia.edu/tag/0FHI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow
open scoped TensorProduct

universe u w

namespace Stacks.WeilCohomology

section Diagonal

variable {k : Type u} [Field k]

local notation "ℙ" => relativeProjectiveLine (Spec (CommRingCat.of k))

local notation "σ" => (ℙ ↘ Spec (CommRingCat.of k))

local notation "σ₂" => pullback.fst σ σ ≫ σ

attribute [local instance] isClosedImmersion_graphMorphism

/-- **`[Δ] = [x × 𝐏¹] + [𝐏¹ × x]` in `CH¹(𝐏¹_k × 𝐏¹_k)`**, the codimension-graded form of the
identity of divisors `Δ = pr₁^*x + pr₂^*x` of the proof of Lemma 0FHI, for a rational point `x`.
`𝐏¹_k × 𝐏¹_k` is equidimensional of dimension `2`, so `CH¹` is `CH₁` on its part of dimension `2`
and vanishes on the other parts. -/
theorem closedSubschemeClass_diagonal_eq_add (x : (fieldChowSituation k).S ⟶ ℙ)
    (hx : x ≫ σ = 𝟙 (fieldChowSituation k).S) (h2 : AlgebraicGeometry.RelativeDimension σ₂ 2) :
    closedSubschemeClass σ₂ (pullback.diagonal σ) 1 =
      closedSubschemeClass σ₂ (pointFibreEmbedding x hx) 1 +
        closedSubschemeClass σ₂ (fibrePointEmbedding x hx) 1 := by
  funext e
  by_cases he : e = 2
  · subst he
    rw [Pi.add_apply, closedSubschemeClass_apply, closedSubschemeClass_apply,
      closedSubschemeClass_apply, ← map_add]
    congr 1
    exact diagonal_cycle_eq_add_fibres x hx
  · have := isEmpty_dimPart_of_ne σ₂ h2 he
    have := subsingleton_chowGroup_of_isEmpty (fieldChowSituation k) (partBase σ₂ e)
      ((e : ℤ) - 1)
    exact Subsingleton.elim _ _

end Diagonal

end Stacks.WeilCohomology

namespace Stacks.WeilCohomology.WeilData

variable {k : Type u} [Field k] {F : Type w} [Field F] {W : WeilData k F}

/-- **Poincaré duality on `𝐏¹_k`**: `H^0(𝐏¹_k)` and `H^2(𝐏¹_k)` have the same dimension, the
pairing `H^0(𝐏¹_k) × H^2(𝐏¹_k)(1) → F` being perfect (axiom (A)(b)). -/
theorem finrank_grade_projectiveLineObj_zero_eq_two (hA : W.PoincareDuality) :
    Module.finrank F (W.grade (projectiveLineObj k) 0) =
      Module.finrank F (W.grade (projectiveLineObj k) 2) := by
  have hP := isNonemptyEquidimensional_projectiveLineObj k
  have := hA.finiteDimensionality _ 1 hP 0
  have := hA.finiteDimensionality _ 1 hP 2
  have : FiniteDimensional F (W.Tw (projectiveLineObj k) 2 1) :=
    LinearEquiv.finiteDimensional (W.twCoord (projectiveLineObj k) 2 1).symm
  have h02 : (0 : ℤ) + 2 = 2 * ((1 : ℕ) : ℤ) := by norm_num
  have := hA.perfectPairing _ 1 hP 0 2 h02
  exact (Module.finrank_of_isPerfPair (W.pairing (projectiveLineObj k) 1 hP 0 2 h02)).trans
    (W.twCoord (projectiveLineObj k) 2 1).finrank_eq

/-! ### Künneth components of pulled back classes -/

section Components

variable (hBa : W.KunnethIsomorphism) (X : (SmoothProjectiveScheme k).FullSubcategory)

/-- `pr₁^*a = a ⊗ 1` in Künneth coordinates. -/
theorem kunnethComponent_pull_fst (p q : ℤ) (a : W.H X) :
    kunnethComponent X hBa p q (W.pull (SmoothProjectiveScheme.fst X X) a) =
      bidegreeComponent X p q (a ⊗ₜ 1) := by
  rw [← kunnethComponent_kunnethMap X hBa, kunnethMap_tmul, map_one, mul_one]

/-- `pr₂^*b = 1 ⊗ b` in Künneth coordinates. -/
theorem kunnethComponent_pull_snd (p q : ℤ) (b : W.H X) :
    kunnethComponent X hBa p q (W.pull (SmoothProjectiveScheme.snd X X) b) =
      bidegreeComponent X p q (1 ⊗ₜ b) := by
  rw [← kunnethComponent_kunnethMap X hBa, kunnethMap_tmul, map_one, one_mul]

/-- The twisted Künneth component, read in coordinates on the second factor. -/
abbrev kunnethComponentTwCoord (n m i j : ℤ) :
    W.Tw (SmoothProjectiveScheme.prod X X) n m →ₗ[F] W.grade X i ⊗[F] W.grade X j :=
  (TensorProduct.map LinearMap.id (W.twCoord X j m).toLinearMap).comp
    (kunnethComponentTw X hBa n m i j)

/-- The `(i, j)` twisted Künneth component of `z`, read in coordinates, is the `(i, j)` Künneth
component of the untwisted class `W.twCoord _ n m z`. -/
theorem kunnethComponentTwCoord_apply (n m i j : ℤ)
    (z : W.Tw (SmoothProjectiveScheme.prod X X) n m) :
    kunnethComponentTwCoord hBa X n m i j z =
      kunnethComponent X hBa i j (W.twCoord _ n m z : W.H (SmoothProjectiveScheme.prod X X)) :=
  map_twCoord_kunnethComponentTw X hBa n m i j z

end Components

/-! ### The tensor-rank bound -/

section Bound

variable (hA : W.PoincareDuality) (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing)

/-- The class `γ([Δ]) ∈ H²(𝐏¹ × 𝐏¹)(1)` of the diagonal of `𝐏¹_k`. -/
abbrev diagonalClassProjectiveLine (W : WeilData k F) :
    W.Tw (SmoothProjectiveScheme.prod (projectiveLineObj k) (projectiveLineObj k))
      (2 * ((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ) :=
  W.cycleClass (SmoothProjectiveScheme.prod (projectiveLineObj k) (projectiveLineObj k)) (1 : ℕ)
    (closedSubschemeClass
      (SmoothProjectiveScheme.prod (projectiveLineObj k) (projectiveLineObj k)).obj.hom
      (SmoothProjectiveScheme.diag (projectiveLineObj k)).hom.left (1 : ℕ))

include hB hC in
/-- **The tensor-rank bound of Lemma 0FHI.** If `γ([Δ]) = pr₁^*c + pr₂^*c` for a class
`c ∈ H²(𝐏¹_k)(1)`, then `dim H^i(𝐏¹_k) ≤ 1` for `i = 0, 2` and `H^i(𝐏¹_k) = 0` otherwise: by
Lemma 0FHH the `(i, 2 - i)` Künneth component of `γ([Δ])` is `∑_j e_j ⊗ e'_j` for a basis `e` of
`H^i(𝐏¹_k)` with `e'` linearly independent, while the component of `c ⊗ 1 + 1 ⊗ c` is a single
pure tensor for `i = 0, 2` and zero otherwise. -/
theorem finrank_grade_projectiveLineObj_le
    (c : W.Tw (projectiveLineObj k) (2 * ((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ))
    (hΔ : diagonalClassProjectiveLine W =
      W.pullTw (SmoothProjectiveScheme.fst (projectiveLineObj k) (projectiveLineObj k)) _ _ c +
        W.pullTw (SmoothProjectiveScheme.snd (projectiveLineObj k) (projectiveLineObj k)) _ _ c)
    (i : ℤ) :
    Module.finrank F (W.grade (projectiveLineObj k) i) ≤ if i = 0 ∨ i = 2 then 1 else 0 := by
  classical
  let X := projectiveLineObj k
  have hX := isNonemptyEquidimensional_projectiveLineObj k
  have hBa := hB.kunnethIsomorphism
  have := hA.finiteDimensionality X 1 hX i
  set e := Module.finBasis F (W.grade X i)
  set e' := W.diagonalKunnethCoordinates hBa X 1 i e
  have hli : LinearIndependent F
      (fun j ↦ W.twCoord X (2 * ((1 : ℕ) : ℤ) - i) ((1 : ℕ) : ℤ) (e' j)) := by
    refine LinearIndependent.map' ?_ _ (W.twCoord X _ _).ker
    refine linearIndependent_of_pairing_eq_single
      (W.pairing X 1 hX i (2 * ((1 : ℕ) : ℤ) - i) (by ring)) e e'
      (fun _ ↦ ((i.negOnePow : ℤ) : F)) (fun _ ↦ ?_) (fun j j' ↦ ?_)
    · rcases Int.isUnit_iff.mp (i.negOnePow).isUnit with h | h <;> simp [h]
    · rw [pairing_diagonalKunnethCoordinates hX hA hB hC i e j j']
      split_ifs <;> simp
  have hsum := congrArg (TensorProduct.map LinearMap.id
    (W.twCoord X (2 * ((1 : ℕ) : ℤ) - i) ((1 : ℕ) : ℤ)).toLinearMap)
    (kunnethComponentTw_diagonal_eq_sum (X := X) (d := 1) hBa i e)
  rw [map_twCoord_kunnethComponentTw, map_sum] at hsum
  simp only [TensorProduct.map_tmul, LinearMap.id_apply, LinearEquiv.coe_coe] at hsum
  change kunnethComponent X hBa i _ ((W.twCoord _ _ _ (diagonalClassProjectiveLine W) :
    W.H (SmoothProjectiveScheme.prod X X))) = _ at hsum
  rw [hΔ, map_add, Submodule.coe_add, twCoord_pullTw, twCoord_pullTw, coe_pullDeg, coe_pullDeg,
    map_add, kunnethComponent_pull_fst, kunnethComponent_pull_snd] at hsum
  set c' := W.twCoord X _ _ c
  have h1 : (1 : W.H X) ∈ W.grade X 0 := SetLike.GradedOne.one_mem
  have hc' : (c' : W.H X) ∈ W.grade X 2 := by simp
  by_cases h2 : i = 2
  · subst h2
    have h1' : (1 : W.H X) ∈ W.grade X (2 * ((1 : ℕ) : ℤ) - 2) := by simpa using h1
    rw [bidegreeComponent_tmul_self X hc' h1',
      bidegreeComponent_tmul_of_ne X h1 c'.2 (by simp)] at hsum
    have hle := finrank_le_card_of_sum_tmul_eq_sum_tmul e _ hli (M := Unit)
      (fun _ ↦ ⟨c', hc'⟩) (fun _ ↦ ⟨1, h1'⟩) (by rw [← hsum]; simp)
    simpa using hle
  by_cases h0 : i = 0
  · subst h0
    have hc'' : (c' : W.H X) ∈ W.grade X (2 * ((1 : ℕ) : ℤ) - 0) := by simp
    rw [bidegreeComponent_tmul_of_ne X hc' h1 (by simp),
      bidegreeComponent_tmul_self X h1 hc''] at hsum
    have hle := finrank_le_card_of_sum_tmul_eq_sum_tmul e _ hli (M := Unit)
      (fun _ ↦ ⟨1, h1⟩) (fun _ ↦ ⟨c', hc''⟩) (by rw [← hsum]; simp)
    simpa using hle
  · rw [bidegreeComponent_tmul_of_ne X hc' h1 (by simp [Ne.symm h2]),
      bidegreeComponent_tmul_of_ne X h1 c'.2 (by simp [Ne.symm h0]), add_zero] at hsum
    have hle := finrank_le_card_of_sum_tmul_eq_sum_tmul e _ hli (M := Empty)
      (fun m ↦ m.elim) (fun m ↦ m.elim) (by rw [← hsum]; simp)
    simpa [h0, h2] using hle

end Bound

/-! ### The cohomology of `𝐏¹_k` -/

/-- The rational point `∞` of `𝐏¹_k`. -/
abbrev pointInfinity (k : Type u) [Field k] :
    (fieldChowSituation k).S ⟶ relativeProjectiveLine (Spec (CommRingCat.of k)) :=
  lineInfinitySection (Spec (CommRingCat.of k))

/-- `∞` is a section of the structure morphism `𝐏¹_k → Spec k`. -/
theorem pointInfinity_comp (k : Type u) [Field k] :
    pointInfinity k ≫ (relativeProjectiveLine (Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) =
      𝟙 (fieldChowSituation k).S :=
  lineInfinitySection_comp _

/-- The point `∞` is a closed immersion into `𝐏¹_k`. -/
@[ega "II 7.4.14" "partial"]
instance isClosedImmersion_pointInfinity (k : Type u) [Field k] :
    IsClosedImmersion (pointInfinity k) :=
  isClosedImmersion_lineConstantSection _ _

/-- The fibre `∞ × 𝐏¹ ⊂ 𝐏¹ × 𝐏¹`, `y ↦ (∞, y)`, as a morphism of smooth projective schemes. -/
def pointFibreHom (k : Type u) [Field k] :
    projectiveLineObj k ⟶ SmoothProjectiveScheme.prod (projectiveLineObj k)
        (projectiveLineObj k) :=
  ObjectProperty.homMk (Over.homMk (pointFibreEmbedding (pointInfinity k) (pointInfinity_comp k))
    (pointFibreEmbedding_comp _ _))

/-- The fibre `𝐏¹ × ∞ ⊂ 𝐏¹ × 𝐏¹`, `y ↦ (y, ∞)`, as a morphism of smooth projective schemes. -/
def fibrePointHom (k : Type u) [Field k] :
    projectiveLineObj k ⟶ SmoothProjectiveScheme.prod (projectiveLineObj k)
        (projectiveLineObj k) :=
  ObjectProperty.homMk (Over.homMk (fibrePointEmbedding (pointInfinity k) (pointInfinity_comp k))
    (fibrePointEmbedding_comp _ _))

/-- The fibre `∞ × 𝐏¹ → 𝐏¹ × 𝐏¹` is a closed immersion. -/
instance isClosedImmersion_pointFibreHom (k : Type u) [Field k] :
    IsClosedImmersion (pointFibreHom k).hom.left :=
  isClosedImmersion_graphMorphism _ _ _
    (constantMorphism_comp_base _ (pointInfinity k) (pointInfinity_comp k))

/-- The fibre `𝐏¹ × ∞ → 𝐏¹ × 𝐏¹` is a closed immersion. -/
instance isClosedImmersion_fibrePointHom (k : Type u) [Field k] :
    IsClosedImmersion (fibrePointHom k).hom.left := by
  have : IsClosedImmersion (pointFibreEmbedding (pointInfinity k) (pointInfinity_comp k)) :=
    isClosedImmersion_graphMorphism _ _ _
      (constantMorphism_comp_base _ (pointInfinity k) (pointInfinity_comp k))
  exact IsClosedImmersion.comp _ (pullbackSymmetry
      (relativeProjectiveLine (Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))
      (relativeProjectiveLine (Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))).hom

/-- The fibre `∞ × 𝐏¹` is the scheme-theoretic fibre of the first projection over `∞`. -/
theorem isPullback_pointFibreHom (k : Type u) [Field k] :
    IsPullback (pointFibreHom k).hom.left (projectiveLineObj k).obj.hom
      (SmoothProjectiveScheme.fst (projectiveLineObj k) (projectiveLineObj k)).hom.left
      (pointInfinity k) := by
  have hx := pointInfinity_comp k
  set σ := (relativeProjectiveLine (Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))
  change IsPullback (graphMorphism σ σ (σ ≫ pointInfinity k)
    (constantMorphism_comp_base σ (pointInfinity k) hx)) σ (pullback.fst σ σ) (pointInfinity k)
  refine IsPullback.of_right (h₁₂ := pullback.snd σ σ) (h₂₂ := σ) (v₁₃ := σ) ?_
    (graphMorphism_fst _ _ _ _) (IsPullback.of_hasPullback σ σ).flip
  rw [graphMorphism_snd, hx]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

/-- The fibre `𝐏¹ × ∞` is the scheme-theoretic fibre of the second projection over `∞`. -/
theorem isPullback_fibrePointHom (k : Type u) [Field k] :
    IsPullback (fibrePointHom k).hom.left (projectiveLineObj k).obj.hom
      (SmoothProjectiveScheme.snd (projectiveLineObj k) (projectiveLineObj k)).hom.left
      (pointInfinity k) := by
  have hx := pointInfinity_comp k
  set σ := (relativeProjectiveLine (Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))
  change IsPullback (graphMorphism σ σ (σ ≫ pointInfinity k)
      (constantMorphism_comp_base σ (pointInfinity k) hx) ≫ (pullbackSymmetry σ σ).hom) σ
    (pullback.snd σ σ) (pointInfinity k)
  refine IsPullback.of_right (h₁₂ := pullback.fst σ σ) (h₂₂ := σ) (v₁₃ := σ) ?_
    (by rw [Category.assoc, pullbackSymmetry_hom_comp_snd, graphMorphism_fst])
    (IsPullback.of_hasPullback σ σ)
  rw [Category.assoc, pullbackSymmetry_hom_comp_fst, graphMorphism_snd, hx]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

/-- The point `∞` of `𝐏¹_k` has delta-dimension zero. -/
theorem schemeDeltaDimension_pointInfinity (k : Type u) [Field k] :
    schemeDeltaDimension (fieldChowSituation k) (pointInfinity k ≫ (projectiveLineObj k).obj.hom) ≤
      ((((1 : ℕ) : ℤ) - ((1 : ℕ) : ℤ) : ℤ) : EInt) := by
  have h : pointInfinity k ≫ (projectiveLineObj k).obj.hom = 𝟙 (fieldChowSituation k).S :=
    pointInfinity_comp k
  simp only [h, sub_self]
  exact schemeDeltaDimension_id_le_zero (fieldChowSituation k) (fun _ ↦ rfl)

/-- The first projection `𝐏¹_k × 𝐏¹_k → 𝐏¹_k` is smooth. -/
instance smooth_fst_projectiveLineObj (k : Type u) [Field k] :
    Smooth (SmoothProjectiveScheme.fst (projectiveLineObj k) (projectiveLineObj k)).hom.left :=
  show Smooth (pullback.fst (projectiveLineObj k).obj.hom (projectiveLineObj k).obj.hom) from
    inferInstance

/-- The second projection `𝐏¹_k × 𝐏¹_k → 𝐏¹_k` is smooth. -/
instance smooth_snd_projectiveLineObj (k : Type u) [Field k] :
    Smooth (SmoothProjectiveScheme.snd (projectiveLineObj k) (projectiveLineObj k)).hom.left :=
  show Smooth (pullback.snd (projectiveLineObj k).obj.hom (projectiveLineObj k).obj.hom) from
    inferInstance

/-- The first projection `𝐏¹_k × 𝐏¹_k → 𝐏¹_k` has relative dimension one. -/
theorem relativeDimension_fst_projectiveLineObj (k : Type u) [Field k] :
    AlgebraicGeometry.RelativeDimension
      (SmoothProjectiveScheme.fst (projectiveLineObj k) (projectiveLineObj k)).hom.left 1 :=
  AlgebraicGeometry.RelativeDimension.of_isPullback
    (IsPullback.of_hasPullback (projectiveLineObj k).obj.hom (projectiveLineObj k).obj.hom).flip
    (relativeDimension_relativeProjectiveLine_spec k)

/-- The second projection `𝐏¹_k × 𝐏¹_k → 𝐏¹_k` has relative dimension one. -/
theorem relativeDimension_snd_projectiveLineObj (k : Type u) [Field k] :
    AlgebraicGeometry.RelativeDimension
      (SmoothProjectiveScheme.snd (projectiveLineObj k) (projectiveLineObj k)).hom.left 1 :=
  AlgebraicGeometry.RelativeDimension.of_isPullback
    (IsPullback.of_hasPullback (projectiveLineObj k).obj.hom (projectiveLineObj k).obj.hom)
    (relativeDimension_relativeProjectiveLine_spec k)

/-- The Gysin map of a flat projection of `𝐏¹_k × 𝐏¹_k` carries `[∞]` to the class of the
fibre over `∞`. -/
private theorem codimensionGysin_pointInfinity_eq_of_isPullback (k : Type u) [Field k]
    (p : SmoothProjectiveScheme.prod (projectiveLineObj k) (projectiveLineObj k) ⟶
      projectiveLineObj k)
    (f : projectiveLineObj k ⟶ SmoothProjectiveScheme.prod (projectiveLineObj k)
      (projectiveLineObj k)) [IsClosedImmersion f.hom.left] [Flat p.hom.left]
    (hp : AlgebraicGeometry.RelativeDimension p.hom.left 1)
    (hf : IsPullback f.hom.left (projectiveLineObj k).obj.hom p.hom.left (pointInfinity k)) :
    codimensionGysin
        (SmoothProjectiveScheme.prod (projectiveLineObj k) (projectiveLineObj k)).obj.hom
        (projectiveLineObj k).obj.hom (Over.w p.hom)
        ((1 : ℕ) : ℤ) (closedSubschemeClass (projectiveLineObj k).obj.hom (pointInfinity k)
          ((1 : ℕ) : ℤ)) =
      closedSubschemeClass
        (SmoothProjectiveScheme.prod (projectiveLineObj k) (projectiveLineObj k)).obj.hom
        f.hom.left ((1 : ℕ) : ℤ) := by
  have hP := isNonemptyEquidimensional_projectiveLineObj k
  rw [codimensionGysin_closedSubschemeClass_of_flat _ _ _
    (SmoothProjectiveScheme.isNonemptyEquidimensional_prod hP hP).relativeDimension
    hP.relativeDimension hp rfl (pointInfinity k) _ (schemeDeltaDimension_pointInfinity k)]
  funext e
  rw [closedSubschemeClass_apply, closedSubschemeClass_apply,
    cycleAssociatedToClosedSubscheme_eq_of_iso _ _ _ _ hf.isoPullback hf.isoPullback_hom_fst]

/-- **`pr₁^![∞] = [∞ × 𝐏¹]`** in `CH¹(𝐏¹_k × 𝐏¹_k)`: the Gysin map of the flat projection carries
the class of the point to the class of its fibre. -/
theorem codimensionGysin_fst_pointInfinity (k : Type u) [Field k] :
    codimensionGysin
        (SmoothProjectiveScheme.prod (projectiveLineObj k) (projectiveLineObj k)).obj.hom
        (projectiveLineObj k).obj.hom
        (Over.w (SmoothProjectiveScheme.fst (projectiveLineObj k) (projectiveLineObj k)).hom)
        ((1 : ℕ) : ℤ) (closedSubschemeClass (projectiveLineObj k).obj.hom (pointInfinity k)
          ((1 : ℕ) : ℤ)) =
      closedSubschemeClass
        (SmoothProjectiveScheme.prod (projectiveLineObj k) (projectiveLineObj k)).obj.hom
        (pointFibreHom k).hom.left ((1 : ℕ) : ℤ) :=
  codimensionGysin_pointInfinity_eq_of_isPullback k _ _ (relativeDimension_fst_projectiveLineObj k)
    (isPullback_pointFibreHom k)

/-- **`pr₂^![∞] = [𝐏¹ × ∞]`** in `CH¹(𝐏¹_k × 𝐏¹_k)`. -/
theorem codimensionGysin_snd_pointInfinity (k : Type u) [Field k] :
    codimensionGysin
        (SmoothProjectiveScheme.prod (projectiveLineObj k) (projectiveLineObj k)).obj.hom
        (projectiveLineObj k).obj.hom
        (Over.w (SmoothProjectiveScheme.snd (projectiveLineObj k) (projectiveLineObj k)).hom)
        ((1 : ℕ) : ℤ) (closedSubschemeClass (projectiveLineObj k).obj.hom (pointInfinity k)
          ((1 : ℕ) : ℤ)) =
      closedSubschemeClass
        (SmoothProjectiveScheme.prod (projectiveLineObj k) (projectiveLineObj k)).obj.hom
        (fibrePointHom k).hom.left ((1 : ℕ) : ℤ) :=
  codimensionGysin_pointInfinity_eq_of_isPullback k _ _ (relativeDimension_snd_projectiveLineObj k)
    (isPullback_fibrePointHom k)

section Main

variable (hA : W.PoincareDuality) (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing)

include hC in
/-- `γ([Δ]) = pr₁^*γ([∞]) + pr₂^*γ([∞])` in `H²(𝐏¹_k × 𝐏¹_k)(1)`: the identity
`[Δ] = pr₁^![∞] + pr₂^![∞]` of `CH¹(𝐏¹_k × 𝐏¹_k)` (the fibres `∞ × 𝐏¹` and `𝐏¹ × ∞` being the
Gysin pullbacks of the point) and axiom (C)(a). -/
theorem diagonalClassProjectiveLine_eq :
    diagonalClassProjectiveLine W =
      W.pullTw (SmoothProjectiveScheme.fst (projectiveLineObj k) (projectiveLineObj k)) _ _
          (W.cycleClass (projectiveLineObj k) ((1 : ℕ) : ℤ)
            (closedSubschemeClass (projectiveLineObj k).obj.hom (pointInfinity k)
              ((1 : ℕ) : ℤ))) +
        W.pullTw (SmoothProjectiveScheme.snd (projectiveLineObj k) (projectiveLineObj k)) _ _
          (W.cycleClass (projectiveLineObj k) ((1 : ℕ) : ℤ)
            (closedSubschemeClass (projectiveLineObj k).obj.hom (pointInfinity k)
              ((1 : ℕ) : ℤ))) := by
  have hP := isNonemptyEquidimensional_projectiveLineObj k
  have h2 := (SmoothProjectiveScheme.isNonemptyEquidimensional_prod hP hP).relativeDimension
  rw [diagonalClassProjectiveLine, ← hC.pullback, ← hC.pullback,
    codimensionGysin_fst_pointInfinity, codimensionGysin_snd_pointInfinity, ← map_add]
  congr 1
  exact closedSubschemeClass_diagonal_eq_add (pointInfinity k) (pointInfinity_comp k) h2

include hB hC in
/-- **Stacks Project, Tag 0FHI**, degree by degree: for a Weil cohomology theory in the sense of
Section 0FHA, `dim_F H^i(𝐏¹_k)` is `1` for `i = 0, 2` and `0` otherwise. -/
@[stacks 0FHI "dim_F H^i(P¹_k) = 1 for i = 0, 2 and 0 otherwise, for the actual P¹_k and the \
data (D0)–(D3) satisfying (A), (B), (C); the diagonal identity and H^0 ≠ 0 are derived"]
theorem finrank_grade_projectiveLineObj [CharZero F] (i : ℤ) :
    Module.finrank F (W.grade (projectiveLineObj k) i) = if i = 0 ∨ i = 2 then 1 else 0 := by
  have hP := isNonemptyEquidimensional_projectiveLineObj k
  have hle := finrank_grade_projectiveLineObj_le hA hB hC _ (diagonalClassProjectiveLine_eq hA hC)
  have h02 := finrank_grade_projectiveLineObj_zero_eq_two hA (k := k) (W := W)
  have : Nonempty (projectiveLineObj k).obj.left := hP.nonempty
  have := nontrivial_of_nonempty hA hB hC (projectiveLineObj k)
  have hpos : 0 < Module.finrank F (W.grade (projectiveLineObj k) 0) := by
    have := hA.finiteDimensionality _ 1 hP 0
    refine Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨1, SetLike.GradedOne.one_mem⟩, ?_⟩
    exact fun h ↦ one_ne_zero (congrArg Subtype.val h)
  have h0 := hle 0
  have h2 := hle 2
  simp only [true_or, or_true, ite_true] at h0 h2
  by_cases hi : i = 0 ∨ i = 2
  · rw [ite_eq_left hi]
    rcases hi with rfl | rfl <;> omega
  · rw [ite_eq_right hi]
    have := hle i
    rw [ite_eq_right hi] at this
    omega

include hB hC in
/-- **Stacks Project, Tag 0FHI.** For a Weil cohomology theory in the sense of Section 0FHA — data
(D0)–(D3) satisfying (A), (B) and (C), over a field `k`, with coefficients in a field `F` of
characteristic zero — `H^*(𝐏¹_k)` is one dimensional in degrees `0` and `2` and zero in every
other degree. -/
@[stacks 0FHI "H^*(P¹_k) is 1-dimensional in degrees 0 and 2 and zero in other degrees, for the \
actual P¹_k and the data (D0)–(D3) satisfying (A), (B), (C)"]
theorem cohomology_projectiveLineObj [CharZero F] :
    Module.finrank F (W.grade (projectiveLineObj k) 0) = 1 ∧
      Module.finrank F (W.grade (projectiveLineObj k) 2) = 1 ∧
      ∀ i : ℤ, i ≠ 0 → i ≠ 2 → W.grade (projectiveLineObj k) i = ⊥ := by
  have hP := isNonemptyEquidimensional_projectiveLineObj k
  refine ⟨by simpa using finrank_grade_projectiveLineObj hA hB hC 0,
    by simpa using finrank_grade_projectiveLineObj hA hB hC 2, fun i h0 h2 ↦ ?_⟩
  have := hA.finiteDimensionality _ 1 hP i
  have h := finrank_grade_projectiveLineObj hA hB hC i
  rw [ite_eq_right (by tauto)] at h
  exact Submodule.finrank_eq_zero.mp h

end Main

end Stacks.WeilCohomology.WeilData

end
