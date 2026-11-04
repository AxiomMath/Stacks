module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineLine
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.BaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.Unconditional
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerStructureSheafClass
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ProductOfPuncturedSchemes
public import StacksFrontier.AlgebraicGeometry.Chow.DominantPrimeCycle
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.GlobalTop
public import Mathlib.RingTheory.TensorProduct.Free
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.PointSectionCartier
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.ProductRegular
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveLineDivisorDegree.Infinity
public import
  StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ProjectiveLineDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ProjectiveLineIntegral
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.ProjectiveLineAlgebra

/-!
# The fibre classes of a rational point form a basis of `CH₁(P¹ × P¹)`

Let `k` be a field, `X = P¹_k` and `x ∈ X` a `k`-rational point. The degrees of the pushforwards
along the two projections identify `A₁(X × X)` with `ℤ²`, and the two fibre classes `c₀ = [x × X]`
and `c₂ = [X × x]` form a basis of `CH₁(X × X)` over `ℤ` and of `CH₁(X × X) ⊗ ℚ` over `ℚ`.

## Main definitions

* `Stacks.WeilCohomology.fibreCoordinates`: the degrees of the pushforwards of a one-cycle class
  along the second and the first projection.
* `Stacks.WeilCohomology.chowGroupProjectiveLineSquareEquiv`: the isomorphism
  `A₁(P¹_k × P¹_k) ≃+ ℤ × ℤ`.
* `Stacks.WeilCohomology.projectiveLineFibreBasisInt`: the basis of `A₁(P¹_k × P¹_k)` over `ℤ`
  given by the fibre classes.
* `Stacks.WeilCohomology.projectiveLineFibreBasis`: the basis of `CH₁(P¹_k × P¹_k) ⊗ ℚ` over `ℚ`
  given by the fibre classes.

## Main results

* `Stacks.WeilCohomology.exists_eq_zsmul_add_zsmul_infinity`: the fibres at infinity span
  `A₁(P¹_k × P¹_k)`.
* `Stacks.WeilCohomology.fibreCoordinates_bijective`: the fibre coordinates are bijective.
* `Stacks.WeilCohomology.diagonal_cycle_eq_add_fibres`: `[Δ] = [x × P¹] + [P¹ × x]`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.WeilCohomology

section Line

variable (k : Type u) [Field k]

/-- The projective line `P¹_k`. -/
local notation "ℙ" => relativeProjectiveLine (Spec (CommRingCat.of k))

/-- The structure morphism of `P¹_k`. -/
local notation "σ" => (ℙ ↘ Spec (CommRingCat.of k))


/-! ### The points of the projective line -/

/-- The generic point of `P¹_k` has relative dimension one over `k`. -/
theorem relativeDimension_projectiveLine_genericPoint :
    relativeDimension (fieldChowSituation k).dimensionFunction σ
      (genericPoint ℙ) = 1 := by
  rw [relativeDimension_relativeProjectiveLine_genericPoint (CommRingCat.of k),
    fieldChowSituation_dimensionFunction, zero_add]

/-- A point of `P¹_k` other than the generic point has relative dimension less than one. -/
theorem relativeDimension_projectiveLine_lt {y : ℙ}
    (hy : y ≠ genericPoint (ℙ)) :
    relativeDimension (fieldChowSituation k).dimensionFunction σ y < 1 := by
  rw [← relativeDimension_projectiveLine_genericPoint k]
  exact relativeDimension_lt_of_mem_closure_of_ne (fieldChowSituation k) σ
    (specializes_iff_mem_closure.mp (genericPoint_specializes y)) hy

/-- Every point of `P¹_k` has relative dimension at most one. -/
theorem relativeDimension_projectiveLine_le (y : ℙ) :
    relativeDimension (fieldChowSituation k).dimensionFunction σ y ≤ 1 := by
  by_cases hy : y = genericPoint (ℙ)
  · rw [hy, relativeDimension_projectiveLine_genericPoint]
  · exact (relativeDimension_projectiveLine_lt k hy).le

/-- The only point of `P¹_k` of relative dimension one is the generic point. -/
theorem eq_genericPoint_of_relativeDimension_projectiveLine {y : ℙ}
    (hy : relativeDimension (fieldChowSituation k).dimensionFunction σ y = 1) :
    y = genericPoint (ℙ) := by
  by_contra h
  exact (relativeDimension_projectiveLine_lt k h).ne hy

/-- A rational point of `P¹_k` has relative dimension zero. -/
theorem relativeDimension_projectiveLine_section (x : (fieldChowSituation k).S ⟶ ℙ)
    (hx : x ≫ σ = 𝟙 (fieldChowSituation k).S) (p : (fieldChowSituation k).S) :
    relativeDimension (fieldChowSituation k).dimensionFunction σ (x.base p) = 0 :=
  relativeDimension_eq_zero_of_residueDegree_ne_zero _ (fun _ ↦ rfl) σ _
    (by rw [(residueDegree_eq_one_of_section σ x hx p).1]; exact one_ne_zero)

/-- There are no rational equivalences between one-cycles on `P¹_k`. -/
theorem rationalEquivalences_projectiveLine_one :
    rationalEquivalences (fieldChowSituation k) σ 1 = ⊥ :=
  rationalEquivalences_eq_bot_of_relativeDimension_le (fieldChowSituation k) σ 1
    (relativeDimension_projectiveLine_le k)

/-- The coefficient at the generic point, `A₁(P¹_k) → ℤ`. -/
def projectiveLineGenericCoeff : chowGroup (fieldChowSituation k) σ 1 →+ ℤ :=
  QuotientAddGroup.lift _
    { toFun := fun c ↦ c.1 (genericPoint ℙ)
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
    (fun c hc ↦ by
      rw [rationalEquivalences_projectiveLine_one] at hc
      rw [(AddSubgroup.mem_bot.mp hc)]
      rfl)

/-- The coefficient at the generic point of the class of a one-cycle `c` is the coefficient of `c`
at the generic point. -/
@[simp]
theorem projectiveLineGenericCoeff_mk (c : CycleGroup (fieldChowSituation k) σ 1) :
    projectiveLineGenericCoeff k (QuotientAddGroup.mk c) = c.1 (genericPoint ℙ) :=
  rfl

end Line

/-! ### The product `P¹ × P¹` and the fibre cycles -/

section Fibre

variable {k : Type u} [Field k]

/-- The projective line `P¹_k`. -/
local notation "ℙ" => relativeProjectiveLine (Spec (CommRingCat.of k))

/-- The structure morphism of `P¹_k`. -/
local notation "σ" => (ℙ ↘ Spec (CommRingCat.of k))

/-- The structure morphism of `P¹_k ×_k P¹_k`. -/
local notation "σ₂" => pullback.fst σ σ ≫ σ

/-- The second projection `P¹_k ×_k P¹_k → P¹_k` commutes with the structure morphisms. -/
theorem pullback_snd_projectiveLine_comp : pullback.snd σ σ ≫ σ = σ₂ :=
  pullback.condition.symm

/-! ### Closed copies of `P¹` in `P¹ × P¹` and the two projections -/

/-- The generic point of a closed copy of `P¹` in `P¹ × P¹`, compatible with the structure
morphisms, has relative dimension one over `k`. -/
private theorem relativeDimension_genericPoint_of_closedCopy (j : ℙ ⟶ pullback σ σ)
    [IsClosedImmersion j] (hj : j ≫ σ₂ = σ) :
    relativeDimension (fieldChowSituation k).dimensionFunction σ₂
      (j.base (genericPoint ℙ)) = 1 := by
  rw [← relativeDimension_comp_closedImmersion, hj, relativeDimension_projectiveLine_genericPoint]

/-- A point of a closed copy of `P¹` in `P¹ × P¹` of relative dimension one is the generic point
of the copy. -/
private theorem eq_genericPoint_of_closedCopy (j : ℙ ⟶ pullback σ σ) [IsClosedImmersion j]
    (hj : j ≫ σ₂ = σ) {z : (pullback σ σ : Scheme.{u})} (hz : z ∈ Set.range j.base)
    (hd : relativeDimension (fieldChowSituation k).dimensionFunction σ₂ z = 1) :
    z = j.base (genericPoint ℙ) := by
  obtain ⟨w, rfl⟩ := hz
  rw [← relativeDimension_comp_closedImmersion, hj] at hd
  rw [eq_genericPoint_of_relativeDimension_projectiveLine k hd]

/-- The cycle of the scheme-theoretic image of a closed immersion is the cycle of the closed
immersion. -/
private theorem cycle_imageι_eq (j : ℙ ⟶ pullback σ σ) [IsClosedImmersion j] (n : ℤ) :
    cycleAssociatedToClosedSubscheme (fieldChowSituation k) σ₂ j.imageι n =
      cycleAssociatedToClosedSubscheme (fieldChowSituation k) σ₂ j n :=
  (cycleAssociatedToClosedSubscheme_eq_of_iso (fieldChowSituation k) σ₂ _ _
    (asIso j.toImage) (Scheme.Hom.toImage_imageι _) n).symm

/-- The class of a closed copy `j : P¹ → P¹ × P¹` of the projective line, compatible with the
structure morphisms, is the prime cycle of the image of the generic point. -/
theorem cycle_eq_single_of_isClosedImmersion (j : ℙ ⟶ pullback σ σ)
    [IsClosedImmersion j] (hj : j ≫ σ₂ = σ) :
    (cycleAssociatedToClosedSubscheme (fieldChowSituation k) σ₂ j 1).1 =
      @Function.locallyFinsuppWithin.single _ _ ℤ (Classical.decEq _) _
        (j.base (genericPoint ℙ)) 1 :=
  cycleAssociatedToClosedSubscheme_eq_single (fieldChowSituation k) σ₂ _ 1
    (relativeDimension_genericPoint_of_closedCopy j hj)

/-- The coefficient at the generic point of the pushforward along `p : P¹ × P¹ → P¹` of the class
of a closed copy of `P¹`, `A₁(P¹ × P¹) → A₁(P¹) → ℤ`. -/
abbrev projectionCoeff (p : pullback σ σ ⟶ ℙ) [IsProper p] (hp : p ≫ σ = σ₂) :
    chowGroup (fieldChowSituation k) σ₂ 1 →+ ℤ :=
  (projectiveLineGenericCoeff k).comp
    (properChowPushforward (fieldChowSituation k) σ₂ σ p hp 1
      (properPushforwardDescends _ _ _ _ _ _))

/-- A closed copy `j` of `P¹` which is a section of the projection `p` has pushforward `[P¹]`. -/
theorem projectionCoeff_of_section (p : pullback σ σ ⟶ ℙ) [IsProper p]
    (hp : p ≫ σ = σ₂) (j : ℙ ⟶ pullback σ σ) [IsClosedImmersion j]
    (hj : j ≫ σ₂ = σ) (hjp : j ≫ p = 𝟙 _) :
    projectionCoeff p hp
      (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k) σ₂ j 1)) =
        1 := by
  classical
  change projectiveLineGenericCoeff k (QuotientAddGroup.mk
    (properPushforward (fieldChowSituation k) σ₂ σ p hp 1 _)) = 1
  have hpt : p.base (j.base (genericPoint ℙ)) =
      genericPoint (ℙ) := by
    rw [← Scheme.Hom.comp_apply, hjp]
    rfl
  rw [projectiveLineGenericCoeff_mk, properPushforward_single (fieldChowSituation k) σ₂ σ p hp 1 _ _
    (cycle_eq_single_of_isClosedImmersion j hj), hpt,
    ite_eq_left (relativeDimension_projectiveLine_genericPoint k),
    (residueDegree_eq_one_of_section p j hjp _).1]
  simp [Function.locallyFinsuppWithin.single_apply]

/-- A closed copy `j` of `P¹` which the projection `p` contracts to a rational point has
pushforward zero. -/
theorem projectionCoeff_of_constant (p : pullback σ σ ⟶ ℙ) [IsProper p]
    (hp : p ≫ σ = σ₂) (j : ℙ ⟶ pullback σ σ) [IsClosedImmersion j]
    (hj : j ≫ σ₂ = σ) (x : (fieldChowSituation k).S ⟶ ℙ)
    (hx : x ≫ σ = 𝟙 (fieldChowSituation k).S) (hjp : j ≫ p = σ ≫ x) :
    projectionCoeff p hp
      (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k) σ₂ j 1)) =
        0 := by
  classical
  change projectiveLineGenericCoeff k (QuotientAddGroup.mk
    (properPushforward (fieldChowSituation k) σ₂ σ p hp 1 _)) = 0
  have hpt : p.base (j.base (genericPoint ℙ)) =
      x.base ((ℙ ↘ Spec (CommRingCat.of k)).base (genericPoint ℙ)) := by
    rw [← Scheme.Hom.comp_apply, hjp]
    rfl
  rw [projectiveLineGenericCoeff_mk, properPushforward_single (fieldChowSituation k) σ₂ σ p hp 1 _ _
    (cycle_eq_single_of_isClosedImmersion j hj), hpt,
    ite_eq_right (by rw [relativeDimension_projectiveLine_section k x hx]; exact zero_ne_one)]
  rfl

variable (x : (fieldChowSituation k).S ⟶ relativeProjectiveLine (Spec (.of k)))
  (hx : x ≫ (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) = 𝟙 (fieldChowSituation k).S)

attribute [local instance] isClosedImmersion_graphMorphism

include hx

/-- The closed immersion `P¹ → P¹ × P¹`, `y ↦ (x, y)`, onto the fibre `x × P¹`. -/
abbrev pointFibreEmbedding (x : (fieldChowSituation k).S ⟶ ℙ)
    (hx : x ≫ σ = 𝟙 (fieldChowSituation k).S) :
    ℙ ⟶ pullback σ σ :=
  graphMorphism σ σ (σ ≫ x) (constantMorphism_comp_base σ x hx)

/-- The closed immersion `P¹ → P¹ × P¹`, `y ↦ (y, x)`, onto the fibre `P¹ × x`. -/
abbrev fibrePointEmbedding (x : (fieldChowSituation k).S ⟶ ℙ)
    (hx : x ≫ σ = 𝟙 (fieldChowSituation k).S) :
    ℙ ⟶ pullback σ σ :=
  pointFibreEmbedding x hx ≫ (pullbackSymmetry σ σ).hom

/-- The embedding `y ↦ (x, y)` commutes with the structure morphisms. -/
theorem pointFibreEmbedding_comp : pointFibreEmbedding x hx ≫ σ₂ = σ := by
  rw [← Category.assoc, graphMorphism_fst, constantMorphism_comp_base σ x hx]

/-- The embedding `y ↦ (y, x)` commutes with the structure morphisms. -/
theorem fibrePointEmbedding_comp : fibrePointEmbedding x hx ≫ σ₂ = σ := by
  rw [Category.assoc, ← Category.assoc (pullbackSymmetry σ σ).hom, pullbackSymmetry_hom_comp_fst,
    pullback_snd_projectiveLine_comp, pointFibreEmbedding_comp]

/-- The generic point of the fibre `x × P¹`. -/
abbrev pointFibreGenericPoint (x : (fieldChowSituation k).S ⟶ ℙ)
    (hx : x ≫ σ = 𝟙 (fieldChowSituation k).S) : (pullback σ σ : Scheme.{u}) :=
  (pointFibreEmbedding x hx).base (genericPoint ℙ)

/-- The generic point of the fibre `P¹ × x`. -/
abbrev fibrePointGenericPoint (x : (fieldChowSituation k).S ⟶ ℙ)
    (hx : x ≫ σ = 𝟙 (fieldChowSituation k).S) : (pullback σ σ : Scheme.{u}) :=
  (fibrePointEmbedding x hx).base (genericPoint ℙ)

/-- The generic point of the fibre `x × P¹` has relative dimension one over `k`. -/
theorem relativeDimension_pointFibreGenericPoint :
    relativeDimension (fieldChowSituation k).dimensionFunction σ₂ (pointFibreGenericPoint x hx) =
      1 :=
  relativeDimension_genericPoint_of_closedCopy _ (pointFibreEmbedding_comp x hx)

/-- The generic point of the fibre `P¹ × x` has relative dimension one over `k`. -/
theorem relativeDimension_fibrePointGenericPoint :
    relativeDimension (fieldChowSituation k).dimensionFunction σ₂ (fibrePointGenericPoint x hx) =
      1 :=
  relativeDimension_genericPoint_of_closedCopy _ (fibrePointEmbedding_comp x hx)

/-- The cycle `[x × P¹]` is the prime cycle of the generic point of the fibre. -/
theorem cycle_pointFibreEmbedding :
    (cycleAssociatedToClosedSubscheme (fieldChowSituation k) σ₂ (pointFibreEmbedding x hx) 1).1 =
      @Function.locallyFinsuppWithin.single _ _ ℤ (Classical.decEq _) _
        (pointFibreGenericPoint x hx) 1 :=
  cycle_eq_single_of_isClosedImmersion _ (pointFibreEmbedding_comp x hx)

/-- The cycle `[P¹ × x]` is the prime cycle of the generic point of the fibre. -/
theorem cycle_fibrePointEmbedding :
    (cycleAssociatedToClosedSubscheme (fieldChowSituation k) σ₂ (fibrePointEmbedding x hx) 1).1 =
      @Function.locallyFinsuppWithin.single _ _ ℤ (Classical.decEq _) _
        (fibrePointGenericPoint x hx) 1 :=
  cycle_eq_single_of_isClosedImmersion _ (fibrePointEmbedding_comp x hx)

/-- The cycle of the scheme-theoretic image of `y ↦ (x, y)` is the cycle of the fibre
`x × P¹`. -/
theorem cycle_pointFibre_imageι (n : ℤ) :
    cycleAssociatedToClosedSubscheme (fieldChowSituation k) σ₂
        (pointFibreEmbedding x hx).imageι n =
      cycleAssociatedToClosedSubscheme (fieldChowSituation k) σ₂ (pointFibreEmbedding x hx) n :=
  cycle_imageι_eq _ n

/-- The cycle of the scheme-theoretic image of `y ↦ (y, x)` is the cycle of the fibre
`P¹ × x`. -/
theorem cycle_fibrePoint_imageι (n : ℤ) :
    cycleAssociatedToClosedSubscheme (fieldChowSituation k) σ₂
        (fibrePointEmbedding x hx).imageι n =
      cycleAssociatedToClosedSubscheme (fieldChowSituation k) σ₂ (fibrePointEmbedding x hx) n :=
  cycle_imageι_eq _ n

/-- `y ↦ (x, y)` is the base change of `x : Spec k → P¹` along the first projection. -/
theorem isPullback_pointFibreEmbedding :
    IsPullback (pointFibreEmbedding x hx) σ (pullback.fst σ σ) x :=
  IsPullback.of_right (h₁₂ := pullback.snd σ σ) (v₁₃ := σ) (h₂₂ := σ)
    (by
      rw [graphMorphism_snd, hx]
      exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩)
    (graphMorphism_fst _ _ _ _) (IsPullback.of_hasPullback σ σ).flip

/-- The fibre `x × P¹` is the preimage of `x` under the first projection. -/
theorem range_pointFibreEmbedding :
    Set.range (pointFibreEmbedding x hx).base =
      (pullback.fst σ σ).base ⁻¹' Set.range x.base :=
  range_fst_of_isPullback (isPullback_pointFibreEmbedding x hx)

/-- The fibre `P¹ × x` is the preimage of `x` under the second projection. -/
theorem range_fibrePointEmbedding :
    Set.range (fibrePointEmbedding x hx).base =
      (pullback.snd σ σ).base ⁻¹' Set.range x.base := by
  ext z
  refine ⟨?_, fun hz ↦ ?_⟩
  · rintro ⟨w, rfl⟩
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, Category.assoc,
      pullbackSymmetry_hom_comp_snd, graphMorphism_fst]
    exact ⟨_, rfl⟩
  · have hz' : (pullbackSymmetry σ σ).inv.base z ∈
        Set.range (pointFibreEmbedding x hx).base := by
      rw [range_pointFibreEmbedding x hx, Set.mem_preimage, ← Scheme.Hom.comp_apply,
        pullbackSymmetry_inv_comp_fst]
      exact hz
    obtain ⟨w, hw⟩ := hz'
    refine ⟨w, ?_⟩
    change ((pointFibreEmbedding x hx) ≫ (pullbackSymmetry σ σ).hom).base w = z
    rw [Scheme.Hom.comp_apply, hw, ← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl

/-- A point of `x × P¹` of relative dimension one is the generic point of the fibre. -/
theorem eq_pointFibreGenericPoint {z : (pullback σ σ : Scheme.{u})}
    (hz : z ∈ Set.range (pointFibreEmbedding x hx).base)
    (hd : relativeDimension (fieldChowSituation k).dimensionFunction σ₂ z = 1) :
    z = pointFibreGenericPoint x hx :=
  eq_genericPoint_of_closedCopy _ (pointFibreEmbedding_comp x hx) hz hd

/-- A point of `P¹ × x` of relative dimension one is the generic point of the fibre. -/
theorem eq_fibrePointGenericPoint {z : (pullback σ σ : Scheme.{u})}
    (hz : z ∈ Set.range (fibrePointEmbedding x hx).base)
    (hd : relativeDimension (fieldChowSituation k).dimensionFunction σ₂ z = 1) :
    z = fibrePointGenericPoint x hx :=
  eq_genericPoint_of_closedCopy _ (fibrePointEmbedding_comp x hx) hz hd

/-- The generic points of the two fibres through `x` are distinct. -/
theorem pointFibreGenericPoint_ne : pointFibreGenericPoint x hx ≠ fibrePointGenericPoint x hx := by
  intro h
  have h1 := congrArg (pullback.fst σ σ).base h
  simp only [pointFibreGenericPoint, fibrePointGenericPoint, ← Scheme.Hom.comp_apply,
    Category.assoc, graphMorphism_fst, pullbackSymmetry_hom_comp_fst, graphMorphism_snd] at h1
  have h2 := relativeDimension_projectiveLine_section k x hx
    ((ℙ ↘ Spec (CommRingCat.of k)).base (genericPoint ℙ))
  rw [show x.base ((ℙ ↘ Spec (CommRingCat.of k)).base (genericPoint ℙ)) = genericPoint ℙ from h1,
    relativeDimension_projectiveLine_genericPoint] at h2
  exact one_ne_zero h2

/-! ### The projections of the fibre classes -/

/-- The pushforward of `[x × P¹]` along the second projection is `[P¹]`. -/
theorem projectionCoeff_snd_pointFibre :
    projectionCoeff (pullback.snd σ σ) pullback_snd_projectiveLine_comp
      (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k) σ₂
        (pointFibreEmbedding x hx) 1)) = 1 :=
  projectionCoeff_of_section _ _ _ (pointFibreEmbedding_comp x hx) (graphMorphism_snd _ _ _ _)

/-- The pushforward of `[x × P¹]` along the first projection is zero. -/
theorem projectionCoeff_fst_pointFibre :
    projectionCoeff (pullback.fst σ σ) rfl
      (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k) σ₂
        (pointFibreEmbedding x hx) 1)) = 0 :=
  projectionCoeff_of_constant _ _ _ (pointFibreEmbedding_comp x hx) x hx
    (graphMorphism_fst _ _ _ _)

/-- The pushforward of `[P¹ × x]` along the first projection is `[P¹]`. -/
theorem projectionCoeff_fst_fibrePoint :
    projectionCoeff (pullback.fst σ σ) rfl
      (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k) σ₂
        (fibrePointEmbedding x hx) 1)) = 1 :=
  projectionCoeff_of_section _ _ _ (fibrePointEmbedding_comp x hx) (by
    rw [Category.assoc, pullbackSymmetry_hom_comp_fst, graphMorphism_snd])

/-- The pushforward of `[P¹ × x]` along the second projection is zero. -/
theorem projectionCoeff_snd_fibrePoint :
    projectionCoeff (pullback.snd σ σ) pullback_snd_projectiveLine_comp
      (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k) σ₂
        (fibrePointEmbedding x hx) 1)) = 0 :=
  projectionCoeff_of_constant _ _ _ (fibrePointEmbedding_comp x hx) x hx (by
    rw [Category.assoc, pullbackSymmetry_hom_comp_snd, graphMorphism_fst])

end Fibre

/-! ### The affine line and the affine plane -/

section AffinePlane

/-- Over a field there are no cycle classes of negative dimension. -/
theorem subsingleton_chowGroup_fieldChowSituation_of_neg (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType p] {n : ℤ} (hn : n < 0) :
    Subsingleton (chowGroup (fieldChowSituation k) p n) := by
  have h0 : ∀ a : CycleGroup (fieldChowSituation k) p n, a = 0 := fun a ↦ by
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
    change a.1 x = 0
    by_contra hx
    have h1 := (mem_cyclesOfDimension_iff_forall_point _ p n a.1).1 a.2 x hx
    have h2 := relativeDimension_fieldChowSituation_nonneg k p x
    lia
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective b
  rw [h0 a, h0 b]

/-- The affine line `𝔸¹_S` of the two-chart projective line is the affine space of dimension one
over `S`. -/
def affineLineOverIsoAffineSpaceFinOne (S : Scheme.{u}) :
    affineLineOver S ≅ 𝔸(ULift.{u} (Fin 1); S) :=
  affineLineOverIsoAffineSpace S ≪≫
    affineSpaceReindexIso (Equiv.ofUnique PUnit.{u + 1} (ULift.{u} (Fin 1))) S

/-- The isomorphism `affineLineOverIsoAffineSpaceFinOne S` is compatible with the structure
morphisms to `S`. -/
theorem affineLineOverIsoAffineSpaceFinOne_hom_over (S : Scheme.{u}) :
    (affineLineOverIsoAffineSpaceFinOne S).hom ≫ (𝔸(ULift.{u} (Fin 1); S) ↘ S) =
      affineLineOverHom S := by
  calc (affineLineOverIsoAffineSpaceFinOne S).hom ≫ (𝔸(ULift.{u} (Fin 1); S) ↘ S)
      = (affineLineOverIsoAffineSpace S).hom ≫
          ((affineSpaceReindexIso (Equiv.ofUnique PUnit.{u + 1} (ULift.{u} (Fin 1))) S).hom ≫
            (𝔸(ULift.{u} (Fin 1); S) ↘ S)) := Category.assoc _ _ _
    _ = (affineLineOverIsoAffineSpace S).hom ≫ (𝔸(PUnit.{u + 1}; S) ↘ S) :=
        congrArg ((affineLineOverIsoAffineSpace S).hom ≫ ·) (affineSpaceReindexIso_hom_over _ S)
    _ = affineLineOverHom S := toAffineSpace_fst S

/-- The affine line `𝔸¹_S → S` is an affine-space bundle of rank one. -/
theorem isAffineSpaceBundle_affineLineOverHom (S : Scheme.{u}) :
    IsAffineSpaceBundle (affineLineOverHom S) 1 :=
  isAffineSpaceBundle_of_isPullback
    (IsPullback.of_horiz_isIso
      ⟨by rw [affineLineOverIsoAffineSpaceFinOne_hom_over, Category.comp_id]⟩ :
      IsPullback (affineLineOverIsoAffineSpaceFinOne S).hom (affineLineOverHom S)
        (𝔸(ULift.{u} (Fin 1); S) ↘ S) (𝟙 S))
    (isAffineSpaceBundle_affineSpaceOver S 1)

/-- The affine line `𝔸¹_S → S` is locally of finite type. -/
theorem locallyOfFiniteType_affineLineOverHom (S : Scheme.{u}) :
    LocallyOfFiniteType (affineLineOverHom S) :=
  locallyOfFiniteType_of_isAffineSpaceBundle _ _ (isAffineSpaceBundle_affineLineOverHom S)

attribute [local instance] locallyOfFiniteType_affineLineOverHom

variable (k : Type u) [Field k]

/-- The projective line `P¹_k`. -/
local notation "ℙ" => relativeProjectiveLine (Spec (CommRingCat.of k))

/-- The structure morphism of `P¹_k`. -/
local notation "σ" => (ℙ ↘ Spec (CommRingCat.of k))

/-- The structure morphism of `P¹_k ×_k P¹_k`. -/
local notation "σ₂" => pullback.fst σ σ ≫ σ

/-- The affine line `𝔸¹_k`. -/
local notation "τ" => affineLineOverHom (Spec (CommRingCat.of k))

/-- The affine line has no zero-cycles up to rational equivalence. -/
theorem subsingleton_chowGroup_affineLine_zero :
    Subsingleton (chowGroup (fieldChowSituation k) τ 0) := by
  have hb := isAffineSpaceBundle_affineLineOverHom (Spec (CommRingCat.of k))
  have := flat_of_isAffineSpaceBundle _ _ hb
  have hsurj := flatPullbackChow_surjective_of_isAffineSpaceBundle_unconditional
    (fieldChowSituation k) (𝟙 (fieldChowSituation k).S) τ 1
    (relativeDimension_of_isAffineSpaceBundle _ _ hb) hb (-1)
  have := subsingleton_chowGroup_fieldChowSituation_of_neg k (𝟙 (fieldChowSituation k).S)
    (n := -1) (by norm_num)
  have := hsurj.subsingleton
  exact ((chowGroupDegreeEquiv _ _ (by norm_num : (-1 : ℤ) + ((1 : ℕ) : ℤ) = 0)).trans
    (chowGroupCongr _ (Category.comp_id τ) 0)).symm.toEquiv.subsingleton

/-- The affine plane `𝔸¹_k ×_k 𝔸¹_k` has no one-cycles up to rational equivalence. -/
theorem subsingleton_chowGroup_affinePlane_one :
    Subsingleton (chowGroup (fieldChowSituation k) (pullback.snd τ τ ≫ τ) 1) := by
  have hb' : IsAffineSpaceBundle (pullback.snd τ τ) 1 :=
    isAffineSpaceBundle_of_isPullback (IsPullback.of_hasPullback τ τ)
      (isAffineSpaceBundle_affineLineOverHom _)
  have := flat_of_isAffineSpaceBundle _ _ hb'
  have hsurj := flatPullbackChow_surjective_of_isAffineSpaceBundle_unconditional
    (fieldChowSituation k) τ (pullback.snd τ τ) 1
    (relativeDimension_of_isAffineSpaceBundle _ _ hb') hb' 0
  have := subsingleton_chowGroup_affineLine_zero k
  have := hsurj.subsingleton
  exact (chowGroupDegreeEquiv _ _
    (by norm_num : (0 : ℤ) + ((1 : ℕ) : ℤ) = 1)).symm.toEquiv.subsingleton

/-- The open immersion `𝔸¹_k × 𝔸¹_k → P¹_k × P¹_k` of the product of the affine charts. -/
abbrev affinePlaneEmbedding : (pullback τ τ : Scheme.{u}) ⟶ pullback σ σ :=
  pullback.map τ τ σ σ (affineChart _) (affineChart _) (𝟙 _)
    (by rw [Category.comp_id, affineChart_comp]) (by rw [Category.comp_id, affineChart_comp])

/-- The embedding `𝔸¹_k × 𝔸¹_k → P¹_k × P¹_k` commutes with the structure morphisms. -/
theorem affinePlaneEmbedding_comp :
    affinePlaneEmbedding k ≫ σ₂ = pullback.snd τ τ ≫ τ := by
  rw [← Category.assoc, pullback.lift_fst, Category.assoc, affineChart_comp, pullback.condition]

/-- The affine plane `𝔸¹_k × 𝔸¹_k`, as an open subscheme of `P¹_k × P¹_k`. -/
abbrev affinePlaneOpen : (pullback σ σ : Scheme.{u}).Opens := (affinePlaneEmbedding k).opensRange

/-- The open affine plane of `P¹_k × P¹_k` has no one-cycles up to rational equivalence. -/
theorem subsingleton_chowGroup_affinePlaneOpen_one :
    Subsingleton (chowGroup (fieldChowSituation k) ((affinePlaneOpen k).ι ≫ σ₂) 1) := by
  have := subsingleton_chowGroup_affinePlane_one k
  exact (chowGroupEquivOfIso (fieldChowSituation k) (pullback.snd τ τ ≫ τ)
    ((affinePlaneOpen k).ι ≫ σ₂) (affinePlaneEmbedding k).isoOpensRange.hom
    (by rw [← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, affinePlaneEmbedding_comp k])
    1).symm.toEquiv.subsingleton

/-- A point of `P¹_k × P¹_k` outside the affine plane lies over the point at infinity of one of
the two factors. -/
theorem mem_range_infinity_of_notMem_affinePlaneOpen {z : (pullback σ σ : Scheme.{u})}
    (hz : z ∉ affinePlaneOpen k) :
    (pullback.fst σ σ).base z ∈ Set.range (lineInfinitySection (Spec (CommRingCat.of k))).base ∨
      (pullback.snd σ σ).base z ∈
        Set.range (lineInfinitySection (Spec (CommRingCat.of k))).base := by
  rw [← SetLike.mem_coe, Scheme.Hom.coe_opensRange, Scheme.Pullback.range_map] at hz
  rw [← compl_range_affineChart]
  by_contra h
  exact hz ⟨not_not.mp fun h1 ↦ h (Or.inl h1), not_not.mp fun h2 ↦ h (Or.inr h2)⟩

end AffinePlane

/-! ### The fibres at infinity span `A₁(P¹ × P¹)` -/

section Spanning

variable (k : Type u) [Field k]

/-- The projective line `P¹_k`. -/
local notation "ℙ" => relativeProjectiveLine (Spec (CommRingCat.of k))

/-- The structure morphism of `P¹_k`. -/
local notation "σ" => (ℙ ↘ Spec (CommRingCat.of k))

/-- The structure morphism of `P¹_k ×_k P¹_k`. -/
local notation "σ₂" => pullback.fst σ σ ≫ σ

attribute [local instance] isClosedImmersion_graphMorphism

/-- **The fibres at infinity span `A₁(P¹_k × P¹_k)`.** Every one-cycle on `P¹ × P¹` is rationally
equivalent to `a [∞ × P¹] + b [P¹ × ∞]` for some integers `a` and `b`. -/
theorem exists_eq_zsmul_add_zsmul_infinity (q : chowGroup (fieldChowSituation k) σ₂ 1) :
    ∃ a b : ℤ, q =
      a • (cycleAssociatedToClosedSubscheme (fieldChowSituation k) σ₂
        (pointFibreEmbedding (lineInfinitySection _) (lineInfinitySection_comp _)) 1 :
          chowGroup (fieldChowSituation k) σ₂ 1) +
      b • (cycleAssociatedToClosedSubscheme (fieldChowSituation k) σ₂
        (fibrePointEmbedding (lineInfinitySection _) (lineInfinitySection_comp _)) 1 :
          chowGroup (fieldChowSituation k) σ₂ 1) := by
  classical
  have hx : lineInfinitySection (Spec (CommRingCat.of k)) ≫ σ = 𝟙 _ := lineInfinitySection_comp _
  obtain ⟨α, rfl⟩ := QuotientAddGroup.mk_surjective q
  let Z : TopologicalSpace.Closeds (pullback σ σ : Scheme.{u}) :=
    ⟨((affinePlaneOpen k : (pullback σ σ : Scheme.{u}).Opens) : Set _)ᶜ,
      (affinePlaneOpen k).isOpen.isClosed_compl⟩
  let i := (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι
  have hrange : Set.range i.base = (Set.range (affinePlaneOpen k).ι.base)ᶜ := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Opens.range_ι]
    simp [Z]
  have hV : RationallyEquivalent (fieldChowSituation k) ((affinePlaneOpen k).ι ≫ σ₂) 1
      (cycleGroupOpensRestrict (fieldChowSituation k) σ₂ (affinePlaneOpen k) 1 α)
      (cycleGroupOpensRestrict (fieldChowSituation k) σ₂ (affinePlaneOpen k) 1 0) := by
    have := subsingleton_chowGroup_affinePlaneOpen_one k
    exact (QuotientAddGroup.eq_zero_iff _).mp (Subsingleton.elim _ _)
  obtain ⟨γ, hγ⟩ := exists_rationallyEquivalent_properPushforward_of_cycleGroupRestrict
    (fieldChowSituation k) σ₂ (i ≫ σ₂) i rfl (affinePlaneOpen k) hrange 1 α 0 hV
  set β := properPushforward (fieldChowSituation k) (i ≫ σ₂) σ₂ i rfl 1 γ with hβdef
  have hβV : ∀ z, z ∈ affinePlaneOpen k → β.1 z = 0 := by
    intro z hz
    rw [hβdef, properPushforward_apply]
    have hempty : i.base ⁻¹' {z} = ∅ := by
      ext w
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro hw
      have hzi : z ∈ Set.range i.base := ⟨w, hw⟩
      rw [hrange, Scheme.Opens.range_ι] at hzi
      exact hzi hz
    rw [hempty, finsum_mem_empty]
  have hβ : β = β.1 (pointFibreGenericPoint _ hx) •
        cycleAssociatedToClosedSubscheme (fieldChowSituation k) σ₂ (pointFibreEmbedding _ hx) 1 +
      β.1 (fibrePointGenericPoint _ hx) •
        cycleAssociatedToClosedSubscheme (fieldChowSituation k) σ₂
          (fibrePointEmbedding _ hx) 1 := by
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun z ↦ ?_)
    change β.1 z = β.1 (pointFibreGenericPoint _ hx) *
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) σ₂
          (pointFibreEmbedding _ hx) 1).1 z +
      β.1 (fibrePointGenericPoint _ hx) *
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) σ₂
          (fibrePointEmbedding _ hx) 1).1 z
    rw [cycle_pointFibreEmbedding _ hx, cycle_fibrePointEmbedding _ hx]
    have hne := pointFibreGenericPoint_ne _ hx
    by_cases h0 : z = pointFibreGenericPoint _ hx
    · subst h0
      simp [Function.locallyFinsuppWithin.single_apply, hne]
    by_cases h2 : z = fibrePointGenericPoint _ hx
    · subst h2
      simp [Function.locallyFinsuppWithin.single_apply, Ne.symm hne]
    simp only [Function.locallyFinsuppWithin.single_apply, h0, h2, ite_false, mul_zero, add_zero]
    by_contra hβz
    have hd := (mem_cyclesOfDimension_iff_forall_point (fieldChowSituation k) σ₂ 1 β.1).1 β.2 z hβz
    rcases mem_range_infinity_of_notMem_affinePlaneOpen k (fun hz ↦ hβz (hβV z hz)) with h | h
    · exact h0 (eq_pointFibreGenericPoint _ hx (by rwa [range_pointFibreEmbedding]) hd)
    · exact h2 (eq_fibrePointGenericPoint _ hx (by rwa [range_fibrePointEmbedding]) hd)
  refine ⟨β.1 (pointFibreGenericPoint _ hx), β.1 (fibrePointGenericPoint _ hx), ?_⟩
  rw [← QuotientAddGroup.mk_zsmul, ← QuotientAddGroup.mk_zsmul, ← QuotientAddGroup.mk_add, ← hβ,
    QuotientAddGroup.eq_iff_sub_mem]
  simpa only [zero_add] using hγ

end Spanning

/-! ### `A₁(P¹ × P¹) = ℤ²` and the fibre bases -/

section Basis

variable (k : Type u) [Field k]

/-- The projective line `P¹_k`. -/
local notation "ℙ" => relativeProjectiveLine (Spec (CommRingCat.of k))

/-- The structure morphism of `P¹_k`. -/
local notation "σ" => (ℙ ↘ Spec (CommRingCat.of k))

/-- The structure morphism of `P¹_k ×_k P¹_k`. -/
local notation "σ₂" => pullback.fst σ σ ≫ σ

attribute [local instance] isClosedImmersion_graphMorphism

/-- The two coordinates of a one-cycle class on `P¹ × P¹`: the degrees of its pushforwards
along the second and the first projection, `α ↦ (pr₂,* α, pr₁,* α) ∈ ℤ²`. -/
def fibreCoordinates : chowGroup (fieldChowSituation k) σ₂ 1 →+ ℤ × ℤ :=
  (projectionCoeff (pullback.snd σ σ) pullback_snd_projectiveLine_comp).prod
    (projectionCoeff (pullback.fst σ σ) rfl)

variable {k}

/-- The fibre coordinates of `[x × P¹]` are `(1, 0)`. -/
theorem fibreCoordinates_pointFibre (x : (fieldChowSituation k).S ⟶ ℙ)
    (hx : x ≫ σ = 𝟙 (fieldChowSituation k).S) :
    fibreCoordinates k (cycleAssociatedToClosedSubscheme (fieldChowSituation k) σ₂
      (pointFibreEmbedding x hx) 1 : chowGroup (fieldChowSituation k) σ₂ 1) = (1, 0) :=
  Prod.ext (projectionCoeff_snd_pointFibre x hx) (projectionCoeff_fst_pointFibre x hx)

/-- The fibre coordinates of `[P¹ × x]` are `(0, 1)`. -/
theorem fibreCoordinates_fibrePoint (x : (fieldChowSituation k).S ⟶ ℙ)
    (hx : x ≫ σ = 𝟙 (fieldChowSituation k).S) :
    fibreCoordinates k (cycleAssociatedToClosedSubscheme (fieldChowSituation k) σ₂
      (fibrePointEmbedding x hx) 1 : chowGroup (fieldChowSituation k) σ₂ 1) = (0, 1) :=
  Prod.ext (projectionCoeff_snd_fibrePoint x hx) (projectionCoeff_fst_fibrePoint x hx)

/-- The fibre coordinates of the diagonal are `(1, 1)`. -/
theorem fibreCoordinates_diagonal :
    fibreCoordinates k (cycleAssociatedToClosedSubscheme (fieldChowSituation k) σ₂
      (graphMorphism σ σ (𝟙 ℙ) (Category.id_comp σ)) 1 :
        chowGroup (fieldChowSituation k) σ₂ 1) = (1, 1) := by
  have hj : graphMorphism σ σ (𝟙 ℙ) (Category.id_comp σ) ≫ σ₂ = σ := by
    rw [← Category.assoc, graphMorphism_fst, Category.id_comp]
  exact Prod.ext (projectionCoeff_of_section _ _ _ hj (graphMorphism_snd _ _ _ _))
    (projectionCoeff_of_section _ _ _ hj (graphMorphism_fst _ _ _ _))

variable (k)

/-- The fibre coordinates are a bijection `A₁(P¹ × P¹) → ℤ²`. -/
theorem fibreCoordinates_bijective : Function.Bijective (fibreCoordinates k) := by
  have hx : lineInfinitySection (Spec (CommRingCat.of k)) ≫ σ = 𝟙 _ := lineInfinitySection_comp _
  refine ⟨(injective_iff_map_eq_zero _).mpr fun q hq ↦ ?_, fun ⟨a, b⟩ ↦ ?_⟩
  · obtain ⟨a, b, rfl⟩ := exists_eq_zsmul_add_zsmul_infinity k q
    rw [map_add, map_zsmul, map_zsmul, fibreCoordinates_pointFibre _ hx,
      fibreCoordinates_fibrePoint _ hx] at hq
    have ha : a = 0 := by simpa using congrArg Prod.fst hq
    have hb : b = 0 := by simpa using congrArg Prod.snd hq
    rw [ha, hb, zero_smul, zero_smul, add_zero]
  · refine ⟨a • (cycleAssociatedToClosedSubscheme (fieldChowSituation k) σ₂
        (pointFibreEmbedding _ hx) 1 : chowGroup (fieldChowSituation k) σ₂ 1) +
      b • (cycleAssociatedToClosedSubscheme (fieldChowSituation k) σ₂
        (fibrePointEmbedding _ hx) 1 : chowGroup (fieldChowSituation k) σ₂ 1), ?_⟩
    rw [map_add, map_zsmul, map_zsmul, fibreCoordinates_pointFibre _ hx,
      fibreCoordinates_fibrePoint _ hx]
    simp

/-- **`A₁(P¹_k × P¹_k) = ℤ²`**, through the degrees of the pushforwards along the two
projections. -/
def chowGroupProjectiveLineSquareEquiv : chowGroup (fieldChowSituation k) σ₂ 1 ≃+ ℤ × ℤ :=
  AddEquiv.ofBijective (fibreCoordinates k) (fibreCoordinates_bijective k)

variable {k}

/-- **The diagonal of `P¹_k` is the sum of the two fibres through any rational point**:
`[Δ] = [x × P¹] + [P¹ × x]` in `CH₁(P¹_k × P¹_k)`. -/
theorem diagonal_cycle_eq_add_fibres (x : (fieldChowSituation k).S ⟶ ℙ)
    (hx : x ≫ σ = 𝟙 (fieldChowSituation k).S) :
    (cycleAssociatedToClosedSubscheme (fieldChowSituation k) σ₂
        (graphMorphism σ σ (𝟙 ℙ) (Category.id_comp σ)) 1 :
          chowGroup (fieldChowSituation k) σ₂ 1) =
      (cycleAssociatedToClosedSubscheme (fieldChowSituation k) σ₂
        (pointFibreEmbedding x hx) 1 : chowGroup (fieldChowSituation k) σ₂ 1) +
      (cycleAssociatedToClosedSubscheme (fieldChowSituation k) σ₂
        (fibrePointEmbedding x hx) 1 : chowGroup (fieldChowSituation k) σ₂ 1) :=
  (fibreCoordinates_bijective k).1 (by
    rw [map_add, fibreCoordinates_diagonal, fibreCoordinates_pointFibre x hx,
      fibreCoordinates_fibrePoint x hx]
    rfl)

/-- The fibre class `[x × P¹]` does not depend on the rational point `x`. -/
theorem pointFibre_cycle_eq (x y : (fieldChowSituation k).S ⟶ ℙ)
    (hx : x ≫ σ = 𝟙 (fieldChowSituation k).S) (hy : y ≫ σ = 𝟙 (fieldChowSituation k).S) :
    (cycleAssociatedToClosedSubscheme (fieldChowSituation k) σ₂
        (pointFibreEmbedding x hx) 1 : chowGroup (fieldChowSituation k) σ₂ 1) =
      (cycleAssociatedToClosedSubscheme (fieldChowSituation k) σ₂
        (pointFibreEmbedding y hy) 1 : chowGroup (fieldChowSituation k) σ₂ 1) :=
  (fibreCoordinates_bijective k).1 (by
    rw [fibreCoordinates_pointFibre x hx, fibreCoordinates_pointFibre y hy])

/-- The fibre class `[P¹ × x]` does not depend on the rational point `x`. -/
theorem fibrePoint_cycle_eq (x y : (fieldChowSituation k).S ⟶ ℙ)
    (hx : x ≫ σ = 𝟙 (fieldChowSituation k).S) (hy : y ≫ σ = 𝟙 (fieldChowSituation k).S) :
    (cycleAssociatedToClosedSubscheme (fieldChowSituation k) σ₂
        (fibrePointEmbedding x hx) 1 : chowGroup (fieldChowSituation k) σ₂ 1) =
      (cycleAssociatedToClosedSubscheme (fieldChowSituation k) σ₂
        (fibrePointEmbedding y hy) 1 : chowGroup (fieldChowSituation k) σ₂ 1) :=
  (fibreCoordinates_bijective k).1 (by
    rw [fibreCoordinates_fibrePoint x hx, fibreCoordinates_fibrePoint y hy])

variable (k)

/-- The basis of `A₁(P¹_k × P¹_k)` over `ℤ` given by the fibre classes `[x × P¹]`, `[P¹ × x]` of
any rational point `x`. -/
def projectiveLineFibreBasisInt : Module.Basis (Fin 2) ℤ (chowGroup (fieldChowSituation k) σ₂ 1) :=
  (Module.Basis.finTwoProd ℤ).map (chowGroupProjectiveLineSquareEquiv k).toIntLinearEquiv.symm

variable {k}

/-- The first vector of `projectiveLineFibreBasisInt k` is `[x × P¹]`. -/
theorem projectiveLineFibreBasisInt_zero (x : (fieldChowSituation k).S ⟶ ℙ)
    (hx : x ≫ σ = 𝟙 (fieldChowSituation k).S) :
    projectiveLineFibreBasisInt k 0 =
      (cycleAssociatedToClosedSubscheme (fieldChowSituation k) σ₂
        (pointFibreEmbedding x hx) 1 : chowGroup (fieldChowSituation k) σ₂ 1) := by
  rw [projectiveLineFibreBasisInt, Module.Basis.map_apply, Module.Basis.finTwoProd_zero,
    LinearEquiv.symm_apply_eq]
  exact (fibreCoordinates_pointFibre x hx).symm

/-- The second vector of `projectiveLineFibreBasisInt k` is `[P¹ × x]`. -/
theorem projectiveLineFibreBasisInt_one (x : (fieldChowSituation k).S ⟶ ℙ)
    (hx : x ≫ σ = 𝟙 (fieldChowSituation k).S) :
    projectiveLineFibreBasisInt k 1 =
      (cycleAssociatedToClosedSubscheme (fieldChowSituation k) σ₂
        (fibrePointEmbedding x hx) 1 : chowGroup (fieldChowSituation k) σ₂ 1) := by
  rw [projectiveLineFibreBasisInt, Module.Basis.map_apply, Module.Basis.finTwoProd_one,
    LinearEquiv.symm_apply_eq]
  exact (fibreCoordinates_fibrePoint x hx).symm

variable (k)

/-- The basis of `CH₁(P¹_k × P¹_k) ⊗ ℚ = Corr⁰(P¹_k, P¹_k)` over `ℚ` given by the fibre classes
`c₀ = [x × P¹]` and `c₂ = [P¹ × x]` of any rational point `x`. -/
def projectiveLineFibreBasis :
    Module.Basis (Fin 2) ℚ (Correspondence (fieldChowSituation k) σ σ 1 0) :=
  Algebra.TensorProduct.basis ℚ (projectiveLineFibreBasisInt k)

variable {k}

/-- The first vector of `projectiveLineFibreBasis k` is the correspondence `c₀ = [x × P¹]`. -/
theorem projectiveLineFibreBasis_zero (x : (fieldChowSituation k).S ⟶ ℙ)
    (hx : x ≫ σ = 𝟙 (fieldChowSituation k).S) :
    projectiveLineFibreBasis k 0 = pointFibreCorrespondence (fieldChowSituation k) σ x hx 1 := by
  rw [projectiveLineFibreBasis, Algebra.TensorProduct.basis_apply,
    projectiveLineFibreBasisInt_zero x hx, pointFibreCorrespondence, cycle_pointFibre_imageι x hx]
  rfl

/-- The second vector of `projectiveLineFibreBasis k` is the correspondence `c₂ = [P¹ × x]`. -/
theorem projectiveLineFibreBasis_one (x : (fieldChowSituation k).S ⟶ ℙ)
    (hx : x ≫ σ = 𝟙 (fieldChowSituation k).S) :
    projectiveLineFibreBasis k 1 = fibrePointCorrespondence (fieldChowSituation k) σ x hx 1 := by
  rw [projectiveLineFibreBasis, Algebra.TensorProduct.basis_apply,
    projectiveLineFibreBasisInt_one x hx, fibrePointCorrespondence, cycle_fibrePoint_imageι x hx]
  rfl

end Basis

end Stacks.WeilCohomology

end
