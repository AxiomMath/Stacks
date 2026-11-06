module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ClosedImmersionCycles
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerStructureSheafClass
public import StacksFrontier.AlgebraicGeometry.Chow.DominantPrimeCycle
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductAssociativity
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.DisjointDivisors
public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.NegativeDimensionCycles
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.LocallyPrincipal
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.DisjointSections
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FamilyFibreDifferenceExistence
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FibreDifferencePushforward
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.ProductRegular
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.Cycles
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.PrimeDivisorDimension
public import StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ProjectiveLineDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecialFibreDimension
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Intersection.ExteriorProductIntersection
public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.KeyLemma
public import StacksFrontier.AlgebraicGeometry.Intersection.ProjectionFormulaFlat.Basic
public import StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.FlatPullbackWhole
public import StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.IntersectProperlyLinear
public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToDiagonal.SubvarietyProductAssociativity
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.FibreCycleNonsingularVariety
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.FibreCycleRationalEquivalenceCycle
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.IrreducibleCriterion
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Product

/-!
# The family `V × 𝐏¹` and products with the zero section

Preliminaries for Tag 0B1M (`ZeroFibreDegeneration`), on a variety `P` over an algebraically
closed field `K` and the family `P × 𝐏¹`:

* basic facts on `𝐏¹` and on the support and dimension of products of prime cycles;
* `Stacks.Intersection.torFormula_single_single_swap` — exchanging the two outer factors of a
  triple product (Tag 0B1L twice);
* the family `V × 𝐏¹ ⊆ P × 𝐏¹` over a closed subvariety `V ⊆ P`, its generic point
  `Stacks.Intersection.lineGenericPoint`, and the flat pullback of the prime cycle of `V`;
* `Stacks.Intersection.properPushforward_flatPullback_product_zeroSection` —
  `pr_*(pr^* a · (P × 0)) = a`;
* `Stacks.Intersection.torFormula_lineGenericPoint_zeroSection` — `(V × 𝐏¹) · (P × 0) = V × 0`.

## References

* [Stacks Project, Tag 0B07](https://stacks.math.columbia.edu/tag/0B07)
* [Stacks Project, Tag 0B1L](https://stacks.math.columbia.edu/tag/0B1L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.TorFormula Stacks.Chow

universe u

namespace Stacks.Intersection

variable (K : Type u) [Field K]

/-- The projective line over a field is a variety. -/
instance isVariety_relativeProjectiveLine :
    IsVariety K (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) where
  toIsIntegral := isIntegral_relativeProjectiveLine _

/-- The family `X × 𝐏¹ ⟶ P × 𝐏¹` over the closed immersion `ι : X ⟶ P` lies over the base. -/
theorem familyBaseChange_comp_structure {X P : Scheme.{u}} (sP : P ⟶ Spec (.of K))
    (ι : X ⟶ P) :
    familyBaseChange sP ι ≫
        (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP) =
      pullback.fst (ι ≫ sP) (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ ι ≫ sP := by
  rw [← Category.assoc, familyBaseChange_comp_fst, Category.assoc]

/-- The projective line over a field has dimension one. -/
theorem topologicalKrullDim_relativeProjectiveLine :
    topologicalKrullDim (relativeProjectiveLine (Spec (.of K))) = 1 := by
  have h := topologicalKrullDim_closure_singleton_eq K
    (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))
    (genericPoint (relativeProjectiveLine (Spec (.of K))))
  rw [genericPoint_closure, topologicalKrullDim_univ,
    relativeDimension_relativeProjectiveLine_genericPoint,
    fieldChowSituation_dimensionFunction] at h
  simpa using h

/-- The family of projective lines over a variety has one more dimension. -/
theorem topologicalKrullDim_projectiveLineProduct {V : Scheme.{u}} (s : V ⟶ Spec (.of K))
    [IsVariety K s] :
    topologicalKrullDim (projectiveLineProduct s) = topologicalKrullDim V + 1 := by
  rw [projectiveLineProduct, topologicalKrullDim_pullback_of_isVariety,
    topologicalKrullDim_relativeProjectiveLine]

/-- Over a field a point specializing to a point of the same relative dimension is that point. -/
theorem eq_of_mem_closure_of_relativeDimension_eq {Y : Scheme.{u}} (s : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType s] {y z : Y} (hy : y ∈ closure ({z} : Set Y))
    (h : relativeDimension (fieldChowSituation K).dimensionFunction s y =
      relativeDimension (fieldChowSituation K).dimensionFunction s z) : y = z := by
  obtain ⟨d, hd⟩ := relativeDimension_isDimensionFunction
    (fieldChowSituation K).isUniversallyCatenary (fieldChowSituation K).dimensionFunction s
  by_contra hne
  have hlt := d.strictAnti_specializes (specializes_iff_mem_closure.mpr hy) (Ne.symm hne)
  change d.toFun y < d.toFun z at hlt
  have h1 := hd y
  have h2 := hd z
  change d.toFun y = _ at h1
  change d.toFun z = _ at h2
  omega

/-- The product of two prime cycles is the total product of the two points. -/
private theorem torFormulaCycleIntersectionProduct_single_single_eq_total
    (C : Stacks.Chow.ChowSituation.{u}) {Y : Scheme.{u}} (s : Y ⟶ C.S) [LocallyOfFiniteType s]
    [IsLocallyNoetherian Y] (hY : IsRegular Y) [DecidableEq Y] (n : ℤ) (x y : Y) :
    torFormulaCycleIntersectionProduct C s hY n (Function.locallyFinsuppWithin.single x 1)
        (Function.locallyFinsuppWithin.single y 1) =
      torFormulaSubvarietyProductTotal C s hY n x y := by
  rw [torFormulaCycleIntersectionProduct, cycleIntersectionProduct_single_single, one_mul,
    one_smul]

open scoped Classical in
/-- **The components of the product of two prime cycles.** A point carrying a nonzero coefficient
in `[x] · [y]`, formed in dimension `n`, lies on both closures and has relative dimension `n`. -/
theorem mem_inter_of_torFormula_single_single_ne_zero {Y : Scheme.{u}} (s : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType s] [IsLocallyNoetherian Y] (hY : IsRegular Y) {dY : ℕ}
    (hdY : topologicalKrullDim Y = (dY : WithBot ℕ∞)) (n : ℤ) (x y z : Y)
    (hz : torFormulaCycleIntersectionProduct (fieldChowSituation K) s hY n
      (Function.locallyFinsuppWithin.single x 1) (Function.locallyFinsuppWithin.single y 1) z ≠
        0) :
    z ∈ closure ({x} : Set Y) ∩ closure ({y} : Set Y) ∧
      relativeDimension (fieldChowSituation K).dimensionFunction s z = n := by
  rw [torFormulaCycleIntersectionProduct_single_single_eq_total, torFormulaSubvarietyProductTotal]
    at hz
  split_ifs at hz with hb
  · exact
      ReductionToDiagonal.mem_inter_and_relativeDimension_eq_of_torSubvarietyProductOfBound_ne_zero
        K s hY hdY n hb hz
  · exact (hz rfl).elim

section Associativity

open Stacks.Intersection.ReductionToDiagonal

variable [IsAlgClosed K] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of K)) [IsVariety K f]
  (hY : IsRegular Y) [IsLocallyNoetherian Y]

/-- The Section 43.14 product of two closed subvarieties is symmetric. -/
theorem torSubvarietyProductOfBound_comm {n : ℤ} {x y : Y}
    (h : TorSupportBound (fieldChowSituation K) f hY n x y)
    (h' : TorSupportBound (fieldChowSituation K) f hY n y x) :
    torSubvarietyProductOfBound (fieldChowSituation K) f hY n h =
      torSubvarietyProductOfBound (fieldChowSituation K) f hY n h' :=
  intersectionProductCycle_comm (fieldChowSituation K) f hY _ _ _ _ n _ _

/-- The product of two prime cycles is the Section 43.14 product of the two closures, when the
latter is defined. -/
theorem torFormula_single_single_eq_ofBound [DecidableEq Y] {n : ℤ} {x y : Y}
    (h : TorSupportBound (fieldChowSituation K) f hY n x y) :
    torFormulaCycleIntersectionProduct (fieldChowSituation K) f hY n
        (Function.locallyFinsuppWithin.single x 1) (Function.locallyFinsuppWithin.single y 1) =
      torSubvarietyProductOfBound (fieldChowSituation K) f hY n h := by
  rw [torFormulaCycleIntersectionProduct_single_single_eq_total,
    torFormulaSubvarietyProductTotal_eq_of_bound]

/-- **Exchanging the two outer factors of a triple product (Tag 0B1L twice).** For three closed
subvarieties `U`, `V`, `W` of a nonsingular variety intersecting properly pairwise and with
`dim (U ∩ V ∩ W) ≤ dim U + dim V + dim W - 2 dim X`, `(U · V) · W = (U · W) · V`. -/
theorem torFormula_single_single_swap [DecidableEq Y] (u v w : Y) (dX r s t : ℕ)
    (hdX : topologicalKrullDim Y = (dX : WithBot ℕ∞))
    (hu : topologicalKrullDim (closure ({u} : Set Y)) = (r : WithBot ℕ∞))
    (hv : topologicalKrullDim (closure ({v} : Set Y)) = (s : WithBot ℕ∞))
    (hw : topologicalKrullDim (closure ({w} : Set Y)) = (t : WithBot ℕ∞))
    (huv : AlgebraicGeometry.IntersectProperly
      ⟨closure {u}, isIrreducible_singleton.closure, isClosed_closure⟩
      ⟨closure {v}, isIrreducible_singleton.closure, isClosed_closure⟩)
    (hvw : AlgebraicGeometry.IntersectProperly
      ⟨closure {v}, isIrreducible_singleton.closure, isClosed_closure⟩
      ⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩)
    (huw : AlgebraicGeometry.IntersectProperly
      ⟨closure {u}, isIrreducible_singleton.closure, isClosed_closure⟩
      ⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩)
    (huvw : topologicalKrullDim
        (↥(closure ({u} : Set Y) ∩ closure ({v} : Set Y) ∩ closure ({w} : Set Y))) +
          ((2 * dX : ℕ) : WithBot ℕ∞) ≤ ((r + s + t : ℕ) : WithBot ℕ∞)) :
    torFormulaCycleIntersectionProduct (fieldChowSituation K) f hY ((r : ℤ) + s + t - 2 * dX)
        (torFormulaCycleIntersectionProduct (fieldChowSituation K) f hY ((r : ℤ) + s - dX)
          (Function.locallyFinsuppWithin.single u 1) (Function.locallyFinsuppWithin.single v 1))
        (Function.locallyFinsuppWithin.single w 1) =
      torFormulaCycleIntersectionProduct (fieldChowSituation K) f hY ((r : ℤ) + s + t - 2 * dX)
        (torFormulaCycleIntersectionProduct (fieldChowSituation K) f hY ((r : ℤ) + t - dX)
          (Function.locallyFinsuppWithin.single u 1) (Function.locallyFinsuppWithin.single w 1))
        (Function.locallyFinsuppWithin.single v 1) := by
  have h1 := (torFormulaCycleIntersectionProduct_assoc K f hY u v w dX r s t hdX hu hv hw huv hvw
    huw huvw).2.2
  have huvw' : topologicalKrullDim
      (↥(closure ({u} : Set Y) ∩ closure ({w} : Set Y) ∩ closure ({v} : Set Y))) +
        ((2 * dX : ℕ) : WithBot ℕ∞) ≤ ((r + t + s : ℕ) : WithBot ℕ∞) := by
    rw [Set.inter_assoc, Set.inter_comm (closure {w}), ← Set.inter_assoc,
      show r + t + s = r + s + t by omega]
    exact huvw
  have hwv : AlgebraicGeometry.IntersectProperly
      ⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩
      ⟨closure {v}, isIrreducible_singleton.closure, isClosed_closure⟩ :=
    intersectProperly_symm hvw
  have h2 := (torFormulaCycleIntersectionProduct_assoc K f hY u w v dX r t s hdX hu hw hv huw
    hwv huv huvw').2.2
  have e : ((s : ℤ) + t - dX) = (t : ℤ) + s - dX := by ring
  have hb : TorSupportBound (fieldChowSituation K) f hY ((t : ℤ) + s - dX) v w := by
    rw [← e]; exact torSupportBound_of_intersectProperly_of_eq K f hY v w hdX hv hw hvw
  have hcomm : torSubvarietyProductOfBound (fieldChowSituation K) f hY ((s : ℤ) + t - dX)
      (torSupportBound_of_intersectProperly_of_eq K f hY v w hdX hv hw hvw) =
      torSubvarietyProductOfBound (fieldChowSituation K) f hY ((t : ℤ) + s - dX)
      (torSupportBound_of_intersectProperly_of_eq K f hY w v hdX hw hv hwv) :=
    (torSubvarietyProductOfBound_congr (fieldChowSituation K) f hY e _ hb).trans
      (torSubvarietyProductOfBound_comm K f hY _ _)
  have e2 : ((r : ℤ) + s + t - 2 * dX) = (r : ℤ) + t + s - 2 * dX := by ring
  calc _ = torFormulaCycleIntersectionProduct (fieldChowSituation K) f hY
          ((r : ℤ) + s + t - 2 * dX)
          (torSubvarietyProductOfBound (fieldChowSituation K) f hY ((r : ℤ) + s - dX)
            (torSupportBound_of_intersectProperly_of_eq K f hY u v hdX hu hv huv))
          (Function.locallyFinsuppWithin.single w 1) := by
        rw [torFormula_single_single_eq_ofBound K f hY
          (torSupportBound_of_intersectProperly_of_eq K f hY u v hdX hu hv huv)]
    _ = _ := h1.symm
    _ = torFormulaCycleIntersectionProduct (fieldChowSituation K) f hY
          ((r : ℤ) + t + s - 2 * dX) (Function.locallyFinsuppWithin.single u 1)
          (torSubvarietyProductOfBound (fieldChowSituation K) f hY ((t : ℤ) + s - dX)
            (torSupportBound_of_intersectProperly_of_eq K f hY w v hdX hw hv hwv)) := by
        rw [hcomm, e2]
    _ = _ := h2
    _ = _ := by
        rw [torFormula_single_single_eq_ofBound K f hY
          (torSupportBound_of_intersectProperly_of_eq K f hY u w hdX hu hw huw), e2]

end Associativity

open scoped Classical in
/-- The product of a cycle with a prime cycle is supported on the closure of the latter. -/
theorem mem_closure_of_torFormula_single_right_ne_zero {Y : Scheme.{u}} (s : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType s] [IsLocallyNoetherian Y] [CompactSpace Y] (hY : IsRegular Y) {dY : ℕ}
    (hdY : topologicalKrullDim Y = (dY : WithBot ℕ∞)) (n : ℤ) (α : AlgebraicCycle Y ℤ) (b z : Y)
    (hz : torFormulaCycleIntersectionProduct (fieldChowSituation K) s hY n α
      (Function.locallyFinsuppWithin.single b 1) z ≠ 0) :
    z ∈ closure ({b} : Set Y) := by
  by_contra hzb
  apply hz
  rw [torFormulaCycleIntersectionProduct,
    cycleIntersectionProduct_single_right _ (finite_support_of_compactSpace α),
    Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply]
  have h0 : torFormulaSubvarietyProductTotal (fieldChowSituation K) s hY n a b z = 0 := by
    by_contra hne
    have h1 : torFormulaCycleIntersectionProduct (fieldChowSituation K) s hY n
        (Function.locallyFinsuppWithin.single a 1) (Function.locallyFinsuppWithin.single b 1) z ≠
          0 := by
      rwa [torFormulaCycleIntersectionProduct_single_single_eq_total]
    exact hzb (mem_inter_of_torFormula_single_single_ne_zero K s hY hdY n a b z h1).1.2
  rw [h0, smul_zero]

/-- A cycle supported on the image of a closed immersion is the pushforward of a cycle. -/
theorem exists_properPushforward_eq_of_support_subset {Y Z : Scheme.{u}}
    (sZ : Z ⟶ Spec (.of K)) [LocallyOfFiniteType sZ] (sY : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType sY] (i : Y ⟶ Z) [IsClosedImmersion i] (hi : i ≫ sZ = sY) (k : ℤ)
    (c : AlgebraicCycle Z ℤ) (hc : c ∈ cyclesOfDimension (fieldChowSituation K) sZ k)
    (hsupp : ∀ z, c z ≠ 0 → z ∈ closure (Set.range i.base)) :
    ∃ c' : CycleGroup (fieldChowSituation K) sY k,
      (properPushforward (fieldChowSituation K) sY sZ i hi k c').1 = c := by
  refine ⟨cyclePullbackAlongClosedImmersion (fieldChowSituation K) sY sZ i hi k ⟨c, hc⟩, ?_⟩
  refine Function.locallyFinsuppWithin.ext fun z => ?_
  rw [properPushforward_cyclePullbackAlongClosedImmersion_apply]
  by_cases hz : z ∈ Set.range i.base
  · rw [Set.indicator_of_mem hz]
  · rw [Set.indicator_of_notMem hz]
    by_contra hne
    exact hz (i.isClosedEmbedding.isClosed_range.closure_eq ▸ hsupp z (Ne.symm hne))

/-- The generic point of the integral closed subscheme attached to `y` maps to `y`. -/
private theorem subschemeι_base_genericPoint_integralComponentAt {Y : Scheme.{u}} (y : Y) :
    haveI := isIntegral_integralComponentAt y
    (integralComponentAt y).subschemeι.base (genericPoint (integralComponentAt y).subscheme) =
      y := by
  simpa [genericPointOf] using genericPointOf_integralComponentAt y

/-- A point of `P × 𝐏¹` whose closure has one more dimension than that of a point `z` of `P` has
one more relative dimension than `z`. -/
private theorem relativeDimension_eq_succ_of_topologicalKrullDim_closure {P : Scheme.{u}}
    (sP : P ⟶ Spec (.of K)) [LocallyOfFiniteType sP] {y : projectiveLineProduct sP} {z : P}
    (h : topologicalKrullDim (closure ({y} : Set (projectiveLineProduct sP))) =
      topologicalKrullDim (closure ({z} : Set P)) + 1) :
    relativeDimension (fieldChowSituation K).dimensionFunction
        (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP) y =
      relativeDimension (fieldChowSituation K).dimensionFunction sP z + 1 := by
  rw [topologicalKrullDim_closure_singleton_eq K
      (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP),
    topologicalKrullDim_closure_singleton_eq K sP] at h
  have h' : (relativeDimension (fieldChowSituation K).dimensionFunction
      (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP) y).toNat =
      (relativeDimension (fieldChowSituation K).dimensionFunction sP z).toNat + 1 := by
    exact_mod_cast h
  have h1 := relativeDimension_fieldChowSituation_nonneg K
    (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP) y
  have h2 := relativeDimension_fieldChowSituation_nonneg K sP z
  omega

section LineFamily

variable {K} [IsAlgClosed K] {V P : Scheme.{u}} (sP : P ⟶ Spec (.of K)) (i : V ⟶ P)

/-- The family over a closed immersion is cut out by the inverse image of its ideal. -/
theorem ker_familyBaseChange [IsClosedImmersion i] :
    (familyBaseChange sP i).ker =
      i.ker.comap (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))) :=
  ker_eq_comap_ker_of_isPullback (isPullback_familyBaseChange sP i).flip

/-- The image of the family over `V` is the inverse image of `V`. -/
theorem range_familyBaseChange :
    Set.range (familyBaseChange sP i).base =
      (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))).base ⁻¹'
        Set.range i.base := by
  rw [← (isPullback_familyBaseChange sP i).flip.isoPullback_hom_fst, Scheme.Hom.comp_base,
    TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr, Set.image_univ,
    Scheme.Pullback.range_fst]
  exact ((isPullback_familyBaseChange sP i).flip.isoPullback.hom.homeomorph).surjective

/-- The projection of the family over a variety carries generic point to generic point. -/
theorem fst_genericPoint_projectiveLineProduct (s : V ⟶ Spec (.of K)) [IsVariety K s] :
    (pullback.fst s (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))).base
        (genericPoint (projectiveLineProduct s)) = genericPoint V :=
  genericPoint_eq_of_surjective _

/-- The family over `V` has its generic point over the generic point of `V`. -/
theorem fst_familyBaseChange_genericPoint [IsVariety K (i ≫ sP)] :
    (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))).base
        ((familyBaseChange sP i).base (genericPoint (projectiveLineProduct (i ≫ sP)))) =
      i.base (genericPoint V) := by
  rw [← Scheme.Hom.comp_apply, familyBaseChange_comp_fst, Scheme.Hom.comp_apply,
    fst_genericPoint_projectiveLineProduct]

/-- The reduced closure of the image of the generic point of an integral closed subscheme has
the dimension of the subscheme. -/
theorem topologicalKrullDim_closure_image_genericPoint {T Z : Scheme.{u}} (i : Z ⟶ T)
    [IsClosedImmersion i] [IsIntegral Z] :
    topologicalKrullDim (closure ({i.base (genericPoint Z)} : Set T)) = topologicalKrullDim Z := by
  rw [← range_eq_closure_singleton i]
  exact (IsHomeomorph.topologicalKrullDim_eq _
    i.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph).symm

/-- The closure of the generic point of the family over `V` is the inverse image of `V`. -/
theorem closure_familyBaseChange_genericPoint [IsClosedImmersion i] [IsVariety K (i ≫ sP)] :
    closure ({(familyBaseChange sP i).base (genericPoint (projectiveLineProduct (i ≫ sP)))} :
        Set (projectiveLineProduct sP)) =
      (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))).base ⁻¹'
        Set.range i.base := by
  rw [← range_eq_closure_singleton, range_familyBaseChange]

/-- The closure of the generic point of the family over `V` has one more dimension than `V`. -/
theorem topologicalKrullDim_closure_familyBaseChange_genericPoint [IsClosedImmersion i]
    [IsVariety K (i ≫ sP)] :
    topologicalKrullDim (closure
        ({(familyBaseChange sP i).base (genericPoint (projectiveLineProduct (i ≫ sP)))} :
          Set (projectiveLineProduct sP))) =
      topologicalKrullDim V + 1 := by
  rw [topologicalKrullDim_closure_image_genericPoint, topologicalKrullDim_projectiveLineProduct]

/-- The generic point of the family over `V` has one more relative dimension than the generic
point of `V`. -/
theorem relativeDimension_familyBaseChange_genericPoint [IsVariety K sP] [IsClosedImmersion i]
    [IsVariety K (i ≫ sP)] :
    relativeDimension (fieldChowSituation K).dimensionFunction
        (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP)
        ((familyBaseChange sP i).base (genericPoint (projectiveLineProduct (i ≫ sP)))) =
      relativeDimension (fieldChowSituation K).dimensionFunction sP (i.base (genericPoint V)) +
        1 := by
  exact relativeDimension_eq_succ_of_topologicalKrullDim_closure K sP (by
    rw [topologicalKrullDim_closure_familyBaseChange_genericPoint,
      topologicalKrullDim_closure_image_genericPoint])

open scoped Classical in
/-- **The flat pullback of the prime cycle of `V` along `pr : P × 𝐏¹ ⟶ P`** is the prime cycle
of `V × 𝐏¹`. -/
theorem flatPullback_cycleAssociatedToClosedSubscheme_eq_single [IsVariety K sP]
    [IsClosedImmersion i] [IsVariety K (i ≫ sP)] (hf : RelativeDimension
      (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))) 1) (n : ℤ)
    (hn : relativeDimension (fieldChowSituation K).dimensionFunction sP
      (i.base (genericPoint V)) = n) :
    (flatPullback (fieldChowSituation K)
        (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP) sP
        (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))) rfl 1 hf n
        (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sP i n)).1 =
      Function.locallyFinsuppWithin.single
        ((familyBaseChange sP i).base (genericPoint (projectiveLineProduct (i ≫ sP)))) 1 := by
  have hZ : schemeDeltaDimension (fieldChowSituation K) (i ≫ sP) = (n : EInt) := by
    rw [schemeDeltaDimension_eq_genericPoint, relativeDimension_comp_closedImmersion, hn]
  rw [flatPullback_cycleAssociatedToClosedSubscheme (fieldChowSituation K) _ sP _ rfl 1 hf n i hZ]
  rw [← cycleAssociatedToClosedSubscheme_eq_of_iso (fieldChowSituation K) _
    (familyBaseChange sP i) _ (isPullback_familyBaseChange sP i).flip.isoPullback
    (isPullback_familyBaseChange sP i).flip.isoPullback_hom_fst]
  rw [cycleAssociatedToClosedSubscheme_eq_single (fieldChowSituation K) _
    (familyBaseChange sP i) _ ((relativeDimension_familyBaseChange_genericPoint sP i).trans
      (by rw [hn]; push_cast; ring))]

end LineFamily

section LinePoint

variable {K} [IsAlgClosed K] {P : Scheme.{u}} (sP : P ⟶ Spec (.of K)) [IsVariety K sP]

/-- The generic point of `V × 𝐏¹ ⊆ P × 𝐏¹` for the reduced closure `V` of a point `v` of `P`. -/
def lineGenericPoint (v : P) : projectiveLineProduct sP :=
  haveI := isIntegral_integralComponentAt v
  (familyBaseChange sP (integralComponentAt v).subschemeι).base
    (genericPoint (projectiveLineProduct ((integralComponentAt v).subschemeι ≫ sP)))

variable (v : P)

/-- The generic point of `V × 𝐏¹` lies over the generic point `v` of `V`. -/
theorem fst_lineGenericPoint :
    (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))).base
      (lineGenericPoint sP v) = v := by
  have := isIntegral_integralComponentAt v
  rw [lineGenericPoint, fst_familyBaseChange_genericPoint]
  simpa using subschemeι_base_genericPoint_integralComponentAt v

/-- The closure of the generic point of `V × 𝐏¹` is the inverse image of `V`. -/
theorem closure_lineGenericPoint :
    closure ({lineGenericPoint sP v} : Set (projectiveLineProduct sP)) =
      (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))).base ⁻¹'
        closure {v} := by
  have := isIntegral_integralComponentAt v
  rw [lineGenericPoint, closure_familyBaseChange_genericPoint,
    Scheme.IdealSheafData.range_subschemeι, coe_support_integralComponentAt]

/-- The reduced closure of the generic point of `V × 𝐏¹` is the inverse image of `V`. -/
theorem integralComponentAt_lineGenericPoint :
    integralComponentAt (lineGenericPoint sP v) =
      (integralComponentAt v).comap
        (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))) := by
  have := isIntegral_integralComponentAt v
  rw [lineGenericPoint, ← ker_eq_integralComponentAt, ker_familyBaseChange,
    Scheme.IdealSheafData.ker_subschemeι]

/-- The zero fibre of `V × 𝐏¹` is `V`. -/
theorem zeroFiber_integralComponentAt_lineGenericPoint :
    zeroFiber sP (integralComponentAt (lineGenericPoint sP v)) = integralComponentAt v := by
  rw [integralComponentAt_lineGenericPoint, zeroFiber, ← Scheme.IdealSheafData.comap_comp,
    zeroSection_comp_fst, Scheme.IdealSheafData.comap_id]

/-- `V × 𝐏¹` has one more dimension than `V`. -/
theorem topologicalKrullDim_closure_lineGenericPoint :
    topologicalKrullDim (closure ({lineGenericPoint sP v} : Set (projectiveLineProduct sP))) =
      topologicalKrullDim (closure ({v} : Set P)) + 1 := by
  have := isIntegral_integralComponentAt v
  have := ExteriorProductProjections.isVariety_subschemeι_comp K sP (integralComponentAt v)
  rw [lineGenericPoint, topologicalKrullDim_closure_familyBaseChange_genericPoint,
    topologicalKrullDim_subscheme, coe_support_integralComponentAt]

/-- `V × 𝐏¹` is not contained in the zero section. -/
theorem not_range_subset_zeroSection_lineGenericPoint :
    ¬ Set.range (integralComponentAt (lineGenericPoint sP v)).subschemeι.base ⊆
      Set.range (zeroSection sP).base := by
  intro h
  have hmem : (infinitySection sP).base v ∈
      Set.range (integralComponentAt (lineGenericPoint sP v)).subschemeι.base := by
    rw [Scheme.IdealSheafData.range_subschemeι, coe_support_integralComponentAt,
      closure_lineGenericPoint, Set.mem_preimage, ← Scheme.Hom.comp_apply,
      infinitySection_comp_fst]
    exact subset_closure rfl
  obtain ⟨x, hx⟩ := h hmem
  exact zeroSection_ne_infinitySection sP x v hx

/-- The generic point of `V × 𝐏¹` has one more relative dimension than `v`. -/
theorem relativeDimension_lineGenericPoint :
    relativeDimension (fieldChowSituation K).dimensionFunction
        (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP)
        (lineGenericPoint sP v) =
      relativeDimension (fieldChowSituation K).dimensionFunction sP v + 1 := by
  exact relativeDimension_eq_succ_of_topologicalKrullDim_closure K sP
    (topologicalKrullDim_closure_lineGenericPoint sP v)

/-- The delta-dimension of the reduced closure of a point is its relative dimension. -/
theorem schemeDeltaDimension_integralComponentAt_eq {Y : Scheme.{u}} (s : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType s] (y : Y) :
    schemeDeltaDimension (fieldChowSituation K) ((integralComponentAt y).subschemeι ≫ s) =
      (relativeDimension (fieldChowSituation K).dimensionFunction s y : EInt) := by
  have := isIntegral_integralComponentAt y
  rw [schemeDeltaDimension_eq_genericPoint, relativeDimension_comp_closedImmersion]
  congr 2
  exact subschemeι_base_genericPoint_integralComponentAt y

open scoped Classical in
/-- **The flat pullback of a prime cycle along `pr : P × 𝐏¹ ⟶ P`** is the prime cycle of
`V × 𝐏¹`. -/
theorem flatPullback_primeCycle_eq_single (hf : RelativeDimension
      (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))) 1) (n : ℤ)
    (hv : relativeDimension (fieldChowSituation K).dimensionFunction sP v = n) :
    (flatPullback (fieldChowSituation K)
        (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP) sP
        (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))) rfl 1 hf n
        (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sP
          (integralComponentAt v).subschemeι n)).1 =
      Function.locallyFinsuppWithin.single (lineGenericPoint sP v) 1 := by
  have := isIntegral_integralComponentAt v
  have := ExteriorProductProjections.isVariety_subschemeι_comp K sP (integralComponentAt v)
  rw [flatPullback_cycleAssociatedToClosedSubscheme (fieldChowSituation K) _ sP _ rfl 1 hf n
    (integralComponentAt v).subschemeι
    ((schemeDeltaDimension_integralComponentAt_eq sP v).trans (by rw [hv]))]
  rw [← cycleAssociatedToClosedSubscheme_eq_of_iso (fieldChowSituation K) _
    (familyBaseChange sP (integralComponentAt v).subschemeι) _
    (isPullback_familyBaseChange sP (integralComponentAt v).subschemeι).flip.isoPullback
    (isPullback_familyBaseChange sP (integralComponentAt v).subschemeι).flip.isoPullback_hom_fst]
  have hk : relativeDimension (fieldChowSituation K).dimensionFunction
      (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP)
      ((familyBaseChange sP (integralComponentAt v).subschemeι).base
        (genericPoint (projectiveLineProduct ((integralComponentAt v).subschemeι ≫ sP)))) =
      n + ((1 : ℕ) : ℤ) :=
    (relativeDimension_lineGenericPoint sP v).trans (by rw [hv]; push_cast; ring)
  rw [cycleAssociatedToClosedSubscheme_eq_single (fieldChowSituation K) _
    (familyBaseChange sP (integralComponentAt v).subschemeι) _ hk]
  congr 1

end LinePoint

section ZeroSection

variable {K} [IsAlgClosed K] {P : Scheme.{u}} (sP : P ⟶ Spec (.of K)) [IsVariety K sP]
  (hQ : IsRegular (projectiveLineProduct sP)) [IsLocallyNoetherian (projectiveLineProduct sP)]

/-- The dimension of `P × 𝐏¹` is bounded by a natural number. -/
theorem exists_topologicalKrullDim_projectiveLineProduct_le_of_isVariety :
    ∃ d : ℕ, topologicalKrullDim (projectiveLineProduct sP) ≤ (d : WithBot ℕ∞) := by
  have : IsVariety K (sP ≫ eqToHom (rfl : (fieldChowSituation K).S = Spec (.of K))) := by
    simpa using ‹IsVariety K sP›
  exact exists_topologicalKrullDim_projectiveLineProduct_le K (fieldChowSituation K) rfl sP

open scoped Classical in
/-- **Stacks 0B07, part (1)(b), on `P × 𝐏¹`, for a prime cycle.** -/
theorem properPushforward_eq_zeroFiberCycle_of_coe_eq_single (x : projectiveLineProduct sP)
    (k : ℤ) (hx : relativeDimension (fieldChowSituation K).dimensionFunction
      (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP) x = k + 1)
    (h₀ : ¬ Set.range (integralComponentAt x).subschemeι.base ⊆ Set.range (zeroSection sP).base)
    (A : CycleGroup (fieldChowSituation K)
      (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP) k)
    (hA : A.1 = torFormulaCycleIntersectionProduct (fieldChowSituation K)
      (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP) hQ k
      (Function.locallyFinsuppWithin.single x 1)
      (Function.locallyFinsuppWithin.single ((zeroSection sP).base (genericPoint P)) 1)) :
    properPushforward (fieldChowSituation K)
        (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP) sP
        (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))) rfl k A =
      cycleAssociatedToClosedSubscheme (fieldChowSituation K) sP
        (zeroFiber sP (integralComponentAt x)).subschemeι k := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_projectiveLineProduct_le_of_isVariety sP
  refine properPushforward_eq_zeroFiberCycle_of_coe_eq (fieldChowSituation K) sP hQ k d x hd hx
    h₀ A ?_
  rw [hA, torFormulaCycleIntersectionProduct_single_single_eq_total]

open scoped Classical in
/-- **`pr_*(pr^* a · (P × 0)) = a`.** For an `m`-cycle `a` on `P`, intersecting its flat
pullback to `P × 𝐏¹` with the zero section and pushing forward returns `a`. -/
theorem properPushforward_flatPullback_product_zeroSection (hf : RelativeDimension
      (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))) 1) (m : ℤ)
    (a : CycleGroup (fieldChowSituation K) sP m) :
    properPushforward (fieldChowSituation K)
        (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP) sP
        (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))) rfl m
        ⟨torFormulaCycleIntersectionProduct (fieldChowSituation K)
          (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP) hQ m
          (flatPullback (fieldChowSituation K)
            (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP) sP
            (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))) rfl 1 hf m
            a).1
          (Function.locallyFinsuppWithin.single ((zeroSection sP).base (genericPoint P)) 1),
          torFormulaCycleIntersectionProduct_mem_cyclesOfDimension _ _ _ _ _ _⟩ = a := by
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace sP
  have : CompactSpace (projectiveLineProduct sP) := QuasiCompact.compactSpace_of_compactSpace
    (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP)
  set L := relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)
  have hfin := finite_support_of_compactSpace a.1
  have hdim : ∀ v ∈ hfin.toFinset,
      relativeDimension (fieldChowSituation K).dimensionFunction sP v = m := fun v hv =>
    (mem_cyclesOfDimension_iff_forall_point (fieldChowSituation K) sP m a.1).1 a.2 v
      (hfin.mem_toFinset.1 hv)
  have hpull : (flatPullback (fieldChowSituation K) (pullback.fst sP L ≫ sP) sP
      (pullback.fst sP L) rfl 1 hf m a).1 =
      ∑ v ∈ hfin.toFinset,
        a.1 v • Function.locallyFinsuppWithin.single (lineGenericPoint sP v) 1 := by
    conv_lhs => rw [cycle_eq_sum_zsmul_primeCycles a hfin]
    rw [map_sum]
    simp only [map_zsmul, AddSubgroup.val_finset_sum, AddSubgroup.coe_zsmul]
    exact Finset.sum_congr rfl fun v hv => by
      rw [flatPullback_primeCycle_eq_single sP v hf m (hdim v hv)]
  have key : ∀ v ∈ hfin.toFinset, properPushforward (fieldChowSituation K)
      (pullback.fst sP L ≫ sP) sP (pullback.fst sP L) rfl m
      ⟨torFormulaCycleIntersectionProduct (fieldChowSituation K) (pullback.fst sP L ≫ sP) hQ m
        (Function.locallyFinsuppWithin.single (lineGenericPoint sP v) 1)
        (Function.locallyFinsuppWithin.single ((zeroSection sP).base (genericPoint P)) 1),
        torFormulaCycleIntersectionProduct_mem_cyclesOfDimension _ _ _ _ _ _⟩ =
      cycleAssociatedToClosedSubscheme (fieldChowSituation K) sP
        (integralComponentAt v).subschemeι m := by
    intro v hv
    rw [properPushforward_eq_zeroFiberCycle_of_coe_eq_single sP hQ (lineGenericPoint sP v) m
      (by rw [relativeDimension_lineGenericPoint, hdim v hv])
      (not_range_subset_zeroSection_lineGenericPoint sP v) _ rfl,
      zeroFiber_integralComponentAt_lineGenericPoint]
  have hsum : (⟨torFormulaCycleIntersectionProduct (fieldChowSituation K)
        (pullback.fst sP L ≫ sP) hQ m
        (flatPullback (fieldChowSituation K) (pullback.fst sP L ≫ sP) sP
          (pullback.fst sP L) rfl 1 hf m a).1
        (Function.locallyFinsuppWithin.single ((zeroSection sP).base (genericPoint P)) 1),
        torFormulaCycleIntersectionProduct_mem_cyclesOfDimension _ _ _ _ _ _⟩ :
      CycleGroup (fieldChowSituation K) (pullback.fst sP L ≫ sP) m) =
      ∑ v ∈ hfin.toFinset, a.1 v •
        ⟨torFormulaCycleIntersectionProduct (fieldChowSituation K) (pullback.fst sP L ≫ sP) hQ m
          (Function.locallyFinsuppWithin.single (lineGenericPoint sP v) 1)
          (Function.locallyFinsuppWithin.single ((zeroSection sP).base (genericPoint P)) 1),
          torFormulaCycleIntersectionProduct_mem_cyclesOfDimension _ _ _ _ _ _⟩ := by
    apply Subtype.ext
    simp only [AddSubgroup.val_finset_sum, AddSubgroup.coe_zsmul]
    rw [hpull, torFormulaCycleIntersectionProduct, cycleIntersectionProduct_sum_left]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [cycleIntersectionProduct_zsmul_left _ _ (finite_support_of_compactSpace _)
      (finite_support_of_compactSpace _)]
    rfl
  rw [hsum, ← properPushforwardHom_apply, map_sum]
  conv_rhs => rw [cycle_eq_sum_zsmul_primeCycles a hfin]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [map_zsmul, properPushforwardHom_apply, key v hv]

open scoped Classical in
/-- Pushing forward along `pr : P × 𝐏¹ ⟶ P` the prime cycle of the image under the zero section
of the closure of `z` gives the prime cycle of `z`. -/
theorem properPushforward_single_zeroSection (z : P) (r : ℤ)
    (hz : relativeDimension (fieldChowSituation K).dimensionFunction sP z = r)
    (hmem : Function.locallyFinsuppWithin.single ((zeroSection sP).base z) (1 : ℤ) ∈
      cyclesOfDimension (fieldChowSituation K)
        (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP) r) :
    (properPushforward (fieldChowSituation K)
        (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP) sP
        (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))) rfl r
        ⟨_, hmem⟩).1 = Function.locallyFinsuppWithin.single z 1 := by
  have := isIntegral_integralComponentAt z
  have : IsClosedImmersion (((integralComponentAt z).subschemeι ≫ zeroSection sP) ≫
      pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))) := by
    rw [Category.assoc, zeroSection_comp_fst, Category.comp_id]; infer_instance
  have hgen := subschemeι_base_genericPoint_integralComponentAt z
  have h1 := cycleAssociatedToClosedSubscheme_eq_single (fieldChowSituation K)
    (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP)
    ((integralComponentAt z).subschemeι ≫ zeroSection sP) r (by
      rw [Scheme.Hom.comp_apply, hgen, ← relativeDimension_comp_closedImmersion,
        ← Category.assoc, zeroSection_comp_fst, Category.id_comp, hz])
  have h2 := cycleAssociatedToClosedSubscheme_eq_single (fieldChowSituation K) sP
    (((integralComponentAt z).subschemeι ≫ zeroSection sP) ≫
      pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))) r (by
      rw [Category.assoc, zeroSection_comp_fst, Category.comp_id, hgen, hz])
  have h3 := properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp
    (fieldChowSituation K)
    (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP) sP
    (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))) rfl
    ((integralComponentAt z).subschemeι ≫ zeroSection sP) r
  have h4 : (⟨_, hmem⟩ : CycleGroup (fieldChowSituation K)
      (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP) r) =
      cycleAssociatedToClosedSubscheme (fieldChowSituation K)
        (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP)
        ((integralComponentAt z).subschemeι ≫ zeroSection sP) r := by
    apply Subtype.ext
    rw [h1, Scheme.Hom.comp_apply, hgen]
  rw [h4, h3, h2]
  simp only [Category.assoc, zeroSection_comp_fst, Category.comp_id, hgen]

/-- The zero section preserves relative dimension. -/
theorem relativeDimension_zeroSection (y : P) :
    relativeDimension (fieldChowSituation K).dimensionFunction
        (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP)
        ((zeroSection sP).base y) =
      relativeDimension (fieldChowSituation K).dimensionFunction sP y := by
  rw [← relativeDimension_comp_closedImmersion, ← Category.assoc, zeroSection_comp_fst,
    Category.id_comp]

open scoped Classical in
/-- The prime cycle of `σ(z)` is a cycle of the dimension of `z`. -/
theorem single_zeroSection_mem_cyclesOfDimension (z : P) (r : ℤ)
    (hz : relativeDimension (fieldChowSituation K).dimensionFunction sP z = r) :
    Function.locallyFinsuppWithin.single ((zeroSection sP).base z) (1 : ℤ) ∈
      cyclesOfDimension (fieldChowSituation K)
        (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP) r := by
  rw [mem_cyclesOfDimension_iff_forall_point]
  intro x hx
  rw [Function.locallyFinsuppWithin.single_apply] at hx
  split_ifs at hx with h
  · rw [h, relativeDimension_zeroSection, hz]
  · exact (hx rfl).elim

open scoped Classical in
/-- **`(V × 𝐏¹) · (P × 0) = V × 0`.** The product of the prime cycle of `V × 𝐏¹` with the image
of the zero section is the prime cycle of the image of `V` under the zero section. -/
theorem torFormula_lineGenericPoint_zeroSection (z : P) (r : ℤ)
    (hz : relativeDimension (fieldChowSituation K).dimensionFunction sP z = r) {dQ : ℕ}
    (hdQ : topologicalKrullDim (projectiveLineProduct sP) = (dQ : WithBot ℕ∞)) :
    torFormulaCycleIntersectionProduct (fieldChowSituation K)
        (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP) hQ r
        (Function.locallyFinsuppWithin.single (lineGenericPoint sP z) 1)
        (Function.locallyFinsuppWithin.single ((zeroSection sP).base (genericPoint P)) 1) =
      Function.locallyFinsuppWithin.single ((zeroSection sP).base z) 1 := by
  set L := relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)
  set c := torFormulaCycleIntersectionProduct (fieldChowSituation K)
    (pullback.fst sP L ≫ sP) hQ r
    (Function.locallyFinsuppWithin.single (lineGenericPoint sP z) 1)
    (Function.locallyFinsuppWithin.single ((zeroSection sP).base (genericPoint P)) 1) with hcdef
  have hmemc : c ∈ cyclesOfDimension (fieldChowSituation K) (pullback.fst sP L ≫ sP) r :=
    torFormulaCycleIntersectionProduct_mem_cyclesOfDimension _ _ _ _ _ _
  have hsupp : ∀ x, c x ≠ 0 → x = (zeroSection sP).base z := by
    intro x hx
    obtain ⟨⟨hx1, hx2⟩, hxr⟩ := mem_inter_of_torFormula_single_single_ne_zero K _ hQ hdQ r _ _ x hx
    rw [← range_eq_closure_singleton] at hx2
    obtain ⟨y, rfl⟩ := hx2
    rw [closure_lineGenericPoint, Set.mem_preimage, ← Scheme.Hom.comp_apply,
      zeroSection_comp_fst] at hx1
    rw [relativeDimension_zeroSection] at hxr
    replace hx1 : y ∈ closure ({z} : Set P) := hx1
    rw [eq_of_mem_closure_of_relativeDimension_eq K sP hx1 (hxr.trans hz.symm)]
  have hc : c = c ((zeroSection sP).base z) •
      Function.locallyFinsuppWithin.single ((zeroSection sP).base z) 1 := by
    refine Function.locallyFinsuppWithin.ext fun x => ?_
    rw [Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply,
      Function.locallyFinsuppWithin.single_apply]
    split_ifs with h
    · rw [h, smul_eq_mul, mul_one]
    · rw [smul_zero]
      by_contra hne
      exact h (hsupp x hne)
  have hsing := single_zeroSection_mem_cyclesOfDimension sP z r hz
  have hpush1 := properPushforward_eq_zeroFiberCycle_of_coe_eq_single sP hQ (lineGenericPoint sP z)
    r (by rw [relativeDimension_lineGenericPoint, hz])
    (not_range_subset_zeroSection_lineGenericPoint sP z) ⟨c, hmemc⟩ rfl
  rw [zeroFiber_integralComponentAt_lineGenericPoint] at hpush1
  have hpush2 : properPushforward (fieldChowSituation K) (pullback.fst sP L ≫ sP) sP
      (pullback.fst sP L) rfl r ⟨c, hmemc⟩ =
      c ((zeroSection sP).base z) • properPushforward (fieldChowSituation K)
        (pullback.fst sP L ≫ sP) sP (pullback.fst sP L) rfl r ⟨_, hsing⟩ := by
    rw [← properPushforwardHom_apply, ← properPushforwardHom_apply, ← map_zsmul]
    congr 1
    exact Subtype.ext hc
  have hz1 : (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sP
      (integralComponentAt z).subschemeι r).1 = Function.locallyFinsuppWithin.single z 1 := by
    have := isIntegral_integralComponentAt z
    have hgen := subschemeι_base_genericPoint_integralComponentAt z
    rw [cycleAssociatedToClosedSubscheme_eq_single _ _ _ _ (by rw [hgen, hz]), hgen]
  have hval : (1 : ℤ) = c ((zeroSection sP).base z) := by
    have h := congrArg (fun A : CycleGroup (fieldChowSituation K) sP r => A.1 z)
      (hpush1.symm.trans hpush2)
    simp only [AddSubgroup.coe_zsmul] at h
    rw [hz1, properPushforward_single_zeroSection sP z r hz hsing] at h
    simpa using h
  rw [hc, ← hval, one_smul]

end ZeroSection

end Stacks.Intersection

end
