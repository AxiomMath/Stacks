module

public import StacksFrontier.AlgebraicGeometry.Intersection.ProjectionFormulaFlat.ZeroFibreDegeneration.LineFamilyZeroSection

/-!
# The projection formula for `P × 𝐏¹ ⟶ P` on cycles supported on `P × 0`

Part of Tag 0B1M (`ZeroFibreDegeneration`). Let `X ⟶ P` be a closed immersion of varieties over
an algebraically closed field `K`.

## Main results

* `Stacks.Intersection.torFormula_properPushforward_eq_properPushforward_zeroSection` — the
  projection formula `pr_*(γ) · X = pr_*(γ · X × 𝐏¹)` for cycles `γ` on `P × 0`.
* `Stacks.Intersection.properPushforward_properPushforward_product_zeroSection` — intersecting
  with the zero section commutes with the inclusion `X × 𝐏¹ ⊆ P × 𝐏¹`.

## Implementation notes

For a closed subvariety `Z ⊆ P`, `Z × 0 = (Z × 𝐏¹) · (P × 0)` by Tag 0B07, so
`(Z × 0) · (X × 𝐏¹)` is `((Z × 𝐏¹) · (X × 𝐏¹)) · (P × 0)` by Tag 0B1L, which is
`pr^*(Z · X) · (P × 0)` by Tag 0B0Z, and `pr_*(pr^* a · (P × 0)) = a` by Tag 0B07.

## References

* [Stacks Project, Tag 0B07](https://stacks.math.columbia.edu/tag/0B07)
* [Stacks Project, Tag 0B1L](https://stacks.math.columbia.edu/tag/0B1L)
* [Stacks Project, Tag 0B0Z](https://stacks.math.columbia.edu/tag/0B0Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.TorFormula Stacks.Chow

universe u

namespace Stacks.Intersection

variable (K : Type u) [Field K]

section Projection

variable {K} [IsAlgClosed K] {X P : Scheme.{u}} (sP : P ⟶ Spec (.of K)) [IsVariety K sP]
  (ι : X ⟶ P) [IsClosedImmersion ι] [IsVariety K (ι ≫ sP)]

omit [IsAlgClosed K] [IsVariety K sP] in
/-- The part of the image of the zero section lying over `A ⊆ P` is the image of `A`. -/
theorem range_zeroSection_inter_preimage (A : Set P) :
    Set.range (zeroSection sP).base ∩
        (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))).base ⁻¹' A =
      (zeroSection sP).base '' A := by
  ext x
  constructor
  · rintro ⟨⟨y, rfl⟩, hy⟩
    refine ⟨y, ?_, rfl⟩
    rwa [Set.mem_preimage, ← Scheme.Hom.comp_apply, zeroSection_comp_fst] at hy
  · rintro ⟨y, hy, rfl⟩
    refine ⟨⟨y, rfl⟩, ?_⟩
    rwa [Set.mem_preimage, ← Scheme.Hom.comp_apply, zeroSection_comp_fst]

omit [IsAlgClosed K] [IsVariety K sP] in
/-- The zero section preserves dimensions of subsets. -/
theorem topologicalKrullDim_image_zeroSection (A : Set P) :
    topologicalKrullDim ((zeroSection sP).base '' A) = topologicalKrullDim A :=
  topologicalKrullDim_image_eq_of_isEmbedding (zeroSection sP).isClosedEmbedding.isEmbedding A

omit [IsAlgClosed K] in
/-- The closure of the image of the generic point of `P` under the zero section is the image of
the zero section. -/
theorem closure_zeroSection_genericPoint :
    closure ({(zeroSection sP).base (genericPoint P)} : Set (projectiveLineProduct sP)) =
      Set.range (zeroSection sP).base :=
  (range_eq_closure_singleton (zeroSection sP)).symm

/-- Proper intersection of two prime cycles is proper intersection of their closures. -/
theorem intersectProperly_closure_of_single {Y' : Scheme.{u}} [DecidableEq Y'] {a b : Y'}
    (h : AlgebraicCycle.IntersectProperly (Function.locallyFinsuppWithin.single a (1 : ℤ))
      (Function.locallyFinsuppWithin.single b (1 : ℤ))) :
    AlgebraicGeometry.IntersectProperly
      ⟨closure {a}, isIrreducible_singleton.closure, isClosed_closure⟩
      ⟨closure {b}, isIrreducible_singleton.closure, isClosed_closure⟩ :=
  h _ _ (by rw [genericPoint_closure_singleton]; simp)
    (by rw [genericPoint_closure_singleton]; simp)

/-- Proper intersection of two point closures, in terms of dimensions. -/
theorem intersectProperly_closure_singleton_iff {Y' : Scheme.{u}} (a b : Y') :
    AlgebraicGeometry.IntersectProperly
      ⟨closure {a}, isIrreducible_singleton.closure, isClosed_closure⟩
      ⟨closure {b}, isIrreducible_singleton.closure, isClosed_closure⟩ ↔
    topologicalKrullDim ↥(closure ({a} : Set Y') ∩ closure {b}) + topologicalKrullDim Y' ≤
      topologicalKrullDim (closure ({a} : Set Y')) + topologicalKrullDim (closure ({b} : Set Y')) :=
  AlgebraicGeometry.intersectProperly_iff ..

/-- The generic point of the integral component at `e` maps to `e`. -/
private theorem integralComponentAt_subschemeι_genericPoint {Y : Scheme.{u}} (e : Y)
    [AlgebraicGeometry.IsIntegral (integralComponentAt e).subscheme] :
    (integralComponentAt e).subschemeι.base (genericPoint (integralComponentAt e).subscheme) =
      e := by
  simpa [genericPointOf] using genericPointOf_integralComponentAt e

/-- The cycle of the integral component at `e` is the prime cycle of `e`. -/
private theorem cycleAssociatedToClosedSubscheme_integralComponentAt_eq_single {F : Type u}
    [Field F] {Y : Scheme.{u}} [DecidableEq Y] (sY : Y ⟶ Spec (.of F)) [LocallyOfFiniteType sY]
    (e : Y) (k : ℤ)
    (he : relativeDimension (fieldChowSituation F).dimensionFunction sY e = k) :
    (cycleAssociatedToClosedSubscheme (fieldChowSituation F) sY
      (integralComponentAt e).subschemeι k).1 = Function.locallyFinsuppWithin.single e 1 := by
  have := isIntegral_integralComponentAt e
  have hgen := integralComponentAt_subschemeι_genericPoint e
  obtain rfl := Subsingleton.elim ‹DecidableEq Y› (Classical.decEq Y)
  rw [cycleAssociatedToClosedSubscheme_eq_single _ _ _ _ (by rw [hgen, he]), hgen]

/-- The intersection product is additive in its first argument, on sums of prime cycles. -/
private theorem torFormulaCycleIntersectionProduct_sum_single_left {F : Type u} [Field F]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of F)) [DecidableEq Y] [LocallyOfFiniteType sY]
    [IsLocallyNoetherian Y] [CompactSpace Y]
    (hY : IsRegular Y) (n : ℤ) {J : Type*} (s : Finset J) (a : J → ℤ) (f : J → Y)
    (c : AlgebraicCycle Y ℤ) :
    (⟨torFormulaCycleIntersectionProduct (fieldChowSituation F) sY hY n
        (∑ e ∈ s, a e • Function.locallyFinsuppWithin.single (f e) 1) c,
      torFormulaCycleIntersectionProduct_mem_cyclesOfDimension _ _ _ _ _ _⟩ :
        CycleGroup (fieldChowSituation F) sY n) =
      ∑ e ∈ s, a e • ⟨torFormulaCycleIntersectionProduct (fieldChowSituation F) sY hY n
        (Function.locallyFinsuppWithin.single (f e) 1) c,
        torFormulaCycleIntersectionProduct_mem_cyclesOfDimension _ _ _ _ _ _⟩ := by
  apply Subtype.ext
  rw [AddSubgroup.val_finsetSum]
  simp only [AddSubgroup.coe_zsmul]
  rw [torFormulaCycleIntersectionProduct, cycleIntersectionProduct_sum_left]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [cycleIntersectionProduct_zsmul_left _ _ (finite_support_of_compactSpace _)
    (finite_support_of_compactSpace _)]
  rfl

/-- The intersection product of a cycle of finite support, as a sum over its components. -/
private theorem torFormulaCycleIntersectionProduct_eq_sum_single_left {F : Type u}
    [Field F] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of F)) [DecidableEq Y] [LocallyOfFiniteType sY]
    [IsLocallyNoetherian Y] [CompactSpace Y]
    (hY : IsRegular Y) (n : ℤ) (c d : AlgebraicCycle Y ℤ) (hc : (Function.support c).Finite) :
    (⟨torFormulaCycleIntersectionProduct (fieldChowSituation F) sY hY n c d,
      torFormulaCycleIntersectionProduct_mem_cyclesOfDimension _ _ _ _ _ _⟩ :
        CycleGroup (fieldChowSituation F) sY n) =
      ∑ e ∈ hc.toFinset, c e • ⟨torFormulaCycleIntersectionProduct (fieldChowSituation F) sY hY n
        (Function.locallyFinsuppWithin.single e 1) d,
        torFormulaCycleIntersectionProduct_mem_cyclesOfDimension _ _ _ _ _ _⟩ :=
  (Subtype.ext (congrArg (torFormulaCycleIntersectionProduct (fieldChowSituation F) sY hY n · d)
    (AlgebraicCycle.eq_sum_zsmul_single hc))).trans
    (torFormulaCycleIntersectionProduct_sum_single_left sY hY n hc.toFinset c id d)

/-- The proper pushforward of a cycle of finite support is the sum of the pushforwards of its
components. -/
private theorem properPushforward_eq_sum_single {F : Type u} [Field F] {Y Z : Scheme.{u}}
    [DecidableEq Y] [DecidableEq Z] (sY : Y ⟶ Spec (.of F))
    [LocallyOfFiniteType sY] (sZ : Z ⟶ Spec (.of F)) [LocallyOfFiniteType sZ] (f : Y ⟶ Z)
    [IsProper f] (hf : f ≫ sZ = sY) (k : ℤ) (γ : CycleGroup (fieldChowSituation F) sY k)
    (hfin : (Function.support γ.1).Finite) (g : Y → Z)
    (hmem : ∀ q ∈ hfin.toFinset, Function.locallyFinsuppWithin.single q (1 : ℤ) ∈
      cyclesOfDimension (fieldChowSituation F) sY k)
    (hg : ∀ q (hq : q ∈ hfin.toFinset),
      (properPushforward (fieldChowSituation F) sY sZ f hf k ⟨_, hmem q hq⟩).1 =
        Function.locallyFinsuppWithin.single (g q) 1) :
    (properPushforward (fieldChowSituation F) sY sZ f hf k γ).1 =
      ∑ q ∈ hfin.toFinset, γ.1 q • Function.locallyFinsuppWithin.single (g q) 1 := by
  have hsum : γ = ∑ q ∈ hfin.toFinset.attach, γ.1 q •
      (⟨Function.locallyFinsuppWithin.single q 1, hmem q q.2⟩ :
        CycleGroup (fieldChowSituation F) sY k) := by
    apply Subtype.ext
    rw [AddSubgroup.val_finsetSum]
    simp only [AddSubgroup.coe_zsmul]
    rw [Finset.sum_attach hfin.toFinset
      (fun q => γ.1 q • Function.locallyFinsuppWithin.single q 1)]
    exact AlgebraicCycle.eq_sum_zsmul_single hfin
  refine (congrArg (fun c => (properPushforward (fieldChowSituation F) sY sZ f hf k c).1)
    hsum).trans ?_
  rw [← properPushforwardHom_apply, map_sum, AddSubgroup.val_finsetSum,
    ← Finset.sum_attach hfin.toFinset
      (fun q => γ.1 q • Function.locallyFinsuppWithin.single (g q) (1 : ℤ))]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_zsmul, AddSubgroup.coe_zsmul, properPushforwardHom_apply, hg q q.2]

open scoped Classical in
/-- **The intersection with `X` of a subvariety `Z ⊆ P`, computed on `P × 𝐏¹`.** For a closed
subvariety `Z = closure {z}` of `P` of dimension `r` meeting `X` properly, the intersection
product `Z · X` on `P` is the pushforward along `pr : P × 𝐏¹ ⟶ P` of the product of the image
`Z × 0` of `Z` under the zero section with `X × 𝐏¹`. -/
theorem torFormula_single_eq_properPushforward_zeroSection (hP : IsRegular P)
    (d p r n : ℕ) (hd : topologicalKrullDim X = (d : WithBot ℕ∞))
    (hp : topologicalKrullDim P = (p : WithBot ℕ∞)) (z : P)
    (hz : relativeDimension (fieldChowSituation K).dimensionFunction sP z = r)
    (hrn : r + d = p + n)
    (hprop : AlgebraicGeometry.IntersectProperly
      ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩
      ⟨closure {ι.base (genericPoint X)}, isIrreducible_singleton.closure, isClosed_closure⟩) :
    letI : IsLocallyNoetherian P := isLocallyNoetherian_of_isRegular hP
    letI : IsLocallyNoetherian (projectiveLineProduct sP) :=
      isLocallyNoetherian_of_isRegular (isRegular_projectiveLineProduct sP hP)
    torFormulaCycleIntersectionProduct (fieldChowSituation K) sP hP n
        (Function.locallyFinsuppWithin.single z 1)
        (Function.locallyFinsuppWithin.single (ι.base (genericPoint X)) 1) =
      (properPushforward (fieldChowSituation K)
        (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP) sP
        (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))) rfl n
        ⟨torFormulaCycleIntersectionProduct (fieldChowSituation K)
          (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP)
          (isRegular_projectiveLineProduct sP hP) n
          (Function.locallyFinsuppWithin.single ((zeroSection sP).base z) 1)
          (Function.locallyFinsuppWithin.single
            ((familyBaseChange sP ι).base (genericPoint (projectiveLineProduct (ι ≫ sP)))) 1),
          torFormulaCycleIntersectionProduct_mem_cyclesOfDimension _ _ _ _ _ _⟩).1 := by
  let : IsLocallyNoetherian P := isLocallyNoetherian_of_isRegular hP
  let : IsLocallyNoetherian (projectiveLineProduct sP) :=
    isLocallyNoetherian_of_isRegular (isRegular_projectiveLineProduct sP hP)
  set L := relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)
  set hQ := isRegular_projectiveLineProduct sP hP
  set w := lineGenericPoint sP z
  set δ := (zeroSection sP).base (genericPoint P)
  set y := (familyBaseChange sP ι).base (genericPoint (projectiveLineProduct (ι ≫ sP)))
  set x := ι.base (genericPoint X)
  -- dimensions
  have he : topologicalKrullDim (projectiveLineProduct sP) =
      topologicalKrullDim P + ((1 : ℕ) : WithBot ℕ∞) := by
    rw [topologicalKrullDim_projectiveLineProduct]; rfl
  have hdQ : topologicalKrullDim (projectiveLineProduct sP) = ((p + 1 : ℕ) : WithBot ℕ∞) := by
    rw [he, hp]; push_cast; rfl
  have hf := relativeDimension_of_flat_of_isVariety K (pullback.fst sP L ≫ sP) sP
    (pullback.fst sP L) rfl 1 he
  have hzr : topologicalKrullDim (closure ({z} : Set P)) = (r : WithBot ℕ∞) := by
    rw [topologicalKrullDim_closure_singleton_eq K sP z, hz]; rfl
  have hw : topologicalKrullDim (closure ({w} : Set (projectiveLineProduct sP))) =
      ((r + 1 : ℕ) : WithBot ℕ∞) := by
    rw [topologicalKrullDim_closure_lineGenericPoint, hzr]; push_cast; rfl
  have hδ : topologicalKrullDim (closure ({δ} : Set (projectiveLineProduct sP))) =
      (p : WithBot ℕ∞) := by
    rw [topologicalKrullDim_closure_image_genericPoint, hp]
  have hy : topologicalKrullDim (closure ({y} : Set (projectiveLineProduct sP))) =
      ((d + 1 : ℕ) : WithBot ℕ∞) := by
    rw [topologicalKrullDim_closure_familyBaseChange_genericPoint, hd]; push_cast; rfl
  have hxd : relativeDimension (fieldChowSituation K).dimensionFunction sP x = d := by
    have h := topologicalKrullDim_closure_image_genericPoint ι
    rw [topologicalKrullDim_closure_singleton_eq K sP, hd] at h
    have h' : (relativeDimension (fieldChowSituation K).dimensionFunction sP x).toNat = d := by
      exact_mod_cast h
    have := relativeDimension_fieldChowSituation_nonneg K sP x
    omega
  have hxdim : topologicalKrullDim (closure ({x} : Set P)) = (d : WithBot ℕ∞) := by
    rw [topologicalKrullDim_closure_image_genericPoint, hd]
  -- the closed sets involved
  have hcw : closure ({w} : Set (projectiveLineProduct sP)) =
      (pullback.fst sP L).base ⁻¹' closure {z} := closure_lineGenericPoint sP z
  have hcδ : closure ({δ} : Set (projectiveLineProduct sP)) = Set.range (zeroSection sP).base :=
    closure_zeroSection_genericPoint sP
  have hcy : closure ({y} : Set (projectiveLineProduct sP)) =
      (pullback.fst sP L).base ⁻¹' Set.range ι.base := closure_familyBaseChange_genericPoint sP ι
  have hcx : closure ({x} : Set P) = Set.range ι.base := (range_eq_closure_singleton ι).symm
  have hwδset : closure ({w} : Set (projectiveLineProduct sP)) ∩ closure {δ} =
      (zeroSection sP).base '' closure {z} := by
    rw [hcw, hcδ, Set.inter_comm, range_zeroSection_inter_preimage]
  have hδyset : closure ({δ} : Set (projectiveLineProduct sP)) ∩ closure {y} =
      (zeroSection sP).base '' Set.range ι.base := by
    rw [hcδ, hcy, range_zeroSection_inter_preimage]
  have htriset : closure ({w} : Set (projectiveLineProduct sP)) ∩ closure {δ} ∩ closure {y} =
      (zeroSection sP).base '' (closure {z} ∩ Set.range ι.base) := by
    rw [hcw, hcδ, hcy, ← range_zeroSection_inter_preimage, Set.preimage_inter]
    ext q
    simp only [Set.mem_inter_iff]
    tauto
  have hprop' : topologicalKrullDim (↥(closure ({z} : Set P) ∩ Set.range ι.base)) +
      (p : WithBot ℕ∞) ≤ ((r + d : ℕ) : WithBot ℕ∞) := by
    have h := hprop
    rw [AlgebraicGeometry.intersectProperly_iff] at h
    change topologicalKrullDim (↥(closure ({z} : Set P) ∩ closure {x})) + topologicalKrullDim P ≤
      topologicalKrullDim (closure ({z} : Set P)) + topologicalKrullDim (closure ({x} : Set P))
      at h
    rw [hcx, hp, hzr, ← hcx, hxdim, hcx] at h
    exact_mod_cast h
  -- the pairwise proper intersections
  have hwδ : AlgebraicGeometry.IntersectProperly
      ⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩
      ⟨closure {δ}, isIrreducible_singleton.closure, isClosed_closure⟩ := by
    rw [intersectProperly_closure_singleton_iff, hwδset, topologicalKrullDim_image_zeroSection,
      hzr, hdQ, hw, hδ]
    exact_mod_cast (by omega : r + (p + 1) ≤ r + 1 + p)
  have hδy : AlgebraicGeometry.IntersectProperly
      ⟨closure {δ}, isIrreducible_singleton.closure, isClosed_closure⟩
      ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩ := by
    rw [intersectProperly_closure_singleton_iff, hδyset, topologicalKrullDim_image_zeroSection,
      ← hcx, hxdim, hdQ, hy, hδ]
    exact_mod_cast (by omega : d + (p + 1) ≤ p + (d + 1))
  -- the flat pullbacks of the two prime cycles
  set α := cycleAssociatedToClosedSubscheme (fieldChowSituation K) sP
    (integralComponentAt z).subschemeι (r : ℤ)
  set β := cycleAssociatedToClosedSubscheme (fieldChowSituation K) sP ι (d : ℤ)
  have hα1 : α.1 = Function.locallyFinsuppWithin.single z 1 :=
    cycleAssociatedToClosedSubscheme_integralComponentAt_eq_single sP z r hz
  have hβ1 : β.1 = Function.locallyFinsuppWithin.single x 1 := by
    rw [cycleAssociatedToClosedSubscheme_eq_single _ _ _ _ hxd]
  have hαβ : AlgebraicCycle.IntersectProperly α.1 β.1 := by
    rw [hα1, hβ1]
    have h := AlgebraicCycle.intersectProperly_single_genericPoint hprop
    have e1 : (⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩ :
        IrreducibleCloseds P).isIrreducible.genericPoint = z := genericPoint_closure_singleton z
    have e2 : (⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩ :
        IrreducibleCloseds P).isIrreducible.genericPoint = x := genericPoint_closure_singleton x
    rwa [e1, e2] at h
  have hpα : (flatPullback (fieldChowSituation K) (pullback.fst sP L ≫ sP) sP (pullback.fst sP L)
      rfl 1 hf (r : ℤ) α).1 = Function.locallyFinsuppWithin.single w 1 :=
    flatPullback_primeCycle_eq_single sP z hf r hz
  have hpβ : (flatPullback (fieldChowSituation K) (pullback.fst sP L ≫ sP) sP (pullback.fst sP L)
      rfl 1 hf (d : ℤ) β).1 = Function.locallyFinsuppWithin.single y 1 :=
    flatPullback_cycleAssociatedToClosedSubscheme_eq_single sP ι hf d hxd
  have hZ := CycleFlatPullback.flatPullback_torFormulaCycleIntersectionProduct_eq K
    (pullback.fst sP L ≫ sP) sP hQ hP (pullback.fst sP L) rfl 1 p r d n hp he hrn α β hαβ
  have hwy : AlgebraicGeometry.IntersectProperly
      ⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩
      ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩ := by
    have h := hZ.1
    rw [hpα, hpβ] at h
    exact intersectProperly_closure_of_single h
  have htriple : topologicalKrullDim
      (↥(closure ({w} : Set (projectiveLineProduct sP)) ∩ closure {δ} ∩ closure {y})) +
        ((2 * (p + 1) : ℕ) : WithBot ℕ∞) ≤ ((r + 1 + p + (d + 1) : ℕ) : WithBot ℕ∞) := by
    rw [htriset, topologicalKrullDim_image_zeroSection]
    calc topologicalKrullDim (↥(closure ({z} : Set P) ∩ Set.range ι.base)) +
          ((2 * (p + 1) : ℕ) : WithBot ℕ∞)
        = (topologicalKrullDim (↥(closure ({z} : Set P) ∩ Set.range ι.base)) +
            (p : WithBot ℕ∞)) + ((p + 2 : ℕ) : WithBot ℕ∞) := by
          rw [add_assoc]; congr 1; push_cast; ring
      _ ≤ ((r + d : ℕ) : WithBot ℕ∞) + ((p + 2 : ℕ) : WithBot ℕ∞) := add_le_add hprop' le_rfl
      _ = ((r + 1 + p + (d + 1) : ℕ) : WithBot ℕ∞) := by push_cast; ring
  have hswap := torFormula_single_single_swap K (pullback.fst sP L ≫ sP) hQ w δ y (p + 1) (r + 1)
    p (d + 1) hdQ hw hδ hy hwδ hδy hwy htriple
  have e1 : (((r + 1 : ℕ) : ℤ) + (p : ℤ) - ((p + 1 : ℕ) : ℤ)) = (r : ℤ) := by push_cast; ring
  have e2 : (((r + 1 : ℕ) : ℤ) + (p : ℤ) + ((d + 1 : ℕ) : ℤ) - 2 * ((p + 1 : ℕ) : ℤ)) =
      (n : ℤ) := by
    push_cast; omega
  have e3 : (((r + 1 : ℕ) : ℤ) + ((d + 1 : ℕ) : ℤ) - ((p + 1 : ℕ) : ℤ)) =
      (n : ℤ) + ((1 : ℕ) : ℤ) := by push_cast; omega
  rw [e1, e2, e3] at hswap
  have hi := torFormula_lineGenericPoint_zeroSection sP hQ z r hz hdQ
  have hiv := properPushforward_flatPullback_product_zeroSection sP hQ hf n
    ⟨torFormulaCycleIntersectionProduct (fieldChowSituation K) sP hP (n : ℤ) α.1 β.1,
      torFormulaCycleIntersectionProduct_mem_cyclesOfDimension _ _ _ _ _ _⟩
  have hprod : torFormulaCycleIntersectionProduct (fieldChowSituation K) (pullback.fst sP L ≫ sP)
      hQ n (flatPullback (fieldChowSituation K) (pullback.fst sP L ≫ sP) sP (pullback.fst sP L)
        rfl 1 hf n ⟨torFormulaCycleIntersectionProduct (fieldChowSituation K) sP hP (n : ℤ) α.1 β.1,
          torFormulaCycleIntersectionProduct_mem_cyclesOfDimension _ _ _ _ _ _⟩).1
        (Function.locallyFinsuppWithin.single δ 1) =
      torFormulaCycleIntersectionProduct (fieldChowSituation K) (pullback.fst sP L ≫ sP) hQ n
        (Function.locallyFinsuppWithin.single ((zeroSection sP).base z) 1)
        (Function.locallyFinsuppWithin.single y 1) := by
    rw [hZ.2, hpα, hpβ, ← hswap, hi]
  calc torFormulaCycleIntersectionProduct (fieldChowSituation K) sP hP n
        (Function.locallyFinsuppWithin.single z 1) (Function.locallyFinsuppWithin.single x 1)
      = torFormulaCycleIntersectionProduct (fieldChowSituation K) sP hP (n : ℤ) α.1 β.1 := by
        rw [hα1, hβ1]
    _ = _ := (congrArg Subtype.val hiv).symm
    _ = _ := congrArg (fun c => (properPushforward (fieldChowSituation K)
        (pullback.fst sP L ≫ sP) sP (pullback.fst sP L) rfl n c).1) (Subtype.ext hprod)


open scoped Classical in
/-- **The projection formula for `pr : P × 𝐏¹ ⟶ P` on cycles supported on `P × 0`.** For an
`r`-cycle `γ` on `P × 𝐏¹` supported on the image of the zero section whose pushforward meets
`X` properly, `pr_*(γ) · X = pr_*(γ · (X × 𝐏¹))`. -/
theorem torFormula_properPushforward_eq_properPushforward_zeroSection (hP : IsRegular P)
    (d p r n : ℕ) (hd : topologicalKrullDim X = (d : WithBot ℕ∞))
    (hp : topologicalKrullDim P = (p : WithBot ℕ∞)) (hrn : r + d = p + n)
    (γ : CycleGroup (fieldChowSituation K)
      (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP) (r : ℤ))
    (hγ : ∀ q, γ.1 q ≠ 0 → q ∈ Set.range (zeroSection sP).base)
    (hγX : AlgebraicCycle.IntersectProperly
      (properPushforward (fieldChowSituation K)
        (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP) sP
        (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))) rfl r γ).1
      (Function.locallyFinsuppWithin.single (ι.base (genericPoint X)) 1)) :
    letI : IsLocallyNoetherian P := isLocallyNoetherian_of_isRegular hP
    letI : IsLocallyNoetherian (projectiveLineProduct sP) :=
      isLocallyNoetherian_of_isRegular (isRegular_projectiveLineProduct sP hP)
    torFormulaCycleIntersectionProduct (fieldChowSituation K) sP hP n
        (properPushforward (fieldChowSituation K)
          (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP) sP
          (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))) rfl r γ).1
        (Function.locallyFinsuppWithin.single (ι.base (genericPoint X)) 1) =
      (properPushforward (fieldChowSituation K)
        (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP) sP
        (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))) rfl n
        ⟨torFormulaCycleIntersectionProduct (fieldChowSituation K)
          (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP)
          (isRegular_projectiveLineProduct sP hP) n γ.1
          (Function.locallyFinsuppWithin.single
            ((familyBaseChange sP ι).base (genericPoint (projectiveLineProduct (ι ≫ sP)))) 1),
          torFormulaCycleIntersectionProduct_mem_cyclesOfDimension _ _ _ _ _ _⟩).1 := by
  let : IsLocallyNoetherian P := isLocallyNoetherian_of_isRegular hP
  let : IsLocallyNoetherian (projectiveLineProduct sP) :=
    isLocallyNoetherian_of_isRegular (isRegular_projectiveLineProduct sP hP)
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace sP
  have : CompactSpace (projectiveLineProduct sP) := QuasiCompact.compactSpace_of_compactSpace
    (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP)
  have hfin := finite_support_of_compactSpace γ.1
  have hsec : ∀ q ∈ hfin.toFinset,
      (zeroSection sP).base
        ((pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))).base q) = q := by
    intro q hq
    obtain ⟨z, rfl⟩ := hγ q (hfin.mem_toFinset.1 hq)
    have h : (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))).base
        ((zeroSection sP).base z) = z := by
      rw [← Scheme.Hom.comp_apply, zeroSection_comp_fst]; rfl
    rw [h]
  have hdimq : ∀ q ∈ hfin.toFinset,
      relativeDimension (fieldChowSituation K).dimensionFunction sP
        ((pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))).base q) = r := by
    intro q hq
    have h := (mem_cyclesOfDimension_iff_forall_point (fieldChowSituation K) _ r γ.1).1 γ.2 q
      (hfin.mem_toFinset.1 hq)
    have h' := relativeDimension_zeroSection sP
      ((pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))).base q)
    rw [hsec q hq] at h'
    rw [← h']; exact h
  have hmemq : ∀ q ∈ hfin.toFinset, Function.locallyFinsuppWithin.single q (1 : ℤ) ∈
      cyclesOfDimension (fieldChowSituation K)
        (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP) r := by
    intro q hq
    rw [← hsec q hq]
    exact single_zeroSection_mem_cyclesOfDimension sP _ r (hdimq q hq)
  -- the pushforward of `γ`
  have hpush := properPushforward_eq_sum_single
    (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP) sP
    (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))) rfl r γ hfin
    (fun q => (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))).base q)
    hmemq fun q hq => by
      have h := properPushforward_single_zeroSection sP
        ((pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))).base q) r
        (hdimq q hq) (by rw [hsec q hq]; exact hmemq q hq)
      convert h using 4; rw [hsec q hq]
  -- the coefficients of the pushforward
  have hinj : ∀ q ∈ hfin.toFinset, ∀ q' ∈ hfin.toFinset,
      (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))).base q =
        (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))).base q' →
        q = q' := by
    intro q hq q' hq' h
    rw [← hsec q hq, ← hsec q' hq', h]
  have hcoef : ∀ q ∈ hfin.toFinset, (properPushforward (fieldChowSituation K)
      (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP) sP
      (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))) rfl r γ).1
      ((pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))).base q) =
        γ.1 q := by
    intro q hq
    rw [hpush, Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply,
      Finset.sum_eq_single q]
    · simp
    · intro q' hq' hne
      rw [Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply,
        Function.locallyFinsuppWithin.single_apply, ite_eq_right, smul_zero]
      exact fun h => hne (hinj q' hq' q hq h.symm)
    · exact fun h => (h hq).elim
  have hpropq : ∀ q ∈ hfin.toFinset, AlgebraicGeometry.IntersectProperly
      ⟨closure {(pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))).base q},
        isIrreducible_singleton.closure, isClosed_closure⟩
      ⟨closure {ι.base (genericPoint X)}, isIrreducible_singleton.closure, isClosed_closure⟩ := by
    intro q hq
    refine hγX _ _ ?_ ?_
    · rw [genericPoint_closure_singleton, hcoef q hq]; exact hfin.mem_toFinset.1 hq
    · rw [genericPoint_closure_singleton, Function.locallyFinsuppWithin.single_apply,
        ite_eq_left rfl]; exact one_ne_zero
  -- both sides as sums over the components of `γ`
  rw [hpush, torFormulaCycleIntersectionProduct, cycleIntersectionProduct_sum_left,
    torFormulaCycleIntersectionProduct_eq_sum_single_left _ _ _ _ _ hfin,
    ← properPushforwardHom_apply, map_sum, AddSubgroup.val_finsetSum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [cycleIntersectionProduct_zsmul_left _ _ (finite_support_of_compactSpace _)
    (finite_support_of_compactSpace _), map_zsmul, AddSubgroup.coe_zsmul,
    properPushforwardHom_apply]
  congr 1
  have h := torFormula_single_eq_properPushforward_zeroSection sP ι hP d p r n hd hp _
    (hdimq q hq) hrn (hpropq q hq)
  rw [hsec q hq] at h
  exact h


/-- **The zero fibre commutes with the inclusion `X × 𝐏¹ ⊆ P × 𝐏¹`.** For a point `e` of
`X × 𝐏¹`, the pushforward to `P` of the cycle of the zero fibre of the closure of `e` is the
cycle of the zero fibre of the closure of its image in `P × 𝐏¹`. -/
theorem properPushforward_zeroFiber_familyBaseChange (e : projectiveLineProduct (ι ≫ sP))
    (k : ℤ) :
    properPushforward (fieldChowSituation K) (ι ≫ sP) sP ι rfl k
        (cycleAssociatedToClosedSubscheme (fieldChowSituation K) (ι ≫ sP)
          (zeroFiber (ι ≫ sP) (integralComponentAt e)).subschemeι k) =
      cycleAssociatedToClosedSubscheme (fieldChowSituation K) sP
        (zeroFiber sP (integralComponentAt ((familyBaseChange sP ι).base e))).subschemeι k := by
  have hgen := integralComponentAt_subschemeι_genericPoint e
  have hker :  ((integralComponentAt e).subschemeι ≫ familyBaseChange sP ι).ker =
      integralComponentAt ((familyBaseChange sP ι).base e) := by
    rw [ker_eq_integralComponentAt, Scheme.Hom.comp_apply, hgen]
  have hsq : IsPullback
      (pullback.fst (zeroSection (ι ≫ sP)) (integralComponentAt e).subschemeι ≫ ι)
      (pullback.snd (zeroSection (ι ≫ sP)) (integralComponentAt e).subschemeι) (zeroSection sP)
      ((integralComponentAt e).subschemeι ≫ familyBaseChange sP ι) :=
    ((IsPullback.of_hasPullback (zeroSection (ι ≫ sP))
      (integralComponentAt e).subschemeι).flip.paste_vert
      (isPullback_constantSection_familyBaseChange sP ι integralZeroSection)).flip
  rw [properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp]
  rw [cycleAssociatedToClosedSubscheme_eq_of_iso (fieldChowSituation K) sP
    ((zeroFiber (ι ≫ sP) (integralComponentAt e)).subschemeι ≫ ι)
    (pullback.fst (zeroSection (ι ≫ sP)) (integralComponentAt e).subschemeι ≫ ι)
    (Scheme.IdealSheafData.comapIso _ _)
    (by rw [← Category.assoc]; exact congrArg (· ≫ ι) (Scheme.IdealSheafData.comapIso_hom_fst _ _))]
  rw [cycleAssociatedToClosedSubscheme_eq_of_iso (fieldChowSituation K) sP
    (pullback.fst (zeroSection (ι ≫ sP)) (integralComponentAt e).subschemeι ≫ ι)
    (pullback.fst (zeroSection sP) ((integralComponentAt e).subschemeι ≫ familyBaseChange sP ι))
    hsq.isoPullback
    hsq.isoPullback_hom_fst]
  rw [cycleAssociatedToClosedSubscheme_ker, Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    hker]
  rfl

omit [IsAlgClosed K] in
open scoped Classical in
/-- Pushing forward a prime cycle along a closed immersion gives the prime cycle of the image. -/
theorem properPushforward_single_of_isClosedImmersion {Y Z : Scheme.{u}}
    (sZ : Z ⟶ Spec (.of K)) [LocallyOfFiniteType sZ] (sY : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType sY] (i : Y ⟶ Z) [IsClosedImmersion i] (hi : i ≫ sZ = sY) (k : ℤ)
    (e : Y) (he : relativeDimension (fieldChowSituation K).dimensionFunction sY e = k)
    (hmem : Function.locallyFinsuppWithin.single e (1 : ℤ) ∈
      cyclesOfDimension (fieldChowSituation K) sY k) :
    (properPushforward (fieldChowSituation K) sY sZ i hi k ⟨_, hmem⟩).1 =
      Function.locallyFinsuppWithin.single (i.base e) 1 := by
  have := isIntegral_integralComponentAt e
  have hgen := integralComponentAt_subschemeι_genericPoint e
  have h1 : (⟨_, hmem⟩ : CycleGroup (fieldChowSituation K) sY k) =
      cycleAssociatedToClosedSubscheme (fieldChowSituation K) sY
        (integralComponentAt e).subschemeι k :=
    Subtype.ext (cycleAssociatedToClosedSubscheme_integralComponentAt_eq_single sY e k he).symm
  rw [h1, properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp,
    cycleAssociatedToClosedSubscheme_eq_single _ _ _ _ (by
      rw [Scheme.Hom.comp_apply, hgen, ← relativeDimension_comp_closedImmersion, hi, he]),
    Scheme.Hom.comp_apply, hgen]

open scoped Classical in
/-- **Intersecting with the zero section commutes with `X × 𝐏¹ ⊆ P × 𝐏¹`.** For a
`(k + 1)`-cycle `β` on `X × 𝐏¹` none of whose components, nor their images in `P × 𝐏¹`, lies on
the zero section, `ι_* pr_{X,*}(β · X × 0) = pr_{P,*}(j_* β · P × 0)`. -/
theorem properPushforward_properPushforward_product_zeroSection (hX : IsRegular X)
    (hP : IsRegular P) (k : ℤ)
    (β : CycleGroup (fieldChowSituation K)
      (pullback.fst (ι ≫ sP) (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ ι ≫ sP)
      (k + 1))
    (hβ1 : ∀ e, β.1 e ≠ 0 → ¬ Set.range (integralComponentAt e).subschemeι.base ⊆
      Set.range (zeroSection (ι ≫ sP)).base)
    (hβ2 : ∀ e, β.1 e ≠ 0 → ¬ Set.range
      (integralComponentAt ((familyBaseChange sP ι).base e)).subschemeι.base ⊆
        Set.range (zeroSection sP).base) :
    letI : IsLocallyNoetherian (projectiveLineProduct sP) :=
      isLocallyNoetherian_of_isRegular (isRegular_projectiveLineProduct sP hP)
    letI : IsLocallyNoetherian (projectiveLineProduct (ι ≫ sP)) :=
      isLocallyNoetherian_of_isRegular (isRegular_projectiveLineProduct (ι ≫ sP) hX)
    properPushforward (fieldChowSituation K) (ι ≫ sP) sP ι rfl k
        (properPushforward (fieldChowSituation K)
          (pullback.fst (ι ≫ sP) (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ ι ≫ sP)
          (ι ≫ sP) (pullback.fst (ι ≫ sP) (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)))
          rfl k
          ⟨torFormulaCycleIntersectionProduct (fieldChowSituation K)
              (pullback.fst (ι ≫ sP) (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫
                ι ≫ sP)
              (isRegular_projectiveLineProduct (ι ≫ sP) hX) k β.1
              (Function.locallyFinsuppWithin.single
                ((zeroSection (ι ≫ sP)).base (genericPoint X)) 1),
            torFormulaCycleIntersectionProduct_mem_cyclesOfDimension _ _ _ _ _ _⟩) =
      properPushforward (fieldChowSituation K)
        (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP) sP
        (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))) rfl k
        ⟨torFormulaCycleIntersectionProduct (fieldChowSituation K)
            (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP)
            (isRegular_projectiveLineProduct sP hP) k
            (properPushforward (fieldChowSituation K) _
              (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP)
              (familyBaseChange sP ι) (familyBaseChange_comp_structure K sP ι) _ β).1
            (Function.locallyFinsuppWithin.single ((zeroSection sP).base (genericPoint P)) 1),
          torFormulaCycleIntersectionProduct_mem_cyclesOfDimension _ _ _ _ _ _⟩ := by
  let : IsLocallyNoetherian (projectiveLineProduct sP) :=
    isLocallyNoetherian_of_isRegular (isRegular_projectiveLineProduct sP hP)
  let : IsLocallyNoetherian (projectiveLineProduct (ι ≫ sP)) :=
    isLocallyNoetherian_of_isRegular (isRegular_projectiveLineProduct (ι ≫ sP) hX)
  have : CompactSpace (projectiveLineProduct sP) := QuasiCompact.compactSpace_of_compactSpace
    (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP)
  have : CompactSpace (projectiveLineProduct (ι ≫ sP)) :=
    QuasiCompact.compactSpace_of_compactSpace
      (pullback.fst (ι ≫ sP) (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ ι ≫ sP)
  have hfin := finite_support_of_compactSpace β.1
  have hdim : ∀ e ∈ hfin.toFinset, relativeDimension (fieldChowSituation K).dimensionFunction
      (pullback.fst (ι ≫ sP) (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ ι ≫ sP) e =
        k + 1 := fun e he =>
    (mem_cyclesOfDimension_iff_forall_point (fieldChowSituation K) _ _ β.1).1 β.2 e
      (hfin.mem_toFinset.1 he)
  have hdimj : ∀ e ∈ hfin.toFinset, relativeDimension (fieldChowSituation K).dimensionFunction
      (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP)
        ((familyBaseChange sP ι).base e) = k + 1 := by
    intro e he
    rw [← relativeDimension_comp_closedImmersion, familyBaseChange_comp_structure, hdim e he]
  have hmemj : ∀ e ∈ hfin.toFinset, Function.locallyFinsuppWithin.single e (1 : ℤ) ∈
      cyclesOfDimension (fieldChowSituation K)
        (pullback.fst (ι ≫ sP) (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ ι ≫ sP)
        (k + 1) := by
    intro e he
    rw [mem_cyclesOfDimension_iff_forall_point]
    intro z hz
    rw [Function.locallyFinsuppWithin.single_apply] at hz
    split_ifs at hz with h
    · rw [h]; exact hdim e he
    · exact (hz rfl).elim
  have hjβ := properPushforward_eq_sum_single _
    (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP)
    (familyBaseChange sP ι) (familyBaseChange_comp_structure K sP ι) _ β hfin
    (fun e => (familyBaseChange sP ι).base e) hmemj fun e he =>
      properPushforward_single_of_isClosedImmersion _ _ _ _ _ _ (hdim e he) _
  rw [hjβ, torFormulaCycleIntersectionProduct_sum_single_left _ _ _ hfin.toFinset,
    torFormulaCycleIntersectionProduct_eq_sum_single_left _ _ _ _ _ hfin,
    ← properPushforwardHom_apply, ← properPushforwardHom_apply, ← properPushforwardHom_apply,
    map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [map_zsmul, map_zsmul, map_zsmul, properPushforwardHom_apply, properPushforwardHom_apply,
    properPushforwardHom_apply]
  congr 1
  rw [properPushforward_eq_zeroFiberCycle_of_coe_eq_single (ι ≫ sP)
      (isRegular_projectiveLineProduct (ι ≫ sP) hX) e k (hdim e he)
      (hβ1 e (hfin.mem_toFinset.1 he)) _ rfl,
    properPushforward_eq_zeroFiberCycle_of_coe_eq_single sP
      (isRegular_projectiveLineProduct sP hP) _ k (hdimj e he)
      (hβ2 e (hfin.mem_toFinset.1 he)) _ rfl,
    properPushforward_zeroFiber_familyBaseChange]


end Projection

end Stacks.Intersection

end
