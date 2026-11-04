module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ClosedImmersionCycles
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.IdealSheafInclusion

/-!
# Cycles on a union of two closed subschemes

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `X` be a scheme
locally of finite type over `S`. Let `I` and `J` be two ideal sheaves on `X`, cutting out closed
subschemes `X₁` and `X₂`. Their scheme-theoretic intersection `X₁ ∩ X₂` is cut out by `I ⊔ J`,
and for every `k` the sequence of abelian groups

  `Z_k(X₁ ∩ X₂) → Z_k(X₁) ⊕ Z_k(X₂) → Z_k(X) → 0`

is exact, provided `X₁` and `X₂` cover `X` set-theoretically. The first map is the pair of
pushforwards with the second one negated, the second map is the sum of the two pushforwards.

## Main definitions

* `Stacks.Chow.intersectionToSummands` — the pair of pushforwards from the scheme-theoretic
  intersection, the second one negated.
* `Stacks.Chow.summandsToUnion` — the sum of the pushforwards from the two closed subschemes.

## Main results

* `Stacks.Chow.exact_intersectionToSummands_summandsToUnion` — exactness in the middle.
* `Stacks.Chow.surjective_summandsToUnion` — exactness at `Z_k(X)`, which needs the two closed
  subschemes to cover `X`.
* `Stacks.Chow.mem_range_inclusion_iff` — a point of the closed subscheme cut out by `I` comes
  from the one cut out by `K ≥ I` exactly when its image in `X` lies in the support of `K`.

## References

* [Stacks Project, Tag 0F92](https://stacks.math.columbia.edu/tag/0F92)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

open Scheme.IdealSheafData (inclusion inclusion_subschemeι inclusion_subschemeι_assoc)

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}}

/-! ### Points of an inclusion of closed subschemes -/

/-- On points, the inclusion of the closed subscheme cut out by `K` into the one cut out by
`I ≤ K` is compatible with the two closed immersions into the ambient scheme. -/
theorem inclusion_subschemeι_base {I K : X.IdealSheafData} (h : I ≤ K) (z : K.subscheme) :
    I.subschemeι.base ((inclusion h).base z) = K.subschemeι.base z :=
  congrArg (fun g : K.subscheme ⟶ X ↦ g.base z) (inclusion_subschemeι h)

/-- A point of the closed subscheme cut out by `I` comes from the smaller closed subscheme cut
out by `K ≥ I` exactly when its image in the ambient scheme lies in the support of `K`. -/
theorem mem_range_inclusion_iff {I K : X.IdealSheafData} (h : I ≤ K) (y : I.subscheme) :
    y ∈ Set.range (inclusion h).base ↔ I.subschemeι.base y ∈ (K.support : Set X) := by
  rw [← K.range_subschemeι]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, (inclusion_subschemeι_base h z).symm⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, I.subschemeι.isClosedEmbedding.injective
      ((inclusion_subschemeι_base h z).trans hz)⟩

/-- A point of the closed subscheme cut out by `I` comes from the scheme-theoretic intersection
with the closed subscheme cut out by `J` exactly when its image in the ambient scheme lies in the
support of `J`. -/
theorem mem_range_inclusion_le_sup_left_iff (I J : X.IdealSheafData) (y : I.subscheme) :
    y ∈ Set.range (inclusion (le_sup_left : I ≤ I ⊔ J)).base ↔
      I.subschemeι.base y ∈ (J.support : Set X) := by
  rw [mem_range_inclusion_iff, Scheme.IdealSheafData.support_sup]
  simp only [Closeds.coe_inf, Set.mem_inter_iff]
  exact and_iff_right (by rw [← I.range_subschemeι]; exact Set.mem_range_self y)

/-- A point of the closed subscheme cut out by `J` comes from the scheme-theoretic intersection
with the closed subscheme cut out by `I` exactly when its image in the ambient scheme lies in the
support of `I`. -/
theorem mem_range_inclusion_le_sup_right_iff (I J : X.IdealSheafData) (z : J.subscheme) :
    z ∈ Set.range (inclusion (le_sup_right : J ≤ I ⊔ J)).base ↔
      J.subschemeι.base z ∈ (I.support : Set X) := by
  rw [mem_range_inclusion_iff, Scheme.IdealSheafData.support_sup]
  simp only [Closeds.coe_inf, Set.mem_inter_iff]
  exact and_iff_left (by rw [← J.range_subschemeι]; exact Set.mem_range_self z)

/-! ### The two maps of the sequence -/

variable (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (I J : X.IdealSheafData) (k : ℤ)

/-- The first map of the sequence of a union of two closed subschemes: a `k`-cycle on the
scheme-theoretic intersection is sent to its pushforward to the closed subscheme cut out by `I`
together with minus its pushforward to the one cut out by `J`. -/
def intersectionToSummands :
    CycleGroup C ((I ⊔ J).subschemeι ≫ sX) k →+
      CycleGroup C (I.subschemeι ≫ sX) k × CycleGroup C (J.subschemeι ≫ sX) k :=
  (properPushforwardHom C ((I ⊔ J).subschemeι ≫ sX) (I.subschemeι ≫ sX)
      (inclusion (le_sup_left : I ≤ I ⊔ J))
      (inclusion_subschemeι_assoc (le_sup_left : I ≤ I ⊔ J) sX) k).prod
    (-properPushforwardHom C ((I ⊔ J).subschemeι ≫ sX) (J.subschemeι ≫ sX)
      (inclusion (le_sup_right : J ≤ I ⊔ J))
      (inclusion_subschemeι_assoc (le_sup_right : J ≤ I ⊔ J) sX) k)

/-- The second map of the sequence of a union of two closed subschemes: a pair of `k`-cycles on
the two closed subschemes is sent to the sum of their pushforwards to the ambient scheme. -/
def summandsToUnion :
    CycleGroup C (I.subschemeι ≫ sX) k × CycleGroup C (J.subschemeι ≫ sX) k →+
      CycleGroup C sX k :=
  (properPushforwardHom C (I.subschemeι ≫ sX) sX I.subschemeι rfl k).coprod
    (properPushforwardHom C (J.subschemeι ≫ sX) sX J.subschemeι rfl k)

/-- The first component of `Stacks.Chow.intersectionToSummands` is the pushforward along the
inclusion of the scheme-theoretic intersection into the closed subscheme cut out by `I`. -/
theorem intersectionToSummands_apply_fst (c : CycleGroup C ((I ⊔ J).subschemeι ≫ sX) k) :
    (intersectionToSummands C sX I J k c).1 =
      properPushforward C ((I ⊔ J).subschemeι ≫ sX) (I.subschemeι ≫ sX)
        (inclusion (le_sup_left : I ≤ I ⊔ J))
        (inclusion_subschemeι_assoc (le_sup_left : I ≤ I ⊔ J) sX) k c :=
  rfl

/-- The second component of `Stacks.Chow.intersectionToSummands` is minus the pushforward along
the inclusion of the scheme-theoretic intersection into the closed subscheme cut out by `J`. -/
theorem intersectionToSummands_apply_snd (c : CycleGroup C ((I ⊔ J).subschemeι ≫ sX) k) :
    (intersectionToSummands C sX I J k c).2 =
      -properPushforward C ((I ⊔ J).subschemeι ≫ sX) (J.subschemeι ≫ sX)
        (inclusion (le_sup_right : J ≤ I ⊔ J))
        (inclusion_subschemeι_assoc (le_sup_right : J ≤ I ⊔ J) sX) k c :=
  rfl

/-- `Stacks.Chow.summandsToUnion` is the sum of the two pushforwards to the ambient scheme. -/
theorem summandsToUnion_apply
    (p : CycleGroup C (I.subschemeι ≫ sX) k × CycleGroup C (J.subschemeι ≫ sX) k) :
    summandsToUnion C sX I J k p =
      properPushforward C (I.subschemeι ≫ sX) sX I.subschemeι rfl k p.1 +
        properPushforward C (J.subschemeι ≫ sX) sX J.subschemeι rfl k p.2 :=
  rfl

/-! ### Exactness in the middle -/

/-- The composite of the two maps of the sequence of a union of two closed subschemes is zero. -/
theorem summandsToUnion_intersectionToSummands
    (c : CycleGroup C ((I ⊔ J).subschemeι ≫ sX) k) :
    summandsToUnion C sX I J k (intersectionToSummands C sX I J k c) = 0 := by
  have hcomp (K : X.IdealSheafData) (h : K ≤ I ⊔ J) :
      properPushforward C (K.subschemeι ≫ sX) sX K.subschemeι rfl k
        (properPushforward C ((I ⊔ J).subschemeι ≫ sX) (K.subschemeι ≫ sX) (inclusion h)
          (inclusion_subschemeι_assoc h sX) k c) =
      properPushforward C ((I ⊔ J).subschemeι ≫ sX) sX (I ⊔ J).subschemeι rfl k c := by
    simpa only [inclusion_subschemeι] using properPushforward_properPushforward C
      ((I ⊔ J).subschemeι ≫ sX) (K.subschemeι ≫ sX) sX (inclusion h) K.subschemeι
      (inclusion_subschemeι_assoc h sX) rfl k c
  rw [summandsToUnion_apply, intersectionToSummands_apply_fst, intersectionToSummands_apply_snd,
    properPushforward_neg, hcomp I le_sup_left, hcomp J le_sup_right, add_neg_cancel]

/-- A pair of `k`-cycles killed by the sum of the pushforwards comes from the scheme-theoretic
intersection. -/
private theorem mem_range_intersectionToSummands_of_summandsToUnion_eq_zero
    (a : CycleGroup C (I.subschemeι ≫ sX) k) (b : CycleGroup C (J.subschemeι ≫ sX) k)
    (hzero : summandsToUnion C sX I J k (a, b) = 0) :
    (a, b) ∈ Set.range (intersectionToSummands C sX I J k) := by
  have hneg (q : CycleGroup C (J.subschemeι ≫ sX) k) (w : J.subscheme) :
      (-q).1 w = -q.1 w := rfl
  have hcoeff (x : X) :
      (properPushforward C (I.subschemeι ≫ sX) sX I.subschemeι rfl k a).1 x +
        (properPushforward C (J.subschemeι ≫ sX) sX J.subschemeι rfl k b).1 x = 0 := by
    simpa [summandsToUnion_apply] using congrArg (fun q : CycleGroup C sX k ↦ q.1 x) hzero
  refine ⟨cyclePullbackAlongClosedImmersion C ((I ⊔ J).subschemeι ≫ sX) (I.subschemeι ≫ sX)
    (inclusion (le_sup_left : I ≤ I ⊔ J))
    (inclusion_subschemeι_assoc (le_sup_left : I ≤ I ⊔ J) sX) k a, Prod.ext ?_ ?_⟩
  · dsimp only
    rw [intersectionToSummands_apply_fst]
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
    rw [properPushforward_cyclePullbackAlongClosedImmersion_apply]
    by_cases hy : y ∈ Set.range (inclusion (le_sup_left : I ≤ I ⊔ J)).base
    · rw [Set.indicator_of_mem hy]
    · have hJ : I.subschemeι.base y ∉ Set.range J.subschemeι.base := by
        rw [J.range_subschemeι]
        exact fun h ↦ hy ((mem_range_inclusion_le_sup_left_iff I J y).2 h)
      have hx := hcoeff (I.subschemeι.base y)
      rw [properPushforward_apply_image_of_isClosedImmersion,
        properPushforward_apply_of_notMem_range C (J.subschemeι ≫ sX) sX J.subschemeι rfl k b
          hJ] at hx
      rw [Set.indicator_of_notMem hy]
      omega
  · dsimp only
    rw [intersectionToSummands_apply_snd]
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun z ↦ ?_)
    rw [hneg]
    have hz := hcoeff (J.subschemeι.base z)
    rw [properPushforward_apply_image_of_isClosedImmersion] at hz
    by_cases hzI : J.subschemeι.base z ∈ (I.support : Set X)
    · obtain ⟨w, hw⟩ := (mem_range_inclusion_le_sup_right_iff I J z).2 hzI
      have himage : I.subschemeι.base ((inclusion (le_sup_left : I ≤ I ⊔ J)).base w) =
          J.subschemeι.base z := by
        rw [inclusion_subschemeι_base, ← inclusion_subschemeι_base (le_sup_right : J ≤ I ⊔ J) w,
          hw]
      rw [← himage, properPushforward_apply_image_of_isClosedImmersion] at hz
      conv_lhs => rw [← hw]
      rw [properPushforward_apply_image_of_isClosedImmersion,
        cyclePullbackAlongClosedImmersion_apply]
      omega
    · have hI : J.subschemeι.base z ∉ Set.range I.subschemeι.base := by
        rwa [I.range_subschemeι]
      have hnot : z ∉ Set.range (inclusion (le_sup_right : J ≤ I ⊔ J)).base := fun h ↦
        hzI ((mem_range_inclusion_le_sup_right_iff I J z).1 h)
      rw [properPushforward_apply_of_notMem_range C (I.subschemeι ≫ sX) sX I.subschemeι rfl k a
        hI] at hz
      rw [properPushforward_apply_of_notMem_range C ((I ⊔ J).subschemeι ≫ sX)
        (J.subschemeι ≫ sX) (inclusion (le_sup_right : J ≤ I ⊔ J))
        (inclusion_subschemeι_assoc (le_sup_right : J ≤ I ⊔ J) sX) k _ hnot]
      omega

/-- The sequence of a union of two closed subschemes is exact in the middle: a pair of
`k`-cycles on the two closed subschemes has vanishing sum of pushforwards exactly when it comes
from a `k`-cycle on the scheme-theoretic intersection. -/
@[stacks 0F92 "exactness in the middle"]
theorem exact_intersectionToSummands_summandsToUnion :
    Function.Exact (intersectionToSummands C sX I J k) (summandsToUnion C sX I J k) := by
  rintro ⟨a, b⟩
  refine ⟨mem_range_intersectionToSummands_of_summandsToUnion_eq_zero C sX I J k a b, ?_⟩
  rintro ⟨c, hc⟩
  exact hc ▸ summandsToUnion_intersectionToSummands C sX I J k c

/-! ### Surjectivity -/

/-- If two closed subschemes cover the ambient scheme set-theoretically, every `k`-cycle on it is
the sum of the pushforwards of a `k`-cycle on each of them. -/
@[stacks 0F92 "surjectivity"]
theorem surjective_summandsToUnion (hcover : I.support ⊔ J.support = ⊤) :
    Function.Surjective (summandsToUnion C sX I J k) := by
  intro c
  have hadd (q r : CycleGroup C sX k) (w : X) : (q + r).1 w = q.1 w + r.1 w := rfl
  refine ⟨(cyclePullbackAlongClosedImmersion C (I.subschemeι ≫ sX) sX I.subschemeι rfl k c,
    cyclePullbackAlongClosedImmersion C (J.subschemeι ≫ sX) sX J.subschemeι rfl k
      (cycleRestrict C sX k c ((I.support : Set X)ᶜ))),
    Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)⟩
  have hcover' : y ∈ (I.support : Set X) ∨ y ∈ (J.support : Set X) := by
    rw [← Set.mem_union, ← Closeds.coe_sup, hcover]
    exact Set.mem_univ y
  rw [summandsToUnion_apply, hadd]
  dsimp only
  rw [properPushforward_cyclePullbackAlongClosedImmersion_apply,
    properPushforward_cyclePullbackAlongClosedImmersion_apply, I.range_subschemeι,
    J.range_subschemeι]
  by_cases hI : y ∈ (I.support : Set X)
  · rw [Set.indicator_of_mem hI, Set.indicator_apply_eq_zero.2 fun _ ↦
      cycleRestrict_apply_of_notMem C sX k c (by simpa using hI), add_zero]
  · rw [Set.indicator_of_notMem hI, Set.indicator_of_mem (hcover'.resolve_left hI),
      cycleRestrict_apply_of_mem C sX k c hI, zero_add]

end Stacks.Chow

end
