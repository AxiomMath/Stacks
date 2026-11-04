module

public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisorCycles.PointChartDifference
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.FibreCyclePointSectionPushforward
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.FibreCycleRationalEquivalence
import StacksCore.Tactic.StacksAttribute

/-!
# The fibre cycles of a subvariety at two arbitrary points are rationally equivalent

This file proves part (2) of Tag 0B07 at an arbitrary pair of closed points, from the
arbitrary-point principal divisor `Stacks.Chow.principalDivisorCycle_eq_sub_linePointFibreCycles`.
For an integral closed subscheme `W ⊆ X ×_S ℙ¹_S` of
delta-dimension `k + 1` and a point `a` of the affine chart attached to `t : Γ(S, ⊤)`:

* the rational function `z - t` on `W` has principal divisor `[W_a]_k - [W_∞]_k` as cycles on
  `W`, where the two closed subschemes of `W` are `Stacks.Chow.pointDivisor` and
  `Stacks.Chow.infinityDivisor`;
* proper pushforward along `pr : X ×_S ℙ¹_S ⟶ X` carries those to the two fibre cycles on `X`,
  so `[W_a]_k - [W_∞]_k` is the pushforward of a principal divisor;
* hence `[W_a]_k` and `[W_∞]_k` are rationally equivalent on `X`, by the same two-branch argument
  that `Stacks.Chow.fibreCyclesRationallyEquivalentWithin` runs at `a = 0`: if the projection
  `W ⟶ X` keeps the delta-dimension this is Stacks 02RT, and if it drops it the pushforward of
  every principal divisor vanishes.

Taking two points `a` and `b` of the chart and cancelling the common `[W_∞]_k` term gives
`[W_a]_k - [W_b]_k` rationally equivalent to zero. **This is what makes the arbitrary pair
reachable without moving it to `(0, ∞)`**: no basic rational equivalence of Tag 0AZG is
exhibited, and `Stacks.Chow.fibreDifferences` — whose generating set has the zero and the
infinity fibre hard-coded — is never unfolded. What is used instead is that rational equivalence
is defined by *arbitrary* principal divisors (Tag 02RW), and `z - t` is one.

## Main definitions

* `Stacks.Chow.pointFibreCoordinate` — the rational function `z - t` on `W`.
* `Stacks.Chow.pointPrincipalDivisorCycle` — its principal divisor, at index `k`.

## Main results

* `Stacks.Chow.pointDivisor_eq_comap_lineSection` — the divisor of `W` at `a` is the inverse
  image of `D_a ⊆ ℙ¹_S` along the second projection.
* `Stacks.Chow.pointDivisor_ne_bot` — it is a proper closed subscheme of `W` exactly under the
  tag's hypothesis that `W` is not contained in the section at `a`.
* `Stacks.Chow.principalDivisorCycle_eq_sub_pointDivisorCycles` — `div_W(z - t)` on `W`.
* `Stacks.Chow.pointFibreDifference_eq_properPushforward` — `[W_a]_k - [W_∞]_k` on `X` is the
  pushforward of that principal divisor.
* `Stacks.Chow.disjoint_range_pointSection_infinitySection` — the section at a point of the chart
  and the infinity section have disjoint images, with no hypothesis relating the two points: the
  first lands in the affine chart, whose complement is the image of the second.
* `Stacks.Chow.pointFiberCycle_rationallyEquivalent_infinityFiberCycle` — **`[W_a]_k` and
  `[W_∞]_k` are rationally equivalent.**
* `Stacks.Chow.pointFiberCycles_rationallyEquivalent` — **`[W_a]_k` and `[W_b]_k` are rationally
  equivalent, for two arbitrary points `a`, `b` of the affine chart.**

## Implementation notes

`Stacks.Chow.pointFiberCycles_rationallyEquivalent` does not assume that `W` meets the infinity
section properly, although the route through `[W_∞]_k` would need it: if `W` *is* contained in
the infinity section then both fibre cycles at points of the chart vanish, the two sections
having disjoint images, and the statement is `0` rationally equivalent to `0`.

## References

* [Stacks Project, Tag 0B07](https://stacks.math.columbia.edu/tag/0B07)
* [Stacks Project, Tag 02S4](https://stacks.math.columbia.edu/tag/02S4)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02RT](https://stacks.math.columbia.edu/tag/02RT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The divisor of `W` at an arbitrary point of the chart -/

section Divisor

variable {X S : Scheme.{u}} (f : X ⟶ S) (t : Γ(S, ⊤))
  (W : (projectiveLineProduct f).IdealSheafData)

/-- **The divisor of `W` at the point `a` attached to `t` is the inverse image of `D_a ⊆ ℙ¹_S`
along the second projection.** This is the arbitrary-point analogue of
`Stacks.Chow.zeroDivisor_eq_comap_lineZeroDivisor`, and unlike it needs no reducedness of `W`,
the divisor being defined by the kernel ideal sheaf of the section. -/
theorem pointDivisor_eq_comap_lineSection :
    pointDivisor f t W = (lineSection S t).ker.comap (fibreLineProjection f W) := by
  rw [pointDivisor, ker_pointSection, fibreLineProjection_def f W,
    Scheme.IdealSheafData.comap_comp]

/-- The divisor of `W` at `a` is supported on the part of `W` lying in the image of the section
at `a`. -/
theorem coe_support_pointDivisor :
    ((pointDivisor f t W).support : Set W.subscheme) =
      W.subschemeι ⁻¹' Set.range (pointSection f t) := by
  rw [pointDivisor, Scheme.IdealSheafData.support_comap,
    TopologicalSpace.Closeds.coe_preimage, Scheme.Hom.support_ker,
    IsClosed.closure_eq (pointSection f t).isClosedEmbedding.isClosed_range]

/-- For reduced `W` the divisor at `a` is the whole of `W` exactly when `W` is contained in the
image of the section at `a`. -/
theorem pointDivisor_eq_bot_iff [IsReduced W.subscheme] :
    pointDivisor f t W = ⊥ ↔ Set.range W.subschemeι ⊆ Set.range (pointSection f t) := by
  rw [← Scheme.IdealSheafData.support_eq_top_iff, ← Closeds.coe_eq_univ,
    coe_support_pointDivisor, Set.preimage_eq_univ_iff]

/-- **The first step of part (1) of Tag 02S4 at an arbitrary point.** Under the tag's
nondegeneracy hypothesis the divisor at `a` is a proper closed subscheme of `W`. -/
theorem pointDivisor_ne_bot [IsReduced W.subscheme]
    (h : ¬ Set.range W.subschemeι ⊆ Set.range (pointSection f t)) :
    pointDivisor f t W ≠ ⊥ :=
  fun hb => h ((pointDivisor_eq_bot_iff f t W).mp hb)

/-- An integral `W` not contained in the image of the section at `a` has its generic point off
the divisor at `a`. -/
theorem notMem_support_pointDivisor_genericPoint [IsIntegral W.subscheme]
    (h : ¬ Set.range W.subschemeι ⊆ Set.range (pointSection f t)) :
    genericPoint W.subscheme ∉ ((pointDivisor f t W).support : Set W.subscheme) :=
  notMem_support_genericPoint_of_ne_bot (pointDivisor_ne_bot f t W h)

/-- **The section at a point of the affine chart and the infinity section have disjoint
images.** No relation between the two points is needed: the image of the first lies over the
affine chart of `ℙ¹_S`, and the image of the second is exactly the complement of that chart. -/
theorem disjoint_range_pointSection_infinitySection :
    Disjoint (Set.range (pointSection f t)) (Set.range (infinitySection f)) := by
  rw [Set.disjoint_left]
  rintro z ⟨x, rfl⟩ ⟨y, hy⟩
  have h1 : (pullback.snd f (relativeProjectiveLine S ↘ S)) (pointSection f t x) =
      lineSection S t (f x) := by
    rw [← Scheme.Hom.comp_apply, pointSection_comp_snd, Scheme.Hom.comp_apply]
  have h2 : (pullback.snd f (relativeProjectiveLine S ↘ S)) (infinitySection f y) =
      lineInfinitySection S (f y) := by
    rw [← Scheme.Hom.comp_apply, infinitySection_comp_snd, Scheme.Hom.comp_apply]
  have heq : lineSection S t (f x) = lineInfinitySection S (f y) := by
    rw [← h1, ← h2, hy]
  have hchart : lineSection S t (f x) ∈ Set.range (affineChart S) := by
    refine supportSet_ker_lineSection_subset S t ?_
    rw [show (lineSection S t).ker.supportSet =
      ((lineSection S t).ker.support : Set (relativeProjectiveLine S)) from rfl,
      Scheme.Hom.support_ker]
    exact subset_closure ⟨f x, rfl⟩
  rw [heq] at hchart
  exact absurd hchart (by rw [← Set.mem_compl_iff, compl_range_affineChart S]; exact ⟨f y, rfl⟩)

end Divisor

/-! ### The principal divisor of `z - t` on `W` -/

section Principal

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (W : (projectiveLineProduct f).IdealSheafData) [IsIntegral W.subscheme] (t : Γ(C.S, ⊤))

/-- **The rational function `z - t` on `W`**, the coordinate of the first chart of `ℙ¹_S` read
along the second projection and shifted by `t`. At `t = 0` it is
`Stacks.Chow.fibreCoordinate`. -/
def pointFibreCoordinate
    (hInf : ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection f)) :
    W.subscheme.functionField :=
  linePointFunction (fibreLineProjection f W) t (genericPoint_mem_preimage_chartOpen f W hInf)

/-- The scheme `V` is locally Noetherian, being of finite type over `S`. -/
private instance isLocallyNoetherian_subscheme {Y : Scheme.{u}} (g : Y ⟶ C.S)
    [LocallyOfFiniteType g] (V : (projectiveLineProduct g).IdealSheafData) :
    IsLocallyNoetherian V.subscheme :=
  LocallyOfFiniteType.isLocallyNoetherian (familyBase g V)

/-- The generic point of an integral `V` not contained in the section at `a` is not in the
preimage of the divisor of the section. -/
private theorem genericPoint_notMem_range_comap_lineSection {Y : Scheme.{u}} (g : Y ⟶ C.S)
    (V : (projectiveLineProduct g).IdealSheafData) [IsIntegral V.subscheme]
    (hT : ¬ Set.range V.subschemeι ⊆ Set.range (pointSection g t)) :
    genericPoint V.subscheme ∉
      Set.range ((lineSection C.S t).ker.comap (fibreLineProjection g V)).subschemeι.base := by
  rw [Scheme.IdealSheafData.range_subschemeι, ← pointDivisor_eq_comap_lineSection]
  exact notMem_support_pointDivisor_genericPoint g t V hT

omit [LocallyOfFiniteType f] in
/-- `z - t` is a nonzero rational function on `W`. -/
theorem pointFibreCoordinate_ne_zero
    (hT : ¬ Set.range W.subschemeι ⊆ Set.range (pointSection f t))
    (hInf : ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection f)) :
    pointFibreCoordinate C f W t hInf ≠ 0 := by
  exact linePointFunction_ne_zero (fibreLineProjection f W) t _
    (genericPoint_notMem_range_comap_lineSection C t f W hT)

/-- **The principal divisor of `z - t` on an integral family over the projective line.** Let
`W ⊆ X ×_S ℙ¹_S` be integral of delta-dimension `n` over the base, contained in neither the image
of the section at `a` nor the image of the infinity section. Then

  `div_W(z - t) = [W_a]_{n-1} - [W_∞]_{n-1}`

as cycles on `W`, the two closed subschemes being the divisor of `W` at `a` and the infinity
divisor of `W`. At `t = 0` this is `Stacks.Chow.principalDivisorCycle_eq_sub_fibreDivisorCycles`.
-/
theorem principalDivisorCycle_eq_sub_pointDivisorCycles {n : ℤ}
    (hdim : schemeDeltaDimension C (familyBase f W) = (n : EInt))
    (hT : ¬ Set.range W.subschemeι ⊆ Set.range (pointSection f t))
    (hInf : ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection f)) :
    principalDivisorCycle C (familyBase f W) hdim (pointFibreCoordinate C f W t hInf) =
      cycleAssociatedToClosedSubscheme C (familyBase f W)
          (pointDivisor f t W).subschemeι (n - 1) -
        cycleAssociatedToClosedSubscheme C (familyBase f W)
          (infinityDivisor f W).subschemeι (n - 1) := by
  have hgenInf : genericPoint W.subscheme ∉
      Set.range ((lineInfinityDivisor C.S).comap
        (fibreLineProjection f W)).subschemeι.base := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      ← infinityDivisor_eq_comap_lineInfinityDivisor f W]
    exact notMem_support_infinityDivisor_genericPoint f W hInf
  have hmain := principalDivisorCycle_eq_sub_linePointFibreCycles C (familyBase f W)
    (fibreLineProjection f W) t hdim (genericPoint_mem_preimage_chartOpen f W hInf)
    (genericPoint_notMem_range_comap_lineSection C t f W hT) hgenInf
  rw [← pointDivisor_eq_comap_lineSection,
    ← infinityDivisor_eq_comap_lineInfinityDivisor f W] at hmain
  exact hmain

variable (k : ℤ)

/-- The principal divisor of `z - t` on `W`, as a `k`-cycle. This is
`Stacks.Chow.principalDivisorCycle`, whose index is `k + 1 - 1` rather than `k`. -/
def pointPrincipalDivisorCycle
    (hdim : schemeDeltaDimension C (familyBase f W) = ((k + 1 : ℤ) : EInt))
    (hInf : ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection f)) :
    CycleGroup C (familyBase f W) k :=
  letI : IsLocallyNoetherian W.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (familyBase f W)
  ⟨principalCycle W.subscheme (pointFibreCoordinate C f W t hInf), by
    have h := principalCycle_mem_cyclesOfDimension C (familyBase f W) hdim
      (pointFibreCoordinate C f W t hInf)
    rwa [show (k + 1 - 1 : ℤ) = k from by ring] at h⟩

/-- The `k`-cycle `div_W(z - t)` on `W` is `[W_a]_k - [W_∞]_k`, the difference of the cycles of
the divisor of `W` at `a` and of the infinity divisor of `W`. -/
theorem pointPrincipalDivisorCycle_eq_sub
    (hdim : schemeDeltaDimension C (familyBase f W) = ((k + 1 : ℤ) : EInt))
    (hT : ¬ Set.range W.subschemeι ⊆ Set.range (pointSection f t))
    (hInf : ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection f)) :
    pointPrincipalDivisorCycle C f W t k hdim hInf =
      cycleAssociatedToClosedSubscheme C (familyBase f W) (pointDivisor f t W).subschemeι k -
        cycleAssociatedToClosedSubscheme C (familyBase f W)
          (infinityDivisor f W).subschemeι k := by
  have h := congrArg Subtype.val
    (principalDivisorCycle_eq_sub_pointDivisorCycles C f W t hdim hT hInf)
  rw [AddSubgroup.coe_sub,
    show (principalDivisorCycle C (familyBase f W) hdim (pointFibreCoordinate C f W t hInf) :
      AlgebraicCycle W.subscheme ℤ) =
      principalCycle W.subscheme (pointFibreCoordinate C f W t hInf) from rfl] at h
  rw [show (k + 1 - 1 : ℤ) = k from by ring] at h
  exact Subtype.ext (by rw [AddSubgroup.coe_sub]; exact h)

omit [AlgebraicGeometry.IsIntegral W.subscheme] in
/-- **Proper pushforward carries the cycle of the divisor of `W` at `a` to the cycle of the fibre
of `W` at `a` on `X`.** This is the closed-immersion case of Stacks 02R6 together with
`Stacks.Chow.ker_pointDivisor_subschemeι_comp`, the identification of the two presentations of
the fibre. -/
theorem properPushforward_cycleAssociatedToClosedSubscheme_pointDivisor :
    properPushforward C (familyBase f W) f (fibreBaseProjection f W)
        (fibreBaseProjection_comp f W) k
        (cycleAssociatedToClosedSubscheme C (familyBase f W)
          (pointDivisor f t W).subschemeι k) =
      cycleAssociatedToClosedSubscheme C f (pointFiber f t W).subschemeι k := by
  rw [properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp C
      (familyBase f W) f (fibreBaseProjection f W) (fibreBaseProjection_comp f W)
      (pointDivisor f t W).subschemeι k,
    cycleAssociatedToClosedSubscheme_ker C f
      ((pointDivisor f t W).subschemeι ≫ fibreBaseProjection f W) k,
    ker_pointDivisor_subschemeι_comp f t W]

/-- **The difference of the fibre cycles of `W` at `a` and at `∞` is the proper pushforward of a
principal divisor on `W`.** -/
theorem pointFibreDifference_eq_properPushforward
    (hdim : schemeDeltaDimension C (familyBase f W) = ((k + 1 : ℤ) : EInt))
    (hT : ¬ Set.range W.subschemeι ⊆ Set.range (pointSection f t))
    (hInf : ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection f)) :
    cycleAssociatedToClosedSubscheme C f (pointFiber f t W).subschemeι k -
        cycleAssociatedToClosedSubscheme C f (infinityFiber f W).subschemeι k =
      properPushforward C (familyBase f W) f (fibreBaseProjection f W)
        (fibreBaseProjection_comp f W) k
        (pointPrincipalDivisorCycle C f W t k hdim hInf) := by
  rw [pointPrincipalDivisorCycle_eq_sub C f W t k hdim hT hInf, properPushforward_sub,
    properPushforward_cycleAssociatedToClosedSubscheme_pointDivisor C f W t k,
    properPushforward_cycleAssociatedToClosedSubscheme_infinityDivisor C f W k]

end Principal

/-! ### The fibre cycles at two points of the chart are rationally equivalent -/

section Equivalence

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (W : (projectiveLineProduct f).IdealSheafData) (t : Γ(C.S, ⊤)) (k : ℤ)

/-- If `W` is contained in the image of the infinity section then its fibre at a point of the
affine chart is empty, so the fibre cycle vanishes. The two sections have disjoint images, so no
point of `W` lies on the section at `a`. -/
theorem cycleAssociatedToClosedSubscheme_pointFiber_eq_zero
    (hW : Set.range W.subschemeι ⊆ Set.range (infinitySection f)) :
    cycleAssociatedToClosedSubscheme C f (pointFiber f t W).subschemeι k = 0 := by
  have hempty : ∀ x : X, x ∉ Set.range (pointFiber f t W).subschemeι.base := by
    intro x hx
    rw [Scheme.IdealSheafData.range_subschemeι, pointFiber,
      Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
      ← Scheme.IdealSheafData.range_subschemeι] at hx
    exact Set.disjoint_left.mp (disjoint_range_pointSection_infinitySection f t)
      ⟨x, rfl⟩ (hW hx)
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x => ?_)
  rw [cycleAssociatedToClosedSubscheme_apply_eq_zero_of_notMem_range C f
    (pointFiber f t W).subschemeι k (hempty x)]
  rfl

/-- **The fibre cycle of `W` at an arbitrary point `a` of the affine chart is rationally
equivalent to the fibre cycle at `∞`.** The hypotheses are the source's own: `W` is an integral
closed subscheme of delta-dimension `k + 1` meeting the images of the two sections properly.

The difference is the proper pushforward of the principal divisor of `z - t`, by
`Stacks.Chow.pointFibreDifference_eq_properPushforward`, and the two-branch argument of part (2)
of Tag 02S4 applies to it verbatim: when the projection `W ⟶ X` keeps the delta-dimension it is
Stacks 02RT, and when it drops it the pushforward of every principal divisor is zero. -/
theorem pointFiberCycle_rationallyEquivalent_infinityFiberCycle [IsIntegral W.subscheme]
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase f W) ξ.1 = k + 1)
    (hT : ¬ Set.range W.subschemeι ⊆ Set.range (pointSection f t))
    (hInf : ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection f)) :
    RationallyEquivalent C f k
      (cycleAssociatedToClosedSubscheme C f (pointFiber f t W).subschemeι k)
      (cycleAssociatedToClosedSubscheme C f (infinityFiber f W).subschemeι k) := by
  have hdim := schemeDeltaDimension_familyBase C f W hDim
  have hne : pointFibreCoordinate C f W t hInf ≠ 0 :=
    pointFibreCoordinate_ne_zero C f W t hT hInf
  rw [RationallyEquivalent, pointFibreDifference_eq_properPushforward C f W t k hdim hT hInf]
  by_cases hker : schemeDeltaDimension C ((fibreBaseProjection f W).ker.subschemeι ≫ f) =
      ((k + 1 : ℤ) : EInt)
  · rw [mem_rationalEquivalences]
    exact (isRationallyEquivalentToZeroWithin_properPushforward_principalCycle C f
      (familyBase f W) (fibreBaseProjection f W) (fibreBaseProjection_comp f W) hdim hker hne
      _ rfl).isRationallyEquivalentToZero
  · have hz : properPushforward C (familyBase f W) f (fibreBaseProjection f W)
        (fibreBaseProjection_comp f W) k (pointPrincipalDivisorCycle C f W t k hdim hInf) = 0 :=
      properPushforward_eq_zero_of_val_eq C (familyBase f W) f (fibreBaseProjection f W)
        (fibreBaseProjection_comp f W) (pointPrincipalDivisorCycle C f W t k hdim hInf)
        (principalDivisorCycle C (familyBase f W) hdim (pointFibreCoordinate C f W t hInf)) rfl
        (properPushforward_principalDivisorCycle_eq_zero_of_schemeDeltaDimension_image_ne C
          (familyBase f W) f hdim (fibreBaseProjection f W) (fibreBaseProjection_comp f W) hker
          (pointFibreCoordinate C f W t hInf))
    rw [hz]
    exact zero_mem _

/-- **The fibre cycles of `W` at two arbitrary points `a`, `b` of the affine chart are rationally
equivalent.** The hypotheses are the source's own: `W` is an integral closed subscheme of
delta-dimension `k + 1` meeting the images of the two sections properly. Nothing is assumed about
the two distinguished points `0` and `∞` of `ℙ¹_S`, and no basic rational equivalence of Tag
0AZG is exhibited: the difference is the pushforward of the principal divisor of
`(z - t) / (z - t')`, which Tag 02RW admits for any rational function.

If `W` meets the infinity section properly the two differences `[W_a]_k - [W_∞]_k` and
`[W_b]_k - [W_∞]_k` are each rationally equivalent to zero and their difference is
`[W_a]_k - [W_b]_k`. Otherwise `W` is contained in the infinity section, and then both fibre
cycles vanish because the section at a point of the affine chart misses the infinity section. -/
theorem pointFiberCycles_rationallyEquivalent [IsIntegral W.subscheme] (t' : Γ(C.S, ⊤))
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase f W) ξ.1 = k + 1)
    (hT : ¬ Set.range W.subschemeι ⊆ Set.range (pointSection f t))
    (hT' : ¬ Set.range W.subschemeι ⊆ Set.range (pointSection f t')) :
    RationallyEquivalent C f k
      (cycleAssociatedToClosedSubscheme C f (pointFiber f t W).subschemeι k)
      (cycleAssociatedToClosedSubscheme C f (pointFiber f t' W).subschemeι k) := by
  by_cases hInf : Set.range W.subschemeι ⊆ Set.range (infinitySection f)
  · rw [cycleAssociatedToClosedSubscheme_pointFiber_eq_zero C f W t k hInf,
      cycleAssociatedToClosedSubscheme_pointFiber_eq_zero C f W t' k hInf,
      RationallyEquivalent, sub_self]
    exact zero_mem _
  · have h1 := pointFiberCycle_rationallyEquivalent_infinityFiberCycle C f W t k hDim hT hInf
    have h2 := pointFiberCycle_rationallyEquivalent_infinityFiberCycle C f W t' k hDim hT' hInf
    simpa using sub_mem h1 h2

end Equivalence

/-! ### Part (2) of Tag 0B07 at an arbitrary pair of closed points -/

section PartTwo

open AlgebraicGeometry.TorFormula

attribute [local instance 100000] HasDerivedCategory.standard

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  (W : (projectiveLineProduct p).IdealSheafData) [IsIntegral W.subscheme] (k : ℤ) (d : ℕ)
  (t t' : Γ(C.S, ⊤))

/-- **Stacks 0B07 part (2) for a prime cycle, at an arbitrary pair of closed points of the
affine chart.** Let `W ⊆ X ×_S ℙ¹_S` be a closed subvariety of delta-dimension `k + 1` meeting
the images of the sections at `a` and at `b` properly. Then `pr_{X,*}(W · X × a - W · X × b)` is
rationally equivalent to zero: by part (1)(b) at an arbitrary point it is the difference
`[W_a]_k - [W_b]_k` of the two fibre cycles, and
`Stacks.Chow.pointFiberCycles_rationallyEquivalent` writes that difference as the proper
pushforward of a principal divisor on `W`. -/
theorem sub_properPushforward_intersectionProductCycle_pointSection_mem_rationalEquivalences
    (_hne : t ≠ t') (hY : IsRegular (projectiveLineProduct p))
    (hd : topologicalKrullDim (projectiveLineProduct p) ≤ (d : WithBot ℕ∞))
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase p W) ξ.1 = k + 1)
    (hT : ¬ Set.range W.subschemeι ⊆ Set.range (pointSection p t))
    (hT' : ¬ Set.range W.subschemeι ⊆ Set.range (pointSection p t'))
    (hWD : schemeDeltaDimension C ((W ⊔ (pointSection p t).ker).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt))
    (hWD' : schemeDeltaDimension C ((W ⊔ (pointSection p t').ker).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt)) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        ⟨intersectionProductCycle C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY
            (subschemeStructureSheaf W) (subschemeStructureSheaf (pointSection p t).ker)
            (isCoherent_subschemeStructureSheaf W)
            (isCoherent_subschemeStructureSheaf (pointSection p t).ker) k
            (schemeDeltaDimension_reducedSupport_torSheaf_le C
              (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY W
              (pointSection p t).ker k hWD),
          intersectionProductCycle_mem_cyclesOfDimension C
            (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY W
            (pointSection p t).ker k hWD⟩ -
      properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        ⟨intersectionProductCycle C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY
            (subschemeStructureSheaf W) (subschemeStructureSheaf (pointSection p t').ker)
            (isCoherent_subschemeStructureSheaf W)
            (isCoherent_subschemeStructureSheaf (pointSection p t').ker) k
            (schemeDeltaDimension_reducedSupport_torSheaf_le C
              (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY W
              (pointSection p t').ker k hWD'),
          intersectionProductCycle_mem_cyclesOfDimension C
            (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY W
            (pointSection p t').ker k hWD'⟩ ∈
      rationalEquivalences C p k := by
  have : IsLocallyNoetherian (projectiveLineProduct p) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
  rw [properPushforward_intersectionProductCycle_eq_pointFiberCycle C p t W k d hY hd hDim hWD,
    properPushforward_intersectionProductCycle_eq_pointFiberCycle C p t' W k d hY hd hDim hWD']
  exact pointFiberCycles_rationallyEquivalent C p W t k t' hDim hT hT'

/-- **Stacks 0B07 part (2) for a prime cycle, at an arbitrary point of the affine chart and the
point at infinity.** Together with the two-chart-points statement this covers an arbitrary pair
of closed points of `ℙ¹` over an algebraically closed field. -/
theorem sub_properPushforward_intersectionProductCycle_pointInfinity_mem_rationalEquivalences
    (hY : IsRegular (projectiveLineProduct p))
    (hd : topologicalKrullDim (projectiveLineProduct p) ≤ (d : WithBot ℕ∞))
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase p W) ξ.1 = k + 1)
    (hT : ¬ Set.range W.subschemeι ⊆ Set.range (pointSection p t))
    (hInf : ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection p))
    (hWD : schemeDeltaDimension C ((W ⊔ (pointSection p t).ker).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt))
    (hWDinf : schemeDeltaDimension C ((W ⊔ (infinitySection p).ker).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt)) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        ⟨intersectionProductCycle C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY
            (subschemeStructureSheaf W) (subschemeStructureSheaf (pointSection p t).ker)
            (isCoherent_subschemeStructureSheaf W)
            (isCoherent_subschemeStructureSheaf (pointSection p t).ker) k
            (schemeDeltaDimension_reducedSupport_torSheaf_le C
              (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY W
              (pointSection p t).ker k hWD),
          intersectionProductCycle_mem_cyclesOfDimension C
            (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY W
            (pointSection p t).ker k hWD⟩ -
      properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        ⟨intersectionProductCycle C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY
            (subschemeStructureSheaf W) (subschemeStructureSheaf (infinitySection p).ker)
            (isCoherent_subschemeStructureSheaf W)
            (isCoherent_subschemeStructureSheaf (infinitySection p).ker) k
            (schemeDeltaDimension_reducedSupport_torSheaf_le C
              (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY W
              (infinitySection p).ker k hWDinf),
          intersectionProductCycle_mem_cyclesOfDimension C
            (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY W
            (infinitySection p).ker k hWDinf⟩ ∈
      rationalEquivalences C p k := by
  have : IsLocallyNoetherian (projectiveLineProduct p) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
  rw [properPushforward_intersectionProductCycle_eq_pointFiberCycle C p t W k d hY hd hDim hWD,
    properPushforward_intersectionProductCycle_eq_infinityFiberCycle C p W k d hY hd hDim hWDinf]
  exact pointFiberCycle_rationallyEquivalent_infinityFiberCycle C p W t k hDim hT hInf

end PartTwo

/-! ### Part (2) at an arbitrary pair for a nonsingular variety -/

section NonsingularVariety

open AlgebraicGeometry.TorFormula

attribute [local instance 100000] HasDerivedCategory.standard

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  (Kf : Type u) [Field Kf] [IsAlgClosed Kf]
  (hC : C.S = AlgebraicGeometry.Spec (CommRingCat.of Kf))
  [AlgebraicGeometry.IsVariety Kf (p ≫ eqToHom hC)] (hX : IsRegular X)
  (W : (projectiveLineProduct p).IdealSheafData) [IsIntegral W.subscheme] (k : ℤ)
  (t t' : Γ(C.S, ⊤))

/-- **Stacks 0B07 part (2) for a prime cycle at an arbitrary pair of closed points of the affine
chart, for a nonsingular variety.** Nothing is assumed about the ambient family. -/
theorem
  sub_properPushforward_intersectionProductCycle_pointSection_mem_rationalEquivalences_of_isRegular
    (hne : t ≠ t')
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase p W) ξ.1 = k + 1)
    (hT : ¬ Set.range W.subschemeι ⊆ Set.range (pointSection p t))
    (hT' : ¬ Set.range W.subschemeι ⊆ Set.range (pointSection p t'))
    (hWD : schemeDeltaDimension C ((W ⊔ (pointSection p t).ker).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt))
    (hWD' : schemeDeltaDimension C ((W ⊔ (pointSection p t').ker).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt)) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        ⟨intersectionProductCycle C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
            (isRegular_projectiveLineProduct_of_eq p hC hX)
            (subschemeStructureSheaf W) (subschemeStructureSheaf (pointSection p t).ker)
            (isCoherent_subschemeStructureSheaf W)
            (isCoherent_subschemeStructureSheaf (pointSection p t).ker) k
            (schemeDeltaDimension_reducedSupport_torSheaf_le C
              (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
              (isRegular_projectiveLineProduct_of_eq p hC hX) W
              (pointSection p t).ker k hWD),
          intersectionProductCycle_mem_cyclesOfDimension C
            (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
            (isRegular_projectiveLineProduct_of_eq p hC hX) W
            (pointSection p t).ker k hWD⟩ -
      properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        ⟨intersectionProductCycle C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
            (isRegular_projectiveLineProduct_of_eq p hC hX)
            (subschemeStructureSheaf W) (subschemeStructureSheaf (pointSection p t').ker)
            (isCoherent_subschemeStructureSheaf W)
            (isCoherent_subschemeStructureSheaf (pointSection p t').ker) k
            (schemeDeltaDimension_reducedSupport_torSheaf_le C
              (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
              (isRegular_projectiveLineProduct_of_eq p hC hX) W
              (pointSection p t').ker k hWD'),
          intersectionProductCycle_mem_cyclesOfDimension C
            (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
            (isRegular_projectiveLineProduct_of_eq p hC hX) W
            (pointSection p t').ker k hWD'⟩ ∈
      rationalEquivalences C p k := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_projectiveLineProduct_le Kf C hC p
  exact sub_properPushforward_intersectionProductCycle_pointSection_mem_rationalEquivalences
    C p W k d t t' hne (isRegular_projectiveLineProduct_of_eq p hC hX) hd hDim hT hT' hWD hWD'

/-- **Stacks 0B07 part (2) for a prime cycle at an arbitrary point of the affine chart and at
infinity, for a nonsingular variety.** Nothing is assumed about the ambient family. -/
theorem
  sub_properPushforward_intersectionProductCycle_pointInfinity_mem_rationalEquivalences_of_isRegular
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase p W) ξ.1 = k + 1)
    (hT : ¬ Set.range W.subschemeι ⊆ Set.range (pointSection p t))
    (hInf : ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection p))
    (hWD : schemeDeltaDimension C ((W ⊔ (pointSection p t).ker).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt))
    (hWDinf : schemeDeltaDimension C ((W ⊔ (infinitySection p).ker).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt)) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        ⟨intersectionProductCycle C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
            (isRegular_projectiveLineProduct_of_eq p hC hX)
            (subschemeStructureSheaf W) (subschemeStructureSheaf (pointSection p t).ker)
            (isCoherent_subschemeStructureSheaf W)
            (isCoherent_subschemeStructureSheaf (pointSection p t).ker) k
            (schemeDeltaDimension_reducedSupport_torSheaf_le C
              (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
              (isRegular_projectiveLineProduct_of_eq p hC hX) W
              (pointSection p t).ker k hWD),
          intersectionProductCycle_mem_cyclesOfDimension C
            (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
            (isRegular_projectiveLineProduct_of_eq p hC hX) W
            (pointSection p t).ker k hWD⟩ -
      properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        ⟨intersectionProductCycle C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
            (isRegular_projectiveLineProduct_of_eq p hC hX)
            (subschemeStructureSheaf W) (subschemeStructureSheaf (infinitySection p).ker)
            (isCoherent_subschemeStructureSheaf W)
            (isCoherent_subschemeStructureSheaf (infinitySection p).ker) k
            (schemeDeltaDimension_reducedSupport_torSheaf_le C
              (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
              (isRegular_projectiveLineProduct_of_eq p hC hX) W
              (infinitySection p).ker k hWDinf),
          intersectionProductCycle_mem_cyclesOfDimension C
            (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
            (isRegular_projectiveLineProduct_of_eq p hC hX) W
            (infinitySection p).ker k hWDinf⟩ ∈
      rationalEquivalences C p k := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_projectiveLineProduct_le Kf C hC p
  exact sub_properPushforward_intersectionProductCycle_pointInfinity_mem_rationalEquivalences
    C p W k d t (isRegular_projectiveLineProduct_of_eq p hC hX) hd hDim hT hInf hWD hWDinf

end NonsingularVariety

end Stacks.Chow

end
