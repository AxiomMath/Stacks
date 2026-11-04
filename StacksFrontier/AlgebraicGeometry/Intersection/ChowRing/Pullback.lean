module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersection
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.MaximalDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.GeneralRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.GysinGysinCommute
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.GenericFibre
public import StacksFrontier.AlgebraicGeometry.Intersection.ChowRing.Basic
public import StacksFrontier.AlgebraicGeometry.Intersection.ProjectionFormulaFlat.Cycles
public import StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.FlatPullbackWhole
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularSmooth
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pullback along a morphism of nonsingular projective varieties

Let `f : X ⟶ Y` be a morphism of nonsingular projective varieties over an algebraically closed
field. Section 43.23 of the source (Tag 0B0H) defines

`f^* : CH_k(Y) ⟶ CH_{k + dim X - dim Y}(X)`,  `f^*(α) = pr_{X,*}(Γ_f · pr_Y^*(α))`,

where `Γ_f ⊆ X × Y` is the graph of `f` and `·` is the intersection product of Section 43.21 on
the nonsingular projective variety `X × Y`. Tag 0B2X then shows that `f^*` is a ring map
`CH^*(Y) ⟶ CH^*(X)`, that `(g ∘ f)^* = f^* ∘ g^*`, that the projection formula
`f_*(α) · β = f_*(α · f^*β)` holds, and that `f^*` is flat pullback when `f` is flat.

## Main definitions

* `Stacks.Intersection.ChowRing.graph`: the graph morphism `X ⟶ X ×_k Y` of `f`.
* `Stacks.Intersection.ChowRing.graphClass`: the class `[Γ_f] ∈ CH_{dim X}(X × Y)`.
* `Stacks.Intersection.ChowRing.chowPullback`: the pullback `f^*` of Tag 0B0H.
* `Stacks.Intersection.ChowRing.chowPullbackRingHom`: `f^*` as a ring homomorphism
  `CH^*(Y) ⟶ CH^*(X)`.

## Main results

* `Stacks.Intersection.ChowRing.flatPullbackChow_chowMulFun`: flat pullback is multiplicative on
  Chow groups (Tag 0B0Z on classes).
* `Stacks.Intersection.ChowRing.properChowPushforward_chowMulFun`: the projection formula for a
  flat proper morphism on Chow groups (Tag 0B10 on classes).
* `Stacks.Intersection.ChowRing.chowMulFun_graphClass_prXPullback`: `[Γ_f] · pr_X^*(z) = s_*(z)`,
  the source's remark on graphs.
* `Stacks.Intersection.ChowRing.graphPush_chowPullback`: `s_*(f^* b) = [Γ_f] · pr_Y^*(b)`.
* `Stacks.Intersection.ChowRing.chowPullback_isRingHom`: **Tag 0B2X, part (1)**.
* `Stacks.Intersection.ChowRing.chowMulFun_properChowPushforward_eq`: **Tag 0B2X, part (3)**.
* `Stacks.Intersection.ChowRing.chowPullback_eq_flatPullbackChow`: **Tag 0B2X, part (4)**.

Part (2) of Tag 0B2X is `Stacks.Intersection.ChowRing.chowPullback_comp`, in
`StacksFrontier.AlgebraicGeometry.Intersection.ChowRing.PullbackComposition`.

## Implementation notes

Every proof goes through the graph `s : X ⟶ X × Y`. A class of the form `[Γ_f] · w` is pushed
forward from `X`, and `pr_{X,*} ∘ s_* = id`, so `f^*` is characterised by
`s_*(f^* b) = [Γ_f] · pr_Y^*(b)`; and `[Γ_f] · pr_X^*(z) = s_*(z)` because the graph is a section
of the flat projection `pr_X`, which makes it Tor independent of every `pr_X⁻¹(Z)`. The flat case
is the same computation with `pr_Y`, using that `s ≫ pr_Y = f` is flat.

## References

* [Stacks Project, Tag 0B0H](https://stacks.math.columbia.edu/tag/0B0H)
* [Stacks Project, Tag 0B2X](https://stacks.math.columbia.edu/tag/0B2X)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Chow AlgebraicGeometry.TorFormula

universe u

namespace Stacks.Intersection.ChowRing

/-! ### The product of two projective varieties -/

section Product

variable (K : Type u) [Field K] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K))
  (sY : Y ⟶ Spec (.of K))

/-- **The product of two projective varieties over an algebraically closed field is a projective
variety**: it is a variety by Tag 05P3, and the projection to `X` followed by the structure
morphism of `X` is H-projective, being the composite of the base change of `X ⟶ Spec K` and of
`Y ⟶ Spec K` (Tags 01WF and 01WE). -/
instance isProjectiveVariety_pullback [IsAlgClosed K] [IsProjectiveVariety K sX]
    [IsProjectiveVariety K sY] : IsProjectiveVariety K (pullback.fst sX sY ≫ sX) := by
  refine (isProjectiveVariety_iff K _).2 ⟨inferInstance, ?_⟩
  rw [pullback.condition]
  exact (IsProjectiveVariety.isProjective (k := K) (f := sX)).baseChange sY |>.comp
    (IsProjectiveVariety.isProjective (k := K) (f := sY))

end Product

/-! ### The graph of a morphism -/

section Graph

variable {K : Type u} [Field K] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of K)}
  {sY : Y ⟶ Spec (.of K)} (f : X ⟶ Y) (hf : f ≫ sY = sX)

/-- The graph `X ⟶ X ×_K Y`, `x ↦ (x, f(x))`, of a morphism `f : X ⟶ Y` over `K`. -/
def graph : X ⟶ pullback sX sY :=
  pullback.lift (𝟙 X) f (by rw [Category.id_comp, hf])

/-- The graph followed by the first projection is the identity. -/
@[reassoc (attr := simp)]
theorem graph_fst : graph f hf ≫ pullback.fst sX sY = 𝟙 X := pullback.lift_fst _ _ _

/-- The graph followed by the second projection is `f`. -/
@[reassoc (attr := simp)]
theorem graph_snd : graph f hf ≫ pullback.snd sX sY = f := pullback.lift_snd _ _ _

/-- The graph is a morphism over `K`. -/
theorem graph_comp_structure : graph f hf ≫ (pullback.fst sX sY ≫ sX) = sX := by
  rw [graph_fst_assoc]

/-- **The graph of a morphism to a separated scheme is a closed immersion**: it is a section of
the separated projection `X ×_K Y ⟶ X`. -/
@[ega "I 5.4.3" "special case",
  ega "IV 20.4.1" "special case",
  sga "3 VIB 5.6.3" "(i) ⇒ (ii), special case"]
instance isClosedImmersion_graph [IsSeparated sY] : IsClosedImmersion (graph f hf) := by
  have : IsClosedImmersion (graph f hf ≫ pullback.fst sX sY) := by
    rw [graph_fst]; infer_instance
  exact IsClosedImmersion.of_comp (graph f hf) (pullback.fst sX sY)

include hf in
/-- A morphism over the base from a proper scheme to a separated one is proper. -/
theorem isProper_of_comp_eq [IsProper sX] [IsSeparated sY] : IsProper f := by
  have : IsProper (f ≫ sY) := by rw [hf]; infer_instance
  exact IsProper.of_comp f sY

/-- The graph followed by the first projection, the identity, is flat. -/
instance flat_graph_comp_fst : Flat (graph f hf ≫ pullback.fst sX sY) := by
  rw [graph_fst]; infer_instance

/-- Pushing forward along the graph and then along the first projection is the identity. -/
theorem properPushforward_fst_properPushforward_graph [IsProper sX] [IsProper sY] (k : ℤ)
    (z : CycleGroup (fieldChowSituation K) sX k) :
    properPushforward (fieldChowSituation K) (pullback.fst sX sY ≫ sX) sX (pullback.fst sX sY) rfl k
        (properPushforward (fieldChowSituation K) sX (pullback.fst sX sY ≫ sX) (graph f hf)
          (graph_comp_structure f hf) k z) = z := by
  rw [properPushforward_properPushforward,
    congrFun (properPushforward_congr (fieldChowSituation K) sX sX _ (𝟙 X) (graph_fst f hf) _
      (Category.id_comp sX) k) z, properPushforward_id]

/-- Pushing forward along the graph and then along the second projection is `f_*`. -/
theorem properPushforward_snd_properPushforward_graph [IsProper sX] [IsProper sY] [IsProper f]
    (k : ℤ)
    (z : CycleGroup (fieldChowSituation K) sX k) :
    properPushforward (fieldChowSituation K) (pullback.fst sX sY ≫ sX) sY (pullback.snd sX sY)
        pullback.condition.symm k
        (properPushforward (fieldChowSituation K) sX (pullback.fst sX sY ≫ sX) (graph f hf)
          (graph_comp_structure f hf) k z) =
      properPushforward (fieldChowSituation K) sX sY f hf k z := by
  rw [properPushforward_properPushforward,
    congrFun (properPushforward_congr (fieldChowSituation K) sX sY _ f (graph_snd f hf) _ hf k) z]

/-- A dimension equal to `b + e` with `b = d` is `d + e`. -/
private theorem eq_natCast_add_of_eq_add {a b : WithBot ℕ∞} {d e : ℕ}
    (he : a = b + (e : WithBot ℕ∞)) (hb : b = (d : WithBot ℕ∞)) :
    a = ((d + e : ℕ) : WithBot ℕ∞) := by
  rw [he, hb]; push_cast; rfl

/-- The dimension of `X × Y` is that of `X` plus `dim Y`. -/
private theorem topologicalKrullDim_pullback_eq_add_fst (K : Type u) [Field K] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) [IsVariety K sX] [IsVariety K sY] {dY : ℕ}
    (hdY : topologicalKrullDim Y = (dY : WithBot ℕ∞)) :
    topologicalKrullDim (pullback sX sY : Scheme.{u}) =
      topologicalKrullDim X + (dY : WithBot ℕ∞) := by
  rw [topologicalKrullDim_pullback_of_isVariety, hdY]

/-- The dimension of `X × Y` is that of `Y` plus `dim X`. -/
private theorem topologicalKrullDim_pullback_eq_add_snd (K : Type u) [Field K] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) [IsVariety K sX] [IsVariety K sY] {dX : ℕ}
    (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞)) :
    topologicalKrullDim (pullback sX sY : Scheme.{u}) =
      topologicalKrullDim Y + (dX : WithBot ℕ∞) := by
  rw [topologicalKrullDim_pullback_of_isVariety, hdX, add_comm]

/-- A component of a `d`-cycle has dimension `d`, so `d` is a natural number and the component's
closed subscheme has delta-dimension at most `d`. -/
private theorem exists_nat_eq_and_deltaDimension_le (K : Type u) [Field K] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of K)) [IsVariety K sX] {d : ℤ} (z : CycleGroup (fieldChowSituation K) sX d)
    {v : X} (hv : v ∈ Function.support z.1) :
    ∃ d' : ℕ, d = d' ∧
      topologicalKrullDim ((integralComponentAt v).support : Set X) ≤ (d' : WithBot ℕ∞) ∧
      schemeDeltaDimension (fieldChowSituation K) ((integralComponentAt v).subschemeι ≫ sX) ≤
        ((d' : ℤ) : EInt) := by
  have hvd : relativeDimension (fieldChowSituation K).dimensionFunction sX v = d :=
    (mem_cyclesOfDimension_iff_forall_point (fieldChowSituation K) sX d z.1).1 z.2 v hv
  obtain ⟨d', rfl⟩ : ∃ d' : ℕ, d = (d' : ℤ) :=
    ⟨d.toNat, by
      have := relativeDimension_nonneg (fieldChowSituation K) (fun _ _ => rfl) sX v
      omega⟩
  have hsupp : topologicalKrullDim ((integralComponentAt v).support : Set X) ≤
      (d' : WithBot ℕ∞) := by
    rw [coe_support_integralComponentAt,
      ExteriorProductProjections.topologicalKrullDim_closure_of_relativeDimension_eq K sX v d' hvd]
  exact ⟨d', rfl, hsupp, ExteriorProductProjections.schemeDeltaDimension_subschemeι_le K sX
    (integralComponentAt v) d' hsupp⟩

/-- The Tor-formula product of `A z` with a fixed cycle is additive in `z`, so an identity with
`B z` which holds for the prime cycles of `z` holds for `z`. -/
private theorem torFormulaCycleIntersectionProduct_eq_of_primeCycles (K : Type u) [Field K]
    {X P : Scheme.{u}} (sX : X ⟶ Spec (.of K)) [IsVariety K sX] (sP : P ⟶ Spec (.of K))
    [LocallyOfFiniteType sP] [IsLocallyNoetherian P] [CompactSpace P] (hP : IsRegular P)
    {d d' m : ℤ}
    (A : CycleGroup (fieldChowSituation K) sX d →+ CycleGroup (fieldChowSituation K) sP d')
    (B : CycleGroup (fieldChowSituation K) sX d →+ CycleGroup (fieldChowSituation K) sP m)
    (Γ : AlgebraicCycle P ℤ) (z : CycleGroup (fieldChowSituation K) sX d)
    (hz : (Function.support z.1).Finite)
    (h : ∀ v ∈ hz.toFinset, torFormulaCycleIntersectionProduct (fieldChowSituation K) sP hP m
      (A (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sX
        (integralComponentAt v).subschemeι d)).1 Γ =
      (B (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sX
        (integralComponentAt v).subschemeι d)).1) :
    torFormulaCycleIntersectionProduct (fieldChowSituation K) sP hP m (A z).1 Γ = (B z).1 := by
  classical
  rw [cycle_eq_sum_zsmul_primeCycles z hz, map_sum, map_sum]
  simp only [map_zsmul, AddSubgroup.val_finsetSum, AddSubgroup.coe_zsmul]
  rw [torFormulaCycleIntersectionProduct, cycleIntersectionProduct_sum_left]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [cycleIntersectionProduct_zsmul_left _ _ (finite_support_of_compactSpace _)
    (finite_support_of_compactSpace _)]
  exact congrArg _ (h v hv)

end Graph

/-! ### Pullback along a morphism -/

section Pullback

variable (K : Type u) [Field K] [IsAlgClosed K] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K))
  (sY : Y ⟶ Spec (.of K)) [IsProjectiveVariety K sX] [IsProjectiveVariety K sY]
  (hX : IsRegular X) (hY : IsRegular Y) {dX dY : ℕ}
  (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞))
  (hdY : topologicalKrullDim Y = (dY : WithBot ℕ∞))

omit [IsAlgClosed K] in
include hdX hdY in
/-- The dimension of `X × Y` is `dim X + dim Y`. -/
theorem topologicalKrullDim_pullback_eq :
    topologicalKrullDim (pullback sX sY : Scheme.{u}) = ((dX + dY : ℕ) : WithBot ℕ∞) := by
  exact eq_natCast_add_of_eq_add (topologicalKrullDim_pullback_eq_add_fst K sX sY hdY) hdX

/-- The class `[Γ_f] ∈ CH_{dim X}(X × Y)` of the graph of `f`. -/
def graphClass (f : X ⟶ Y) (hf : f ≫ sY = sX) :
    chowGroup (fieldChowSituation K) (pullback.fst sX sY ≫ sX) (dX : ℤ) :=
  QuotientAddGroup.mk' _
    (cycleAssociatedToClosedSubscheme (fieldChowSituation K) (pullback.fst sX sY ≫ sX)
      (graph f hf) (dX : ℤ))

/-- **Stacks 0B0H: pullback along a morphism of nonsingular projective varieties.** For
`f : X ⟶ Y`, `f^* : CH_k(Y) ⟶ CH_m(X)`, `k + dim X = dim Y + m`, is

`f^*(α) = pr_{X,*}(Γ_f · pr_Y^*(α))`,

the flat pullback `pr_Y^*` along the second projection of `X × Y` (of relative dimension
`dim X`), the intersection product of Section 43.21 with the class of the graph on the
nonsingular projective variety `X × Y`, and proper pushforward along the first projection. -/
def chowPullback (f : X ⟶ Y) (hf : f ≫ sY = sX) {k m : ℤ} (hkm : k + dX = dY + m) :
    chowGroup (fieldChowSituation K) sY k →+ chowGroup (fieldChowSituation K) sX m :=
  (properChowPushforward (fieldChowSituation K) (pullback.fst sX sY ≫ sX) sX
      (pullback.fst sX sY) rfl m
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper (fieldChowSituation K)
        (pullback.fst sX sY ≫ sX) sX (pullback.fst sX sY) rfl m)).comp
    ((chowMul K (pullback.fst sX sY ≫ sX) (isRegular_pullback_of_isRegular sX sY hX hY)
        (topologicalKrullDim_pullback_eq K sX sY hdX hdY)
        (show (dX : ℤ) + (k + dX) = ((dX + dY : ℕ) : ℤ) + m by push_cast; omega)
        (graphClass K sX sY f hf)).comp
      (flatPullbackChowOfRelativeDimension (fieldChowSituation K) (pullback.fst sX sY ≫ sX) sY
        (pullback.snd sX sY) pullback.condition.symm dX
        (ExteriorProductProjections.relativeDimension_pullbackSnd sX sY dX hdX) k))

end Pullback

/-! ### The graph meets the pullbacks of cycles transversally -/

section GraphTransversal

variable (K : Type u) [Field K] [IsAlgClosed K] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K))
  (sY : Y ⟶ Spec (.of K)) [IsVariety K sX] [IsVariety K sY]
  (hX : IsRegular X) (hY : IsRegular Y) {dX dY : ℕ}
  (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞))
  (hdY : topologicalKrullDim Y = (dY : WithBot ℕ∞)) (f : X ⟶ Y) (hf : f ≫ sY = sX)

include hdX in
/-- **The remark on graphs in the proof of Tag 0B2X**, on cycles: for every `d`-cycle `z` on `X`,
`pr_X^*(z) · [Γ_f] = s_*(z)`, where `s : X ⟶ X × Y` is the graph. -/
theorem torFormulaCycleIntersectionProduct_flatPullback_fst_graph (d : ℤ)
    (z : CycleGroup (fieldChowSituation K) sX d) :
    letI : IsLocallyNoetherian (pullback sX sY : Scheme.{u}) :=
      isLocallyNoetherian_of_isRegular (isRegular_pullback_of_isRegular sX sY hX hY)
    torFormulaCycleIntersectionProduct (fieldChowSituation K) (pullback.fst sX sY ≫ sX)
        (isRegular_pullback_of_isRegular sX sY hX hY) d
        (flatPullback (fieldChowSituation K) (pullback.fst sX sY ≫ sX) sX (pullback.fst sX sY) rfl
          dY (ExteriorProductProjections.relativeDimension_pullbackFst sX sY dY hdY) d z).1
        (cycleAssociatedToClosedSubscheme (fieldChowSituation K) (pullback.fst sX sY ≫ sX)
          (graph f hf) (dX : ℤ)).1 =
      (properPushforward (fieldChowSituation K) sX (pullback.fst sX sY ≫ sX) (graph f hf)
        (graph_comp_structure f hf) d z).1 := by
  have hP := isRegular_pullback_of_isRegular sX sY hX hY
  let : IsLocallyNoetherian (pullback sX sY : Scheme.{u}) := isLocallyNoetherian_of_isRegular hP
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : CompactSpace (pullback sX sY : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst sX sY ≫ sX)
  have hz : (Function.support z.1).Finite := finite_support_of_compactSpace z.1
  have hdP := eq_natCast_add_of_eq_add (topologicalKrullDim_pullback_eq_add_fst K sX sY hdY) hdX
  have hep := topologicalKrullDim_pullback_eq_add_fst K sX sY hdY
  have heq : topologicalKrullDim X = topologicalKrullDim X + ((0 : ℕ) : WithBot ℕ∞) := by simp
  have hprime : ∀ v ∈ hz.toFinset,
      torFormulaCycleIntersectionProduct (fieldChowSituation K) (pullback.fst sX sY ≫ sX) hP d
          (flatPullback (fieldChowSituation K) (pullback.fst sX sY ≫ sX) sX (pullback.fst sX sY)
            rfl dY (ExteriorProductProjections.relativeDimension_pullbackFst sX sY dY hdY) d
            (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sX
              (integralComponentAt v).subschemeι d)).1
          (cycleAssociatedToClosedSubscheme (fieldChowSituation K) (pullback.fst sX sY ≫ sX)
            (graph f hf) (dX : ℤ)).1 =
        (properPushforward (fieldChowSituation K) sX (pullback.fst sX sY ≫ sX) (graph f hf)
          (graph_comp_structure f hf) d
          (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sX
            (integralComponentAt v).subschemeι d)).1 := by
    intro v hv
    obtain ⟨d', rfl, hsupp, hδ⟩ := exists_nat_eq_and_deltaDimension_le K sX z (hz.mem_toFinset.1 hv)
    rw [flatPullback_cycleAssociatedToClosedSubscheme_comap_of_le _ _ _ _ _ _ _ _ _ hδ]
    have h := torFormulaCycleIntersectionProduct_comap_closedImmersion K sX
      (pullback.fst sX sY ≫ sX) sX (graph f hf) (graph_comp_structure f hf) (pullback.fst sX sY)
      rfl hP (dX + dY) dX dY 0 d' hdP hdX hep heq (integralComponentAt v) hsupp
    rwa [graph_fst, Scheme.IdealSheafData.comap_id, Nat.add_zero, Nat.cast_add] at h
  exact torFormulaCycleIntersectionProduct_eq_of_primeCycles K sX _ hP
    (flatPullback (fieldChowSituation K) (pullback.fst sX sY ≫ sX) sX (pullback.fst sX sY) rfl dY
      (ExteriorProductProjections.relativeDimension_pullbackFst sX sY dY hdY) d)
    (properPushforwardHom (fieldChowSituation K) sX (pullback.fst sX sY ≫ sX) (graph f hf)
      (graph_comp_structure f hf) d) _ z hz hprime

include hdX hdY in
/-- The pullback `pr_X^*(z)` of a cycle on `X` meets the graph properly. -/
theorem intersectProperly_flatPullback_fst_graph (d : ℤ)
    (z : CycleGroup (fieldChowSituation K) sX d) :
    AlgebraicCycle.IntersectProperly
      (flatPullback (fieldChowSituation K) (pullback.fst sX sY ≫ sX) sX (pullback.fst sX sY) rfl
          dY (ExteriorProductProjections.relativeDimension_pullbackFst sX sY dY hdY) d z).1
      (cycleAssociatedToClosedSubscheme (fieldChowSituation K) (pullback.fst sX sY ≫ sX)
          (graph f hf) (dX : ℤ)).1 := by
  have hdP := eq_natCast_add_of_eq_add (topologicalKrullDim_pullback_eq_add_fst K sX sY hdY) hdX
  have hep := topologicalKrullDim_pullback_eq_add_fst K sX sY hdY
  have heq : topologicalKrullDim X = topologicalKrullDim X + ((0 : ℕ) : WithBot ℕ∞) := by simp
  exact intersectProperly_flatPullback_closedImmersion K sX (pullback.fst sX sY ≫ sX) sX
    (graph f hf) (graph_comp_structure f hf) (pullback.fst sX sY) rfl (dX + dY) dX dY 0 hdP hdX
    hep heq d z

include hdX hdY in
/-- When `f` is flat, the pullback `pr_Y^*(w)` of a cycle on `Y` meets the graph properly. -/
theorem intersectProperly_flatPullback_snd_graph [Flat f] (e : ℕ)
    (he : topologicalKrullDim X = topologicalKrullDim Y + (e : WithBot ℕ∞)) (d : ℤ)
    (w : CycleGroup (fieldChowSituation K) sY d) :
    AlgebraicCycle.IntersectProperly
      (flatPullback (fieldChowSituation K) (pullback.fst sX sY ≫ sX) sY (pullback.snd sX sY)
          pullback.condition.symm dX
          (ExteriorProductProjections.relativeDimension_pullbackSnd sX sY dX hdX) d w).1
      (cycleAssociatedToClosedSubscheme (fieldChowSituation K) (pullback.fst sX sY ≫ sX)
          (graph f hf) (dX : ℤ)).1 := by
  have : Flat (graph f hf ≫ pullback.snd sX sY) := by rw [graph_snd]; infer_instance
  have hdP := eq_natCast_add_of_eq_add (topologicalKrullDim_pullback_eq_add_fst K sX sY hdY) hdX
  have hep := topologicalKrullDim_pullback_eq_add_snd K sX sY hdX
  exact intersectProperly_flatPullback_closedImmersion K sX (pullback.fst sX sY ≫ sX) sY
    (graph f hf) (graph_comp_structure f hf) (pullback.snd sX sY) pullback.condition.symm
    (dX + dY) dX dX e hdP hdX hep he d w

include hdX hdY in
/-- **The computation behind part (4) of Tag 0B2X**, on cycles: when `f` is flat of relative
dimension `e`, for every `d`-cycle `w` on `Y`, `pr_Y^*(w) · [Γ_f] = s_*(f^*w)`. -/
theorem torFormulaCycleIntersectionProduct_flatPullback_snd_graph [Flat f] (e : ℕ)
    (he : topologicalKrullDim X = topologicalKrullDim Y + (e : WithBot ℕ∞)) (d : ℤ)
    (w : CycleGroup (fieldChowSituation K) sY d) :
    letI : IsLocallyNoetherian (pullback sX sY : Scheme.{u}) :=
      isLocallyNoetherian_of_isRegular (isRegular_pullback_of_isRegular sX sY hX hY)
    letI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hf
    torFormulaCycleIntersectionProduct (fieldChowSituation K) (pullback.fst sX sY ≫ sX)
        (isRegular_pullback_of_isRegular sX sY hX hY) (d + (e : ℤ))
        (flatPullback (fieldChowSituation K) (pullback.fst sX sY ≫ sX) sY (pullback.snd sX sY)
          pullback.condition.symm dX
          (ExteriorProductProjections.relativeDimension_pullbackSnd sX sY dX hdX) d w).1
        (cycleAssociatedToClosedSubscheme (fieldChowSituation K) (pullback.fst sX sY ≫ sX)
          (graph f hf) (dX : ℤ)).1 =
      (properPushforward (fieldChowSituation K) sX (pullback.fst sX sY ≫ sX) (graph f hf)
        (graph_comp_structure f hf) (d + (e : ℤ))
        (flatPullback (fieldChowSituation K) sX sY f hf e
          (relativeDimension_of_flat_of_isVariety K sX sY f hf e he) d w)).1 := by
  have hP := isRegular_pullback_of_isRegular sX sY hX hY
  let : IsLocallyNoetherian (pullback sX sY : Scheme.{u}) := isLocallyNoetherian_of_isRegular hP
  let : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hf
  have : Flat (graph f hf ≫ pullback.snd sX sY) := by rw [graph_snd]; infer_instance
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : CompactSpace (pullback sX sY : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst sX sY ≫ sX)
  have hw : (Function.support w.1).Finite := finite_support_of_compactSpace w.1
  have hdP := eq_natCast_add_of_eq_add (topologicalKrullDim_pullback_eq_add_fst K sX sY hdY) hdX
  have hep := topologicalKrullDim_pullback_eq_add_snd K sX sY hdX
  have hprime : ∀ v ∈ hw.toFinset,
      torFormulaCycleIntersectionProduct (fieldChowSituation K) (pullback.fst sX sY ≫ sX) hP
          (d + (e : ℤ))
          (flatPullback (fieldChowSituation K) (pullback.fst sX sY ≫ sX) sY (pullback.snd sX sY)
            pullback.condition.symm dX
            (ExteriorProductProjections.relativeDimension_pullbackSnd sX sY dX hdX) d
            (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sY
              (integralComponentAt v).subschemeι d)).1
          (cycleAssociatedToClosedSubscheme (fieldChowSituation K) (pullback.fst sX sY ≫ sX)
            (graph f hf) (dX : ℤ)).1 =
        (properPushforward (fieldChowSituation K) sX (pullback.fst sX sY ≫ sX) (graph f hf)
          (graph_comp_structure f hf) (d + (e : ℤ))
          (flatPullback (fieldChowSituation K) sX sY f hf e
            (relativeDimension_of_flat_of_isVariety K sX sY f hf e he) d
            (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sY
              (integralComponentAt v).subschemeι d))).1 := by
    intro v hv
    obtain ⟨d', rfl, hsupp, hδ⟩ := exists_nat_eq_and_deltaDimension_le K sY w (hw.mem_toFinset.1 hv)
    rw [flatPullback_cycleAssociatedToClosedSubscheme_comap_of_le _ _ _ _ _ _ _ _ _ hδ,
      flatPullback_cycleAssociatedToClosedSubscheme_comap_of_le _ _ _ _ _ _ _ _ _ hδ]
    have h := torFormulaCycleIntersectionProduct_comap_closedImmersion K sX
      (pullback.fst sX sY ≫ sX) sY (graph f hf) (graph_comp_structure f hf) (pullback.snd sX sY)
      pullback.condition.symm hP (dX + dY) dX dX e d' hdP hdX hep he (integralComponentAt v)
      hsupp
    rwa [graph_snd, Nat.cast_add, Nat.cast_add] at h
  exact torFormulaCycleIntersectionProduct_eq_of_primeCycles K sY _ hP
    (flatPullback (fieldChowSituation K) (pullback.fst sX sY ≫ sX) sY (pullback.snd sX sY)
      pullback.condition.symm dX
      (ExteriorProductProjections.relativeDimension_pullbackSnd sX sY dX hdX) d)
    ((properPushforwardHom (fieldChowSituation K) sX (pullback.fst sX sY ≫ sX) (graph f hf)
      (graph_comp_structure f hf) (d + (e : ℤ))).comp
      (flatPullback (fieldChowSituation K) sX sY f hf e
        (relativeDimension_of_flat_of_isVariety K sX sY f hf e he) d)) _ w hw hprime

end GraphTransversal

/-- `CH_k(X) = 0` for `k < 0`, for a variety `X` over a field. -/
private theorem chowGroup_eq_zero_of_neg_field (K : Type u) [Field K] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of K)) [IsVariety K sX] {k : ℤ} (hk : k < 0)
    (x : chowGroup (fieldChowSituation K) sX k) : x = 0 :=
  Stacks.Chow.chowGroup_eq_zero_of_neg (fieldChowSituation K) (fun _ _ => rfl) sX hk x

/-! ### Flat pullback is multiplicative -/

section FlatProduct

variable (K : Type u) [Field K] [IsAlgClosed K] {P Y : Scheme.{u}} (sP : P ⟶ Spec (.of K))
  (sY : Y ⟶ Spec (.of K)) [IsProjectiveVariety K sP] [IsProjectiveVariety K sY]
  (hP : IsRegular P) (hY : IsRegular Y) (p : P ⟶ Y) [Flat p] (hp : p ≫ sY = sP) (e : ℕ)
  (he : topologicalKrullDim P = topologicalKrullDim Y + (e : WithBot ℕ∞)) {dY : ℕ}
  (hdY : topologicalKrullDim Y = (dY : WithBot ℕ∞))

include hdY in
/-- **Tag 0B0Z on Chow groups: flat pullback is multiplicative**,
`p^*(a · b) = p^*a · p^*b` for a flat morphism `p` of nonsingular projective varieties. Both
classes are represented by properly intersecting cycles (Tag 0B1U); when the expected dimension
is nonnegative this is Tag 0B0Z, and otherwise both sides vanish, the components of the two
cycles, and hence of their pullbacks, being disjoint. -/
theorem flatPullbackChow_chowMulFun {r s m : ℤ} (hm : r + s = dY + m)
    (a : chowGroup (fieldChowSituation K) sY r) (b : chowGroup (fieldChowSituation K) sY s) :
    letI : LocallyOfFiniteType p := locallyOfFiniteType_of_isVariety_comp K sP sY p hp
    flatPullbackChowOfRelativeDimension (fieldChowSituation K) sP sY p hp e
        (relativeDimension_of_flat_of_isVariety K sP sY p hp e he) m (chowMulFun K sY hY m a b) =
      chowMulFun K sP hP (m + e)
        (flatPullbackChowOfRelativeDimension (fieldChowSituation K) sP sY p hp e
          (relativeDimension_of_flat_of_isVariety K sP sY p hp e he) r a)
        (flatPullbackChowOfRelativeDimension (fieldChowSituation K) sP sY p hp e
          (relativeDimension_of_flat_of_isVariety K sP sY p hp e he) s b) := by
  let : LocallyOfFiniteType p := locallyOfFiniteType_of_isVariety_comp K sP sY p hp
  set hrel := relativeDimension_of_flat_of_isVariety K sP sY p hp e he
  have hdP := eq_natCast_add_of_eq_add he hdY
  have hm' : (r + e) + (s + e) = ((dY + e : ℕ) : ℤ) + (m + e) := by push_cast; omega
  by_cases hr : r < 0
  · rw [chowGroup_eq_zero_of_neg_field K sY hr a, chowMulFun_zero_left hdY hm, map_zero,
      map_zero, chowMulFun_zero_left hdP hm']
  by_cases hs : s < 0
  · rw [chowGroup_eq_zero_of_neg_field K sY hs b, chowMulFun_zero_right hdY hm, map_zero, map_zero,
      chowMulFun_zero_right hdP hm']
  obtain ⟨r', rfl⟩ : ∃ r' : ℕ, r = r' := ⟨r.toNat, by omega⟩
  obtain ⟨s', rfl⟩ : ∃ s' : ℕ, s = s' := ⟨s.toNat, by omega⟩
  obtain ⟨β, rfl⟩ := QuotientAddGroup.mk'_surjective _ b
  obtain ⟨α, rfl, hαβ⟩ := exists_mk_eq_intersectProperly (hX := hY) a (fun _ : Unit => β)
  have hαβ' : AlgebraicCycle.IntersectProperly α.1 β.1 := hαβ ()
  have hpαβ := Stacks.Intersection.CycleFlatPullback.intersectProperly_flatPullback K sP sY p hp e
    he r' s' α β hαβ'
  rw [chowMulFun_mk hdY hm α β hαβ', flatPullbackChowOfRelativeDimension_mk,
    flatPullbackChowOfRelativeDimension_mk, flatPullbackChowOfRelativeDimension_mk,
    chowMulFun_mk hdP hm' _ _ hpαβ]
  by_cases hmneg : m < 0
  · rw [← flatPullbackChowOfRelativeDimension_mk,
      chowGroup_eq_zero_of_neg_field K sY hmneg (QuotientAddGroup.mk' _ _), map_zero]
    · symm
      rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
      convert (rationalEquivalences (fieldChowSituation K) sP (m + e)).zero_mem
      refine Subtype.ext ?_
      refine torFormulaCycleIntersectionProduct_eq_zero_of_disjoint (K := K) (sX := sP) (hX := hP)
        hdP _ fun x y hx hy => ?_
      rw [flatPullback_apply] at hx hy
      have hx' := left_ne_zero_of_mul hx
      have hy' := left_ne_zero_of_mul hy
      have hdisj := inter_eq_empty_of_intersectProperly (K := K) (sX := sY) hdY (by omega) α β
        hαβ' hx' hy'
      refine Set.eq_empty_of_subset_empty fun z hz => ?_
      have hsub : ∀ w : P, closure ({w} : Set P) ⊆ p.base ⁻¹' closure ({p.base w} : Set Y) :=
        fun w => closure_minimal (Set.singleton_subset_iff.2 (subset_closure rfl))
          (isClosed_closure.preimage p.continuous)
      have hpz : p.base z ∈ closure ({p.base x} : Set Y) ∩ closure ({p.base y} : Set Y) :=
        ⟨hsub x hz.1, hsub y hz.2⟩
      rw [hdisj] at hpz
      exact hpz
  obtain ⟨n', rfl⟩ : ∃ n' : ℕ, m = n' := ⟨m.toNat, by omega⟩
  obtain ⟨-, h0B0Z⟩ :=
    Stacks.Intersection.CycleFlatPullback.flatPullback_torFormulaCycleIntersectionProduct_eq K sP sY
      hP hY p hp e dY
    r' s' n' hdY he (by omega) α β hαβ'
  exact congrArg _ (Subtype.ext h0B0Z)

include hdY in
/-- **Tag 0B10 on Chow groups: the projection formula for a flat proper morphism**,
`p_*(a · p^*b) = p_*(a) · b`. Represent `b` by a cycle `β` and `a` by a cycle meeting `p^*β`
properly (Tag 0B1U); then this is Tag 0B10 for cycles. -/
theorem properChowPushforward_chowMulFun [IsProper p] {r s n : ℤ} (hn : r + s = dY + n)
    (a : chowGroup (fieldChowSituation K) sP r) (b : chowGroup (fieldChowSituation K) sY s) :
    letI : LocallyOfFiniteType p := locallyOfFiniteType_of_isVariety_comp K sP sY p hp
    properChowPushforward (fieldChowSituation K) sP sY p hp n
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper (fieldChowSituation K) sP
          sY p hp n)
        (chowMulFun K sP hP n a (flatPullbackChowOfRelativeDimension (fieldChowSituation K) sP sY
          p hp e (relativeDimension_of_flat_of_isVariety K sP sY p hp e he) s b)) =
      chowMulFun K sY hY n
        (properChowPushforward (fieldChowSituation K) sP sY p hp r
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper (fieldChowSituation K)
            sP sY p hp r) a) b := by
  let : LocallyOfFiniteType p := locallyOfFiniteType_of_isVariety_comp K sP sY p hp
  have hdP := eq_natCast_add_of_eq_add he hdY
  have hn' : r + (s + e) = ((dY + e : ℕ) : ℤ) + n := by push_cast; omega
  by_cases hr : r < 0
  · rw [chowGroup_eq_zero_of_neg_field K sP hr a, chowMulFun_zero_left hdP hn', map_zero, map_zero,
      chowMulFun_zero_left hdY hn]
  by_cases hs : s < 0
  · rw [chowGroup_eq_zero_of_neg_field K sY hs b, map_zero, chowMulFun_zero_right hdP hn', map_zero,
      chowMulFun_zero_right hdY hn]
  obtain ⟨r', rfl⟩ : ∃ r' : ℕ, r = r' := ⟨r.toNat, by omega⟩
  obtain ⟨s', rfl⟩ : ∃ s' : ℕ, s = s' := ⟨s.toNat, by omega⟩
  obtain ⟨β, rfl⟩ := QuotientAddGroup.mk'_surjective _ b
  set pβ := flatPullback (fieldChowSituation K) sP sY p hp e
    (relativeDimension_of_flat_of_isVariety K sP sY p hp e he) (s' : ℤ) β
  obtain ⟨α, rfl, hα⟩ := exists_mk_eq_intersectProperly (hX := hP) a (fun _ : Unit => pβ)
  obtain ⟨hprop, hid⟩ :=
    Stacks.Intersection.ProjectionFormula.properPushforward_torFormulaCycleIntersectionProduct_eq
      K sP sY hP hY p hp e dY r' s' n hdY he hn α β (hα ())
  rw [flatPullbackChowOfRelativeDimension_mk, chowMulFun_mk hdP hn' α pβ (hα ()),
    properChowPushforward_mk, properChowPushforward_mk, chowMulFun_mk hdY hn _ β hprop]
  exact congrArg _ (Subtype.ext hid)

end FlatProduct

/-! ### The graph on Chow groups -/

section GraphChow

variable (K : Type u) [Field K] [IsAlgClosed K] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K))
  (sY : Y ⟶ Spec (.of K)) [IsProjectiveVariety K sX] [IsProjectiveVariety K sY]
  (hX : IsRegular X) (hY : IsRegular Y) {dX dY : ℕ}
  (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞))
  (hdY : topologicalKrullDim Y = (dY : WithBot ℕ∞)) (f : X ⟶ Y) (hf : f ≫ sY = sX)

/-- Flat pullback `pr_X^* : CH_d(X) ⟶ CH_{d + dim Y}(X × Y)` along the first projection. -/
abbrev prXPullback (d : ℤ) :
    chowGroup (fieldChowSituation K) sX d →+
      chowGroup (fieldChowSituation K) (pullback.fst sX sY ≫ sX) (d + (dY : ℤ)) :=
  flatPullbackChowOfRelativeDimension (fieldChowSituation K) (pullback.fst sX sY ≫ sX) sX
    (pullback.fst sX sY) rfl dY
    (ExteriorProductProjections.relativeDimension_pullbackFst sX sY dY hdY)
    d

/-- Flat pullback `pr_Y^* : CH_d(Y) ⟶ CH_{d + dim X}(X × Y)` along the second projection. -/
abbrev prYPullback (d : ℤ) :
    chowGroup (fieldChowSituation K) sY d →+
      chowGroup (fieldChowSituation K) (pullback.fst sX sY ≫ sX) (d + (dX : ℤ)) :=
  flatPullbackChowOfRelativeDimension (fieldChowSituation K) (pullback.fst sX sY ≫ sX) sY
    (pullback.snd sX sY) pullback.condition.symm dX
    (ExteriorProductProjections.relativeDimension_pullbackSnd sX sY dX hdX) d

/-- `pr_X^*` unfolded to the flat pullback along the first projection. -/
private theorem prXPullback_eq (d : ℤ) (z : chowGroup (fieldChowSituation K) sX d) :
    prXPullback K sX sY hdY d z = flatPullbackChowOfRelativeDimension (fieldChowSituation K)
      (pullback.fst sX sY ≫ sX) sX (pullback.fst sX sY) rfl dY
      (relativeDimension_of_flat_of_isVariety K _ sX (pullback.fst sX sY) rfl dY
        (topologicalKrullDim_pullback_eq_add_fst K sX sY hdY)) d z :=
  rfl

/-- `pr_Y^*` unfolded to the flat pullback along the second projection. -/
private theorem prYPullback_eq (d : ℤ) (z : chowGroup (fieldChowSituation K) sY d) :
    prYPullback K sX sY hdX d z = flatPullbackChowOfRelativeDimension (fieldChowSituation K)
      (pullback.fst sX sY ≫ sX) sY (pullback.snd sX sY) pullback.condition.symm dX
      (relativeDimension_of_flat_of_isVariety K _ sY (pullback.snd sX sY)
        pullback.condition.symm dX (topologicalKrullDim_pullback_eq_add_snd K sX sY hdX)) d z :=
  rfl

/-- Proper pushforward `pr_{X,*} : CH_d(X × Y) ⟶ CH_d(X)`. -/
abbrev prXPush (d : ℤ) :
    chowGroup (fieldChowSituation K) (pullback.fst sX sY ≫ sX) d →+
      chowGroup (fieldChowSituation K) sX d :=
  properChowPushforward (fieldChowSituation K) (pullback.fst sX sY ≫ sX) sX (pullback.fst sX sY)
    rfl d (properPushforwardFactorsThroughRationalEquivalence_of_isProper (fieldChowSituation K)
      (pullback.fst sX sY ≫ sX) sX (pullback.fst sX sY) rfl d)

/-- Proper pushforward `s_* : CH_d(X) ⟶ CH_d(X × Y)` along the graph of `f`. -/
abbrev graphPush (d : ℤ) :
    chowGroup (fieldChowSituation K) sX d →+
      chowGroup (fieldChowSituation K) (pullback.fst sX sY ≫ sX) d :=
  properChowPushforward (fieldChowSituation K) sX (pullback.fst sX sY ≫ sX) (graph f hf)
    (graph_comp_structure f hf) d
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper (fieldChowSituation K) sX
      (pullback.fst sX sY ≫ sX) (graph f hf) (graph_comp_structure f hf) d)

omit [IsAlgClosed K] in
/-- `pr_{X,*} ∘ s_* = id` on Chow groups. -/
theorem prXPush_graphPush (d : ℤ) (z : chowGroup (fieldChowSituation K) sX d) :
    prXPush K sX sY d (graphPush K sX sY f hf d z) = z := by
  obtain ⟨ζ, rfl⟩ := QuotientAddGroup.mk'_surjective _ z
  simp only [properChowPushforward_mk]
  rw [properPushforward_fst_properPushforward_graph f hf d ζ]

include hdX hdY in
/-- **The remark on graphs, on Chow groups**: `[Γ_f] · pr_X^*(z) = s_*(z)`. -/
theorem chowMulFun_graphClass_prXPullback (d : ℤ) (z : chowGroup (fieldChowSituation K) sX d) :
    chowMulFun K (pullback.fst sX sY ≫ sX) (isRegular_pullback_of_isRegular sX sY hX hY) d
        (graphClass K sX sY (dX := dX) f hf) (prXPullback K sX sY hdY d z) =
      graphPush K sX sY f hf d z := by
  obtain ⟨ζ, rfl⟩ := QuotientAddGroup.mk'_surjective _ z
  have hP := isRegular_pullback_of_isRegular sX sY hX hY
  have hdP := topologicalKrullDim_pullback_eq K sX sY hdX hdY
  have : CompactSpace (pullback sX sY : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst sX sY ≫ sX)
  rw [prXPullback, flatPullbackChowOfRelativeDimension_mk, graphClass,
    chowMulFun_mk hdP (by push_cast; ring) _ _
      (Stacks.Intersection.ReductionToDiagonal.cycle_intersectProperly_symm
        (intersectProperly_flatPullback_fst_graph K sX sY hdX hdY f hf d ζ)),
    graphPush, properChowPushforward_mk]
  congr 1
  refine Subtype.ext ?_
  rw [coe_mulCycle, torFormulaCycleIntersectionProduct_comm]
  exact torFormulaCycleIntersectionProduct_flatPullback_fst_graph K sX sY hX hY hdX hdY f hf d ζ

include hdX hdY in
/-- **A product with the graph is pushed forward from `X`**: for every class `w` on `X × Y`,
`[Γ_f] · w = s_*(pr_{X,*}([Γ_f] · w))`. Represent `w` by a cycle meeting the graph properly
(Tag 0B1U); the product of cycles is then supported on the graph, so it is the pushforward of a
cycle on `X`, and `pr_{X,*} ∘ s_* = id`. -/
theorem chowMulFun_graphClass_eq_graphPush {s m : ℤ} (hm : (dX : ℤ) + s = ((dX + dY : ℕ) : ℤ) + m)
    (w : chowGroup (fieldChowSituation K) (pullback.fst sX sY ≫ sX) s) :
    chowMulFun K (pullback.fst sX sY ≫ sX) (isRegular_pullback_of_isRegular sX sY hX hY) m
        (graphClass K sX sY (dX := dX) f hf) w =
      graphPush K sX sY f hf m (prXPush K sX sY m
        (chowMulFun K (pullback.fst sX sY ≫ sX) (isRegular_pullback_of_isRegular sX sY hX hY) m
          (graphClass K sX sY (dX := dX) f hf) w)) := by
  have hP := isRegular_pullback_of_isRegular sX sY hX hY
  have hdP := topologicalKrullDim_pullback_eq K sX sY hdX hdY
  have : IsIntegral X := IsVariety.toIsIntegral (k := K) (f := sX)
  set Γc := cycleAssociatedToClosedSubscheme (fieldChowSituation K) (pullback.fst sX sY ≫ sX)
    (graph f hf) (dX : ℤ)
  obtain ⟨ω, rfl, hω⟩ := exists_mk_eq_intersectProperly (hX := hP) w (fun _ : Unit => Γc)
  have hΓω : AlgebraicCycle.IntersectProperly Γc.1 ω.1 :=
    Stacks.Intersection.ReductionToDiagonal.cycle_intersectProperly_symm (hω ())
  rw [graphClass, chowMulFun_mk hdP hm _ _ hΓω]
  set c := mulCycle K (pullback.fst sX sY ≫ sX) hP m Γc.1 ω.1
  have hc : ∀ z, z ∉ Set.range (graph f hf).base → c.1 z = 0 := by
    intro z hz
    by_contra hcz
    obtain ⟨x, y, hx, -, hzx, -⟩ :=
      exists_mem_closure_inter_of_torFormulaCycleIntersectionProduct_ne_zero (K := K)
        (sX := pullback.fst sX sY ≫ sX) (hX := hP) hdP m hcz
    have hxgen : x = (graph f hf).base (genericPoint X) := by
      by_contra hne
      exact hx (cycleAssociatedToClosedSubscheme_isIntegral_apply_of_ne (fieldChowSituation K)
        _ (graph f hf) _ hne)
    rw [hxgen, ← Set.image_singleton, (graph f hf).isClosedEmbedding.closure_image_eq,
      genericPoint_spec, Set.image_univ] at hzx
    exact hz hzx
  have hceq := properPushforward_cyclePullbackAlongClosedImmersion_eq (fieldChowSituation K) sX
    (pullback.fst sX sY ≫ sX) (graph f hf) (graph_comp_structure f hf) m c hc
  rw [graphPush, prXPush, properChowPushforward_mk, ← hceq,
    properPushforward_fst_properPushforward_graph f hf m, properChowPushforward_mk, hceq]

include hdX hdY in
/-- **The defining property of `f^*`**: `s_*(f^*(b)) = [Γ_f] · pr_Y^*(b)`. -/
theorem graphPush_chowPullback {k m : ℤ} (hkm : k + dX = dY + m)
    (b : chowGroup (fieldChowSituation K) sY k) :
    graphPush K sX sY f hf m (chowPullback K sX sY hX hY hdX hdY f hf hkm b) =
      chowMulFun K (pullback.fst sX sY ≫ sX) (isRegular_pullback_of_isRegular sX sY hX hY) m
        (graphClass K sX sY (dX := dX) f hf) (prYPullback K sX sY hdX k b) := by
  rw [chowMulFun_graphClass_eq_graphPush K sX sY hX hY hdX hdY f hf (by push_cast; omega)]
  rfl

include hdX hdY in
/-- **Stacks 0B2X, part (4): for flat `f` the pullback is flat pullback.** If `f` is flat of
relative dimension `e`, then `f^* = f^*_{flat} : CH_k(Y) ⟶ CH_{k+e}(X)`. -/
@[stacks 0B2X "part (4): for flat `f` of relative dimension `e`, the pullback `f^*` of Tag 0B0H \
is the flat pullback `CH_k(Y) → CH_{k+e}(X)` of Section 43.9"]
theorem chowPullback_eq_flatPullbackChow [Flat f] (e : ℕ)
    (he : topologicalKrullDim X = topologicalKrullDim Y + (e : WithBot ℕ∞)) {k : ℤ}
    (hkm : k + dX = dY + (k + e)) :
    letI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hf
    chowPullback K sX sY hX hY hdX hdY f hf hkm =
      flatPullbackChowOfRelativeDimension (fieldChowSituation K) sX sY f hf e
        (relativeDimension_of_flat_of_isVariety K sX sY f hf e he) k := by
  let : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hf
  have hP := isRegular_pullback_of_isRegular sX sY hX hY
  have hdP := topologicalKrullDim_pullback_eq K sX sY hdX hdY
  refine AddMonoidHom.ext fun b => ?_
  rw [← prXPush_graphPush K sX sY f hf (k + e) (chowPullback K sX sY hX hY hdX hdY f hf hkm b),
    graphPush_chowPullback K sX sY hX hY hdX hdY f hf hkm b,
    ← prXPush_graphPush K sX sY f hf (k + e)
      (flatPullbackChowOfRelativeDimension _ _ _ _ _ _ _ _ b)]
  congr 1
  obtain ⟨β, rfl⟩ := QuotientAddGroup.mk'_surjective _ b
  rw [prYPullback, flatPullbackChowOfRelativeDimension_mk, flatPullbackChowOfRelativeDimension_mk,
    graphClass, chowMulFun_mk hdP (by push_cast; omega) _ _
      (Stacks.Intersection.ReductionToDiagonal.cycle_intersectProperly_symm
        (intersectProperly_flatPullback_snd_graph K sX sY hdX hdY f hf e he k β)),
    graphPush, properChowPushforward_mk]
  congr 1
  refine Subtype.ext ?_
  have : CompactSpace (pullback sX sY : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst sX sY ≫ sX)
  rw [coe_mulCycle, torFormulaCycleIntersectionProduct_comm]
  exact torFormulaCycleIntersectionProduct_flatPullback_snd_graph K sX sY hX hY hdX hdY f hf e
    he k β

include hdX hdY in
/-- **Stacks 0B2X, part (1), multiplicativity: `f^*(a · b) = f^*a · f^*b`.** -/
theorem chowPullback_chowMulFun {r s t r' s' t' : ℤ} (hr : r + dX = dY + r')
    (hs : s + dX = dY + s') (ht : t + dX = dY + t') (hrst : r + s = dY + t)
    (a : chowGroup (fieldChowSituation K) sY r) (b : chowGroup (fieldChowSituation K) sY s) :
    chowPullback K sX sY hX hY hdX hdY f hf ht (chowMulFun K sY hY t a b) =
      chowMulFun K sX hX t' (chowPullback K sX sY hX hY hdX hdY f hf hr a)
        (chowPullback K sX sY hX hY hdX hdY f hf hs b) := by
  have hP := isRegular_pullback_of_isRegular sX sY hX hY
  have hdP := topologicalKrullDim_pullback_eq K sX sY hdX hdY
  have hfst := topologicalKrullDim_pullback_eq_add_fst K sX sY hdY
  have hsnd := topologicalKrullDim_pullback_eq_add_snd K sX sY hdX
  set fa := chowPullback K sX sY hX hY hdX hdY f hf hr a
  set fb := chowPullback K sX sY hX hY hdX hdY f hf hs b
  set G := graphClass K sX sY (dX := dX) f hf
  have hpX := prXPullback_eq K sX sY hdY
  have hpY := prYPullback_eq K sX sY hdX
  have hGX := chowMulFun_graphClass_prXPullback K sX sY hX hY hdX hdY f hf
  have hChar : ∀ {k m : ℤ} (hkm : k + dX = dY + m) (z : chowGroup (fieldChowSituation K) sY k),
      graphPush K sX sY f hf m (chowPullback K sX sY hX hY hdX hdY f hf hkm z) =
        chowMulFun K (pullback.fst sX sY ≫ sX) hP m G (prYPullback K sX sY hdX k z) :=
    fun hkm z => graphPush_chowPullback K sX sY hX hY hdX hdY f hf hkm z
  rw [← prXPush_graphPush K sX sY f hf t' (chowPullback K sX sY hX hY hdX hdY f hf ht _),
    ← prXPush_graphPush K sX sY f hf t' (chowMulFun K sX hX t' fa fb)]
  refine congrArg (prXPush K sX sY t') ?_
  rw [hChar, ← hGX, hpX,
    flatPullbackChow_chowMulFun K (pullback.fst sX sY ≫ sX) sX hP hX _ rfl dY hfst hdX
      (show r' + s' = dX + t' by omega) fa fb, ← hpX, ← hpX, hpY,
    flatPullbackChow_chowMulFun K (pullback.fst sX sY ≫ sX) sY hP hY _ pullback.condition.symm dX
      hsnd hdY hrst a b,
    ← hpY, ← hpY]
  set A := prYPullback K sX sY hdX r a
  set B := prYPullback K sX sY hdX s b
  set FA := prXPullback K sX sY hdY r' fa
  set FB := prXPullback K sX sY hdY s' fb
  have e1 := chowMulFun_assoc (hX := hP) hdP (m₁ := r') (m₂ := t' + dY) (m := t')
    (by push_cast; omega) (by push_cast; omega) (by push_cast; omega) G FA FB
  have e2 : chowMulFun K _ hP r' G FA = chowMulFun K _ hP r' G A := by
    rw [hGX, hChar hr a]
  have e3 := chowMulFun_comm (hX := hP) hdP (m := r') (by push_cast; omega) G A
  have e4 := chowMulFun_assoc (hX := hP) hdP (m₁ := r') (m₂ := s') (m := t')
    (by push_cast; omega) (by push_cast; omega) (by push_cast; omega) A G FB
  have e5 : chowMulFun K _ hP s' G FB = chowMulFun K _ hP s' G B := by
    rw [hGX, hChar hs b]
  have e6 := chowMulFun_assoc (hX := hP) hdP (m₁ := r') (m₂ := s') (m := t')
    (by push_cast; omega) (by push_cast; omega) (by push_cast; omega) A G B
  have e7 := chowMulFun_assoc (hX := hP) hdP (m₁ := r') (m₂ := t + dX) (m := t')
    (by push_cast; omega) (by push_cast; omega) (by push_cast; omega) G A B
  rw [← e1, e2, e3, e4, e5, ← e6, ← e3, e7]

include hdX hdY in
/-- **Stacks 0B2X, part (1), the unit: `f^*[Y] = [X]`.** -/
theorem chowPullback_fundamentalClass {k m : ℤ} (hk : k = dY) (hm : m = dX)
    (hkm : k + dX = dY + m) :
    chowPullback K sX sY hX hY hdX hdY f hf hkm
        (QuotientAddGroup.mk' _
          (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sY (𝟙 Y) k)) =
      QuotientAddGroup.mk' _
        (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sX (𝟙 X) m) := by
  subst hk hm
  have hP := isRegular_pullback_of_isRegular sX sY hX hY
  have hdP := topologicalKrullDim_pullback_eq K sX sY hdX hdY
  have : JacobsonSpace (fieldChowSituation K).S :=
    inferInstanceAs (JacobsonSpace (Spec (CommRingCat.of K)))
  rw [← prXPush_graphPush K sX sY f hf (dX : ℤ) (chowPullback K sX sY hX hY hdX hdY f hf hkm _),
    graphPush_chowPullback K sX sY hX hY hdX hdY f hf hkm, prYPullback,
    flatPullbackChowOfRelativeDimension_mk]
  have hδ : schemeDeltaDimension (fieldChowSituation K) sY ≤ ((dY : ℤ) : EInt) := by
    have h := schemeDeltaDimension_le_of_forall_relativeDimension_le (fieldChowSituation K) sY
      (𝟙 Y) (k := (dY : ℤ)) fun y => relativeDimension_le_of_topologicalKrullDim_le
        (fieldChowSituation K) (fun _ _ => rfl) sY isClosed_univ
        (by rw [topologicalKrullDim_univ, hdY]) (Set.mem_univ y)
    simpa using h
  have hfund := flatPullback_fundamentalCycle (fieldChowSituation K) (pullback.fst sX sY ≫ sX) sY
    (pullback.snd sX sY) pullback.condition.symm dX
    (ExteriorProductProjections.relativeDimension_pullbackSnd sX sY dX hdX) (dY : ℤ) hδ
  rw [fundamentalCycle, fundamentalCycle] at hfund
  rw [hfund, chowMulFun_comm hdP (by push_cast; ring),
    chowMulFun_fundamentalClass_of_eq hdP (by push_cast; ring), graphClass]
  have hΓ : QuotientAddGroup.mk' _ (cycleAssociatedToClosedSubscheme (fieldChowSituation K)
      (pullback.fst sX sY ≫ sX) (graph f hf) (dX : ℤ)) =
      graphPush K sX sY f hf (dX : ℤ) (QuotientAddGroup.mk' _
        (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sX (𝟙 X) (dX : ℤ))) := by
    rw [graphPush, properChowPushforward_mk,
      properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp,
      cycleAssociatedToClosedSubscheme_of_hom_eq (fieldChowSituation K) _ (Category.id_comp _)]
  rw [hΓ, prXPush_graphPush]

/-- Proper pushforward `pr_{Y,*} : CH_d(X × Y) ⟶ CH_d(Y)`. -/
abbrev prYPush (d : ℤ) :
    chowGroup (fieldChowSituation K) (pullback.fst sX sY ≫ sX) d →+
      chowGroup (fieldChowSituation K) sY d :=
  properChowPushforward (fieldChowSituation K) (pullback.fst sX sY ≫ sX) sY (pullback.snd sX sY)
    pullback.condition.symm d (properPushforwardFactorsThroughRationalEquivalence_of_isProper
      (fieldChowSituation K) (pullback.fst sX sY ≫ sX) sY (pullback.snd sX sY)
      pullback.condition.symm d)

omit [IsAlgClosed K] in
/-- `pr_{Y,*} ∘ s_* = f_*` on Chow groups. -/
theorem prYPush_graphPush (d : ℤ) (z : chowGroup (fieldChowSituation K) sX d) :
    letI := isProper_of_comp_eq f hf
    prYPush K sX sY d (graphPush K sX sY f hf d z) =
      properChowPushforward (fieldChowSituation K) sX sY f hf d
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper (fieldChowSituation K) sX
          sY f hf d) z := by
  let := isProper_of_comp_eq f hf
  obtain ⟨ζ, rfl⟩ := QuotientAddGroup.mk'_surjective _ z
  simp only [properChowPushforward_mk]
  rw [properPushforward_snd_properPushforward_graph f hf d ζ]

include hdX hdY in
/-- **Stacks 0B2X, part (3): the projection formula** `f_*(a) · b = f_*(a · f^*b)`. With `s` the
graph, `s_*(a · f^*b) = s_*(a) · pr_Y^* b` on `X × Y` by the remark on graphs, and
`f_* = pr_{Y,*} ∘ s_*`, so this is the flat projection formula (Tag 0B10) for `pr_Y`. -/
@[stacks 0B2X "part (3): the projection formula `f_*(α) · β = f_*(α · f^*β)` on Chow groups, \
for `α ∈ CH_r(X)` and `β ∈ CH_k(Y)`, `f^*β ∈ CH_m(X)` with `k + dim X = dim Y + m`, and both \
products in `CH_n` with `r + m = dim X + n`", sga "7 XVII 5.2" "partial"]
theorem chowMulFun_properChowPushforward_eq {r k m n : ℤ} (hkm : k + dX = dY + m)
    (hn : r + m = dX + n) (a : chowGroup (fieldChowSituation K) sX r)
    (b : chowGroup (fieldChowSituation K) sY k) :
    letI := isProper_of_comp_eq f hf
    chowMulFun K sY hY n
        (properChowPushforward (fieldChowSituation K) sX sY f hf r
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper (fieldChowSituation K)
            sX sY f hf r) a) b =
      properChowPushforward (fieldChowSituation K) sX sY f hf n
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper (fieldChowSituation K)
          sX sY f hf n)
        (chowMulFun K sX hX n a (chowPullback K sX sY hX hY hdX hdY f hf hkm b)) := by
  let := isProper_of_comp_eq f hf
  have hP := isRegular_pullback_of_isRegular sX sY hX hY
  have hdP := topologicalKrullDim_pullback_eq K sX sY hdX hdY
  have hfst := topologicalKrullDim_pullback_eq_add_fst K sX sY hdY
  have hsnd := topologicalKrullDim_pullback_eq_add_snd K sX sY hdX
  set fb := chowPullback K sX sY hX hY hdX hdY f hf hkm b
  set G := graphClass K sX sY (dX := dX) f hf
  have hpX := prXPullback_eq K sX sY hdY
  have hpY := prYPullback_eq K sX sY hdX
  have hGX := chowMulFun_graphClass_prXPullback K sX sY hX hY hdX hdY f hf
  have hA : graphPush K sX sY f hf n (chowMulFun K sX hX n a fb) =
      chowMulFun K (pullback.fst sX sY ≫ sX) hP n (graphPush K sX sY f hf r a)
        (prYPullback K sX sY hdX k b) := by
    set PA := prXPullback K sX sY hdY r a
    set PB := prXPullback K sX sY hdY m fb
    set QB := prYPullback K sX sY hdX k b
    rw [← hGX, hpX, flatPullbackChow_chowMulFun K (pullback.fst sX sY ≫ sX) sX hP hX _ rfl dY hfst
      hdX hn a fb, ← hpX, ← hpX]
    have e1 := chowMulFun_assoc (hX := hP) hdP (m₁ := r) (m₂ := n + dY) (m := n)
      (by push_cast; omega) (by push_cast; omega) (by push_cast; omega) G PA PB
    have e2 := chowMulFun_comm (hX := hP) hdP (m := r) (by push_cast; omega) G PA
    have e3 := chowMulFun_assoc (hX := hP) hdP (m₁ := r) (m₂ := m) (m := n)
      (by push_cast; omega) (by push_cast; omega) (by push_cast; omega) PA G PB
    have e4 : chowMulFun K _ hP m G PB = chowMulFun K _ hP m G QB := by
      rw [hGX, graphPush_chowPullback K sX sY hX hY hdX hdY f hf hkm b]
    have e5 := chowMulFun_assoc (hX := hP) hdP (m₁ := r) (m₂ := m) (m := n)
      (by push_cast; omega) (by push_cast; omega) (by push_cast; omega) PA G QB
    rw [← e1, e2, e3, e4, ← e5, ← e2, hGX]
  rw [← prYPush_graphPush K sX sY f hf n, hA, ← prYPush_graphPush K sX sY f hf r, hpY]
  exact (properChowPushforward_chowMulFun K (pullback.fst sX sY ≫ sX) sY hP hY
    (pullback.snd sX sY) pullback.condition.symm dX hsnd hdY (r := r) (s := k) (n := n)
    (by omega) _ b).symm

end GraphChow

/-! ### The ring map `f^* : CH^*(Y) ⟶ CH^*(X)` -/

section RingMap

variable (K : Type u) [Field K] [IsAlgClosed K] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K))
  (sY : Y ⟶ Spec (.of K)) [IsProjectiveVariety K sX] [IsProjectiveVariety K sY]
  (hX : IsRegular X) (hY : IsRegular Y) {dX dY : ℕ}
  (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞))
  (hdY : topologicalKrullDim Y = (dY : WithBot ℕ∞)) (f : X ⟶ Y) (hf : f ≫ sY = sX)

/-- `f^*` on the graded piece `CH^c(Y) = CH_{dim Y - c}(Y)`, landing in
`CH^c(X) = CH_{dim X - c}(X)`. -/
abbrev chowPullbackGrade (c : ℕ) :
    ChowGrade K sY dY hY hdY c →+ ChowGrade K sX dX hX hdX c :=
  chowPullback K sX sY hX hY hdX hdY f hf (k := (dY : ℤ) - c) (m := (dX : ℤ) - c) (by ring)

/-- `f^* : CH^*(Y) ⟶ CH^*(X)` as a ring homomorphism, `f^*` on each graded piece. -/
def chowPullbackRingHom :
    ChowRing K sY hY dY hdY →+* ChowRing K sX hX dX hdX :=
  DirectSum.toSemiring
    (fun c => (DirectSum.of (ChowGrade K sX dX hX hdX) c).comp
      (chowPullbackGrade K sX sY hX hY hdX hdY f hf c))
    (by
      rw [AddMonoidHom.comp_apply, DirectSum.one_def]
      congr 1
      exact chowPullback_fundamentalClass K sX sY hX hY hdX hdY f hf (by simp) (by simp) _)
    (by
      intro i j ai aj
      rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
        DirectSum.of_mul_of]
      congr 1
      exact chowPullback_chowMulFun K sX sY hX hY hdX hdY f hf (by ring) (by ring) (by ring)
        (by push_cast; ring) ai aj)

/-- The ring map `chowPullbackRingHom` is `f^*` on each graded piece. -/
theorem chowPullbackRingHom_of (c : ℕ) (a : ChowGrade K sY dY hY hdY c) :
    chowPullbackRingHom K sX sY hX hY hdX hdY f hf (DirectSum.of _ c a) =
      DirectSum.of _ c (chowPullback K sX sY hX hY hdX hdY f hf (k := (dY : ℤ) - c)
        (m := (dX : ℤ) - c) (by ring) a) :=
  DirectSum.toSemiring_of _ _ _ c a

/-- **Stacks Project, Tag 0B2X, part (1).** Let `f : X ⟶ Y` be a morphism of nonsingular
projective varieties over an algebraically closed field (the chapter's convention, Tag 0AZ8).
Then the pullback `f^* : CH^*(Y) ⟶ CH^*(X)` of Section 43.23 (Tag 0B0H) is a ring map: there is
a ring homomorphism between the Chow rings of Section 43.21 (Tag 0B0G) which is `f^*` on every
graded piece `CH^c(Y) ⟶ CH^c(X)`. -/
@[stacks 0B2X "part (1): `f^* : CH^*(Y) → CH^*(X)` is a ring map, stated as the existence of a \
ring homomorphism between the Chow rings `⨁_c CH^c` which is `f^*` on each graded piece \
`CH^c(Y) = CH_{dim Y - c}(Y) → CH^c(X) = CH_{dim X - c}(X)`; the content is \
`chowPullback_chowMulFun` (`f^*(a · b) = f^*a · f^*b`) and `chowPullback_fundamentalClass` \
(`f^*[Y] = [X]`)"]
theorem chowPullback_isRingHom :
    ∃ φ : ChowRing K sY hY dY hdY →+* ChowRing K sX hX dX hdX,
      ∀ (c : ℕ) (a : ChowGrade K sY dY hY hdY c),
        φ (DirectSum.of _ c a) =
          DirectSum.of _ c (chowPullback K sX sY hX hY hdX hdY f hf (k := (dY : ℤ) - c)
            (m := (dX : ℤ) - c) (by ring) a) :=
  ⟨chowPullbackRingHom K sX sY hX hY hdX hdY f hf,
    chowPullbackRingHom_of K sX sY hX hY hdX hdY f hf⟩

end RingMap

end Stacks.Intersection.ChowRing

end
