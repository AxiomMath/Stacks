module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Examples.GroupSchemes.DoubleGlue

/-!
# The spectrum of `k⟦t⟧` with its closed point doubled

Let `k` be a field and `A = k⟦t⟧`. Gluing two copies of `Spec A` along the open subscheme
`D(t) = Spec A[1/t]`, which is the generic point, gives a scheme `X` with a morphism `X ⟶ Spec A`
restricting to the identity on each copy. Its fibre over the closed point consists of two
distinct points, the two copies of the closed point, while its generic fibre is a single point.

The structure morphism is flat, locally of finite type and quasi-compact, but not separated:
`D(t)` is not closed in `Spec A`. This is the scheme used for the counterexamples to
algebraization of coherent sheaves on non-separated schemes, Stacks 0ARF.

## Main definitions

* `Stacks.Examples.powerSeriesGenericLocus` — the open `D(t)` of `Spec k⟦t⟧`.
* `Stacks.Examples.doubledClosedPoint` — two copies of `Spec k⟦t⟧` glued along `D(t)`, as a
  section cover of `Spec k⟦t⟧`.

## Main results

* `Stacks.Examples.not_isClosed_powerSeriesGenericLocus`: `D(t)` is not closed.
* `Stacks.Examples.not_isSeparated_doubledClosedPoint_proj`: the structure morphism is not
  separated.
* `Stacks.Examples.doubledClosedPoint_chart_closedPoint_ne`: the two copies of the closed point
  are distinct points of `X`.

## References

* [Stacks Project, Tag 0ARF](https://stacks.math.columbia.edu/tag/0ARF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Examples

variable (k : Type u) [Field k]

/-- The open subscheme `D(t)` of `Spec k⟦t⟧`, consisting of the generic point. -/
public def powerSeriesGenericLocus : (Spec (.of (PowerSeries k))).Opens :=
  PrimeSpectrum.basicOpen (PowerSeries.X : PowerSeries k)

/-- The generic point of `Spec k⟦t⟧` lies in `D(t)`. -/
public theorem genericPoint_mem_powerSeriesGenericLocus :
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (PowerSeries k)) ∈ powerSeriesGenericLocus k := by
  change (PowerSeries.X : PowerSeries k) ∉ (⊥ : Ideal (PowerSeries k))
  exact PowerSeries.X_ne_zero

/-- The closed point of `Spec k⟦t⟧` does not lie in `D(t)`. -/
public theorem closedPoint_notMem_powerSeriesGenericLocus :
    IsLocalRing.closedPoint (PowerSeries k) ∉ powerSeriesGenericLocus k := by
  change ¬ (PowerSeries.X : PowerSeries k) ∉ IsLocalRing.maximalIdeal (PowerSeries k)
  rw [not_not, PowerSeries.maximalIdeal_eq_span_X]
  exact Ideal.subset_span rfl

/-- A point of `Spec k⟦t⟧` lies in `D(t)` exactly when it is not the closed point. -/
public theorem mem_powerSeriesGenericLocus_iff (p : PrimeSpectrum (PowerSeries k)) :
    p ∈ powerSeriesGenericLocus k ↔ p ≠ IsLocalRing.closedPoint (PowerSeries k) := by
  constructor
  · rintro hp rfl
    exact closedPoint_notMem_powerSeriesGenericLocus k hp
  · intro hp
    change (PowerSeries.X : PowerSeries k) ∉ p.asIdeal
    intro hX
    apply hp
    refine PrimeSpectrum.ext (le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) ?_)
    change IsLocalRing.maximalIdeal (PowerSeries k) ≤ p.asIdeal
    rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.span_le]
    rintro _ rfl
    exact hX

/-- `D(t)` is not closed in `Spec k⟦t⟧`: it contains the generic point, which specialises to the
closed point. -/
public theorem not_isClosed_powerSeriesGenericLocus :
    ¬ IsClosed (powerSeriesGenericLocus k : Set (Spec (.of (PowerSeries k)))) := fun hclosed =>
  closedPoint_notMem_powerSeriesGenericLocus k (hclosed.stableUnderSpecialization
    ((PrimeSpectrum.le_iff_specializes ⟨⊥, Ideal.isPrime_bot⟩ _).mp bot_le)
    (genericPoint_mem_powerSeriesGenericLocus k))

/-- Two copies of `Spec k⟦t⟧` glued along `D(t)`: the spectrum of `k⟦t⟧` with its closed point
doubled, with its two copies as the two sections of its structure morphism. -/
public abbrev doubledClosedPoint : SectionCoverData (Spec (.of (PowerSeries k))) :=
  doubleSectionCover _ (powerSeriesGenericLocus k)

attribute [local instance] SectionCoverData.isOpenImmersion_chart

/-- The structure morphism of the doubled closed point is flat. -/
public instance flat_doubledClosedPoint_proj : Flat (doubledClosedPoint k).proj :=
  (doubledClosedPoint k).proj_prop _
    (HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat)) inferInstance

/-- The structure morphism of the doubled closed point is locally of finite type. -/
public instance locallyOfFiniteType_doubledClosedPoint_proj :
    LocallyOfFiniteType (doubledClosedPoint k).proj :=
  (doubledClosedPoint k).proj_prop _
    (HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFiniteType)) inferInstance

/-- The structure morphism of the doubled closed point is quasi-compact. -/
public instance quasiCompact_doubledClosedPoint_proj :
    QuasiCompact (doubledClosedPoint k).proj := by
  have : CompactSpace (Spec (.of (PowerSeries k))) := PrimeSpectrum.compactSpace
  exact (doubledClosedPoint k).quasiCompact_proj

/-- The structure morphism of the doubled closed point is not separated. -/
public theorem not_isSeparated_doubledClosedPoint_proj :
    ¬ IsSeparated (doubledClosedPoint k).proj :=
  doubleSectionCover_not_isSeparated _ _ (not_isClosed_powerSeriesGenericLocus k)

/-- The two copies of a point of `D(t)` are the same point of the doubled closed point. -/
public theorem doubledClosedPoint_chart_true_apply_eq (v : (powerSeriesGenericLocus k).toScheme) :
    (doubledClosedPoint k).chart true ((powerSeriesGenericLocus k).ι v) =
      (doubledClosedPoint k).chart false ((powerSeriesGenericLocus k).ι v) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, doubleSectionCover_chart_agree]

/-- A point lying on both copies lies over `D(t)`. -/
public theorem mem_powerSeriesGenericLocus_of_chart_eq {b c : Bool} (hbc : b ≠ c)
    {y y' : Spec (.of (PowerSeries k))}
    (e : (doubledClosedPoint k).chart b y = (doubledClosedPoint k).chart c y') :
    y ∈ powerSeriesGenericLocus k := by
  have hp := doubleSectionCover_isPullback_chart _ (powerSeriesGenericLocus k) hbc
  have hx : (doubledClosedPoint k).chart b y ∈ Set.range
      (pullback.fst ((doubledClosedPoint k).chart b) ((doubledClosedPoint k).chart c) ≫
        (doubledClosedPoint k).chart b) := by
    rw [IsOpenImmersion.range_pullback_to_base_of_left]
    exact ⟨⟨y, rfl⟩, ⟨y', e.symm⟩⟩
  obtain ⟨q, hq⟩ := hx
  rw [← hp.isoPullback_inv_fst, Category.assoc, Scheme.Hom.comp_apply,
    Scheme.Hom.comp_apply] at hq
  have hy := ((doubledClosedPoint k).chart b).isOpenEmbedding.injective hq
  rw [← hy, ← SetLike.mem_coe, ← Scheme.Opens.range_ι]
  exact Set.mem_range_self _

/-- The two copies of the closed point of `Spec k⟦t⟧` are distinct points of the doubled closed
point. -/
public theorem doubledClosedPoint_chart_closedPoint_ne :
    (doubledClosedPoint k).chart true (IsLocalRing.closedPoint (PowerSeries k)) ≠
      (doubledClosedPoint k).chart false (IsLocalRing.closedPoint (PowerSeries k)) := fun e =>
  closedPoint_notMem_powerSeriesGenericLocus k
    (mem_powerSeriesGenericLocus_of_chart_eq k (by decide) e)

/-- Each copy of the generic point of `Spec k⟦t⟧` specialises to both copies of the closed
point: the closure of the image of either chart contains the closed point of the other. -/
public theorem doubledClosedPoint_chart_closedPoint_mem_closure (b c : Bool) :
    (doubledClosedPoint k).chart c (IsLocalRing.closedPoint (PowerSeries k)) ∈
      closure (Set.range ((doubledClosedPoint k).chart b)) := by
  let η : PrimeSpectrum (PowerSeries k) := ⟨⊥, Ideal.isPrime_bot⟩
  have hη : (doubledClosedPoint k).chart c η ∈ Set.range ((doubledClosedPoint k).chart b) := by
    refine ⟨η, ?_⟩
    have hv := doubledClosedPoint_chart_true_apply_eq k
      ⟨η, genericPoint_mem_powerSeriesGenericLocus k⟩
    simp only [Scheme.Opens.ι_apply] at hv
    cases b <;> cases c
    · rfl
    · exact hv.symm
    · exact hv
    · rfl
  have hspec : (doubledClosedPoint k).chart c η ⤳
      (doubledClosedPoint k).chart c (IsLocalRing.closedPoint (PowerSeries k)) :=
    ((PrimeSpectrum.le_iff_specializes η _).mp bot_le).map
      ((doubledClosedPoint k).chart c).continuous
  exact hspec.mem_closed isClosed_closure (subset_closure hη)

end Stacks.Examples

end
