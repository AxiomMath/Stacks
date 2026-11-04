module

public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.Support
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Effective
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecialFibreDimension
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecializationCycle
public import StacksFrontier.AlgebraicGeometry.Chow.Setup.CycleSupport
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The support of the specialization of a cycle over a discrete valuation ring

Let `R` be a discrete valuation ring with fraction field `K` and residue field `κ`, let
`f : X ⟶ Spec R` be locally of finite type and let `r ≥ 0`. The specialization map
`sp_{X/R} : Z_r(X_K) ⟶ Z_r(X_κ)` of Section 0H4H sends a cycle `c` on the generic fibre to a
cycle on the special fibre, and this file locates the support of `sp_{X/R}(c)` inside `X`.

Both inclusions hold. The support of `sp_{X/R}(c)` is never larger than it should be: every
point of it lies, in `X`, in the closure of the image of the support of `c`, because the only
integral closed subschemes of the generic fibre contributing to a coefficient of `sp_{X/R}(c)`
at a point `x` are those whose generic point has `x` in its closure. Conversely, when `c` is
effective no cancellation can occur, so the support of `sp_{X/R}(c)` is exactly as large as the
closure of the image of the support of `c` allows: it contains every point of the special fibre
which is a specialization, in `X`, of a point carrying a nonzero coefficient of `c`.

## Main results

* `Stacks.Chow.fiberι_mem_closure_image_support_of_mem_tsupport_specializationCycle` — the
  support of `sp_{X/R}(c)` maps into the closure in `X` of the image of the support of `c`.
* `Stacks.Chow.mem_tsupport_specializationCycle_of_specializes` — for effective `c`, the support
  of `sp_{X/R}(c)` contains every point of `X_κ` whose image in `X` is a specialization of the
  image of a point carrying a nonzero coefficient of `c`.

## Implementation notes

The second result is the geometric half of the pair, and rests on the dimension statement
`Stacks.Chow.fiberPointDimension_specializationSpecialFibre`: if the integral closed subscheme
`Z ⊆ X_K` of dimension `r` with generic point `ξ` has `x ∈ X_κ` in the closure of the image of
`ξ`, then *every* generic point of the special fibre `\overline{Z}_κ` of the scheme-theoretic
image of `Z` again has dimension `r`.

Every coefficient of `sp_{X/R}(c)` is a locally finite sum of products `c(ξ) · m` with `m` a
multiplicity, and multiplicities are positive at generic points, so for effective `c` the sum
of nonnegative terms is positive as soon as one term is.

## References

* [Stacks Project, Tag 0H5W](https://stacks.math.columbia.edu/tag/0H5W)
* [Stacks Project, Section 0H4H](https://stacks.math.columbia.edu/tag/0H4H)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Sums of integers -/

/-- A summable family of integers whose sum is nonzero has a nonzero term. -/
private theorem exists_ne_zero_of_hasSum_ne_zero {ι : Type*} {a : ℤ} {b : ι → ℤ}
    (hb : HasSum b a) (ha : a ≠ 0) : ∃ i, b i ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  refine ha (hb.unique ?_)
  rw [funext h]
  exact hasSum_zero

/-- A summable family of nonnegative integers with one positive term has positive sum. -/
private theorem hasSum_pos_of_nonneg_of_term_pos {ι : Type*} {a : ℤ} {b : ι → ℤ}
    (hb : HasSum b a) (hnonneg : ∀ i, 0 ≤ b i) (i : ι) (hi : 0 < b i) : 0 < a := by
  have hle := sum_le_hasSum ({i} : Finset ι) (fun j _ ↦ hnonneg j) hb
  rw [Finset.sum_singleton] at hle
  exact hi.trans_le hle

/-! ### The support of a cycle -/

/-- A point lies in the support of a cycle exactly when some point carrying a nonzero
coefficient specializes to it: the support is the union of the integral closed subschemes
occurring in the cycle, and the integral closed subscheme attached to a point consists of its
specializations. -/
@[ega "IV 21.6.1" "more general"]
private theorem mem_tsupport_iff_exists_specializes {Y : Type u} [TopologicalSpace Y]
    {c : Y → ℤ} (hc : LocallyFiniteSupport c) (x : Y) :
    x ∈ tsupport c ↔ ∃ y, c y ≠ 0 ∧ y ⤳ x := by
  rw [tsupport_eq_biUnion_closure_singleton hc, Set.biUnion_eq_iUnion, Set.mem_iUnion]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y.1, Function.mem_support.mp y.2, specializes_iff_mem_closure.mpr hy⟩
  · rintro ⟨y, hy, hyx⟩
    exact ⟨⟨y, Function.mem_support.mpr hy⟩, specializes_iff_mem_closure.mp hyx⟩

/-! ### Positivity of the coefficients of the cycle of a closed subscheme -/

/-- The multiplicity of an irreducible component of a closed subscheme of a locally Noetherian
scheme is positive: it is the length of a nonzero module of finite length. -/
private theorem componentMultiplicity_pos {Y W : Scheme.{u}} [IsLocallyNoetherian Y]
    [IsLocallyNoetherian W] (i : W ⟶ Y) [IsClosedImmersion i] (ζ : genericPoints W) :
    0 < componentMultiplicity i ζ :=
  (componentMultiplicity_nonneg i ζ).lt_of_ne' (componentMultiplicity_ne_zero i ζ)

/-- At the image of a generic point of a closed subscheme `W ⊆ Y` of relative dimension `k`,
the cycle `[W]_k` has a positive coefficient. -/
private theorem cycleAssociatedToClosedSubscheme_apply_pos (C : ChowSituation.{u})
    {Y W : Scheme.{u}} (p : Y ⟶ C.S) [LocallyOfFiniteType p] (i : W ⟶ Y) [IsClosedImmersion i]
    (k : ℤ) (ζ : genericPoints W)
    (hζ : relativeDimension C.dimensionFunction p (i ζ.1) = k) :
    0 < (cycleAssociatedToClosedSubscheme C p i k).1 (i ζ.1) := by
  let _ : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  let _ : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (i ≫ p)
  rw [cycleAssociatedToClosedSubscheme_apply C p i k ζ hζ]
  exact componentMultiplicity_pos i ζ

/-- If every generic point of a closed subscheme `W ⊆ Y` has relative dimension `k`, then the
whole of `W` lies in the support of the cycle `[W]_k`: the generic points do, because their
coefficients are positive, and they are dense in `W`. -/
private theorem range_subset_tsupport_cycleAssociatedToClosedSubscheme (C : ChowSituation.{u})
    {Y W : Scheme.{u}} (p : Y ⟶ C.S) [LocallyOfFiniteType p] (i : W ⟶ Y) [IsClosedImmersion i]
    (k : ℤ)
    (hdim : ∀ ζ : genericPoints W, relativeDimension C.dimensionFunction p (i ζ.1) = k) :
    Set.range i.base ⊆ tsupport (cycleAssociatedToClosedSubscheme C p i k).1 := by
  have hsub : genericPoints W ⊆
      i.base ⁻¹' tsupport (cycleAssociatedToClosedSubscheme C p i k).1 := by
    intro z hz
    exact subset_closure
      (cycleAssociatedToClosedSubscheme_apply_pos C p i k ⟨z, hz⟩ (hdim ⟨z, hz⟩)).ne'
  have hclosed : IsClosed (i.base ⁻¹' tsupport (cycleAssociatedToClosedSubscheme C p i k).1) :=
    (isClosed_tsupport _).preimage i.continuous
  rintro y ⟨z, rfl⟩
  have hz : z ∈ closure (genericPoints W) := by
    rw [genericPoints.closure]
    trivial
  exact closure_minimal hsub hclosed hz

/-! ### Cycles on a scheme-theoretic fibre -/

/-- The coefficients of the cycle `[W]_k` of a closed subscheme of a scheme-theoretic fibre are
nonnegative, being multiplicities. -/
private theorem fiberSubschemeCycle_apply_nonneg {Y S : Scheme.{u}} (p : Y ⟶ S)
    [LocallyOfFiniteType p] (s : S) (k : ℕ) (W : (p.fiber s).IdealSheafData) (y : p.fiber s) :
    0 ≤ (fiberSubschemeCycle p s k W).1 y :=
  closedSubschemeCycleCoeff_nonneg (fieldChowSituation (S.residueField s))
    (p.fiberToSpecResidueField s) W.subschemeι (k : ℤ) y

/-- If every generic point of a closed subscheme `W` of a scheme-theoretic fibre has dimension
`k`, then the whole of `W` lies in the support of the cycle `[W]_k`. -/
private theorem range_subset_tsupport_fiberSubschemeCycle {Y S : Scheme.{u}} (p : Y ⟶ S)
    [LocallyOfFiniteType p] (s : S) (k : ℕ) (W : (p.fiber s).IdealSheafData)
    (hdim : ∀ ζ : genericPoints W.subscheme,
      fiberPointDimension p s (W.subschemeι ζ.1) = (k : ℤ)) :
    Set.range W.subschemeι.base ⊆ tsupport (fiberSubschemeCycle p s k W).1 :=
  range_subset_tsupport_cycleAssociatedToClosedSubscheme (fieldChowSituation (S.residueField s))
    (p.fiberToSpecResidueField s) W.subschemeι (k : ℤ) hdim

/-- A point carrying a nonzero coefficient of a `k`-cycle on a scheme-theoretic fibre has
dimension `k`. -/
private theorem fiberPointDimension_eq_of_apply_ne_zero {Y S : Scheme.{u}} (p : Y ⟶ S)
    [LocallyOfFiniteType p] (s : S) (k : ℕ) (c : FiberCycleGroup p s k) (y : p.fiber s)
    (hy : c.1 y ≠ 0) : fiberPointDimension p s y = (k : ℤ) :=
  (mem_cyclesOfDimension_iff_forall_point (fieldChowSituation (S.residueField s))
    (p.fiberToSpecResidueField s) (k : ℤ) c.1).mp c.2 y hy

/-! ### The specialization map -/

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] (r : ℕ)

/-! ### The support of the specialization of a cycle -/

/-- The coefficients of `[\overline{Z}_κ]_r` are nonnegative, being multiplicities. -/
private theorem specializationIntegralCycle_apply_nonneg
    (ξ : f.fiber (genericPoint (Spec (.of R))))
    (x : f.fiber (IsLocalRing.closedPoint R)) :
    0 ≤ (specializationIntegralCycle f r ξ).1 x :=
  fiberSubschemeCycle_apply_nonneg f (IsLocalRing.closedPoint R) r
    (specializationSpecialFibre f ξ) x

/-- A point of the special fibre at which `[\overline{Z}_κ]_r` has a nonzero coefficient is, in
the total space, a specialization of the image of the generic point of `Z`. -/
private theorem specializes_of_specializationIntegralCycle_apply_ne_zero
    (ξ : f.fiber (genericPoint (Spec (.of R))))
    (x : f.fiber (IsLocalRing.closedPoint R))
    (hx : (specializationIntegralCycle f r ξ).1 x ≠ 0) :
    f.fiberι (genericPoint (Spec (.of R))) ξ ⤳ f.fiberι (IsLocalRing.closedPoint R) x := by
  by_contra h
  exact hx (specializationIntegralCycle_apply_eq_zero_of_not_specializes f r ξ x h)

/-- A nonzero coefficient of `sp_{X/R}(c)` receives a nonzero contribution from some integral
closed subscheme of the generic fibre of dimension `r` occurring in `c`. -/
private theorem exists_ne_zero_specializationTerm
    (c : FiberCycleGroup f (genericPoint (Spec (.of R))) r)
    (x : f.fiber (IsLocalRing.closedPoint R)) (hx : (specializationCycle f r c).1 x ≠ 0) :
    ∃ ξ : {ξ : f.fiber (genericPoint (Spec (.of R))) //
        fiberPointDimension f (genericPoint (Spec (.of R))) ξ = (r : ℤ)},
      c.1 ξ.1 ≠ 0 ∧ (specializationIntegralCycle f r ξ.1).1 x ≠ 0 := by
  obtain ⟨ξ, hξ⟩ := exists_ne_zero_of_hasSum_ne_zero (hasSum_specializationCycle f r c x) hx
  rw [specializationCycle_integralGenericCycle f r ξ.1 ξ.2] at hξ
  exact ⟨ξ, (mul_ne_zero_iff.mp hξ).1, (mul_ne_zero_iff.mp hξ).2⟩

/-- Over a discrete valuation ring base, every point of the support of the specialization of a
cycle on the generic fibre lies, in the total space, in the closure of the image of the support
of that cycle.

Indeed a point `x` of the support of `sp_{X/R}(c)` is a specialization of a point `y` with
`sp_{X/R}(c)(y) ≠ 0`, that coefficient is a sum of contributions of the integral closed
subschemes `Z_ξ` of the generic fibre occurring in `c`, and a nonzero contribution of `Z_ξ`
forces `y`, hence `x`, to lie in the closure of the image of `ξ`. -/
theorem fiberι_mem_closure_image_support_of_mem_tsupport_specializationCycle
    (c : FiberCycleGroup f (genericPoint (Spec (.of R))) r)
    {x : f.fiber (IsLocalRing.closedPoint R)}
    (hx : x ∈ tsupport ((specializationCycle f r c).1 :
      f.fiber (IsLocalRing.closedPoint R) → ℤ)) :
    f.fiberι (IsLocalRing.closedPoint R) x ∈
      closure (f.fiberι (genericPoint (Spec (.of R))) '' Function.support c.1) := by
  obtain ⟨y, hy, hyx⟩ := (mem_tsupport_iff_exists_specializes
    (specializationCycle f r c).1.locallyFiniteSupport x).mp hx
  obtain ⟨ξ, hξc, hξy⟩ := exists_ne_zero_specializationTerm f r c y hy
  have hspec : f.fiberι (genericPoint (Spec (.of R))) ξ.1 ⤳
      f.fiberι (IsLocalRing.closedPoint R) x :=
    (specializes_of_specializationIntegralCycle_apply_ne_zero f r ξ.1 y hξy).trans
      ((f.fiberι (IsLocalRing.closedPoint R)).continuous.specialization_monotone hyx)
  refine closure_mono ?_ (specializes_iff_mem_closure.mp hspec)
  rintro z hz
  rw [Set.mem_singleton_iff] at hz
  subst hz
  exact ⟨ξ.1, Function.mem_support.mpr hξc, rfl⟩

/-- Over a discrete valuation ring base, the support of the specialization of an *effective*
cycle on the generic fibre contains every point of the special fibre whose image in the total
space is a specialization of the image of a point carrying a nonzero coefficient.

Let `ξ` be such a point and `Z ⊆ X_K` the integral closed subscheme it generates; since `c` is
a cycle of dimension `r`, `Z` has dimension `r`. The point `x` lies in the special fibre
`\overline{Z}_κ` of the scheme-theoretic image of `Z`, each of whose generic points again has
dimension `r`, so the coefficient of `[\overline{Z}_κ]_r` is nonzero at some point `y`
specializing to `x`. As `c` is effective, every contribution to `sp_{X/R}(c)(y)` is nonnegative
and the one coming from `Z` is positive, so `sp_{X/R}(c)(y) > 0` and `x` lies in the closure of
`y`. -/
theorem mem_tsupport_specializationCycle_of_specializes
    (c : FiberCycleGroup f (genericPoint (Spec (.of R))) r) (hc : ∀ ξ, 0 ≤ c.1 ξ)
    {ξ : f.fiber (genericPoint (Spec (.of R)))} (hξ : c.1 ξ ≠ 0)
    (x : f.fiber (IsLocalRing.closedPoint R))
    (hspec : f.fiberι (genericPoint (Spec (.of R))) ξ ⤳
      f.fiberι (IsLocalRing.closedPoint R) x) :
    x ∈ tsupport ((specializationCycle f r c).1 :
      f.fiber (IsLocalRing.closedPoint R) → ℤ) := by
  have hdim : fiberPointDimension f (genericPoint (Spec (.of R))) ξ = (r : ℤ) :=
    fiberPointDimension_eq_of_apply_ne_zero f (genericPoint (Spec (.of R))) r c ξ hξ
  have hxint : x ∈ tsupport ((specializationIntegralCycle f r ξ).1 :
      f.fiber (IsLocalRing.closedPoint R) → ℤ) :=
    range_subset_tsupport_fiberSubschemeCycle f (IsLocalRing.closedPoint R) r
      (specializationSpecialFibre f ξ)
      (fiberPointDimension_specializationSpecialFibre f r ξ hdim x hspec)
      (by
        rw [Scheme.IdealSheafData.range_subschemeι, specializationSpecialFibre,
          Scheme.IdealSheafData.support_comap, Closeds.coe_preimage,
          coe_support_specializationClosure]
        exact specializes_iff_mem_closure.mp hspec)
  obtain ⟨y, hy, hyx⟩ := (mem_tsupport_iff_exists_specializes
    (specializationIntegralCycle f r ξ).1.locallyFiniteSupport x).mp hxint
  have hterm : 0 < (specializationCycle f r (integralGenericCycle f r ξ)).1 y := by
    rw [specializationCycle_integralGenericCycle f r ξ hdim]
    exact (specializationIntegralCycle_apply_nonneg f r ξ y).lt_of_ne' hy
  have hcy : 0 < (specializationCycle f r c).1 y :=
    hasSum_pos_of_nonneg_of_term_pos (hasSum_specializationCycle f r c y)
      (fun ζ ↦ by
        rw [specializationCycle_integralGenericCycle f r ζ.1 ζ.2]
        exact mul_nonneg (hc ζ.1) (specializationIntegralCycle_apply_nonneg f r ζ.1 y))
      ⟨ξ, hdim⟩ (mul_pos ((hc ξ).lt_of_ne' hξ) hterm)
  exact (mem_tsupport_iff_exists_specializes
    (specializationCycle f r c).1.locallyFiniteSupport x).mpr ⟨y, hcy.ne', hyx⟩

end Stacks.Chow

end
