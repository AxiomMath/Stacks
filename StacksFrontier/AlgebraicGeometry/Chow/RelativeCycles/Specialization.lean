module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward.ComponentRule
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.ComponentRules
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalenceDefs
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.FibreMap
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Fibre
public import StacksCore.Tactic.StacksAttribute

/-!
# Specialization of cycles

Let `R` be a discrete valuation ring with fraction field `K` and residue field `κ`, let `X` be a
scheme locally of finite type over `R` and let `r ≥ 0`. The *specialization map*

  `sp_{X/R} : Z_r(X_K) ⟶ Z_r(X_κ)`

is the unique additive map sending the fundamental cycle of an integral closed subscheme
`Z ⊆ X_K` of dimension `r` to `[Z̄_κ]_r`, where `Z̄ ⊆ X` is the scheme-theoretic image of
`Z ⟶ X`. This file builds that map; that it commutes with proper pushforward, which is
Stacks 0H4M, is proved in
`StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecializationProperPushforward`.

The two fibres `X_K` and `X_κ` are the scheme-theoretic fibres of `X ⟶ Spec R` at the generic
and the closed point of `Spec R`, and `Z_r` of a fibre is the group of `r`-cycles for the Chow
situation on the spectrum of the residue field of that point, which is
`Stacks.Chow.FiberCycleGroup`. The construction and the theorem are carried out for an arbitrary
base scheme `S` and an arbitrary pair of points of `S`, of which the discrete-valuation-ring
situation is the instance named in the source.

## Main definitions

* `Stacks.Chow.inverseImageCycle` — the `k`-cycle `[i^{-1}(Z)]_k` of the scheme-theoretic
  inverse image along `i : W ⟶ X` of the integral closed subscheme `Z = closure {x}` of `X`.
* `Stacks.Chow.inverseImageCycleMap` — the additive map taking a cycle on `X` to the
  `k`-cycle on `W` obtained by replacing each component by the inverse image of its closure.
* `Stacks.Chow.ofFiberCycle` — a cycle on a scheme-theoretic fibre, read as a cycle on the
  ambient scheme.
* `Stacks.Chow.fiberSpecializationMap` — specialization of `r`-cycles from the fibre over one
  point of the base to the fibre over another.
* `Stacks.Chow.specializationMap` — **Stacks 0H4H**: the specialization map `sp_{X/R}` of a
  scheme locally of finite type over a discrete valuation ring.

## Main results

* `Stacks.Chow.fiberSpecializationMap_single` — the characterizing property: the
  specialization of the fundamental cycle of the integral closed subscheme `closure {x}` of the
  fibre over `η` is the `r`-cycle of the inverse image, in the fibre over `s`, of the reduced
  closure of the image of `x` in `X`.

## Implementation notes

### The scheme-theoretic image is the reduced closure of the generic point

For an integral closed subscheme `Z ⊆ X_K` the source identifies the scheme-theoretic image of
`Z ⟶ X` with "the unique integral closed subscheme whose generic point is the image of the
generic point of `Z`", using that `X_K ⟶ X` is quasi-compact and that taking scheme-theoretic
images commutes with flat base change (Stacks 081I, which is
`AlgebraicGeometry.ker_pullback_snd_eq_comap` in this repository). That description is
the one used here: `Stacks.Chow.inverseImageCycle` is built from the vanishing ideal sheaf of
`closure {x}`, which is exactly the reduced induced structure on the closure of a point.

### The map is a locally finite sum, and goes through the ambient scheme

A cycle on `X_K` is only *locally* finite, so `sp_{X/R}` cannot be defined on a basis. It is
defined, as the source's proof reads it, by first viewing a cycle on `X_K` as a cycle on `X`
(`Stacks.Chow.ofFiberCycle`, legitimate because `X_K ⟶ X` is quasi-compact, so the pushforward
of a locally finite family stays locally finite) and then applying the coefficientwise rule
`Z ↦ [Z_κ]_r` on the integral closed subschemes of `X`. The second step is
`Stacks.Chow.ComponentRule.extend`, the mechanism by which every coefficientwise construction of
chapter 42 is extended over a locally finite sum.

### The truncation at dimension `r` is harmless, and that is Stacks 0B2J

The `r`-cycle `[W]_r` of a closed subscheme records only the components of delta-dimension `r`,
so the definition above would silently drop a component of `Z̄_κ` of the wrong dimension. No
component is dropped: `Z̄` is integral and dominates `R`, so `Z̄_κ` is equidimensional of
dimension `r` by Stacks 0B2J, which is
`AlgebraicGeometry.specialFiber_equidimensional` in this repository. That equidimensionality is
therefore needed for the *faithfulness* of the construction rather than for its
well-definedness:
`Stacks.Chow.inverseImageCycleMap` lands in `Z_r` with no hypothesis at all, since the coefficient
function of `[W]_r` vanishes off the points of delta-dimension `r` by construction.

## References

* [Stacks Project, Tag 0H4H](https://stacks.math.columbia.edu/tag/0H4H)
* [Stacks Project, Tag 081I](https://stacks.math.columbia.edu/tag/081I)
* [Stacks Project, Tag 0B2J](https://stacks.math.columbia.edu/tag/0B2J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The cycle of an inverse image -/

section InverseImage

variable (C : ChowSituation.{u}) {W X : Scheme.{u}} (sW : W ⟶ C.S) [LocallyOfFiniteType sW]
  (i : W ⟶ X) (k : ℤ)

/-- The `k`-cycle on `W` of the scheme-theoretic inverse image along `i : W ⟶ X` of the integral
closed subscheme `closure {x}` of `X`, the latter being presented by its vanishing ideal
sheaf. -/
def inverseImageCycle (x : X) : CycleGroup C sW k :=
  cycleAssociatedToClosedSubscheme C sW
    ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).comap i).subschemeι k

/-- A point with a nonzero coefficient in `Stacks.Chow.inverseImageCycle` is the image of a generic
point of the inverse image and has relative dimension `k`. -/
private theorem exists_of_inverseImageCycle_ne_zero (x : X) (w : W)
    (h : (inverseImageCycle C sW i k x).1 w ≠ 0) :
    ∃ ξ : genericPoints ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).comap i).subscheme,
      ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).comap i).subschemeι ξ.1 = w ∧
        relativeDimension C.dimensionFunction sW w = k := by
  classical
  have h' : closedSubschemeCycleCoeff C sW
      ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).comap i).subschemeι k w ≠ 0 := h
  unfold closedSubschemeCycleCoeff at h'
  split_ifs at h' with hex
  · exact hex
  · exact (h' rfl).elim

/-- A point of `W` with a nonzero coefficient in `Stacks.Chow.inverseImageCycle` at `x` lies
over the closure of `x`: the cycle is supported on the inverse image of that closure. -/
theorem mem_closure_of_inverseImageCycle_ne_zero (x : X) (w : W)
    (h : (inverseImageCycle C sW i k x).1 w ≠ 0) : i.base w ∈ closure ({x} : Set X) := by
  obtain ⟨ξ, hξ, -⟩ := exists_of_inverseImageCycle_ne_zero C sW i k x w h
  have hw : w ∈ Set.range
      ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).comap i).subschemeι.base := ⟨ξ.1, hξ⟩
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap] at hw
  have hmem : i.base w ∈ (Closeds.closure ({x} : Set X) : Set X) := by
    simpa [Scheme.IdealSheafData.coe_support_vanishingIdeal] using hw
  simpa using hmem

/-- A point of `W` with a nonzero coefficient in `Stacks.Chow.inverseImageCycle` has relative
dimension `k`: the coefficient function of the cycle of a closed subscheme vanishes off the
points of delta-dimension `k`. -/
theorem relativeDimension_of_inverseImageCycle_ne_zero (x : X) (w : W)
    (h : (inverseImageCycle C sW i k x).1 w ≠ 0) :
    relativeDimension C.dimensionFunction sW w = k :=
  (exists_of_inverseImageCycle_ne_zero C sW i k x w h).choose_spec.2

/-- The rule on the integral closed subschemes of `X` attaching to `closure {x}` the `k`-cycle
of its scheme-theoretic inverse image in `W`. -/
def inverseImageComponentRule : ComponentRule i.base where
  cycle x := (inverseImageCycle C sW i k x).1
  mem_closure_of_apply_ne_zero := mem_closure_of_inverseImageCycle_ne_zero C sW i k

/-- Restriction of cycles along `i : W ⟶ X`: a cycle on `X` is sent to the `k`-cycle on `W`
obtained by replacing each integral component by the `k`-cycle of its inverse image, weighted by
its coefficient. -/
def inverseImageCycleMap : AlgebraicCycle X ℤ →+ CycleGroup C sW k where
  toFun α := ⟨(inverseImageComponentRule C sW i k).extend i.continuous α, by
    rw [mem_cyclesOfDimension_iff_forall_point]
    intro w hw
    obtain ⟨x, hx⟩ := Set.mem_iUnion.1
      ((inverseImageComponentRule C sW i k).support_extend_subset i.continuous α (by exact hw))
    exact relativeDimension_of_inverseImageCycle_ne_zero C sW i k x w (by exact hx)⟩
  map_zero' := Subtype.ext <| map_zero ((inverseImageComponentRule C sW i k).extend i.continuous)
  map_add' α β :=
    Subtype.ext <| map_add ((inverseImageComponentRule C sW i k).extend i.continuous) α β

/-- The coefficient of a restricted cycle is the locally finite sum, over the components of the
original cycle, of the coefficients of the cycles of their inverse images. -/
theorem inverseImageCycleMap_apply (α : AlgebraicCycle X ℤ) (w : W) :
    (inverseImageCycleMap C sW i k α).1 w =
      ∑ᶠ x : X, α x * (inverseImageCycle C sW i k x).1 w := rfl

end InverseImage

/-! ### Cycles on a fibre, read on the ambient scheme -/

section OfFiber

variable {S X : Scheme.{u}} (sX : X ⟶ S) (s : S)

/-- The preimage under the inclusion of a fibre of the image of a point is that point. -/
private theorem preimage_fiberι_singleton (x : sX.fiber s) :
    (sX.fiberι s).base ⁻¹' {(sX.fiberι s).base x} = {x} := by
  ext y
  simp [(sX.fiberι s).isEmbedding.injective.eq_iff]

/-- A cycle on the scheme-theoretic fibre of `sX` over `s`, read as a cycle on `X`: the
coefficient at a point of the fibre is carried over unchanged, and every other coefficient is
zero. -/
def ofFiberCycle (α : AlgebraicCycle (sX.fiber s) ℤ) : AlgebraicCycle X ℤ :=
  Function.locallyFinsupp.map (sX.fiberι s).base (fun _ ↦ 1) (sX.fiberι s).isSpectralMap α

/-- At the image of a point of the fibre, a cycle read on the ambient scheme has the same
coefficient as the original cycle on the fibre. -/
@[simp]
theorem ofFiberCycle_apply_fiberι (α : AlgebraicCycle (sX.fiber s) ℤ) (x : sX.fiber s) :
    ofFiberCycle sX s α ((sX.fiberι s).base x) = α x := by
  rw [ofFiberCycle, Function.locallyFinsupp.map_apply, preimage_fiberι_singleton,
    finsum_mem_singleton, mul_one]

/-- Off the fibre, a cycle read on the ambient scheme has coefficient zero. -/
theorem ofFiberCycle_apply_of_notMem_range (α : AlgebraicCycle (sX.fiber s) ℤ) (y : X)
    (hy : y ∉ Set.range (sX.fiberι s).base) : ofFiberCycle sX s α y = 0 := by
  rw [ofFiberCycle, Function.locallyFinsupp.map_apply, Set.preimage_singleton_eq_empty.2 hy,
    finsum_mem_empty]

/-- The zero cycle on a fibre is read as the zero cycle on the ambient scheme. -/
@[simp]
theorem ofFiberCycle_zero : ofFiberCycle sX s 0 = 0 := by
  ext y
  by_cases hy : y ∈ Set.range (sX.fiberι s).base
  · obtain ⟨x, rfl⟩ := hy
    simp
  · simp [ofFiberCycle_apply_of_notMem_range sX s 0 y hy]

/-- Reading a cycle on a fibre as a cycle on the ambient scheme is additive. -/
theorem ofFiberCycle_add (α β : AlgebraicCycle (sX.fiber s) ℤ) :
    ofFiberCycle sX s (α + β) = ofFiberCycle sX s α + ofFiberCycle sX s β := by
  ext y
  by_cases hy : y ∈ Set.range (sX.fiberι s).base
  · obtain ⟨x, rfl⟩ := hy
    simp
  · simp [ofFiberCycle_apply_of_notMem_range sX s _ y hy]

/-- The prime cycle of a point of the fibre is read as the prime cycle of its image. -/
theorem ofFiberCycle_single [DecidableEq X] [DecidableEq (sX.fiber s)]
    (x : sX.fiber s) (n : ℤ) :
    ofFiberCycle sX s (Function.locallyFinsuppWithin.single x n) =
      Function.locallyFinsuppWithin.single ((sX.fiberι s).base x) n := by
  ext y
  by_cases hy : y ∈ Set.range (sX.fiberι s).base
  · obtain ⟨z, rfl⟩ := hy
    rw [ofFiberCycle_apply_fiberι]
    simp only [Function.locallyFinsuppWithin.single_apply,
      (sX.fiberι s).isEmbedding.injective.eq_iff]
  · rw [ofFiberCycle_apply_of_notMem_range sX s _ y hy,
      Function.locallyFinsuppWithin.single_apply]
    exact (ite_eq_right_iff.2 fun h ↦ absurd ⟨x, h.symm⟩ hy).symm

/-- A locally finite sum over `X` whose terms are weighted by a cycle read off a fibre is the
corresponding sum over that fibre: the weights vanish off the fibre, and the inclusion of the
fibre is injective. -/
theorem finsum_ofFiberCycle_mul (α : AlgebraicCycle (sX.fiber s) ℤ) (h : X → ℤ)
    (hfin : (Function.support fun x ↦ α x * h ((sX.fiberι s).base x)).Finite) :
    (∑ᶠ y : X, ofFiberCycle sX s α y * h y) =
      ∑ᶠ x : sX.fiber s, α x * h ((sX.fiberι s).base x) := by
  rw [← finsum_finsum_mem_fiber (sX.fiberι s).base _ hfin]
  refine finsum_congr fun y ↦ ?_
  by_cases hy : y ∈ Set.range (sX.fiberι s).base
  · obtain ⟨x, rfl⟩ := hy
    rw [ofFiberCycle_apply_fiberι, preimage_fiberι_singleton, finsum_mem_singleton]
  · rw [ofFiberCycle_apply_of_notMem_range sX s α y hy, zero_mul,
      Set.preimage_singleton_eq_empty.2 hy, finsum_mem_empty]

end OfFiber

/-! ### The specialization map -/

section Specialization

variable {S X : Scheme.{u}} (sX : X ⟶ S) [LocallyOfFiniteType sX] (η s : S) (r : ℕ)

/-- Specialization of `r`-cycles from the fibre of `sX` over `η` to the fibre over `s`: a cycle
is read as a cycle on `X` and then each of its integral components is replaced by the `r`-cycle
of the inverse image of its closure in the fibre over `s`. -/
def fiberSpecializationMap : FiberCycleGroup sX η r →+ FiberCycleGroup sX s r where
  toFun α := inverseImageCycleMap (fieldChowSituation (S.residueField s))
    (sX.fiberToSpecResidueField s) (sX.fiberι s) (r : ℤ) (ofFiberCycle sX η α.1)
  map_zero' := by
    change inverseImageCycleMap _ _ _ _ (ofFiberCycle sX η (0 : AlgebraicCycle (sX.fiber η) ℤ)) = 0
    rw [ofFiberCycle_zero, map_zero]
  map_add' α β := by
    change inverseImageCycleMap _ _ _ _ (ofFiberCycle sX η (α.1 + β.1)) = _
    rw [ofFiberCycle_add, map_add]

/-- The coefficientwise formula for the specialization map: at a point of the fibre over `s` the
coefficient is the locally finite sum, over the integral closed subschemes of `X`, of the
coefficient of the cycle read on `X` times the coefficient of the cycle of the inverse image of
that subscheme in the fibre over `s`. -/
theorem fiberSpecializationMap_apply (α : FiberCycleGroup sX η r) (z : sX.fiber s) :
    (fiberSpecializationMap sX η s r α).1 z =
      ∑ᶠ y : X, ofFiberCycle sX η α.1 y *
        (inverseImageCycle (fieldChowSituation (S.residueField s))
          (sX.fiberToSpecResidueField s) (sX.fiberι s) (r : ℤ) y).1 z := rfl

/-- **The characterizing property.** The specialization of the fundamental cycle of the integral
closed subscheme `closure {x}` of the fibre over `η` is the `r`-cycle of the inverse image, in
the fibre over `s`, of the reduced closure of the image of `x` in `X`. -/
theorem fiberSpecializationMap_single [DecidableEq (sX.fiber η)]
    (x : sX.fiber η) (α : FiberCycleGroup sX η r)
    (hα : α.1 = Function.locallyFinsuppWithin.single x 1) :
    fiberSpecializationMap sX η s r α =
      inverseImageCycle (fieldChowSituation (S.residueField s))
        (sX.fiberToSpecResidueField s) (sX.fiberι s) (r : ℤ) ((sX.fiberι η).base x) := by
  classical
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro z
  have hdef : (fiberSpecializationMap sX η s r α).1 z =
      ((inverseImageComponentRule (fieldChowSituation (S.residueField s))
        (sX.fiberToSpecResidueField s) (sX.fiberι s) (r : ℤ)).extend
          (sX.fiberι s).continuous (ofFiberCycle sX η α.1)) z := rfl
  rw [hdef, hα, ofFiberCycle_single, ComponentRule.extend_apply_single]
  simp [inverseImageComponentRule]

end Specialization

/-! ### The specialization map of a scheme over a discrete valuation ring -/

/-- **Stacks 0H4H.** The specialization map `sp_{X/R} : Z_r(X_K) ⟶ Z_r(X_κ)` of a scheme locally
of finite type over a discrete valuation ring `R`, from the cycles on the generic fibre to the
cycles on the closed fibre. The generic fibre is the scheme-theoretic fibre over the generic
point of `Spec R`, whose residue field is the fraction field `K`, and the closed fibre is the
one over the closed point, whose residue field is `κ`. -/
@[stacks 0H4H "the specialization map sp_{X/R}"]
def specializationMap (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of R)) [LocallyOfFiniteType sX] (r : ℕ) :
    FiberCycleGroup sX (genericPoint (Spec (.of R))) r →+
      FiberCycleGroup sX (IsLocalRing.closedPoint R) r :=
  fiberSpecializationMap sX _ _ r

end Stacks.Chow

end
