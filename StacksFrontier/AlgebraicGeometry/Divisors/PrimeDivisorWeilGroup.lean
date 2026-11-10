module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.Topology.LocallyFinite
public import StacksFrontier.AlgebraicGeometry.Scheme.Immersion.Basic
public import StacksFrontier.Topology.Dimension.Codimension
public import StacksFrontier.Topology.Dimension.SpecializingSurjection

/-!
# Prime divisors and Weil divisors

A prime divisor of a scheme `X` is an integral closed subscheme of codimension one. A Weil divisor
is a family of integers indexed by the prime divisors whose nonzero members form a locally finite
family of closed subsets of `X`; Weil divisors form an additive subgroup of all such families.

## Main definitions

* `PrimeDivisor`: an integral closed subscheme of codimension one.
* `PrimeDivisor.support`, `PrimeDivisor.genericPoint`: its underlying closed set and its generic
  point in the ambient scheme.
* `WeilDivisor`: the additive subgroup of Weil divisors.

## References

* [Stacks Project, Tag 0BE2](https://stacks.math.columbia.edu/tag/0BE2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry TopologicalSpace

universe u

namespace StacksDraft.AlgebraicGeometry.Divisors.PrimeDivisorWeilGroup

/-- An integral closed subscheme of codimension one. -/
public structure PrimeDivisor (X : Scheme.{u}) where
  idealSheaf : X.IdealSheafData
  integral : IsIntegral idealSheaf.subscheme
  codimension_one :
    letI := integral
    codimension (IrreducibleCloseds.closureSingleton
      (idealSheaf.subschemeι (_root_.genericPoint idealSheaf.subscheme))) = 1

/-- The underlying closed set of a prime divisor. -/
public abbrev PrimeDivisor.support {X : Scheme.{u}} (Z : PrimeDivisor X) : Set X :=
  Z.idealSheaf.support

/-- The generic point of a prime divisor, viewed in the ambient scheme. -/
public def PrimeDivisor.genericPoint {X : Scheme.{u}} (Z : PrimeDivisor X) : X :=
  letI := Z.integral
  Z.idealSheaf.subschemeι (_root_.genericPoint Z.idealSheaf.subscheme)

/-- Weil divisors: integral coefficient families whose nonzero prime divisors
form a locally finite collection in the ambient scheme. -/
public def WeilDivisor (X : Scheme.{u}) : AddSubgroup (PrimeDivisor X → ℤ) where
  carrier := {D | LocallyFinite (fun Z : PrimeDivisor X =>
    if D Z = 0 then ∅ else Z.support)}
  zero_mem' x := ⟨Set.univ, Filter.univ_mem, by simp⟩
  add_mem' := by
    intro D E hD hE x
    obtain ⟨U, hU, hUD⟩ := hD x
    obtain ⟨V, hV, hVE⟩ := hE x
    refine ⟨U ∩ V, Filter.inter_mem hU hV, ?_⟩
    apply (hUD.union hVE).subset
    intro Z hZ
    simp only [Set.mem_ofPred_eq] at hZ ⊢
    have hDE : D Z + E Z ≠ 0 := fun he ↦ by simp [he] at hZ
    simp only [Pi.add_apply, ite_eq_right hDE] at hZ
    obtain ⟨p, hpS, hpUV⟩ := hZ
    by_cases hDZ : D Z = 0
    · have hEZ : E Z ≠ 0 := fun he ↦ hDE (by simp [hDZ, he])
      exact .inr ⟨p, by simpa [hEZ] using hpS, hpUV.2⟩
    · exact .inl ⟨p, by simpa [hDZ] using hpS, hpUV.1⟩
  neg_mem' {D} hD := by simpa only [Set.mem_ofPred_eq, Pi.neg_apply, neg_eq_zero] using hD

/-- A coefficient family is a Weil divisor exactly when its nonzero prime
divisors form a locally finite family of underlying closed subsets. -/
@[simp]
public theorem mem_weilDivisor_iff {X : Scheme.{u}} (D : PrimeDivisor X → ℤ) :
    D ∈ WeilDivisor X ↔
      LocallyFinite (fun Z : PrimeDivisor X => if D Z = 0 then ∅ else Z.support) :=
  Iff.rfl

end StacksDraft.AlgebraicGeometry.Divisors.PrimeDivisorWeilGroup
