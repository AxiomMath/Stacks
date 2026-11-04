module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.Topology.LocallyFinite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.Topology.Dimension.Codimension
public import StacksFrontier.Topology.Dimension.SpecializingSurjection

/-!
# Prime divisors are the points of coheight one

Let `X` be a scheme. A prime divisor of `X` is an integral closed subscheme of codimension one
(`Stacks.Divisors.PrimeDivisor`, Stacks 0BE2), while Mathlib, and with it
`AlgebraicGeometry.AlgebraicCycle`, indexes an integral closed subscheme by the generic point of
its support instead. This file is the dictionary between the two presentations in codimension
one: a prime divisor is determined by its generic point
(`Stacks.Divisors.PrimeDivisor.genericPoint_injective`), that point has coheight one
(`Stacks.Divisors.PrimeDivisor.coheight_genericPoint`), and conversely every point of coheight
one is the generic point of a prime divisor
(`Stacks.Divisors.PrimeDivisor.ofCoheightOne`). Together these give the equivalence
`Stacks.Divisors.PrimeDivisor.equivCoheightOne` between prime divisors and points of coheight
one, which is what lets a Weil divisor be read as an algebraic cycle.

## Main definitions

* `Stacks.Divisors.PrimeDivisor` — an integral closed subscheme of codimension one.
* `Stacks.Divisors.PrimeDivisor.genericPoint` — its generic point, viewed in `X`.
* `Stacks.Divisors.PrimeDivisor.ofCoheightOne` — the prime divisor attached to a point of
  coheight one.
* `Stacks.Divisors.PrimeDivisor.equivCoheightOne` — prime divisors are the points of
  coheight one.
* `Stacks.Divisors.WeilDivisor` — the group of Weil divisors, as an `AddSubgroup`.

## Main results

* `Stacks.Divisors.mem_weilDivisor_iff` — membership in `Div(X)` is local finiteness.
* `Stacks.Divisors.PrimeDivisor.support_eq_closure` — the support of a prime divisor is the
  closure of its generic point.
* `Stacks.Divisors.PrimeDivisor.genericPoint_injective` — a prime divisor is determined by its
  generic point.
* `Stacks.Divisors.PrimeDivisor.coheight_genericPoint` — the generic point of a prime divisor has
  coheight one.

## Implementation notes

THE LIBRARY HAS A SECOND PRIME-DIVISOR DEVELOPMENT, and a reader of this file should know it:
`AlgebraicGeometry.PrimeDivisor` and `AlgebraicGeometry.WeilDivisor` of
`StacksFrontier.AlgebraicGeometry.Divisors.PrimeDivisor` (:57 and :89) carry the same two clause
strings of Stacks 0BE2 and the same three fields, differing only in spelling the generic point
`idealSheaf.subschemeι (genericPoint idealSheaf.subscheme)` where this file writes
`Stacks.Chow.genericPointOf`, which is that term. A third, untagged copy is
`StacksDraft.AlgebraicGeometry.Divisors.PrimeDivisorWeilGroup` (:23 and :42). The three are one
notion; this one has 14 consumer files against 8 and 1, and six results the others lack
(`support_eq_closure`, `genericPoint_injective`, `coheight_genericPoint`,
`genericPoint_eq_genericPointOf`, `ofCoheightOne` with `genericPoint_ofCoheightOne`, and
`equivCoheightOne`), so it is the one onto which the other two should be merged.

The passage to points reuses `Stacks.Chow.integralComponentAt` and
`Stacks.Chow.genericPointOf`, the inverse bijection between integral closed subschemes and
points established in `StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent`;
nothing about that bijection is re-derived here. The generic point of a prime divisor is the
generic point of its underlying integral closed subscheme in that sense, by definition
(`Stacks.Divisors.PrimeDivisor.genericPoint_eq_genericPointOf`), which is what makes the
bijection applicable. Only the codimension condition is new, and it transports along the order
isomorphism `TopologicalSpace.irreducibleSetEquivPoints` between irreducible closed subsets of a
sober space and its points.

## References

* [Stacks Project, Tag 0BE2](https://stacks.math.columbia.edu/tag/0BE2)
* [Stacks Project, Tag 02RO](https://stacks.math.columbia.edu/tag/02RO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace

universe u

namespace Stacks.Divisors

/-- **Stacks 0BE2 (1).** A prime divisor of `X` is an integral closed subscheme of codimension
one, recorded by its ideal sheaf. -/
@[stacks 0BE2 "part (1): prime divisors"]
structure PrimeDivisor (X : Scheme.{u}) where
  /-- The ideal sheaf cutting out the closed subscheme. -/
  idealSheaf : X.IdealSheafData
  /-- The closed subscheme is integral. -/
  integral : IsIntegral idealSheaf.subscheme
  /-- The closed subscheme has codimension one in `X`. -/
  codimension_one :
    letI := integral
    codimension (IrreducibleCloseds.closureSingleton
      (Stacks.Chow.genericPointOf idealSheaf integral)) = 1

namespace PrimeDivisor

variable {X : Scheme.{u}}

/-- The underlying closed set of a prime divisor. -/
abbrev support (Z : PrimeDivisor X) : Set X := Z.idealSheaf.support

/-- The generic point of a prime divisor, viewed as a point of the ambient scheme. -/
def genericPoint (Z : PrimeDivisor X) : X :=
  Stacks.Chow.genericPointOf Z.idealSheaf Z.integral

/-- The generic point of a prime divisor is the generic point of the integral closed subscheme
cut out by its ideal sheaf, in the sense of `Stacks.Chow.genericPointOf`. -/
theorem genericPoint_eq_genericPointOf (Z : PrimeDivisor X) :
    Z.genericPoint = Stacks.Chow.genericPointOf Z.idealSheaf Z.integral :=
  rfl

/-- The support of a prime divisor is the closure of its generic point. -/
theorem support_eq_closure (Z : PrimeDivisor X) :
    Z.support = closure ({Z.genericPoint} : Set X) :=
  Stacks.Chow.support_eq_closure_genericPointOf Z.idealSheaf Z.integral

/-- A prime divisor is determined by its generic point: the closed subscheme is the reduced
induced structure on the closure of that point, and the two remaining fields are propositions. -/
theorem genericPoint_injective : Function.Injective (genericPoint (X := X)) := by
  intro Z W h
  have hI : Z.idealSheaf = W.idealSheaf := by
    rw [← Stacks.Chow.integralComponentAt_genericPointOf Z.idealSheaf Z.integral,
      ← Stacks.Chow.integralComponentAt_genericPointOf W.idealSheaf W.integral]
    exact congrArg Stacks.Chow.integralComponentAt h
  cases Z with | mk IZ hIZ hcodZ =>
  cases W with | mk IW hIW hcodW =>
  cases hI
  rfl

/-- The codimension of an irreducible closed subset of a scheme is the coheight of its generic
point: the sober-space order isomorphism between irreducible closed subsets and points carries
one to the other. -/
theorem codimension_closureSingleton (x : X) :
    codimension (IrreducibleCloseds.closureSingleton x) = coheight x := by
  have hEq : (irreducibleSetEquivPoints (α := X)).symm x =
      IrreducibleCloseds.closureSingleton x :=
    IrreducibleCloseds.ext rfl
  rw [codimension_eq_coheight, ← hEq,
    coheight_orderIso (irreducibleSetEquivPoints (α := X)).symm]

/-- The generic point of a prime divisor has coheight one. -/
theorem coheight_genericPoint (Z : PrimeDivisor X) : coheight Z.genericPoint = 1 := by
  rw [← codimension_closureSingleton]
  exact Z.codimension_one

/-- The prime divisor attached to a point of coheight one: the reduced induced structure on the
closure of that point, which has codimension one exactly because the point has coheight one. -/
def ofCoheightOne (x : X) (hx : coheight x = 1) : PrimeDivisor X where
  idealSheaf := Stacks.Chow.integralComponentAt x
  integral := Stacks.Chow.isIntegral_integralComponentAt x
  codimension_one := by
    rw [Stacks.Chow.genericPointOf_integralComponentAt x, codimension_closureSingleton]
    exact hx

@[simp]
theorem genericPoint_ofCoheightOne (x : X) (hx : coheight x = 1) :
    (ofCoheightOne x hx).genericPoint = x :=
  Stacks.Chow.genericPointOf_integralComponentAt x

/-- **Prime divisors are the points of coheight one.** The two presentations of a prime divisor
— as an integral closed subscheme of codimension one, and as a point of the ambient scheme of
coheight one — carry the same information. -/
def equivCoheightOne : PrimeDivisor X ≃ {x : X // coheight x = 1} where
  toFun Z := ⟨Z.genericPoint, Z.coheight_genericPoint⟩
  invFun x := ofCoheightOne x.1 x.2
  left_inv _Z := genericPoint_injective (genericPoint_ofCoheightOne _ _)
  right_inv x := Subtype.ext (genericPoint_ofCoheightOne x.1 x.2)

end PrimeDivisor

/-! ### Weil divisors -/

/-- **Stacks 0BE2 (2).** The group `Div(X)` of Weil divisors: integer-valued coefficient
families indexed by the prime divisors of `X` whose nonzero prime divisors form a locally finite
collection of closed subsets of `X`. -/
@[stacks 0BE2 "part (2): Weil divisors"]
def WeilDivisor (X : Scheme.{u}) : AddSubgroup (PrimeDivisor X → ℤ) where
  carrier := {D | LocallyFinite fun Z : PrimeDivisor X => if D Z = 0 then ∅ else Z.support}
  zero_mem' := by
    intro x
    exact ⟨Set.univ, Filter.univ_mem, by simp⟩
  add_mem' := by
    intro D E hD hE x
    obtain ⟨U, hU, hUD⟩ := hD x
    obtain ⟨V, hV, hVE⟩ := hE x
    refine ⟨U ∩ V, Filter.inter_mem hU hV, (hUD.union hVE).subset fun Z hZ => ?_⟩
    simp only [Set.mem_ofPred_eq] at hZ ⊢
    have hDE : D Z + E Z ≠ 0 := fun he => by simp [Pi.add_apply, he] at hZ
    simp only [Pi.add_apply, ite_eq_right hDE] at hZ
    obtain ⟨p, hpS, hpUV⟩ := hZ
    by_cases hDZ : D Z = 0
    · have hEZ : E Z ≠ 0 := fun he => hDE (by simp [hDZ, he])
      exact Or.inr ⟨p, by simpa [hEZ] using hpS, hpUV.2⟩
    · exact Or.inl ⟨p, by simpa [hDZ] using hpS, hpUV.1⟩
  neg_mem' := by
    intro D hD
    change LocallyFinite fun Z : PrimeDivisor X => if D Z = 0 then ∅ else Z.support at hD
    change LocallyFinite fun Z : PrimeDivisor X => if (-D) Z = 0 then ∅ else Z.support
    simpa only [Pi.neg_apply, neg_eq_zero] using hD

/-- A coefficient family is a Weil divisor exactly when its nonzero prime divisors form a
locally finite family of closed subsets of `X`. -/
@[simp]
theorem mem_weilDivisor_iff {X : Scheme.{u}} (D : PrimeDivisor X → ℤ) :
    D ∈ WeilDivisor X ↔
      LocallyFinite fun Z : PrimeDivisor X => if D Z = 0 then ∅ else Z.support :=
  Iff.rfl

end Stacks.Divisors

end
