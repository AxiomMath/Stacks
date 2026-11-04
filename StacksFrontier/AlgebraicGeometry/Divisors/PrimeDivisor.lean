module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.Topology.LocallyFinite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Dimension.Codimension
public import StacksFrontier.Topology.Dimension.SpecializingSurjection

/-!
# Prime divisors and Weil divisors

A *prime divisor* of a scheme `X` is an integral closed subscheme of codimension one. A *Weil
divisor* is an integral formal sum of prime divisors whose support is locally finite.

A closed subscheme is presented by an ideal sheaf, through `AlgebraicGeometry.Scheme.IdealSheafData`
and its canonical closed immersion `AlgebraicGeometry.Scheme.IdealSheafData.subschemeι`; the
codimension of the subscheme is the codimension in `X` of the closure of the image of its generic
point, which exists because the subscheme is integral. The local finiteness condition is imposed on
the underlying closed subsets of the prime divisors rather than only on their generic points, so it
constrains the family at every point of `X`.

The definitions require nothing of `X` beyond being a scheme, although they are used for locally
Noetherian integral schemes. A Weil divisor is an additive subgroup of the integer-valued
coefficient families, whose group structure is coefficientwise.

## Main definitions

* `AlgebraicGeometry.PrimeDivisor`: an integral closed subscheme of codimension one.
* `AlgebraicGeometry.PrimeDivisor.support`: its underlying closed subset of `X`.
* `AlgebraicGeometry.PrimeDivisor.genericPoint`: its generic point, viewed in `X`.
* `AlgebraicGeometry.WeilDivisor`: the additive group of locally finite integral coefficient
  families indexed by the prime divisors.

## Main results

* `AlgebraicGeometry.PrimeDivisor.codimension_closureSingleton_genericPoint`: the closure of the
  generic point of a prime divisor has codimension one in `X`.
* `AlgebraicGeometry.mem_weilDivisor_iff`: membership of `WeilDivisor X` is local finiteness of
  the supports of the prime divisors with nonzero coefficient.

## References

* [Stacks Project, Tag 0BE2](https://stacks.math.columbia.edu/tag/0BE2)
-/

@[expose] public noncomputable section

open TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A prime divisor of a scheme is an integral closed subscheme of codimension one, presented by
its ideal sheaf. The codimension is that of the closure in the ambient scheme of the image of the
generic point of the subscheme. -/
@[stacks 0BE2 "part (1): prime divisors"]
structure PrimeDivisor (X : Scheme.{u}) where
  /-- The ideal sheaf cutting out the closed subscheme. -/
  idealSheaf : X.IdealSheafData
  /-- The closed subscheme is integral. -/
  integral : IsIntegral idealSheaf.subscheme
  /-- The closure of the image of the generic point has codimension one in the ambient scheme. -/
  codimension_one :
    letI := integral
    codimension (IrreducibleCloseds.closureSingleton
      (idealSheaf.subschemeι (_root_.genericPoint idealSheaf.subscheme))) = 1

/-- The underlying closed subset of a prime divisor, namely the support of its ideal sheaf. -/
abbrev PrimeDivisor.support {X : Scheme.{u}} (Z : PrimeDivisor X) : Set X :=
  Z.idealSheaf.support

/-- The generic point of a prime divisor, viewed as a point of the ambient scheme. -/
def PrimeDivisor.genericPoint {X : Scheme.{u}} (Z : PrimeDivisor X) : X :=
  letI := Z.integral
  Z.idealSheaf.subschemeι (_root_.genericPoint Z.idealSheaf.subscheme)

/-- The closure of the generic point of a prime divisor has codimension one, which is the
defining condition of a prime divisor read at
`AlgebraicGeometry.PrimeDivisor.genericPoint`. -/
theorem PrimeDivisor.codimension_closureSingleton_genericPoint {X : Scheme.{u}}
    (Z : PrimeDivisor X) :
    codimension (IrreducibleCloseds.closureSingleton Z.genericPoint) = 1 :=
  Z.codimension_one

/-- The Weil divisors of a scheme: the integral coefficient families indexed by prime divisors
whose prime divisors with nonzero coefficient have locally finite supports. The additive group
structure is the coefficientwise one. -/
@[stacks 0BE2 "part (2): Weil divisors"]
def WeilDivisor (X : Scheme.{u}) : AddSubgroup (PrimeDivisor X → ℤ) where
  carrier := {D | LocallyFinite (fun Z : PrimeDivisor X =>
    if D Z = 0 then ∅ else Z.support)}
  zero_mem' := by
    intro x
    refine ⟨Set.univ, Filter.univ_mem, ?_⟩
    simp
  add_mem' := by
    intro D E hD hE x
    obtain ⟨U, hU, hUD⟩ := hD x
    obtain ⟨V, hV, hVE⟩ := hE x
    refine ⟨U ∩ V, Filter.inter_mem hU hV, ?_⟩
    apply (hUD.union hVE).subset
    intro Z hZ
    simp only [Set.mem_ofPred_eq] at hZ ⊢
    have hDE : D Z + E Z ≠ 0 := by
      intro he
      simp [Pi.add_apply, he] at hZ
    simp only [Pi.add_apply, ite_eq_right hDE] at hZ
    obtain ⟨p, hpS, hpUV⟩ := hZ
    by_cases hDZ : D Z = 0
    · right
      have hEZ : E Z ≠ 0 := by
        intro he
        apply hDE
        simp [hDZ, he]
      exact ⟨p, by simpa [hEZ] using hpS, hpUV.2⟩
    · left
      exact ⟨p, by simpa [hDZ] using hpS, hpUV.1⟩
  neg_mem' := by
    intro D hD
    change LocallyFinite (fun Z : PrimeDivisor X =>
      if D Z = 0 then ∅ else Z.support) at hD
    change LocallyFinite (fun Z : PrimeDivisor X =>
      if (-D) Z = 0 then ∅ else Z.support)
    simpa only [Pi.neg_apply, neg_eq_zero] using hD

/-- A coefficient family is a Weil divisor exactly when the supports of the prime divisors with
nonzero coefficient form a locally finite family. -/
@[simp]
theorem mem_weilDivisor_iff {X : Scheme.{u}} (D : PrimeDivisor X → ℤ) :
    D ∈ WeilDivisor X ↔
      LocallyFinite (fun Z : PrimeDivisor X => if D Z = 0 then ∅ else Z.support) :=
  Iff.rfl

end AlgebraicGeometry

end
