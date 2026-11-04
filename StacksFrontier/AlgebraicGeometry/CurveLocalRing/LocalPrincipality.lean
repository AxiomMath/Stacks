module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalEquationMultiplicity
public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.ClosedPointDivisor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.OrderOfVanishingPointHom

/-!
# Local principality: the order of vanishing at a point with a discrete valuation stalk is onto

Let `x` be a point of codimension one of an integral locally Noetherian scheme `X` whose local
ring `𝒪_{X,x}` is a discrete valuation ring. The order of vanishing
`AlgebraicGeometry.Scheme.ord` at `x` attains every integer, and the rational function realising
a prescribed value can be chosen with no other zero or pole on a neighbourhood of `x`. A closed
point of a curve smooth over a field is such a point, so on a nonsingular curve every divisor is
locally the divisor of a function.

## Main results

* `AlgebraicGeometry.Scheme.exists_ord_eq_one_of_isDiscreteValuationRing`: a rational function
  with order of vanishing `1` at a codimension-one point with a discrete valuation stalk.
* `AlgebraicGeometry.Scheme.exists_ord_eq_of_isDiscreteValuationRing`: the order of vanishing
  there attains every integer.
* `AlgebraicGeometry.Scheme.exists_ord_eq_and_forall_ord_eq_zero_of_isDiscreteValuationRing`:
  a rational function with order of vanishing `n` at `x` and zero at every other point of an open
  neighbourhood of `x`.
* `AlgebraicGeometry.IsCurve.exists_ord_eq_one`,
  `AlgebraicGeometry.IsCurve.surjective_ordAddMonoidHom`,
  `AlgebraicGeometry.IsCurve.exists_ord_eq` and
  `AlgebraicGeometry.IsCurve.exists_ord_eq_and_forall_ord_eq_zero`: the same statements at a
  closed point of a smooth curve over a field.

## References

* [Stacks Project, Tag 0B8Y](https://stacks.math.columbia.edu/tag/0B8Y): the local ring at a
  closed point of a curve.
* [Stacks Project, Tag 03RI](https://stacks.math.columbia.edu/tag/03RI): the fundamental exact
  sequence.
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace Scheme

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- **A local parameter at a codimension-one point whose local ring is a discrete valuation ring:**
there is a nonzero rational function whose order of vanishing at the point is `1`. -/
theorem exists_ord_eq_one_of_isDiscreteValuationRing {x : X} (hco : coheight x = 1)
    (hdvr : IsDiscreteValuationRing (X.presheaf.stalk x)) :
    ∃ g : X.functionField, g ≠ 0 ∧ X.ord g x = 1 := by
  have := hdvr
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk x)
  obtain ⟨V, hxV, t, ht⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf π
  have hirr : Irreducible ((X.presheaf.germ V x hxV).hom t) := by rw [ht]; exact hπ
  have hne : t ≠ 0 := fun h => hirr.ne_zero (by rw [h]; simp)
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  refine ⟨X.germToFunctionField V t, fun h => hne ?_, Stacks.Chow.ord_eq_ringOrd_germ hco hxV t
    hne (n := 1) (by rw [Ring.ord_of_irreducible hirr]; rfl)⟩
  exact Scheme.germToFunctionField_injective X V (by simpa using h)

/-- The order of vanishing of the `n`-th power of a function of order `1` is `n`. -/
private theorem ordAddMonoidHom_zsmul_mk0 {x : X} {g : X.functionField} (hg0 : g ≠ 0)
    (hg : X.ord g x = 1) (n : ℤ) :
    Scheme.ordAddMonoidHom x (n • Additive.ofMul (Units.mk0 g hg0)) = n := by
  rw [map_zsmul, Scheme.ordAddMonoidHom_apply]
  change n • X.ord g x = n
  rw [hg, smul_eq_mul, mul_one]

/-- **The order of vanishing at a codimension-one point with a discrete valuation stalk attains
every integer.** -/
theorem exists_ord_eq_of_isDiscreteValuationRing {x : X} (hco : coheight x = 1)
    (hdvr : IsDiscreteValuationRing (X.presheaf.stalk x)) (n : ℤ) :
    ∃ g : X.functionField, g ≠ 0 ∧ X.ord g x = n := by
  obtain ⟨g, hg0, hg⟩ := exists_ord_eq_one_of_isDiscreteValuationRing hco hdvr
  refine ⟨(Additive.toMul (n • Additive.ofMul (Units.mk0 g hg0)) : (X.functionField)ˣ),
    Units.ne_zero _, ?_⟩
  rw [← Scheme.ordAddMonoidHom_apply x, ordAddMonoidHom_zsmul_mk0 hg0 hg]

/-- **A rational function with a prescribed divisor on a neighbourhood of a codimension-one point
with a discrete valuation stalk:** for every integer `n` there are an open neighbourhood `U` of `x`
and a nonzero rational function whose order of vanishing is `n` at `x` and zero at every other
point of `U`. -/
theorem exists_ord_eq_and_forall_ord_eq_zero_of_isDiscreteValuationRing [NoetherianSpace X]
    {x : X} (hco : coheight x = 1) (hdvr : IsDiscreteValuationRing (X.presheaf.stalk x))
    (n : ℤ) :
    ∃ (U : X.Opens) (g : X.functionField), x ∈ U ∧ g ≠ 0 ∧ X.ord g x = n ∧
      ∀ y ∈ U, y ≠ x → X.ord g y = 0 := by
  obtain ⟨g, hg0, hgx⟩ := exists_ord_eq_of_isDiscreteValuationRing hco hdvr n
  obtain ⟨U, hxU, hU⟩ := exists_opens_forall_ord_eq_zero hco g
  exact ⟨U, g, hxU, hg0, hgx, hU⟩

end Scheme

namespace IsCurve

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
  [IsLocallyNoetherian X]

/-- **A local parameter at a closed point of a smooth curve:** there is a nonzero rational function
on a curve smooth over a field whose order of vanishing at a given closed point is `1`. -/
theorem exists_ord_eq_one {x : X} (hx : IsClosed ({x} : Set X)) (hxg : x ≠ genericPoint X) :
    ∃ g : X.functionField, g ≠ 0 ∧ X.ord g x = 1 :=
  Scheme.exists_ord_eq_one_of_isDiscreteValuationRing (coheight_eq_one f hxg)
    (isDiscreteValuationRing_stalk_of_isClosed k f hx)

/-- **The order of vanishing at a closed point of a smooth curve attains every integer:**
`AlgebraicGeometry.Scheme.ordAddMonoidHom` at the point, on the units of the function field, is
surjective. -/
theorem surjective_ordAddMonoidHom {x : X} (hx : IsClosed ({x} : Set X))
    (hxg : x ≠ genericPoint X) :
    Function.Surjective (Scheme.ordAddMonoidHom (X := X) x) := by
  obtain ⟨g, hg0, hg⟩ := exists_ord_eq_one k f hx hxg
  exact fun n => ⟨n • Additive.ofMul (Units.mk0 g hg0),
    Scheme.ordAddMonoidHom_zsmul_mk0 hg0 hg n⟩

/-- **A nonzero rational function with a prescribed order of vanishing at a closed point of a
smooth curve.** -/
theorem exists_ord_eq {x : X} (hx : IsClosed ({x} : Set X)) (hxg : x ≠ genericPoint X) (n : ℤ) :
    ∃ g : X.functionField, g ≠ 0 ∧ X.ord g x = n :=
  Scheme.exists_ord_eq_of_isDiscreteValuationRing (coheight_eq_one f hxg)
    (isDiscreteValuationRing_stalk_of_isClosed k f hx) n

/-- **A rational function with a prescribed divisor on a neighbourhood of a closed point of a
smooth curve.** Given a closed point `x` of a smooth curve and an integer `n`, there is an open
neighbourhood `U` of `x` and a nonzero rational function whose order of vanishing is `n` at `x` and
zero at every other point of `U`. -/
theorem exists_ord_eq_and_forall_ord_eq_zero {x : X} (hx : IsClosed ({x} : Set X))
    (hxg : x ≠ genericPoint X) (n : ℤ) :
    ∃ (U : X.Opens) (g : X.functionField), x ∈ U ∧ g ≠ 0 ∧ X.ord g x = n ∧
      ∀ y ∈ U, y ≠ x → X.ord g y = 0 := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := IsNoetherian.mk
  exact Scheme.exists_ord_eq_and_forall_ord_eq_zero_of_isDiscreteValuationRing
    (coheight_eq_one f hxg) (isDiscreteValuationRing_stalk_of_isClosed k f hx) n

end IsCurve

end AlgebraicGeometry

end
