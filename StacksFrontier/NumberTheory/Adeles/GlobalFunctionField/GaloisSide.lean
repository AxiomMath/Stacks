module

public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.SmoothUpperBound
public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.ValuationCenter
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDivisorMiddleExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafFrobenius
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.FundamentalGroupTheorem
public import StacksFrontier.NumberTheory.Adeles.SwitchingEll

/-!
# The Galois side of the Drinfeld correspondence for `GL₂`

Let `k` be a finite field and `X` a smooth projective geometrically irreducible curve over `k`
with function field `K = k(X)`. This file sets up the Galois-side objects of Stacks Theorems
03VT and 03VU: the closed point of `X` at which a place `v` of `K` is centred, the geometric
Frobenius elements `F_v ∈ π₁(X)` at `v`, and the compatibility of a representation
`ρ : π₁(X) → GL₂(E)` with a system `(t_v, u_v)` of Hecke eigenvalues,
`t_v = Tr ρ(F_v)` and `u_v = q_v⁻¹ det ρ(F_v)`.

## Main definitions

* `Stacks.Adeles.GlobalFunctionField.IsCentreOf` — the point `x` of `X` is the centre of the
  place `v`: the image of `𝒪_{X,x}` in `K` is the valuation ring of `v`.
* `Stacks.Adeles.GlobalFunctionField.IsGeometricFrobeniusAt` — `F ∈ π₁(X, x̄)` is a geometric
  Frobenius element at `v`: the inverse of a Frobenius element
  (`AlgebraicGeometry.FrobeniusData.element`, the arithmetic Frobenius `a ↦ a ^ #κ(x)` of the
  residue field transported to the base point) at the centre of `v`.
* `Stacks.Adeles.GlobalFunctionField.IsFrobeniusCompatible` — `t_v = Tr ρ(F_v)` and
  `u_v = q_v⁻¹ det ρ(F_v)` for every place `v` and every geometric Frobenius element `F_v` at
  `v`.

## Main results

* `Stacks.Adeles.GlobalFunctionField.exists_isCentreOf` and
  `Stacks.Adeles.GlobalFunctionField.eq_of_isCentreOf` — every place of `K` is centred at exactly
  one closed point of `X`; this is the identification "a place `v` of `K` is the same thing as a
  closed point `x ∈ X`" of the source.
* `Stacks.Adeles.GlobalFunctionField.exists_isGeometricFrobeniusAt` — every place carries a
  geometric Frobenius element, so the compatibility condition is never vacuous at a place.
* `Stacks.Adeles.GlobalFunctionField.IsGeometricFrobeniusAt.isConj` — the geometric Frobenius
  elements at a place form one conjugacy class.
* `Stacks.Adeles.GlobalFunctionField.isFrobeniusCompatible_of_forall_exists` — compatibility may
  be checked at one geometric Frobenius element per place.

## Implementation notes

The source writes `F_v` for a Frobenius element at `v`, defined up to conjugation. The trace and
determinant are conjugation invariant, so `IsFrobeniusCompatible` quantifies over all of them.
The Frobenius elements are geometric, the convention of the source's trace formula
`Tr(ρ(F_x)) = Tr(π_x^* | ℱ_ρ)` (see `Stacks.EtaleCohomology.geometricFrobeniusFamily`).

## References

* [Stacks Project, Tag 03VT](https://stacks.math.columbia.edu/tag/03VT)
* [Stacks Project, Tag 03VU](https://stacks.math.columbia.edu/tag/03VU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order

universe u

namespace Stacks.Adeles.GlobalFunctionField

section Defs

variable {X : Scheme.{u}} [IsIntegral X]

/-- The point `x` of an integral scheme `X` is the *centre* of the place `v` of its function
field `K`: the image of the local ring `𝒪_{X,x}` in `K` is the valuation ring of `v`. -/
public def IsCentreOf (v : Place X.functionField) (x : X) : Prop :=
  ∀ g : X.functionField, g ∈ v.1 ↔ ∃ a : X.presheaf.stalk x, algebraMap _ X.functionField a = g

variable [ConnectedSpace X]

/-- `F ∈ π₁(X, x̄)` is a *geometric Frobenius element at the place `v`*: at the closed point `x`
which is the centre of `v`, whose residue field `κ(x)` is finite, `F` is the inverse of the
arithmetic Frobenius `a ↦ a ^ #κ(x)` of `Gal(κ(x)^alg / κ(x)) = π₁(Spec κ(x))`, pushed into
`π₁(X)` at the geometric point over `x` and transported to the base point along some path `t`
(`Stacks.EtaleCohomology.frobeniusDataOfPath`). As `t` varies these elements form one
conjugacy class (`Stacks.Adeles.GlobalFunctionField.IsGeometricFrobeniusAt.isConj`). -/
public def IsGeometricFrobeniusAt (base : GeometricPoint X) (v : Place X.functionField)
    (F : EtaleFundamentalGroup X base) : Prop :=
  ∃ x : closedPoints X, IsCentreOf v x.1 ∧ ∃ (_ : Finite (X.residueField x.1))
    (t : finiteEtaleFiberFunctor (Stacks.Frobenius.geometricPointAt X x.1) ≅
      finiteEtaleFiberFunctor base),
      (Stacks.EtaleCohomology.frobeniusDataOfPath base x t).element⁻¹ = F

/-- A geometric Frobenius element at `v` is the inverse of a Frobenius element at the centre of
`v`, in the sense of `AlgebraicGeometry.frobeniusElements`. -/
public theorem IsGeometricFrobeniusAt.inv_mem_frobeniusElements {base : GeometricPoint X}
    {v : Place X.functionField} {F : EtaleFundamentalGroup X base}
    (hF : IsGeometricFrobeniusAt base v F) :
    ∃ x : closedPoints X, IsCentreOf v x.1 ∧ F⁻¹ ∈ frobeniusElements base {x} := by
  obtain ⟨x, hx, _, t, rfl⟩ := hF
  exact ⟨x, hx, x, Set.mem_singleton x, _, (inv_inv _).symm⟩

/-- The representation `ρ : π₁(X, x̄) → GL₂(E)`, read in `Ω` along `j : E → Ω`, is *compatible*
with the eigenvalues `t_v`, `u_v`: for every place `v` and every geometric Frobenius element
`F_v` at `v`, `t_v = Tr ρ(F_v)` and `u_v = q_v⁻¹ det ρ(F_v)`, where `q_v = #κ_v`. -/
public def IsFrobeniusCompatible (base : GeometricPoint X) {E : Type*} {Ω : Type*} [Field E]
    [Field Ω] (ρ : EtaleFundamentalGroup X base →* GL (Fin 2) E) (j : E →+* Ω)
    (t u : Place X.functionField → Ω) : Prop :=
  ∀ (v : Place X.functionField) (F : EtaleFundamentalGroup X base),
    IsGeometricFrobeniusAt base v F →
      t v = j (Matrix.trace (ρ F : Matrix (Fin 2) (Fin 2) E)) ∧
        u v = (Place.residueCard v : Ω)⁻¹ * j (Matrix.det (ρ F : Matrix (Fin 2) (Fin 2) E))

end Defs

/-- Trace and determinant of `ρ` agree at conjugate elements. -/
public theorem trace_det_eq_of_isConj {G : Type*} [Group G] {E : Type*} [Field E]
    (ρ : G →* GL (Fin 2) E) {g g' : G} (h : IsConj g g') :
    Matrix.trace (ρ g : Matrix (Fin 2) (Fin 2) E) =
        Matrix.trace (ρ g' : Matrix (Fin 2) (Fin 2) E) ∧
      Matrix.det (ρ g : Matrix (Fin 2) (Fin 2) E) =
        Matrix.det (ρ g' : Matrix (Fin 2) (Fin 2) E) := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  have hρ : (ρ (c * g * c⁻¹) : Matrix (Fin 2) (Fin 2) E) =
      (ρ c : Matrix (Fin 2) (Fin 2) E) * (ρ g : Matrix (Fin 2) (Fin 2) E) *
        ((ρ c)⁻¹ : GL (Fin 2) E) := by
    rw [map_mul, map_mul, map_inv]
    rfl
  rw [hρ]
  exact ⟨(Matrix.trace_units_conj (ρ c) _).symm, (Matrix.det_units_conj (ρ c) _).symm⟩

section Curve

variable {k : Type u} [Field k] [Finite k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

include f

variable [IsIntegral X] in
/-- Every valuation subring of the function field of a scheme over a finite field contains the
image of the finite field: an element `c` with `c ^ q = c` has valuation `1` or `0`. -/
public theorem fieldToStalk_mem_valuationSubring (V : ValuationSubring X.functionField) (c : k) :
    (fieldToStalk f (genericPoint X)).hom c ∈ V := by
  let := Fintype.ofFinite k
  set y := (fieldToStalk f (genericPoint X)).hom c
  have hy : y ^ Fintype.card k = y := by
    simp only [y, ← map_pow, FiniteField.pow_card]
  have hq : 1 < Fintype.card k := Fintype.one_lt_card
  rw [← V.valuation_le_one_iff]
  by_contra h
  push Not at h
  have h1 : V.valuation y < V.valuation y ^ Fintype.card k := by
    have := one_lt_pow₀ h (Nat.sub_ne_zero_of_lt hq)
    calc V.valuation y = V.valuation y * 1 := (mul_one _).symm
      _ < V.valuation y * V.valuation y ^ (Fintype.card k - 1) :=
          mul_lt_mul_of_pos_left this (zero_lt_one.trans h)
      _ = V.valuation y ^ Fintype.card k := by
          rw [← pow_succ', Nat.sub_add_cancel hq.le]
  rw [← map_pow, hy] at h1
  exact lt_irrefl _ h1

variable [IsCurve k f] [Smooth f] [IsProper f]

/-- **Every place of `K` is centred at a closed point of `X`.** -/
public theorem exists_isCentreOf (v : Place X.functionField) :
    ∃ x : closedPoints X, IsCentreOf v x.1 := by
  obtain ⟨P, hP⟩ := Stacks.BombieriStepanov.exists_curvePlace_mem_iff f
    (fun x hx => Stacks.BombieriStepanov.isDiscreteValuationRing_stalk_of_coheight_eq_one f x hx)
    v.1 (fun c => fieldToStalk_mem_valuationSubring f v.1 c) v.2
  exact ⟨⟨P.1, Stacks.EtaleCohomology.isClosed_singleton_of_coheight_eq_one f P.2⟩, hP⟩

omit [Finite k] [IsProper f] in
/-- **A place of `K` is centred at only one closed point of `X`.** -/
public theorem eq_of_isCentreOf {v : Place X.functionField} {x y : closedPoints X}
    (hx : IsCentreOf v x.1) (hy : IsCentreOf v y.1) : x = y := by
  have := IsCurve.isDiscreteValuationRing_stalk_of_isClosed k f x.2
  have := IsCurve.isDiscreteValuationRing_stalk_of_isClosed k f y.2
  exact Subtype.ext (Stacks.BombieriStepanov.eq_of_forall_algebraMap_iff f fun g =>
    (hx g).symm.trans (hy g))

/-- **Every place carries a geometric Frobenius element.** -/
public theorem exists_isGeometricFrobeniusAt [ConnectedSpace X] (base : GeometricPoint X)
    (v : Place X.functionField) : ∃ F : EtaleFundamentalGroup X base,
      IsGeometricFrobeniusAt base v F := by
  obtain ⟨x, hx⟩ := exists_isCentreOf f v
  have := Stacks.EtaleCohomology.finite_residueField f x.1 x.2
  exact ⟨_, x, hx, inferInstance,
    (nonempty_finiteEtaleFiberFunctorIso_of_connectedSpace X _ base).some, rfl⟩

omit [Finite k] [IsProper f] in
/-- **The geometric Frobenius elements at a place form one conjugacy class**: any two of them
are conjugate in `π₁(X, x̄)`. -/
public theorem IsGeometricFrobeniusAt.isConj [ConnectedSpace X] {base : GeometricPoint X}
    {v : Place X.functionField} {F F' : EtaleFundamentalGroup X base}
    (hF : IsGeometricFrobeniusAt base v F) (hF' : IsGeometricFrobeniusAt base v F') :
    IsConj F F' := by
  obtain ⟨x, hx, _, t, rfl⟩ := hF
  obtain ⟨x', hx', _, t', rfl⟩ := hF'
  obtain rfl := eq_of_isCentreOf f hx hx'
  let g : EtaleFundamentalGroup X base := t.symm ≪≫ t'
  have hg : (Stacks.EtaleCohomology.frobeniusDataOfPath base x t').element =
      g * (Stacks.EtaleCohomology.frobeniusDataOfPath base x t).element * g⁻¹ := by
    rw [← FrobeniusData.element_path_trans]
    congr 2
    simp only [g, Stacks.EtaleCohomology.frobeniusDataOfPath]
    exact (Iso.self_symm_id_assoc t t').symm
  rw [hg]
  exact isConj_iff.2 ⟨g, rfl⟩

omit [Finite k] [IsProper f] in
/-- **Compatibility can be checked at one Frobenius element per place.** Since the geometric
Frobenius elements at a place are conjugate, it suffices that each place carry one geometric
Frobenius element `F_v` with `t_v = Tr ρ(F_v)` and `u_v = q_v⁻¹ det ρ(F_v)`. -/
public theorem isFrobeniusCompatible_of_forall_exists [ConnectedSpace X]
    {base : GeometricPoint X} {E : Type*} {Ω : Type*} [Field E] [Field Ω]
    {ρ : EtaleFundamentalGroup X base →* GL (Fin 2) E} {j : E →+* Ω}
    {t u : Place X.functionField → Ω}
    (h : ∀ v : Place X.functionField, ∃ F : EtaleFundamentalGroup X base,
      IsGeometricFrobeniusAt base v F ∧
        t v = j (Matrix.trace (ρ F : Matrix (Fin 2) (Fin 2) E)) ∧
          u v = (Place.residueCard v : Ω)⁻¹ * j (Matrix.det (ρ F : Matrix (Fin 2) (Fin 2) E))) :
    IsFrobeniusCompatible base ρ j t u := by
  intro v F' hF'
  obtain ⟨F, hF, ht, hu⟩ := h v
  obtain ⟨htr, hdet⟩ := trace_det_eq_of_isConj ρ (IsGeometricFrobeniusAt.isConj f hF hF')
  exact ⟨ht.trans (by rw [htr]), hu.trans (by rw [hdet])⟩

end Curve

end Stacks.Adeles.GlobalFunctionField

end
