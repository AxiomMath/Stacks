module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.KrullDimension
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersectionLeadingTerm
public import StacksFrontier.Order.GradeHeight
public import StacksFrontier.Topology.Dimension.DimensionFunctionCatenary
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.NormalPosition.LocalDimension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A dimension function vanishing at closed points

Let `X` be a quasi-compact scheme and `δ` a dimension function on `X` ([Stacks, Tag 02I8]) which
vanishes at the closed points. Then `δ(x) = dim(closure {x})` for every point `x`, and
`dim(closure {x}) + dim(𝒪_{X,x}) = dim(X)` holds exactly at the points lying on an irreducible
component of dimension `dim(X)`.

This is the argument of the proof of [Stacks, Tag 0AWN]: for `X` proper over a Noetherian local
ring with its normalized relative dualizing complex, the associated dimension function vanishes at
the closed points, and "hence `δ_X(ξ) = dim(closure {ξ})` for any point `ξ ∈ X`".

## Main results

* `AlgebraicGeometry.topologicalKrullDim_closure_singleton_eq_height` — in the specialization
  order the dimension of the closure of a point is its height.
* `AlgebraicGeometry.topologicalKrullDim_closure_eq_of_dimensionFunction` — `δ(x)` is the
  dimension of the closure of `x`.
* `AlgebraicGeometry.dim_closure_add_dim_stalk_eq_iff_of_dimensionFunction` —
  `dim(closure {x}) + dim(𝒪_{X,x}) = dim(X)` exactly on the union of the components of dimension
  `dim(X)`.

## Implementation notes

The specialization order of a scheme is a preorder in Mathlib (`x ≤ y` when `y ⤳ x`); it is
antisymmetric because schemes are `T0`, and `AlgebraicGeometry.Scheme.specializationPartialOrder`
records this as a partial order with the same `≤`, so that the order-theoretic results
`Order.height_eq_of_grade` and `Order.height_add_coheight_eq_iff_of_grade` apply. The dimension of
the local ring is the coheight of the point, `AlgebraicGeometry.ringKrullDim_stalk_eq_coheight`.

## References

* [Stacks Project, Tag 0AWN](https://stacks.math.columbia.edu/tag/0AWN)
* [Stacks Project, Tag 02I8](https://stacks.math.columbia.edu/tag/02I8)
-/

@[expose] public section

open TopologicalSpace Order

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The specialization preorder of a scheme is a partial order: a scheme is `T0`. -/
@[sga "4 IV 4.2.2" "special case"]
abbrev Scheme.specializationPartialOrder (X : Scheme.{u}) : PartialOrder X :=
  { (inferInstance : Preorder X) with
    le_antisymm := fun a b hab hba =>
      (Specializes.antisymm (show a ⤳ b from hba) (show b ⤳ a from hab)).eq }

/-- A point is minimal in the specialization order exactly when it is closed. -/
theorem isMin_iff_isClosed_singleton (x : X) : IsMin x ↔ IsClosed ({x} : Set X) := by
  refine ⟨fun h => closure_subset_iff_isClosed.mp fun y hy => ?_, fun h y hy => ?_⟩
  · have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hy
    exact (hxy.antisymm
      (Scheme.le_iff_specializes.mp (h (Scheme.le_iff_specializes.mpr hxy)))).eq.symm
  · obtain rfl : y = x :=
      h.closure_subset (specializes_iff_mem_closure.mp (Scheme.le_iff_specializes.mp hy))
    exact le_rfl

/-- In a quasi-compact scheme every point specializes to a closed point. -/
theorem exists_isMin_le [CompactSpace X] (x : X) : ∃ c ≤ x, IsMin c := by
  obtain ⟨c, hc, hcl⟩ := (isClosed_closure (s := ({x} : Set X))).exists_closed_singleton
    ⟨x, subset_closure rfl⟩
  exact ⟨c, Scheme.le_iff_specializes.mpr (specializes_iff_mem_closure.mpr hc),
    (isMin_iff_isClosed_singleton c).mpr hcl⟩

/-- A point of an irreducible component specializes from the generic point of that component. -/
private theorem exists_le_closure_singleton_eq {C : Set X} (hC : C ∈ irreducibleComponents X)
    {x : X} (hx : x ∈ C) : ∃ η : X, x ≤ η ∧ closure ({η} : Set X) = C := by
  obtain ⟨η, hη⟩ := QuasiSober.sober hC.1 (isClosed_of_mem_irreducibleComponents C hC)
  exact ⟨η, Scheme.le_iff_specializes.mpr (hη.specializes hx), hη.def⟩

/-- A point is maximal in the specialization order exactly when its closure is an irreducible
component. -/
theorem isMax_iff_closure_mem_irreducibleComponents (η : X) :
    IsMax η ↔ closure ({η} : Set X) ∈ irreducibleComponents X := by
  refine ⟨fun h => ?_, fun h ξ hle => ?_⟩
  · obtain ⟨C, hC, hηC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
      (closure ({η} : Set X)) isIrreducible_singleton.closure
    obtain ⟨ξ, hle, hξ⟩ := exists_le_closure_singleton_eq hC (hηC (subset_closure rfl))
    obtain rfl : η = ξ :=
      (Scheme.le_iff_specializes.mp (h hle)).antisymm (Scheme.le_iff_specializes.mp hle) |>.eq
    rwa [hξ]
  · rw [Scheme.le_iff_specializes, specializes_iff_closure_subset]
    exact h.2 isIrreducible_singleton.closure
      (specializes_iff_closure_subset.mp (Scheme.le_iff_specializes.mp hle))

/-- Every point of a scheme lies below a maximal point, the generic point of an irreducible
component containing it. -/
theorem exists_le_isMax (x : X) : ∃ η, x ≤ η ∧ IsMax η := by
  obtain ⟨C, hC, hxC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({x} : Set X)) isIrreducible_singleton.closure
  obtain ⟨η, hxη, hη⟩ := exists_le_closure_singleton_eq hC (hxC (subset_closure rfl))
  exact ⟨η, hxη, by rwa [isMax_iff_closure_mem_irreducibleComponents, hη]⟩

/-- **The dimension of the closure of a point is its height** in the specialization order. -/
theorem topologicalKrullDim_closure_singleton_eq_height (x : X) :
    topologicalKrullDim (closure ({x} : Set X)) = (Order.height x : WithBot ℕ∞) := by
  have := topologicalKrullDim_irreducibleCloseds (irreducibleSetEquivPoints.symm x)
  rw [coe_irreducibleEquivPoints_symm_apply] at this
  rw [this, Order.height_orderIso]

/-! ### Dimension functions as gradings of the specialization order -/

namespace DimensionFunctionGrade

/-- A dimension function is strictly monotone for the specialization order. -/
theorem strictMono (d : DimensionFunction X) :
    letI := Scheme.specializationPartialOrder X
    StrictMono d.toFun := fun _ _ hab =>
  d.strictAnti_specializes (Scheme.le_iff_specializes.mp hab.le) hab.ne'

/-- A dimension function increases by one along a covering relation of the specialization order:
a covering relation is an immediate specialization. -/
theorem covBy (d : DimensionFunction X) {a b : X}
    (h : letI := Scheme.specializationPartialOrder X; a ⋖ b) : d.toFun b = d.toFun a + 1 :=
  let := Scheme.specializationPartialOrder X
  d.step_immediate ⟨Scheme.le_iff_specializes.mp h.le, h.ne', fun z hbz hza => by
    by_contra hne
    push Not at hne
    exact h.2 (lt_of_le_of_ne' (Scheme.le_iff_specializes.mpr hza) hne.2)
      (lt_of_le_of_ne (Scheme.le_iff_specializes.mpr hbz) hne.1)⟩

end DimensionFunctionGrade

/-- A dimension function vanishing at the closed points gives the height of a point. -/
private theorem height_eq_toNat_of_dimensionFunction [CompactSpace X] (d : DimensionFunction X)
    (hd : ∀ x : X, IsClosed ({x} : Set X) → d x = 0) (x : X) :
    letI := Scheme.specializationPartialOrder X
    0 ≤ d.toFun x ∧ Order.height x = ((d.toFun x).toNat : ℕ∞) :=
  letI := Scheme.specializationPartialOrder X
  Order.height_eq_of_grade (DimensionFunctionGrade.strictMono d)
    (fun _ _ => DimensionFunctionGrade.covBy d)
    (fun a ha => hd a ((isMin_iff_isClosed_singleton a).mp ha)) exists_isMin_le x

/-- **A dimension function vanishing at the closed points is the dimension of the closure.** On a
quasi-compact scheme, a dimension function `δ` with `δ(x) = 0` at every closed point satisfies
`δ(x) = dim(closure {x})` at every point; in particular it is nonnegative. -/
theorem topologicalKrullDim_closure_eq_of_dimensionFunction [CompactSpace X]
    (d : DimensionFunction X) (hd : ∀ x : X, IsClosed ({x} : Set X) → d x = 0) (x : X) :
    0 ≤ d x ∧ topologicalKrullDim (closure ({x} : Set X)) = (((d x).toNat : ℕ) : WithBot ℕ∞) := by
  let := Scheme.specializationPartialOrder X
  obtain ⟨h0, hh⟩ := height_eq_toNat_of_dimensionFunction d hd x
  rw [topologicalKrullDim_closure_singleton_eq_height]
  exact ⟨h0, by exact_mod_cast hh⟩

/-- **The points where the dimension of the closure and of the local ring add up to `dim(X)`.**
On a quasi-compact scheme of dimension `n` carrying a dimension function vanishing at the closed
points, `dim(closure {x}) + dim(𝒪_{X,x}) = n` holds exactly when `x` lies on an irreducible
component of dimension `n`. -/
theorem dim_closure_add_dim_stalk_eq_iff_of_dimensionFunction [CompactSpace X]
    (d : DimensionFunction X) (hd : ∀ x : X, IsClosed ({x} : Set X) → d x = 0) (n : ℕ)
    (hn : topologicalKrullDim X = (n : WithBot ℕ∞)) (x : X) :
    topologicalKrullDim (closure ({x} : Set X)) + ringKrullDim (X.presheaf.stalk x) =
        (n : WithBot ℕ∞) ↔
      x ∈ ⋃₀ {C ∈ irreducibleComponents X | topologicalKrullDim C = (n : WithBot ℕ∞)} := by
  let := Scheme.specializationPartialOrder X
  have hgr := DimensionFunctionGrade.strictMono d
  have hcov : ∀ a b : X, a ⋖ b → d.toFun b = d.toFun a + 1 :=
    fun _ _ => DimensionFunctionGrade.covBy d
  have hmin : ∀ a : X, IsMin a → d.toFun a = 0 :=
    fun a ha => hd a ((isMin_iff_isClosed_singleton a).mp ha)
  have hgrade := height_eq_toNat_of_dimensionFunction d hd
  have hle : ∀ y : X, d.toFun y ≤ n := fun y => by
    have := Order.height_le_krullDim y
    rw [← Stacks.ResolutionOfSurfaces.topologicalKrullDim_eq_krullDim, hn, (hgrade y).2] at this
    have : (d.toFun y).toNat ≤ n := by exact_mod_cast this
    omega
  rw [topologicalKrullDim_closure_singleton_eq_height, ringKrullDim_stalk_eq_coheight,
    ← WithBot.coe_add, show ((n : ℕ) : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) from rfl,
    WithBot.coe_inj,
    Order.height_add_coheight_eq_iff_of_grade hgr hcov hmin exists_isMin_le exists_le_isMax x n
      (fun η _ _ => hle η)]
  refine ⟨fun ⟨η, hxη, hη, hdη⟩ => ?_, fun ⟨C, ⟨hC, hCn⟩, hxC⟩ => ?_⟩
  · refine ⟨closure ({η} : Set X),
      ⟨(isMax_iff_closure_mem_irreducibleComponents η).mp hη, ?_⟩,
      specializes_iff_mem_closure.mp (Scheme.le_iff_specializes.mp hxη)⟩
    rw [topologicalKrullDim_closure_singleton_eq_height]
    rw [(hgrade η).2, hdη, Int.toNat_natCast]
  · obtain ⟨η, hxη, hη⟩ := exists_le_closure_singleton_eq hC hxC
    refine ⟨η, hxη, ?_, ?_⟩
    · rwa [isMax_iff_closure_mem_irreducibleComponents, hη]
    · rw [← hη, topologicalKrullDim_closure_singleton_eq_height, (hgrade η).2] at hCn
      have := (hgrade η).1
      have : (d.toFun η).toNat = n := by exact_mod_cast hCn
      omega

/-- **A Noetherian scheme with a dimension function vanishing at the closed points has finite
dimension.** Every point lies below the generic point of one of the finitely many irreducible
components, and the height of that generic point is the value of the dimension function there. -/
theorem exists_topologicalKrullDim_eq_of_dimensionFunction [CompactSpace X]
    [NoetherianSpace X] [Nonempty X]
    (d : DimensionFunction X) (hd : ∀ x : X, IsClosed ({x} : Set X) → d x = 0) :
    ∃ n : ℕ, topologicalKrullDim X = (n : WithBot ℕ∞) := by
  let := Scheme.specializationPartialOrder X
  have hfin : {η : X | IsMax η}.Finite :=
    (genericPoints.finite NoetherianSpace.finite_irreducibleComponents).subset
      fun η => (isMax_iff_closure_mem_irreducibleComponents η).mp
  let M : ℕ := hfin.toFinset.sup fun η => (d.toFun η).toNat
  have hbound : ∀ x : X, Order.height x ≤ (M : ℕ∞) := fun x => by
    obtain ⟨η, hxη, hη⟩ := exists_le_isMax x
    refine (Order.height_mono hxη).trans ?_
    rw [(height_eq_toNat_of_dimensionFunction d hd η).2]
    exact_mod_cast Finset.le_sup (f := fun η => (d.toFun η).toNat)
      (hfin.mem_toFinset.mpr hη)
  refine ⟨(⨆ x : X, Order.height x).toNat, ?_⟩
  rw [Stacks.ResolutionOfSurfaces.topologicalKrullDim_eq_krullDim,
    Order.krullDim_eq_iSup_height_of_nonempty]
  conv_lhs => rw [← ENat.natCast_toNat (ne_top_of_le_ne_top (by simp) (iSup_le hbound))]
  rfl

end AlgebraicGeometry
