module

public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.StalkDimension
public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.ProductDecomposition
public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToDiagonal.TorFormulaDeficient
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersectionLeadingTerm

/-!
# The local dimensions at the generic point of `Z` in Stacks 0B0E

The local form of Stacks 0B1J which the display `C · X = [Z] + ∑ m_j [Z_j]` of Stacks 0B0E goes
through takes its proper-intersection hypothesis at the generic point `ξ` of `Z`, in the shape

`dim 𝒪_{𝐏^N, ξ} ≤ dim (𝒪_{𝐏^N, ξ} ⧸ I₀) + dim (𝒪_{𝐏^N, ξ} ⧸ J₀)`

with `I₀` and `J₀` the local ideals of `C` and of `X` at `ξ`. On a scheme over a field every one
of those three dimensions is a difference of relative dimensions — `N - d`, `dim C - d` and
`dim X - d` — so the hypothesis is the numerical inequality `N + d ≤ dim C + dim X`, which is the
inequality the construction of the cone supplies. It is *not* proper intersection of `C` and `X`,
which is the opposite inequality; here the two are the two directions of an equality.

## Main results

* `AlgebraicGeometry.relativeDimension_eq_of_topologicalKrullDim_closure_eq`: the relative
  dimension at a point is the dimension of the closure of that point.
* `AlgebraicGeometry.ringKrullDim_quotient_localIdealAt_eq`: the dimension of the local ring of
  the reduced closure of `x` at a point `ξ` of that closure is the difference of the relative
  dimensions at `x` and at `ξ`.
* `AlgebraicGeometry.ringKrullDim_stalk_le_add_ringKrullDim_quotient_localIdealAt`: the
  proper-intersection hypothesis of the local form of Stacks 0B1J, from the numerical inequality.

## Implementation notes

The dimension of the local ring is read through
`Stacks.Chow.ringKrullDim_stalk_eq_toNat_sub_relativeDimension`, which asks that every
irreducible component of the scheme have the same relative dimension. For the ambient `𝐏^N` and
for the integral closed subschemes attached to points that is one component, so the hypothesis is
`Stacks.Chow.relativeDimension_genericPoint_of_irreducibleSpace`; the subscheme case is packaged
as `Stacks.Intersection.ReductionToDiagonal.ringKrullDim_stalk_subscheme_eq_toNat_sub`, and
`Stacks.Chow.ringKrullDim_quotient_idealStalk_eq` is what identifies the quotient of the ambient
local ring by the local ideal with the local ring of the subscheme.

Nothing here needs the dimension of `C` as a natural number: the relative dimension at its
generic point plays that role throughout, and the one place a natural number is wanted — the
comparison with the bound of the cone construction — converts in the other direction, through
`Stacks.Chow.topologicalKrullDim_eq_relativeDimension_toNat`.

## References

* [Stacks Project, Tag 0B0E](https://stacks.math.columbia.edu/tag/0B0E)
* [Stacks Project, Tag 0B1J](https://stacks.math.columbia.edu/tag/0B1J)
* [Stacks Project, Tag 02QO](https://stacks.math.columbia.edu/tag/02QO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.Chow

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- **The relative dimension at a point is the dimension of the closure of that point.** The
reduced closure of `x` is an integral closed subscheme whose space is the closure of `x`, so Tag
02QO reads its dimension as the relative dimension at `x`; nonnegativity of the relative
dimension turns the truncation `Int.toNat` into an equality of integers. -/
public theorem relativeDimension_eq_of_topologicalKrullDim_closure_eq (k : Type u) [Field k]
    (q : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType q] {n : ℕ} {x : X}
    (hdim : topologicalKrullDim ↥(closure ({x} : Set X)) = (n : WithBot ℕ∞)) :
    relativeDimension (fieldChowSituation k).dimensionFunction q x = (n : ℤ) := by
  have : IsIntegral (integralComponentAt x).subscheme := isIntegral_integralComponentAt x
  have hgen : IsGenericPoint (genericPoint (integralComponentAt x).subscheme)
      (Set.univ : Set (integralComponentAt x).subscheme) :=
    (IrreducibleSpace.isIrreducible_univ _).isGenericPoint_genericPoint isClosed_univ
  have hkey := topologicalKrullDim_eq_relativeDimension_toNat (fieldChowSituation k)
    (fun _ _ ↦ rfl) q (integralComponentAt x).subschemeι
    (genericPoint (integralComponentAt x).subscheme) hgen
  rw [show (integralComponentAt x).subschemeι.base
      (genericPoint (integralComponentAt x).subscheme) = x from
    genericPointOf_integralComponentAt x, ← topologicalKrullDim_support_eq
    (integralComponentAt x), coe_support_integralComponentAt, hdim] at hkey
  have hnat : n = (relativeDimension (fieldChowSituation k).dimensionFunction q x).toNat := by
    exact_mod_cast hkey
  have hnn := relativeDimension_nonneg (fieldChowSituation k) (fun _ _ ↦ rfl) q x
  omega

/-- **The dimension of the local ring of a closed subvariety at a point of it.** For `ξ` in the
closure of `x`, the quotient of the local ring of the ambient scheme at `ξ` by the local ideal of
`closure {x}` is the local ring of the reduced closure of `x` at the point of it over `ξ`, whose
dimension is the difference of the relative dimensions at `x` and at `ξ`. -/
public theorem ringKrullDim_quotient_localIdealAt_eq (k : Type u) [Field k]
    (q : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType q] (x : X) {ξ : X}
    (hξ : ξ ∈ closure ({x} : Set X)) :
    ringKrullDim (X.presheaf.stalk ξ ⧸ TorFormula.localIdealAt x ξ) =
      ((((relativeDimension (fieldChowSituation k).dimensionFunction q x -
        relativeDimension (fieldChowSituation k).dimensionFunction q ξ).toNat : ℕ) : ℕ∞) :
          WithBot ℕ∞) := by
  have hI := isIntegral_integralComponentAt x
  have hmem : ξ ∈ Set.range (integralComponentAt x).subschemeι.base := by
    rw [Scheme.IdealSheafData.range_subschemeι, coe_support_integralComponentAt]
    exact hξ
  obtain ⟨v, hv⟩ := hmem
  rw [show TorFormula.localIdealAt x ξ = IdealSheafData.stalk (integralComponentAt x) ξ from rfl,
    ← hv, ringKrullDim_quotient_idealStalk_eq (integralComponentAt x) v,
    Stacks.Intersection.ReductionToDiagonal.ringKrullDim_stalk_subscheme_eq_toNat_sub
      (fieldChowSituation k) q (integralComponentAt x) hI v,
    genericPointOf_integralComponentAt x, hv]

/-- **The proper-intersection hypothesis of the local form of Stacks 0B1J, from the numerical
inequality.** Let `x`, `y` be points of an irreducible scheme `X` over a field, with relative
dimensions `c` and `b` at them, let `ξ` be a point of both their closures of relative dimension
`e`, and let the relative dimension at the generic point of `X` be `m`. If `m + e ≤ c + b` then

`dim 𝒪_{X, ξ} ≤ dim (𝒪_{X, ξ} ⧸ I₀) + dim (𝒪_{X, ξ} ⧸ J₀)`

for the local ideals `I₀`, `J₀` of `closure {x}` and `closure {y}` at `ξ`.

In Stacks 0B0E this is applied with `X = 𝐏^N`, `x` the generic point of the cone `C`, `y` the
generic point of the nonsingular subvariety and `ξ` the generic point of `Z`, where the numerical
inequality is `N + d ≤ dim C + dim X` — the bound
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_coneCl_intersectProperly_inter_eq` returns
beside the proper intersection, and not proper intersection itself, which is the opposite
inequality. -/
public theorem ringKrullDim_stalk_le_add_ringKrullDim_quotient_localIdealAt (k : Type u) [Field k]
    [IrreducibleSpace X] (q : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType q] {x y ξ : X}
    (hξx : ξ ∈ closure ({x} : Set X)) (hξy : ξ ∈ closure ({y} : Set X))
    (hnum : relativeDimension (fieldChowSituation k).dimensionFunction q (genericPoint X) +
        relativeDimension (fieldChowSituation k).dimensionFunction q ξ ≤
      relativeDimension (fieldChowSituation k).dimensionFunction q x +
        relativeDimension (fieldChowSituation k).dimensionFunction q y) :
    ringKrullDim (X.presheaf.stalk ξ) ≤
      ringKrullDim (X.presheaf.stalk ξ ⧸ TorFormula.localIdealAt x ξ) +
        ringKrullDim (X.presheaf.stalk ξ ⧸ TorFormula.localIdealAt y ξ) := by
  obtain ⟨d, hd⟩ := relativeDimension_isDimensionFunction
    (fieldChowSituation k).isUniversallyCatenary (fieldChowSituation k).dimensionFunction q
  -- the relative dimension drops along specialization, so `ξ` has the smallest of the four
  have hmono : ∀ z w : X, z ∈ closure ({w} : Set X) →
      relativeDimension (fieldChowSituation k).dimensionFunction q z ≤
        relativeDimension (fieldChowSituation k).dimensionFunction q w := by
    intro z w hzw
    rcases eq_or_ne z w with heq | hne
    · exact le_of_eq (by rw [heq])
    · have hlt := d.strictAnti_specializes
        (by simpa [specializes_iff_mem_closure] using hzw) (Ne.symm hne)
      rw [hd z, hd w] at hlt
      omega
  have hle := hmono ξ (genericPoint X)
    (specializes_iff_mem_closure.mp (genericPoint_specializes ξ))
  have hlex := hmono ξ x hξx
  have hley := hmono ξ y hξy
  rw [ringKrullDim_stalk_eq_toNat_sub_relativeDimension (fieldChowSituation k) q
      (Stacks.Intersection.ReductionToDiagonal.relativeDimension_genericPoint_of_irreducibleSpace
        (fieldChowSituation k) q rfl) ξ,
    ringKrullDim_quotient_localIdealAt_eq k q x hξx,
    ringKrullDim_quotient_localIdealAt_eq k q y hξy]
  have hnat : (relativeDimension (fieldChowSituation k).dimensionFunction q (genericPoint X) -
        relativeDimension (fieldChowSituation k).dimensionFunction q ξ).toNat ≤
      (relativeDimension (fieldChowSituation k).dimensionFunction q x -
          relativeDimension (fieldChowSituation k).dimensionFunction q ξ).toNat +
        (relativeDimension (fieldChowSituation k).dimensionFunction q y -
          relativeDimension (fieldChowSituation k).dimensionFunction q ξ).toNat := by
    omega
  exact_mod_cast hnat

end AlgebraicGeometry

end
