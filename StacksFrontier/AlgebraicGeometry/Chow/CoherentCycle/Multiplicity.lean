module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.CoherentSupportDimension

/-!
# The multiplicity of a coherent sheaf at a point

Let `X` be a scheme locally of finite type over the base scheme `S` of chapter 42 of the Stacks
Project and let `F` be a coherent `𝒪_X`-module whose support has delta-dimension at most `k`.
This file records what the multiplicity `Stacks.Chow.sheafMultiplicity` of `F` detects.

The stalk of `F` at a point of delta-dimension exactly `k` has finite length, so the
multiplicity there is the honest length of that stalk; it is strictly positive exactly on the
support, and vanishes off it. These are the facts that let a multiplicity be multiplied,
compared with zero, and used to decide membership in a support.

## Main results

* `Stacks.Chow.isFiniteLength_stalk_of_relativeDimension_eq` — the stalk at a point of relative
  dimension `k` has finite length.
* `Stacks.Chow.sheafMultiplicity_pos_of_mem_supp` — the multiplicity is positive on the support
  wherever the stalk has finite length.
* `Stacks.Chow.mem_supp_of_sheafMultiplicity_ne_zero` — a nonzero multiplicity places the point
  in the support.

## Implementation notes

The finiteness of the length at a point of relative dimension `k` splits into the two cases of
Stacks 02QW: on the support the point is the generic point of an irreducible component, where
`Stacks.Chow.isFiniteLength_stalk_of_isGenericPoint_component_supp` applies, and off the support
the stalk vanishes.

## References

* [Stacks Project, Tag 02QW](https://stacks.math.columbia.edu/tag/02QW)
* [Stacks Project, Tag 02QX](https://stacks.math.columbia.edu/tag/02QX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}}

/-- A point lies in the support of a sheaf of modules exactly when its stalk has positive length. -/
private theorem mem_supp_iff_length_pos (F : X.Modules) (x : X) :
    x ∈ SheafOfModules.supp F ↔
      0 < Module.length (R := X.presheaf.stalk x) (M := F.presheaf.stalk x) :=
  (SheafOfModules.mem_supp_iff_nontrivial_stalk F x).trans
    (Module.length_pos_iff (R := X.presheaf.stalk x) (M := F.presheaf.stalk x)).symm

/-- On the support of a sheaf of modules the multiplicity is strictly positive, provided the
stalk there has finite length: the stalk is nonzero, so its length is nonzero, and finiteness
makes the cast to an integer faithful. -/
theorem sheafMultiplicity_pos_of_mem_supp (F : X.Modules) {x : X}
    (hlen : IsFiniteLength (X.presheaf.stalk x) (F.presheaf.stalk x))
    (hx : x ∈ SheafOfModules.supp F) : 0 < sheafMultiplicity F x := by
  have := ENat.toNat_pos ((mem_supp_iff_length_pos F x).mp hx).ne'
    (Module.length_ne_top_iff.mpr hlen)
  simpa [sheafMultiplicity] using Int.ofNat_lt.mpr this

/-- A point at which the multiplicity of a sheaf of modules is nonzero lies in its support: the
length of the stalk is nonzero, so the stalk is nonzero. -/
theorem mem_supp_of_sheafMultiplicity_ne_zero (F : X.Modules) {x : X}
    (hx : sheafMultiplicity F x ≠ 0) : x ∈ SheafOfModules.supp F :=
  (mem_supp_iff_length_pos F x).mpr
    (pos_iff_ne_zero.mpr fun h ↦ hx (by simp [sheafMultiplicity, h]))

/-- At a point of relative dimension `k`, the stalk of a coherent sheaf whose support has
delta-dimension at most `k` has finite length over the local ring of the scheme. On the support
the point is the generic point of an irreducible component, and off the support the stalk is
zero. -/
theorem isFiniteLength_stalk_of_relativeDimension_eq (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsCoherent] {k : ℤ}
    (hFk : schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ f) ≤ (k : EInt)) {x : X}
    (hx : relativeDimension C.dimensionFunction f x = k) :
    IsFiniteLength (X.presheaf.stalk x) (F.presheaf.stalk x) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  by_cases hxF : x ∈ SheafOfModules.supp F
  · obtain ⟨Z, hZ⟩ :=
      isGenericPoint_component_supp_of_relativeDimension_eq C f F k x hFk hxF hx
    exact isFiniteLength_stalk_of_isGenericPoint_component_supp F Z x hZ
  · exact Module.length_ne_top_iff.mp
      (ne_top_of_le_ne_top ENat.zero_ne_top (not_lt.mp (mt (mem_supp_iff_length_pos F x).mpr hxF)))

end Stacks.Chow
