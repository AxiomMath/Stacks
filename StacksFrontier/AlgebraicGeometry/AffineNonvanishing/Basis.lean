module

public import StacksFrontier.AlgebraicGeometry.Ample.Defs
public import StacksFrontier.AlgebraicGeometry.AffineNonvanishing.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Tag 01PX: the affine members of a basis of nonvanishing opens are already a basis

Let `X` be a scheme and `L` an invertible sheaf of `𝒪_X`-modules.  Suppose the nonvanishing
opens `X_s` of global sections `s` of the positive tensor powers `L^{⊗ n}` form a basis of the
topology of `X`.  Then the *affine* ones among them already form a basis
([Stacks, Tag 01PX]).

## Main results

* `AlgebraicGeometry.Scheme.Modules.isBasis_affine_nonvanishingOpens`: **Tag 01PX**.

## Implementation notes

The proof is the composite of two bases.  Given a point `x` and an open `V ∋ x`, the affine
opens of a scheme are a basis (`AlgebraicGeometry.Scheme.isBasis_affineOpens`), so `x` has an
affine open neighbourhood `U ⊆ V`; the hypothesis then puts a nonvanishing open
`W = X_s ⊆ U` between `x` and `U`.  Tag 01PV
(`AlgebraicGeometry.Scheme.Modules.isAffineOpen_inf_nonvanishingOpen`) says `U ⊓ X_s` is
affine, and `W ≤ U` makes that intersection `W` itself, so `W` is a member of the smaller set.

The tensor powers are `Stacks.SheafOfModules.Invertible.tensorPower` (Tag 01CU) and the
nonvanishing open is `Stacks.SheafOfModules.nonvanishingOpen` (Tag 01CY), which is the
vocabulary `AlgebraicGeometry.Scheme.Modules.IsAmple` (Tag 01PS) is stated in.  Invertibility of
a tensor power, which is what makes its nonvanishing open meaningful, is supplied by the
exported instance `AlgebraicGeometry.Scheme.Modules.isInvertible_tensorPower`, so no local
instance and no transparency option is needed here.

## References

* [Stacks Project, Tag 01PX](https://stacks.math.columbia.edu/tag/01PX)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

open Stacks.SheafOfModules Stacks.SheafOfModules.Invertible

variable (X : Scheme.{u}) (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L]

/-- **Stacks Project, Tag 01PX.** If the nonvanishing opens of global sections of the positive
tensor powers of an invertible sheaf form a basis of the topology, then the affine ones among
them already form a basis. -/
@[stacks 01PX]
public theorem isBasis_affine_nonvanishingOpens
    (hBasis : Opens.IsBasis
      {U : X.Opens | ∃ n : ℕ, 1 ≤ n ∧
        ∃ s : (tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L (n : ℤ)).sections,
          U = nonvanishingOpen (X := X.toLocallyRingedSpace.toRingedSpace)
            (tensorPower X.toRingedSpace.presheaf
              (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s}) :
    Opens.IsBasis
      {U : X.Opens | (∃ n : ℕ, 1 ≤ n ∧
        ∃ s : (tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L (n : ℤ)).sections,
          U = nonvanishingOpen (X := X.toLocallyRingedSpace.toRingedSpace)
            (tensorPower X.toRingedSpace.presheaf
              (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s) ∧
          IsAffineOpen U} := by
  rw [Opens.isBasis_iff_nbhd]
  intro V x hx
  obtain ⟨U, hU, hxU, hUV⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hx
  obtain ⟨W, ⟨n, hn, s, rfl⟩, hxW, hWU⟩ := (Opens.isBasis_iff_nbhd.mp hBasis) hxU
  refine ⟨_, ⟨⟨n, hn, s, rfl⟩, ?_⟩, hxW, hWU.trans hUV⟩
  simpa only [inf_eq_right.mpr hWU] using isAffineOpen_inf_nonvanishingOpen _ s U hU

end AlgebraicGeometry.Scheme.Modules

end
