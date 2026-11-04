module

public import StacksFrontier.AlgebraicGeometry.Thickenings.InfinitesimalTower

/-!
# The bottom stage of the tower of infinitesimal neighbourhoods

Let `i : Z ⟶ X` be an immersion of schemes and let `Zₙ` denote its `n`th-order infinitesimal
neighbourhood `Stacks.Thickenings.nthOrderInfinitesimalNeighbourhood`, the closed subscheme of
the canonical open neighbourhood of the image of `i` cut out by `K ^ (n + 1)`, where `K` is the
defining ideal sheaf of the closed-immersion factorization
`AlgebraicGeometry.Scheme.Hom.liftCoborder` of `i`. At `n = 0` the cutting ideal sheaf is `K`
itself, and the closed subscheme it cuts out is the scheme-theoretic image of `i.liftCoborder`,
which is `Z`, so `Z₀` is identified with `Z`.

## Main results

* `Stacks.Thickenings.isIso_nthOrderInclusion_zero`: the inclusion `Z ⟶ Z₀` is an isomorphism.
* `Stacks.Thickenings.nthOrderZeroIso`: the resulting isomorphism `Z ≅ Z₀`.
* `Stacks.Thickenings.ker_nthOrderToBase_zero`: the structure morphism `Z₀ ⟶ X` has the same
  defining ideal sheaf as `i`.

## Implementation notes

No hypothesis beyond `IsImmersion i` is needed, even though `Z₀` is a closed subscheme of the
open subscheme `AlgebraicGeometry.Scheme.Hom.coborderRange` of `X`: the factorization
`i.liftCoborder` of an immersion through that open subscheme is already a closed immersion, and
`Z₀` is cut out by precisely its defining ideal sheaf. In particular the statement for a closed
immersion `i`, where `Z₀` is the closed subscheme of `X` cut out by `i.ker`, is the case
`i.coborderRange = ⊤`.

The isomorphism is `AlgebraicGeometry.IsClosedImmersion.isIso_of_ker_eq`: two closed immersions
into the same scheme with the same defining ideal sheaf are identified by any morphism
commuting with them.

## References

* [Stacks Project, Tag 04EY](https://stacks.math.columbia.edu/tag/04EY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Thickenings

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/-- The zeroth-order infinitesimal neighbourhood of an immersion is cut out by the defining
ideal sheaf `K` of its closed-immersion factorization itself, not by a proper power of `K`. -/
theorem nthOrderι_ker_zero : (nthOrderι i 0).ker = i.liftCoborder.ker := by
  rw [nthOrderι_ker, zero_add, pow_one]

/-- The bottom stage of the tower of infinitesimal neighbourhoods is `Z` itself: the
inclusion of `Z` into its zeroth-order infinitesimal neighbourhood is an isomorphism, because
both `Z` and that neighbourhood are closed subschemes of the canonical open neighbourhood of the
image of `i` cut out by the same ideal sheaf. -/
instance isIso_nthOrderInclusion_zero : IsIso (nthOrderInclusion i 0) :=
  IsClosedImmersion.isIso_of_ker_eq i.liftCoborder (nthOrderι i 0) (nthOrderInclusion i 0)
    (nthOrderInclusion_nthOrderι i 0) (nthOrderι_ker_zero i).symm

/-- `Z` is its own zeroth-order infinitesimal neighbourhood in `X`, by
`Stacks.Thickenings.isIso_nthOrderInclusion_zero`. -/
def nthOrderZeroIso : Z ≅ nthOrderInfinitesimalNeighbourhood i 0 :=
  asIso (nthOrderInclusion i 0)

/-- The identification of `Z` with its zeroth-order infinitesimal neighbourhood is the inclusion
`Z ⟶ Z₀`. -/
@[simp]
theorem nthOrderZeroIso_hom : (nthOrderZeroIso i).hom = nthOrderInclusion i 0 := rfl

/-- The inverse of the identification of `Z` with its zeroth-order infinitesimal neighbourhood,
followed by `i`, is the structure morphism of that neighbourhood. -/
@[reassoc (attr := simp)]
theorem nthOrderZeroIso_inv_comp : (nthOrderZeroIso i).inv ≫ i = nthOrderToBase i 0 := by
  rw [Iso.inv_comp_eq, nthOrderZeroIso_hom, nthOrderInclusion_toBase]

/-- The inverse of the identification of `Z` with its zeroth-order infinitesimal neighbourhood,
followed by the closed-immersion factorization of `i`, is the closed immersion of that
neighbourhood into the canonical open neighbourhood of the image of `i`. -/
@[reassoc (attr := simp)]
theorem nthOrderZeroIso_inv_liftCoborder :
    (nthOrderZeroIso i).inv ≫ i.liftCoborder = nthOrderι i 0 := by
  rw [Iso.inv_comp_eq, nthOrderZeroIso_hom, nthOrderInclusion_nthOrderι]

/-- Under the identification of `Z` with the bottom stage of the tower of infinitesimal
neighbourhoods, the first stage `Z₀ ⟶ Z₁` of the tower is the inclusion of `Z` into its
first-order infinitesimal neighbourhood. -/
@[reassoc (attr := simp)]
theorem nthOrderZeroIso_hom_nthOrderSucc :
    (nthOrderZeroIso i).hom ≫ nthOrderSucc i 0 = nthOrderInclusion i 1 := by
  rw [nthOrderZeroIso_hom, nthOrderInclusion_nthOrderSucc]

/-- The structure morphism `Z₀ ⟶ X` of the zeroth-order infinitesimal neighbourhood has the same
defining ideal sheaf as `i`, since it differs from `i` by the isomorphism
`Stacks.Thickenings.nthOrderZeroIso`. -/
theorem ker_nthOrderToBase_zero : (nthOrderToBase i 0).ker = i.ker :=
  (Scheme.Hom.ker_comp_of_isIso (nthOrderInclusion i 0) (nthOrderToBase i 0)).symm.trans
    (congrArg Scheme.Hom.ker (nthOrderInclusion_toBase i 0))

section ClosedImmersion

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The zeroth-order infinitesimal neighbourhood of a closed immersion is a closed subscheme of
the base: its structure morphism is `i` composed with an isomorphism. -/
instance isClosedImmersion_nthOrderToBase_zero :
    IsClosedImmersion (nthOrderToBase i 0) := by
  rw [← nthOrderZeroIso_inv_comp]
  infer_instance

end ClosedImmersion

end Stacks.Thickenings

end
