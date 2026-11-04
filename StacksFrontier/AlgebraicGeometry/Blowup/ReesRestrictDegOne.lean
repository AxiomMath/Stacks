module

public import StacksFrontier.AlgebraicGeometry.Blowup.Existence
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesSheafData

/-!
# Restricting a section of the centre and its degree-one Rees element

Let `S` be a scheme, `ℐ` a quasi-coherent ideal sheaf on it and `h : U ≤ V` an inclusion of
affine opens of `S`. A section of `ℐ` over `V` restricts to one over `U`, and the degree-one
element it contributes to the Rees algebra restricts to the degree-one element of the restricted
section. These two facts are what makes the Tag 01NO chart transition of the blowup carry the
chart at `a` to the chart at the restriction of `a`.

## Main results

* `Stacks.Blowup.sheafRestrict_mem_ideal`: the restriction of a section of `ℐ(V)` lies in `ℐ(U)`.
* `Stacks.Blowup.reesRestrict_reesDegOne`: `Stacks.Blowup.reesRestrict` carries
  `Stacks.Blowup.reesDegOne` of a section to that of its restriction.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial

universe u

namespace Stacks.Blowup

variable {S : Scheme.{u}} (ℐ : S.IdealSheafData)

/-- The restriction of a section of `ℐ(V)` to a smaller affine open is a section of `ℐ(U)`. -/
theorem sheafRestrict_mem_ideal {U V : S.affineOpens} (h : U ≤ V) (a : ℐ.ideal V) :
    (sheafRestrict h).hom (a : Γ(S, V.1)) ∈ ℐ.ideal U := by
  rw [← ℐ.map_ideal h]
  exact Ideal.mem_map_of_mem _ a.2

/-- The restriction homomorphism of Rees algebras carries the degree-one element of a section to
the degree-one element of its restriction. -/
theorem reesRestrict_reesDegOne {U V : S.affineOpens} (h : U ≤ V) (a : ℐ.ideal V) :
    reesRestrict ℐ h (reesDegOne (ℐ.ideal V) a.2)
      = reesDegOne (ℐ.ideal U) (sheafRestrict_mem_ideal ℐ h a) :=
  Subtype.ext (by rw [coe_reesRestrict, coe_reesDegOne, coe_reesDegOne, map_monomial])

end Stacks.Blowup

end
