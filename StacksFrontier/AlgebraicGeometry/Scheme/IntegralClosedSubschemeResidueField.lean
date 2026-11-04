module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# The function field of an integral closed subscheme is a residue field of the ambient scheme

Let `i : Z ⟶ X` be a closed immersion with `Z` integral and let `η` be the generic point of
`Z`. The stalk map `𝒪_{X, i η} ⟶ 𝒪_{Z, η}` is surjective onto a field, so its kernel is the
maximal ideal and it exhibits the function field of `Z` as the residue field of `X` at `i η`.

## Main results

* `AlgebraicGeometry.ker_stalkMap_genericPoint_eq_maximalIdeal`: the kernel is the maximal
  ideal.
* `AlgebraicGeometry.residueFieldEquivFunctionField`: the resulting isomorphism of fields.
* `AlgebraicGeometry.residueFieldEquivFunctionField_residue`: it carries the residue map to the
  stalk map.

## Implementation notes

The ambient scheme is arbitrary; only `Z` is assumed integral. For an integral effective
Cartier divisor this says that the local ring of the divisor at its generic point is the
residue field of the ambient local ring there, which is the point at which the quotient in
[Stacks, Tag 0B3T] becomes a vector space over the residue field.

**No `@[stacks]` attribute.** This is not an assertion of a tag.

## References

* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Z : Scheme.{u}} [IsIntegral Z] (i : Z ⟶ X) [IsClosedImmersion i]

/-- **The kernel of the stalk map of a closed immersion from an integral scheme at the generic
point is the maximal ideal.** The stalk of `Z` there is its function field, so the kernel is a
maximal ideal of a local ring. -/
theorem ker_stalkMap_genericPoint_eq_maximalIdeal :
    RingHom.ker (i.stalkMap (_root_.genericPoint (Z : Type u))).hom =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (i (_root_.genericPoint (Z : Type u)))) := by
  have hsurj : Function.Surjective (i.stalkMap (_root_.genericPoint (Z : Type u))).hom :=
    i.stalkMap_surjective _
  have hfield : IsField (Z.presheaf.stalk (_root_.genericPoint (Z : Type u))) :=
    Field.toIsField Z.functionField
  have hbot : (⊥ : Ideal (Z.presheaf.stalk (_root_.genericPoint (Z : Type u)))).IsMaximal := by
    rw [← IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield]
    exact IsLocalRing.maximalIdeal.isMaximal _
  exact IsLocalRing.eq_maximalIdeal
    (Ideal.comap_isMaximal_of_surjective _ hsurj (K := ⊥) (H := hbot))

/-- **The function field of an integral closed subscheme is the residue field of the ambient
scheme at the image of the generic point.** -/
noncomputable def residueFieldEquivFunctionField :
    X.residueField (i (_root_.genericPoint (Z : Type u))) ≃+* Z.functionField :=
  (Ideal.quotEquivOfEq (ker_stalkMap_genericPoint_eq_maximalIdeal i).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (i.stalkMap_surjective (_root_.genericPoint (Z : Type u))))

/-- The isomorphism carries the residue map of `X` to the stalk map of `i`. -/
@[simp] theorem residueFieldEquivFunctionField_residue
    (a : X.presheaf.stalk (i (_root_.genericPoint (Z : Type u)))) :
    residueFieldEquivFunctionField i
        ((X.residue (i (_root_.genericPoint (Z : Type u)))).hom a) =
      (i.stalkMap (_root_.genericPoint (Z : Type u))).hom a := rfl

end AlgebraicGeometry

end
