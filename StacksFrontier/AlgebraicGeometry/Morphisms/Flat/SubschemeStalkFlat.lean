module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.TestModuleStalk
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat

/-!
# Flatness over the base of a closed subscheme, read at a point

Let `p : W ⟶ S` be a morphism of schemes and let `Z ⊆ W` be the closed subscheme cut out by an
ideal sheaf `ℐ`. The local ring of `Z` at a point `ζ` is `𝒪_{W,z} ⧸ ℐ_z` for `z` the image of
`ζ` (`AlgebraicGeometry.IdealSheafData.subschemeStalkQuotEquiv`), so `Z ⟶ S` is flat at `ζ`
exactly when that quotient is flat over `𝒪_{S, p z}`.

This is the shape in which the local analysis of a deformation problem — which produces a
regular sequence in `𝒪_{W,z}` generating `ℐ_z` and the flatness of the quotient it cuts out,
as in [Stacks, Tag 0G0N] — is handed to a statement about the morphism `Z ⟶ S`.

## Main results

* `AlgebraicGeometry.IdealSheafData.isFlatAt_subschemeι_comp_iff`: `Z ⟶ S` is flat at `ζ` if and
  only if the composite `𝒪_{S, p z} ⟶ 𝒪_{W,z} ⟶ 𝒪_{W,z} ⧸ ℐ_z` is a flat ring map.

## Implementation notes

`AlgebraicGeometry.IsFlatAt` is flatness of the stalk map as a `RingHom`, and the stalk map of a
composite factors (`AlgebraicGeometry.Scheme.Hom.stalkMap_comp`), so the statement is about the
ring map `𝒪_{S, p z} ⟶ 𝒪_{Z, ζ}`. The quotient identification is a ring *isomorphism* under
which that map becomes `𝒪_{S, p z} ⟶ 𝒪_{W,z} ⧸ ℐ_z`, and flatness is insensitive to
postcomposition with a bijection (`RingHom.Flat.comp_iff_of_bijective_left`); no module has to be
transported.

## References

* [Stacks Project, Tag 0G0N](https://stacks.math.columbia.edu/tag/0G0N)
* [Stacks Project, Tag 0G0R](https://stacks.math.columbia.edu/tag/0G0R)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IdealSheafData

variable {W S : Scheme.{u}} (p : W ⟶ S) (J : W.IdealSheafData) (ζ : J.subscheme)

/-- The map of local rings induced by the closed immersion of the subscheme is the quotient map,
read through `AlgebraicGeometry.IdealSheafData.subschemeStalkQuotEquiv`. -/
theorem subschemeStalkQuotEquiv_comp_mk :
    (subschemeStalkQuotEquiv J ζ : (W.presheaf.stalk (J.subschemeι ζ) ⧸
          IdealSheafData.stalk J (J.subschemeι ζ)) →+* J.subscheme.presheaf.stalk ζ).comp
        (Ideal.Quotient.mk (IdealSheafData.stalk J (J.subschemeι ζ))) =
      (J.subschemeι.stalkMap ζ).hom :=
  RingHom.ext fun a => subschemeStalkQuotEquiv_mk J ζ a

/-- **A closed subscheme is flat over the base at a point exactly when the quotient of the local
ring by the stalk of its ideal sheaf is.** -/
theorem isFlatAt_subschemeι_comp_iff :
    AlgebraicGeometry.IsFlatAt (J.subschemeι ≫ p).toLRSHom.toShHom ζ ↔
      RingHom.Flat ((Ideal.Quotient.mk (IdealSheafData.stalk J (J.subschemeι ζ))).comp
        (p.stalkMap (J.subschemeι ζ)).hom) := by
  have hcomp : ((J.subschemeι ≫ p).stalkMap ζ).hom =
      (J.subschemeι.stalkMap ζ).hom.comp (p.stalkMap (J.subschemeι ζ)).hom := by
    rw [Scheme.Hom.stalkMap_comp]
    rfl
  have hfac : ((J.subschemeι ≫ p).stalkMap ζ).hom =
      (subschemeStalkQuotEquiv J ζ : (W.presheaf.stalk (J.subschemeι ζ) ⧸
          IdealSheafData.stalk J (J.subschemeι ζ)) →+* J.subscheme.presheaf.stalk ζ).comp
        ((Ideal.Quotient.mk (IdealSheafData.stalk J (J.subschemeι ζ))).comp
          (p.stalkMap (J.subschemeι ζ)).hom) := by
    rw [hcomp, ← subschemeStalkQuotEquiv_comp_mk J ζ, RingHom.comp_assoc]
  show RingHom.Flat ((J.subschemeι ≫ p).stalkMap ζ).hom ↔ _
  rw [hfac]
  exact RingHom.Flat.comp_iff_of_bijective_left (subschemeStalkQuotEquiv J ζ).bijective

end AlgebraicGeometry.IdealSheafData

end
