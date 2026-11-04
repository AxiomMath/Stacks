module

public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleDominating
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsComplete
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierDescent.StalkBaseChange
public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafComapMul

/-!
# Transporting a blowup computation between the two constructions of the blowup

There are two constructions of the blowup of a scheme `S` in a quasi-coherent ideal sheaf `ℐ`,
both relative `Proj`s of the Rees algebra but glued from different local data:
`Stacks.Blowup.blowUp ℐ` and `AlgebraicGeometry.blowUp ℐ` ([Stacks, Tag 01OG]). They are
canonically isomorphic over `S` by `Stacks.Blowup.blowUpIso`.

Writing `e := Stacks.Blowup.blowUpIso ℐ`, this module shows that inverse image along `e.hom`
carries each piece of data on `AlgebraicGeometry.blowUp ℐ` to the corresponding piece on
`Stacks.Blowup.blowUp ℐ`: inverse-image ideal sheaves of the base, the exceptional ideal, products
and powers, supports, stalk colengths, and regularity and dimension of the local rings; and that
an equality or an inequality of ideal sheaves may be checked after this transport.

## Main results

* `Stacks.ResolutionOfSurfaces.CartierDescent.comap_blowUpIso_hom_comap_blowUpToBase`: the inverse
  image of an ideal sheaf of `S` along one blowup morphism is carried to its inverse image along
  the other.
* `Stacks.ResolutionOfSurfaces.CartierDescent.comap_blowUpIso_hom_exceptionalIdeal`: the two
  exceptional ideal sheaves correspond.
* `Stacks.ResolutionOfSurfaces.CartierDescent.eq_of_comap_blowUpIso_hom_eq` and
  `Stacks.ResolutionOfSurfaces.CartierDescent.le_of_comap_blowUpIso_hom_le`: an equality or an
  inequality of ideal sheaves on `AlgebraicGeometry.blowUp ℐ` may be checked after transport.
* `Stacks.ResolutionOfSurfaces.CartierDescent.comap_blowUpIso_hom_mul` and
  `Stacks.ResolutionOfSurfaces.CartierDescent.comap_blowUpIso_hom_pow`: the transport is
  multiplicative.
* `Stacks.ResolutionOfSurfaces.CartierDescent.support_comap_blowUpIso_hom`: supports correspond.
* `Stacks.ResolutionOfSurfaces.CartierDescent.length_stalk_quotient_comap_blowUpIso_hom`: stalk
  colengths correspond.
* `Stacks.ResolutionOfSurfaces.CartierDescent.isRegularLocalRing_stalk_iff` and
  `Stacks.ResolutionOfSurfaces.CartierDescent.ringKrullDim_stalk_eq`: regularity and Krull
  dimension of the local rings correspond.

## Implementation notes

The stalk statements all factor through
`Stacks.ResolutionOfSurfaces.CartierDescent.stalkRingEquivBlowUpIso`, the isomorphism of local
rings induced by `Stacks.Blowup.blowUpIso`, which points from the local ring of
`AlgebraicGeometry.blowUp ℐ` to that of `Stacks.Blowup.blowUp ℐ`, following the direction of
`AlgebraicGeometry.Scheme.Hom.stalkMap`.

No `@[stacks]` attribute is attached to anything here. Tag 01OG is already carried by the two
constructions themselves and by their exceptional ideal sheaves, and tags 0AGT and 0AHH are
statements about surfaces and colengths which this module only makes expressible; what is proved
below is the comparison of two models of one object, not a formalization of a tag.

## References

* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
* [Stacks Project, Tag 0AHH](https://stacks.math.columbia.edu/tag/0AHH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.ResolutionOfSurfaces.CartierDescent

variable {S : Scheme.{u}} (ℐ : S.IdealSheafData)

/-! ### Inverse-image ideal sheaves of the base -/

/-- **Inverse images from the base correspond under the comparison isomorphism.** For an ideal
sheaf `J` on `S`, transporting its inverse image along `AlgebraicGeometry.blowUpToBase ℐ` by
`Stacks.Blowup.blowUpIso ℐ` gives its inverse image along `Stacks.Blowup.blowUpToBase ℐ`. -/
theorem comap_blowUpIso_hom_comap_blowUpToBase (J : S.IdealSheafData) :
    (J.comap (AlgebraicGeometry.blowUpToBase ℐ)).comap (Stacks.Blowup.blowUpIso ℐ).hom =
      J.comap (Stacks.Blowup.blowUpToBase ℐ) := by
  rw [← Scheme.IdealSheafData.comap_comp, Stacks.Blowup.blowUpIso_hom_comp]

/-- **The two exceptional ideal sheaves correspond under the comparison isomorphism.** Both are
the inverse image of the centre `ℐ` along the respective blowup morphism, so this is the case
`J = ℐ` of `Stacks.ResolutionOfSurfaces.CartierDescent.comap_blowUpIso_hom_comap_blowUpToBase`. -/
theorem comap_blowUpIso_hom_exceptionalIdeal :
    (AlgebraicGeometry.exceptionalIdeal ℐ).comap (Stacks.Blowup.blowUpIso ℐ).hom =
      Stacks.Blowup.exceptionalIdeal ℐ :=
  comap_blowUpIso_hom_comap_blowUpToBase ℐ ℐ

/-! ### Transporting equalities and inequalities back -/

/-- **An equality of ideal sheaves on `AlgebraicGeometry.blowUp ℐ` may be checked after
transport.** Inverse image along an isomorphism of schemes is injective. -/
theorem eq_of_comap_blowUpIso_hom_eq {I J : (AlgebraicGeometry.blowUp ℐ).IdealSheafData}
    (h : I.comap (Stacks.Blowup.blowUpIso ℐ).hom = J.comap (Stacks.Blowup.blowUpIso ℐ).hom) :
    I = J :=
  Scheme.IdealSheafData.comap_injective (Stacks.Blowup.blowUpIso ℐ).hom h

/-- **An inequality of ideal sheaves on `AlgebraicGeometry.blowUp ℐ` may be checked after
transport.** Inverse image along an isomorphism of schemes is monotone, and is inverted by
inverse image along the inverse isomorphism. -/
theorem le_of_comap_blowUpIso_hom_le {I J : (AlgebraicGeometry.blowUp ℐ).IdealSheafData}
    (h : I.comap (Stacks.Blowup.blowUpIso ℐ).hom ≤ J.comap (Stacks.Blowup.blowUpIso ℐ).hom) :
    I ≤ J := by
  have h' : (I.comap (Stacks.Blowup.blowUpIso ℐ).hom).comap
        (inv (Stacks.Blowup.blowUpIso ℐ).hom) ≤
      (J.comap (Stacks.Blowup.blowUpIso ℐ).hom).comap (inv (Stacks.Blowup.blowUpIso ℐ).hom) :=
    Scheme.IdealSheafData.comap_mono _ h
  rwa [Scheme.IdealSheafData.comap_comap_inv, Scheme.IdealSheafData.comap_comap_inv] at h'

/-- **Transport along the comparison isomorphism reflects inequalities as well as implying
them**: an inequality of ideal sheaves on `AlgebraicGeometry.blowUp ℐ` holds exactly when it
holds after transport. -/
theorem comap_blowUpIso_hom_le_comap_blowUpIso_hom_iff
    {I J : (AlgebraicGeometry.blowUp ℐ).IdealSheafData} :
    I.comap (Stacks.Blowup.blowUpIso ℐ).hom ≤ J.comap (Stacks.Blowup.blowUpIso ℐ).hom ↔ I ≤ J :=
  ⟨le_of_comap_blowUpIso_hom_le ℐ, fun h ↦ Scheme.IdealSheafData.comap_mono _ h⟩

/-! ### Products and powers -/

/-- **The transport is multiplicative**: the specialisation of `Stacks.IdealSheaf.comap_mul` to
the comparison isomorphism of the two blowups. -/
theorem comap_blowUpIso_hom_mul (I J : (AlgebraicGeometry.blowUp ℐ).IdealSheafData) :
    (I * J).comap (Stacks.Blowup.blowUpIso ℐ).hom =
      I.comap (Stacks.Blowup.blowUpIso ℐ).hom * J.comap (Stacks.Blowup.blowUpIso ℐ).hom :=
  Stacks.IdealSheaf.comap_mul I J (Stacks.Blowup.blowUpIso ℐ).hom

/-- **The transport commutes with powers**: the specialisation of `Stacks.IdealSheaf.comap_pow` to
the comparison isomorphism of the two blowups. -/
theorem comap_blowUpIso_hom_pow (I : (AlgebraicGeometry.blowUp ℐ).IdealSheafData) (n : ℕ) :
    (I ^ n).comap (Stacks.Blowup.blowUpIso ℐ).hom = I.comap (Stacks.Blowup.blowUpIso ℐ).hom ^ n :=
  Stacks.IdealSheaf.comap_pow I (Stacks.Blowup.blowUpIso ℐ).hom n

/-- **A power of the exceptional ideal corresponds to the same power of the other exceptional
ideal.** -/
theorem comap_blowUpIso_hom_exceptionalIdeal_pow (n : ℕ) :
    (AlgebraicGeometry.exceptionalIdeal ℐ ^ n).comap (Stacks.Blowup.blowUpIso ℐ).hom =
      Stacks.Blowup.exceptionalIdeal ℐ ^ n := by
  rw [comap_blowUpIso_hom_pow, comap_blowUpIso_hom_exceptionalIdeal]

/-! ### Supports -/

/-- **Supports correspond under the comparison isomorphism**: the support of a transported ideal
sheaf is the preimage of its support under the homeomorphism of underlying spaces. -/
theorem support_comap_blowUpIso_hom (I : (AlgebraicGeometry.blowUp ℐ).IdealSheafData) :
    ((I.comap (Stacks.Blowup.blowUpIso ℐ).hom).support : Set (Stacks.Blowup.blowUp ℐ)) =
      (Stacks.Blowup.blowUpIso ℐ).hom.base ⁻¹'
        (I.support : Set (AlgebraicGeometry.blowUp ℐ)) := by
  rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage]

/-! ### Local rings -/

/-- The comparison isomorphism of the two blowups is an isomorphism on every local ring, being an
isomorphism of schemes. -/
theorem isIso_stalkMap_blowUpIso_hom (z : Stacks.Blowup.blowUp ℐ) :
    IsIso ((Stacks.Blowup.blowUpIso ℐ).hom.stalkMap z) :=
  ((AlgebraicGeometry.isIso_iff_isIso_stalkMap (Stacks.Blowup.blowUpIso ℐ).hom).mp
    inferInstance).2 z

/-- **The isomorphism of local rings induced by the comparison isomorphism of the two blowups.**
It points from the local ring of `AlgebraicGeometry.blowUp ℐ` at the image point to the local ring
of `Stacks.Blowup.blowUp ℐ` at `z`, following the direction of
`AlgebraicGeometry.Scheme.Hom.stalkMap`. -/
def stalkRingEquivBlowUpIso (z : Stacks.Blowup.blowUp ℐ) :
    (AlgebraicGeometry.blowUp ℐ).presheaf.stalk ((Stacks.Blowup.blowUpIso ℐ).hom.base z) ≃+*
      (Stacks.Blowup.blowUp ℐ).presheaf.stalk z :=
  have := isIso_stalkMap_blowUpIso_hom ℐ z
  (asIso ((Stacks.Blowup.blowUpIso ℐ).hom.stalkMap z)).commRingCatIsoToRingEquiv

/-- **Stalk colengths correspond under the comparison isomorphism.** The colength at `z` of a
transported ideal sheaf is its colength at the image of `z`; this is
`Stacks.ResolutionOfSurfaces.CartierDescent.length_stalk_quotient_comap_of_isIso_stalkMap` applied
to the comparison isomorphism. -/
theorem length_stalk_quotient_comap_blowUpIso_hom
    (I : (AlgebraicGeometry.blowUp ℐ).IdealSheafData) (z : Stacks.Blowup.blowUp ℐ) :
    Module.length ((Stacks.Blowup.blowUp ℐ).presheaf.stalk z)
        ((Stacks.Blowup.blowUp ℐ).presheaf.stalk z ⧸
          AlgebraicGeometry.IdealSheafData.stalk (I.comap (Stacks.Blowup.blowUpIso ℐ).hom) z) =
      Module.length ((AlgebraicGeometry.blowUp ℐ).presheaf.stalk
            ((Stacks.Blowup.blowUpIso ℐ).hom.base z))
        ((AlgebraicGeometry.blowUp ℐ).presheaf.stalk ((Stacks.Blowup.blowUpIso ℐ).hom.base z) ⧸
          AlgebraicGeometry.IdealSheafData.stalk I ((Stacks.Blowup.blowUpIso ℐ).hom.base z)) :=
  length_stalk_quotient_comap_of_isIso_stalkMap (Stacks.Blowup.blowUpIso ℐ).hom I z
    (isIso_stalkMap_blowUpIso_hom ℐ z)

/-- **Regularity of the local rings corresponds under the comparison isomorphism**, the two local
rings being isomorphic. -/
theorem isRegularLocalRing_stalk_iff (z : Stacks.Blowup.blowUp ℐ) :
    IsRegularLocalRing ((Stacks.Blowup.blowUp ℐ).presheaf.stalk z) ↔
      IsRegularLocalRing ((AlgebraicGeometry.blowUp ℐ).presheaf.stalk
        ((Stacks.Blowup.blowUpIso ℐ).hom.base z)) :=
  ⟨fun _ ↦ .of_ringEquiv (stalkRingEquivBlowUpIso ℐ z).symm,
    fun _ ↦ .of_ringEquiv (stalkRingEquivBlowUpIso ℐ z)⟩

/-- **The Krull dimensions of the local rings agree under the comparison isomorphism**, the two
local rings being isomorphic. -/
theorem ringKrullDim_stalk_eq (z : Stacks.Blowup.blowUp ℐ) :
    ringKrullDim ((Stacks.Blowup.blowUp ℐ).presheaf.stalk z) =
      ringKrullDim ((AlgebraicGeometry.blowUp ℐ).presheaf.stalk
        ((Stacks.Blowup.blowUpIso ℐ).hom.base z)) :=
  (ringKrullDim_eq_of_ringEquiv (stalkRingEquivBlowUpIso ℐ z)).symm

end Stacks.ResolutionOfSurfaces.CartierDescent

end
