module

public import StacksFrontier.AlgebraicGeometry.Blowup.ClassifyingMorphism
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.ZeroSectionCartier
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceVectorBundle
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsComplete
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.ConormalLineBundle
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalBundle
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalConeNormalBundleIso

/-!
# The zero section of the normal cone of an effective Cartier divisor

For an effective Cartier divisor `D ⊆ X` the normal cone `C_DX` is a line bundle over `D`, and
[Stacks, Tag 0FEB] writes `o : D ⟶ C_DX` for its zero section. This file puts `o` on the normal
**cone**.

## Main definitions

* `Stacks.Conormal.totalSpaceIsoNormalCone`: **the total space of the conormal line-bundle
  situation is the normal cone** `C_DX`.
* `Stacks.Conormal.normalConeZeroSection`: **the zero section `o : D ⟶ C_DX`** of [Stacks,
  Tag 0FEB], the zero section of that situation read on the normal cone.

## Main results

* `Stacks.Conormal.normalConeZeroSection_comp_normalConeToBase`: **`o` splits the projection**
  `C_DX ⟶ D`, which is what makes it a section.
* `Stacks.Conormal.isEffectiveCartierDivisor_ker_normalConeZeroSection`: **the image `o(D)` is an
  effective Cartier divisor on `C_DX`**, which is what makes the bivariant class
  `o^* \in A^1(D ⟶ C_DX)` of [Stacks, Tag 0B79] exist.

## How the transport is assembled

`Stacks.Conormal.conormalZeroSection` is the zero section of
`Stacks.Conormal.conormalSituation`, hence a morphism into that situation's *total space*, and
the implementation notes of `StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.ConormalLineBundle`
left the identification of that total space with the normal cone to the consumer. The two inputs
are composed here, in the direction that lands on the cone:

* `Stacks.LineBundle.Situation.totalSpaceIsoVectorBundle` identifies the total space with
  `Scheme.Modules.vectorBundle D.subscheme (conormalSheafDegreeOne D.subschemeι)`,
  which is `Stacks.Conormal.normalBundle D.subschemeι` on the nose; and
* `Stacks.Conormal.isIso_normalConeToNormalBundle_of_isEffectiveCartierDivisor` inverts the
  Tag 0637 morphism `C_DX ⟶ N_DX`, which is an isomorphism exactly because `D` is an effective
  Cartier divisor.

Both inputs are isomorphisms over `D`, by
`Stacks.LineBundle.Situation.totalSpaceIsoVectorBundle_hom_comp_vectorBundleToBase` and
`Stacks.Conormal.normalConeToNormalBundle_toBase`, so the composite is too, and the section
property of `o` transports with it.

## The divisor `o(D)` and the bivariant class `o^*`

[Stacks, Tag 0FEB] is stated with the bivariant class `o^* \in A^1(D \to C_DX)` of [Stacks,
Tag 0B79], which exists because `o(D)` is an effective Cartier divisor on `C_DX`. That is proved
here as `Stacks.Conormal.isEffectiveCartierDivisor_ker_normalConeZeroSection`, by carrying
`Stacks.LineBundle.Situation.isEffectiveCartierDivisor_ker_zeroSection` across the isomorphism
above: `Stacks.Blowup.isEffectiveCartierDivisor_comap_of_isOpenImmersion` moves an effective
Cartier divisor along an open immersion, an isomorphism is one, and
`AlgebraicGeometry.Scheme.IdealSheafData.comap_map_of_isIso` together with `comap_inv_comap` and
`comap_injective` identify the direct image of the ideal along the isomorphism with its inverse
image along the inverse.

The *existence* of that bivariant class — the axioms of Definition 0B76 checked for the cap
operation `Stacks.Chow.gysinBivariantCap`, as the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Basic` record — is not available, and nothing below
asserts it. The statement of [Stacks, Tag 0FEB] does not depend on it:
`Stacks.Chow.gysinBivariantCap` is unconditional and
`Stacks.Chow.IsGysinBivariantClass` pins the class to it, so the identity of the tag can be
written at the cap operation with no hypothesis asserting that the class exists. That is
`Stacks.Chow.gysinBivariantCap_fundamentalChowClass_normalCone` of
`StacksFrontier.AlgebraicGeometry.Chow.NormalConeZeroSectionGysin`, which takes the divisor
`o(D)` from the theorem above and presents it as a zero scheme by the canonical
`Stacks.Divisors.divisorSheaf`.

## References

* [Stacks Project, Tag 0FEB](https://stacks.math.columbia.edu/tag/0FEB)
* [Stacks Project, Tag 0637](https://stacks.math.columbia.edu/tag/0637)
* [Stacks Project, Tag 01WR](https://stacks.math.columbia.edu/tag/01WR)
* [Stacks Project, Tag 0B79](https://stacks.math.columbia.edu/tag/0B79)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Conormal

variable {X : Scheme.{u}} (D : X.IdealSheafData)
  [Stacks.Divisors.IsEffectiveCartierDivisor D]
  [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent (normalBundleAlgebra D.subschemeι)]
  [(conormalAlgebraSheaf D.subschemeι).IsQuasicoherent]

/-- **The normal cone of an effective Cartier divisor is its normal bundle**, i.e. the Tag 0637
morphism `C_DX ⟶ N_DX` read as an isomorphism. The inversion is
`Stacks.Conormal.isIso_normalConeToNormalBundle_of_isEffectiveCartierDivisor`. -/
def normalConeIsoNormalBundle : normalCone D.subschemeι ≅ normalBundle D.subschemeι :=
  @asIso _ _ _ _ (normalConeToNormalBundle D.subschemeι)
    (isIso_normalConeToNormalBundle_of_isEffectiveCartierDivisor D)

/-- The forward map of `Stacks.Conormal.normalConeIsoNormalBundle` is the Tag 0637 morphism. -/
theorem normalConeIsoNormalBundle_hom :
    (normalConeIsoNormalBundle D).hom = normalConeToNormalBundle D.subschemeι := rfl

/-- `Stacks.Conormal.normalConeIsoNormalBundle` is an isomorphism over `D`: this is
`Stacks.Conormal.normalConeToNormalBundle_normalBundleToBase`. -/
theorem normalConeIsoNormalBundle_hom_comp_normalBundleToBase :
    (normalConeIsoNormalBundle D).hom ≫ normalBundleToBase D.subschemeι =
      normalConeToBase D.subschemeι :=
  normalConeToNormalBundle_normalBundleToBase D.subschemeι

/-- The inverse of `Stacks.Conormal.normalConeIsoNormalBundle` is an isomorphism over `D` too. -/
theorem normalConeIsoNormalBundle_inv_comp_normalConeToBase :
    (normalConeIsoNormalBundle D).inv ≫ normalConeToBase D.subschemeι =
      normalBundleToBase D.subschemeι :=
  (congrArg ((normalConeIsoNormalBundle D).inv ≫ ·)
      (normalConeIsoNormalBundle_hom_comp_normalBundleToBase D).symm).trans
    (Iso.inv_hom_id_assoc _ _)

/-- **The total space of the conormal line-bundle situation of an effective Cartier divisor is
the normal cone `C_DX`.** It is `Stacks.LineBundle.Situation.totalSpaceIsoVectorBundle`, which
lands on `N_DX`, followed by the inverse of `Stacks.Conormal.normalConeIsoNormalBundle`. -/
def totalSpaceIsoNormalCone :
    (conormalSituation D).totalSpace ≅ normalCone D.subschemeι :=
  (conormalSituation D).totalSpaceIsoVectorBundle ≪≫ (normalConeIsoNormalBundle D).symm

/-- **The identification of the total space with the normal cone is an isomorphism over `D`**:
it carries the projection `C_DX ⟶ D` of the normal cone to the projection of the total space. -/
theorem totalSpaceIsoNormalCone_hom_comp_normalConeToBase :
    (totalSpaceIsoNormalCone D).hom ≫ normalConeToBase D.subschemeι =
      (conormalSituation D).totalSpaceToBase :=
  (Category.assoc (conormalSituation D).totalSpaceIsoVectorBundle.hom
        (normalConeIsoNormalBundle D).inv (normalConeToBase D.subschemeι)).trans
    ((congrArg ((conormalSituation D).totalSpaceIsoVectorBundle.hom ≫ ·)
          (normalConeIsoNormalBundle_inv_comp_normalConeToBase D)).trans
      (conormalSituation D).totalSpaceIsoVectorBundle_hom_comp_vectorBundleToBase)

/-- **The zero section `o : D ⟶ C_DX` of the normal cone of an effective Cartier divisor**, the
morphism written `o` in [Stacks, Tag 0FEB]. It is `Stacks.Conormal.conormalZeroSection`, the
zero section of the conormal line-bundle situation, read on the normal cone through
`Stacks.Conormal.totalSpaceIsoNormalCone`. -/
def normalConeZeroSection : D.subscheme ⟶ normalCone D.subschemeι :=
  conormalZeroSection D ≫ (totalSpaceIsoNormalCone D).hom

/-- **The zero section splits the projection of the normal cone**: `o` followed by
`C_DX ⟶ D` is the identity of `D`, which is the section property [Stacks, Tag 0FEB] uses when it
calls `o` a section. -/
theorem normalConeZeroSection_comp_normalConeToBase :
    normalConeZeroSection D ≫ normalConeToBase D.subschemeι = 𝟙 D.subscheme :=
  (Category.assoc (conormalZeroSection D) (totalSpaceIsoNormalCone D).hom
        (normalConeToBase D.subschemeι)).trans
    ((congrArg (conormalZeroSection D ≫ ·)
          (totalSpaceIsoNormalCone_hom_comp_normalConeToBase D)).trans
      (conormalSituation D).zeroSection_comp_totalSpaceToBase)

/-! ### The divisor cut out by the zero section -/

/-- The zero section of the normal cone is a closed immersion, being the zero section of the
total space followed by an isomorphism. -/
instance isClosedImmersion_normalConeZeroSection :
    IsClosedImmersion (normalConeZeroSection D) :=
  haveI : IsClosedImmersion (conormalZeroSection D) :=
    (conormalSituation D).isClosedImmersion_zeroSection
  inferInstanceAs
    (IsClosedImmersion (conormalZeroSection D ≫ (totalSpaceIsoNormalCone D).hom))

/-- **The ideal of `o(D)` on the normal cone is the direct image of the ideal of `o(D)` on the
total space** along `Stacks.Conormal.totalSpaceIsoNormalCone`. -/
theorem ker_normalConeZeroSection :
    (normalConeZeroSection D).ker =
      (conormalSituation D).zeroSection.ker.map (totalSpaceIsoNormalCone D).hom :=
  Scheme.Hom.ker_comp _ _

/-- The ideal of `o(D)` on the normal cone is also the inverse image, along the inverse
isomorphism, of the ideal of `o(D)` on the total space. -/
theorem ker_normalConeZeroSection_eq_comap :
    (normalConeZeroSection D).ker =
      (conormalSituation D).zeroSection.ker.comap (inv (totalSpaceIsoNormalCone D).hom) :=
  Scheme.IdealSheafData.comap_injective (totalSpaceIsoNormalCone D).hom
    (((congrArg (fun I : (normalCone D.subschemeι).IdealSheafData =>
            I.comap (totalSpaceIsoNormalCone D).hom) (ker_normalConeZeroSection D)).trans
          (Scheme.IdealSheafData.comap_map_of_isIso (totalSpaceIsoNormalCone D).hom _)).trans
      (Scheme.IdealSheafData.comap_inv_comap (totalSpaceIsoNormalCone D).hom _).symm)

/-- **The image `o(D)` of the zero section is an effective Cartier divisor on the normal cone**
([Stacks, Tag 01WR]). This is what makes the bivariant Gysin class
`o^* ∈ A^1(D ⟶ C_DX)` of [Stacks, Tag 0B79] — the class [Stacks, Tag 0FEB] is stated with —
exist. It is `Stacks.LineBundle.Situation.isEffectiveCartierDivisor_ker_zeroSection` carried
across `Stacks.Conormal.totalSpaceIsoNormalCone`, an isomorphism and hence an open immersion. -/
theorem isEffectiveCartierDivisor_ker_normalConeZeroSection :
    Stacks.Divisors.IsEffectiveCartierDivisor (normalConeZeroSection D).ker :=
  (ker_normalConeZeroSection_eq_comap D) ▸
    Stacks.Blowup.isEffectiveCartierDivisor_comap_of_isOpenImmersion _
      (conormalSituation D).isEffectiveCartierDivisor_ker_zeroSection
      (inv (totalSpaceIsoNormalCone D).hom)

end Stacks.Conormal

end
