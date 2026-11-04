module

public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupFormsDirectImage

/-!
# The exceptional divisor of the standard coordinate blowup

Fix a ring `R`, put `S = Spec(R)` and fix `0 ≤ m` and `1 ≤ n`. Let

`i : Z = 𝐀^m_S ⟶ 𝐀^{m+n}_S = X`

be the coordinate closed immersion, let `b : L ⟶ X` be the blowing up of `X` along `Z`, let
`E ⊆ L` be the exceptional divisor and let `P = 𝐏^{n-1}_Z` with its projection `p : P ⟶ Z`.
This file relates `E` to `Z` and to `P`.

The first statement holds for every `n`: the exceptional divisor is the scheme-theoretic inverse
image `b^{-1}(Z) = L ×_X Z` of the centre, so it comes with a projection `E ⟶ Z` fitting into a
cartesian square

```
E ⟶ L
↓     ↓ b
Z ⟶ X
    i
```

The second holds for `n = 1`: there `b` is an isomorphism, so the projection `E ⟶ Z` is an
isomorphism, and `P = 𝐏⁰_Z` is the centre as well, which gives

`P ≅ E` together with a closed immersion `P ⟶ L` satisfying `P ⟶ L ⟶ X = p ≫ i`.

## Main definitions

* `Stacks.DeRham.coordinateExceptionalScheme`, `Stacks.DeRham.coordinateExceptionalι`: the
  exceptional divisor `E` of the standard coordinate blowup, as a scheme, and its closed
  immersion `E ⟶ L`.
* `Stacks.DeRham.coordinateExceptionalToCentre`: the projection `E ⟶ Z` onto the centre.
* `Stacks.DeRham.coordinateBundleExceptionalIso`: **for `n = 1`, the identification `P ≅ E`.**
* `Stacks.DeRham.coordinateBundleToBlowup`: for `n = 1`, the resulting closed immersion
  `P ⟶ L`.

## Main results

* `Stacks.DeRham.coordinateExceptionalι_comp_blowupToAmbient`: the square above commutes, for
  every `n`.
* `Stacks.DeRham.isPullback_coordinateExceptionalι`: **the square above is cartesian**, for every
  `n`: `E = L ×_X Z`.
* `Stacks.DeRham.coordinateBundleExceptionalIso_hom_comp_toCentre` and
  `Stacks.DeRham.coordinateBundleToBlowup_comp_blowupToAmbient`: for `n = 1` the identification
  `P ≅ E` is compatible with the projections to the centre, and the closed immersion `P ⟶ L` it
  produces satisfies `P ⟶ L ⟶ X = p ≫ i`.

## References

* [Stacks Project, Tag 0FUR](https://stacks.math.columbia.edu/tag/0FUR)
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
* [Stacks Project, Tag 0807](https://stacks.math.columbia.edu/tag/0807)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.DeRham

attribute [local instance] Stacks.MoreMorphisms.coordinateEmbedding_isClosedImmersion

variable (R : Type u) [CommRing R] (m n : ℕ)

/-! ### The exceptional divisor as the inverse image of the centre -/

/-- The exceptional divisor `E` of the standard coordinate blowup, as a scheme. -/
abbrev coordinateExceptionalScheme : Scheme.{u} :=
  exceptionalDivisor (Stacks.MoreMorphisms.coordinateIdeal R m n)

/-- The closed immersion `E ⟶ L` of the exceptional divisor into the standard coordinate
blowup. -/
abbrev coordinateExceptionalι :
    coordinateExceptionalScheme R m n ⟶ coordinateBlowup R m n :=
  (coordinateExceptional R m n).subschemeι

namespace CoordinateExceptional

/-- The ideal sheaf of the centre is the kernel both of the coordinate closed immersion and of
the inclusion of the closed subscheme it cuts out. -/
theorem ker_coordinateEmbedding_eq :
    (Stacks.MoreMorphisms.coordinateEmbedding R m n).ker =
      (Stacks.MoreMorphisms.coordinateIdeal R m n).subschemeι.ker :=
  (Scheme.IdealSheafData.ker_subschemeι (Stacks.MoreMorphisms.coordinateIdeal R m n)).symm

/-- The comparison morphism from the closed subscheme cut out by the ideal sheaf of the centre to
the centre itself. -/
def centreFromSubscheme :
    (Stacks.MoreMorphisms.coordinateIdeal R m n).subscheme ⟶ coordinateBlowupCentre R m :=
  IsClosedImmersion.lift (Stacks.MoreMorphisms.coordinateEmbedding R m n)
    (Stacks.MoreMorphisms.coordinateIdeal R m n).subschemeι
    (ker_coordinateEmbedding_eq R m n).le

/-- The comparison morphism is a morphism over the ambient affine space: composing it with the
coordinate closed immersion recovers the inclusion of the closed subscheme. -/
@[reassoc]
theorem centreFromSubscheme_comp_coordinateEmbedding :
    centreFromSubscheme R m n ≫ Stacks.MoreMorphisms.coordinateEmbedding R m n =
      (Stacks.MoreMorphisms.coordinateIdeal R m n).subschemeι :=
  IsClosedImmersion.lift_fac _ _ _

end CoordinateExceptional

/-- The projection `E ⟶ Z` of the exceptional divisor onto the centre of the standard coordinate
blowup: the exceptional divisor is the fibre product `L ×_X Z`, and this is its second
projection, read through the identification of the closed subscheme cut out by the ideal sheaf of
the centre with the centre itself. -/
def coordinateExceptionalToCentre :
    coordinateExceptionalScheme R m n ⟶ coordinateBlowupCentre R m :=
  ((Stacks.MoreMorphisms.coordinateIdeal R m n).comapIso
      (coordinateBlowupToAmbient R m n)).hom ≫
    pullback.snd _ _ ≫ CoordinateExceptional.centreFromSubscheme R m n

/-- **The exceptional divisor lies over the centre.** The square

```
E ⟶ L
↓     ↓ b
Z ⟶ X
    i
```

commutes, for every `n`. -/
theorem coordinateExceptionalι_comp_blowupToAmbient :
    coordinateExceptionalι R m n ≫ coordinateBlowupToAmbient R m n =
      coordinateExceptionalToCentre R m n ≫
        Stacks.MoreMorphisms.coordinateEmbedding R m n := by
  rw [coordinateExceptionalToCentre, Category.assoc, Category.assoc,
    CoordinateExceptional.centreFromSubscheme_comp_coordinateEmbedding,
    show coordinateExceptionalι R m n =
        ((Stacks.MoreMorphisms.coordinateIdeal R m n).comapIso
          (coordinateBlowupToAmbient R m n)).hom ≫ pullback.fst _ _ from
      (Scheme.IdealSheafData.comapIso_hom_fst _ _).symm,
    Category.assoc, pullback.condition]

/-- **The exceptional divisor of the standard coordinate blowup is the inverse image of the
centre:** `E = L ×_X Z`, for every `n`. -/
theorem isPullback_coordinateExceptionalι :
    IsPullback (coordinateExceptionalι R m n) (coordinateExceptionalToCentre R m n)
      (coordinateBlowupToAmbient R m n)
      (Stacks.MoreMorphisms.coordinateEmbedding R m n) := by
  refine AlgebraicGeometry.isPullback_of_isClosedImmersion _ _ _ _
    (coordinateExceptionalι_comp_blowupToAmbient R m n) ?_
  rw [Scheme.IdealSheafData.ker_subschemeι]
  rfl

/-! ### The case `n = 1`: the exceptional divisor is the projective bundle -/

namespace CoordinateExceptional

open MvPolynomial Stacks.MoreMorphisms

/-- **For `n = 1` the projection `E ⟶ Z` is an isomorphism.** -/
theorem isIso_coordinateExceptionalToCentre :
    IsIso (coordinateExceptionalToCentre R m 1) :=
  (isPullback_coordinateExceptionalι R m 1).isIso_snd_of_isIso
    (isIso_coordinateBlowupToAmbient_one R m)

end CoordinateExceptional

/-- **For `n = 1`, the identification of the projective bundle of the centre with the exceptional
divisor:** `P = 𝐏^{n-1}_Z ≅ E`, the isomorphism `P ⟶ Z` onto the centre followed by the inverse
of the isomorphism `E ⟶ Z`. -/
def coordinateBundleExceptionalIso :
    coordinateBlowupBundle R m 1 ≅ coordinateExceptionalScheme R m 1 :=
  letI := isIso_coordinateBlowupBundleToCentre_of_one R m
  letI := CoordinateExceptional.isIso_coordinateExceptionalToCentre R m
  (asIso (coordinateBlowupBundleToCentre R m 1)).trans
    (asIso (coordinateExceptionalToCentre R m 1)).symm

/-- **The identification `P ≅ E` is compatible with the projections to the centre:** it carries
the projection `E ⟶ Z` to the projection `p : P ⟶ Z`. -/
theorem coordinateBundleExceptionalIso_hom_comp_toCentre :
    (coordinateBundleExceptionalIso R m).hom ≫ coordinateExceptionalToCentre R m 1 =
      coordinateBlowupBundleToCentre R m 1 := by
  have := isIso_coordinateBlowupBundleToCentre_of_one R m
  have := CoordinateExceptional.isIso_coordinateExceptionalToCentre R m
  have hhom : (coordinateBundleExceptionalIso R m).hom =
      coordinateBlowupBundleToCentre R m 1 ≫
        inv (coordinateExceptionalToCentre R m 1) := rfl
  rw [hhom, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- The closed immersion `P ⟶ L` of the projective bundle of the centre into the standard
coordinate blowup, for `n = 1`: the identification `P ≅ E` followed by the inclusion of the
exceptional divisor. -/
def coordinateBundleToBlowup :
    coordinateBlowupBundle R m 1 ⟶ coordinateBlowup R m 1 :=
  (coordinateBundleExceptionalIso R m).hom ≫ coordinateExceptionalι R m 1

/-- **For `n = 1`, the closed immersion `P ⟶ L` lies over the centre:** followed by the
blowing-up morphism `b : L ⟶ X` it is the projection `p : P ⟶ Z` followed by the coordinate
closed immersion `i : Z ⟶ X`. -/
theorem coordinateBundleToBlowup_comp_blowupToAmbient :
    coordinateBundleToBlowup R m ≫ coordinateBlowupToAmbient R m 1 =
      coordinateBlowupBundleToCentre R m 1 ≫
        Stacks.MoreMorphisms.coordinateEmbedding R m 1 := by
  rw [coordinateBundleToBlowup, Category.assoc,
    coordinateExceptionalι_comp_blowupToAmbient R m 1, ← Category.assoc,
    coordinateBundleExceptionalIso_hom_comp_toCentre]

end Stacks.DeRham

end
