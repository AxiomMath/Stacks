module

public import StacksFrontier.Cotangent.KoszulRegularIdealQuotient
public import StacksFrontier.Cotangent.KoszulRegularQuotientUnconditional
public import StacksFrontier.Cotangent.LocalizationUnconditional

/-!
# Lemma 08SK

This module carries the registration of **[Stacks, Tag 08SK]**:
`CommAlgCat.nonempty_cotangentComplex_iso_single_of_isKoszulRegular_unconditional`. Let `A → B`
be a surjective ring map whose kernel `I` is a Koszul-regular ideal (Tag 07CV (2),
`Ideal.IsKoszulRegular`). Then `L_{B/A}` is isomorphic in `D(B)` to the conormal module `I/I²`
placed in cohomological degree `-1`, that is, to `I/I²[1]`. The statement takes exactly the
source's two hypotheses.

The proof is that of `StacksFrontier.Cotangent.KoszulRegularIdealQuotient`, which takes two inputs
as parameters: [Stacks, Tag 08SF] at the principal localizations `A_g → B_g`, as
`CommAlgCat.HasLocalizedCotangentComplexAt`, and Proposition 08QX at the towers
`A_g → P → A_g`, as `CommAlgCat.HasFundamentalTriangleAtPolynomialRetractions`. Both are proved
and supplied here: the first is the special case `S = {gⁿ}`, `T = {(image of g)ⁿ}` of
`CommAlgCat.nonempty_extendScalars_cotangentComplex_iso_localization`, the degreewise reading of
Tag 08SF, where its hypothesis that `S` map into `T` is automatic
(`CommAlgCat.powers_le_comap_powers`); the second is `CommAlgCat.hasFundamentalTriangleAt`.

## Main results

* `CommAlgCat.isScalarTower_awayAlgebra`: `A → A_g → B_g` is a tower.
* `CommAlgCat.hasLocalizedCotangentComplexAt`: [Stacks, Tag 08SF] at `A_g → B_g`, for every
  `g : A`.
* `CommAlgCat.isZero_homology_cotangentComplex_of_isKoszulRegular_unconditional`:
  `H^i(L_{B/A}) = 0` for `i ≤ -2`, when `ker(A → B)` is a Koszul-regular ideal.
* `CommAlgCat.nonempty_cotangentComplex_iso_single_of_isKoszulRegular_unconditional`:
  **[Stacks, Tag 08SK]**.

## References

* [Stacks Project, Tag 08SK](https://stacks.math.columbia.edu/tag/08SK)
* [Stacks Project, Tag 08SF](https://stacks.math.columbia.edu/tag/08SF)
* [Stacks Project, Tag 08QX](https://stacks.math.columbia.edu/tag/08QX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CommAlgCat

attribute [local instance] HasDerivedCategory.standard

section Away

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

attribute [local instance] awayAlgebra

/-- `A → A_g → B_g` is a tower: the structure map `A_g → B_g` is `IsLocalization.map`, which by
`IsLocalization.map_comp` agrees on `A` with `A → B → B_g`. -/
theorem isScalarTower_awayAlgebra (g : A) :
    IsScalarTower A (Localization.Away g)
      (Localization.Away (algebraMap A (B : Type u) g)) :=
  IsScalarTower.of_algebraMap_eq fun x => by
    have h := RingHom.congr_fun
      (IsLocalization.map_comp (M := Submonoid.powers g) (S := Localization.Away g)
        (Q := Localization.Away (algebraMap A (B : Type u) g))
        (g := algebraMap A (B : Type u)) (powers_le_comap_powers A B g)) x
    rw [IsScalarTower.algebraMap_apply A (B : Type u)
      (Localization.Away (algebraMap A (B : Type u) g))]
    exact h.symm

attribute [local instance] isScalarTower_awayAlgebra

/-- **[Stacks, Tag 08SF] at the principal localization `A_g → B_g`, proved.** This is the
special case `S = {gⁿ}`, `T = {(image of g)ⁿ}` of
`CommAlgCat.nonempty_extendScalars_cotangentComplex_iso_localization`, the degreewise reading of
Tag 08SF. The hypothesis "`S` maps into `T`" that Tag 08SF asks for is automatic here, being
`CommAlgCat.powers_le_comap_powers`, so the statement holds for *every* `g : A`. -/
theorem hasLocalizedCotangentComplexAt (g : A) : HasLocalizedCotangentComplexAt A B g :=
  nonempty_extendScalars_cotangentComplex_iso_localization A (B : Type u) (Submonoid.powers g)
    (Submonoid.powers (algebraMap A (B : Type u) g)) (Localization.Away g)
    (Localization.Away (algebraMap A (B : Type u) g)) (powers_le_comap_powers A B g)

end Away

section KoszulRegularIdeal

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-- **`H^i(L_{B/A}) = 0` for `i ≤ -2`**, when `A → B` is surjective with Koszul-regular kernel.
This is `CommAlgCat.isZero_homology_cotangentComplex_of_isKoszulRegular` with its two inputs
supplied by `CommAlgCat.hasLocalizedCotangentComplexAt` and
`CommAlgCat.hasFundamentalTriangleAt`. -/
theorem isZero_homology_cotangentComplex_of_isKoszulRegular_unconditional
    (h : Function.Surjective (algebraMap A (B : Type u)))
    (hI : Ideal.IsKoszulRegular (RingHom.ker (algebraMap A (B : Type u))))
    (i : ℤ) (hi : i ≤ -2) :
    IsZero ((cotangentComplex A B).homology i) :=
  isZero_homology_cotangentComplex_of_isKoszulRegular A B h hI
    (fun g _ => hasLocalizedCotangentComplexAt A B g)
    (fun g _ P _ _ _ _ _ => hasFundamentalTriangleAt (Localization.Away g) P _) i hi

/-- **Stacks Project, Tag 08SK.** Let `A → B` be a surjective map of commutative rings whose
kernel `I` is a Koszul-regular ideal, Tag 07CV (2). Then `L_{B/A}` is quasi-isomorphic to
`I/I²[1]`, that is, isomorphic in `D(B)` to the conormal module `I/I²` placed in cohomological
degree `-1`.

The proof is the source's: locally on `Spec(A)` the ideal `I` is generated by a Koszul-regular
sequence, so [Stacks, Tag 08SJ] at the localizations `A_g → B_g` and the localization lemma
[Stacks, Tag 08SF] give `H^i(L_{B/A}) = 0` for `i ≤ -2`, whence the identification with
`I/I²[1]`. It is `CommAlgCat.nonempty_cotangentComplex_iso_single_of_isKoszulRegular` with its two
inputs supplied by `CommAlgCat.hasLocalizedCotangentComplexAt` (Tag 08SF) and
`CommAlgCat.hasFundamentalTriangleAt` (Proposition 08QX), so the hypotheses are the source's
own two. -/
@[stacks 08SK "the lemma in full: A -> B surjective with kernel I a Koszul-regular ideal \
  (Tag 07CV (2), `Ideal.IsKoszulRegular`: at every prime containing I, some principal \
  localization A_g has I A_g generated by a Koszul-regular sequence). The conclusion is an \
  isomorphism in D(B) between L_{B/A} (the cotangent complex of the standard resolution, Tag \
  08PN) and I/I^2 placed in cohomological degree -1, that is I/I^2[1]; I/I^2 is the conormal \
  module of the surjection, as the cotangent module of the corresponding algebra extension. \
  NOTHING is carried: the hypotheses are the source's two. The localization lemma Tag 08SF is \
  proved at every principal localization A_g -> B_g by \
  `CommAlgCat.hasLocalizedCotangentComplexAt`, from \
  `CommAlgCat.nonempty_extendScalars_cotangentComplex_iso_localization`; Proposition 08QX at \
  the towers A_g -> P -> A_g that Tag 08SJ uses is `CommAlgCat.hasFundamentalTriangleAt`, \
  from `CommAlgCat.productFundamentalTriangle_distinguished`. Everything else is proved \
  outright: the Koszul cover generates the unit ideal, the localized map is surjective with \
  kernel the localized ideal, Tag 08SJ at it, the flatness of B -> B_g, and the Zariski descent \
  of the vanishing of H^i(L_{B/A}) for i <= -2"]
theorem nonempty_cotangentComplex_iso_single_of_isKoszulRegular_unconditional
    (h : Function.Surjective (algebraMap A (B : Type u)))
    (hI : Ideal.IsKoszulRegular (RingHom.ker (algebraMap A (B : Type u)))) :
    Nonempty (DerivedCategory.Q.obj (cotangentComplex A B) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (B : Type u)) (-1)).obj
        (ModuleCat.of (B : Type u) (surjectionExtension A B h).Cotangent)) :=
  nonempty_cotangentComplex_iso_single_of_isKoszulRegular A B h hI
    (fun g _ => hasLocalizedCotangentComplexAt A B g)
    (fun g _ P _ _ _ _ _ => hasFundamentalTriangleAt (Localization.Away g) P _)

end KoszulRegularIdeal

end CommAlgCat

end
