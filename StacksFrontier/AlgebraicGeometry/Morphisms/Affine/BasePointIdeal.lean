module

public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# The prime a point lies over, read on the germ of the structure map

For a scheme `g : Y ⟶ Spec R` over an affine base and a point `y` of `Y`, the prime of `R`
corresponding to the image point `g y` is the contraction of the maximal ideal of `𝒪_{Y, y}`
along the germ at `y` of the structure map of `R`: a section of `R` vanishes at `g y` exactly
when its germ at `y` is not a unit.

**This is the comparison that identifies the base point of a local criterion.**  Smoothness at a
point is checked through a model `A_p → B_q` of the stalk map, and the model produced by the
reduced fibre theorem at a generic point of a fibre names `q` — a prime of an integral closure —
while the point of `Spec B` below is named by the morphism.  The two agree, and this is why.

## Main results

* `AlgebraicGeometry.asIdeal_base_eq_comap_maximalIdeal`: the prime of `R` at the image point is
  the contraction of the maximal ideal of the stalk.
* `AlgebraicGeometry.asIdeal_base_eq_comap_of_ringEquiv_localizationAtPrime`: the same read
  through an identification of the stalk with a localization, which is the form in which the
  identification of the local rings of a normalized base change delivers it.

## Implementation notes

The composite `R → Γ(Y, ⊤) → 𝒪_{Y, y}` is factored as the germ of the structure sheaf of
`Spec R` at `g y` followed by the stalk map of `g`.  The first factor is
`AlgebraicGeometry.Spec.algebraMap_stalkIso_inv`, which presents it as the localization map of
`R` at the prime, and the second is a local homomorphism, so each contraction of a maximal ideal
is the maximal ideal below.

## References

* [Stacks Project, Tag 01I1](https://stacks.math.columbia.edu/tag/01I1)
* [Stacks Project, Tag 09IL](https://stacks.math.columbia.edu/tag/09IL)
-/

public noncomputable section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/-- **The germ of the structure map of an affine base is the localization map at the image
point.**  For `g : Y ⟶ Spec R` and `y : Y`, the composite `R → Γ(Y, ⊤) → 𝒪_{Y, y}` is the
localization of `R` at the prime of `g y`, followed by the identification of that localization
with the stalk of `Spec R` and the stalk map of `g`. -/
theorem germ_structureMap_eq {R : CommRingCat.{u}} {Y : Scheme.{u}} (g : Y ⟶ Spec R) (y : Y) :
    haveI : (g.base y).asIdeal.IsPrime := (g.base y).isPrime
    (Scheme.ΓSpecIso R).inv ≫ g.appTop ≫ Y.presheaf.germ ⊤ y trivial =
      CommRingCat.ofHom (algebraMap R (Localization.AtPrime (g.base y).asIdeal)) ≫
        (Spec.stalkIso R (g.base y)).inv ≫ g.stalkMap y := by
  have : (g.base y).asIdeal.IsPrime := (g.base y).isPrime
  have h2 : (Spec R).presheaf.germ ⊤ (g.base y) trivial ≫ g.stalkMap y =
      g.appTop ≫ Y.presheaf.germ ⊤ y trivial := Scheme.Hom.germ_stalkMap g ⊤ y trivial
  rw [← h2, ← Category.assoc]
  exact (Spec.algebraMap_stalkIso_inv_assoc (R := R) (x := g.base y) (g.stalkMap y)).symm

/-- **The prime a point lies over is the contraction of the maximal ideal of its local ring.**
For `g : Y ⟶ Spec R` and `y : Y`, the prime of `R` corresponding to `g y` is the preimage of the
maximal ideal of `𝒪_{Y, y}` under the germ at `y` of the structure map of `R`. -/
theorem asIdeal_base_eq_comap_maximalIdeal {R : CommRingCat.{u}} {Y : Scheme.{u}}
    (g : Y ⟶ Spec R) (y : Y) :
    (g.base y).asIdeal =
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).comap
        ((Scheme.ΓSpecIso R).inv ≫ g.appTop ≫ Y.presheaf.germ ⊤ y trivial).hom := by
  have : (g.base y).asIdeal.IsPrime := (g.base y).isPrime
  have : IsLocalHom (g.stalkMap y).hom := g.toLRSHom.prop y
  have : IsLocalHom ((Spec.stalkIso R (g.base y)).inv).hom := isLocalHom_of_isIso _
  rw [germ_structureMap_eq, CommRingCat.hom_comp, CommRingCat.hom_comp,
    ← Ideal.comap_comap, ← Ideal.comap_comap, IsLocalRing.maximalIdeal_comap (g.stalkMap y).hom,
    IsLocalRing.maximalIdeal_comap ((Spec.stalkIso R (g.base y)).inv).hom]
  exact (IsLocalization.AtPrime.under_maximalIdeal
    (Localization.AtPrime (g.base y).asIdeal) (g.base y).asIdeal).symm

/-- **The prime a point lies over, read through a presentation of its local ring as a
localization.**  Suppose the local ring of `Y` at `y` is identified with the localization of a
ring `T` at a prime `q`, by an isomorphism carrying the germ of a section of `R` to the image of
its value under a ring map `ι : R → T`.  Then the prime of `R` at `g y` is the contraction of
`q` along `ι`.

This is the form delivered by
`Scheme.exists_ringEquiv_stalk_normalizationScheme_pullback_localizationAtPrime_germ`,
whose `φ` and compatibility statement are exactly the hypotheses here. -/
theorem asIdeal_base_eq_comap_of_ringEquiv_localizationAtPrime {R : CommRingCat.{u}}
    {Y : Scheme.{u}} (g : Y ⟶ Spec R) (y : Y) {T : Type v} [CommRing T] (q : Ideal T)
    [q.IsPrime] (ι : R →+* T)
    (φ : Y.presheaf.stalk y ≃+* Localization.AtPrime q)
    (hφ : ∀ r : R, φ (((Scheme.ΓSpecIso R).inv ≫ g.appTop ≫
        Y.presheaf.germ ⊤ y trivial).hom r) =
      algebraMap T (Localization.AtPrime q) (ι r)) :
    (g.base y).asIdeal = q.comap ι := by
  have hhom : (φ : Y.presheaf.stalk y →+* Localization.AtPrime q).comp
        ((Scheme.ΓSpecIso R).inv ≫ g.appTop ≫ Y.presheaf.germ ⊤ y trivial).hom =
      (algebraMap T (Localization.AtPrime q)).comp ι := RingHom.ext hφ
  rw [asIdeal_base_eq_comap_maximalIdeal g y,
    ← IsLocalRing.maximalIdeal_comap (φ : Y.presheaf.stalk y →+* Localization.AtPrime q),
    Ideal.comap_comap, hhom, ← Ideal.comap_comap]
  exact congrArg (Ideal.comap ι)
    (IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime q) q)

end AlgebraicGeometry

end
