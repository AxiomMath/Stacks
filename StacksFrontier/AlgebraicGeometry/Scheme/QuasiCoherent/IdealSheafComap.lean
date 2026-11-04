module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# The inverse image of a quasi-coherent ideal sheaf along an open immersion

Mathlib's `AlgebraicGeometry.Scheme.IdealSheafData` carries an idempotent commutative semiring
structure, in which the product of two ideal sheaves is computed ideal by ideal on affine opens,
and the inverse image `AlgebraicGeometry.Scheme.IdealSheafData.comap` along a morphism of schemes
is recorded as a monotone map, compatible with `⊥`, `⊤` and `⊔` but with nothing said about the
product. This file proves that along an *open immersion* the inverse image is also multiplicative,
hence a homomorphism of semirings, and that the inverse images along an affine open cover jointly
determine an ideal sheaf.

Both statements are false, or unavailable, for a general morphism: the inverse image of a product
of ideal sheaves along an arbitrary morphism is only contained in the product of the inverse
images, since already for rings one has `(K · L) · S ⊆ (K · S) · (L · S)` with equality requiring
the extension of scalars to behave like a localization.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.comap_mul_of_isOpenImmersion` and
  `AlgebraicGeometry.Scheme.IdealSheafData.comap_pow_of_isOpenImmersion`: the inverse image
  along an open immersion commutes with the product and with the powers of ideal sheaves.
* `AlgebraicGeometry.Scheme.IdealSheafData.eq_of_comap_eq_of_iUnion_range_eq_univ`: two ideal
  sheaves with the same inverse image on every member of a cover by affine open subschemes are
  equal.
* `Ideal.comap_mul_of_bijective`: the ring-theoretic input, that `Ideal.comap` along a bijective
  ring homomorphism is multiplicative.

## Implementation notes

Mathlib computes the inverse image along an open immersion by
`AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion`: on an affine open `U`
of the source it is the `Ideal.comap` of the ideal on the image `f ''ᵁ U` along the ring
*isomorphism* `(f.appIso U).inv`. So the whole content at the level of schemes is that
`Ideal.comap` along a bijective ring homomorphism is multiplicative, which is
`Ideal.comap_mul_of_bijective`; that in turn holds because for a ring isomorphism `Ideal.comap`
is `Ideal.map` of the inverse (`Ideal.map_symm`), and `Ideal.map` is multiplicative for every
ring homomorphism. The product and the powers of ideal sheaves are definitionally the pointwise
product and powers of the ideals, so no lemma is needed to take the semiring operations through
`AlgebraicGeometry.Scheme.IdealSheafData.ideal`.

The cover in `eq_of_comap_eq_of_iUnion_range_eq_univ` is given by morphisms from affine schemes
rather than by affine opens, because that is the shape in which the charts of a glued scheme —
for instance the standard charts of a blowup — present themselves. The affine opens it feeds to
`AlgebraicGeometry.Scheme.IdealSheafData.ext_of_iSup_eq_top` are the images `g i ''ᵁ ⊤`.

No `@[stacks]` attribute is attached: these are statements about Mathlib's representation of a
quasi-coherent sheaf of ideals by its ideals on affine opens, not formalizations of a tagged
result.

## References

* [Stacks Project, Tag 01QX](https://stacks.math.columbia.edu/tag/01QX), quasi-coherent sheaves
  of ideals and their inverse images.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

/-- `Ideal.comap` along a *bijective* ring homomorphism is multiplicative. For a bijective `φ`
the inverse image of an ideal is the image of it under the inverse, and `Ideal.map` is
multiplicative for every ring homomorphism. -/
theorem Ideal.comap_mul_of_bijective {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Bijective φ) (I J : Ideal S) :
    (I * J).comap φ = I.comap φ * J.comap φ := by
  have h (K : Ideal S) : K.comap φ = K.map (RingEquiv.ofBijective φ hφ).symm :=
    (Ideal.map_symm (RingEquiv.ofBijective φ hφ)).symm
  rw [h, h, h, Ideal.map_mul]

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

/-- **The inverse image of ideal sheaves along an open immersion is multiplicative.** On an
affine open of the source the inverse image is `Ideal.comap` along a ring isomorphism, and
`Ideal.comap` along a bijection is multiplicative. -/
theorem comap_mul_of_isOpenImmersion (I J : Y.IdealSheafData) :
    (I * J).comap f = I.comap f * J.comap f := by
  refine IdealSheafData.ext (funext fun U => ?_)
  show ((I * J).comap f).ideal U = (I.comap f).ideal U * (J.comap f).ideal U
  rw [ideal_comap_of_isOpenImmersion (I * J) f U, ideal_comap_of_isOpenImmersion I f U,
    ideal_comap_of_isOpenImmersion J f U]
  exact Ideal.comap_mul_of_bijective _ (ConcreteCategory.bijective_of_isIso _) _ _

/-- **The inverse image of ideal sheaves along an open immersion commutes with powers.** -/
theorem comap_pow_of_isOpenImmersion (I : Y.IdealSheafData) (n : ℕ) :
    (I ^ n).comap f = I.comap f ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, show (1 : Y.IdealSheafData) = ⊤ from rfl,
      show (1 : X.IdealSheafData) = ⊤ from rfl, comap_top]
  | succ n ih => rw [pow_succ, pow_succ, comap_mul_of_isOpenImmersion, ih]

/-- **An ideal sheaf is determined by its inverse images on a cover by affine open subschemes.**
If the images of morphisms `g i : Z i ⟶ X` from affine schemes, each an open immersion, cover `X`,
and two ideal sheaves on `X` have the same inverse image along every `g i`, then they are
equal. -/
theorem eq_of_comap_eq_of_iUnion_range_eq_univ {ι : Type*} {Z : ι → Scheme.{u}}
    [∀ i, IsAffine (Z i)] (g : ∀ i, Z i ⟶ X) [∀ i, IsOpenImmersion (g i)]
    (hg : ⋃ i, Set.range (g i).base = Set.univ) {I J : X.IdealSheafData}
    (h : ∀ i, I.comap (g i) = J.comap (g i)) : I = J := by
  refine ext_of_iSup_eq_top
    (fun i => ⟨g i ''ᵁ ⊤, (isAffineOpen_top (X := Z i)).image_of_isOpenImmersion (g i)⟩)
    (SetLike.coe_injective ?_) fun i => ?_
  · simpa [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.coe_opensRange] using hg
  · have hi := congrArg (fun K : (Z i).IdealSheafData => K.ideal ⟨⊤, isAffineOpen_top _⟩) (h i)
    rw [ideal_comap_of_isOpenImmersion, ideal_comap_of_isOpenImmersion] at hi
    exact Ideal.comap_injective_of_surjective _
      (ConcreteCategory.bijective_of_isIso ((g i).appIso ⊤).inv).2 hi

end AlgebraicGeometry.Scheme.IdealSheafData
