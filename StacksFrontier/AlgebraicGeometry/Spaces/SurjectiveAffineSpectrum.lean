module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges

/-!
# Surjectivity on the prime spectra of the rings of global functions

A morphism of affine schemes is determined by the ring map it induces on global functions, and
each of the two schemes is recovered from its ring of global functions by the unit
`X ⟶ Spec Γ(X, ⊤)` of the `Γ`–`Spec` adjunction, which is an isomorphism exactly because the
scheme is affine. Consequently a surjective morphism of affine schemes induces a surjective map
of prime spectra: the comparison square of the unit identifies the morphism of schemes with
`Spec` of the ring map, and surjectivity may be transported along the two isomorphisms.

The same statement is then read on the big fppf site: if `U` and `V` are objects of the big fppf
category over `S` whose underlying schemes are affine, and if the morphism of algebraic spaces
represented by a morphism `U ⟶ V` is surjective in the sense of Tag 03ME, then the induced map on
the prime spectra of the rings of global functions of the two underlying schemes is surjective.
The last form is the one needed when the surjective morphism out of a representable presheaf is
presented as a morphism into an arbitrary presheaf together with an identification of that
presheaf with a representable one.

This is the geometric input to the commutative-algebra descent step in the proof of Tag 07SQ,
where a surjection of prime spectra is what makes a system of finitely presented algebras
descend.

## Main results

* `AlgebraicGeometry.surjective_primeSpectrum_comap_appTop_of_surjective`: a morphism of affine
  schemes which is surjective on points induces a surjective map on the prime spectra of the
  rings of global functions.
* `AlgebraicGeometry.Space.surjective_primeSpectrum_comap_appTop_of_isSurjective`: the same
  conclusion for a morphism of objects of the big fppf category over `S` with affine underlying
  schemes whose represented morphism of algebraic spaces is surjective.
* `AlgebraicGeometry.Space.surjective_primeSpectrum_comap_appTop_of_isSurjective_of_iso`: the
  variant in which the surjective morphism is given into an arbitrary presheaf which is only
  later identified with a representable one.

## Implementation notes

The scheme-level statement is proved through the Mathlib class
`AlgebraicGeometry.Surjective`, which is surjectivity of the underlying map of topological
spaces: an isomorphism is surjective, a composite of surjective morphisms is surjective, and
surjectivity of a composite passes to its second factor. Applying the last of these to the
naturality square `f ≫ Z.toSpecΓ = Y.toSpecΓ ≫ Spec.map f.appTop` yields surjectivity of
`Spec.map f.appTop`, whose underlying map is by definition the comap of the ring map on global
functions.

For the site-level statements the geometric surjectivity hypothesis is converted into
surjectivity of the underlying morphism of schemes by
`AlgebraicGeometry.Space.surjective_of_isSurjective_yonedaMap`, and in the last statement the
morphism of presheaves is first composed with the given isomorphism, surjectivity being stable
under composition and automatic for an isomorphism, and then recognised as the image under the
Yoneda embedding of a morphism of the site, the embedding being full.

## References

* [Stacks Project, Tag 03ME](https://stacks.math.columbia.edu/tag/03ME)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- **A surjective morphism of affine schemes is surjective on prime spectra of global
functions.** For affine `Y` and `Z` the units `Y ⟶ Spec Γ(Y, ⊤)` and `Z ⟶ Spec Γ(Z, ⊤)` of the
`Γ`–`Spec` adjunction are isomorphisms, and they fit into a commuting square with `f` and with
`Spec` of the ring map `f.appTop` on global functions. Surjectivity of `f` therefore transports
to surjectivity of `Spec Γ(Y, ⊤) ⟶ Spec Γ(Z, ⊤)`, that is to surjectivity of the comap of
`f.appTop` on prime spectra. -/
theorem surjective_primeSpectrum_comap_appTop_of_surjective {Y Z : Scheme.{u}}
    [IsAffine Y] [IsAffine Z] (f : Y ⟶ Z) (hf : Function.Surjective f.base) :
    Function.Surjective (PrimeSpectrum.comap f.appTop.hom) := by
  have : Surjective f := ⟨hf⟩
  have : Surjective (Y.toSpecΓ ≫ Spec.map f.appTop) := by
    rw [← Scheme.toSpecΓ_naturality]
    infer_instance
  have : Surjective (Spec.map f.appTop) := Surjective.of_comp Y.toSpecΓ (Spec.map f.appTop)
  exact (Spec.map f.appTop).surjective

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A surjective morphism of affine objects of the big fppf site is surjective on the prime
spectra of the rings of global functions.** Surjectivity of the represented morphism of algebraic
spaces, Tag 03ME, is surjectivity of the underlying morphism of schemes, and for affine
underlying schemes that is surjectivity on prime spectra of global functions. -/
theorem surjective_primeSpectrum_comap_appTop_of_isSurjective {U V : BigFppfOver B S hS}
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (φ : U ⟶ V) (hφ : IsSurjective B S hS (yoneda.map φ)) :
    Function.Surjective (PrimeSpectrum.comap ((BigFppfOver.toScheme B S hS).map φ).appTop.hom) :=
  surjective_primeSpectrum_comap_appTop_of_surjective _
    (surjective_of_isSurjective_yonedaMap B S hS φ hφ)

/-- **The surjectivity on prime spectra of global functions obtained from a surjective morphism
into a presheaf identified with a representable one.** Composing the surjective morphism `k` with
the identification `e` is again surjective, an isomorphism being surjective on points and
surjectivity being stable under composition, and the composite is the image under the Yoneda
embedding of a morphism of the site because that embedding is full. -/
theorem surjective_primeSpectrum_comap_appTop_of_isSurjective_of_iso {U : BigFppfOver B S hS}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V : BigFppfOver B S hS}
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (k : yoneda.obj U ⟶ F) (e : F ≅ yoneda.obj V) (hk : IsSurjective B S hS k) :
    Function.Surjective (PrimeSpectrum.comap
      ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (k ≫ e.hom))).appTop.hom) := by
  refine surjective_primeSpectrum_comap_appTop_of_isSurjective B S hS hU hV _ ?_
  rw [Functor.map_preimage]
  exact isSurjective_comp B S hS hk (isSurjective_of_isIso B S hS e.hom)

end Space

end AlgebraicGeometry

end
