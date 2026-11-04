module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksFrontier.AlgebraicGeometry.Descent.Algebra.SpecOverFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability

/-!
# Affine objects of a big fppf site over an affine base are spectra of algebras

Let `B` be a big fppf site and `R` a ring with `Spec R` an object of `B`. The big fppf
category over `Spec R` then contains, for every `R`-algebra `A` whose spectrum `B` contains,
the object `Spec A` with its structure morphism `Spec A ⟶ Spec R`; this file shows that the
affine objects of the site over `Spec R` are *exactly* these, that their morphisms over
`Spec R` are exactly the `R`-algebra maps in the other direction, and that base change along
`Spec R₂ ⟶ Spec R` is the pushout of algebras.

## Main definitions

* `AlgebraicGeometry.Space.specSite`: the spectrum of an `R`-algebra, as an object of the big
  fppf category over `Spec R`.
* `AlgebraicGeometry.Space.specSiteHomEquiv`: the bijection between morphisms of the site over
  `Spec R` and `R`-algebra maps in the opposite direction.
* `AlgebraicGeometry.Space.specSiteIsoOfAlgEquiv`: the isomorphism of the site induced by an
  isomorphism of `R`-algebras.
* `AlgebraicGeometry.Space.specSiteBaseChangeIso`: the base change of `Spec A` along
  `Spec R₂ ⟶ Spec R` is `Spec A₂` for a pushout square of rings.

## Main results

* `AlgebraicGeometry.Space.toScheme_obj_specSite` and
  `AlgebraicGeometry.Space.inclusion_map_specSite_hom`: the underlying scheme of
  `AlgebraicGeometry.Space.specSite` and its structure morphism.
* `AlgebraicGeometry.Space.exists_specSite_iso_of_isAffineSpace`: **the presentation
  theorem.** An affine algebraic space over `Spec R` is represented by the spectrum of an
  `R`-algebra which the site contains.
* `AlgebraicGeometry.Space.inclusion_map_specSiteHomEquiv_symm` and
  `AlgebraicGeometry.Space.specSiteHomEquiv_apply_eq`: the morphism of schemes underlying the
  morphism of the site attached to an algebra map is `Spec` of that map, and conversely.
* `AlgebraicGeometry.Space.hom_ext_toScheme_map`: a morphism of the site over `Spec R` is
  determined by the underlying morphism of schemes.
* `AlgebraicGeometry.Space.isPullback_specSiteScheme`: for a pushout square of rings, the
  square of spectra is a fibre product square in the underlying category of the site.
* `AlgebraicGeometry.Space.specSiteBaseChangeIso_inv_left_comp_fst`: the base change
  isomorphism is compatible with the projection to `Spec A`.

## Implementation notes

The `R`-algebra structure on the global sections of an affine object `T` of the site comes
from its structure morphism together with `AlgebraicGeometry.Scheme.ΓSpecIso`, exactly as in
`AlgebraicGeometry.Space.IsGlueableGlobalSections`, so that the two agree definitionally.

Reading the structure morphism of an affine object `T` through
`AlgebraicGeometry.Scheme.isoSpec` is what identifies it with `Spec` of the algebra map of
those global sections.

The hom dictionary is obtained by transporting `AlgebraicGeometry.specOverMapEquiv` along the
faithful inclusion of the site into schemes: a morphism of the site over `Spec R` between two
objects of the form `Spec A` is the same as a morphism of schemes over `Spec R`, because the
inclusion is faithful and a morphism of schemes over `Spec R` between contained objects lifts.

The base change statement is proved in the underlying category `B.Schemes` of the site first:
the square of spectra is a fibre product square in schemes by
`AlgebraicGeometry.isPullback_SpecMap_of_isPushout`, and a fully faithful functor reflects
limits, so the square it comes from in `B.Schemes` is one as well. The over-category
statement is then the induced isomorphism with the chosen fibre product.

The hypothesis of the base change statements is a pushout square of `CommRingCat` together
with a bare ring map `A → A₂` for the fourth corner, rather than
`Algebra.IsPushout R R₂ A A₂` for a scalar tower: for an honest tensor product
`A₂ = R₂ ⊗[R] A` the algebra structure of `A₂` over `A` is
`Algebra.TensorProduct.rightAlgebra`, which is not a global instance, so the scalar-tower
form is not available at the places which use these statements. Only the algebra structure of
`A₂` over the left factor `R₂`, which is what its structure morphism to `Spec R₂` needs, is
assumed.

## References

* [Stacks Project, Tag 01I1](https://stacks.math.columbia.edu/tag/01I1)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) {R : Type u} [CommRing R]
  (hX : B.Contains (Spec (.of R)))

section Objects

variable {A : Type u} [CommRing A] [Algebra R A]

/-- The spectrum of an `R`-algebra whose spectrum the site contains, as an object of the big
fppf category over `Spec R`, with its structure morphism `Spec A ⟶ Spec R`. -/
def specSite (hA : B.Contains (Spec (.of A))) : BigFppfOver B (Spec (.of R)) hX :=
  BigFppfOver.mk B (Spec (.of R)) hX hA (Spec.map (CommRingCat.ofHom (algebraMap R A)))

/-- The underlying scheme of `AlgebraicGeometry.Space.specSite` is `Spec A`. -/
theorem toScheme_obj_specSite (hA : B.Contains (Spec (.of A))) :
    (BigFppfOver.toScheme B (Spec (.of R)) hX).obj (specSite B hX hA) = Spec (.of A) :=
  rfl

/-- The structure morphism of `AlgebraicGeometry.Space.specSite` is `Spec` of the algebra
map. -/
theorem inclusion_map_specSite_hom (hA : B.Contains (Spec (.of A))) :
    B.inclusion.map (specSite B hX hA).hom =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) :=
  rfl

/-- The underlying scheme of `AlgebraicGeometry.Space.specSite` is affine. -/
instance isAffine_toScheme_obj_specSite (hA : B.Contains (Spec (.of A))) :
    IsAffine ((BigFppfOver.toScheme B (Spec (.of R)) hX).obj (specSite B hX hA)) :=
  inferInstanceAs (IsAffine (Spec (.of A)))

end Objects

/-- A morphism from an affine scheme to `Spec R₀`, precomposed with the inverse of `isoSpec`,
is `Spec` of the induced map on global sections. -/
theorem isoSpec_inv_comp_eq_spec_map {R₀ : CommRingCat.{u}} {T₀ : Scheme.{u}} [IsAffine T₀]
    (q : T₀ ⟶ Spec R₀) :
    T₀.isoSpec.inv ≫ q = Spec.map ((Scheme.ΓSpecIso R₀).inv ≫ q.appTop) := by
  apply (cancel_epi T₀.toSpecΓ).mp
  simp only [Scheme.toSpecΓ_isoSpec_inv_assoc, Spec.map_comp]
  rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- **The presentation theorem for affine algebraic spaces over an affine base.** An affine
algebraic space over `Spec R` is represented by the spectrum of an `R`-algebra whose spectrum
the site contains, namely by the global sections of any representing affine object. -/
theorem exists_specSite_iso_of_isAffineSpace
    (F : (BigFppfOver B (Spec (.of R)) hX)ᵒᵖ ⥤ Type u)
    (hF : IsAffineSpace B (Spec (.of R)) hX F) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A) (hA : B.Contains (Spec (.of A))),
      Nonempty (F ≅ yoneda.obj (specSite B hX hA)) := by
  obtain ⟨T, hT, ⟨e⟩⟩ := hF
  let algT : Algebra R Γ((BigFppfOver.toScheme B (Spec (.of R)) hX).obj T, ⊤) :=
    (((Scheme.ΓSpecIso (.of R)).inv ≫ (B.inclusion.map T.hom).appTop).hom).toAlgebra
  have hA : B.Contains
      (Spec (.of Γ((BigFppfOver.toScheme B (Spec (.of R)) hX).obj T, ⊤))) := by
    show (Spec Γ((BigFppfOver.toScheme B (Spec (.of R)) hX).obj T, ⊤)).size < B.cutoff
    rw [← Scheme.size_congr ((BigFppfOver.toScheme B (Spec (.of R)) hX).obj T).isoSpec]
    exact T.left.2
  refine ⟨Γ((BigFppfOver.toScheme B (Spec (.of R)) hX).obj T, ⊤), inferInstance, algT, hA,
    ⟨e ≪≫ yoneda.mapIso (Over.isoMk (ObjectProperty.isoMk _
      ((BigFppfOver.toScheme B (Spec (.of R)) hX).obj T).isoSpec) ?_)⟩⟩
  apply B.inclusion.map_injective
  rw [Functor.map_comp]
  show ((BigFppfOver.toScheme B (Spec (.of R)) hX).obj T).isoSpec.hom ≫
    Spec.map ((Scheme.ΓSpecIso (.of R)).inv ≫ (B.inclusion.map T.hom).appTop) =
      B.inclusion.map T.hom
  rw [← isoSpec_inv_comp_eq_spec_map (R₀ := CommRingCat.of R)
    (T₀ := (BigFppfOver.toScheme B (Spec (.of R)) hX).obj T) (B.inclusion.map T.hom),
    Iso.hom_inv_id_assoc]

section Hom

variable {A₁ A₂ : Type u} [CommRing A₁] [Algebra R A₁] [CommRing A₂] [Algebra R A₂]
  {hA₁ : B.Contains (Spec (.of A₁))} {hA₂ : B.Contains (Spec (.of A₂))}

/-- Two morphisms of the big fppf category over `Spec R` whose underlying morphisms of schemes
agree are equal. -/
theorem hom_ext_toScheme_map {T T' : BigFppfOver B (Spec (.of R)) hX} {a b : T ⟶ T'}
    (h : (BigFppfOver.toScheme B (Spec (.of R)) hX).map a =
      (BigFppfOver.toScheme B (Spec (.of R)) hX).map b) : a = b :=
  BigFppfOver.map_toScheme_injective B (Spec (.of R)) hX h

/-- A morphism of the site over `Spec R` between spectra of `R`-algebras, as a morphism of
schemes over `Spec R`. -/
def specSiteOverMap (f : specSite B hX hA₁ ⟶ specSite B hX hA₂) :
    specOver R A₁ ⟶ specOver R A₂ :=
  Over.homMk ((BigFppfOver.toScheme B (Spec (.of R)) hX).map f) (by
    have h := congrArg B.inclusion.map (Over.w f)
    rw [Functor.map_comp] at h
    exact h)

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.specSiteOverMap`. -/
@[simp]
theorem specSiteOverMap_left (f : specSite B hX hA₁ ⟶ specSite B hX hA₂) :
    (specSiteOverMap B hX f).left = (BigFppfOver.toScheme B (Spec (.of R)) hX).map f :=
  rfl

/-- **The hom dictionary.** A morphism `Spec A₁ ⟶ Spec A₂` of the big fppf category over
`Spec R` is the same thing as an `R`-algebra map `A₂ → A₁`. -/
def specSiteHomEquiv (hA₁ : B.Contains (Spec (.of A₁))) (hA₂ : B.Contains (Spec (.of A₂))) :
    (specSite B hX hA₁ ⟶ specSite B hX hA₂) ≃ (A₂ →ₐ[R] A₁) where
  toFun f := algHomOfSpecOverMap (specSiteOverMap B hX f)
  invFun φ := Over.homMk
    (ObjectProperty.homMk (X := (specSite B hX hA₁).left) (Y := (specSite B hX hA₂).left)
      (Spec.map (CommRingCat.ofHom φ.toRingHom))) (by
      apply ObjectProperty.hom_ext
      change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R A₂)) =
        Spec.map (CommRingCat.ofHom (algebraMap R A₁))
      rw [← Spec.map_comp]
      congr 1
      ext r
      exact φ.commutes r)
  left_inv f := BigFppfOver.map_toScheme_injective B (Spec (.of R)) hX (by
    have h := congrArg Over.Hom.left
      (specOverMap_algHomOfSpecOverMap (specSiteOverMap B hX f))
    rw [specOverMap_left, specSiteOverMap_left] at h
    exact h)
  right_inv φ := specOverMap_injective (by
    rw [specOverMap_algHomOfSpecOverMap]
    exact Over.OverMorphism.ext rfl)

/-- The morphism of schemes underlying the morphism of the site attached to an algebra map is
`Spec` of that map. -/
theorem inclusion_map_specSiteHomEquiv_symm (hA₁ : B.Contains (Spec (.of A₁)))
    (hA₂ : B.Contains (Spec (.of A₂))) (φ : A₂ →ₐ[R] A₁) :
    (BigFppfOver.toScheme B (Spec (.of R)) hX).map ((specSiteHomEquiv B hX hA₁ hA₂).symm φ) =
      Spec.map (CommRingCat.ofHom φ.toRingHom) :=
  rfl

/-- The morphism of schemes underlying a morphism of the site is `Spec` of the `R`-algebra map
the hom dictionary attaches to it. -/
theorem specSiteHomEquiv_apply_eq (hA₁ : B.Contains (Spec (.of A₁)))
    (hA₂ : B.Contains (Spec (.of A₂))) (f : specSite B hX hA₁ ⟶ specSite B hX hA₂) :
    (BigFppfOver.toScheme B (Spec (.of R)) hX).map f =
      Spec.map (CommRingCat.ofHom (specSiteHomEquiv B hX hA₁ hA₂ f).toRingHom) := by
  conv_lhs => rw [← (specSiteHomEquiv B hX hA₁ hA₂).symm_apply_apply f]
  exact inclusion_map_specSiteHomEquiv_symm B hX hA₁ hA₂ _

/-- **`Spec` of an isomorphism of algebras, in the site.** An isomorphism `A₁ ≃ₐ[R] A₂` of
`R`-algebras induces an isomorphism `Spec A₂ ≅ Spec A₁` of the big fppf category over
`Spec R`; the direction is reversed because `Spec` is contravariant. -/
def specSiteIsoOfAlgEquiv (hA₁ : B.Contains (Spec (.of A₁)))
    (hA₂ : B.Contains (Spec (.of A₂))) (e : A₁ ≃ₐ[R] A₂) :
    specSite B hX hA₂ ≅ specSite B hX hA₁ where
  hom := (specSiteHomEquiv B hX hA₂ hA₁).symm e.toAlgHom
  inv := (specSiteHomEquiv B hX hA₁ hA₂).symm e.symm.toAlgHom
  hom_inv_id := hom_ext_toScheme_map B hX (by
    have hc : CommRingCat.ofHom e.symm.toAlgHom.toRingHom ≫
        CommRingCat.ofHom e.toAlgHom.toRingHom = 𝟙 (CommRingCat.of A₂) := by
      ext a
      exact e.apply_symm_apply a
    change Spec.map (CommRingCat.ofHom e.toAlgHom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom e.symm.toAlgHom.toRingHom) =
      𝟙 (Spec (CommRingCat.of A₂))
    rw [← Spec.map_comp, hc, Spec.map_id])
  inv_hom_id := hom_ext_toScheme_map B hX (by
    have hc : CommRingCat.ofHom e.toAlgHom.toRingHom ≫
        CommRingCat.ofHom e.symm.toAlgHom.toRingHom = 𝟙 (CommRingCat.of A₁) := by
      ext a
      exact e.symm_apply_apply a
    change Spec.map (CommRingCat.ofHom e.symm.toAlgHom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom e.toAlgHom.toRingHom) =
      𝟙 (Spec (CommRingCat.of A₁))
    rw [← Spec.map_comp, hc, Spec.map_id])

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.specSiteIsoOfAlgEquiv` is
`Spec` of the algebra isomorphism. -/
theorem toScheme_map_specSiteIsoOfAlgEquiv_hom (hA₁ : B.Contains (Spec (.of A₁)))
    (hA₂ : B.Contains (Spec (.of A₂))) (e : A₁ ≃ₐ[R] A₂) :
    (BigFppfOver.toScheme B (Spec (.of R)) hX).map
        (specSiteIsoOfAlgEquiv B hX hA₁ hA₂ e).hom =
      Spec.map (CommRingCat.ofHom e.toAlgHom.toRingHom) :=
  rfl

end Hom

section BaseChange

variable {R₂ A A₂ : Type u} [CommRing R₂] [CommRing A] [CommRing A₂]
  [Algebra R R₂] [Algebra R A] [Algebra R₂ A₂]

/-- **A pushout square of rings gives a fibre product square of spectra in the site.** The map
`A → A₂` of the fourth corner is an arbitrary ring map, not required to be an algebra map for a
scalar tower: the hypothesis is the pushout square of `CommRingCat` itself. -/
theorem isPullback_specSiteScheme (u : A →+* A₂)
    (hpush : IsPushout
      (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom (algebraMap R R₂))
      (CommRingCat.ofHom u) (CommRingCat.ofHom (algebraMap R₂ A₂)))
    (hX₂ : B.Contains (Spec (.of R₂))) (hA : B.Contains (Spec (.of A)))
    (hA₂ : B.Contains (Spec (.of A₂))) :
    IsPullback
      (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom u)) : B.obj hA₂ ⟶ B.obj hA)
      (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R₂ A₂))) :
        B.obj hA₂ ⟶ B.obj hX₂)
      (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A))) :
        B.obj hA ⟶ B.obj hX)
      (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R R₂))) :
        B.obj hX₂ ⟶ B.obj hX) :=
  IsPullback.of_map_of_faithful B.inclusion (isPullback_SpecMap_of_isPushout _ _ _ _ hpush)

/-- **Base change of an affine object along an affine base change.** For a pushout square of
rings, `Spec A₂` is the base change of `Spec A` from `Spec R` to `Spec R₂` in the site. -/
def specSiteBaseChangeIso (u : A →+* A₂)
    (hpush : IsPushout
      (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom (algebraMap R R₂))
      (CommRingCat.ofHom u) (CommRingCat.ofHom (algebraMap R₂ A₂)))
    (hX₂ : B.Contains (Spec (.of R₂))) (hA : B.Contains (Spec (.of A)))
    (hA₂ : B.Contains (Spec (.of A₂))) :
    (CategoryTheory.Over.pullback (specSite B hX hX₂).hom).obj (specSite B hX hA) ≅
      specSite B hX₂ hA₂ :=
  Over.isoMk (isPullback_specSiteScheme B hX u hpush hX₂ hA hA₂).isoPullback.symm
    (isPullback_specSiteScheme B hX u hpush hX₂ hA hA₂).isoPullback_inv_snd

/-- The base change isomorphism of `AlgebraicGeometry.Space.specSiteBaseChangeIso` is
compatible with the projection to `Spec A`: that projection is `Spec` of `A → A₂`. -/
theorem specSiteBaseChangeIso_inv_left_comp_fst (u : A →+* A₂)
    (hpush : IsPushout
      (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom (algebraMap R R₂))
      (CommRingCat.ofHom u) (CommRingCat.ofHom (algebraMap R₂ A₂)))
    (hX₂ : B.Contains (Spec (.of R₂))) (hA : B.Contains (Spec (.of A)))
    (hA₂ : B.Contains (Spec (.of A₂))) :
    (specSiteBaseChangeIso B hX u hpush hX₂ hA hA₂).inv.left ≫
        pullback.fst (specSite B hX hA).hom (specSite B hX hX₂).hom =
      (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom u)) : B.obj hA₂ ⟶ B.obj hA) :=
  (isPullback_specSiteScheme B hX u hpush hX₂ hA hA₂).isoPullback_hom_fst

end BaseChange

end AlgebraicGeometry.Space

end

end
