module

public import StacksFrontier.AlgebraicGeometry.Descent.Algebra.SpecProduct

/-!
# `Spec` is fully faithful on algebras over a base

`AlgebraicGeometry.specOverMap_injective` says that `Spec` is faithful on morphisms of
`R`-algebras: two algebra maps inducing the same morphism of spectra over `Spec R` are equal.
This file supplies the other half, fullness, and packages the two as an equivalence.

So a morphism of schemes `Spec A₁ ⟶ Spec A₂` over `Spec R` is an `R`-algebra map `A₂ → A₁`, and an
isomorphism of such schemes is an isomorphism of `R`-algebras.

## Main definitions

* `AlgebraicGeometry.algHomOfSpecOverMap`: the `R`-algebra map underlying a morphism of spectra of
  `R`-algebras over `Spec R`.
* `AlgebraicGeometry.specOverMapEquiv`: the resulting bijection between morphisms over `Spec R` and
  `R`-algebra maps.
* `AlgebraicGeometry.algEquivOfSpecOverIso`: the `R`-algebra isomorphism underlying an
  isomorphism of spectra over `Spec R`.

## Main results

* `AlgebraicGeometry.specOverMap_algHomOfSpecOverMap` and
  `AlgebraicGeometry.algHomOfSpecOverMap_specOverMap`: the two round trips.
* `AlgebraicGeometry.specOverMapIso_symm` and `AlgebraicGeometry.specOverMapIso_trans`: `Spec` of
  an isomorphism of algebras, as an isomorphism of spectra, is contravariantly functorial.
* `AlgebraicGeometry.algHomOfSpecOverMap_comp` and `AlgebraicGeometry.algHomOfSpecOverMap_id`:
  the passage from morphisms over `Spec R` to `R`-algebra maps is functorial.

## Implementation notes

Fullness is `AlgebraicGeometry.Spec.preimage`, the preimage under the fully faithful functor
`Spec : CommRingCatᵒᵖ ⥤ Scheme`; the resulting ring map is an `R`-algebra map by the triangle
`Over.w` of the given morphism read through `AlgebraicGeometry.Spec.preimage_comp`.

`CategoryTheory.Functor.FullyFaithful.over` makes `Over.post Spec` fully faithful, and
`AlgebraicGeometry.algSpec.fullyFaithful` makes `Spec` fully faithful from `(CommAlgCat R)ᵒᵖ` to
`Over (Spec R)`. Both are stated for bundled algebra objects; the statements here are for a type
`A` carrying an `Algebra R A` instance, with `AlgebraicGeometry.specOver` and
`AlgebraicGeometry.specOverMap` as the passage to schemes.

## References

* [Stacks Project, Tag 01I1](https://stacks.math.columbia.edu/tag/01I1)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CommRingCat

variable {R : Type u} [CommRing R]
  {A₁ A₂ A₃ : Type u} [CommRing A₁] [CommRing A₂] [CommRing A₃]
  [Algebra R A₁] [Algebra R A₂] [Algebra R A₃]

/-- The `R`-algebra map `A₂ →ₐ[R] A₁` underlying a morphism `specOver R A₁ ⟶ specOver R A₂` of
spectra over `Spec R`. -/
def algHomOfSpecOverMap (f : specOver R A₁ ⟶ specOver R A₂) : A₂ →ₐ[R] A₁ where
  __ := (Spec.preimage f.left).hom
  commutes' r := by
    have h := Over.w f
    dsimp only [specOver, Over.mk_hom] at h
    have h2 := congrArg Spec.preimage h
    rw [Spec.preimage_comp, Spec.preimage_map, Spec.preimage_map] at h2
    exact congrArg (fun k ↦ (CommRingCat.Hom.hom k) r) h2

/-- `specOverMap` of the `R`-algebra map underlying a morphism `f` over `Spec R` is `f`. -/
@[simp]
lemma specOverMap_algHomOfSpecOverMap (f : specOver R A₁ ⟶ specOver R A₂) :
    specOverMap (algHomOfSpecOverMap f) = f :=
  Over.OverMorphism.ext (Spec.map_preimage f.left)

/-- The `R`-algebra map underlying `specOverMap p` is `p`. -/
@[simp]
lemma algHomOfSpecOverMap_specOverMap (p : A₂ →ₐ[R] A₁) :
    algHomOfSpecOverMap (specOverMap p) = p :=
  specOverMap_injective (specOverMap_algHomOfSpecOverMap _)

/-- Every morphism of spectra of `R`-algebras over `Spec R` is induced by an `R`-algebra map. -/
lemma specOverMap_surjective :
    Function.Surjective (specOverMap (R := R) (A₁ := A₁) (A₂ := A₂)) :=
  fun f ↦ ⟨algHomOfSpecOverMap f, specOverMap_algHomOfSpecOverMap f⟩

/-- `specOverMap` is a bijection between `R`-algebra maps `A₂ →ₐ[R] A₁` and morphisms
`specOver R A₁ ⟶ specOver R A₂` over `Spec R`. -/
lemma specOverMap_bijective :
    Function.Bijective (specOverMap (R := R) (A₁ := A₁) (A₂ := A₂)) :=
  ⟨specOverMap_injective, specOverMap_surjective⟩

/-- The bijection between morphisms `Spec A₁ ⟶ Spec A₂` of schemes over `Spec R` and `R`-algebra
maps `A₂ →ₐ[R] A₁`. -/
def specOverMapEquiv : (specOver R A₁ ⟶ specOver R A₂) ≃ (A₂ →ₐ[R] A₁) where
  toFun := algHomOfSpecOverMap
  invFun := specOverMap
  left_inv := specOverMap_algHomOfSpecOverMap
  right_inv := algHomOfSpecOverMap_specOverMap

/-- The forward map of `specOverMapEquiv` is `algHomOfSpecOverMap`. -/
@[simp]
lemma specOverMapEquiv_apply (f : specOver R A₁ ⟶ specOver R A₂) :
    specOverMapEquiv f = algHomOfSpecOverMap f := rfl

/-- The inverse map of `specOverMapEquiv` is `specOverMap`. -/
@[simp]
lemma specOverMapEquiv_symm_apply (p : A₂ →ₐ[R] A₁) :
    specOverMapEquiv.symm p = specOverMap p := rfl

/-- The `R`-algebra map underlying a composite `f ≫ g` of morphisms over `Spec R` is the composite
of the underlying algebra maps in the opposite order. -/
@[simp]
lemma algHomOfSpecOverMap_comp (f : specOver R A₁ ⟶ specOver R A₂)
    (g : specOver R A₂ ⟶ specOver R A₃) :
    algHomOfSpecOverMap (f ≫ g) =
      (algHomOfSpecOverMap f).comp (algHomOfSpecOverMap g) :=
  specOverMap_injective (by
    rw [specOverMap_algHomOfSpecOverMap, ← specOverMap_comp,
      specOverMap_algHomOfSpecOverMap, specOverMap_algHomOfSpecOverMap])

/-- The `R`-algebra map underlying the identity of `specOver R A₁` is the identity of `A₁`. -/
@[simp]
lemma algHomOfSpecOverMap_id :
    algHomOfSpecOverMap (𝟙 (specOver R A₁)) = AlgHom.id R A₁ :=
  specOverMap_injective (by rw [specOverMap_algHomOfSpecOverMap, specOverMap_id])

/-- The `R`-algebra isomorphism `A₂ ≃ₐ[R] A₁` underlying an isomorphism
`specOver R A₁ ≅ specOver R A₂` of spectra over `Spec R`. -/
def algEquivOfSpecOverIso (e : specOver R A₁ ≅ specOver R A₂) : A₂ ≃ₐ[R] A₁ :=
  AlgEquiv.ofAlgHom (algHomOfSpecOverMap e.hom) (algHomOfSpecOverMap e.inv)
    (by rw [← algHomOfSpecOverMap_comp, e.hom_inv_id, algHomOfSpecOverMap_id])
    (by rw [← algHomOfSpecOverMap_comp, e.inv_hom_id, algHomOfSpecOverMap_id])

/-- The underlying algebra map of `algEquivOfSpecOverIso e` is the one underlying `e.hom`. -/
@[simp]
lemma algEquivOfSpecOverIso_toAlgHom (e : specOver R A₁ ≅ specOver R A₂) :
    (algEquivOfSpecOverIso e).toAlgHom = algHomOfSpecOverMap e.hom := rfl

/-- `algEquivOfSpecOverIso e` acts on elements as the algebra map underlying `e.hom`. -/
@[simp]
lemma algEquivOfSpecOverIso_apply (e : specOver R A₁ ≅ specOver R A₂) (a : A₂) :
    algEquivOfSpecOverIso e a = algHomOfSpecOverMap e.hom a := rfl

/-- `specOverMapIso` of the `R`-algebra isomorphism underlying an isomorphism `e` over `Spec R` is
`e`. -/
@[simp]
lemma specOverMapIso_algEquivOfSpecOverIso (e : specOver R A₁ ≅ specOver R A₂) :
    specOverMapIso (algEquivOfSpecOverIso e) = e :=
  Iso.ext (specOverMap_algHomOfSpecOverMap e.hom)

/-- `specOverMapIso` commutes with taking inverses. -/
@[simp]
lemma specOverMapIso_symm (e : A₂ ≃ₐ[R] A₁) :
    (specOverMapIso e).symm = specOverMapIso e.symm := Iso.ext rfl

/-- `specOverMapIso` sends a composite `e.trans f` of algebra isomorphisms to the composite of the
induced isomorphisms of spectra in the opposite order. -/
lemma specOverMapIso_trans (e : A₃ ≃ₐ[R] A₂) (f : A₂ ≃ₐ[R] A₁) :
    specOverMapIso (e.trans f) = specOverMapIso f ≪≫ specOverMapIso e :=
  Iso.ext (specOverMap_comp f.toAlgHom e.toAlgHom).symm

/-- The `R`-algebra isomorphism underlying the identity isomorphism of `specOver R A₁` is the
identity of `A₁`. -/
@[simp]
lemma algEquivOfSpecOverIso_refl :
    algEquivOfSpecOverIso (Iso.refl (specOver R A₁)) = AlgEquiv.refl :=
  AlgEquiv.coe_toAlgHom_injective (by
    rw [algEquivOfSpecOverIso_toAlgHom, Iso.refl_hom, algHomOfSpecOverMap_id]
    rfl)

/-- The `R`-algebra isomorphism underlying `specOverMapIso φ` is `φ`. -/
@[simp]
lemma algEquivOfSpecOverIso_specOverMapIso (φ : A₂ ≃ₐ[R] A₁) :
    algEquivOfSpecOverIso (specOverMapIso φ) = φ :=
  AlgEquiv.coe_toAlgHom_injective (by
    rw [algEquivOfSpecOverIso_toAlgHom, specOverMapIso_hom, algHomOfSpecOverMap_specOverMap])

end AlgebraicGeometry

end

end
