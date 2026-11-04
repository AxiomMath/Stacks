module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Products of affine schemes over an affine base are spectra of tensor products

Let `R` be a commutative ring.  The spectra of `R`-algebras, viewed as schemes over `Spec R`,
are closed under binary products, and the product of `Spec A₁` and `Spec A₂` is the spectrum of
`A₁ ⊗[R] A₂`.  This file records that identification together with the dictionary that makes it
usable: the two projections are the two inclusions of the tensor factors, and the morphism
induced into a product by a pair of morphisms is the morphism induced out of a tensor product by
a pair of algebra maps.

Everything is phrased in the category `Over (Spec R)`.

## Main definitions

* `AlgebraicGeometry.specOver` is `Spec A` for an `R`-algebra `A`, as a scheme over `Spec R`.
* `AlgebraicGeometry.specOverMap` is `Spec` of an `R`-algebra map, as a morphism over `Spec R`.
* `AlgebraicGeometry.specOverProdIso` identifies `specOver R A₁ ⨯ specOver R A₂` with
  `specOver R (A₁ ⊗[R] A₂)`.

## Main results

* `AlgebraicGeometry.specOverMap_injective`: `Spec` is faithful on `R`-algebra maps.
* `AlgebraicGeometry.specOverProdIso_inv_fst` and
  `AlgebraicGeometry.specOverProdIso_inv_snd`: the two projections of the product are `Spec` of
  the two inclusions `A₁ → A₁ ⊗[R] A₂` and `A₂ → A₁ ⊗[R] A₂`.
* `AlgebraicGeometry.prod_lift_specOverMap`: the morphism into the product induced by `Spec` of
  two algebra maps `p : A₁ →ₐ[R] T` and `q : A₂ →ₐ[R] T` is `Spec` of
  `Algebra.TensorProduct.lift p q`.

## Implementation notes

The underlying isomorphism of schemes is `CategoryTheory.Over.prodLeftIsoPullback` followed by
`AlgebraicGeometry.pullbackSpecIso`; that this is a morphism over `Spec R` is
`AlgebraicGeometry.pullbackSpecIso_hom_base`.  All further computations are reduced to the two
projections by `CategoryTheory.Limits.prod.hom_ext`, so no property of `Spec` beyond its
faithfulness is used.

Every ring here lives in a single universe, because `AlgebraicGeometry.pullbackSpecIso` is
stated for rings in the universe of the schemes.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits TensorProduct CommRingCat

variable (R : Type u) [CommRing R]

/-- `Spec A` for an `R`-algebra `A`, as a scheme over `Spec R`. -/
abbrev specOver (A : Type u) [CommRing A] [Algebra R A] : Over (Spec (.of R)) :=
  Over.mk (Spec.map (ofHom (algebraMap R A)))

section Map

variable {R}
variable {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂] [Algebra R A₁] [Algebra R A₂]

/-- `Spec` of a morphism of `R`-algebras, as a morphism of schemes over `Spec R`. -/
def specOverMap (p : A₂ →ₐ[R] A₁) : specOver R A₁ ⟶ specOver R A₂ :=
  Over.homMk (Spec.map (ofHom p.toRingHom)) (by
    dsimp only [specOver, Over.mk_hom]
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact p.commutes r)

/-- The underlying morphism of schemes of `specOverMap p` is `Spec.map` of `p`. -/
@[simp]
lemma specOverMap_left (p : A₂ →ₐ[R] A₁) :
    (specOverMap p).left = Spec.map (ofHom p.toRingHom) := rfl

/-- `Spec` is faithful on morphisms of `R`-algebras. -/
lemma specOverMap_injective : Function.Injective (specOverMap (R := R) (A₁ := A₁) (A₂ := A₂)) := by
  intro p q h
  have h' : Spec.map (ofHom p.toRingHom) = Spec.map (ofHom q.toRingHom) :=
    congrArg Over.Hom.left h
  exact AlgHom.coe_ringHom_injective (congrArg CommRingCat.Hom.hom (Spec.map_injective h'))

/-- `Spec` of the identity `R`-algebra map is the identity morphism over `Spec R`. -/
@[simp]
lemma specOverMap_id : specOverMap (AlgHom.id R A₁) = 𝟙 (specOver R A₁) := by
  apply Over.OverMorphism.ext
  rw [specOverMap_left, Over.id_left,
    show ofHom (AlgHom.id R A₁).toRingHom = 𝟙 (CommRingCat.of A₁) from rfl, Spec.map_id]
  rfl

variable {A₃ : Type u} [CommRing A₃] [Algebra R A₃]

/-- `Spec` reverses composition of `R`-algebra maps: `specOverMap p ≫ specOverMap q` is
`specOverMap (p.comp q)`. -/
@[reassoc]
lemma specOverMap_comp (p : A₂ →ₐ[R] A₁) (q : A₃ →ₐ[R] A₂) :
    specOverMap p ≫ specOverMap q = specOverMap (p.comp q) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, specOverMap_left, specOverMap_left, specOverMap_left, ← Spec.map_comp]
  rfl

/-- `Spec` of an isomorphism of `R`-algebras, as an isomorphism of schemes over `Spec R`. -/
def specOverMapIso (e : A₂ ≃ₐ[R] A₁) : specOver R A₁ ≅ specOver R A₂ where
  hom := specOverMap e.toAlgHom
  inv := specOverMap e.symm.toAlgHom
  hom_inv_id := by
    rw [specOverMap_comp, show e.toAlgHom.comp e.symm.toAlgHom = AlgHom.id R A₁ from
      AlgHom.ext fun x ↦ e.apply_symm_apply x, specOverMap_id]
  inv_hom_id := by
    rw [specOverMap_comp, show e.symm.toAlgHom.comp e.toAlgHom = AlgHom.id R A₂ from
      AlgHom.ext fun x ↦ e.symm_apply_apply x, specOverMap_id]

/-- The forward morphism of `specOverMapIso e` is `Spec` of the algebra map underlying `e`. -/
@[simp]
lemma specOverMapIso_hom (e : A₂ ≃ₐ[R] A₁) :
    (specOverMapIso e).hom = specOverMap e.toAlgHom := rfl

/-- The inverse morphism of `specOverMapIso e` is `Spec` of the algebra map underlying
`e.symm`. -/
@[simp]
lemma specOverMapIso_inv (e : A₂ ≃ₐ[R] A₁) :
    (specOverMapIso e).inv = specOverMap e.symm.toAlgHom := rfl

end Map

section Prod

variable (A₁ A₂ : Type u) [CommRing A₁] [CommRing A₂] [Algebra R A₁] [Algebra R A₂]

/-- The product of `Spec A₁` and `Spec A₂` over `Spec R` is `Spec (A₁ ⊗[R] A₂)`. -/
def specOverProdIso :
    (specOver R A₁ ⨯ specOver R A₂) ≅ specOver R (A₁ ⊗[R] A₂) :=
  Over.isoMk
    (Over.prodLeftIsoPullback (specOver R A₁) (specOver R A₂) ≪≫ pullbackSpecIso R A₁ A₂)
    (by
      have h1 : (Over.prodLeftIsoPullback (specOver R A₁) (specOver R A₂)).hom ≫
          pullback.fst (Spec.map (ofHom (algebraMap R A₁)))
            (Spec.map (ofHom (algebraMap R A₂))) =
            (prod.fst : specOver R A₁ ⨯ specOver R A₂ ⟶ specOver R A₁).left :=
        Over.prodLeftIsoPullback_hom_fst ..
      dsimp only [specOver, Over.mk_hom, Iso.trans_hom]
      rw [Category.assoc, pullbackSpecIso_hom_base, ← Category.assoc, h1]
      exact Over.w (prod.fst : specOver R A₁ ⨯ specOver R A₂ ⟶ specOver R A₁))

/-- The underlying morphism of schemes of the inverse of `specOverProdIso` is the inverse of
`AlgebraicGeometry.pullbackSpecIso` followed by that of
`CategoryTheory.Over.prodLeftIsoPullback`. -/
lemma specOverProdIso_inv_left :
    (specOverProdIso R A₁ A₂).inv.left =
      (pullbackSpecIso R A₁ A₂).inv ≫
        (Over.prodLeftIsoPullback (specOver R A₁) (specOver R A₂)).inv := rfl

/-- Under `specOverProdIso`, the first projection of the product is `Spec` of the inclusion
`A₁ → A₁ ⊗[R] A₂`. -/
@[reassoc (attr := simp)]
lemma specOverProdIso_inv_fst :
    (specOverProdIso R A₁ A₂).inv ≫ prod.fst =
      specOverMap (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := A₁) (B := A₂)) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, specOverProdIso_inv_left, specOverMap_left, Category.assoc,
    Over.prodLeftIsoPullback_inv_fst]
  exact pullbackSpecIso_inv_fst R A₁ A₂

/-- Under `specOverProdIso`, the second projection of the product is `Spec` of the inclusion
`A₂ → A₁ ⊗[R] A₂`. -/
@[reassoc (attr := simp)]
lemma specOverProdIso_inv_snd :
    (specOverProdIso R A₁ A₂).inv ≫ prod.snd =
      specOverMap (Algebra.TensorProduct.includeRight (R := R) (A := A₁) (B := A₂)) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, specOverProdIso_inv_left, specOverMap_left, Category.assoc,
    Over.prodLeftIsoPullback_inv_snd]
  exact pullbackSpecIso_inv_snd R A₁ A₂

variable {T : Type u} [CommRing T] [Algebra R T]

/-- The morphism into a product of spectra induced by `Spec` of two algebra maps is `Spec` of
the morphism out of the tensor product that they induce. -/
lemma prod_lift_specOverMap (p : A₁ →ₐ[R] T) (q : A₂ →ₐ[R] T) :
    (prod.lift (specOverMap p) (specOverMap q) : specOver R T ⟶ _) ≫
        (specOverProdIso R A₁ A₂).hom =
      specOverMap (Algebra.TensorProduct.lift p q fun _ _ ↦ Commute.all _ _) := by
  rw [← Iso.eq_comp_inv]
  apply prod.hom_ext
  · rw [prod.lift_fst, Category.assoc, specOverProdIso_inv_fst, specOverMap_comp,
      Algebra.TensorProduct.lift_comp_includeLeft]
  · rw [prod.lift_snd, Category.assoc, specOverProdIso_inv_snd, specOverMap_comp,
      Algebra.TensorProduct.lift_comp_includeRight']

end Prod

end AlgebraicGeometry

end

end
