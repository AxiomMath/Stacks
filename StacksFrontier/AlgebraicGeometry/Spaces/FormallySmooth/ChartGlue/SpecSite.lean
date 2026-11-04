module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability

/-!
# Spectra of algebras over an affine object of the big fppf site

Let `T'` be an object of the big fppf site over `S` whose underlying scheme is affine, with ring
of global sections `A'`. An `A'`-algebra `C` whose spectrum belongs to the site gives an object
`Spec C` of the site over `S`, mapping to `T'` through `Spec C ⟶ Spec A' ≅ T'`, and an algebra
map `C → D` gives a morphism `Spec D ⟶ Spec C` over `T'`.

## Main definitions

* `AlgebraicGeometry.Space.ChartGlue.ringOf`: the ring `A' = Γ(T', ⊤)`.
* `AlgebraicGeometry.Space.ChartGlue.specObj`: the object `Spec C` of the site.
* `AlgebraicGeometry.Space.ChartGlue.specToT`: its morphism to `T'`.
* `AlgebraicGeometry.Space.ChartGlue.specMap`: the morphism `Spec D ⟶ Spec C` of an algebra map.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space.ChartGlue

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (T' : BigFppfOver B S hS)

/-- The ring of global sections `A' = Γ(T', ⊤)`. -/
abbrev ringOf : CommRingCat.{u} := Γ((BigFppfOver.toScheme B S hS).obj T', ⊤)

/-- The structure map of the spectrum of an `A'`-algebra, to `T'`, through `T' ≅ Spec A'` when `T'`
is affine. -/
def specStr (C : Type u) [CommRing C] [Algebra (ringOf B S hS T') C]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] :
    Spec (CommRingCat.of C) ⟶ (BigFppfOver.toScheme B S hS).obj T' :=
  Spec.map (CommRingCat.ofHom (algebraMap (ringOf B S hS T') C)) ≫
    ((BigFppfOver.toScheme B S hS).obj T').isoSpec.inv

variable [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]

/-- **The spectrum of an `A'`-algebra**, as an object of the site over `S`. -/
def specObj (C : Type u) [CommRing C] [Algebra (ringOf B S hS T') C]
    (hC : B.Contains (Spec (CommRingCat.of C))) : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS hC (specStr B S hS T' C ≫ B.inclusion.map T'.hom)

/-- The underlying scheme of `specObj B S hS T' C hC` is `Spec C`. -/
lemma toScheme_specObj (C : Type u) [CommRing C] [Algebra (ringOf B S hS T') C]
    (hC : B.Contains (Spec (CommRingCat.of C))) :
    (BigFppfOver.toScheme B S hS).obj (specObj B S hS T' C hC) = Spec (CommRingCat.of C) := rfl

/-- The morphism `Spec C ⟶ T'`. -/
def specToT (C : Type u) [CommRing C] [Algebra (ringOf B S hS T') C]
    (hC : B.Contains (Spec (CommRingCat.of C))) : specObj B S hS T' C hC ⟶ T' :=
  Over.homMk (ObjectProperty.homMk (specStr B S hS T' C)) (by
    apply ObjectProperty.hom_ext
    rfl)

/-- The underlying morphism of schemes of `specToT B S hS T' C hC` is `specStr B S hS T' C`. -/
lemma toScheme_map_specToT (C : Type u) [CommRing C] [Algebra (ringOf B S hS T') C]
    (hC : B.Contains (Spec (CommRingCat.of C))) :
    (BigFppfOver.toScheme B S hS).map (specToT B S hS T' C hC) = specStr B S hS T' C := rfl

/-- For an `A'`-algebra map `f : C → D`, the structure map of `Spec D` to `T'` factors as `Spec f`
followed by the structure map of `Spec C`. -/
lemma specMap_comm {C D : Type u} [CommRing C] [Algebra (ringOf B S hS T') C] [CommRing D]
    [Algebra (ringOf B S hS T') D] (f : C →ₐ[ringOf B S hS T'] D) :
    Spec.map (CommRingCat.ofHom (f : C →+* D)) ≫ specStr B S hS T' C = specStr B S hS T' D := by
  simp only [specStr, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    AlgHom.comp_algebraMap]

/-- **The morphism `Spec D ⟶ Spec C` of an algebra map `C → D`.** -/
def specMap {C D : Type u} [CommRing C] [Algebra (ringOf B S hS T') C] [CommRing D]
    [Algebra (ringOf B S hS T') D] (hC : B.Contains (Spec (CommRingCat.of C)))
    (hD : B.Contains (Spec (CommRingCat.of D))) (f : C →ₐ[ringOf B S hS T'] D) :
    specObj B S hS T' D hD ⟶ specObj B S hS T' C hC :=
  BigFppfOver.homMk B S hS hC _ (Spec.map (CommRingCat.ofHom (f : C →+* D))) (by
    change Spec.map (CommRingCat.ofHom (f : C →+* D)) ≫ specStr B S hS T' C ≫
      B.inclusion.map T'.hom = specStr B S hS T' D ≫ B.inclusion.map T'.hom
    rw [← Category.assoc, specMap_comm])

/-- The underlying morphism of schemes of `specMap B S hS T' hC hD f` is `Spec f`. -/
lemma toScheme_map_specMap {C D : Type u} [CommRing C] [Algebra (ringOf B S hS T') C] [CommRing D]
    [Algebra (ringOf B S hS T') D] (hC : B.Contains (Spec (CommRingCat.of C)))
    (hD : B.Contains (Spec (CommRingCat.of D))) (f : C →ₐ[ringOf B S hS T'] D) :
    (BigFppfOver.toScheme B S hS).map (specMap B S hS T' hC hD f) =
      Spec.map (CommRingCat.ofHom (f : C →+* D)) := rfl

/-- The morphism `specMap B S hS T' hC hD f` is a morphism over `T'`. -/
lemma specMap_specToT {C D : Type u} [CommRing C] [Algebra (ringOf B S hS T') C] [CommRing D]
    [Algebra (ringOf B S hS T') D] (hC : B.Contains (Spec (CommRingCat.of C)))
    (hD : B.Contains (Spec (CommRingCat.of D))) (f : C →ₐ[ringOf B S hS T'] D) :
    specMap B S hS T' hC hD f ≫ specToT B S hS T' C hC = specToT B S hS T' D hD :=
  (BigFppfOver.toScheme B S hS).map_injective (specMap_comm B S hS T' f)

/-- `specMap` reverses composition: the morphism of `g.comp f` is that of `g` followed by that of
`f`. -/
lemma specMap_comp {C D E : Type u} [CommRing C] [Algebra (ringOf B S hS T') C] [CommRing D]
    [Algebra (ringOf B S hS T') D] [CommRing E] [Algebra (ringOf B S hS T') E]
    (hC : B.Contains (Spec (CommRingCat.of C))) (hD : B.Contains (Spec (CommRingCat.of D)))
    (hE : B.Contains (Spec (CommRingCat.of E))) (f : C →ₐ[ringOf B S hS T'] D)
    (g : D →ₐ[ringOf B S hS T'] E) :
    specMap B S hS T' hC hE (g.comp f) = specMap B S hS T' hD hE g ≫ specMap B S hS T' hC hD f := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  change Spec.map (CommRingCat.ofHom ((g.comp f : C →ₐ[_] E) : C →+* E)) =
    Spec.map (CommRingCat.ofHom (g : D →+* E)) ≫ Spec.map (CommRingCat.ofHom (f : C →+* D))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- `specMap` sends the identity algebra map to the identity morphism. -/
lemma specMap_id {C : Type u} [CommRing C] [Algebra (ringOf B S hS T') C]
    (hC : B.Contains (Spec (CommRingCat.of C))) :
    specMap B S hS T' hC hC (AlgHom.id _ C) = 𝟙 _ :=
  (BigFppfOver.toScheme B S hS).map_injective (Spec.map_id (CommRingCat.of C))

end AlgebraicGeometry.Space.ChartGlue

end
