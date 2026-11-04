module

public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Spectra of algebras over a fixed ring, as objects of the big fppf site

Fix a ring `A'` and a morphism `Spec A' ⟶ S`. An `A'`-algebra `R` whose spectrum lies in the big
fppf site gives an object `AlgebraicGeometry.Space.specOver` of the site over `S` through
`Spec R ⟶ Spec A' ⟶ S`, and a map of `A'`-algebras gives a morphism of such objects
(`AlgebraicGeometry.Space.specOverHom`). An affine object of the site, and an affine object over
it, are identified with such spectra (`AlgebraicGeometry.Space.isoSpecOverSelf`,
`AlgebraicGeometry.Space.isoSpecOver`): this is how lifting problems over affine objects are
reduced to lifting problems over rings.

## Main definitions

* `AlgebraicGeometry.Space.specOver` and `AlgebraicGeometry.Space.specOverHom`.
* `AlgebraicGeometry.Space.specStructure`: the structure morphism `Spec Γ(T') ⟶ S` of an affine
  object `T'`.
* `AlgebraicGeometry.Space.isoSpecOverSelf` and `AlgebraicGeometry.Space.isoSpecOver`.

## Main results

* `AlgebraicGeometry.Space.specOverHom_comp` and `AlgebraicGeometry.Space.specOverHom_id`:
  functoriality.
* `AlgebraicGeometry.Space.isoSpecOver_inv_comp`: a morphism of affine objects is, under these
  identifications, the spectrum of the map of rings of global sections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Spectra of algebras over a fixed ring, as objects of the site -/

section SpecOver

variable {A' : Type u} [CommRing A'] (s₀ : Spec (.of A') ⟶ S)

/-- The spectrum of an `A'`-algebra contained in the site, lying over `S` through a fixed
`Spec A' ⟶ S`. -/
abbrev specOver (R : Type u) [CommRing R] [Algebra A' R] (hR : B.Contains (Spec (.of R))) :
    BigFppfOver B S hS :=
  siteObject B S hS hR (Spec.map (CommRingCat.ofHom (algebraMap A' R)) ≫ s₀)

/-- The morphism of `specOver` objects induced by a map of `A'`-algebras. -/
def specOverHom {R R' : Type u} [CommRing R] [CommRing R'] [Algebra A' R] [Algebra A' R']
    (hR : B.Contains (Spec (.of R))) (hR' : B.Contains (Spec (.of R'))) (g : R →ₐ[A'] R') :
    specOver B S hS s₀ R' hR' ⟶ specOver B S hS s₀ R hR :=
  Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (g : R →+* R')))) (by
    apply ObjectProperty.hom_ext
    change Spec.map (CommRingCat.ofHom (g : R →+* R')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A' R)) ≫ s₀ =
      Spec.map (CommRingCat.ofHom (algebraMap A' R')) ≫ s₀
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, g.comp_algebraMap])

variable {B S hS s₀}

/-- The underlying morphism of schemes of `specOverHom` is `Spec` of the algebra map. -/
@[simp]
theorem toScheme_map_specOverHom {R R' : Type u} [CommRing R] [CommRing R'] [Algebra A' R]
    [Algebra A' R'] {hR : B.Contains (Spec (.of R))} {hR' : B.Contains (Spec (.of R'))}
    (g : R →ₐ[A'] R') :
    (BigFppfOver.toScheme B S hS).map (specOverHom B S hS s₀ hR hR' g) =
      Spec.map (CommRingCat.ofHom (g : R →+* R')) := rfl

/-- `specOverHom` sends a composite of algebra maps to the composite in the opposite order. -/
theorem specOverHom_comp {R R' R'' : Type u} [CommRing R] [CommRing R'] [CommRing R'']
    [Algebra A' R] [Algebra A' R'] [Algebra A' R''] {hR : B.Contains (Spec (.of R))}
    {hR' : B.Contains (Spec (.of R'))} {hR'' : B.Contains (Spec (.of R''))}
    (g : R →ₐ[A'] R') (g' : R' →ₐ[A'] R'') :
    specOverHom B S hS s₀ hR' hR'' g' ≫ specOverHom B S hS s₀ hR hR' g =
      specOverHom B S hS s₀ hR hR'' (g'.comp g) := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  rw [Functor.map_comp, toScheme_map_specOverHom, toScheme_map_specOverHom,
    toScheme_map_specOverHom, ← Spec.map_comp]
  rfl

/-- `specOverHom` of equal algebra maps agree. -/
theorem specOverHom_congr {R R' : Type u} [CommRing R] [CommRing R'] [Algebra A' R]
    [Algebra A' R'] {hR : B.Contains (Spec (.of R))} {hR' : B.Contains (Spec (.of R'))}
    {g g' : R →ₐ[A'] R'} (h : g = g') :
    specOverHom B S hS s₀ hR hR' g = specOverHom B S hS s₀ hR hR' g' := by
  subst h; rfl

/-- Two maps of `A'`-algebras out of `A'` agree. -/
theorem algHom_self_ext {R : Type u} [CommRing R] [Algebra A' R] (g g' : A' →ₐ[A'] R) :
    g = g' :=
  AlgHom.ext fun a => (g.commutes a).trans (g'.commutes a).symm

/-- `specOverHom` sends the identity algebra map to the identity. -/
@[simp]
theorem specOverHom_id {R : Type u} [CommRing R] [Algebra A' R]
    {hR : B.Contains (Spec (.of R))} :
    specOverHom B S hS s₀ hR hR (AlgHom.id A' R) = 𝟙 _ := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  rw [toScheme_map_specOverHom, CategoryTheory.Functor.map_id]
  exact Spec.map_id _

end SpecOver

/-! ### Affine objects as spectra of algebras over a base object -/

section IsoSpec

variable (T' : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]

/-- The structure morphism `Spec Γ(T') ⟶ S` of an affine object `T'` of the site. -/
abbrev specStructure : Spec (.of Γ((BigFppfOver.toScheme B S hS).obj T', ⊤)) ⟶ S :=
  ((BigFppfOver.toScheme B S hS).obj T').isoSpec.inv ≫ B.inclusion.map T'.hom

/-- The spectrum of the ring of global sections of an affine object of the site lies in the
site. -/
theorem contains_spec_sections (V : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] :
    B.Contains (Spec (.of Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))) :=
  Scheme.size_lt_of_mono_quasiCompact ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv
    V.left.property

/-- An affine object of the site is the spectrum of its ring of global sections, over `S`
through `Spec Γ(T') ⟶ S`. -/
def isoSpecOverSelf :
    T' ≅ specOver B S hS (specStructure B S hS T') Γ((BigFppfOver.toScheme B S hS).obj T', ⊤)
      (contains_spec_sections B S hS T') :=
  Over.isoMk (B.inclusion.preimageIso ((BigFppfOver.toScheme B S hS).obj T').isoSpec) (by
    apply B.inclusion.map_injective
    rw [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
    change ((BigFppfOver.toScheme B S hS).obj T').isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap _ _)) ≫
          ((BigFppfOver.toScheme B S hS).obj T').isoSpec.inv ≫ B.inclusion.map T'.hom = _
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp,
      Iso.hom_inv_id_assoc])

variable {T'} in
/-- An affine object `V` of the site over an affine object `T'` is the spectrum of its ring of
global sections, as an algebra over that of `T'`. -/
def isoSpecOver {V : BigFppfOver B S hS} (v : V ⟶ T')
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj T', ⊤) Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
    (hv : algebraMap Γ((BigFppfOver.toScheme B S hS).obj T', ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) =
        ((BigFppfOver.toScheme B S hS).map v).appTop.hom) :
    V ≅ specOver B S hS (specStructure B S hS T') Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      (contains_spec_sections B S hS V) :=
  Over.isoMk (B.inclusion.preimageIso ((BigFppfOver.toScheme B S hS).obj V).isoSpec) (by
    apply B.inclusion.map_injective
    rw [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
    change ((BigFppfOver.toScheme B S hS).obj V).isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap _ _)) ≫
          ((BigFppfOver.toScheme B S hS).obj T').isoSpec.inv ≫ B.inclusion.map T'.hom = _
    rw [hv, CommRingCat.ofHom_hom, Scheme.isoSpec_hom_naturality_assoc, Iso.hom_inv_id_assoc]
    exact (B.inclusion.map_comp v.left T'.hom).symm.trans (congrArg B.inclusion.map (Over.w v)))

/-- The underlying morphism of schemes of `(isoSpecOverSelf B S hS T').inv` is `isoSpec.inv`. -/
theorem toScheme_map_isoSpecOverSelf_inv :
    (BigFppfOver.toScheme B S hS).map (isoSpecOverSelf B S hS T').inv =
      ((BigFppfOver.toScheme B S hS).obj T').isoSpec.inv := by
  show B.inclusion.map (B.inclusion.preimageIso _).inv = _
  rw [Functor.preimageIso_inv, Functor.map_preimage]

variable {T'} in
/-- The underlying morphism of schemes of `(isoSpecOver B S hS v hv).inv` is `isoSpec.inv`. -/
theorem toScheme_map_isoSpecOver_inv {V : BigFppfOver B S hS} (v : V ⟶ T')
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj T', ⊤) Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
    (hv : algebraMap Γ((BigFppfOver.toScheme B S hS).obj T', ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) =
        ((BigFppfOver.toScheme B S hS).map v).appTop.hom) :
    (BigFppfOver.toScheme B S hS).map (isoSpecOver B S hS v hv).inv =
      ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv := by
  show B.inclusion.map (B.inclusion.preimageIso _).inv = _
  rw [Functor.preimageIso_inv, Functor.map_preimage]

variable {T'} in
/-- Under the identifications with spectra, a morphism `V ⟶ T'` of affine objects is the
spectrum of the structure map `Γ(T') ⟶ Γ(V)`. -/
theorem isoSpecOver_inv_comp {V : BigFppfOver B S hS} (v : V ⟶ T')
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj T', ⊤) Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
    (hv : algebraMap Γ((BigFppfOver.toScheme B S hS).obj T', ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) =
        ((BigFppfOver.toScheme B S hS).map v).appTop.hom) :
    (isoSpecOver B S hS v hv).inv ≫ v =
      specOverHom B S hS (specStructure B S hS T') (contains_spec_sections B S hS T')
        (contains_spec_sections B S hS V) (Algebra.ofId _ _) ≫ (isoSpecOverSelf B S hS T').inv := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  rw [Functor.map_comp, Functor.map_comp, toScheme_map_isoSpecOver_inv,
    toScheme_map_isoSpecOverSelf_inv, toScheme_map_specOverHom]
  show _ = Spec.map (CommRingCat.ofHom (algebraMap _ _)) ≫ _
  rw [hv, CommRingCat.ofHom_hom, Scheme.isoSpec_inv_naturality]

end IsoSpec

end AlgebraicGeometry.Space

end
