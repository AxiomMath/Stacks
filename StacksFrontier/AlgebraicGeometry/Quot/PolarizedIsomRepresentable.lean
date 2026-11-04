module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitEqualizerTorsion
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedIsoOverBase
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedIsomSheaf
public import StacksFrontier.AlgebraicGeometry.Scheme.SpecRingHomEquiv
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOpenRepresentability
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria

/-!
# Representability of the isomorphism presheaf of `𝒫olarized`

Let `x`, `y` be two objects of the stack `𝒫olarized` of polarized families over an object `U` of
the big fppf site of a terminal scheme `S`, and write `U'` for the scheme underlying `U`. This file
proves that the presheaf `Isom(x, y)` on the big fppf site of `U'` is representable, given two
inputs: that it is an fppf sheaf, and that the isomorphisms of polarized families over an affine
base are corepresented
(`AlgebraicGeometry.PolarizedFamily.IsIsoOverBaseCorepresented`).

By `AlgebraicGeometry.Space.isRepresentable_of_isAffineOpen_represented` it suffices to
represent, for every affine open `V` of `U'`, the functor `T ↦ Isom(x, y)(T) × Hom(T, V)` on
affine test objects `T`. With `a`, `b` the chosen pullbacks of `x`, `y` to `V`, the
corepresentability hypothesis gives a `Γ(V)`-algebra `H`; the representing object is `Spec H`
over `V`, and the representing section is the isomorphism corresponding to the identity of
`Spec H`.

## Main definitions

* `AlgebraicGeometry.specHomEquivGlobalSections`: morphisms `Y ⟶ Spec R` as ring maps
  `R ⟶ Γ(Y, ⊤)`.
* `AlgebraicGeometry.BigFppfOver.specAlgebraObj` and
  `AlgebraicGeometry.BigFppfOver.specAlgebraHom`: the spectrum of an algebra over the global
  sections of an affine object `W₀` of the site, as an object of the site over `W₀`.
* `AlgebraicGeometry.BigFppfOver.specAlgebraHomEquiv`: morphisms into it over `W₀` are ring maps
  over `Γ(W₀)`.
* `AlgebraicGeometry.polarizedIsomSectionEquiv`: the sections of `Isom(x, y)` over `W` are the
  morphisms of polarized families between the chosen pullbacks over the identity of the base.

## Main results

* `AlgebraicGeometry.comp_specMap_comp_isoSpec_inv_eq_iff`: morphisms into `Spec R` over an
  affine scheme `A`, for a `Γ(A)`-algebra `R`.
* `AlgebraicGeometry.polarizedIsomSectionEquiv_map`: the restriction maps of `Isom(x, y)` in
  these terms.
* `AlgebraicGeometry.exists_bijective_polarizedIsomPresheaf_specAlgebraObj`: over an affine
  object `W₀`, the corepresenting algebra represents `Isom(x, y) × Hom(-, W₀)` on affine test
  objects.
* `AlgebraicGeometry.isRepresentable_isomPresheaf_of_corepresented`: `Isom(x, y)` is
  representable.

## Implementation notes

The bases of the chosen pullbacks are equal to the underlying schemes of the objects of the site
only propositionally, so the comparison maps carry `eqToHom`s; the statements about
`AlgebraicGeometry.BigFppfOver.specAlgebraObj` are phrased with an arbitrary scheme `Y` of the
site and an equality `Y = W.left`, which is then instantiated with the base of a chosen pullback.

The object `AlgebraicGeometry.BigFppfOver.specAlgebraObj` has underlying scheme `Spec R` only up
to unfolding, so its morphisms are handled through
`AlgebraicGeometry.BigFppfOver.specAlgebraObjHomScheme` and
`AlgebraicGeometry.BigFppfOver.specAlgebraObjHomMk`, whose types display `Spec R`; similarly
`AlgebraicGeometry.specHomEquivGlobalSections` is `AlgebraicGeometry.specRingHomEquiv` with its
target displayed as `Γ(Y, ⊤)`.

## References

* [Stacks Project, Tag 0D42](https://stacks.math.columbia.edu/tag/0D42)
* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-! ### Morphisms into the spectrum of an algebra over an affine scheme -/

/-- `AlgebraicGeometry.specRingHomEquiv` with its target written as the global sections
`Γ(Y, ⊤)`: morphisms `Y ⟶ Spec R` are the ring maps `R ⟶ Γ(Y, ⊤)`. -/
def specHomEquivGlobalSections (R : Type u) [CommRing R] (Y : Scheme.{u}) :
    (Y ⟶ Spec (CommRingCat.of R)) ≃ (R →+* Γ(Y, ⊤)) :=
  specRingHomEquiv R Y

/-- `AlgebraicGeometry.specHomEquivGlobalSections` is natural in the scheme. -/
theorem specHomEquivGlobalSections_comp (R : Type u) [CommRing R] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Spec (CommRingCat.of R)) :
    specHomEquivGlobalSections R X (f ≫ g) =
      f.appTop.hom.comp (specHomEquivGlobalSections R Y g) :=
  specRingHomEquiv_comp R f g

/-- `AlgebraicGeometry.specHomEquivGlobalSections` is the map induced on global sections, read
through the global-sections isomorphism of the spectrum. -/
theorem specHomEquivGlobalSections_apply (R : Type u) [CommRing R] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of R)) :
    specHomEquivGlobalSections R Y g =
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appTop).hom := by
  have h := specHomEquivGlobalSections_comp R g (𝟙 _)
  rw [Category.comp_id] at h
  rw [h, show specHomEquivGlobalSections R _ (𝟙 (Spec (CommRingCat.of R))) =
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom from specRingHomEquiv_id R]
  rfl

/-- **Morphisms into `Spec R` over an affine scheme.** For an affine scheme `A` and a ring map
`ι : Γ(A) ⟶ R`, a morphism `g : Y ⟶ Spec R` lies over `τ : Y ⟶ A` (through
`Spec R ⟶ Spec Γ(A) ≅ A`) exactly when its ring map `R ⟶ Γ(Y)` restricts along `ι` to the map
induced by `τ` on global sections. -/
theorem comp_specMap_comp_isoSpec_inv_eq_iff {A Y : Scheme.{u}} [IsAffine A] {R : Type u}
    [CommRing R] (ι : Γ(A, ⊤) →+* R) (g : Y ⟶ Spec (CommRingCat.of R)) (τ : Y ⟶ A) :
    g ≫ Spec.map (CommRingCat.ofHom ι) ≫ A.isoSpec.inv = τ ↔
      (specHomEquivGlobalSections R Y g).comp ι = τ.appTop.hom := by
  rw [specHomEquivGlobalSections_apply]
  constructor
  · rintro rfl
    rw [Scheme.Hom.comp_appTop, Scheme.appTop_specMap_comp_isoSpec_inv]
    rfl
  · intro h
    apply ext_of_isAffine
    rw [Scheme.Hom.comp_appTop, Scheme.appTop_specMap_comp_isoSpec_inv]
    ext r
    exact congrArg (fun φ : Γ(A, ⊤) →+* Γ(Y, ⊤) => φ r) h

/-! ### The spectrum of an algebra over an affine object of the site -/

namespace BigFppfOver

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)

section SpecAlgebra

variable {W₀ : BigFppfOver B S hS} {Z : B.Schemes} (hZ : Z = W₀.left)
  [IsAffine (B.inclusion.obj Z)] {R : Type u} [CommRing R] (ι : Γ(B.inclusion.obj Z, ⊤) →+* R)
  (hR : B.Contains (Spec (CommRingCat.of R)))

/-- The structure morphism `Spec R ⟶ Spec Γ(Z) ≅ Z = W₀` of the spectrum of an algebra `R` over
the ring of global sections of an affine scheme `Z` of the site equal to the underlying scheme of
`W₀`. -/
def specAlgebraToScheme : Spec (CommRingCat.of R) ⟶ B.inclusion.obj W₀.left :=
  Spec.map (CommRingCat.ofHom ι) ≫ (B.inclusion.obj Z).isoSpec.inv ≫
    eqToHom (congrArg B.inclusion.obj hZ)

/-- The spectrum of an algebra `R` over the global sections of an affine scheme `Z = W₀`, as an
object of the big fppf site of `S`, through `Spec R ⟶ W₀ ⟶ S`. -/
def specAlgebraObj : BigFppfOver B S hS :=
  Over.mk (ObjectProperty.homMk (X := B.obj hR) (Y := B.obj hS)
    (specAlgebraToScheme B hS hZ ι ≫ B.inclusion.map W₀.hom))

/-- The structure morphism of `AlgebraicGeometry.BigFppfOver.specAlgebraObj` to `W₀`, as a
morphism of the site. -/
def specAlgebraHom : specAlgebraObj B hS hZ ι hR ⟶ W₀ :=
  Over.homMk (ObjectProperty.homMk (X := B.obj hR) (specAlgebraToScheme B hS hZ ι)) rfl

/-- The morphism of schemes `W ⟶ Spec R` underlying a morphism of the site into
`AlgebraicGeometry.BigFppfOver.specAlgebraObj`. -/
def specAlgebraObjHomScheme {W : BigFppfOver B S hS} (f : W ⟶ specAlgebraObj B hS hZ ι hR) :
    B.inclusion.obj W.left ⟶ Spec (CommRingCat.of R) :=
  B.inclusion.map f.left

/-- A morphism of schemes `W ⟶ Spec R` over `S` as a morphism of the site into
`AlgebraicGeometry.BigFppfOver.specAlgebraObj`. -/
def specAlgebraObjHomMk {W : BigFppfOver B S hS}
    (g : B.inclusion.obj W.left ⟶ Spec (CommRingCat.of R))
    (hg : g ≫ specAlgebraToScheme B hS hZ ι ≫ B.inclusion.map W₀.hom = B.inclusion.map W.hom) :
    W ⟶ specAlgebraObj B hS hZ ι hR :=
  Over.homMk (ObjectProperty.homMk g) (ObjectProperty.hom_ext _ hg)

/-- The underlying morphism of `AlgebraicGeometry.BigFppfOver.specAlgebraObjHomMk`. -/
theorem specAlgebraObjHomScheme_homMk {W : BigFppfOver B S hS}
    (g : B.inclusion.obj W.left ⟶ Spec (CommRingCat.of R))
    (hg : g ≫ specAlgebraToScheme B hS hZ ι ≫ B.inclusion.map W₀.hom = B.inclusion.map W.hom) :
    specAlgebraObjHomScheme B hS hZ ι hR (specAlgebraObjHomMk B hS hZ ι hR g hg) = g :=
  rfl

/-- The underlying morphism of a composite with the structure morphism to `W₀`. -/
theorem specAlgebraObjHomScheme_comp {W : BigFppfOver B S hS}
    (f : W ⟶ specAlgebraObj B hS hZ ι hR) :
    specAlgebraObjHomScheme B hS hZ ι hR f ≫ specAlgebraToScheme B hS hZ ι =
      B.inclusion.map (f ≫ specAlgebraHom B hS hZ ι hR).left :=
  rfl

/-- The underlying morphism of a precomposite. -/
theorem specAlgebraObjHomScheme_precomp {W W' : BigFppfOver B S hS} (k : W' ⟶ W)
    (f : W ⟶ specAlgebraObj B hS hZ ι hR) :
    specAlgebraObjHomScheme B hS hZ ι hR (k ≫ f) =
      B.inclusion.map k.left ≫ specAlgebraObjHomScheme B hS hZ ι hR f :=
  rfl

/-- The underlying morphism of the identity. -/
theorem specAlgebraObjHomScheme_id :
    specAlgebraObjHomScheme B hS hZ ι hR (𝟙 _) = 𝟙 (Spec (CommRingCat.of R)) :=
  rfl

/-- A morphism of the site into `AlgebraicGeometry.BigFppfOver.specAlgebraObj` is determined by
its underlying morphism of schemes. -/
theorem specAlgebraObjHomScheme_injective {W : BigFppfOver B S hS}
    {f₁ f₂ : W ⟶ specAlgebraObj B hS hZ ι hR}
    (h : specAlgebraObjHomScheme B hS hZ ι hR f₁ = specAlgebraObjHomScheme B hS hZ ι hR f₂) :
    f₁ = f₂ := by
  ext1
  exact B.inclusion.map_injective h

/-- The ring map `R ⟶ Γ(Y)` of a morphism `f : W ⟶ Spec R` of the site, read on a scheme `Y`
of the site equal to the underlying scheme of `W`. -/
def specAlgebraRingHom {W : BigFppfOver B S hS} {Y : B.Schemes} (hY : Y = W.left)
    (f : W ⟶ specAlgebraObj B hS hZ ι hR) : R →+* Γ(B.inclusion.obj Y, ⊤) :=
  specHomEquivGlobalSections R (B.inclusion.obj Y)
    (eqToHom (congrArg B.inclusion.obj hY) ≫ specAlgebraObjHomScheme B hS hZ ι hR f)

/-- `AlgebraicGeometry.BigFppfOver.specAlgebraRingHom` is injective in the morphism. -/
theorem specAlgebraRingHom_injective {W : BigFppfOver B S hS} {Y : B.Schemes} (hY : Y = W.left)
    {f₁ f₂ : W ⟶ specAlgebraObj B hS hZ ι hR}
    (h : specAlgebraRingHom B hS hZ ι hR hY f₁ = specAlgebraRingHom B hS hZ ι hR hY f₂) :
    f₁ = f₂ :=
  specAlgebraObjHomScheme_injective B hS hZ ι hR
    ((cancel_epi _).1 ((specHomEquivGlobalSections R _).injective h))

/-- A morphism `g : W ⟶ Spec R` lies over `t : W ⟶ W₀` exactly when its ring map, read on
`Y = W`, restricts along `ι` to the map on global sections of `Y = W ⟶ W₀ = Z`. -/
theorem comp_specAlgebraToScheme_eq_iff {W : BigFppfOver B S hS} {Y : B.Schemes}
    (hY : Y = W.left) (t : W ⟶ W₀) (g : B.inclusion.obj W.left ⟶ Spec (CommRingCat.of R)) :
    g ≫ specAlgebraToScheme B hS hZ ι = B.inclusion.map t.left ↔
      (specHomEquivGlobalSections R (B.inclusion.obj Y)
          (eqToHom (congrArg B.inclusion.obj hY) ≫ g)).comp ι =
        (eqToHom (congrArg B.inclusion.obj hY) ≫ B.inclusion.map t.left ≫
          eqToHom (congrArg B.inclusion.obj hZ).symm).appTop.hom := by
  rw [← comp_specMap_comp_isoSpec_inv_eq_iff, specAlgebraToScheme]
  constructor
  · intro h
    rw [← h]
    simp
  · intro h
    rw [← cancel_epi (eqToHom (congrArg B.inclusion.obj hY)), ← cancel_mono
      (eqToHom (congrArg B.inclusion.obj hZ).symm)]
    simpa using h

/-- **Morphisms into `Spec R` over `W₀` are ring maps.** For `t : W ⟶ W₀`, the morphisms
`f : W ⟶ Spec R` with `f ≫ (Spec R ⟶ W₀) = t` correspond, through
`AlgebraicGeometry.BigFppfOver.specAlgebraRingHom`, to the ring maps `R ⟶ Γ(Y)` restricting
along `ι` to the map on global sections of `Y = W ⟶ W₀ = Z`. -/
def specAlgebraHomEquiv {W : BigFppfOver B S hS} {Y : B.Schemes} (hY : Y = W.left)
    (t : W ⟶ W₀) :
    {f : W ⟶ specAlgebraObj B hS hZ ι hR // f ≫ specAlgebraHom B hS hZ ι hR = t} ≃
      {φ : R →+* Γ(B.inclusion.obj Y, ⊤) // φ.comp ι =
        (eqToHom (congrArg B.inclusion.obj hY) ≫ B.inclusion.map t.left ≫
          eqToHom (congrArg B.inclusion.obj hZ).symm).appTop.hom} where
  toFun f := ⟨specAlgebraRingHom B hS hZ ι hR hY f.1,
    (comp_specAlgebraToScheme_eq_iff B hS hZ ι hY t _).1 (by
      rw [specAlgebraObjHomScheme_comp, f.2])⟩
  invFun φ := by
    have h := (comp_specAlgebraToScheme_eq_iff B hS hZ ι hY t
      (eqToHom (congrArg B.inclusion.obj hY).symm ≫
        (specHomEquivGlobalSections R _).symm φ.1)).2 (by simpa using φ.2)
    refine ⟨specAlgebraObjHomMk B hS hZ ι hR
      (eqToHom (congrArg B.inclusion.obj hY).symm ≫ (specHomEquivGlobalSections R _).symm φ.1)
      ?_, ?_⟩
    · rw [Category.assoc, reassoc_of% h, ← Functor.map_comp, Over.w t]
    · ext1
      apply B.inclusion.map_injective
      rw [← specAlgebraObjHomScheme_comp, specAlgebraObjHomScheme_homMk, h]
  left_inv f := by
    apply Subtype.ext
    apply specAlgebraObjHomScheme_injective B hS hZ ι hR
    simp [specAlgebraRingHom, specAlgebraObjHomScheme_homMk]
  right_inv φ := by
    apply Subtype.ext
    simp [specAlgebraRingHom, specAlgebraObjHomScheme_homMk]

/-- The first component of `AlgebraicGeometry.BigFppfOver.specAlgebraHomEquiv` is
`AlgebraicGeometry.BigFppfOver.specAlgebraRingHom`. -/
theorem specAlgebraHomEquiv_apply_coe {W : BigFppfOver B S hS} {Y : B.Schemes}
    (hY : Y = W.left) (t : W ⟶ W₀)
    (f : {f : W ⟶ specAlgebraObj B hS hZ ι hR // f ≫ specAlgebraHom B hS hZ ι hR = t}) :
    (specAlgebraHomEquiv B hS hZ ι hR hY t f).1 = specAlgebraRingHom B hS hZ ι hR hY f.1 :=
  rfl

/-- **Naturality of `AlgebraicGeometry.BigFppfOver.specAlgebraRingHom`.** The ring map of
`f : W ⟶ Spec R` is that of the identity of `Spec R` followed by the map on global sections of
`f`, read on schemes `Y = W` and `Y' = Spec R` of the site. -/
theorem specAlgebraRingHom_eq_comp {W : BigFppfOver B S hS} {Y Y' : B.Schemes} (hY : Y = W.left)
    (hY' : Y' = (specAlgebraObj B hS hZ ι hR).left) (f : W ⟶ specAlgebraObj B hS hZ ι hR)
    (k : Y ⟶ Y') (hk : k = eqToHom hY ≫ f.left ≫ eqToHom hY'.symm) :
    specAlgebraRingHom B hS hZ ι hR hY f =
      (B.inclusion.map k).appTop.hom.comp (specAlgebraRingHom B hS hZ ι hR hY' (𝟙 _)) := by
  rw [specAlgebraRingHom, specAlgebraRingHom, ← specHomEquivGlobalSections_comp]
  congr 1
  subst hk hY hY'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [← specAlgebraObjHomScheme_precomp, Category.comp_id]

end SpecAlgebra

end BigFppfOver

/-! ### Restrictions to the big fppf site of the base of `U` -/

section Restrictions

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S) (hT : IsTerminal (B.obj hS))
  (U : BigFppfOver B S hS)

/-- The base of the chosen pullback `AlgebraicGeometry.polarizedRestriction` of `x` to `W` is the
underlying scheme of `W`. -/
theorem polarizedRestriction_base (x : (polarizedSliceProjection B hS hT).Fiber U)
    (W : BigFppfOver B U.left.obj U.left.property) :
    (polarizedRestriction B hS hT U x W).1.base = W.left :=
  polarizedSliceProjection_fiber_base B hS hT _

/-- The chosen pullbacks of `x` and of `y` to `W` have the same base. -/
theorem polarizedRestriction_base_eq_base (x y : (polarizedSliceProjection B hS hT).Fiber U)
    (W : BigFppfOver B U.left.obj U.left.property) :
    (polarizedRestriction B hS hT U x W).1.base = (polarizedRestriction B hS hT U y W).1.base :=
  (polarizedRestriction_base B hS hT U x W).trans (polarizedRestriction_base B hS hT U y W).symm

/-- The base of the chosen pullback of `x` to `W` is affine when the underlying scheme of `W`
is. -/
theorem isAffine_polarizedRestriction_base (x : (polarizedSliceProjection B hS hT).Fiber U)
    (W : BigFppfOver B U.left.obj U.left.property)
    (hW : IsAffine ((BigFppfOver.toScheme B U.left.obj U.left.property).obj W)) :
    IsAffine (B.inclusion.obj (polarizedRestriction B hS hT U x W).1.base) := by
  rwa [polarizedRestriction_base]

/-- The base map of `AlgebraicGeometry.polarizedRestrictionMap` along `f` is the underlying
morphism of `f`. -/
theorem polarizedRestrictionMap_baseMap (x : (polarizedSliceProjection B hS hT).Fiber U)
    {W₁ W₂ : BigFppfOver B U.left.obj U.left.property} (f : W₁ ⟶ W₂) :
    (polarizedRestrictionMap B hS hT U x f).baseMap =
      eqToHom (polarizedRestriction_base B hS hT U x W₁) ≫ f.left ≫
        eqToHom (polarizedRestriction_base B hS hT U x W₂).symm :=
  polarizedSliceProjection_baseMap_eq B hS hT ((Over.iteratedSliceBackward U).map f).left _

/-- The base map of `AlgebraicGeometry.polarizedRestrictionMap`, as a morphism of schemes. -/
theorem inclusion_map_polarizedRestrictionMap_baseMap
    (x : (polarizedSliceProjection B hS hT).Fiber U)
    {W₁ W₂ : BigFppfOver B U.left.obj U.left.property} (f : W₁ ⟶ W₂) :
    B.inclusion.map (polarizedRestrictionMap B hS hT U x f).baseMap =
      eqToHom (congrArg B.inclusion.obj (polarizedRestriction_base B hS hT U x W₁)) ≫
        B.inclusion.map f.left ≫
          eqToHom (congrArg B.inclusion.obj (polarizedRestriction_base B hS hT U x W₂)).symm :=
  polarizedSliceProjection_inclusion_map_baseMap_eq B hS hT
    ((Over.iteratedSliceBackward U).map f).left _

/-- The base maps of the restriction maps of the pullbacks of `x` and of `y` agree, through the
identifications of the bases. -/
theorem polarizedRestrictionMap_baseMap_comm (x y : (polarizedSliceProjection B hS hT).Fiber U)
    {W₁ W₂ : BigFppfOver B U.left.obj U.left.property} (f : W₁ ⟶ W₂) :
    (polarizedRestrictionMap B hS hT U x f).baseMap ≫
        eqToHom (polarizedRestriction_base_eq_base B hS hT U x y W₂) =
      eqToHom (polarizedRestriction_base_eq_base B hS hT U x y W₁) ≫
        (polarizedRestrictionMap B hS hT U y f).baseMap := by
  simp [polarizedRestrictionMap_baseMap]

/-- The restriction maps of the chosen pullbacks compose. -/
theorem polarizedRestrictionMap_comp (x : (polarizedSliceProjection B hS hT).Fiber U)
    {W₁ W₂ W₃ : BigFppfOver B U.left.obj U.left.property} (f : W₁ ⟶ W₂) (g : W₂ ⟶ W₃) :
    polarizedRestrictionMap B hS hT U x f ≫ polarizedRestrictionMap B hS hT U x g =
      polarizedRestrictionMap B hS hT U x (f ≫ g) := by
  rw [Functor.pullbackFiberMap_comp, ← Functor.map_comp]

/-- The sections over `W` of the isomorphism presheaf `Isom(x, y)` are the morphisms of polarized
families between the chosen pullbacks over the identity of the base:
`AlgebraicGeometry.polarizedIsomPresheafObjEquiv` followed by
`AlgebraicGeometry.polarizedFiberHomEquiv`. -/
def polarizedIsomSectionEquiv (x y : (polarizedStackUnconditional B hS hT).val.p.Fiber U)
    (W : BigFppfOver B U.left.obj U.left.property) :
    (polarizedIsomPresheaf B hS hT U x y).obj (op W) ≃
      PolarizedFamily.IsoOverBase (polarizedRestriction B hS hT U x W).1
        (polarizedRestriction B hS hT U y W).1
        (polarizedRestriction_base_eq_base B hS hT U x y W) :=
  (polarizedIsomPresheafObjEquiv B hS hT U x y W).trans (polarizedFiberHomEquiv B hS hT _ _)

/-- The restriction maps of the isomorphism presheaf, read through
`AlgebraicGeometry.polarizedIsomSectionEquiv`: restricting a section along `f` commutes with the
restriction maps of the chosen pullbacks. -/
theorem polarizedIsomSectionEquiv_map (x y : (polarizedStackUnconditional B hS hT).val.p.Fiber U)
    {W₁ W₂ : BigFppfOver B U.left.obj U.left.property} (f : W₁ ⟶ W₂)
    (s : (polarizedIsomPresheaf B hS hT U x y).obj (op W₂)) :
    (polarizedIsomSectionEquiv B hS hT U x y W₁
        ((polarizedIsomPresheaf B hS hT U x y).map f.op s)).1 ≫
        polarizedRestrictionMap B hS hT U y f =
      polarizedRestrictionMap B hS hT U x f ≫ (polarizedIsomSectionEquiv B hS hT U x y W₂ s).1 :=
  (polarizedIsomPresheaf_map_eq_iff B hS hT U x y f s _).1 rfl

/-- **The corepresenting ring represents the isomorphisms over an affine object.** Let `W₀` be
an object of the big fppf site of the underlying scheme `U'` of `U`, and suppose the
isomorphisms between pullbacks of `x|_{W₀}` and `y|_{W₀}` are corepresented by a
`Γ(W₀)`-algebra `H` whose spectrum lies in the site. Then there is a section of the isomorphism
presheaf over `Spec H` such that, on affine test objects `T`, morphisms `T ⟶ Spec H` are the
pairs of a section over `T` and a morphism `T ⟶ W₀`.

The section is the one corresponding to the identity of `H`, read as `H ⟶ Γ(Spec H)`; its
restriction along `f : T ⟶ Spec H` corresponds to the ring map of `f` by the naturality clause of
`AlgebraicGeometry.PolarizedFamily.IsIsoOverBaseCorepresented`, and the ring maps over
`Γ(W₀)` are the morphisms over `W₀` by
`AlgebraicGeometry.BigFppfOver.specAlgebraHomEquiv`. -/
theorem exists_bijective_polarizedIsomPresheaf_specAlgebraObj
    (x y : (polarizedStackUnconditional B hS hT).val.p.Fiber U)
    (W₀ : BigFppfOver B U.left.obj U.left.property)
    [IsAffine (B.inclusion.obj (polarizedRestriction B hS hT U x W₀).1.base)]
    (H : Type u) [CommRing H]
    (ι : Γ(B.inclusion.obj (polarizedRestriction B hS hT U x W₀).1.base, ⊤) →+* H)
    (hH : B.Contains (Spec (CommRingCat.of H)))
    (hrep : PolarizedFamily.IsIsoOverBaseCorepresented (polarizedRestriction B hS hT U x W₀).1
      (polarizedRestriction B hS hT U y W₀).1 (polarizedRestriction_base_eq_base B hS hT U x y W₀)
      H ι) :
    ∃ p : yoneda.obj (BigFppfOver.specAlgebraObj B U.left.property
          (polarizedRestriction_base B hS hT U x W₀) ι hH) ⟶
        (Over.iteratedSliceBackward U).op ⋙
          (polarizedStackUnconditional B hS hT).val.p.isomPresheaf x y,
      ∀ T : BigFppfOver B U.left.obj U.left.property,
        IsAffine ((BigFppfOver.toScheme B U.left.obj U.left.property).obj T) →
          Function.Bijective (fun f : T ⟶ BigFppfOver.specAlgebraObj B U.left.property
              (polarizedRestriction_base B hS hT U x W₀) ι hH =>
            ((⟨p.app (op T) f, f ≫ BigFppfOver.specAlgebraHom B U.left.property
              (polarizedRestriction_base B hS hT U x W₀) ι hH⟩ : _ × (T ⟶ W₀)))) := by
  obtain ⟨e, hnat⟩ := hrep
  set π := BigFppfOver.specAlgebraHom B U.left.property
    (polarizedRestriction_base B hS hT U x W₀) ι hH
  have econg : ∀ (W : BigFppfOver B U.left.obj U.left.property)
      (hW : IsAffine (B.inclusion.obj (polarizedRestriction B hS hT U x W).1.base))
      (c₁ c₂ : (polarizedRestriction B hS hT U x W).1 ⟶ (polarizedRestriction B hS hT U x W₀).1)
      (d₁ d₂ : (polarizedRestriction B hS hT U y W).1 ⟶ (polarizedRestriction B hS hT U y W₀).1)
      (h₁ : c₁.baseMap ≫ eqToHom (polarizedRestriction_base_eq_base B hS hT U x y W₀) =
        eqToHom (polarizedRestriction_base_eq_base B hS hT U x y W) ≫ d₁.baseMap)
      (h₂ : c₂.baseMap ≫ eqToHom (polarizedRestriction_base_eq_base B hS hT U x y W₀) =
        eqToHom (polarizedRestriction_base_eq_base B hS hT U x y W) ≫ d₂.baseMap)
      (φ₁ φ₂ : PolarizedFamily.IsoOverBase (polarizedRestriction B hS hT U x W).1
        (polarizedRestriction B hS hT U y W).1
        (polarizedRestriction_base_eq_base B hS hT U x y W)),
      c₁ = c₂ → d₁ = d₂ → φ₁ = φ₂ →
        (e _ _ _ hW c₁ d₁ h₁ φ₁).1 = (e _ _ _ hW c₂ d₂ h₂ φ₂).1 := by
    rintro W hW c₁ c₂ d₁ d₂ h₁ h₂ φ₁ φ₂ rfl rfl rfl
    rfl
  have hc : ∀ (T : BigFppfOver B U.left.obj U.left.property) (t : T ⟶ W₀),
      (B.inclusion.map (polarizedRestrictionMap B hS hT U x t).baseMap).appTop.hom =
        (eqToHom (congrArg B.inclusion.obj (polarizedRestriction_base B hS hT U x T)) ≫
          B.inclusion.map t.left ≫
            eqToHom (congrArg B.inclusion.obj (polarizedRestriction_base B hS hT U x W₀)).symm
              ).appTop.hom := fun T t =>
    congrArg (fun k => k.appTop.hom) (inclusion_map_polarizedRestrictionMap_baseMap B hS hT U x t)
  have hXaff : IsAffine (B.inclusion.obj ((polarizedRestriction B hS hT U x
      (BigFppfOver.specAlgebraObj B U.left.property
        (polarizedRestriction_base B hS hT U x W₀) ι hH)).1).base) :=
    isAffine_polarizedRestriction_base B hS hT U x _
      (show IsAffine (Spec (CommRingCat.of H)) from inferInstance)
  obtain ⟨u, hu⟩ : ∃ u : ((Over.iteratedSliceBackward U).op ⋙
        (polarizedStackUnconditional B hS hT).val.p.isomPresheaf x y).obj
        (op (BigFppfOver.specAlgebraObj B U.left.property
          (polarizedRestriction_base B hS hT U x W₀) ι hH)),
      (e _ _ _ hXaff (polarizedRestrictionMap B hS hT U x π)
        (polarizedRestrictionMap B hS hT U y π)
        (polarizedRestrictionMap_baseMap_comm B hS hT U x y _)
        (polarizedIsomSectionEquiv B hS hT U x y _ u)).1 =
        BigFppfOver.specAlgebraRingHom B U.left.property (polarizedRestriction_base B hS hT U x W₀)
          ι hH (polarizedRestriction_base B hS hT U x _) (𝟙 _) := by
    refine ⟨(polarizedIsomSectionEquiv B hS hT U x y _).symm ((e _ _ _ hXaff
      (polarizedRestrictionMap B hS hT U x π)
      (polarizedRestrictionMap B hS hT U y π)
      (polarizedRestrictionMap_baseMap_comm B hS hT U x y _)).symm
        ⟨BigFppfOver.specAlgebraRingHom B U.left.property (polarizedRestriction_base B hS hT U x W₀)
          ι hH (polarizedRestriction_base B hS hT U x _) (𝟙 _), ?_⟩), ?_⟩
    · exact (BigFppfOver.specAlgebraHomEquiv B U.left.property
        (polarizedRestriction_base B hS hT U x W₀) ι hH (polarizedRestriction_base B hS hT U x _) _
        ⟨𝟙 _, Category.id_comp _⟩).2.trans (hc _ _).symm
    · simp
  have key : ∀ (T : BigFppfOver B U.left.obj U.left.property)
      (hTa : IsAffine (B.inclusion.obj (polarizedRestriction B hS hT U x T).1.base))
      (f : T ⟶ BigFppfOver.specAlgebraObj B U.left.property
        (polarizedRestriction_base B hS hT U x W₀) ι hH),
      (e _ _ _ hTa (polarizedRestrictionMap B hS hT U x (f ≫ π))
        (polarizedRestrictionMap B hS hT U y (f ≫ π))
        (polarizedRestrictionMap_baseMap_comm B hS hT U x y _)
        (polarizedIsomSectionEquiv B hS hT U x y T (((Over.iteratedSliceBackward U).op ⋙
          (polarizedStackUnconditional B hS hT).val.p.isomPresheaf x y).map f.op u))).1 =
        BigFppfOver.specAlgebraRingHom B U.left.property (polarizedRestriction_base B hS hT U x W₀)
          ι hH (polarizedRestriction_base B hS hT U x T) f := by
    intro T hTa f
    have h1 := hnat _ _ _ hXaff
      (polarizedRestrictionMap B hS hT U x π)
      (polarizedRestrictionMap B hS hT U y π)
      (polarizedRestrictionMap_baseMap_comm B hS hT U x y _)
      _ _ _ hTa (polarizedRestrictionMap B hS hT U x f) (polarizedRestrictionMap B hS hT U y f)
      (polarizedRestrictionMap_baseMap_comm B hS hT U x y f) _ _
      (polarizedIsomSectionEquiv_map B hS hT U x y f u)
    rw [hu] at h1
    exact (econg T hTa _ _ _ _ _ _ _ _ (polarizedRestrictionMap_comp B hS hT U x _ _).symm
      (polarizedRestrictionMap_comp B hS hT U y _ _).symm rfl).trans (h1.trans
        (BigFppfOver.specAlgebraRingHom_eq_comp B U.left.property _ ι hH _ _ f _
          (polarizedRestrictionMap_baseMap B hS hT U x f)).symm)
  refine ⟨yonedaEquiv.symm u, fun T hTa' => ?_⟩
  have hTa := isAffine_polarizedRestriction_base B hS hT U x T hTa'
  constructor
  · intro f₁ f₂ hf
    have hs : ((Over.iteratedSliceBackward U).op ⋙
        (polarizedStackUnconditional B hS hT).val.p.isomPresheaf x y).map f₁.op u =
        ((Over.iteratedSliceBackward U).op ⋙
          (polarizedStackUnconditional B hS hT).val.p.isomPresheaf x y).map f₂.op u :=
      congrArg Prod.fst hf
    have ht := congrArg Prod.snd hf
    dsimp only at ht
    apply BigFppfOver.specAlgebraRingHom_injective B U.left.property _ ι hH
      (polarizedRestriction_base B hS hT U x T)
    rw [← key T hTa f₁, ← key T hTa f₂]
    exact econg T hTa _ _ _ _ _ _ _ _ (by rw [ht]) (by rw [ht]) (by rw [hs])
  · rintro ⟨s, t⟩
    obtain ⟨⟨f, hf⟩, hfφ⟩ : ∃ f : {f : T ⟶ BigFppfOver.specAlgebraObj B U.left.property
          (polarizedRestriction_base B hS hT U x W₀) ι hH // f ≫ π = t},
        BigFppfOver.specAlgebraRingHom B U.left.property (polarizedRestriction_base B hS hT U x W₀)
          ι hH (polarizedRestriction_base B hS hT U x T) f.1 =
        (e _ _ _ hTa (polarizedRestrictionMap B hS hT U x t) (polarizedRestrictionMap B hS hT U y t)
          (polarizedRestrictionMap_baseMap_comm B hS hT U x y t)
          (polarizedIsomSectionEquiv B hS hT U x y T s)).1 := by
      have hφ := (e _ _ _ hTa (polarizedRestrictionMap B hS hT U x t)
        (polarizedRestrictionMap B hS hT U y t)
        (polarizedRestrictionMap_baseMap_comm B hS hT U x y t)
        (polarizedIsomSectionEquiv B hS hT U x y T s)).2
      exact ⟨(BigFppfOver.specAlgebraHomEquiv B U.left.property
        (polarizedRestriction_base B hS hT U x W₀) ι hH (polarizedRestriction_base B hS hT U x T)
          t).symm ⟨_, hφ.trans (hc _ _)⟩,
          congrArg Subtype.val ((BigFppfOver.specAlgebraHomEquiv B U.left.property
            (polarizedRestriction_base B hS hT U x W₀) ι hH
              (polarizedRestriction_base B hS hT U x T) t).apply_symm_apply _)⟩
    refine ⟨f, Prod.ext ?_ hf⟩
    change ((Over.iteratedSliceBackward U).op ⋙
      (polarizedStackUnconditional B hS hT).val.p.isomPresheaf x y).map f.op u = s
    apply (polarizedIsomSectionEquiv B hS hT U x y T).injective
    apply (e _ _ _ hTa _ _ (polarizedRestrictionMap_baseMap_comm B hS hT U x y t)).injective
    apply Subtype.ext
    exact (econg T hTa _ _ _ _ _ _ _ _ (by rw [hf]) (by rw [hf]) rfl).trans
      ((key T hTa f).trans hfφ)

end Restrictions

/-! ### Representability of the isomorphism presheaf -/

section Representability

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S) (hT : IsTerminal (B.obj hS))

/-- The isomorphism presheaf of two objects of `𝒫olarized` over `U` is representable, given
that it is an fppf sheaf and that isomorphisms of polarized families over affine bases are
corepresented. -/
theorem isRepresentable_isomPresheaf_of_corepresented (U : BigFppfOver B S hS)
    (x y : (polarizedStackUnconditional B hS hT).val.p.Fiber U)
    (hsheaf : Presheaf.IsSheaf (BigFppfOver.topology B U.left.obj U.left.property)
      ((Over.iteratedSliceBackward U).op ⋙
        (polarizedStackUnconditional B hS hT).val.p.isomPresheaf x y))
    (hcore : ∀ (a b : PolarizedFamily B) (hab : a.base = b.base),
      IsAffine (B.inclusion.obj a.base) →
      ∃ (H : Type u) (_ : CommRing H) (ι : Γ(B.inclusion.obj a.base, ⊤) →+* H),
        Cardinal.mk H ≤ max Cardinal.aleph0 (Cardinal.mk Γ(B.inclusion.obj a.base, ⊤)) ∧
          PolarizedFamily.IsIsoOverBaseCorepresented a b hab H ι) :
    ((Over.iteratedSliceBackward U).op ⋙
        (polarizedStackUnconditional B hS hT).val.p.isomPresheaf x y).IsRepresentable := by
  refine Space.isRepresentable_of_isAffineOpen_represented B U.left.obj U.left.property _ hsheaf
    fun V => ?_
  have hV : IsAffine (B.inclusion.obj ((polarizedRestriction B hS hT U x
      (BigFppfOver.opensObj B U.left.obj U.left.property V.1)).1).base) :=
    isAffine_polarizedRestriction_base B hS hT U x _ (V.2 : IsAffineOpen V.1)
  obtain ⟨H, _, ι, hcard, hrep⟩ := hcore _ _
    (polarizedRestriction_base_eq_base B hS hT U x y _) hV
  have hsize : (Spec (CommRingCat.of H)).size ≤ U.left.obj.size := by
    rw [Scheme.size_Spec]
    refine max_le U.left.obj.aleph0_le_size (hcard.trans (max_le U.left.obj.aleph0_le_size ?_))
    refine ((B.inclusion.obj _).mk_sections_le_size ⟨⊤, isAffineOpen_top _⟩).trans ?_
    exact (Scheme.size_congr (eqToIso (congrArg B.inclusion.obj
      (polarizedRestriction_base B hS hT U x _)))).le.trans
        (Scheme.size_le_of_isOpenImmersion V.1.ι)
  obtain ⟨p, hp⟩ := exists_bijective_polarizedIsomPresheaf_specAlgebraObj B hS hT U x y
    _ H ι (hsize.trans_lt U.left.property) hrep
  exact ⟨_, p, _, hp, hsize⟩

end Representability

end AlgebraicGeometry

end
