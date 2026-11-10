module

public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff

/-!
# Spectra of algebras over the ring of functions of an affine object of the site

Let `T` be an object of the big fppf site of `S` whose underlying scheme is affine, with ring of
global functions `A = Γ(T, ⊤)`.  For an `A`-algebra `R` whose spectrum satisfies the site's size
cutoff, `Spec R` is an object of the site over `T`.  A morphism of affine objects over `T` into
`Spec R` is given by a ring map `R ⟶ Γ(V, ⊤)` compatible with `A`, and a morphism out of an
algebraic space with a surjective étale chart descends from the chart.

## Main definitions

* `AlgebraicGeometry.Space.specOverAffineBase`: the object `Spec R` of the site.
* `AlgebraicGeometry.Space.specOverAffineBaseHom`: the morphism `Spec R' ⟶ Spec R` of an
  `A`-algebra map `R ⟶ R'`.
* `AlgebraicGeometry.Space.toSpecOverAffineBase`: the morphism `V ⟶ Spec R` of a ring map
  `R ⟶ Γ(V, ⊤)` over `A`.

## Main results

* `AlgebraicGeometry.Space.exists_desc_of_isPullback`: a morphism out of a chart which
  identifies the two projections of its kernel pair descends to the algebraic space.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Descent of a morphism into a represented presheaf along a surjective étale chart.** -/
theorem exists_desc_of_isPullback {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) {W R : BigFppfOver B S hS} (w : yoneda.obj W ⟶ X)
    {s t : R ⟶ W} (hR : IsPullback (yoneda.map s) (yoneda.map t) w w)
    (hws : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) w)
    (hwe : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) w)
    {Y : BigFppfOver B S hS} (g : W ⟶ Y) (hg : s ≫ g = t ≫ g) :
    ∃ φ : X ⟶ yoneda.obj Y, w ≫ φ = yoneda.map g := by
  obtain ⟨hRsh, hWsh, ⟨hc⟩⟩ := isCoequalizer_of_surjectiveEtale B S hS w s t hR hX hws hwe
  let J := BigFppfOver.topology B S hS
  let WF : Sheaf J (Type u) := ⟨yoneda.obj W, hWsh⟩
  let YF : Sheaf J (Type u) := ⟨yoneda.obj Y, (isAlgebraicSpace_yoneda B S hS Y).isSheaf⟩
  let gf : WF ⟶ YF := ⟨yoneda.map g⟩
  let c := Cofork.IsColimit.desc hc gf (by
    apply Sheaf.hom_ext
    change yoneda.map s ≫ yoneda.map g = yoneda.map t ≫ yoneda.map g
    rw [← Functor.map_comp, ← Functor.map_comp, hg])
  exact ⟨c.hom, congrArg (fun z ↦ z.hom) (Cofork.IsColimit.π_desc' hc gf _)⟩

section Spec

variable {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]

/-- The ring of global functions of the affine object `T`. -/
abbrev affineBaseRing (T : BigFppfOver B S hS) : CommRingCat.{u} :=
  Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)

/-- The structure morphism `Spec R ⟶ S` of an algebra over the functions of `T`. -/
abbrev specOverAffineBaseStructure (R : Type u) [CommRing R] [Algebra (affineBaseRing B S hS T) R] :
    Spec (CommRingCat.of R) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap (affineBaseRing B S hS T) R)) ≫
    ((BigFppfOver.toScheme B S hS).obj T).isoSpec.inv ≫ B.inclusion.map T.hom

variable (T) in
/-- `Spec R`, for an algebra `R` over the functions of `T`, as an object of the site. -/
abbrev specOverAffineBase (R : Type u) [CommRing R] [Algebra (affineBaseRing B S hS T) R]
    (hR : B.Contains (Spec (CommRingCat.of R))) : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS hR (specOverAffineBaseStructure B S hS (T := T) R)

/-- The underlying scheme of `specOverAffineBase B S hS T R hR` is affine. -/
instance (R : Type u) [CommRing R] [Algebra (affineBaseRing B S hS T) R]
    (hR : B.Contains (Spec (CommRingCat.of R))) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (specOverAffineBase B S hS T R hR)) :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of R)))

/-- The structure morphism `Spec R ⟶ T` in the site. -/
def specOverAffineBaseToBase (R : Type u) [CommRing R] [Algebra (affineBaseRing B S hS T) R]
    (hR : B.Contains (Spec (CommRingCat.of R))) : specOverAffineBase B S hS T R hR ⟶ T :=
  Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom
      (algebraMap (affineBaseRing B S hS T) R)) ≫
    ((BigFppfOver.toScheme B S hS).obj T).isoSpec.inv)) (by
    apply ObjectProperty.hom_ext
    rfl)

/-- The underlying morphism of schemes of `specOverAffineBaseToBase` is `Spec (algebraMap A R)`
followed by the inverse of `T.isoSpec`. -/
theorem toScheme_map_specOverAffineBaseToBase (R : Type u) [CommRing R]
    [Algebra (affineBaseRing B S hS T) R] (hR : B.Contains (Spec (CommRingCat.of R))) :
    (BigFppfOver.toScheme B S hS).map (specOverAffineBaseToBase B S hS R hR) =
      Spec.map (CommRingCat.ofHom (algebraMap (affineBaseRing B S hS T) R)) ≫
        ((BigFppfOver.toScheme B S hS).obj T).isoSpec.inv :=
  rfl

/-- The morphism `Spec R' ⟶ Spec R` of a morphism of algebras over the functions of `T`. -/
def specOverAffineBaseHom {R R' : Type u} [CommRing R] [CommRing R']
    [Algebra (affineBaseRing B S hS T) R] [Algebra (affineBaseRing B S hS T) R']
    (hR : B.Contains (Spec (CommRingCat.of R)))
    (hR' : B.Contains (Spec (CommRingCat.of R'))) (f : R →ₐ[affineBaseRing B S hS T] R') :
    specOverAffineBase B S hS T R' hR' ⟶ specOverAffineBase B S hS T R hR :=
  BigFppfOver.homMk B S hS hR _ (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    change _ ≫ specOverAffineBaseStructure B S hS (T := T) R =
      specOverAffineBaseStructure B S hS (T := T) R'
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show f.toRingHom.comp (algebraMap (affineBaseRing B S hS T) R) = algebraMap _ R' from
        RingHom.ext f.commutes])

/-- The underlying morphism of schemes of `specOverAffineBaseHom` is `Spec.map f`. -/
theorem toScheme_map_specOverAffineBaseHom {R R' : Type u} [CommRing R] [CommRing R']
    [Algebra (affineBaseRing B S hS T) R] [Algebra (affineBaseRing B S hS T) R']
    (hR : B.Contains (Spec (CommRingCat.of R))) (hR' : B.Contains (Spec (CommRingCat.of R')))
    (f : R →ₐ[affineBaseRing B S hS T] R') :
    (BigFppfOver.toScheme B S hS).map (specOverAffineBaseHom B S hS hR hR' f) =
      Spec.map (CommRingCat.ofHom f.toRingHom) :=
  rfl

/-- `specOverAffineBaseHom` commutes with the structure morphisms to `T`. -/
theorem specOverAffineBaseHom_toBase {R R' : Type u} [CommRing R] [CommRing R']
    [Algebra (affineBaseRing B S hS T) R] [Algebra (affineBaseRing B S hS T) R']
    (hR : B.Contains (Spec (CommRingCat.of R))) (hR' : B.Contains (Spec (CommRingCat.of R')))
    (f : R →ₐ[affineBaseRing B S hS T] R') :
    specOverAffineBaseHom B S hS hR hR' f ≫ specOverAffineBaseToBase B S hS R hR =
      specOverAffineBaseToBase B S hS R' hR' := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  rw [Functor.map_comp]
  change (Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (affineBaseRing B S hS T) R)) ≫
        ((BigFppfOver.toScheme B S hS).obj T).isoSpec.inv : Spec (CommRingCat.of R') ⟶ _) =
    Spec.map (CommRingCat.ofHom (algebraMap (affineBaseRing B S hS T) R')) ≫
      ((BigFppfOver.toScheme B S hS).obj T).isoSpec.inv
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    show f.toRingHom.comp (algebraMap (affineBaseRing B S hS T) R) = algebraMap _ R' from
        RingHom.ext f.commutes]

/-- The morphism `V ⟶ Spec R` of a ring map `θ : R ⟶ Γ(V, ⊤)` over the functions of `T`, for an
affine object `V` over `T`. -/
def toSpecOverAffineBase {V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (ωV : V ⟶ T) {R : Type u} [CommRing R] [Algebra (affineBaseRing B S hS T) R]
    (hR : B.Contains (Spec (CommRingCat.of R)))
    (θ : R →+* Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
    (hθ : θ.comp (algebraMap (affineBaseRing B S hS T) R) =
      ((BigFppfOver.toScheme B S hS).map ωV).appTop.hom) :
    V ⟶ specOverAffineBase B S hS T R hR :=
  BigFppfOver.homMk B S hS hR _
    (((BigFppfOver.toScheme B S hS).obj V).isoSpec.hom ≫ Spec.map (CommRingCat.ofHom θ)) (by
    rw [Category.assoc, ← Category.assoc (Spec.map _), ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      hθ, CommRingCat.ofHom_hom, Scheme.isoSpec_hom_naturality_assoc, Iso.hom_inv_id_assoc]
    exact congrArg (fun k ↦ k.hom) (Over.w ωV))

/-- The underlying morphism of schemes of `toSpecOverAffineBase` is `V.isoSpec.hom` followed by
`Spec.map θ`. -/
theorem toScheme_map_toSpecOverAffineBase {V : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] (ωV : V ⟶ T) {R : Type u} [CommRing R]
    [Algebra (affineBaseRing B S hS T) R] (hR : B.Contains (Spec (CommRingCat.of R)))
    (θ : R →+* Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
    (hθ : θ.comp (algebraMap (affineBaseRing B S hS T) R) =
      ((BigFppfOver.toScheme B S hS).map ωV).appTop.hom) :
    (BigFppfOver.toScheme B S hS).map (toSpecOverAffineBase B S hS ωV hR θ hθ) =
      ((BigFppfOver.toScheme B S hS).obj V).isoSpec.hom ≫ Spec.map (CommRingCat.ofHom θ) :=
  rfl

/-- The ring map underlying `toSpecOverAffineBase`, read back on global functions. -/
theorem appTop_toSpecOverAffineBase {V : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] (ωV : V ⟶ T) {R : Type u} [CommRing R]
    [Algebra (affineBaseRing B S hS T) R] (hR : B.Contains (Spec (CommRingCat.of R)))
    (θ : R →+* Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
    (hθ : θ.comp (algebraMap (affineBaseRing B S hS T) R) =
      ((BigFppfOver.toScheme B S hS).map ωV).appTop.hom) :
    ((BigFppfOver.toScheme B S hS).map (toSpecOverAffineBase B S hS ωV hR θ hθ)).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom θ := by
  change Scheme.Hom.appTop (X := (BigFppfOver.toScheme B S hS).obj V)
      (Y := Spec (CommRingCat.of R))
      (((BigFppfOver.toScheme B S hS).obj V).isoSpec.hom ≫ Spec.map (CommRingCat.ofHom θ)) = _
  rw [Scheme.Hom.comp_appTop, Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop]
  simp [Scheme.ΓSpecIso_naturality]

/-- Two morphisms of an object of the site into `Spec R` with the same ring map on global
functions agree. -/
theorem hom_ext_specOverAffineBase {V : BigFppfOver B S hS} {R : Type u} [CommRing R]
    [Algebra (affineBaseRing B S hS T) R] {hR : B.Contains (Spec (CommRingCat.of R))}
    {a b : V ⟶ specOverAffineBase B S hS T R hR}
    (h : ((BigFppfOver.toScheme B S hS).map a).appTop =
      ((BigFppfOver.toScheme B S hS).map b).appTop) : a = b :=
  (BigFppfOver.toScheme B S hS).map_injective (ext_of_isAffine h)

end Spec

end AlgebraicGeometry.Space

end
