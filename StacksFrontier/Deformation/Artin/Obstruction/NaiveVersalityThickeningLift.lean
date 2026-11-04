module

public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityFibreProduct
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityRestriction
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityThickeningSite
public import StacksFrontier.Deformation.Artin.RimSchlessinger.FibreProductLift
public import StacksFrontier.Deformation.Artin.Versality.NonversalThickeningSequence

/-!
# The lift of `x` across the thickening `A ×_C C'`

In the direction `(2) ⇒ (1)` of [Stacks, Tag 07YM] the family `x` over `Spec A` has to be
lifted across the square-zero thickening `Spec A ⟶ Spec (A ×_C C')` attached to a small
extension `C' → C` of Artinian local `Λ`-algebras and a `Λ`-algebra map `φ : A → C`. The lift
is produced by axiom (RS\*): the square

```
Spec C  ---->  Spec C'
  |              |
  v              v
Spec A  ---->  Spec (A ×_C C')
```

is cartesian on global sections with the upper leg a square-zero surjection, so the family `x`
over `Spec A` and a lift `y` of its restriction to `Spec C` over `Spec C'` glue to a family over
`Spec (A ×_C C')`.

This file carries out that step, and delivers the result in the shape hypothesis (i) of the tag
consumes: a `Deformation.Artin.SquareZeroThickening` whose surjection is `A ×_C C' → A`,
together with an inhabitant of the category of lifts of condition (iii) of
[Stacks, Tag 07YX] over its structure arrow.

## Main results

* `Deformation.Artin.isHomLift_affineSiteHom_of_schemeMap` — an arrow of the fibred category
  whose underlying morphism of schemes is named lies over the affine-site morphism that names
  it. This is the converse of `Deformation.Artin.schemeMap_eq_of_isHomLift`, and it is what
  turns the `Deformation.Artin.schemeMap` equations the deformation vocabulary is written with
  into the `IsHomLift`s that (RS\*) consumes.
* `Deformation.Artin.nonempty_underFiber_of_isHomLift` — an arrow lying over an arrow of the
  base inhabits the category of lifts over it. This is the converse of
  `Deformation.Artin.lift_obj` together with `Deformation.Artin.isHomLift_lift_hom`.
* `Deformation.Artin.exists_squareZeroThickening_underFiber_of_satisfiesRSStar` — **the step**:
  the thickening `A ×_C C' → A` together with the lift of `x` across it.

## Implementation notes

The square is fed to (RS\*) with its four corners the *literal* affine schemes over `S`, not the
objects `(p ⋙ Over.post B.inclusion).obj` returns: that is what keeps the hypothesis on global
sections free of transport morphisms, so that it is exactly
`Deformation.Artin.specMap_appTop_isPullback` applied to
`Stacks.Pushout.isPullback_ofHom_pullback` and nothing has to be conjugated by `appTop` of an
`eqToHom`. The price is one transport, `Deformation.Artin.overSiteObj_eq_algebraOver`,
identifying the site object built from `Spec A` over `S` with the one
`Deformation.Artin.algebraOver` builds.

The thickening is *constructed* rather than taken from
`Deformation.Artin.squareZeroThickeningOfMkLe`, and its structure arrow is the affine-site
morphism that (RS\*) produced the lift over. Hypothesis (i) of the tag quantifies over every
square-zero thickening whose surjection is `algebraMap A' A`, so a consumer may be handed this
one; building it here avoids having to identify the arrow (RS\*) delivers with the one
`Deformation.Artin.squareZeroThickeningOfTower` chooses, and no size estimate on the kernel is
needed, the containment of `Spec (A ×_C C')` being an explicit hypothesis.

## References

* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
* [Stacks Project, Tag 07YX](https://stacks.math.columbia.edu/tag/07YX)
* [Stacks Project, Tag 07Y8](https://stacks.math.columbia.edu/tag/07Y8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace Deformation.Artin

/-! ### Transports between the two presentations of an affine site object -/

section SiteObjects

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The site object built from an affine scheme over `S` is the one
`Deformation.Artin.algebraOver` builds: both are the slice object on the structure morphism,
one with the full-subcategory inclusion's `preimage` and one with `ObjectProperty.homMk`. -/
public theorem overSiteObj_eq_algebraOver {A : Type u} [CommRing A]
    (toS : Spec (CommRingCat.of A) ⟶ S) (hA : B.Contains (Spec (CommRingCat.of A))) :
    overSiteObj B S hS (Over.mk toS) hA = algebraOver A B S hS toS hA := by
  show Over.mk _ = Over.mk _
  congr 1
  apply B.inclusion.map_injective
  rw [B.inclusion.map_preimage]
  rfl

variable {F : Type v} [Category.{w} F] (p : F ⥤ BigFppfOver B S hS)

/-- An object lying over `Deformation.Artin.algebraOver` lies over `Spec A` as a scheme over
`S`. -/
public theorem algebraOver_post {A : Type u} [CommRing A]
    (toS : Spec (CommRingCat.of A) ⟶ S) (hA : B.Contains (Spec (CommRingCat.of A)))
    {Xf : F} (hX : p.obj Xf = algebraOver A B S hS toS hA) :
    (p ⋙ Over.post B.inclusion).obj Xf = Over.mk toS := by
  show (Over.post B.inclusion).obj (p.obj Xf) = _
  rw [hX]
  rfl

/-- The object over `S` underlying a site object built from a scheme over `S`. -/
public theorem overSiteObj_post_of_eq {Z : Over S} {hZ' : B.Contains Z.left} {Zf : F}
    (hZ : p.obj Zf = overSiteObj B S hS Z hZ') :
    (p ⋙ Over.post B.inclusion).obj Zf = Z := by
  show (Over.post B.inclusion).obj (p.obj Zf) = Z
  rw [hZ]
  exact overSiteObj_post B S hS Z hZ'

/-- **An arrow lies over the affine-site morphism its underlying morphism of schemes names.**
This is the converse of `Deformation.Artin.schemeMap_eq_of_isHomLift`: both ends of the arrow
being presented as affine schemes over `S` inside the site, an equation
`Deformation.Artin.schemeMap … = f.left` says exactly that the arrow lies over the site
morphism `Deformation.Artin.affineSiteHom` builds from `f`. -/
public theorem isHomLift_affineSiteHom_of_schemeMap
    {Z X : Over S} {hZ' : B.Contains Z.left} {hX' : B.Contains X.left}
    [IsAffine Z.left] [IsAffine X.left]
    {Zf Xf : F} (hZ : p.obj Zf = overSiteObj B S hS Z hZ')
    (hX : p.obj Xf = overSiteObj B S hS X hX')
    (f : Z ⟶ X) (α : Zf ⟶ Xf)
    (hα : schemeMap (p ⋙ Over.post B.inclusion)
        (overSiteObj_post_of_eq B S hS p hZ) (overSiteObj_post_of_eq B S hS p hX) α = f.left) :
    p.IsHomLift ((BigAffineFppf.inclusion B S hS).map
      (affineSiteHom B S hS (hA := hZ') (hT := hX') f)) α := by
  apply IsHomLift.of_fac p _ α hZ hX
  apply (BigFppfOver.toScheme B S hS).map_injective
  show (BigAffineFppf.toScheme B S hS).map (affineSiteHom B S hS f) = _
  rw [affineSiteHom_toScheme, ← hα]
  simp only [Functor.map_comp, eqToHom_map]
  rfl

end SiteObjects

/-! ### Inhabiting the category of lifts -/

section UnderFiber

variable {C : Type u} [Category.{v} C] {X : Type*} [Category X]

/-- **An arrow lying over an arrow of the base inhabits the category of lifts over it.**
Condition (iii) of [Stacks, Tag 07YX] asks for non-emptiness of the fibre of
`CategoryTheory.Under.post p` over the arrow; this is what produces an inhabitant, and is the
converse of `Deformation.Artin.lift_obj` together with
`Deformation.Artin.isHomLift_lift_hom`. -/
public theorem nonempty_underFiber_of_isHomLift (p : X ⥤ C) {U W : C} {x x' : X}
    (hx : p.obj x = U) (ν : U ⟶ W) (hx' : p.obj x' = W) (w : x ⟶ x')
    (hw : p.IsHomLift ν w) :
    Nonempty ((Under.post p).Fiber (Under.mk (eqToHom hx ≫ ν))) := by
  refine ⟨⟨Under.mk w, ?_⟩⟩
  apply StructuredArrow.obj_ext _ _ hx'
  show p.map w ≫ eqToHom hx' = eqToHom hx ≫ ν
  rw [IsHomLift.fac' p ν w]
  simp

/-- Lying over an arrow of the base is unchanged by transporting its source along an equality
of objects. -/
public theorem isHomLift_eqToHom_comp (p : X ⥤ C) {U U' W : C} (e : U = U') {x x' : X}
    (ν : U' ⟶ W) (w : x ⟶ x') (hw : p.IsHomLift ν w) :
    p.IsHomLift (eqToHom e ≫ ν) w := by
  refine IsHomLift.of_fac' p (eqToHom e ≫ ν) w ((IsHomLift.domain_eq p ν w).trans e.symm)
    (IsHomLift.codomain_eq p ν w) ?_
  rw [IsHomLift.fac' p ν w]
  simp

end UnderFiber

/-! ### The thickening `A ×_C C'` and the lift of `x` across it -/

section Glue

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F : Type v} [Category.{w} F] (p : F ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp)
  {Λ A C C' : Type u} [CommRing Λ] [CommRing A] [CommRing C] [CommRing C']
  [Algebra Λ A] [Algebra Λ C] [Algebra Λ C']
  (iΛ : Spec (CommRingCat.of Λ) ⟶ S)
  (φ : A →ₐ[Λ] C) (fC : C' →ₐ[Λ] C)

include hp hRS in
/-- **The lift of `x` across the thickening `A ×_C C'`.** Let `fC : C' → C` be a square-zero
surjection of `Λ`-algebras, let `φ : A → C` be a map of `Λ`-algebras, let `x` be a family over
`Spec A`, let `z` be a family over `Spec C` with an arrow to `x` over `Spec φ`, and let `y` be a
family over `Spec C'` with an arrow from `z` over `Spec fC`. Then `A ×_C C' → A` is a
square-zero thickening of `Spec A` over `S` across which `x` lifts.

The square of the four spectra is cartesian on global sections with the leg `Spec C ⟶ Spec C'`
a square-zero surjection, so axiom (RS\*) glues `x` and `y` along the identification of their
restrictions to `Spec C` that the two arrows out of `z` provide. -/
public theorem exists_squareZeroThickening_underFiber_of_satisfiesRSStar
    (hfC : Function.Surjective fC)
    (hsqC : RingHom.ker (fC : C' →+* C) ^ 2 = ⊥)
    (hA : B.Contains (Spec (CommRingCat.of A)))
    (hC : B.Contains (Spec (CommRingCat.of C)))
    (hC' : B.Contains (Spec (CommRingCat.of C')))
    (hA' : B.Contains (Spec (CommRingCat.of (AlgHom.pullback φ fC))))
    {Xf Zf Yf : F}
    (hXf : p.obj Xf = algebraOver A B S hS
      (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) hA)
    (hZf : p.obj Zf = algebraOver C B S hS
      (Spec.map (CommRingCat.ofHom (algebraMap Λ C)) ≫ iΛ) hC)
    (hYf : p.obj Yf = algebraOver C' B S hS
      (Spec.map (CommRingCat.ofHom (algebraMap Λ C')) ≫ iΛ) hC')
    (α : Zf ⟶ Xf) (β : Zf ⟶ Yf)
    (hα : schemeMap (p ⋙ Over.post B.inclusion)
        (algebraOver_post B S hS p _ hC hZf) (algebraOver_post B S hS p _ hA hXf) α =
      Spec.map (CommRingCat.ofHom (φ : A →+* C)))
    (hβ : schemeMap (p ⋙ Over.post B.inclusion)
        (algebraOver_post B S hS p _ hC hZf) (algebraOver_post B S hS p _ hC' hYf) β =
      Spec.map (CommRingCat.ofHom (fC : C' →+* C))) :
    ∃ D : SquareZeroThickening A B S hS
        (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) hA (AlgHom.pullback φ fC),
      D.q = algebraMap (AlgHom.pullback φ fC) A ∧
      Nonempty ((Under.post p).Fiber (Under.mk (eqToHom hXf ≫ D.arrow))) ∧
      Spec.map (CommRingCat.ofHom (algebraMap Λ (AlgHom.pullback φ fC))) ≫ iΛ =
        B.inclusion.map D.toS' := by
  let UU : Over S := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ C)) ≫ iΛ)
  let VV : Over S := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ)
  let WW : Over S := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ C')) ≫ iΛ)
  let PP : Over S :=
    Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap Λ (AlgHom.pullback φ fC))) ≫ iΛ)
  have : IsAffine UU.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of C)))
  have : IsAffine VV.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))
  have : IsAffine WW.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of C')))
  have : IsAffine PP.left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (AlgHom.pullback φ fC))))
  have hUU : B.Contains UU.left := hC
  have hVV : B.Contains VV.left := hA
  have hWW : B.Contains WW.left := hC'
  have hPP : B.Contains PP.left := hA'
  -- a `Λ`-algebra map is a morphism over `S` of the two spectra
  have hcomm : ∀ {R T : Type u} [CommRing R] [CommRing T] [Algebra Λ R] [Algebra Λ T]
      (ψ : R →ₐ[Λ] T),
      Spec.map (CommRingCat.ofHom (ψ : R →+* T)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap Λ R)) ≫ iΛ =
        Spec.map (CommRingCat.ofHom (algebraMap Λ T)) ≫ iΛ := by
    intro R T _ _ _ _ ψ
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    apply CommRingCat.hom_ext
    exact RingHom.ext fun l => ψ.commutes l
  let fm : UU ⟶ VV := Over.homMk (Spec.map (CommRingCat.ofHom (φ : A →+* C))) (hcomm φ)
  let gm : UU ⟶ WW := Over.homMk (Spec.map (CommRingCat.ofHom (fC : C' →+* C))) (hcomm fC)
  let im : VV ⟶ PP :=
    Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap (AlgHom.pullback φ fC) A)))
      (hcomm (AlgHom.pullbackFst φ fC))
  let jm : WW ⟶ PP :=
    Over.homMk (Spec.map (CommRingCat.ofHom
      (AlgHom.pullbackSnd φ fC : (AlgHom.pullback φ fC) →+* C')))
      (hcomm (AlgHom.pullbackSnd φ fC))
  have hsquare : fm ≫ im = gm ≫ jm := by
    apply Over.OverMorphism.ext
    show Spec.map (CommRingCat.ofHom (φ : A →+* C)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (AlgHom.pullback φ fC) A)) =
      Spec.map (CommRingCat.ofHom (fC : C' →+* C)) ≫
        Spec.map (CommRingCat.ofHom
          (AlgHom.pullbackSnd φ fC : (AlgHom.pullback φ fC) →+* C'))
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact RingHom.ext fun z => fibreProduct_prop φ fC z
  have hpb : IsPullback im.left.appTop jm.left.appTop fm.left.appTop gm.left.appTop :=
    specMap_appTop_isPullback
      (Stacks.Pushout.isPullback_ofHom_pullback (φ : A →+* C) (fC : C' →+* C))
  have hZo : p.obj Zf = overSiteObj B S hS UU hUU :=
    hZf.trans (overSiteObj_eq_algebraOver B S hS _ hC).symm
  have hXo : p.obj Xf = overSiteObj B S hS VV hVV :=
    hXf.trans (overSiteObj_eq_algebraOver B S hS _ hA).symm
  have hYo : p.obj Yf = overSiteObj B S hS WW hWW :=
    hYf.trans (overSiteObj_eq_algebraOver B S hS _ hC').symm
  obtain ⟨zz, ai, bj, hai, -, -⟩ := exists_compatible_maps_over_scheme_square B S hS p hp hRS
    (hU := hUU) (hA := hVV) (hT := hWW) (hP := hPP) fm gm im jm hsquare hpb
    (specMap_appTop_surjective _ hfC) (specMap_appTop_ker_sq _ hsqC)
    ⟨Zf, hZo⟩ ⟨Xf, hXo⟩ ⟨Yf, hYo⟩ α
    (isHomLift_affineSiteHom_of_schemeMap B S hS p hZo hXo fm α hα) β
    (isHomLift_affineSiteHom_of_schemeMap B S hS p hZo hYo gm β hβ)
  refine ⟨{ q := algebraMap (AlgHom.pullback φ fC) A
            squareZeroSurjection :=
              ⟨surjective_fibreProduct_algebraMap φ fC hfC,
                ker_fibreProduct_sq_eq_bot φ fC hsqC⟩
            hA' := hA'
            toS' := (overSiteObj B S hS PP hPP).hom
            arrow := eqToHom (overSiteObj_eq_algebraOver B S hS
                (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) hA).symm ≫
              (BigAffineFppf.inclusion B S hS).map
                (affineSiteHom B S hS (hA := hVV) (hT := hPP) im)
            arrow_spec := ?_ }, rfl, ?_, ?_⟩
  · simp only [Over.comp_left, Over.eqToHom_left, Functor.map_comp, eqToHom_map]
    show eqToHom _ ≫ (BigAffineFppf.toScheme B S hS).map
        (affineSiteHom B S hS (hA := hVV) (hT := hPP) im) = _
    rw [affineSiteHom_toScheme]
    exact Category.id_comp _
  · exact nonempty_underFiber_of_isHomLift p hXf _ zz.2 ai
      (isHomLift_eqToHom_comp p _ _ ai hai)
  · exact (B.inclusion.map_preimage
      (show B.inclusion.obj (B.obj hPP) ⟶ B.inclusion.obj (B.obj hS) from PP.hom)).symm

end Glue

end Deformation.Artin

end
