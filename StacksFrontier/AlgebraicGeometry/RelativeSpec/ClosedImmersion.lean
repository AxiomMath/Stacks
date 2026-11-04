module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.AlgebraHomComparison
public import StacksFrontier.AlgebraicGeometry.SectionEpiAffine.AlgebraSheaf

/-!
# Closed immersions into a relative spectrum

Let `s` be a relative-spectrum situation, with base `S`, quasi-coherent algebra `A` and relative
spectrum `π : Spec_S(A) ⟶ S`. A morphism `T ⟶ Spec_S(A)` is, by [Stacks, Tag 01LV], a pair
`(g : T ⟶ S, φ : A ⟶ g_* 𝒪_T)`, and this file gives the criterion for the morphism it determines
to be a closed immersion: on a family of affine opens `U` covering `S` the inverse image
`g⁻¹(U)` has to be affine and `φ` has to be surjective on sections over `U`.

The case the construction was written for is a morphism of algebras on one base: if
`ψ : A ⟶ B` is surjective on sections over the affine opens of `S`, then
`Spec_S(B) ⟶ Spec_S(A)` is a closed immersion. That is the relative-spectrum form of
"the spectrum of a surjective ring map is a closed immersion",
`AlgebraicGeometry.IsClosedImmersion.spec_of_surjective`.

## Main definitions

* `Stacks.RelativeSpec.pairRestrict`: the restriction over an affine open `U` of the base of the
  morphism attached to a pair, as a morphism `g⁻¹(U) ⟶ π⁻¹(U)`.

## Main results

* `Stacks.RelativeSpec.isAffineOpen_toBase_preimage`: the inverse image in the relative spectrum
  of an affine open of the base is affine.
* `Stacks.RelativeSpec.isPullback_pairRestrict`: over an affine open `U` of the base, the
  morphism attached to a pair is cartesian over the inclusion of `π⁻¹(U)`, and
  `Stacks.RelativeSpec.exists_iso_morphismRestrict_pairToHom`: so its restriction over `π⁻¹(U)`
  is that morphism.
* `Stacks.RelativeSpec.isClosedImmersion_pairToHom`: **the criterion**.
* `Stacks.RelativeSpec.isClosedImmersion_relativeSpectrumMapOfAlgebraHom`: **the morphism of
  relative spectra attached to a surjective morphism of algebras on one base is a closed
  immersion**, and
  `Stacks.RelativeSpec.isClosedImmersion_relativeSpectrumMapOfAlgebraHom_of_isLocallySurjective`:
  the same from local surjectivity of the morphism of algebra sheaves, which is what
  surjectivity of a morphism of sheaves means.

## Implementation notes

Being a closed immersion is local on the target, so the criterion is checked on the cover of
`Spec_S(A)` by the inverse images `π⁻¹(U)` of the given affine opens of the base. Over such a `U`
the morphism attached to the pair is `Stacks.RelativeSpec.pairLocal`, i.e. the canonical morphism
of `g⁻¹(U)` to the spectrum of its sections followed by the spectrum of `φ(U)` and the chart of
`U` — a composite of an isomorphism (`g⁻¹(U)` being affine), the spectrum of a surjective ring
map, and an open immersion onto `π⁻¹(U)`.

What makes that computation usable is that it is *cartesian*: the square with `g⁻¹(U) ⟶ T` on
top and `π⁻¹(U) ⟶ Spec_S(A)` on the bottom is a pullback square, obtained by cancelling the
chart square of `Stacks.RelativeSpec.GluedSpectrum` out of the square that defines `g⁻¹(U)` as
the inverse image of `U`. The restriction of the morphism over `π⁻¹(U)` is then identified with
that composite by the uniqueness of pullbacks, and no transport along an equality of opens is
needed.

For the morphism of algebras on one base the pair is the one that defines
`Stacks.RelativeSpec.relativeSpectrumMapOfAlgebraHom`, whose algebra component is `ψ` followed
by the universal algebra map of `B`; the latter is an isomorphism on sections over an affine open
by `Stacks.RelativeSpec.isIso_universalAlgebraMap_app`, so surjectivity of the component is
surjectivity of `ψ` there.

Surjectivity of a morphism of *sheaves* is local surjectivity, not surjectivity on sections, and
the two are reconciled by
`Stacks.SectionEpiAffine.surjective_sections_of_isLocallySurjective`: for quasi-coherent algebra
sheaves a locally surjective morphism is surjective on sections over an affine open. So the
hypothesis of the last result above is the one a morphism of algebra sheaves actually comes
with.

## References

* [Stacks Project, Tag 01LP](https://stacks.math.columbia.edu/tag/01LP)
* [Stacks Project, Tag 01LV](https://stacks.math.columbia.edu/tag/01LV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.RelativeSpec

/-! ### The inverse images of the affine opens of the base -/

section Cover

variable (s : RelativeSpecSituation.{u})

/-- **The inverse image in the relative spectrum of an affine open `U` of the base is affine**:
`Stacks.RelativeSpec.GluedSpectrum.chartIsoPreimage` identifies it with `Spec A(U)`. -/
theorem isAffineOpen_toBase_preimage (U : s.base.affineOpens) :
    IsAffineOpen ((gluedSpectrum s).toBase ⁻¹ᵁ U.1) :=
  IsAffine.of_isIso ((gluedSpectrum s).chartIsoPreimage U).inv

end Cover

/-! ### The morphism attached to a pair, restricted over an affine open of the base -/

section Pair

variable {s : RelativeSpecSituation.{u}} {T : Scheme.{u}} (p : RelativeSpecPair s T)

/-- **The restriction over an affine open `U` of the base of the morphism attached to a pair
`(g, φ)`**, as a morphism `g⁻¹(U) ⟶ π⁻¹(U)`: the canonical morphism of `g⁻¹(U)` to the spectrum
of its sections, the spectrum of `φ(U)`, and the identification of `Spec A(U)` with `π⁻¹(U)`.

That this really is the restriction of `Stacks.RelativeSpec.pairToHom` is
`Stacks.RelativeSpec.isPullback_pairRestrict`. -/
def pairRestrict (U : s.base.affineOpens) :
    (p.1 ⁻¹ᵁ U.1).toScheme ⟶ ((gluedSpectrum s).toBase ⁻¹ᵁ U.1).toScheme :=
  (p.1 ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (p.2.right.app (.op U.1)) ≫
    ((gluedSpectrum s).chartIsoPreimage U).hom

/-- `Stacks.RelativeSpec.pairRestrict` is a morphism of open subschemes over the morphism
attached to the pair. -/
theorem pairRestrict_comp_ι (U : s.base.affineOpens) :
    pairRestrict p U ≫ ((gluedSpectrum s).toBase ⁻¹ᵁ U.1).ι =
      (p.1 ⁻¹ᵁ U.1).ι ≫ pairToHom p := by
  rw [ι_pairToHom, pairLocal]
  dsimp only [pairRestrict]
  rw [Category.assoc, Category.assoc, GluedSpectrum.chartIsoPreimage_hom_ι]

/-- `Stacks.RelativeSpec.pairRestrict` lies over the restriction of the base morphism of the
pair: this is the chart square of the relative spectrum, read through the identification of the
chart with `π⁻¹(U)`. -/
theorem pairRestrict_comp_morphismRestrict (U : s.base.affineOpens) :
    pairRestrict p U ≫ (gluedSpectrum s).toBase ∣_ U.1 = p.1 ∣_ U.1 := by
  have hw : s.algebra.hom.hom.app (.op U.1) ≫ p.2.right.app (.op U.1) = p.1.app U.1 :=
    congrArg (fun k => k.app (.op U.1)) (Under.w p.2)
  calc pairRestrict p U ≫ (gluedSpectrum s).toBase ∣_ U.1
      = (p.1 ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (p.2.right.app (.op U.1)) ≫
          (((gluedSpectrum s).chartIsoPreimage U).hom ≫
            (gluedSpectrum s).toBase ∣_ U.1) := by
        dsimp only [pairRestrict]
        rw [Category.assoc, Category.assoc]
    _ = (p.1 ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (p.2.right.app (.op U.1)) ≫
          Spec.map (s.algebra.hom.hom.app (.op U.1)) ≫ U.2.isoSpec.inv :=
        congrArg (fun k => (p.1 ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (p.2.right.app (.op U.1)) ≫ k)
          ((gluedSpectrum s).chartIsoPreimage_hom_comp_morphismRestrict U)
    _ = (p.1 ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (p.1.app U.1) ≫ U.2.isoSpec.inv :=
        congrArg (fun k => (p.1 ⁻¹ᵁ U.1).toSpecΓ ≫ k)
          ((Spec.map_comp_assoc (s.algebra.hom.hom.app (.op U.1)) (p.2.right.app (.op U.1))
              U.2.isoSpec.inv).symm.trans
            (congrArg (fun m => Spec.map m ≫ U.2.isoSpec.inv) hw))
    _ = p.1 ∣_ U.1 ≫ U.1.toSpecΓ ≫ U.2.isoSpec.inv :=
        Scheme.Opens.toSpecΓ_naturality_assoc p.1 U.1 U.2.isoSpec.inv
    _ = p.1 ∣_ U.1 :=
        (congrArg (fun k => p.1 ∣_ U.1 ≫ k) U.2.isoSpec.hom_inv_id).trans (Category.comp_id _)

/-- **Over an affine open `U` of the base, the morphism attached to a pair `(g, φ)` is cartesian
over the inclusion of `π⁻¹(U)`**: the square with `g⁻¹(U) ⟶ T` on top,
`Stacks.RelativeSpec.pairRestrict` on the left and `π⁻¹(U) ⟶ Spec_S(A)` on the bottom is a
pullback square.

It is the square defining `g⁻¹(U)` as the inverse image of `U` along `g`, with the chart square
of the relative spectrum cancelled out of it. -/
theorem isPullback_pairRestrict (U : s.base.affineOpens) :
    IsPullback (p.1 ⁻¹ᵁ U.1).ι (pairRestrict p U) (pairToHom p)
      ((gluedSpectrum s).toBase ⁻¹ᵁ U.1).ι := by
  refine IsPullback.of_bot ?_ (pairRestrict_comp_ι p U).symm
    (isPullback_morphismRestrict (gluedSpectrum s).toBase U.1).flip
  rw [pairRestrict_comp_morphismRestrict, pairToHom_toBase]
  exact (isPullback_morphismRestrict p.1 U.1).flip

/-- **Over an affine open `U` of the base, the restriction of the morphism attached to a pair is
`Stacks.RelativeSpec.pairRestrict`**, up to the canonical identification of `g⁻¹(U)` with
`(pairToHom p)⁻¹(π⁻¹(U))`. Both are pullbacks of `pairToHom p` along the inclusion of `π⁻¹(U)`,
by `Stacks.RelativeSpec.isPullback_pairRestrict`. -/
theorem exists_iso_morphismRestrict_pairToHom (U : s.base.affineOpens) :
    ∃ e : (p.1 ⁻¹ᵁ U.1).toScheme ≅
      (pairToHom p ⁻¹ᵁ ((gluedSpectrum s).toBase ⁻¹ᵁ U.1)).toScheme,
      pairToHom p ∣_ ((gluedSpectrum s).toBase ⁻¹ᵁ U.1) = e.inv ≫ pairRestrict p U :=
  ⟨_, ((isPullback_pairRestrict p U).isoIsPullback_inv_snd _ _
    (isPullback_morphismRestrict (pairToHom p) ((gluedSpectrum s).toBase ⁻¹ᵁ U.1)).flip).symm⟩

/-- **The criterion for the morphism attached to a pair `(g, φ)` to be a closed immersion**: for
a family `V` of affine opens covering the base, the inverse image `g⁻¹(V a)` is affine and `φ` is
surjective on sections over `V a`.

Being a closed immersion is local on the target, and over `π⁻¹(V a)` the morphism is
`Stacks.RelativeSpec.pairRestrict`, a composite of the isomorphism
`g⁻¹(V a) ≅ Spec Γ(T, g⁻¹(V a))`, the spectrum of the surjection `φ(V a)` and the isomorphism
`Spec A(V a) ≅ π⁻¹(V a)`.

A family is asked for rather than all the affine opens of the base because surjectivity on
sections is typically available only on the charts an algebra is presented on; take
`V := id` and `AlgebraicGeometry.iSup_affineOpens_eq_top` for all of them. -/
theorem isClosedImmersion_pairToHom {ι : Type*} (V : ι → s.base.affineOpens)
    (hV : ⨆ a, (V a).1 = ⊤)
    (haff : ∀ a, IsAffineOpen (p.1 ⁻¹ᵁ (V a).1))
    (hsurj : ∀ a, Function.Surjective (p.2.right.app (.op (V a).1))) :
    IsClosedImmersion (pairToHom p) := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun a => (gluedSpectrum s).toBase ⁻¹ᵁ (V a).1)
    ((gluedSpectrum s).toBase.iSup_preimage_eq_top hV) fun a => ?_
  have hiso : IsIso (p.1 ⁻¹ᵁ (V a).1).toSpecΓ := by
    rw [← IsAffineOpen.isoSpec_hom (haff a)]
    infer_instance
  have hrestrict : IsClosedImmersion (pairRestrict p (V a)) := by
    dsimp only [pairRestrict]
    rw [MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion,
      MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion]
    exact IsClosedImmersion.spec_of_surjective _ (hsurj a)
  obtain ⟨e, he⟩ := exists_iso_morphismRestrict_pairToHom p (V a)
  rwa [he, MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion]

end Pair

/-! ### A surjective morphism of algebras on one base -/

section AlgebraHom

variable (s : RelativeSpecSituation.{u}) (B : AlgebraSheaf s.base) (hB : B.IsQuasicoherent)
  (ψ : s.algebra ⟶ B)

/-- **The morphism of relative spectra attached to a surjective morphism of quasi-coherent
algebras on one base is a closed immersion.** Surjectivity is asked for on sections over a family
`V` of affine opens covering the base, which is where the statement is checked: chart by chart
the morphism is `Spec B(V a) ⟶ Spec A(V a)`, the spectrum of `ψ(V a)`, so this is
`AlgebraicGeometry.IsClosedImmersion.spec_of_surjective` glued over the base. -/
theorem isClosedImmersion_relativeSpectrumMapOfAlgebraHom {ι : Type*}
    (V : ι → s.base.affineOpens) (hV : ⨆ a, (V a).1 = ⊤)
    (hψ : ∀ a, Function.Surjective (ψ.right.hom.app (op (V a).1))) :
    IsClosedImmersion (relativeSpectrumMapOfAlgebraHom s B hB ψ) := by
  refine isClosedImmersion_pairToHom (s := s)
    ⟨(gluedSpectrum (s.withAlgebra B hB)).toBase,
      algebraHomAsUnder ψ ≫ (universalAlgebraMap (s.withAlgebra B hB))⟩
    V hV (fun a => isAffineOpen_toBase_preimage (s.withAlgebra B hB) (V a)) fun a y => ?_
  obtain ⟨z, hz⟩ := (ConcreteCategory.bijective_of_isIso
    ((universalAlgebraMap (s.withAlgebra B hB)).right.app (op (V a).1))).2 y
  obtain ⟨x, hx⟩ := hψ a z
  refine ⟨x, ?_⟩
  show ((universalAlgebraMap (s.withAlgebra B hB)).right.app (op (V a).1))
      ((ψ.right.hom.app (op (V a).1)) x) = y
  rw [hx, hz]

/-- **The morphism of relative spectra attached to a locally surjective morphism of
quasi-coherent algebras on one base is a closed immersion.** This is the form the statement is
usually met in: surjectivity of a morphism of sheaves is local surjectivity, and
`Stacks.SectionEpiAffine.surjective_sections_of_isLocallySurjective` — the `H¹`-vanishing content
of [Stacks, Tag 01XB] for the kernel — upgrades it to surjectivity on sections over every affine
open of the base. -/
theorem isClosedImmersion_relativeSpectrumMapOfAlgebraHom_of_isLocallySurjective
    (hψ : Sheaf.IsLocallySurjective ψ.right) :
    IsClosedImmersion (relativeSpectrumMapOfAlgebraHom s B hB ψ) :=
  isClosedImmersion_relativeSpectrumMapOfAlgebraHom s B hB ψ (fun U : s.base.affineOpens => U)
    (iSup_affineOpens_eq_top s.base) fun U =>
      Stacks.SectionEpiAffine.surjective_sections_of_isLocallySurjective ψ
        s.isQuasicoherent hB hψ U.1 U.2

end AlgebraHom

end Stacks.RelativeSpec

end
