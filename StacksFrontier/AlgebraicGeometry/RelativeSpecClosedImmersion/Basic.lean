module

public import StacksFrontier.AlgebraicGeometry.FiniteFactorization.FromSubalgebra
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.RelativeSpecCriterion
public import StacksFrontier.AlgebraicGeometry.SectionEpiAffine.AlgebraSheaf

/-!
# The relative spectrum of a surjection of algebra sheaves is a closed immersion

Let `S` be a scheme and `φ : 𝓐 ⟶ 𝓑` a morphism of quasi-coherent sheaves of commutative
`𝒪_S`-algebras whose underlying morphism of sheaves of rings is locally surjective. This file
proves that the induced morphism of relative spectra `Spec_S(𝓑) ⟶ Spec_S(𝓐)` is a closed
immersion.

## The route

`AlgebraicGeometry.IsClosedImmersion` is Zariski-local on the target, and the preimages in
`Spec_S(𝓐)` of the affine opens of `S` cover it, so it is enough to check the restriction of the
morphism to one such preimage `Z = π_𝓐⁻¹U`. Over an affine open `U` of `S` three things hold at
once: `Z` is affine ([Stacks, Tag 01LX] part (1),
`Stacks.AffineAlgebraEquivalence.isAffineOpen_preimage_relativeSpecToBase`); the preimage of `Z`
in `Spec_S(𝓑)` is `π_𝓑⁻¹U`, hence also affine, because the morphism of relative spectra is a
morphism over `S`; and the map on sections is `𝓐(U) ⟶ 𝓑(U)` read through the two
identifications `π_*𝒪 ≅ 𝓐` and `π_*𝒪 ≅ 𝓑` of [Stacks, Tag 01LX] part (3), which is surjective
because a locally surjective morphism of quasi-coherent algebra sheaves is surjective on the
sections over an affine open
(`Stacks.SectionEpiAffine.surjective_sections_of_isLocallySurjective`). A morphism of schemes
restricted to an affine open of the target over which the source is affine and the map on
sections is surjective is a closed immersion
(`Stacks.FiniteFactorization.isClosedImmersion_morphismRestrict`).

## Main results

* `Stacks.RelativeSpecClosedImmersion.preimage_relativeSpecMapOfAlgebraHom`: the preimage in
  `Spec_S(𝓑)` of the preimage in `Spec_S(𝓐)` of an open of `S` is its preimage in `Spec_S(𝓑)`.
* `Stacks.RelativeSpecClosedImmersion.surjective_app_relativeSpecMapOfAlgebraHom`: the morphism
  of relative spectra is surjective on the sections over the preimage of an affine open of the
  base.
* `Stacks.RelativeSpecClosedImmersion.isClosedImmersion_relativeSpecMapOfAlgebraHom`: **the
  relative spectrum of a locally surjective morphism of quasi-coherent algebra sheaves is a
  closed immersion.**

## Implementation notes

The hypothesis is local surjectivity of `φ.right`, the morphism of sheaves of commutative rings
underlying `φ`, rather than `CategoryTheory.Epi φ`: epimorphy in the category of algebra sheaves
is not a local condition, while local surjectivity is what
`Stacks.SectionEpiAffine.surjective_sections_of_isLocallySurjective` consumes and what an
epimorphism of the underlying quasi-coherent modules provides.

The identification of the map on sections with `φ` over `U` is
`Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap_relativeSpecMapOfAlgebraHom` read on
sections by `Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap_app`; the two outer factors
are components of the isomorphisms
`Stacks.AffineAlgebraEquivalence.pushforwardAlgebraIso`, and their surjectivity is produced from
`CategoryTheory.Iso.inv_hom_id` rather than from an `IsIso` instance on the component, exactly
as in `Stacks.RelativeSpec.isFiniteType_of_iso`.

## References

* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01S8](https://stacks.math.columbia.edu/tag/01S8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.AffineAlgebraEquivalence
open Stacks.RelativeSpec (AlgebraSheaf)

universe u

namespace Stacks.RelativeSpecClosedImmersion

variable {S : Scheme.{u}} (A B : AlgebraSheaf S)
  [AlgebraSheaf.IsQuasicoherent A] [AlgebraSheaf.IsQuasicoherent B] (φ : A ⟶ B)

/-- **The morphism of relative spectra is a morphism over `S`**, read on preimages: the preimage
in `Spec_S(𝓑)` of the preimage in `Spec_S(𝓐)` of an open `U` of `S` is the preimage of `U` in
`Spec_S(𝓑)`. -/
theorem preimage_relativeSpecMapOfAlgebraHom (U : S.Opens) :
    (relativeSpecMapOfAlgebraHom A B φ).left ⁻¹ᵁ (relativeSpecToBase A ⁻¹ᵁ U) =
      relativeSpecToBase B ⁻¹ᵁ U :=
  congrArg (fun g : relativeSpec B ⟶ S => g ⁻¹ᵁ U)
    (Over.w (relativeSpecMapOfAlgebraHom A B φ))

/-- **A morphism of schemes is surjective on the sections over an open of the target as soon as
it is so on the sections into a given open of the source equal to the full preimage.** This is
how the identification of the sections of a relative spectrum, which is stated for the preimage
of an open of the base, is read as a statement about `Scheme.Hom.app`. -/
theorem surjective_app_of_surjective_appLE {X Y : Scheme.{u}} (h : X ⟶ Y) {P : Y.Opens}
    {W : X.Opens} (hW : h ⁻¹ᵁ P = W) (e : W ≤ h ⁻¹ᵁ P)
    (hs : Function.Surjective (h.appLE P W e)) : Function.Surjective (h.app P) := by
  subst hW
  rwa [Scheme.Hom.appLE_eq_app] at hs

/-- A component of an isomorphism of algebra sheaves is surjective on sections. The inverse
provides the preimage, by `CategoryTheory.Iso.inv_hom_id`. -/
theorem surjective_app_of_algebraIso {A' B' : AlgebraSheaf S} (e : A' ≅ B') (U : (Opens ↥S)ᵒᵖ) :
    Function.Surjective (e.hom.right.hom.app U) := fun y =>
  ⟨e.inv.right.hom.app U y,
    congrFun (congrArg (fun f : B' ⟶ B' => ((f.right.hom.app U).hom : _ → _)) e.inv_hom_id) y⟩

/-- **The morphism of relative spectra is surjective on the sections over the preimage of an
affine open of the base.** Those sections are `𝓐(U)` and `𝓑(U)` by [Stacks, Tag 01LX] part (3),
and the map between them is `φ` over `U`, which is surjective because `φ` is locally
surjective. -/
theorem surjective_app_relativeSpecMapOfAlgebraHom
    (hφ : CategoryTheory.Sheaf.IsLocallySurjective φ.right) {U : S.Opens} (hU : IsAffineOpen U) :
    Function.Surjective ((relativeSpecMapOfAlgebraHom A B φ).left.app
      (relativeSpecToBase A ⁻¹ᵁ U)) := by
  have hφU : Function.Surjective (φ.right.hom.app (op U)) :=
    Stacks.SectionEpiAffine.surjective_sections_of_isLocallySurjective φ
      ‹AlgebraSheaf.IsQuasicoherent A› ‹AlgebraSheaf.IsQuasicoherent B› hφ U hU
  have key : Function.Surjective
      ((pushforwardAlgebraMap (relativeSpecMapOfAlgebraHom A B φ)).right.hom.app (op U)) := by
    rw [pushforwardAlgebraMap_relativeSpecMapOfAlgebraHom]
    exact Stacks.FiniteFactorization.surjective_comp
      (surjective_app_of_algebraIso (pushforwardAlgebraIso A) (op U))
      (Stacks.FiniteFactorization.surjective_comp hφU
        (surjective_app_of_algebraIso (pushforwardAlgebraIso B).symm (op U)))
  rw [pushforwardAlgebraMap_app (relativeSpecMapOfAlgebraHom A B φ) U
    (preimage_le_preimage_preimage (relativeSpecMapOfAlgebraHom A B φ) U)] at key
  exact surjective_app_of_surjective_appLE _ (preimage_relativeSpecMapOfAlgebraHom A B φ U) _ key

/-- **The relative spectrum of a locally surjective morphism of quasi-coherent algebra sheaves is
a closed immersion.** This is the statement that makes a surjection of quasi-coherent algebra
sheaves cut out a closed subscheme of a relative spectrum. -/
theorem isClosedImmersion_relativeSpecMapOfAlgebraHom
    (hφ : CategoryTheory.Sheaf.IsLocallySurjective φ.right) :
    IsClosedImmersion (relativeSpecMapOfAlgebraHom A B φ).left := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun U : S.affineOpens => relativeSpecToBase A ⁻¹ᵁ (U : S.Opens))
    ((relativeSpecToBase A).iSup_preimage_eq_top (iSup_affineOpens_eq_top S)) fun U => ?_
  refine Stacks.FiniteFactorization.isClosedImmersion_morphismRestrict _ _
    (isAffineOpen_preimage_relativeSpecToBase A U) ?_
    (surjective_app_relativeSpecMapOfAlgebraHom A B φ hφ U.2)
  rw [preimage_relativeSpecMapOfAlgebraHom A B φ (U : S.Opens)]
  exact isAffineOpen_preimage_relativeSpecToBase B U

end Stacks.RelativeSpecClosedImmersion

end
