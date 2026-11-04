module

public import StacksFrontier.AlgebraicGeometry.RelativeSpec.Representability
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The canonical morphism to the relative spectrum of the pushed-forward structure sheaf

Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes. Then the direct
image `f_* 𝒪_X` is a quasi-coherent sheaf of commutative `𝒪_S`-algebras, so it has a relative
spectrum `π : Spec_S(f_* 𝒪_X) ⟶ S`, and the identity map of `f_* 𝒪_X` is a relative-spectrum
pair for `f`. The morphism it classifies is the canonical morphism
`can : X ⟶ Spec_S(f_* 𝒪_X)` over `S`, and over an affine open `U` of `S` it restricts to the
canonical morphism `f⁻¹(U) ⟶ Spec Γ(f⁻¹(U), 𝒪_X)`. Over such a `U` the canonical morphism is
moreover an isomorphism on sections, inverse to the universal algebra map.

## Main definitions

* `Stacks.RelativeSpec.pushforwardSituation` is the relative-spectrum situation of `f_* 𝒪_X`,
  and `Stacks.RelativeSpec.pushforwardSpectrum` is its relative spectrum together with all its
  affine charts.
* `Stacks.RelativeSpec.pushforwardPair` is the relative-spectrum pair consisting of `f` together
  with the identity map of `f_* 𝒪_X`.
* `Stacks.RelativeSpec.toRelativeSpec` is the canonical morphism `X ⟶ Spec_S(f_* 𝒪_X)`;
  `Stacks.RelativeSpec.canonicalMorphism` is the same morphism under the name by which it is
  referred to downstream.

## Main results

* `Stacks.RelativeSpec.AlgebraSheaf.isQuasicoherent_pushforwardAlgebra`: the algebra `f_* 𝒪_X`
  is quasi-coherent.
* `Stacks.RelativeSpec.isAffineHom_toBase`: the relative spectrum of a quasi-coherent algebra is
  affine over its base.
* `Stacks.RelativeSpec.toRelativeSpec_toBase`: the canonical morphism is a morphism over `S`.
* `Stacks.RelativeSpec.ι_toRelativeSpec`: over an affine open `U` of the base, the canonical
  morphism restricts to `f⁻¹(U).toSpecΓ` followed by the chart of `U`; and
  `Stacks.RelativeSpec.ι_toRelativeSpec_eq_chartIsoPreimage` is the same statement read in the
  open subscheme `π⁻¹(U)`.
* `Stacks.RelativeSpec.universalAlgebraMap_app_comp_canonicalMorphism_appLE`,
  `Stacks.RelativeSpec.isIso_canonicalMorphism_appLE` and
  `Stacks.RelativeSpec.isIso_canonicalMorphism_app`: over an affine open `U` of the base, the
  canonical morphism identifies the sections of the relative spectrum over `π⁻¹(U)` with the
  sections of `X` over `f⁻¹(U)`, being inverse there to the universal algebra map.

## Implementation notes

Quasi-coherence of `f_* 𝒪_X` is quasi-coherence of its underlying `𝒪_S`-module, which is by
definition the direct image of the unit module `𝒪_X`; so it is Tag 01LC applied to
`SheafOfModules.unit X.ringCatSheaf`. Note that
`Stacks.AffineAlgebraEquivalence.isQuasicoherent_pushforwardAlgebra` is the same statement for
an *affine* morphism, where no quasi-coherence of direct images is needed.

The canonical morphism is `Stacks.RelativeSpec.pairToHom` applied to the pair `(f, 𝟙)`; this is
the inverse direction of the representing bijection of Tag 01LV, so the assertions about it are
the general facts `pairToHom_toBase`, `ι_pairToHom` and `pairToHom_appLE` about that
construction, the second simplified by `Spec.map (𝟙 _) = 𝟙 _`. The algebra component of the
pair is literally an identity morphism because `(f_* 𝒪_X).hom.hom` is `f.c`.

Affineness of the structure morphism of a relative spectrum is `isAffineHom_relativeSpecToBase`;
it is restated here for `Stacks.RelativeSpec.gluedSpectrum` so that it is found by instance
search at the form in which the structure morphism occurs downstream.

## References

* [Stacks Project, Tag 01LY](https://stacks.math.columbia.edu/tag/01LY)
* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
* [Stacks Project, Tag 01I1](https://stacks.math.columbia.edu/tag/01I1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.RelativeSpec

/-! ### Affineness of the structure morphism of a relative spectrum -/

/-- The relative spectrum of a quasi-coherent algebra is affine over its base: the inverse image
of an affine open `U` of the base is the spectrum of the sections of the algebra over `U`. -/
@[sga "3 I 4.2" "Spec(A) is affine over S"]
instance isAffineHom_toBase (s : RelativeSpecSituation.{u}) :
    IsAffineHom (gluedSpectrum s).toBase :=
  isAffineHom_relativeSpecToBase s.algebra

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-! ### Quasi-coherence of the pushed-forward structure sheaf -/

/-- For a quasi-compact and quasi-separated morphism of schemes `f : X ⟶ S`, the sheaf of
`𝒪_S`-algebras `f_* 𝒪_X` is quasi-coherent.

This is Tag 01LC for the structure sheaf of `X`: the `𝒪_S`-module underlying `f_* 𝒪_X` is the
direct image of the unit module over `𝒪_X`. -/
@[stacks 01LY "quasi-coherence of the pushed-forward algebra",
  ega "I 4.1.1" "more general",
  ega "I 9.2.2" "special case",
  ega "IV 11.10.3",
  ega "IV 21.12.1",
  ega "IV 3.1.10.2" "special case",
  sga "3 III 0.13" "special case",
  sga "3 VIB 11.0" "special case"]
instance AlgebraSheaf.isQuasicoherent_pushforwardAlgebra [QuasiCompact f] [QuasiSeparated f] :
    AlgebraSheaf.IsQuasicoherent (pushforwardAlgebra f) :=
  AlgebraicGeometry.pushforward_isQuasicoherent f (SheafOfModules.unit X.ringCatSheaf)

/-! ### The relative spectrum of the pushed-forward structure sheaf -/

variable [QuasiCompact f] [QuasiSeparated f]

/-- The relative-spectrum situation attached to a quasi-compact and quasi-separated morphism
`f : X ⟶ S`: the base `S` together with the quasi-coherent algebra `f_* 𝒪_X`. -/
noncomputable abbrev pushforwardSituation : RelativeSpecSituation.{u} :=
  situation (pushforwardAlgebra f)

/-- The base of `pushforwardSituation f` is `S`. -/
@[simp]
theorem pushforwardSituation_base : (pushforwardSituation f).base = S := rfl

/-- The algebra of `pushforwardSituation f` is `f_* 𝒪_X`. -/
@[simp]
theorem pushforwardSituation_algebra :
    (pushforwardSituation f).algebra = pushforwardAlgebra f := rfl

/-- The relative spectrum `Spec_S(f_* 𝒪_X)` of the pushed-forward structure sheaf of a
quasi-compact and quasi-separated morphism, together with its structure morphism to `S` and its
affine charts. -/
noncomputable abbrev pushforwardSpectrum : GluedSpectrum (pushforwardSituation f) :=
  gluedSpectrum (pushforwardSituation f)

/-- The relative-spectrum pair over `X` consisting of `f` itself together with the identity map
of `f_* 𝒪_X`. The structure morphism of the algebra `f_* 𝒪_X` is `f.c`, so the identity map of
`f_* 𝒪_X` is literally an identity morphism of objects under `f.c`. -/
noncomputable def pushforwardPair : RelativeSpecPair (pushforwardSituation f) X := ⟨f, 𝟙 _⟩

/-- The morphism of `pushforwardPair f` is `f`. -/
@[simp]
theorem pushforwardPair_fst : (pushforwardPair f).1 = f := rfl

/-- Over an open `U` of `S`, the algebra map of `pushforwardPair f` is the identity of
`Γ(X, f⁻¹(U))`. -/
@[simp]
theorem pushforwardPair_snd_app (U : S.Opens) :
    (pushforwardPair f).2.right.app (op U) = 𝟙 Γ(X, f ⁻¹ᵁ U) := rfl

/-! ### The canonical morphism -/

/-- The canonical morphism `can : X ⟶ Spec_S(f_* 𝒪_X)` from the source of a quasi-compact,
quasi-separated morphism to the relative spectrum of the direct image of its structure sheaf. It
is the morphism classified by the identity map of `f_* 𝒪_X` under the representing bijection of
Tag 01LV. -/
@[stacks 01LY "canonical morphism", ega "III 4.3.1"]
noncomputable def toRelativeSpec : X ⟶ (gluedSpectrum (pushforwardSituation f)).scheme :=
  pairToHom (pushforwardPair f)

/-- The canonical morphism `can : X ⟶ Spec_S(f_* 𝒪_X)`, under the name by which it is referred
to in the literature and downstream in this library. It is `toRelativeSpec`. -/
noncomputable abbrev canonicalMorphism : X ⟶ (pushforwardSpectrum f).scheme := toRelativeSpec f

/-- The canonical morphism is the morphism attached by the universal property of the relative
spectrum to the pair `(f, id)`. -/
theorem canonicalMorphism_eq_pairToHom :
    canonicalMorphism f = pairToHom (pushforwardPair f) := rfl

/-- The canonical morphism to the relative spectrum of `f_* 𝒪_X` is a morphism of schemes over
`S`. -/
@[stacks 01LY "morphism over the base"]
theorem toRelativeSpec_toBase :
    toRelativeSpec f ≫ (gluedSpectrum (pushforwardSituation f)).toBase = f :=
  pairToHom_toBase (pushforwardPair f)

/-- The canonical morphism to the relative spectrum of `f_* 𝒪_X` is a morphism of schemes over
`S`, stated for `canonicalMorphism`. -/
theorem canonicalMorphism_comp_toBase :
    canonicalMorphism f ≫ (pushforwardSpectrum f).toBase = f :=
  toRelativeSpec_toBase f

/-- The inverse image under the canonical morphism of the inverse image in the relative spectrum
of an open of the base is the inverse image of that open under `f`. -/
@[simp]
theorem canonicalMorphism_preimage_preimage (U : S.Opens) :
    canonicalMorphism f ⁻¹ᵁ ((pushforwardSpectrum f).toBase ⁻¹ᵁ U) = f ⁻¹ᵁ U := by
  rw [← Scheme.Hom.comp_preimage, canonicalMorphism_comp_toBase]

/-- Over an affine open `U` of the base, the canonical morphism to the relative spectrum of
`f_* 𝒪_X` restricts on `f⁻¹(U)` to the canonical morphism `f⁻¹(U) ⟶ Spec Γ(f⁻¹(U), 𝒪_X)`,
followed by the chart of `U`. -/
@[stacks 01LY "identification on affine opens"]
theorem ι_toRelativeSpec (U : S.affineOpens) :
    (f ⁻¹ᵁ U.1).ι ≫ toRelativeSpec f =
      (f ⁻¹ᵁ U.1).toSpecΓ ≫ (gluedSpectrum (pushforwardSituation f)).chart U := by
  refine (ι_pairToHom (pushforwardPair f) U).trans ?_
  have e : Spec.map (𝟙 Γ(X, f ⁻¹ᵁ U.1)) = 𝟙 (Spec Γ(X, f ⁻¹ᵁ U.1)) := Spec.map_id _
  exact (congrArg (fun k => (f ⁻¹ᵁ U.1).toSpecΓ ≫
    k ≫ (gluedSpectrum (pushforwardSituation f)).chart U) e).trans
      (congrArg (fun k => (f ⁻¹ᵁ U.1).toSpecΓ ≫ k) (Category.id_comp _))

/-- Over an affine open `U` of the base, the restriction of the canonical morphism to `f⁻¹(U)`,
read in the open subscheme `π⁻¹(U)`, is the canonical morphism `f⁻¹(U) ⟶ Spec Γ(f⁻¹(U), 𝒪_X)`
followed by the identification of that spectrum with `π⁻¹(U)`. -/
theorem ι_toRelativeSpec_eq_chartIsoPreimage (U : S.affineOpens) :
    (f ⁻¹ᵁ U.1).ι ≫ toRelativeSpec f =
      (f ⁻¹ᵁ U.1).toSpecΓ ≫ ((pushforwardSpectrum f).chartIsoPreimage U).hom ≫
        ((pushforwardSpectrum f).toBase ⁻¹ᵁ U.1).ι :=
  (ι_toRelativeSpec f U).trans <|
    (congrArg (fun k => (f ⁻¹ᵁ U.1).toSpecΓ ≫ k)
      ((pushforwardSpectrum f).chartIsoPreimage_hom_ι U)).symm

/-! ### The canonical morphism on sections -/

/-- **Stacks Project, Tag 01LY.** Over an affine open `U` of the base, the canonical morphism
identifies the sections of the relative spectrum over `π⁻¹(U)` with the sections
`Γ(X, f⁻¹(U))`: it is inverse to the universal algebra map at `U`. -/
theorem universalAlgebraMap_app_comp_canonicalMorphism_appLE (U : S.affineOpens) :
    (universalAlgebraMap (pushforwardSituation f)).right.app (op U.1) ≫
        (canonicalMorphism f).appLE ((pushforwardSpectrum f).toBase ⁻¹ᵁ U.1) (f ⁻¹ᵁ U.1)
          (canonicalMorphism_preimage_preimage f U.1).ge =
      𝟙 Γ(X, f ⁻¹ᵁ U.1) :=
  pairToHom_appLE (pushforwardPair f) U (canonicalMorphism_preimage_preimage f U.1).ge

/-- The canonical morphism is an isomorphism on the sections over `π⁻¹(U)`, for every affine
open `U` of the base, as a map to the sections over `f⁻¹(U)`. -/
theorem isIso_canonicalMorphism_appLE (U : S.affineOpens) :
    IsIso ((canonicalMorphism f).appLE ((pushforwardSpectrum f).toBase ⁻¹ᵁ U.1) (f ⁻¹ᵁ U.1)
      (canonicalMorphism_preimage_preimage f U.1).ge) := by
  have _ := isIso_universalAlgebraMap_app (pushforwardSituation f) U
  have h := universalAlgebraMap_app_comp_canonicalMorphism_appLE f U
  have hc : IsIso ((universalAlgebraMap (pushforwardSituation f)).right.app (op U.1) ≫
      (canonicalMorphism f).appLE ((pushforwardSpectrum f).toBase ⁻¹ᵁ U.1) (f ⁻¹ᵁ U.1)
        (canonicalMorphism_preimage_preimage f U.1).ge) := by
    rw [h]
    exact IsIso.id _
  exact IsIso.of_isIso_comp_left
    ((universalAlgebraMap (pushforwardSituation f)).right.app (op U.1)) _

/-- The canonical morphism is an isomorphism on the sections over `π⁻¹(U)` for every affine
open `U` of the base. -/
instance isIso_canonicalMorphism_app (U : S.affineOpens) :
    IsIso ((canonicalMorphism f).app ((pushforwardSpectrum f).toBase ⁻¹ᵁ U.1)) := by
  rw [Scheme.Hom.app_eq_appLE]
  exact (Scheme.Hom.appLE_congr _ le_rfl rfl (canonicalMorphism_preimage_preimage f U.1)
    fun g ↦ IsIso g).mpr (isIso_canonicalMorphism_appLE f U)

end Stacks.RelativeSpec

end
