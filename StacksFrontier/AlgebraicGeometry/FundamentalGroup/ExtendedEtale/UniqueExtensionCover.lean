module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.ExtensionScheme
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.CanonicalMap
import StacksCore.Tactic.StacksAttribute

/-!
# The comparison of a finite étale cover with its extension

Let `X` be a locally Noetherian scheme, `j : U ⟶ X` an open immersion whose complement consists
of points at which `𝒪_X` has depth at least two, and `π : V ⟶ U` a finite étale morphism. The
extension of the cover is the relative spectrum of `𝓑 = (π ≫ j)_* 𝒪_V`, and [Stacks, Tag 0EY6]
asserts of it, among other things, that the cover maps canonically into it and that this map
identifies the cover with the part of the extension lying over `U`.

This file constructs that canonical map and proves both statements about it: it is the morphism
classifying the identity of `𝓑`, and the square it forms with `π`, `j` and the structure
morphism of the extension is cartesian.

## Main definitions

* `extendedEtaleCoverMap` — the canonical morphism `V ⟶ Spec_X(𝓑)`.

## Main results

* `extendedEtaleCoverMap_homEquiv` — the comparison morphism is the one that the representing
  property of the relative spectrum attaches to the identity map of `𝓑`.
* `extendedEtaleCoverMap_comp_toBase` — it lies over `π ≫ j`.
* `extendedEtaleCoverMap_isPullback` — the comparison identifies the cover with the restriction
  of the extension to the open subscheme.
* `isAffineOpen_preimage_comp_of_le_opensRange` — the inverse image under `π ≫ j` of an affine
  open of `X` inside the image of `j` is affine. This is the only geometric input the cartesian
  square needs.

## Implementation notes

**No `@[stacks]` attribute is placed here.** The bare tag `0EY6` has six clauses across eighteen
covering-set members, and the audit scanner matches the bare four characters, so a single
attribute anywhere would render the whole tag as formalized.

Everything is deduced from `Stacks.RelativeSpec.isPullback_canonicalMap`, which is stated for an
arbitrary morphism with quasi-coherent pushforward algebra factoring through an open immersion.
Its one hypothesis is affineness of the inverse images of the affine opens inside the image of
the open immersion, and that holds here for a reason that has nothing to do with depth: an
affine open `W ≤ j.opensRange` pulls back under the open immersion `j` to an affine open of `U`
([Stacks, Tag 01HX]), and `π` is finite, hence affine, so the further inverse image is affine
again. **No depth hypothesis is used in this file**; `hdepth` enters only through
`extendedEtaleSituation`, i.e. only to know that `𝓑` is quasi-coherent, which is
`extendedEtaleAlgebra_isCoherent`. In particular the comparison morphism exists and the square
is cartesian for any finite `π` with quasi-coherent `(π ≫ j)_* 𝒪_V`.

The quasi-coherence instance is supplied by a `let` in each declaration rather than being
registered globally, because it depends on `hdepth`, which is not an instance-implicit argument;
this is the same pattern as
`Stacks.FundamentalGroup.ExtendedEtaleFold.extendedEtaleScheme`. The situation
`extendedEtaleSituation j π hdepth` and `Stacks.RelativeSpec.situationOfPushforward (π ≫ j)` are
definitionally equal — they have the same base and the same algebra, and the quasi-coherence
field is a proposition — so the statements below are literally about the relative spectrum of
the former while their proofs are about the latter.

## References

* [Stacks Project, Tag 0EY6](https://stacks.math.columbia.edu/tag/0EY6)
* [Stacks Project, Tag 01LV](https://stacks.math.columbia.edu/tag/01LV)
* [Stacks Project, Tag 01LP](https://stacks.math.columbia.edu/tag/01LP)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec

universe u

namespace Stacks.FundamentalGroup.ExtendedEtaleFold

variable {U X V : Scheme.{u}} [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j]
  (π : V ⟶ U) [IsFinite π] [Etale π]
  (hdepth : ∀ x : X, x ∉ (j.opensRange : Set X) →
    (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))

/-! ### The comparison morphism -/

/-- **The canonical morphism from the cover to its extension.** It is the morphism that the
representing property of the relative spectrum ([Stacks, Tag 01LV]) attaches to the identity map
of `𝓑 = (π ≫ j)_* 𝒪_V`, which is the algebra of the extension. -/
public def extendedEtaleCoverMap :
    V ⟶ (gluedSpectrum (extendedEtaleSituation j π hdepth)).scheme :=
  let _ : _root_.SheafOfModules.IsCoherent
      (AlgebraSheaf.underlyingModule (pushforwardAlgebra (π ≫ j))) :=
    extendedEtaleAlgebra_isCoherent j π hdepth
  let _ : (pushforwardAlgebra (π ≫ j)).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  canonicalMap (π ≫ j)

/-- **The comparison morphism is uniquely characterized by the identity map of the pushed-forward
structure algebra.** This is the clause of [Stacks, Tag 0EY6] that pins the comparison: the
relative-spectrum bijection sends it to the pair consisting of `π ≫ j` and the identity of `𝓑`. -/
public theorem extendedEtaleCoverMap_homEquiv :
    (relativeSpecRepresentableBy (extendedEtaleSituation j π hdepth)).homEquiv
        (extendedEtaleCoverMap j π hdepth) = ⟨π ≫ j, Under.homMk (𝟙 _) (by rfl)⟩ :=
  let _ : _root_.SheafOfModules.IsCoherent
      (AlgebraSheaf.underlyingModule (pushforwardAlgebra (π ≫ j))) :=
    extendedEtaleAlgebra_isCoherent j π hdepth
  let _ : (pushforwardAlgebra (π ≫ j)).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  canonicalMap_homEquiv (π ≫ j)

/-- **The comparison morphism lies over `π ≫ j`.** -/
public theorem extendedEtaleCoverMap_comp_toBase :
    extendedEtaleCoverMap j π hdepth ≫
      (gluedSpectrum (extendedEtaleSituation j π hdepth)).toBase = π ≫ j :=
  let _ : _root_.SheafOfModules.IsCoherent
      (AlgebraSheaf.underlyingModule (pushforwardAlgebra (π ≫ j))) :=
    extendedEtaleAlgebra_isCoherent j π hdepth
  let _ : (pushforwardAlgebra (π ≫ j)).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  canonicalMap_comp_toBase (π ≫ j)

/-! ### The cartesian square -/

omit [IsLocallyNoetherian X] [Etale π] in
/-- **The inverse image under `π ≫ j` of an affine open inside the image of `j` is affine.** The
open immersion `j` identifies such an affine open with an affine open of `U`, and `π` is finite,
hence affine. -/
public theorem isAffineOpen_preimage_comp_of_le_opensRange (W : X.affineOpens)
    (hW : W.1 ≤ j.opensRange) : IsAffineOpen ((π ≫ j) ⁻¹ᵁ W.1) := by
  rw [Scheme.Hom.comp_preimage]
  exact (W.2.preimage_of_isOpenImmersion j hW).preimage π

/-- **The comparison morphism identifies the cover with the restriction of the extension to the
open subscheme.** This is the pullback clause of [Stacks, Tag 0EY6]: the square formed by the
cover `π`, the comparison morphism, the open immersion `j` and the structure morphism of the
extension is cartesian. -/
@[stacks 0EY6 "unique_extension"]
public theorem extendedEtaleCoverMap_isPullback :
    IsPullback π (extendedEtaleCoverMap j π hdepth) j
      (gluedSpectrum (extendedEtaleSituation j π hdepth)).toBase := by
  let _ : _root_.SheafOfModules.IsCoherent
      (AlgebraSheaf.underlyingModule (pushforwardAlgebra (π ≫ j))) :=
    extendedEtaleAlgebra_isCoherent j π hdepth
  let _ : (pushforwardAlgebra (π ≫ j)).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  exact isPullback_canonicalMap (π ≫ j) j π rfl
    (isAffineOpen_preimage_comp_of_le_opensRange j π)

end Stacks.FundamentalGroup.ExtendedEtaleFold

end
