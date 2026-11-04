module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.Algebra
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.RelativeSpec

/-!
# The extension of a finite étale cover across a depth-two complement, as a scheme

Let `X` be a locally Noetherian scheme, `j : U ⟶ X` an open immersion whose complement consists
of points at which `𝒪_X` has depth at least two, and `π : V ⟶ U` a finite étale morphism.
[Stacks, Tag 0EY6] attaches to this data the scheme `Spec_X(𝓑)` for `𝓑 = (π ≫ j)_* 𝒪_V`, and
every remaining clause of that tag — finiteness, the comparison with the cover, uniqueness,
étaleness versus flatness, étaleness versus finite local freeness — is a statement about it.

## Main definitions

* `extendedEtaleScheme` — the scheme `Spec_X(𝓑)`.
* `extendedEtaleToBase` — its structure morphism to `X`.

## Main results

* `isAffineHom_extendedEtaleToBase` — the structure morphism is affine.

## References

* [Stacks Project, Tag 0EY6](https://stacks.math.columbia.edu/tag/0EY6)
* [Stacks Project, Tag 01LP](https://stacks.math.columbia.edu/tag/01LP)
-/


@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec

universe u

namespace Stacks.FundamentalGroup.ExtendedEtaleFold

variable {U X V : Scheme.{u}} [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j]
  (π : V ⟶ U) [IsFinite π] [Etale π]
  (hdepth : ∀ x : X, x ∉ (j.opensRange : Set X) →
    (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))

/-- **The extension of a finite étale cover across a depth-two complement.** This is
`Spec_X(𝓑)` for `𝓑 = (π ≫ j)_* 𝒪_V`, the scheme that [Stacks, Tag 0EY6] attaches to a finite
étale cover `π` of an open subscheme `j` whose complement carries depth at least two. -/
public def extendedEtaleScheme : Scheme.{u} :=
  letI : _root_.SheafOfModules.IsCoherent
      (AlgebraSheaf.underlyingModule (pushforwardAlgebra (π ≫ j))) :=
    extendedEtaleAlgebra_isCoherent j π hdepth
  letI : (pushforwardAlgebra (π ≫ j)).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  relativeSpec (pushforwardAlgebra (π ≫ j))

/-- **The structure morphism of the extension.** -/
public def extendedEtaleToBase : extendedEtaleScheme j π hdepth ⟶ X :=
  letI : _root_.SheafOfModules.IsCoherent
      (AlgebraSheaf.underlyingModule (pushforwardAlgebra (π ≫ j))) :=
    extendedEtaleAlgebra_isCoherent j π hdepth
  letI : (pushforwardAlgebra (π ≫ j)).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  relativeSpecToBase (pushforwardAlgebra (π ≫ j))

/-- **The structure morphism of the extension is an affine morphism.** The preimage of an affine
open `W` of `X` is the spectrum of `𝓑(W)`. -/
public instance isAffineHom_extendedEtaleToBase :
    IsAffineHom (extendedEtaleToBase j π hdepth) :=
  letI : _root_.SheafOfModules.IsCoherent
      (AlgebraSheaf.underlyingModule (pushforwardAlgebra (π ≫ j))) :=
    extendedEtaleAlgebra_isCoherent j π hdepth
  letI : (pushforwardAlgebra (π ≫ j)).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  isAffineHom_relativeSpecToBase (pushforwardAlgebra (π ≫ j))

end Stacks.FundamentalGroup.ExtendedEtaleFold

end
