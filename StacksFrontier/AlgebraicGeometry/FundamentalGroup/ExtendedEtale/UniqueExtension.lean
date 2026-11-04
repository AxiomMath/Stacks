module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.ExtensionScheme
public import StacksFrontier.AlgebraicGeometry.QuasicoherentAlgebraEqualizer.FiniteEtale
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.GluingCharacterization
public import StacksFrontier.AlgebraicGeometry.Reflexive.ExtensionChain.Depth
import StacksCore.Tactic.StacksAttribute

/-!
# The extension of a finite étale cover is finite over the base

Let `X` be a locally Noetherian scheme, `j : U ⟶ X` an open immersion whose complement consists
of points at which `𝒪_X` has depth at least two, and `π : V ⟶ U` a finite étale morphism. The
extension `Spec_X(𝓑)` of the cover, for `𝓑 = (π ≫ j)_* 𝒪_V`, is
`Stacks.FundamentalGroup.ExtendedEtaleFold.extendedEtaleScheme`. Its structure morphism is
finite, and at the points of `X` outside the range of `j` the stalks of `𝓑` have depth at least
two over the local rings of `X`.

## Main results

* `isFinite_relativeSpecToBase_of_isFiniteType` — the structure morphism of the relative spectrum
  of a quasi-coherent algebra of finite type is a finite morphism.
* `isFinite_extendedEtaleToBase` — the extension of a finite étale cover is finite over the base.
* `isFinite_relativeSpectrum_extendedEtaleSituation` — the same statement written with the bundled
  relative spectrum of [Stacks, Tag 01LP].
* `two_le_depth_stalk_extendedEtaleAlgebra` — off the cover, the stalk of the extension algebra
  has depth at least two over the local ring of the base.

## References

* [Stacks Project, Tag 0EY6](https://stacks.math.columbia.edu/tag/0EY6)
* [Stacks Project, Tag 01LP](https://stacks.math.columbia.edu/tag/01LP)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
* [Stacks Project, Tag 0EBI](https://stacks.math.columbia.edu/tag/0EBI)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.QuasicoherentAlgebraEqualizer

universe u

namespace Stacks.FundamentalGroup.ExtendedEtaleFold

/-! ### Finiteness of a relative spectrum -/

/-- The relative spectrum of a quasi-coherent algebra of finite type is finite over the base. -/
public theorem isFinite_relativeSpecToBase_of_isFiniteType {X : Scheme.{u}} (A : AlgebraSheaf X)
    [A.IsQuasicoherent]
    [SheafOfModules.IsFiniteType.{u, u, u} (AlgebraSheaf.underlyingModule A)] :
    IsFinite (relativeSpecToBase A) :=
  isFinite_relativeSpecToBase A fun W =>
    AlgebraicGeometry.moduleFinite_sections_on_affine (AlgebraSheaf.underlyingModule A) W.1 W.2

/-! ### The extension of a finite étale cover -/

variable {U X V : Scheme.{u}} [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j]
  (π : V ⟶ U) [IsFinite π] [Etale π]
  (hdepth : ∀ x : X, x ∉ (j.opensRange : Set X) →
    (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))

/-- The extension of a finite étale cover across a depth-two complement is finite over the base:
the structure morphism of `Spec_X(𝓑)`, for `𝓑 = (π ≫ j)_* 𝒪_V`, is a finite morphism. -/
@[stacks 0EY6 "unique_extension"]
public instance isFinite_extendedEtaleToBase : IsFinite (extendedEtaleToBase j π hdepth) :=
  haveI : _root_.SheafOfModules.IsCoherent
      (AlgebraSheaf.underlyingModule (pushforwardAlgebra (π ≫ j))) :=
    extendedEtaleAlgebra_isCoherent j π hdepth
  haveI : (pushforwardAlgebra (π ≫ j)).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  haveI : SheafOfModules.IsFiniteType.{u, u, u}
      (AlgebraSheaf.underlyingModule (pushforwardAlgebra (π ≫ j))) :=
    _root_.SheafOfModules.IsCoherent.isFiniteType
  isFinite_relativeSpecToBase_of_isFiniteType (pushforwardAlgebra (π ≫ j))

/-- The structure morphism of the bundled relative spectrum of [Stacks, Tag 01LP],
`Stacks.RelativeSpec.relativeSpectrum (extendedEtaleSituation j π hdepth)`, is finite. -/
public theorem isFinite_relativeSpectrum_extendedEtaleSituation :
    IsFinite (relativeSpectrum (extendedEtaleSituation j π hdepth)).toBase :=
  isFinite_extendedEtaleToBase j π hdepth

/-! ### Depth of the extension algebra off the cover -/


include hdepth in
/-- At a point `x` of `X` outside the range of `j`, the stalk of the `𝒪_X`-module underlying
`𝓑 = (π ≫ j)_* 𝒪_V` has depth at least two over `𝒪_{X, x}`. -/
public theorem two_le_depth_stalk_extendedEtaleAlgebra (x : X)
    (hx : x ∉ (j.opensRange : Set X)) :
    (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      ((AlgebraSheaf.underlyingModule (pushforwardAlgebra (π ≫ j))).presheaf.stalk x) :=
  have : _root_.SheafOfModules.IsCoherent
      (AlgebraSheaf.underlyingModule (pushforwardAlgebra (π ≫ j))) :=
    extendedEtaleAlgebra_isCoherent j π hdepth
  depth_stalk_ge_two_of_isReflexive _ (extendedEtaleAlgebra_isReflexive j π hdepth) x
    (hdepth x hx)

end Stacks.FundamentalGroup.ExtendedEtaleFold

end
