module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType

/-!
# A quasi-coherent module of finite type is a finite `tilde` on every affine open

On a scheme `X`, a quasi-coherent `𝒪_X`-module of finite type restricts, over every affine open
`U`, to the sheaf associated with a finite `Γ(X, U)`-module. This is the implication
(2) ⇒ (4) of the coherence characterisation of a locally Noetherian scheme.

## Main results

* `Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_restrict`: finite type is preserved by
  restriction along an open immersion of schemes.
* `Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteTildeOn_of_isQuasicoherent_of_isFiniteType`:
  a quasi-coherent module of finite type satisfies `IsFiniteTildeOn` at every affine open.

## Implementation notes

`Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteTildeOn_of_finite_specModule` reduces the second
statement to finiteness of the `Γ(X, U)`-module `specModule F hU`. That finiteness is read off
the affine statement that the sheaf associated with a module is of finite type exactly when the
module is finitely generated, applied on `Spec Γ(X, U)` to `specModule F hU`: the restriction
`specRestrict F hU` is quasi-coherent, hence isomorphic to the sheaf associated with its global
sections, and it is of finite type because `F` is and because restriction preserves finite type.

Restriction preserves finite type because the restriction functor is isomorphic to the pullback
functor, and the scheme-level pullback of modules is the ringed-space pullback of the underlying
morphism of ringed spaces, for which preservation of finite type is already available.

## References

* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
* [Stacks Project, Tag 01B6](https://stacks.math.columbia.edu/tag/01B6)
-/

@[expose] public section

open CategoryTheory Limits SheafOfModules TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.CoherentTFAE

variable {X Y : Scheme.{u}}

/-- **Finite type is preserved by restriction along an open immersion.** The restriction functor
is isomorphic to the pullback functor, and the pullback of a finite type module along a morphism
of ringed spaces is of finite type. -/
theorem isFiniteType_restrict (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules)
    [M.IsFiniteType] : (M.restrict f).IsFiniteType :=
  have : ((Scheme.Modules.pullback f).obj M).IsFiniteType :=
    _root_.AlgebraicGeometry.SheafOfModules.pullback_isFiniteType f.toLRSHom.toShHom M
  Stacks.SheafOfModules.isFiniteType_of_iso.{u}
    ((Scheme.Modules.restrictFunctorIsoPullback f).app M).symm

/-- **(2) ⇒ (4) of [Stacks, Tag 01XZ].** A quasi-coherent module of finite type is, on every
affine open `U`, the sheaf associated with a finite `Γ(X, U)`-module. -/
theorem isFiniteTildeOn_of_isQuasicoherent_of_isFiniteType (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (U : X.Opens) (hU : IsAffineOpen U) :
    IsFiniteTildeOn F U hU :=
  have : (F.restrict U.ι).IsFiniteType := isFiniteType_restrict U.ι F
  have : (specRestrict F hU).IsFiniteType := isFiniteType_restrict hU.isoSpec.inv _
  have : (specRestrict F hU).IsQuasicoherent := inferInstance
  have h : (tilde (specModule F hU)).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_iso.{u} (M := specRestrict F hU)
      (asIso (specRestrict F hU).fromTildeΓ).symm
  isFiniteTildeOn_of_finite_specModule F U hU
    ((AlgebraicGeometry.tilde_isFiniteType_iff (specModule F hU)).mp h)

/-- **(1) ⇒ (4) of [Stacks, Tag 01XZ].** A coherent module is, on every affine open `U`, the
sheaf associated with a finite `Γ(X, U)`-module. -/
theorem isFiniteTildeOn_of_isCoherent (F : X.Modules) [F.IsCoherent] (U : X.Opens)
    (hU : IsAffineOpen U) : IsFiniteTildeOn F U hU :=
  have ⟨h₁, h₂⟩ := isQuasicoherent_isFiniteType_of_isCoherent F
  have := h₁
  have := h₂
  isFiniteTildeOn_of_isQuasicoherent_of_isFiniteType F U hU

end Stacks.AlgebraicGeometry.CoherentTFAE
