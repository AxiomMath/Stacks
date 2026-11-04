module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyQuasiAffine

/-!
# Stacks 0GUU reduced to Stacks 0GUT at the module universe of the schemes

Stacks 0GUU asserts that the source of an affine or quasi-affine morphism `f : X ⟶ Y` of
algebraic spaces over a scheme `S` has the resolution property as soon as `Y` is quasi-compact,
quasi-separated and has the resolution property.  Its proof is a reduction: by Stacks 0GUQ the
structure sheaf `𝒪_X` is `f`-ample for such an `f`, so the statement is the case `L = 𝒪_X` of
Stacks 0GUT.

`AlgebraicGeometry.Space.HasResolutionProperty` keeps the universe of the module sections free,
and `StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyQuasiAffine` carries both
the statement of Stacks 0GUT and the reduction with that universe free.  Every tool this tree
has for *proving* Stacks 0GUT, however, lives at the module universe of the schemes:
`AlgebraicGeometry.Space.modulePushforward` and `AlgebraicGeometry.Space.modulePullback` are
defined only at `AlgebraicGeometry.Space.Modules.{u, u}`, and accordingly
`AlgebraicGeometry.Space.exists_finiteLocallyFree_modulePullback_hom_of_hasResolutionProperty`
consumes `AlgebraicGeometry.Space.HasResolutionProperty.{u, u}`.  This file therefore records
the statement of Stacks 0GUT and the reduction of Stacks 0GUU to it **at that pinned module
universe**, which is the form in which the eventual proof of Stacks 0GUT will arrive.

## Main definitions

* `AlgebraicGeometry.Space.HasResolutionPropertyOfRelativelyAmpleSmall` is the statement of
  Stacks 0GUT with the module universe pinned to the universe of the schemes: for every
  morphism of algebraic spaces over `S` carrying a relatively ample module onto a quasi-compact,
  quasi-separated target with the resolution property at
  `AlgebraicGeometry.Space.Modules.{u, u}`, the source has the resolution property at
  `AlgebraicGeometry.Space.Modules.{u, u}`.

## Main results

* `AlgebraicGeometry.Space.hasResolutionPropertyOfRelativelyAmpleSmall_iff`: that statement is
  exactly `AlgebraicGeometry.Space.HasResolutionPropertyOfRelativelyAmple.{u, u}`, the free
  universe of the general statement taken at the universe of the schemes.
* `AlgebraicGeometry.Space.hasResolutionProperty_of_isQuasiAffineHom_small` and
  `AlgebraicGeometry.Space.hasResolutionProperty_of_isAffineHom_small`: the reduction of the
  quasi-affine and of the affine case of Stacks 0GUU to Stacks 0GUT, at the pinned module
  universe.

## Implementation notes

**The hypotheses carried, and why each is an input rather than part of the conclusion.**

* `hGUT : AlgebraicGeometry.Space.HasResolutionPropertyOfRelativelyAmpleSmall B S hS hZ` is the
  statement of **Stacks 0GUT**, which this tree does not prove.  It is an input because the
  conclusion of Stacks 0GUU *is* the conclusion of Stacks 0GUT read through Stacks 0GUQ: with
  Stacks 0GUT unavailable there is nothing left of Stacks 0GUU to prove, and the content of
  each theorem below is only the application of Stacks 0GUQ that identifies the two.  It
  quantifies over an arbitrary relatively ample `L`, as Stacks 0GUT does; specializing it to
  `L = 𝒪_X` would, by Stacks 0GUQ, make it equivalent to the conclusion being proved and the
  implication empty.  **The theorems below therefore carry no `stacks` attribute.**
* `hZ : B.Contains (⊤_ Scheme.{u})` is the containment of the terminal scheme in the site that
  the absolute quasi-separatedness of Stacks 03BS, part (3),
  `AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated`, needs in order to be stated at all; see
  `StacksFrontier.AlgebraicGeometry.Spaces.Separated`.  It is an input because it is a property of
  the ambient site, not of `f`; it is used nowhere below except to state `hYqs` and to pass it
  to `hGUT`, so it is also the form in which `hGUT` asks for quasi-separatedness.

Nothing else is assumed: `hYqc`, `hYqs` and `hYres` are the three hypotheses Stacks 0GUU puts
on the target, and the conclusion is the full resolution property of `X`.

**No step of the reduction uses the free module universe.**  The reduction is the application
of `hGUT` to the structure sheaf of `X`, which Stacks 0GUQ exhibits as relatively ample.  Both
`AlgebraicGeometry.Space.IsRelativelyAmple` and
`AlgebraicGeometry.Space.isRelativelyAmple_unit_of_isQuasiAffineHom` already pin the ample
module to `AlgebraicGeometry.Space.Modules.{u, u}` — relative ampleness is tested on scheme
base changes, which live at the universe of the schemes — so the module universe of the
resolution property is a parameter the reduction only passes along.  Pinning it is consequently
a universe instantiation and not a change of argument:
`AlgebraicGeometry.Space.hasResolutionPropertyOfRelativelyAmpleSmall_iff` holds by `Iff.rfl`,
and the proofs below are, term for term, those of
`AlgebraicGeometry.Space.hasResolutionProperty_of_isQuasiAffineHom` and
`AlgebraicGeometry.Space.hasResolutionProperty_of_isAffineHom`.  What the pinning buys is that
these statements can be discharged by a proof of Stacks 0GUT built from the `Modules.{u, u}`
machinery above, whereas the free-universe statements of
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyQuasiAffine` ask for Stacks 0GUT
uniformly in a universe in which this tree's pushforward and pullback of modules do not exist.

## References

* [Stacks Project, Tag 0GUU](https://stacks.math.columbia.edu/tag/0GUU)
* [Stacks Project, Tag 0GUT](https://stacks.math.columbia.edu/tag/0GUT)
* [Stacks Project, Tag 0GUQ](https://stacks.math.columbia.edu/tag/0GUQ)
* [Stacks Project, Tag 0GUS](https://stacks.math.columbia.edu/tag/0GUS)
* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The statement of Stacks 0GUT at the module universe of the schemes**, for algebraic spaces
over the scheme `S`: a morphism of algebraic spaces carrying a relatively ample module whose
target is quasi-compact, quasi-separated and has the resolution property for
`AlgebraicGeometry.Space.Modules.{u, u}` has a source with the resolution property for
`AlgebraicGeometry.Space.Modules.{u, u}`.

This is `AlgebraicGeometry.Space.HasResolutionPropertyOfRelativelyAmple` with its free module
universe taken at the universe of the schemes, which is where this tree's
`AlgebraicGeometry.Space.modulePushforward` and `AlgebraicGeometry.Space.modulePullback`, and
hence any proof of Stacks 0GUT it can produce, live. -/
def HasResolutionPropertyOfRelativelyAmpleSmall (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u})) : Prop :=
  ∀ (X Y : AlgebraicSpaces B S hS) (f : X ⟶ Y) (L : Modules.{u, u} B S hS X.1 X.2),
    IsRelativelyAmple B S hS f L → IsQuasiCompactSpace B S hS Y.1 →
      IsAbsolutelyQuasiSeparated B S hS hZ Y.1 →
        HasResolutionProperty.{u, u} B S hS Y.1 Y.2 →
          HasResolutionProperty.{u, u} B S hS X.1 X.2

/-- The pinned form of Stacks 0GUT is the general form at the universe of the schemes: the free
module universe of `AlgebraicGeometry.Space.HasResolutionPropertyOfRelativelyAmple` is a
universe parameter, and pinning it changes nothing but that parameter. -/
theorem hasResolutionPropertyOfRelativelyAmpleSmall_iff (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u})) :
    HasResolutionPropertyOfRelativelyAmpleSmall B S hS hZ ↔
      HasResolutionPropertyOfRelativelyAmple.{u, u} B S hS hZ :=
  Iff.rfl

/-- **The reduction of the quasi-affine case of Stacks 0GUU to Stacks 0GUT, at the module
universe of the schemes.** For `f : X ⟶ Y` a quasi-affine morphism of algebraic spaces over `S`
with `Y` quasi-compact, quasi-separated and carrying the resolution property for
`AlgebraicGeometry.Space.Modules.{u, u}`, the statement of Stacks 0GUT at that module universe
implies the resolution property of `X` for `AlgebraicGeometry.Space.Modules.{u, u}`.

By Stacks 0GUQ the structure sheaf of `X` is `f`-ample, which is the case `L = 𝒪_X` of
Stacks 0GUT; the module universe is only passed along, relative ampleness being stated at the
universe of the schemes already.  **No `stacks` attribute is carried**: `hGUT` is the statement
of Stacks 0GUT, which this tree does not prove, so only the reduction is content here. -/
theorem hasResolutionProperty_of_isQuasiAffineHom_small (hZ : B.Contains (⊤_ Scheme.{u}))
    (hGUT : HasResolutionPropertyOfRelativelyAmpleSmall B S hS hZ)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsQuasiAffineHom B S hS f.hom)
    (hYqc : IsQuasiCompactSpace B S hS Y.1) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
    (hYres : HasResolutionProperty.{u, u} B S hS Y.1 Y.2) :
    HasResolutionProperty.{u, u} B S hS X.1 X.2 :=
  hGUT X Y f _ (isRelativelyAmple_unit_of_isQuasiAffineHom f hf) hYqc hYqs hYres

/-- **The reduction of the affine case of Stacks 0GUU to Stacks 0GUT, at the module universe of
the schemes.** For `f : X ⟶ Y` an affine morphism of algebraic spaces over `S` with `Y`
quasi-compact, quasi-separated and carrying the resolution property for
`AlgebraicGeometry.Space.Modules.{u, u}`, the statement of Stacks 0GUT at that module universe
implies the resolution property of `X` for `AlgebraicGeometry.Space.Modules.{u, u}`.

An affine morphism is quasi-affine, so this is the previous theorem.  **No `stacks` attribute is
carried**, for the same reason as there. -/
theorem hasResolutionProperty_of_isAffineHom_small (hZ : B.Contains (⊤_ Scheme.{u}))
    (hGUT : HasResolutionPropertyOfRelativelyAmpleSmall B S hS hZ)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom)
    (hYqc : IsQuasiCompactSpace B S hS Y.1) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
    (hYres : HasResolutionProperty.{u, u} B S hS Y.1 Y.2) :
    HasResolutionProperty.{u, u} B S hS X.1 X.2 :=
  hasResolutionProperty_of_isQuasiAffineHom_small hZ hGUT f
    (isQuasiAffineHom_of_isAffineHom hf) hYqc hYqs hYres

end AlgebraicGeometry.Space

end
