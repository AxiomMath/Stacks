module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyQuasiAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyRelativeAmpleMain

/-!
# Stacks 0GUU: the source of an affine or quasi-affine morphism has the resolution property

**Stacks 0GUU.** Let `f : X ⟶ Y` be an affine, or more generally a quasi-affine, morphism of
algebraic spaces over a scheme `S`, and assume `Y` is quasi-compact, quasi-separated and has the
resolution property.  Then `X` has the resolution property.

The source's proof is a reduction: by Stacks 0GUQ the structure sheaf `𝒪_X` is `f`-ample for such
an `f`, so the statement is the case `L = 𝒪_X` of Stacks 0GUT.  This file runs that reduction
against the proved form of Stacks 0GUT,
`AlgebraicGeometry.Space.hasResolutionProperty_source_of_isRelativelyAmple`.

## Main results

* `AlgebraicGeometry.Space.isInvertibleModule_unit`: the structure sheaf of an algebraic space,
  viewed as a module over itself, is invertible.
* `AlgebraicGeometry.Space.hasResolutionProperty_source_of_isQuasiAffineHom` and
  `AlgebraicGeometry.Space.hasResolutionProperty_source_of_isAffineHom`: **Stacks 0GUU**, in its
  quasi-affine and its affine case.

## Implementation notes

**Relation to the conditional reductions.**  The reductions of Stacks 0GUU to Stacks 0GUT in
`AlgebraicGeometry.Space.hasResolutionProperty_of_isQuasiAffineHom` and
`AlgebraicGeometry.Space.hasResolutionProperty_of_isQuasiAffineHom_small` assume the
*unparameterised* statement `AlgebraicGeometry.Space.HasResolutionPropertyOfRelativelyAmple`
(respectively `AlgebraicGeometry.Space.HasResolutionPropertyOfRelativelyAmpleSmall`), which
quantifies over a relatively ample `L` with no invertibility hypothesis and is therefore strictly
stronger than Stacks 0GUT.  The theorems below apply the proved Stacks 0GUT at `L = 𝒪_X`, whose
invertibility is `AlgebraicGeometry.Space.isInvertibleModule_unit`.

**Invertibility of the unit.**  `AlgebraicGeometry.Space.IsInvertibleModule X (𝒪_X)` is not found
by instance search — search for `Stacks.SheafOfModules.IsInvertible` on
`AlgebraicGeometry.Space.Modules` gets stuck on universe constraints — so
`Stacks.SheafOfModules.isInvertible_unit` is applied by hand.

**The module universe.**  As for Stacks 0GUT, everything is at
`AlgebraicGeometry.Space.Modules.{u, u}`: relative ampleness is tested on scheme base changes and
so is pinned there already, and the proof of Stacks 0GUT lives at that universe.

## References

* [Stacks Project, Tag 0GUU](https://stacks.math.columbia.edu/tag/0GUU)
* [Stacks Project, Tag 0GUT](https://stacks.math.columbia.edu/tag/0GUT)
* [Stacks Project, Tag 0GUQ](https://stacks.math.columbia.edu/tag/0GUQ)
* [Stacks Project, Tag 0GUS](https://stacks.math.columbia.edu/tag/0GUS)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 01CS for the structure sheaf.**  The structure sheaf of an algebraic space, viewed as
a module over itself, is an invertible `𝒪_X`-module: tensoring by it is the identity up to
isomorphism.  This is `Stacks.SheafOfModules.isInvertible_unit` at the structure sheaf of the
small étale site. -/
theorem isInvertibleModule_unit (X : AlgebraicSpaces B S hS) :
    IsInvertibleModule X (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) :=
  Stacks.SheafOfModules.isInvertible_unit _ _

/-- **Stacks 0GUU, the quasi-affine case.**  For `f : X ⟶ Y` a quasi-affine morphism of algebraic
spaces over `S` with `Y` quasi-compact, quasi-separated and carrying the resolution property, `X`
has the resolution property.

This is the source's reduction: by Stacks 0GUQ the structure sheaf of `X` is `f`-ample
(`AlgebraicGeometry.Space.isRelativelyAmple_unit_of_isQuasiAffineHom`) and invertible
(`AlgebraicGeometry.Space.isInvertibleModule_unit`), so this is Stacks 0GUT,
`AlgebraicGeometry.Space.hasResolutionProperty_source_of_isRelativelyAmple`, at `L = 𝒪_X`. -/
@[stacks 0GUU "the quasi-affine case; the affine case is \
`AlgebraicGeometry.Space.hasResolutionProperty_source_of_isAffineHom`, and the two together are \
the tag's \"affine or quasi-affine\""]
theorem hasResolutionProperty_source_of_isQuasiAffineHom (hZ : B.Contains (⊤_ Scheme.{u}))
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsQuasiAffineHom B S hS f.hom)
    (hYqc : IsQuasiCompactSpace B S hS Y.1) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
    (hYres : HasResolutionProperty.{u, u} B S hS Y.1 Y.2) :
    HasResolutionProperty.{u, u} B S hS X.1 X.2 :=
  hasResolutionProperty_source_of_isRelativelyAmple hZ f _ (isInvertibleModule_unit X)
    (isRelativelyAmple_unit_of_isQuasiAffineHom f hf) hYqc hYqs hYres

/-- **Stacks 0GUU, the affine case.**  For `f : X ⟶ Y` an affine morphism of algebraic spaces over
`S` with `Y` quasi-compact, quasi-separated and carrying the resolution property, `X` has the
resolution property.

An affine morphism of algebraic spaces is quasi-affine
(`AlgebraicGeometry.Space.isQuasiAffineHom_of_isAffineHom`), so this is the quasi-affine case. -/
@[stacks 0GUU "the affine case; the quasi-affine case is \
`AlgebraicGeometry.Space.hasResolutionProperty_source_of_isQuasiAffineHom`, and the two together \
are the tag's \"affine or quasi-affine\""]
theorem hasResolutionProperty_source_of_isAffineHom (hZ : B.Contains (⊤_ Scheme.{u}))
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom)
    (hYqc : IsQuasiCompactSpace B S hS Y.1) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
    (hYres : HasResolutionProperty.{u, u} B S hS Y.1 Y.2) :
    HasResolutionProperty.{u, u} B S hS X.1 X.2 :=
  hasResolutionProperty_source_of_isQuasiAffineHom hZ f (isQuasiAffineHom_of_isAffineHom hf)
    hYqc hYqs hYres

end AlgebraicGeometry.Space

end
