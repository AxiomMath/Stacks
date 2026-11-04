module

public import StacksFrontier.AlgebraicGeometry.RingedSpace.NaiveCotangentComplex
public import Mathlib.AlgebraicGeometry.Scheme

/-!
# The naive cotangent complex of a morphism of schemes

For a morphism of schemes `f : X ⟶ Y` the naive cotangent complex `NL_f = NL_{X/Y}` is the
naive cotangent complex of the underlying morphism of ringed spaces, that is
`NL_{𝒪_X / f^{-1}𝒪_Y}`: the two-term complex of sheaves of `𝒪_X`-modules

`I/I² ⟶ Ω_{f^{-1}𝒪_Y[𝒪_X] / f^{-1}𝒪_Y} ⊗_{f^{-1}𝒪_Y[𝒪_X]} 𝒪_X`

in degrees `-1` and `0` attached to the canonical presentation of `𝒪_X` over `f^{-1}𝒪_Y`.

## Main definitions

* `AlgebraicGeometry.Scheme.naiveCotangentComplex` is `NL_{X/Y}`.

## Main results

* `AlgebraicGeometry.Scheme.naiveCotangentComplex_eq` records that it is the complex of
  Stacks 08TN of the underlying morphism of ringed spaces;
* `naiveCotangentComplex_X_negOne` and `naiveCotangentComplex_X_zero` identify its two terms
  as the conormal sheaf of the canonical presentation and the scalar extension to `𝒪_X` of the
  relative differentials of that presentation; `naiveCotangentComplex_isZero_X` records that
  the remaining terms vanish and `naiveCotangentComplex_d_negOne_zero` that the one nonzero
  differential is the conormal map.

## Implementation notes

The underlying morphism of ringed spaces of `f` is `f.toLRSHom.toShHom`, a morphism of
`AlgebraicGeometry.RingedSpace.{u, u}`, which is exactly the generality in which
`AlgebraicGeometry.RingedSpace.naiveCotangentComplex` is available: `Scheme.{u}.toRingedSpace`
lands at `RingedSpace.{u, u}` because a scheme's structure sheaf and underlying space lie in
one universe. So nothing is specialized in passing from ringed spaces to schemes.

The source's definition cites "the complex defined in Modules, Definition 17.31.6", whose
upstream label reads `modules-definition-cotangent-complex-morphism-ringed-topoi`. That label
is a misnomer: the definition it labels is about ringed **spaces**, and the Modules chapter has
no topoi in it. The sites-level complex lives in Modules on Sites under
[Stacks Project, Tag 08U0] and is a different (though quasi-isomorphic) object, reached by a
different route — it is what the algebraic-space-level
[Stacks Project, Tag 0D0V] goes through, since an algebraic space has no underlying ringed
space. A scheme does, so this definition is one level shorter.

## References

* [Stacks Project, Tag 0D0H](https://stacks.math.columbia.edu/tag/0D0H)
* [Stacks Project, Tag 08TN](https://stacks.math.columbia.edu/tag/08TN), the naive cotangent
  complex of a morphism of ringed spaces.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open Stacks.Sheaves.RingedSpaceDifferentials (inverseImageSheaf inverseImageStructureMap)

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Stacks 0D0H.** The naive cotangent complex `NL_f = NL_{X/Y}` of a morphism of schemes
`f : X ⟶ Y`: the naive cotangent complex of Stacks 08TN of the underlying morphism of ringed
spaces of `f`, that is, `NL_{𝒪_X / f^{-1}𝒪_Y}`. -/
@[stacks 0D0H]
noncomputable def naiveCotangentComplex :
    CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology X.toRingedSpace.carrier) X.toRingedSpace.sheaf)) ℤ :=
  RingedSpace.naiveCotangentComplex f.toLRSHom.toShHom

/-- `NL_{X/Y}` of a morphism of schemes is `NL` of its underlying morphism of ringed spaces. -/
theorem naiveCotangentComplex_eq :
    naiveCotangentComplex f = RingedSpace.naiveCotangentComplex f.toLRSHom.toShHom :=
  rfl

/-- The conormal sheaf of the canonical presentation of `𝒪_X` over `f^{-1}𝒪_Y` is the degree
`-1` term of `NL_{X/Y}`. -/
@[simp] theorem naiveCotangentComplex_X_negOne :
    (naiveCotangentComplex f).X (-1) =
      (Stacks.SheafOfModules.canonicalConormalSequence.{u, u, u, u}
        (Opens.grothendieckTopology X.toRingedSpace.carrier)
        (inverseImageSheaf f.toLRSHom.toShHom) X.toRingedSpace.sheaf
        (inverseImageStructureMap f.toLRSHom.toShHom)).X₁ :=
  RingedSpace.naiveCotangentComplex_X_negOne f.toLRSHom.toShHom

/-- The scalar extension to `𝒪_X` of the relative differentials of the canonical presentation is
the degree `0` term of `NL_{X/Y}`. -/
@[simp] theorem naiveCotangentComplex_X_zero :
    (naiveCotangentComplex f).X 0 =
      (Stacks.SheafOfModules.canonicalConormalSequence.{u, u, u, u}
        (Opens.grothendieckTopology X.toRingedSpace.carrier)
        (inverseImageSheaf f.toLRSHom.toShHom) X.toRingedSpace.sheaf
        (inverseImageStructureMap f.toLRSHom.toShHom)).X₂ :=
  RingedSpace.naiveCotangentComplex_X_zero f.toLRSHom.toShHom

/-- `NL_{X/Y}` has no terms outside degrees `-1` and `0`. -/
theorem naiveCotangentComplex_isZero_X (i : ℤ) (hneg : i ≠ -1) (hzero : i ≠ 0) :
    Limits.IsZero ((naiveCotangentComplex f).X i) :=
  RingedSpace.naiveCotangentComplex_isZero_X f.toLRSHom.toShHom i hneg hzero

/-- The only nonzero differential of `NL_{X/Y}` is the conormal map. -/
theorem naiveCotangentComplex_d_negOne_zero :
    (naiveCotangentComplex f).d (-1) 0 =
      eqToHom (naiveCotangentComplex_X_negOne f) ≫
        (Stacks.SheafOfModules.canonicalConormalSequence.{u, u, u, u}
          (Opens.grothendieckTopology X.toRingedSpace.carrier)
          (inverseImageSheaf f.toLRSHom.toShHom) X.toRingedSpace.sheaf
          (inverseImageStructureMap f.toLRSHom.toShHom)).f ≫
        eqToHom (naiveCotangentComplex_X_zero f).symm :=
  RingedSpace.naiveCotangentComplex_d_negOne_zero f.toLRSHom.toShHom

end AlgebraicGeometry.Scheme

end
