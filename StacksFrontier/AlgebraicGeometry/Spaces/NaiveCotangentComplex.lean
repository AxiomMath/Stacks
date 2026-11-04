module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangent

/-!
# The naive cotangent complex of a morphism of algebraic spaces

Let `S` be a scheme and let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`.  The naive
cotangent complex `NL_{X/Y} = NL_f` of `f` is the naive cotangent complex of Stacks 08U0 for the
morphism of ringed topoi `f_small` of Stacks 03G8 between the small étale sites of `X` and `Y`:
the two-term complex of sheaves of `𝒪_X`-modules

`I/I² ⟶ 𝒪_X ⊗_{f⁻¹𝒪_Y[𝒪_X]} Ω[f⁻¹𝒪_Y[𝒪_X] / f⁻¹𝒪_Y]`

in degrees `-1` and `0` attached to the inverse-image form `f⁻¹𝒪_Y ⟶ 𝒪_X` of the structure map
of `f_small`.

## Main definitions

* `AlgebraicGeometry.Space.naiveCotangentComplex` is the naive cotangent complex of a morphism
  of algebraic spaces.

## Implementation notes

`Stacks.SheafOfModules.naiveCotangentComplex` has a free universe parameter for the sections of
the sheaves of modules it produces, which only enters the complex through the maximum of it with
the universe of the objects of the site.  The small étale site of an algebraic space over
`S : Scheme.{u}` has objects in `Type (u + 1)`, so that maximum is `u + 1` for every choice at
or below `u + 1`, and the parameter is pinned at `u`.

## References

* [Stacks Project, Tag 0D0V](https://stacks.math.columbia.edu/tag/0D0V)
* [Stacks Project, Tag 08U0](https://stacks.math.columbia.edu/tag/08U0), the naive cotangent
  complex of a morphism of ringed topoi.
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the morphism of small
  étale ringed topoi.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 0D0V.** The naive cotangent complex `NL_{X/Y} = NL_f` of a morphism `f : X ⟶ Y` of
algebraic spaces: the naive cotangent complex of the inverse-image form `f⁻¹𝒪_Y ⟶ 𝒪_X` of the
structure map of the morphism of small étale ringed topoi of `f`. -/
@[stacks 0D0V]
noncomputable def naiveCotangentComplex (f : X ⟶ Y) :
    CochainComplex (_root_.SheafOfModules.{u + 1, u, u + 1, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u}
        (smallEtaleRingedTopos B S hS X).O)) ℤ :=
  Stacks.SheafOfModules.naiveCotangentComplex.{u, u + 1, u, u}
    (smallEtaleRingedTopos B S hS X).J
    ((inverseImageCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).obj
      (smallEtaleRingedTopos B S hS Y).O)
    (smallEtaleRingedTopos B S hS X).O
    (smallEtaleRingedToposHom B S hS f).fSharpInverseImage

end AlgebraicGeometry.Space
