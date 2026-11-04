module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChangeEpi

/-!
# Inverse images of a surjective conormal module map

Let `Z'` be a closed subspace of an algebraic space `X'` and let `g : X ⟶ X'` be a morphism of
algebraic spaces over a scheme `S` contained in a big fppf site `B`.  For the fibre product
square whose upper closed subspace is the inverse image `g⁻¹(Z') ⊆ X`, the canonical map of
conormal modules `f^*𝒞_{Z'/X'} ⟶ 𝒞_{g⁻¹(Z')/X}` of Stacks 04CP is surjective; that is the
surjectivity clause of Stacks 04CQ, `AlgebraicGeometry.Space.epi_conormalMap`.

This file records that the surjectivity survives a further inverse image.  For a morphism
`a : W ⟶ g⁻¹(Z')` of algebraic spaces the map `a^*f^*𝒞_{Z'/X'} ⟶ a^*𝒞_{g⁻¹(Z')/X}` is again
surjective, because inverse image of `𝒪`-modules is a left adjoint
(`AlgebraicGeometry.Space.modulePullbackAdjunction`, the adjunction half of Stacks 03LU) and a
left adjoint preserves epimorphisms.

This is the step of Stacks 0CK7 which passes from surjectivity of `h^*𝒞_{Z/Z'} ⟶ 𝒞_{Y/Y'}`, for
a thickening `Y = Z ×_{Z'} Y'` obtained by base change, to surjectivity of its inverse image
`a^*h^*𝒞_{Z/Z'} ⟶ a^*𝒞_{Y/Y'}` along a morphism `a : X ⟶ Y`.

## Main results

* `AlgebraicGeometry.Space.preservesEpimorphisms_modulePullback`: inverse image of
  `𝒪`-modules along a morphism of algebraic spaces preserves epimorphisms.
* `AlgebraicGeometry.Space.epi_modulePullback_map_conormalMap`: the inverse image of an
  epimorphic conormal module map of a commutative square is an epimorphism.
* `AlgebraicGeometry.Space.epi_modulePullback_conormalMap`: the inverse image along an
  arbitrary morphism of the surjection of Stacks 04CQ is an epimorphism.

## Implementation notes

Epimorphy of a map of modules on the small étale site is surjectivity, by Stacks 01AH; that
identification is the one `AlgebraicGeometry.Space.epi_conormalMap` already uses, so the
statements here are phrased with `Epi` throughout and no local surjectivity appears.

That a left adjoint preserves epimorphisms is recorded as a named theorem rather than used
inline, because the adjunction has to be supplied explicitly: the inverse image functor carries
its universe and sheafification side conditions in its definition, and instance search does not
produce `CategoryTheory.Functor.PreservesEpimorphisms` for it.

The closed subspace `g⁻¹(Z')` enters as an algebraic space through the anonymous constructor
`⟨Z.1.toFunctor, Z.2.1⟩`, which is the spelling the conormal module development uses for the
space underlying a closed subspace; no abbreviation for it is introduced here.

## References

* [Stacks Project, Tag 0CK7](https://stacks.math.columbia.edu/tag/0CK7)
* [Stacks Project, Tag 04CQ](https://stacks.math.columbia.edu/tag/04CQ)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Inverse image of `𝒪`-modules preserves epimorphisms.**  Along any morphism of algebraic
spaces the functor `f^*` is a left adjoint, by the adjunction half of Stacks 03LU, and a left
adjoint preserves epimorphisms. -/
theorem preservesEpimorphisms_modulePullback {W V : AlgebraicSpaces B S hS} (a : W ⟶ V) :
    (modulePullback B S hS a).PreservesEpimorphisms :=
  Functor.preservesEpimorphisms_of_adjunction (modulePullbackAdjunction B S hS a)

section Square

variable {X X' : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
    (Z' : ClosedSubspaces B S hS X'.1) (g : X ⟶ X')
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))

/-- **An epimorphic conormal module map stays epimorphic under inverse image.**  For a
commutative square of algebraic spaces in which `Z` is a closed subspace of `X` and `Z'` a
closed subspace of `X'`, and a morphism `a : W ⟶ Z`, the inverse image along `a` of the
canonical map `f^*𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}` of Stacks 04CP is an epimorphism as soon as that map
is. -/
theorem epi_modulePullback_map_conormalMap
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z')
    {W : AlgebraicSpaces B S hS}
    (a : W ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
    (hep : Epi (conormalMap B S hS Z Z' g f hsq)) :
    Epi ((modulePullback B S hS a).map (conormalMap B S hS Z Z' g f hsq)) :=
  have := hep
  (preservesEpimorphisms_modulePullback B S hS a).preserves _

end Square

/-- **The inverse image of the surjection of Stacks 0CK7 is surjective.**  Let `Z'` be a closed
subspace of an algebraic space `X'`, let `g : X ⟶ X'` be a morphism of algebraic spaces, and let
`a : W ⟶ g⁻¹(Z')` be a morphism of algebraic spaces.  The inverse image along `a` of the
canonical map of conormal modules `f^*𝒞_{Z'/X'} ⟶ 𝒞_{g⁻¹(Z')/X}` of the fibre product square is
an epimorphism of `𝒪_W`-modules.

In the situation of Stacks 0CK7 the base is a thickening `Z ⊆ Z'` and `Y = Z ×_{Z'} Y'`, so the
map `h^*𝒞_{Z/Z'} ⟶ 𝒞_{Y/Y'}` is the conormal map of a fibre product square and is surjective by
the surjectivity clause of Stacks 04CQ; this is the passage from that surjectivity to
surjectivity of `a^*h^*𝒞_{Z/Z'} ⟶ a^*𝒞_{Y/Y'}` along `a : X ⟶ Y`, which the source performs in
order to see that the map `A : a^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` is determined by `a`. -/
@[stacks 0CK7 "surjectivity of the inverse image along `a` of the conormal surjection of a \
cartesian thickening"]
theorem epi_modulePullback_conormalMap {X X' : AlgebraicSpaces B S hS} (g : X ⟶ X')
    (Z' : ClosedSubspaces B S hS X'.1) {W : AlgebraicSpaces B S hS}
    (a : W ⟶ (⟨(preimageSubspace B S hS g Z').1.toFunctor,
      (preimageSubspace B S hS g Z').2.1⟩ : AlgebraicSpaces B S hS)) :
    Epi ((modulePullback B S hS a).map
      (conormalMap B S hS (preimageSubspace B S hS g Z') Z' g
        (preimageProjection B S hS g Z')
        (conormalEtaleRestrictionSquare B S hS g Z'))) :=
  epi_modulePullback_map_conormalMap B S hS (preimageSubspace B S hS g Z') Z' g
    (preimageProjection B S hS g Z') (conormalEtaleRestrictionSquare B S hS g Z') a
    (epi_conormalMap B S hS g Z')

end AlgebraicGeometry.Space

end
