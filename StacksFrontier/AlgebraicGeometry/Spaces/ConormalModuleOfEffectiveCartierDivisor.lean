module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModule
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisor

/-!
# The conormal module of an effective Cartier divisor

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let
`D ⊆ X` be an effective Cartier divisor, that is, a closed subspace whose defining ideal sheaf
`𝓘_D ⊆ 𝒪_X` is an invertible `𝒪_X`-module (`AlgebraicGeometry.Space.IsEffectiveCartierDivisor`,
Stacks 083B, part 2).  **Stacks 0B4F** is the chain of two identifications

`𝒞_{D/X} = 𝓘_D|_D = 𝒪_X(D)^{⊗ -1}|_D`

of `𝒪_D`-modules, where `-|_D` is restriction to `D`, that is, the inverse image
`AlgebraicGeometry.Space.modulePullback` along the inclusion `i : D ⟶ X` (Stacks 03LU).

## Main definitions

* `AlgebraicGeometry.Space.conormalModuleIsoPullbackIdealSheaf`: **the first identification of
  Stacks 0B4F**, `𝒞_{Z/X} ≅ 𝓘_Z|_Z`, for an arbitrary closed subspace `Z ⊆ X`.
* `AlgebraicGeometry.Space.pullbackIdealSheafIsoPullbackNegativeDivisorSheaf`: **the second
  identification of Stacks 0B4F**, `𝓘_D|_D ≅ 𝒪_X(D)^{⊗ -1}|_D`, for an effective Cartier
  divisor `D ⊆ X`.
* `AlgebraicGeometry.Space.conormalModuleIsoPullbackNegativeDivisorSheaf`: the composite of the
  two, `𝒞_{D/X} ≅ 𝒪_X(D)^{⊗ -1}|_D`.

## Main results

* `AlgebraicGeometry.Space.conormalModuleIsoPullbackIdealSheaf_hom`: the first identification is
  the identity morphism.
* `AlgebraicGeometry.Space.pullbackIdealSheafIsoPullbackNegativeDivisorSheaf_eq_mapIso_symm`:
  the second identification is the inverse image of the canonical identification
  `𝒪_X(-D) ≅ 𝓘_D` of Stacks 0841, part 3.
* `AlgebraicGeometry.Space.conormalModuleIsoPullbackNegativeDivisorSheaf_eq`: the composite of
  the two identifications is the second one.

## Implementation notes

The conormal module `AlgebraicGeometry.Space.conormalModule` of a closed subspace is defined as
the inverse image of its defining ideal sheaf, so the first identification is `Iso.refl`.  It
holds for every closed subspace `Z ⊆ X`; the second needs `𝓘_D` to be invertible, since `𝒪_X(D)`
(`AlgebraicGeometry.Space.associatedInvertibleSheaf`) is only defined then.  The sheaf
`𝒪_X(D)^{⊗ -1}` is `AlgebraicGeometry.Space.negativeDivisorSheaf`, the tensor inverse of the
tensor inverse of `𝓘_D`, which is not `𝓘_D` on the nose.

## References

* [Stacks Project, Tag 0B4F](https://stacks.math.columbia.edu/tag/0B4F)
* [Stacks Project, Tag 0841](https://stacks.math.columbia.edu/tag/0841)
* [Stacks Project, Tag 083B](https://stacks.math.columbia.edu/tag/083B)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The first identification of Stacks 0B4F**, `𝒞_{Z/X} = 𝓘_Z|_Z`: the conormal module of a
closed subspace `Z` of an algebraic space `X` is the restriction to `Z` of the defining ideal
sheaf `𝓘_Z ⊆ 𝒪_X`, where restriction is the inverse image along the inclusion `i : Z ⟶ X`.
`Z` need not be an effective Cartier divisor. -/
@[stacks 0B4F "the conormal sheaf is the restriction of the ideal sheaf"]
noncomputable def conormalModuleIsoPullbackIdealSheaf (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) :
    conormalModule B S hS X Z ≅
      (modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
        (idealSheafOfModules B S hS X Z) :=
  Iso.refl _

/-- The first identification of Stacks 0B4F is the identity morphism: the two `𝒪_Z`-modules it
compares are the same module, not merely isomorphic ones. -/
@[simp]
theorem conormalModuleIsoPullbackIdealSheaf_hom (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) :
    (conormalModuleIsoPullbackIdealSheaf B S hS X Z).hom = 𝟙 _ :=
  rfl

/-- **The second identification of Stacks 0B4F**, `𝓘_D|_D = 𝒪_X(D)^{⊗ -1}|_D`: for an effective
Cartier divisor `D ⊆ X`, the restriction to `D` of the defining ideal sheaf `𝓘_D` agrees with the
restriction to `D` of `𝒪_X(-D) = 𝒪_X(D)^{⊗ -1}`.

It is the inverse image along the inclusion `i : D ⟶ X` of the canonical identification
`𝒪_X(-D) ≅ 𝓘_D` of Stacks 0841, part 3 (`AlgebraicGeometry.Space.negativeDivisorSheafIso`). -/
@[stacks 0B4F "the restriction of the ideal sheaf is the restriction of the inverse of O_X(D)"]
noncomputable def pullbackIdealSheafIsoPullbackNegativeDivisorSheaf
    (X : AlgebraicSpaces B S hS) (D : ClosedSubspaces B S hS X.1)
    (hD : IsEffectiveCartierDivisor B S hS X D) :
    (modulePullback B S hS (subspaceInclusion B S hS X D)).obj
        (idealSheafOfModules B S hS X D) ≅
      (modulePullback B S hS (subspaceInclusion B S hS X D)).obj
        (negativeDivisorSheaf B S hS X D hD) :=
  (modulePullback B S hS (subspaceInclusion B S hS X D)).mapIso
    (negativeDivisorSheafIso B S hS X D hD).symm

/-- The second identification of Stacks 0B4F **is** the inverse image along the inclusion of the
identification `𝒪_X(-D) ≅ 𝓘_D` of Stacks 0841, part 3, read in the direction `𝓘_D → 𝒪_X(-D)`. -/
theorem pullbackIdealSheafIsoPullbackNegativeDivisorSheaf_eq_mapIso_symm
    (X : AlgebraicSpaces B S hS) (D : ClosedSubspaces B S hS X.1)
    (hD : IsEffectiveCartierDivisor B S hS X D) :
    pullbackIdealSheafIsoPullbackNegativeDivisorSheaf B S hS X D hD =
      ((modulePullback B S hS (subspaceInclusion B S hS X D)).mapIso
        (negativeDivisorSheafIso B S hS X D hD)).symm :=
  Functor.mapIso_symm _ _

/-- **Stacks 0B4F, the chain read end to end**, `𝒞_{D/X} ≅ 𝒪_X(D)^{⊗ -1}|_D`: the conormal
module of an effective Cartier divisor `D ⊆ X` is the restriction to `D` of `𝒪_X(-D)`.  It is
the composite of `conormalModuleIsoPullbackIdealSheaf` and
`pullbackIdealSheafIsoPullbackNegativeDivisorSheaf`. -/
noncomputable def conormalModuleIsoPullbackNegativeDivisorSheaf
    (X : AlgebraicSpaces B S hS) (D : ClosedSubspaces B S hS X.1)
    (hD : IsEffectiveCartierDivisor B S hS X D) :
    conormalModule B S hS X D ≅
      (modulePullback B S hS (subspaceInclusion B S hS X D)).obj
        (negativeDivisorSheaf B S hS X D hD) :=
  conormalModuleIsoPullbackIdealSheaf B S hS X D ≪≫
    pullbackIdealSheafIsoPullbackNegativeDivisorSheaf B S hS X D hD

/-- The composite `𝒞_{D/X} ≅ 𝒪_X(D)^{⊗ -1}|_D` of the two identifications of Stacks 0B4F is the
second identification `pullbackIdealSheafIsoPullbackNegativeDivisorSheaf`. -/
theorem conormalModuleIsoPullbackNegativeDivisorSheaf_eq
    (X : AlgebraicSpaces B S hS) (D : ClosedSubspaces B S hS X.1)
    (hD : IsEffectiveCartierDivisor B S hS X D) :
    conormalModuleIsoPullbackNegativeDivisorSheaf B S hS X D hD =
      pullbackIdealSheafIsoPullbackNegativeDivisorSheaf B S hS X D hD :=
  Iso.refl_trans _

end AlgebraicGeometry.Space

end
