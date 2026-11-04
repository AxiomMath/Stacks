module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsEtaleSourceComparisonMap
import StacksCore.Tactic.StacksAttribute

/-!
# The middle term of the conormal sequence commutes with étale base change

Let `B` be a big fppf site containing a scheme `S`, let `φ : U ⟶ X` be an étale morphism of
algebraic spaces over `S`, let `Z ⊆ X` be a closed subspace with inclusion
`i : Z ⟶ X` and let `b : X ⟶ Bb` be a structure morphism.  Write `Z_U = φ⁻¹(Z)` for the inverse
image closed subspace of `U`, with inclusion `i_U : Z_U ⟶ U` and projection `p : Z_U ⟶ Z`,
sitting in the commutative square `i_U ≫ φ = p ≫ i` of
`AlgebraicGeometry.Space.conormalEtaleRestrictionSquare`.

The sequence of Stacks 05ZA for `Z ⊆ X` over `Bb` is
```
  𝒞_{Z/X} ⟶ i^*Ω_{X/Bb} ⟶ Ω_{Z/Bb} ⟶ 0
```
Its left term under étale base change is the conormal-module clause of Stacks 04CO.  This file
identifies the inverse image along `p` of its middle term with the middle term of the sequence
for `Z_U ⊆ U` over `Bb`:

`p^*i^*Ω_{X/Bb} ≅ i_U^*Ω_{U/Bb}`.

The identification is the square comparison `p^*i^* ≅ i_U^*φ^*` of the proof of Stacks 04CP,
followed by the inverse image along `i_U` of the comparison map `c_φ : φ^*Ω_{X/Bb} ⟶ Ω_{U/Bb}`
of Stacks 04CX, which is invertible along the étale `φ` by Stacks 04CU.  As for the conormal
module of Stacks 04CN, `Z` is a closed subspace.

All names are in the namespace `AlgebraicGeometry.Space`.

## Main definitions

* `conormalSequenceMiddleEtaleRestrictionIso`: the identification `p^*i^*Ω_{X/Bb} ≅ i_U^*Ω_{U/Bb}`
  of the middle term of the sequence of Stacks 05ZA under étale base change of the ambient space.

## Main results

* `isIso_map_pullbackDifferentialsMap_of_isEtale`: the inverse image along any morphism of the
  comparison map along an étale `φ` is invertible.

## References

* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA), the conormal sequence.
* [Stacks Project, Tag 04CO](https://stacks.math.columbia.edu/tag/04CO), the conormal module
  under étale base change.
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU), the étale localization
  of the sheaf of differentials.
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX), the comparison map
  `c_φ`.
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP), the square comparison
  `p^*i^* ≅ i_U^*φ^*`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U X Bb : AlgebraicSpaces B S hS}

/-! ### The comparison map along an étale morphism, restricted to the inverse image -/

/-- **The inverse image along any morphism of the comparison map along an étale morphism is
invertible.**  For an étale `φ : U ⟶ X`, any `b : X ⟶ Bb` and any morphism `a` out of an
algebraic space into `U`, the inverse image along `a` of the comparison map
`c_φ : φ^*Ω_{X/Bb} ⟶ Ω_{U/Bb}` of Stacks 04CX is an isomorphism. -/
theorem isIso_map_pullbackDifferentialsMap_of_isEtale {W : AlgebraicSpaces B S hS} (a : W ⟶ U)
    (φ : U ⟶ X) (hφ : IsEtale B S hS φ.hom) (b : X ⟶ Bb) :
    IsIso ((modulePullback B S hS a).map (pullbackDifferentialsMap B S hS φ b)) := by
  have : IsIso (pullbackDifferentialsMap B S hS φ b) :=
    isIso_pullbackDifferentialsMap_of_isEtale B S hS φ hφ b
  infer_instance

/-! ### The middle term under étale base change -/

/-- **The middle term of the sequence of Stacks 05ZA commutes with étale base change.**  Let
`φ : U ⟶ X` be étale, let `Z ⊆ X` be a closed subspace with inverse image `Z_U = φ⁻¹(Z)` and
projection `p : Z_U ⟶ Z`, and let `b : X ⟶ Bb`.  Then the inverse image along `p` of the middle
term `i^*Ω_{X/Bb}` of the sequence of Stacks 05ZA for `Z ⊆ X` is the middle term
`i_U^*Ω_{U/Bb}` of that sequence for `Z_U ⊆ U`:

`p^*i^*Ω_{X/Bb} ≅ i_U^*Ω_{U/Bb}`.

The isomorphism is the square comparison `p^*i^* ≅ i_U^*φ^*` of
`AlgebraicGeometry.Space.conormalPullbackCompIso` followed by the inverse image along `i_U` of
the comparison map `c_φ` of Stacks 04CX, which is invertible along the étale `φ` by
Stacks 04CU. -/
noncomputable def conormalSequenceMiddleEtaleRestrictionIso (φ : U ⟶ X)
    (hφ : IsEtale B S hS φ.hom) (Z : ClosedSubspaces B S hS X.1) (b : X ⟶ Bb) :
    (modulePullback B S hS
          (ObjectProperty.homMk (Z.1.fromPreimage φ.hom) :
            (⟨(Z.1.preimage φ.hom).toFunctor,
                (isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2).1⟩ :
              AlgebraicSpaces B S hS) ⟶
            (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))).obj
        ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
          (sheafOfDifferentials B S hS b)) ≅
      (modulePullback B S hS (subspaceInclusion B S hS U (⟨Z.1.preimage φ.hom,
            isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2⟩ :
            ClosedSubspaces B S hS U.1))).obj
        (sheafOfDifferentials B S hS (φ ≫ b)) :=
  (conormalPullbackCompIso B S hS (⟨Z.1.preimage φ.hom,
          isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2⟩ :
          ClosedSubspaces B S hS U.1) Z φ
        (ObjectProperty.homMk (Z.1.fromPreimage φ.hom))
        (conormalEtaleRestrictionSquare B S hS φ Z)).app
      (sheafOfDifferentials B S hS b) ≪≫
    (modulePullback B S hS (subspaceInclusion B S hS U (⟨Z.1.preimage φ.hom,
        isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2⟩ :
        ClosedSubspaces B S hS U.1))).mapIso
      (sheafOfDifferentialsEtaleSourceLocalizationIso B S hS φ hφ b)

end AlgebraicGeometry.Space

end
