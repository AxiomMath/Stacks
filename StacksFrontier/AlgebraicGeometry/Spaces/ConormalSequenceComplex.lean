module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceDerivationVanishing
import StacksCore.Tactic.StacksAttribute

/-!
# The conormal sequence of an immersion is a complex

Let `B` be a big fppf site over a scheme `S`, let `Z` be a closed subspace of an algebraic space
`X` over `B` with inclusion `i : Z ⟶ X`, and let `b : X ⟶ Bb` be the structure morphism.
Stacks 05ZA attaches to this datum the sequence
```
  𝒞_{Z/X} ⟶ i^*Ω_{X/Bb} ⟶ Ω_{Z/Bb} ⟶ 0
```
of sheaves of `𝒪_Z`-modules on the small étale site of `Z`, whose first arrow
`AlgebraicGeometry.Space.conormalSequenceFirstMap` is built in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceDifferentials.lean` and whose second arrow
is the comparison map `AlgebraicGeometry.Space.pullbackDifferentialsMap` of Stacks 04CX.

This file proves that the two arrows **compose to zero**, so that the sequence is a complex.

## The route

Everything happens across the adjunction `i^* ⊣ i_*` of Stacks 03LU, which is the adjunction both
arrows live in.  Write `𝓘 ⊆ 𝒪_X` for the defining ideal sheaf of `Z`, `D` for the adjoint form
`AlgebraicGeometry.Space.conormalSequenceIdealDifferential` of the first arrow — the morphism
`𝓘 ⟶ i_*i^*Ω_{X/Bb}` of `𝒪_X`-modules whose transpose the first arrow is — and `c` for the
second arrow.

1. The transpose of the second arrow is pinned on universal differentials by the characterizing
   property `AlgebraicGeometry.Space.IsSheafOfDifferentialsMap` of Stacks 04CX, which
   `AlgebraicGeometry.Space.isSheafOfDifferentialsMap_sheafOfDifferentialsMap` supplies: it
   carries `d_{X/Bb}(t)` to the value at `t` of the `Bb`-derivation `i_*d_{Z/Bb} ∘ i♯` of
   Stacks 04CX.  On a section of `𝓘` that value is zero, because `𝓘` is by definition the kernel
   of `i♯` (`AlgebraicGeometry.Space.mem_definingIdealAt_iff`) and that derivation kills whatever
   `i♯` kills (`AlgebraicGeometry.Space.pushforwardUniversalDerivation_d_eq_zero`).
2. `D` carries a section `a` of `𝓘` to `η(d_{X/Bb}(a))`, with `η` the unit of the adjunction:
   that is the definition of
   `AlgebraicGeometry.Space.conormalSequenceUnitDerivation` together with
   `PresheafOfModules.Derivation.postcomp_d_apply`.  Since the transpose of `c` is `η` followed
   by `i_*c` (`CategoryTheory.Adjunction.homEquiv_unit`), step 1 says exactly that
   `D ≫ i_*c` vanishes on every local section of `𝓘`.
3. A morphism out of `𝓘` vanishing on every local section is the transpose of the zero morphism,
   by `AlgebraicGeometry.Space.modulePullbackAdjunction_homEquiv_zero_val_app_apply`; and the
   transposition is natural in its right argument
   (`CategoryTheory.Adjunction.homEquiv_naturality_right_symm`), so the transpose of `D ≫ i_*c`
   is the composite of the two arrows.  Transposing back gives the conclusion.

## Main results

* `AlgebraicGeometry.Space.conormalSequenceUnitDerivation_d`: the `Bb`-derivation that induces
  the first arrow carries a local section of `𝒪_X` to its universal differential followed by the
  unit of `i^* ⊣ i_*`.
* `AlgebraicGeometry.Space.conormalSequenceIdealDifferential_comp_val_app_apply_eq_zero`: the
  adjoint form of the first arrow followed by the direct image of the second arrow vanishes on
  every local section of the defining ideal sheaf.
* `AlgebraicGeometry.Space.conormalSequenceIdealDifferential_comp_eq_homEquiv_zero`: that
  composite is the transpose of the zero morphism.
* `AlgebraicGeometry.Space.conormalSequenceIdealPullbackMap_comp_pullbackDifferentialsMap` and
  `AlgebraicGeometry.Space.conormalSequenceFirstMap_comp_pullbackDifferentialsMap`:
  **Stacks 05ZA**, the composite of the two arrows of the sequence is zero.  The two differ only
  in how the source is written, `i^*𝓘` and `𝒞_{Z/X}`.

## Implementation notes

**Why the three steps are separate named lemmas.**  The *What is not proved* section of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceDerivationVanishing.lean` records that
steps 2 and 3 can exceed the default heartbeat budget.  They do, when they are
stated in one go or applied by unification against a goal mentioning
`AlgebraicGeometry.Space.conormalSequenceUnitDerivation` or
`AlgebraicGeometry.Space.conormalSequenceIdealPullbackMap`: the unifier is then free to take the
expensive route, which is to reduce the transposition of the adjunction or the coefficient module
of a derivation to normal form.  Cutting the composite into the lemmas below, and delta-reducing
the two definitions *syntactically* with `unfold` before appealing to
`PresheafOfModules.Derivation.postcomp_d_apply` and to reflexivity, keeps every step inside the
budget.  This development raises no compiler option, and none is raised here.

**Where the arrows come from.**  Neither arrow is built in this file.  The first is
`AlgebraicGeometry.Space.conormalSequenceFirstMap`, with its adjoint form; the second is
`AlgebraicGeometry.Space.pullbackDifferentialsMap`, registered under Stacks 05ZA in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceSecondMap.lean`.  The import surface is
that of `ConormalSequenceDerivationVanishing.lean`, which already has both.

**What is still open for Stacks 05ZA.**  Exactness at the middle term; see the *What is not
proved* section of `ConormalSequenceDifferentials.lean`.  Exactness at the right term is proved,
in `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceDifferentialsEpi.lean`.  As everywhere
in this part of the development, the statements are for a closed subspace: the reduction of an
immersion to a closed immersion is absent, as `ConormalSequenceDifferentials.lean` records.

## References

* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA)
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX), the comparison map of a
  commutative square and the derivation it is built from.
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU), the adjunction
  `i^* ⊣ i_*`.
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB), the defining ideal sheaf
  of a closed subspace as the kernel of the structure map.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Complex

variable {X Bb : AlgebraicSpaces B S hS}

/-- The `Bb`-derivation `AlgebraicGeometry.Space.conormalSequenceUnitDerivation` that induces the
first arrow of Stacks 05ZA carries a local section `t` of `𝒪_X` to the universal differential
`d_{X/Bb}(t)` followed by the unit of the adjunction `i^* ⊣ i_*` of Stacks 03LU.

This is the defining equation of that derivation, an instance of
`PresheafOfModules.Derivation.postcomp_d_apply`.  The definition is delta-reduced before the
instance is applied, because at these coefficient modules the unifier does not find the step on
its own inside the default heartbeat budget. -/
theorem conormalSequenceUnitDerivation_d (Z : ClosedSubspaces B S hS X.1) (b : X ⟶ Bb)
    (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (t : ToType ((structureRingSheaf B S hS X).obj.obj U)) :
    (conormalSequenceUnitDerivation B S hS Z b).d t =
      (ModuleCat.Hom.hom
        (((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).unit.app
          (sheafOfDifferentials B S hS b)).val.app U))
        ((universalDerivation B S hS b).d t) := by
  unfold conormalSequenceUnitDerivation
  rfl

/-- **The non-formal step of the composite-is-zero clause of Stacks 05ZA.**  The adjoint form
`𝓘 ⟶ i_*i^*Ω_{X/Bb}` of the first arrow, followed by the direct image of the second arrow,
vanishes on every local section of the defining ideal sheaf of `Z`.

On a section `a` of `𝓘` the first arrow's adjoint form is `η(d_{X/Bb}(a))`, by
`AlgebraicGeometry.Space.conormalSequenceUnitDerivation_d`; and `η` followed by the direct image
of the second arrow is the transpose of the second arrow, by
`CategoryTheory.Adjunction.homEquiv_unit`.  That transpose carries `d_{X/Bb}(a)` to the value at
`a` of the `Bb`-derivation of Stacks 04CX, by
`AlgebraicGeometry.Space.isSheafOfDifferentialsMap_sheafOfDifferentialsMap`, and that value is
zero because `a` is killed by `i♯` — which is what membership of the defining ideal sheaf means,
by `AlgebraicGeometry.Space.mem_definingIdealAt_iff` — and that derivation kills whatever `i♯`
kills, by `AlgebraicGeometry.Space.pushforwardUniversalDerivation_d_eq_zero`. -/
theorem conormalSequenceIdealDifferential_comp_val_app_apply_eq_zero
    (Z : ClosedSubspaces B S hS X.1) (b : X ⟶ Bb) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : (definingIdealSheaf B S hS X Z).toSheafOfModules.val.obj U) :
    (ModuleCat.Hom.hom
      ((conormalSequenceIdealDifferential B S hS Z b ≫
        (modulePushforward B S hS (subspaceInclusion B S hS X Z)).map
          (pullbackDifferentialsMap B S hS (subspaceInclusion B S hS X Z) b)).val.app U)) x =
      0 := by
  have hvanish := (isSheafOfDifferentialsMap_sheafOfDifferentialsMap B S hS
      (subspaceInclusion B S hS X Z) b (subspaceInclusion B S hS X Z ≫ b) (𝟙 Bb)
      (by simp) U x.1).trans
    (pushforwardUniversalDerivation_d_eq_zero B S hS (subspaceInclusion B S hS X Z) b
      (subspaceInclusion B S hS X Z ≫ b) (𝟙 Bb) (by simp) U x.1
      ((mem_definingIdealAt_iff B S hS X Z U x.1).1 x.2))
  rw [Adjunction.homEquiv_unit] at hvanish
  exact (congrArg _ (conormalSequenceIdealDifferential_val_app_apply B S hS Z b U x)).trans
    ((congrArg _ (conormalSequenceUnitDerivation_d B S hS Z b U x.1)).trans hvanish)

/-- The adjoint form of the first arrow of Stacks 05ZA followed by the direct image of the second
arrow is the transpose of the zero morphism `i^*𝓘 ⟶ Ω_{Z/Bb}`.

Both morphisms `𝓘 ⟶ i_*Ω_{Z/Bb}` vanish on every local section: the left-hand one by
`AlgebraicGeometry.Space.modulePullbackAdjunction_homEquiv_zero_val_app_apply` and the right-hand
one by
`AlgebraicGeometry.Space.conormalSequenceIdealDifferential_comp_val_app_apply_eq_zero`. -/
theorem conormalSequenceIdealDifferential_comp_eq_homEquiv_zero
    (Z : ClosedSubspaces B S hS X.1) (b : X ⟶ Bb) :
    ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).homEquiv
        (definingIdealSheaf B S hS X Z).toSheafOfModules
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS X Z ≫ b)))
      (0 : (modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
            (definingIdealSheaf B S hS X Z).toSheafOfModules ⟶
          sheafOfDifferentials B S hS (subspaceInclusion B S hS X Z ≫ b)) =
      conormalSequenceIdealDifferential B S hS Z b ≫
        (modulePushforward B S hS (subspaceInclusion B S hS X Z)).map
          (pullbackDifferentialsMap B S hS (subspaceInclusion B S hS X Z) b) := by
  ext U x
  exact (modulePullbackAdjunction_homEquiv_zero_val_app_apply B S hS
      (subspaceInclusion B S hS X Z) (definingIdealSheaf B S hS X Z).toSheafOfModules
      (sheafOfDifferentials B S hS (subspaceInclusion B S hS X Z ≫ b)) U x).trans
    (conormalSequenceIdealDifferential_comp_val_app_apply_eq_zero B S hS Z b U x).symm

/-- The first arrow of Stacks 05ZA is the transpose of its adjoint form; this is its definition,
delta-reduced. -/
theorem conormalSequenceIdealPullbackMap_eq_homEquiv_symm
    (Z : ClosedSubspaces B S hS X.1) (b : X ⟶ Bb) :
    conormalSequenceIdealPullbackMap B S hS Z b =
      ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).homEquiv
        (definingIdealSheaf B S hS X Z).toSheafOfModules
        ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
          (sheafOfDifferentials B S hS b))).symm
      (conormalSequenceIdealDifferential B S hS Z b) := by
  simp only [conormalSequenceIdealPullbackMap, submoduleTranspose]

/-- **Stacks 05ZA, the composite of the two arrows is zero**, written out of `i^*𝓘`.

The transposition of `i^* ⊣ i_*` is a bijection natural in its right argument, so the composite
is the transpose of the adjoint form of the first arrow followed by the direct image of the
second, which is the transpose of zero by
`AlgebraicGeometry.Space.conormalSequenceIdealDifferential_comp_eq_homEquiv_zero`. -/
theorem conormalSequenceIdealPullbackMap_comp_pullbackDifferentialsMap
    (Z : ClosedSubspaces B S hS X.1) (b : X ⟶ Bb) :
    conormalSequenceIdealPullbackMap B S hS Z b ≫
        pullbackDifferentialsMap B S hS (subspaceInclusion B S hS X Z) b = 0 :=
  (congrArg (fun m ↦ m ≫ pullbackDifferentialsMap B S hS (subspaceInclusion B S hS X Z) b)
      (conormalSequenceIdealPullbackMap_eq_homEquiv_symm B S hS Z b)).trans
    ((Adjunction.homEquiv_naturality_right_symm
        (modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z))
        (conormalSequenceIdealDifferential B S hS Z b)
        (pullbackDifferentialsMap B S hS (subspaceInclusion B S hS X Z) b)).symm.trans
      ((congrArg ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).homEquiv
            (definingIdealSheaf B S hS X Z).toSheafOfModules
            (sheafOfDifferentials B S hS (subspaceInclusion B S hS X Z ≫ b))).symm
          (conormalSequenceIdealDifferential_comp_eq_homEquiv_zero B S hS Z b).symm).trans
        (Equiv.symm_apply_apply _ _)))

/-- **Stacks 05ZA, the composite of the two arrows is zero.**  For a closed subspace `Z` of an
algebraic space `X` over `Bb`, with inclusion `i : Z ⟶ X`, the sequence
```
  𝒞_{Z/X} ⟶ i^*Ω_{X/Bb} ⟶ Ω_{Z/Bb}
```
is a complex.

This is
`AlgebraicGeometry.Space.conormalSequenceIdealPullbackMap_comp_pullbackDifferentialsMap` with the
source of the first arrow read as the conormal module, which it is by
`AlgebraicGeometry.Space.conormalModule_eq`. -/
@[stacks 05ZA "the composite of the two arrows is zero, so the sequence \
`𝒞_{Z/X} ⟶ i^*Ω_{X/Bb} ⟶ Ω_{Z/Bb}` is a complex, for a closed subspace.  Unconditional"]
theorem conormalSequenceFirstMap_comp_pullbackDifferentialsMap
    (Z : ClosedSubspaces B S hS X.1) (b : X ⟶ Bb) :
    conormalSequenceFirstMap B S hS Z b ≫
        pullbackDifferentialsMap B S hS (subspaceInclusion B S hS X Z) b = 0 :=
  conormalSequenceIdealPullbackMap_comp_pullbackDifferentialsMap B S hS Z b

end Complex

end AlgebraicGeometry.Space

end
