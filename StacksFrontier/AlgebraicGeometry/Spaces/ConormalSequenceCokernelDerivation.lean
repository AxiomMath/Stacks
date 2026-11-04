module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceInclusionParameter
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceDerivationVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivationsIntoDirectImage

/-!
# The derivation attached to a map out of the middle term of the conormal sequence

Let `Z ⊆ X` be a closed subspace of an algebraic space over `B`, let `i` be a morphism with
target `X` whose structure map kills the defining ideal of `Z`, and let `b : X ⟶ B` be the
structure morphism.  Stacks 05ZA attaches to this datum the sequence
```
  𝒞_{Z/X} ⟶ i^*Ω_{X/B} ⟶ Ω_{Z/B} ⟶ 0
```
whose first arrow is `AlgebraicGeometry.Space.conormalSequenceFirstMapAt`.

This file transposes a morphism `θ : i^*Ω_{X/B} ⟶ M` out of the middle term into derivation
language, which is what the cokernel property of the second arrow is proved in.

## Main results

* `AlgebraicGeometry.Space.derivationDirectImageEquiv_d`: the `B`-derivation of `𝒪_X` with values
  in `i_*M` that Equation (0619) attaches to `θ` carries a local section `a` of `𝒪_X` to the
  direct image of `θ` applied to `d_{X/B}(a)` followed by the unit of `i^* ⊣ i_*`, that is, to
  `i_*θ` applied to `AlgebraicGeometry.Space.pullbackUnitDerivation`.
* `AlgebraicGeometry.Space.derivationDirectImageEquiv_d_eq_zero`: **if `θ` annihilates the first
  arrow then that derivation annihilates the defining ideal sheaf of `Z`.**  This is the
  hypothesis the derivation descent along the structure map of `i` consumes.

## Implementation notes

Both statements leave `i` a variable and are phrased through the named constants
`AlgebraicGeometry.Space.pullbackUnitDerivation` and
`AlgebraicGeometry.Space.submoduleTranspose`, for the reason the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceDifferentials.lean` record: at a concrete
inclusion of a closed subspace the coefficient module of the derivation has to be compared with
the one the adjunction writes through the composite functor `i^* ⋙ i_*`, and that comparison
does not fit in the default heartbeat budget.  Through the constants the comparison is of two
applications of one constant and `rfl` decides it.

The vanishing is read off the first arrow by transposing `hθ` across `i^* ⊣ i_*`:
`CategoryTheory.Adjunction.homEquiv_naturality_right` turns `first ≫ θ = 0` into
`AlgebraicGeometry.Space.conormalSequenceIdealDifferentialAt ≫ i_*θ = 0`, the left-hand side of
which is computed on sections by
`AlgebraicGeometry.Space.conormalSequenceIdealDifferentialAt_val_app_apply` and the right-hand
side by `AlgebraicGeometry.Space.modulePullbackAdjunction_homEquiv_zero_val_app_apply`.

Nothing here is a clause of Stacks 05ZA: these are two computations with the adjunction of
Stacks 03LU and Equation (0619), and no `@[stacks]` attribute is claimed.

## References

* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA), the conormal sequence,
  for whose exactness at the middle term this is an input.
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619), the bijection between
  maps out of a pulled back sheaf of differentials and derivations into a direct image.
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU), the adjunction
  `i^* ⊣ i_*`.
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB), the defining ideal sheaf
  of a closed subspace.
-/

@[expose] public section

open CategoryTheory Opposite
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Bb W : AlgebraicSpaces B S hS}

/-- **The derivation of Equation (0619) on a local section.**  The `B`-derivation of `𝒪_X` with
values in `i_*M` attached by `AlgebraicGeometry.Space.derivationDirectImageEquiv` to a morphism
`θ : i^*Ω_{X/B} ⟶ M` carries a local section `a` of `𝒪_X` to `i_*θ` applied to
`AlgebraicGeometry.Space.pullbackUnitDerivation` of `a`, that is, to `d_{X/B}(a)` pushed through
the unit of `i^* ⊣ i_*` and then through the direct image of `θ`.

The transpose of `θ` is the unit followed by `i_*θ`
(`CategoryTheory.Adjunction.homEquiv_unit`), and both derivations are the universal derivation
postcomposed with a morphism of modules, so this is
`PresheafOfModules.Derivation.postcomp_d_apply` twice. -/
theorem derivationDirectImageEquiv_d (i : W ⟶ X) (b : X ⟶ Bb)
    (M : Modules.{u, u} B S hS W.1 W.2)
    (θ : (modulePullback B S hS i).obj (sheafOfDifferentials B S hS b) ⟶ M)
    (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (a : ToType ((structureRingSheaf B S hS X).obj.obj U)) :
    (derivationDirectImageEquiv B S hS i b M θ).d a =
      (((modulePushforward B S hS i).map θ).val.app U).hom
        ((pullbackUnitDerivation B S hS i b).d a) := by
  have hu := Adjunction.homEquiv_unit (modulePullbackAdjunction B S hS i)
    (sheafOfDifferentials B S hS b) M θ
  refine Eq.trans ?_ (congrArg (fun m ↦ (((modulePushforward B S hS i).map θ).val.app U).hom m)
    (PresheafOfModules.Derivation.postcomp_d_apply (universalDerivation B S hS b)
      ((modulePullbackAdjunction B S hS i).unit.app (sheafOfDifferentials B S hS b)).val a).symm)
  refine Eq.trans (PresheafOfModules.Derivation.postcomp_d_apply (universalDerivation B S hS b)
    (((modulePullbackAdjunction B S hS i).homEquiv _ _) θ).val a) ?_
  exact congrArg (fun m ↦ (ModuleCat.Hom.hom ((SheafOfModules.Hom.val m).app U))
    ((universalDerivation B S hS b).d a)) hu

/-- **The derivation of a morphism annihilating the first arrow annihilates the defining
ideal.**  If `θ : i^*Ω_{X/B} ⟶ M` is annihilated by the first arrow
`AlgebraicGeometry.Space.conormalSequenceFirstMapAt` of the conormal sequence of `Z`, then the
`B`-derivation of `𝒪_X` with values in `i_*M` that Equation (0619) attaches to `θ` kills every
local section of the defining ideal sheaf of `Z`.

This is the hypothesis consumed by the descent of derivations along the structure map of `i`,
whose kernel is that ideal sheaf. -/
theorem derivationDirectImageEquiv_d_eq_zero (Z : ClosedSubspaces B S hS X.1) (b : X ⟶ Bb)
    (i : W ⟶ X) (hi : StructureSharpKillsDefiningIdeal B S hS Z i)
    (M : Modules.{u, u} B S hS W.1 W.2)
    (θ : (modulePullback B S hS i).obj (sheafOfDifferentials B S hS b) ⟶ M)
    (hθ : conormalSequenceFirstMapAt B S hS Z b i hi ≫ θ = 0)
    (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : (definingIdealSheaf B S hS X Z).toSheafOfModules.val.obj U) :
    (derivationDirectImageEquiv B S hS i b M θ).d x.1 = 0 := by
  -- the first arrow is the transpose of its adjoint form, by its definition
  have hfirst : conormalSequenceFirstMapAt B S hS Z b i hi =
      submoduleTranspose B S hS i (definingIdealSheaf B S hS X Z)
        ((modulePullback B S hS i).obj (sheafOfDifferentials B S hS b))
        (conormalSequenceIdealDifferentialAt B S hS Z b i hi) :=
    rfl
  have htr : ((modulePullbackAdjunction B S hS i).homEquiv
        (definingIdealSheaf B S hS X Z).toSheafOfModules
        ((modulePullback B S hS i).obj (sheafOfDifferentials B S hS b)))
      (conormalSequenceFirstMapAt B S hS Z b i hi) =
      conormalSequenceIdealDifferentialAt B S hS Z b i hi :=
    (congrArg (fun m ↦ ((modulePullbackAdjunction B S hS i).homEquiv
          (definingIdealSheaf B S hS X Z).toSheafOfModules
          ((modulePullback B S hS i).obj (sheafOfDifferentials B S hS b))) m) hfirst).trans
      (homEquiv_submoduleTranspose B S hS i (definingIdealSheaf B S hS X Z)
        ((modulePullback B S hS i).obj (sheafOfDifferentials B S hS b))
        (conormalSequenceIdealDifferentialAt B S hS Z b i hi))
  -- the transposed form of `hθ`
  have hnat : ((modulePullbackAdjunction B S hS i).homEquiv
        (definingIdealSheaf B S hS X Z).toSheafOfModules M)
      (conormalSequenceFirstMapAt B S hS Z b i hi ≫ θ) =
      conormalSequenceIdealDifferentialAt B S hS Z b i hi ≫
        (modulePushforward B S hS i).map θ :=
    (Adjunction.homEquiv_naturality_right (modulePullbackAdjunction B S hS i)
        (conormalSequenceFirstMapAt B S hS Z b i hi) θ).trans
      (congrArg (fun m ↦ m ≫ (modulePushforward B S hS i).map θ) htr)
  have hzero : ((modulePullbackAdjunction B S hS i).homEquiv
        (definingIdealSheaf B S hS X Z).toSheafOfModules M)
      (conormalSequenceFirstMapAt B S hS Z b i hi ≫ θ) =
      ((modulePullbackAdjunction B S hS i).homEquiv
        (definingIdealSheaf B S hS X Z).toSheafOfModules M) 0 :=
    congrArg _ hθ
  -- read both sides on the section `x` of the defining ideal sheaf
  have hsec : (((conormalSequenceIdealDifferentialAt B S hS Z b i hi ≫
      (modulePushforward B S hS i).map θ).val.app U).hom x) = 0 :=
    (congrArg (fun m ↦ (ModuleCat.Hom.hom ((SheafOfModules.Hom.val m).app U)) x)
      (hnat.symm.trans hzero)).trans
      (modulePullbackAdjunction_homEquiv_zero_val_app_apply B S hS i
        (definingIdealSheaf B S hS X Z).toSheafOfModules M U x)
  refine (derivationDirectImageEquiv_d B S hS i b M θ U x.1).trans (Eq.trans ?_ hsec)
  exact congrArg (fun m ↦ (((modulePushforward B S hS i).map θ).val.app U).hom m)
    (conormalSequenceIdealDifferentialAt_val_app_apply B S hS Z b i hi U x).symm

/-- `AlgebraicGeometry.Space.derivationDirectImageEquiv_d_eq_zero` read at a local section of the
structure sheaf together with a proof that it lies in the defining ideal, which is the form the
derivation descent along the structure map of `i` consumes. -/
theorem derivationDirectImageEquiv_d_eq_zero_of_mem (Z : ClosedSubspaces B S hS X.1) (b : X ⟶ Bb)
    (i : W ⟶ X) (hi : StructureSharpKillsDefiningIdeal B S hS Z i)
    (M : Modules.{u, u} B S hS W.1 W.2)
    (θ : (modulePullback B S hS i).obj (sheafOfDifferentials B S hS b) ⟶ M)
    (hθ : conormalSequenceFirstMapAt B S hS Z b i hi ≫ θ = 0)
    (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (a : ToType ((structureRingSheaf B S hS X).obj.obj U))
    (ha : a ∈ definingIdealAt B S hS X Z U) :
    (derivationDirectImageEquiv B S hS i b M θ).d a = 0 :=
  derivationDirectImageEquiv_d_eq_zero B S hS Z b i hi M θ hθ U ⟨a, ha⟩

end AlgebraicGeometry.Space

end
