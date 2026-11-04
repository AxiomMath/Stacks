module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceCompositeZero
import StacksCore.Tactic.StacksAttribute

/-!
# The first arrow of the conormal sequence, with the inclusion as a parameter

Stacks 05ZA attaches to a closed subspace `Z ⊆ X` of an algebraic space, with inclusion
`i : Z ⟶ X` and structure morphism `b : X ⟶ B`, the sequence
```
  𝒞_{Z/X} ⟶ i^*Ω_{X/B} ⟶ Ω_{Z/B} ⟶ 0
```
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceDifferentials.lean` builds its first arrow,
and `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceCompositeZero.lean` proves the
composite of the two arrows is zero, both with `i` taken to be
`AlgebraicGeometry.Space.subspaceInclusion` of the bundled closed subspace.

**This file states the same arrow and the same clause with `i` an explicit parameter.**  The
mathematical content is unchanged and nothing here is new mathematics; what changes is that a
consumer which already has the inclusion in hand under some other name instantiates these
declarations at that name, instead of at `subspaceInclusion` followed by a conversion.

## Why the parameter is needed

`AlgebraicGeometry.Space.universalThickeningInclusion` of a universal first-order thickening is
*by definition* `AlgebraicGeometry.Space.subspaceInclusion` of
`AlgebraicGeometry.Space.thickeningClosedSubspace`, so the specialized statements do apply to it
in principle.  In practice they do not: deciding the two spellings equal is `rfl` and cheap at
the bare arrow, but underneath a composition the conversion has to be settled inside
`AlgebraicGeometry.Space.sheafOfDifferentials` of `i ≫ b`, and that exceeds the heartbeat budget
— it fails for `exact`, for `show`, for `Eq.trans … rfl` and for `convert … using 2`,
the last of these in the kernel rather than the elaborator.  Instantiating the general
`AlgebraicGeometry.Space.submoduleTranspose_comp_pullbackDifferentialsMap_eq_zero'` at the other
spelling fares no better: it elaborates and then times out in the kernel on the two `rfl`
arguments it is handed, because those `rfl`s carry the conversion in their types.

The declarations below are shaped so that those `rfl` arguments **do not arise at all**: the
derivation and the transpose are taken at `i` itself, so each `rfl` passed to
`submoduleTranspose_comp_pullbackDifferentialsMap_eq_zero'` is syntactic.  The one conversion
that remains for a consumer is in `hi` below, whose statement is an equation between sections
over a single chart; that is shallow enough to decide inside the budget.

## What `hi` is

Nothing here assumes `i` is the inclusion of `Z`.  What is assumed, as `hi`, is the one property
of the inclusion the argument uses: that `i♯` kills the defining ideal of `Z`, which for the
inclusion itself is `AlgebraicGeometry.Space.mem_definingIdealAt_iff`.  Stating it this way is
what keeps `i` free.

At the canonical inclusion `hi` is discharged by
`AlgebraicGeometry.Space.structureSharpKillsDefiningIdeal_subspaceInclusion` below, and at the
inclusion of a universal first-order thickening by
`AlgebraicGeometry.Space.thickeningStructureSharpKillsDefiningIdeal`.
-/

@[expose] public section

open CategoryTheory Opposite
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section InclusionParameter

variable {X Bb W : AlgebraicSpaces B S hS}

/-- The structure map of `i` kills the defining ideal of the closed subspace `Z`, chart by
chart.  This is the only property of the inclusion of `Z` that the first arrow of Stacks 05ZA
and the vanishing of the composite actually use; for the inclusion itself it is
`AlgebraicGeometry.Space.mem_definingIdealAt_iff`, which is
`AlgebraicGeometry.Space.structureSharpKillsDefiningIdeal_subspaceInclusion` below. -/
abbrev StructureSharpKillsDefiningIdeal (Z : ClosedSubspaces B S hS X.1) (i : W ⟶ X) : Prop :=
  ∀ (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (a : ToType ((structureRingSheaf B S hS X).obj.obj U)),
    a ∈ definingIdealAt B S hS X Z U →
      ((structureSharp B S hS i).hom.app U).hom a = 0

/-- **The inclusion of a closed subspace satisfies
`AlgebraicGeometry.Space.StructureSharpKillsDefiningIdeal`**: its structure map kills the
defining ideal sheaf of `Z`, by `AlgebraicGeometry.Space.mem_definingIdealAt_iff`.

This is the *kills* half of that bi-implication; the *kernel* half is
`AlgebraicGeometry.Space.structureSharpKernelLeDefiningIdeal_subspaceInclusion`.  Together the
two discharge both stand-in hypotheses of
`AlgebraicGeometry.Space.conormalSequenceAt_exact` at the canonical inclusion, which is what
`AlgebraicGeometry.Space.conormalSequence_exact` does. -/
theorem structureSharpKillsDefiningIdeal_subspaceInclusion (Z : ClosedSubspaces B S hS X.1) :
    StructureSharpKillsDefiningIdeal B S hS Z (subspaceInclusion B S hS X Z) :=
  fun U a ha ↦ (mem_definingIdealAt_iff B S hS X Z U a).1 ha

/-- **Stacks 04CJ, part (3), with the inclusion as a parameter.**  A section of the defining
ideal sheaf of `Z` annihilates every section of a direct image along any morphism `i` whose
structure map kills that ideal.

This is `AlgebraicGeometry.Space.definingIdealAt_smul_modulePushforward_eq_zero` with `i` free:
that statement's proof uses the inclusion only through
`AlgebraicGeometry.Space.mem_definingIdealAt_iff`, which is exactly what `hi` supplies here. -/
theorem smul_modulePushforward_eq_zero_of_structureSharp
    (Z : ClosedSubspaces B S hS X.1) (i : W ⟶ X)
    (hi : StructureSharpKillsDefiningIdeal B S hS Z i)
    (G : Modules.{u, u} B S hS W.1 W.2) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (a : ToType ((structureRingSheaf B S hS X).obj.obj U))
    (ha : a ∈ definingIdealAt B S hS X Z U)
    (m : ((modulePushforward B S hS i).obj G).val.obj U) :
    letI : Module ((structureRingSheaf B S hS X).obj.obj U)
        (((modulePushforward B S hS i).obj G).val.obj U) :=
      (((modulePushforward B S hS i).obj G).val.obj U).isModule
    a • m = 0 :=
  Stacks.Sheaves.PushforwardEssentialImage.smul_restrictScalars_eq_zero
    (structureSharp B S hS i) ((moduleDirectImage B S hS i).obj G) U a (hi U a ha) m

/-- **The adjoint form of the first arrow of Stacks 05ZA, with the inclusion as a parameter**:
the morphism `𝓘 ⟶ i_*i^*Ω_{X/B}` restricting the derivation `d_{X/B}` followed by the unit of
`i^* ⊣ i_*` to the defining ideal sheaf of `Z`.

At `i := subspaceInclusion B S hS X Z` this is
`AlgebraicGeometry.Space.conormalSequenceIdealDifferential`; the derivation is taken at `i`
itself, which is what keeps the `rfl` arguments of the vanishing proof syntactic. -/
noncomputable def conormalSequenceIdealDifferentialAt
    (Z : ClosedSubspaces B S hS X.1) (b : X ⟶ Bb) (i : W ⟶ X)
    (hi : StructureSharpKillsDefiningIdeal B S hS Z i) :
    (definingIdealSheaf B S hS X Z).toSheafOfModules ⟶
      (modulePushforward B S hS i).obj
        ((modulePullback B S hS i).obj (sheafOfDifferentials B S hS b)) :=
  conormalSequenceIdealHom B S hS Z _ (pullbackUnitDerivation B S hS i b)
    fun U a ha m ↦ smul_modulePushforward_eq_zero_of_structureSharp B S hS Z i hi _ U a ha m

/-- **Stacks 05ZA, "the first arrow is induced by `d_{X/B}`", with the inclusion as a
parameter.**  The adjoint form of the first arrow carries a local section `a` of the defining
ideal sheaf to `D(a)`, where `D` is `d_{X/B}` followed by the unit of `i^* ⊣ i_*`. -/
theorem conormalSequenceIdealDifferentialAt_val_app_apply
    (Z : ClosedSubspaces B S hS X.1) (b : X ⟶ Bb) (i : W ⟶ X)
    (hi : StructureSharpKillsDefiningIdeal B S hS Z i)
    (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : (definingIdealSheaf B S hS X Z).toSheafOfModules.val.obj U) :
    ((conormalSequenceIdealDifferentialAt B S hS Z b i hi).val.app U).hom x =
      (pullbackUnitDerivation B S hS i b).d x.1 :=
  conormalSequenceIdealHom_val_app_apply B S hS Z _ (pullbackUnitDerivation B S hS i b) _ U x

/-- **The first arrow of Stacks 05ZA, with the inclusion as a parameter**, written out of
`i^*𝓘`: the transpose across `i^* ⊣ i_*` of
`AlgebraicGeometry.Space.conormalSequenceIdealDifferentialAt`.

At `i := subspaceInclusion B S hS X Z` this is
`AlgebraicGeometry.Space.conormalSequenceIdealPullbackMap`, and so also
`AlgebraicGeometry.Space.conormalSequenceFirstMap`, whose source `i^*𝓘` is the conormal module
`𝒞_{Z/X}` of Stacks 04CN by `AlgebraicGeometry.Space.conormalModule_eq`. -/
noncomputable def conormalSequenceFirstMapAt
    (Z : ClosedSubspaces B S hS X.1) (b : X ⟶ Bb) (i : W ⟶ X)
    (hi : StructureSharpKillsDefiningIdeal B S hS Z i) :
    (modulePullback B S hS i).obj (definingIdealSheaf B S hS X Z).toSheafOfModules ⟶
      (modulePullback B S hS i).obj (sheafOfDifferentials B S hS b) :=
  submoduleTranspose B S hS i (definingIdealSheaf B S hS X Z)
    ((modulePullback B S hS i).obj (sheafOfDifferentials B S hS b))
    (conormalSequenceIdealDifferentialAt B S hS Z b i hi)

/-- **Stacks 05ZA, the composite of the two arrows is zero, with the inclusion as a
parameter.**  The first arrow `i^*𝓘 ⟶ i^*Ω_{X/B}` followed by the second arrow
`AlgebraicGeometry.Space.pullbackDifferentialsMap` is zero, for any `i` whose structure map
kills the defining ideal of `Z`.

This is the clause of the tag that
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceCompositeZero.lean` proves, stated so that
a consumer holding the inclusion under another name instantiates it directly.  Every `rfl` handed
to `AlgebraicGeometry.Space.submoduleTranspose_comp_pullbackDifferentialsMap_eq_zero'` below is
syntactic, because the derivation and the transpose are both taken at `i`. -/
theorem conormalSequenceFirstMapAt_comp_pullbackDifferentialsMap_eq_zero
    (Z : ClosedSubspaces B S hS X.1) (b : X ⟶ Bb) (i : W ⟶ X)
    (hi : StructureSharpKillsDefiningIdeal B S hS Z i) :
    conormalSequenceFirstMapAt B S hS Z b i hi ≫ pullbackDifferentialsMap B S hS i b = 0 :=
  submoduleTranspose_comp_pullbackDifferentialsMap_eq_zero' B S hS i b
    (definingIdealSheaf B S hS X Z)
    (conormalSequenceIdealDifferentialAt B S hS Z b i hi)
    (pullbackUnitDerivation B S hS i b) rfl
    (conormalSequenceIdealDifferentialAt_val_app_apply B S hS Z b i hi)
    (fun U x ↦ hi U x.1 x.2) rfl

end InclusionParameter

end AlgebraicGeometry.Space

end
