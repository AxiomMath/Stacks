module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceCokernelDerivation
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionDirectImageDerivationKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealBijection

/-!
# The factorization through `Ω_{Z/B}` of a map out of the middle term of the conormal sequence

Let `Z ⊆ X` be a closed subspace of an algebraic space over `B` with structure morphism
`b : X ⟶ B`, and let `i` be a morphism with target `X` whose structure map has the defining ideal
sheaf of `Z` for its kernel. Stacks 05ZA attaches to this datum the sequence
```
  𝒞_{Z/X} ⟶ i^*Ω_{X/B} ⟶ Ω_{Z/B} ⟶ 0
```
whose first arrow is `AlgebraicGeometry.Space.conormalSequenceFirstMapAt` and whose second is
`AlgebraicGeometry.Space.pullbackDifferentialsMap`. This file constructs, for every morphism
`θ : i^*Ω_{X/B} ⟶ W` annihilating the first arrow, a morphism `Ω_{Z/B} ⟶ W`.

## Main definitions

* `AlgebraicGeometry.Space.StructureSharpKernelLeDefiningIdeal`: every local section the structure
  map of `i` kills lies in the defining ideal of `Z`.
* `AlgebraicGeometry.Space.conormalSequenceMiddleDerivation`: the `B`-derivation of `𝒪_Z` with
  values in `W` attached to `θ`.
* `AlgebraicGeometry.Space.conormalSequenceMiddleDesc`: the morphism `Ω_{Z/B} ⟶ W`.

## Main results

* `AlgebraicGeometry.Space.structureSharpCommRing_app_apply`: the commutative-ring structure map
  acts on local sections by the same map as the ring-valued one.
* `AlgebraicGeometry.Space.structureSharpKernelLeDefiningIdeal_subspaceInclusion`: the inclusion
  of a closed subspace satisfies `AlgebraicGeometry.Space.StructureSharpKernelLeDefiningIdeal`.

## References

* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA), the conormal sequence.
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619).
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT), the universal property of
  the sheaf of differentials.
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB), the defining ideal sheaf
  as the kernel of the structure map.
-/

@[expose] public section

open CategoryTheory Opposite
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Bb Zs : AlgebraicSpaces B S hS}

/-- The structure map of Stacks 03G8 as a homomorphism of sheaves of *commutative* rings acts on
local sections by the same map as the ring-valued one. -/
theorem structureSharpCommRing_app_apply (i : Zs ⟶ X) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (a : ToType ((structureRingSheaf B S hS X).obj.obj U)) :
    ((structureSharpCommRing B S hS i).hom.app U) a =
      ((structureSharp B S hS i).hom.app U).hom a :=
  congrArg
    (fun m : structureRingSheaf B S hS X ⟶ structureRingSheafDirectImage B S hS i ↦
      (m.hom.app U).hom a)
    (map_structureSharpCommRing B S hS i)

/-- **The kernel of the structure map of `i` is contained in the defining ideal of `Z`**, chart by
chart: every local section of `𝒪_X` that the structure map of `i` sends to zero lies in the
defining ideal of `Z`. -/
abbrev StructureSharpKernelLeDefiningIdeal (Z : ClosedSubspaces B S hS X.1) (i : Zs ⟶ X) : Prop :=
  ∀ (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (a : ToType ((structureRingSheaf B S hS X).obj.obj U)),
    ((structureSharpCommRing B S hS i).hom.app U) a = 0 →
      a ∈ definingIdealAt B S hS X Z U

/-- The inclusion of a closed subspace satisfies
`AlgebraicGeometry.Space.StructureSharpKernelLeDefiningIdeal`: its structure map has the defining
ideal sheaf for kernel. -/
theorem structureSharpKernelLeDefiningIdeal_subspaceInclusion
    (Z : ClosedSubspaces B S hS X.1) :
    StructureSharpKernelLeDefiningIdeal B S hS Z (subspaceInclusion B S hS X Z) :=
  fun U a ha ↦ (mem_definingIdealAt_iff B S hS X Z U a).2
    ((structureSharpCommRing_app_apply B S hS (subspaceInclusion B S hS X Z) U a).symm.trans ha)

/-- **The derivation of `𝒪_Z` attached to a morphism out of the middle term of the conormal
sequence of Stacks 05ZA annihilating the first arrow**: the descent along the structure map of
`i` of the `B`-derivation of `𝒪_X` with values in `i_*W` that Equation (0619) attaches to `θ`. -/
noncomputable def conormalSequenceMiddleDerivation (Z : ClosedSubspaces B S hS X.1) (b : X ⟶ Bb)
    (i : Zs ⟶ X) (hi : StructureSharpKillsDefiningIdeal B S hS Z i)
    (hker : StructureSharpKernelLeDefiningIdeal B S hS Z i)
    (hclosed : IsClosedImmersion B S hS i.hom) (W : Modules.{u, u} B S hS Zs.1 Zs.2)
    (θ : (modulePullback B S hS i).obj (sheafOfDifferentials B S hS b) ⟶ W)
    (hθ : conormalSequenceFirstMapAt B S hS Z b i hi ≫ θ = 0) :
    PresheafOfModulesOfCommRing.Derivation' W.val (structureSharpInverseImage B S hS (i ≫ b)).hom :=
  (directImageDerivationKernelEquiv B S hS i hclosed b W).symm
    ⟨derivationDirectImageEquiv B S hS i b W θ,
      fun U x hx ↦ derivationDirectImageEquiv_d_eq_zero_of_mem B S hS Z b i hi W θ hθ U x
        (hker U x hx)⟩

/-- **The morphism `Ω_{Z/B} ⟶ W` attached to a morphism `θ : i^*Ω_{X/B} ⟶ W` out of the middle
term of the conormal sequence of Stacks 05ZA annihilating the first arrow**: the morphism
attached by the universal property of Stacks 04CT to
`AlgebraicGeometry.Space.conormalSequenceMiddleDerivation`. -/
noncomputable def conormalSequenceMiddleDesc (Z : ClosedSubspaces B S hS X.1) (b : X ⟶ Bb)
    (i : Zs ⟶ X) (hi : StructureSharpKillsDefiningIdeal B S hS Z i)
    (hker : StructureSharpKernelLeDefiningIdeal B S hS Z i)
    (hclosed : IsClosedImmersion B S hS i.hom) (W : Modules.{u, u} B S hS Zs.1 Zs.2)
    (θ : (modulePullback B S hS i).obj (sheafOfDifferentials B S hS b) ⟶ W)
    (hθ : conormalSequenceFirstMapAt B S hS Z b i hi ≫ θ = 0) :
    sheafOfDifferentials B S hS (i ≫ b) ⟶ W :=
  (differentialsHomEquiv B S hS (i ≫ b) W).symm
    (conormalSequenceMiddleDerivation B S hS Z b i hi hker hclosed W θ hθ)

end AlgebraicGeometry.Space

end
