module

public import StacksCore.CategoryTheory.Abelian.SerreClass.Localization
public import StacksFrontier.AlgebraicGeometry.ProjSerreCorrespondence.IrrelevantQuotientFunctor
public import StacksFrontier.AlgebraicGeometry.ProjSerreCorrespondence.TorsionKernel
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Generation in degree one: the kernel of `M ↦ M̃` is exactly the torsion modules

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring which is Noetherian as a ring and which is generated
over `𝒜 0` by its degree-one part, and let `X = Proj(A)`. This file proves that the kernel of
`M ↦ M̃` on the category `Mod^fg_A` of finitely generated graded `A`-modules is exactly the
subcategory of torsion modules, and hence that the functor
`Mod^fg_A / Mod^fg_{A, torsion} ⟶ Mod(𝒪_X)` induced by `M ↦ M̃` on the quotient category is
faithful. This is part of Stacks 0BXD.

Without generation in degree one the kernel can be strictly larger: over `k[x]` with `x` in degree
two, the module `A(1)` has `A(1)~ = 0` but is not torsion.

## Main results

* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.kernel_finiteAssociatedSheafFunctor`: for
  `A` generated in degree one, the torsion subcategory of `Mod^fg_A` is the kernel of `M ↦ M̃`.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.faithful_irrelevantQuotientFunctor_one`: the
  functor `Mod^fg_A / Mod^fg_{A, torsion} ⟶ Mod(𝒪_X)` induced by `M ↦ M̃` is faithful.

## References

* [Stacks Project, Tag 0BXD](https://stacks.math.columbia.edu/tag/0BXD)
* [Stacks Project, Tag 0BXF](https://stacks.math.columbia.edu/tag/0BXF)
* [Stacks Project, Tag 06XK](https://stacks.math.columbia.edu/tag/06XK)
* [Stacks Project, Tag 02MS](https://stacks.math.columbia.edu/tag/02MS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality

namespace Stacks.AlgebraicGeometry.ProjSerreCorrespondence

universe u w

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮] [IsNoetherianRing S]

/-- Over a Noetherian graded ring generated in degree one, the kernel of `M ↦ M̃` on the finitely
generated graded modules (the objects whose associated sheaf is a zero object) is exactly the
torsion subcategory, that is, the irrelevant modules of Tag 0BXE in generation degree one. -/
theorem kernel_finiteAssociatedSheafFunctor
    (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤) :
    irrelevantModules.{u, u, w} 𝒮 1 = (finiteAssociatedSheafFunctor.{u, w} 𝒮).kernel := by
  refine le_antisymm (irrelevantModules_le_kernel 𝒮 Nat.one_pos) fun M hM => ?_
  have : Module.Finite S M.obj.carrier := M.property
  exact (isIrrelevant_iff_gradeEventuallyZero 𝒮 Nat.one_pos).2
    ((isZero_associatedModuleSheaf_iff_gradeEventuallyZero 𝒮 hgen).1 hM)

/-- Over a Noetherian graded ring generated in degree one, the functor
`Mod^fg_A / Mod^fg_{A, torsion} ⟶ Mod(𝒪_X)` induced by `M ↦ M̃` is faithful. -/
@[ega "III 2.3.3" "partial"]
theorem faithful_irrelevantQuotientFunctor_one
    (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤) :
    (irrelevantQuotientFunctor.{u, w} 𝒮 Nat.one_pos).Faithful := by
  have := isSerreClass_irrelevantModules.{u, u, w} 𝒮 Nat.one_pos
  have := preservesFiniteLimits_finiteAssociatedSheafFunctor.{u, w} 𝒮
  have := preservesFiniteColimits_finiteAssociatedSheafFunctor.{u, w} 𝒮
  exact (ObjectProperty.SerreClassLocalization.faithful_liftOfLeKernel_iff
    (toIrrelevantQuotient 𝒮 Nat.one_pos) (irrelevantModules.{u, u, w} 𝒮 1)
    (finiteAssociatedSheafFunctor.{u, w} 𝒮)
    (le_of_eq (kernel_finiteAssociatedSheafFunctor 𝒮 hgen))).2
      (kernel_finiteAssociatedSheafFunctor 𝒮 hgen)

end Stacks.AlgebraicGeometry.ProjSerreCorrespondence

end
