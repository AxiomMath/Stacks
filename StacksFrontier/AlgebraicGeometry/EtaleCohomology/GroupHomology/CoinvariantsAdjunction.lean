module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupHomology.DerivedCoinvariants

/-!
# The coinvariants of `Λ[[G]]`-modules are a left adjoint

Let `Λ` be a ring and `G` a topological group. The coinvariants `N ↦ Λ ⊗_{Λ[[G]]} N = N / I N` of
`Λ[[G]]`-modules are left adjoint to the functor viewing a `Λ`-module as a `Λ[[G]]`-module through
the augmentation `Λ[[G]] → Λ`: a `Λ[[G]]`-linear map `N → L` into a module on which `Λ[[G]]` acts
through the augmentation kills `I N`. Hence the coinvariants are right exact, and the left derived
functor in degree zero is the coinvariants themselves.

## Main definitions

* `Stacks.GroupHomology.coinvariantsAdjunction`: the adjunction.

## Main results

* `Stacks.GroupHomology.preservesFiniteColimits_coinvariantsFunctor`: the coinvariants are right
  exact.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.GroupHomology

open CompletedGroupAlgebra

variable (Λ : Type u) [Ring Λ] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable {Λ G} in
/-- `a n - ε(a) n` lies in `I N`, `ε` the augmentation. -/
theorem sub_const_augmentation_smul_mem {N : Type*} [AddCommGroup N]
    [Module (CompletedGroupAlgebra Λ G) N] (a : CompletedGroupAlgebra Λ G) (n : N) :
    a • n - (const (augmentation a) : CompletedGroupAlgebra Λ G) • n ∈
      augmentationSubmodule Λ G N := by
  rw [← sub_smul]
  apply smul_mem_augmentationSubmodule
  rw [map_sub, augmentation_const, sub_self]

/-- The class of `n` in the coinvariants. -/
abbrev coinvariantsMk {N : ModuleCat.{u} (CompletedGroupAlgebra Λ G)} (n : N) :
    (coinvariantsFunctor Λ G).obj N :=
  Submodule.Quotient.mk n

/-- The class of a sum is the sum of the classes. -/
theorem coinvariantsMk_add {N : ModuleCat.{u} (CompletedGroupAlgebra Λ G)} (n n' : N) :
    coinvariantsMk Λ G (n + n') = coinvariantsMk Λ G n + coinvariantsMk Λ G n' :=
  rfl

/-- The class of `a n` is `ε(a)` times the class of `n`, `ε` the augmentation. -/
theorem coinvariantsMk_smul {N : ModuleCat.{u} (CompletedGroupAlgebra Λ G)}
    (a : CompletedGroupAlgebra Λ G) (n : N) :
    coinvariantsMk Λ G (a • n) = augmentation a • coinvariantsMk Λ G n :=
  (Submodule.Quotient.eq _).2 (sub_const_augmentation_smul_mem a n)

/-- `I N` lies in the kernel of a `Λ[[G]]`-linear map into a module on which `Λ[[G]]` acts through
the augmentation. -/
theorem augmentationSubmodule_le_ker {N : ModuleCat.{u} (CompletedGroupAlgebra Λ G)}
    {L : ModuleCat.{u} Λ}
    (f : N ⟶ (ModuleCat.restrictScalars (augmentation : CompletedGroupAlgebra Λ G →+* Λ)).obj L) :
    augmentationSubmodule Λ G N ≤ LinearMap.ker f.hom :=
  Submodule.span_le.2 (by
    rintro _ ⟨a, ha, n, rfl⟩
    change f.hom (a • n) = 0
    rw [map_smul, ModuleCat.restrictScalars.smul_def, ha, zero_smul]
    rfl)

/-- The `Λ`-linear map out of the coinvariants induced by a `Λ[[G]]`-linear map into a module on
which `Λ[[G]]` acts through the augmentation. -/
def coinvariantsLift {N : ModuleCat.{u} (CompletedGroupAlgebra Λ G)} {L : ModuleCat.{u} Λ}
    (f : N ⟶ (ModuleCat.restrictScalars (augmentation : CompletedGroupAlgebra Λ G →+* Λ)).obj L) :
    (coinvariantsFunctor Λ G).obj N ⟶ L :=
  let F := (augmentationSubmodule Λ G N).liftQ f.hom (augmentationSubmodule_le_ker Λ G f)
  ModuleCat.ofHom (X := (coinvariantsFunctor Λ G).obj N) (Y := L)
    { toFun := F
      map_add' := map_add F
      map_smul' c x := by
        have := F.map_smul (const c) x
        rw [ModuleCat.restrictScalars.smul_def, augmentation_const] at this
        exact this }

/-- The `Λ[[G]]`-linear map into a module on which `Λ[[G]]` acts through the augmentation,
induced by a `Λ`-linear map out of the coinvariants. -/
def coinvariantsRestrict {N : ModuleCat.{u} (CompletedGroupAlgebra Λ G)} {L : ModuleCat.{u} Λ}
    (g : (coinvariantsFunctor Λ G).obj N ⟶ L) :
    N ⟶ (ModuleCat.restrictScalars (augmentation : CompletedGroupAlgebra Λ G →+* Λ)).obj L :=
  ModuleCat.ofHom (X := N)
    (Y := (ModuleCat.restrictScalars (augmentation : CompletedGroupAlgebra Λ G →+* Λ)).obj L)
    { toFun := fun n ↦ g.hom (coinvariantsMk Λ G n)
      map_add' := fun n n' ↦
        (congrArg g.hom (coinvariantsMk_add Λ G n n')).trans (map_add g.hom _ _)
      map_smul' := fun a n ↦
        (congrArg g.hom (coinvariantsMk_smul Λ G a n)).trans (map_smul g.hom (augmentation a) _) }

/-- **The coinvariants are left adjoint to restriction along the augmentation.** -/
def coinvariantsAdjunction :
    coinvariantsFunctor Λ G ⊣
      ModuleCat.restrictScalars (augmentation : CompletedGroupAlgebra Λ G →+* Λ) :=
  Adjunction.mkOfHomEquiv
    { homEquiv N L :=
        { toFun := coinvariantsRestrict Λ G
          invFun := coinvariantsLift Λ G
          left_inv g := by
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro x
            exact Submodule.Quotient.induction_on (augmentationSubmodule Λ G N) x fun _ ↦ rfl
          right_inv f := rfl }
      homEquiv_naturality_left_symm _ _ := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact Submodule.Quotient.induction_on _ x fun _ ↦ rfl
      homEquiv_naturality_right _ _ := rfl }

/-- The coinvariants are a left adjoint. -/
instance : (coinvariantsFunctor Λ G).IsLeftAdjoint :=
  (coinvariantsAdjunction Λ G).isLeftAdjoint

/-- **The coinvariants are right exact.** -/
instance preservesFiniteColimits_coinvariantsFunctor :
    PreservesFiniteColimits (coinvariantsFunctor Λ G) :=
  inferInstance

end Stacks.GroupHomology

end
