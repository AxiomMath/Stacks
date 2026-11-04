module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleEquivalence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallSiteMonoidalClosed
public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctor
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObjectInternalHom

/-!
# The dual of an invertible module on an algebraic space

Let `Z` be an algebraic space over a scheme `S` and `ℒ` an invertible `𝒪_Z`-module on the small
étale site. Its dual `ℒ^∨ = 𝓗om(ℒ, 𝒪_Z)` is an inverse of `ℒ` for the tensor product:

  `ℒ^∨ ≅ ℒ^{⊗ -1}`,   `ℒ^∨ ⊗ ℒ ≅ 𝒪_Z`,   `ℒ ⊗ ℒ^∨ ≅ 𝒪_Z`,

and in particular `ℒ^∨` is invertible. This is the rank one case of the duality used in the proof
of Stacks 0ESD.

## Main definitions

* `AlgebraicGeometry.Space.dualTensorSelfIso` and `AlgebraicGeometry.Space.selfTensorDualIso`:
  `ℒ^∨ ⊗ ℒ ≅ 𝒪_Z` and `ℒ ⊗ ℒ^∨ ≅ 𝒪_Z`.

## Main results

* `AlgebraicGeometry.Space.isInvertibleModule_dual`: **the dual of an invertible `𝒪_Z`-module is
  invertible.**
* `AlgebraicGeometry.Space.eq_neg_of_dual`: an invariant of invertible modules which is additive
  on tensor products, invariant under isomorphism and zero on `𝒪_Z` changes sign on duals.

## Implementation notes

Invertibility is `AlgebraicGeometry.Space.IsInvertibleModule`, tensoring by the module being an
equivalence (Stacks 01CS); by `Stacks.SheafOfModules.hasInverse_of_isInvertible` this provides a
two-sided tensor inverse for `AlgebraicGeometry.Space.modulesMonoidalCategory`, and the internal
Hom out of an object with a two-sided inverse is tensoring by the inverse
(`CategoryTheory.MonoidalCategory.HasInverse.ihomIso`).

## References

* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 0FFN](https://stacks.math.columbia.edu/tag/0FFN)
* [Stacks Project, Tag 0ESD](https://stacks.math.columbia.edu/tag/0ESD)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] modulesMonoidalCategory modulesMonoidalClosed

/-- The two-sided tensor inverse of an invertible `𝒪_Z`-module. -/
def IsInvertibleModule.hasInverse {Z : AlgebraicSpaces B S hS} {L : Modules.{u, u} B S hS Z.1 Z.2}
    (hL : IsInvertibleModule Z L) : HasInverse L :=
  let := hL
  Stacks.SheafOfModules.hasInverse_of_isInvertible (structureSheaf B S hS Z.1 Z.2).obj
    (structureRingPresheaf_isSheaf B S hS Z.1 Z.2) L

/-- **The dual of an invertible `𝒪_Z`-module is its inverse**: `ℒ^∨ ≅ ℒ^{⊗ -1}`. -/
def IsInvertibleModule.dualIsoInv {Z : AlgebraicSpaces B S hS}
    {L : Modules.{u, u} B S hS Z.1 Z.2} (hL : IsInvertibleModule Z L) :
    (ihom L).obj (𝟙_ _) ≅ hL.hasInverse.inv :=
  hL.hasInverse.ihomUnitIso

/-- The evaluation isomorphism `ℒ^∨ ⊗ ℒ ≅ 𝒪_Z` of an invertible `𝒪_Z`-module. -/
def dualTensorSelfIso {Z : AlgebraicSpaces B S hS} {L : Modules.{u, u} B S hS Z.1 Z.2}
    (hL : IsInvertibleModule Z L) : (ihom L).obj (𝟙_ _) ⊗ L ≅ 𝟙_ _ :=
  hL.hasInverse.ihomUnitHasInverse.isoLeft

/-- The isomorphism `ℒ ⊗ ℒ^∨ ≅ 𝒪_Z` of an invertible `𝒪_Z`-module. -/
def selfTensorDualIso {Z : AlgebraicSpaces B S hS} {L : Modules.{u, u} B S hS Z.1 Z.2}
    (hL : IsInvertibleModule Z L) : L ⊗ (ihom L).obj (𝟙_ _) ≅ 𝟙_ _ :=
  hL.hasInverse.ihomUnitHasInverse.isoRight

/-- An `𝒪_Z`-module with a two-sided tensor inverse is invertible. -/
private theorem isInvertibleModule_of_hasInverse {Z : AlgebraicSpaces B S hS}
    {L : Modules.{u, u} B S hS Z.1 Z.2} (h : HasInverse L) : IsInvertibleModule Z L :=
  Stacks.SheafOfModules.isInvertible_of_hasInverse (structureSheaf B S hS Z.1 Z.2).obj
    (structureRingPresheaf_isSheaf B S hS Z.1 Z.2) h

/-- **The dual of an invertible `𝒪_Z`-module is invertible.** -/
theorem isInvertibleModule_dual {Z : AlgebraicSpaces B S hS} {L : Modules.{u, u} B S hS Z.1 Z.2}
    (hL : IsInvertibleModule Z L) : IsInvertibleModule Z ((ihom L).obj (𝟙_ _)) :=
  isInvertibleModule_of_hasInverse hL.hasInverse.ihomUnitHasInverse

/-- `ℒ ⊗ ℒ^∨` is invertible, being isomorphic to `𝒪_Z`. -/
theorem isInvertibleModule_tensorObj_dual {Z : AlgebraicSpaces B S hS}
    {L : Modules.{u, u} B S hS Z.1 Z.2} (hL : IsInvertibleModule Z L) :
    IsInvertibleModule Z (L ⊗ (ihom L).obj (𝟙_ _)) :=
  isInvertibleModule_of_hasInverse
    (show HasInverse (L ⊗ (ihom L).obj (𝟙_ _)) from
      { inv := 𝟙_ _
        isoLeft := ρ_ _ ≪≫ selfTensorDualIso hL
        isoRight := λ_ _ ≪≫ selfTensorDualIso hL })

/-- **An additive invariant of invertible modules changes sign on duals.** If `x` is a function
on the invertible `𝒪_Z`-modules with values in an abelian group, additive on tensor products,
invariant under isomorphism and zero on `𝒪_Z`, then `x(ℒ^∨) = -x(ℒ)`; for the first Chern class
this is the identity `c₁(ℒ^∨) = -c₁(ℒ)` of the proof of Stacks 0ESD, from Stacks 0EQK. -/
theorem eq_neg_of_dual {G : Type*} [AddCommGroup G] {Z : AlgebraicSpaces B S hS}
    (x : ∀ L : Modules.{u, u} B S hS Z.1 Z.2, IsInvertibleModule Z L → G)
    (hadd : ∀ (L M : Modules.{u, u} B S hS Z.1 Z.2) hL hM hLM,
      x (L ⊗ M) hLM = x L hL + x M hM)
    (hiso : ∀ (L L' : Modules.{u, u} B S hS Z.1 Z.2) hL hL', Nonempty (L ≅ L') →
      x L hL = x L' hL')
    (hunit : ∀ h, x (𝟙_ _) h = 0) {L : Modules.{u, u} B S hS Z.1 Z.2}
    (hL : IsInvertibleModule Z L) :
    x ((ihom L).obj (𝟙_ _)) (isInvertibleModule_dual hL) = -x L hL := by
  have h := hadd L _ hL (isInvertibleModule_dual hL) (isInvertibleModule_tensorObj_dual hL)
  rw [hiso _ (𝟙_ _) _ (isInvertibleModule_of_hasInverse
      (hasInverseUnit (C := Modules.{u, u} B S hS Z.1 Z.2))) ⟨selfTensorDualIso hL⟩,
    hunit] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

end AlgebraicGeometry.Space

end
