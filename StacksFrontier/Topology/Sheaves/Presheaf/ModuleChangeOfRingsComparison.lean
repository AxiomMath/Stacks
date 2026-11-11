module

public import StacksFrontier.Topology.Sheaves.Presheaf.ModuleChangeOfRings
public import StacksFrontier.Topology.Sheaves.Sheafify.ModuleChangeOfRingsSheaf

/-!
# Mathlib's pullback of presheaves of modules is the sectionwise tensor product

Let `α : 𝒪₁ ⟶ 𝒪₂` be a morphism of presheaves of commutative rings on a topological space `X`.
Mathlib's abstract pullback `tensorPresheaf α` (`PresheafOfModules.pullback`) is isomorphic to the
change of rings functor `Stacks.Sheafify.ChangeOfRingsAdjunction.tensorPresheafFunctor` on the
explicit sectionwise tensor product presheaf `U ↦ 𝒪₂(U) ⊗_{𝒪₁(U)} 𝒢(U)`, both being left adjoint
to restriction of scalars.

## Main results

* `tensorPresheafIsoTensorPresheafFunctor`: the comparison isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory

/-- On the site of opens of a topological space `X`, Mathlib's abstract pullback
`tensorPresheaf α` is isomorphic to the change of rings functor on the explicit sectionwise tensor
product presheaf `U ↦ 𝒪₂(U) ⊗_{𝒪₁(U)} 𝒢(U)`,
`Stacks.Sheafify.ChangeOfRingsAdjunction.tensorPresheafFunctor`: both are left adjoint to
restriction of scalars. -/
noncomputable def tensorPresheafIsoTensorPresheafFunctor {X : TopCat.{u}}
    {𝒪₁ 𝒪₂ : TopCat.Presheaf CommRingCat.{u} X} (α : 𝒪₁ ⟶ 𝒪₂) :
    tensorPresheaf α ≅ Stacks.Sheafify.ChangeOfRingsAdjunction.tensorPresheafFunctor 𝒪₁ 𝒪₂ α :=
  (tensorPresheafAdj α).leftAdjointUniq
    ((Stacks.Sheafify.ChangeOfRingsAdjunction.tensorPresheafAdjunction 𝒪₁ 𝒪₂ α).ofNatIsoRight
      (Iso.refl _))
