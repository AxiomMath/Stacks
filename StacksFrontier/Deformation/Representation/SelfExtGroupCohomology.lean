module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RepresentationTheory.GroupAlgebraExtOneCohomology

/-! # Self-extensions of a representation are first group cohomology (Stacks 0DVT)

Let `ρ₀` be a finite-dimensional representation of a group `Γ` on a `k`-vector space `V`. The
tangent space of the deformation category of `ρ₀` is its first self-extension group over the
group algebra, `Ext¹_{k[Γ]}(V, V)`; that is the clause
`Deformation.tangentSpaceEquivSelfExt` of Stacks 0DVT. This file discharges the second
identification of the same tag,

`Ext¹_{k[Γ]}(V, V) = H¹(Γ, End_k(V))`,

for the conjugation action of `Γ` on `End_k(V)`. Together with the degree-zero statement
`Deformation.infinitesimalAutomorphismsEquivH0` it is what lets the deformation theory of a
representation be read off from the group cohomology of its endomorphism algebra.

The identification itself is `MonoidAlgebra.extOneEquivGroupCohomologyOne`, proved from a single
free presentation of `V` over `k[Γ]`; what is done here is to feed it the `k[Γ]`-module attached
to `ρ₀` by `Rep.equivalenceModuleMonoidAlgebra`, which is the module the tangent-space clause is
stated over.

## Main results

* `Deformation.selfExtEquivGroupCohomologyOne`: **Stacks 0DVT**, the identification of the first
  self-extension group over the group algebra with `H¹(Γ, End_k(V))`.

## References

* [Stacks Project, Tag 0DVT](https://stacks.math.columbia.edu/tag/0DVT)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] HasExt.standard

attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

universe w

namespace Deformation

variable {k Γ : Type w} [Field k] [Group Γ]

/-- The `k`-module underlying the `k[Γ]`-module attached to a representation is the
representation space itself: the `k`-action restricted along `k → k[Γ]` is the original one. -/
def representationModuleEquiv (V : Type w) [AddCommGroup V] [Module k V]
    (ρ₀ : Representation k Γ V) :
    V ≃ₗ[k]
      ((Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj (Rep.of ρ₀) :
        Type w) :=
  { ρ₀.asModuleEquiv.symm.toAddEquiv with
    map_smul' := fun a x ↦ ρ₀.asModuleEquiv_symm_map_smul a x }

/-- **Stacks 0DVT.** The first self-extension group over the group algebra of a
finite-dimensional representation `ρ₀` of `Γ` on `V` is the first group cohomology of the
conjugation action of `Γ` on `End_k(V)`:

`Ext¹_{k[Γ]}(V, V) = H¹(Γ, End_k(V))`.

The extension group is taken over the `k[Γ]`-module attached to `ρ₀`, which is the module over
which the tangent-space clause `Deformation.tangentSpaceEquivSelfExt` of the same tag is
stated. No hypothesis on `Γ` is needed. -/
@[stacks 0DVT "clause 2: `Ext¹_{k[Γ]}(V, V) = H¹(Γ, End_k(V))` for the conjugation action of \
`Γ` on `End_k(V)`, over the `k[Γ]`-module attached to `ρ₀` by \
`Rep.equivalenceModuleMonoidAlgebra`, which is the module clause 1 states its `Ext¹` over. No \
hypothesis on `Γ`"]
def selfExtEquivGroupCohomologyOne (V : Type w) [AddCommGroup V] [Module k V]
    [Module.Finite k V] (ρ₀ : Representation k Γ V) :
    Abelian.Ext
        ((Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj (Rep.of ρ₀))
        ((Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj (Rep.of ρ₀)) 1 ≃ₗ[k]
      (groupCohomology (Rep.of (Representation.linHom ρ₀ ρ₀)) 1 : Type w) := by
  have : Module.Finite k
      (((Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj (Rep.of ρ₀)) :
        Type w) :=
    Module.Finite.equiv (representationModuleEquiv V ρ₀)
  exact MonoidAlgebra.extOneEquivGroupCohomologyOne
    (representationModuleEquiv V ρ₀) (representationModuleEquiv V ρ₀)
    (fun γ v ↦ ρ₀.asModuleEquiv_symm_map_rho γ v)
    (fun γ v ↦ ρ₀.asModuleEquiv_symm_map_rho γ v)

end Deformation

end
