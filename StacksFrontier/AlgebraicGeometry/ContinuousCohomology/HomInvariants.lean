module

public import Mathlib.LinearAlgebra.Contraction
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.DualTensor
public import StacksFrontier.Algebra.Category.ModuleCat.DiscreteTopology

/-!
# `Hom(M, N)` is the invariants of `Mᵛ ⊗ N`

Let `G` be a topological group, `R` a commutative ring, and let `M` and `N` be continuous
discrete `R`-`G`-modules with `M` finite projective over `R`. This file proves the degree-zero
case of [Stacks, Tag 0DVE]: the `R`-module of morphisms `M ⟶ N` of continuous `R`-`G`-modules is
the `R`-module of `G`-invariants of `Mᵛ ⊗_R N` with the diagonal action.

## Main definitions

* `Stacks.ContinuousCohomology.homEquivInvariantsDualTensor` — the `R`-linear isomorphism
  `(M ⟶ N) ≃ₗ[R] Hⁱ(G, Mᵛ ⊗_R N)` for `i = 0`, in the form
  `(M ⟶ N) ≃ₗ[R] (continuousModuleInvariants R G).obj (dualTensorContinuousModule R G M N)`.

## References

* [Stacks Project, Tag 0DVE](https://stacks.math.columbia.edu/tag/0DVE)
-/


@[expose] public noncomputable section

open CategoryTheory TensorProduct

universe u v w

namespace Stacks.ContinuousCohomology

attribute [local instance] Stacks.DiscreteModuleTopology.hasForget₂ModuleCatTopCat
  Stacks.DiscreteModuleTopology.actionDiscreteTopology

section Invariants

variable {R : Type*} [CommRing R] {G : Type*} [Group G]
  {V W : Type*} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  {ρ : Representation R G V} {σ : Representation R G W}

/-- An `R`-linear isomorphism intertwining two representations restricts to an `R`-linear
isomorphism of their submodules of invariants. -/
def invariantsEquivOfLinearEquiv (e : V ≃ₗ[R] W)
    (he : ∀ (g : G) (x : V), e (ρ g x) = σ g (e x)) :
    ρ.invariants ≃ₗ[R] σ.invariants where
  toFun x := ⟨e x.1, fun g => by
    rw [← he g x.1, (Representation.mem_invariants ρ x.1).1 x.2 g]⟩
  invFun y := ⟨e.symm y.1, fun g => by
    apply e.injective
    rw [he g (e.symm y.1), e.apply_symm_apply,
      (Representation.mem_invariants σ y.1).1 y.2 g]⟩
  map_add' x y := Subtype.ext (map_add e x.1 y.1)
  map_smul' r x := Subtype.ext (map_smul e r x.1)
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv y := Subtype.ext (e.apply_symm_apply y.1)

end Invariants

variable (R : Type u) [CommRing R] (G : Type v) [Group G] [TopologicalSpace G]
  (M N : Stacks.Injectives.ContinuousModule.{u, v, w} R G)

/-- Membership in the invariants of the conjugation action on `Hom_R(M, N)` says exactly that an
`R`-linear map is `G`-equivariant. -/
lemma mem_linHom_invariants_iff (f : M.obj.obj.V →ₗ[R] N.obj.obj.V) :
    f ∈ (Representation.linHom (rep R G M) (rep R G N)).invariants ↔
      ∀ (g : G) (x : M.obj.obj.V), f (rep R G M g x) = rep R G N g (f x) := by
  rw [Representation.mem_invariants]
  simp only [Representation.linHom_apply]
  rw [Representation.mem_linHom_invariants_iff_isIntertwining]
  exact ⟨fun h => h.isIntertwining, fun h => ⟨h⟩⟩

/-- A morphism of continuous discrete `R`-`G`-modules is the same thing as a `G`-equivariant
`R`-linear map, i.e. an invariant of the conjugation action on `Hom_R(M, N)`. -/
def homEquivLinHomInvariants :
    (M ⟶ N) ≃ₗ[R] (Representation.linHom (rep R G M) (rep R G N)).invariants where
  toFun f := ⟨f.hom.hom.hom.hom, (mem_linHom_invariants_iff R G M N _).2 fun g x =>
    ConcreteCategory.congr_hom (f.hom.hom.comm g) x⟩
  invFun f := ObjectProperty.homMk (ObjectProperty.homMk
    { hom := ModuleCat.ofHom f.1
      comm := fun g => by
        apply ModuleCat.hom_ext
        ext x
        exact (mem_linHom_invariants_iff R G M N f.1).1 f.2 g x })
  map_add' f g := Subtype.ext rfl
  map_smul' r f := Subtype.ext rfl
  left_inv f := rfl
  right_inv f := Subtype.ext rfl

section FiniteProjective

variable [Module.Finite R M.obj.obj.V] [Module.Projective R M.obj.obj.V]

/-- The `R`-linear isomorphism from the presentation of `Mᵛ ⊗_R N` to `Hom_R(M, N)`: undo the
presentation, then contract. -/
def smallModelEquivHom :
    Stacks.DualTensor.smallModel R M.obj.obj.V N.obj.obj.V ≃ₗ[R]
      (M.obj.obj.V →ₗ[R] N.obj.obj.V) :=
  (Stacks.DualTensor.smallModelEquiv R M.obj.obj.V N.obj.obj.V).symm.trans
    (dualTensorHomEquiv R M.obj.obj.V N.obj.obj.V)

/-- `smallModelEquivHom` intertwines the transported diagonal action with the conjugation action
on `Hom_R(M, N)`. -/
lemma smallModelEquivHom_intertwines (g : G)
    (z : Stacks.DualTensor.smallModel R M.obj.obj.V N.obj.obj.V) :
    smallModelEquivHom R G M N (dualTensorSmallRep R G M N g z) =
      Representation.linHom (rep R G M) (rep R G N) g (smallModelEquivHom R G M N z) := by
  have h := congr($(Representation.dualTensorHom_comm (rep R G M) (rep R G N) g)
    ((Stacks.DualTensor.smallModelEquiv R M.obj.obj.V N.obj.obj.V).symm z))
  simp only [LinearMap.comp_apply] at h
  have e : ∀ x, dualTensorHomEquiv R M.obj.obj.V N.obj.obj.V x =
      dualTensorHom R M.obj.obj.V N.obj.obj.V x := fun _ => rfl
  simpa [smallModelEquivHom, dualTensorSmallRep_apply, e] using h

/-- For `M` finite projective over `R`, the `R`-module of morphisms `M ⟶ N` of continuous
discrete `R`-`G`-modules is the `R`-module of `G`-invariants of `Mᵛ ⊗_R N` with the diagonal
action, that is, `H⁰(G, Mᵛ ⊗_R N)`. -/
def homEquivInvariantsDualTensor :
    (M ⟶ N) ≃ₗ[R]
      (continuousModuleInvariants.{u, v, w} R G).obj
        (dualTensorContinuousModule.{u, v, w} R G M N) :=
  (homEquivLinHomInvariants R G M N).trans
    (invariantsEquivOfLinearEquiv (ρ := dualTensorSmallRep R G M N)
      (σ := Representation.linHom (rep R G M) (rep R G N))
      (smallModelEquivHom R G M N) (smallModelEquivHom_intertwines R G M N)).symm

end FiniteProjective

end Stacks.ContinuousCohomology
