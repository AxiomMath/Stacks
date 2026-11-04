module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Flat.Basic

/-!
# Tensoring modules on the right at split universes

Mathlib's `MonoidalCategory (ModuleCat.{u} R)` — and with it
`MonoidalCategory.tensorRight`, `ModuleCat.monoidalClosed` and
`Module.Flat.iff_preservesFiniteLimits_tensorRight` — is stated only for a ring
carrier `R : Type u` in the *same* universe as the modules. The underlying
constructions have no such constraint: for `R : Type w` and `M N : Type m` both
`N ⊗[R] M` and `M →ₗ[R] N` live in `Type m`, whatever `w` is. This file re-runs
the part of that theory which exactness of the tensor product needs, with the
ring universe `w` and the module universe `m` independent.

Three things are proved, and all three are assembly rather than new mathematics:
the pieces (`TensorProduct`, `LinearMap.rTensor`, `Module.Flat`,
`Module.Flat.rTensor_exact`, `ModuleCat.abelian`,
`ShortComplex.ShortExact.moduleCat_exact_iff_function_exact`,
`CategoryTheory.Functor.exact_tfae`) are already universe-independent.

## Main definitions

* `ModuleCat.tensorRightSplit M`: the endofunctor `N ↦ N ⊗[R] M` of
  `ModuleCat.{m} R` for `R : Type w`, with `m` and `w` independent.
* `ModuleCat.ihomSplit M`: its right adjoint `N ↦ (M →ₗ[R] N)`.

## Main results

* `ModuleCat.tensorHomAdjunctionSplit`: the tensor-hom adjunction
  `tensorRightSplit M ⊣ ihomSplit M`.
* `ModuleCat.preservesColimitsOfSize_tensorRightSplit`: tensoring on the right
  preserves all colimits.
* `ModuleCat.preservesFiniteLimits_tensorRightSplit`: **flat implies left
  exact** — tensoring on the right with a flat module preserves finite limits.
* `ModuleCat.exact_map_tensorRightSplit`: tensoring on the right with a flat
  module preserves exactness of short complexes.

## Implementation notes

The ring universe `w` and the module universe `m` are completely free here: no
`UnivLE` hypothesis and no `max` appears. That is the point — the only reason
Mathlib's monoidal structure on `ModuleCat` forces `m = w` is that the monoidal
unit is `R` itself, which is an object of `ModuleCat.{w} R` and of no other
`ModuleCat.{m} R`. Tensoring on the right with a *fixed* module never mentions
the unit, so it survives the separation.
-/

@[expose] public section

universe m w

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace ModuleCat

variable {R : Type w} [CommRing R]

/-- Tensoring on the right with `M`, as an endofunctor of `ModuleCat.{m} R` for a
ring `R : Type w`. The two universes are independent; this is
`MonoidalCategory.tensorRight` with the module universe separated from the ring
universe. -/
noncomputable def tensorRightSplit (M : ModuleCat.{m} R) :
    ModuleCat.{m} R ⥤ ModuleCat.{m} R where
  obj N := ModuleCat.of R (N ⊗[R] M)
  map {_ _} f := ofHom (LinearMap.rTensor M f.hom)
  map_id _ :=
    ModuleCat.hom_ext <| TensorProduct.ext' fun _ _ ↦ rfl
  map_comp {_ _ _} _ _ :=
    ModuleCat.hom_ext <| TensorProduct.ext' fun _ _ ↦ rfl

/-- The functor `ModuleCat.tensorRightSplit M` sends `f` to `f ⊗ id`: on a pure tensor,
`n ⊗ₜ x ↦ f n ⊗ₜ x`. -/
@[simp]
lemma tensorRightSplit_map_tmul {M N N' : ModuleCat.{m} R} (f : N ⟶ N') (n : N) (x : M) :
    (tensorRightSplit M).map f (n ⊗ₜ[R] x) = f n ⊗ₜ[R] x := rfl

/-- The internal hom `N ↦ (M →ₗ[R] N)`, as an endofunctor of `ModuleCat.{m} R`
for a ring `R : Type w`. This is the right adjoint of
`ModuleCat.tensorRightSplit M`. -/
noncomputable def ihomSplit (M : ModuleCat.{m} R) :
    ModuleCat.{m} R ⥤ ModuleCat.{m} R where
  obj N := ModuleCat.of R (M →ₗ[R] N)
  map {_ N'} g := ofHom
    { toFun := fun h ↦ g.hom ∘ₗ h
      map_add' := fun h₁ h₂ ↦ by ext x; simp
      map_smul' := fun r h ↦ by ext x; simp }
  map_id N := by
    apply ModuleCat.hom_ext
    ext h x
    rfl
  map_comp {N₁ N₂ N₃} f g := by
    apply ModuleCat.hom_ext
    ext h x
    rfl

/-- **The tensor-hom adjunction at split universes.** For `R : Type w` and
modules with carrier in `Type m`, tensoring on the right with `M` is left
adjoint to `M →ₗ[R] -`. -/
noncomputable def tensorHomAdjunctionSplit (M : ModuleCat.{m} R) :
    tensorRightSplit M ⊣ ihomSplit M :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun N P ↦
        { toFun := fun φ ↦ ofHom (TensorProduct.curry φ.hom)
          invFun := fun ψ ↦ ofHom (TensorProduct.lift ψ.hom)
          left_inv := fun φ ↦
            ModuleCat.hom_ext <| TensorProduct.ext' fun _ _ ↦ rfl
          right_inv := fun ψ ↦ by
            apply ModuleCat.hom_ext
            ext n x
            rfl }
      homEquiv_naturality_left_symm := fun {N N' P} f g ↦
        ModuleCat.hom_ext <| TensorProduct.ext' fun _ _ ↦ rfl
      homEquiv_naturality_right := fun {N P P'} f g ↦ by
        apply ModuleCat.hom_ext
        ext n
        rfl }

/-- Tensoring on the right with `M` is a left adjoint. -/
instance isLeftAdjoint_tensorRightSplit (M : ModuleCat.{m} R) :
    (tensorRightSplit M).IsLeftAdjoint :=
  ⟨_, ⟨tensorHomAdjunctionSplit M⟩⟩

/-- **Tensoring on the right preserves all colimits**, at split universes. -/
instance preservesColimitsOfSize_tensorRightSplit (M : ModuleCat.{m} R) :
    PreservesColimitsOfSize.{m, m} (tensorRightSplit M) :=
  (tensorHomAdjunctionSplit M).leftAdjoint_preservesColimits

/-- Tensoring on the right with `M` preserves finite colimits. -/
instance preservesFiniteColimits_tensorRightSplit (M : ModuleCat.{m} R) :
    PreservesFiniteColimits (tensorRightSplit M) :=
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- Tensoring on the right with `M` is an additive functor. -/
instance additive_tensorRightSplit (M : ModuleCat.{m} R) : (tensorRightSplit M).Additive where
  map_add {_ _} f g :=
    ModuleCat.hom_ext <| TensorProduct.ext' fun n x ↦ TensorProduct.add_tmul (f n) (g n) x

/-- **Tensoring on the right with a flat module preserves exactness**, at split
universes. -/
lemma exact_map_tensorRightSplit (M : ModuleCat.{m} R) [Module.Flat R M]
    (S : ShortComplex (ModuleCat.{m} R)) (hS : S.Exact) :
    (S.map (tensorRightSplit M)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
  exact Module.Flat.rTensor_exact M hS

/-- **Flat implies left exact**, at split universes: tensoring on the right with
a flat module preserves finite limits. -/
lemma preservesFiniteLimits_tensorRightSplit (M : ModuleCat.{m} R) [Module.Flat R M] :
    PreservesFiniteLimits (tensorRightSplit M) :=
  (((tensorRightSplit M).exact_tfae.out 2 4 rfl rfl).1 (exact_map_tensorRightSplit M)).1

end ModuleCat
