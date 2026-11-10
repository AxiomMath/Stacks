module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.CharacterModule
public import Mathlib.CategoryTheory.Limits.Shapes.SplitCoequalizer
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import StacksCore.Tactic.StacksAttribute

/-!
# The Hom-tensor adjunction for character modules

For a commutative ring `R` the character module functor `C(M) = Hom_{Ab}(M, ℚ / ℤ)` satisfies
`C(M₁ ⊗_R M₂) ≅ Hom_R(M₁, C(M₂))`, naturally in both variables, and consequently a split
coequalizer of character modules stays a split coequalizer after tensoring the modules with an
arbitrary module inside `C`.

## Main definitions

* `CharacterModule.tensorRightHomEquiv` is the adjunction isomorphism read with the tensor
  factor on the right, `C(M ⊗ Q) ≅ Hom_R(Q, C(M))`.
* `CharacterModule.tensorRightMap` sends a map of character modules to the map obtained from it
  by tensoring with `Q` inside `C`.

## Main results

* `CharacterModule.dual_map_conj_homEquiv` is the naturality of the adjunction isomorphism in
  both variables at once.
* `CharacterModule.isSplitCoequalizer_dual_rTensor` is the corollary of the remark: a split
  coequalizer `C(M) ⇉ C(N) → C(P)` of character-module duals remains a split coequalizer after
  replacing `M`, `N`, `P` by `M ⊗ Q`, `N ⊗ Q`, `P ⊗ Q`.

## Implementation notes

The isomorphism itself and the formula `f ↦ (m₁ ↦ (m₂ ↦ f (m₁ ⊗ m₂)))` displayed in the remark
are `CharacterModule.homEquiv` and `CharacterModule.homEquiv_symm_apply_apply_apply` in Mathlib,
so they are registered rather than restated. Naturality is recorded as one equation for an
arbitrary pair of linear maps `f`, `g`, which is naturality of the isomorphism of contravariant
bifunctors `Mod_R × Mod_R → Mod_R` displayed in the remark; Mathlib's
`CharacterModule.dual_rTensor_conj_homEquiv` is its special case `g = id`.

The arrows of the remark's split coequalizer diagram are the character-module duals `C(u)` of
linear maps `u`, since that is what makes the second diagram -- obtained by tensoring the three
modules with `Q` inside `C` -- determined by the first; this is also how the diagram arises
where the remark is used. The proof is the one in the remark: under the adjunction the functor
`C(- ⊗ Q)` becomes `Hom_R(Q, C(-))`, which is postcomposition on arrows, and split
coequalizers are preserved by any functor. The analogous statement for the tensor factor on the
left, for a module which is moreover an `R`-algebra, is
`ModuleCat.characterDual_splitCoequalizer_tensor_any`.

## References

* [Stacks Project, Tag 08WS](https://stacks.math.columbia.edu/tag/08WS)
-/

@[expose] public section

universe u v

open CategoryTheory TensorProduct

namespace CharacterModule

variable {R : Type u} [CommRing R]

section Naturality

variable {M₁ M₁' M₂ M₂' : Type v}
  [AddCommGroup M₁] [AddCommGroup M₁'] [AddCommGroup M₂] [AddCommGroup M₂']
  [Module R M₁] [Module R M₁'] [Module R M₂] [Module R M₂']

/-- **Stacks 08WS.** The adjunction isomorphism `C(• ⊗_R •) ≅ Hom_R(•, C(•))` is natural in
both variables: conjugating `C(f ⊗ g)` by it gives `φ ↦ C(g) ∘ φ ∘ f`. -/
@[stacks 08WS "naturality of the adjunction isomorphism"]
theorem dual_map_conj_homEquiv (f : M₁ →ₗ[R] M₁') (g : M₂ →ₗ[R] M₂') :
    homEquiv.symm.toLinearMap ∘ₗ dual (TensorProduct.map f g) ∘ₗ homEquiv.toLinearMap =
      LinearMap.compRight R (dual g) ∘ₗ LinearMap.lcomp R (CharacterModule M₂') f :=
  rfl

end Naturality

section TensorRight

variable (M Q : Type v) [AddCommGroup M] [Module R M] [AddCommGroup Q] [Module R Q]

/-- The adjunction isomorphism `C(M ⊗_R Q) ≅ Hom_R(Q, C(M))`, that is, the isomorphism of the
remark read with the tensor factor on the right. -/
noncomputable def tensorRightHomEquiv :
    CharacterModule (M ⊗[R] Q) ≃ₗ[R] (Q →ₗ[R] CharacterModule M) :=
  (CharacterModule.congr (TensorProduct.comm R M Q)).trans homEquiv.symm

variable {M Q}

/-- `tensorRightHomEquiv M Q χ` sends `q` to the character `m ↦ χ (m ⊗ q)`. -/
@[simp]
theorem tensorRightHomEquiv_apply_apply (χ : CharacterModule (M ⊗[R] Q)) (q : Q) (m : M) :
    tensorRightHomEquiv M Q χ q m = χ (m ⊗ₜ[R] q) := by
  simp only [tensorRightHomEquiv, LinearEquiv.trans_apply]
  rfl

/-- The inverse of `tensorRightHomEquiv M Q` sends `ψ` to the character `m ⊗ q ↦ ψ q m`. -/
@[simp]
theorem tensorRightHomEquiv_symm_apply_tmul (ψ : Q →ₗ[R] CharacterModule M) (m : M) (q : Q) :
    (tensorRightHomEquiv M Q).symm ψ (m ⊗ₜ[R] q) = ψ q m := by
  have h := tensorRightHomEquiv_apply_apply ((tensorRightHomEquiv M Q).symm ψ) q m
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

end TensorRight

section SplitCoequalizer

variable {M N P : Type v}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/-- Tensoring with `Q` inside `C`: the map of character modules of the tensor products which
corresponds to `h` under the adjunction `C(- ⊗_R Q) ≅ Hom_R(Q, C(-))`. -/
noncomputable def tensorRightMap (h : CharacterModule M →ₗ[R] CharacterModule N)
    (Q : Type v) [AddCommGroup Q] [Module R Q] :
    CharacterModule (M ⊗[R] Q) →ₗ[R] CharacterModule (N ⊗[R] Q) :=
  (tensorRightHomEquiv N Q).symm.toLinearMap ∘ₗ LinearMap.compRight R h ∘ₗ
    (tensorRightHomEquiv M Q).toLinearMap

variable (Q : Type v) [AddCommGroup Q] [Module R Q]

/-- `tensorRightMap h Q χ` takes `n ⊗ q` to `h (tensorRightHomEquiv M Q χ q) n`. -/
theorem tensorRightMap_apply_tmul (h : CharacterModule M →ₗ[R] CharacterModule N)
    (χ : CharacterModule (M ⊗[R] Q)) (n : N) (q : Q) :
    tensorRightMap h Q χ (n ⊗ₜ[R] q) = h (tensorRightHomEquiv M Q χ q) n := by
  simp [tensorRightMap]

/-- Under `tensorRightHomEquiv`, `tensorRightMap h Q` is postcomposition with `h`. -/
@[simp]
theorem tensorRightHomEquiv_tensorRightMap (h : CharacterModule M →ₗ[R] CharacterModule N)
    (χ : CharacterModule (M ⊗[R] Q)) (q : Q) :
    tensorRightHomEquiv N Q (tensorRightMap h Q χ) q = h (tensorRightHomEquiv M Q χ q) := by
  ext n
  rw [tensorRightHomEquiv_apply_apply, tensorRightMap_apply_tmul]

/-- Maps out of `C(M ⊗_R Q)` into `C(N ⊗_R Q)` agree once they agree on pure tensors. -/
private theorem tensorRightMap_ext
    {f g : CharacterModule (M ⊗[R] Q) →ₗ[R] CharacterModule (N ⊗[R] Q)}
    (H : ∀ χ n q, f χ (n ⊗ₜ[R] q) = g χ (n ⊗ₜ[R] q)) : f = g := by
  ext χ x
  induction x using TensorProduct.inductionOn with
  | tmul n q => exact H χ n q
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- Tensoring with `Q` inside `C` takes the dual of `u` to the dual of `u ⊗ 1_Q`. -/
theorem tensorRightMap_dual (u : N →ₗ[R] M) :
    tensorRightMap (dual u) Q = dual (u.rTensor Q) := by
  refine tensorRightMap_ext Q fun χ n q => ?_
  rw [tensorRightMap_apply_tmul]
  change tensorRightHomEquiv M Q χ q (u n) = χ (u.rTensor Q (n ⊗ₜ[R] q))
  rw [tensorRightHomEquiv_apply_apply, LinearMap.rTensor_tmul]

/-- Tensoring with `Q` inside `C` takes the identity to the identity. -/
theorem tensorRightMap_id :
    tensorRightMap (LinearMap.id : CharacterModule M →ₗ[R] CharacterModule M) Q =
      LinearMap.id :=
  tensorRightMap_ext Q fun χ m q => by
    rw [tensorRightMap_apply_tmul, LinearMap.id_apply, LinearMap.id_apply,
      tensorRightHomEquiv_apply_apply]

/-- Tensoring with `Q` inside `C` takes a composite to the composite of the tensored maps. -/
theorem tensorRightMap_comp (h : CharacterModule M →ₗ[R] CharacterModule N)
    (h' : CharacterModule N →ₗ[R] CharacterModule P) :
    tensorRightMap (h'.comp h) Q = (tensorRightMap h' Q).comp (tensorRightMap h Q) :=
  tensorRightMap_ext Q fun χ p q => by
    rw [tensorRightMap_apply_tmul, LinearMap.comp_apply, LinearMap.comp_apply,
      tensorRightMap_apply_tmul, tensorRightHomEquiv_tensorRightMap]

/-- **Stacks 08WS**, the corollary of the adjunction. If
`C(M) ⇉ C(N) → C(P)` is a split coequalizer diagram of `R`-modules, the arrows being the
character-module duals of `u`, `v : N → M` and `w : P → N`, then so is
`C(M ⊗_R Q) ⇉ C(N ⊗_R Q) → C(P ⊗_R Q)`, for any `R`-module `Q`. -/
@[stacks 08WS "split coequalizers of character modules are preserved by tensoring inside C"]
noncomputable def isSplitCoequalizer_dual_rTensor (u v : N →ₗ[R] M) (w : P →ₗ[R] N)
    (q : IsSplitCoequalizer (ModuleCat.ofHom (dual u)) (ModuleCat.ofHom (dual v))
      (ModuleCat.ofHom (dual w))) :
    IsSplitCoequalizer (ModuleCat.ofHom (dual (u.rTensor Q)))
      (ModuleCat.ofHom (dual (v.rTensor Q))) (ModuleCat.ofHom (dual (w.rTensor Q))) := by
  refine {
    rightSection := ModuleCat.ofHom (tensorRightMap q.rightSection.hom Q)
    leftSection := ModuleCat.ofHom (tensorRightMap q.leftSection.hom Q)
    condition := ?_
    rightSection_π := ?_
    leftSection_bottom := ?_
    leftSection_top := ?_ }
  · apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom]
    have h := congrArg ModuleCat.Hom.hom q.condition
    change (dual w).comp (dual u) = (dual w).comp (dual v) at h
    simpa only [tensorRightMap_comp, tensorRightMap_dual] using
      congrArg (fun k => tensorRightMap k Q) h
  · apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_id]
    have h := congrArg ModuleCat.Hom.hom q.rightSection_π
    change (dual w).comp q.rightSection.hom = LinearMap.id at h
    simpa only [tensorRightMap_comp, tensorRightMap_dual, tensorRightMap_id] using
      congrArg (fun k => tensorRightMap k Q) h
  · apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_id]
    have h := congrArg ModuleCat.Hom.hom q.leftSection_bottom
    change (dual v).comp q.leftSection.hom = LinearMap.id at h
    simpa only [tensorRightMap_comp, tensorRightMap_dual, tensorRightMap_id] using
      congrArg (fun k => tensorRightMap k Q) h
  · apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom]
    have h := congrArg ModuleCat.Hom.hom q.leftSection_top
    change (dual u).comp q.leftSection.hom = q.rightSection.hom.comp (dual w) at h
    simpa only [tensorRightMap_comp, tensorRightMap_dual] using
      congrArg (fun k => tensorRightMap k Q) h

end SplitCoequalizer

end CharacterModule

section Registrations

-- The isomorphism (08WT) of the remark, and the formula displayed for it, are Mathlib's.
add_to_stacks 08WS "adjunction isomorphism" CharacterModule.homEquiv
add_to_sga "5 IIIB 5.2" "5.2.1 with K = B = Z" CharacterModule.homEquiv

add_to_stacks 08WS "the displayed formula for the isomorphism"
  CharacterModule.homEquiv_symm_apply_apply_apply

end Registrations
