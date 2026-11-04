module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import StacksCore.Algebra.Homology.ShortComplex.ExactFunctor

/-! ## Hom complexes of a short complex of modules

For a short complex `S` of `R`-modules and a module `N`, the short complexes of abelian
groups obtained by applying the preadditive (co)yoneda functors are, up to the identification
of `ModuleCat` morphisms with linear maps, the complexes of `R`-linear maps

* `Hom(N, S.X₁) → Hom(N, S.X₂) → Hom(N, S.X₃)`, given by post-composition
  (`LinearMap.compRight`), and
* `Hom(S.X₃, N) → Hom(S.X₂, N) → Hom(S.X₁, N)`, given by pre-composition
  (`LinearMap.lcomp`).

The lemmas below express monomorphy and exactness of those short complexes in terms of
`Function.Injective` and `Function.Exact` of the corresponding linear maps. They are the
translation layer used to deduce the module statement of Stacks tag 0582 from the abelian
category statement of tag 05AA.

Since `R` is not assumed commutative, the hom-groups are only additive groups; the
composition maps are therefore taken `ℕ`-linear.
-/

@[expose] public section

universe u v

open CategoryTheory Limits Opposite ModuleCat

namespace CategoryTheory.ShortComplex

variable {R : Type u} [Ring R] (S : ShortComplex (ModuleCat.{v} R)) (N : ModuleCat.{v} R)

-- The `map_homLeft`/`map_homRight` equations hold by `rfl`, but the stricter isDefEq
-- transparency means their patterns are no longer found by `rw`; the definitional
-- equalities are supplied by type ascription instead, and `set_option` lets the
-- elaborator unfold the hom-group carriers when checking them.
set_option backward.isDefEq.respectTransparency.types false in
lemma moduleCat_mono_map_preadditiveCoyoneda_iff :
    Mono (S.map (preadditiveCoyoneda.obj (Opposite.op N))).f ↔
      Function.Injective (LinearMap.compRight (M := N) ℕ S.f.hom) := by
  rw [AddCommGrpCat.mono_iff_injective]
  constructor
  · intro h φ₁ φ₂ hφ
    exact ModuleCat.hom_ext_iff.1 (h (a₁ := ModuleCat.ofHom φ₁) (a₂ := ModuleCat.ofHom φ₂)
      (show ModuleCat.ofHom φ₁ ≫ S.f = ModuleCat.ofHom φ₂ ≫ S.f from ModuleCat.hom_ext hφ))
  · intro h φ₁ φ₂ hφ
    have hφ' : φ₁ ≫ S.f = φ₂ ≫ S.f := hφ
    exact ModuleCat.hom_ext (h (ModuleCat.hom_ext_iff.1 hφ'))

set_option backward.isDefEq.respectTransparency.types false in
lemma moduleCat_exact_map_preadditiveCoyoneda_iff :
    (S.map (preadditiveCoyoneda.obj (Opposite.op N))).Exact ↔
      Function.Exact (LinearMap.compRight (M := N) ℕ S.f.hom)
        (LinearMap.compRight (M := N) ℕ S.g.hom) := by
  rw [ShortComplex.ab_exact_iff]
  refine ⟨fun h ↦ Function.Exact.of_comp_of_mem_range (by ext; simp) fun ψ hψ ↦ ?_, fun h ψ hψ ↦ ?_⟩
  · obtain ⟨φ, hφ⟩ := h (ModuleCat.ofHom ψ)
      (show ModuleCat.ofHom ψ ≫ S.g = 0 from ModuleCat.hom_ext hψ)
    have hφ' : φ ≫ S.f = ModuleCat.ofHom ψ := hφ
    exact ⟨φ.hom, ModuleCat.hom_ext_iff.1 hφ'⟩
  · have hψ' : ψ ≫ S.g = 0 := hψ
    obtain ⟨φ, hφ⟩ := (h ψ.hom).1 (ModuleCat.hom_ext_iff.1 hψ')
    exact ⟨ModuleCat.ofHom φ, show ModuleCat.ofHom φ ≫ S.f = ψ from ModuleCat.hom_ext hφ⟩

set_option backward.isDefEq.respectTransparency.types false in
lemma moduleCat_mono_op_map_preadditiveYoneda_iff :
    Mono (S.op.map (preadditiveYoneda.obj N)).f ↔
      Function.Injective (LinearMap.lcomp ℕ N S.g.hom) := by
  rw [AddCommGrpCat.mono_iff_injective]
  refine ⟨fun h φ₁ φ₂ hφ ↦ ModuleCat.hom_ext_iff.1 <| h ?_, fun h φ₁ φ₂ hφ ↦ ?_⟩
  · exact show S.g ≫ ModuleCat.ofHom φ₁ = S.g ≫ ModuleCat.ofHom φ₂ from ModuleCat.hom_ext hφ
  · have hφ' : S.g ≫ φ₁ = S.g ≫ φ₂ := hφ
    exact ModuleCat.hom_ext (h (ModuleCat.hom_ext_iff.1 hφ'))

set_option backward.isDefEq.respectTransparency.types false in
lemma moduleCat_exact_op_map_preadditiveYoneda_iff :
    (S.op.map (preadditiveYoneda.obj N)).Exact ↔
      Function.Exact (LinearMap.lcomp ℕ N S.g.hom) (LinearMap.lcomp ℕ N S.f.hom) := by
  rw [ShortComplex.ab_exact_iff]
  refine ⟨fun h ↦ Function.Exact.of_comp_of_mem_range (by ext; simp) fun ψ hψ ↦ ?_, fun h ψ hψ ↦ ?_⟩
  · obtain ⟨φ, hφ⟩ := h (ModuleCat.ofHom ψ)
      (show S.f ≫ ModuleCat.ofHom ψ = 0 from ModuleCat.hom_ext hψ)
    have hφ' : S.g ≫ φ = ModuleCat.ofHom ψ := hφ
    exact ⟨φ.hom, ModuleCat.hom_ext_iff.1 hφ'⟩
  · have hψ' : S.f ≫ ψ = 0 := hψ
    obtain ⟨φ, hφ⟩ := (h ψ.hom).1 (ModuleCat.hom_ext_iff.1 hψ')
    exact ⟨ModuleCat.ofHom φ, show S.g ≫ ModuleCat.ofHom φ = ψ from ModuleCat.hom_ext hφ⟩

end CategoryTheory.ShortComplex
