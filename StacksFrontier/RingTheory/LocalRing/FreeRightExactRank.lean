module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.OrzechProperty
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Ranks along a right exact sequence of finite free modules over a local ring

Let `C` be a local ring and `M₁ --f--> M₀ --g--> F ⟶ 0` a right exact sequence of `C`-modules
with `M₁` and `M₀` finite free of ranks `c` and `d`.

* If `F` is projective and `f` is injective, then `F` is free and `c + rank F = d`.
* If `F` is free of rank `n` with `c + n = d`, then `f` is injective.

These are the rank computations behind the smoothness criterion of [Stacks, Tag 0E9Z].
-/

@[expose] public section

open Module

namespace Function.Exact

variable {C M₁ M₀ F : Type*} [CommRing C] [IsLocalRing C] [AddCommGroup M₁] [Module C M₁]
  [AddCommGroup M₀] [Module C M₀] [AddCommGroup F] [Module C F]
  {f : M₁ →ₗ[C] M₀} {g : M₀ →ₗ[C] F}

section Instances

variable [Module.Free C M₁] [Module.Finite C M₁] [Module.Free C M₀] [Module.Finite C M₀]

omit [Module.Free C M₀] in
/-- **A projective cokernel of an injection of finite free modules over a local ring is free, and
ranks add up.** -/
theorem free_and_finrank_add_of_injective (h : Function.Exact f g) (hg : Surjective g)
    (hf : Injective f) [Module.Projective C F] :
    Module.Free C F ∧ finrank C M₁ + finrank C F = finrank C M₀ := by
  obtain ⟨l, hl⟩ := Module.projective_lifting_property g LinearMap.id hg
  let e : M₀ ≃ₗ[C] M₁ × F := (h.splitSurjectiveEquiv hf ⟨l, hl⟩).1
  have : Module.Finite C F := Module.Finite.of_surjective g hg
  have : Module.Free C F := Module.free_of_flat_of_isLocalRing
  exact ⟨inferInstance, by rw [← Module.finrank_prod, e.finrank_eq]⟩

/-- **An exact sequence `M₁ ⟶ M₀ ⟶ F ⟶ 0` of finite free modules over a local ring whose ranks
add up starts with an injection.** -/
theorem injective_of_finrank_add (h : Function.Exact f g) (hg : Surjective g)
    [Module.Free C F] [Module.Finite C F]
    (hrank : finrank C M₁ + finrank C F = finrank C M₀) : Injective f := by
  obtain ⟨l, hl⟩ := Module.projective_lifting_property g LinearMap.id hg
  let K := LinearMap.ker g
  let e : M₀ ≃ₗ[C] K × F :=
    ((LinearMap.exact_subtype_ker_map g).splitSurjectiveEquiv K.injective_subtype ⟨l, hl⟩).1
  have : Module.Projective C (K × F) := Module.Projective.of_equiv e
  have : Module.Projective C K := Module.Projective.of_split (LinearMap.inl C K F)
    (LinearMap.fst C K F) (LinearMap.fst_comp_inl C K F)
  have : Module.Finite C K :=
    Module.Finite.of_surjective (LinearMap.fst C K F ∘ₗ e.toLinearMap)
      (fun k => ⟨e.symm (k, 0), by simp⟩)
  have : Module.Free C K := Module.free_of_flat_of_isLocalRing
  have hKrank : finrank C K = finrank C M₁ := by
    have := e.finrank_eq
    rw [Module.finrank_prod] at this
    omega
  let f' : M₁ →ₗ[C] K := f.codRestrict K h.apply_apply_eq_zero
  have hf' : Surjective f' := by
    rintro ⟨k, hk⟩
    obtain ⟨x, hx⟩ := (h k).1 hk
    exact ⟨x, Subtype.ext hx⟩
  let eK : K ≃ₗ[C] M₁ := LinearEquiv.ofFinrankEq K M₁ hKrank
  have hinj : Injective (eK.toLinearMap ∘ₗ f') :=
    OrzechProperty.injective_of_surjective_endomorphism _ (eK.surjective.comp hf')
  exact fun x y hxy => hinj (congrArg eK (Subtype.ext hxy : f' x = f' y))

end Instances

/-- `Function.Exact.free_and_finrank_add_of_injective` with the two finite free modules given by
bases: the cokernel is free of rank `d - c` and `c ≤ d`. -/
theorem nonempty_basis_of_injective {c d : ℕ} (b₁ : Module.Basis (Fin c) C M₁)
    (b₀ : Module.Basis (Fin d) C M₀) (h : Function.Exact f g) (hg : Surjective g)
    (hf : Injective f) (hF : Module.Projective C F) :
    c ≤ d ∧ Nonempty (Module.Basis (Fin (d - c)) C F) := by
  have := Module.Free.of_basis b₁
  have := Module.Finite.of_basis b₁
  have := Module.Free.of_basis b₀
  have := Module.Finite.of_basis b₀
  obtain ⟨hfree, hrank⟩ := h.free_and_finrank_add_of_injective hg hf
  have : Module.Finite C F := Module.Finite.of_surjective g hg
  rw [Module.finrank_eq_card_basis b₁, Module.finrank_eq_card_basis b₀, Fintype.card_fin,
    Fintype.card_fin] at hrank
  exact ⟨by omega, ⟨Module.finBasisOfFinrankEq _ _ (by omega)⟩⟩

/-- `Function.Exact.injective_of_finrank_add` with the three finite free modules given by bases
of ranks `c`, `d` and `d - c`, `c ≤ d`. -/
theorem injective_of_basis {c d : ℕ} (b₁ : Module.Basis (Fin c) C M₁)
    (b₀ : Module.Basis (Fin d) C M₀) (bF : Module.Basis (Fin (d - c)) C F) (hcd : c ≤ d)
    (h : Function.Exact f g) (hg : Surjective g) : Injective f := by
  have := Module.Free.of_basis b₁
  have := Module.Finite.of_basis b₁
  have := Module.Free.of_basis b₀
  have := Module.Finite.of_basis b₀
  have := Module.Free.of_basis bF
  have := Module.Finite.of_basis bF
  refine h.injective_of_finrank_add hg ?_
  rw [Module.finrank_eq_card_basis b₁, Module.finrank_eq_card_basis b₀,
    Module.finrank_eq_card_basis bF]
  simp only [Fintype.card_fin]
  omega

end Function.Exact
