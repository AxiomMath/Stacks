module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.CharacterModule
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import StacksCore.Tactic.StacksAttribute

/-!
# Character duality on modules

Let `R` be a commutative ring. Sending an `R`-module `M` to its character module
`M^∨ = Hom_ℤ(M, ℚ/ℤ)`, with the `R`-action `(r • φ)(x) = φ(r • x)`, is a contravariant functor
on `R`-modules. This functor is exact, and the evaluation map `M → (M^∨)^∨` is injective. Here
`ℚ/ℤ` is `AddCircle (1 : ℚ)` and `M^∨` is `CharacterModule M`.

## Main definitions

* `CharacterModule.dualFunctor`: the contravariant functor `M ↦ M^∨` on `R`-modules.
* `CharacterModule.evalₗ`: the evaluation map `M → (M^∨)^∨`, as an `R`-linear map.

## Main results

* `CharacterModule.dual_exact`: character duality turns an exact pair of linear maps into an
  exact pair.
* `CharacterModule.dualFunctor_exact`: `CharacterModule.dualFunctor` is an exact functor.
* `CharacterModule.eval_injective`: evaluation `M → (M^∨)^∨` is injective.
* `CharacterModule.evalₗ_injective`: the `R`-linear evaluation `M → (M^∨)^∨` is injective.
* `CharacterModule.evalₗ_naturality`: evaluation is natural in `M`.

## References

* [Stacks Project, Tag 01D9](https://stacks.math.columbia.edu/tag/01D9)
* [Stacks Project, Tag 01DA](https://stacks.math.columbia.edu/tag/01DA)
* [Stacks Project, Tag 01DB](https://stacks.math.columbia.edu/tag/01DB)
* [Stacks Project, Tag 08WQ](https://stacks.math.columbia.edu/tag/08WQ)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CharacterModule

/-- Character duality fixes the identity: `(id_M)^∨ = id_{M^∨}`. -/
theorem dual_id (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] :
    dual (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  ext
  rfl

/-- The contravariant functor `M ↦ M^∨ = Hom_ℤ(M, ℚ/ℤ)` on modules over a commutative ring,
acting on a linear map by precomposition (`CharacterModule.dual`). -/
@[stacks 01D9 "the contravariant functor `M ↦ M^∨`", stacks 08WQ]
noncomputable def dualFunctor (R : Type u) [CommRing R] :
    (ModuleCat.{u} R)ᵒᵖ ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (CharacterModule (M.unop : Type u))
  map f := ModuleCat.ofHom (dual (ConcreteCategory.hom f.unop))
  map_id M := by
    apply ModuleCat.hom_ext
    ext c x
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    ext c x
    rfl

/-- `CharacterModule.dualFunctor` sends `M` to its character module `M^∨`. -/
@[simp]
theorem dualFunctor_obj (R : Type u) [CommRing R] (M : (ModuleCat.{u} R)ᵒᵖ) :
    (dualFunctor R).obj M = ModuleCat.of R (CharacterModule (M.unop : Type u)) :=
  rfl

/-- `CharacterModule.dualFunctor` sends a linear map `f` to its dual `f^∨`. -/
@[simp]
theorem dualFunctor_map {R : Type u} [CommRing R] {M N : (ModuleCat.{u} R)ᵒᵖ} (f : M ⟶ N) :
    (dualFunctor R).map f = ModuleCat.ofHom (dual f.unop.hom) :=
  rfl

/-- On underlying linear maps, `CharacterModule.dualFunctor` acts by `CharacterModule.dual`,
that is, by precomposition of characters. -/
theorem dualFunctor_map_hom {R : Type u} [CommRing R] {M N : (ModuleCat.{u} R)ᵒᵖ}
    (f : M ⟶ N) : ((dualFunctor R).map f).hom = dual f.unop.hom :=
  rfl

/-- Character duality is exact on linear maps: if `f` and `g` are exact then so are their
duals, in the opposite order. -/
theorem dual_exact {R : Type u} [CommRing R]
    {A B C : Type u} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : Function.Exact f g) :
    Function.Exact (dual (R := R) g) (dual (R := R) f) := by
  rw [LinearMap.exact_iff]
  apply le_antisymm
  · intro χ hχ
    rw [LinearMap.mem_ker] at hχ
    let gr : B →+ LinearMap.range g := g.toAddMonoidHom.rangeRestrict
    have hgr : Function.Surjective gr := AddMonoidHom.rangeRestrict_surjective _
    have hker : gr.ker ≤ χ.ker := fun x hx ↦ by
      obtain ⟨a, rfl⟩ := (h x).mp (congr_arg Subtype.val (AddMonoidHom.mem_ker.mp hx))
      exact DFunLike.congr_fun hχ a
    let χrange : LinearMap.range g →+ AddCircle (1 : ℚ) :=
      gr.liftOfRightInverse (Function.surjInv hgr)
        (Function.rightInverse_surjInv hgr) ⟨χ, hker⟩
    obtain ⟨ψ, hψ⟩ :=
      (Module.Baer.of_divisible (AddCircle (1 : ℚ))).extension_property_addMonoidHom
        (LinearMap.range g).subtype.toAddMonoidHom
        (Submodule.injective_subtype (LinearMap.range g)) χrange
    refine ⟨ψ, DFunLike.ext _ _ fun b ↦ (DFunLike.congr_fun hψ ⟨g b, b, rfl⟩).trans ?_⟩
    exact gr.liftOfRightInverse_comp_apply (Function.surjInv hgr)
      (Function.rightInverse_surjInv hgr) ⟨χ, hker⟩ b
  · rintro ψ ⟨χ, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← dual_comp, h.linearMap_comp_eq_zero,
      dual_zero, LinearMap.zero_apply]

/-- The contravariant character-dual functor on modules over a commutative ring is exact. -/
@[stacks 01DA]
theorem dualFunctor_exact (R : Type u) [CommRing R] :
    exactFunctor (ModuleCat.{u} R)ᵒᵖ (ModuleCat.{u} R) (dualFunctor R) := by
  have : (dualFunctor R).Additive :=
    { map_add := by
        intro X Y f g
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro χ
        apply CharacterModule.ext
        intro x
        change CharacterModule (X.unop : Type u) at χ
        show χ ((f + g).unop x) = χ (f.unop x) + χ (g.unop x)
        simp }
  apply (Functor.exact_tfae (dualFunctor R)).out 2 4 |>.mp
  intro S hS
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  exact dual_exact S.unop.f.hom S.unop.g.hom
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S.unop).mp hS.unop)

/-- The canonical evaluation map from an additive commutative group into its double character
module is injective. -/
@[stacks 01DB]
theorem eval_injective (M : Type u) [AddCommGroup M] :
    Function.Injective (AddMonoidHom.eval : M →+ CharacterModule (CharacterModule M)) :=
  (injective_iff_map_eq_zero _).mpr fun _ hx ↦
    eq_zero_of_character_apply fun c ↦ DFunLike.congr_fun hx c

/-- The evaluation map `ev : M → (M^∨)^∨`, `x ↦ (φ ↦ φ x)`, as an `R`-linear map. -/
noncomputable def evalₗ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] :
    M →ₗ[R] CharacterModule (CharacterModule M) where
  toFun x := AddMonoidHom.eval x
  map_add' x y := DFunLike.ext _ _ fun φ ↦ map_add φ x y
  map_smul' _ _ := DFunLike.ext _ _ fun _ ↦ rfl

/-- The evaluation map sends `x` to the character `φ ↦ φ x`. -/
@[simp]
theorem evalₗ_apply {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (x : M) (φ : CharacterModule M) : evalₗ R M x φ = φ x :=
  rfl

/-- Evaluation into the double character module is injective; the `R`-linear form of
`CharacterModule.eval_injective`. -/
theorem evalₗ_injective (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] :
    Function.Injective (evalₗ R M) :=
  fun _ _ h => eval_injective M h

/-- Evaluation is natural: `ev_N ∘ f = (f^∨)^∨ ∘ ev_M` for a linear map `f : M → N`. -/
theorem evalₗ_naturality {R : Type u} [CommRing R] {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    (evalₗ R N).comp f = (dual (dual f)).comp (evalₗ R M) := by
  ext x φ
  rfl

end CharacterModule

end
