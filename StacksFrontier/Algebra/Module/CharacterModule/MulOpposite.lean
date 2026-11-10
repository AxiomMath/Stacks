module

public import StacksFrontier.Algebra.Module.CharacterModule.Duality

/-!
# Character modules over a noncommutative ring

Let `R` be a ring, not necessarily commutative, and `A` a left `R`-module. Its character module
`A^∨ = Hom_ℤ(A, ℚ/ℤ)` (Mathlib's `CharacterModule A`) is a *right* `R`-module,
`(c · r)(a) = c(r • a)`, that is, a left `Rᵐᵒᵖ`-module; dually the character module of a left
`Rᵐᵒᵖ`-module is a left `R`-module. Mathlib equips `A^∨` with an `R`-module structure only for
commutative `R`. This file provides the two module structures for an arbitrary ring, the duals of
linear maps, the evaluation maps into double duals, and the two contravariant functors

`(ModuleCat R)ᵒᵖ ⥤ ModuleCat Rᵐᵒᵖ` and `(ModuleCat Rᵐᵒᵖ)ᵒᵖ ⥤ ModuleCat R`,

and proves that character duality is exact for arbitrary (not necessarily finite) groups.

## Main definitions

* `CharacterModule.MulOppositeAction.moduleMulOpposite` — the `Rᵐᵒᵖ`-module `A^∨` of a left
  `R`-module `A` (a scoped instance).
* `CharacterModule.MulOppositeAction.moduleOfMulOpposite` — the `R`-module `A^∨` of a left
  `Rᵐᵒᵖ`-module `A` (a scoped instance).
* `CharacterModule.dualMulOpposite`, `CharacterModule.dualOfMulOpposite` — `f ↦ (c ↦ c ∘ f)`.
* `CharacterModule.evalMulOpposite`, `CharacterModule.evalOfMulOpposite` — `A → (A^∨)^∨`.
* `CharacterModule.moduleCatDualFunctor`, `CharacterModule.moduleCatDualOfMulOppositeFunctor`.

## Main results

* `CharacterModule.exact_comp_of_exact` — `Hom_ℤ(-, ℚ/ℤ)` is exact, for arbitrary groups.
* `CharacterModule.exact_moduleCatDualFunctor_map`,
  `CharacterModule.exact_moduleCatDualOfMulOppositeFunctor_map`.

## Implementation notes

The instances are scoped (`open scoped CharacterModule.MulOppositeAction`) so that they never
meet Mathlib's instance `Module R (CharacterModule A)` for commutative `R`: for commutative `R`
the double dual of an `R`-module would otherwise carry two `R`-module structures, equal but not
reducibly so.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace CharacterModule

section Exact

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

/-- **Character duality is exact**, for arbitrary abelian groups: if `A → B → C` is exact then
so is `C^∨ → B^∨ → A^∨`. -/
theorem exact_comp_of_exact (f : A →+ B) (g : B →+ C) (h : Function.Exact f g) :
    Function.Exact (fun c : CharacterModule C ↦ (c.comp g : CharacterModule B))
      (fun c : CharacterModule B ↦ (c.comp f : CharacterModule A)) := by
  intro χ
  constructor
  · intro hχ
    let gr : B →+ g.range := g.rangeRestrict
    have hgr : Function.Surjective gr := g.rangeRestrict_surjective
    have hker : gr.ker ≤ (χ : B →+ AddCircle (1 : ℚ)).ker := by
      intro x hx
      rw [AddMonoidHom.mem_ker] at hx ⊢
      obtain ⟨a, rfl⟩ := (h x).mp (congr_arg Subtype.val hx)
      exact DFunLike.congr_fun hχ a
    let χrange : g.range →+ AddCircle (1 : ℚ) :=
      gr.liftOfRightInverse (Function.surjInv hgr) (Function.rightInverse_surjInv hgr) ⟨χ, hker⟩
    obtain ⟨ψ, hψ⟩ :=
      (Module.Baer.of_divisible (AddCircle (1 : ℚ))).extension_property_addMonoidHom
        g.range.subtype Subtype.val_injective χrange
    refine ⟨ψ, ?_⟩
    apply CharacterModule.ext
    intro b
    change ψ (g b) = χ b
    have hext := DFunLike.congr_fun hψ ⟨g b, ⟨b, rfl⟩⟩
    change ψ (g b) = χrange ⟨g b, ⟨b, rfl⟩⟩ at hext
    rw [hext]
    exact AddMonoidHom.liftOfRightInverse_comp_apply gr
      (Function.surjInv hgr) (Function.rightInverse_surjInv hgr) ⟨χ, hker⟩ b
  · rintro ⟨c, rfl⟩
    apply CharacterModule.ext
    intro a
    change c (g (f a)) = 0
    rw [h.apply_apply_eq_zero, map_zero]

/-- **Character duality is exact** for modules over a commutative ring, with Mathlib's
`R`-module structure on characters. -/
theorem exact_dual_of_exact {R : Type u} [CommRing R] [Module R A] [Module R B] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : Function.Exact f g) :
    Function.Exact (dual (R := R) g) (dual (R := R) f) :=
  exact_comp_of_exact f.toAddMonoidHom g.toAddMonoidHom h

/-- Precomposition with a surjective map is injective on characters. -/
theorem comp_injective_of_surjective (f : A →+ B) (hf : Function.Surjective f) :
    Function.Injective (fun c : CharacterModule B ↦ (c.comp f : CharacterModule A)) := by
  intro φ ψ e
  apply CharacterModule.ext
  intro x
  obtain ⟨y, rfl⟩ := hf x
  exact DFunLike.congr_fun e y

/-- Precomposition with an injective map is surjective on characters (`ℚ/ℤ` is divisible). -/
theorem comp_surjective_of_injective (f : A →+ B) (hf : Function.Injective f) :
    Function.Surjective (fun c : CharacterModule B ↦ (c.comp f : CharacterModule A)) :=
  fun c ↦ (Module.Baer.of_divisible (AddCircle (1 : ℚ))).extension_property_addMonoidHom f hf c

end Exact

namespace MulOppositeAction

variable {R : Type u} [Ring R] {A : Type v} [AddCommGroup A]

/-- **The character module of a left `R`-module is a left `Rᵐᵒᵖ`-module**:
`(r • c)(a) = c(r.unop • a)`. -/
scoped instance moduleMulOpposite [Module R A] : Module Rᵐᵒᵖ (CharacterModule A) where
  smul r c := c.comp (DistribSMul.toAddMonoidHom A r.unop)
  one_smul c := AddMonoidHom.ext fun a ↦ congrArg c (one_smul R a)
  mul_smul r s c := AddMonoidHom.ext fun a ↦ congrArg c (mul_smul s.unop r.unop a)
  smul_zero _ := rfl
  smul_add _ _ _ := rfl
  add_smul r s c := AddMonoidHom.ext fun a ↦ by
    change c ((r + s).unop • a) = c (r.unop • a) + c (s.unop • a)
    rw [MulOpposite.unop_add, add_smul, map_add]
  zero_smul c := AddMonoidHom.ext fun a ↦ by
    change c ((0 : Rᵐᵒᵖ).unop • a) = 0
    rw [MulOpposite.unop_zero, zero_smul, map_zero]

/-- **The character module of a left `Rᵐᵒᵖ`-module is a left `R`-module**:
`(r • c)(a) = c(op r • a)`. -/
scoped instance moduleOfMulOpposite [Module Rᵐᵒᵖ A] : Module R (CharacterModule A) where
  smul r c := c.comp (DistribSMul.toAddMonoidHom A (MulOpposite.op r))
  one_smul c := AddMonoidHom.ext fun a ↦ congrArg c (one_smul Rᵐᵒᵖ a)
  mul_smul r s c := AddMonoidHom.ext fun a ↦
    congrArg c (mul_smul (MulOpposite.op s) (MulOpposite.op r) a)
  smul_zero _ := rfl
  smul_add _ _ _ := rfl
  add_smul r s c := AddMonoidHom.ext fun a ↦ by
    change c (MulOpposite.op (r + s) • a) = c (MulOpposite.op r • a) + c (MulOpposite.op s • a)
    rw [MulOpposite.op_add, add_smul, map_add]
  zero_smul c := AddMonoidHom.ext fun a ↦ by
    change c (MulOpposite.op (0 : R) • a) = 0
    rw [MulOpposite.op_zero, zero_smul, map_zero]

/-- For a left `R`-module `A`, `r : Rᵐᵒᵖ` acts on a character by `(r • c)(a) = c(r.unop • a)`. -/
lemma smul_apply_mulOpposite [Module R A] (r : Rᵐᵒᵖ) (c : CharacterModule A) (a : A) :
    (r • c) a = c (r.unop • a) :=
  rfl

/-- For a left `Rᵐᵒᵖ`-module `A`, `r : R` acts on a character by `(r • c)(a) = c(op r • a)`. -/
lemma smul_apply_ofMulOpposite [Module Rᵐᵒᵖ A] (r : R) (c : CharacterModule A) (a : A) :
    (r • c) a = c (MulOpposite.op r • a) :=
  rfl

end MulOppositeAction

open scoped MulOppositeAction

section Linear

variable {R : Type u} [Ring R] {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup C]

/-- **The dual of an `R`-linear map**, `c ↦ c ∘ f`, an `Rᵐᵒᵖ`-linear map. -/
def dualMulOpposite [Module R A] [Module R B] (f : A →ₗ[R] B) :
    CharacterModule B →ₗ[Rᵐᵒᵖ] CharacterModule A where
  toFun c := c.comp f.toAddMonoidHom
  map_add' _ _ := rfl
  map_smul' r c := AddMonoidHom.ext fun a ↦ by
    change c (r.unop • f a) = c (f (r.unop • a))
    rw [f.map_smul]

/-- The dual `dualMulOpposite f` sends a character `c` to `a ↦ c (f a)`. -/
@[simp]
lemma dualMulOpposite_apply [Module R A] [Module R B] (f : A →ₗ[R] B) (c : CharacterModule B)
    (a : A) : dualMulOpposite f c a = c (f a) :=
  rfl

/-- **The dual of an `Rᵐᵒᵖ`-linear map**, `c ↦ c ∘ f`, an `R`-linear map. -/
def dualOfMulOpposite [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ B] (f : A →ₗ[Rᵐᵒᵖ] B) :
    CharacterModule B →ₗ[R] CharacterModule A where
  toFun c := c.comp f.toAddMonoidHom
  map_add' _ _ := rfl
  map_smul' r c := AddMonoidHom.ext fun a ↦ by
    change c (MulOpposite.op r • f a) = c (f (MulOpposite.op r • a))
    rw [f.map_smul]

/-- The dual `dualOfMulOpposite f` sends a character `c` to `a ↦ c (f a)`. -/
@[simp]
lemma dualOfMulOpposite_apply [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ B] (f : A →ₗ[Rᵐᵒᵖ] B)
    (c : CharacterModule B) (a : A) : dualOfMulOpposite f c a = c (f a) :=
  rfl

/-- If `A → B → C` is an exact sequence of left `R`-modules, then the dual sequence
`C^∨ → B^∨ → A^∨` of left `Rᵐᵒᵖ`-modules is exact. -/
lemma exact_dualMulOpposite [Module R A] [Module R B] [Module R C] (f : A →ₗ[R] B)
    (g : B →ₗ[R] C) (h : Function.Exact f g) :
    Function.Exact (dualMulOpposite g) (dualMulOpposite f) :=
  exact_comp_of_exact f.toAddMonoidHom g.toAddMonoidHom h

/-- If `A → B → C` is an exact sequence of left `Rᵐᵒᵖ`-modules, then the dual sequence
`C^∨ → B^∨ → A^∨` of left `R`-modules is exact. -/
lemma exact_dualOfMulOpposite [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ B] [Module Rᵐᵒᵖ C]
    (f : A →ₗ[Rᵐᵒᵖ] B) (g : B →ₗ[Rᵐᵒᵖ] C) (h : Function.Exact f g) :
    Function.Exact (dualOfMulOpposite (R := R) g) (dualOfMulOpposite f) :=
  exact_comp_of_exact f.toAddMonoidHom g.toAddMonoidHom h

/-- **Evaluation into the double dual of a left `R`-module**, `a ↦ (c ↦ c(a))`, `R`-linear. -/
def evalMulOpposite (R : Type u) [Ring R] (A : Type*) [AddCommGroup A] [Module R A] :
    A →ₗ[R] CharacterModule (CharacterModule A) where
  toFun a := AddMonoidHom.eval a
  map_add' a b := AddMonoidHom.ext fun c ↦ map_add c a b
  map_smul' _ _ := rfl

/-- The evaluation `evalMulOpposite R A a` sends a character `c` to `c a`. -/
@[simp]
lemma evalMulOpposite_apply [Module R A] (a : A) (c : CharacterModule A) :
    evalMulOpposite R A a c = c a :=
  rfl

/-- **Evaluation into the double dual of a left `Rᵐᵒᵖ`-module**, `a ↦ (c ↦ c(a))`,
`Rᵐᵒᵖ`-linear. -/
def evalOfMulOpposite (R : Type u) [Ring R] (A : Type*) [AddCommGroup A] [Module Rᵐᵒᵖ A] :
    A →ₗ[Rᵐᵒᵖ] CharacterModule (CharacterModule A) where
  toFun a := AddMonoidHom.eval a
  map_add' a b := AddMonoidHom.ext fun c ↦ map_add c a b
  map_smul' _ _ := rfl

/-- The evaluation `evalOfMulOpposite R A a` sends a character `c` to `c a`. -/
@[simp]
lemma evalOfMulOpposite_apply [Module Rᵐᵒᵖ A] (a : A) (c : CharacterModule A) :
    evalOfMulOpposite R A a c = c a :=
  rfl

end Linear

section Functor

variable (R : Type u) [Ring R]

/-- **The contravariant functor `M ↦ M^∨` from left `R`-modules to left `Rᵐᵒᵖ`-modules**, for a
module universe `w` independent of the universe of `R`. -/
def moduleCatDualFunctor : (ModuleCat.{w} R)ᵒᵖ ⥤ ModuleCat.{w} Rᵐᵒᵖ where
  obj M := ModuleCat.of Rᵐᵒᵖ (CharacterModule (M.unop : Type w))
  map f := ModuleCat.ofHom (dualMulOpposite (ConcreteCategory.hom f.unop))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **The contravariant functor `M ↦ M^∨` from left `Rᵐᵒᵖ`-modules to left `R`-modules.** -/
def moduleCatDualOfMulOppositeFunctor : (ModuleCat.{w} Rᵐᵒᵖ)ᵒᵖ ⥤ ModuleCat.{w} R where
  obj M := ModuleCat.of R (CharacterModule (M.unop : Type w))
  map f := ModuleCat.ofHom (dualOfMulOpposite (ConcreteCategory.hom f.unop))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The functor `moduleCatDualFunctor R` is additive. -/
instance moduleCatDualFunctor_additive : (moduleCatDualFunctor.{u, w} R).Additive where
  map_add {X Y f g} := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro χ
    change CharacterModule (X.unop : Type w) at χ
    apply CharacterModule.ext
    intro x
    change χ ((f + g).unop.hom x) = χ (f.unop.hom x) + χ (g.unop.hom x)
    simp

/-- The functor `moduleCatDualOfMulOppositeFunctor R` is additive. -/
instance moduleCatDualOfMulOppositeFunctor_additive :
    (moduleCatDualOfMulOppositeFunctor.{u, w} R).Additive where
  map_add {X Y f g} := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro χ
    change CharacterModule (X.unop : Type w) at χ
    apply CharacterModule.ext
    intro x
    change χ ((f + g).unop.hom x) = χ (f.unop.hom x) + χ (g.unop.hom x)
    simp

/-- The dual of an exact sequence of left `R`-modules is exact. -/
theorem exact_moduleCatDualFunctor_map {S : ShortComplex (ModuleCat.{w} R)} (hS : S.Exact) :
    (S.op.map (moduleCatDualFunctor R)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
  exact exact_dualMulOpposite S.f.hom S.g.hom hS

/-- The dual of an exact sequence of left `Rᵐᵒᵖ`-modules is exact. -/
theorem exact_moduleCatDualOfMulOppositeFunctor_map {S : ShortComplex (ModuleCat.{w} Rᵐᵒᵖ)}
    (hS : S.Exact) : (S.op.map (moduleCatDualOfMulOppositeFunctor R)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
  exact exact_dualOfMulOpposite S.f.hom S.g.hom hS

/-- The dual of a surjective `R`-linear map is injective, as a statement in `ModuleCat`. -/
theorem mono_moduleCatDualFunctor_map {M N : ModuleCat.{w} R} (f : M ⟶ N) [Epi f] :
    Mono ((moduleCatDualFunctor R).map f.op) := by
  rw [ModuleCat.mono_iff_injective]
  exact comp_injective_of_surjective f.hom.toAddMonoidHom
    ((ModuleCat.epi_iff_surjective f).mp inferInstance)

/-- The dual of an injective `R`-linear map is surjective, as a statement in `ModuleCat`. -/
theorem epi_moduleCatDualFunctor_map {M N : ModuleCat.{w} R} (f : M ⟶ N) [Mono f] :
    Epi ((moduleCatDualFunctor R).map f.op) := by
  rw [ModuleCat.epi_iff_surjective]
  exact comp_surjective_of_injective f.hom.toAddMonoidHom
    ((ModuleCat.mono_iff_injective f).mp inferInstance)

/-- The dual of a surjective `Rᵐᵒᵖ`-linear map is injective, as a statement in `ModuleCat`. -/
theorem mono_moduleCatDualOfMulOppositeFunctor_map {M N : ModuleCat.{w} Rᵐᵒᵖ} (f : M ⟶ N)
    [Epi f] : Mono ((moduleCatDualOfMulOppositeFunctor R).map f.op) := by
  rw [ModuleCat.mono_iff_injective]
  exact comp_injective_of_surjective f.hom.toAddMonoidHom
    ((ModuleCat.epi_iff_surjective f).mp inferInstance)

/-- The dual of an injective `Rᵐᵒᵖ`-linear map is surjective, as a statement in `ModuleCat`. -/
theorem epi_moduleCatDualOfMulOppositeFunctor_map {M N : ModuleCat.{w} Rᵐᵒᵖ} (f : M ⟶ N)
    [Mono f] : Epi ((moduleCatDualOfMulOppositeFunctor R).map f.op) := by
  rw [ModuleCat.epi_iff_surjective]
  exact comp_surjective_of_injective f.hom.toAddMonoidHom
    ((ModuleCat.mono_iff_injective f).mp inferInstance)

end Functor

end CharacterModule

end
