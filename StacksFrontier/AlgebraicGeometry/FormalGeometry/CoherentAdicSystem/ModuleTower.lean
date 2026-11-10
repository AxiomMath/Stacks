module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import StacksFrontier.RingTheory.AdicCompletion.Basic
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.AdicCompletion.InverseLimit
public import StacksFrontier.RingTheory.AdicCompletion.QuotPow
public import StacksFrontier.RingTheory.AdicCompletion.Noetherian
public import StacksFrontier.RingTheory.AdicCompletion.Finiteness
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Towers of modules whose transitions are the ideal-power quotients

Let `A` be a commutative ring and `I ⊆ A` an ideal. This file studies a tower `(T n)` of
`A`-modules whose transition `T (n+1) ⟶ T n` is surjective with kernel `I ^ (n+1) T (n+1)`, and
the categorical limit of the corresponding functor `ℕᵒᵖ ⥤ ModuleCat A`. The conclusions are those
of Stacks 09B8, transported from the bundled `Stacks.AdicCompletion.InverseLimit.InverseSystem` to
  the two shapes that
the coherent-adic-system comparison of Stacks 087W needs: the submodule of compatible families in
`∀ n, T n`, and the limit of a functor out of `ℕᵒᵖ`.

For finitely generated `I` the limit is `I`-adically complete, its projection to level `n` is
surjective with kernel `I ^ (n+1)` times the limit, and a morphism between two such limits is
induced by a (unique up to the projections) morphism of towers.

In the other direction, a finite module over the completion `A^∧` gives such a tower by reducing
modulo the powers of `I`, and the limit of that tower recovers the module.

## Main definitions

* `Stacks.Coherent.moduleTowerLimit` — the submodule of compatible families in `∀ n, T n`.
* `Stacks.Coherent.moduleTowerLimitProj` — its projection to level `n`.
* `Stacks.Coherent.moduleLimitTowerEquiv` — the categorical limit of `F : ℕᵒᵖ ⥤ ModuleCat A`
  identified with `moduleTowerLimit`.
* `Stacks.Coherent.completionModuleReductionTower` — the tower `n ↦ N / I ^ (n+1) N` of a finite
  module `N` over `AdicCompletion I A`.

## Main results

* `Stacks.Coherent.moduleLimit_projection_surjective` and
  `Stacks.Coherent.moduleLimit_projection_ker` — the limit projections are surjective with kernel
  the ideal-power multiple.
* `Stacks.Coherent.moduleLimit_isAdicComplete` — the limit is `I`-adically complete.
* `Stacks.Coherent.exists_natTrans_of_limitHom` — a map between two such limits comes from a map
  of towers.
* `Stacks.Coherent.completionModuleReductionLimitEquiv` — the limit of the reduction tower of a
  finite `A^∧`-module is that module.
* `Stacks.Coherent.coherentAdicCompletionOfFiniteReduction`, stated as
  `Stacks.Coherent.finite_adicCompletion_of_finite_reduction` — the completion of a module with
  finite reduction modulo `I` is a finite `A^∧`-module.

## Implementation notes

`Stacks.AdicCompletion.InverseLimit.InverseSystem` indexes its modules so that `ker (π n) = I ^ n M
  (n+1)`, whereas a
coherent adic system has `ker` the `(n+1)`-st power; `shiftModuleTower` inserts a zero module at
level `0` to absorb the shift, and `shiftModuleTowerLimitEquiv` identifies the two limits. Nothing
below depends on which of the two indexings is used downstream.

The results about `limit F` for `F : ℕᵒᵖ ⥤ ModuleCat A` are obtained from the ones about
`moduleTowerLimit` by transporting along `moduleLimitTowerEquiv`, whose construction is the only
place where the concrete description of limits in `ModuleCat` (compatible families, shrunk to the
right universe) is used.

These are statements of commutative algebra and belong morally in `StacksFrontier/RingTheory/`; they
are collected here because the only consumer is the comparison of Stacks 087W and that tree is
owned elsewhere.

## References

* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
* [Stacks Project, Tag 09B8](https://stacks.math.columbia.edu/tag/09B8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Coherent

/-- An `I`-adically complete module is its own `I`-adic completion. -/
public noncomputable def completeModuleEquivAdicCompletion
    {A : Type u} [CommRing A] (I : Ideal A) {M : Type u} [AddCommGroup M]
    [Module A M] [IsAdicComplete I M] : M ≃ₗ[A] AdicCompletion I M :=
  LinearEquiv.ofBijective (AdicCompletion.of I M) (AdicCompletion.of_bijective I M)

/-- A tower `(T n)` with `ker (t n) = I ^ (n+1) T (n+1)`, as an inverse system in the sense of
Stacks 09B8: a zero module is inserted at level `0` to absorb the index shift. -/
public noncomputable def shiftModuleTower
    {A : Type u} [CommRing A] {I : Ideal A}
    (T : ℕ → Type u) [∀ n, AddCommGroup (T n)] [∀ n, Module A (T n)]
    (t : ∀ n, T (n + 1) →ₗ[A] T n)
    (hsurj : ∀ n, Function.Surjective (t n))
    (hker : ∀ n, LinearMap.ker (t n) = I ^ (n + 1) • (⊤ : Submodule A (T (n + 1)))) :
    Stacks.AdicCompletion.InverseLimit.InverseSystem I where
  M := fun
    | 0 => Fin 0 → A
    | n + 1 => T n
  addCommGroup n := by cases n <;> infer_instance
  module n := by cases n <;> infer_instance
  π := fun
    | 0 => 0
    | n + 1 => t n
  surjective n := by
    cases n with
    | zero => intro x; exact ⟨0, Subsingleton.elim _ _⟩
    | succ k => exact hsurj k
  ker_π n := by
    cases n with
    | zero => simp
    | succ k => exact hker k

/-- The limit of a tower of modules: the compatible families in the product. -/
public def moduleTowerLimit
    {A : Type u} [CommRing A] (T : ℕ → Type u)
    [∀ n, AddCommGroup (T n)] [∀ n, Module A (T n)]
    (t : ∀ n, T (n + 1) →ₗ[A] T n) : Submodule A (∀ n, T n) where
  carrier := {x | ∀ n, t n (x (n + 1)) = x n}
  add_mem' := by intro x y hx hy n; simp [hx n, hy n]
  zero_mem' := by intro n; simp
  smul_mem' := by intro a x hx n; simp [hx n]

/-- The limit of the shifted inverse system is the limit of the tower. -/
public noncomputable def shiftModuleTowerLimitEquiv
    {A : Type u} [CommRing A] {I : Ideal A}
    (T : ℕ → Type u) [∀ n, AddCommGroup (T n)] [∀ n, Module A (T n)]
    (t : ∀ n, T (n + 1) →ₗ[A] T n)
    (hsurj : ∀ n, Function.Surjective (t n))
    (hker : ∀ n, LinearMap.ker (t n) = I ^ (n + 1) • (⊤ : Submodule A (T (n + 1)))) :
    (shiftModuleTower T t hsurj hker).limit ≃ₗ[A] moduleTowerLimit T t := by
  let S := shiftModuleTower T t hsurj hker
  let f : S.limit →ₗ[A] moduleTowerLimit T t := {
    toFun := fun x => ⟨fun n => x.1 (n + 1), fun n => by
      change t n (x.1 (n + 1 + 1)) = x.1 (n + 1)
      exact x.2 (n + 1)⟩
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  let g : moduleTowerLimit T t →ₗ[A] S.limit := {
    toFun := fun x => ⟨(fun n => Nat.casesOn n (0 : Fin 0 → A) (fun k => x.1 k)), by
      intro n
      cases n with
      | zero => funext i; exact Fin.elim0 i
      | succ k => exact x.2 k⟩
    map_add' := by
      intro x y
      apply Subtype.ext
      funext n
      cases n with
      | zero => funext i; exact Fin.elim0 i
      | succ k => rfl
    map_smul' := by
      intro a x
      apply Subtype.ext
      funext n
      cases n with
      | zero => funext i; exact Fin.elim0 i
      | succ k => rfl }
  exact LinearEquiv.ofLinearMap f g (LinearMap.ext fun _ => rfl) (by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext n
    cases n with
    | zero =>
        change (g (f x)).1 0 = x.1 0
        change (0 : Fin 0 → A) = x.1 0
        funext i
        exact Fin.elim0 i
    | succ k => rfl)

/-- The projection of the limit of a tower onto its `n`-th term. -/
public noncomputable def moduleTowerLimitProj
    {A : Type u} [CommRing A] {T : ℕ → Type u}
    [∀ n, AddCommGroup (T n)] [∀ n, Module A (T n)]
    (t : ∀ n, T (n + 1) →ₗ[A] T n) (n : ℕ) :
    moduleTowerLimit T t →ₗ[A] T n where
  toFun x := x.1 n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The projection from the limit of a tower of surjections is surjective. -/
public theorem moduleTowerLimitProj_surjective
    {A : Type u} [CommRing A] {I : Ideal A}
    (T : ℕ → Type u) [∀ n, AddCommGroup (T n)] [∀ n, Module A (T n)]
    (t : ∀ n, T (n + 1) →ₗ[A] T n)
    (hsurj : ∀ n, Function.Surjective (t n))
    (hker : ∀ n, LinearMap.ker (t n) =
      I ^ (n + 1) • (⊤ : Submodule A (T (n + 1)))) (n : ℕ) :
    Function.Surjective (moduleTowerLimitProj (t := t) n) := by
  intro y
  obtain ⟨x, hx⟩ := (shiftModuleTower T t hsurj hker).proj_surjective (n + 1) y
  exact ⟨shiftModuleTowerLimitEquiv T t hsurj hker x, hx⟩

/-- The image of `J • ⊤` under a surjection is `J • ⊤`. -/
public theorem map_smul_top_local
    {A : Type u} [CommRing A] {M N : Type u} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (J : Ideal A) (f : M →ₗ[A] N)
    (hf : Function.Surjective f) :
    Submodule.map f (J • (⊤ : Submodule A M)) = J • (⊤ : Submodule A N) := by
  rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hf]

/-- The kernel of the projection from the limit of a tower onto its `n`-th term is the
`(n+1)`-st ideal-power multiple of the limit. -/
public theorem moduleTowerLimitProj_ker
    {A : Type u} [CommRing A] {I : Ideal A}
    (T : ℕ → Type u) [∀ n, AddCommGroup (T n)] [∀ n, Module A (T n)]
    (t : ∀ n, T (n + 1) →ₗ[A] T n)
    (hsurj : ∀ n, Function.Surjective (t n))
    (hker : ∀ n, LinearMap.ker (t n) =
      I ^ (n + 1) • (⊤ : Submodule A (T (n + 1))))
    (hI : I.FG) (n : ℕ) :
    LinearMap.ker (moduleTowerLimitProj (t := t) n) =
      I ^ (n + 1) • (⊤ : Submodule A (moduleTowerLimit T t)) := by
  let S := shiftModuleTower T t hsurj hker
  let e := shiftModuleTowerLimitEquiv T t hsurj hker
  have hbridge (y : S.limit) :
      moduleTowerLimitProj (t := t) n (e y) = S.proj (n + 1) y := rfl
  apply le_antisymm
  · intro x hx
    have hx' : e.symm x ∈ I ^ (n + 1) • (⊤ : Submodule A S.limit) := by
      rwa [← S.ker_proj hI (n + 1), LinearMap.mem_ker, ← hbridge, e.apply_symm_apply]
    simpa using Submodule.smul_top_le_comap_smul_top (I ^ (n + 1)) e.toLinearMap hx'
  · intro x hx
    have hzero : I ^ (n + 1) • (⊤ : Submodule A (T n)) = ⊥ := by
      rw [← map_smul_top_local (I ^ (n + 1)) (t n) (hsurj n), ← hker n, eq_bot_iff,
        Submodule.map_le_iff_le_comap, Submodule.comap_bot]
    have hp : moduleTowerLimitProj (t := t) n x ∈
        I ^ (n + 1) • (⊤ : Submodule A (T n)) :=
      Submodule.smul_top_le_comap_smul_top _ _ hx
    apply LinearMap.mem_ker.mpr
    simpa [hzero] using hp

/-- `IsAdicComplete` transports along a linear equivalence. -/
private theorem isAdicComplete_of_linearEquiv_aux
    {A : Type u} [CommRing A] (I : Ideal A) {M N : Type u} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (e : N ≃ₗ[A] M) (hadic : IsAdicComplete I M) :
    IsAdicComplete I N := by
  let c := AdicCompletion.congr I e
  apply AdicCompletion.of_bijective_iff.mp
  constructor
  · intro x y hxy
    have hxy' := congrArg c hxy
    have hxy'' : AdicCompletion.of I M (e x) = AdicCompletion.of I M (e y) := by
      simpa [c, AdicCompletion.congr_apply, AdicCompletion.map_of] using hxy'
    exact e.injective ((AdicCompletion.of_bijective I M).1 hxy'')
  · intro y
    obtain ⟨x, hx⟩ := (AdicCompletion.of_bijective I M).2 (c y)
    refine ⟨e.symm x, ?_⟩
    apply c.injective
    simp [c, AdicCompletion.congr_apply, AdicCompletion.map_of, hx]

/-- The limit of a tower with surjective transitions and ideal-power kernels is `I`-adically
complete. -/
public theorem moduleTowerLimit_isAdicComplete
    {A : Type u} [CommRing A] {I : Ideal A}
    (T : ℕ → Type u) [∀ n, AddCommGroup (T n)] [∀ n, Module A (T n)]
    (t : ∀ n, T (n + 1) →ₗ[A] T n)
    (hsurj : ∀ n, Function.Surjective (t n))
    (hker : ∀ n, LinearMap.ker (t n) =
      I ^ (n + 1) • (⊤ : Submodule A (T (n + 1))))
    (hI : I.FG) : IsAdicComplete I (moduleTowerLimit T t) := by
  let S := shiftModuleTower T t hsurj hker
  let e := shiftModuleTowerLimitEquiv T t hsurj hker
  exact isAdicComplete_of_linearEquiv_aux I e.symm (S.isAdicComplete hI)

/-- Precomposing with a linear equivalence transports the kernel description. -/
public theorem ker_comp_linearEquiv_pow_smul_top
    {A : Type u} [CommRing A] {M N P : Type u}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [AddCommGroup P] [Module A P] (J : Ideal A)
    (e : M ≃ₗ[A] N) (f : N →ₗ[A] P)
    (hker : LinearMap.ker f = J • (⊤ : Submodule A N)) :
    LinearMap.ker (f.comp e.toLinearMap) = J • (⊤ : Submodule A M) := by
  rw [LinearMap.ker_comp, hker,
    ← map_smul_top_local J e.toLinearMap e.surjective]
  exact Submodule.comap_map_eq_self (by simp)

/-- A compatible family over `ℕᵒᵖ` is determined by its successive transitions: the value at `m`
is the image of the value at any `k ≥ m`. -/
public theorem functorNat_map_sections
    {A : Type u} [CommRing A] (F : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (x : ∀ n : ℕ, F.obj (op n))
    (hx : ∀ n, (F.map (homOfLE (Nat.le_succ n)).op) (x (n + 1)) = x n)
    {m k : ℕ} (h : m ≤ k) : (F.map (homOfLE h).op) (x k) = x m := by
  induction k with
  | zero =>
      obtain rfl : m = 0 := by omega
      simp
  | succ k ih =>
      by_cases hmk : m ≤ k
      · calc
          (F.map (homOfLE h).op) (x (k + 1)) =
              (F.map (homOfLE hmk).op)
                ((F.map (homOfLE (Nat.le_succ k)).op) (x (k + 1))) := by
            rw [show (homOfLE h).op = (homOfLE (Nat.le_succ k)).op ≫ (homOfLE hmk).op from
              Subsingleton.elim _ _, Functor.map_comp]
            rfl
          _ = x m := by rw [hx k, ih hmk]
      · obtain rfl : m = k + 1 := by omega
        rw [show (homOfLE h).op = 𝟙 (op (k + 1)) from Subsingleton.elim _ _]
        simp

/-- A compatible family of elements of `F.obj (op n)` as a section of `F ⋙ forget`. -/
public def functorNatSection
    {A : Type u} [CommRing A] (F : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (x : ∀ n : ℕ, F.obj (op n))
    (hx : ∀ n, (F.map (homOfLE (Nat.le_succ n)).op) (x (n + 1)) = x n) :
    (F ⋙ forget (ModuleCat A)).sections :=
  ⟨fun i => x i.unop, by
    rintro ⟨i⟩ ⟨j⟩ f
    rw [show f = (homOfLE (leOfHom f.unop)).op from Subsingleton.elim _ _]
    exact functorNat_map_sections F x hx (leOfHom f.unop)⟩

/-- The value at level `n` of the limit element produced by a compatible family. -/
public theorem limit_lift_functorNatSection_π
    {A : Type u} [CommRing A] (F : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (x : ∀ n : ℕ, F.obj (op n))
    (hx : ∀ n, (F.map (homOfLE (Nat.le_succ n)).op) (x (n + 1)) = x n) (n : ℕ) :
    (limit.π F (op n)).hom
        ((limit.lift F (ModuleCat.HasLimits.limitCone F)).hom
          (equivShrink (F ⋙ forget (ModuleCat A)).sections (functorNatSection F x hx))) =
      x n := by
  let s := functorNatSection F x hx
  let sh := equivShrink (F ⋙ forget (ModuleCat A)).sections s
  let c : Cone F := ModuleCat.HasLimits.limitCone F
  have hs : (c.π.app (op n)).hom sh = x n := by
    change ModuleCat.limitπLinearMap F (op n) sh = x n
    change ((equivShrink (F ⋙ forget (ModuleCat A)).sections).symm
      (equivShrink (F ⋙ forget (ModuleCat A)).sections s)).val (op n) = x n
    rw [Equiv.symm_apply_apply]
    rfl
  have hp := congrArg (fun g => g.hom sh) (limit.lift_π c (op n))
  change (limit.π F (op n)).hom ((limit.lift F c).hom sh) =
    (c.π.app (op n)).hom sh at hp
  exact hp.trans hs

/-- The projection from the limit of an inverse system of modules indexed by `ℕᵒᵖ` with
surjective transitions is surjective. -/
public theorem moduleLimit_projection_surjective
    {A : Type u} [CommRing A] (F : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hsurj : ∀ n : ℕ, Function.Surjective
      (((F.map (homOfLE (Nat.le_succ n)).op).hom))) (n : ℕ) :
    Function.Surjective ((limit.π F (op n)).hom) := by
  let T : ℕ → Type u := fun k => (F.obj (op k))
  let t : ∀ k, T (k + 1) →ₗ[A] T k :=
    fun k => (F.map (homOfLE (Nat.le_succ k)).op).hom
  intro y
  obtain ⟨x, hx⟩ := invLimit.proj_surjective T t hsurj n y
  exact ⟨_, limit_lift_functorNatSection_π F x.1 x.2 n |>.trans hx⟩

/-- The map from the categorical limit of `F : ℕᵒᵖ ⥤ ModuleCat A` to the module of compatible
families, given by the limit projections. -/
public def moduleLimitTowerMap
    {A : Type u} [CommRing A] (F : ℕᵒᵖ ⥤ ModuleCat.{u} A) :
    (limit F : ModuleCat.{u} A) →ₗ[A]
      moduleTowerLimit (fun n => F.obj (op n))
        (fun n => (F.map (homOfLE (Nat.le_succ n)).op).hom) where
  toFun x := ⟨fun n => (limit.π F (op n)).hom x, fun n =>
    congrArg (fun f => f.hom x) (limit.w F (homOfLE (Nat.le_succ n)).op)⟩
  map_add' := by intro x y; apply Subtype.ext; funext n; simp
  map_smul' := by intro a x; apply Subtype.ext; funext n; simp

/-- The categorical limit of `F : ℕᵒᵖ ⥤ ModuleCat A` is the module of compatible families. -/
public noncomputable def moduleLimitTowerEquiv
    {A : Type u} [CommRing A] (F : ℕᵒᵖ ⥤ ModuleCat.{u} A) :
    (limit F : ModuleCat.{u} A) ≃ₗ[A]
      moduleTowerLimit (fun n => F.obj (op n))
        (fun n => (F.map (homOfLE (Nat.le_succ n)).op).hom) :=
  LinearEquiv.ofBijective (moduleLimitTowerMap F) ⟨by
      intro x y hxy
      apply Concrete.limit_ext F x y
      intro j
      exact congrArg (fun z => z.1 j.unop) hxy, by
      intro y
      refine ⟨(limit.lift F (ModuleCat.HasLimits.limitCone F)).hom
        (equivShrink (F ⋙ forget (ModuleCat A)).sections (functorNatSection F y.1 y.2)), ?_⟩
      apply Subtype.ext
      funext n
      exact limit_lift_functorNatSection_π F y.1 y.2 n⟩

/-- The components of `moduleLimitTowerEquiv` are the limit projections. -/
public theorem moduleLimitTowerEquiv_apply_coe
    {A : Type u} [CommRing A] (F : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (x : (limit F : ModuleCat.{u} A)) (n : ℕ) :
    ((moduleLimitTowerEquiv F) x).1 n = (limit.π F (op n)).hom x := rfl

/-- The kernel of the projection from the limit onto level `n` is the `(n+1)`-st ideal-power
multiple of the limit. -/
public theorem moduleLimit_projection_ker
    {A : Type u} [CommRing A] {I : Ideal A}
    (F : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hsurj : ∀ n, Function.Surjective
      ((F.map (homOfLE (Nat.le_succ n)).op).hom))
    (hker : ∀ n, LinearMap.ker
      ((F.map (homOfLE (Nat.le_succ n)).op).hom) =
        I ^ (n + 1) • (⊤ : Submodule A (F.obj (op (n + 1)))))
    (hI : I.FG) (n : ℕ) :
    LinearMap.ker ((limit.π F (op n)).hom) =
      I ^ (n + 1) • (⊤ : Submodule A (limit F : ModuleCat.{u} A)) := by
  let T : ℕ → Type u := fun k => F.obj (op k)
  let t : ∀ k, T (k + 1) →ₗ[A] T k :=
    fun k => (F.map (homOfLE (Nat.le_succ k)).op).hom
  let e := moduleLimitTowerEquiv F
  have hcomp : (moduleTowerLimitProj (t := t) n).comp e.toLinearMap =
      (limit.π F (op n)).hom :=
    LinearMap.ext fun x => moduleLimitTowerEquiv_apply_coe F x n
  rw [← hcomp]
  exact ker_comp_linearEquiv_pow_smul_top (I ^ (n + 1)) e
    (moduleTowerLimitProj (t := t) n)
    (moduleTowerLimitProj_ker T t hsurj hker hI n)

/-- If the bottom of the tower is a finite module then so is the reduction of the limit
modulo `I`. -/
public theorem moduleLimit_zeroQuotient_finite
    {A : Type u} [CommRing A] {I : Ideal A}
    (F : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hsurj : ∀ n, Function.Surjective
      ((F.map (homOfLE (Nat.le_succ n)).op).hom))
    (hker : ∀ n, LinearMap.ker
      ((F.map (homOfLE (Nat.le_succ n)).op).hom) =
        I ^ (n + 1) • (⊤ : Submodule A (F.obj (op (n + 1)))))
    (hI : I.FG) (hfin : Module.Finite A (F.obj (op 0))) :
    Module.Finite A ((limit F : ModuleCat A) ⧸
      (I • (⊤ : Submodule A (limit F : ModuleCat A)))) := by
  let p := (limit.π F (op 0)).hom
  have hp : Function.Surjective p := moduleLimit_projection_surjective F hsurj 0
  have hk : LinearMap.ker p = I • (⊤ : Submodule A (limit F : ModuleCat A)) := by
    simpa using moduleLimit_projection_ker F hsurj hker hI 0
  let e : ((limit F : ModuleCat A) ⧸
      (I • (⊤ : Submodule A (limit F : ModuleCat A)))) ≃ₗ[A] F.obj (op 0) :=
    (Submodule.quotEquivOfEq _ _ hk.symm).trans (p.quotKerEquivOfSurjective hp)
  exact hfin.equiv e.symm

/-- The limit of a tower of modules over `ℕᵒᵖ` with surjective transitions and ideal-power
kernels is `I`-adically complete. -/
public theorem moduleLimit_isAdicComplete
    {A : Type u} [CommRing A] {I : Ideal A}
    (F : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hsurj : ∀ n, Function.Surjective
      ((F.map (homOfLE (Nat.le_succ n)).op).hom))
    (hker : ∀ n, LinearMap.ker
      ((F.map (homOfLE (Nat.le_succ n)).op).hom) =
        I ^ (n + 1) • (⊤ : Submodule A (F.obj (op (n + 1)))))
    (hI : I.FG) : IsAdicComplete I (limit F : ModuleCat A) := by
  let T : ℕ → Type u := fun n => F.obj (op n)
  let t : ∀ n, T (n + 1) →ₗ[A] T n :=
    fun n => (F.map (homOfLE (Nat.le_succ n)).op).hom
  let e := moduleLimitTowerEquiv F
  have hadic : IsAdicComplete I (moduleTowerLimit T t) :=
    moduleTowerLimit_isAdicComplete T t hsurj hker hI
  exact isAdicComplete_of_linearEquiv_aux I e hadic

/-- **`IsAdicComplete` transports along a linear equivalence.** The same conjugation-by-`congr`
argument as `Stacks.Coherent.moduleLimit_isAdicComplete`, stated for an arbitrary pair of
modules identified by a `LinearEquiv` instead of for the specific tower limit and its
`moduleTowerLimit` model. -/
public theorem isAdicComplete_of_linearEquiv
    {A : Type u} [CommRing A] (I : Ideal A) {M N : Type u} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (e : N ≃ₗ[A] M) (hadic : IsAdicComplete I M) :
    IsAdicComplete I N := by
  exact isAdicComplete_of_linearEquiv_aux I e hadic

/-- A surjection factors any map killing its kernel. -/
public theorem exists_desc_of_ker_le
    {R : Type u} [CommRing R] {M N P : ModuleCat.{u} R}
    (p : M ⟶ N) (q : M ⟶ P) (hp : Function.Surjective p.hom)
    (hk : LinearMap.ker p.hom ≤ LinearMap.ker q.hom) :
    ∃ f : N ⟶ P, p ≫ f = q := by
  let e := p.hom.quotKerEquivOfSurjective hp
  let f := (LinearMap.ker p.hom).liftQ q.hom hk
  refine ⟨ModuleCat.ofHom (f.comp e.symm.toLinearMap), ?_⟩
  ext x
  change f (e.symm (e (Submodule.Quotient.mk x))) = q.hom x
  rw [e.symm_apply_apply]
  rfl

/-- A morphism between two limits whose projections are surjective with ideal-power kernels is
induced by a morphism of the diagrams. -/
public theorem exists_natTrans_of_limitHom
    {R : Type u} [CommRing R] (I : Ideal R)
    (F G : ℕᵒᵖ ⥤ ModuleCat.{u} R)
    (hs : ∀ n, Function.Surjective (limit.π F (op n)).hom)
    (hF : ∀ n, LinearMap.ker (limit.π F (op n)).hom =
      I ^ (n + 1) • (⊤ : Submodule R (limit F : ModuleCat R)))
    (hG : ∀ n, LinearMap.ker (limit.π G (op n)).hom =
      I ^ (n + 1) • (⊤ : Submodule R (limit G : ModuleCat R)))
    (l : limit F ⟶ limit G) : ∃ τ : F ⟶ G, limMap τ = l := by
  have hd (n : ℕᵒᵖ) : ∃ f : F.obj n ⟶ G.obj n,
      limit.π F n ≫ f = l ≫ limit.π G n := by
    apply exists_desc_of_ker_le _ _ (hs n.unop)
    change LinearMap.ker (limit.π F (op n.unop)).hom ≤
      LinearMap.ker ((limit.π G (op n.unop)).hom.comp l.hom)
    rw [hF, LinearMap.ker_comp, hG]
    exact Submodule.smul_top_le_comap_smul_top _ _
  choose φ hφ using hd
  have hepi (n : ℕᵒᵖ) : Epi (limit.π F n) :=
    (ModuleCat.epi_iff_surjective _).mpr (hs n.unop)
  let τ : F ⟶ G := {
    app := φ
    naturality := fun i j a => by
      apply (cancel_epi (limit.π F i)).mp
      calc
        limit.π F i ≫ F.map a ≫ φ j = limit.π F j ≫ φ j := by simp
        _ = l ≫ limit.π G j := hφ j
        _ = (l ≫ limit.π G i) ≫ G.map a := by simp
        _ = limit.π F i ≫ φ i ≫ G.map a := by rw [← hφ i, Category.assoc]
  }
  exact ⟨τ, limit.hom_ext fun n => by simpa [τ] using hφ n⟩

/-- Finiteness of the reduction modulo `I` passes to the base change along `R ⟶ A`. -/
public theorem finite_quotient_map_smul_top_local
    {R A N : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    (I : Ideal R)
    (h : Module.Finite R (N ⧸ (I • (⊤ : Submodule R N)))) :
    Module.Finite (A ⧸ I.map (algebraMap R A))
      (N ⧸ (I.map (algebraMap R A) • (⊤ : Submodule A N))) := by
  have hres : Module.Finite R
      (N ⧸ ((I.map (algebraMap R A) • (⊤ : Submodule A N)).restrictScalars R)) := by
    rwa [Submodule.restrictScalars_map_smul_eq, Submodule.restrictScalars_top]
  have _ := hres.equiv (Submodule.Quotient.restrictScalarsEquiv R _)
  have _ := Module.Finite.of_restrictScalars_finite R A
    (N ⧸ (I.map (algebraMap R A) • (⊤ : Submodule A N)))
  exact Module.Finite.of_restrictScalars_finite A (A ⧸ I.map (algebraMap R A)) _

/-- A module whose reduction modulo `I` is finite has finite `I`-adic completion over the
completed ring. -/
@[ega "0 7.2.12" "special case"]
public theorem finite_adicCompletion_of_finite_reduction
    {R : Type u} [CommRing R] {I : Ideal R} (hI : I.FG)
    (M : Type u) [AddCommGroup M] [Module R M]
    (hfib : Module.Finite R (M ⧸ (I • (⊤ : Submodule R M)))) :
    Module.Finite (AdicCompletion I R) (AdicCompletion I M) := by
  have hpre : IsPrecomplete (I.map (algebraMap R (AdicCompletion I R)))
      (AdicCompletion I R) :=
    (AdicCompletion.isAdicComplete_self I hI).toIsPrecomplete
  have e := AdicCompletion.quotPowSMulTopEquiv hI M 1
  rw [pow_one] at e
  exact Module.Finite.of_iInf_pow_smul_top_eq_bot_of_finite_quotient_smul_top _
    (IsHausdorff.map_algebraMap_iff.mpr
      (AdicCompletion.instIsHausdorff I M)).iInf_pow_smul
    (finite_quotient_map_smul_top_local I (hfib.equiv e.symm))

/-- A finite module over a Noetherian `I`-adically complete ring is `I`-adically complete. -/
@[ega "IV 18.5.16" "more general"]
public theorem finiteModule_isAdicComplete
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    [IsAdicComplete I R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsAdicComplete I M :=
  isAdicComplete_of_iInf_smul_eq_bot I
    (Ideal.iInf_pow_smul_eq_bot_of_le_jacobson I (IsAdicComplete.le_jacobson_bot I))

/-- A finite module over the `I`-adic completion of a Noetherian ring is `I`-adically complete
as a module over the ring itself. -/
public theorem finiteCompletionModule_isAdicComplete
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : I.FG)
    (M : Type u) [AddCommGroup M] [Module (AdicCompletion I A) M]
    [Module.Finite (AdicCompletion I A) M]
    [Module A M] [IsScalarTower A (AdicCompletion I A) M] :
    IsAdicComplete I M := by
  let J := I.map (algebraMap A (AdicCompletion I A))
  have hR : IsAdicComplete J (AdicCompletion I A) :=
    AdicCompletion.isAdicComplete_self I hI
  exact (IsAdicComplete.map_algebraMap_iff I M).mp (finiteModule_isAdicComplete J M)

/-- An element of the completion is approximated modulo `I ^ n` by an element of the ring. -/
public theorem completion_exists_approximation {A : Type u} [CommRing A]
    (I : Ideal A) (hI : I.FG) (r : AdicCompletion I A) (n : ℕ) :
    ∃ a : A, r - algebraMap A (AdicCompletion I A) a ∈
      I ^ n • (⊤ : Submodule A (AdicCompletion I A)) := by
  obtain ⟨a, ha⟩ := (I ^ n • (⊤ : Submodule A A)).mkQ_surjective
    (AdicCompletion.eval I A n r)
  refine ⟨a, ?_⟩
  rw [AdicCompletion.pow_smul_top_eq_ker_eval hI]
  change AdicCompletion.eval I A n (r - AdicCompletion.of I A a) = 0
  rw [map_sub, AdicCompletion.eval_of, ha, sub_self]

/-- Scaling by an element of the completion and by one of its approximations agree modulo
`I ^ n`. -/
public theorem completion_smul_difference_mem {A : Type u} [CommRing A]
    (I : Ideal A) {M : Type u} [AddCommGroup M]
    [Module (AdicCompletion I A) M] [Module A M]
    [IsScalarTower A (AdicCompletion I A) M]
    {r : AdicCompletion I A} {a : A} {n : ℕ}
    (h : r - algebraMap A (AdicCompletion I A) a ∈
      I ^ n • (⊤ : Submodule A (AdicCompletion I A))) (x : M) :
    r • x - a • x ∈ I ^ n • (⊤ : Submodule A M) := by
  let f := (LinearMap.toSpanSingleton (AdicCompletion I A) M x).restrictScalars A
  have hf : f (r - algebraMap A (AdicCompletion I A) a) ∈
      I ^ n • (⊤ : Submodule A M) :=
    Submodule.smul_top_le_comap_smul_top (I ^ n) f h
  simpa [f, sub_smul, IsScalarTower.algebraMap_smul] using hf

/-- An `A`-linear map between modules over the completion, with Hausdorff target, is linear over
the completion. -/
public theorem completion_linearMap_smul {A : Type u} [CommRing A]
    (I : Ideal A) (hI : I.FG)
    {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module (AdicCompletion I A) M] [Module (AdicCompletion I A) N]
    [Module A M] [Module A N]
    [IsScalarTower A (AdicCompletion I A) M]
    [IsScalarTower A (AdicCompletion I A) N] [IsHausdorff I N]
    (f : M →ₗ[A] N) (r : AdicCompletion I A) (x : M) : f (r • x) = r • f x := by
  apply (IsHausdorff.eq_iff_smodEq (I := I)).mpr
  intro n
  obtain ⟨a, ha⟩ := completion_exists_approximation I hI r n
  have hm := completion_smul_difference_mem I ha x
  have hn := completion_smul_difference_mem I ha (f x)
  have hfm : f (r • x) - a • f x ∈ I ^ n • (⊤ : Submodule A N) := by
    simpa using Submodule.smul_top_le_comap_smul_top (I ^ n) f hm
  rw [SModEq.sub_mem]
  convert (I ^ n • (⊤ : Submodule A N)).sub_mem hfm hn using 1
  abel

/-- The reduction modulo `I ^ n` of a finite module over the completion is a finite
`A`-module. -/
public theorem completion_quotient_finite {A : Type u} [CommRing A]
    (I : Ideal A) (hI : I.FG)
    (M : Type u) [AddCommGroup M] [Module (AdicCompletion I A) M]
    [Module.Finite (AdicCompletion I A) M]
    [Module A M] [IsScalarTower A (AdicCompletion I A) M] (n : ℕ) :
    Module.Finite A (M ⧸ (I ^ n • (⊤ : Submodule A M))) := by
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := AdicCompletion I A) (M := M)
  let q := (I ^ n • (⊤ : Submodule A M)).mkQ
  let P := Submodule.span A (Set.range (fun i => q (s i)))
  have hP : P = ⊤ := by
    apply top_unique
    rintro x -
    obtain ⟨y, rfl⟩ := (I ^ n • (⊤ : Submodule A M)).mkQ_surjective x
    have hy : y ∈ Submodule.span (AdicCompletion I A) (Set.range s) := by rw [hs]; trivial
    induction hy using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨i, rfl⟩ := hz
        exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add z w hz hw iz iw => simpa using P.add_mem iz iw
    | smul r z hz iz =>
        obtain ⟨a, ha⟩ := completion_exists_approximation I hI r n
        have hq : q (r • z) = a • q z := by
          rw [← map_smul, ← sub_eq_zero, ← map_sub]
          exact (Submodule.Quotient.mk_eq_zero _).mpr (completion_smul_difference_mem I ha z)
        rw [hq]
        exact P.smul_mem a iz
  exact ⟨hP ▸ Submodule.fg_span (Set.finite_range _)⟩

/-- The `n`-th reduction `N / I ^ (n+1) N` of a finite module over the completion.

Reducible, so that instance search sees through it to the quotient module; the ideal-power
multiples of the quotient are compared with those of the module itself throughout. -/
public noncomputable abbrev completionModuleReduction
    {A : Type u} [CommRing A] (I : Ideal A)
    (N : FGModuleCat.{u} (AdicCompletion I A)) (n : ℕ) : ModuleCat.{u} A :=
  ModuleCat.of A
    (((ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).obj N.obj) ⧸
      (I ^ (n + 1) • (⊤ : Submodule A
        ((ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).obj N.obj))))

/-- The transition of the reduction tower. -/
public noncomputable def completionModuleReductionMap
    {A : Type u} [CommRing A] (I : Ideal A)
    (N : FGModuleCat.{u} (AdicCompletion I A)) (n : ℕ) :
    completionModuleReduction I N (n + 1) ⟶ completionModuleReduction I N n := by
  let R := AdicCompletion I A
  let M : ModuleCat A := (ModuleCat.restrictScalars (algebraMap A R)).obj N.obj
  change ModuleCat.of A (M ⧸ (I ^ (n + 2) • (⊤ : Submodule A M))) ⟶
    ModuleCat.of A (M ⧸ (I ^ (n + 1) • (⊤ : Submodule A M)))
  have h : I ^ (n + 2) • (⊤ : Submodule A M) ≤
      (I ^ (n + 1) • (⊤ : Submodule A M)).comap
        (LinearMap.id : M →ₗ[A] M) := by
    simpa using (Submodule.pow_smul_top_le I M (by omega : n + 1 ≤ n + 2))
  exact ModuleCat.ofHom
    ((I ^ (n + 2) • (⊤ : Submodule A M)).mapQ
      (I ^ (n + 1) • (⊤ : Submodule A M)) LinearMap.id h)

/-- The tower `n ↦ N / I ^ (n+1) N` of reductions of a finite module over the completion. -/
public noncomputable def completionModuleReductionTower
    {A : Type u} [CommRing A] (I : Ideal A)
    (N : FGModuleCat.{u} (AdicCompletion I A)) : ℕᵒᵖ ⥤ ModuleCat.{u} A :=
  Functor.ofOpSequence (X := fun n => completionModuleReduction I N n)
    (fun n => completionModuleReductionMap I N n)

/-- The transitions of the reduction tower are surjective. -/
public theorem completionModuleReductionMap_surjective
    {A : Type u} [CommRing A] (I : Ideal A)
    (N : FGModuleCat.{u} (AdicCompletion I A)) (n : ℕ) :
    Function.Surjective (completionModuleReductionMap I N n).hom := by
  let M := (ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).obj N.obj
  intro y
  obtain ⟨x, rfl⟩ := (I ^ (n + 1) • (⊤ : Submodule A M)).mkQ_surjective y
  exact ⟨Submodule.Quotient.mk x, rfl⟩

/-- The kernel of a transition of the reduction tower is the corresponding ideal-power
multiple. -/
public theorem completionModuleReductionMap_ker
    {A : Type u} [CommRing A] (I : Ideal A)
    (N : FGModuleCat.{u} (AdicCompletion I A)) (n : ℕ) :
    LinearMap.ker (completionModuleReductionMap I N n).hom =
      I ^ (n + 1) • (⊤ : Submodule A (completionModuleReduction I N (n + 1))) := by
  let M := (ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).obj N.obj
  let q := (I ^ (n + 2) • (⊤ : Submodule A M)).mkQ
  let t := (completionModuleReductionMap I N n).hom
  have hq : Function.Surjective q := Submodule.mkQ_surjective _
  have htx (x : M) : t (q x) = (I ^ (n + 1) • (⊤ : Submodule A M)).mkQ x := rfl
  have hker : LinearMap.ker t = Submodule.map q (I ^ (n + 1) • (⊤ : Submodule A M)) := by
    apply le_antisymm
    · intro z hz
      obtain ⟨x, rfl⟩ := hq z
      exact Submodule.mem_map_of_mem <| (Submodule.Quotient.mk_eq_zero _).mp ((htx x).symm.trans hz)
    · rintro z ⟨x, hx, rfl⟩
      exact (htx x).trans ((Submodule.Quotient.mk_eq_zero _).mpr hx)
  rw [hker, map_smul_top_local _ q hq]

/-- The limit of the reduction tower of a finite module over the completion is that module. -/
@[sga "7 VI 5.5" "special case"]
public noncomputable def completionModuleReductionLimitEquiv
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (N : FGModuleCat.{u} (AdicCompletion I A)) :
    (limit (completionModuleReductionTower I N) : ModuleCat.{u} A) ≃ₗ[A]
      (ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).obj N.obj := by
  let M := (ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).obj N.obj
  letI : Module.Finite (AdicCompletion I A) M := N.property
  letI : IsScalarTower A (AdicCompletion I A) M := ⟨fun a r x => by
    change (algebraMap A (AdicCompletion I A) a * r) • x =
      algebraMap A (AdicCompletion I A) a • (r • x)
    exact mul_smul _ _ _⟩
  have hcomplete : IsAdicComplete I M := finiteCompletionModule_isAdicComplete I
    I.fg_of_isNoetherianRing M
  let T := completionModuleReductionTower I N
  let p (n : ℕ) : (limit T : ModuleCat A) →ₗ[A]
      (M ⧸ (I ^ (n + 1) • (⊤ : Submodule A M))) :=
    (limit.π T (op n)).hom
  have hp : ∀ n, (Submodule.factorPow I M (Nat.succ_le_succ (Nat.le_succ n))).comp
      (p (n + 1)) = p n := by
    intro n
    have hh := congrArg ModuleCat.Hom.hom (limit.w T (homOfLE (Nat.le_succ n)).op)
    rw [show T.map (homOfLE (Nat.le_succ n)).op = completionModuleReductionMap I N n from
      Functor.ofOpSequence_map_homOfLE_succ _ n] at hh
    exact hh
  have hstrict : StrictMono (fun n : ℕ => n + 1) := fun _ _ h => Nat.succ_lt_succ h
  let l := IsAdicComplete.StrictMono.lift I hstrict p (fun {n} => hp n)
  have hl (n : ℕ) (x : (limit T : ModuleCat A)) :
      (I ^ (n + 1) • (⊤ : Submodule A M)).mkQ (l x) = p n x :=
    IsAdicComplete.StrictMono.mk_lift I hstrict p (fun {n} => hp n) x
  have hinj : Function.Injective l := by
    intro x y hxy
    apply Concrete.limit_ext T x y
    intro n
    change p n.unop x = p n.unop y
    rw [← hl, ← hl, hxy]
  have hsurj : Function.Surjective l := by
    intro y
    let e := moduleLimitTowerEquiv T
    let s : moduleTowerLimit (fun n => T.obj (op n))
        (fun n => (T.map (homOfLE (Nat.le_succ n)).op).hom) := ⟨
      fun n => (I ^ (n + 1) • (⊤ : Submodule A M)).mkQ y, by
        intro n
        change (T.map (homOfLE (Nat.le_succ n)).op).hom _ = _
        simp only [T, completionModuleReductionTower, Functor.ofOpSequence_map_homOfLE_succ]
        rfl⟩
    refine ⟨e.symm s, ?_⟩
    have hfun := IsHausdorff.StrictMono.funext I hstrict
      (f := fun _ : Unit => l (e.symm s)) (g := fun _ => y) (fun n _ => ?_)
    · exact congrFun hfun ()
    · change (I ^ (n + 1) • (⊤ : Submodule A M)).mkQ (l (e.symm s)) = _
      rw [hl]
      exact congrArg (fun z => z.val n) (e.apply_symm_apply s)
  exact LinearEquiv.ofBijective l ⟨hinj, hsurj⟩

end Stacks.Coherent

end
