module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.Reduction
public import Mathlib.CategoryTheory.Abelian.Exact
public import StacksCore.Tactic.StacksAttribute

/-!
# Ideal powers in the limit of an adic inverse system

Let `X` be a scheme, `I` a quasi-coherent ideal sheaf of finite type on `X` and `(F_n)` an adic
inverse system of quasi-coherent modules with limit `F = lim F_n`. The subsheaf `I^n F` of the
limit is the limit of the subsheaves `I^n F_m`: a morphism `T ⟶ F` factors through `I^n F`
exactly when each of its projections `T ⟶ F_m`, for `m` large enough, factors through
`I^n F_m`.

## Main definitions

* `Stacks.Algebraization.factorThroughTop` — the factorization of a morphism through the top
  subsheaf of its target.

## Main results

* `Stacks.Algebraization.idealPowerMultiple_le_sheafSubmoduleComap` — a morphism carries `I^n M`
  into any subsheaf of the target containing `I^n N`.
* `Stacks.Algebraization.idealPowerMultiple_zero` — `I⁰ M = M`.
* `Stacks.Algebraization.comp_sheafBot_ι_eq_zero` — a morphism factoring through the zero
  subsheaf is zero.
* `Stacks.Algebraization.AdicInverseSystem.idealPowerMultiple_eq_bot` — `I^(k+1)` annihilates
  the `k`-th term of the system.
* `Stacks.Algebraization.AdicInverseSystem.idealPowerMultiple_limit` — the limit description of
  `I^n F`.

## Implementation notes

The system is zero-indexed, so the source's condition `m ≥ n` on the index of the term reads
`n ≤ m + 1` here. Only one projection is ever needed: once `n = k + 1`, the term `F_k` already
has `I^(k+1) F_k = 0`, so a morphism whose projection to `F_k` lands in `I^(k+1) F_k` has
vanishing projection to `F_k`, and therefore factors through the kernel of that projection,
which is `I^(k+1) F` by `exists_idealPowerQuotientIso`. The other direction is functoriality
of `I^n`.

Comparison of two subsheaves is stated through the preimage subsheaf
`AlgebraicGeometry.sheafSubmoduleComap` and the induced morphism
`AlgebraicGeometry.sheafSubmoduleMap`.

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf` and the two
presentations carry separately declared category instances, so a rewrite under a composite that
mixes them is not type-correct at the transparency `rw` builds its motive at; several proofs
below are therefore written as explicit `Category.assoc` and `congrArg` chains. For the same
reason the equalities whose right-hand side is a zero morphism carry an explicit type ascription
naming the category.

## References

* [Stacks Project, Tag 0EI8](https://stacks.math.columbia.edu/tag/0EI8)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

/-! ### Bridging instances for the scalar action on sections

The module structure on sections is declared over `X.ringCatSheaf.obj.obj U` in
`Mathlib.Algebra.Category.ModuleCat.Sheaf` and over `Γ(X, U)` in
`Mathlib.AlgebraicGeometry.Modules.Sheaf`, and instance search cannot cross the `TopCat.Sheaf`
definition to see that the two agree. The bridging instances are stated once in
`Completion.IdealPowerQuasicoherent` and re-enabled here. -/

attribute [local instance] sectionsModuleΓ sectionsModuleΓSheaf
  sectionsModuleRingCatSheaf monoSubmoduleι

/-- A morphism of sheaves of modules carries `I ^ n M` into any subsheaf of the target
containing `I ^ n N`. -/
public lemma idealPowerMultiple_le_sheafSubmoduleComap {X : Scheme.{u}} (I : X.IdealSheafData)
    (n : ℕ) {M N : X.Modules} (f : M ⟶ N) (Q : N.Submodule)
    (hq : idealPowerMultiple I n N ≤ Q) :
    idealPowerMultiple I n M ≤ AlgebraicGeometry.sheafSubmoduleComap f Q := by
  refine (idealPowerMultiple_le_iff I n M _).2 fun U => ?_
  have hqU : I.ideal U ^ n • (⊤ : Submodule Γ(X, U) Γ(N, U)) ≤ Q.toSubmodule.obj (op U.1) :=
    (idealPowerMultiple_le_iff I n N Q).mp hq U
  exact (Submodule.smul_top_le_comap_smul_top (I.ideal U ^ n)
    (ModuleCat.Hom.hom (f.val.app (op U.1)))).trans (Submodule.comap_mono hqU)

/-- The zeroth ideal-power multiple of `M` is all of `M`. -/
public lemma idealPowerMultiple_zero {X : Scheme.{u}} (I : X.IdealSheafData) (M : X.Modules) :
    idealPowerMultiple I 0 M = ⊤ := by
  refine AlgebraicGeometry.sheafSubmodule_eq_top_of_affine _ fun U => ?_
  simpa using (idealPowerMultiple_le_iff I 0 M (idealPowerMultiple I 0 M)).mp le_rfl U

/-- A morphism factoring through the zero subsheaf of `M` is the zero morphism. -/
public lemma comp_sheafBot_ι_eq_zero {X : Scheme.{u}} {M T : X.Modules}
    (g : T ⟶ (⊥ : M.Submodule).toSheafOfModules) :
    g ≫ (⊥ : M.Submodule).ι = (0 : T ⟶ M) := by
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext x
  have hx : ((g.app V).hom x).1 ∈ (⊥ : Submodule (X.ringCatSheaf.obj.obj (op V)) Γ(M, V)) :=
    (SetLike.ext_iff.mp (SheafOfModules.Submodule.bot_obj M (op V)) _).mp
      ((g.app V).hom x).property
  simp only [Scheme.Modules.Hom.zero_app]
  exact (Submodule.mem_bot _).mp hx

/-- Any morphism into `M` factors through the top subsheaf of `M`. -/
public noncomputable def factorThroughTop {X : Scheme.{u}} {T M : X.Modules} (f : T ⟶ M) :
    T ⟶ (⊤ : M.Submodule).toSheafOfModules :=
  f ≫ (AlgebraicGeometry.sheafTopIso M).inv

/-- The factorization through the top subsheaf recovers the original morphism. -/
public lemma factorThroughTop_comp_ι {X : Scheme.{u}} {T M : X.Modules} (f : T ⟶ M) :
    factorThroughTop f ≫ (⊤ : M.Submodule).ι = f :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun g => f ≫ g) (AlgebraicGeometry.sheafTopIso M).inv_hom_id).trans
      (Category.comp_id _))

namespace AdicInverseSystem

variable (S : AdicInverseSystem.{u})

/-- `I^(k+1)` annihilates the `k`-th term of an adic inverse system: that term is the quotient
of the next one by `I^(k+1)`. -/
public theorem idealPowerMultiple_eq_bot (k : ℕ) :
    idealPowerMultiple S.I (k + 1) (S.system.obj (op k)) = ⊥ := by
  refine le_antisymm
    ((idealPowerMultiple_le_iff S.I (k + 1) (S.system.obj (op k)) ⊥).2 fun U => ?_) bot_le
  rw [S.pow_smul_sections_eq_bot U k]
  exact bot_le

/-- A morphism into the limit whose `n`-th projection vanishes factors through `I^(n+1)` of the
limit: that subsheaf is the kernel of the projection. -/
private theorem exists_factor_of_limitProjection_eq_zero
    (hI : Scheme.IdealSheafData.IsFiniteType S.I) (n : ℕ) (T : S.X.Modules)
    (f : T ⟶ S.limitModule)
    (hf : f ≫ limit.π S.system (op n) = (0 : T ⟶ S.system.obj (op n))) :
    ∃ g : T ⟶ (idealPowerMultiple S.I (n + 1) S.limitModule).toSheafOfModules,
      g ≫ (idealPowerMultiple S.I (n + 1) S.limitModule).ι = f := by
  obtain ⟨e, he⟩ := S.exists_idealPowerQuotientIso hI n
  have hq : f ≫ cokernel.π (C := S.X.Modules)
        (idealPowerMultiple S.I (n + 1) S.limitModule).ι =
      (0 : T ⟶ (idealPowerQuotient S.I (n + 1) S.limitModule : S.X.Modules)) := by
    exact (cancel_mono e.hom).1 (((Category.assoc _ _ _).trans
      ((congrArg (f ≫ ·) he).trans hf)).trans zero_comp.symm)
  have hex := ShortComplex.exact_cokernel (C := S.X.Modules)
    (idealPowerMultiple S.I (n + 1) S.limitModule).ι
  exact ⟨hex.lift f hq, hex.lift_f f hq⟩

/-- A morphism into the inverse limit factors through `I ^ n` of the limit if and only if all
its projections to the terms `F_m`, for `m ≥ n`, factor through `I ^ n F_m`. This is the
canonical limit description of the ideal-power submodule. -/
@[stacks 0EI8 "ideal_powers"]
public theorem idealPowerMultiple_limit (hI : Scheme.IdealSheafData.IsFiniteType S.I) (n : ℕ)
    (T : S.X.Modules) (f : T ⟶ S.limitModule) :
    (∃ g : T ⟶ (idealPowerMultiple S.I n S.limitModule).toSheafOfModules,
      g ≫ (idealPowerMultiple S.I n S.limitModule).ι = f) ↔
    (∀ m : ℕ, n ≤ m + 1 →
      ∃ g : T ⟶ (idealPowerMultiple S.I n (S.system.obj (op m))).toSheafOfModules,
        g ≫ (idealPowerMultiple S.I n (S.system.obj (op m))).ι =
          f ≫ limit.π S.system (op m)) := by
  constructor
  · rintro ⟨g, hg⟩ m -
    have hle : idealPowerMultiple S.I n S.limitModule ≤
        AlgebraicGeometry.sheafSubmoduleComap (limit.π S.system (op m))
          (idealPowerMultiple S.I n (S.system.obj (op m))) :=
      idealPowerMultiple_le_sheafSubmoduleComap S.I n (limit.π S.system (op m)) _ le_rfl
    refine ⟨g ≫ AlgebraicGeometry.sheafSubmoduleMap (limit.π S.system (op m)) _ _ hle, ?_⟩
    calc (g ≫ AlgebraicGeometry.sheafSubmoduleMap (limit.π S.system (op m)) _ _ hle) ≫
          (idealPowerMultiple S.I n (S.system.obj (op m))).ι
        = g ≫ (AlgebraicGeometry.sheafSubmoduleMap (limit.π S.system (op m)) _ _ hle ≫
            (idealPowerMultiple S.I n (S.system.obj (op m))).ι) := Category.assoc _ _ _
      _ = g ≫ ((idealPowerMultiple S.I n S.limitModule).ι ≫ limit.π S.system (op m)) :=
          congrArg (fun t => g ≫ t)
            (AlgebraicGeometry.sheafSubmoduleMap_comp_ι (limit.π S.system (op m)) _ _ hle)
      _ = (g ≫ (idealPowerMultiple S.I n S.limitModule).ι) ≫ limit.π S.system (op m) :=
          (Category.assoc _ _ _).symm
      _ = f ≫ limit.π S.system (op m) :=
          congrArg (fun t => t ≫ limit.π S.system (op m)) hg
  · intro hall
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [idealPowerMultiple_zero]
      exact ⟨factorThroughTop f, factorThroughTop_comp_ι f⟩
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      obtain ⟨g₀, hg₀⟩ := hall k le_rfl
      have key : ∀ Q : (S.system.obj (op k)).Submodule, Q = ⊥ →
          ∀ g : T ⟶ (Q.toSheafOfModules : S.X.Modules),
            g ≫ Q.ι = f ≫ limit.π S.system (op k) →
            f ≫ limit.π S.system (op k) = (0 : T ⟶ S.system.obj (op k)) := by
        rintro Q rfl g hgQ
        exact hgQ.symm.trans (comp_sheafBot_ι_eq_zero g)
      exact S.exists_factor_of_limitProjection_eq_zero hI k T f
        (key _ (S.idealPowerMultiple_eq_bot k) g₀ hg₀)

end AdicInverseSystem

end Stacks.Algebraization

end

end
