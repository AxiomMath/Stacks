module

public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzSerreFreeStalk
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.StructureSheafStalk
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.CompletedStalkFinite
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.Basic
public import StacksFrontier.RingTheory.AdicCompletion.Units

/-!
# The completed stalk of the completion of the structure sheaf

Let `X` be a locally Noetherian scheme, let `ℐ` be a quasi-coherent sheaf of ideals on `X` and
let `x` be a point of `X`. The structure sheaf `𝒪_X` is coherent, so its completion
`(𝒪_X / ℐ^{n+1})_n` along `ℐ` is an object of `Coh(X, ℐ)`. This file proves that its completed
stalk at `x` is free of rank one over the completed local ring `𝒪_{X,x}^∧`.

## Main definitions

* `Stacks.Algebraization.structureAdicSystem` — the completion of `𝒪_X` along `ℐ`, as a coherent
  adic system.
* `Stacks.Algebraization.stalkStructureAdicSystemLinearEquiv` — the stalk of its `n`-th term is
  `𝒪_{X,x} / ℐ_x^{n+1}`.

## Main results

* `Stacks.Algebraization.nonempty_linearEquiv_adicCompletion_of_quotient` — a finite module `M`
  over `Ĉ = C^∧` (the `I`-adic completion of a ring `C`, with `I` finitely generated) whose
  reductions `M / (IĈ)^{n+1} M` are all isomorphic to `C / I^{n+1}` as `C`-modules is isomorphic
  to `Ĉ`.
* `Stacks.Algebraization.nonempty_completedStalk_structureAdicSystem_linearEquiv` — the completed
  stalk of `structureAdicSystem` at `x` is isomorphic to `𝒪_{X,x}^∧`.

## Implementation notes

The completed stalk is not computed as a limit. Instead the reductions are identified
level by level: the `n`-th reduction of the completed stalk is the stalk of `𝒪_X / ℐ^{n+1}`
(`Stacks.Algebraization.completedStalkQuotientEquivStalk`), which is `𝒪_{X,x} / ℐ_x^{n+1}`. The
algebraic lemma then concludes without any compatibility between the levels. A lift `m` of the
generator of the level-zero reduction generates `M` by Nakayama's lemma, since `IĈ` lies in the
Jacobson radical of `Ĉ` (Stacks 05GI). If `a • m = 0`, write `a = c + b` with `c ∈ C` and
`b ∈ (IĈ)^{n+1}`; then `c` kills the reduction `M / (IĈ)^{n+1} M ≅ C / I^{n+1}`, so `c ∈ I^{n+1}`
and `a ∈ (IĈ)^{n+1}`. As this holds for all `n` and `Ĉ` is `I`-adically Hausdorff, `a = 0`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.ModuleSkyscraper

universe u v

namespace Stacks.Algebraization

/-! ### A module over a completion with the reductions of the ring is the completion -/

section Algebra

variable {C : Type u} [CommRing C] (I : Ideal C)

/-- **A finite module over `Ĉ` with the reductions of the ring is free of rank one.**

Let `I` be a finitely generated ideal of a ring `C` and `Ĉ` the `I`-adic completion. If `M` is
a finite `Ĉ`-module whose reductions `M / (IĈ)^{n+1} M` are isomorphic, as `C`-modules, to
`C / I^{n+1}` for every `n`, then `M ≅ Ĉ`. -/
theorem nonempty_linearEquiv_adicCompletion_of_quotient (hI : I.FG)
    (M : Type v) [AddCommGroup M] [Module (AdicCompletion I C) M] [Module C M]
    [IsScalarTower C (AdicCompletion I C) M] [Module.Finite (AdicCompletion I C) M]
    (e : ∀ n : ℕ, (M ⧸ ((I.map (algebraMap C (AdicCompletion I C))) ^ (n + 1) •
        (⊤ : Submodule (AdicCompletion I C) M))) ≃ₗ[C] (C ⧸ I ^ (n + 1))) :
    Nonempty (M ≃ₗ[AdicCompletion I C] AdicCompletion I C) := by
  set A := AdicCompletion I C
  set Î := I.map (algebraMap C A)
  -- a lift of the generator of the level-zero reduction
  obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective _
    ((e 0).symm (Submodule.Quotient.mk (1 : C)))
  -- every element is a `C`-multiple of `m` modulo `IĈ M`
  have hgen : ∀ y : M, ∃ c : C, y - c • m ∈ Î ^ (0 + 1) • (⊤ : Submodule A M) := by
    intro y
    obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (e 0 (Submodule.Quotient.mk y))
    refine ⟨c, ?_⟩
    rw [← Submodule.Quotient.eq]
    apply (e 0).injective
    rw [Submodule.Quotient.mk_smul, map_smul, hm, LinearEquiv.apply_symm_apply, ← hc,
      ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]
  -- Nakayama: `m` generates `M`
  have hspan : Submodule.span A {m} = ⊤ := by
    have hjac : Î ≤ (⊥ : Ideal A).jacobson :=
      (AdicCompletion.isUnit_of_isUnit_evalOneₐ_and_isUnit_one_add_and_le_jacobson_bot I).2.2.2.1
    refine top_le_iff.1
      (Submodule.le_of_le_smul_of_le_jacobson_bot (I := Î) Module.Finite.fg_top hjac ?_)
    intro y _
    obtain ⟨c, hc⟩ := hgen y
    rw [zero_add, pow_one] at hc
    refine Submodule.mem_sup.2 ⟨c • m, ?_, y - c • m, hc, add_sub_cancel _ _⟩
    rw [← algebraMap_smul A c m]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self m)
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton A M m) := by
    rw [← LinearMap.range_eq_top, ← LinearMap.span_singleton_eq_range]
    exact hspan
  -- injectivity
  have hinj : Function.Injective (LinearMap.toSpanSingleton A M m) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro a ha
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at ha
    refine IsHausdorff.haus (AdicCompletion.instIsHausdorff I C) a fun n => ?_
    rw [SModEq.zero]
    cases n with
    | zero =>
      rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
      exact Submodule.mem_top
    | succ k =>
      obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval I C (k + 1) a)
      have hb : a - algebraMap C A c ∈ I ^ (k + 1) • (⊤ : Submodule C A) := by
        rw [AdicCompletion.pow_smul_top_eq_ker_eval hI, LinearMap.mem_ker, map_sub,
          AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
          AdicCompletion.eval_of, ← hc, Submodule.mkQ_apply, sub_self]
      have hb' : a - algebraMap C A c ∈ Î ^ (k + 1) := by
        rw [Ideal.smul_top_eq_map, Ideal.map_pow] at hb
        exact hb
      have hcm : c • m ∈ Î ^ (k + 1) • (⊤ : Submodule A M) := by
        have h1 : (a - algebraMap C A c) • m ∈ Î ^ (k + 1) • (⊤ : Submodule A M) :=
          Submodule.smul_mem_smul hb' Submodule.mem_top
        rw [sub_smul, ha, zero_sub, neg_mem_iff, algebraMap_smul] at h1
        exact h1
      have hkill : ∀ z : C ⧸ I ^ (k + 1), c • z = 0 := by
        intro z
        obtain ⟨z, rfl⟩ := (e k).surjective z
        rw [← map_smul]
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
        obtain ⟨a', rfl⟩ := hsurj y
        rw [← Submodule.Quotient.mk_smul, LinearMap.toSpanSingleton_apply,
          (Submodule.Quotient.mk_eq_zero _).2, map_zero]
        rw [smul_comm]
        exact Submodule.smul_mem _ _ hcm
      have hcI : c ∈ I ^ (k + 1) := by
        have := hkill (Submodule.Quotient.mk 1)
        rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one,
          Submodule.Quotient.mk_eq_zero] at this
        exact this
      have hcA : algebraMap C A c ∈ I ^ (k + 1) • (⊤ : Submodule C A) := by
        rw [Algebra.algebraMap_eq_smul_one]
        exact Submodule.smul_mem_smul hcI Submodule.mem_top
      simpa using add_mem hb hcA
  exact ⟨(LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩).symm⟩

end Algebra

/-! ### The completion of the structure sheaf -/

section Geometry

variable (X : Scheme.{u}) [IsLocallyNoetherian X] (J : X.IdealSheafData)

/-- **The completion of the structure sheaf along `ℐ`**: the coherent adic system
`(𝒪_X / ℐ^{n+1})_n`, the image of the coherent module `𝒪_X` under
`Stacks.Algebraization.completionFunctor`. -/
def structureAdicSystem : Stacks.Coherent.CoherentAdicSystems J :=
  (completionFunctor X J).obj
    ⟨SheafOfModules.unit X.ringCatSheaf,
      Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit⟩

/-- The stalk at `x` of the `n`-th term `𝒪_X / ℐ^{n+1}` of `structureAdicSystem` is
`𝒪_{X,x} / ℐ_x^{n+1}`. -/
def stalkStructureAdicSystemLinearEquiv (x : X) (n : ℕ) :
    (modulesStalkFunctor X x).obj ((structureAdicSystem X J).obj.obj (op n)) ≃ₗ[X.presheaf.stalk x]
      (X.presheaf.stalk x ⧸ IdealSheafData.stalk J x ^ (n + 1)) :=
  (((modulesStalkFunctor X x).mapIso (eqToIso (completionFunctor_obj X J
      ⟨SheafOfModules.unit X.ringCatSheaf,
        Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit⟩ n))).toLinearEquiv.trans
    (idealPowerQuotientStalkLinearEquiv J (n + 1)
      (SheafOfModules.unit X.ringCatSheaf) x).symm).trans
    ((Submodule.Quotient.equiv _ _ (structureSheafStalkLinearEquiv X x)
        (map_smul_top_linearEquiv _ _)).trans
      (Submodule.quotEquivOfEq _ _ (by rw [smul_eq_mul, Ideal.mul_top])))

/-- **The completed stalk of the completion of the structure sheaf is the completed local
ring.** For a quasi-coherent ideal sheaf `ℐ` on a locally Noetherian scheme `X` and a point `x`,
the completed stalk of `structureAdicSystem X ℐ` at `x` is free of rank one over `𝒪_{X,x}^∧`.

Its reductions are the stalks `𝒪_{X,x} / ℐ_x^{n+1}` of the terms
(`Stacks.Algebraization.completedStalkQuotientEquivStalk` and
`Stacks.Algebraization.stalkStructureAdicSystemLinearEquiv`), it is finite over `𝒪_{X,x}^∧`
(`Stacks.Algebraization.finite_completedStalk`), and
`Stacks.Algebraization.nonempty_linearEquiv_adicCompletion_of_quotient` concludes. -/
theorem nonempty_completedStalk_structureAdicSystem_linearEquiv (x : X) :
    Nonempty (completedStalk J (structureAdicSystem X J) x ≃ₗ[completedLocalRing J x]
      completedLocalRing J x) :=
  have := finite_completedStalk J (structureAdicSystem X J) x
  nonempty_linearEquiv_adicCompletion_of_quotient (IdealSheafData.stalk J x)
    (Ideal.fg_of_isNoetherianRing _) _ fun n =>
      (completedStalkQuotientEquivStalk (structureAdicSystem X J) x n).trans
        (stalkStructureAdicSystemLinearEquiv X J x n)

end Geometry

end Stacks.Algebraization

end
