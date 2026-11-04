module

public import StacksFrontier.Algebra.Module.LocalizedEquiv
public import StacksFrontier.AlgebraicGeometry.Algebraization.DepthInequalities
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.CompletedStalkFinite
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.Basic
import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ClosedImmersionCompletion
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.Support.DepthAdicCompletion
public import StacksFrontier.RingTheory.AdicCompletion.EventuallyBijective

/-!
# The formal stalk of a completed coherent module

Let `X` be a locally Noetherian scheme, `ℐ` a quasi-coherent sheaf of ideals and `ℱ` a coherent
`𝒪_X`-module. Completing `ℱ` along `ℐ` gives the coherent adic system
`(ℱ / ℐ^{n+1} ℱ)` of `Stacks.Algebraization.completionFunctor`, and this file identifies its
formal stalk at a point `x` with the `ℐ_x`-adic completion of the stalk `ℱ_x`:

  `lim (ℱ / ℐ^{n+1} ℱ)_x = (ℱ_x)^∧`.

## Main results

* `Stacks.Algebraization.formalStalkCompletionFunctorEquiv` — the identification above, as a
  `𝒪_{X,x}`-linear equivalence.
* `Stacks.Algebraization.completedStalkCompletionFunctorEquiv` — the same identification read on
  `Stacks.Algebraization.completedStalk`, hence linear over the completed local ring
  `𝒪_{X,x}^∧`, which is the ring that acts on the formal stalk.

## Implementation notes

The comparison map is the one induced by the projections `ℱ ⟶ ℱ / ℐ^{n+1} ℱ` of
`Stacks.Algebraization.completionProjection`: their stalks are compatible with the transition
maps of the system, so they assemble into `𝒪_{X,x}`-linear map
`ℱ_x ⟶ lim (ℱ / ℐ^{n+1} ℱ)_x` whose `ℐ_x`-adic completion is the identification. That the
completion of a map is an isomorphism as soon as the map is bijective modulo every deep enough
power of the ideal is `Crystalline.map_bijective_of_reduceModIdeal_eventually`; here the levels
from `1` on are used, and the level-`n+1` statement is exactly that both
`ℱ_x ⟶ (ℱ / ℐ^{n+1} ℱ)_x` and the limit projection
`lim (ℱ / ℐ^{m+1} ℱ)_x ⟶ (ℱ / ℐ^{n+1} ℱ)_x` are surjective with kernel the `(n+1)`-st
ideal-power multiple — the first by exactness of the stalk functor together with
`Stacks.Algebraization.stalk_idealPowerMultiple`, the second by
`Stacks.Coherent.moduleLimit_projection_ker`.

As for `Stacks.Algebraization.finite_completedStalk`, the work is done in the
`Stacks.ModuleSkyscraper.modulesStalkFunctor` spelling of the stalk,
where the germ computations and the exactness instances live, and transported once to
`Stacks.Algebraization.stalkModuleFunctor` along
`AlgebraicGeometry.restrictScalarsStalkFunctorIso`.

No `stacks` attribute is placed: the source states this identification only in passing, inside
the discussion of Stacks 0EJ3, and the tags that consume it need further inputs.

## References

* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880), the completion functor.
* [Stacks Project, Tag 0EJ3](https://stacks.math.columbia.edu/tag/0EJ3), where the formal stalk
  of a completion is used.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.ModuleSkyscraper

universe u

namespace Stacks.Algebraization

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (J : X.IdealSheafData)
  (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (x : X)

/-! ### The stalk tower of a completion -/

/-- The tower `n ↦ (ℱ / ℐ^{n+1} ℱ)_x` of stalks of the completion of `ℱ`. -/
public abbrev completionStalkTower : ℕᵒᵖ ⥤ ModuleCat.{u} (X.presheaf.stalk x) :=
  ((completionFunctor X J).obj F).obj ⋙ modulesStalkFunctor X x

/-- The stalk at `x` of the projection `ℱ ⟶ ℱ / ℐ^{n+1} ℱ`. -/
public def stalkCompletionProjection (n : ℕ) :
    ((modulesStalkFunctor X x).obj F.obj) →ₗ[X.presheaf.stalk x]
      ((completionStalkTower J F x).obj (op n)) :=
  ((modulesStalkFunctor X x).map (completionProjection X J F n)).hom

/-- The stalk of the identification of the `n`-th term of the completion with `ℱ / ℐ^{n+1} ℱ` is
bijective. -/
public theorem bijective_stalk_eqToHom (n : ℕ) :
    Function.Bijective ((modulesStalkFunctor X x).map
      (eqToHom (completionFunctor_obj X J F n).symm)).hom := by
  have hiso : IsIso ((modulesStalkFunctor X x).map
      (eqToHom (completionFunctor_obj X J F n).symm)) := Functor.map_isIso _ _
  exact ⟨(ModuleCat.mono_iff_injective _).mp inferInstance,
    (ModuleCat.epi_iff_surjective _).mp inferInstance⟩

/-- The stalk of the projection onto the `n`-th term of the completion, factored through the
stalk of the quotient projection `ℱ ⟶ ℱ / ℐ^{n+1} ℱ`. -/
public theorem stalkCompletionProjection_factor (n : ℕ) :
    stalkCompletionProjection J F x n =
      ((modulesStalkFunctor X x).map
            (eqToHom (completionFunctor_obj X J F n).symm)).hom.comp
        ((modulesStalkFunctor X x).map
          (cokernel.π (idealPowerMultiple J (n + 1) F.obj).ι)).hom :=
  congrArg ModuleCat.Hom.hom
    ((congrArg (fun f => (modulesStalkFunctor X x).map f) (completionProjection_eq J F n)).trans
      ((modulesStalkFunctor X x).map_comp _ _))

omit [IsLocallyNoetherian X] in
/-- `ℱ` is quasi-coherent, being coherent. -/
public theorem isQuasicoherent_coherentModules_obj : F.obj.IsQuasicoherent := by
  have : F.obj.IsCoherent := F.property
  exact isQuasicoherent_of_isCoherent _

/-- **The stalk of the projection onto the `n`-th term of the completion is surjective.** -/
public theorem surjective_stalkCompletionProjection (n : ℕ) :
    Function.Surjective (stalkCompletionProjection J F x n) := by
  rw [stalkCompletionProjection_factor]
  exact (bijective_stalk_eqToHom J F x n).2.comp
    (surjective_stalk_cokernel_π (idealPowerMultiple J (n + 1) F.obj) x)

/-- **The kernel of the stalk of the projection onto the `n`-th term of the completion is
`ℐ_x^{n+1} ℱ_x`.** -/
public theorem ker_stalkCompletionProjection (n : ℕ) :
    LinearMap.ker (stalkCompletionProjection J F x n) =
      IdealSheafData.stalk J x ^ (n + 1) •
        (⊤ : Submodule (X.presheaf.stalk x) ((modulesStalkFunctor X x).obj F.obj)) := by
  have hq : F.obj.IsQuasicoherent := isQuasicoherent_coherentModules_obj F
  have hinj := (bijective_stalk_eqToHom J F x n).1
  have hfac := stalkCompletionProjection_factor J F x n
  have hkey : LinearMap.ker (stalkCompletionProjection J F x n) =
      LinearMap.ker ((modulesStalkFunctor X x).map
        (cokernel.π (idealPowerMultiple J (n + 1) F.obj).ι)).hom :=
    (congrArg LinearMap.ker hfac).trans
      ((LinearMap.ker_comp _ _).trans
        ((congrArg (Submodule.comap _) (LinearMap.ker_eq_bot.2 hinj)).trans
          (Submodule.comap_bot _)))
  exact hkey.trans
    ((range_stalk_submodule_ι_eq_ker_stalk_cokernel_π
        (idealPowerMultiple J (n + 1) F.obj) x).symm.trans
      (stalk_idealPowerMultiple J (n + 1) F.obj x))

/-! ### The comparison map -/

/-- The stalks of the projections of `ℱ` onto the terms of its completion, as a compatible family
in the tower of stalks. -/
public def stalkCompletionTowerSection :
    ((modulesStalkFunctor X x).obj F.obj) →ₗ[X.presheaf.stalk x]
      Stacks.Coherent.moduleTowerLimit (fun n => (completionStalkTower J F x).obj (op n))
        (fun n => ((completionStalkTower J F x).map (homOfLE (Nat.le_succ n)).op).hom) where
  toFun z := ⟨fun n => stalkCompletionProjection J F x n z, fun n => by
    have h : (modulesStalkFunctor X x).map (completionProjection X J F (n + 1)) ≫
        (modulesStalkFunctor X x).map
          (((completionFunctor X J).obj F).obj.map (homOfLE (Nat.le_succ n)).op) =
        (modulesStalkFunctor X x).map (completionProjection X J F n) :=
      ((modulesStalkFunctor X x).map_comp _ _).symm.trans
        (congrArg (fun f => (modulesStalkFunctor X x).map f)
          (completionProjection_transition X J F n))
    exact congrArg (fun k : (modulesStalkFunctor X x).obj F.obj ⟶
      (completionStalkTower J F x).obj (op n) => k.hom z) h⟩
  map_add' _ _ := by apply Subtype.ext; funext n; exact map_add _ _ _
  map_smul' _ _ := by apply Subtype.ext; funext n; exact map_smul _ _ _

/-- **The comparison map `ℱ_x ⟶ lim (ℱ / ℐ^{n+1} ℱ)_x`** induced by the projections of `ℱ` onto
the terms of its completion. -/
public def stalkToCompletionLimit :
    ((modulesStalkFunctor X x).obj F.obj) →ₗ[X.presheaf.stalk x]
      (limit (completionStalkTower J F x) : ModuleCat.{u} (X.presheaf.stalk x)) :=
  (Stacks.Coherent.moduleLimitTowerEquiv (completionStalkTower J F x)).symm.toLinearMap.comp
    (stalkCompletionTowerSection J F x)

/-- The level-`n` component of the comparison map is the stalk of the projection onto the `n`-th
term of the completion. -/
public theorem limit_π_stalkToCompletionLimit (n : ℕ)
    (z : (modulesStalkFunctor X x).obj F.obj) :
    (limit.π (completionStalkTower J F x) (op n)).hom (stalkToCompletionLimit J F x z) =
      stalkCompletionProjection J F x n z := by
  rw [← Stacks.Coherent.moduleLimitTowerEquiv_apply_coe]
  exact congrArg (fun s : Stacks.Coherent.moduleTowerLimit
      (fun k => (completionStalkTower J F x).obj (op k))
      (fun k => ((completionStalkTower J F x).map (homOfLE (Nat.le_succ k)).op).hom) => s.1 n)
    ((Stacks.Coherent.moduleLimitTowerEquiv (completionStalkTower J F x)).apply_symm_apply
      (stalkCompletionTowerSection J F x z))

/-! ### Levelwise bijectivity -/

/-- The limit projections of the tower of stalks are surjective. -/
public theorem surjective_limit_π_completionStalkTower (n : ℕ) :
    Function.Surjective ((limit.π (completionStalkTower J F x) (op n)).hom) :=
  Stacks.Coherent.moduleLimit_projection_surjective _
    (fun k => surjective_stalk_coherentAdicTransition ((completionFunctor X J).obj F) x k) n

/-- The kernel of the limit projection of the tower of stalks is the `(n+1)`-st ideal-power
multiple of the limit. -/
public theorem ker_limit_π_completionStalkTower (n : ℕ) :
    LinearMap.ker ((limit.π (completionStalkTower J F x) (op n)).hom) =
      IdealSheafData.stalk J x ^ (n + 1) •
        (⊤ : Submodule (X.presheaf.stalk x)
          (limit (completionStalkTower J F x) : ModuleCat.{u} (X.presheaf.stalk x))) :=
  Stacks.Coherent.moduleLimit_projection_ker _
    (fun k => surjective_stalk_coherentAdicTransition ((completionFunctor X J).obj F) x k)
    (fun k => ker_stalk_coherentAdicTransition ((completionFunctor X J).obj F) x k)
    (Ideal.fg_of_isNoetherianRing _) n

/-- **The comparison map is bijective modulo every positive power of `ℐ_x`:** both it and the
limit projection to level `m` are surjective with kernel the `(m+1)`-st ideal-power multiple. -/
public theorem bijective_reduceModIdeal_stalkToCompletionLimit (m : ℕ) :
    Function.Bijective
      ((stalkToCompletionLimit J F x).reduceModIdeal (IdealSheafData.stalk J x ^ (m + 1))) := by
  rw [Crystalline.bijective_reduceModIdeal_iff]
  refine ⟨fun y => ?_, fun z hz => ?_⟩
  · obtain ⟨z, hz⟩ := surjective_stalkCompletionProjection J F x m
      ((limit.π (completionStalkTower J F x) (op m)).hom y)
    refine ⟨z, ?_⟩
    rw [← ker_limit_π_completionStalkTower]
    refine LinearMap.mem_ker.2 ?_
    rw [map_sub, limit_π_stalkToCompletionLimit, hz, sub_self]
  · rw [← ker_limit_π_completionStalkTower, LinearMap.mem_ker,
      limit_π_stalkToCompletionLimit] at hz
    rw [← ker_stalkCompletionProjection]
    exact LinearMap.mem_ker.2 hz

/-- **The `ℐ_x`-adic completion of the comparison map is bijective.** -/
public theorem bijective_map_stalkToCompletionLimit :
    Function.Bijective
      (AdicCompletion.map (IdealSheafData.stalk J x) (stalkToCompletionLimit J F x)) :=
  Crystalline.map_bijective_of_reduceModIdeal_eventually _ _ 1 (fun n hn => by
    cases n with
    | zero => exact absurd hn (by omega)
    | succ m => exact bijective_reduceModIdeal_stalkToCompletionLimit J F x m)

/-! ### The identification -/

/-- **The completed stalk of the completion of a coherent module is the `ℐ_x`-adic completion of
its stalk**, as a module over the completed local ring `𝒪_{X,x}^∧`:

  `(ℱ_x)^∧ ≅ lim (ℱ / ℐ^{n+1} ℱ)_x`.

The identification is the `ℐ_x`-adic completion of the comparison map induced by the projections
`ℱ ⟶ ℱ / ℐ^{n+1} ℱ`, which is bijective because the comparison map is bijective modulo every
positive power of `ℐ_x`. -/
public def completedStalkCompletionFunctorEquiv :
    AdicCompletion (IdealSheafData.stalk J x) ((stalkModuleFunctor x).obj F.obj)
      ≃ₗ[completedLocalRing J x] completedStalk J ((completionFunctor X J).obj F) x :=
  (AdicCompletion.congr (IdealSheafData.stalk J x)
      ((AlgebraicGeometry.restrictScalarsStalkFunctorIso x).app F.obj).toLinearEquiv).trans
    ((LinearEquiv.ofBijective _ (bijective_map_stalkToCompletionLimit J F x)).trans
      (AdicCompletion.congr (IdealSheafData.stalk J x)
        (formalStalkEquivModuleStalkLimit ((completionFunctor X J).obj F) x).symm))

/-- **The formal stalk of the completion of a coherent module is the `ℐ_x`-adic completion of its
stalk:**

  `lim (ℱ / ℐ^{n+1} ℱ)_x ≅ (ℱ_x)^∧`.

This is `Stacks.Algebraization.completedStalkCompletionFunctorEquiv` read on
`Stacks.Algebraization.formalStalk`, which is the formal stalk itself because it is already
`ℐ_x`-adically complete (`Stacks.Algebraization.formalStalkEquivCompletedStalk`). -/
public def formalStalkCompletionFunctorEquiv :
    formalStalk ((completionFunctor X J).obj F) x ≃ₗ[X.presheaf.stalk x]
      AdicCompletion (IdealSheafData.stalk J x) ((stalkModuleFunctor x).obj F.obj) :=
  (formalStalkEquivCompletedStalk ((completionFunctor X J).obj F) x).trans
    (LinearEquiv.ofBijective
      ((completedStalkCompletionFunctorEquiv J F x).symm.toLinearMap.restrictScalars
        (X.presheaf.stalk x))
      (completedStalkCompletionFunctorEquiv J F x).symm.bijective)

/-! ### The depth transfer -/

omit [IsLocallyNoetherian X] in
/-- The stalk of a coherent module is a finite `𝒪_{X,x}`-module, coherence giving finite type. -/
public theorem finite_stalkModuleFunctor_coherentModules_obj :
    Module.Finite (X.presheaf.stalk x) ((stalkModuleFunctor x).obj F.obj) := by
  have hcoh : _root_.SheafOfModules.IsCoherent.{u} F.obj := F.property
  have : F.obj.IsFiniteType := _root_.SheafOfModules.IsCoherent.isFiniteType
  have h : Module.Finite (X.presheaf.stalk x) ((modulesStalkFunctor X x).obj F.obj) :=
    _root_.SheafOfModules.finite_stalk X.sheaf F.obj x
  exact h.equiv
    ((AlgebraicGeometry.restrictScalarsStalkFunctorIso x).app F.obj).toLinearEquiv.symm

/-- **The depth of the formal stalk of a completion is the depth of the completed stalk.** At
every prime `𝔭` of `𝒪_{X,x}^∧`, `Stacks.Algebraization.completedStalkDepth` of the completion of
`ℱ` is the depth of the localization at `𝔭` of the `ℐ_x`-adic completion of `ℱ_x`.

This is `Stacks.Algebraization.completedStalkCompletionFunctorEquiv` localized at `𝔭`, which is
`Module.localizedEquiv`. -/
public theorem completedStalkDepth_completionFunctor_eq_depth_adicCompletion
    (p : PrimeSpectrum (completedLocalRing J x)) :
    completedStalkDepth J ((completionFunctor X J).obj F) x p =
      Module.depth (Localization.AtPrime p.asIdeal)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl
          (AdicCompletion (IdealSheafData.stalk J x) ((stalkModuleFunctor x).obj F.obj))) :=
  Module.depth_eq_depth_of_linearEquiv _
    (Module.localizedEquiv p.asIdeal.primeCompl
      (completedStalkCompletionFunctorEquiv J F x).symm)

/-- **The depth transfer for a completed coherent module.** Let `𝔭` be a prime of `𝒪_{X,x}^∧`
lying over the prime `𝔮` of `𝒪_{X,x}`. Then the depth of the formal stalk of the completion of
`ℱ` at `𝔭` is the depth of `(ℱ_x)_𝔮` plus the depth of the fibre
`(𝒪_{X,x}^∧)_𝔭 / 𝔮 (𝒪_{X,x}^∧)_𝔭`.

The formal stalk of the completion of `ℱ` is the `ℐ_x`-adic completion of `ℱ_x`
(`Stacks.Algebraization.completedStalkCompletionFunctorEquiv`), and
`AlgebraicGeometry.depth_localized_adicCompletion` — Stacks 0EHW — is the additivity of depth
under completion and localization at a prime for a finite module, which `ℱ_x` is because `ℱ` is
coherent. -/
public theorem completedStalkDepth_completionFunctor
    (p : PrimeSpectrum (completedLocalRing J x)) (q : Ideal (X.presheaf.stalk x)) [q.IsPrime]
    [p.asIdeal.LiesOver q] :
    completedStalkDepth J ((completionFunctor X J).obj F) x p =
      Module.depth (Localization.AtPrime q)
          (IsLocalRing.maximalIdeal (Localization.AtPrime q))
          (LocalizedModule q.primeCompl ((stalkModuleFunctor x).obj F.obj)) +
        Module.depth (Localization.AtPrime p.asIdeal)
          (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
          (Localization.AtPrime p.asIdeal ⧸
            q.map (algebraMap (X.presheaf.stalk x) (Localization.AtPrime p.asIdeal))) := by
  have : p.asIdeal.IsPrime := p.isPrime
  have := finite_stalkModuleFunctor_coherentModules_obj F x
  exact (completedStalkDepth_completionFunctor_eq_depth_adicCompletion J F x p).trans
    (AlgebraicGeometry.depth_localized_adicCompletion (IdealSheafData.stalk J x) q p.asIdeal)

end Stacks.Algebraization

end
