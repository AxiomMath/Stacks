module

public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzSerreConditionSpecialCases
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientMap
public import StacksFrontier.RingTheory.AdicCompletion.KerEval
public import StacksFrontier.RingTheory.AdicCompletion.QuotientDimensionSplit
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.CompletionShrinkFreeLocus

/-!
# The completed stalk of a finite locally free object of `Coh(X, 𝓘)` is free

Let `X` be a locally Noetherian scheme, `𝓘` a quasi-coherent sheaf of ideals and `(𝓕_n)` an
object of `Coh(X, 𝓘)` which is finite locally free, i.e. each `𝓕_n` is a finite locally free
`𝒪_X/𝓘^{n+1}`-module (`Stacks.Algebraization.IsFiniteLocallyFreeAdic`). At a point `y` of the
closed subscheme cut out by `𝓘` the completed stalk `𝓕_y^∧ = lim 𝓕_{n,y}` is then a finite free
module over the completed local ring `𝒪_{X,y}^∧`. A coherent `𝒪_X`-module whose completion is
such an object is finite locally free on an open neighbourhood of `V(𝓘)`.

## Main results

* `Stacks.Algebraization.free_quotient_adicCompletion_of_linearEquiv`: If the reduction
  `M / (J R^∧)^n M` of a module `M` over the `J`-adic completion `R^∧` is, as an `R`-module,
  isomorphic to a free `R / J^n`-module, then it is free over `R^∧ / (J R^∧)^n`.
* `Stacks.Algebraization.free_completedStalk_of_isFiniteLocallyFreeAdic`: The completed stalk of
  a finite locally free object of `Coh(X, 𝓘)` is free over `𝒪_{X,y}^∧` at every `y ∈ V(𝓘)`.
* `Stacks.Algebraization.exists_isFiniteLocallyFree_restrict_of_completion_iso`: A coherent
  `𝒪_X`-module whose completion is a finite locally free object of `Coh(X, 𝓘)` is finite locally
  free on an open neighbourhood of `V(𝓘)`.

## References

* [Stacks Project, Tag 0EL7](https://stacks.math.columbia.edu/tag/0EL7)
* [Stacks Project, Tag 0EJE](https://stacks.math.columbia.edu/tag/0EJE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.ModuleSkyscraper

universe u

namespace Stacks.Algebraization

/-- **Freeness of a reduction of a module over an adic completion.** Let `J` be a finitely
generated ideal of `R`, `M` a module over the `J`-adic completion `R^∧` and `n` a natural number.
If the reduction `M / (J R^∧)^n M` is, `R`-linearly, isomorphic to a free `R / J^n`-module, then it
is free over `R^∧ / (J R^∧)^n`. -/
public theorem free_quotient_adicCompletion_of_linearEquiv {R : Type u} [CommRing R] (J : Ideal R)
    (hJ : J.FG) (n : ℕ) {M : Type*} [AddCommGroup M] [Module (AdicCompletion J R) M] [Module R M]
    [IsScalarTower R (AdicCompletion J R) M] {N : Type*} [AddCommGroup N] [Module R N]
    [Module (R ⧸ J ^ n) N] [IsScalarTower R (R ⧸ J ^ n) N] [Module.Free (R ⧸ J ^ n) N]
    (f : (M ⧸ ((J.map (algebraMap R (AdicCompletion J R))) ^ n •
        (⊤ : Submodule (AdicCompletion J R) M))) ≃ₗ[R] N) :
    Module.Free (AdicCompletion J R ⧸ (J.map (algebraMap R (AdicCompletion J R))) ^ n)
      (M ⧸ ((J.map (algebraMap R (AdicCompletion J R))) ^ n •
        (⊤ : Submodule (AdicCompletion J R) M))) := by
  set K := J.map (algebraMap R (AdicCompletion J R)) with hKdef
  have hev : ∀ b : R, AdicCompletion.evalₐ J n (algebraMap R (AdicCompletion J R) b) =
      Ideal.Quotient.mk (J ^ n) b := fun b => by
    rw [AlgHom.commutes]
    rfl
  have hsurj : Function.Surjective (AdicCompletion.evalₐ J n).toRingHom := by
    intro c
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact ⟨algebraMap R _ b, hev b⟩
  let e : (AdicCompletion J R ⧸ K ^ n) ≃+* (R ⧸ J ^ n) :=
    (Ideal.quotEquivOfEq (AdicCompletion.ker_evalₐ J hJ n).symm).trans
      (RingHom.quotientKerEquivOfSurjective hsurj)
  refine free_of_ringEquiv_of_addEquiv e f.toAddEquiv ?_
  intro c m
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J n a)
  have hab : a - algebraMap R (AdicCompletion J R) b ∈ K ^ n := by
    rw [← AdicCompletion.ker_evalₐ J hJ n, RingHom.mem_ker]
    show AdicCompletion.evalₐ J n (a - algebraMap R (AdicCompletion J R) b) = 0
    rw [map_sub, hev, hb, sub_self]
  have he : e (Ideal.Quotient.mk (K ^ n) a) = Ideal.Quotient.mk (J ^ n) b := hb.symm
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  have h1 : (Ideal.Quotient.mk (K ^ n) a) •
      (Submodule.Quotient.mk m : M ⧸ (K ^ n • (⊤ : Submodule (AdicCompletion J R) M))) =
      Submodule.Quotient.mk (b • m) := by
    show Submodule.Quotient.mk (a • m) = _
    rw [Submodule.Quotient.eq, ← algebraMap_smul (AdicCompletion J R) b m, ← sub_smul]
    exact Submodule.smul_mem_smul hab Submodule.mem_top
  rw [h1, he]
  show f (b • Submodule.Quotient.mk m) = _
  rw [f.map_smul, ← algebraMap_smul (R ⧸ J ^ n) b]
  rfl

variable {X : Scheme.{u}}

/-- **The completed stalk of a finite locally free object of `Coh(X, 𝓘)` is free.** Let `X` be
locally Noetherian, `𝓘` a quasi-coherent sheaf of ideals and `(𝓕_n)` an object of `Coh(X, 𝓘)`
each of whose terms is a finite locally free `𝒪_X/𝓘^{n+1}`-module. At every point `y` of the
support of `𝓘` the completed stalk `𝓕_y^∧ = lim 𝓕_{n,y}` is a free module over the completed
local ring `𝒪_{X,y}^∧`. -/
public theorem free_completedStalk_of_isFiniteLocallyFreeAdic [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (F : Stacks.Coherent.CoherentAdicSystems I)
    (hF : IsFiniteLocallyFreeAdic I F) {y : X} (hy : y ∈ I.support) :
    Module.Free (completedLocalRing I y) (completedStalk I F y) := by
  have hI : IdealSheafData.stalk I y ≠ ⊤ := fun hc =>
    (IdealSheafData.stalk_eq_top_iff_notMem_support I y).mp hc hy
  have hle : IdealSheafData.stalk I y ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk y) :=
    IsLocalRing.le_maximalIdeal hI
  have hfg : (IdealSheafData.stalk I y).FG := Ideal.fg_of_isNoetherianRing _
  have : IsNoetherianRing (completedLocalRing I y) := AdicCompletion.isNoetherianRing _
  have : IsLocalRing (completedLocalRing I y) :=
    Stacks.AdicCompletionDimension.isLocalRing_adicCompletion_of_le_maximalIdeal _ hle
  have : Module.Finite (completedLocalRing I y) (completedStalk I F y) :=
    finite_completedStalk I F y
  have hK : completedLocalIdeal I y ≠ ⊤ := by
    intro htop
    have hker := AdicCompletion.ker_evalOneₐ_eq_map (IdealSheafData.stalk I y) hfg
    have h1 : (1 : completedLocalRing I y) ∈
        RingHom.ker (AdicCompletion.evalOneₐ (IdealSheafData.stalk I y)).toRingHom := by
      rw [hker]
      show (1 : completedLocalRing I y) ∈ completedLocalIdeal I y
      rw [htop]
      exact Submodule.mem_top
    rw [RingHom.mem_ker, map_one] at h1
    exact hI (Ideal.Quotient.zero_eq_one_iff.mp h1.symm)
  refine Stacks.FreeOfAdicQuotients.free_of_forall_free_quotient_pow_smul_top hK fun n => ?_
  obtain ⟨N, hN, ⟨eN⟩⟩ := hF n
  have hcoh : _root_.SheafOfModules.IsCoherent.{u} (F.obj.obj (op n)) := F.property.1 n
  have : (F.obj.obj (op n)).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1
  have hiso := isIso_cokernel_π_of_idealPowerMultiple_eq_bot I (n + 1) _ (F.property.2.1 n)
  let eπ : idealPowerQuotient I (n + 1) (F.obj.obj (op n)) ≅ F.obj.obj (op n) :=
    (@asIso _ _ _ _ (cokernel.π (C := X.Modules)
      (idealPowerMultiple I (n + 1) (F.obj.obj (op n))).ι) hiso).symm
  have := free_quotient_stalk_of_pushforward_iso I (F.obj.obj (op n)) (Nat.succ_ne_zero n) hy
    N hN (eπ ≪≫ eN.symm)
  exact free_quotient_adicCompletion_of_linearEquiv _ hfg (n + 1)
    ((completedStalkQuotientEquivStalk F y n).trans
      ((((modulesStalkFunctor X y).mapIso eπ).toLinearEquiv.symm).trans
        (idealPowerQuotientStalkLinearEquiv I (n + 1) (F.obj.obj (op n)) y).symm))

/-- **A coherent module whose completion is a finite locally free object is finite locally free
near the closed subscheme.** Let `X` be locally Noetherian, `𝓘` a quasi-coherent sheaf of ideals,
`(𝓕_n)` a finite locally free object of `Coh(X, 𝓘)` and `𝒢` a coherent `𝒪_X`-module with
`𝒢^∧ ≅ (𝓕_n)`. Then `𝒢` is finite locally free on an open neighbourhood of `V(𝓘)`. -/
public theorem exists_isFiniteLocallyFree_restrict_of_completion_iso [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (F : Stacks.Coherent.CoherentAdicSystems I)
    (hF : IsFiniteLocallyFreeAdic I F)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (e : ((completionFunctor X I).obj G).obj ≅ F.obj) :
    ∃ V : X.Opens, (I.support : Set X) ⊆ (V : Set X) ∧
      AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree
        (Scheme.Modules.restrict (show X.Modules from G.obj) V.ι) := by
  have hfp := _root_.isFinitePresentation_of_isCoherent G.obj
  have hqc := _root_.isQuasicoherent_of_isFinitePresentation G.obj
  refine AlgebraicGeometry.Scheme.Modules.exists_isFiniteLocallyFree_restrict_of_free_stalks
    G.obj G.property _ fun y hy => ?_
  exact free_stalk_of_forall_pushforward_iso I (show X.Modules from G.obj) hy fun n => by
    obtain ⟨N, hN, ⟨eN⟩⟩ := hF n
    exact ⟨N, hN, ⟨(eqToIso (completionFunctor_obj X I G n).symm ≪≫ e.app (op n)) ≪≫ eN.symm⟩⟩

end Stacks.Algebraization

end
