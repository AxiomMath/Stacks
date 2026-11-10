module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Smooth.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.DualizingModulesQuasi.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Discriminant.TargetLocalization
public import StacksFrontier.RingTheory.Flat.TowerLTensor

/-!
# Flatness of the relative dualizing module over the base

For a flat quasi-finite homomorphism of Noetherian rings, the relative dualizing module is flat
over the base ring.

## Main results

* `Stacks.Discriminant.dualizingModule_flat`: the relative dualizing module of a flat
  quasi-finite map of Noetherian rings is flat over the base.

## Implementation notes

Flatness is checked after localizing the target at each of its maximal ideals. There an étale
neighbourhood of the base separates a finite direct factor of the target containing the chosen
prime; over that factor the relative dualizing module is the linear dual of a finite flat
module and so is flat, and localizing commutes with forming it. The two localizations are
related by a faithfully flat local map, along which flatness descends.

Since `Algebra.QuasiFinite` records the fibrewise finiteness condition but not finite type, the
latter is assumed separately. The module structure of the relative dualizing module over the
base is the restriction of its natural structure over the target.

## References

* [Stacks Project, Tag 0BVE](https://stacks.math.columbia.edu/tag/0BVE)
-/

@[expose] public section

universe u v w x y

namespace Stacks.Discriminant

open Topology
open TensorProduct
open scoped TensorProduct

/-- For a finite flat algebra over a Noetherian base the relative dualizing module is the
linear dual of the algebra, hence flat over the base. -/
private lemma dualizingModule_flat_of_finite_flat
    {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [Module.Finite A B] [Module.Flat A B]
    (F : FiniteOpenFactorization.{u, v, w} A B) :
    letI : Module A (dualizingModule F) :=
      Module.compHom (dualizingModule F) (algebraMap A B)
    Module.Flat A (dualizingModule F) := by
  let G : FiniteOpenFactorization.{u, v, v} A B := identityFactorization
  let : Module B (Module.Dual A B) := algebraDualModule A B
  let : Module A (dualizingModule F) := Module.compHom _ (algebraMap A B)
  let : Module A (dualizingModule G) := Module.compHom _ (algebraMap A B)
  let : AddCommGroup (Module.Dual A B ⊗[B] B) :=
    dualizingModule.instAddCommGroup G
  let comm : (Module.Dual A B ⊗[B] B) ≃+ (B ⊗[B] Module.Dual A B) :=
    (TensorProduct.comm B (Module.Dual A B) B).toAddEquiv
  let : Module B (Module.Dual A B ⊗[B] B) := comm.module B
  let : Module B (dualizingModule G) := comm.module B
  let : IsScalarTower A B (Module.Dual A B) := IsScalarTower.of_algebraMap_smul (by
    intro a f
    ext x
    change f ((algebraMap A B a) * x) = a * f x
    rw [← Algebra.smul_def]
    simp)
  let : IsScalarTower A B (dualizingModule F) := IsScalarTower.of_algebraMap_smul (by
    intro a x
    rfl)
  let : IsScalarTower A B (dualizingModule G) := IsScalarTower.of_compHom A B _
  let e₀ : dualizingModule G ≃ₗ[B] Module.Dual A B := by
    dsimp [G, identityFactorization, dualizingModule]
    exact (comm.linearEquiv B).trans (TensorProduct.lid B (Module.Dual A B))
  let e : dualizingModule F ≃ₗ[B] dualizingModule G := dualizingModuleEquiv F G
  let : Module.FinitePresentation A B := Module.finitePresentation_of_finite A B
  let : Module.Projective A B := Module.Flat.projective_of_finitePresentation
  let : Module.Projective A (Module.Dual A B) :=
    Module.dual_projective (R := A) (M := B)
  have : Module.Flat A (Module.Dual A B) := Module.Flat.of_projective
  exact Module.Flat.of_linearEquiv ((e.trans e₀).restrictScalars A)

/-- If an away localization of the target is finite and flat over the base, then the
corresponding localization of the relative dualizing module is flat over the base. -/
private lemma localizedDualizingModule_flat_of_finite_flat
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    [Algebra B C] [IsScalarTower A B C] [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra.QuasiFinite A B]
    (e : B) [IsLocalization.Away e C]
    (F : FiniteOpenFactorization.{u, v, x} A B)
    (G : FiniteOpenFactorization.{u, w, y} A C)
    [Module.Finite A C] [Module.Flat A C] :
    let : Module C (LocalizedModule (Submonoid.powers e) (dualizingModule F)) :=
      LocalizedModule.moduleOfIsLocalization
        (R := B) (S := Submonoid.powers e) (M := dualizingModule F) (T := C)
    let : Module A (LocalizedModule (Submonoid.powers e) (dualizingModule F)) :=
      Module.compHom _ (algebraMap A C)
    let : IsScalarTower A C (LocalizedModule (Submonoid.powers e) (dualizingModule F)) :=
      IsScalarTower.of_compHom A C _
    IsScalarTower A C (LocalizedModule (Submonoid.powers e) (dualizingModule F)) ∧
    Module.Flat A (LocalizedModule (Submonoid.powers e) (dualizingModule F)) := by
  let : Module C (LocalizedModule (Submonoid.powers e) (dualizingModule F)) :=
    LocalizedModule.moduleOfIsLocalization
      (R := B) (S := Submonoid.powers e) (M := dualizingModule F) (T := C)
  let : Module A (LocalizedModule (Submonoid.powers e) (dualizingModule F)) :=
    Module.compHom _ (algebraMap A C)
  let : IsScalarTower A C
      (LocalizedModule (Submonoid.powers e) (dualizingModule F)) :=
    IsScalarTower.of_compHom A C _
  let localizationMap :=
    LocalizedModule.mkLinearMap (Submonoid.powers e) (dualizingModule F)
  let hM : IsLocalizedModule (Submonoid.powers e) localizationMap := inferInstance
  let e' := localizedModule_dualizingModule_equiv e F G localizationMap hM
  let : Module A (dualizingModule G) := Module.compHom _ (algebraMap A C)
  let : IsScalarTower A C (dualizingModule G) := IsScalarTower.of_compHom A C _
  let : Module.Flat A (dualizingModule G) := dualizingModule_flat_of_finite_flat G
  exact ⟨inferInstance, Module.Flat.of_linearEquiv (e'.restrictScalars A)⟩

/-- **Stacks Project, Tag 0BVE.** The relative dualizing module of a flat quasi-finite
homomorphism of Noetherian rings is flat over the base ring. -/
@[stacks 0BVE]
public lemma dualizingModule_flat
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra.FiniteType A B]
    [Algebra.QuasiFinite A B] [Module.Flat A B]
    (F : FiniteOpenFactorization.{u, v, w} A B) :
    letI : Module A (dualizingModule F) :=
      Module.compHom (dualizingModule F) (algebraMap A B)
    Module.Flat A (dualizingModule F) := by
  let : Module A (dualizingModule F) := Module.compHom _ (algebraMap A B)
  let : IsScalarTower A B (dualizingModule F) := IsScalarTower.of_compHom A B _
  refine Module.flat_of_isLocalized_maximal B (dualizingModule F)
    (fun q _ => LocalizedModule.AtPrime q (dualizingModule F))
    (fun q _ => LocalizedModule.mkLinearMap q.primeCompl (dualizingModule F)) ?_
  intro q hq
  let : q.IsPrime := hq.isPrime
  let p := q.comap (algebraMap A B)
  let : p.IsPrime := Ideal.comap_isPrime _ _
  let : q.LiesOver p := ⟨rfl⟩
  obtain ⟨A', hA'comm, hA'algebra, hA'etale, p', hp', hp'p, e, he, q', hq', hq'p,
    hq'q, heq', hres, hfinite, huniq⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq p q
  let : Algebra A A' := hA'algebra
  let B' := A' ⊗[A] B
  let : Algebra A' B' := Algebra.TensorProduct.leftAlgebra
  let : Algebra B B' := Algebra.TensorProduct.rightAlgebra
  let : IsNoetherianRing A' := Algebra.FiniteType.isNoetherianRing A A'
  let : Algebra.FiniteType A' B' := inferInstance
  let : IsNoetherianRing B' := Algebra.FiniteType.isNoetherianRing A' B'
  let : Algebra B' (Localization.Away e) := inferInstance
  let : Algebra A' (Localization.Away e) := inferInstance
  let : IsScalarTower A' B' (Localization.Away e) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite A' (Localization.Away e) := hfinite
  let : Module.Flat A' B' := Module.Flat.baseChange A A' B
  let : Module.Flat B' (Localization.Away e) :=
    IsLocalization.flat (Localization.Away e) (Submonoid.powers e)
  let : Module.Flat A' (Localization.Away e) :=
    Module.Flat.trans A' B' (Localization.Away e)
  let F' := FiniteOpenFactorization.baseChange F A'
  let G : FiniteOpenFactorization A' (Localization.Away e) := identityFactorization
  let moduleAaway : Module A' (Localization.Away e) :=
    (algebraMap A' (Localization.Away e)).toModule
  let (priority := 100000) : Module A' (Localization.Away e) := moduleAaway
  let (priority := 100000) : DistribMulAction A' (Localization.Away e) :=
    moduleAaway.toDistribMulAction
  let (priority := 100000) : SMul A' (Localization.Away e) := moduleAaway.toSMul
  obtain ⟨_, haway⟩ := localizedDualizingModule_flat_of_finite_flat e F' G
  let qC : Ideal (Localization.Away e) := Ideal.map (algebraMap B' (Localization.Away e)) q'
  have heDisj : Disjoint (Submonoid.powers e : Set B') (q' : Set B') := by
    rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]
  let : qC.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers e) _ q' hq' heDisj
  let : qC.LiesOver q' :=
    IsLocalization.liesOver_map_of_isPrime_disjoint (Submonoid.powers e) _ heDisj
  let Cq := Localization.AtPrime qC
  let N := LocalizedModule (Submonoid.powers e) (dualizingModule F')
  let moduleAwayN : Module (Localization.Away e) N :=
    LocalizedModule.moduleOfIsLocalization
      (R := B') (S := Submonoid.powers e) (M := dualizingModule F')
      (T := Localization.Away e)
  let (priority := 100000) : Module (Localization.Away e) N := moduleAwayN
  let (priority := 100000) : DistribMulAction (Localization.Away e) N :=
    moduleAwayN.toDistribMulAction
  let (priority := 100000) : SMul (Localization.Away e) N := moduleAwayN.toSMul
  let moduleAN : Module A' N := Module.compHom N (algebraMap A' (Localization.Away e))
  let distribAN : DistribMulAction A' N :=
    DistribMulAction.compHom N (algebraMap A' (Localization.Away e)).toMonoidHom
  let (priority := 100000) : Module A' N := moduleAN
  let (priority := 100000) : DistribMulAction A' N := distribAN
  let (priority := 100000) : MulAction A' N := distribAN.toMulAction
  let (priority := 100000) : SMul A' N := distribAN.toDistribSMul.toSMul
  let : IsScalarTower A' (Localization.Away e) N :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : Module.Flat A' N := haway
  let Nq := Cq ⊗[Localization.Away e] N
  let fN : N →ₗ[Localization.Away e] Nq := TensorProduct.mk _ _ _ 1
  have hfN : IsBaseChange Cq fN := TensorProduct.isBaseChange _ _ _
  let : Module (Localization.Away e) Cq := Algebra.toModule
  let : Module A' Cq := Algebra.toModule
  let : Module.Flat A' Nq :=
    Module.Flat.tensorProduct_of_flat_left (A := A') (C := Localization.Away e) (D := Cq) (P := N)
  let Bq := Localization.AtPrime q
  let M := dualizingModule F
  let Mq := LocalizedModule.AtPrime q M
  let fAt : M →ₗ[B] Mq := LocalizedModule.mkLinearMap q.primeCompl M
  have hfAt : IsBaseChange Bq fAt := IsLocalizedModule.isBaseChange q.primeCompl Bq fAt
  let : Module.Flat A A' := Algebra.Smooth.flat A A'
  let : Module.Flat B B' := by
    let : Algebra.IsPushout A B A' B' := Algebra.IsPushout.symm inferInstance
    exact Module.Flat.isBaseChange A B A' B' Algebra.IsPushout.out
  let : Module.Flat (Localization.Away e) Cq :=
    IsLocalization.flat Cq (Algebra.algebraMapSubmonoid (Localization.Away e) qC.primeCompl)
  let : q'.LiesOver q := ⟨hq'q.symm⟩
  let : qC.LiesOver q := Ideal.LiesOver.trans qC q' q
  let : Algebra Bq Cq := Localization.AtPrime.algebraOfLiesOver q qC
  let : IsScalarTower B Bq Cq := inferInstance
  let : Module.Flat B Cq := Module.Flat.trans B (Localization.Away e) Cq
  let : Module.Flat Bq Cq :=
    (Module.flat_iff_of_isLocalization Bq q.primeCompl Cq).mpr inferInstance
  let : Module.FaithfullyFlat Bq Cq := Module.FaithfullyFlat.of_flat_of_isLocalHom
  let fBC := dualizingModule.baseChange F A'
  have hfBC := dualizingModule_isBaseChange_of_flat F A'
  let : Module B (dualizingModule F') := Module.compHom _ (algebraMap B B')
  let : IsScalarTower B B' (dualizingModule F') := IsScalarTower.of_compHom B B' _
  let : IsScalarTower B' (Localization.Away e) N := inferInstance
  let : IsScalarTower B' Cq Nq := inferInstance
  let : IsScalarTower B B' Nq := inferInstance
  let : IsScalarTower B Cq Nq := inferInstance
  let : IsScalarTower Bq Cq Nq := inferInstance
  let : IsScalarTower B Bq Nq := inferInstance
  let fAway := LocalizedModule.mkLinearMap (Submonoid.powers e) (dualizingModule F')
  have hfAway : IsBaseChange (Localization.Away e) fAway :=
    IsLocalizedModule.isBaseChange (Submonoid.powers e) (Localization.Away e) fAway
  let fLoc : dualizingModule F' →ₗ[A' ⊗[A] B] Nq :=
    (fN.restrictScalars (A' ⊗[A] B)).comp fAway
  have hfLoc : IsBaseChange Cq fLoc := hfAway.comp hfN
  have hcomp : IsBaseChange Cq ((fLoc.restrictScalars B).comp fBC) :=
    hfBC.comp hfLoc
  let f0 : M →ₗ[B] Nq := (fLoc.restrictScalars B).comp fBC
  let g : Mq →ₗ[Bq] Nq := hfAt.lift f0
  have hg : IsBaseChange Cq g := (IsBaseChange.comp_iff hfAt).mp (by rwa [hfAt.lift_comp])
  let : IsScalarTower A A' Nq := inferInstance
  let : Module.Flat A Nq := Module.Flat.trans A A' Nq
  let : IsScalarTower A Bq Nq := inferInstance
  have : Module.Flat A (Cq ⊗[Bq] Mq) := Module.Flat.of_linearEquiv (hg.equiv.restrictScalars A)
  exact Module.Flat.of_tensorProduct_of_faithfullyFlat (A := A) (C := Bq) (D := Cq) (P := Mq)

end Stacks.Discriminant
