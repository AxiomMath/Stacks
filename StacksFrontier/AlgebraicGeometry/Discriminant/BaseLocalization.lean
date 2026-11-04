module

public import Mathlib.RingTheory.Flat.Localization
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.DualizingModulesQuasi.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleRestriction
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleLocalization

/-!
# Replacing the base by a localization through which the map factors

Let `A → B` be a quasi-finite map of Noetherian rings which factors through the localization
`A_f` of the base away from an element `f`. Then the relative dualizing module of `B` over `A`
and the relative dualizing module of `B` over `A_f` agree. This file constructs that
identification, computes it on pure tensors, and shows that it does not depend on either of the
two finite-open factorizations used to define the two dualizing modules.

## Main definitions

* `Stacks.Discriminant.dualizingModule_equiv_of_isLocalization_away` is the identification of
  the two relative dualizing modules.

## Main results

* `Stacks.Discriminant.dualizingModule_equiv_of_isLocalization_away_tmul` characterizes the
  identification on a pure tensor: a functional is carried to its scalar extension.
* `Stacks.Discriminant.dualizingModule_equiv_of_isLocalization_away_natural`: the identification
  commutes with the canonical comparisons of factorizations on both sides.

## Implementation notes

The identification is assembled from three moves. Flat base change along `A → A_f` replaces the
dualizing module of the original factorization by that of its base change, whose target is
`A_f ⊗[A] B`; since `f` is already invertible in `B`, that target is `B` again, and transporting
the factorization along this isomorphism gives a finite-open factorization of `B` over `A_f`;
the canonical comparison of factorizations over `A_f` then reaches the given one.

Naturality is proved on pure tensors after refining both factorizations of `B` over `A` to a
common one, which is where the injectivity of the refined intermediate algebra into `B` is used.

## References

* [Stacks Project, Tag 0BT2](https://stacks.math.columbia.edu/tag/0BT2)
-/

@[expose] public section

namespace Stacks.Discriminant

universe u v w x y z t

open Topology
open scoped TensorProduct

attribute [local instance] algebraDualModule

/-- `Af ⊗[A] B` is an `Af`-`B`-tower for the right `B`-algebra structure, when `A → B` factors
through `Af`. -/
private theorem isScalarTower_tensor_right
    {A : Type*} {B : Type*} {Af : Type*} [CommRing A] [CommRing B] [CommRing Af]
    [Algebra A B] [Algebra A Af] [Algebra Af B] [IsScalarTower A Af B]
    (f : A) [IsLocalization.Away f Af] :
    letI : Algebra B (Af ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
    IsScalarTower Af B (Af ⊗[A] B) :=
  letI : Algebra B (Af ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  IsScalarTower.of_algebraMap_eq' (by
    apply IsLocalization.ringHom_ext (.powers f)
    ext a
    change (algebraMap A Af a) ⊗ₜ[A] (1 : B) =
      (1 : Af) ⊗ₜ[A] algebraMap Af B (algebraMap A Af a)
    rw [← IsScalarTower.algebraMap_apply A Af B a]
    exact Algebra.TensorProduct.tmul_one_eq_one_tmul a)

/-- **Stacks Project, Tag 0BT2, part (1).** If `A → B` factors through the localization of
`A` away from `f`, then computing the relative dualizing module over that localization does not
change it. -/
@[stacks 0BT2 "part (1)"]
public noncomputable def dualizingModule_equiv_of_isLocalization_away
    {A : Type u} {B : Type v} {Af : Type w}
    [CommRing A] [CommRing B] [CommRing Af]
    [Algebra A B] [Algebra A Af] [Algebra Af B] [IsScalarTower A Af B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra.QuasiFinite A B]
    (f : A) [IsLocalization.Away f Af]
    (F : FiniteOpenFactorization.{u, v, x} A B)
    (G : FiniteOpenFactorization.{w, v, y} Af B) :
    dualizingModule F ≃ₗ[B] dualizingModule G := by
  let Fbc := FiniteOpenFactorization.baseChange F Af
  let E := Af ⊗[A] B
  letI : Algebra B E := Algebra.TensorProduct.rightAlgebra
  letI : IsScalarTower Af B E := IsScalarTower.of_algebraMap_eq' (by
    apply IsLocalization.ringHom_ext (.powers f)
    ext a
    change (algebraMap A Af a) ⊗ₜ[A] (1 : B) =
      (1 : Af) ⊗ₜ[A] algebraMap Af B (algebraMap A Af a)
    rw [← IsScalarTower.algebraMap_apply A Af B a]
    exact Algebra.TensorProduct.tmul_one_eq_one_tmul a)
  letI : IsNoetherianRing Af :=
    IsLocalization.isNoetherianRing (Submonoid.powers f) Af inferInstance
  let g := algebraMap A B f
  have hg : IsUnit g := by
    have h := IsLocalization.Away.algebraMap_isUnit (R := A) (S := Af) f
    change IsUnit (algebraMap A B f)
    rw [IsScalarTower.algebraMap_apply A Af B f]
    exact h.map (algebraMap Af B)
  letI : Algebra B (Af ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  letI : IsLocalization.Away g B :=
    IsLocalization.away_of_isUnit_of_bijective (S := B) (r := g) hg
      Function.bijective_id
  letI : Algebra B (B ⊗[A] Af) := Algebra.TensorProduct.leftAlgebra
  letI : IsScalarTower A B (B ⊗[A] Af) := IsScalarTower.of_algebraMap_eq' (by
    ext a
    simp [Algebra.TensorProduct.algebraMap_apply])
  let eSwapRing : (Af ⊗[A] B) ≃+* (B ⊗[A] Af) :=
    (Algebra.TensorProduct.comm A Af B).toRingEquiv
  let eSwap : Af ⊗[A] B ≃ₐ[B] B ⊗[A] Af :=
    AlgEquiv.ofRingEquiv (f := eSwapRing) (by
      intro b
      change Algebra.TensorProduct.comm A Af B (1 ⊗ₜ[A] b) = b ⊗ₜ[A] 1
      simp)
  let eTensor : B ⊗[A] Af ≃ₐ[B] Localization.Away g :=
    IsLocalization.Away.tensorEquiv (R := A) (S := B) f Af
  let eAway : Localization.Away g ≃ₐ[B] B :=
    IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g) B
  let eB := eSwap.trans (eTensor.trans eAway)
  let eAf := eB.restrictScalars Af
  letI : Module B (dualizingModule Fbc) := Module.compHom _ (algebraMap B E)
  letI : IsScalarTower B E (dualizingModule Fbc) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  letI : CommRing Fbc.middle := Fbc.commRingMiddle
  letI : Algebra Af Fbc.middle := Fbc.algebraMiddle
  letI : Algebra Fbc.middle E := Fbc.algebraTarget
  letI : IsScalarTower Af Fbc.middle E := Fbc.scalarTower
  let target : Fbc.middle →+* B := eAf.toRingHom.comp (algebraMap Fbc.middle E)
  letI : Algebra Fbc.middle B := target.toAlgebra
  have hTower : IsScalarTower Af Fbc.middle B := IsScalarTower.of_algebraMap_eq' (by
    ext a
    change algebraMap Af B a = target (algebraMap Af Fbc.middle a)
    calc
      algebraMap Af B a = eAf (algebraMap Af E a) := (eAf.commutes a).symm
      _ = eAf (algebraMap Fbc.middle E (algebraMap Af Fbc.middle a)) := by
        rw [IsScalarTower.algebraMap_apply Af Fbc.middle E a]
      _ = target (algebraMap Af Fbc.middle a) := rfl)
  have hOpen : Topology.IsOpenEmbedding (PrimeSpectrum.comap target) := by
    have hHome : IsHomeomorph (PrimeSpectrum.comap eAf.toRingHom) :=
      PrimeSpectrum.isHomeomorph_comap_of_bijective eAf.bijective
    have hcomp : PrimeSpectrum.comap target =
        (PrimeSpectrum.comap (algebraMap Fbc.middle E)) ∘
          (PrimeSpectrum.comap eAf.toRingHom) := by
      rw [PrimeSpectrum.comap_comp]
    rw [hcomp]
    exact Fbc.isOpenEmbedding_comap.comp hHome.isOpenEmbedding
  let Fret : FiniteOpenFactorization Af B := by
    refine {
      middle := Fbc.middle
      commRingMiddle := Fbc.commRingMiddle
      algebraMiddle := Fbc.algebraMiddle
      algebraTarget := target.toAlgebra
      scalarTower := hTower
      finite_middle := Fbc.finite_middle
      isOpenEmbedding_comap := hOpen
      awayMap_bijective := ?_ }
    intro c hc
    let d := algebraMap Fbc.middle E c
    let b := algebraMap Fbc.middle B c
    have hdb : eAf d = b := rfl
    let TD := Localization.Away d
    let TB := Localization.Away b
    have : IsLocalization.Away (eAf d) TB := by
      rw [show eAf d = b from hdb]
      infer_instance
    let eAway : TD →+* TB := IsLocalization.Away.map TD TB eAf.toRingHom d
    have hAwayBij : Function.Bijective eAway := by
      constructor
      · change Function.Injective (IsLocalization.map TB eAf.toRingHom _)
        exact IsLocalization.map_injective_of_injective _ _ _ eAf.bijective.1
      · change Function.Surjective (IsLocalization.map TB eAf.toRingHom _)
        exact IsLocalization.map_surjective_of_surjective _ _ _ eAf.bijective.2
    have hAwayComp : eAway.comp
        (Localization.awayMap (algebraMap Fbc.middle E) c) =
        Localization.awayMap (algebraMap Fbc.middle B) c := by
      apply IsLocalization.ringHom_ext (.powers c)
      ext a
      have hleft : Localization.awayMap (algebraMap Fbc.middle E) c
          (algebraMap Fbc.middle (Localization.Away c) a) =
          algebraMap E TD (algebraMap Fbc.middle E a) := by
        rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
      have hright : Localization.awayMap (algebraMap Fbc.middle B) c
          (algebraMap Fbc.middle (Localization.Away c) a) =
          algebraMap B TB (algebraMap Fbc.middle B a) := by
        rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
      have hmap (x : E) :
          eAway (algebraMap E TD x) = algebraMap B TB (eAf.toRingHom x) := by
        change IsLocalization.map TB eAf.toRingHom _ (algebraMap E TD x) = _
        rw [IsLocalization.map_eq]
      change eAway (Localization.awayMap (algebraMap Fbc.middle E) c
          (algebraMap Fbc.middle (Localization.Away c) a)) =
        Localization.awayMap (algebraMap Fbc.middle B) c
          (algebraMap Fbc.middle (Localization.Away c) a)
      rw [hleft, hmap, hright]
      rfl
    have hcOld : (PrimeSpectrum.basicOpen c : Set (PrimeSpectrum Fbc.middle)) ⊆
        Set.range (PrimeSpectrum.comap (algebraMap Fbc.middle E)) := by
      intro p hp
      obtain ⟨q, hq⟩ := hc hp
      refine ⟨PrimeSpectrum.comap eAf.toRingHom q, ?_⟩
      apply PrimeSpectrum.ext
      change Ideal.comap (algebraMap Fbc.middle E)
          (Ideal.comap eAf.toRingHom q.asIdeal) = p.asIdeal
      rw [Ideal.comap_comap]
      change Ideal.comap target q.asIdeal = p.asIdeal
      exact congrArg PrimeSpectrum.asIdeal hq
    rw [← hAwayComp]
    exact hAwayBij.comp (Fbc.awayMap_bijective c hcOld)
  letI : Module B (dualizingModule Fret) := dualizingModule.instModule Fret
  letI : IsScalarTower Fbc.middle B E := IsScalarTower.of_algebraMap_eq' (by
    ext c
    apply eAf.injective
    calc
      eAf (algebraMap Fbc.middle E c) = algebraMap Fbc.middle B c := rfl
      _ = eAf (algebraMap B E (algebraMap Fbc.middle B c)) := by
        symm
        change eB (algebraMap B E (algebraMap Fbc.middle B c)) = _
        exact eB.commutes (algebraMap Fbc.middle B c))
  letI : Module E (dualizingModule Fbc) := dualizingModule.instModule Fbc
  let M₀ := Module.Dual Af Fbc.middle
  letI : Module Fbc.middle M₀ := algebraDualModule Af Fbc.middle
  letI : AddCommGroup (M₀ ⊗[Fbc.middle] E) := by
    change AddCommGroup (dualizingModule Fbc)
    exact dualizingModule.instAddCommGroup Fbc
  letI : AddCommGroup (M₀ ⊗[Fbc.middle] B) := by
    change AddCommGroup (dualizingModule Fret)
    exact dualizingModule.instAddCommGroup Fret
  letI : Module E (M₀ ⊗[Fbc.middle] E) :=
    (TensorProduct.comm Fbc.middle M₀ E).toAddEquiv.module E
  letI : Module B (M₀ ⊗[Fbc.middle] B) :=
    (TensorProduct.comm Fbc.middle M₀ B).toAddEquiv.module B
  let eC : E ≃ₐ[Fbc.middle] B :=
    AlgEquiv.ofRingEquiv (f := eAf.toRingEquiv) (fun _ => rfl)
  let eTensor : (M₀ ⊗[Fbc.middle] E) ≃ₗ[Fbc.middle]
      (M₀ ⊗[Fbc.middle] B) := LinearEquiv.lTensor M₀ eC.toLinearEquiv
  let eAdd : dualizingModule Fbc ≃+ dualizingModule Fret := {
    toFun := fun z => eTensor z
    invFun := fun z => eTensor.symm z
    left_inv := eTensor.left_inv
    right_inv := eTensor.right_inv
    map_add' := eTensor.map_add }
  let eRet : dualizingModule Fbc ≃ₗ[B] dualizingModule Fret :=
    eAdd.toLinearEquiv (by
      intro b z
      change eTensor ((algebraMap B E b) • z) = b • eTensor z
      induction z using TensorProduct.induction_on with
      | zero =>
        calc
          eTensor ((algebraMap B E b) • (0 : M₀ ⊗[Fbc.middle] E)) =
              eTensor 0 := by rw [smul_zero]
          _ = 0 := map_zero eTensor
      | add z z' hz hz' =>
        calc
          eTensor ((algebraMap B E b) • (z + z')) =
              eTensor ((algebraMap B E b) • z + (algebraMap B E b) • z') := by
            rw [smul_add]
          _ = eTensor ((algebraMap B E b) • z) +
              eTensor ((algebraMap B E b) • z') := eTensor.map_add _ _
          _ = b • eTensor z + b • eTensor z' := congrArg₂ (· + ·) hz hz'
          _ = b • eTensor (z + z') := by rw [eTensor.map_add, ← smul_add]
      | tmul φ d =>
        change eTensor ((TensorProduct.comm Fbc.middle M₀ E).symm
            ((algebraMap B E b) • (d ⊗ₜ[Fbc.middle] φ))) =
          (TensorProduct.comm Fbc.middle M₀ B).symm (b • (eAf d ⊗ₜ[Fbc.middle] φ))
        simp only [TensorProduct.smul_tmul', TensorProduct.comm_symm_tmul,
          Algebra.smul_def]
        change eTensor (φ ⊗ₜ[Fbc.middle] ((algebraMap B E b) * d)) =
          φ ⊗ₜ[Fbc.middle] (b * eAf d)
        have hPure : eTensor (φ ⊗ₜ[Fbc.middle] ((algebraMap B E b) * d)) =
            φ ⊗ₜ[Fbc.middle] eC ((algebraMap B E b) * d) := by
          simp [eTensor]
        have hb' : eC (algebraMap B E b) = b := by
          change eB (algebraMap B E b) = b
          exact eB.commutes b
        have hcoeff : eC ((algebraMap B E b) * d) = b * eAf d := by
          calc
            eC ((algebraMap B E b) * d) =
                eC (algebraMap B E b) * eC d := map_mul eC.toRingHom _ _
            _ = b * eAf d := by rw [hb']; rfl
        rw [hPure, hcoeff])
  letI : Module.Flat A Af := IsLocalization.flat Af (Submonoid.powers f)
  let hBC := dualizingModule_isBaseChange_of_flat F Af
  let eBC : E ⊗[B] dualizingModule F ≃ₗ[B] dualizingModule Fbc :=
    hBC.equiv.restrictScalars B
  let eTensor : E ⊗[B] dualizingModule F ≃ₗ[B]
      B ⊗[B] dualizingModule F :=
    LinearEquiv.rTensor (M := dualizingModule F) eB.toLinearEquiv
  let eSource := eTensor.trans (TensorProduct.lid B (dualizingModule F))
  exact (eSource.symm.trans
    (eBC.trans eRet)).trans
      (dualizingModuleEquiv Fret G)

/-- The base-localization identification on a pure tensor, through the explicit
factorizations used to construct it. -/
private theorem dualizingModule_equiv_of_isLocalization_away_tmul_aux
    {A : Type u} {B : Type v} {Af : Type w}
    [CommRing A] [CommRing B] [CommRing Af]
    [Algebra A B] [Algebra A Af] [Algebra Af B] [IsScalarTower A Af B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra.QuasiFinite A B]
    (f : A) [IsLocalization.Away f Af]
    (F : FiniteOpenFactorization.{u, v, x} A B)
    (G : FiniteOpenFactorization.{w, v, y} Af B)
    (φ : Module.Dual A F.middle) (b : B) :
    let Fbc := FiniteOpenFactorization.baseChange F Af
    let E := Af ⊗[A] B
    letI : Algebra B E := Algebra.TensorProduct.rightAlgebra
    letI : IsScalarTower Af B E := isScalarTower_tensor_right f
    letI : IsNoetherianRing Af :=
      IsLocalization.isNoetherianRing (Submonoid.powers f) Af inferInstance
    letI : Module.Flat A Af := IsLocalization.flat Af (Submonoid.powers f)
    let eB := baseChangeTargetEquiv (A := A) (B := B) (Af := Af) f
    let eAf := eB.restrictScalars Af
    let Fret := retargetFactorization Fbc eAf
    letI : Module B (dualizingModule Fret) := dualizingModule.instModule Fret
    let φC : Module.Dual Af Fbc.middle := Module.Dual.baseChange Af φ
    dualizingModule_equiv_of_isLocalization_away f F G (dualizingModule.tmul F φ b) =
      dualizingModuleEquiv Fret G
        (dualizingModule.tmul Fret φC b) := by
  classical
  let Fbc := FiniteOpenFactorization.baseChange F Af
  let E := Af ⊗[A] B
  let : Algebra B E := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower Af B E := isScalarTower_tensor_right f
  let eB := baseChangeTargetEquiv (A := A) (B := B) (Af := Af) f
  let eAf := eB.restrictScalars Af
  let : IsNoetherianRing Af :=
    IsLocalization.isNoetherianRing (Submonoid.powers f) Af inferInstance
  let Fret := retargetFactorization Fbc eAf
  let : Module B (dualizingModule Fbc) := Module.compHom _ (algebraMap B E)
  let : IsScalarTower B E (dualizingModule Fbc) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let : Module B (dualizingModule Fret) := dualizingModule.instModule Fret
  let : Module.Flat A Af := IsLocalization.flat Af (Submonoid.powers f)
  let hBC := dualizingModule_isBaseChange_of_flat F Af
  let eBC : E ⊗[B] dualizingModule F ≃ₗ[B] dualizingModule Fbc :=
    hBC.equiv.restrictScalars B
  have heAfTarget : ∀ b : B, eAf (algebraMap B E b) = b := fun b => eB.commutes b
  let eRet := dualizingModule_retargetEquiv Fbc eAf heAfTarget
  let eTensor : E ⊗[B] dualizingModule F ≃ₗ[B]
      B ⊗[B] dualizingModule F :=
    LinearEquiv.rTensor (M := dualizingModule F) eB.toLinearEquiv
  let eSource := eTensor.trans (TensorProduct.lid B (dualizingModule F))
  let φC : Module.Dual Af Fbc.middle := Module.Dual.baseChange Af φ
  have hSource : eSource.symm (dualizingModule.tmul F φ b) =
      (1 : E) ⊗ₜ[B] dualizingModule.tmul F φ b := by
    simp [eSource, eTensor, LinearEquiv.rTensor_tmul]
  have hBase : eBC ((1 : E) ⊗ₜ[B] dualizingModule.tmul F φ b) =
      dualizingModule.tmul Fbc φC ((1 : Af) ⊗ₜ[A] b) := by
    show hBC.equiv ((1 : E) ⊗ₜ[B] dualizingModule.tmul F φ b) = _
    rw [IsBaseChange.equiv_tmul, one_smul,
      dualizingModule.baseChange_tmul]
  have hRet : eRet (dualizingModule.tmul Fbc φC ((1 : Af) ⊗ₜ[A] b)) =
      dualizingModule.tmul Fret φC b := by
    have hd : eAf ((1 : Af) ⊗ₜ[A] b) = b := by
      show eB (algebraMap B E b) = b
      exact eB.commutes b
    simp only [eRet, Fret]
    rw [dualizingModule_retargetEquiv_tmul, hd]
  show dualizingModuleEquiv Fret G
      ((eSource.symm.trans (eBC.trans eRet)) (dualizingModule.tmul F φ b)) = _
  simp only [LinearEquiv.trans_apply]
  rw [hSource, hBase, hRet]

/-- The base-localization identification carries a functional to its scalar extension along a
compatible finite-open factorization.  The displayed equation characterizes this operation on
generators and avoids treating the equivalence as an arbitrary module isomorphism. -/
@[stacks 0BT2 "part (1), characterization"]
public theorem dualizingModule_equiv_of_isLocalization_away_tmul
    {A : Type u} {B : Type v} {Af : Type w}
    [CommRing A] [CommRing B] [CommRing Af]
    [Algebra A B] [Algebra A Af] [Algebra Af B] [IsScalarTower A Af B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra.QuasiFinite A B]
    (f : A) [IsLocalization.Away f Af]
    (F : FiniteOpenFactorization.{u, v, x} A B)
    (G : FiniteOpenFactorization.{w, v, y} Af B)
    [Algebra A G.middle] [IsScalarTower A Af G.middle]
    (r : F.middle →ₐ[A] G.middle)
    (hrloc : letI := r.toRingHom.toAlgebra
      IsLocalization.Away (algebraMap A F.middle f) G.middle)
    (hr : ∀ c : F.middle,
      G.algebraTarget.algebraMap (r c) = F.algebraTarget.algebraMap c)
    (φ : Module.Dual A F.middle) (ψ : Module.Dual Af G.middle)
    (hψ : ∀ c : F.middle, ψ (r c) = algebraMap A Af (φ c)) (b : B) :
    dualizingModule_equiv_of_isLocalization_away f F G
        (dualizingModule.tmul F φ b) = dualizingModule.tmul G ψ b :=
  by
    classical
    let Fbc := FiniteOpenFactorization.baseChange F Af
    let E := Af ⊗[A] B
    let : Algebra B E := Algebra.TensorProduct.rightAlgebra
    let : IsScalarTower Af B E := isScalarTower_tensor_right f
    let eB := baseChangeTargetEquiv (A := A) (B := B) (Af := Af) f
    let eAf := eB.restrictScalars Af
    let : IsNoetherianRing Af :=
      IsLocalization.isNoetherianRing (Submonoid.powers f) Af inferInstance
    let Fret := retargetFactorization Fbc eAf
    let : Algebra Fbc.middle B := Fret.algebraTarget
    let : IsScalarTower Af Fbc.middle B := Fret.scalarTower
    let : Module Fbc.middle B := Fret.algebraTarget.toModule
    let φC : Module.Dual Af Fbc.middle := Module.Dual.baseChange Af φ
    let : CommRing F.middle := F.commRingMiddle
    let : Algebra A F.middle := F.algebraMiddle
    let : Algebra F.middle G.middle := r.toRingHom.toAlgebra
    let : IsScalarTower A F.middle G.middle := IsScalarTower.of_algebraMap_eq' (by
      ext a
      exact (r.commutes a).symm)
    let : IsLocalization.Away (algebraMap A F.middle f) G.middle := hrloc
    let : CommRing Fbc.middle := Fbc.commRingMiddle
    let : Algebra Af Fbc.middle := Fbc.algebraMiddle
    let : Algebra A Fbc.middle := Algebra.compHom Fbc.middle (algebraMap A Af)
    let : IsScalarTower A Af Fbc.middle := IsScalarTower.of_algebraMap_eq' (by
      ext a
      rfl)
    let : Algebra F.middle Fbc.middle := Algebra.TensorProduct.rightAlgebra
    let : IsScalarTower A F.middle Fbc.middle := IsScalarTower.of_algebraMap_eq' (by
      ext a
      show (algebraMap A Af a) ⊗ₜ[A] (1 : F.middle) =
        (1 : Af) ⊗ₜ[A] algebraMap A F.middle a
      exact Algebra.TensorProduct.tmul_one_eq_one_tmul a)
    let : Algebra F.middle (F.middle ⊗[A] Af) := Algebra.TensorProduct.leftAlgebra
    let eSwapRing : Fbc.middle ≃+* F.middle ⊗[A] Af :=
      (Algebra.TensorProduct.comm A Af F.middle).toRingEquiv
    let eSwap : Fbc.middle ≃ₐ[F.middle] F.middle ⊗[A] Af :=
      AlgEquiv.ofRingEquiv (f := eSwapRing) (by
        intro c
        show Algebra.TensorProduct.comm A Af F.middle (1 ⊗ₜ[A] c) = c ⊗ₜ[A] 1
        simp)
    let eLoc : F.middle ⊗[A] Af ≃ₐ[F.middle]
        Localization.Away (algebraMap A F.middle f) :=
      IsLocalization.Away.tensorEquiv (R := A) (S := F.middle) f Af
    let eToG : Localization.Away (algebraMap A F.middle f) ≃ₐ[F.middle]
        G.middle :=
      IsLocalization.algEquiv (Submonoid.powers (algebraMap A F.middle f))
        _ G.middle
    let eMiddle := eSwap.trans (eLoc.trans eToG)
    have heAf : eMiddle.toRingEquiv.toRingHom.comp (algebraMap Af Fbc.middle) =
        algebraMap Af G.middle := by
      apply IsLocalization.ringHom_ext (Submonoid.powers f)
      ext a
      simp only [RingHom.comp_apply]
      rw [← IsScalarTower.algebraMap_apply A Af Fbc.middle a,
        ← IsScalarTower.algebraMap_apply A Af G.middle a]
      show eMiddle (algebraMap A Fbc.middle a) = algebraMap A G.middle a
      rw [IsScalarTower.algebraMap_apply A F.middle Fbc.middle a,
        IsScalarTower.algebraMap_apply A F.middle G.middle a]
      simp [eMiddle, eSwap, eLoc, eToG]
    let eAfMiddle : Fbc.middle ≃ₐ[Af] G.middle :=
      AlgEquiv.ofRingEquiv (f := eMiddle.toRingEquiv) (fun a =>
        congrArg (fun k : Af →+* G.middle => k a) heAf)
    let q := eAfMiddle.symm.toAlgHom
    have hqr (c : F.middle) :
        q (r c) = algebraMap F.middle Fbc.middle c := by
      apply eAfMiddle.injective
      show eAfMiddle (eAfMiddle.symm (r c)) =
        eAfMiddle (algebraMap F.middle Fbc.middle c)
      rw [eAfMiddle.apply_symm_apply]
      calc
        r c = algebraMap F.middle G.middle c := rfl
        _ = eMiddle (algebraMap F.middle Fbc.middle c) := by
          simp only [eMiddle, AlgEquiv.trans_apply]
          rw [eSwap.commutes, eLoc.commutes, eToG.commutes]
    have hTarget :
        (algebraMap Fbc.middle E).comp q.toRingHom =
          (algebraMap B E).comp (algebraMap G.middle B) := by
      apply IsLocalization.ringHom_ext (Submonoid.powers (algebraMap A F.middle f))
      ext c
      show algebraMap Fbc.middle E (q (r c)) =
        algebraMap B E (G.algebraTarget.algebraMap (r c))
      rw [hqr]
      rw [hr]
      show Algebra.TensorProduct.map (AlgHom.id A Af)
          (IsScalarTower.toAlgHom A F.middle B) ((1 : Af) ⊗ₜ[A] c) =
        (1 : Af) ⊗ₜ[A] algebraMap F.middle B c
      rw [Algebra.TensorProduct.map_tmul]
      simp
    have hFunc : φC.comp q.toLinearMap = ψ := by
      ext z
      let fAf : Af := algebraMap A Af f
      let fF : F.middle := algebraMap A F.middle f
      have hfAf : IsUnit fAf := IsLocalization.Away.algebraMap_isUnit (R := A) (S := Af) f
      obtain ⟨n, c, hcz⟩ := IsLocalization.Away.surj
        (R := F.middle) (S := G.middle) (algebraMap A F.middle f) z
      have hden : algebraMap F.middle G.middle (fF ^ n) =
          algebraMap Af G.middle (fAf ^ n) := by
        have hF : algebraMap F.middle G.middle fF = algebraMap A G.middle f := by
          simpa [fF] using (IsScalarTower.algebraMap_apply A F.middle G.middle f).symm
        have hAf : algebraMap Af G.middle fAf = algebraMap A G.middle f := by
          simpa [fAf] using (IsScalarTower.algebraMap_apply A Af G.middle f).symm
        calc
          algebraMap F.middle G.middle (fF ^ n) =
              (algebraMap F.middle G.middle fF) ^ n := map_pow _ _ _
          _ = (algebraMap A G.middle f) ^ n := by rw [hF]
          _ = (algebraMap Af G.middle fAf) ^ n := by rw [hAf]
          _ = algebraMap Af G.middle (fAf ^ n) := (map_pow _ _ _).symm
      have hczF : z * algebraMap F.middle G.middle (fF ^ n) =
          algebraMap F.middle G.middle c := by simpa [fF] using hcz
      have hcz' : algebraMap Af G.middle (fAf ^ n) * z =
          algebraMap F.middle G.middle c := by
        calc
          algebraMap Af G.middle (fAf ^ n) * z =
              z * algebraMap F.middle G.middle (fF ^ n) := by rw [hden, mul_comm]
          _ = algebraMap F.middle G.middle c := hczF
      have hψmul : fAf ^ n * ψ z = algebraMap A Af (φ c) := by
        calc
          fAf ^ n * ψ z = ψ (algebraMap Af G.middle (fAf ^ n) * z) := by
            simpa [Algebra.smul_def] using (map_smul ψ (fAf ^ n) z).symm
          _ = ψ (algebraMap F.middle G.middle c) := congrArg ψ hcz'
          _ = algebraMap A Af (φ c) := hψ c
      have hθmul : fAf ^ n * (φC.comp q.toLinearMap) z =
          algebraMap A Af (φ c) := by
        calc
          fAf ^ n * (φC.comp q.toLinearMap) z =
              φC (algebraMap Af Fbc.middle (fAf ^ n) * q z) := by
            simpa [Algebra.smul_def] using (map_smul φC (fAf ^ n) (q z)).symm
          _ = φC (q (algebraMap Af G.middle (fAf ^ n) * z)) := by
            congr 1
            simp [map_mul]
          _ = φC (q (algebraMap F.middle G.middle c)) := by
            rw [hcz']
          _ = φC (algebraMap F.middle Fbc.middle c) := by
            have hr' : algebraMap F.middle G.middle c = r c := rfl
            rw [hr', hqr]
          _ = algebraMap A Af (φ c) := by
            show (Module.Dual.baseChange Af φ)
              ((1 : Af) ⊗ₜ[A] c) = algebraMap A Af (φ c)
            rw [Module.Dual.baseChange_apply_tmul]
            simp [Algebra.smul_def]
      have hmul := hψmul.trans hθmul.symm
      exact (IsUnit.mul_right_inj (hfAf.pow n)).mp hmul.symm
    have hCompat (c : G.middle) :
        algebraMap Fret.middle B (q c) = G.algebraTarget.algebraMap c := by
      show eAf (algebraMap Fbc.middle E (q c)) = algebraMap G.middle B c
      have h := congrArg eAf (DFunLike.congr_fun hTarget c)
      change eB (algebraMap Fbc.middle E (q c)) =
        eB (algebraMap B E (algebraMap G.middle B c)) at h
      rw [eB.commutes] at h
      exact h
    have hCompare := comparison_restrict_of_equiv
      G Fret eAfMiddle.symm hCompat φC b
    refine (dualizingModule_equiv_of_isLocalization_away_tmul_aux f F G φ b).trans ?_
    exact hCompare.trans (congrArg (fun θ => dualizingModule.tmul G θ b) hFunc)

/-- The base-localization identification, computed on a pure tensor through the explicit
factorizations used to construct it. -/
theorem dualizingModule_equiv_of_isLocalization_away_formula
    {A : Type u} {B : Type v} {Af : Type w}
    [CommRing A] [CommRing B] [CommRing Af]
    [Algebra A B] [Algebra A Af] [Algebra Af B] [IsScalarTower A Af B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra.QuasiFinite A B]
    (f : A) [IsLocalization.Away f Af]
    (F : FiniteOpenFactorization.{u, v, x} A B)
    (G : FiniteOpenFactorization.{w, v, y} Af B)
    (φ : Module.Dual A F.middle) (b : B) :
    let Fbc := FiniteOpenFactorization.baseChange F Af
    let E := Af ⊗[A] B
    letI : Algebra B E := Algebra.TensorProduct.rightAlgebra
    letI : IsScalarTower Af B E := IsScalarTower.of_algebraMap_eq' (by
      apply IsLocalization.ringHom_ext (Submonoid.powers f)
      ext a
      change (algebraMap A Af a) ⊗ₜ[A] (1 : B) =
        (1 : Af) ⊗ₜ[A] algebraMap Af B (algebraMap A Af a)
      rw [← IsScalarTower.algebraMap_apply A Af B a]
      exact Algebra.TensorProduct.tmul_one_eq_one_tmul a)
    letI : IsNoetherianRing Af :=
      IsLocalization.isNoetherianRing (Submonoid.powers f) Af inferInstance
    letI : Module.Flat A Af := IsLocalization.flat Af (Submonoid.powers f)
    let eB := baseChangeTargetEquiv (A := A) (B := B) (Af := Af) f
    let eAf := eB.restrictScalars Af
    let Fret := retargetFactorization Fbc eAf
    letI : Module B (dualizingModule Fret) := dualizingModule.instModule Fret
    let φC : Module.Dual Af Fbc.middle := Module.Dual.baseChange Af φ
    dualizingModule_equiv_of_isLocalization_away f F G (dualizingModule.tmul F φ b) =
      dualizingModuleEquiv Fret G
        (dualizingModule.tmul Fret φC b) :=
  dualizingModule_equiv_of_isLocalization_away_tmul_aux f F G φ b

/-- Base change along `A → Af` is compatible with a refinement of finite-open factorizations:
mapping a scalar-extended intermediate algebra into `Af ⊗[A] B` through the refinement agrees
with mapping it in directly. -/
private theorem baseChange_map_comp_algebraMap
    {A : Type*} {B : Type*} {Af : Type*} {C : Type*} {D : Type*}
    [CommRing A] [CommRing B] [CommRing Af] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A Af] [Algebra A C] [Algebra A D]
    [Algebra C B] [Algebra D B] [IsScalarTower A C B] [IsScalarTower A D B]
    (r : C →ₐ[A] D)
    (hr : ∀ c : C, algebraMap D B (r c) = algebraMap C B c) :
    (Algebra.TensorProduct.map (AlgHom.id A Af)
          (IsScalarTower.toAlgHom A D B)).toRingHom.comp
        (Algebra.TensorProduct.map (AlgHom.id A Af) r).toRingHom =
      (Algebra.TensorProduct.map (AlgHom.id A Af)
        (IsScalarTower.toAlgHom A C B)).toRingHom := by
  apply RingHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul a c =>
    show (Algebra.TensorProduct.map (AlgHom.id A Af)
        (IsScalarTower.toAlgHom A D B))
        ((Algebra.TensorProduct.map (AlgHom.id A Af) r) (a ⊗ₜ[A] c)) =
      (Algebra.TensorProduct.map (AlgHom.id A Af)
        (IsScalarTower.toAlgHom A C B)) (a ⊗ₜ[A] c)
    simp only [Algebra.TensorProduct.map_tmul]
    exact congrArg (fun z : B => a ⊗ₜ[A] z) (hr c)

/-- Base change along `A → Af` is compatible with restriction of a functional along a
refinement: restricting the scalar extension of a functional along the scalar extension of the
refinement is the scalar extension of the restricted functional. -/
private theorem dual_baseChange_comp_map
    {A : Type*} {Af : Type*} {C : Type*} {D : Type*}
    [CommRing A] [CommRing Af] [CommRing C] [CommRing D]
    [Algebra A Af] [Algebra A C] [Algebra A D]
    (r : C →ₐ[A] D) (g : Af ⊗[A] C →ₗ[Af] Af ⊗[A] D)
    (hg : ∀ (a : Af) (c : C), g (a ⊗ₜ[A] c) = a ⊗ₜ[A] r c)
    (φ : Module.Dual A D) :
    (Module.Dual.baseChange Af φ).comp g =
      Module.Dual.baseChange Af (φ.comp r.toLinearMap) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' => simp only [LinearMap.map_add, hz, hz']
  | tmul a c =>
    show (Module.Dual.baseChange Af φ) (g (a ⊗ₜ[A] c)) =
      (Module.Dual.baseChange Af (φ.comp r.toLinearMap)) (a ⊗ₜ[A] c)
    rw [hg]
    show φ (r c) • a = φ (r c) • a
    rfl

/-- The comparison from a factorization `H` with injective middle algebra to a refinement `F`
sends a pure tensor to the pure tensor of the restricted functional. -/
private theorem dualizingModuleEquiv_tmul_comp
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    (H : FiniteOpenFactorization.{u, v, w} A B) (F : FiniteOpenFactorization.{u, v, x} A B)
    (hH : Function.Injective (algebraMap H.middle B)) (r : F.middle →ₐ[A] H.middle)
    (hr : ∀ c : F.middle, algebraMap H.middle B (r c) = algebraMap F.middle B c)
    (φ : Module.Dual A H.middle) (b : B) :
    dualizingModuleEquiv H F (dualizingModule.tmul H φ b) =
      dualizingModule.tmul F (φ.comp r.toLinearMap) b := by
  simpa only [AlgHom.toLinearMap_id, LinearMap.comp_id] using
    dualizingModuleEquiv_tmul H F H hH (AlgHom.id A H.middle) r (fun _ => rfl) hr φ b

/-- Comparing the restriction of a pure tensor along a refinement agrees with comparing the
original pure tensor. -/
private theorem dualizingModuleEquiv_comp_tmul_comp
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    (H : FiniteOpenFactorization.{u, v, w} A B) (F : FiniteOpenFactorization.{u, v, x} A B)
    (G : FiniteOpenFactorization.{u, v, y} A B)
    (hH : Function.Injective (algebraMap H.middle B)) (r : F.middle →ₐ[A] H.middle)
    (hr : ∀ c : F.middle, algebraMap H.middle B (r c) = algebraMap F.middle B c)
    (φ : Module.Dual A H.middle) (b : B) :
    dualizingModuleEquiv F G (dualizingModule.tmul F (φ.comp r.toLinearMap) b) =
      dualizingModuleEquiv H G (dualizingModule.tmul H φ b) := by
  rw [← dualizingModuleEquiv_tmul_comp H F hH r hr, ← LinearEquiv.trans_apply,
    dualizingModuleEquiv_trans]

/-- Changing either finite-open factorization does not change the base-localization map. -/
@[stacks 0BT2 "part (1), naturality"]
public theorem dualizingModule_equiv_of_isLocalization_away_natural
    {A : Type u} {B : Type v} {Af : Type w}
    [CommRing A] [CommRing B] [CommRing Af]
    [Algebra A B] [Algebra A Af] [Algebra Af B] [IsScalarTower A Af B]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing Af]
    [Algebra.QuasiFinite A B]
    (f : A) [IsLocalization.Away f Af]
    (F : FiniteOpenFactorization.{u, v, x} A B)
    (F' : FiniteOpenFactorization.{u, v, z} A B)
    (G : FiniteOpenFactorization.{w, v, y} Af B)
    (G' : FiniteOpenFactorization.{w, v, t} Af B) (m : dualizingModule F) :
    dualizingModuleEquiv G G'
        (dualizingModule_equiv_of_isLocalization_away f F G m) =
      dualizingModule_equiv_of_isLocalization_away f F' G'
        (dualizingModuleEquiv F F' m) :=
  by
    classical
    obtain ⟨H, rF, rF', hH, hF, hF'⟩ :=
      exists_common_finite_open_factorization F F'
    let : CommRing H.middle := H.commRingMiddle
    let : Algebra A H.middle := H.algebraMiddle
    let : Algebra H.middle B := H.algebraTarget
    let : IsScalarTower A H.middle B := H.scalarTower
    let : Module.Finite A H.middle := H.finite_middle
    let eHF := dualizingModuleEquiv H F
    let eHF' := dualizingModuleEquiv H F'
    let E := Af ⊗[A] B
    let : Algebra B E := Algebra.TensorProduct.rightAlgebra
    let : IsScalarTower Af B E := isScalarTower_tensor_right f
    let eB := baseChangeTargetEquiv (A := A) (B := B) (Af := Af) f
    let eAf := eB.restrictScalars Af
    let Fbc := FiniteOpenFactorization.baseChange F Af
    let F'bc := FiniteOpenFactorization.baseChange F' Af
    let Hbc := FiniteOpenFactorization.baseChange H Af
    let Fret := retargetFactorization Fbc eAf
    let F'ret := retargetFactorization F'bc eAf
    let Hret := retargetFactorization Hbc eAf
    let : Algebra Fbc.middle B := Fret.algebraTarget
    let : Algebra F'bc.middle B := F'ret.algebraTarget
    let : Algebra Hbc.middle B := Hret.algebraTarget
    let fF : F.middle →ₐ[A] H.middle := rF
    let fF' : F'.middle →ₐ[A] H.middle := rF'
    let rFbc : Fbc.middle →ₐ[Af] Hbc.middle := {
      toRingHom := (Algebra.TensorProduct.map (AlgHom.id A Af) fF).toRingHom
      commutes' := by
        intro a
        show (Algebra.TensorProduct.map (AlgHom.id A Af) fF)
          (a ⊗ₜ[A] (1 : F.middle)) = a ⊗ₜ[A] (1 : H.middle)
        simp [Algebra.TensorProduct.map_tmul] }
    let rF'bc : F'bc.middle →ₐ[Af] Hbc.middle := {
      toRingHom := (Algebra.TensorProduct.map (AlgHom.id A Af) fF').toRingHom
      commutes' := by
        intro a
        show (Algebra.TensorProduct.map (AlgHom.id A Af) fF')
          (a ⊗ₜ[A] (1 : F'.middle)) = a ⊗ₜ[A] (1 : H.middle)
        simp [Algebra.TensorProduct.map_tmul] }
    have hTargetF :
        (algebraMap Hbc.middle E).comp rFbc.toRingHom =
          algebraMap Fbc.middle E :=
      baseChange_map_comp_algebraMap (Af := Af) rF hF
    have hTargetF' :
        (algebraMap Hbc.middle E).comp rF'bc.toRingHom =
          algebraMap F'bc.middle E :=
      baseChange_map_comp_algebraMap (Af := Af) rF' hF'
    have hCompatF (c : Fret.middle) :
        algebraMap Hret.middle B (rFbc c) = algebraMap Fret.middle B c := by
      show eAf (algebraMap Hbc.middle E (rFbc c)) =
        eAf (algebraMap Fbc.middle E c)
      exact congrArg eAf (DFunLike.congr_fun hTargetF c)
    have hCompatF' (c : F'ret.middle) :
        algebraMap Hret.middle B (rF'bc c) = algebraMap F'ret.middle B c := by
      show eAf (algebraMap Hbc.middle E (rF'bc c)) =
        eAf (algebraMap F'bc.middle E c)
      exact congrArg eAf (DFunLike.congr_fun hTargetF' c)
    have hDualF (φ : Module.Dual A H.middle) :
        (Module.Dual.baseChange Af φ).comp rFbc.toLinearMap =
          Module.Dual.baseChange Af (φ.comp rF.toLinearMap) :=
      dual_baseChange_comp_map (Af := Af) rF rFbc.toLinearMap (fun _ _ => rfl) φ
    have hDualF' (φ : Module.Dual A H.middle) :
        (Module.Dual.baseChange Af φ).comp rF'bc.toLinearMap =
          Module.Dual.baseChange Af (φ.comp rF'.toLinearMap) :=
      dual_baseChange_comp_map (Af := Af) rF' rF'bc.toLinearMap (fun _ _ => rfl) φ
    have hinjHret : Function.Injective (algebraMap Hret.middle B) := by
      let fH := algebraMap A H.middle f
      let fB := algebraMap H.middle B fH
      have hfB : fB = algebraMap A B f := by
        show algebraMap H.middle B (algebraMap A H.middle f) = algebraMap A B f
        exact (IsScalarTower.algebraMap_apply A H.middle B f).symm
      have hfBunit : IsUnit fB := by
        rw [hfB]
        have h := IsLocalization.Away.algebraMap_isUnit (R := A) (S := Af) f
        rw [IsScalarTower.algebraMap_apply A Af B f]
        exact h.map (algebraMap Af B)
      let : IsLocalization.Away fB B :=
        IsLocalization.away_of_isUnit_of_bijective (S := B) (r := fB) hfBunit
          Function.bijective_id
      let eSwapRing : Hbc.middle ≃+* H.middle ⊗[A] Af :=
        (Algebra.TensorProduct.comm A Af H.middle).toRingEquiv
      let : Algebra A Hbc.middle := Algebra.compHom Hbc.middle (algebraMap A Af)
      let : Algebra H.middle Hbc.middle := Algebra.TensorProduct.rightAlgebra
      let : IsScalarTower A H.middle Hbc.middle :=
        IsScalarTower.of_algebraMap_eq' (by
          ext a
          show (algebraMap A Af a) ⊗ₜ[A] (1 : H.middle) =
            (1 : Af) ⊗ₜ[A] algebraMap A H.middle a
          exact Algebra.TensorProduct.tmul_one_eq_one_tmul a)
      let eSwap : Hbc.middle ≃ₐ[H.middle] H.middle ⊗[A] Af :=
        AlgEquiv.ofRingEquiv (f := eSwapRing) (by
          intro c
          show Algebra.TensorProduct.comm A Af H.middle
            (algebraMap H.middle Hbc.middle c) = c ⊗ₜ[A] 1
          rw [show algebraMap H.middle Hbc.middle c = (1 : Af) ⊗ₜ[A] c by rfl]
          simp)
      let eLoc : H.middle ⊗[A] Af ≃ₐ[H.middle] Localization.Away fH :=
        IsLocalization.Away.tensorEquiv (R := A) (S := H.middle) f Af
      let eMiddle := eSwap.trans eLoc
      let : IsLocalization.Away fH Hbc.middle :=
        IsLocalization.isLocalization_of_algEquiv (Submonoid.powers fH)
          eMiddle.symm
      let away : Localization.Away fH →+* Localization.Away fB :=
        Localization.awayMap (algebraMap H.middle B) fH
      have hAway : Function.Injective away := by
        apply Localization.awayMap_injective_iff.mpr
        intro a ha
        have ha0 : a = 0 := hH (by simpa using RingHom.mem_ker.mp ha)
        exact ⟨0, by simp [ha0]⟩
      let eAway : Localization.Away fB ≃ₐ[B] B :=
        IsLocalization.algEquiv (Submonoid.powers fB) (Localization.Away fB) B
      have hMap : algebraMap Hbc.middle B =
          eAway.toRingHom.comp (away.comp eMiddle.toRingEquiv.toRingHom) := by
        apply IsLocalization.ringHom_ext (Submonoid.powers fH)
        ext c
        have hL : algebraMap Hbc.middle B
            (algebraMap H.middle Hbc.middle c) = algebraMap H.middle B c := by
          show eAf (algebraMap Hbc.middle E
            (algebraMap H.middle Hbc.middle c)) = _
          show eAf ((Algebra.TensorProduct.map (AlgHom.id A Af)
            (IsScalarTower.toAlgHom A H.middle B))
              ((1 : Af) ⊗ₜ[A] c)) = _
          rw [Algebra.TensorProduct.map_tmul]
          show eB (algebraMap B E (algebraMap H.middle B c)) = _
          exact eB.commutes (algebraMap H.middle B c)
        have hR : eAway (away (eMiddle (algebraMap H.middle Hbc.middle c))) =
            algebraMap H.middle B c := by
          rw [eMiddle.commutes]
          show eAway (away (algebraMap H.middle (Localization.Away fH) c)) = _
          show eAway ((Localization.awayMap (algebraMap H.middle B) fH)
            (algebraMap H.middle (Localization.Away fH) c)) = _
          rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
          exact eAway.commutes (algebraMap H.middle B c)
        exact hL.trans hR.symm
      show Function.Injective (algebraMap Hbc.middle B)
      rw [hMap]
      exact eAway.injective.comp (hAway.comp eMiddle.injective)
    let lhs : dualizingModule F →ₗ[B] dualizingModule G' :=
      (dualizingModuleEquiv G G').toLinearMap.comp
        (dualizingModule_equiv_of_isLocalization_away f F G).toLinearMap
    let rhs : dualizingModule F →ₗ[B] dualizingModule G' :=
      (dualizingModule_equiv_of_isLocalization_away f F' G').toLinearMap.comp
        ((dualizingModuleEquiv F F').toLinearMap)
    have hmaps : ∀ w : dualizingModule H, lhs (eHF w) = rhs (eHF w) := by
      intro w
      induction w using dualizingModule.induction_on with
      | zero => simp [lhs, rhs]
      | add y z hy hz =>
        rw [map_add eHF, map_add, map_add, hy, hz]
      | tmul φ b =>
        rw [dualizingModuleEquiv_tmul_comp H F hH rF hF φ b]
        show dualizingModuleEquiv G G'
            (dualizingModule_equiv_of_isLocalization_away f F G
              (dualizingModule.tmul F (φ.comp rF.toLinearMap) b)) =
          dualizingModule_equiv_of_isLocalization_away f F' G'
            (dualizingModuleEquiv F F'
              (dualizingModule.tmul F (φ.comp rF.toLinearMap) b))
        rw [dualizingModuleEquiv_comp_tmul_comp H F F' hH rF hF φ b,
          dualizingModuleEquiv_tmul_comp H F' hH rF' hF' φ b,
          dualizingModule_equiv_of_isLocalization_away_formula f F G (φ.comp rF.toLinearMap) b,
          dualizingModule_equiv_of_isLocalization_away_formula f F' G' (φ.comp rF'.toLinearMap) b,
          ← LinearEquiv.trans_apply, dualizingModuleEquiv_trans, ← hDualF φ, ← hDualF' φ]
        exact (dualizingModuleEquiv_comp_tmul_comp Hret Fret G' hinjHret rFbc hCompatF
          (Module.Dual.baseChange Af φ) b).trans
          (dualizingModuleEquiv_comp_tmul_comp Hret F'ret G' hinjHret rF'bc hCompatF'
            (Module.Dual.baseChange Af φ) b).symm
    have hfinal := hmaps (eHF.symm m)
    rw [eHF.apply_symm_apply] at hfinal
    exact hfinal

end Stacks.Discriminant
