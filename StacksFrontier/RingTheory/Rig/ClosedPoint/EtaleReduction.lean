module

public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.LocalProperties.Reduced
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.Finiteness
public import StacksFrontier.RingTheory.Rig.AdicBasic
public import StacksFrontier.RingTheory.Rig.ClosedPoint
public import StacksFrontier.RingTheory.Smooth.Reduced
public import StacksFrontier.Topology.Algebra.AdicTopology.AdmissibleRings
import StacksFrontier.Topology.Algebra.AdicTopology.QuotientAdic

/-!
# Étale reductions at rig-closed points

Let `φ : A → B` be an adic morphism of Noetherian weakly admissible topological rings which is
topologically of finite type and flat, and whose reduction `A/I → B/IB` modulo an ideal of
definition `I ⊆ A` is étale.  Let `q ⊆ B` be a rig-closed prime whose contraction
`p = φ⁻¹(q)` is rig-closed as well.  Then `p B_q = q B_q`: the extended prime already generates
the maximal ideal of the local ring of `B` at `q`.

The proof passes to the quotients `R = A/p` and `C = B/pB`.  Both are complete one-dimensional
local Noetherian domains by the rig-point criterion, and `C` is a finite `R`-module: its
reduction modulo the ideal of definition of `R` is a quotient of the étale base change
`(A/I ⊗ R) → (B/IB ⊗ R)` over an Artinian ring, hence finite, and finiteness lifts over a
separated complete filtration.  Being finite, flat and formally unramified over `R`, the algebra
`C` is étale, hence reduced; so `q` becomes a minimal prime of `C` over the zero ideal of `R`,
and its image in the localization of `C` at `q` is zero.  Reading that back in `B` is exactly
the asserted equality of ideals.

## Main results

* `Rig.map_comap_eq_map_of_rigPoint_of_etale_quotient`: **Stacks 0GGI**.

## Implementation notes

The source's equality `p B_q = q B_q` is stated as an equality of ideals of
`Localization.AtPrime q`, the left-hand side being the extension of `p` along the composite
`A → B → B_q`.  Rig-closedness of a prime is the complete one-dimensional local condition of the
rig-point criterion of Tag 0GG8, and the étale reduction is the induced quotient map
`A ⧸ I → B ⧸ IB`.

Vanishing of the differentials of `C` over `R` is obtained from formal unramifiedness of
`C ⊗_R R/Ī` over `R/Ī` by Nakayama: the module of differentials is finite over `R` and
`Ī Ω = Ω`, with `Ī` inside the Jacobson radical.

## References

* [Stacks Project, Tag 0GGI](https://stacks.math.columbia.edu/tag/0GGI)
* [Stacks Project, Tag 0GG8](https://stacks.math.columbia.edu/tag/0GG8)
-/

@[expose] public section

namespace Rig

open Filter
open scoped Topology TensorProduct

/-- An étale algebra over an Artinian ring is a finite module: each of its fibres is a finite
product of finite field extensions, so the algebra is quasi-finite. -/
private lemma finite_of_etale_over_isArtinianRing
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsArtinianRing R] [Algebra.Etale R S] :
    Module.Finite R S := by
  classical
  let : Algebra.QuasiFinite R S := by
    refine ⟨fun p hp ↦ ?_⟩
    let : p.IsPrime := hp
    let : Algebra.Etale p.ResidueField (p.Fiber S) := inferInstance
    rcases (Algebra.Etale.iff_exists_algEquiv_prod
      (K := p.ResidueField) (A := p.Fiber S)).mp inferInstance with
      ⟨ι, hι, F, hF, hAlg, e, hfin⟩
    let : Finite ι := hι
    have (i : ι) : Module.Finite p.ResidueField (F i) := (hfin i).1
    let eL : p.Fiber S ≃ₗ[p.ResidueField] (∀ i, F i) := e.toLinearEquiv
    exact Module.Finite.of_surjective eL.symm.toLinearMap eL.symm.surjective
  exact Module.Finite.of_quasiFinite

/-- The image of an ideal inside the Jacobson radical under a surjection is again inside the
Jacobson radical. -/
private lemma map_le_jacobson_of_surjective
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (J : Ideal R)
    (hJ : J ≤ (⊥ : Ideal R).jacobson) :
    J.map f ≤ (⊥ : Ideal S).jacobson := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  apply Ideal.mem_jacobson_bot.mpr
  intro y
  obtain ⟨y, rfl⟩ := hf y
  simpa using f.isUnit_map (Ideal.mem_jacobson_bot.mp (hJ hx) y)

/-- **Stacks 0GGI.** Let `φ : A → B` be an adic morphism of Noetherian weakly admissible
topological rings which is topologically of finite type and flat and whose reduction modulo an
ideal of definition `I ⊆ A` is étale.  If `q ⊆ B` is a rig-closed prime whose contraction to `A`
is rig-closed as well, then the extension of that contraction to the local ring of `B` at `q` is
the extension of `q` itself. -/
@[stacks 0GGI]
public lemma map_comap_eq_map_of_rigPoint_of_etale_quotient
    {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (_hA : TopologicalRing.IsWeaklyAdmissible A)
    (hB : TopologicalRing.IsWeaklyAdmissible B)
    (φ : A →+* B) (hφ : Continuous φ)
    (hadic : RingHom.IsAdic φ)
    (_hft : TopologicalRing.IsTopologicallyOfFiniteType φ)
    (hflat : φ.Flat)
    (I : Ideal A) (hI : TopologicalRing.IsIdealOfDefinition I)
    (hetale : (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map).Etale)
    (q : Ideal B) [q.IsPrime]
    (_hq : Ideal.IsRigPointLocalCondition q)
    (hp : Ideal.IsRigPointLocalCondition (q.comap φ)) :
    (q.comap φ).map ((algebraMap B (Localization.AtPrime q)).comp φ) =
      q.map (algebraMap B (Localization.AtPrime q)) := by
  rcases hadic with ⟨I₀, hI₀, hJ₀⟩
  let p : Ideal A := q.comap φ
  let P : Ideal B := p.map φ
  let R := A ⧸ p
  let C := B ⧸ P
  let Ibar : Ideal R := I.map (Ideal.Quotient.mk p)
  let : IsLocalRing R := hp.choose
  let : IsNoetherianRing R := hp.choose_spec.2.1
  let : IsDomain R := hp.choose_spec.2.2.1
  have hIadic : IsAdic I := (isIdealOfDefinition_iff_isAdic ⟨I₀, hI₀⟩ I).mp hI
  have hIbarAdic : IsAdic Ibar := isAdic_map_quotient_mk I p hIadic
  let : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
  let : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup (G := R)
  have hRcomplete : IsAdicComplete Ibar R :=
    hIbarAdic.isAdicComplete_iff.mpr ⟨hp.choose_spec.2.2.2.1, hp.choose_spec.2.2.2.2.1⟩
  have hRprecomplete : IsPrecomplete Ibar R := hRcomplete.toIsPrecomplete
  have hradIbar : Ibar.radical = IsLocalRing.maximalIdeal R :=
    hp.choose_spec.2.2.2.2.2 I hI
  have hIbarle : Ibar ≤ IsLocalRing.maximalIdeal R := Ideal.le_radical.trans_eq hradIbar
  have hIbarArtinian : IsArtinianRing (R ⧸ Ibar) := by
    let : IsNoetherianRing (R ⧸ Ibar) := inferInstance
    have hIbarne : Ibar ≠ ⊤ := fun h ↦
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.mp (h ▸ hIbarle))
    let : Nontrivial (R ⧸ Ibar) := Ideal.Quotient.nontrivial_iff.mpr hIbarne
    let : IsLocalRing (R ⧸ Ibar) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk Ibar) Ideal.Quotient.mk_surjective
    have hmaxpow : ∃ n, (IsLocalRing.maximalIdeal R) ^ n ≤ Ibar :=
      Ideal.exists_pow_le_of_le_radical_of_fg (by rw [hradIbar])
        (IsNoetherian.noetherian (IsLocalRing.maximalIdeal R))
    apply (isArtinianRing_iff_isNilpotent_maximalIdeal (R ⧸ Ibar)).2
    obtain ⟨n, hn⟩ := hmaxpow
    have hnil : (IsLocalRing.maximalIdeal (R ⧸ Ibar)) ^ n = ⊥ := by
      rw [← IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective,
        ← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
      exact hn
    exact ⟨n, by simpa using hnil⟩
  let : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B
  let : IsUniformAddGroup B := isUniformAddGroup_of_addCommGroup (G := B)
  have hBcomplete : IsAdicComplete (I₀.map φ) B :=
    hJ₀.isAdicComplete_iff.mpr ⟨hB.2.1, hB.2.2⟩
  have hIimageJac : I.map φ ≤ (⊥ : Ideal B).jacobson := by
    refine Ideal.map_le_iff_le_comap.mpr fun a ha ↦ ?_
    have htn : IsTopologicallyNilpotent (φ a) :=
      (isTopologicallyNilpotent_of_mem_isIdealOfDefinition hI ha).map hφ
    have hJopen : IsOpen ((I₀.map φ : Ideal B) : Set B) := by
      simpa using (isAdic_iff.mp hJ₀).1 1
    obtain ⟨n, hn⟩ := htn.exists_pow_mem_of_mem_nhds (hJopen.mem_nhds (Ideal.zero_mem _))
    exact ((Ideal.radical_mono (IsAdicComplete.le_jacobson_bot (I₀.map φ))).trans
      (Ideal.isRadical_jacobson (⊥ : Ideal B))) (Ideal.mem_radical_iff.mpr ⟨n, hn⟩)
  let fbar : R →+* C := Ideal.quotientMap P φ Ideal.le_comap_map
  let : Algebra R C := fbar.toAlgebra
  have hfbar : fbar.comp (Ideal.Quotient.mk p) = (Ideal.Quotient.mk P).comp φ :=
    Ideal.quotientMap_comp_mk Ideal.le_comap_map
  have hJmap : (I.map φ).map (Ideal.Quotient.mk P) = Ibar.map fbar := by
    rw [Ideal.map_map, Ideal.map_map, ← hfbar]
  have hIbarJac : Ibar.map fbar ≤ (⊥ : Ideal C).jacobson := by
    rw [← hJmap]
    exact map_le_jacobson_of_surjective (Ideal.Quotient.mk P)
      Ideal.Quotient.mk_surjective (I.map φ) hIimageJac
  have hCsep : ⨅ n : ℕ, Ibar ^ n • (⊤ : Submodule R C) = ⊥ := by
    let : IsNoetherianRing C := inferInstance
    have hHausC : IsHausdorff (Ibar.map fbar) C := IsHausdorff.of_le_jacobson _ _ hIbarJac
    have hHausR : IsHausdorff Ibar C := by
      rw [← IsHausdorff.map_algebraMap_iff (R := R) (S := C) (M := C) (I := Ibar)]
      simpa only [RingHom.algebraMap_toAlgebra] using hHausC
    exact hHausR.iInf_pow_smul
  let E := A ⧸ I
  let D := B ⧸ (I.map φ)
  let T := R ⧸ Ibar
  let eToT : E →+* T := Ideal.quotientMap Ibar (Ideal.Quotient.mk p) Ideal.le_comap_map
  let fAD : E →+* D := Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map
  let : Algebra E T := eToT.toAlgebra
  let : Algebra E D := fAD.toAlgebra
  let : Algebra.Etale E D := hetale
  let : Algebra.Etale T (TensorProduct E T D) := Algebra.Etale.baseChange E D T
  have hfiniteTensor : Module.Finite T (TensorProduct E T D) :=
    finite_of_etale_over_isArtinianRing (R := T) (S := TensorProduct E T D)
  let K : Ideal C := Ibar.map fbar
  let Q := C ⧸ K
  let gR : R →+* Q := (Ideal.Quotient.mk K).comp fbar
  have hkillIbar : Ibar ≤ RingHom.ker gR := by
    intro x hx
    change Ideal.Quotient.mk K (fbar x) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem fbar hx)
  let tmap : T →+* Q := Ideal.Quotient.lift Ibar gR hkillIbar
  let gB : B →+* Q := (Ideal.Quotient.mk K).comp (Ideal.Quotient.mk P)
  have hkillJ : I.map φ ≤ RingHom.ker gB := fun a ha ↦
    Ideal.Quotient.eq_zero_iff_mem.mpr (hJmap.le (Ideal.mem_map_of_mem _ ha))
  let dmap : D →+* Q := Ideal.Quotient.lift (I.map φ) gB hkillJ
  have hcompTD : tmap.comp eToT = dmap.comp fAD := by
    refine RingHom.ext fun x ↦ ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change (Ideal.Quotient.mk K) (fbar (Ideal.Quotient.mk p a)) =
      (Ideal.Quotient.mk K) (Ideal.Quotient.mk P (φ a))
    exact congrArg (Ideal.Quotient.mk K) (congrArg (fun f : A →+* C ↦ f a) hfbar)
  let : Algebra T Q := tmap.toAlgebra
  let : Algebra E Q := (tmap.comp eToT).toAlgebra
  have hTowerETQ : IsScalarTower E T Q := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let fAlg : T →ₐ[T] Q := { toRingHom := tmap, commutes' := fun _ ↦ rfl }
  let dAlg : D →ₐ[E] Q :=
    { toRingHom := dmap
      commutes' := by
        intro x
        change dmap (fAD x) = (tmap.comp eToT) x
        exact (congrArg (fun f : E →+* Q ↦ f x) hcompTD).symm }
  let hcomm : ∀ x y, Commute (fAlg x) (dAlg y) := fun _ _ ↦ Commute.all _ _
  let tensMap := Algebra.TensorProduct.lift fAlg dAlg hcomm
  have htensSurj : Function.Surjective tensMap := by
    intro x
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
    refine ⟨1 ⊗ₜ[E] (Ideal.Quotient.mk (I.map φ) b), ?_⟩
    dsimp [tensMap]
    simp only [map_one, one_mul, fAlg, dAlg]
    dsimp [dmap]
    rfl
  have hfiniteQ : Module.Finite T Q :=
    Module.Finite.of_surjective tensMap.toLinearMap htensSurj
  have hcompRT : tmap.comp (Ideal.Quotient.mk Ibar) = gR := Ideal.Quotient.lift_comp_mk _ _ _
  let : IsScalarTower R T Q :=
    IsScalarTower.of_algebraMap_eq' (R := R) (S := T) (A := Q) hcompRT.symm
  have hNK : (Ibar • (⊤ : Submodule R C)) = K.restrictScalars R := by
    simp [K, RingHom.algebraMap_toAlgebra]
  have hfiniteQR : Module.Finite R Q := Module.Finite.trans T Q
  have eFiber : (C ⧸ (Ibar • (⊤ : Submodule R C))) ≃ₗ[R] Q := by
    rw [hNK]
    exact Submodule.Quotient.restrictScalarsEquiv R K
  have hfiniteFiberR : Module.Finite R (C ⧸ (Ibar • (⊤ : Submodule R C))) :=
    hfiniteQR.equiv eFiber.symm
  have hFiberTorsion : Module.IsTorsionBySet R
      (C ⧸ (Ibar • (⊤ : Submodule R C))) (Ibar : Set R) := by
    intro x r
    refine Submodule.Quotient.induction_on _ x fun c ↦ ?_
    change Submodule.Quotient.mk (p := Ibar • (⊤ : Submodule R C)) (r • c) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul r.2 Submodule.mem_top
  let : Module T (C ⧸ (Ibar • (⊤ : Submodule R C))) := hFiberTorsion.module
  have : IsScalarTower R T (C ⧸ (Ibar • (⊤ : Submodule R C))) :=
    hFiberTorsion.isScalarTower
  have hfiniteFiberT : Module.Finite T (C ⧸ (Ibar • (⊤ : Submodule R C))) :=
    Module.Finite.of_restrictScalars_finite R T (C ⧸ (Ibar • (⊤ : Submodule R C)))
  have hfiniteC : Module.Finite R C :=
    Module.Finite.of_iInf_pow_smul_top_eq_bot_of_finite_quotient_smul_top
      Ibar hCsep hfiniteFiberT
  let : Algebra.FiniteType R C := inferInstance
  let : Algebra.EssFiniteType R C := inferInstance
  have : IsScalarTower R C Ω[C⁄R] := inferInstance
  have hfiniteOmegaR : Module.Finite R Ω[C⁄R] := Module.Finite.trans C Ω[C⁄R]
  have hQformallyUnramified : Algebra.FormallyUnramified T Q :=
    Algebra.FormallyUnramified.of_surjective (R := T) (A := TensorProduct E T D) (B := Q)
      tensMap htensSurj
  let eCQ := Algebra.TensorProduct.quotIdealMapEquivTensorQuot C Ibar
  have hpushCT : Algebra.IsPushout R C T Q := by
    refine ⟨IsBaseChange.of_equiv eCQ.symm.toLinearEquiv fun x ↦ ?_⟩
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    change (Algebra.TensorProduct.quotIdealMapEquivTensorQuot C Ibar).symm
      (1 ⊗ₜ[R] (r : R ⧸ Ibar)) = tmap (Ideal.Quotient.mk Ibar r)
    rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul]
    change Ideal.Quotient.mk K (fbar r * 1) =
      Ideal.Quotient.lift Ibar gR hkillIbar (Ideal.Quotient.mk Ibar r)
    rw [mul_one]
    rfl
  let : Algebra.IsPushout R T C Q := hpushCT.symm
  let eOmega := KaehlerDifferential.tensorKaehlerEquivBase R T C Q
  have hOmegaTensorSubsingleton : Subsingleton (T ⊗[R] Ω[C⁄R]) :=
    ⟨fun x y ↦ eOmega.injective (Subsingleton.elim _ _)⟩
  let eOmegaQuot : (T ⊗[R] Ω[C⁄R]) ≃ₗ[R] Ω[C⁄R] ⧸ Ibar • (⊤ : Submodule R Ω[C⁄R]) :=
    (TensorProduct.comm R T Ω[C⁄R]).trans (TensorProduct.tensorQuotEquivQuotSMul Ω[C⁄R] Ibar)
  have hOmegaQuotSubsingleton :
      Subsingleton (Ω[C⁄R] ⧸ Ibar • (⊤ : Submodule R Ω[C⁄R])) :=
    ⟨fun x y ↦ eOmegaQuot.symm.injective (hOmegaTensorSubsingleton.elim _ _)⟩
  have hOmegaSpan : Ibar • (⊤ : Submodule R Ω[C⁄R]) = ⊤ :=
    Submodule.Quotient.subsingleton_iff.mp hOmegaQuotSubsingleton
  have hIbarJacR : Ibar ≤ (⊥ : Ideal R).jacobson :=
    hIbarle.trans (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  have hOmegaBot : (⊤ : Submodule R Ω[C⁄R]) = ⊥ := by
    apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot Ibar ⊤
      (Module.finite_def.mp hfiniteOmegaR) ?_ hIbarJacR
    rw [hOmegaSpan]
  have hOmegaZero (x : Ω[C⁄R]) : x = 0 := (Submodule.mem_bot R).mp (hOmegaBot ▸ Submodule.mem_top)
  have : Algebra.FormallyUnramified R C :=
    ⟨⟨fun x y ↦ (hOmegaZero x).trans (hOmegaZero y).symm⟩⟩
  let : Algebra A B := φ.toAlgebra
  let : Module.Flat A B := hflat
  have hflatfbar : fbar.Flat := by
    let : Algebra R C := Ideal.Quotient.algebraQuotientMapQuotient
    let : Module.Flat R (R ⊗[A] B) := inferInstance
    let : Module.Flat R C := Module.Flat.of_linearEquiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B p).toLinearEquiv
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have hflatC : Module.Flat R C := RingHom.flat_algebraMap_iff.mp hflatfbar
  let : Algebra.FinitePresentation R C :=
    (Algebra.FinitePresentation.of_finiteType (R := R) (A := C)).mp inferInstance
  let : Algebra.Etale R C := Algebra.Etale.of_formallyUnramified_of_flat (R := R) (S := C)
  have hReducedC : IsReduced C := Algebra.isReduced_of_smooth R C
  let qC : Ideal C := q.map (Ideal.Quotient.mk P)
  have hPq : P ≤ q := Ideal.map_comap_le
  have hqCPrime : qC.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hPq
  have hqCcomap : qC.comap (Ideal.Quotient.mk P) = q := Ideal.comap_map_mk hPq
  have hqCunder : qC.under R = ⊥ := by
    change qC.comap (algebraMap R C) = ⊥
    apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk p)
      Ideal.Quotient.mk_surjective
    change qC.comap (fbar.comp (Ideal.Quotient.mk p)) =
      (⊥ : Ideal R).comap (Ideal.Quotient.mk p)
    rw [hfbar, ← Ideal.comap_comap, hqCcomap, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  let : Algebra.IsIntegral R C := inferInstance
  have hqCminimal : qC ∈ (⊥ : Ideal C).minimalPrimes := by
    simpa [hqCunder] using (Ideal.IsIntegral.mem_minimalPrimes_map_under (R := R) qC)
  let L := Localization.AtPrime q
  let Iq : Ideal L := P.map (algebraMap B L)
  let S := L ⧸ Iq
  have hqCmapZero : qC.map (algebraMap C S) = ⊥ := by
    let : IsLocalization (Algebra.algebraMapSubmonoid C q.primeCompl) S := inferInstance
    have hsub : Algebra.algebraMapSubmonoid C q.primeCompl = qC.primeCompl := by
      ext x
      constructor
      · rintro ⟨b, hb, rfl⟩ hmem
        exact hb (hqCcomap ▸ (hmem : b ∈ qC.comap (Ideal.Quotient.mk P)))
      · intro hx
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
        exact ⟨b, fun hbq ↦ hx (Ideal.mem_map_of_mem (Ideal.Quotient.mk P) hbq), rfl⟩
    let : IsLocalization qC.primeCompl S :=
      hsub ▸ (inferInstance : IsLocalization (Algebra.algebraMapSubmonoid C q.primeCompl) S)
    have hReducedS : IsReduced S := isReduced_localizationPreserves qC.primeCompl S hReducedC
    have hrad := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes S qC ⊥ hqCminimal
    rw [Ideal.map_bot, Ideal.radical_bot_of_isReduced] at hrad
    exact hrad.symm
  have hqLeIq : q.map (algebraMap B L) ≤ Iq := by
    rw [← (Ideal.mk_ker (I := Iq))]
    apply (Ideal.map_eq_bot_iff_le_ker (f := Ideal.Quotient.mk Iq)).mp
    have hcomp : (algebraMap C S).comp (Ideal.Quotient.mk P) =
        (Ideal.Quotient.mk Iq).comp (algebraMap B L) := by ext b; rfl
    rw [Ideal.map_map, ← hcomp, ← Ideal.map_map]
    exact hqCmapZero
  have hIqLeq : Iq ≤ q.map (algebraMap B L) := Ideal.map_mono hPq
  change p.map ((algebraMap B L).comp φ) = q.map (algebraMap B L)
  rw [← Ideal.map_map]
  exact le_antisymm hIqLeq hqLeIq

end Rig

end
