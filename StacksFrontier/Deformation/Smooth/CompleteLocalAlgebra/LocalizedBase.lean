module

public import Mathlib.RingTheory.AdicCompletion.Topology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.SchlessingerConditions.SmoothMorphisms
public import StacksFrontier.Deformation.Smooth.PowerSeries
public import StacksFrontier.RingTheory.FormallySmooth.SpecialFibre
public import StacksFrontier.RingTheory.GeometricallyRegular.FormalSmoothness
import StacksFrontier.Deformation.Predeformation.PointsFromBase

/-!
# Smooth complete local algebras: localizing the base and the special fibre

Auxiliary results for Stacks 0DYL. Adic formal smoothness of `Λ → R` is unchanged by
localizing `Λ` at `p = ker(Λ → k)`, and is equivalent to geometric regularity of the special
fibre; the special fibre `R ⊗[Λ] k'` over `k' = Λ / p` is identified with the special fibre of
the localized structure map `Λ_p → R`, which is local, and flatness transfers along it. This
part also defines `Deformation.restrictedCoyonedaProjection`.
-/

@[expose] public section

open CategoryTheory
open IsLocalRing
open scoped TensorProduct

universe u v w

namespace Deformation

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

private alias residueEquiv_structureMap := residueEquiv_algebraMap

private theorem residueKernel_eq_comap_maximal
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    RingHom.ker (algebraMap Λ k) =
      (maximalIdeal R).comap (algebraMap Λ R) := by
  ext a
  show algebraMap Λ k a = 0 ↔ algebraMap Λ R a ∈ maximalIdeal R
  rw [← IsLocalRing.residue_eq_zero_iff]
  constructor
  · intro h
    apply R.residueEquiv.injective
    rw [residueEquiv_structureMap]
    simpa using h
  · intro h
    have hz := congrArg R.residueEquiv h
    rw [residueEquiv_structureMap] at hz
    simpa using hz

private theorem structureMap_isUnit_of_not_mem_residueKernel
    {R : Type v} [CommRing R] [Algebra Λ R] [IsLocalRing R]
    (e : ResidueField R ≃ₐ[Λ] k)
    (a : Λ) (ha : a ∉ RingHom.ker (algebraMap Λ k)) :
    IsUnit (algebraMap Λ R a) := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
  intro hz
  refine ha (RingHom.mem_ker.mpr ?_)
  rw [← residueEquiv_structureMap e a, hz, map_zero]

private theorem formallySmoothNAdic_iff_localizationBase
    {A : Type u} {S : Type v} {T : Type w}
    [CommRing A] [CommRing S] [CommRing T] [Algebra A T]
    (M : Submonoid A) [IsLocalization M T]
    (φ : A →+* S) (n : Ideal S) (g : T →+* S)
    (hcomp : g.comp (algebraMap A T) = φ)
    (hφunits : ∀ s : M, IsUnit (φ s)) :
    RingHom.FormallySmoothNAdic.{max u v w} φ n ↔
      RingHom.FormallySmoothNAdic.{max u v w} g n := by
  constructor
  · intro h E _ J hJ f ψ hcomm hpow
    let f₀ := f.comp (algebraMap A T)
    have hcomm₀ : ψ.comp φ = (Ideal.Quotient.mk J).comp f₀ := by
      rw [← hcomp, ← RingHom.comp_assoc, hcomm, RingHom.comp_assoc]
    obtain ⟨ℓ, hquot, hbase⟩ := h E J hJ f₀ ψ hcomm₀ hpow
    exact ⟨ℓ, hquot, IsLocalization.ringHom_ext M (by rw [RingHom.comp_assoc, hcomp, hbase])⟩
  · intro h E _ J hJ f ψ hcomm hpow
    have hunits : ∀ s : M, IsUnit (f s) := by
      intro s
      have hu : IsUnit (ψ (φ s)) := (hφunits s).map ψ
      have hv : ψ (φ s) = Ideal.Quotient.mk J (f s) := by
        simpa only [RingHom.comp_apply] using RingHom.congr_fun hcomm s
      rw [hv] at hu
      exact (IsNilpotent.isUnit_quotient_mk_iff (I := J) ⟨2, hJ⟩).mp hu
    let f₀ : T →+* E := IsLocalization.lift (M := M) (g := f) hunits
    have hlift : f₀.comp (algebraMap A T) = f :=
      IsLocalization.lift_comp (M := M) (g := f) hunits
    have hcomm₀ : ψ.comp g = (Ideal.Quotient.mk J).comp f₀ := by
      apply IsLocalization.ringHom_ext M
      apply RingHom.ext
      intro a
      have hg : g (algebraMap A T a) = φ a := by
        simpa only [RingHom.comp_apply] using RingHom.congr_fun hcomp a
      have hf : f₀ (algebraMap A T a) = f a := by
        simpa only [RingHom.comp_apply] using RingHom.congr_fun hlift a
      calc
        ψ (g (algebraMap A T a)) = ψ (φ a) := congrArg ψ hg
        _ = Ideal.Quotient.mk J (f a) := RingHom.congr_fun hcomm a
        _ = Ideal.Quotient.mk J (f₀ (algebraMap A T a)) :=
          congrArg (Ideal.Quotient.mk J) hf.symm
    obtain ⟨ℓ, hquot, hbase⟩ := h E J hJ f₀ ψ hcomm₀ hpow
    exact ⟨ℓ, hquot, by rw [← hcomp, ← RingHom.comp_assoc, hbase, hlift]⟩

/-- A ring map killing a positive power of `I` is continuous for the `I`-adic topology and the
discrete topology on the target. -/
private theorem continuous_adicTopology_to_bot {P : Type*} {X : Type*} [CommRing P] [CommRing X]
    (I : Ideal P) (g : P →+* X) (m : ℕ) (hm : 0 < m) (hg : I ^ m ≤ RingHom.ker g) :
    @Continuous P X I.adicTopology ⊥ g := by
  let : TopologicalSpace X := ⊥
  have : DiscreteTopology X := ⟨rfl⟩
  have hdisc : (⊥ : TopologicalSpace X) = (⊥ : Ideal X).adicTopology :=
    (is_bot_adic_iff (A := X)).2 inferInstance
  rw [hdisc]
  exact (RingHom.continuous_adic_iff g I ⊥).2 ⟨m, hm, fun x hx => by simpa using hg hx⟩

private theorem formallySmoothNAdic_of_isFormallySmooth_adic.{u₁}
    {A : Type u} {B : Type v} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] (φ : A →+* B) [IsLocalHom φ]
    (h : @IsFormallySmooth.{u₁, u, v} A B _
      (maximalIdeal A).adicTopology
      (maximalIdeal A).ringFilterBasis.isTopologicalRing
      (maximalIdeal A).isLinearTopology _
      (maximalIdeal B).adicTopology
    (maximalIdeal B).ringFilterBasis.isTopologicalRing
      (maximalIdeal B).isLinearTopology φ) :
    RingHom.FormallySmoothNAdic.{u₁} φ (maximalIdeal B) := by
  let : TopologicalSpace A := (maximalIdeal A).adicTopology
  let : IsTopologicalRing A := (maximalIdeal A).ringFilterBasis.isTopologicalRing
  let : IsLinearTopology A A := (maximalIdeal A).isLinearTopology
  let : TopologicalSpace B := (maximalIdeal B).adicTopology
  let : IsTopologicalRing B := (maximalIdeal B).ringFilterBasis.isTopologicalRing
  let : IsLinearTopology B B := (maximalIdeal B).isLinearTopology
  intro E _ J hJ f ψ hcomm ⟨n, hn, hψ⟩
  let : TopologicalSpace E := ⊥
  let : DiscreteTopology E := ⟨rfl⟩
  let : DiscreteTopology (E ⧸ J) :=
    QuotientAddGroup.discreteTopology (N := J.toAddSubgroup) (isOpen_discrete _)
  have hmapφ : Ideal.map φ (maximalIdeal A) ≤ maximalIdeal B :=
    Ideal.map_le_iff_le_comap.2 fun x hx => map_nonunit φ x hx
  have hmapf : Ideal.map f (maximalIdeal A ^ n) ≤ J := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    have hxφ : φ x ∈ maximalIdeal B ^ n := by
      have hx' : φ x ∈ Ideal.map φ (maximalIdeal A ^ n) :=
        Ideal.mem_map_of_mem φ hx
      rw [Ideal.map_pow] at hx'
      exact (Ideal.pow_right_mono hmapφ n) hx'
    have hz : ψ (φ x) = 0 := hψ hxφ
    have heq := congrArg (fun f : A →+* E ⧸ J => f x) hcomm
    change ψ (φ x) = Ideal.Quotient.mk J (f x) at heq
    rw [hz] at heq
    show f x ∈ J
    exact (Ideal.Quotient.eq_zero_iff_mem).mp heq.symm
  have hmapf2 : Ideal.map f (maximalIdeal A ^ (2 * n)) = ⊥ := by
    refine le_antisymm ?_ bot_le
    calc
      Ideal.map f (maximalIdeal A ^ (2 * n)) =
          Ideal.map f (maximalIdeal A ^ n * maximalIdeal A ^ n) := by
            rw [← pow_add, two_mul]
      _ = Ideal.map f (maximalIdeal A ^ n) *
            Ideal.map f (maximalIdeal A ^ n) := Ideal.map_mul _ _ _
      _ ≤ J * J := Ideal.mul_mono hmapf hmapf
      _ = ⊥ := by rwa [pow_two] at hJ
  have hfcont := continuous_adicTopology_to_bot (maximalIdeal A) f (2 * n) (by omega) fun x hx => by
    simpa [hmapf2] using Ideal.mem_map_of_mem f hx
  have hψcont := continuous_adicTopology_to_bot (maximalIdeal B) ψ n hn hψ
  obtain ⟨g, _, hgφ, hgm⟩ := h.2 E J hJ f hfcont ψ hψcont hcomm
  exact ⟨g, hgm, hgφ⟩

@[ega "0 19.6.5" "more general",
  ega "0 19.6.7",
  ega "0 22.5.8",
  ega "0 22.6.7" "more general",
  ega "IV 7.5.4" "special case"]
private theorem geometricallyRegular_iff_formallySmoothNAdic
    {K : Type u} {C : Type v} [Field K] [CommRing C] [Algebra K C]
    [IsNoetherianRing C] [IsLocalRing C] :
    Algebra.IsGeometricallyRegular K C ↔
      RingHom.FormallySmoothNAdic.{max u v} (algebraMap K C) (maximalIdeal C) := by
  let : TopologicalSpace K := ⊥
  let : DiscreteTopology K := ⟨rfl⟩
  let : TopologicalSpace C := (maximalIdeal C).adicTopology
  let : IsTopologicalRing C := (maximalIdeal C).ringFilterBasis.isTopologicalRing
  let : IsLinearTopology C C := (maximalIdeal C).isLinearTopology
  show Algebra.IsGeometricallyRegular K C ↔
    RingHom.FormallySmoothNAdic.{max u v} (algebraMap K C) (maximalIdeal C)
  obtain hchar | ⟨p, hp, hchar⟩ := CharP.exists' K
  · let : CharZero K := hchar
    rw [← isFormallySmooth_iff_formallySmoothNAdic
      (algebraMap K C) (maximalIdeal C) (by rfl)]
    rw [← (formalSmoothness_maximalIdeal_characterizations K C).1]
    constructor
    · intro h
      have hreg : IsRegularRing (K ⊗[K] C) := h.isRegularRing_tensorProduct K
      have hregC : IsRegularRing C := by
        let e : K ⊗[K] C ≃+* C :=
          (Algebra.TensorProduct.lid K C).toRingEquiv
        exact IsRegularRing.of_ringEquiv e
      let : IsRegularRing C := hregC
      exact IsRegularLocalRing.of_isRegularRing_of_isLocalRing C
    · intro h
      let : IsRegularLocalRing C := h
      have hreg : IsRegularRing C :=
        ((IsLocalRing.isRegularRing_tfae (R := C)).out 1 3).mp h
      exact ⟨fun L _ _ _ => by
        revert L
        refine
          (Algebra.forall_isRegularRing_tensorProduct_essFiniteType_iff_finite_isPurelyInseparable
            K C).mpr ?_
        intro L _ _ _ _
        have hbij : Function.Bijective (algebraMap K L) :=
          ⟨(algebraMap K L).injective,
            IsPurelyInseparable.surjective_algebraMap_of_isSeparable K L⟩
        let e : L ≃ₐ[K] K :=
          (AlgEquiv.ofBijective (Algebra.ofId K L) hbij).symm
        let e' : L ⊗[K] C ≃+* C :=
          ((Algebra.TensorProduct.congr e AlgEquiv.refl).trans
            (Algebra.TensorProduct.lid K C)).toRingEquiv
        exact IsRegularRing.of_ringEquiv e'.symm⟩
  · let : Fact p.Prime := hp
    let : CharP K p := hchar
    rw [← isFormallySmooth_iff_formallySmoothNAdic
      (algebraMap K C) (maximalIdeal C) (by rfl)]
    exact ((formalSmoothness_maximalIdeal_characterizations K C).2 p).out 1 2

private noncomputable def specialFibre_algEquiv_quotient
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (p : Ideal Λ) [p.IsMaximal] :
    letI : Field (Λ ⧸ p) := Ideal.Quotient.field p
    let Bbar := R ⊗[Λ] (Λ ⧸ p)
    letI : Algebra (Λ ⧸ p) Bbar := Algebra.TensorProduct.rightAlgebra
    (R ⧸ Ideal.map (algebraMap Λ R) p) ≃ₐ[Λ ⧸ p] Bbar := by
  letI : Field (Λ ⧸ p) := Ideal.Quotient.field p
  let Bbar := R ⊗[Λ] (Λ ⧸ p)
  letI : Algebra (Λ ⧸ p) Bbar := Algebra.TensorProduct.rightAlgebra
  let e₁ : (R ⧸ Ideal.map (algebraMap Λ R) p) ≃ₐ[Λ ⧸ p]
      (Λ ⧸ p) ⊗[Λ] R :=
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor R p
  let e₂ : ((Λ ⧸ p) ⊗[Λ] R) ≃ₐ[Λ ⧸ p] Bbar :=
    { toRingEquiv := (Algebra.TensorProduct.comm Λ (Λ ⧸ p) R).toRingEquiv
      commutes' := by
        intro a
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
        change (Algebra.TensorProduct.comm Λ (Λ ⧸ p) R)
          (Ideal.Quotient.mk p r ⊗ₜ[Λ] (1 : R)) =
          (1 : R) ⊗ₜ[Λ] Ideal.Quotient.mk p r
        rfl }
  exact e₁.trans e₂

private noncomputable def specialFibre_ringEquiv_quotient
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (p : Ideal Λ) [p.IsMaximal] :
    (R ⊗[Λ] (Λ ⧸ p)) ≃+* R ⧸ Ideal.map (algebraMap Λ R) p := by
  letI : Field (Λ ⧸ p) := Ideal.Quotient.field p
  let Bbar := R ⊗[Λ] (Λ ⧸ p)
  letI : Algebra (Λ ⧸ p) Bbar := Algebra.TensorProduct.rightAlgebra
  exact (specialFibre_algEquiv_quotient R p).symm.toRingEquiv

private theorem specialFibre_isLocalNoetherian
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (p : Ideal Λ) [p.IsMaximal]
    (hp : p = RingHom.ker (algebraMap Λ k)) :
    letI : Field (Λ ⧸ p) := Ideal.Quotient.field p
    let Bbar := R ⊗[Λ] (Λ ⧸ p)
    Nontrivial Bbar ∧ IsLocalRing Bbar ∧ IsNoetherianRing Bbar := by
  let : Field (Λ ⧸ p) := Ideal.Quotient.field p
  let J : Ideal R := Ideal.map (algebraMap Λ R) p
  have hJle : J ≤ maximalIdeal R := by
    rw [Ideal.map_le_iff_le_comap, hp, residueKernel_eq_comap_maximal R]
  have hJne : J ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hJle
  let : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJne
  let : IsLocalRing (R ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let : IsNoetherianRing (R ⧸ J) :=
    isNoetherianRing_of_surjective R (R ⧸ J) (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective
  let e := specialFibre_ringEquiv_quotient R p
  let : Nontrivial (R ⊗[Λ] (Λ ⧸ p)) := Function.Injective.nontrivial e.symm.injective
  let : IsLocalRing (R ⊗[Λ] (Λ ⧸ p)) :=
    IsLocalRing.of_surjective' e.symm.toRingHom e.symm.surjective
  let : IsNoetherianRing (R ⊗[Λ] (Λ ⧸ p)) :=
    isNoetherianRing_of_ringEquiv (R ⧸ J) e.symm
  exact ⟨inferInstance, inferInstance, inferInstance⟩

private theorem specialFibre_includeLeft_surjective
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (p : Ideal Λ) :
    let Bbar := R ⊗[Λ] (Λ ⧸ p)
    letI : Algebra (Λ ⧸ p) Bbar := Algebra.TensorProduct.rightAlgebra
    Function.Surjective (Algebra.TensorProduct.includeLeftRingHom : R →+* Bbar) := by
  dsimp only
  let Bbar := R ⊗[Λ] (Λ ⧸ p)
  let : Algebra (Λ ⧸ p) Bbar := Algebra.TensorProduct.rightAlgebra
  let e : Bbar ≃+* (Λ ⧸ p) ⊗[Λ] R :=
    (Algebra.TensorProduct.comm Λ R (Λ ⧸ p)).toRingEquiv
  intro x
  obtain ⟨r, hr⟩ := TensorProduct.mk_surjective Λ R (Λ ⧸ p)
    Ideal.Quotient.mk_surjective (e x)
  refine ⟨r, ?_⟩
  apply e.injective
  show (1 : Λ ⧸ p) ⊗ₜ[Λ] r = e x
  exact hr

private theorem specialFibre_geometricallyRegular_iff_formallySmooth
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (p : Ideal Λ) [p.IsMaximal]
    (hp : p = RingHom.ker (algebraMap Λ k)) :
    letI : Field (Λ ⧸ p) := Ideal.Quotient.field p
    let Bbar := R ⊗[Λ] (Λ ⧸ p)
    letI : Algebra (Λ ⧸ p) Bbar := Algebra.TensorProduct.rightAlgebra
    Algebra.IsGeometricallyRegular (Λ ⧸ p) Bbar ↔
      RingHom.FormallySmoothNAdic.{max u v}
        (algebraMap (Λ ⧸ p) Bbar)
        (Ideal.map (Algebra.TensorProduct.includeLeftRingHom : R →+* Bbar)
          (maximalIdeal R)) := by
  let : Field (Λ ⧸ p) := Ideal.Quotient.field p
  let Bbar := R ⊗[Λ] (Λ ⧸ p)
  let : Algebra (Λ ⧸ p) Bbar := Algebra.TensorProduct.rightAlgebra
  obtain ⟨htriv, hlocal, hnoeth⟩ := specialFibre_isLocalNoetherian R p hp
  let : Nontrivial Bbar := htriv
  let : IsLocalRing Bbar := hlocal
  let : IsNoetherianRing Bbar := hnoeth
  show Algebra.IsGeometricallyRegular (Λ ⧸ p) Bbar ↔
    RingHom.FormallySmoothNAdic.{max u v}
      (algebraMap (Λ ⧸ p) Bbar)
      (Ideal.map (Algebra.TensorProduct.includeLeftRingHom : R →+* Bbar)
        (maximalIdeal R))
  have hincl := specialFibre_includeLeft_surjective R p
  have hmax : Ideal.map (Algebra.TensorProduct.includeLeftRingHom : R →+* Bbar)
      (maximalIdeal R) = maximalIdeal Bbar :=
    IsLocalRing.map_maximalIdeal_of_surjective _ hincl
  rw [hmax]
  exact geometricallyRegular_iff_formallySmoothNAdic

private theorem formallySmoothNAdic_iff_comp_ringEquiv
    {A : Type u} {B : Type u} {C : Type v} [CommRing A] [CommRing B] [CommRing C]
    (φ : B →+* C) (e : A ≃+* B) (n : Ideal C) :
    RingHom.FormallySmoothNAdic.{max u v} φ n ↔
      RingHom.FormallySmoothNAdic.{max u v} (φ.comp e.toRingHom) n := by
  have key : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : B →+* C) (e : A ≃+* B),
      RingHom.FormallySmoothNAdic.{max u v} φ n →
        RingHom.FormallySmoothNAdic.{max u v} (φ.comp e.toRingHom) n := by
    intro A B _ _ φ e h E _ J hJ f ψ hcomm hk
    have hcomm' : ψ.comp φ =
        (Ideal.Quotient.mk J).comp (f.comp e.symm.toRingHom) := by
      ext a
      simpa using RingHom.congr_fun hcomm (e.symm a)
    obtain ⟨g, hq, hg⟩ := h E J hJ (f.comp e.symm.toRingHom) ψ hcomm' hk
    refine ⟨g, hq, ?_⟩
    ext a
    simpa using RingHom.congr_fun hg (e a)
  refine ⟨key φ e, fun h => ?_⟩
  have h' := key _ e.symm h
  rwa [RingHom.comp_assoc, ← RingEquiv.toRingHom_trans', e.symm_trans_self] at h'

-- Transporting the lifting square elaborates several quotient ring structures.
private theorem formallySmoothNAdic_iff_comp_codomainRingEquiv
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (e : B ≃+* C) (n : Ideal C) :
    RingHom.FormallySmoothNAdic.{max u v w} φ (Ideal.comap e n) ↔
      RingHom.FormallySmoothNAdic.{max u v w} (e.toRingHom.comp φ) n := by
  have hmem : ∀ k x, x ∈ Ideal.comap e n ^ k ↔ e x ∈ n ^ k := fun k x => by
    rw [← Ideal.apply_mem_of_equiv_iff (f := e), Ideal.map_pow,
      Ideal.map_comap_of_surjective e e.surjective n]
  constructor
  · intro h E _ J hJ f ψ hcomm ⟨k, hk, hpow⟩
    let ψB := ψ.comp e.toRingHom
    have hcommB : ψB.comp φ = (Ideal.Quotient.mk J).comp f := by
      simpa [ψB, RingHom.comp_assoc] using hcomm
    have hpowB : (Ideal.comap e n) ^ k ≤ RingHom.ker ψB := fun x hx => by
      simpa [ψB] using hpow ((hmem k x).1 hx)
    obtain ⟨g, hgq, hgf⟩ := h E J hJ f ψB hcommB ⟨k, hk, hpowB⟩
    refine ⟨g.comp e.symm.toRingHom, ?_, ?_⟩
    · ext x
      simpa [ψB] using RingHom.congr_fun hgq (e.symm x)
    · ext x
      simpa [RingHom.comp_assoc] using RingHom.congr_fun hgf x
  · intro h E _ J hJ f ψ hcomm ⟨k, hk, hpow⟩
    let ψC := ψ.comp e.symm.toRingHom
    have hcommC : ψC.comp (e.toRingHom.comp φ) =
        (Ideal.Quotient.mk J).comp f := by
      apply RingHom.ext
      intro x
      show ψ (e.symm (e (φ x))) = _
      rw [e.symm_apply_apply]
      exact RingHom.congr_fun hcomm x
    have hpowC : n ^ k ≤ RingHom.ker ψC := fun x hx => by
      simpa [ψC] using hpow ((hmem k _).2 (by simpa using hx))
    obtain ⟨g, hgq, hgf⟩ := h E J hJ f ψC hcommC ⟨k, hk, hpowC⟩
    refine ⟨g.comp e.toRingHom, ?_, ?_⟩
    · ext x
      simpa [ψC] using RingHom.congr_fun hgq (e x)
    · ext x
      simpa [RingHom.comp_assoc] using RingHom.congr_fun hgf x

/-- The structure functor of the restricted representable category of `R`, as a morphism of
categories over `𝒞_Λ` to that base category regarded as a based category over itself. -/
public def restrictedCoyonedaProjection
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    BasedFunctor (restrictedRepresentable R)
      (BasedCategory.ofFunctor (𝟭 (ArtinianLocalAlgCat.{u, v, w} Λ k))) where
  toFunctor := CategoryOfElements.π (restrictedCoyoneda R)
  w := rfl

variable [IsNoetherianRing Λ] [Module.Finite Λ k]

private noncomputable def localizedStructureMap
    {p : Ideal Λ} [p.IsPrime]
    (R : CompleteLocalAlgCat.{u, v, w} Λ k)
    (hp : p = RingHom.ker (algebraMap Λ k)) :
    Localization.AtPrime p →+* R :=
  IsLocalization.lift (M := p.primeCompl) (g := algebraMap Λ R)
    (fun s => structureMap_isUnit_of_not_mem_residueKernel R.residueEquiv s.1
      (by simpa [hp] using s.2))

omit [IsNoetherianRing Λ] [Module.Finite Λ k] in
private theorem localizedStructureMap_comp
    {p : Ideal Λ} [p.IsPrime]
    (R : CompleteLocalAlgCat.{u, v, w} Λ k)
    (hp : p = RingHom.ker (algebraMap Λ k)) :
    (localizedStructureMap R hp).comp (algebraMap Λ (Localization.AtPrime p)) =
      algebraMap Λ R :=
  IsLocalization.lift_comp (M := p.primeCompl) (g := algebraMap Λ R) _

private theorem residueField_eq_maximalIdeal_quotient
    {A : Type*} [CommRing A] [IsLocalRing A] :
    ResidueField A = (A ⧸ maximalIdeal A) := rfl

-- The composite equivalence elaborates the localized tensor product and quotient structures.
private noncomputable def localizedSpecialFibre_ringEquiv_quotient
    {p : Ideal Λ} [p.IsPrime]
    (R : CompleteLocalAlgCat.{u, v, w} Λ k)
    (hp : p = RingHom.ker (algebraMap Λ k)) :
    let T := Localization.AtPrime p
    letI : Algebra T R := (localizedStructureMap R hp).toAlgebra
    (R ⊗[T] ResidueField T) ≃+*
      R ⧸ Ideal.map (localizedStructureMap R hp) (maximalIdeal T) := by
  let T := Localization.AtPrime p
  letI : Algebra T R := (localizedStructureMap R hp).toAlgebra
  let e₁ : (R ⊗[T] ResidueField T) ≃+* ResidueField T ⊗[T] R :=
    (Algebra.TensorProduct.comm T R (ResidueField T)).toRingEquiv
  let eK : ResidueField T ≃ₐ[T] (T ⧸ maximalIdeal T) :=
    { toRingEquiv :=
        { toFun := @Equiv.cast (ResidueField T) (T ⧸ maximalIdeal T)
            (residueField_eq_maximalIdeal_quotient (A := T))
          invFun := @Equiv.cast (T ⧸ maximalIdeal T) (ResidueField T)
            (residueField_eq_maximalIdeal_quotient (A := T)).symm
          left_inv _ := by simp
          right_inv _ := by simp
          map_mul' _ _ := rfl
          map_add' _ _ := rfl }
      commutes' := by
        intro x
        rw [IsLocalRing.ResidueField.algebraMap_eq]
        rfl }
  let e₂ : (ResidueField T ⊗[T] R) ≃+*
      (T ⊗[T] R) ⧸ Ideal.map (algebraMap T (T ⊗[T] R)) (maximalIdeal T) :=
    ((Algebra.TensorProduct.congr eK (AlgEquiv.refl : R ≃ₐ[T] R)).toRingEquiv).trans
      (Algebra.TensorProduct.quotientTensorEquiv (S := T) R T
        (maximalIdeal T)).toRingEquiv
  let e₃ : (T ⊗[T] R) ≃ₐ[T] R := Algebra.TensorProduct.lid T R
  let I : Ideal (T ⊗[T] R) := Ideal.map (algebraMap T (T ⊗[T] R)) (maximalIdeal T)
  let J : Ideal R := Ideal.map (algebraMap T R) (maximalIdeal T)
  let f : (T ⊗[T] R) →+* R := (e₃.toRingEquiv : (T ⊗[T] R) →+* R)
  have hc : f.comp (algebraMap T (T ⊗[T] R)) = algebraMap T R := by
    ext a
    simp [f, e₃, Algebra.smul_def]
  have hIJ : J = Ideal.map f I := by
    dsimp [J, I]
    rw [← hc]
    exact (Ideal.map_map (algebraMap T (T ⊗[T] R)) f).symm
  let e₄ : ((T ⊗[T] R) ⧸ I) ≃+* (R ⧸ J) :=
    Ideal.quotientEquiv I J e₃.toRingEquiv (by simpa [f] using hIJ)
  exact e₁.trans (e₂.trans e₄)

omit [IsNoetherianRing Λ] [Module.Finite Λ k] in
private theorem localizedSpecialFibre_ideal_eq
    {p : Ideal Λ} [p.IsPrime]
    (R : CompleteLocalAlgCat.{u, v, w} Λ k)
    (hp : p = RingHom.ker (algebraMap Λ k)) :
    let T := Localization.AtPrime p
    letI : Algebra T R := (localizedStructureMap R hp).toAlgebra
    Ideal.map (localizedStructureMap R hp) (maximalIdeal T) =
      Ideal.map (algebraMap Λ R) p := by
  let T := Localization.AtPrime p
  let : Algebra T R := (localizedStructureMap R hp).toAlgebra
  show Ideal.map (localizedStructureMap R hp) (maximalIdeal T) =
    Ideal.map (algebraMap Λ R) p
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p T, Ideal.map_map,
    localizedStructureMap_comp]

omit [IsNoetherianRing Λ] [Module.Finite Λ k] in
private noncomputable def localizedSpecialFibre_algEquiv
    {p : Ideal Λ} [p.IsMaximal]
    (R : CompleteLocalAlgCat.{u, v, w} Λ k)
    (hp : p = RingHom.ker (algebraMap Λ k)) :
    letI : Field (Λ ⧸ p) := Ideal.Quotient.field p
    let T := Localization.AtPrime p
    letI : Algebra T R := (localizedStructureMap R hp).toAlgebra
    let F := R ⊗[T] ResidueField T
    letI : Algebra (ResidueField T) F := Algebra.TensorProduct.rightAlgebra
    let eK : (Λ ⧸ p) ≃+* ResidueField T :=
      (IsLocalization.AtPrime.equivQuotMaximalIdeal p T).toRingEquiv
    let Bbar := R ⊗[Λ] (Λ ⧸ p)
    letI : Algebra (Λ ⧸ p) F :=
      ((algebraMap (ResidueField T) F).comp eK.toRingHom).toAlgebra
    letI : Algebra (Λ ⧸ p) Bbar := Algebra.TensorProduct.rightAlgebra
    F ≃ₐ[Λ ⧸ p] Bbar := by
  letI : Field (Λ ⧸ p) := Ideal.Quotient.field p
  let T := Localization.AtPrime p
  letI : Algebra T R := (localizedStructureMap R hp).toAlgebra
  let F := R ⊗[T] ResidueField T
  let Bbar := R ⊗[Λ] (Λ ⧸ p)
  letI : Algebra (ResidueField T) F := Algebra.TensorProduct.rightAlgebra
  let eK : (Λ ⧸ p) ≃+* ResidueField T :=
    (IsLocalization.AtPrime.equivQuotMaximalIdeal p T).toRingEquiv
  letI : Algebra (Λ ⧸ p) F :=
    ((algebraMap (ResidueField T) F).comp eK.toRingHom).toAlgebra
  letI : Algebra (Λ ⧸ p) Bbar := Algebra.TensorProduct.rightAlgebra
  let J₁ : Ideal R := Ideal.map (localizedStructureMap R hp) (maximalIdeal T)
  let J₂ : Ideal R := Ideal.map (algebraMap Λ R) p
  let e₁ := localizedSpecialFibre_ringEquiv_quotient R hp
  let e₂ := specialFibre_ringEquiv_quotient R p
  have hJ : J₁ = J₂ := localizedSpecialFibre_ideal_eq R hp
  let q : (R ⧸ J₁) ≃+* (R ⧸ J₂) :=
    Ideal.quotientEquiv J₁ J₂ (RingEquiv.refl R) (by simpa using hJ.symm)
  let e : F ≃+* Bbar := e₁.trans (q.trans e₂.symm)
  refine { toRingEquiv := e, commutes' := ?_ }
  intro a
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
  have heKval : eK (Ideal.Quotient.mk p r) =
      Ideal.Quotient.mk (maximalIdeal T) (algebraMap Λ T r) := rfl
  have h₁ : e₁ (algebraMap (Λ ⧸ p) F (Ideal.Quotient.mk p r)) =
      Ideal.Quotient.mk J₁ (algebraMap Λ R r) := by
    change e₁ ((algebraMap (ResidueField T) F) (eK (Ideal.Quotient.mk p r))) = _
    rw [heKval]
    let z : ResidueField T := Ideal.Quotient.mk (maximalIdeal T) (algebraMap Λ T r)
    change e₁ ((1 : R) ⊗ₜ[T] z) = _
    simp only [e₁, localizedSpecialFibre_ringEquiv_quotient, RingEquiv.trans_apply]
    have hcomm :
        (Algebra.TensorProduct.comm T R (ResidueField T)).toRingEquiv
          ((1 : R) ⊗ₜ[T] z) = z ⊗ₜ[T] (1 : R) :=
      Algebra.TensorProduct.comm_tmul T (1 : R) z
    rw [hcomm]
    simp only [RingEquiv.coe_mk, AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe,
      Algebra.TensorProduct.congr_apply, AlgEquiv.refl_toAlgHom, Ideal.quotientEquiv_apply,
      AlgEquiv.toRingEquiv_toRingHom, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
      MonoidHom.toOneHom_coe, MonoidHom.coe_coe, Ideal.Quotient.mk_algebraMap]
    change (Ideal.quotientMap _ _ _)
      (Algebra.TensorProduct.quotientTensorEquiv (R := T) (S := T) (T := R)
        (A := T) (maximalIdeal T)
        ((algebraMap Λ (T ⧸ maximalIdeal T) r) ⊗ₜ[T] (1 : R))) = _
    rw [show algebraMap Λ (T ⧸ maximalIdeal T) r =
      Ideal.Quotient.mk (maximalIdeal T) (algebraMap Λ T r) by rfl]
    rw [Algebra.TensorProduct.quotientTensorEquiv_apply_tmul]
    rw [Ideal.quotientMap_mk]
    change Ideal.Quotient.mk J₁
      ((Algebra.TensorProduct.lid T R) ((algebraMap Λ T r) ⊗ₜ[T] (1 : R))) = _
    rw [Algebra.TensorProduct.lid_tmul]
    rw [← Algebra.algebraMap_eq_smul_one]
    change Ideal.Quotient.mk J₁
      (algebraMap T R (algebraMap Λ T r)) =
      Ideal.Quotient.mk J₁ (algebraMap Λ R r)
    have h := RingHom.congr_fun (localizedStructureMap_comp R hp) r
    change algebraMap T (R ⧸ J₁) (algebraMap Λ T r) = _
    rw [show algebraMap T (R ⧸ J₁) (algebraMap Λ T r) =
      Ideal.Quotient.mk J₁ (localizedStructureMap R hp (algebraMap Λ T r)) by rfl]
    simpa using congrArg (Ideal.Quotient.mk J₁) h
  have hscalar : algebraMap (Λ ⧸ p) (R ⧸ J₂) (Ideal.Quotient.mk p r) =
      Ideal.Quotient.mk J₂ (algebraMap Λ R r) := rfl
  have h₂ : e₂.symm (Ideal.Quotient.mk J₂ (algebraMap Λ R r)) =
      algebraMap (Λ ⧸ p) Bbar (Ideal.Quotient.mk p r) := by
    rw [← hscalar]
    change (specialFibre_algEquiv_quotient R p)
      (algebraMap (Λ ⧸ p) (R ⧸ J₂) (Ideal.Quotient.mk p r)) = _
    exact (specialFibre_algEquiv_quotient R p).commutes _
  change e₂.symm (q (e₁ (algebraMap (Λ ⧸ p) F (Ideal.Quotient.mk p r)))) = _
  rw [h₁, Ideal.quotientEquiv_mk]
  exact h₂

omit [IsNoetherianRing Λ] [Module.Finite Λ k] in
private theorem localizedStructureMap_isLocalHom
    {p : Ideal Λ} [p.IsPrime]
    (R : CompleteLocalAlgCat.{u, v, w} Λ k)
    (hp : p = RingHom.ker (algebraMap Λ k)) :
    IsLocalHom (localizedStructureMap R hp) := by
  let q := maximalIdeal R
  have hpq : p = q.comap (algebraMap Λ R) := hp.trans (residueKernel_eq_comap_maximal R)
  let l := Localization.localRingHom p q (algebraMap Λ R) hpq
  have hunit : q.primeCompl ≤ IsUnit.submonoid R := by
    intro x hx
    apply (IsLocalRing.residue_ne_zero_iff_isUnit x).mp
    intro hz
    exact hx ((IsLocalRing.residue_eq_zero_iff x).mp hz)
  let e : R ≃ₐ[R] Localization.AtPrime q :=
    IsLocalization.atUnits R q.primeCompl hunit
  have heq : (localizedStructureMap R hp).comp (algebraMap Λ (Localization.AtPrime p)) =
      ((e.symm : Localization.AtPrime q →ₐ[R] R).toRingHom.comp l).comp
        (algebraMap Λ (Localization.AtPrime p)) := by
    ext a
    rw [localizedStructureMap_comp (R := R) hp]
    simp [RingHom.comp_apply, Localization.localRingHom_to_map, l, e]
  have hmaps : localizedStructureMap R hp =
      (e.symm : Localization.AtPrime q →ₐ[R] R).toRingHom.comp l :=
    IsLocalization.ringHom_ext p.primeCompl heq
  let : IsLocalHom l := Localization.isLocalHom_localRingHom p q
    (algebraMap Λ R) hpq
  let : IsLocalHom (e.symm : Localization.AtPrime q →+* R) :=
    isLocalHom_of_leftInverse (e : R →+* Localization.AtPrime q) e.apply_symm_apply
  rw [hmaps]
  exact RingHom.isLocalHom_comp (e.symm : Localization.AtPrime q →+* R) l

omit [IsNoetherianRing Λ] [Module.Finite Λ k] in
private theorem flat_iff_flat_localizedStructureMap
    {p : Ideal Λ} [p.IsPrime]
    (R : CompleteLocalAlgCat.{u, v, w} Λ k)
    (hp : p = RingHom.ker (algebraMap Λ k)) :
    let T := Localization.AtPrime p
    letI : Algebra T R := (localizedStructureMap R hp).toAlgebra
    Module.Flat Λ R ↔ Module.Flat (Localization.AtPrime p) R := by
  let T := Localization.AtPrime p
  let : Algebra T R := (localizedStructureMap R hp).toAlgebra
  let : IsScalarTower Λ T R := IsScalarTower.of_algebraMap_eq
    (fun a => (RingHom.congr_fun (localizedStructureMap_comp R hp) a).symm)
  let : IsLocalizedModule p.primeCompl (LinearMap.id : R →ₗ[Λ] R) :=
    isLocalizedModule_id p.primeCompl R T
  exact (Module.flat_iff_of_isLocalization (R := Λ) (S := T)
    (M := R) p.primeCompl).symm

end Deformation

end
