module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Support
public import StacksCore.RingTheory.Localization.Ideal
public import StacksFrontier.RingTheory.Flat.FibrewiseCriterionEssFPBase
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Critère de platitude par fibres: locally nilpotent ideals

Let `R → S → S'` be ring maps, let `I ⊆ R` be a locally nilpotent ideal and let `M` be an
`S'`-module. Assume that `R → S` is of finite type, that `R → S'` is of finite presentation, that
`M` is a finitely presented `S'`-module, that `M/IM` is flat over `S/IS` and that `M` is flat over
`R`. Then `M` is flat over `S`, and `S_q` is flat and essentially of finite presentation over `R`
at every prime `q ⊆ S` with `M ⊗_S κ(q) ≠ 0`. Here `IM` is written `IS • ⊤` inside `M` viewed as an
`S`-module, "locally nilpotent" means that every element of `I` is nilpotent, and `S_q` is any
localization of `S` at `q` which is an `R`-algebra compatibly with `R → S`.

## Main results

* `Module.flat_and_flat_localization_of_flat_quotient_of_locallyNilpotent`: the statement above.
* `Module.flat_of_isLocalizedModule`: a localization of an `R`-flat module at a multiplicative
  subset of an `R`-algebra is `R`-flat.
* `Module.Flat.localization_quotient_smul_top`: flatness of a fibre `M/KM` over `A/K` survives
  localization at primes of `A` and of an `A`-algebra acting on `M`.
* `Module.Flat.quotient_smul_top_of_le`: flatness of `M/IM` over `S/I` gives flatness of `M/JM`
  over `S/J` for every ideal `J ⊇ I`.

## References

* [Stacks Project, Tag 0CEL](https://stacks.math.columbia.edu/tag/0CEL)
-/

@[expose] public section

open TensorProduct

/-! ### Flatness of fibres -/

/-- If `e : A ≃+* A'` and `φ : N ≃+ N'` is
semilinear over `e`, then flatness of `N'` over `A'` gives flatness of `N` over `A`. -/
private theorem flat_of_ringEquiv {A A' N N' : Type*} [CommRing A] [CommRing A']
    [AddCommGroup N] [AddCommGroup N'] [Module A N] [Module A' N'] [Module.Flat A' N']
    (e : A ≃+* A') (φ : N ≃+ N') (hφ : ∀ (a : A) (n : N), φ (a • n) = e a • φ n) :
    Module.Flat A N := by
  let algAA' : Algebra A A' := (e : A →+* A').toAlgebra
  let modAN' : Module A N' := Module.compHom N' (e : A →+* A')
  have hsmul : ∀ (a : A) (n : N'), a • n = e a • n := fun _ _ => rfl
  have : IsScalarTower A A' N' := IsScalarTower.of_algebraMap_smul fun a n => hsmul a n
  have : Module.Flat A A' := RingHom.Flat.of_bijective (f := (e : A →+* A')) e.bijective
  have : Module.Flat A N' := Module.Flat.trans A A' N'
  exact Module.Flat.of_linearEquiv (φ.toLinearEquiv (R := A) fun a n => by rw [hφ, hsmul])


/-- Let `S` be an `R`-algebra and `M` an `S`-module which is flat over `R`. Then every
localization of `M` at a submonoid of `S` is flat over `R`. -/
theorem Module.flat_of_isLocalizedModule {R : Type*} (S : Type*) [CommSemiring R] [CommSemiring S]
    [Algebra R S] {M Mₚ : Type*} [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
    [AddCommMonoid Mₚ] [Module R Mₚ] [Module S Mₚ] [IsScalarTower R S Mₚ]
    (p : Submonoid S) (f : M →ₗ[S] Mₚ) [IsLocalizedModule p f] [Module.Flat R M] :
    Module.Flat R Mₚ := by
  have H := (Module.Flat.iff_lTensor_injectiveₛ (R := R) (M := M)).mp inferInstance
  rw [Module.Flat.iff_lTensor_injectiveₛ]
  simp_rw [← AlgebraTensorModule.coe_lTensor (A := S)] at H ⊢
  intro P _ _ N
  have := IsLocalizedModule.map_injective p (AlgebraTensorModule.rTensor R N f)
    (AlgebraTensorModule.rTensor R P f) _ (H N)
  simpa [IsLocalizedModule.map_lTensor] using this

/-- The localization of an ideal `J` of `B`, as a submodule of `B`, is the extended ideal. -/
theorem Submodule.localized'_ideal_eq_map {B Bₚ : Type*} [CommSemiring B] [CommSemiring Bₚ]
    [Algebra B Bₚ] (T : Submonoid B) [IsLocalization T Bₚ] (J : Ideal B) :
    (J : Submodule B B).localized' Bₚ T (Algebra.linearMap B Bₚ) = J.map (algebraMap B Bₚ) := by
  rw [Submodule.localized'_eq_span]
  rfl

/-- If `P` is flat over `A`, then `P/KP` is flat over `A/K`. -/
theorem Module.Flat.quotient_smul_top {A P : Type*} [CommRing A] [AddCommGroup P] [Module A P]
    [Module.Flat A P] (K : Ideal A) : Module.Flat (A ⧸ K) (P ⧸ (K • ⊤ : Submodule A P)) := by
  exact Module.Flat.of_linearEquiv ((TensorProduct.quotTensorEquivQuotSMul P K)
    |>.extendScalarsOfSurjective (S := A ⧸ K) Ideal.Quotient.mk_surjective).symm

/-- If `I ≤ J` are ideals of `S` and `M/IM` is flat over `S/I`, then `M/JM` is flat over
`S/J`. -/
theorem Module.Flat.quotient_smul_top_of_le {S M : Type*} [CommRing S] [AddCommGroup M] [Module S M]
    {I J : Ideal S} (h : I ≤ J) [Module.Flat (S ⧸ I) (M ⧸ (I • ⊤ : Submodule S M))] :
    Module.Flat (S ⧸ J) (M ⧸ (J • ⊤ : Submodule S M)) := by
  set P₁ := M ⧸ (I • ⊤ : Submodule S M)
  set K₁ : Ideal (S ⧸ I) := J.map (Ideal.Quotient.mk I)
  have := Module.Flat.quotient_smul_top (A := S ⧸ I) (P := P₁) K₁
  have hle : (I • ⊤ : Submodule S M) ≤ J • ⊤ := Submodule.smul_mono_left h
  have hset : ((K₁ • ⊤ : Submodule (S ⧸ I) P₁) : Set P₁) =
      (((J • ⊤ : Submodule S M).map (I • ⊤ : Submodule S M).mkQ : Submodule S P₁) : Set P₁) := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
    exact Stacks.Flatness.FibrewiseCriterionEssFP.coe_map_smul_top (R := S) (A := S ⧸ I)
      (M := P₁) J
  let φ : (P₁ ⧸ (K₁ • ⊤ : Submodule (S ⧸ I) P₁)) ≃+ M ⧸ (J • ⊤ : Submodule S M) :=
    (Stacks.Flatness.FibrewiseCriterionEssFP.quotAddEquivOfCoeEq _ _ hset).trans
      (Submodule.quotientQuotientEquivQuotient _ _ hle).toAddEquiv
  refine Stacks.Flatness.EssFPLocalCriterion.flat_of_ringEquiv_of_addEquiv
    (DoubleQuot.quotQuotEquivQuotOfLE h).symm φ.symm fun a x => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hx : Submodule.Quotient.mk x = φ (Submodule.Quotient.mk (Submodule.Quotient.mk x)) := rfl
  rw [hx, AddEquiv.symm_apply_apply, DoubleQuot.quotQuotEquivQuotOfLE_symm_mk]
  rfl

/-- Flatness over `A ⧸ K` transfers between two quotients of `P` by submodules (over possibly
different rings) with the same elements, when `A ⧸ K` acts on both through `A`. -/
private theorem flat_quotient_of_coe_eq {A B₁ B₂ P : Type*} [CommRing A] [CommRing B₁]
    [CommRing B₂] [AddCommGroup P] [Module A P] [Module B₁ P] [Module B₂ P] (K : Ideal A)
    (Q₁ : Submodule B₁ P) (Q₂ : Submodule B₂ P) [Module (A ⧸ K) (P ⧸ Q₁)]
    [Module (A ⧸ K) (P ⧸ Q₂)] [Module.Flat (A ⧸ K) (P ⧸ Q₂)] (hset : (Q₁ : Set P) = Q₂)
    (h₁ : ∀ (a : A) (x : P),
      Ideal.Quotient.mk K a • (Submodule.Quotient.mk x : P ⧸ Q₁) = Submodule.Quotient.mk (a • x))
    (h₂ : ∀ (a : A) (x : P),
      Ideal.Quotient.mk K a • (Submodule.Quotient.mk x : P ⧸ Q₂) = Submodule.Quotient.mk (a • x)) :
    Module.Flat (A ⧸ K) (P ⧸ Q₁) := by
  refine Stacks.Flatness.EssFPLocalCriterion.flat_of_ringEquiv_of_addEquiv (RingEquiv.refl _)
    (Stacks.Flatness.FibrewiseCriterionEssFP.quotAddEquivOfCoeEq _ _ hset) fun a x => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact (congrArg _ (h₁ a x)).trans (h₂ a x).symm

/-- The localization of `M` at the prime `P`, as the base change `M ⊗[S'] S'_P`. -/
private theorem isLocalizedModule_mk_tensor {S' : Type*} [CommRing S'] {M : Type*}
    [AddCommGroup M] [Module S' M] (P : Ideal S') [P.IsPrime] :
    IsLocalizedModule P.primeCompl (TensorProduct.mk S' (Localization.AtPrime P) M 1) :=
  (isLocalizedModule_iff_isBaseChange _ _ _).mpr (TensorProduct.isBaseChange S' M _)

/-- Let `A → B` be a ring map, `P` a `B`-module, `K` an ideal of `A`
with `P/KP` flat over `A/K`. Let `Aₚ` be a localization of `A`, `Bₚ` a localization of `B` which is
an `A`-algebra compatibly, and `Pₚ` the localization of `P` at the same submonoid of `B`, a module
over `Aₚ` compatibly with `A`. Then `Pₚ/KPₚ` is flat over `Aₚ/KAₚ`. -/
theorem Module.Flat.localization_quotient_smul_top {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B]
    {P : Type*} [AddCommGroup P] [Module A P] [Module B P] [IsScalarTower A B P]
    (K : Ideal A) [Module.Flat (A ⧸ K) (P ⧸ (K • ⊤ : Submodule A P))]
    (U : Submonoid A) (Aₚ : Type*) [CommRing Aₚ] [Algebra A Aₚ] [IsLocalization U Aₚ]
    (T : Submonoid B) (Bₚ : Type*) [CommRing Bₚ] [Algebra B Bₚ] [IsLocalization T Bₚ]
    [Algebra A Bₚ] [IsScalarTower A B Bₚ]
    {Pₚ : Type*} [AddCommGroup Pₚ] [Module A Pₚ] [Module Aₚ Pₚ] [Module B Pₚ] [Module Bₚ Pₚ]
    [IsScalarTower A Aₚ Pₚ] [IsScalarTower B Bₚ Pₚ] [IsScalarTower A Bₚ Pₚ]
    (f : P →ₗ[B] Pₚ) [IsLocalizedModule T f] :
    Module.Flat (Aₚ ⧸ K.map (algebraMap A Aₚ))
      (Pₚ ⧸ (K.map (algebraMap A Aₚ) • ⊤ : Submodule Aₚ Pₚ)) := by
  set KB : Ideal B := K.map (algebraMap A B)
  set KBₚ : Ideal Bₚ := KB.map (algebraMap B Bₚ)
  set KAₚ : Ideal Aₚ := K.map (algebraMap A Aₚ)
  have hKBₚ : KBₚ = K.map (algebraMap A Bₚ) := by
    simp only [KBₚ, KB, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  let modX' : Module (A ⧸ K) (P ⧸ (KB • ⊤ : Submodule B P)) :=
    Module.compHom _ (algebraMap (A ⧸ K) (B ⧸ KB))
  have towX' : IsScalarTower (A ⧸ K) (B ⧸ KB) (P ⧸ (KB • ⊤ : Submodule B P)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have flatX' : Module.Flat (A ⧸ K) (P ⧸ (KB • ⊤ : Submodule B P)) := by
    refine flat_quotient_of_coe_eq K _ (K • ⊤ : Submodule A P)
      (Stacks.Flatness.FibrewiseCriterionEssFP.coe_map_smul_top (R := A) (A := B) (M := P) K)
      (fun a x => congrArg Submodule.Quotient.mk (algebraMap_smul B a x)) fun _ _ => rfl
  set Y' := Pₚ ⧸ (KBₚ • ⊤ : Submodule Bₚ Pₚ)
  have hloc : (KB • ⊤ : Submodule B P).localized' Bₚ T f = KBₚ • ⊤ :=
    Submodule.localized'_smul_top T KB Bₚ f
  let gB : P ⧸ (KB • ⊤ : Submodule B P) →ₗ[B] Y' :=
    ((Submodule.quotEquivOfEq _ _ hloc).restrictScalars B).toLinearMap ∘ₗ
      (KB • ⊤ : Submodule B P).toLocalizedQuotient' Bₚ T f
  have : IsLocalizedModule T gB := inferInstance
  let modY' : Module (B ⧸ KB) Y' := Module.compHom _ (algebraMap (B ⧸ KB) (Bₚ ⧸ KBₚ))
  have towBY' : IsScalarTower B (B ⧸ KB) Y' := IsScalarTower.of_algebraMap_smul fun b y => by
    show (algebraMap (B ⧸ KB) (Bₚ ⧸ KBₚ) (algebraMap B (B ⧸ KB) b)) • y = b • y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    show Submodule.Quotient.mk (algebraMap B Bₚ b • y) = Submodule.Quotient.mk (b • y)
    rw [algebraMap_smul]
  let g : P ⧸ (KB • ⊤ : Submodule B P) →ₗ[B ⧸ KB] Y' :=
    gB.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  have : IsLocalizedModule T (g.restrictScalars B) := by
    show IsLocalizedModule T gB
    infer_instance
  have : IsLocalizedModule (Algebra.algebraMapSubmonoid (B ⧸ KB) T) g :=
    IsLocalizedModule.of_restrictScalars T g
  let modY'A : Module (A ⧸ K) Y' := Module.compHom _ (algebraMap (A ⧸ K) (B ⧸ KB))
  have towY' : IsScalarTower (A ⧸ K) (B ⧸ KB) Y' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have flatY' : Module.Flat (A ⧸ K) Y' :=
    Module.flat_of_isLocalizedModule (B ⧸ KB) (Algebra.algebraMapSubmonoid (B ⧸ KB) T) g
  set Y := Pₚ ⧸ (KAₚ • ⊤ : Submodule Aₚ Pₚ)
  let modY : Module (A ⧸ K) Y := Module.compHom _ (algebraMap (A ⧸ K) (Aₚ ⧸ KAₚ))
  have towY : IsScalarTower (A ⧸ K) (Aₚ ⧸ KAₚ) Y := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hset : ((KAₚ • ⊤ : Submodule Aₚ Pₚ) : Set Pₚ) = ((KBₚ • ⊤ : Submodule Bₚ Pₚ) : Set Pₚ) := by
    rw [Stacks.Flatness.FibrewiseCriterionEssFP.coe_map_smul_top (R := A) (A := Aₚ) (M := Pₚ) K,
      hKBₚ,
      Stacks.Flatness.FibrewiseCriterionEssFP.coe_map_smul_top (R := A) (A := Bₚ) (M := Pₚ) K]
  have flatY : Module.Flat (A ⧸ K) Y := by
    exact flat_quotient_of_coe_eq K _ _ hset
      (fun a y => congrArg Submodule.Quotient.mk (algebraMap_smul Aₚ a y))
      fun a y => congrArg Submodule.Quotient.mk
        (by rw [← IsScalarTower.algebraMap_apply, algebraMap_smul] :
          algebraMap B Bₚ (algebraMap A B a) • y = a • y)
  exact (Module.flat_iff_of_isLocalization (Aₚ ⧸ KAₚ)
    (Algebra.algebraMapSubmonoid (A ⧸ K) U) Y).mpr flatY

/-! ### Essential finite presentation -/

/-- A localization of a finitely presented `R`-algebra is essentially of finite presentation
over `R`. -/
theorem RingHom.EssentiallyOfFinitePresentation.of_isLocalization {R C S : Type*} [CommRing R]
    [CommRing C] [CommRing S] [Algebra R C] [Algebra C S] [Algebra R S] [IsScalarTower R C S]
    [Algebra.FinitePresentation R C] (U : Submonoid C) [IsLocalization U S] :
    (algebraMap R S).EssentiallyOfFinitePresentation := by
  obtain ⟨A, _, _, _, _, _, U', _⟩ := essFP_reuniverse (R := R) (T := S) C U
  have h := IsScalarTower.algebraMap_eq R A S
  let := (algebraMap R S).toAlgebra
  refine ⟨A, inferInstance, inferInstance, inferInstance, ?_, inferInstance, U', inferInstance⟩
  exact IsScalarTower.of_algebraMap_eq' h

/-- Composing a ring map essentially of finite presentation with a ring isomorphism gives a ring
map essentially of finite presentation. -/
theorem RingHom.EssentiallyOfFinitePresentation.comp_ringEquiv {R S S₂ : Type*} [CommRing R]
    [CommRing S] [CommRing S₂] {f : R →+* S} (hf : f.EssentiallyOfFinitePresentation)
    (e : S ≃+* S₂) : ((e : S →+* S₂).comp f).EssentiallyOfFinitePresentation := by
  let := f.toAlgebra
  obtain ⟨A, _, _, _, _, _, T, hloc⟩ := hf
  have h := IsScalarTower.algebraMap_eq R A S
  let := ((e : S →+* S₂).comp f).toAlgebra
  let : Algebra A S₂ := ((e : S →+* S₂).comp (algebraMap A S)).toAlgebra
  have : IsScalarTower R A S₂ := IsScalarTower.of_algebraMap_eq' <| by
    show (e : S →+* S₂).comp f = ((e : S →+* S₂).comp (algebraMap A S)).comp (algebraMap R A)
    rw [RingHom.comp_assoc, ← h]
    rfl
  have : IsLocalization T S₂ := (IsLocalization.isLocalization_iff_of_ringEquiv T e).mp hloc
  exact RingHom.EssentiallyOfFinitePresentation.of_isLocalization (C := A) T

/-! ### The criterion -/

open IsLocalRing in
/-- Let `q'` be a prime of `S'` lying over `q ⊆ S` and `p ⊆ R` with `M_{q'} ≠ 0`, and suppose that
`M/pM` is flat over `S/pS`. Then `S_q` is flat and essentially of finite presentation over `R`,
and `M_{q'}` is flat over `S`. -/
private theorem flat_localization_of_flat_fibre {R S S' : Type*} [CommRing R] [CommRing S]
    [CommRing S'] [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    {M : Type*} [AddCommGroup M] [Module R M] [Module S M]
    [Module S' M] [IsScalarTower R S M] [IsScalarTower S S' M]
    [Algebra.FiniteType R S] [Algebra.FinitePresentation R S'] [Module.FinitePresentation S' M]
    [Module.Flat R M] (q' : Ideal S') [q'.IsPrime]
    [Module.Flat (S ⧸ (q'.under R).map (algebraMap R S))
      (M ⧸ ((q'.under R).map (algebraMap R S) • (⊤ : Submodule S M)))]
    [Nontrivial (Localization.AtPrime q' ⊗[S'] M)] :
    Module.Flat R (Localization.AtPrime (q'.under S)) ∧
      (algebraMap R (Localization.AtPrime (q'.under S))).EssentiallyOfFinitePresentation ∧
      Module.Flat S (Localization.AtPrime q' ⊗[S'] M) := by
  set p := q'.under R
  set q := q'.under S
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let Sq' := Localization.AtPrime q'
  let N := Sq' ⊗[S'] M
  let := Localization.AtPrime.algebraOfLiesOver q q'
  let := Localization.AtPrime.algebraOfLiesOver p q'
  let := Localization.AtPrime.algebraOfLiesOver p q
  have : IsScalarTower R S' M := IsScalarTower.of_algebraMap_smul fun r m => by
    rw [IsScalarTower.algebraMap_apply R S S', algebraMap_smul, algebraMap_smul]
  have : IsLocalHom (algebraMap Rp Sq) := Localization.isLocalHom_localRingHom _ _ _ _
  have : IsLocalHom (algebraMap Sq Sq') := Localization.isLocalHom_localRingHom _ _ _ _
  have hN : IsLocalizedModule q'.primeCompl (TensorProduct.mk S' Sq' M 1) :=
    isLocalizedModule_mk_tensor q'
  have : Algebra.EssFiniteType R Sq := by
    have : Algebra.EssFiniteType S Sq := Algebra.EssFiniteType.of_isLocalization Sq q.primeCompl
    exact Algebra.EssFiniteType.comp R S Sq
  have : Algebra.EssFiniteType Rp Sq := Algebra.EssFiniteType.of_comp R Rp Sq
  have : Module.Flat R N :=
    Module.flat_of_isLocalizedModule S' q'.primeCompl (TensorProduct.mk S' Sq' M 1)
  have : Module.Flat Rp N := (Module.flat_iff_of_isLocalization Rp p.primeCompl N).mpr this
  have hfib : Module.Flat (Sq ⧸ (maximalIdeal Rp).map (algebraMap Rp Sq))
      (N ⧸ ((maximalIdeal Rp).map (algebraMap Rp Sq) • (⊤ : Submodule Sq N))) := by
    have hK : (maximalIdeal Rp).map (algebraMap Rp Sq) =
        (p.map (algebraMap R S)).map (algebraMap S Sq) := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_map,
        ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
    rw [hK]
    exact Module.Flat.localization_quotient_smul_top (p.map (algebraMap R S)) q.primeCompl Sq
      q'.primeCompl Sq' (TensorProduct.mk S' Sq' M 1)
  have hS' : (algebraMap Rp Sq').EssentiallyOfFinitePresentation := by
    let : Algebra S' (Rp ⊗[R] S') := Algebra.TensorProduct.rightAlgebra
    have : IsLocalization (Algebra.algebraMapSubmonoid S' p.primeCompl) (Rp ⊗[R] S') :=
      IsLocalization.tensorRight Rp p.primeCompl
    let φ : Rp ⊗[R] S' →ₐ[Rp] Sq' := Algebra.TensorProduct.lift (Algebra.ofId Rp Sq')
      (IsScalarTower.toAlgHom R S' Sq') fun _ _ => Commute.all _ _
    let : Algebra (Rp ⊗[R] S') Sq' := φ.toRingHom.toAlgebra
    have : IsScalarTower S' (Rp ⊗[R] S') Sq' := IsScalarTower.of_algebraMap_eq fun s => by
      show _ = φ (1 ⊗ₜ s)
      simp [φ]
    have : IsScalarTower Rp (Rp ⊗[R] S') Sq' :=
      IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
    have hle : Algebra.algebraMapSubmonoid S' p.primeCompl ≤ q'.primeCompl := by
      rintro _ ⟨r, hr, rfl⟩; exact hr
    have := IsLocalization.isLocalization_of_submonoid_le (Rp ⊗[R] S') Sq' _ _ hle
    exact RingHom.EssentiallyOfFinitePresentation.of_isLocalization (C := Rp ⊗[R] S')
      (q'.primeCompl.map (algebraMap S' (Rp ⊗[R] S')))
  obtain ⟨hefp, hflat, hflatM⟩ :=
    Module.essentiallyOfFinitePresentation_and_flat_and_flat_of_flat_quotient_maximalIdeal
      (R := Rp) (S := Sq) (S' := Sq') (M := N) hS'
  refine ⟨Module.Flat.trans R Rp Sq, ?_, Module.Flat.trans S Sq N⟩
  rw [IsScalarTower.algebraMap_eq R Rp Sq]
  exact essFinitePresentation_comp
    (RingHom.EssentiallyOfFinitePresentation.of_isLocalization (C := R) p.primeCompl) hefp

/-- Let `M` be a finite `S'`-module over an `S`-algebra `S'` and `q` a prime of `S` with
`M ⊗_S κ(q) ≠ 0`. Then there is a prime `q'` of `S'` lying over `q` with `M_{q'} ≠ 0`. -/
theorem Ideal.exists_under_eq_and_nontrivial_localization_tensor {S S' : Type*} [CommRing S]
    [CommRing S'] [Algebra S S']
    {M : Type*} [AddCommGroup M] [Module S M] [Module S' M] [IsScalarTower S S' M]
    [Module.Finite S' M] (q : Ideal S) [q.IsPrime] [Nontrivial (M ⊗[S] q.ResidueField)] :
    ∃ (q' : Ideal S') (_ : q'.IsPrime), q'.under S = q ∧
      Nontrivial (Localization.AtPrime q' ⊗[S'] M) := by
  set a := Module.annihilator S' M
  have hfib : Nontrivial (q.ResidueField ⊗[S] (S' ⧸ a)) := by
    refine not_subsingleton_iff_nontrivial.mp fun hcon => ?_
    have : Subsingleton (M ⊗[S] q.ResidueField) := by
      refine subsingleton_of_forall_eq 0 fun x => ?_
      induction x using TensorProduct.induction_on with
      | zero => rfl
      | add x y hx hy => rw [hx, hy, add_zero]
      | tmul m k =>
        let φ : (S' ⧸ a) →ₗ[S] M :=
          (((a.restrictScalars S).liftQ ((LinearMap.toSpanSingleton S' M m).restrictScalars S)
            fun x hx => by
              simp only [LinearMap.mem_ker, LinearMap.restrictScalars_apply,
                LinearMap.toSpanSingleton_apply]
              exact Module.mem_annihilator.mp hx m)).comp
            (Submodule.Quotient.restrictScalarsEquiv S a).symm.toLinearMap
        have : m ⊗ₜ[S] k = (φ.rTensor _) (TensorProduct.comm S _ _ (k ⊗ₜ 1)) := by
          have h1 : (Submodule.Quotient.restrictScalarsEquiv S a).symm 1 =
              Submodule.Quotient.mk (1 : S') := rfl
          simp [φ, h1]
        rw [this, Subsingleton.elim (k ⊗ₜ[S] (1 : S' ⧸ a)) 0, map_zero, map_zero]
    exact not_subsingleton _ this
  obtain ⟨Q, hQ⟩ := (PrimeSpectrum.nontrivial_iff_mem_rangeComap ⟨q, inferInstance⟩).mp hfib
  have hQ' : Q.asIdeal.comap (algebraMap S (S' ⧸ a)) = q := congrArg PrimeSpectrum.asIdeal hQ
  refine ⟨Q.asIdeal.comap (Ideal.Quotient.mk a), inferInstance, ?_, ?_⟩
  · rw [← hQ', Ideal.under, Ideal.comap_comap, IsScalarTower.algebraMap_eq S S' (S' ⧸ a),
      Ideal.Quotient.algebraMap_eq]
  · have hmem : (⟨Q.asIdeal.comap (Ideal.Quotient.mk a), inferInstance⟩ : PrimeSpectrum S') ∈
        Module.support S' M :=
      Module.mem_support_iff_of_finite.mpr fun x hx => by
        show Ideal.Quotient.mk a x ∈ Q.asIdeal
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
        exact zero_mem _
    rw [Module.mem_support_iff] at hmem
    have := isLocalizedModule_mk_tensor (M := M) (Q.asIdeal.comap (Ideal.Quotient.mk a))
    exact (IsLocalizedModule.linearEquiv (Q.asIdeal.comap (Ideal.Quotient.mk a)).primeCompl
      (LocalizedModule.mkLinearMap (Q.asIdeal.comap (Ideal.Quotient.mk a)).primeCompl M)
      (TensorProduct.mk S' _ M 1)).injective.nontrivial

/-- Let `R → S → S'` be ring maps with `R → S` of finite type and `R → S'` of finite
presentation, let `I ⊆ R` be an ideal all of whose elements are nilpotent, and let `M` be a
finitely presented `S'`-module. If `M/IM` is flat over `S/IS` and `M` is flat over `R`, then `M` is
flat over `S`, and `S_q` is flat and essentially of finite presentation over `R` for every prime
`q ⊆ S` with `M ⊗_S κ(q)` nonzero. -/
@[stacks 0CEL "\"Locally nilpotent\" is `∀ x ∈ I, IsNilpotent x`. `IM` is written as `IS • ⊤`
over `S`, `S_q` is an abstract localization of `S` at `q`, and \"essentially of finite
presentation\" is `RingHom.EssentiallyOfFinitePresentation`; see the module docstring.",
  ega "IV 11.3.11" "(a) ⇒ (b), special case",
  sga "1 IV 5.9" "(ii) ⇒ (i), special case",
  sga "3 VIB 1.3.0" "special case",
  sga "3 VIB 2.5" "flatness clause"]
theorem Module.flat_and_flat_localization_of_flat_quotient_of_locallyNilpotent
    {R S S' : Type*} [CommRing R] [CommRing S] [CommRing S'] [Algebra R S] [Algebra S S']
    [Algebra R S'] [IsScalarTower R S S']
    {M : Type*} [AddCommGroup M] [Module R M] [Module S M] [Module S' M]
    [IsScalarTower R S M] [IsScalarTower S S' M]
    (I : Ideal R) (hI : ∀ x ∈ I, IsNilpotent x)
    [Algebra.FiniteType R S] [Algebra.FinitePresentation R S'] [Module.FinitePresentation S' M]
    [Module.Flat (S ⧸ I.map (algebraMap R S))
      (M ⧸ (I.map (algebraMap R S) • (⊤ : Submodule S M)))]
    [Module.Flat R M] :
    Module.Flat S M ∧
      ∀ (q : Ideal S) [q.IsPrime] (Sq : Type*) [CommRing Sq] [Algebra S Sq]
        [IsLocalization.AtPrime Sq q] [Algebra R Sq] [IsScalarTower R S Sq],
        Nontrivial (M ⊗[S] q.ResidueField) →
          Module.Flat R Sq ∧ (algebraMap R Sq).EssentiallyOfFinitePresentation := by
  have hfib : ∀ (p : Ideal R) [p.IsPrime], Module.Flat (S ⧸ p.map (algebraMap R S))
      (M ⧸ (p.map (algebraMap R S) • (⊤ : Submodule S M))) := fun p _ =>
    Module.Flat.quotient_smul_top_of_le (Ideal.map_mono fun x hx => by
      obtain ⟨n, hn⟩ := hI x hx
      exact Ideal.IsPrime.mem_of_pow_mem inferInstance n (hn ▸ zero_mem p))
  refine ⟨?_, fun q _ Sq _ _ _ _ _ hq => ?_⟩
  · have hloc : ∀ (P : Ideal S') [P.IsMaximal], IsLocalizedModule.AtPrime P
        (TensorProduct.mk S' (Localization.AtPrime P) M 1) := fun P _ =>
      isLocalizedModule_mk_tensor P
    refine Module.flat_of_isLocalized_maximal S' M
      (fun P _ => Localization.AtPrime P ⊗[S'] M) (fun P _ => TensorProduct.mk S' _ M 1)
      fun P _ => ?_
    rcases subsingleton_or_nontrivial (Localization.AtPrime P ⊗[S'] M) with h | h
    · infer_instance
    · exact (flat_localization_of_flat_fibre (R := R) (S := S) (M := M) P).2.2
  · obtain ⟨q', _, rfl, _⟩ :=
      Ideal.exists_under_eq_and_nontrivial_localization_tensor (S' := S') (M := M) q
    obtain ⟨hflat, hefp, -⟩ := flat_localization_of_flat_fibre (R := R) (S := S) (M := M) q'
    let e : Localization.AtPrime (q'.under S) ≃ₐ[S] Sq :=
      IsLocalization.algEquiv (q'.under S).primeCompl _ _
    refine ⟨Module.Flat.of_linearEquiv (e.toLinearEquiv.restrictScalars R).symm, ?_⟩
    have : algebraMap R Sq = (e.toRingEquiv : _ →+* Sq).comp
        (algebraMap R (Localization.AtPrime (q'.under S))) := by
      ext r
      simp [IsScalarTower.algebraMap_apply R S Sq, IsScalarTower.algebraMap_apply R S
        (Localization.AtPrime (q'.under S))]
    rw [this]
    exact hefp.comp_ringEquiv e.toRingEquiv

end
