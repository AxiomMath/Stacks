module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.GeneralizationDifferent.DedekindCase
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.DedekindComparison
public import StacksFrontier.AlgebraicGeometry.Different.DualizingModulesQuasi.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Different.DualizingModulesQuasi.AssociatedPrimes
public import StacksFrontier.AlgebraicGeometry.Discriminant.TargetLocalization
public import StacksFrontier.RingTheory.TraceElement.BaseChange
public import StacksFrontier.RingTheory.TraceElement.Independence
public import StacksFrontier.RingTheory.TraceElement.LocalizationCover
public import StacksFrontier.RingTheory.Flat.OpenFlatLocus
public import StacksFrontier.RingTheory.Rig.Flat

/-!
# Trace elements on flat localizations when the Dedekind different is defined

Let `A → B` be a finite map for which the Dedekind different is defined, and let `φ` be an
element of the relative dualizing module `ω_{B/A} = Hom_A(B, A)`.  Then the following are
equivalent:

* `φ` induces the trace of the generic fibre: `φ(b) = Trace_{L/K}(b)` in `K = Q(A)` for every
  `b ∈ B`, where `L = B ⊗_A K`;
* for every `g ∈ B` such that `B_g` is flat over `A`, the image of `φ` in `ω_{B_g/A}` is the
  trace element of the flat quasi-finite map `A → B_g`.

This is the algebraic content of [Stacks, Tag 0BWN]: the trace element `τ_{V/X}` of the flat
locus `V ⊆ Spec B` comes from the global section `φ` exactly when `φ` is the generic trace.

## Main results

* `Stacks.Discriminant.isTraceElement_locFact_iff`: the equivalence above.

## Implementation notes

Both directions are proved after the flat base change `A → K`.  Over `K` the algebra
`K ⊗_A B` is finite étale, so its trace is the trace element (Tag 0BT8), and target
localization (Tag 0BT9) carries it to the trace element of `K ⊗_A B_g`.  On the other hand the
base change of the trace element of `A → B_g` is a trace element (Tag 0BT9), and the base change
map `ω_{B_g/A} → ω_{K ⊗ B_g/K}` is injective because the associated primes of `ω_{B_g/A}` lie
over associated primes of `A` (Tag 0BVD), so that nonzerodivisors of `A` act injectively.
Uniqueness of trace elements (Tag 0BT7) then gives the first implication; for the converse the
two candidates agree on a principal cover of `K ⊗_A B` by the elements `1 ⊗ g` with `B_g` flat,
which exists because `A → B_q` is flat at every prime `q` of `B` not meeting the nonzerodivisors
of `A` (Tag 0BWL) and the flat locus is open (Tag 00RC).

## References

* [Stacks Project, Tag 0BWN](https://stacks.math.columbia.edu/tag/0BWN)
* [Stacks Project, Tag 0BT7](https://stacks.math.columbia.edu/tag/0BT7)
* [Stacks Project, Tag 0BT8](https://stacks.math.columbia.edu/tag/0BT8)
* [Stacks Project, Tag 0BT9](https://stacks.math.columbia.edu/tag/0BT9)
* [Stacks Project, Tag 0BVD](https://stacks.math.columbia.edu/tag/0BVD)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace Stacks.Discriminant

attribute [local instance] algebraDualModule

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- If `B` is of finite type over a Noetherian ring `A` and `A → B_q` is flat at a prime `q`,
then `B_g` is flat over `A` for some `g ∉ q`: the flat locus is open (Tag 00RC). -/
theorem exists_flat_away_of_flat_atPrime {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Algebra.FiniteType R S] (q : Ideal S) [q.IsPrime]
    (hq : Module.Flat R (Localization.AtPrime q)) :
    ∃ g : S, g ∉ q ∧ Module.Flat R (Localization.Away g) := by
  have hiff (Q : Ideal S) [Q.IsPrime] :
      Module.Flat R (LocalizedModule.AtPrime Q S) ↔ Module.Flat R (Localization.AtPrime Q) :=
    Module.Flat.equiv_iff ((IsLocalizedModule.linearEquiv Q.primeCompl
      (LocalizedModule.mkLinearMap Q.primeCompl S)
      (Algebra.linearMap S (Localization.AtPrime Q))).restrictScalars R)
  have hopen := Module.isOpen_setOf_flat_localizedModule_atPrime_of_isNoetherianRing
    (R := R) (S := S) (M := S)
  obtain ⟨-, ⟨g, rfl⟩, hqg, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (show (⟨q, inferInstance⟩ : PrimeSpectrum S) ∈
      {Q : PrimeSpectrum S | Module.Flat R (LocalizedModule.AtPrime Q.asIdeal S)} from
      (hiff q).mpr hq) hopen
  refine ⟨g, hqg, ?_⟩
  have h := Rig.flat_away_of_flat_atPrime (algebraMap R S) g fun Q _ hgQ => by
    have hQ := (hiff Q).mp (hsub (show (⟨Q, inferInstance⟩ : PrimeSpectrum S) ∈
      PrimeSpectrum.basicOpen g from hgQ))
    rw [← IsScalarTower.algebraMap_eq]
    exact RingHom.flat_algebraMap_iff.mpr hQ
  rw [← IsScalarTower.algebraMap_eq] at h
  exact RingHom.flat_algebraMap_iff.mp h

namespace DedekindTraceElement

variable [setup : DedekindDifferentSetup A B]
include setup

/-! ### The generic fibre `K ⊗_A B` -/

/-- The total quotient ring `K = Q(A)` of `A` is Noetherian. -/
theorem isNoetherianRing_fractionRing : IsNoetherianRing (FractionRing A) :=
  let : IsNoetherianRing A := setup.isNoetherianRing
  IsLocalization.isNoetherianRing (nonZeroDivisors A) (FractionRing A) inferInstance

/-- `K ⊗_A B` is a finite `K`-module. -/
theorem finite_tensor : Module.Finite (FractionRing A) (FractionRing A ⊗[A] B) :=
  let : Module.Finite A B := setup.finite
  Module.Finite.base_change A (FractionRing A) B

/-- `K ⊗_A B` is a flat `K`-module. -/
theorem flat_tensor : Module.Flat (FractionRing A) (FractionRing A ⊗[A] B) :=
  (fractionBaseChangeFlat_of_dedekindDifferentSetup setup).2

/-- `K ⊗_A B` is a projective `K`-module. -/
theorem projective_tensor : Module.Projective (FractionRing A) (FractionRing A ⊗[A] B) :=
  let := isNoetherianRing_fractionRing (setup := setup)
  let := finite_tensor (setup := setup)
  let := flat_tensor (setup := setup)
  let : Module.FinitePresentation (FractionRing A) (FractionRing A ⊗[A] B) :=
    Module.finitePresentation_of_finite _ _
  Module.Flat.projective_of_finitePresentation

/-- `K ⊗_A B` is a Noetherian ring. -/
theorem isNoetherianRing_tensor : IsNoetherianRing (FractionRing A ⊗[A] B) :=
  let := isNoetherianRing_fractionRing (setup := setup)
  let := finite_tensor (setup := setup)
  IsNoetherianRing.of_finite (FractionRing A) _

/-- `K ⊗_A B` is quasi-finite over `K`. -/
theorem quasiFinite_tensor : Algebra.QuasiFinite (FractionRing A) (FractionRing A ⊗[A] B) :=
  let := finite_tensor (setup := setup)
  inferInstance

/-- The trace of multiplication by `1 ⊗ b` on `K ⊗_A B` is the generic-fibre trace of `b`. -/
theorem finiteProjectiveTrace_lmul_one_tmul (b : B) :
    letI := finite_tensor (setup := setup)
    letI := projective_tensor (setup := setup)
    letI : Algebra (FractionRing A) (B ⊗[A] FractionRing A) := Algebra.TensorProduct.rightAlgebra
    finiteProjectiveTrace (FractionRing A) (FractionRing A ⊗[A] B)
        (Algebra.lmul (FractionRing A) (FractionRing A ⊗[A] B) ((1 : FractionRing A) ⊗ₜ b)) =
      setup.trace (algebraMap B (B ⊗[A] FractionRing A) b) := by
  let K := FractionRing A
  let L := B ⊗[A] K
  let M := K ⊗[A] B
  let : Module.Finite A B := setup.finite
  let : Module.Finite K M := finite_tensor (setup := setup)
  let : Module.Projective K M := projective_tensor (setup := setup)
  let : Algebra K L := Algebra.TensorProduct.rightAlgebra
  let e : M ≃ₐ[K] L := Algebra.TensorProduct.commRight A K B
  let : Module.Finite K L := Module.Finite.equiv e.toLinearEquiv
  let : Module.Projective K L := Module.Projective.of_equiv' e.toLinearEquiv
  let x : L := algebraMap B L b
  let T : L →ₗ[K] L := Algebra.lmul K L x
  have hx : e ((1 : K) ⊗ₜ[A] b) = x := by
    change Algebra.TensorProduct.commRight A K B (1 ⊗ₜ[A] b) = algebraMap B (B ⊗[A] K) b
    simp
  have hconj : e.toLinearEquiv.conj (Algebra.lmul K M ((1 : K) ⊗ₜ b)) = T := by
    apply LinearMap.ext
    intro z
    change e ((1 ⊗ₜ[A] b) * e.symm z) = x * z
    rw [map_mul, hx, AlgEquiv.apply_symm_apply]
  change _ = contractLeft K L ((dualTensorHomEquiv K L L).symm T)
  rw [← finiteProjectiveTrace_eq_contract (R := K) (P := L) T, ← hconj,
    finiteProjectiveTrace_conj_linearEquiv]

omit setup in
/-- The total quotient ring of a Noetherian ring `A` is Noetherian. -/
theorem isNoetherianRing_fractionRing' [IsNoetherianRing A] : IsNoetherianRing (FractionRing A) :=
  IsLocalization.isNoetherianRing (nonZeroDivisors A) (FractionRing A) inferInstance

attribute [local instance] DedekindDifferentSetup.isNoetherianRing DedekindDifferentSetup.finite
  isNoetherianRing_fractionRing' finite_tensor flat_tensor projective_tensor isNoetherianRing_tensor
  quasiFinite_tensor

/-- `B` is a Noetherian ring. -/
theorem isNoetherianRing_target : IsNoetherianRing B := IsNoetherianRing.of_finite A B

/-- The trace form `x ↦ Trace_{K ⊗ B/K}(x)` of the generic fibre. -/
def genericTrace : Module.Dual (FractionRing A) (FractionRing A ⊗[A] B) :=
  (finiteProjectiveTrace (FractionRing A) (FractionRing A ⊗[A] B)).comp
    (Algebra.lmul (FractionRing A) (FractionRing A ⊗[A] B)).toLinearMap

/-- A functional `ψ : Hom_A(B, A)` induces the generic trace exactly when its scalar extension
to `K` is the trace form of `K ⊗_A B`. -/
theorem baseChange_eq_genericTrace_iff (ψ : Module.Dual A B) :
    letI : Algebra (FractionRing A) (B ⊗[A] FractionRing A) := Algebra.TensorProduct.rightAlgebra
    ψ.baseChange (FractionRing A) = genericTrace ↔
      ∀ b : B, algebraMap A (FractionRing A) (ψ b) =
        setup.trace (algebraMap B (B ⊗[A] FractionRing A) b) := by
  have key (b : B) : genericTrace ((1 : FractionRing A) ⊗ₜ[A] b) =
      setup.trace (algebraMap B (B ⊗[A] FractionRing A) b) :=
    finiteProjectiveTrace_lmul_one_tmul b
  refine ⟨fun h b => by
    rw [← key, ← h, Module.Dual.baseChange_apply_tmul, Algebra.smul_def, mul_one],
    fun h => TensorProduct.AlgebraTensorModule.ext fun k b => ?_⟩
  have hk : (k ⊗ₜ[A] b : FractionRing A ⊗[A] B) = k • ((1 : FractionRing A) ⊗ₜ[A] b) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [Module.Dual.baseChange_apply_tmul, hk, map_smul, key, ← h, smul_eq_mul, Algebra.smul_def,
    mul_comm]

/-! ### The relative dualizing modules over `A` and over `K` -/

omit setup in
/-- The identification of `ω_{B/A}` for the identity factorization with `Hom_A(B, A)` sends the
pure tensor `ψ ⊗ 1` to `ψ`. -/
theorem selfFactorizationDualEquiv_tmul_one {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] (ψ : Module.Dual R S) :
    selfFactorizationDualEquiv (dualizingModule.tmul (selfFactorization R S) ψ 1) = ψ := by
  change TensorProduct.lid S (Module.Dual R S)
    ((TensorProduct.comm S (Module.Dual R S) S) (ψ ⊗ₜ (1 : S))) = ψ
  simp

omit setup in
/-- Every element of `ω_{B/A}` for the identity factorization is the pure tensor of its image in
`Hom_A(B, A)` with `1`. -/
theorem eq_tmul_selfFactorizationDualEquiv {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Finite R S] (φ : dualizingModule (selfFactorization R S)) :
    φ = dualizingModule.tmul (selfFactorization R S) (selfFactorizationDualEquiv φ) 1 :=
  selfFactorizationDualEquiv.injective
    (selfFactorizationDualEquiv_tmul_one (R := R) (S := S) _).symm

/-- The Dedekind setup read on the intermediate algebra of the identity factorization, which is
`B` itself. -/
theorem setupMiddle : DedekindDifferentSetup A (selfFactorization A B).middle := setup

attribute [local instance] setupMiddle

/-- The base change to `K` of the identity factorization of `A → B`. -/
abbrev factK : FiniteOpenFactorization.{u, u, u} (FractionRing A) (FractionRing A ⊗[A] B) :=
  FiniteOpenFactorization.baseChange (selfFactorization A B) (FractionRing A)

/-- The structure map from the intermediate algebra of `factK`, which is `K ⊗_A B`, to
`K ⊗_A B` is the identity. -/
theorem algebraMap_factK (c : FractionRing A ⊗[A] B) :
    algebraMap (factK (A := A) (B := B)).middle (FractionRing A ⊗[A] B) c = c := by
  have h : IsScalarTower.toAlgHom A B B = AlgHom.id A B := AlgHom.ext fun _ => rfl
  change (Algebra.TensorProduct.map (AlgHom.id A (FractionRing A))
    (IsScalarTower.toAlgHom A B B)) c = c
  rw [h, Algebra.TensorProduct.map_id]
  rfl

/-- Comparison of a pure tensor `f ⊗ b` for the identity factorization of `K → K ⊗ B` with the
same pure tensor for `factK`. -/
theorem dualizingModuleEquiv_self_factK_tmul
    (f : Module.Dual (FractionRing A) (FractionRing A ⊗[A] B)) (b : FractionRing A ⊗[A] B) :
    dualizingModuleEquiv (selfFactorization (FractionRing A) (FractionRing A ⊗[A] B)) factK
        (dualizingModule.tmul _ f b) = dualizingModule.tmul factK f b := by
  let H := selfFactorization (FractionRing A) (FractionRing A ⊗[A] B)
  have hH : Function.Injective (algebraMap H.middle (FractionRing A ⊗[A] B)) := fun _ _ h => h
  exact dualizingModuleEquiv_tmul H factK H hH (AlgHom.id _ H.middle) (AlgHom.id _ _)
    (fun _ => rfl) (fun c => (algebraMap_factK c).symm) f b

/-- Comparison of a pure tensor `f ⊗ b` for `factK` with the same pure tensor for the identity
factorization of `K → K ⊗_A B`. -/
theorem dualizingModuleEquiv_factK_self_tmul
    (f : Module.Dual (FractionRing A) (FractionRing A ⊗[A] B)) (b : FractionRing A ⊗[A] B) :
    dualizingModuleEquiv factK (selfFactorization (FractionRing A) (FractionRing A ⊗[A] B))
        (dualizingModule.tmul factK f b) = dualizingModule.tmul _ f b := by
  let H := selfFactorization (FractionRing A) (FractionRing A ⊗[A] B)
  have hH : Function.Injective (algebraMap H.middle (FractionRing A ⊗[A] B)) := fun _ _ h => h
  exact dualizingModuleEquiv_tmul factK H H hH (AlgHom.id _ _) (AlgHom.id _ H.middle)
    (fun c => (algebraMap_factK c).symm) (fun _ => rfl) f b

/-- The map `f ↦ f ⊗ 1` from `Hom_K(K ⊗_A B, K)` to `ω` of `factK` is injective. -/
theorem tmul_factK_one_injective {f f' : Module.Dual (FractionRing A) (FractionRing A ⊗[A] B)}
    (h : dualizingModule.tmul factK f 1 = dualizingModule.tmul factK f' 1) : f = f' := by
  have h' := congrArg (fun x => selfFactorizationDualEquiv
    (dualizingModuleEquiv factK (selfFactorization (FractionRing A) (FractionRing A ⊗[A] B)) x)) h
  simpa only [dualizingModuleEquiv_factK_self_tmul, selfFactorizationDualEquiv_tmul_one] using h'

/-- The trace element of the finite flat algebra `K ⊗_A B`, in `ω` of `factK`. -/
def traceK : dualizingModule (factK (A := A) (B := B)) :=
  dualizingModuleEquiv (selfFactorization (FractionRing A) (FractionRing A ⊗[A] B)) factK
    (finiteFlatTraceElement (FractionRing A) (FractionRing A ⊗[A] B))

/-- The trace element `traceK` is the pure tensor `genericTrace ⊗ 1`. -/
theorem traceK_eq : traceK (A := A) (B := B) =
    dualizingModule.tmul (factK (A := A) (B := B)) genericTrace 1 :=
  dualizingModuleEquiv_self_factK_tmul _ _

/-- `traceK` is a trace element of `factK`. -/
theorem isTraceElement_traceK :
    IsTraceElement.{u, u, u, u, u, u} (factK (A := A) (B := B)) traceK :=
  (isTraceElement_congr _ (factK (A := A) (B := B)) _).mp
    (isTraceElement_finiteFlatTraceElement (FractionRing A) (FractionRing A ⊗[A] B))

/-- The base change to `K` of `φ ∈ ω_{B/A}` is the trace element of `K ⊗_A B` exactly when `φ`
induces the generic trace. -/
theorem baseChange_eq_traceK_iff (φ : dualizingModule (selfFactorization A B)) :
    letI : Algebra (FractionRing A) (B ⊗[A] FractionRing A) := Algebra.TensorProduct.rightAlgebra
    dualizingModule.baseChange (selfFactorization A B) (FractionRing A) φ =
        traceK (A := A) (B := B) ↔
      ∀ b : B, algebraMap A (FractionRing A) (selfFactorizationDualEquiv φ b) =
        setup.trace (algebraMap B (B ⊗[A] FractionRing A) b) := by
  rw [← baseChange_eq_genericTrace_iff, traceK_eq]
  conv_lhs => rw [eq_tmul_selfFactorizationDualEquiv φ]
  rw [dualizingModule.baseChange_tmul]
  exact ⟨fun h => tmul_factK_one_injective h,
    fun h => congrArg (fun f => dualizingModule.tmul (factK (A := A) (B := B)) f 1) h⟩

/-! ### Injectivity of the base change to `K` -/

omit setup in
/-- A nonzerodivisor of `A` acts injectively on the relative dualizing module of a
quasi-finite algebra: the associated primes of `ω_{C/A}` lie over associated primes of `A`
(Tag 0BVD), which consist of zerodivisors. -/
theorem eq_zero_of_algebraMap_smul_eq_zero {C : Type u} [CommRing C] [Algebra A C]
    [IsNoetherianRing A] [IsNoetherianRing C] (G : FiniteOpenFactorization.{u, u, u} A C)
    {a : A} (ha : a ∈ nonZeroDivisors A) {m : dualizingModule G}
    (hm : algebraMap A C a • m = 0) : m = 0 := by
  by_contra hne
  have hmem : algebraMap A C a ∈
      ⋃ p ∈ associatedPrimes C (dualizingModule G), (p : Set C) := by
    rw [biUnion_associatedPrimes_eq_zero_divisors]
    exact ⟨m, hne, hm⟩
  obtain ⟨p, hp, hap⟩ := Set.mem_iUnion₂.mp hmem
  have : p.IsPrime := hp.isPrime
  have h := (mem_associatedPrimes_dualizingModule_iff G ⟨p, this⟩).mp hp
  have ha' : a ∈ ⋃ p ∈ associatedPrimes A A, (p : Set A) :=
    Set.mem_iUnion₂.mpr ⟨_, h, hap⟩
  rw [biUnion_associatedPrimes_eq_zero_divisors] at ha'
  obtain ⟨x, hx, hax⟩ := ha'
  exact hx ((mem_nonZeroDivisors_iff_right.mp ha) x (by rw [mul_comm]; exact hax))

omit setup in
/-- The base change map `ω_{C/A} → ω_{K ⊗_A C/K}` to the total quotient ring of `A` is
injective. -/
theorem baseChange_fractionRing_injective {C : Type u} [CommRing C] [Algebra A C]
    [IsNoetherianRing A] [IsNoetherianRing C] (G : FiniteOpenFactorization.{u, u, u} A C) :
    Function.Injective (dualizingModule.baseChange G (FractionRing A)) := by
  let : Algebra C (FractionRing A ⊗[A] C) := Algebra.TensorProduct.rightAlgebra
  let : Module C (dualizingModule (FiniteOpenFactorization.baseChange G (FractionRing A))) :=
    Module.compHom _ (algebraMap C (FractionRing A ⊗[A] C))
  let : IsScalarTower C (FractionRing A ⊗[A] C)
      (dualizingModule (FiniteOpenFactorization.baseChange G (FractionRing A))) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  have : Module.Flat A (FractionRing A) := IsLocalization.flat _ (nonZeroDivisors A)
  have hb := dualizingModule_isBaseChange_of_flat G (FractionRing A)
  have hl : IsLocalizedModule (Algebra.algebraMapSubmonoid C (nonZeroDivisors A))
      (dualizingModule.baseChange G (FractionRing A)) :=
    (isLocalizedModule_iff_isBaseChange _ (FractionRing A ⊗[A] C) _).mpr hb
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro m hm
  obtain ⟨⟨s, hs⟩, hsm⟩ := (IsLocalizedModule.eq_zero_iff
    (Algebra.algebraMapSubmonoid C (nonZeroDivisors A))
    (dualizingModule.baseChange G (FractionRing A))).mp hm
  obtain ⟨a, ha, rfl⟩ := hs
  exact eq_zero_of_algebraMap_smul_eq_zero G ha hsm

/-! ### Localizing the target and base change to `K` commute -/

section Localization

variable {Bg : Type u} [CommRing Bg] [Algebra B Bg] [Algebra A Bg] [IsScalarTower A B Bg]
  (g : B) [IsLocalization.Away g Bg]

omit setup in
/-- The map `K ⊗_A B → K ⊗_A B_g`. -/
@[instance_reducible]
def tensorLocAlgebra : Algebra (FractionRing A ⊗[A] B) (FractionRing A ⊗[A] Bg) :=
  (Algebra.TensorProduct.map (AlgHom.id A (FractionRing A))
    (IsScalarTower.toAlgHom A B Bg)).toRingHom.toAlgebra

attribute [local instance] tensorLocAlgebra

omit setup in
/-- The map `K ⊗_A B → K ⊗_A B_g` sends `k ⊗ b` to `k ⊗ b`, with `b` read in `B_g`. -/
theorem algebraMap_tensorLoc_tmul (k : FractionRing A) (b : B) :
    algebraMap (FractionRing A ⊗[A] B) (FractionRing A ⊗[A] Bg) (k ⊗ₜ b) =
      k ⊗ₜ algebraMap B Bg b := by
  change (Algebra.TensorProduct.map (AlgHom.id A (FractionRing A))
    (IsScalarTower.toAlgHom A B Bg)) (k ⊗ₜ b) = _
  simp

omit setup in
/-- The map `K ⊗_A B → K ⊗_A B_g` is `K`-linear. -/
theorem isScalarTower_tensorLoc :
    IsScalarTower (FractionRing A) (FractionRing A ⊗[A] B) (FractionRing A ⊗[A] Bg) :=
  IsScalarTower.of_algebraMap_eq fun k => by
    change (k ⊗ₜ[A] (1 : Bg) : FractionRing A ⊗[A] Bg) =
      algebraMap (FractionRing A ⊗[A] B) (FractionRing A ⊗[A] Bg) (k ⊗ₜ[A] (1 : B))
    rw [algebraMap_tensorLoc_tmul, map_one]

attribute [local instance] isScalarTower_tensorLoc

omit setup in
/-- `K ⊗_A B_g` is the localization of `K ⊗_A B` away from `1 ⊗ g`. -/
theorem isLocalization_tensorLoc :
    IsLocalization.Away ((1 : FractionRing A) ⊗ₜ[A] g) (FractionRing A ⊗[A] Bg) := by
  have hincludeRight : (algebraMap (FractionRing A ⊗[A] B) (FractionRing A ⊗[A] Bg)).comp
        Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom.comp (algebraMap B Bg) := by
    ext b
    exact algebraMap_tensorLoc_tmul 1 b
  exact isLocalization_away_one_tmul hincludeRight g

attribute [local instance] isLocalization_tensorLoc

/-- The factorization of `A → B_g` obtained by localizing the identity factorization. -/
abbrev locF : FiniteOpenFactorization.{u, u, u} A Bg :=
  locFact (Bg := Bg) g (selfFactorization A B)

/-- Its base change to `K`, a factorization of `K → K ⊗_A B_g`. -/
abbrev locK : FiniteOpenFactorization.{u, u, u} (FractionRing A) (FractionRing A ⊗[A] Bg) :=
  FiniteOpenFactorization.baseChange (locF (A := A) (B := B) (Bg := Bg) g) (FractionRing A)

/-- The image of `φ ∈ ω_{B/A}` in `ω_{B_g/A}`. -/
def locElt (φ : dualizingModule (selfFactorization A B)) :
    dualizingModule (locF (A := A) (B := B) (Bg := Bg) g) :=
  dualizingTensorLocalizationEquiv (A := A) (Bg := Bg) g (selfFactorization A B)
    (targetLocalizationMap (A := A) (Bg := Bg) g (selfFactorization A B) φ)

/-- The image in `ω_{B_g/A}` of the pure tensor `ψ ⊗ b` is the pure tensor `ψ ⊗ b` for `locF`,
with `b` read in `B_g`. -/
theorem locElt_tmul (ψ : Module.Dual A B) (b : B) :
    locElt (A := A) (B := B) (Bg := Bg) g (dualizingModule.tmul (selfFactorization A B) ψ b) =
      dualizingModule.tmul (locF (A := A) (B := B) (Bg := Bg) g) ψ (algebraMap B Bg b) :=
  dualizingTensorLocalizationEquiv_tmul (A := A) (Bg := Bg) g (selfFactorization A B) ψ b

/-- The localization map `ω_{K ⊗ B/K} → (K ⊗ B_g) ⊗ ω_{K ⊗ B/K}`. -/
abbrev lamK := targetLocalizationMap (Bg := FractionRing A ⊗[A] Bg)
  ((1 : FractionRing A) ⊗ₜ[A] g) (factK (A := A) (B := B))

/-- The identification of the localized `ω_{K ⊗ B/K}` with `ω` of `locK`. -/
abbrev locKEquiv :=
  letI := isNoetherianRing_target (setup := setup)
  localizedModule_dualizingModule_equiv ((1 : FractionRing A) ⊗ₜ[A] g) (factK (A := A) (B := B))
    (locK (A := A) (B := B) (Bg := Bg) g) (lamK (A := A) (B := B) (Bg := Bg) g)
    (targetLocalizationMap_isLocalized (Bg := FractionRing A ⊗[A] Bg) _ _)

/-- Localizing at `1 ⊗ g` commutes with base change to `K`: for `φ ∈ ω_{B/A}`, the localization
at `1 ⊗ g` of the base change of `φ` to `K`, read in `ω` of `locK`, is the base change to `K`
of the image of `φ` in `ω_{B_g/A}`. -/
theorem locKEquiv_lamK_baseChange (φ : dualizingModule (selfFactorization A B)) :
    locKEquiv (A := A) (B := B) (Bg := Bg) g
        (lamK (A := A) (B := B) (Bg := Bg) g
          (dualizingModule.baseChange (selfFactorization A B) (FractionRing A) φ)) =
      dualizingModule.baseChange (locF (A := A) (B := B) (Bg := Bg) g) (FractionRing A)
        (locElt (A := A) (B := B) (Bg := Bg) g φ) := by
  induction φ using dualizingModule.induction_on with
  | add x y hx hy => simp only [map_add, locElt] at hx hy ⊢; rw [hx, hy]
  | tmul ψ b =>
    rw [locElt_tmul (setup := setup) (Bg := Bg) g ψ b]
    have hr : ∀ c : (locK (A := A) (B := B) (Bg := Bg) g).middle,
        algebraMap (FractionRing A ⊗[A] B) (FractionRing A ⊗[A] Bg)
            ((factK (A := A) (B := B)).algebraTarget.algebraMap
              ((AlgEquiv.refl :
                (locK (A := A) (B := B) (Bg := Bg) g).middle ≃ₐ[FractionRing A] _) c)) =
          (locK (A := A) (B := B) (Bg := Bg) g).algebraTarget.algebraMap c := by
      intro c
      have h1 : IsScalarTower.toAlgHom A (locF (A := A) (B := B) (Bg := Bg) g).middle Bg =
          IsScalarTower.toAlgHom A B Bg := AlgHom.ext fun _ => rfl
      change algebraMap (FractionRing A ⊗[A] B) (FractionRing A ⊗[A] Bg)
          (algebraMap (factK (A := A) (B := B)).middle (FractionRing A ⊗[A] B) c) =
        (Algebra.TensorProduct.map (AlgHom.id A (FractionRing A))
          (IsScalarTower.toAlgHom A (locF (A := A) (B := B) (Bg := Bg) g).middle Bg)) c
      refine (congrArg (algebraMap (FractionRing A ⊗[A] B) (FractionRing A ⊗[A] Bg))
        (algebraMap_factK (setup := setup) (c : FractionRing A ⊗[A] B))).trans ?_
      rw [h1]
      rfl
    have := localizedModule_dualizingModule_equiv_tmul ((1 : FractionRing A) ⊗ₜ[A] g)
      (factK (A := A) (B := B)) (locK (A := A) (B := B) (Bg := Bg) g)
      (lamK (A := A) (B := B) (Bg := Bg) g)
      (targetLocalizationMap_isLocalized (Bg := FractionRing A ⊗[A] Bg) _ _) AlgEquiv.refl hr
      (ψ.baseChange (FractionRing A)) ((1 : FractionRing A) ⊗ₜ[A] b)
    refine this.trans ?_
    rw [algebraMap_tensorLoc_tmul]
    rfl

omit [Algebra A Bg] [IsScalarTower A B Bg] in
/-- A localization of `B` away from an element `g'` is a Noetherian ring. -/
theorem isNoetherianRing_loc (g' : B) [IsLocalization.Away g' Bg] : IsNoetherianRing Bg :=
  IsLocalization.isNoetherianRing (Submonoid.powers g') Bg
    (isNoetherianRing_target (setup := setup))

/-- A localization of `B` away from an element `g'` is quasi-finite over `A`. -/
theorem quasiFinite_loc (g' : B) [IsLocalization.Away g' Bg] : Algebra.QuasiFinite A Bg :=
  let : Algebra.QuasiFinite B Bg := Algebra.QuasiFinite.of_isLocalization (Submonoid.powers g')
  Algebra.QuasiFinite.trans A B Bg

attribute [local instance] Module.finitePresentation_of_finite

/-- The base change to `K` of a trace element of `A → B_g` is the localization at `1 ⊗ g` of the
trace element of `K ⊗_A B`, read in `ω` of `locK`. -/
private theorem baseChange_eq_locKEquiv_lamK_traceK [Module.Flat A Bg]
    (ψ : dualizingModule (locF (A := A) (B := B) (Bg := Bg) g))
    (h : letI := isNoetherianRing_loc (setup := setup) (Bg := Bg) g
      letI := quasiFinite_loc (setup := setup) (Bg := Bg) g
      IsTraceElement.{u, u, u, u, u, u} (locF (A := A) (B := B) (Bg := Bg) g) ψ) :
    dualizingModule.baseChange (locF (A := A) (B := B) (Bg := Bg) g) (FractionRing A) ψ =
      locKEquiv (A := A) (B := B) (Bg := Bg) g
        (lamK (A := A) (B := B) (Bg := Bg) g (traceK (A := A) (B := B))) := by
  let := isNoetherianRing_loc (setup := setup) (Bg := Bg) g
  let := quasiFinite_loc (setup := setup) (Bg := Bg) g
  let := isNoetherianRing_target (setup := setup)
  let : Algebra.FiniteType A Bg :=
    finiteType_of_finiteOpenFactorization (locF (A := A) (B := B) (Bg := Bg) g)
  let : IsNoetherianRing (FractionRing A ⊗[A] Bg) :=
    Algebra.FiniteType.isNoetherianRing (FractionRing A) _
  let : Module.Flat (FractionRing A) (FractionRing A ⊗[A] Bg) := Module.Flat.baseChange A _ Bg
  let : Algebra.QuasiFinite (FractionRing A) (FractionRing A ⊗[A] Bg) := inferInstance
  have hb := isTraceElement_baseChange (locF (A := A) (B := B) (Bg := Bg) g) (FractionRing A) _ h
  have hl := isTraceElement_localization.{u, u, u, u, u, u, u, u, u}
    ((1 : FractionRing A) ⊗ₜ[A] g) (factK (A := A) (B := B)) (locK (A := A) (B := B) (Bg := Bg) g)
    (lamK (A := A) (B := B) (Bg := Bg) g)
    (targetLocalizationMap_isLocalized (Bg := FractionRing A ⊗[A] Bg) _ _)
    (isTraceElement_traceK (setup := setup))
  exact isTraceElement_unique (locK (A := A) (B := B) (Bg := Bg) g) hb hl

/-- **The first direction.** If the base change of `φ` to `K` is the trace element of
`K ⊗_A B`, then the image of `φ` in `ω_{B_g/A}` is a trace element whenever `B_g` is flat
over `A`. -/
theorem isTraceElement_locElt_of_baseChange_eq [Module.Flat A Bg]
    (φ : dualizingModule (selfFactorization A B))
    (h : dualizingModule.baseChange (selfFactorization A B) (FractionRing A) φ =
      traceK (A := A) (B := B)) :
    letI := isNoetherianRing_loc (setup := setup) (Bg := Bg) g
    letI := quasiFinite_loc (setup := setup) (Bg := Bg) g
    IsTraceElement.{u, u, u, u, u, u} (locF (A := A) (B := B) (Bg := Bg) g)
      (locElt (A := A) (B := B) (Bg := Bg) g φ) := by
  let := isNoetherianRing_loc (setup := setup) (Bg := Bg) g
  let := quasiFinite_loc (setup := setup) (Bg := Bg) g
  let := isNoetherianRing_target (setup := setup)
  let G := locF (A := A) (B := B) (Bg := Bg) g
  have hτ := isTraceElement_traceCandidate.{u, u, u, u, u, u} G
  have heq := baseChange_eq_locKEquiv_lamK_traceK (setup := setup) g _ hτ
  have hcomm := locKEquiv_lamK_baseChange (setup := setup) (Bg := Bg) g φ
  rw [h] at hcomm
  rw [← baseChange_fractionRing_injective G (heq.trans hcomm)]
  exact hτ

/-- **The trace elements on the two sides of the base change to `K`.** If `B_g` is flat over
`A` and the image of `φ` in `ω_{B_g/A}` is a trace element, then the localizations at `1 ⊗ g`
of the base change of `φ` and of the trace element of `K ⊗_A B` agree. -/
theorem lamK_baseChange_eq_lamK_traceK [Module.Flat A Bg]
    (φ : dualizingModule (selfFactorization A B))
    (h : letI := isNoetherianRing_loc (setup := setup) (Bg := Bg) g
      letI := quasiFinite_loc (setup := setup) (Bg := Bg) g
      IsTraceElement.{u, u, u, u, u, u} (locF (A := A) (B := B) (Bg := Bg) g)
        (locElt (A := A) (B := B) (Bg := Bg) g φ)) :
    lamK (A := A) (B := B) (Bg := Bg) g
        (dualizingModule.baseChange (selfFactorization A B) (FractionRing A) φ) =
      lamK (A := A) (B := B) (Bg := Bg) g (traceK (A := A) (B := B)) :=
  (locKEquiv (A := A) (B := B) (Bg := Bg) g).injective
    ((locKEquiv_lamK_baseChange (setup := setup) (Bg := Bg) g φ).trans
      (baseChange_eq_locKEquiv_lamK_traceK (setup := setup) g _ h))

end Localization

attribute [local instance] tensorLocAlgebra isScalarTower_tensorLoc isLocalization_tensorLoc

/-- The elements `1 ⊗ g` of `K ⊗_A B` with `B_g` flat over `A` generate the unit ideal. -/
theorem span_one_tmul_flat_eq_top :
    Ideal.span (Set.range fun g : {g : B // Module.Flat A (Localization.Away g)} =>
      ((1 : FractionRing A) ⊗ₜ[A] g.1 : FractionRing A ⊗[A] B)) = ⊤ := by
  by_contra hne
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
  let iB : B →+* FractionRing A ⊗[A] B := Algebra.TensorProduct.includeRight.toRingHom
  let q : Ideal B := P.comap iB
  have : q.IsPrime := Ideal.comap_isPrime _ _
  have hS : ∀ s : A, s ∈ nonZeroDivisors A → algebraMap A B s ∉ q := fun s hs hmem => by
    have h : iB (algebraMap A B s) =
        algebraMap (FractionRing A) (FractionRing A ⊗[A] B) (algebraMap A (FractionRing A) s) :=
      (Algebra.TensorProduct.tmul_one_eq_one_tmul _).symm
    exact hP.ne_top (Ideal.eq_top_of_isUnit_mem P hmem
      (h ▸ (IsLocalization.map_units (FractionRing A) ⟨s, hs⟩).map _))
  have hflat := flatAtPrime_of_fractionBaseChangeFlat A B (flat_tensor (setup := setup))
    ⟨q, inferInstance⟩ hS
  obtain ⟨g, hgq, hg⟩ := exists_flat_away_of_flat_atPrime q hflat
  exact hgq (hle (Ideal.subset_span ⟨⟨g, hg⟩, rfl⟩))

/-- **The second direction.** Let `B_g` be a choice of away localization for every `g ∈ B`.
If the image of `φ` in `ω_{B_g/A}` is a trace element for every `g` with `B_g` flat over `A`,
then the base change of `φ` to `K` is the trace element of `K ⊗_A B`. -/
theorem baseChange_eq_traceK_of_isTraceElement (Bg : B → Type u) [∀ g, CommRing (Bg g)]
    [∀ g, Algebra B (Bg g)] [∀ g, Algebra A (Bg g)] [∀ g, IsScalarTower A B (Bg g)]
    [∀ g, IsLocalization.Away g (Bg g)] (φ : dualizingModule (selfFactorization A B))
    (h : ∀ (g : B) [Module.Flat A (Bg g)],
      letI := isNoetherianRing_loc (setup := setup) (Bg := Bg g) g
      letI := quasiFinite_loc (setup := setup) (Bg := Bg g) g
      IsTraceElement.{u, u, u, u, u, u} (locF (A := A) (B := B) (Bg := Bg g) g)
        (locElt (A := A) (B := B) (Bg := Bg g) g φ)) :
    dualizingModule.baseChange (selfFactorization A B) (FractionRing A) φ =
      traceK (A := A) (B := B) := by
  let R := FractionRing A ⊗[A] B
  let M := dualizingModule (factK (A := A) (B := B))
  let s : Set R := Set.range fun g : {g : B // Module.Flat A (Localization.Away g)} =>
    ((1 : FractionRing A) ⊗ₜ[A] g.1 : R)
  refine Module.eq_of_isLocalized_span s (span_one_tmul_flat_eq_top (setup := setup))
    (fun r => LocalizedModule (Submonoid.powers r.1) M)
    (fun r => LocalizedModule.mkLinearMap (Submonoid.powers r.1) M) _ _ fun r => ?_
  obtain ⟨_, ⟨g, hg⟩, rfl⟩ := r
  have : Module.Flat A (Bg g) := (Module.Flat.equiv_iff
    ((IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g)
      (Bg g)).toLinearEquiv.restrictScalars A)).mp hg
  have hloc := lamK_baseChange_eq_lamK_traceK (setup := setup) (Bg := Bg g) g φ (h g)
  have : IsLocalizedModule (Submonoid.powers ((1 : FractionRing A) ⊗ₜ[A] g : R))
      (lamK (A := A) (B := B) (Bg := Bg g) g) :=
    targetLocalizationMap_isLocalized (Bg := FractionRing A ⊗[A] Bg g) _ _
  obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_iff_exists
    (Submonoid.powers ((1 : FractionRing A) ⊗ₜ[A] g : R))
    (lamK (A := A) (B := B) (Bg := Bg g) g)).mp hloc
  exact (IsLocalizedModule.eq_iff_exists (Submonoid.powers ((1 : FractionRing A) ⊗ₜ[A] g : R))
    (LocalizedModule.mkLinearMap (Submonoid.powers ((1 : FractionRing A) ⊗ₜ[A] g : R)) M)).mpr
      ⟨c, hc⟩

section Localized

variable {Bg : Type u} [CommRing Bg] [Algebra B Bg] [Algebra A Bg] [IsScalarTower A B Bg]
  (g : B) [IsLocalization.Away g Bg]

/-- The trace-element property of the image of `φ` in `ω_{B_g/A}` does not depend on how that
image is computed: through any localization map of `ω_{B/A}` and any factorization of
`A → B_g`. -/
theorem isTraceElement_localized_iff [Module.Flat A Bg] (G : FiniteOpenFactorization.{u, u, u} A Bg)
    {M : Type u} [AddCommGroup M] [Module B M] [Module Bg M] [IsScalarTower B Bg M]
    (r : dualizingModule (selfFactorization A B) →ₗ[B] M)
    (hr : IsLocalizedModule (Submonoid.powers g) r) (φ : dualizingModule (selfFactorization A B)) :
    letI := isNoetherianRing_loc (setup := setup) (Bg := Bg) g
    letI := isNoetherianRing_target (setup := setup)
    letI := quasiFinite_loc (setup := setup) (Bg := Bg) g
    IsTraceElement.{u, u, u, u, u, u} G
        (localizedModule_dualizingModule_equiv g (selfFactorization A B) G r hr (r φ)) ↔
      IsTraceElement.{u, u, u, u, u, u} (locF (A := A) (B := B) (Bg := Bg) g)
        (locElt (A := A) (B := B) (Bg := Bg) g φ) := by
  let := isNoetherianRing_loc (setup := setup) (Bg := Bg) g
  let := isNoetherianRing_target (setup := setup)
  let := quasiFinite_loc (setup := setup) (Bg := Bg) g
  rw [localizedModule_dualizingModule_equiv_apply]
  exact (isTraceElement_congr (locF (A := A) (B := B) (Bg := Bg) g) G _).symm

end Localized

end DedekindTraceElement

end Stacks.Discriminant
