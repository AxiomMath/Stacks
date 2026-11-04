module

public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapSituation
public import StacksFrontier.Algebra.Module.RingEquivTransport
public import StacksFrontier.RingTheory.AdicCompletion.CompletionMap
public import StacksFrontier.RingTheory.Depth.SemilinearEquiv
public import StacksFrontier.RingTheory.Dualizing.Complex
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimension.ChangeOfRings
public import StacksFrontier.RingTheory.Rig.AdicCompletionMap

/-!
# Transport of a bootstrap situation along a ring isomorphism

A bootstrap situation (Stacks 0EFU) only depends on its data up to isomorphism: given a
situation over `A`, a ring isomorphism `φ : A ≃+* R'` and a `φ`-semilinear isomorphism
`M ≃ M'` onto an `R'`-module, the transported data — the ring `R'`, the ideal `I R'`, the
module `M'`, the preimage of the locus under `Spec R' → Spec A`, and the same bounds `s`, `d` —
again satisfy all four assumptions. The construction is
`Stacks.Algebraization.BootstrapSituation.congr`.

Each assumption transports for its own reason, through three pieces of general infrastructure
proved here first:

* `LocalizedModule.semilinearMap` — localization of modules is functorial in semilinear maps
  over a ring map carrying one submonoid into the other; at a ring isomorphism this gives
  `LocalizedModule.depth_atPrime_comap_eq_of_ringEquiv`, the invariance of the depth of the
  localization at a prime.
* `AdicCompletion.semilinearMap` — adic completion of modules is functorial in semilinear maps,
  linearly over `adicCompletionMap`; at a ring isomorphism this gives the ring isomorphism
  `AdicCompletion.ringEquivOfRingEquiv` and the compatible additive isomorphism
  `AdicCompletion.addEquivOfRingEquiv` of completed modules.
* the comparison of Krull dimensions of the quotients `A_q ⧸ p A_q`.

## Main definitions

* `Stacks.Algebraization.BootstrapSituation.congr` — the transported situation.

## References

* [Stacks Project, Tag 0EFU](https://stacks.math.columbia.edu/tag/0EFU)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u v w

/-! ### Localization of modules along a semilinear map -/

namespace LocalizedModule

variable {R S : Type*} [CommRing R] [CommRing S] (σ : R →+* S)
  {S₀ : Submonoid R} {S₁ : Submonoid S} (hS : S₀ ≤ S₁.comap σ)
  {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]

/-- The underlying function of `LocalizedModule.semilinearMap`: `m / s ↦ f m / σ s`. -/
def semilinearMapFun (f : M →ₛₗ[σ] N) (x : LocalizedModule S₀ M) : LocalizedModule S₁ N :=
  x.liftOn (fun p => LocalizedModule.mk (f p.1) ⟨σ p.2, hS p.2.2⟩) (by
    rintro ⟨m, s⟩ ⟨m', s'⟩ ⟨u, hu⟩
    refine LocalizedModule.mk_eq.mpr ⟨⟨σ u, hS u.2⟩, ?_⟩
    have h := congrArg f hu
    simp only [Submonoid.smul_def, map_smulₛₗ] at h
    simpa only [Submonoid.smul_def] using h)

/-- `semilinearMapFun` on a fraction. -/
@[simp]
theorem semilinearMapFun_mk (f : M →ₛₗ[σ] N) (m : M) (s : S₀) :
    semilinearMapFun σ hS f (LocalizedModule.mk m s) =
      LocalizedModule.mk (f m) ⟨σ s, hS s.2⟩ :=
  LocalizedModule.liftOn_mk _ m s

/-- **Localization is functorial in semilinear maps.** A `σ`-semilinear map `f : M → N` over a
ring map `σ : R →+* S` carrying `S₀` into `S₁` induces `m / s ↦ f m / σ s`, semilinear over the
induced map `S₀⁻¹R → S₁⁻¹S` of localizations. -/
def semilinearMap (f : M →ₛₗ[σ] N) :
    LocalizedModule S₀ M →ₛₗ[IsLocalization.map (S := Localization S₀) (Localization S₁) σ hS]
      LocalizedModule S₁ N where
  toFun := semilinearMapFun σ hS f
  map_add' x y := by
    induction x using LocalizedModule.induction_on with
    | h m s =>
    induction y using LocalizedModule.induction_on with
    | h m' s' =>
    rw [LocalizedModule.mk_add_mk, semilinearMapFun_mk, semilinearMapFun_mk,
      semilinearMapFun_mk, LocalizedModule.mk_add_mk]
    congr 1
    · simp only [Submonoid.smul_def, map_add, map_smulₛₗ]
    · ext
      simp
  map_smul' r x := by
    induction x using LocalizedModule.induction_on with
    | h m s =>
    induction r using Localization.induction_on with
    | H p =>
    obtain ⟨a, t⟩ := p
    rw [LocalizedModule.mk_smul_mk, semilinearMapFun_mk, semilinearMapFun_mk,
      Localization.mk_eq_mk', IsLocalization.map_mk', ← Localization.mk_eq_mk',
      LocalizedModule.mk_smul_mk]
    congr 1
    · simp [map_smulₛₗ]
    · ext
      simp

/-- `semilinearMap` on a fraction: `m / s ↦ f m / σ s`. -/
@[simp]
theorem semilinearMap_mk (f : M →ₛₗ[σ] N) (m : M) (s : S₀) :
    semilinearMap σ hS f (LocalizedModule.mk m s) =
      LocalizedModule.mk (f m) ⟨σ s, hS s.2⟩ :=
  semilinearMapFun_mk σ hS f m s

variable {σ} in
/-- At a ring isomorphism carrying `S₀` onto `S₁`, the localizations of two modules matched by a
semilinear additive isomorphism are matched by an additive isomorphism. -/
def addEquivOfRingEquiv (e : R ≃+* S) (he : ∀ r : R, r ∈ S₀ ↔ e r ∈ S₁)
    (f : M ≃+ N) (hf : ∀ (a : R) (m : M), f (a • m) = e a • f m) :
    LocalizedModule S₀ M ≃+ LocalizedModule S₁ N where
  toFun := semilinearMapFun (e : R →+* S)
    (show S₀ ≤ S₁.comap (e : R →+* S) from fun r hr => (he r).mp hr)
    { f with map_smul' := hf }
  invFun := semilinearMapFun (e.symm : S →+* R)
    (show S₁ ≤ S₀.comap (e.symm : S →+* R) from fun s hs => (he _).mpr (by simpa using hs))
    { f.symm with
      map_smul' := fun b n => by
        apply f.injective
        simp only [AddEquiv.toFun_eq_coe, RingHom.coe_coe, AddEquiv.apply_symm_apply, hf,
          RingEquiv.apply_symm_apply] }
  left_inv x := by
    induction x using LocalizedModule.induction_on with
    | h m s =>
    rw [semilinearMapFun_mk, semilinearMapFun_mk]
    refine LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
    simp [Submonoid.smul_def]
  right_inv x := by
    induction x using LocalizedModule.induction_on with
    | h m s =>
    rw [semilinearMapFun_mk, semilinearMapFun_mk]
    refine LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
    simp [Submonoid.smul_def]
  map_add' x y := (semilinearMap (e : R →+* S)
    (show S₀ ≤ S₁.comap (e : R →+* S) from fun r hr => (he r).mp hr)
    { f with map_smul' := hf }).map_add x y

/-- The localization of a ring at a prime `P` of an isomorphic ring `S`, read through the
isomorphism: `R_{e⁻¹P} ≃ S_P`. -/
def atPrimeRingEquiv (e : R ≃+* S) (P : Ideal S) [P.IsPrime] :
    Localization.AtPrime (P.comap (e : R →+* S)) ≃+* Localization.AtPrime P :=
  IsLocalization.ringEquivOfRingEquiv (M := (P.comap (e : R →+* S)).primeCompl)
    (T := P.primeCompl) _ _ e (by
    ext s
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact hr
    · intro hs
      refine ⟨e.symm s, ?_, e.apply_symm_apply s⟩
      change e.symm s ∉ P.comap (e : R →+* S)
      rw [Ideal.mem_comap, RingHom.coe_coe, e.apply_symm_apply]
      exact hs)

/-- `atPrimeRingEquiv` is compatible with the structure maps. -/
theorem atPrimeRingEquiv_algebraMap (e : R ≃+* S) (P : Ideal S) [P.IsPrime] (r : R) :
    atPrimeRingEquiv e P (algebraMap R _ r) = algebraMap S _ (e r) :=
  IsLocalization.ringEquivOfRingEquiv_eq _ r

/-- `atPrimeRingEquiv` is compatible with the structure maps, as ring maps. -/
theorem atPrimeRingEquiv_comp_algebraMap (e : R ≃+* S) (P : Ideal S) [P.IsPrime] :
    (atPrimeRingEquiv e P : Localization.AtPrime (P.comap (e : R →+* S)) →+*
        Localization.AtPrime P).comp (algebraMap R _) =
      (algebraMap S (Localization.AtPrime P)).comp (e : R →+* S) :=
  RingHom.ext (atPrimeRingEquiv_algebraMap e P)

/-- A semilinear additive isomorphism over a ring isomorphism `e` induces an additive isomorphism
of the localizations at a prime `P` and its preimage, semilinear over `atPrimeRingEquiv e P`. -/
private theorem exists_addEquiv_atPrime_smul (e : R ≃+* S) (f : M ≃+ N)
    (hf : ∀ (a : R) (m : M), f (a • m) = e a • f m) (P : Ideal S) [P.IsPrime] :
    ∃ g : LocalizedModule (P.comap (e : R →+* S)).primeCompl M ≃+
        LocalizedModule P.primeCompl N,
      ∀ (r : Localization.AtPrime (P.comap (e : R →+* S)))
        (x : LocalizedModule (P.comap (e : R →+* S)).primeCompl M),
        g (r • x) = atPrimeRingEquiv e P r • g x :=
  ⟨addEquivOfRingEquiv (S₀ := (P.comap (e : R →+* S)).primeCompl) (S₁ := P.primeCompl) e
    (fun _ => Iff.rfl) f hf,
    fun r x => (semilinearMap (S₀ := (P.comap (e : R →+* S)).primeCompl)
      (S₁ := P.primeCompl) (e : R →+* S) (fun _ hr => hr) { f with map_smul' := hf }).map_smulₛₗ
        r x⟩

/-- **Depth at a prime is invariant under a ring isomorphism.** For `e : R ≃+* S`, an
`e`-semilinear additive isomorphism `f : M ≃+ N` and a prime `P` of `S`, the localizations
`M_{e⁻¹P}` and `N_P` have the same depth over their local rings. -/
theorem depth_atPrime_comap_eq_of_ringEquiv (e : R ≃+* S) (f : M ≃+ N)
    (hf : ∀ (a : R) (m : M), f (a • m) = e a • f m) (P : Ideal S) [P.IsPrime] :
    Module.depth (Localization.AtPrime (P.comap (e : R →+* S)))
        (maximalIdeal (Localization.AtPrime (P.comap (e : R →+* S))))
        (LocalizedModule (P.comap (e : R →+* S)).primeCompl M) =
      Module.depth (Localization.AtPrime P) (maximalIdeal (Localization.AtPrime P))
        (LocalizedModule P.primeCompl N) := by
  obtain ⟨g, hg⟩ := exists_addEquiv_atPrime_smul e f hf P
  rw [Module.depth_eq_of_semilinearEquiv (atPrimeRingEquiv e P) _ g hg]
  congr 1
  exact IsLocalRing.map_ringEquiv_maximalIdeal _

/-- **The relative dimension `dim(S_Q ⧸ P S_Q)` is invariant under a ring isomorphism.** -/
theorem ringKrullDim_quotient_atPrime_comap_eq_of_ringEquiv (e : R ≃+* S)
    (P Q : Ideal S) [Q.IsPrime] :
    ringKrullDim (Localization.AtPrime (Q.comap (e : R →+* S)) ⧸
        (P.comap (e : R →+* S)).map
          (algebraMap R (Localization.AtPrime (Q.comap (e : R →+* S))))) =
      ringKrullDim (Localization.AtPrime Q ⧸ P.map (algebraMap S (Localization.AtPrime Q))) := by
  refine ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ (atPrimeRingEquiv e Q) ?_)
  rw [Ideal.map_map, atPrimeRingEquiv_comp_algebraMap, ← Ideal.map_map,
    Ideal.map_comap_of_surjective (e : R →+* S) e.surjective]

end LocalizedModule

/-! ### Adic completion of modules along a semilinear map -/

namespace AdicCompletion

variable {R S : Type*} [CommRing R] [CommRing S] (σ : R →+* S)
  {I : Ideal R} {J : Ideal S} (hIJ : I.map σ ≤ J)
  {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]

include hIJ in
/-- A `σ`-semilinear map carries `I ^ n M` into `J ^ n N` when `σ` carries `I` into `J`. -/
theorem pow_smul_top_le_comap (f : M →ₛₗ[σ] N) (n : ℕ) :
    (I ^ n • ⊤ : Submodule R M) ≤ (J ^ n • ⊤ : Submodule S N).comap f := by
  refine Submodule.smul_le.mpr fun r hr m _ => ?_
  rw [Submodule.mem_comap, map_smulₛₗ]
  refine Submodule.smul_mem_smul (Ideal.pow_right_mono hIJ n ?_) Submodule.mem_top
  rw [← Ideal.map_pow]
  exact Ideal.mem_map_of_mem σ hr

/-- The level-`n` reduction `M ⧸ I ^ n M → N ⧸ J ^ n N` of a semilinear map. -/
def semilinearLevelMap (f : M →ₛₗ[σ] N) (n : ℕ) :
    M ⧸ (I ^ n • ⊤ : Submodule R M) →ₛₗ[σ] N ⧸ (J ^ n • ⊤ : Submodule S N) :=
  Submodule.mapQ _ _ f (pow_smul_top_le_comap σ hIJ f n)

/-- `semilinearLevelMap` on a class. -/
@[simp]
theorem semilinearLevelMap_mk (f : M →ₛₗ[σ] N) (n : ℕ) (m : M) :
    semilinearLevelMap σ hIJ f n (Submodule.Quotient.mk m) = Submodule.Quotient.mk (f m) :=
  rfl

/-- The underlying function of `AdicCompletion.semilinearMap`, level by level. -/
def semilinearMapFun (f : M →ₛₗ[σ] N) (x : AdicCompletion I M) : AdicCompletion J N :=
  ⟨fun n => semilinearLevelMap σ hIJ f n (x.val n), fun {m n} hmn => by
    have hx := x.property hmn
    change transitionMap J N hmn (semilinearLevelMap σ hIJ f n (x.val n)) =
      semilinearLevelMap σ hIJ f m (x.val m)
    rw [← hx]
    generalize x.val n = y
    induction y using Submodule.Quotient.induction_on with
    | H y => rfl⟩

/-- The levels of `semilinearMapFun`. -/
@[simp]
theorem semilinearMapFun_val (f : M →ₛₗ[σ] N) (x : AdicCompletion I M) (n : ℕ) :
    (semilinearMapFun σ hIJ f x).val n = semilinearLevelMap σ hIJ f n (x.val n) :=
  rfl

/-- **Adic completion is functorial in semilinear maps.** A `σ`-semilinear map `f : M → N` over
a ring map carrying `I` into `J` induces a map of completions, semilinear over the induced map
`adicCompletionMap σ I J` of completed rings. -/
def semilinearMap (f : M →ₛₗ[σ] N) :
    AdicCompletion I M →ₛₗ[adicCompletionMap σ I J hIJ] AdicCompletion J N where
  toFun := semilinearMapFun σ hIJ f
  map_add' x y := by
    ext n
    simp only [semilinearMapFun_val, val_add_apply, map_add]
  map_smul' r x := by
    ext n
    simp only [semilinearMapFun_val, smul_eval]
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalₐ I n r)
    have hr : r.val n = Submodule.Quotient.mk a := val_eq_mk I n r a ha.symm
    have hr' : (adicCompletionMap σ I J hIJ r).val n = Submodule.Quotient.mk (σ a) := by
      refine val_eq_mk J n _ (σ a) ?_
      rw [adicCompletionMap_evalₐ, ← ha]
      rfl
    rw [hr, hr']
    induction x.val n using Submodule.Quotient.induction_on with
    | H y =>
      change semilinearLevelMap σ hIJ f n (Submodule.Quotient.mk (a • y)) =
        Submodule.Quotient.mk (σ a • f y)
      rw [semilinearLevelMap_mk, map_smulₛₗ]

/-- The levels of `semilinearMap` are the level reductions of the map. -/
@[simp]
theorem semilinearMap_val (f : M →ₛₗ[σ] N) (x : AdicCompletion I M) (n : ℕ) :
    (semilinearMap σ hIJ f x).val n = semilinearLevelMap σ hIJ f n (x.val n) :=
  rfl

variable {σ}

/-- The ring isomorphism of adic completions induced by a ring isomorphism carrying one ideal
onto the other. -/
def ringEquivOfRingEquiv (e : R ≃+* S) (he : I.map (e : R →+* S) = J) :
    AdicCompletion I R ≃+* AdicCompletion J S :=
  RingEquiv.ofRingHom (adicCompletionMap (e : R →+* S) I J he.le)
    (adicCompletionMap (e.symm : S →+* R) J I (by
      rw [← he, Ideal.map_map]
      simp))
    (by
      rw [Rig.adicCompletionMap_comp _ _ _ _ _ _ _ (by simp)]
      simp only [RingEquiv.comp_symm]
      exact Rig.adicCompletionMap_id J _)
    (by
      rw [Rig.adicCompletionMap_comp _ _ _ _ _ _ _ (by simp)]
      simp only [RingEquiv.symm_comp]
      exact Rig.adicCompletionMap_id I _)

/-- The underlying ring map of `ringEquivOfRingEquiv` is `adicCompletionMap`. -/
theorem ringEquivOfRingEquiv_toRingHom (e : R ≃+* S) (he : I.map (e : R →+* S) = J) :
    (ringEquivOfRingEquiv e he : AdicCompletion I R →+* AdicCompletion J S) =
      adicCompletionMap (e : R →+* S) I J he.le :=
  rfl

/-- `ringEquivOfRingEquiv` is compatible with the maps from the uncompleted rings. -/
theorem ringEquivOfRingEquiv_algebraMap (e : R ≃+* S) (he : I.map (e : R →+* S) = J) (r : R) :
    ringEquivOfRingEquiv e he (algebraMap R _ r) = algebraMap S _ (e r) :=
  RingHom.congr_fun (adicCompletionMap_comp_algebraMap (e : R →+* S) I J he.le) r

/-- The additive isomorphism of adic completions induced by a ring isomorphism carrying one
ideal onto the other and a semilinear additive isomorphism of modules over it. -/
def addEquivOfRingEquiv (e : R ≃+* S) (he : I.map (e : R →+* S) = J)
    (f : M ≃+ N) (hf : ∀ (a : R) (m : M), f (a • m) = e a • f m) :
    AdicCompletion I M ≃+ AdicCompletion J N where
  toFun := semilinearMapFun (e : R →+* S) he.le { f with map_smul' := hf }
  invFun := semilinearMapFun (e.symm : S →+* R) (by rw [← he, Ideal.map_map]; simp)
    { f.symm with
      map_smul' := fun b n => by
        apply f.injective
        simp only [AddEquiv.toFun_eq_coe, RingHom.coe_coe, AddEquiv.apply_symm_apply, hf,
          RingEquiv.apply_symm_apply] }
  left_inv x := by
    ext n
    simp only [semilinearMapFun_val]
    induction x.val n using Submodule.Quotient.induction_on with
    | H y => simp
  right_inv x := by
    ext n
    simp only [semilinearMapFun_val]
    induction x.val n using Submodule.Quotient.induction_on with
    | H y => simp
  map_add' x y := (semilinearMap (e : R →+* S) he.le { f with map_smul' := hf }).map_add x y

/-- `addEquivOfRingEquiv` is semilinear over `ringEquivOfRingEquiv`. -/
theorem addEquivOfRingEquiv_smul (e : R ≃+* S) (he : I.map (e : R →+* S) = J)
    (f : M ≃+ N) (hf : ∀ (a : R) (m : M), f (a • m) = e a • f m)
    (r : AdicCompletion I R) (x : AdicCompletion I M) :
    addEquivOfRingEquiv e he f hf (r • x) =
      ringEquivOfRingEquiv e he r • addEquivOfRingEquiv e he f hf x :=
  (semilinearMap (e : R →+* S) he.le { f with map_smul' := hf }).map_smulₛₗ r x

end AdicCompletion

/-! ### The transported bootstrap situation -/

namespace Stacks.Algebraization.BootstrapSituation

variable (B : BootstrapSituation.{u, v, w}) {R' : Type u} [CommRing R'] [IsNoetherianRing R']
  {M' : Type v} [AddCommGroup M'] [Module R' M'] (φ : B.A ≃+* R')
  (e : B.M ≃+ M') (he : ∀ (a : B.A) (m : B.M), e (a • m) = φ a • e m)

include he in
omit [IsNoetherianRing R'] in
/-- The transported module is finite. -/
theorem finite_congr : Module.Finite R' M' :=
  Module.Finite.of_semilinearEquiv φ.symm e.symm (fun b n => by
    apply e.injective
    simp [he])

/-- The transported locus: the preimage of `T` under `Spec R' → Spec A`. -/
abbrev congrLocus : Set (PrimeSpectrum R') :=
  PrimeSpectrum.comap (φ : B.A →+* R') ⁻¹' B.T

omit [IsNoetherianRing R'] in
/-- The transported locus lies in the adic locus of `I R'`. -/
theorem subset_adicLocus_congr :
    congrLocus B φ ⊆ PrimeSpectrum.zeroLocus ((B.I.map (φ : B.A →+* R')) : Set R') :=
  fun _ hp => Ideal.map_le_iff_le_comap.mpr (B.subset_adicLocus hp)

omit [IsNoetherianRing R'] in
/-- The transported locus is stable under specialization. -/
theorem stableUnderSpecialization_congr : StableUnderSpecialization (congrLocus B φ) :=
  B.stableUnderSpecialization.preimage (PrimeSpectrum.continuous_comap _)

include B φ in
/-- Assumption (1) transports: a ring isomorphic to one with a dualizing complex has one. -/
theorem dualizing_congr :
    ∃ K : DerivedCategory (ModuleCat.{max u w} R'), Dualizing.IsDualizingComplex K := by
  obtain ⟨K, hK⟩ := B.dualizing
  let : Algebra B.A R' := (φ : B.A →+* R').toAlgebra
  let T : Submonoid B.A := (IsUnit.submonoid R').map (φ.symm : R' →+* B.A)
  have : IsLocalization T R' :=
    IsLocalization.isLocalization_of_base_ringEquiv (IsUnit.submonoid R') R' φ.symm
  exact ⟨_, Dualizing.isDualizingComplex_localization (B := R') T K hK⟩

/-- Assumption (3) transports: the cohomological dimension of `I R'` is at most `d`. -/
theorem cohomologicalDimension_le_congr :
    Stacks.LocalCohomology.cohomologicalDimension R' (B.I.map (φ : B.A →+* R'))
      (Ideal.fg_of_isNoetherianRing _) ≤ B.d :=
  (Stacks.LocalCohomology.cohomologicalDimension_map_le (φ : B.A →+* R') B.I
    (Ideal.fg_of_isNoetherianRing B.I)).trans B.cohomologicalDimension_le

omit [IsNoetherianRing R'] in
/-- Pulling a prime back along a ring isomorphism and pushing the ideal forward: `I ⊆ φ⁻¹ p` iff
`I R' ⊆ p`. -/
private theorem mem_zeroLocus_comap_iff (p : PrimeSpectrum R') :
    PrimeSpectrum.comap (φ : B.A →+* R') p ∈ PrimeSpectrum.zeroLocus (B.I : Set B.A) ↔
      p ∈ PrimeSpectrum.zeroLocus ((B.I.map (φ : B.A →+* R')) : Set R') :=
  (Ideal.map_le_iff_le_comap).symm

include he in
omit [IsNoetherianRing R'] in
/-- Assumption (4) transports along the ring isomorphism. -/
theorem depth_or_depth_add_dimension_congr :
    ∀ p r q : PrimeSpectrum R',
      p.asIdeal ≤ r.asIdeal → r.asIdeal ≤ q.asIdeal →
      p ∉ PrimeSpectrum.zeroLocus ((B.I.map (φ : B.A →+* R')) : Set R') →
      r ∈ PrimeSpectrum.zeroLocus ((B.I.map (φ : B.A →+* R')) : Set R') →
      r ∉ congrLocus B φ → q ∈ congrLocus B φ →
      (enatToEInt
          (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl M')) ≥ (B.s : EInt)) ∨
      (enatToEInt
          (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl M')) +
        krullDimToEInt
          (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
            p.asIdeal.map (algebraMap R' (Localization.AtPrime q.asIdeal)))) >
        ((B.d + B.s : ℤ) : EInt)) := by
  intro p r q hpr hrq hp hr hrT hqT
  let c := PrimeSpectrum.comap (φ : B.A →+* R')
  rw [← LocalizedModule.depth_atPrime_comap_eq_of_ringEquiv φ e he p.asIdeal,
    ← LocalizedModule.ringKrullDim_quotient_atPrime_comap_eq_of_ringEquiv φ p.asIdeal q.asIdeal]
  exact B.depth_or_depth_add_dimension (c p) (c r) (c q) (Ideal.comap_mono hpr)
    (Ideal.comap_mono hrq) (fun h => hp ((mem_zeroLocus_comap_iff B φ p).mp h))
    ((mem_zeroLocus_comap_iff B φ r).mpr hr) hrT hqT

/-- Along a ring isomorphism `Ψ`, the primes above `Ψ⁻¹ p` and an ideal `a` are the pullbacks of
the primes above `p` and `Ψ a`; so if the latter are exactly `{m}`, the former are exactly
`{Ψ⁻¹ m}`. -/
private theorem setOf_prime_le_comap_eq_singleton {X Y : Type*} [CommRing X] [CommRing Y]
    (Ψ : X ≃+* Y) (p : Ideal Y) (a : Ideal X) (m : Ideal Y)
    (h : {r : Ideal Y | r.IsPrime ∧ p ≤ r ∧ a.map (Ψ : X →+* Y) ≤ r} = {m}) :
    {r : Ideal X | r.IsPrime ∧ p.comap (Ψ : X →+* Y) ≤ r ∧ a ≤ r} =
      {m.comap (Ψ : X →+* Y)} := by
  ext r
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hr, hpr, har⟩
    have hmem : r.map (Ψ : X →+* Y) ∈
        {r : Ideal Y | r.IsPrime ∧ p ≤ r ∧ a.map (Ψ : X →+* Y) ≤ r} := by
      refine ⟨Ideal.map_isPrime_of_equiv Ψ, ?_, Ideal.map_mono har⟩
      rw [← Ideal.map_comap_of_surjective (Ψ : X →+* Y) Ψ.surjective p]
      exact Ideal.map_mono hpr
    rw [h] at hmem
    rw [← Set.mem_singleton_iff.mp hmem, Ideal.comap_map_of_bijective (Ψ : X →+* Y) Ψ.bijective]
  · rintro rfl
    obtain ⟨hm, hpm, ham⟩ := (Set.ext_iff.mp h m).mpr (Set.mem_singleton m)
    exact ⟨Ideal.comap_isPrime _ _, Ideal.comap_mono hpm,
      Ideal.map_le_iff_le_comap.mp ham⟩

include he in
omit [IsNoetherianRing R'] in
/-- Assumption (6) transports along the ring isomorphism: the completed localizations, their
primes and the completed localized modules are all matched by `φ`. -/
theorem completedLocalDepth_congr :
    ∀ q : PrimeSpectrum R', q ∈ congrLocus B φ →
      let Aq := Localization.AtPrime q.asIdeal
      let Iq := (B.I.map (φ : B.A →+* R')).map (algebraMap R' Aq)
      let Mq := LocalizedModule q.asIdeal.primeCompl M'
      let A' := AdicCompletion Iq Aq
      let I' := Iq.map (algebraMap Aq A')
      let m' := (maximalIdeal Aq).map (algebraMap Aq A')
      ∀ p' : PrimeSpectrum A',
        ¬ I' ≤ p'.asIdeal →
        {r' : Ideal A' | r'.IsPrime ∧ p'.asIdeal ≤ r' ∧ I' ≤ r'} = {m'} →
        enatToEInt
          (Module.depth (Localization.AtPrime p'.asIdeal)
            (maximalIdeal (Localization.AtPrime p'.asIdeal))
            (LocalizedModule p'.asIdeal.primeCompl (AdicCompletion Iq Mq))) >
          (B.s : EInt) := by
  intro q hq
  dsimp only
  intro p' hp'I hp'set
  have h := B.completedLocalDepth (PrimeSpectrum.comap (φ : B.A →+* R') q) hq
  dsimp only at h
  let q₀ : Ideal B.A := q.asIdeal.comap (φ : B.A →+* R')
  let A₀ := Localization.AtPrime q₀
  let A₁ := Localization.AtPrime q.asIdeal
  let eq : A₀ ≃+* A₁ := LocalizedModule.atPrimeRingEquiv φ q.asIdeal
  let I₀ : Ideal A₀ := B.I.map (algebraMap B.A A₀)
  let I₁ : Ideal A₁ := (B.I.map (φ : B.A →+* R')).map (algebraMap R' A₁)
  have hI : I₀.map (eq : A₀ →+* A₁) = I₁ := by
    simp only [I₀, I₁, eq, Ideal.map_map]
    rw [LocalizedModule.atPrimeRingEquiv_comp_algebraMap]
  obtain ⟨eM, hM⟩ := LocalizedModule.exists_addEquiv_atPrime_smul φ e he q.asIdeal
  let Ψ : AdicCompletion I₀ A₀ ≃+* AdicCompletion I₁ A₁ :=
    AdicCompletion.ringEquivOfRingEquiv eq hI
  let eC := AdicCompletion.addEquivOfRingEquiv eq hI eM hM
  have hΨalg : (Ψ : AdicCompletion I₀ A₀ →+* AdicCompletion I₁ A₁).comp
      (algebraMap A₀ (AdicCompletion I₀ A₀)) =
        (algebraMap A₁ (AdicCompletion I₁ A₁)).comp (eq : A₀ →+* A₁) :=
    RingHom.ext (AdicCompletion.ringEquivOfRingEquiv_algebraMap eq hI)
  have hI' : (I₀.map (algebraMap A₀ (AdicCompletion I₀ A₀))).map
      (Ψ : AdicCompletion I₀ A₀ →+* AdicCompletion I₁ A₁) =
        I₁.map (algebraMap A₁ (AdicCompletion I₁ A₁)) := by
    rw [Ideal.map_map, hΨalg, ← Ideal.map_map, hI]
  have hm' : ((maximalIdeal A₀).map (algebraMap A₀ (AdicCompletion I₀ A₀))).map
      (Ψ : AdicCompletion I₀ A₀ →+* AdicCompletion I₁ A₁) =
        (maximalIdeal A₁).map (algebraMap A₁ (AdicCompletion I₁ A₁)) := by
    rw [Ideal.map_map, hΨalg, ← Ideal.map_map]
    congr 1
    exact IsLocalRing.map_ringEquiv_maximalIdeal eq
  have h1 : ¬ I₀.map (algebraMap A₀ (AdicCompletion I₀ A₀)) ≤
      p'.asIdeal.comap (Ψ : AdicCompletion I₀ A₀ →+* AdicCompletion I₁ A₁) :=
    fun hle => hp'I <| by
      rw [← hI']
      exact Ideal.map_le_iff_le_comap.mpr hle
  have h2 := setOf_prime_le_comap_eq_singleton Ψ p'.asIdeal
    (I₀.map (algebraMap A₀ (AdicCompletion I₀ A₀))) _ (by rwa [hI'])
  rw [← hm', Ideal.comap_map_of_bijective
    (Ψ : AdicCompletion I₀ A₀ →+* AdicCompletion I₁ A₁) Ψ.bijective] at h2
  rw [← LocalizedModule.depth_atPrime_comap_eq_of_ringEquiv Ψ eC
    (AdicCompletion.addEquivOfRingEquiv_smul eq hI eM hM) p'.asIdeal]
  exact h (PrimeSpectrum.comap (Ψ : AdicCompletion I₀ A₀ →+* AdicCompletion I₁ A₁) p') h1 h2

/-- **Transport of a bootstrap situation along a ring isomorphism.** Given a bootstrap situation
over `A` (Stacks 0EFU), a ring isomorphism `φ : A ≃+* R'` onto a Noetherian ring and a
`φ`-semilinear additive isomorphism `e : M ≃+ M'` onto an `R'`-module, the data `R'`, `I R'`,
`M'`, the preimage of `T` under `Spec R' → Spec A`, and the same bounds `s` and `d` form a
bootstrap situation. -/
def congr : BootstrapSituation.{u, v, w} :=
  letI : Module.Finite R' M' := finite_congr B φ e he
  { A := R'
    I := B.I.map (φ : B.A →+* R')
    M := M'
    T := congrLocus B φ
    subset_adicLocus := subset_adicLocus_congr B φ
    stableUnderSpecialization := stableUnderSpecialization_congr B φ
    s := B.s
    d := B.d
    dualizing := dualizing_congr B φ
    cohomologicalDimension_le := cohomologicalDimension_le_congr B φ
    depth_or_depth_add_dimension := depth_or_depth_add_dimension_congr B φ e he
    completedLocalDepth := completedLocalDepth_congr B φ e he }

/-- The `A` of the transported situation. -/
theorem congr_A : (congr B φ e he).A = R' := rfl

/-- The `I` of the transported situation. -/
theorem congr_I : (congr B φ e he).I = B.I.map (φ : B.A →+* R') := rfl

/-- The `M` of the transported situation. -/
theorem congr_M : (congr B φ e he).M = M' := rfl

/-- The `T` of the transported situation. -/
theorem congr_T :
    (congr B φ e he).T = PrimeSpectrum.comap (φ : B.A →+* R') ⁻¹' B.T := rfl

/-- The `s` of the transported situation. -/
@[simp] theorem congr_s : (congr B φ e he).s = B.s := rfl

/-- The `d` of the transported situation. -/
@[simp] theorem congr_d : (congr B φ e he).d = B.d := rfl

end Stacks.Algebraization.BootstrapSituation

end
