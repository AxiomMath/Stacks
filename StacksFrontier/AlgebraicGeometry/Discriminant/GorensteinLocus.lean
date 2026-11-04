module

public import Mathlib.RingTheory.Artinian.Ring
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleCompleteIntersection
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleInvertibility
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleInvertibilityFree
public import StacksFrontier.AlgebraicGeometry.Discriminant.TargetLocalization
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModule0BVG
public import StacksFrontier.RingTheory.Dualizing.GorensteinFormalFibreAxioms
public import StacksFrontier.RingTheory.Dualizing.GorensteinTransport
public import StacksFrontier.RingTheory.Flat.SyzygyFreeLocus

/-!
# The Gorenstein locus of a flat quasi-finite algebra

Let `A → B` be a flat quasi-finite homomorphism of finite type of Noetherian rings, with relative
dualizing module `ω_{B/A}`. The local ring at a prime `q` of the fibre through `q` is Gorenstein
exactly when `(ω_{B/A})_q` is an invertible `B_q`-module. Consequently the set of primes of `B`
at which the fibre local ring is Gorenstein is open.

## Main results

* `Stacks.Discriminant.isGorensteinLocalRing_iff_invertible_baseChange_dual`: for a finite algebra
  `F` over a field `k` and a prime `Q` of `F`, the local ring `F_Q` is Gorenstein exactly when
  `F_Q ⊗_F Hom_k(F, k)` is an invertible `F_Q`-module.
* `Stacks.Discriminant.isGorensteinLocalRing_fiber_iff_invertible_dualizingModule`: the pointwise
  criterion in terms of `ω_{B/A}`.
* `Stacks.Discriminant.isOpen_setOf_isGorensteinLocalRing_fiber`: openness of the locus.

## References

* [Stacks Project, Tag 0BVA](https://stacks.math.columbia.edu/tag/0BVA)
* [Stacks Project, Tag 0BT2](https://stacks.math.columbia.edu/tag/0BT2)
* [Stacks Project, Tag 0BVD](https://stacks.math.columbia.edu/tag/0BVD)
* [Stacks Project, Tag 0DWK](https://stacks.math.columbia.edu/tag/0DWK)
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace Stacks.Discriminant

attribute [local instance] algebraDualModule

/-- Invertibility of a base change passes along a homomorphism of algebras. -/
theorem invertible_baseChange_of_algHom {R S T M : Type*} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T] [AddCommGroup M] [Module R M]
    (φ : S →ₐ[R] T) (h : Module.Invertible S (S ⊗[R] M)) :
    Module.Invertible T (T ⊗[R] M) := by
  let : Algebra S T := φ.toRingHom.toAlgebra
  let : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  exact Module.Invertible.congr (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T M)

/-- Invertibility is invariant under linear equivalence. -/
private theorem invertible_iff_of_linearEquiv {R M N : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    Module.Invertible R M ↔ Module.Invertible R N :=
  ⟨fun _ => Module.Invertible.congr e, fun _ => Module.Invertible.congr e.symm⟩

/-- An invertible module over a local ring is free of rank one. -/
theorem nonempty_linearEquiv_of_invertible_of_isLocalRing {R M : Type*} [CommRing R]
    [IsLocalRing R] [AddCommGroup M] [Module R M] [Module.Invertible R M] :
    Nonempty (M ≃ₗ[R] R) :=
  Module.Invertible.free_iff_linearEquiv.mp inferInstance

/-- In an artinian ring every prime `Q` is the only prime avoiding some element. -/
theorem exists_notMem_and_forall_mem_of_ne {F : Type*} [CommRing F] [IsArtinianRing F]
    (Q : Ideal F) [hQ : Q.IsPrime] :
    ∃ h : F, h ∉ Q ∧ ∀ P : Ideal F, P.IsPrime → P ≠ Q → h ∈ P := by
  classical
  have hpick (P : PrimeSpectrum F) : ∃ a : F, a ∉ Q ∧ (P.asIdeal ≠ Q → a ∈ P.asIdeal) := by
    by_cases hP : P.asIdeal = Q
    · exact ⟨1, Q.ne_top_iff_one.mp hQ.ne_top, fun h => absurd hP h⟩
    · have hle : ¬ P.asIdeal ≤ Q := fun hle =>
        hP ((IsArtinianRing.isMaximal_of_isPrime P.asIdeal).eq_of_le hQ.ne_top hle)
      obtain ⟨a, haP, haQ⟩ := Set.not_subset.mp hle
      exact ⟨a, haQ, fun _ => haP⟩
  choose a ha using hpick
  have : Fintype (PrimeSpectrum F) := Fintype.ofFinite _
  refine ⟨∏ P, a P, fun hmem => ?_, fun P hP hne => ?_⟩
  · obtain ⟨P, -, hP⟩ := (hQ.prod_mem_iff).mp hmem
    exact (ha P).1 hP
  · exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem a (Finset.mem_univ ⟨P, hP⟩))
      ((ha ⟨P, hP⟩).2 hne)

/-- **The Gorenstein criterion over a field, at a prime.** Let `F` be a finite algebra over a
field `k` and let `L` be the localization of `F` at a prime `Q`. Then `L` is Gorenstein exactly
when `L ⊗_F Hom_k(F, k)` is an invertible `L`-module. -/
theorem isGorensteinLocalRing_iff_invertible_baseChange_dual
    {k F L : Type u} [Field k] [CommRing F] [Algebra k F] [Module.Finite k F]
    [CommRing L] [Algebra F L] (Q : Ideal F) [Q.IsPrime] [IsLocalization.AtPrime L Q]
    [IsNoetherianRing L] [IsLocalRing L] :
    Dualizing.IsGorensteinLocalRing L ↔ Module.Invertible L (L ⊗[F] Module.Dual k F) := by
  have : IsArtinianRing F := IsArtinianRing.of_finite k F
  obtain ⟨h, hhQ, hh⟩ := exists_notMem_and_forall_mem_of_ne Q
  let Fh := Localization.Away h
  have : IsLocalization.AtPrime Fh Q := by
    refine IsLocalization.of_le (Submonoid.powers h) Q.primeCompl
      (Submonoid.powers_le.mpr hhQ) fun s hs => ?_
    by_contra hns
    obtain ⟨M, hM, hsM⟩ := exists_max_ideal_of_mem_nonunits hns
    have hPQ : M.comap (algebraMap F Fh) = Q := by
      by_contra hne
      exact hM.ne_top (Ideal.eq_top_of_isUnit_mem _ (hh _ (Ideal.IsPrime.comap _) hne)
        (IsLocalization.Away.algebraMap_isUnit h))
    exact hs (hPQ ▸ hsM)
  let e : L ≃ₐ[F] Fh := IsLocalization.algEquiv Q.primeCompl L Fh
  have : IsLocalRing Fh := e.toRingEquiv.isLocalRing
  have : IsNoetherianRing Fh := isNoetherianRing_of_ringEquiv L e.toRingEquiv
  have : Module.Finite k Fh :=
    Module.Finite.of_surjective (IsScalarTower.toAlgHom k F Fh).toLinearMap
      (IsArtinianRing.localization_surjective (Submonoid.powers h) Fh)
  have hG : Dualizing.IsGorensteinLocalRing L ↔ Dualizing.IsGorensteinLocalRing Fh :=
    Stacks.Duality.isGorensteinLocalRing_ringEquiv_iff e.toRingEquiv
  have hInv : Module.Invertible L (L ⊗[F] Module.Dual k F) ↔
      Module.Invertible Fh (Fh ⊗[F] Module.Dual k F) :=
    ⟨invertible_baseChange_of_algHom e.toAlgHom, invertible_baseChange_of_algHom e.symm.toAlgHom⟩
  have hRing : Dualizing.IsGorensteinLocalRing Fh ↔ Dualizing.IsGorensteinRing Fh := by
    refine ⟨fun hFh P hP => ?_, Dualizing.isGorensteinLocalRing_of_isGorensteinRing Fh⟩
    obtain rfl : P = IsLocalRing.maximalIdeal Fh :=
      IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime P)
    exact Dualizing.isGorensteinLocalRing_of_ringEquiv
      (IsLocalization.atUnits Fh (IsLocalRing.maximalIdeal Fh).primeCompl
        (S := Localization.AtPrime (IsLocalRing.maximalIdeal Fh))
        (fun x hx => (IsLocalRing.notMem_maximalIdeal.mp hx : IsUnit x))).symm.toRingEquiv hFh
  let ω := dualizingModule (selfFactorization k F)
  let e₁ : Fh ⊗[F] Module.Dual k F ≃ₗ[Fh] Fh ⊗[F] ω :=
    LinearEquiv.baseChange F Fh _ _ selfFactorizationDualEquiv.symm
  let e₂ : Fh ⊗[F] ω ≃ₗ[Fh] LocalizedModule (Submonoid.powers h) ω :=
    (LocalizedModule.isBaseChange (Submonoid.powers h) ω).equiv
  let e₃ : LocalizedModule (Submonoid.powers h) ω ≃ₗ[Fh]
      dualizingModule (selfFactorization k Fh) :=
    localizedModule_dualizingModule_equiv h (selfFactorization k F) (selfFactorization k Fh)
      (LocalizedModule.mkLinearMap _ _) inferInstance
  let eDual : Fh ⊗[F] Module.Dual k F ≃ₗ[Fh] Module.Dual k Fh :=
    e₁.trans (e₂.trans (e₃.trans selfFactorizationDualEquiv))
  have hDual : Dualizing.IsGorensteinRing Fh ↔ Module.Invertible Fh (Fh ⊗[F] Module.Dual k F) :=
    ⟨fun hFh => (invertible_iff_of_linearEquiv eDual).mpr
        (invertible_dual_of_isGorensteinRing (k := k) hFh),
      fun hFh => let := (invertible_iff_of_linearEquiv eDual).mp hFh
        isGorensteinRing_of_invertible_dual (k := k)⟩
  exact hG.trans (hRing.trans (hDual.trans hInv.symm))

/-- Two primes of the fibre `κ(𝔭) ⊗_A B` with the same contraction to `B` are equal. -/
theorem fiber_prime_eq_of_comap_eq {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] (P Q : Ideal (p.Fiber B)) [P.IsPrime] [Q.IsPrime]
    (h : P.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] p.Fiber B).toRingHom =
      Q.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] p.Fiber B).toRingHom) : P = Q := by
  have := (PrimeSpectrum.preimageEquivFiber A B ⟨p, inferInstance⟩).symm.injective
    (a₁ := ⟨P, inferInstance⟩) (a₂ := ⟨Q, inferInstance⟩) (Subtype.ext (PrimeSpectrum.ext h))
  exact congrArg PrimeSpectrum.asIdeal this

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **The Gorenstein criterion for a flat quasi-finite algebra, at a prime.** Let `A → B` be a
flat quasi-finite homomorphism of finite type of Noetherian rings with relative dualizing module
`ω_{B/A}`, let `q` be a prime of `B` over `𝔭`, and let `Q` be the corresponding prime of the
fibre `κ(𝔭) ⊗_A B`. The local ring of the fibre at `Q` is Gorenstein exactly when `(ω_{B/A})_q`
is an invertible `B_q`-module. -/
theorem isGorensteinLocalRing_fiber_iff_invertible_dualizingModule
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    [IsNoetherianRing R] [IsNoetherianRing B]
    [Algebra.FiniteType R B] [Algebra.QuasiFinite R B] [Module.Flat R B]
    (F : FiniteOpenFactorization.{u, u, u} R B) (q : Ideal B) [q.IsPrime]
    (p : Ideal R) [p.IsPrime] (Q : Ideal (p.Fiber B)) [Q.IsPrime]
    (hQ : Q.comap (Algebra.TensorProduct.includeRight : B →ₐ[R] p.Fiber B).toRingHom = q) :
    Dualizing.IsGorensteinLocalRing (Localization.AtPrime Q) ↔
      Module.Invertible (Localization.AtPrime q)
        (LocalizedModule q.primeCompl (dualizingModule F)) := by
  classical
  have hp : q.under R = p := by
    rw [← hQ, Ideal.under, Ideal.comap_comap, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]
    exact (Ideal.LiesOver.over (P := Q) (p := p)).symm
  subst hp
  let k := (q.under R).ResidueField
  let Fib := (q.under R).Fiber B
  let L := Localization.AtPrime Q
  let ω := dualizingModule F
  have : Module.Finite k Fib := Module.Finite.of_quasiFinite
  have hC := isGorensteinLocalRing_iff_invertible_baseChange_dual (k := k) (F := Fib) (L := L) Q
  let H := FiniteOpenFactorization.baseChange F k
  let eB : Fib ⊗[B] ω ≃ₗ[Fib] dualizingModule H :=
    LinearEquiv.ofBijective (dualizingModule.baseChangeLinearMap F k)
      (dualizingModule.baseChangeLinearMap_bijective F k)
  let eL : L ⊗[Fib] Module.Dual k Fib ≃ₗ[L] L ⊗[B] ω :=
    (LinearEquiv.baseChange Fib L _ _ (eB.trans ((dualizingModuleEquiv H
      (selfFactorization k Fib)).trans selfFactorizationDualEquiv)).symm).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange B Fib L L ω)
  let S := Localization.AtPrime q
  let N := LocalizedModule q.primeCompl ω
  let J := (q.under R).map (algebraMap R S)
  let T := S ⧸ J
  have : IsLocalRing T := (Ideal.localizationFiberPointRingEquiv R q).isLocalRing
  have hker : q.under R ≤ RingHom.ker (algebraMap R T) := by
    intro a ha
    change algebraMap R T a = 0
    rw [← Ideal.Quotient.mk_algebraMap R J, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ ha
  have hunits : (q.under R).primeCompl ≤
      Submonoid.comap (algebraMap R T) (IsUnit.submonoid T) := by
    intro a ha
    change IsUnit (algebraMap R T a)
    rw [IsScalarTower.algebraMap_apply R S T]
    apply IsUnit.map
    rw [IsScalarTower.algebraMap_apply R B S]
    exact IsLocalization.map_units (M := q.primeCompl) S ⟨algebraMap R B a, ha⟩
  let φ := Ideal.ResidueField.lift (q.under R) (algebraMap R T) hker hunits
  let : Algebra k T := φ.toAlgebra
  let : IsScalarTower R k T :=
    IsScalarTower.of_algebraMap_eq fun a => (Ideal.ResidueField.lift_algebraMap _ _ _ _ a).symm
  let ψ : Fib →ₐ[R] T := Algebra.TensorProduct.lift
    (IsScalarTower.toAlgHom R k T) (IsScalarTower.toAlgHom R B T)
    (fun _ _ => Commute.all _ _)
  let ψB : Fib →ₐ[B] T :=
    { ψ with
      commutes' := fun b => by
        change ψ (1 ⊗ₜ[R] b) = algebraMap B T b
        rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
        rfl }
  have hmaxT : (IsLocalRing.maximalIdeal T).comap (algebraMap B T) = q := by
    rw [IsScalarTower.algebraMap_eq B S T, ← Ideal.comap_comap]
    have : (IsLocalRing.maximalIdeal T).comap (algebraMap S T) = IsLocalRing.maximalIdeal S :=
      IsLocalRing.eq_maximalIdeal
        (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
    rw [this]
    exact Localization.AtPrime.under_maximalIdeal
  have hψunits : ∀ y : Q.primeCompl, IsUnit (ψB y) := by
    intro ⟨y, hy⟩
    by_contra hny
    have hmem : ψB y ∈ IsLocalRing.maximalIdeal T := hny
    let P := (IsLocalRing.maximalIdeal T).comap ψB.toRingHom
    have hPQ : P = Q := by
      apply fiber_prime_eq_of_comap_eq
      rw [hQ, Ideal.comap_comap]
      convert hmaxT using 2
      exact ψB.comp_algebraMap
    exact hy (hPQ ▸ hmem)
  let φ₁ : L →ₐ[B] T := IsLocalization.liftAlgHom (M := Q.primeCompl) (f := ψB) hψunits
  have hBunits : ∀ y : q.primeCompl, IsUnit ((Algebra.ofId B L) y) := by
    intro ⟨y, hy⟩
    change IsUnit (algebraMap B L y)
    rw [IsScalarTower.algebraMap_apply B Fib L]
    refine IsLocalization.map_units (M := Q.primeCompl) L ⟨algebraMap B Fib y, ?_⟩
    change algebraMap B Fib y ∉ Q
    intro hmem
    exact hy (hQ ▸ hmem)
  let σ : S →ₐ[B] L := IsLocalization.liftAlgHom (M := q.primeCompl) (f := Algebra.ofId B L)
    hBunits
  have hJ : ∀ a ∈ J, σ a = 0 := by
    intro a ha
    refine (Ideal.map_le_iff_le_comap.mpr ?_ ha : a ∈ RingHom.ker σ)
    intro r hr
    change σ (algebraMap R S r) = 0
    rw [IsScalarTower.algebraMap_apply R B S, σ.commutes,
      IsScalarTower.algebraMap_apply B Fib L]
    change algebraMap Fib L ((1 : k) ⊗ₜ[R] algebraMap R B r) = 0
    rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul,
      (Ideal.algebraMap_residueField_eq_zero).mpr hr, TensorProduct.zero_tmul, map_zero]
  let φ₂ : T →ₐ[B] L := Ideal.Quotient.liftₐ J σ hJ
  have hLT : Module.Invertible L (L ⊗[B] ω) ↔ Module.Invertible T (T ⊗[B] ω) :=
    ⟨invertible_baseChange_of_algHom φ₁, invertible_baseChange_of_algHom φ₂⟩
  let eT : T ⊗[S] N ≃ₗ[T] T ⊗[B] ω :=
    (LinearEquiv.baseChange S T _ _
        (LocalizedModule.isBaseChange q.primeCompl ω).equiv.symm).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange B S T T ω)
  have hSN : Module.Invertible T (T ⊗[S] N) ↔ Module.Invertible S N := by
    refine ⟨fun h => ?_, fun h => inferInstance⟩
    let : Module R ω := Module.compHom ω (algebraMap R B)
    have : IsScalarTower R B ω := IsScalarTower.of_compHom R B ω
    have : Module.Finite B ω := dualizingModule_finite F
    have : Module.Flat R ω := dualizingModule_flat F
    have : Module.Free S N := free_localizedModule_of_free_quotient (A := R) (M := ω) q
      (inferInstanceAs (Module.Free T (T ⊗[S] N)))
    exact Module.Invertible.congr (LinearEquiv.ofFinrankEq S N (by
      rw [Module.finrank_self, ← Module.finrank_baseChange (R := T) (S := S),
        Module.Invertible.finrank_eq_one]))
  exact hC.trans ((invertible_iff_of_linearEquiv eL).trans
    (hLT.trans ((invertible_iff_of_linearEquiv eT).symm.trans hSN)))

/-- The primes at which a finitely presented module becomes invertible form an open set. -/
theorem isOpen_setOf_invertible_localizedModule {B M : Type u} [CommRing B] [AddCommGroup M]
    [Module B M] [Module.FinitePresentation B M] :
    IsOpen {q : PrimeSpectrum B | Module.Invertible (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl M)} := by
  have hset : {q : PrimeSpectrum B | Module.Invertible (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl M)} =
      Subtype.val '' {x : Module.freeLocus B M | Module.rankAtStalk M x.1 = 1} := by
    ext q
    constructor
    · intro h
      rw [Set.mem_ofPred_eq] at h
      obtain ⟨e⟩ := nonempty_linearEquiv_of_invertible_of_isLocalRing
        (R := Localization.AtPrime q.asIdeal) (M := LocalizedModule q.asIdeal.primeCompl M)
      have : Module.Free (Localization.AtPrime q.asIdeal)
          (LocalizedModule q.asIdeal.primeCompl M) := Module.Free.of_equiv e.symm
      exact ⟨⟨q, this⟩, Module.Invertible.finrank_eq_one _ _, rfl⟩
    · rintro ⟨⟨q, hq⟩, hr, rfl⟩
      have : Module.Free (Localization.AtPrime q.asIdeal)
          (LocalizedModule q.asIdeal.primeCompl M) := hq
      exact Module.Invertible.congr (LinearEquiv.ofFinrankEq _ _
        (by rw [Module.finrank_self]; exact hr.symm))
  rw [hset]
  exact Module.isOpen_freeLocus.isOpenMap_subtype_val _
    (Module.isLocallyConstant_rankAtStalk_freeLocus.isOpen_fiber 1)

/-- **The Gorenstein locus of a flat quasi-finite algebra is open.** Let `A → B` be a flat
quasi-finite homomorphism of finite type of Noetherian rings. For every prime `q` of `B` let
`Q q` be the prime of the fibre through `q` corresponding to `q`. Then the set of `q` at which the
local ring of the fibre at `Q q` is Gorenstein is open in `Spec B`. -/
theorem isOpen_setOf_isGorensteinLocalRing_fiber
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    [IsNoetherianRing R] [IsNoetherianRing B]
    [Algebra.FiniteType R B] [Algebra.QuasiFinite R B] [Module.Flat R B]
    (p : PrimeSpectrum B → Ideal R) [∀ q, (p q).IsPrime]
    (Q : (q : PrimeSpectrum B) → Ideal ((p q).Fiber B)) [∀ q, (Q q).IsPrime]
    (hQ : ∀ q, (Q q).comap (Algebra.TensorProduct.includeRight :
      B →ₐ[R] (p q).Fiber B).toRingHom = q.asIdeal) :
    IsOpen {q : PrimeSpectrum B |
      Dualizing.IsGorensteinLocalRing (Localization.AtPrime (Q q))} := by
  obtain ⟨F⟩ := exists_finiteOpenFactorization (A := R) (B := B)
  have : Module.Finite B (dualizingModule F) := dualizingModule_finite F
  have : Module.FinitePresentation B (dualizingModule F) :=
    Module.finitePresentation_of_finite B _
  have hset : {q : PrimeSpectrum B | Dualizing.IsGorensteinLocalRing
      (Localization.AtPrime (Q q))} = {q : PrimeSpectrum B | Module.Invertible
        (Localization.AtPrime q.asIdeal) (LocalizedModule q.asIdeal.primeCompl
          (dualizingModule F))} := Set.ext fun q =>
    isGorensteinLocalRing_fiber_iff_invertible_dualizingModule F q.asIdeal (p q) (Q q) (hQ q)
  rw [hset]
  exact isOpen_setOf_invertible_localizedModule

end Stacks.Discriminant

end
