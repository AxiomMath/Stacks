module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksFrontier.RingTheory.Depth.Localization
public import StacksFrontier.RingTheory.Spectrum.Prime.Integral
public import StacksFrontier.RingTheory.Depth.AlgebraMap

/-!
# Depth across a finite ring extension

Let `A → B` be a finite homomorphism of rings with `A` Noetherian, and let `M` be a finite
`B`-module. The depth of `M` localized at a prime `p` of `A` is the infimum of the depths of `M`
localized at the primes of `B` above `p`; in particular it is bounded by the depth at any single
such prime.

## Main results

* `Module.localized_maximal_contracts_to_prime`: a maximal ideal of the localization of `B` at
  the complement of `p` contracts to `p` in `A`.
* `Module.depth_eq_iInf_depth_localized_algebra`: the depth at `p` is the infimum of the depths
  at the maximal ideals of the localized extension.
* `Module.depth_localized_maximal_eq`: those depths are the depths at the corresponding primes
  of `B`.
* `Module.depth_le_depth_at_prime_over`: the depth at `p` is at most the depth at any prime of
  `B` over `p`.

## Implementation notes

The primes of `B` above `p` are indexed by `MaximalSpectrum` of the localization of `B` at the
image of the complement of `p`; this is what makes the decomposition
`Module.depth_eq_iInf_depth_isLocalized_maximal` applicable. The `A`-module structure on `M`,
together with `IsScalarTower A B M`, records restriction of scalars along the given algebra
structure.

## References

* [Stacks Project, Tag 0BJS](https://stacks.math.columbia.edu/tag/0BJS)
-/

@[expose] public section

universe u v w

namespace Module

/-- Scalar multiplication by an element of the base ring is multiplication by its image. -/
private theorem smul_eq_algebraMap
    {R S M : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
    (r : R) (x : M) : r • x = algebraMap R S r • x :=
  (IsScalarTower.algebraMap_smul S r x).symm

/-- The depth of `M` localized at a prime `p` of `A` is the infimum, over the maximal ideals of
the localization of `B` away from `p`, of the depths of the correspondingly localized module. -/
theorem depth_eq_iInf_depth_localized_algebra
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Module.Finite A B]
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [Module.Finite B M]
    (p : Ideal A) [p.IsPrime] :
    Module.depth (Localization.AtPrime p) (IsLocalRing.maximalIdeal (Localization.AtPrime p))
        (LocalizedModule p.primeCompl M) =
      ⨅ P : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid B p.primeCompl)),
        haveI : IsLocalRing (Localization.AtPrime P.asIdeal) :=
          IsLocalization.AtPrime.isLocalRing _ P.asIdeal
        Module.depth (Localization.AtPrime P.asIdeal)
          (IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal))
          (LocalizedModule P.asIdeal.primeCompl
            (LocalizedModule (Algebra.algebraMapSubmonoid B p.primeCompl) M)) := by
  classical
  let T := Algebra.algebraMapSubmonoid B p.primeCompl
  let S := Localization T
  let Rₚ := Localization.AtPrime p
  let Mₚ := LocalizedModule p.primeCompl M
  let Nₚ := LocalizedModule T M
  let : Algebra Rₚ S := inferInstance
  let : Module Rₚ Nₚ := Module.compHom Nₚ (algebraMap Rₚ S)
  let : IsScalarTower Rₚ S Nₚ := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsScalarTower A Rₚ Nₚ := IsScalarTower.of_algebraMap_smul fun a n => by
    show algebraMap Rₚ S (algebraMap A Rₚ a) • n = a • n
    rw [← IsScalarTower.algebraMap_apply A Rₚ S a, IsScalarTower.algebraMap_apply A B S a,
      IsScalarTower.algebraMap_smul S, IsScalarTower.algebraMap_smul B]
  let f : M →ₗ[B] Nₚ := LocalizedModule.mkLinearMap T M
  let fA : M →ₗ[A] Nₚ := f.restrictScalars A
  have hfA : IsLocalizedModule p.primeCompl fA := IsLocalizedModule.restrictScalars p.primeCompl f
  let e : Mₚ ≃ₗ[A] Nₚ :=
    IsLocalizedModule.linearEquiv p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M) fA
  let eₚ : Mₚ ≃ₗ[Rₚ] Nₚ :=
    e.extendScalarsOfIsLocalization p.primeCompl Rₚ
  have hdepth :
      Module.depth Rₚ (IsLocalRing.maximalIdeal Rₚ) Mₚ =
        Module.depth Rₚ (IsLocalRing.maximalIdeal Rₚ) Nₚ :=
    depth_eq_depth_of_linearEquiv _ eₚ
  let Sₘ : MaximalSpectrum S → Type _ := fun P => Localization.AtPrime P.asIdeal
  let Nₘ : MaximalSpectrum S → Type _ := fun P =>
    LocalizedModule P.asIdeal.primeCompl Nₚ
  let g : ∀ P : MaximalSpectrum S, Nₚ →ₗ[S] Nₘ P := fun P =>
    LocalizedModule.mkLinearMap P.asIdeal.primeCompl Nₚ
  exact hdepth.trans (Module.depth_eq_iInf_depth_isLocalized_maximal (R := Rₚ) (S := S) Sₘ Nₘ g)

/-- A maximal ideal of the localization of `B` at the image of the complement of `p` contracts
to `p` in `A`. -/
theorem localized_maximal_contracts_to_prime
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Module.Finite A B]
    (p : Ideal A) [p.IsPrime]
    (P : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid B p.primeCompl))) :
    (P.asIdeal.under B).comap (algebraMap A B) = p := by
  let T := Algebra.algebraMapSubmonoid B p.primeCompl
  let S := Localization T
  let Rp := Localization.AtPrime p
  let : Algebra Rp S := inferInstance
  have hmax : (P.asIdeal.comap (algebraMap Rp S)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P.asIdeal
  have hcontract : P.asIdeal.comap (algebraMap Rp S) = IsLocalRing.maximalIdeal Rp :=
    IsLocalRing.eq_maximalIdeal hmax
  ext a
  show algebraMap B S (algebraMap A B a) ∈ P.asIdeal ↔ a ∈ p
  rw [← IsScalarTower.algebraMap_apply A B S a,
    IsScalarTower.algebraMap_apply A Rp S a]
  show algebraMap A Rp a ∈ P.asIdeal.comap (algebraMap Rp S) ↔ a ∈ p
  rw [hcontract]
  show a ∈ (IsLocalRing.maximalIdeal Rp).comap (algebraMap A Rp) ↔ a ∈ p
  simpa [Ideal.under] using Iff.of_eq (congrArg (fun J : Ideal A => a ∈ J)
    (IsLocalization.AtPrime.under_maximalIdeal Rp p))

/-- Every prime of `B` contracting to `p` arises from a maximal ideal of the localization of `B`
at the image of the complement of `p`. -/
private theorem exists_maximalSpectrum_localization_over_prime
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Module.Finite A B]
    (p : Ideal A) [p.IsPrime] (Q : Ideal B) [Q.IsPrime]
    (hQ : Q.comap (algebraMap A B) = p) :
    ∃ P : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid B p.primeCompl)),
      P.asIdeal.under B = Q := by
  let T := Algebra.algebraMapSubmonoid B p.primeCompl
  let S := Localization T
  let Rp := Localization.AtPrime p
  let hdisj : Disjoint (T : Set B) Q := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ hbQ
    exact ha (hQ ▸ hbQ)
  have hQprime : Q.IsPrime := inferInstance
  let r : Ideal S := Q.map (algebraMap B S)
  have hrprime : r.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint T S Q hQprime hdisj
  have hrunder : r.under B = Q := IsLocalization.under_map_of_isPrime_disjoint
    T S hQprime hdisj
  have hrcon : r.comap (algebraMap Rp S) = IsLocalRing.maximalIdeal Rp := by
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal (Ideal.comap_isPrime _ _).ne_top
    · rw [← Localization.AtPrime.map_eq_maximalIdeal (R := A) (I := p)]
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      have hQa : algebraMap A B a ∈ Q := by
        have : a ∈ Q.comap (algebraMap A B) := by simpa [hQ] using ha
        exact Ideal.mem_comap.mp this
      show algebraMap Rp S (algebraMap A Rp a) ∈ r
      rw [← IsScalarTower.algebraMap_apply A Rp S a,
        IsScalarTower.algebraMap_apply A B S a]
      exact Ideal.mem_map_of_mem (algebraMap B S) hQa
  let : r.IsPrime := hrprime
  let : (r.comap (algebraMap Rp S)).IsMaximal := by
    rw [hrcon]
    infer_instance
  have hrmax : r.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := Rp) r (inferInstance)
  exact ⟨⟨r, hrmax⟩, hrunder⟩

/-- Localizing `M` first away from `p` and then at a maximal ideal `P` gives the same depth as
localizing `M` directly at the prime of `B` underlying `P`. -/
private theorem localizedModule_comp_of_localization
    {R S K M X Y : Type*} [CommRing R] [CommRing S] [CommRing K]
    [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]
    (T U : Submonoid R) (V : Submonoid S)
    [IsLocalization T S] [IsLocalization U K] [IsLocalization V K]
    [AddCommGroup M] [Module R M]
    [AddCommGroup X] [Module R X] [Module S X] [IsScalarTower R S X]
    [AddCommGroup Y] [Module R Y] [Module S Y] [Module K Y]
    [IsScalarTower R S Y] [IsScalarTower S K Y] [IsScalarTower R K Y]
    [SMulCommClass R K Y]
    (hTU : T ≤ U)
    (hunit : ∀ x : R, IsUnit (algebraMap R K x) ↔ x ∈ U)
    (f : M →ₗ[R] X) [IsLocalizedModule T f]
    (g : X →ₗ[S] Y) [IsLocalizedModule V g] :
    IsLocalizedModule U (g.restrictScalars R ∘ₗ f) := by
  have hclear : ∀ v : V, ∃ (b : R) (t : T),
      (v : S) * algebraMap R S t = algebraMap R S b ∧ b ∈ U := by
    intro v
    obtain ⟨⟨b, t⟩, hbt⟩ := IsLocalization.surj (R := R) T (v : S)
    have hvK : IsUnit (algebraMap S K (v : S)) :=
      IsLocalization.map_units (R := S) (M := V) K v
    have htK : IsUnit (algebraMap R K (t : R)) :=
      IsLocalization.map_units (R := R) (M := U) K ⟨t, hTU t.2⟩
    refine ⟨b, t, hbt, (hunit b).mp ?_⟩
    rw [IsScalarTower.algebraMap_apply R S K b, ← hbt, map_mul,
      ← IsScalarTower.algebraMap_apply R S K t]
    exact hvK.mul htK
  refine ⟨?_, ?_, ?_⟩
  · intro x
    show IsUnit (algebraMap R (Module.End R Y) x)
    have hxK : IsUnit (algebraMap R K x) := (hunit x).mpr x.2
    have heq : algebraMap R (Module.End R Y) x =
        (Module.toModuleEnd R Y) (algebraMap R K x) := by
      ext y
      simp only [Module.algebraMap_end_apply, Module.toModuleEnd_apply,
        DistribSMul.toLinearMap_apply]
      exact smul_eq_algebraMap (R := R) (S := K) (M := Y) x y
    rw [heq]
    exact hxK.map (Module.toModuleEnd R Y)
  · intro y
    obtain ⟨⟨x, v⟩, hv⟩ := IsLocalizedModule.surj V g y
    obtain ⟨b, t, hbt, hbU⟩ := hclear v
    obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj T f x
    refine ⟨⟨t • m, ⟨b * s, U.mul_mem hbU (hTU s.2)⟩⟩, ?_⟩
    show (b * s : R) • y = g (f (t • m))
    have hsS : algebraMap R S (s : R) • x = f m := by
      calc
        algebraMap R S (s : R) • x = (s : R) • x :=
          (smul_eq_algebraMap (R := R) (S := S) (M := X) s x).symm
        _ = f m := hs
    have hscalar : algebraMap R S (b * s) =
        (v : S) * algebraMap R S (t * s) := by
      calc
        algebraMap R S (b * s) = algebraMap R S b * algebraMap R S s := map_mul _ _ _
        _ = ((v : S) * algebraMap R S t) * algebraMap R S s := by rw [hbt]
        _ = (v : S) * algebraMap R S (t * s) := by rw [map_mul]; ac_rfl
    have hfs : f (t • m) = algebraMap R S (t : R) • f m := by
      calc
        f (t • m) = (t : R) • f m := f.map_smul _ _
        _ = algebraMap R S (t : R) • f m :=
          smul_eq_algebraMap (R := R) (S := S) (M := X) t (f m)
    calc
      (b * s : R) • y = algebraMap R S (b * s) • y :=
        smul_eq_algebraMap (R := R) (S := S) (M := Y) _ _
      _ = ((v : S) * algebraMap R S (t * s)) • y := by rw [hscalar]
      _ = (v : S) • (algebraMap R S (t * s) • y) := mul_smul _ _ _
      _ = algebraMap R S (t * s) • ((v : S) • y) :=
        smul_comm (v : S) (algebraMap R S (t * s)) y
      _ = algebraMap R S (t * s) • g x := congrArg
        (fun z : Y => algebraMap R S (t * s) • z) hv
      _ = g (algebraMap R S (t * s) • x) := by rw [map_smul]
      _ = g (algebraMap R S (t : R) • f m) := by
        rw [map_mul, mul_smul, hsS]
      _ = g (f (t • m)) := by rw [hfs]
  · intro m₁ m₂ h
    change g (f m₁) = g (f m₂) at h
    obtain ⟨v, hv⟩ := IsLocalizedModule.exists_of_eq (S := V) (f := g) h
    obtain ⟨b, t, hbt, hbU⟩ := hclear v
    have hbf : f (b • m₁) = f (b • m₂) := by
      calc
        f (b • m₁) = (b : R) • f m₁ := f.map_smul _ _
        _ = algebraMap R S b • f m₁ :=
          smul_eq_algebraMap (R := R) (S := S) (M := X) b (f m₁)
        _ = ((v : S) * algebraMap R S t) • f m₁ := by rw [hbt]
        _ = (v : S) • (algebraMap R S t • f m₁) := by rw [mul_smul]
        _ = algebraMap R S t • ((v : S) • f m₁) :=
          smul_comm (v : S) (algebraMap R S t) (f m₁)
        _ = algebraMap R S t • ((v : S) • f m₂) := congrArg
          (fun z : X => algebraMap R S t • z) hv
        _ = (v : S) • (algebraMap R S t • f m₂) :=
          (smul_comm (v : S) (algebraMap R S t) (f m₂)).symm
        _ = ((v : S) * algebraMap R S t) • f m₂ := by rw [mul_smul]
        _ = algebraMap R S b • f m₂ := by rw [← hbt]
        _ = (b : R) • f m₂ :=
          (smul_eq_algebraMap (R := R) (S := S) (M := X) b (f m₂)).symm
        _ = f (b • m₂) := (f.map_smul _ _).symm
    obtain ⟨s, hs⟩ := IsLocalizedModule.exists_of_eq (S := T) (f := f) hbf
    refine ⟨⟨s * b, U.mul_mem (hTU s.2) hbU⟩, ?_⟩
    show (s * b : R) • m₁ = (s * b : R) • m₂
    calc
      (s * b : R) • m₁ = s • (b • m₁) := (smul_smul _ _ _).symm
      _ = s • (b • m₂) := hs
      _ = (s * b : R) • m₂ := smul_smul _ _ _

/-- The depth at a maximal ideal of the localized extension equals the depth at the prime of `B`
it contracts to. -/
theorem depth_localized_maximal_eq
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Module.Finite A B]
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [Module.Finite B M]
    (p : Ideal A) [p.IsPrime]
    (P : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid B p.primeCompl))) :
    Module.depth (Localization.AtPrime P.asIdeal)
        (IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal))
        (LocalizedModule P.asIdeal.primeCompl
          (LocalizedModule (Algebra.algebraMapSubmonoid B p.primeCompl) M)) =
      Module.depth (Localization.AtPrime (P.asIdeal.under B))
        (IsLocalRing.maximalIdeal (Localization.AtPrime (P.asIdeal.under B)))
        (LocalizedModule (P.asIdeal.under B).primeCompl M) := by
  classical
  let T := Algebra.algebraMapSubmonoid B p.primeCompl
  let S := Localization T
  let Q := P.asIdeal.under B
  let U := Q.primeCompl
  let V := P.asIdeal.primeCompl
  let K₀ := Localization.AtPrime Q
  let K := Localization.AtPrime P.asIdeal
  let Nₚ := LocalizedModule T M
  let Y := LocalizedModule V Nₚ
  have hQ : Q.comap (algebraMap A B) = p :=
    localized_maximal_contracts_to_prime p P
  let eRing : K₀ ≃ₐ[B] K :=
    IsLocalization.localizationLocalizationAtPrimeIsoLocalization T P.asIdeal
  let : IsLocalization.AtPrime K Q :=
    IsLocalization.isLocalization_atPrime_localization_atPrime T P.asIdeal
  let : Algebra K₀ K := eRing.toRingEquiv.toRingHom.toAlgebra
  let : IsScalarTower B K₀ K := IsScalarTower.of_algebraMap_eq' (by
    ext b
    exact (eRing.commutes b).symm)
  let : Module K₀ Y := Module.compHom Y eRing.toRingEquiv.toRingHom
  let : IsScalarTower K₀ K Y := IsScalarTower.of_algebraMap_smul fun x y => rfl
  let : IsScalarTower B K Y := inferInstance
  let : IsScalarTower B K₀ Y := IsScalarTower.of_algebraMap_smul fun b y => by
    show eRing (algebraMap B K₀ b) • y = b • y
    rw [eRing.commutes b]
    exact (smul_eq_algebraMap (R := B) (S := K) (M := Y) b y).symm
  have hRingDepth :
      Module.depth K₀ (IsLocalRing.maximalIdeal K₀) Y =
        Module.depth K (IsLocalRing.maximalIdeal K) Y := by
    rw [Module.depth_eq_depth_map_algebraMap eRing.surjective]
    show Module.depth K
      ((IsLocalRing.maximalIdeal K₀).map eRing.toRingEquiv.toRingHom) Y = _
    have hmax : (IsLocalRing.maximalIdeal K₀).map eRing.toRingEquiv.toRingHom =
        IsLocalRing.maximalIdeal K :=
      IsLocalRing.map_ringEquiv_maximalIdeal eRing.toRingEquiv
    rw [hmax]
  let f : M →ₗ[B] Nₚ := LocalizedModule.mkLinearMap T M
  let g : Nₚ →ₗ[S] Y := LocalizedModule.mkLinearMap V Nₚ
  let hcomp : M →ₗ[B] Y := g.restrictScalars B ∘ₗ f
  have hTU : T ≤ U := by
    rintro _ ⟨a, ha, rfl⟩ hbQ
    exact ha (hQ ▸ hbQ)
  have hunit : ∀ b : B, IsUnit (algebraMap B K b) ↔ b ∈ U := by
    intro b
    rw [IsLocalization.algebraMap_isUnit_iff (M := U)]
    constructor
    · rintro ⟨s, hs, hdiv⟩ hb
      obtain ⟨c, rfl⟩ := hdiv
      exact hs (Q.mul_mem_right c hb)
    · intro hb
      exact ⟨b, hb, dvd_rfl⟩
  have hcompLoc : IsLocalizedModule U hcomp :=
    localizedModule_comp_of_localization T U V hTU hunit f g
  let : IsLocalizedModule U hcomp := hcompLoc
  let eM : LocalizedModule U M ≃ₗ[B] Y :=
    IsLocalizedModule.linearEquiv U (LocalizedModule.mkLinearMap U M) hcomp
  let eMK₀ : LocalizedModule U M ≃ₗ[K₀] Y := eM.extendScalarsOfIsLocalization U K₀
  have hModuleDepth : Module.depth K₀ (IsLocalRing.maximalIdeal K₀)
        (LocalizedModule U M) = Module.depth K₀ (IsLocalRing.maximalIdeal K₀) Y :=
    depth_eq_depth_of_linearEquiv _ eMK₀
  show Module.depth K (IsLocalRing.maximalIdeal K) Y =
      Module.depth K₀ (IsLocalRing.maximalIdeal K₀) (LocalizedModule U M)
  exact hRingDepth.symm.trans hModuleDepth.symm

/-- The depth of `M` at a prime `p` of `A` is at most its depth at any prime of `B` above `p`. -/
theorem depth_le_depth_at_prime_over
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Module.Finite A B]
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [Module.Finite B M]
    (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime]
    (hP : P.comap (algebraMap A B) = p) :
    Module.depth (Localization.AtPrime p) (IsLocalRing.maximalIdeal (Localization.AtPrime p))
        (LocalizedModule p.primeCompl M) ≤
      Module.depth (Localization.AtPrime P) (IsLocalRing.maximalIdeal (Localization.AtPrime P))
        (LocalizedModule P.primeCompl M) := by
  obtain ⟨Pm, hPm⟩ := exists_maximalSpectrum_localization_over_prime p P hP
  calc
    Module.depth (Localization.AtPrime p) (IsLocalRing.maximalIdeal (Localization.AtPrime p))
        (LocalizedModule p.primeCompl M) =
      ⨅ R : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid B p.primeCompl)),
        have : IsLocalRing (Localization.AtPrime R.asIdeal) :=
          IsLocalization.AtPrime.isLocalRing _ R.asIdeal
        Module.depth (Localization.AtPrime R.asIdeal)
          (IsLocalRing.maximalIdeal (Localization.AtPrime R.asIdeal))
          (LocalizedModule R.asIdeal.primeCompl
            (LocalizedModule (Algebra.algebraMapSubmonoid B p.primeCompl) M)) :=
      depth_eq_iInf_depth_localized_algebra p
    _ ≤ Module.depth (Localization.AtPrime Pm.asIdeal)
          (IsLocalRing.maximalIdeal (Localization.AtPrime Pm.asIdeal))
          (LocalizedModule Pm.asIdeal.primeCompl
            (LocalizedModule (Algebra.algebraMapSubmonoid B p.primeCompl) M)) := iInf_le _ Pm
    _ = Module.depth (Localization.AtPrime P)
          (IsLocalRing.maximalIdeal (Localization.AtPrime P))
          (LocalizedModule P.primeCompl M) := by
      subst P
      exact depth_localized_maximal_eq (A := A) (B := B) (M := M) p Pm

end Module
