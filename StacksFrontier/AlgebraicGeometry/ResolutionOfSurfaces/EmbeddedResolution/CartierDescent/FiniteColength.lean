module

public import StacksFrontier.RingTheory.Length.SemilocalDecomposition

/-!
# A module of finite colength is the product of its localizations at its support

Let `B` be a commutative ring and let `K : Ideal B` be an ideal whose quotient `B ⧸ K` is an
Artinian ring, equivalently of finite length over `B`. Write `T` for the set of primes of `B`
containing `K`. Every element of `T` is then a *maximal* ideal of `B`, because it contracts a
prime of the Artinian ring `B ⧸ K`, and `T` is finite. This file proves that `B ⧸ K` is the
product of its localizations at the members of `T`:

`B ⧸ K ≃ ∏_{𝔭 ∈ T} (B ⧸ K)_𝔭`,

that the canonical map `B ⟶ ∏_{𝔭 ∈ T} (B ⧸ K)_𝔭` is therefore surjective — the Chinese
remainder step — and that over any base ring `A` acting through `B` the length of `B ⧸ K` is the
sum of the lengths of the factors.

The intended `B` is the standard affine blowup chart `A[𝔪/x]` of the blowup of a two-dimensional
regular local ring at its closed point and `B ⧸ K` the residual quotient of [Stacks, Tag 0AGT],
which is supported at finitely many closed points of the exceptional divisor; the sum over `T` is
then the sum of the stalk colengths appearing in the colength drop of that tag.

## Main results

* `Stacks.ResolutionOfSurfaces.CartierDescent.isMaximal_of_le` — a prime containing `K` is
  maximal.
* `Stacks.ResolutionOfSurfaces.CartierDescent.isArtinian_quotient` — `B ⧸ K` is an Artinian
  `B`-module.
* `Stacks.ResolutionOfSurfaces.CartierDescent.bijective_pi_localizedModule_quotient` — the
  canonical `B`-linear map from `B ⧸ K` to the product of its localizations at the primes
  containing `K` is bijective.
* `Stacks.ResolutionOfSurfaces.CartierDescent.surjective_pi_localizedModule_quotient` — the
  Chinese remainder step: the composite `B ⟶ B ⧸ K ⟶ ∏_{𝔭 ∈ T} (B ⧸ K)_𝔭` is surjective.
* `Stacks.ResolutionOfSurfaces.CartierDescent.length_quotient_eq_sum_length_localizedModule` —
  the length of `B ⧸ K` over a base ring `A` acting through `B` is the sum of the lengths of the
  localizations.
* `Stacks.ResolutionOfSurfaces.CartierDescent.sum_length_localizedModule_le_of_surjective` — the
  comparison consumers need: a module surjecting onto the product bounds the sum of the lengths
  of the factors taken over their own local rings.

## Implementation notes

The factors are spelled `LocalizedModule p.asIdeal.primeCompl (B ⧸ K)`, the localization of the
`B`-module `B ⧸ K` at a *prime of `B`*, rather than `Localization.AtPrime 𝔮` for the
corresponding prime `𝔮` of `B ⧸ K`. The two are canonically isomorphic, but only the first is a
`B`-module — indeed an `A`-module, for `A` acting through `B` — on the nose, and the lengths in
the main results are taken over such a base ring. This is what forces the decomposition to be
proved over `B` rather than over `B ⧸ K`: the semilocal decomposition
`Stacks.Length.nonempty_linearEquiv_pi_localizedModule` applies to a semilocal ring, and `B`
itself is not semilocal, so the local–global criterion
`bijective_of_isLocalized_maximal` is run again here over `B`, with the finite index set `T`
in place of `MaximalSpectrum B`. Only the off-diagonal vanishing is reused, through
`Stacks.Length.subsingleton_localizedModule_localizedModule`; what is new is the second case of
the criterion, at a maximal ideal `P` of `B` *not* containing `K`, where an element of `K ∖ P`
annihilates everything in sight and both sides of the map vanish.

`T` is taken as a `Finset (PrimeSpectrum B)` together with the hypothesis that it is exactly the
set of primes containing `K`, rather than constructed from `K`: the consumer knows the support of
the residual quotient explicitly and would otherwise have to transport along the identification.

## References

* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
* [Stacks Project, Tag 02M0](https://stacks.math.columbia.edu/tag/02M0)
-/

@[expose] public noncomputable section

universe u

namespace Stacks.ResolutionOfSurfaces.CartierDescent

section Auxiliary

/-- Length does not increase when the ring of scalars is enlarged along a scalar tower: every
`S`-submodule is an `R`-submodule with the same carrier. -/
private theorem length_le_length_of_tower (R S : Type*) [CommRing R] [CommRing S] [SMul R S]
    (M : Type*) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] :
    Module.length S M ≤ Module.length R M := by
  calc Module.length S M = Module.length S (⊤ : Submodule S M) := Module.length_top.symm
    _ ≤ Module.length R ((⊤ : Submodule S M).restrictScalars R) :=
        Submodule.length_le_length_restrictScalars R _
    _ = Module.length R M := by rw [Submodule.restrictScalars_top, Module.length_top]

/-- **The localization of a map whose composite with a localization map is again one is
bijective.** If `f : M ⟶ M'` and `g : N ⟶ N'` are localizations at `S` and the composite
`g ∘ F : M ⟶ N'` is also a localization at `S`, then `F` becomes bijective after localizing:
both `M'` and `N'` are then models of `M[S⁻¹]`. -/
private theorem bijective_isLocalizedModule_map {R : Type*} [CommRing R] (S : Submonoid R)
    {M M' N N' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (f : M →ₗ[R] M') [IsLocalizedModule S f] (g : N →ₗ[R] N') [IsLocalizedModule S g]
    (F : M →ₗ[R] N) (hcomp : IsLocalizedModule S (g.comp F)) :
    Function.Bijective (IsLocalizedModule.map S f g F) := by
  let := hcomp
  have key : IsLocalizedModule.map S f g F =
      (IsLocalizedModule.iso S (g.comp F)).toLinearMap.comp
        (IsLocalizedModule.iso S f).symm.toLinearMap := by
    apply IsLocalizedModule.ext S f (fun x => IsLocalizedModule.map_units (g.comp F) x)
    rw [IsLocalizedModule.map_comp]
    refine LinearMap.ext fun m => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    rw [show (IsLocalizedModule.iso S f).symm (f m) = LocalizedModule.mk m 1 from ?_]
    · rw [IsLocalizedModule.iso_apply_mk]; simp
    · rw [IsLocalizedModule.iso_symm_apply' S f (f m) m 1 (by simp)]
  rw [key, LinearMap.coe_comp]
  exact (IsLocalizedModule.iso S (g.comp F)).bijective.comp
    (IsLocalizedModule.iso S f).symm.bijective

end Auxiliary

section Quotient

variable {B : Type u} [CommRing B] (K : Ideal B)

/-- **A quotient that is an Artinian ring is an Artinian module over the base.** The `B`-submodules
of `B ⧸ K` are its ideals, because `B ⟶ B ⧸ K` is surjective. -/
theorem isArtinian_quotient [IsArtinianRing (B ⧸ K)] : IsArtinian B (B ⧸ K) :=
  isArtinian_of_surjective_algebraMap (R := B ⧸ K) (M := B ⧸ K) Ideal.Quotient.mk_surjective

/-- **A prime containing `K` is maximal when `B ⧸ K` is Artinian.** Its image in `B ⧸ K` is a
prime of an Artinian ring, hence maximal, and the contraction of a maximal ideal along the
surjection `B ⟶ B ⧸ K` is maximal. -/
theorem isMaximal_of_le [IsArtinianRing (B ⧸ K)] {p : Ideal B} [p.IsPrime] (hp : K ≤ p) :
    p.IsMaximal := by
  have hsurj : Function.Surjective (Ideal.Quotient.mk K) := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker (Ideal.Quotient.mk K) ≤ p := by rwa [Ideal.mk_ker]
  have : (p.map (Ideal.Quotient.mk K)).IsPrime := Ideal.map_isPrime_of_surjective hsurj hker
  have : (p.map (Ideal.Quotient.mk K)).IsMaximal := IsArtinianRing.isMaximal_of_isPrime _
  have hcomap : ((p.map (Ideal.Quotient.mk K)).comap (Ideal.Quotient.mk K)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective (f := Ideal.Quotient.mk K) hsurj
  rwa [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
    sup_eq_left.mpr hp] at hcomap

/-- An element of `K` annihilates `B ⧸ K`. -/
private theorem smul_quotient_eq_zero {s : B} (hs : s ∈ K) (c : B ⧸ K) : s • c = 0 := by
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
    (Ideal.Quotient.eq_zero_iff_mem (I := K)).mpr hs, zero_mul]

/-- A scalar annihilating a module annihilates every localization of it. -/
private theorem smul_localizedModule_eq_zero {M : Type*} [AddCommGroup M] [Module B M]
    (S : Submonoid B) {s : B} (hs : ∀ m : M, s • m = 0) (x : LocalizedModule S M) :
    s • x = 0 := by
  induction x using LocalizedModule.induction_on with
  | _ m u => rw [LocalizedModule.smul'_mk, hs m, LocalizedModule.zero_mk]

/-- A localization at a submonoid containing an annihilator of the module vanishes. -/
private theorem subsingleton_localizedModule {M : Type*} [AddCommGroup M] [Module B M]
    {S : Submonoid B} {s : B} (hsS : s ∈ S) (hs : ∀ m : M, s • m = 0) :
    Subsingleton (LocalizedModule S M) :=
  LocalizedModule.subsingleton_iff.mpr fun m => ⟨s, hsS, hs m⟩

variable [IsArtinianRing (B ⧸ K)] (T : Finset (PrimeSpectrum B))

/-- **A quotient of finite colength is the product of its localizations at its support.** The
canonical `B`-linear map from `B ⧸ K` to the product of its localizations at the primes of `B`
containing `K` is bijective. The criterion
`bijective_of_isLocalized_maximal` reduces this to each maximal ideal `P` of `B`. If `K ≤ P`,
then `P` is one of the primes indexed by `T`, the factor at `P` localizes to `(B ⧸ K)_P` and
every other factor vanishes by
`Stacks.Length.subsingleton_localizedModule_localizedModule`; if `K ≰ P`, an element of `K ∖ P`
annihilates `B ⧸ K` and all its localizations, so both sides vanish. -/
theorem bijective_pi_localizedModule_quotient
    (hT : ∀ p : PrimeSpectrum B, p ∈ T ↔ K ≤ p.asIdeal) :
    Function.Bijective (LinearMap.pi (fun p : T =>
      LocalizedModule.mkLinearMap (p : PrimeSpectrum B).asIdeal.primeCompl (B ⧸ K))) := by
  classical
  have hart : IsArtinian B (B ⧸ K) := isArtinian_quotient K
  apply bijective_of_isLocalized_maximal (R := B)
    (fun P _ => LocalizedModule P.primeCompl (B ⧸ K))
    (fun P _ => LocalizedModule.mkLinearMap P.primeCompl (B ⧸ K))
    (fun P _ => ∀ p : T, LocalizedModule P.primeCompl
      (LocalizedModule (p : PrimeSpectrum B).asIdeal.primeCompl (B ⧸ K)))
    (fun P _ => LinearMap.pi (fun p : T =>
      (LocalizedModule.mkLinearMap P.primeCompl
        (LocalizedModule (p : PrimeSpectrum B).asIdeal.primeCompl (B ⧸ K))).comp
          (LinearMap.proj p)))
    _
  intro P hP
  refine bijective_isLocalizedModule_map P.primeCompl _ _ _ ?_
  set F := LinearMap.pi (fun p : T =>
    LocalizedModule.mkLinearMap (p : PrimeSpectrum B).asIdeal.primeCompl (B ⧸ K)) with hF
  set g := LinearMap.pi (fun p : T =>
    (LocalizedModule.mkLinearMap P.primeCompl
      (LocalizedModule (p : PrimeSpectrum B).asIdeal.primeCompl (B ⧸ K))).comp
        (LinearMap.proj p)) with hg
  by_cases hKP : K ≤ P
  · -- `P` is one of the primes of `T`; the factor at `P` survives and the others vanish
    set w : T := ⟨⟨P, hP.isPrime⟩, (hT ⟨P, hP.isPrime⟩).mpr hKP⟩ with hw
    let mkw := LocalizedModule.mkLinearMap (w : PrimeSpectrum B).asIdeal.primeCompl (B ⧸ K)
    let mkP := LocalizedModule.mkLinearMap P.primeCompl
      (LocalizedModule (w : PrimeSpectrum B).asIdeal.primeCompl (B ⧸ K))
    have hmkP_bij : Function.Bijective mkP := by
      have hid : IsLocalizedModule P.primeCompl (LinearMap.id (R := B)
          (M := LocalizedModule (w : PrimeSpectrum B).asIdeal.primeCompl (B ⧸ K))) :=
        isLocalizedModule_id P.primeCompl _ (Localization P.primeCompl)
      have hcoe : ⇑mkP = ⇑(IsLocalizedModule.linearEquiv P.primeCompl
          (LinearMap.id (R := B)
            (M := LocalizedModule (w : PrimeSpectrum B).asIdeal.primeCompl (B ⧸ K))) mkP) := by
        funext x
        have h2 := IsLocalizedModule.linearEquiv_apply P.primeCompl
          (LinearMap.id (R := B)
            (M := LocalizedModule (w : PrimeSpectrum B).asIdeal.primeCompl (B ⧸ K))) mkP x
        simpa only [LinearMap.id_coe, id_eq] using h2.symm
      rw [hcoe]
      exact (IsLocalizedModule.linearEquiv P.primeCompl (LinearMap.id (R := B)
        (M := LocalizedModule (w : PrimeSpectrum B).asIdeal.primeCompl (B ⧸ K))) mkP).bijective
    let mkPe : LocalizedModule (w : PrimeSpectrum B).asIdeal.primeCompl (B ⧸ K) ≃ₗ[B]
        LocalizedModule P.primeCompl
          (LocalizedModule (w : PrimeSpectrum B).asIdeal.primeCompl (B ⧸ K)) :=
      LinearEquiv.ofBijective mkP hmkP_bij
    have hsub : ∀ p : T, p ≠ w → Subsingleton (LocalizedModule P.primeCompl
        (LocalizedModule (p : PrimeSpectrum B).asIdeal.primeCompl (B ⧸ K))) := by
      intro p hp
      have hpmax : ((p : PrimeSpectrum B).asIdeal).IsMaximal :=
        isMaximal_of_le K ((hT _).mp p.2)
      refine Stacks.Length.subsingleton_localizedModule_localizedModule (B ⧸ K)
        (v := ⟨(p : PrimeSpectrum B).asIdeal, hpmax⟩) (w := ⟨P, hP⟩) ?_
      intro hvw
      exact hp (Subtype.ext (PrimeSpectrum.ext (congrArg MaximalSpectrum.asIdeal hvw)))
    have hproj : Function.Bijective
        (LinearMap.proj w : (∀ p : T, LocalizedModule P.primeCompl
            (LocalizedModule (p : PrimeSpectrum B).asIdeal.primeCompl (B ⧸ K)))
          →ₗ[B] LocalizedModule P.primeCompl
            (LocalizedModule (w : PrimeSpectrum B).asIdeal.primeCompl (B ⧸ K))) := by
      refine ⟨fun y₁ y₂ hyy => funext fun p => ?_, fun z => ⟨Pi.single w z, by simp⟩⟩
      by_cases hp : p = w
      · subst hp; exact hyy
      · have := hsub p hp; exact Subsingleton.elim _ _
    let pe := LinearEquiv.ofBijective (LinearMap.proj w : (∀ p : T,
        LocalizedModule P.primeCompl
          (LocalizedModule (p : PrimeSpectrum B).asIdeal.primeCompl (B ⧸ K)))
      →ₗ[B] LocalizedModule P.primeCompl
        (LocalizedModule (w : PrimeSpectrum B).asIdeal.primeCompl (B ⧸ K))) hproj
    have hkey : g.comp F = pe.symm.toLinearMap.comp (mkPe.toLinearMap.comp mkw) := by
      refine LinearMap.ext fun m => ?_
      apply pe.injective
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply]
      change (g.comp F m) w = _
      simp only [hg, hF, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.proj_apply]
      rfl
    rw [hkey]
    exact IsLocalizedModule.of_linearEquiv P.primeCompl (mkPe.toLinearMap.comp mkw) pe.symm
  · -- an element of `K ∖ P` annihilates everything, so both sides vanish
    obtain ⟨s, hsK, hsP⟩ : ∃ s ∈ K, s ∉ P := IsConcreteLE.not_le_iff_exists.mp hKP
    have hq : ∀ c : B ⧸ K, s • c = 0 := fun c => smul_quotient_eq_zero K hsK c
    have hfac : ∀ p : T, Subsingleton (LocalizedModule P.primeCompl
        (LocalizedModule (p : PrimeSpectrum B).asIdeal.primeCompl (B ⧸ K))) := fun p =>
      subsingleton_localizedModule (S := P.primeCompl) (Ideal.mem_primeCompl_iff.mpr hsP)
        (fun x => smul_localizedModule_eq_zero _ hq x)
    have hsubs : Subsingleton (∀ p : T, LocalizedModule P.primeCompl
        (LocalizedModule (p : PrimeSpectrum B).asIdeal.primeCompl (B ⧸ K))) := inferInstance
    refine ⟨fun x => isUnit_of_subsingleton _, fun y => ⟨⟨0, 1⟩, Subsingleton.elim _ _⟩,
      fun {x₁ x₂} _ => ⟨⟨s, Ideal.mem_primeCompl_iff.mpr hsP⟩, ?_⟩⟩
    change s • x₁ = s • x₂
    rw [hq x₁, hq x₂]

/-- **The Chinese remainder step.** The composite of `B ⟶ B ⧸ K` with the canonical map to the
product of the localizations of `B ⧸ K` at the primes of `B` containing `K` is surjective. -/
theorem surjective_pi_localizedModule_quotient
    (hT : ∀ p : PrimeSpectrum B, p ∈ T ↔ K ≤ p.asIdeal) :
    Function.Surjective (fun b : B => fun p : T =>
      (LocalizedModule.mkLinearMap (p : PrimeSpectrum B).asIdeal.primeCompl (B ⧸ K))
        (Ideal.Quotient.mk K b)) := by
  intro y
  obtain ⟨c, hc⟩ := (bijective_pi_localizedModule_quotient K T hT).2 y
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
  exact ⟨b, hc⟩

end Quotient

section Length

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The length of a product indexed by a finite set `T` of primes is the sum of the lengths of the
factors. -/
private theorem length_pi_localizedModule {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (T : Finset (PrimeSpectrum B)) (M : Type u) [AddCommGroup M] [Module B M] [Module A M]
    [IsScalarTower A B M] :
    Module.length A (∀ p : T, LocalizedModule (p : PrimeSpectrum B).asIdeal.primeCompl M) =
      ∑ p ∈ T, Module.length A (LocalizedModule p.asIdeal.primeCompl M) := by
  classical
  rw [Module.length_pi_of_fintype]
  exact Finset.sum_coe_sort T (fun p => Module.length A (LocalizedModule p.asIdeal.primeCompl M))

/-- **The length of a quotient of finite colength is the sum of the lengths of its
localizations**, over any base ring `A` acting through `B`. This is the ring-theoretic form of the
sum of stalk colengths in [Stacks, Tag 0AGT], and the analogue over a non-semilocal `B` of
`Stacks.Length.length_eq_sum_length_localizedModule`. -/
theorem length_quotient_eq_sum_length_localizedModule (K : Ideal B) [IsArtinianRing (B ⧸ K)]
    (T : Finset (PrimeSpectrum B)) (hT : ∀ p : PrimeSpectrum B, p ∈ T ↔ K ≤ p.asIdeal) :
    Module.length A (B ⧸ K) =
      ∑ p ∈ T, Module.length A (LocalizedModule p.asIdeal.primeCompl (B ⧸ K)) := by
  classical
  let e := LinearEquiv.ofBijective _ (bijective_pi_localizedModule_quotient K T hT)
  rw [(e.restrictScalars A).length_eq, length_pi_localizedModule]

/-- **The comparison consumers need.** If an `A`-module `N` surjects onto the product of the
localizations of a `B`-module `M` at a finite set `T` of primes of `B`, then the sum over `T` of
the lengths of those localizations, each taken over its own local ring
`Localization.AtPrime 𝔭`, is at most the `A`-length of `N`: lengths only drop when the ring of
scalars grows, and only drop along a surjection. -/
theorem sum_length_localizedModule_le_of_surjective (T : Finset (PrimeSpectrum B))
    (M : Type u) [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    {N : Type u} [AddCommGroup N] [Module A N]
    (φ : N →ₗ[A] (∀ p : T, LocalizedModule (p : PrimeSpectrum B).asIdeal.primeCompl M))
    (hφ : Function.Surjective φ) :
    ∑ p ∈ T, Module.length (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M) ≤ Module.length A N := by
  classical
  calc ∑ p ∈ T, Module.length (Localization.AtPrime p.asIdeal)
          (LocalizedModule p.asIdeal.primeCompl M)
      ≤ ∑ p ∈ T, Module.length A (LocalizedModule p.asIdeal.primeCompl M) :=
        Finset.sum_le_sum fun p _ =>
          (length_le_length_of_tower B (Localization.AtPrime p.asIdeal) _).trans
            (length_le_length_of_tower A B _)
    _ = Module.length A
          (∀ p : T, LocalizedModule (p : PrimeSpectrum B).asIdeal.primeCompl M) := by
        rw [length_pi_localizedModule]
    _ ≤ Module.length A N := Module.length_le_of_surjective φ hφ

end Length

end Stacks.ResolutionOfSurfaces.CartierDescent

end
