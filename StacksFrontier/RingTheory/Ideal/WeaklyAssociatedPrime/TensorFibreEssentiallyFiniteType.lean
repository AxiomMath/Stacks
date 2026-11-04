module

public import Mathlib.Algebra.Module.Shrink
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.RingTheory.EssentialFiniteness.Defs
public import StacksFrontier.RingTheory.Flat.SyzygyFreeLocus
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.RingEquiv
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.TensorFibreFiniteType
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.TensorFibreFormula

/-!
# Weakly associated primes of a flat tensor product over an essentially finite type algebra

Let `R → S` be a ring map essentially of finite type, let `N` be a localization of a finite
`S`-module which is flat over `R`, and let `M` be an `R`-module. This file proves, for a prime
`q` of `S` lying over `p`,

`q ∈ WeakAss_S(N ⊗_R M) ↔ (p ∈ WeakAss_R(M) and q ∈ WeakAss_S(N ⊗_R κ(p)))`,

and reads the result off as the set equality of [Stacks, Tag 05II]. The equivalence rests on
the finite type case
`Stacks.WeaklyAssociatedPrimes.isWeaklyAssociatedPrime_tensorProduct_iff_of_finiteType`, taken
here against the statement `Stacks.WeaklyAssociatedPrimes.TensorFibreFormula05IG` of
[Stacks, Tag 05IG], which `Stacks.WeaklyAssociatedPrimes.tensorFibreFormula05IG` proves.

The passage from the finite type case is the translation the source leaves out. A ring
essentially of finite type is a localization of a finite type algebra `A`, and a finite module
over it is the localization of a finite `A`-module; both sides of the equivalence are unchanged
by that localization, so the statement over `S` follows from the statement over `A`. The
flatness hypothesis is the one thing that has to be carried across: flatness over `R` of the
localization of the model at the contracted prime is `flat_localizedModule_of_finiteTypeModel`.

## Main results

* `isWeaklyAssociatedPrime_tensorProduct_iff_fibre_of_essentiallyOfFiniteType`, in
  `Stacks.WeaklyAssociatedPrimes`, is the pointwise equivalence.
* `weaklyAssociatedPrimes_tensorProduct_eq_fibrewise_assStacks_of_small`, in the same namespace,
  is the set equality of [Stacks, Tag 05II]. The module `M` lives in any universe: a weakly
  associated prime of `N ⊗[R] M`, or of `M`, is already one of `N ⊗[R] M'`, or of `M'`, for a
  finite submodule `M'` of `M`, flatness of `N` making `N ⊗[R] M' → N ⊗[R] M` injective.

## References

* [Stacks Project, Tag 05II](https://stacks.math.columbia.edu/tag/05II)
* [Stacks Project, Tag 05IG](https://stacks.math.columbia.edu/tag/05IG)
-/

@[expose] public section

open TensorProduct

universe u v w x

namespace Stacks.WeaklyAssociatedPrimes

/-- Alias of `AlgebraicGeometry.isWeaklyAssociatedPrime_iff_of_semilinearEquiv`. -/
alias isWeaklyAssociatedPrime_iff_of_semilinearEquiv :=
  AlgebraicGeometry.isWeaklyAssociatedPrime_iff_of_semilinearEquiv

/-- A localization at a larger submonoid of a localization at a smaller one is a localization at
the larger submonoid. -/
theorem isLocalizedModule_comp_of_le
    {R : Type*} [CommSemiring R] {U W : Submonoid R} (hUW : U ≤ W)
    {M M₁ M₂ : Type*} [AddCommMonoid M] [Module R M]
    [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]
    (f : M →ₗ[R] M₁) [IsLocalizedModule U f]
    (g : M₁ →ₗ[R] M₂) [IsLocalizedModule W g] :
    IsLocalizedModule W (g.comp f) where
  map_units := IsLocalizedModule.map_units g
  surj y := by
    obtain ⟨⟨y₁, w⟩, hw⟩ := IsLocalizedModule.surj W g y
    obtain ⟨⟨x, u⟩, hu⟩ := IsLocalizedModule.surj U f y₁
    refine ⟨⟨x, ⟨(u : R) * (w : R), mul_mem (hUW u.2) w.2⟩⟩, ?_⟩
    simp only [Submonoid.smul_def, LinearMap.coe_comp, Function.comp_apply] at hw hu ⊢
    rw [mul_smul, hw, ← map_smul, hu]
  exists_of_eq {x₁ x₂} heq := by
    simp only [LinearMap.coe_comp, Function.comp_apply] at heq
    obtain ⟨w, hw⟩ := IsLocalizedModule.exists_of_eq (S := W) (f := g) heq
    simp only [Submonoid.smul_def] at hw
    obtain ⟨u, hu⟩ := IsLocalizedModule.exists_of_eq (S := U) (f := f)
      (x₁ := (w : R) • x₁) (x₂ := (w : R) • x₂) (by
        rw [map_smul, map_smul]
        exact hw)
    simp only [Submonoid.smul_def] at hu
    exact ⟨⟨(u : R) * (w : R), mul_mem (hUW u.2) w.2⟩, by
      simp only [Submonoid.smul_def]
      rw [mul_smul, mul_smul, hu]⟩

/-- A prime disjoint from the submonoid is weakly associated to a localized module exactly when
it is weakly associated to the module itself. -/
theorem isWeaklyAssociatedPrime_iff_of_isLocalizedModule_disjoint
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (U : Submonoid R) (f : M →ₗ[R] N)
    [IsLocalizedModule U f] (p : Ideal R) (hp : p.IsPrime)
    (hdisj : Disjoint (U : Set R) (p : Set R)) :
    IsWeaklyAssociatedPrime R N p ↔ IsWeaklyAssociatedPrime R M p := by
  let e := IsLocalizedModule.iso U f
  have he := isWeaklyAssociatedPrime_iff_of_semilinearEquiv (RingEquiv.refl R)
    e.toAddEquiv (by intro r m; exact e.map_smul r m) p
  simp only [show (RingEquiv.refl R).toRingHom = RingHom.id R from rfl, Ideal.map_id] at he
  rw [← he]
  have h := Set.ext_iff.mp (weakAss_inter_image_eq_weakAss_localizedModule U (M := M))
    ⟨p, hp⟩
  rw [PrimeSpectrum.localization_comap_range (Localization U) U] at h
  exact h.symm.trans (and_iff_left hdisj)

/-- If a module flat over `R` is the localization of a module over a localization `S` of a finite
type `R`-algebra `T`, then the localization at a prime of the `T`-model is again flat over `R`. -/
theorem flat_localizedModule_of_finiteTypeModel
    {R T S : Type u} [CommRing R] [CommRing T] [CommRing S]
    [Algebra R T] [Algebra R S] [Algebra T S] [IsScalarTower R T S]
    (U : Submonoid T) [IsLocalization U S]
    {P N₀ N : Type*} [AddCommGroup P] [Module T P] [Module R P] [IsScalarTower R T P]
    [AddCommGroup N₀] [Module S N₀] [Module T N₀] [IsScalarTower T S N₀]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Flat R N]
    (φ : P →ₗ[T] N₀) [IsLocalizedModule U φ]
    (V : Submonoid S) (f : N₀ →ₗ[S] N) [IsLocalizedModule V f]
    (q : Ideal S) [q.IsPrime] (hV : V ≤ q.primeCompl) :
    Module.Flat R (LocalizedModule (q.comap (algebraMap T S)).primeCompl P) := by
  let qT := q.comap (algebraMap T S)
  let Q := Localization.AtPrime q
  let L₀ := LocalizedModule q.primeCompl N₀
  let L := LocalizedModule q.primeCompl N
  let : Algebra T Q := inferInstance
  let : IsScalarTower T S Q := inferInstance
  let : IsLocalization qT.primeCompl Q :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization U Q q
  let : Module T L₀ := inferInstance
  let : IsScalarTower T S L₀ := inferInstance
  let : IsScalarTower T Q L₀ := IsScalarTower.of_algebraMap_smul fun r m => by
    rw [IsScalarTower.algebraMap_apply T S Q, algebraMap_smul]
    exact algebraMap_smul S r m
  let g₀ : N₀ →ₗ[S] L₀ := LocalizedModule.mkLinearMap _ _
  let g : N →ₗ[S] L := LocalizedModule.mkLinearMap _ _
  have hφ := IsLocalizedModule.isBaseChange U S φ
  have hg₀ := IsLocalizedModule.isBaseChange q.primeCompl Q g₀
  let : IsLocalizedModule qT.primeCompl ((g₀.restrictScalars T).comp φ) :=
    (isLocalizedModule_iff_isBaseChange qT.primeCompl Q _).mpr (hφ.comp hg₀)
  let e₀ : LocalizedModule qT.primeCompl P ≃ₗ[T] L₀ :=
    IsLocalizedModule.linearEquiv qT.primeCompl (LocalizedModule.mkLinearMap _ _)
      ((g₀.restrictScalars T).comp φ)
  let : IsLocalizedModule q.primeCompl (g.comp f) :=
    isLocalizedModule_comp_of_le hV f g
  let e : L₀ ≃ₗ[S] L := IsLocalizedModule.linearEquiv q.primeCompl g₀ (g.comp f)
  let : Module R L := inferInstance
  let : IsScalarTower R S L := inferInstance
  let : Module.Flat R L := Module.Flat.of_isLocalizedModule_of_tower q.primeCompl g
  let : Module R L₀ := Module.compHom _ (algebraMap R S)
  let : IsScalarTower R S L₀ := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hL₀ : Module.Flat R L₀ := Module.Flat.of_linearEquiv (e.restrictScalars R)
  let : IsScalarTower R T L₀ := IsScalarTower.of_algebraMap_smul fun r m => by
    rw [← algebraMap_smul S (algebraMap R T r), ← IsScalarTower.algebraMap_apply R T S,
      algebraMap_smul]
  exact (Module.Flat.equiv_iff (e₀.restrictScalars R)).mpr hL₀

/-- A finite module over a ring essentially of finite type over `R` is the localization of a
finite module over a finite type `R`-algebra. -/
theorem exists_finite_type_model
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (hfinite : IsEssentiallyOfFiniteType R S (algebraMap R S))
    (N₀ : Type w) [AddCommGroup N₀] [Module S N₀] [Module.Finite S N₀] :
    ∃ (T : Type u) (hT : CommRing T) (aRT : Algebra R T)
      (_hFT : Algebra.FiniteType R T) (U : Submonoid T) (aTS : Algebra T S),
      letI : CommRing T := hT
      letI : Algebra R T := aRT
      letI : Algebra T S := aTS
      letI : Algebra R S := (algebraMap R S).toAlgebra
      ∃ (_hTower : IsScalarTower R T S) (_hLoc : IsLocalization U S)
        (P : Type u) (_hPAdd : AddCommGroup P) (_hPT : Module T P)
        (_hPfin : Module.Finite T P),
        letI : Module T N₀ := Module.compHom N₀ (algebraMap T S)
        letI : IsScalarTower T S N₀ := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
        ∃ φ : P →ₗ[T] N₀, IsLocalizedModule U φ := by
  classical
  let : Algebra R S := (algebraMap R S).toAlgebra
  rcases hfinite with ⟨T, hT, aRT, hFT, U, aTS, hTower, hLoc⟩
  let : CommRing T := hT
  let : Algebra R T := aRT
  let : Algebra.FiniteType R T := hFT
  let : Algebra T S := aTS
  let : IsScalarTower R T S := hTower
  let : IsLocalization U S := hLoc
  let : Module T N₀ := Module.compHom N₀ (algebraMap T S)
  let : IsScalarTower T S N₀ := IsScalarTower.of_algebraMap_smul fun r _ => rfl
  let : IsLocalizedModule U (LinearMap.id : N₀ →ₗ[T] N₀) :=
    isLocalizedModule_id U N₀ S
  obtain ⟨P, hPAdd, hPT, φ, hPfin, hφ, _⟩ :=
    Module.exists_finite_isLocalizedModule_comp U S (LinearMap.id : N₀ →ₗ[T] N₀)
  exact ⟨T, hT, aRT, hFT, U, aTS, hTower, hLoc, P, hPAdd, hPT, hPfin, φ, hφ⟩

/-- A prime is weakly associated to its own residue field, the annihilator of `1` being the
prime itself. -/
theorem isWeaklyAssociatedPrime_residueField
    {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime] :
    IsWeaklyAssociatedPrime R p.ResidueField p := by
  refine ⟨1, ?_⟩
  have h : (R ∙ (1 : p.ResidueField)).annihilator = p := by
    ext r
    simp only [Submodule.mem_annihilator_span_singleton, Algebra.smul_def, mul_one,
      Ideal.algebraMap_residueField_eq_zero]
  rw [h, Ideal.minimalPrimes_eq_subsingleton_self]
  rfl

/-- The fibre ring of a ring map essentially of finite type is Noetherian. -/
theorem isNoetherianRing_tensorResidueField_of_isEssentiallyOfFiniteType
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (hfinite : IsEssentiallyOfFiniteType R S (algebraMap R S))
    (p : Ideal R) [p.IsPrime] :
    IsNoetherianRing (S ⊗[R] p.ResidueField) := by
  rcases hfinite with ⟨A, hA, aRA, hft, U, aAS, hTower, hLoc⟩
  let : CommRing A := hA
  let : Algebra R A := aRA
  let : Algebra.FiniteType R A := hft
  let : Algebra A S := aAS
  have hcomp : (algebraMap A S).comp (algebraMap R A) = algebraMap R S := by
    ext r
    let : Algebra R S := (algebraMap R S).toAlgebra
    let : IsScalarTower R A S := hTower
    exact (IsScalarTower.algebraMap_apply R A S r).symm
  let : IsScalarTower R A S := IsScalarTower.of_algebraMap_eq' hcomp.symm
  let : IsLocalization U S := hLoc
  let : Algebra.EssFiniteType A S := Algebra.EssFiniteType.of_isLocalization S U
  let : Algebra.EssFiniteType R S := Algebra.EssFiniteType.comp R A S
  let : Algebra.EssFiniteType p.ResidueField (p.ResidueField ⊗[R] S) := inferInstance
  let : IsNoetherianRing (p.ResidueField ⊗[R] S) :=
    Algebra.EssFiniteType.isNoetherianRing p.ResidueField _
  exact isNoetherianRing_of_ringEquiv _
    (Algebra.TensorProduct.comm R S p.ResidueField).toRingEquiv.symm

/-- A prime weakly associated to a localized module is disjoint from the submonoid. -/
theorem disjoint_of_isWeaklyAssociatedPrime_localizedModule
    {A L K : Type*} [CommRing A]
    [AddCommGroup L] [Module A L] [AddCommGroup K] [Module A K]
    (U : Submonoid A) (f : L →ₗ[A] K) [IsLocalizedModule U f]
    (q : Ideal A) [q.IsPrime] (hq : IsWeaklyAssociatedPrime A K q) :
    Disjoint (U : Set A) (q : Set A) := by
  let e := IsLocalizedModule.iso U f
  have hq' : IsWeaklyAssociatedPrime A (LocalizedModule U L) q :=
    (isWeaklyAssociatedPrime_iff_of_semilinearEquiv (RingEquiv.refl A)
      e.toAddEquiv (by intro r m; exact e.map_smul r m) q).mpr (by
        convert hq using 1
        simp)
  have h := Set.ext_iff.mp (weakAss_inter_image_eq_weakAss_localizedModule U
    (M := L)) ⟨q, inferInstance⟩
  have hh := h.mpr hq'
  simpa [PrimeSpectrum.localization_comap_range (Localization U) U] using hh.2

/-- A prime of the fibre ring `S ⊗[R] κ(p)` contracts, through `S`, to `p` itself. -/
theorem comap_comap_algebraMap_tensorResidueField
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime]
    (q : Ideal (S ⊗[R] p.ResidueField)) [q.IsPrime] :
    (q.comap (algebraMap S (S ⊗[R] p.ResidueField))).comap (algebraMap R S) = p := by
  let j : p.ResidueField →+* S ⊗[R] p.ResidueField :=
    Algebra.TensorProduct.includeRight.toRingHom
  have hj : q.comap j = ⊥ := Ideal.eq_bot_of_prime _
  have hc : (algebraMap S (S ⊗[R] p.ResidueField)).comp (algebraMap R S) =
      j.comp (algebraMap R p.ResidueField) := by
    ext r
    simp [j, Algebra.TensorProduct.tmul_one_eq_one_tmul]
  rw [Ideal.comap_comap, hc, ← Ideal.comap_comap, hj]
  exact p.ker_algebraMap_residueField

/-- A prime weakly associated to a module is already weakly associated to the submodule spanned
by a single witnessing element. -/
theorem exists_isWeaklyAssociatedPrime_span_singleton
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {p : Ideal R} (h : IsWeaklyAssociatedPrime R M p) :
    ∃ m : M, IsWeaklyAssociatedPrime R (Submodule.span R {m}) p := by
  obtain ⟨m, hm⟩ := h
  refine ⟨m, ⟨⟨m, Submodule.mem_span_singleton_self m⟩, ?_⟩⟩
  have hann : (R ∙ (⟨m, Submodule.mem_span_singleton_self m⟩ :
      Submodule.span R {m})).annihilator = (R ∙ m).annihilator := by
    ext r
    simp only [Submodule.mem_annihilator_span_singleton]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  rwa [hann]

/-- An injective linear map preserves and reflects minimality of a prime over the annihilator of
an element. -/
theorem mem_minimalPrimes_annihilator_iff_of_injective
    {R A B : Type*} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) (hf : Function.Injective f) (p : Ideal R) (a : A) :
    p ∈ (R ∙ a).annihilator.minimalPrimes ↔
      p ∈ (R ∙ f a).annihilator.minimalPrimes := by
  have hann : (R ∙ a).annihilator = (R ∙ f a).annihilator := by
    ext r
    simp only [Submodule.mem_annihilator_span_singleton, ← map_smul]
    exact (map_eq_zero_iff f hf).symm
  rw [hann]

/-- Weak association passes along an injective linear map. -/
theorem isWeaklyAssociatedPrime_of_injective
    {R A B : Type*} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) (hf : Function.Injective f) (p : Ideal R)
    (h : IsWeaklyAssociatedPrime R A p) : IsWeaklyAssociatedPrime R B p := by
  obtain ⟨a, ha⟩ := h
  exact ⟨f a, (mem_minimalPrimes_annihilator_iff_of_injective f hf p a).mp ha⟩

/-- The fibre condition only depends on the prime of the base through its residue field. -/
theorem isWeaklyAssociatedPrime_tensorResidueField_congr
    {R S N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    {p₁ p₂ : Ideal R} [p₁.IsPrime] [p₂.IsPrime]
    (h : p₁ = p₂) (q : Ideal S) :
    IsWeaklyAssociatedPrime S (N ⊗[R] p₁.ResidueField) q ↔
      IsWeaklyAssociatedPrime S (N ⊗[R] p₂.ResidueField) q := by
  subst p₂
  rfl

/-- Weak association of a prime to `N ⊗[R] M` is detected on a finite type model: it holds exactly
when the contracted prime is weakly associated to the tensor product of the model with `M`. -/
theorem isWeaklyAssociatedPrime_tensorProduct_iff_of_finiteTypeModel
    {R A S P N₀ N M : Type*} [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] [Algebra A S] [IsScalarTower R A S]
    [AddCommGroup P] [Module A P] [Module R P] [IsScalarTower R A P]
    [AddCommGroup N₀] [Module S N₀] [Module A N₀] [Module R N₀]
    [IsScalarTower A S N₀] [IsScalarTower R A N₀] [IsScalarTower R S N₀]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [AddCommGroup M] [Module R M]
    (U : Submonoid A) [IsLocalization U S]
    (φ : P →ₗ[A] N₀) [IsLocalizedModule U φ]
    (V : Submonoid S) (f : N₀ →ₗ[S] N) [IsLocalizedModule V f]
    (q : Ideal S) [q.IsPrime] (hdisj : Disjoint (V : Set S) (q : Set S)) :
    IsWeaklyAssociatedPrime S (N ⊗[R] M) q ↔
      IsWeaklyAssociatedPrime A (P ⊗[R] M) (q.comap (algebraMap A S)) := by
  let ψ := TensorProduct.AlgebraTensorModule.map f (LinearMap.id : M →ₗ[R] M)
  let ψ₀ := TensorProduct.AlgebraTensorModule.map φ (LinearMap.id : M →ₗ[R] M)
  let : IsLocalizedModule V ψ :=
    isLocalizedModule_tensorRight (S := Localization V) V f
  let : IsLocalizedModule U ψ₀ := isLocalizedModule_tensorRight (S := S) U φ
  exact (isWeaklyAssociatedPrime_iff_of_isLocalizedModule_disjoint V ψ q inferInstance hdisj).trans
    (isWeaklyAssociatedPrime_iff_of_isLocalization U ψ₀ q inferInstance)

/-- **The equivalence of [Stacks, Tag 05IG] for a localization of a finite module, through a
finite type model.** For `N` a localization of a finite module over a localization `S` of a
finite type `R`-algebra, with `N` flat over `R`, a prime `q` of `S` is weakly associated to
`N ⊗[R] M` exactly when its contraction `p` is weakly associated to `M` and `q` is weakly
associated to `N ⊗[R] κ(p)`. -/
theorem isWeaklyAssociatedPrime_tensorProduct_iff_fibre_of_finiteTypeModel
    (h05IG : TensorFibreFormula05IG.{u})
    (R A S : Type u) [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] [Algebra A S] [IsScalarTower R A S]
    [Algebra.FiniteType R A]
    (P M : Type u) (N₀ : Type w) (N : Type x)
    [AddCommGroup P] [Module A P] [Module R P]
    [IsScalarTower R A P] [Module.Finite A P]
    [AddCommGroup N₀] [Module S N₀] [Module A N₀] [Module R N₀]
    [IsScalarTower A S N₀] [IsScalarTower R A N₀] [IsScalarTower R S N₀]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Flat R N]
    [AddCommGroup M] [Module R M]
    (U : Submonoid A) [IsLocalization U S]
    (φ : P →ₗ[A] N₀) [IsLocalizedModule U φ]
    (V : Submonoid S) (f : N₀ →ₗ[S] N) [IsLocalizedModule V f]
    (q : Ideal S) [q.IsPrime] (hV : V ≤ q.primeCompl) :
    IsWeaklyAssociatedPrime S (N ⊗[R] M) q ↔
      IsWeaklyAssociatedPrime R M (q.comap (algebraMap R S)) ∧
        IsWeaklyAssociatedPrime S
          (N ⊗[R] (q.comap (algebraMap R S)).ResidueField) q := by
  let qA : Ideal A := q.comap (algebraMap A S)
  let : qA.IsPrime := Ideal.IsPrime.comap _
  let p : Ideal R := q.comap (algebraMap R S)
  let : p.IsPrime := Ideal.IsPrime.comap _
  have hp : qA.comap (algebraMap R A) = p := by
    ext r
    show algebraMap A S (algebraMap R A r) ∈ q ↔ algebraMap R S r ∈ q
    rw [← IsScalarTower.algebraMap_apply R A S]
  have hdisj : Disjoint (V : Set S) (q : Set S) :=
    Set.disjoint_left.mpr fun s hs hq => hV hs hq
  have hflatA := flat_localizedModule_of_finiteTypeModel (R := R) (T := A) (S := S) U φ V f q hV
  have : qA.LiesOver p := ⟨hp.symm⟩
  have hA := isWeaklyAssociatedPrime_tensorProduct_iff_of_finiteType h05IG
    (R := R) (A := A) (P := P) (M := M) p qA hflatA
  have hM := isWeaklyAssociatedPrime_tensorProduct_iff_of_finiteTypeModel
    (R := R) (A := A) (S := S) (P := P) (N₀ := N₀) (N := N) (M := M)
    U φ V f q hdisj
  have hK := isWeaklyAssociatedPrime_tensorProduct_iff_of_finiteTypeModel
    (R := R) (A := A) (S := S) (P := P) (N₀ := N₀) (N := N)
    (M := p.ResidueField) U φ V f q hdisj
  exact hM.trans (hA.trans (and_congr_right fun _ => hK.symm))

/-- **The equivalence of [Stacks, Tag 05IG] for an essentially finite type ring map.** For `R → S`
essentially of finite type and `N` a localization of a finite `S`-module which is flat over `R`,
a prime `q` of `S` disjoint from the localizing submonoid is weakly associated to `N ⊗[R] M`
exactly when its contraction `p` is weakly associated to `M` and `q` is weakly associated to
`N ⊗[R] κ(p)`. -/
theorem isWeaklyAssociatedPrime_tensorProduct_iff_fibre_of_essentiallyOfFiniteType
    (h05IG : TensorFibreFormula05IG.{u})
    (R S : Type u) (M : Type u) (N₀ : Type w) (N : Type x)
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N₀] [Module S N₀] [Module.Finite S N₀]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Flat R N]
    (hfinite : IsEssentiallyOfFiniteType R S (algebraMap R S))
    (V : Submonoid S) (f : N₀ →ₗ[S] N) [IsLocalizedModule V f]
    (q : Ideal S) [q.IsPrime]
    (hdisj : Disjoint (V : Set S) (q : Set S)) :
    IsWeaklyAssociatedPrime S (N ⊗[R] M) q ↔
      IsWeaklyAssociatedPrime R M (q.comap (algebraMap R S)) ∧
        IsWeaklyAssociatedPrime S
          (N ⊗[R] (q.comap (algebraMap R S)).ResidueField) q := by
  classical
  obtain ⟨A, hA, aRA, hFT, U, aAS, hTower, hLoc,
    P, hPAdd, hPA, hPfin, φ, hφ⟩ := exists_finite_type_model hfinite N₀
  let : CommRing A := hA
  let : Algebra R A := aRA
  let : Algebra.FiniteType R A := hFT
  let : Algebra A S := aAS
  have hcomp : (algebraMap A S).comp (algebraMap R A) = algebraMap R S := by
    ext r
    let : Algebra R S := (algebraMap R S).toAlgebra
    let : IsScalarTower R A S := hTower
    exact (IsScalarTower.algebraMap_apply R A S r).symm
  let : IsScalarTower R A S := IsScalarTower.of_algebraMap_eq' hcomp.symm
  let : IsLocalization U S := hLoc
  let : AddCommGroup P := hPAdd
  let : Module A P := hPA
  let : Module.Finite A P := hPfin
  let : Module R P := Module.compHom P (algebraMap R A)
  let : IsScalarTower R A P := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : Module A N₀ := Module.compHom N₀ (algebraMap A S)
  let : IsScalarTower A S N₀ := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : Module R N₀ := Module.compHom N₀ (algebraMap R A)
  let : IsScalarTower R A N₀ := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsScalarTower R S N₀ := IsScalarTower.of_algebraMap_smul fun r m => by
    show algebraMap R S r • m = algebraMap A S (algebraMap R A r) • m
    rw [← hcomp]
    rfl
  let : IsLocalizedModule U φ := hφ
  exact isWeaklyAssociatedPrime_tensorProduct_iff_fibre_of_finiteTypeModel h05IG
    R A S P M N₀ N U φ V f q fun _ hs => Set.disjoint_left.mp hdisj hs

/-- **[Stacks, Tag 05II].** For `R → S` essentially of finite type, `N` a localization of a
finite `S`-module flat over `R` and `M` any `R`-module, the weakly associated primes of
`N ⊗[R] M` are the contractions of the primes of the fibre rings `S ⊗[R] κ(p)` associated to the
fibre modules, over the weakly associated primes `p` of `M`. -/
@[stacks 05II "the full set equality; the two rings lie in one universe, as \
`IsEssentiallyOfFiniteType` requires, and the modules are in arbitrary universes"]
theorem weaklyAssociatedPrimes_tensorProduct_eq_fibrewise_assStacks_of_small
    (R S : Type u) (M : Type v) (N₀ : Type w) (N : Type x)
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N₀] [Module S N₀] [Module.Finite S N₀]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Flat R N]
    (hfinite : IsEssentiallyOfFiniteType R S (algebraMap R S))
    (T : Submonoid S) (f : N₀ →ₗ[S] N) [IsLocalizedModule T f] :
    weaklyAssociatedPrimes S (N ⊗[R] M) =
      {q : Ideal S | ∃ p ∈ weaklyAssociatedPrimes R M, ∃ hp : p.IsPrime,
        letI : p.IsPrime := hp
        ∃ q' ∈ assStacks (S ⊗[R] p.ResidueField)
          ((S ⊗[R] p.ResidueField) ⊗[S] N),
          q = Ideal.comap (Algebra.TensorProduct.includeLeft (R := R)
            (S := S) (A := S) (B := p.ResidueField)).toRingHom q'} := by
  classical
  let : Module R N₀ := Module.compHom N₀ (algebraMap R S)
  let : IsScalarTower R S N₀ := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  -- The equivalence of Tag 05IG for a submodule of `M` small over the rings.
  have hsmall : ∀ (M' : Submodule R M) [Small.{u} M'] (q : Ideal S) [q.IsPrime],
      Disjoint (T : Set S) (q : Set S) →
        (IsWeaklyAssociatedPrime S (N ⊗[R] M') q ↔
          IsWeaklyAssociatedPrime R M' (q.comap (algebraMap R S)) ∧
            IsWeaklyAssociatedPrime S (N ⊗[R] (q.comap (algebraMap R S)).ResidueField) q) := by
    intro M' _ q _ hdisj
    let e : Shrink.{u} M' ≃ₗ[R] M' := Shrink.linearEquiv R M'
    let eN : N ⊗[R] Shrink.{u} M' ≃ₗ[S] N ⊗[R] M' :=
      TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S N) e
    have h := isWeaklyAssociatedPrime_tensorProduct_iff_fibre_of_essentiallyOfFiniteType
      tensorFibreFormula05IG R S (Shrink.{u} M') N₀ N hfinite T f q hdisj
    constructor
    · intro hq
      have h' := h.mp
        (isWeaklyAssociatedPrime_of_injective eN.symm.toLinearMap eN.symm.injective q hq)
      exact ⟨isWeaklyAssociatedPrime_of_injective e.toLinearMap e.injective _ h'.1, h'.2⟩
    · rintro ⟨hp, hfib⟩
      exact isWeaklyAssociatedPrime_of_injective eN.toLinearMap eN.injective q
        (h.mpr ⟨isWeaklyAssociatedPrime_of_injective e.symm.toLinearMap e.symm.injective _ hp,
          hfib⟩)
  -- Tensoring the inclusion of a submodule of `M` with the flat module `N` stays injective.
  have hincl : ∀ M' : Submodule R M,
      Function.Injective (TensorProduct.AlgebraTensorModule.map (LinearMap.id : N →ₗ[S] N)
        M'.subtype) := by
    intro M'
    have heq : (TensorProduct.AlgebraTensorModule.map (LinearMap.id : N →ₗ[S] N)
        M'.subtype).restrictScalars R = M'.subtype.lTensor N :=
      TensorProduct.ext' fun _ _ => rfl
    show Function.Injective ((TensorProduct.AlgebraTensorModule.map
      (LinearMap.id : N →ₗ[S] N) M'.subtype).restrictScalars R)
    rw [heq]
    exact Module.Flat.lTensor_preserves_injective_linearMap M'.subtype M'.injective_subtype
  -- The equivalence of Tag 05IG for `M` itself.
  have hpt : ∀ (q : Ideal S) [q.IsPrime], Disjoint (T : Set S) (q : Set S) →
      (IsWeaklyAssociatedPrime S (N ⊗[R] M) q ↔
        IsWeaklyAssociatedPrime R M (q.comap (algebraMap R S)) ∧
          IsWeaklyAssociatedPrime S (N ⊗[R] (q.comap (algebraMap R S)).ResidueField) q) := by
    intro q _ hdisj
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨M', hfin, hsub⟩ :=
        TensorProduct.exists_finite_submodule_right_of_setFinite {x} (Set.finite_singleton x)
      obtain ⟨y, hy⟩ := hsub (Set.mem_singleton x)
      let : Small.{u} M' := Module.Finite.small.{u} R M'
      let ι := TensorProduct.AlgebraTensorModule.map (LinearMap.id : N →ₗ[S] N) M'.subtype
      have hιy : ι y = x := hy
      have hq' : IsWeaklyAssociatedPrime S (N ⊗[R] M') q :=
        ⟨y, (mem_minimalPrimes_annihilator_iff_of_injective ι (hincl M') q y).mpr
          (hιy ▸ hx)⟩
      have h' := (hsmall M' q hdisj).mp hq'
      exact ⟨isWeaklyAssociatedPrime_of_injective M'.subtype M'.injective_subtype _ h'.1, h'.2⟩
    · rintro ⟨hp, hfib⟩
      obtain ⟨m, hm⟩ := exists_isWeaklyAssociatedPrime_span_singleton hp
      exact isWeaklyAssociatedPrime_of_injective _ (hincl (Submodule.span R {m})) q
        ((hsmall (Submodule.span R {m}) q hdisj).mpr ⟨hm, hfib⟩)
  ext q
  constructor
  · intro hq
    have : q.IsPrime := IsWeaklyAssociatedPrime.isPrime S (N ⊗[R] M) hq
    have hdisj : Disjoint (T : Set S) (q : Set S) := by
      let ψ := TensorProduct.AlgebraTensorModule.map f (LinearMap.id : M →ₗ[R] M)
      let : IsLocalizedModule T ψ := isLocalizedModule_tensorRight (S := Localization T) T f
      exact disjoint_of_isWeaklyAssociatedPrime_localizedModule T ψ q
        ((mem_weaklyAssociatedPrimes_iff S (N ⊗[R] M)).mp hq)
    have hh := (hpt q hdisj).mp ((mem_weaklyAssociatedPrimes_iff S (N ⊗[R] M)).mp hq)
    let p := q.comap (algebraMap R S)
    let : p.IsPrime := Ideal.IsPrime.comap _
    let : IsNoetherianRing (S ⊗[R] p.ResidueField) :=
      isNoetherianRing_tensorResidueField_of_isEssentiallyOfFiniteType hfinite p
    obtain ⟨q', hq', hqeq⟩ :=
      (isWeaklyAssociatedPrime_tensorResidueField_iff p q).mp hh.2
    exact ⟨p, hh.1, inferInstance, q', hq', hqeq⟩
  · rintro ⟨p, hp, hprime, q', hq', rfl⟩
    let : p.IsPrime := hprime
    have : q'.IsPrime := hq'.1
    let q := q'.comap (algebraMap S (S ⊗[R] p.ResidueField))
    let : q.IsPrime := Ideal.IsPrime.comap _
    have hbase : q.comap (algebraMap R S) = p := comap_comap_algebraMap_tensorResidueField p q'
    let : IsNoetherianRing (S ⊗[R] p.ResidueField) :=
      isNoetherianRing_tensorResidueField_of_isEssentiallyOfFiniteType hfinite p
    have hfiber : IsWeaklyAssociatedPrime S (N ⊗[R] p.ResidueField) q :=
      (isWeaklyAssociatedPrime_tensorResidueField_iff p q).mpr ⟨q', hq', rfl⟩
    have hdisj : Disjoint (T : Set S) (q : Set S) := by
      let ψ := TensorProduct.AlgebraTensorModule.map f
        (LinearMap.id : p.ResidueField →ₗ[R] p.ResidueField)
      let : IsLocalizedModule T ψ := isLocalizedModule_tensorRight (S := Localization T) T f
      exact disjoint_of_isWeaklyAssociatedPrime_localizedModule T ψ q hfiber
    apply (mem_weaklyAssociatedPrimes_iff S (N ⊗[R] M)).mpr
    refine (hpt q hdisj).mpr
      ⟨?_, (isWeaklyAssociatedPrime_tensorResidueField_congr (N := N) hbase.symm q).mp hfiber⟩
    change IsWeaklyAssociatedPrime R M p at hp
    rwa [hbase]

end Stacks.WeaklyAssociatedPrimes

end
