module

public import Mathlib.Algebra.BigOperators.Finprod
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizationKernel
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Comparison
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesHerbrand.Length
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicLengthSubquotient

/-!
# Splitting a sum over the minimal points of a support

A sum over the subtype cut out by a finite set of indices splits off any one of its members. For
the kernel of the localization map at a minimal point `q` of the support of a finite module, the
support loses `q` and keeps every other minimal point, which is what makes an induction on the
minimal points of the support possible.

## Main results

* `Module.FiniteLength.finsum_subtype_eq_add_finsum_subtype_diff`: the sum over a finite index
  set splits off one member.
* `Module.FiniteLength.support_ker_mkLinearMap_subset`: the support of the kernel of the
  localization map is contained in the support of the module.
* `Module.FiniteLength.mem_support_ker_mkLinearMap_of_minimal_ne`: every minimal point other
  than `q` stays in the support of that kernel.

## Implementation notes

The sums of the conclusion of Tag 02QD are `finsum` over the subtype of minimal points of the
support, so splitting one off goes through `finsum_set_coe_eq_finsum_mem` to the set-indexed form
and then `finsum_mem_insert`, with `Set.insert_sdiff_singleton` restoring the set. The support
inclusion is `Module.support_subset_of_injective` for the inclusion of the kernel, and the
persistence of the other minimal points is
`Module.FiniteLength.bijective_localized_map_subtype_ker`.

## References

* [Stacks Project, Tag 02QD](https://stacks.math.columbia.edu/tag/02QD)
-/

@[expose] public section

open AlgebraicGeometry

namespace Module.FiniteLength

universe u v

/-- A sum over a finite index set splits off any one of its members. -/
theorem finsum_subtype_eq_add_finsum_subtype_diff {α : Type u} {A : Type v} [AddCommMonoid A]
    (f : α → A) {S : Set α} (hS : S.Finite) {q : α} (hq : q ∈ S) :
    ∑ᶠ p : S, f p = f q + ∑ᶠ p : (S \ {q} : Set α), f p := by
  rw [finsum_set_coe_eq_finsum_mem, finsum_set_coe_eq_finsum_mem,
    ← finsum_mem_insert f (by simp) hS.sdiff, Set.insert_sdiff_singleton,
    Set.insert_eq_of_mem hq]

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- The support of the kernel of a localization map is contained in the support of the module. -/
theorem support_ker_mkLinearMap_subset (S : Submonoid R) :
    Module.support R ↥(LinearMap.ker (LocalizedModule.mkLinearMap S M)) ⊆
      Module.support R M :=
  Module.support_subset_of_injective _
    (Submodule.injective_subtype (LinearMap.ker (LocalizedModule.mkLinearMap S M)))

/-- A minimal point of the support other than `q` remains in the support of the kernel of the
localization map at `q`. -/
theorem mem_support_ker_mkLinearMap_of_minimal_ne [IsNoetherianRing R] [Module.Finite R M]
    {q p : PrimeSpectrum R} (hq : Minimal (· ∈ Module.support R M) q)
    (hp : Minimal (· ∈ Module.support R M) p) (hne : q ≠ p) :
    p ∈ Module.support R
      ↥(LinearMap.ker (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M)) := by
  by_contra hmem
  have := Module.notMem_support_iff.mp hmem
  exact Module.notMem_support_iff.mpr
    (bijective_localized_map_subtype_ker (M := M) hq hp hne).2.subsingleton hp.1

open AlgebraicGeometry in
/-- The degree-zero cohomology of a two-periodic complex has finite length exactly when the
quotient of `ker φ` by the image of `ψ` does. -/
theorem isFiniteLength_homology_zero_iff (φ ψ : Module.End R M) (hφψ : φ * ψ = 0)
    (hψφ : ψ * φ = 0) (h : ∀ x, ψ x ∈ LinearMap.ker φ) :
    IsFiniteLength R ((twoPeriodicComplex φ ψ hφψ hψφ).homology (0 : ZMod 2)) ↔
      IsFiniteLength R (↥(LinearMap.ker φ) ⧸
        LinearMap.range (LinearMap.codRestrict (LinearMap.ker φ) ψ h)) := by
  rw [← Module.length_ne_top_iff, ← Module.length_ne_top_iff]
  have hh := homology_length_eq_ker_quotient φ ψ hφψ hψφ (0 : ZMod 2) (Or.inl rfl)
  rw [ite_eq_left rfl] at hh
  rw [hh, range_codRestrict_eq_comap]

open AlgebraicGeometry in
/-- The degree-one cohomology of a two-periodic complex has finite length exactly when the
quotient of `ker ψ` by the image of `φ` does. -/
theorem isFiniteLength_homology_one_iff (φ ψ : Module.End R M) (hφψ : φ * ψ = 0)
    (hψφ : ψ * φ = 0) (h : ∀ x, φ x ∈ LinearMap.ker ψ) :
    IsFiniteLength R ((twoPeriodicComplex φ ψ hφψ hψφ).homology (1 : ZMod 2)) ↔
      IsFiniteLength R (↥(LinearMap.ker ψ) ⧸
        LinearMap.range (LinearMap.codRestrict (LinearMap.ker ψ) φ h)) := by
  rw [← Module.length_ne_top_iff, ← Module.length_ne_top_iff]
  have hh := homology_length_eq_ker_quotient φ ψ hφψ hψφ (1 : ZMod 2) (Or.inr rfl)
  rw [ite_eq_right (by decide : ¬((1 : ZMod 2) = 0))] at hh
  rw [hh, range_codRestrict_eq_comap]

/-- The quotient map intertwines an endomorphism preserving a submodule with the induced one. -/
private theorem mkQ_comp_eq_mapQ_comp_mkQ (K : Submodule R M) (f : Module.End R M)
    (hf : ∀ x ∈ K, f x ∈ K) : K.mkQ ∘ₗ f = K.mapQ K f hf ∘ₗ K.mkQ :=
  LinearMap.ext fun m ↦ by simp

open AlgebraicGeometry in
/-- Finite-length cohomology passes to the quotient by the kernel of the localization map at a
prime `q` other than the closed point, provided the quotient's support meets no prime other than
the closed point and `q`. -/
theorem hasFiniteLengthHomology_mapQ_ker [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R M]
    (φ ψ : Module.End R M) (hφψ : φ * ψ = 0) (hψφ : ψ * φ = 0)
    (q : PrimeSpectrum R) (hqne : q ≠ IsLocalRing.closedPoint R)
    (hfin : HasFiniteLengthHomology (twoPeriodicComplex φ ψ hφψ hψφ))
    (K : Submodule R M)
    (hKdef : K = LinearMap.ker (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M))
    (hφK : ∀ x ∈ K, φ x ∈ K) (hψK : ∀ x ∈ K, ψ x ∈ K)
    (hQφψ : K.mapQ K φ hφK * K.mapQ K ψ hψK = 0)
    (hQψφ : K.mapQ K ψ hψK * K.mapQ K φ hφK = 0)
    (hsupp : Module.support R (M ⧸ K) ⊆ {IsLocalRing.closedPoint R, q}) :
    HasFiniteLengthHomology
      (twoPeriodicComplex (K.mapQ K φ hφK) (K.mapQ K ψ hψK) hQφψ hQψφ) := by
  subst hKdef
  set K := LinearMap.ker (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M)
  set φQ := K.mapQ K φ hφK with hφQ
  set ψQ := K.mapQ K ψ hψK with hψQ
  have hmkQφ : K.mkQ ∘ₗ φ = φQ ∘ₗ K.mkQ := mkQ_comp_eq_mapQ_comp_mkQ K φ hφK
  have hmkQψ : K.mkQ ∘ₗ ψ = ψQ ∘ₗ K.mkQ := mkQ_comp_eq_mapQ_comp_mkQ K ψ hψK
  have hbij : Function.Bijective (LocalizedModule.map q.asIdeal.primeCompl K.mkQ) :=
    bijective_localized_map_mkQ_ker q.asIdeal
  have hmemφ : ∀ x : M, ψ x ∈ LinearMap.ker φ := fun x ↦ LinearMap.congr_fun hφψ x
  have hmemψ : ∀ x : M, φ x ∈ LinearMap.ker ψ := fun x ↦ LinearMap.congr_fun hψφ x
  have hmemφQ : ∀ x, ψQ x ∈ LinearMap.ker φQ := fun x ↦ LinearMap.congr_fun hQφψ x
  have hmemψQ : ∀ x, φQ x ∈ LinearMap.ker ψQ := fun x ↦ LinearMap.congr_fun hQψφ x
  intro i
  fin_cases i
  · refine (isFiniteLength_homology_zero_iff φQ ψQ hQφψ hQψφ hmemφQ).mpr ?_
    refine isFiniteLength_quotient_range_codRestrict_of_support_subset_pair φQ ψQ hmemφQ q
      hsupp ?_
    exact exact_map_of_bijective_of_exact _ φ ψ φQ ψQ K.mkQ hmkQφ hmkQψ hbij
      (exact_map_of_isFiniteLength_quotient_range_codRestrict φ ψ hmemφ q hqne
        ((isFiniteLength_homology_zero_iff φ ψ hφψ hψφ hmemφ).mp (hfin 0)))
  · refine (isFiniteLength_homology_one_iff φQ ψQ hQφψ hQψφ hmemψQ).mpr ?_
    refine isFiniteLength_quotient_range_codRestrict_of_support_subset_pair ψQ φQ hmemψQ q
      hsupp ?_
    exact exact_map_of_bijective_of_exact _ ψ φ ψQ φQ K.mkQ hmkQψ hmkQφ hbij
      (exact_map_of_isFiniteLength_quotient_range_codRestrict ψ φ hmemψ q hqne
        ((isFiniteLength_homology_one_iff φ ψ hφψ hψφ hmemψ).mp (hfin 1)))

/-- A two-periodic complex on a module supported only at the closed point has zero
multiplicity: both its terms are the module itself, of finite length. -/
theorem periodicLength_eq_zero_of_support_subset_closedPoint
    [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R M]
    (φ ψ : Module.End R M) (hφψ : φ * ψ = 0) (hψφ : ψ * φ = 0)
    (hsupp : Module.support R M ⊆ {IsLocalRing.closedPoint R}) :
    periodicLength (twoPeriodicComplex φ ψ hφψ hψφ) = 0 := by
  have hfl : IsFiniteLength R M := by
    rcases subsingleton_or_nontrivial M with hM | hM
    · exact IsFiniteLength.of_subsingleton
    · refine isFiniteLength_of_support (Set.Subset.antisymm hsupp fun p hp ↦ ?_)
      rw [Set.mem_singleton_iff] at hp
      exact hp ▸ IsLocalRing.closedPoint_mem_support R M
  rw [periodicLength_eq_length_sub_length _ hfl hfl]
  exact sub_self _

/-- A nonclosed point of the support is minimal in it, when the support sits inside that of a
module whose support has dimension one. -/
theorem minimal_support_of_subset_of_ne [IsLocalRing R]
    {M₀ : Type v} [AddCommGroup M₀] [Module R M₀] (hdim : Module.supportDim R M₀ = 1)
    (hsub : Module.support R M ⊆ Module.support R M₀) {p : PrimeSpectrum R}
    (hp : p ∈ Module.support R M) (hpc : p ≠ IsLocalRing.closedPoint R) :
    Minimal (· ∈ Module.support R M) p := by
  have hset := minimal_support_eq_nonclosed (R := R) (M := M₀) hdim
  rw [Set.ext_iff] at hset
  have hpM₀ : Minimal (· ∈ Module.support R M₀) p := (hset p).mpr ⟨hsub hp, hpc⟩
  exact ⟨hp, fun y hy hyp ↦ hpM₀.2 (hsub hy) hyp⟩

/-- The quotient by the kernel of the localization map at a nonclosed point `q` of the support
has support inside the closed point together with `q`. -/
theorem support_quotient_ker_subset_pair_of_subset [IsNoetherianRing R] [IsLocalRing R]
    [Module.Finite R M] {M₀ : Type v} [AddCommGroup M₀] [Module R M₀]
    (hdim : Module.supportDim R M₀ = 1)
    (hsub : Module.support R M ⊆ Module.support R M₀) {q : PrimeSpectrum R}
    (hq : q ∈ Module.support R M) (hqc : q ≠ IsLocalRing.closedPoint R) :
    Module.support R
        (M ⧸ LinearMap.ker (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M)) ⊆
      {IsLocalRing.closedPoint R, q} := by
  intro p hp
  have hqN : Minimal (· ∈ Module.support R M) q :=
    minimal_support_of_subset_of_ne hdim hsub hq hqc
  have hpq : q ≤ p := support_quotient_ker_subset_zeroLocus q hqN hp
  have hpN : p ∈ Module.support R M :=
    Module.support_subset_of_surjective _ (Submodule.mkQ_surjective _) hp
  by_cases hpc : p = IsLocalRing.closedPoint R
  · exact Set.mem_insert_iff.mpr (Or.inl hpc)
  · exact Set.mem_insert_iff.mpr (Or.inr (le_antisymm
      ((minimal_support_of_subset_of_ne hdim hsub hpN hpc).2 hq hpq) hpq))

/-- The nonclosed points of the support of the kernel of the localization map at `q` are those
of the module with `q` removed. -/
theorem nonclosed_support_ker_eq_diff [IsNoetherianRing R] [IsLocalRing R]
    [Module.Finite R M] {M₀ : Type v} [AddCommGroup M₀] [Module R M₀]
    (hdim : Module.supportDim R M₀ = 1)
    (hsub : Module.support R M ⊆ Module.support R M₀) {q : PrimeSpectrum R}
    (hq : q ∈ Module.support R M) (hqc : q ≠ IsLocalRing.closedPoint R) :
    {p : PrimeSpectrum R |
        p ∈ Module.support R ↥(LinearMap.ker
          (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M)) ∧
        p ≠ IsLocalRing.closedPoint R} =
      {p : PrimeSpectrum R | p ∈ Module.support R M ∧
        p ≠ IsLocalRing.closedPoint R} \ {q} := by
  have hqN : Minimal (· ∈ Module.support R M) q :=
    minimal_support_of_subset_of_ne hdim hsub hq hqc
  ext p
  constructor
  · intro hp
    refine ⟨⟨support_ker_mkLinearMap_subset _ hp.1, hp.2⟩, fun hpq ↦ ?_⟩
    exact notMem_support_ker_mkLinearMap (M := M) q
      (Set.mem_singleton_iff.mp hpq ▸ hp.1)
  · rintro ⟨hp, hpq⟩
    rw [Set.mem_singleton_iff] at hpq
    exact ⟨mem_support_ker_mkLinearMap_of_minimal_ne hqN
      (minimal_support_of_subset_of_ne hdim hsub hp.1 hp.2) (fun hqp ↦ hpq hqp.symm), hp.2⟩

/-- The order of vanishing of a unit of the residue field at a prime, as an integer. This is the
summand of the formula of Tag 02QD. -/
noncomputable def ordOfResidueUnit [IsNoetherianRing R] (p : PrimeSpectrum R)
    [p.asIdeal.IsPrime] [Ring.KrullDimLE 1 (R ⧸ p.asIdeal)]
    (u : (p.asIdeal.ResidueField)ˣ) : ℤ :=
  Multiplicative.toAdd (WithZero.unzero
    (x := Ring.ordFrac (R ⧸ p.asIdeal) (u : p.asIdeal.ResidueField))
    ((Units.isUnit u).map (Ring.ordFrac (R ⧸ p.asIdeal))).ne_zero)

/-- The order of the periodic determinant at a prime, totalised by zero where the data needed to
form it is absent. Totalising makes it a function of the prime alone, which is what the reduction
of Tag 02QD to the two-point-support case consumes. -/
noncomputable def periodicDeterminantOrder [IsNoetherianRing R]
    (φ ψ : Module.End R M) (p : PrimeSpectrum R) : ℤ :=
  open Classical in
  if h : Ring.KrullDimLE 1 (R ⧸ p.asIdeal) ∧
      IsFiniteLength (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M) ∧
      Function.Exact (LocalizedModule.map p.asIdeal.primeCompl φ)
        (LocalizedModule.map p.asIdeal.primeCompl ψ) ∧
      Function.Exact (LocalizedModule.map p.asIdeal.primeCompl ψ)
        (LocalizedModule.map p.asIdeal.primeCompl φ) then
    @ordOfResidueUnit R _ _ p p.isPrime h.1
      (periodicDeterminant (LocalizedModule.map p.asIdeal.primeCompl φ)
        (LocalizedModule.map p.asIdeal.primeCompl ψ) h.2.2.1 h.2.2.2 h.2.1)
  else 0

/-- Where the data needed to form the periodic determinant is present, the totalised order is
the order of that determinant. -/
theorem periodicDeterminantOrder_eq [IsNoetherianRing R]
    (φ ψ : Module.End R M) (p : PrimeSpectrum R)
    (h₁ : Ring.KrullDimLE 1 (R ⧸ p.asIdeal))
    (h₂ : IsFiniteLength (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl M))
    (h₃ : Function.Exact (LocalizedModule.map p.asIdeal.primeCompl φ)
      (LocalizedModule.map p.asIdeal.primeCompl ψ))
    (h₄ : Function.Exact (LocalizedModule.map p.asIdeal.primeCompl ψ)
      (LocalizedModule.map p.asIdeal.primeCompl φ)) :
    periodicDeterminantOrder φ ψ p = @ordOfResidueUnit R _ _ p p.isPrime h₁
      (periodicDeterminant (LocalizedModule.map p.asIdeal.primeCompl φ)
        (LocalizedModule.map p.asIdeal.primeCompl ψ) h₃ h₄ h₂) := by
  rw [periodicDeterminantOrder, dite_eq_left ⟨h₁, h₂, h₃, h₄⟩]

/-- In support dimension one the minimal points of the support are its nonclosed points, so a
sum over the former is a sum over the latter. -/
theorem finsum_minimal_support_eq_finsum_nonclosed [IsLocalRing R]
    (hdim : Module.supportDim R M = 1) (f : PrimeSpectrum R → ℤ) :
    ∑ᶠ q : {q : PrimeSpectrum R | Minimal (· ∈ Module.support R M) q}, f q =
      ∑ᶠ p : {p : PrimeSpectrum R | p ∈ Module.support R M ∧
        p ≠ IsLocalRing.closedPoint R}, f p := by
  rw [finsum_set_coe_eq_finsum_mem, finsum_set_coe_eq_finsum_mem,
    minimal_support_eq_nonclosed hdim]

/-- Exactness of a pair of endomorphisms transports along a linear equivalence intertwining
them with another pair. Unlike the version for an underlying `R`-linear map, this is symmetric
in the two sides, which is what the transport of the periodic determinant needs. -/
theorem exact_iff_of_linearEquiv_comm {S : Type u} [CommRing S] {A B : Type v}
    [AddCommGroup A] [Module S A] [AddCommGroup B] [Module S B]
    (f g : A →ₗ[S] A) (f' g' : B →ₗ[S] B) (e : A ≃ₗ[S] B)
    (hf : ∀ x, e (f x) = f' (e x)) (hg : ∀ x, e (g x) = g' (e x)) :
    Function.Exact f g ↔ Function.Exact f' g' :=
  (Function.Exact.iff_of_ladder_linearEquiv (e₁ := e) (e₂ := e) (e₃ := e)
    (LinearMap.ext fun x ↦ (hf x).symm) (LinearMap.ext fun x ↦ (hg x).symm)).symm

/-- The order of the periodic determinant is unchanged by a linear map intertwining both
differentials whose localization at the prime is bijective. Applied to `Submodule.subtype` it
compares a stable submodule with the module, and to `Submodule.mkQ` the module with its
quotient. -/
theorem periodicDeterminantOrder_eq_of_bijective [IsNoetherianRing R]
    {N : Type v} [AddCommGroup N] [Module R N]
    (φ ψ : Module.End R M) (φ' ψ' : Module.End R N) (u : M →ₗ[R] N)
    (hφ : u ∘ₗ φ = φ' ∘ₗ u) (hψ : u ∘ₗ ψ = ψ' ∘ₗ u) (p : PrimeSpectrum R)
    (hbij : Function.Bijective (LocalizedModule.map p.asIdeal.primeCompl u)) :
    periodicDeterminantOrder φ ψ p = periodicDeterminantOrder φ' ψ' p := by
  set e := LinearEquiv.ofBijective (LocalizedModule.map p.asIdeal.primeCompl u) hbij
  have hcomm : ∀ (α : Module.End R M) (α' : Module.End R N), u ∘ₗ α = α' ∘ₗ u →
      ∀ x, e (LocalizedModule.map p.asIdeal.primeCompl α x) =
        LocalizedModule.map p.asIdeal.primeCompl α' (e x) := by
    intro α α' hα x
    induction x using LocalizedModule.induction_on with
    | h a s =>
        change LocalizedModule.map p.asIdeal.primeCompl u
            (LocalizedModule.map p.asIdeal.primeCompl α (LocalizedModule.mk a s)) =
          LocalizedModule.map p.asIdeal.primeCompl α'
            (LocalizedModule.map p.asIdeal.primeCompl u (LocalizedModule.mk a s))
        simp only [LocalizedModule.map_mk]
        exact congrArg (fun m ↦ LocalizedModule.mk m s) (LinearMap.congr_fun hα a)
  have hcφ := hcomm φ φ' hφ
  have hcψ := hcomm ψ ψ' hψ
  have hex1 := exact_iff_of_linearEquiv_comm _ _ _ _ e hcφ hcψ
  have hex2 := exact_iff_of_linearEquiv_comm _ _ _ _ e hcψ hcφ
  rw [periodicDeterminantOrder, periodicDeterminantOrder]
  split_ifs with h h' h'
  · congr 1
    exact periodicDeterminant_eq_of_linearEquiv _ _ h.2.2.1 h.2.2.2 _ _ h'.2.2.1 h'.2.2.2 e
      (LinearMap.ext hcφ) (LinearMap.ext hcψ) h.2.1 h'.2.1
  · exact absurd ⟨h.1, e.isFiniteLength h.2.1, hex1.mp h.2.2.1, hex2.mp h.2.2.2⟩ h'
  · exact absurd ⟨h'.1, e.symm.isFiniteLength h'.2.1, hex1.mpr h'.2.2.1, hex2.mpr h'.2.2.2⟩ h
  · rfl

/-- If a module has no nonclosed point in its support, both sides of the formula of Tag 02QD
vanish. -/
private theorem neg_periodicLength_eq_finsum_of_nonclosed_eq_empty
    [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R M]
    (φ ψ : Module.End R M) (hφψ : φ * ψ = 0) (hψφ : ψ * φ = 0)
    (hNC : {p : PrimeSpectrum R | p ∈ Module.support R M ∧
      p ≠ IsLocalRing.closedPoint R} = ∅) :
    -periodicLength (twoPeriodicComplex φ ψ hφψ hψφ) =
      ∑ᶠ p : {p : PrimeSpectrum R | p ∈ Module.support R M ∧
        p ≠ IsLocalRing.closedPoint R}, periodicDeterminantOrder φ ψ p := by
  have hsupp : Module.support R M ⊆ {IsLocalRing.closedPoint R} := fun p hp ↦ by
    by_contra hpc
    exact (hNC ▸ (⟨hp, hpc⟩ : p ∈ {p : PrimeSpectrum R | p ∈ Module.support R M ∧
      p ≠ IsLocalRing.closedPoint R}) : p ∈ (∅ : Set (PrimeSpectrum R)))
  rw [periodicLength_eq_zero_of_support_subset_closedPoint φ ψ hφψ hψφ hsupp,
    finsum_set_coe_eq_finsum_mem, hNC, finsum_mem_empty, neg_zero]

/-- **The reduction of Tag 02QD to the two-point-support case.** Let `M₀` be a finite module over
a Noetherian local ring whose support has dimension one. If every two-periodic complex whose
support meets only the closed point and one further prime `p` has negated multiplicity the order
of its own periodic determinant at `p`, then for every finite module with support inside that of
`M₀` the negated multiplicity is the sum of those orders over the nonclosed points of its
support. The induction is on the number of those points, splitting off one at a time along the
kernel of the localization map there and transporting the determinant order across the two
resulting comparisons. -/
theorem neg_periodicLength_eq_finsum_nonclosed_of_twoPoint
    [IsNoetherianRing R] [IsLocalRing R]
    {M₀ : Type v} [AddCommGroup M₀] [Module R M₀] [Module.Finite R M₀]
    (hdim : Module.supportDim R M₀ = 1)
    (hbase : ∀ (N : Type v) [AddCommGroup N] [Module R N] [Module.Finite R N]
      (φ ψ : Module.End R N) (hφψ : φ * ψ = 0) (hψφ : ψ * φ = 0) (p : PrimeSpectrum R),
      HasFiniteLengthHomology (twoPeriodicComplex φ ψ hφψ hψφ) →
      Module.support R N ⊆ {IsLocalRing.closedPoint R, p} →
      p ≠ IsLocalRing.closedPoint R → p ∈ Module.support R M₀ →
      -periodicLength (twoPeriodicComplex φ ψ hφψ hψφ) = periodicDeterminantOrder φ ψ p)
    (N : Type v) [AddCommGroup N] [Module R N] [Module.Finite R N]
    (φ ψ : Module.End R N) (hφψ : φ * ψ = 0) (hψφ : ψ * φ = 0)
    (hfin : HasFiniteLengthHomology (twoPeriodicComplex φ ψ hφψ hψφ))
    (hsub : Module.support R N ⊆ Module.support R M₀) :
    -periodicLength (twoPeriodicComplex φ ψ hφψ hψφ) =
      ∑ᶠ p : {p : PrimeSpectrum R | p ∈ Module.support R N ∧
        p ≠ IsLocalRing.closedPoint R}, periodicDeterminantOrder φ ψ p := by
  have hNCM₀fin : {p : PrimeSpectrum R | p ∈ Module.support R M₀ ∧
      p ≠ IsLocalRing.closedPoint R}.Finite :=
    minimal_support_eq_nonclosed (R := R) (M := M₀) hdim ▸
      finite_minimal_support (R := R) (M := M₀)
  suffices H : ∀ n : ℕ, ∀ (N : Type v) [AddCommGroup N] [Module R N] [Module.Finite R N]
      (φ ψ : Module.End R N) (hφψ : φ * ψ = 0) (hψφ : ψ * φ = 0),
      HasFiniteLengthHomology (twoPeriodicComplex φ ψ hφψ hψφ) →
      Module.support R N ⊆ Module.support R M₀ →
      {p : PrimeSpectrum R | p ∈ Module.support R N ∧
        p ≠ IsLocalRing.closedPoint R}.ncard ≤ n →
      -periodicLength (twoPeriodicComplex φ ψ hφψ hψφ) =
        ∑ᶠ p : {p : PrimeSpectrum R | p ∈ Module.support R N ∧
          p ≠ IsLocalRing.closedPoint R}, periodicDeterminantOrder φ ψ p by
    exact H _ N φ ψ hφψ hψφ hfin hsub le_rfl
  intro n
  induction n with
  | zero =>
      intro N _ _ _ φ ψ hφψ hψφ hfinN hsubN hcard
      have hNCfin : {p : PrimeSpectrum R | p ∈ Module.support R N ∧
          p ≠ IsLocalRing.closedPoint R}.Finite :=
        hNCM₀fin.subset fun p hp ↦ ⟨hsubN hp.1, hp.2⟩
      exact neg_periodicLength_eq_finsum_of_nonclosed_eq_empty φ ψ hφψ hψφ
        ((Set.ncard_eq_zero hNCfin).mp (Nat.le_zero.mp hcard))
  | succ n ih =>
      intro N _ _ _ φ ψ hφψ hψφ hfinN hsubN hcard
      have hNCfin : {p : PrimeSpectrum R | p ∈ Module.support R N ∧
          p ≠ IsLocalRing.closedPoint R}.Finite :=
        hNCM₀fin.subset fun p hp ↦ ⟨hsubN hp.1, hp.2⟩
      by_cases hNC : {p : PrimeSpectrum R | p ∈ Module.support R N ∧
          p ≠ IsLocalRing.closedPoint R} = ∅
      · exact neg_periodicLength_eq_finsum_of_nonclosed_eq_empty φ ψ hφψ hψφ hNC
      · obtain ⟨q, hq⟩ := Set.nonempty_iff_ne_empty.mpr hNC
        have hφK : ∀ x ∈ LinearMap.ker
            (LocalizedModule.mkLinearMap q.asIdeal.primeCompl N), φ x ∈ LinearMap.ker
            (LocalizedModule.mkLinearMap q.asIdeal.primeCompl N) :=
          fun x hx ↦ mem_ker_mkLinearMap_of_mem _ φ x hx
        have hψK : ∀ x ∈ LinearMap.ker
            (LocalizedModule.mkLinearMap q.asIdeal.primeCompl N), ψ x ∈ LinearMap.ker
            (LocalizedModule.mkLinearMap q.asIdeal.primeCompl N) :=
          fun x hx ↦ mem_ker_mkLinearMap_of_mem _ ψ x hx
        have hsuppQ := support_quotient_ker_subset_pair_of_subset hdim hsubN hq.1 hq.2
        have hQφψ := mapQ_mul_mapQ_eq_zero φ ψ hφψ hφK hψK
        have hQψφ := mapQ_mul_mapQ_eq_zero ψ φ hψφ hψK hφK
        have hSφψ := restrict_mul_restrict_eq_zero φ ψ hφψ hφK hψK
        have hSψφ := restrict_mul_restrict_eq_zero ψ φ hψφ hψK hφK
        have hfinQ := hasFiniteLengthHomology_mapQ_ker φ ψ hφψ hψφ q hq.2 hfinN _ rfl
          hφK hψK hQφψ hQψφ hsuppQ
        have hfinK := hasFiniteLengthHomology_restrict_of_stable φ ψ hφψ hψφ hφK hψK
          hSφψ hSψφ hQφψ hQψφ hfinN hfinQ
        have hadd := periodicLength_add_of_stable φ ψ hφψ hψφ hφK hψK hSφψ hSψφ hQφψ hQψφ
          hfinK hfinQ
        have hQ := hbase _ _ _ hQφψ hQψφ q hfinQ hsuppQ hq.2 (hsubN hq.1)
        -- transport the determinant order across `N → N ⧸ K`
        have hmkQφ := mkQ_comp_eq_mapQ_comp_mkQ _ φ hφK
        have hmkQψ := mkQ_comp_eq_mapQ_comp_mkQ _ ψ hψK
        have htQ := periodicDeterminantOrder_eq_of_bijective φ ψ _ _ _ hmkQφ hmkQψ q
          (bijective_localized_map_mkQ_ker (M := N) q.asIdeal)
        -- transport the determinant order across `K → N`, inside the sum
        have hNCK := nonclosed_support_ker_eq_diff hdim hsubN hq.1 hq.2
        have hcardK : {p : PrimeSpectrum R | p ∈ Module.support R
            ↥(LinearMap.ker (LocalizedModule.mkLinearMap q.asIdeal.primeCompl N)) ∧
            p ≠ IsLocalRing.closedPoint R}.ncard ≤ n := by
          rw [hNCK]
          have hss : ({p : PrimeSpectrum R | p ∈ Module.support R N ∧
              p ≠ IsLocalRing.closedPoint R} \ {q} : Set (PrimeSpectrum R)) ⊂
              {p : PrimeSpectrum R | p ∈ Module.support R N ∧
                p ≠ IsLocalRing.closedPoint R} :=
            ⟨Set.sdiff_subset, fun hsup ↦ (hsup hq).2 rfl⟩
          have hlt := Set.ncard_lt_ncard hss hNCfin
          omega
        have hIH := ih _ (φ.restrict hφK) (ψ.restrict hψK) hSφψ hSψφ hfinK
          ((support_ker_mkLinearMap_subset _).trans hsubN) hcardK
        have htK : ∀ p : {p : PrimeSpectrum R | p ∈ Module.support R
            ↥(LinearMap.ker (LocalizedModule.mkLinearMap q.asIdeal.primeCompl N)) ∧
            p ≠ IsLocalRing.closedPoint R},
            periodicDeterminantOrder (φ.restrict hφK) (ψ.restrict hψK) p.1 =
              periodicDeterminantOrder φ ψ p.1 := by
          intro p
          have hpmem : p.1 ∈ {p : PrimeSpectrum R | p ∈ Module.support R N ∧
              p ≠ IsLocalRing.closedPoint R} \ {q} := hNCK ▸ p.2
          refine periodicDeterminantOrder_eq_of_bijective _ _ φ ψ _
            (LinearMap.subtype_comp_restrict hφK) (LinearMap.subtype_comp_restrict hψK) p.1 ?_
          exact bijective_localized_map_subtype_ker
            (minimal_support_of_subset_of_ne hdim hsubN hq.1 hq.2)
            (minimal_support_of_subset_of_ne hdim hsubN hpmem.1.1 hpmem.1.2)
            (fun hqp ↦ (Set.mem_singleton_iff.mp (hqp ▸ rfl : p.1 ∈ ({q} : Set _)) ▸
              hpmem.2) (Set.mem_singleton_iff.mpr rfl))
        rw [finsum_congr htK] at hIH
        have hsum : ∑ᶠ p : {p : PrimeSpectrum R | p ∈ Module.support R
            ↥(LinearMap.ker (LocalizedModule.mkLinearMap q.asIdeal.primeCompl N)) ∧
            p ≠ IsLocalRing.closedPoint R}, periodicDeterminantOrder φ ψ p.1 =
            ∑ᶠ p : ({p : PrimeSpectrum R | p ∈ Module.support R N ∧
              p ≠ IsLocalRing.closedPoint R} \ {q} : Set (PrimeSpectrum R)),
              periodicDeterminantOrder φ ψ p.1 := by
          rw [finsum_set_coe_eq_finsum_mem, finsum_set_coe_eq_finsum_mem, hNCK]
        rw [finsum_subtype_eq_add_finsum_subtype_diff
          (periodicDeterminantOrder φ ψ) hNCfin hq, ← hsum, ← hIH, htQ]
        omega

end Module.FiniteLength

end
