module

import Mathlib.Algebra.Module.LocalizedModule.Exact

public import StacksFrontier.Algebra.Homology.Resolution.Syzygies
public import StacksFrontier.RingTheory.Flat.FlatAtPointCriteria
public import StacksFrontier.RingTheory.Flat.LocalCriteria
public import StacksFrontier.RingTheory.RegularLocalRing.MvPolynomialFiber
import StacksFrontier.RingTheory.Flat.ShortExact
import StacksFrontier.RingTheory.RegularLocalRing.GlobalDimension
public import StacksFrontier.RingTheory.Sequence.RegularLocus
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The syzygies of a resolution over a polynomial ring are free near a point of flatness

Let `R` be a Noetherian ring, let `P = R[x_1, …, x_n]`, let `M` be a finitely presented `P`-module
and let `𝔮` be a prime of `P` such that `M_𝔮` is flat over `R`. This file proves that `M` has a
resolution `⋯ → F_1 → F_0 → M → 0` by finite free `P`-modules whose `n`-th syzygy
`K_n = ker(F_{n-1} → F_{n-2})` becomes *finite free* after inverting a single element `g ∉ 𝔮`.

This is part of the proof of openness of the flat locus [StacksProject 00RC]. The map `R → P` is
flat and every fibre `P ⊗_R κ(𝔭)` is the polynomial ring `κ(𝔭)[x_1, …, x_n]`, whose local rings
are regular of dimension at most `n`. Over `P_𝔮` the syzygies of a finite free resolution of `M`
are flat over `R` ([StacksProject 00HM]), so the resolution stays exact modulo `𝔭 = R ∩ 𝔮`, the
`n`-th syzygy becomes free over the fibre ring `P_𝔮/𝔭P_𝔮`, and hence `(K_n)_𝔮` is free over
`P_𝔮` ([StacksProject 00MH]); a finitely presented module free at a prime is free on a basic open
neighbourhood of it.

## Main results

* `Module.free_localizedModule_atPrime_of_forall_shortExact`: for a family of short exact
  sequences `0 → K (i+1) → F i → K i → 0` of finite free modules over a flat Noetherian algebra
  `P` whose fibre ring at `𝔮` is regular local of dimension at most `n`, the module `(K n)_𝔮` is
  free if `(K 0)_𝔮` is flat over the base.
* `Module.exists_away_free_syzygy_of_flat_atPrime_mvPolynomial`: the conclusion for
  `P = R[x_1, …, x_n]` and a finite free resolution of `M`.
* `Ideal.localizationFiberPointRingEquiv`: the fibre ring `S_𝔮/𝔭S_𝔮` is the local ring of the
  fibre `κ(𝔭) ⊗_R S` at the point cut out by `𝔮`.
* `Module.Flat.of_forall_shortExact`: dimension shifting for flatness.
* `IsRegularLocalRing.free_of_forall_shortExact`: the `n`-th syzygy over a regular local ring of
  dimension at most `n` is free.

The file also contains lemmas on finitely generated submodules and their localizations:
`Submodule.exists_fg_le_localized_eq` and `Submodule.exists_fg_le_forall_localized_eq` produce one
finitely generated submodule with prescribed localizations,
`Submodule.exists_smul_mem_of_localized_le` turns a containment of localizations into a
denominator, `Submodule.localized_liftQ_injective` tests injectivity of a localized quotient
presentation, `Submodule.fg_localized_ker` makes the localized relation module finite, and
`Module.flat_localizations_injective` together with
`Module.eq_zero_of_forall_exists_smul_eq_zero_of_flat` says that a detecting family of
localizations detects the elements of a flat module.

## Implementation notes

`Module.Flat.of_forall_shortExact` and `IsRegularLocalRing.free_of_forall_shortExact` take the
short exact sequences as two families of maps rather than as a family of `ShortComplex`es, matching
the syzygies `FreeResolutionData.syzygy` of a resolution, for which `K 0` is the module itself.

## References

* [StacksProject 00HM](https://stacks.math.columbia.edu/tag/00HM)
* [StacksProject 00LP](https://stacks.math.columbia.edu/tag/00LP)
* [StacksProject 00MH](https://stacks.math.columbia.edu/tag/00MH)
* [StacksProject 00RC](https://stacks.math.columbia.edu/tag/00RC)

## Tags

syzygy, free resolution, flat module, flat locus, polynomial ring, fibre, regular local ring,
global dimension, dimension shifting
-/

@[expose] public section

open TensorProduct

universe u

/-- **Injectivity of a map reduced modulo an ideal, read on elements.** A map `u : X → Y` of
`A`-modules becomes injective after `(A/J) ⊗[A] -` exactly when `u x ∈ JY` forces `x ∈ JX`. -/
theorem LinearMap.injective_lTensor_quotient_iff {A : Type*} [CommRing A] (J : Ideal A)
    {X Y : Type*} [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y] (u : X →ₗ[A] Y) :
    Function.Injective (LinearMap.lTensor (A ⧸ J) u) ↔
      ∀ x : X, u x ∈ J • (⊤ : Submodule A Y) → x ∈ J • (⊤ : Submodule A X) := by
  constructor
  · intro h x hx
    refine (TensorProduct.one_tmul_eq_zero_iff_mem_smul_top J x).mp (h ?_)
    rw [LinearMap.lTensor_tmul, map_zero]
    exact (TensorProduct.one_tmul_eq_zero_iff_mem_smul_top J _).mpr hx
  · intro h
    rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨x, rfl⟩ := TensorProduct.exists_one_tmul J t
    rw [LinearMap.lTensor_tmul] at ht
    exact (TensorProduct.one_tmul_eq_zero_iff_mem_smul_top J x).mpr
      (h x ((TensorProduct.one_tmul_eq_zero_iff_mem_smul_top J _).mp ht))

/-- For an `R`-algebra `A` and an ideal `I` of `R`, the `R`-submodule `IZ` of an `A`-module `Z` and
the `A`-submodule `(IA)Z` have the same elements. -/
@[ega "0 1.0.4" "JM = (BJ)M"]
theorem Ideal.mem_map_smul_top_iff_mem_smul_top {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (I : Ideal R) {Z : Type*} [AddCommGroup Z] [Module R Z] [Module A Z]
    [IsScalarTower R A Z] (z : Z) :
    z ∈ Ideal.map (algebraMap R A) I • (⊤ : Submodule A Z) ↔ z ∈ I • (⊤ : Submodule R Z) := by
  rw [← Submodule.restrictScalars_mem R (Ideal.map (algebraMap R A) I • (⊤ : Submodule A Z)) z,
    Ideal.smul_restrictScalars, Submodule.restrictScalars_top]

/-- **The fibre of an `A`-module over an ideal of the base may be computed over the base.** For an
`R`-algebra `A` and an ideal `I` of `R`, a map of `A`-modules becomes injective after
`(A/IA) ⊗[A] -` exactly when it does after `(R/I) ⊗[R] -`. -/
theorem LinearMap.injective_baseChange_quotient_iff {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (I : Ideal R) {X Y : Type*} [AddCommGroup X] [Module R X] [Module A X]
    [IsScalarTower R A X]
    [AddCommGroup Y] [Module R Y] [Module A Y] [IsScalarTower R A Y] (u : X →ₗ[A] Y) :
    Function.Injective (LinearMap.baseChange (A ⧸ Ideal.map (algebraMap R A) I) u) ↔
      Function.Injective (LinearMap.lTensor (R ⧸ I) (u.restrictScalars R)) := by
  rw [LinearMap.baseChange_eq_lTensor, LinearMap.injective_lTensor_quotient_iff (X := X)
      (Y := Y), LinearMap.injective_lTensor_quotient_iff (A := R) (X := X) (Y := Y)]
  exact forall_congr' fun x =>
    imp_congr (Ideal.mem_map_smul_top_iff_mem_smul_top I _)
      (Ideal.mem_map_smul_top_iff_mem_smul_top I _)

namespace Ideal
open Stacks.RegularSequence.FibrewiseLocus

/-! ### The fibre ring `S_𝔮/𝔭S_𝔮` is the local ring of the fibre `κ(𝔭) ⊗_R S` -/

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The fibre ring `S_𝔮/𝔭S_𝔮` does not change when the prime is rewritten: an equality of primes
of `S` gives an equality of the ideals the localization is divided by. -/
def fiberRingEquivOfEq (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {r q : Ideal S} [r.IsPrime] [q.IsPrime] (h : r = q) :
    (Localization.AtPrime r ⧸
        ((q.under R).map (algebraMap R S)).map (algebraMap S (Localization.AtPrime r))) ≃+*
      (Localization.AtPrime q ⧸ (q.under R).map (algebraMap R (Localization.AtPrime q))) := by
  subst h
  exact Ideal.quotEquivOfEq (by rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq])

/-- **The fibre ring at `𝔮` is the local ring of the fibre at `q̄`.** For a prime `𝔮` of `S` with
`𝔭 = R ∩ 𝔮`, the localization of the fibre `κ(𝔭) ⊗_R S` at the point `q̄` corresponding to `𝔮` is
the fibre ring `S_𝔮/𝔭S_𝔮`. -/
noncomputable def localizationFiberPointRingEquiv (R : Type*) {S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (q : Ideal S) [q.IsPrime] :
    Localization.AtPrime (fiberPoint R q).asIdeal ≃+*
      (Localization.AtPrime q ⧸ (q.under R).map (algebraMap R (Localization.AtPrime q))) :=
  (Ideal.Fiber.algEquivAux₂ (R := R) (S := S) (p := q.under R)
      (fiberPoint R q).asIdeal).toRingEquiv.trans
    (fiberRingEquivOfEq R (by exact comap_includeRight_fiberPoint R q))

/-! ### The local homomorphism `R_𝔭 → S_𝔮` -/

attribute [local instance] algebraLocalizationAtPrimeUnder isScalarTower_localizationAtPrimeUnder
  isLocalHom_algebraMap_localizationAtPrimeUnder

/-! ### The fibre ring of a polynomial ring is regular local of dimension at most `n` -/

/-- The fibre ring of `R → R[x_1, …, x_n]` at a prime is a regular local ring. -/
theorem isRegularLocalRing_fiberRing_mvPolynomial {R : Type*} [CommRing R] {n : ℕ}
    (q : Ideal (MvPolynomial (Fin n) R)) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q ⧸
      (q.under R).map (algebraMap R (Localization.AtPrime q))) :=
  have := (q.under R).isRegularLocalRing_localization_fiber_mvPolynomial (Fin n)
    (fiberPoint R q).asIdeal
  IsRegularLocalRing.of_ringEquiv (localizationFiberPointRingEquiv R q)

/-- The fibre ring of `R → R[x_1, …, x_n]` at a prime has Krull dimension at most `n`. -/
theorem ringKrullDim_fiberRing_mvPolynomial_le {R : Type*} [CommRing R] {n : ℕ}
    (q : Ideal (MvPolynomial (Fin n) R)) [q.IsPrime] :
    ringKrullDim (Localization.AtPrime q ⧸
        (q.under R).map (algebraMap R (Localization.AtPrime q))) ≤ (n : WithBot ℕ∞) := by
  rw [← ringKrullDim_eq_of_ringEquiv (localizationFiberPointRingEquiv R q)]
  exact (q.under R).ringKrullDim_localization_fiber_mvPolynomial_le (fiberPoint R q).asIdeal

end Ideal

/-! ### Localizing a module -/

/-- **A localization of a free module is free.** If `g : M →ₗ[R] M'` realizes `M'` as the
localization of `M` at `S`, `Rₛ` is the localization of `R` at `S` and `M` is free over `R`, then
`M'` is free over `Rₛ`. -/
theorem Module.Free.of_isLocalizedModule {R : Type*} [CommRing R] (S : Submonoid R)
    {M M' Rₛ : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [CommRing Rₛ] [Algebra R Rₛ] [IsLocalization S Rₛ] [Module Rₛ M'] [IsScalarTower R Rₛ M']
    (g : M →ₗ[R] M') [IsLocalizedModule S g] [Module.Free R M] : Module.Free Rₛ M' :=
  Module.Free.of_basis ((Module.Free.chooseBasis R M).ofIsLocalizedModule Rₛ S g)

/-! ### Finitely generated relations and their localizations -/

/-- **Finitely many relations suffice whenever their localization is finitely generated.** If the
localization of `K ≤ F` at `T` is finitely generated, some finitely generated `L ≤ K` already has
the same localization. -/
theorem Submodule.exists_fg_le_localized_eq
    {S F : Type*} [CommRing S] [AddCommGroup F] [Module S F]
    (T : Submonoid S) (K : Submodule S F) (hK : (K.localized T).FG) :
    ∃ L ≤ K, L.FG ∧ L.localized T = K.localized T := by
  classical
  let f := LocalizedModule.mkLinearMap T F
  rw [Submodule.localized, Submodule.localized'_eq_span,
    Submodule.fg_span_iff_fg_span_finset_subset] at hK
  obtain ⟨t, ht, heq⟩ := hK
  choose k hk he using fun x : t ↦ ht x.property
  let L := Submodule.span S (Set.range k)
  refine ⟨L, Submodule.span_le.mpr ?_, Submodule.fg_span (Set.finite_range k), ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact hk x
  · change (Submodule.span S (Set.range k)).localized' (Localization T) T f = _
    rw [Submodule.localized'_span, Submodule.localized, Submodule.localized'_eq_span, heq,
      ← Set.range_comp, show f ∘ k = Subtype.val from funext he, Subtype.range_coe]

/-- **Equality of localized submodules supplies a denominator for each relation.** If the
localization of `K` at `T` is contained in that of `L`, every `x ∈ K` has a multiple `t • x ∈ L`
by some `t ∈ T`. -/
theorem Submodule.exists_smul_mem_of_localized_le
    {S F : Type*} [CommRing S] [AddCommGroup F] [Module S F]
    (T : Submonoid S) {K L : Submodule S F}
    (h : K.localized T ≤ L.localized T) {x : F} (hx : x ∈ K) :
    ∃ t : T, (t : S) • x ∈ L := by
  have hm : LocalizedModule.mk x (1 : T) ∈ K.localized T :=
    ⟨x, hx, 1, (IsLocalizedModule.mk_eq_mk' _ _).symm⟩
  obtain ⟨y, hy, s, hs⟩ := h hm
  rw [← IsLocalizedModule.mk_eq_mk', LocalizedModule.mk_eq] at hs
  obtain ⟨t, ht⟩ := hs
  refine ⟨t * s, ?_⟩
  have ht' : (t : S) • y = ((t * s : T) : S) • x := by
    simpa only [one_smul, Submonoid.smul_def, Submonoid.coe_mul, mul_smul] using ht
  rw [← ht']
  exact L.smul_mem _ hy

/-- **A finite family of finitely generated localizations is realized by one finite submodule.**
If the localizations of `K ≤ F` at finitely many submonoids `T i` are finitely generated, some
finitely generated `L ≤ K` has the same localizations. -/
theorem Submodule.exists_fg_le_forall_localized_eq
    {S F ι : Type*} [CommRing S] [AddCommGroup F] [Module S F] [Finite ι]
    (T : ι → Submonoid S) (K : Submodule S F)
    (hK : ∀ i, (K.localized (T i)).FG) :
    ∃ L ≤ K, L.FG ∧ ∀ i, L.localized (T i) = K.localized (T i) := by
  choose L hle hfg heq using fun i ↦ Submodule.exists_fg_le_localized_eq (T i) K (hK i)
  refine ⟨⨆ i, L i, iSup_le hle, Submodule.fg_iSup L hfg, fun i ↦ ?_⟩
  apply le_antisymm
  · exact (Submodule.localized'gi _ _ _).gc.monotone_l (iSup_le hle)
  · rw [← heq i]
    exact (Submodule.localized'gi _ _ _).gc.monotone_l (le_iSup L i)

/-- **A localized quotient presentation is injective when all its remaining relations vanish.**
For `f : F →ₗ[S] M` and `L ≤ ker f`, the localization of the induced map `F ⧸ L → M` at `T` is
injective as soon as every element of `ker f` dies in `(F ⧸ L)` localized at `T`. -/
theorem Submodule.localized_liftQ_injective
    {S F M : Type*} [CommRing S] [AddCommGroup F] [Module S F]
    [AddCommGroup M] [Module S M] (T : Submonoid S)
    (f : F →ₗ[S] M) (L : Submodule S F) (hL : L ≤ LinearMap.ker f)
    (h : ∀ x ∈ LinearMap.ker f,
      LocalizedModule.mk (L.mkQ x) (1 : T) = 0) :
    Function.Injective (LocalizedModule.map T (L.liftQ f hL)) := by
  apply IsLocalizedModule.injective_of_map_zero T (LocalizedModule.mkLinearMap T (F ⧸ L))
    (g := (LocalizedModule.map T (L.liftQ f hL)).restrictScalars S)
  intro y hy
  obtain ⟨x, rfl⟩ := L.mkQ_surjective y
  have hy' : LocalizedModule.mk (f x) (1 : T) = 0 := by
    simpa only [LinearMap.restrictScalars_apply, LocalizedModule.mkLinearMap_apply,
      LocalizedModule.map_mk, Submodule.liftQ_apply, Submodule.mkQ_apply] using hy
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff T
    (LocalizedModule.mkLinearMap T M)).mp hy'
  have hx : (t : S) • x ∈ LinearMap.ker f := by
    simpa only [LinearMap.mem_ker, map_smul, Submonoid.smul_def] using ht
  have hz := h _ hx
  apply (IsLocalizedModule.smul_inj (LocalizedModule.mkLinearMap T (F ⧸ L)) t _ 0).mp
  simpa only [Submonoid.smul_def, smul_zero, map_smul,
    LocalizedModule.smul'_mk, LocalizedModule.mkLinearMap_apply] using hz

/-- **A finite family of localizations that jointly detects elements of a ring also jointly
detects elements of any flat module over that ring.** -/
theorem Module.flat_localizations_injective
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Flat R M] {ι : Type*} [Finite ι] (S : ι → Submonoid R)
    (h : Function.Injective (fun r : R ↦ fun i : ι ↦
      algebraMap R (Localization (S i)) r)) :
    Function.Injective (fun m : M ↦ fun i : ι ↦ LocalizedModule.mk m (1 : S i)) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let A := ∀ i : ι, Localization (S i)
  have hA : Function.Injective (algebraMap R A) := h
  have : FaithfulSMul R A :=
    (faithfulSMul_iff_algebraMap_injective R A).mpr hA
  intro x y hxy
  apply Module.Flat.tensorProduct_mk_injective R M A
  apply (TensorProduct.piLeft R M (fun i : ι ↦ Localization (S i))).injective
  ext i
  have hi := congrFun hxy i
  change (1 : Localization (S i)) ⊗ₜ[R] x =
    (1 : Localization (S i)) ⊗ₜ[R] y
  simpa only [LocalizedModule.equivTensorProduct_apply_mk,
    Localization.mk_one] using
    congrArg (LocalizedModule.equivTensorProduct (S i) M) hi

/-- **Flatness and a detecting family turn locally vanishing elements into zero.** An element of a
flat module annihilated by some member of each monoid of a detecting family is zero. -/
theorem Module.eq_zero_of_forall_exists_smul_eq_zero_of_flat
    {R N ι : Type*} [CommRing R] [AddCommGroup N] [Module R N]
    [Module.Flat R N] [Finite ι] (T : ι → Submonoid R)
    (hT : Function.Injective (fun r : R ↦ fun i : ι ↦
      algebraMap R (Localization (T i)) r))
    (x : N) (hx : ∀ i, ∃ t : T i, (t : R) • x = 0) : x = 0 := by
  apply Module.flat_localizations_injective T hT
  funext i
  change LocalizedModule.mk x (1 : T i) = LocalizedModule.mk 0 (1 : T i)
  rw [LocalizedModule.zero_mk]
  exact (IsLocalizedModule.eq_zero_iff (T i)
    (LocalizedModule.mkLinearMap (T i) N)).mpr (hx i)

/-- **Local finite presentation makes the module of localized relations finite.** If `F` is
finitely presented over `S`, `f : F →ₗ[S] M` is surjective and `M` localized at `T` is finitely
presented, then the localization of `ker f` at `T` is finitely generated. -/
theorem Submodule.fg_localized_ker
    {S F M : Type*} [CommRing S] [AddCommGroup F] [Module S F]
    [Module.FinitePresentation S F] [AddCommGroup M] [Module S M]
    (T : Submonoid S) (f : F →ₗ[S] M) (hf : Function.Surjective f)
    [Module.FinitePresentation (Localization T) (LocalizedModule T M)] :
    ((LinearMap.ker f).localized T).FG := by
  rw [Submodule.localized, LinearMap.localized'_ker_eq_ker_localizedMap
    (Localization T) T (LocalizedModule.mkLinearMap T F) (LocalizedModule.mkLinearMap T M)]
  exact Module.FinitePresentation.fg_ker (LocalizedModule.map T f)
    (LocalizedModule.map_surjective T f hf)

/-! ### Dimension shifting along a family of short exact sequences -/

/-- **Dimension shifting for flatness.** Let `K` and `F` be families of `R`-modules fitting into
short exact sequences `0 → K (i+1) → F i → K i → 0`, with every `F i` flat over `R`. If `K 0` is
flat over `R`, then every `K i` is flat over `R`. -/
@[ega "IV 2.1.10" "special case"]
theorem Module.Flat.of_forall_shortExact {R : Type*} [CommRing R] {K F : ℕ → Type*}
    [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)]
    [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)]
    (hF : ∀ i, Module.Flat R (F i))
    (f : ∀ i, K (i + 1) →ₗ[R] F i) (g : ∀ i, F i →ₗ[R] K i)
    (hf : ∀ i, Function.Injective (f i)) (hfg : ∀ i, Function.Exact (f i) (g i))
    (hg : ∀ i, Function.Surjective (g i)) (h0 : Module.Flat R (K 0)) (i : ℕ) :
    Module.Flat R (K i) := by
  induction i with
  | zero => exact h0
  | succ i ih =>
    have := hF i
    have := ih
    exact flat_of_flat_of_flat_quotient (f i) (g i) (hf i) (hfg i) (hg i)

open CategoryTheory in
/-- **The `n`-th syzygy over a regular local ring of dimension at most `n` is free.** Let `A` be a
regular local ring with `dim A ≤ n` and let `K` and `F` be families of `A`-modules fitting into
short exact sequences `0 → K (i+1) → F i → K i → 0` with every `F i` projective. If `K n` is a
finite `A`-module then `K n` is free. -/
theorem IsRegularLocalRing.free_of_forall_shortExact {A : Type u} [CommRing A]
    [IsRegularLocalRing A] {n : ℕ} (hdim : ringKrullDim A ≤ (n : WithBot ℕ∞))
    {K F : ℕ → Type u} [∀ i, AddCommGroup (K i)] [∀ i, Module A (K i)]
    [∀ i, AddCommGroup (F i)] [∀ i, Module A (F i)] [∀ i, Module.Projective A (F i)]
    [Module.Finite A (K n)]
    (f : ∀ i, K (i + 1) →ₗ[A] F i) (g : ∀ i, F i →ₗ[A] K i)
    (hf : ∀ i, Function.Injective (f i)) (hfg : ∀ i, Function.Exact (f i) (g i))
    (hg : ∀ i, Function.Surjective (g i)) :
    Module.Free A (K n) := by
  have hloc : IsLocalRing A := IsRegularLocalRing.toIsLocalRing
  have hnoeth : IsNoetherianRing A := inferInstance
  have hsup : (⨆ M : ModuleCat.{u} A, projectiveDimension M) = ringKrullDim A :=
    ((isRegularLocalRing_tfae (R := A)).out 3 4).mp ‹IsRegularLocalRing A›
  have hpd : ∀ M : ModuleCat.{u} A, HasProjectiveDimensionLE M n := fun M =>
    (projectiveDimension_le_iff M n).mp
      (le_trans (le_iSup (fun M : ModuleCat.{u} A => projectiveDimension M) M) (hsup ▸ hdim))
  have hFproj : ∀ i, HasProjectiveDimensionLT (ModuleCat.of A (F i)) 1 := fun i =>
    have : Projective (ModuleCat.of A (F i)) := (IsProjective.iff_projective (F i)).mp inferInstance
    inferInstance
  have key : ∀ i, i ≤ n → HasProjectiveDimensionLT (ModuleCat.of A (K i)) (n + 1 - i) := by
    intro i
    induction i with
    | zero => intro _; simpa using hpd (ModuleCat.of A (K 0))
    | succ i ih =>
      intro hi
      have hKi := ih (by omega)
      have e1 : n + 1 - i = (n - i) + 1 := by omega
      have e2 : n + 1 - (i + 1) = n - i := by omega
      rw [e1] at hKi
      have hFi : HasProjectiveDimensionLT (ModuleCat.of A (F i)) (n - i) :=
        have := hFproj i
        hasProjectiveDimensionLT_of_ge _ 1 (n - i) (by omega)
      have hSE : (ModuleCat.shortComplexOfCompEqZero (f i) (g i)
          (by ext x; exact (hfg i).apply_apply_eq_zero x)).ShortExact :=
        ModuleCat.shortComplex_shortExact _ (hfg i) (hf i) (hg i)
      rw [e2]
      exact hSE.hasProjectiveDimensionLT_X₁ (n - i) hFi hKi
  have h1 : HasProjectiveDimensionLT (ModuleCat.of A (K n)) 1 := by simpa using key n le_rfl
  have : Projective (ModuleCat.of A (K n)) := inferInstance
  have : Module.Projective A (K n) := (IsProjective.iff_projective (K n)).mpr this
  exact Module.free_of_flat_of_isLocalRing

/-! ### The `n`-th syzygy becomes free after localizing at a point of flatness -/

section Syzygy

attribute [local instance] Ideal.algebraLocalizationAtPrimeUnder
  Ideal.isScalarTower_localizationAtPrimeUnder
  Ideal.isLocalHom_algebraMap_localizationAtPrimeUnder

variable {R P : Type u} [CommRing R] [CommRing P] [Algebra R P]

/-- Let `R → P` be flat with `R` and `P` Noetherian, and let `K` and `F` be families of
`P`-modules, each carrying a compatible `R`-structure, fitting into short exact sequences
`0 → K (i+1) → F i → K i → 0` with every `F i` finite free over `P`. Let `𝔮` be a prime of `P` with
`K 0` flat over `R` at `𝔮`, and suppose the fibre ring `P_𝔮/𝔭P_𝔮`, `𝔭 = R ∩ 𝔮`, is regular local of
dimension at most `n`. Then `(K n)_𝔮` is free over `P_𝔮`. -/
theorem Module.free_localizedModule_atPrime_of_forall_shortExact
    [IsNoetherianRing R] [IsNoetherianRing P] [Module.Flat R P]
    {K F : ℕ → Type u}
    [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)] [∀ i, Module P (K i)]
    [∀ i, IsScalarTower R P (K i)]
    [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)] [∀ i, Module P (F i)]
    [∀ i, IsScalarTower R P (F i)] [∀ i, Module.Free P (F i)] [∀ i, Module.Finite P (F i)]
    (f : ∀ i, K (i + 1) →ₗ[P] F i) (g : ∀ i, F i →ₗ[P] K i)
    (hf : ∀ i, Function.Injective (f i)) (hfg : ∀ i, Function.Exact (f i) (g i))
    (hg : ∀ i, Function.Surjective (g i))
    (q : Ideal P) [q.IsPrime] {n : ℕ} [Module.Finite P (K n)]
    (hreg : IsRegularLocalRing (Localization.AtPrime q ⧸
      (q.under R).map (algebraMap R (Localization.AtPrime q))))
    (hdim : ringKrullDim (Localization.AtPrime q ⧸
      (q.under R).map (algebraMap R (Localization.AtPrime q))) ≤ (n : WithBot ℕ∞))
    (hq : Module.Flat R (LocalizedModule.AtPrime q (K 0))) :
    Module.Free (Localization.AtPrime q) (LocalizedModule.AtPrime q (K n)) := by
  classical
  set Lf : ∀ i, LocalizedModule.AtPrime q (K (i + 1)) →ₗ[Localization.AtPrime q]
      LocalizedModule.AtPrime q (F i) := fun i => LocalizedModule.map q.primeCompl (f i)
  set Lg : ∀ i, LocalizedModule.AtPrime q (F i) →ₗ[Localization.AtPrime q]
      LocalizedModule.AtPrime q (K i) := fun i => LocalizedModule.map q.primeCompl (g i)
  have hLf : ∀ i, Function.Injective (Lf i) := fun i =>
    IsLocalizedModule.map_injective q.primeCompl
      (LocalizedModule.mkLinearMap q.primeCompl (K (i + 1)))
      (LocalizedModule.mkLinearMap q.primeCompl (F i)) (f i) (hf i)
  have hLfg : ∀ i, Function.Exact (Lf i) (Lg i) := fun i =>
    LocalizedModule.map_exact q.primeCompl (f i) (g i) (hfg i)
  have hLg : ∀ i, Function.Surjective (Lg i) := fun i =>
    LocalizedModule.map_surjective q.primeCompl (g i) (hg i)
  have hFfree : ∀ i, Module.Free (Localization.AtPrime q) (LocalizedModule.AtPrime q (F i)) :=
    fun i => Module.Free.of_isLocalizedModule q.primeCompl
      (LocalizedModule.mkLinearMap q.primeCompl (F i))
  have hFflat : ∀ i, Module.Flat R (LocalizedModule.AtPrime q (F i)) := fun i =>
    have : Module.Flat P (F i) := Module.Flat.of_free
    have : Module.Flat R (F i) := Module.Flat.trans R P (F i)
    Module.Flat.of_isLocalizedModule_of_tower q.primeCompl
      (LocalizedModule.mkLinearMap q.primeCompl (F i))
  have hKflat : ∀ i, Module.Flat R (LocalizedModule.AtPrime q (K i)) :=
    Module.Flat.of_forall_shortExact hFflat (fun i => (Lf i).restrictScalars R)
      (fun i => (Lg i).restrictScalars R) hLf hLfg hLg hq
  have hbcinj : ∀ i, Function.Injective (LinearMap.baseChange
      (Localization.AtPrime q ⧸ (q.under R).map (algebraMap R (Localization.AtPrime q)))
      (Lf i)) := by
    intro i
    have := hKflat i
    rw [LinearMap.injective_baseChange_quotient_iff]
    exact LinearMap.lTensor_injective_of_exact_of_flat ((Lg i).restrictScalars R) (hLg i)
      ((Lf i).restrictScalars R) (hLf i) (hLfg i) (R ⧸ q.under R)
  have hbcex : ∀ i, Function.Exact
      (LinearMap.baseChange (Localization.AtPrime q ⧸
        (q.under R).map (algebraMap R (Localization.AtPrime q))) (Lf i))
      (LinearMap.baseChange (Localization.AtPrime q ⧸
        (q.under R).map (algebraMap R (Localization.AtPrime q))) (Lg i)) := fun i =>
    lTensor_exact _ (hLfg i) (hLg i)
  have hbcsurj : ∀ i, Function.Surjective (LinearMap.baseChange
      (Localization.AtPrime q ⧸ (q.under R).map (algebraMap R (Localization.AtPrime q)))
      (Lg i)) := fun i => LinearMap.lTensor_surjective _ (hLg i)
  have := hreg
  have : ∀ i, Module.Free (Localization.AtPrime q) (LocalizedModule.AtPrime q (F i)) := hFfree
  have : Module.Finite (Localization.AtPrime q) (LocalizedModule.AtPrime q (K n)) :=
    inferInstance
  have hfibfree : Module.Free
      (Localization.AtPrime q ⧸ (q.under R).map (algebraMap R (Localization.AtPrime q)))
      ((Localization.AtPrime q ⧸ (q.under R).map (algebraMap R (Localization.AtPrime q)))
        ⊗[Localization.AtPrime q] LocalizedModule.AtPrime q (K n)) :=
    IsRegularLocalRing.free_of_forall_shortExact hdim
      (fun i => LinearMap.baseChange _ (Lf i)) (fun i => LinearMap.baseChange _ (Lg i))
      hbcinj hbcex hbcsurj
  rcases subsingleton_or_nontrivial (LocalizedModule.AtPrime q (K n)) with _ | _
  · exact Module.Free.of_subsingleton _ _
  let : Module (Localization.AtPrime (q.under R)) (LocalizedModule.AtPrime q (K n)) :=
    Module.compHom _
      (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q))
  have : IsScalarTower (Localization.AtPrime (q.under R)) (Localization.AtPrime q)
      (LocalizedModule.AtPrime q (K n)) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower R (Localization.AtPrime (q.under R))
      (LocalizedModule.AtPrime q (K n)) :=
    IsScalarTower.of_algebraMap_smul fun r x => by
      change algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q)
        (algebraMap R (Localization.AtPrime (q.under R)) r) • x = r • x
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_smul]
  have : Module.Flat (Localization.AtPrime (q.under R)) (LocalizedModule.AtPrime q (K n)) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime (q.under R)) (q.under R).primeCompl
      (LocalizedModule.AtPrime q (K n))).mpr (hKflat n)
  refine (Module.Flat.free_and_flat_of_free_maximalIdeal
    (R := Localization.AtPrime (q.under R)) ?_).1
  rw [Ideal.map_maximalIdeal_eq_map_under q]
  exact Module.Free.of_equiv (LinearEquiv.extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective (quotTensorEquivQuotSMul _ _))

/-- **The `n`-th syzygy of a finite free resolution over `P = R[x_1, …, x_n]` becomes finite free
after localizing away from some `g ∉ 𝔮`.** Let `R` be Noetherian, let `M` be a finitely presented
module over `P = R[x_1, …, x_n]` and let `𝔮` be a prime of `P` with `M_𝔮` flat over `R`. Then there
is a resolution of `M` by finite free `P`-modules whose `n`-th syzygy `K_n` is free over `P_g` for
some `g ∉ 𝔮`. -/
theorem Module.exists_away_free_syzygy_of_flat_atPrime_mvPolynomial
    {R M : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    [AddCommGroup M] [Module R M] [Module (MvPolynomial (Fin n) R) M]
    [IsScalarTower R (MvPolynomial (Fin n) R) M]
    [Module.FinitePresentation (MvPolynomial (Fin n) R) M]
    (q : Ideal (MvPolynomial (Fin n) R)) [q.IsPrime]
    (hq : Module.Flat R (LocalizedModule.AtPrime q M)) :
    ∃ Res : FreeResolutionData (MvPolynomial (Fin n) R) M, Res.IsExact ∧ Res.IsFiniteFree ∧
      ∃ g ∉ q, Module.Free (Localization (Submonoid.powers g))
        (LocalizedModule.Away g (Res.syzygy n)) := by
  classical
  have hnoethP : IsNoetherianRing (MvPolynomial (Fin n) R) :=
    Algebra.FiniteType.isNoetherianRing R (MvPolynomial (Fin n) R)
  obtain ⟨Res, hex, hff⟩ := exists_finite_free_resolution (MvPolynomial (Fin n) R) M
  refine ⟨Res, hex, hff, ?_⟩
  let modRF : ∀ i, Module R (Res.F i) := fun _ =>
    Module.compHom _ (algebraMap R (MvPolynomial (Fin n) R))
  have towRF : ∀ i, IsScalarTower R (MvPolynomial (Fin n) R) (Res.F i) := fun _ =>
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let modRK : ∀ i, Module R (Res.syzygy i) := fun i =>
    match i with
    | 0 => inferInstanceAs (Module R M)
    | (_ + 1) => Module.compHom _ (algebraMap R (MvPolynomial (Fin n) R))
  have towRK : ∀ i, IsScalarTower R (MvPolynomial (Fin n) R) (Res.syzygy i) := fun i =>
    match i with
    | 0 => inferInstanceAs (IsScalarTower R (MvPolynomial (Fin n) R) M)
    | (_ + 1) => IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : ∀ i, Module.Free (MvPolynomial (Fin n) R) (Res.F i) := fun i => (hff i).1
  have : ∀ i, Module.Finite (MvPolynomial (Fin n) R) (Res.F i) := fun i => (hff i).2
  have hfinK : ∀ i, Module.Finite (MvPolynomial (Fin n) R) (Res.syzygy i) :=
    Res.finite_syzygy fun i => (hff i).2
  have : Module.FinitePresentation (MvPolynomial (Fin n) R) (Res.syzygy n) :=
    Module.finitePresentation_of_finite _ _
  have : Module.Free (Localization.AtPrime q) (LocalizedModule.AtPrime q (Res.syzygy n)) :=
    Module.free_localizedModule_atPrime_of_forall_shortExact (K := fun i => Res.syzygy i)
      (F := fun i => Res.F i) Res.syzygyIncl (Res.syzygyProj hex.isComplex)
      Res.injective_syzygyIncl (Res.exact_syzygy hex.isComplex) (Res.surjective_syzygyProj hex) q
      (Ideal.isRegularLocalRing_fiberRing_mvPolynomial q)
      (Ideal.ringKrullDim_fiberRing_mvPolynomial_le q) hq
  obtain ⟨g, hgq, hgfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    q.primeCompl (LocalizedModule.mkLinearMap q.primeCompl (Res.syzygy n))
    (Localization.AtPrime q)
  exact ⟨g, hgq, hgfree⟩

end Syzygy

end
