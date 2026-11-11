module

public import StacksFrontier.RingTheory.Flat.FiberExactLocus
public import StacksFrontier.RingTheory.Flat.OpenFlatLocus
import StacksCore.Tactic.StacksAttribute

/-!
# Openness of the fibre-exactness locus, by way of the relative flat locus

Let `R` be Noetherian, let `R → S` be flat of finite type, and let
`0 → F_{e+1} →[φ e] ⋯ →[φ 0] F_0` be a finite complex of finite free `S`-modules. This file proves
that the locus of primes `𝔮` of `S` at which the fibre complex
`F̄_{•,𝔮} = (S_𝔮/𝔭S_𝔮) ⊗_S F_•`, `𝔭 = R ∩ 𝔮`, is exact is open in `Spec S`, with no hypothesis on
the fibres, and deduces Lemma 00RB exactly as the source states it: for fibres
`S ⊗_R κ(𝔭)` Cohen–Macaulay of dimension `d`.

## Main results

* `Algebra.isOpen_setOf_exact_baseChange_fiber_of_flat`: the fibre-exactness locus is open, for
  any flat ring map of finite type over a Noetherian ring.
* `Algebra.isOpen_setOf_exact_baseChange_fiber_of_flat_of_isMaximalCohenMacaulay`: Stacks 00RB.

## Implementation notes

The source proves 00RB through Proposition 00N1 and Lemma 00RA, and Lemma 00RA asks that the
fibres be Cohen–Macaulay *and equidimensional*; that route is
`Algebra.isOpen_setOf_exact_baseChange_fiber_of_flat_of_isMaximalCohenMacaulay_of_equidimensional`,
which is the form Theorem 00RC consumes. Here the openness is read off from Theorem 00RC itself,
`Module.isOpen_setOf_flat_localizedModule_atPrime`, which the library proves. The point is the
pointwise equivalence

  `F̄_{•,𝔮}` is exact  ⟺  `F_{•,𝔮}` is exact and every `(F_k/φ_k(F_{k+1}))_𝔮` is flat over `R`.

*⟹* is Lemma 00MI at one index
(`Module.Flat.ker_eq_range_and_flat_quotient_range_of_mem_sup_smul_top`),
over the local homomorphism `R_𝔭 → S_𝔮`: it gives exactness of `F_{•,𝔮}` together with flatness of
the cokernel of each differential.

*⟸* is the vanishing of `Tor_1` against a flat cokernel
(`LinearMap.lTensor_injective_of_exact_of_flat`): if `Z/f(Y)` is flat over `R` and `f y ∈ 𝔭Z`
then `y ∈ 𝔭Y + Ker f`; applied to `φ_k` over `S_𝔮` this is exactness of `F̄_{•,𝔮}` at `F_{k+1}`.

The right-hand side is open: exactness of `F_{•,𝔮}` by `isOpen_setOf_baseChangeExact_localization`,
and each flatness condition by Theorem 00RC, for the finitely presented `S`-modules
`F_k/φ_k(F_{k+1})` over the finitely presented `R`-algebra `S`. No condition on the fibres enters,
so the Cohen–Macaulay hypothesis of 00RB is not used.

## References

* [StacksProject 00RB](https://stacks.math.columbia.edu/tag/00RB)
* [StacksProject 00MI](https://stacks.math.columbia.edu/tag/00MI)
* [StacksProject 00RC](https://stacks.math.columbia.edu/tag/00RC)

## Tags

exact complex, finite free module, fibre, flat ring map, Cohen-Macaulay ring, open locus, flat locus
-/

namespace Stacks.Flatness.FibreExactnessLocus

open TensorProduct Stacks.RegularSequence.FibrewiseLocus

/-- **A flat cokernel kills `Tor_1`, read on elements.** Let `f : Y → Z` be `R`-linear with
`Z/f(Y)` flat over `R`, and let `I` be an ideal of `R`. If `f y ∈ IZ` then `y ∈ IY + Ker f`. -/
public theorem mem_smul_top_sup_ker_of_flat_quotient_range {R Y Z : Type*} [CommRing R]
    [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z] (f : Y →ₗ[R] Z)
    (hflat : Module.Flat R (Z ⧸ LinearMap.range f)) (I : Ideal R) (y : Y)
    (hy : f y ∈ I • (⊤ : Submodule R Z)) :
    y ∈ I • (⊤ : Submodule R Y) ⊔ LinearMap.ker f := by
  have hinj : Function.Injective ((LinearMap.range f).subtype.lTensor (R ⧸ I)) :=
    LinearMap.lTensor_injective_of_exact_of_flat (LinearMap.range f).mkQ
      (Submodule.mkQ_surjective _) _ (Submodule.injective_subtype _)
      (LinearMap.exact_subtype_mkQ _) (R ⧸ I)
  have h0 : (1 : R ⧸ I) ⊗ₜ[R] (⟨f y, LinearMap.mem_range_self f y⟩ : LinearMap.range f) = 0 := by
    apply hinj
    rw [LinearMap.lTensor_tmul, map_zero]
    exact (TensorProduct.one_tmul_eq_zero_iff_mem_smul_top I (f y)).mpr hy
  rw [TensorProduct.one_tmul_eq_zero_iff_mem_smul_top] at h0
  have hmap : (⟨f y, LinearMap.mem_range_self f y⟩ : LinearMap.range f) ∈
      (I • (⊤ : Submodule R Y)).map f.rangeRestrict := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_rangeRestrict]
    exact h0
  obtain ⟨y', hy', hfy'⟩ := hmap
  refine Submodule.mem_sup.mpr ⟨y', hy', y - y', ?_, by abel⟩
  have h := congrArg Subtype.val hfy'
  rw [LinearMap.mem_ker, map_sub]
  simp only [LinearMap.codRestrict_apply] at h
  rw [h, sub_self]

section BaseChange

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- **Exactness modulo `IA` against a flat cokernel.** Let `X →[g] Y →[f] Z` be an exact
sequence of `A`-modules whose `R`-module structures come from `R → A`, with `Z/f(Y)` flat over `R`.
Then it stays exact after base change along `A → A/IA`. -/
public theorem exact_baseChange_quotient_of_flat_quotient_range {X Y Z : Type*} [AddCommGroup X]
    [Module A X] [AddCommGroup Y] [Module A Y] [Module R Y] [IsScalarTower R A Y]
    [AddCommGroup Z] [Module A Z] [Module R Z] [IsScalarTower R A Z] (I : Ideal R)
    (g : X →ₗ[A] Y) (f : Y →ₗ[A] Z) (hex : Function.Exact g f)
    (hflat : Module.Flat R (Z ⧸ LinearMap.range f)) :
    Function.Exact (g.baseChange (A ⧸ I.map (algebraMap R A)))
      (f.baseChange (A ⧸ I.map (algebraMap R A))) := by
  have hflat' : Module.Flat R (Z ⧸ LinearMap.range (f.restrictScalars R)) := by
    have := hflat
    exact Module.Flat.of_linearEquiv (Submodule.Quotient.restrictScalarsEquiv R (LinearMap.range f))
  intro t
  constructor
  · intro ht
    obtain ⟨y, rfl⟩ := TensorProduct.exists_one_tmul _ t
    rw [LinearMap.baseChange_tmul, TensorProduct.one_tmul_eq_zero_iff_mem_smul_top,
      Module.Flat.mem_map_smul_top_iff] at ht
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      Submodule.mem_sup.mp (mem_smul_top_sup_ker_of_flat_quotient_range _ hflat' I y ht)
    obtain ⟨x, rfl⟩ := (hex b).mp hb
    refine ⟨1 ⊗ₜ[A] x, ?_⟩
    have ha0 : (1 : A ⧸ I.map (algebraMap R A)) ⊗ₜ[A] a = 0 :=
      (TensorProduct.one_tmul_eq_zero_iff_mem_smul_top _ a).mpr
        ((Module.Flat.mem_map_smul_top_iff I a).mpr ha)
    rw [LinearMap.baseChange_tmul, TensorProduct.tmul_add, ha0, zero_add]
  · rintro ⟨u, rfl⟩
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hex.linearMap_comp_eq_zero,
      LinearMap.baseChange_zero, LinearMap.zero_apply]

/-- **Injectivity modulo `IA` against a flat cokernel.** An injective map `f : Y → Z` of
`A`-modules with `Z/f(Y)` flat over `R` stays injective after base change along `A → A/IA`. -/
public theorem injective_baseChange_quotient_of_flat_quotient_range {Y Z : Type*}
    [AddCommGroup Y] [Module A Y] [Module R Y] [IsScalarTower R A Y]
    [AddCommGroup Z] [Module A Z] [Module R Z] [IsScalarTower R A Z] (I : Ideal R)
    (f : Y →ₗ[A] Z) (hf : Function.Injective f)
    (hflat : Module.Flat R (Z ⧸ LinearMap.range f)) :
    Function.Injective (f.baseChange (A ⧸ I.map (algebraMap R A))) := by
  have hflat' : Module.Flat R (Z ⧸ LinearMap.range (f.restrictScalars R)) := by
    have := hflat
    exact Module.Flat.of_linearEquiv (Submodule.Quotient.restrictScalarsEquiv R (LinearMap.range f))
  have hker : LinearMap.ker (f.restrictScalars R) = ⊥ := LinearMap.ker_eq_bot.mpr hf
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨y, rfl⟩ := TensorProduct.exists_one_tmul _ t
  rw [LinearMap.baseChange_tmul, TensorProduct.one_tmul_eq_zero_iff_mem_smul_top,
    Module.Flat.mem_map_smul_top_iff] at ht
  have hy := mem_smul_top_sup_ker_of_flat_quotient_range _ hflat' I y ht
  rw [hker, sup_bot_eq] at hy
  exact (TensorProduct.one_tmul_eq_zero_iff_mem_smul_top _ y).mpr
    ((Module.Flat.mem_map_smul_top_iff I y).mpr hy)

/-- **Lemma 00MI at one index, with the flatness of the cokernel.** Let `R → A` be a local
homomorphism of local rings with `A` Noetherian and flat over `R`, let `J = 𝔪_R A`, and let
`X →[g] Y →[f] Z` be a complex of `A`-modules with `Y` finite and `Z` flat over `A`. If it becomes
exact at `Y` modulo `J`, then `Z/f(Y)` is flat over `R`, and so over any ring `R₀` over which `R`
is flat. -/
public theorem flat_quotient_range_of_exact_baseChange_quotient {R₀ : Type*} [CommRing R₀]
    [Algebra R₀ R] [Algebra R₀ A] [IsScalarTower R₀ R A] [Module.Flat R₀ R] [IsLocalRing R]
    [IsLocalRing A] [IsLocalHom (algebraMap R A)] [IsNoetherianRing A] [Module.Flat R A]
    {X Y Z : Type*} [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    [Module.Finite A Y] [AddCommGroup Z] [Module A Z] [Module R₀ Z] [IsScalarTower R₀ A Z]
    [Module.Flat A Z]
    (J : Ideal A) (hJ : J = (IsLocalRing.maximalIdeal R).map (algebraMap R A))
    (g : X →ₗ[A] Y) (f : Y →ₗ[A] Z) (hfg : f ∘ₗ g = 0)
    (h : Function.Exact (LinearMap.baseChange (A ⧸ J) g) (LinearMap.baseChange (A ⧸ J) f)) :
    Module.Flat R₀ (Z ⧸ LinearMap.range f) := by
  subst hJ
  let _ : Module R Y := Module.compHom _ (algebraMap R A)
  have _ : IsScalarTower R A Y := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let _ : Module R Z := Module.compHom _ (algebraMap R A)
  have _ : IsScalarTower R A Z := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have _ : Module.Flat R Z := Module.Flat.trans R A Z
  have _ : Module.Flat R (Z ⧸ LinearMap.range f) :=
    (Module.Flat.ker_eq_range_and_flat_quotient_range_of_mem_sup_smul_top g f hfg
        (fun y hy => mem_sup_range_of_exact_baseChange _ g f h y hy)).2
  have _ : IsScalarTower R₀ R (Z ⧸ LinearMap.range f) :=
    IsScalarTower.of_algebraMap_smul fun r m => by
      induction m using Submodule.Quotient.induction_on with
      | H x =>
        rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul]
        congr 1
        change algebraMap R A (algebraMap R₀ R r) • x = r • x
        rw [← IsScalarTower.algebraMap_apply, algebraMap_smul]
  exact Module.Flat.trans R₀ R _

end BaseChange

/-- The cokernel of the base change of `φ : M → N` along `S → A`, read through the localization:
for `A = S_𝔮`, flatness over `R` of `(A ⊗ N)/φ(A ⊗ M)` is flatness of `(N/φ(M))_𝔮`. -/
public theorem flat_quotient_range_baseChange_iff {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] {M N : Type*} [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
    [Module R N] [IsScalarTower R S N] (φ : M →ₗ[S] N) (q : Ideal S) [q.IsPrime] :
    Module.Flat R (Localization.AtPrime q ⊗[S] N ⧸
        LinearMap.range (φ.baseChange (Localization.AtPrime q))) ↔
      Module.Flat R (LocalizedModule.AtPrime q (N ⧸ LinearMap.range φ)) := by
  set A := Localization.AtPrime q
  have hex := lTensor_exact A (LinearMap.exact_map_mkQ_range φ) (Submodule.mkQ_surjective _)
  have e2 : (A ⊗[S] N ⧸ LinearMap.range (φ.lTensor A)) ≃ₗ[S] A ⊗[S] (N ⧸ LinearMap.range φ) :=
    hex.linearEquivOfSurjective (LinearMap.lTensor_surjective A (Submodule.mkQ_surjective _))
  have hrange : (LinearMap.range (φ.baseChange A)).restrictScalars S =
      LinearMap.range (φ.lTensor A) := by
    ext x
    simp [LinearMap.baseChange_eq_ltensor]
  have e3 : (A ⊗[S] N ⧸ LinearMap.range (φ.baseChange A)) ≃ₗ[S]
      A ⊗[S] N ⧸ LinearMap.range (φ.lTensor A) :=
    (Submodule.Quotient.restrictScalarsEquiv S (LinearMap.range (φ.baseChange A))).symm.trans
      (Submodule.quotEquivOfEq _ _ hrange)
  have e1 := (LocalizedModule.equivTensorProduct q.primeCompl (N ⧸ LinearMap.range φ))
  constructor
  · intro h
    exact Module.Flat.of_linearEquiv
      ((e1.restrictScalars R).trans ((e3.trans e2).symm.restrictScalars R))
  · intro h
    exact Module.Flat.of_linearEquiv
      (((e3.trans e2).restrictScalars R).trans (e1.restrictScalars R).symm)


attribute [local instance] Ideal.algebraLocalizationAtPrimeUnder
  Ideal.isScalarTower_localizationAtPrimeUnder
  Ideal.isLocalHom_algebraMap_localizationAtPrimeUnder

/-- **The fibre complex is exact exactly where the localised complex is exact with flat
cokernels.** Let `R → S` be flat with `R` and `S` Noetherian and let
`0 → F_{e+1} →[φ e] ⋯ →[φ 0] F_0` be a complex of finite free `S`-modules. Then the fibre complex
`F̄_{•,𝔮} = (S_𝔮/𝔭S_𝔮) ⊗_S F_•` is exact at `F̄_{e+1}, …, F̄_1` if and only if `F_{•,𝔮}` is exact
there and each `(F_k/φ_k(F_{k+1}))_𝔮`, `k ≤ e`, is flat over `R`. -/
public theorem baseChangeExact_fiber_iff_localization_and_flat {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    (e : ℕ) {F : ℕ → Type*} [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    [∀ i, Module R (F i)] [∀ i, IsScalarTower R S (F i)] [∀ i, Module.Free S (F i)]
    [∀ i, Module.Finite S (F i)] (φ : ∀ i, F (i + 1) →ₗ[S] F i)
    (hφ : ∀ k < e, φ k ∘ₗ φ (k + 1) = 0) (q : Ideal S) [q.IsPrime] :
    BaseChangeExact (fiberLocalRing R q) e φ ↔
      BaseChangeExact (Localization.AtPrime q) e φ ∧
        ∀ k ≤ e, Module.Flat R (LocalizedModule.AtPrime q (F k ⧸ LinearMap.range (φ k))) := by
  constructor
  · intro hq
    refine ⟨baseChangeExact_localization_of_baseChangeExact_fiber e φ hφ q hq, fun k hk => ?_⟩
    rw [← flat_quotient_range_baseChange_iff]
    have _ : Module.Flat (Localization.AtPrime (q.under R)) (Localization.AtPrime q) :=
      (Module.flat_iff_of_isLocalization (Localization.AtPrime (q.under R)) (q.under R).primeCompl
            (Localization.AtPrime q)).mpr
        inferInstance
    have _ : IsNoetherianRing (Localization.AtPrime q) :=
      IsLocalization.isNoetherianRing q.primeCompl _ inferInstance
    obtain ⟨hqinj, hqex⟩ :=
      (baseChangeExact_baseChange_iff (Localization.AtPrime q) (fiberLocalRing R q) e φ).mpr hq
    have hJ :
        (q.under R).map (algebraMap R (Localization.AtPrime q)) =
          Ideal.map (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q))
            (IsLocalRing.maximalIdeal (Localization.AtPrime (q.under R))) :=
      (Ideal.map_maximalIdeal_eq_map_under q).symm
    rcases hk.lt_or_eq with hk | rfl
    · exact flat_quotient_range_of_exact_baseChange_quotient
          (R := Localization.AtPrime (q.under R)) _ hJ
          ((φ (k + 1)).baseChange (Localization.AtPrime q))
          ((φ k).baseChange (Localization.AtPrime q))
          (by rw [← LinearMap.baseChange_comp, hφ k hk, LinearMap.baseChange_zero]) (hqex k hk)
    · refine flat_quotient_range_of_exact_baseChange_quotient
          (R := Localization.AtPrime (q.under R)) _ hJ
          (0 : Localization.AtPrime q ⊗[S] F (k + 1) →ₗ[Localization.AtPrime q]
            Localization.AtPrime q ⊗[S] F (k + 1))
          ((φ k).baseChange (Localization.AtPrime q)) (by simp) ?_
      rw [LinearMap.exact_iff, LinearMap.baseChange_zero, LinearMap.range_zero,
        LinearMap.ker_eq_bot]
      exact hqinj
  · rintro ⟨hA, hfl⟩
    have hfl' : ∀ k ≤ e, Module.Flat R (Localization.AtPrime q ⊗[S] F k ⧸
        LinearMap.range ((φ k).baseChange (Localization.AtPrime q))) := fun k hk =>
      (flat_quotient_range_baseChange_iff (φ k) q).mpr (hfl k hk)
    refine (baseChangeExact_baseChange_iff (Localization.AtPrime q) (fiberLocalRing R q) e φ).mp
      ⟨injective_baseChange_quotient_of_flat_quotient_range (q.under R) _ hA.1 (hfl' e le_rfl),
        fun k hk => exact_baseChange_quotient_of_flat_quotient_range (q.under R) _ _ (hA.2 k hk)
          (hfl' k hk.le)⟩

end Stacks.Flatness.FibreExactnessLocus

namespace Algebra

open Stacks.Flatness.FibreExactnessLocus Stacks.RegularSequence.FibrewiseLocus _root_.TensorProduct

/-- **The fibre-exactness locus is open, for any flat ring map of finite type.** Let `R` be
Noetherian, let `R → S` be flat of finite type, and let
`0 → F_{e+1} →[φ e] F_e → ⋯ → F_1 →[φ 0] F_0` be a finite complex of finite free
`S`-modules. Then the set of primes `𝔮` of `S` at which the fibre complex
`F̄_{•,𝔮} = F_{•,𝔮} ⊗_R κ(𝔭) = (S_𝔮/𝔭S_𝔮) ⊗_S F_•`, where `𝔭 = R ∩ 𝔮`, is exact at
`F̄_{e+1}, …, F̄_1` is open in `Spec S`.

No hypothesis on the fibres is needed: the locus is the intersection of the locus where `F_{•,𝔮}`
is exact with the relative flat loci of the cokernels `F_k/φ_k(F_{k+1})`, each open by Theorem
00RC. See the module docstring. -/
public theorem isOpen_setOf_exact_baseChange_fiber_of_flat {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [IsNoetherianRing R] [Algebra.FiniteType R S] [Module.Flat R S]
    (e : ℕ) (F : ℕ → Type*) [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    [∀ i, Module.Free S (F i)] [∀ i, Module.Finite S (F i)] (φ : ∀ i, F (i + 1) →ₗ[S] F i)
    (hφ : ∀ k < e, φ k ∘ₗ φ (k + 1) = 0) :
    IsOpen
      {q : PrimeSpectrum S |
        Function.Injective
            (LinearMap.baseChange
              (Localization.AtPrime q.asIdeal ⧸
                (q.asIdeal.under R).map (algebraMap R (Localization.AtPrime q.asIdeal)))
              (φ e)) ∧
          ∀ k < e,
            Function.Exact
              (LinearMap.baseChange
                (Localization.AtPrime q.asIdeal ⧸
                  (q.asIdeal.under R).map (algebraMap R (Localization.AtPrime q.asIdeal)))
                (φ (k + 1)))
              (LinearMap.baseChange
                (Localization.AtPrime q.asIdeal ⧸
                  (q.asIdeal.under R).map (algebraMap R (Localization.AtPrime q.asIdeal)))
                (φ k))} := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  have : Algebra.FinitePresentation R S := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  let _ : ∀ i, Module R (F i) := fun i => Module.compHom _ (algebraMap R S)
  have _ : ∀ i, IsScalarTower R S (F i) := fun _ =>
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have _ : ∀ k, Module.FinitePresentation S (F k ⧸ LinearMap.range (φ k)) := fun _ =>
    Module.finitePresentation_of_finite _ _
  have hset :
      {q : PrimeSpectrum S |
        Function.Injective
            (LinearMap.baseChange
              (Localization.AtPrime q.asIdeal ⧸
                (q.asIdeal.under R).map (algebraMap R (Localization.AtPrime q.asIdeal)))
              (φ e)) ∧
          ∀ k < e,
            Function.Exact
              (LinearMap.baseChange
                (Localization.AtPrime q.asIdeal ⧸
                  (q.asIdeal.under R).map (algebraMap R (Localization.AtPrime q.asIdeal)))
                (φ (k + 1)))
              (LinearMap.baseChange
                (Localization.AtPrime q.asIdeal ⧸
                  (q.asIdeal.under R).map (algebraMap R (Localization.AtPrime q.asIdeal)))
                (φ k))} =
        {q : PrimeSpectrum S | BaseChangeExact (Localization.AtPrime q.asIdeal) e φ} ∩
          ⋂ k : Fin (e + 1), {q : PrimeSpectrum S |
            Module.Flat R (LocalizedModule.AtPrime q.asIdeal (F k ⧸ LinearMap.range (φ k)))} := by
    ext q
    rw [Set.mem_inter_iff, Set.mem_iInter]
    change BaseChangeExact (fiberLocalRing R q.asIdeal) e φ ↔ _
    rw [baseChangeExact_fiber_iff_localization_and_flat e φ hφ q.asIdeal]
    exact and_congr Iff.rfl
      ⟨fun h k => h k (Nat.lt_succ_iff.mp k.2), fun h k hk => h ⟨k, Nat.lt_succ_iff.mpr hk⟩⟩
  rw [hset]
  exact (isOpen_setOf_baseChangeExact_localization e φ hφ).inter
    (isOpen_iInter_of_finite fun k =>
      Module.isOpen_setOf_flat_localizedModule_atPrime (R := R) (S := S)
        (M := F k ⧸ LinearMap.range (φ k)))

/-- **Stacks 00RB.** Let `R` be Noetherian, let `R → S` be a flat ring map of finite type all of
whose nonempty fibres `S ⊗_R κ(𝔭)` are Cohen–Macaulay (each of their local rings `A` satisfies
`depth_{𝔪_A}(A) = dim A`) of dimension `d`, and let `0 → F_{e+1} →[φ e] F_e → ⋯ → F_1 →[φ 0] F_0`
be a finite complex of finite free `S`-modules. Then the set of primes `𝔮` of `S` at which the
fibre complex `F̄_{•,𝔮} = F_{•,𝔮} ⊗_R κ(𝔭) = (S_𝔮/𝔭S_𝔮) ⊗_S F_•`, where `𝔭 = R ∩ 𝔮`, is exact
at `F̄_{e+1}, …, F̄_1` is open in `Spec S`.

The fibre hypothesis is not used: the conclusion holds for every flat ring map of finite type over
a Noetherian ring, `isOpen_setOf_exact_baseChange_fiber_of_flat`. -/
@[stacks 00RB "The complex is indexed as in 00N1: `φ k : F (k+1) → F k`, read for `k ≤ e`, on
finite free `S`-modules `F i` (the source's `S^{n_i}`), and exactness is injectivity of `φ e` and
exactness at `F_e, …, F_1`. `F_𝔮 ⊗_R κ(𝔭)` is the base change of `F` along `S → S_𝔮/𝔭S_𝔮`, which
is `S_𝔮 ⊗_R κ(𝔭)`. The fibres are Cohen–Macaulay of dimension `d` as in the source: every local
ring of a nonempty fibre is Cohen–Macaulay, and the fibre has Krull dimension `d`; the proof does
not use this hypothesis, going through Theorem 00RC instead of Lemma 00RA."]
public theorem isOpen_setOf_exact_baseChange_fiber_of_flat_of_isMaximalCohenMacaulay
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [Algebra.FiniteType R S] [Module.Flat R S] (d : ℕ)
    (_hfib :
      ∀ (p : Ideal R) [p.IsPrime],
        Nontrivial (p.Fiber S) →
          (∀ (Q : Ideal (p.Fiber S)) [Q.IsPrime],
              Module.IsMaximalCohenMacaulay (Localization.AtPrime Q) (Localization.AtPrime Q)) ∧
            ringKrullDim (p.Fiber S) = (d : WithBot ℕ∞))
    (e : ℕ) (F : ℕ → Type*) [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    [∀ i, Module.Free S (F i)] [∀ i, Module.Finite S (F i)] (φ : ∀ i, F (i + 1) →ₗ[S] F i)
    (hφ : ∀ k < e, φ k ∘ₗ φ (k + 1) = 0) :
    IsOpen
      {q : PrimeSpectrum S |
        Function.Injective
            (LinearMap.baseChange
              (Localization.AtPrime q.asIdeal ⧸
                (q.asIdeal.under R).map (algebraMap R (Localization.AtPrime q.asIdeal)))
              (φ e)) ∧
          ∀ k < e,
            Function.Exact
              (LinearMap.baseChange
                (Localization.AtPrime q.asIdeal ⧸
                  (q.asIdeal.under R).map (algebraMap R (Localization.AtPrime q.asIdeal)))
                (φ (k + 1)))
              (LinearMap.baseChange
                (Localization.AtPrime q.asIdeal ⧸
                  (q.asIdeal.under R).map (algebraMap R (Localization.AtPrime q.asIdeal)))
                (φ k))} :=
  isOpen_setOf_exact_baseChange_fiber_of_flat e F φ hφ

end Algebra
