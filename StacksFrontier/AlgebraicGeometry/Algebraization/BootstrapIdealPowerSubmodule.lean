module

public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.RingTheory.AdicCompletion.Exactness
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Localization.Submodule
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapSituation
import all StacksFrontier.AlgebraicGeometry.Algebraization.DepthInequalitiesBootstrap

/-!
# A bootstrap situation stays one after replacing `M` by `IᵏM`

The four assumptions of Situation [Stacks, Tag 0EFU] are stable under passing from the finite
module `M` to its submodule `IᵏM`. Assumptions (1) and (3) do not mention the module at all, so
there is nothing to check; the two depth assumptions (4) and (6) hold because the inclusion
`IᵏM ⊆ M` becomes an isomorphism exactly where those assumptions look.

Both reductions rest on one observation. The quotient `M/IᵏM` is annihilated by `Iᵏ`, so it
dies after inverting any element of `I`, and an injection whose cokernel dies becomes an
isomorphism. For assumption (4) the prime `𝔭` lies outside `V(I)`, so some element of `I` is
inverted at `𝔭` and `(IᵏM)_𝔭 ≅ M_𝔭`. For assumption (6) the same argument is run one step later:
`I`-adic completion is exact on finite modules over a Noetherian ring
(`AdicCompletion.map_exact`), so the cokernel of `(IᵏM_𝔮)^∧ ⊆ (M_𝔮)^∧` is the completion of
`M_𝔮/IᵏM_𝔮` and is still annihilated by `Iᵏ`; the prime `𝔭'` of the completed localization is
assumed to lie outside the adic locus, so a power of an element of `I'` outside `𝔭'` kills that
cokernel and the two completions agree at `𝔭'`.

## Main definitions

* `Stacks.Algebraization.BootstrapSituation.idealPowerSubmodule` — the bootstrap situation with
  the same ring, ideal, locus and bounds and with `M` replaced by `IᵏM`.

## Main results

* `Stacks.Algebraization.localizedModuleEquivOfExactOfSMulEqZero` — an injection with a
  cokernel annihilated by an element of the submonoid becomes an isomorphism after localizing.
* `Stacks.Algebraization.depth_localizedModule_pow_smul_top_eq` — `IᵏM` and `M` have the same
  depth at a prime outside `V(I)`.
* `Stacks.Algebraization.depth_or_depth_add_dimension_pow_smul_top` and
  `Stacks.Algebraization.completedLocalDepth_pow_smul_top` — assumptions (4) and (6) for `IᵏM`.
* `Stacks.Algebraization.map_subtype_pow_smul_top` — `Iⁿ(IᵏM) = I^{n+k}M` inside `M`, which
  identifies the adic tower of `IᵏM` with the source's system `{I^kM/IⁿM}_{n ≥ k}` read along
  the cofinal shift `n ↦ n + k`.

## Implementation notes

`AdicCompletion.map_injective` and `AdicCompletion.map_exact` are stated in Mathlib for modules
living in the universe of the ring, so the module universe of the situation is pinned to the
ring's throughout; that is the universe in which every closed-point result of this chapter is
stated anyway. The dualizing-complex universe stays free, assumption (1) being untouched.

That a scalar annihilating a module annihilates its adic completion is the private lemma
`Stacks.Algebraization.adicCompletion_smul_eq_zero` of
`StacksFrontier/AlgebraicGeometry/Algebraization/DepthInequalitiesBootstrap.lean`, used here through
`import all` rather than restated.

## References

* [Stacks Project, Tag 0EFU](https://stacks.math.columbia.edu/tag/0EFU)
* [Stacks Project, Tag 0EFV](https://stacks.math.columbia.edu/tag/0EFV)
-/

@[expose] public section

open IsLocalRing

universe u w

namespace Stacks.Algebraization

/-! ### Annihilating a module, its localization and its completion -/

/-- **An extended ideal annihilates whatever its generators annihilate.** If every element of `J`
annihilates an `S`-module `X` through the structure map, then every element of `J S` does. -/
public theorem smul_eq_zero_of_mem_map_of_forall_smul_eq_zero
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {X : Type*} [AddCommGroup X] [Module R X] [Module S X] [IsScalarTower R S X]
    (J : Ideal R) (hJ : ∀ c ∈ J, ∀ x : X, c • x = 0) {a : S}
    (ha : a ∈ J.map (algebraMap R S)) (x : X) : a • x = 0 := by
  have hle : J.map (algebraMap R S) ≤ Module.annihilator S X := by
    rw [Ideal.map_le_iff_le_comap]
    intro c hc
    simp only [Ideal.mem_comap, Module.mem_annihilator]
    intro y
    rw [IsScalarTower.algebraMap_smul]
    exact hJ c hc y
  exact Module.mem_annihilator.mp (hle ha) x

/-- **An element of `Iᵏ` annihilates `M/IᵏM`.** -/
public theorem smul_quotient_pow_smul_top_eq_zero {R : Type*} [CommRing R] (I : Ideal R) (k : ℕ)
    {M : Type*} [AddCommGroup M] [Module R M] {a : R} (ha : a ∈ I ^ k)
    (z : M ⧸ (I ^ k • (⊤ : Submodule R M))) : a • z = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (I ^ k • (⊤ : Submodule R M)) z
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul ha Submodule.mem_top

/-- **An injection with an annihilated cokernel becomes an isomorphism after localizing.** Let
`f : X → Y` be injective and `g : Y → Z` exact at `Y`, and let `a` be an element of the submonoid
`S` which annihilates `Z`. Then `f` induces an isomorphism `X_S ≅ Y_S` of `S⁻¹R`-modules.

*Argument.* Injectivity is preserved by localization. For surjectivity, `g (a • y) = a • g y = 0`
puts `a • y = f x` in the image of `f` for every `y`, and `y/s = (a • y)/(a s) = f x / (a s)`. -/
public noncomputable def localizedModuleEquivOfExactOfSMulEqZero
    {R : Type*} [CommRing R] (S : Submonoid R)
    {X Y Z : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [AddCommGroup Z] [Module R Z]
    (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (hf : Function.Injective f)
    (hfg : Function.Exact f g) {a : R} (ha : a ∈ S) (haZ : ∀ z : Z, a • z = 0) :
    LocalizedModule S X ≃ₗ[Localization S] LocalizedModule S Y :=
  LinearEquiv.ofBijective (LocalizedModule.map S f)
    ⟨LocalizedModule.map_injective S f hf, by
      intro y
      induction y using LocalizedModule.induction_on with
      | _ y s =>
        obtain ⟨x, hx⟩ := (hfg (a • y)).mp (by rw [map_smul, haZ])
        refine ⟨LocalizedModule.mk x (⟨a, ha⟩ * s), ?_⟩
        rw [LocalizedModule.map_mk, hx]
        exact LocalizedModule.mk_cancel_common_left ⟨a, ha⟩ s y⟩

/-! ### The submodule `IᵏM`, its ideal-power filtration and its depth -/

/-- **`Iⁿ(IᵏM) = I^{n+k}M` inside `M`.** So the tower of adic quotients of the module `IᵏM` is
the source's system `{IᵏM/IⁿM}_{n ≥ k}` read along the cofinal shift `n ↦ n + k`. -/
public theorem map_subtype_pow_smul_top {R : Type*} [CommRing R] (I : Ideal R) (k n : ℕ)
    {M : Type*} [AddCommGroup M] [Module R M] :
    Submodule.map (I ^ k • (⊤ : Submodule R M)).subtype
        (I ^ n • (⊤ : Submodule R ↥(I ^ k • (⊤ : Submodule R M)))) =
      I ^ (n + k) • (⊤ : Submodule R M) := by
  rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype, ← Submodule.smul_assoc,
    Ideal.smul_eq_mul, ← pow_add]

/-- The submodule `IᵏM` of a finite module over a Noetherian ring is finite. -/
public theorem finite_pow_smul_top {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (k : ℕ) {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.Finite R ↥(I ^ k • (⊤ : Submodule R M)) :=
  Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)

/-- **`IᵏM` and `M` have the same depth at a prime outside `V(I)`.** Some element of `I` is then
inverted, and `M/IᵏM` is annihilated by `Iᵏ`, so the inclusion `IᵏM ⊆ M` localizes to an
isomorphism and `Module.depth` is invariant under a linear equivalence. -/
public theorem depth_localizedModule_pow_smul_top_eq {R : Type u} [CommRing R] (I : Ideal R)
    (k : ℕ) {M : Type*} [AddCommGroup M] [Module R M] (p : PrimeSpectrum R)
    (hp : ¬ (I : Set R) ⊆ p.asIdeal) :
    Module.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl ↥(I ^ k • (⊤ : Submodule R M))) =
      Module.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl M) := by
  obtain ⟨b, hbI, hbp⟩ := Set.not_subset.mp hp
  refine Module.depth_eq_depth_of_linearEquiv _
    (localizedModuleEquivOfExactOfSMulEqZero p.asIdeal.primeCompl
      (I ^ k • (⊤ : Submodule R M)).subtype (I ^ k • (⊤ : Submodule R M)).mkQ
      (Submodule.injective_subtype _) (LinearMap.exact_subtype_mkQ _)
      (p.asIdeal.primeCompl.pow_mem hbp k) ?_)
  exact fun z => smul_quotient_pow_smul_top_eq_zero I k (Ideal.pow_mem_pow hbI k) z

/-- **The completion of an injection with an annihilated cokernel becomes an isomorphism after
localizing at a prime of the completed ring outside the adic locus.** Let `0 → X → Y → Z → 0` be
exact with `Y` finite over the Noetherian ring `R`, and let `Iᵏ` annihilate `Z`. Then `X` and `Y`
have the same depth after `I`-adic completion and localization at a prime `𝔭'` of `R^∧` with
`I R^∧ ⊄ 𝔭'`.

*Argument.* `I`-adic completion is exact on finite modules over a Noetherian ring
(`AdicCompletion.map_exact`) and preserves the injectivity of `X → Y`
(`AdicCompletion.map_injective`), so `Z^∧` is the cokernel; it is annihilated by `Iᵏ` and hence
by `(I R^∧)ᵏ`. An element `b` of `I R^∧` outside `𝔭'` has `bᵏ` outside `𝔭'` and annihilating
`Z^∧`, so `localizedModuleEquivOfExactOfSMulEqZero` applies. -/
public theorem depth_localizedModule_adicCompletion_eq_of_exact
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) (k : ℕ)
    {X Y Z : Type u} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [AddCommGroup Z] [Module R Z] [Module.Finite R Y]
    (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) (hZ : ∀ c ∈ I ^ k, ∀ z : Z, c • z = 0)
    (p' : PrimeSpectrum (AdicCompletion I R))
    (hp' : ¬ I.map (algebraMap R (AdicCompletion I R)) ≤ p'.asIdeal) :
    Module.depth (Localization.AtPrime p'.asIdeal)
        (maximalIdeal (Localization.AtPrime p'.asIdeal))
        (LocalizedModule p'.asIdeal.primeCompl (AdicCompletion I X)) =
      Module.depth (Localization.AtPrime p'.asIdeal)
        (maximalIdeal (Localization.AtPrime p'.asIdeal))
        (LocalizedModule p'.asIdeal.primeCompl (AdicCompletion I Y)) := by
  obtain ⟨b, hbI, hbp⟩ := IsConcreteLE.not_le_iff_exists.mp hp'
  refine Module.depth_eq_depth_of_linearEquiv _
    (localizedModuleEquivOfExactOfSMulEqZero p'.asIdeal.primeCompl
      (AdicCompletion.map I f) (AdicCompletion.map I g)
      (AdicCompletion.map_injective I hf) (AdicCompletion.map_exact hf hfg hg)
      (p'.asIdeal.primeCompl.pow_mem hbp k) ?_)
  refine fun z => smul_eq_zero_of_mem_map_of_forall_smul_eq_zero (I ^ k)
    (fun c hc => adicCompletion_smul_eq_zero I (hZ c hc)) ?_ z
  rw [Ideal.map_pow]
  exact Ideal.pow_mem_pow hbI k

/-! ### The two depth assumptions for `IᵏM` -/

/-- **Assumption (4) of Situation [Stacks, Tag 0EFU] for `IᵏM`.** The chain-of-primes depth
estimate transfers verbatim: its prime `𝔭` lies outside `V(I)`, where `IᵏM` and `M` have the same
depth. -/
public theorem depth_or_depth_add_dimension_pow_smul_top (S : BootstrapSituation.{u, u, w})
    (k : ℕ) :
    ∀ p r q : PrimeSpectrum S.A,
      p.asIdeal ≤ r.asIdeal → r.asIdeal ≤ q.asIdeal →
      p ∉ PrimeSpectrum.zeroLocus (S.I : Set S.A) →
      r ∈ PrimeSpectrum.zeroLocus (S.I : Set S.A) → r ∉ S.T → q ∈ S.T →
      (enatToEInt
          (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl
              ↥(S.I ^ k • (⊤ : Submodule S.A S.M)))) ≥ (S.s : EInt)) ∨
      (enatToEInt
          (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl
              ↥(S.I ^ k • (⊤ : Submodule S.A S.M)))) +
        krullDimToEInt
          (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
            p.asIdeal.map (algebraMap S.A (Localization.AtPrime q.asIdeal)))) >
        ((S.d + S.s : ℤ) : EInt)) := by
  intro p r q hpr hrq hp hrI hrT hq
  rw [depth_localizedModule_pow_smul_top_eq S.I k p
    (fun hsub => hp (PrimeSpectrum.mem_zeroLocus _ _ |>.2 hsub))]
  exact S.depth_or_depth_add_dimension p r q hpr hrq hp hrI hrT hq

/-- **Assumption (6) of Situation [Stacks, Tag 0EFU] for `IᵏM`.** At a prime `𝔭'` of the
completed localization lying outside the adic locus, the completions of `(IᵏM)_𝔮` and of `M_𝔮`
have the same localization, so the depth bound transfers.

*Argument.* Localization at `𝔮` is exact, so `0 → (IᵏM)_𝔮 → M_𝔮 → (M/IᵏM)_𝔮 → 0` is exact; the
middle term is a finite module over the Noetherian ring `A_𝔮`, so `I_𝔮`-adic completion keeps it
exact (`AdicCompletion.map_exact`) and also keeps the first map injective. The last term is
annihilated by `I_𝔮ᵏ`, hence so is its completion, hence so is `I'ᵏ` by the ideal it generates.
An element `b` of `I'` outside `𝔭'` therefore has `bᵏ` annihilating the cokernel while remaining
outside `𝔭'`, and `localizedModuleEquivOfExactOfSMulEqZero` applies. -/
public theorem completedLocalDepth_pow_smul_top (S : BootstrapSituation.{u, u, w}) (k : ℕ) :
    ∀ q : PrimeSpectrum S.A, q ∈ S.T →
      let Aq := Localization.AtPrime q.asIdeal
      let Iq := S.I.map (algebraMap S.A Aq)
      let Nq := LocalizedModule q.asIdeal.primeCompl ↥(S.I ^ k • (⊤ : Submodule S.A S.M))
      let A' := AdicCompletion Iq Aq
      let I' := Iq.map (algebraMap Aq A')
      let m' := (maximalIdeal Aq).map (algebraMap Aq A')
      ∀ p' : PrimeSpectrum A',
        ¬ I' ≤ p'.asIdeal →
        {r' : Ideal A' | r'.IsPrime ∧ p'.asIdeal ≤ r' ∧ I' ≤ r'} = {m'} →
        enatToEInt
          (Module.depth (Localization.AtPrime p'.asIdeal)
            (maximalIdeal (Localization.AtPrime p'.asIdeal))
            (LocalizedModule p'.asIdeal.primeCompl (AdicCompletion Iq Nq))) >
          (S.s : EInt) := by
  intro q hq
  dsimp only
  intro p' hp'notle huniq
  rw [depth_localizedModule_adicCompletion_eq_of_exact
    (S.I.map (algebraMap S.A (Localization.AtPrime q.asIdeal))) k
    (LocalizedModule.map q.asIdeal.primeCompl (S.I ^ k • (⊤ : Submodule S.A S.M)).subtype)
    (LocalizedModule.map q.asIdeal.primeCompl (S.I ^ k • (⊤ : Submodule S.A S.M)).mkQ)
    (LocalizedModule.map_injective _ _ (Submodule.injective_subtype _))
    (LocalizedModule.map_exact _ _ _ (LinearMap.exact_subtype_mkQ _))
    (LocalizedModule.map_surjective _ _ (Submodule.mkQ_surjective _))
    (fun c hc z => by
      refine smul_eq_zero_of_mem_map_of_forall_smul_eq_zero (S.I ^ k) ?_ ?_ z
      · intro a ha y
        induction y using LocalizedModule.induction_on with
        | _ y s =>
          rw [LocalizedModule.smul'_mk, smul_quotient_pow_smul_top_eq_zero S.I k ha y,
            LocalizedModule.zero_mk]
      · rw [Ideal.map_pow]
        exact hc)
    p' hp'notle]
  exact S.completedLocalDepth q hq p' hp'notle huniq

/-! ### The situation with `M` replaced by `IᵏM` -/

/-- **A bootstrap situation stays one after replacing `M` by `IᵏM`.** The ring, the ideal, the
locus and both bounds are unchanged; only the module moves, to the submodule `IᵏM`, which is
again finite. Assumptions (1) and (3) do not mention the module, and assumptions (4) and (6) are
`depth_or_depth_add_dimension_pow_smul_top` and `completedLocalDepth_pow_smul_top`. -/
public noncomputable def BootstrapSituation.idealPowerSubmodule
    (S : BootstrapSituation.{u, u, w}) (k : ℕ) : BootstrapSituation.{u, u, w} :=
  { S with
    M := ↥(S.I ^ k • (⊤ : Submodule S.A S.M))
    addCommGroup := inferInstance
    module := inferInstance
    finite := finite_pow_smul_top S.I k
    depth_or_depth_add_dimension := depth_or_depth_add_dimension_pow_smul_top S k
    completedLocalDepth := completedLocalDepth_pow_smul_top S k }

end Stacks.Algebraization

end
