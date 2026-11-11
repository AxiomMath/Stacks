module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapPerPrimeProZero
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DualizingExtSystemChartTransport
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationExistence
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.ExtIdealPowerTower
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.LocalDualityExtDetection
public import StacksFrontier.RingTheory.LocalCohomology.IdealPowerProZeroConsequences
public import StacksFrontier.RingTheory.LocalCohomology.UniformLocalizedVanishing

/-!
# The per-prime bound of Tag 0EFX made uniform, and the pro-zero assertion at a general locus

In Situation [Stacks, Tag 0EFU] the proof of [Stacks, Tag 0EFX] produces, for each `𝔮 ∈ T` and
each `i ≤ s`, an index `m'(m, 𝔮)` past which the transition maps
`H^i_{𝔮A_𝔮}((IᵏM)_𝔮) ⟶ H^i_{𝔮A_𝔮}((IᵐM)_𝔮)` vanish. Its last two paragraphs make that index
independent of `𝔮`, and that is what this module proves. With it the pro-zero half of
[Stacks, Tag 0EFX] holds at a **general** specialization-stable `T`, and parts (1), (2) and (4)
of [Stacks, Tag 0EFY] follow at that generality through the engines of
`StacksFrontier/RingTheory/LocalCohomology/IdealPowerProZero.lean`.

## How the uniformity is obtained

Nothing on the local-cohomology side is finite, so the bound cannot be made uniform there. The
source passes to the finite modules `E(n, j) = Ext^j_A(IⁿM, ω)` by local duality, and this module
follows that route with the two transports that are already proved:

* `Dualizing.LocalDuality.comp_eq_zero_of_homologyMap_localCohomology_eq_zero_of_bounded` carries
  the vanishing of `H^i_{𝔮A_𝔮}` over to the vanishing of precomposition on
  `Hom_{D(A_𝔮)}(−, ω_𝔮⟦-δ(𝔮)⟧⟦-i⟧)`;
* `Dualizing.LocalDuality.homologyMap_localCohomology_eq_zero_of_forall_comp_eq_zero_of_bounded`
  carries it back, which is the source's "local duality theorem again (in the opposite
  direction)".

`Dualizing.localized_extIdealPowerTower_map_eq_zero_iff` identifies that precomposition
vanishing with the vanishing of the localization at `𝔮` of a transition map of the direct system
`Dualizing.extIdealPowerTower` of finite `A`-modules. Composing the three gives
`Stacks.Algebraization.localized_localCohomology_map_eq_zero_iff_localized_ext_map_eq_zero`, an
**equivalence**: the two vanishings are the same statement.

On the Ext side the uniformity is `Stacks.LocalCohomology.exists_forall_localized_map_eq_zero`:
the kernels of the transition maps out of a fixed term of a direct system form an ascending chain
in a single Noetherian module, so one index serves every prime of a given set at once. That
replaces the source's spreading-out over a neighbourhood of `𝔮` together with the
quasi-compactness of the locus.

## The δ-stratification, which does not go away

The Ext degree the duality pairs `H^i_𝔮` with is `-δ(𝔮) - i`, because the normalized dualizing
complex of `A_𝔮` is `ω_𝔮⟦-δ(𝔮)⟧` (`Dualizing.dualizingDimension_spec`). So the direct system
whose chain condition is used **depends on `𝔮`** through `δ(𝔮)`, and one system does not serve
all of `T`. The uniformity engine is therefore run once per value of `δ` on `T`, with `T`
replaced by the level set `T_d = {𝔮 ∈ T : δ(𝔮) = d}`, and the finitely many resulting bounds are
maximised: `δ` has finite image by `Stacks.Algebraization.finite_range_dimensionFunction`,
because `A` has finite Krull dimension. What the chain condition removes is the source's
spreading-out and its appeal to quasi-compactness, not the stratification.

## Main results

* `Stacks.Algebraization.localized_localCohomology_map_eq_zero_iff_localized_ext_map_eq_zero` —
  the two sides of local duality, as an equivalence of vanishings, at an arbitrary prime.
* `Stacks.Algebraization.exists_forall_localized_localCohomology_map_eq_zero` — the claim of the
  source's last two paragraphs: one index serves every `𝔮 ∈ T`.
* `Stacks.Algebraization.exists_map_idealPowerTower_eq_zero` — the pro-zero half of
  [Stacks, Tag 0EFX] at a general specialization-stable `T`, in every degree `i ≤ s`.
* `Stacks.Algebraization.exists_forall_injective_localCohomologyAdicProjection`,
  `Stacks.Algebraization.isMittagLefflerCategorical_localCohomologyAdicTower`,
  `Stacks.Algebraization.isIso_limitLift_localCohomologyAdicCone` — parts (1), (2) and (4) of
  [Stacks, Tag 0EFY] at a general specialization-stable `T`.

## References

* [Stacks Project, Tag 0EFX](https://stacks.math.columbia.edu/tag/0EFX)
* [Stacks Project, Tag 0EFY](https://stacks.math.columbia.edu/tag/0EFY)
* [Stacks Project, Tag 0EFU](https://stacks.math.columbia.edu/tag/0EFU)
* [Stacks Project, Tag 0A7W](https://stacks.math.columbia.edu/tag/0A7W)
* [Stacks Project, Tag 0A80](https://stacks.math.columbia.edu/tag/0A80)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

/-- **Precomposition kills every morphism into one object exactly when it kills every morphism
into an isomorphic one.** -/
theorem forall_comp_eq_zero_iff_of_iso {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
    {K K' X Y : C} (g : K' ⟶ K) (e : X ≅ Y) :
    (∀ u : K ⟶ X, g ≫ u = 0) ↔ ∀ u : K ⟶ Y, g ≫ u = 0 := by
  refine ⟨fun hX u => ?_, fun hY u => ?_⟩
  · simpa using congrArg (· ≫ e.hom) (hX (u ≫ e.inv))
  · simpa using congrArg (· ≫ e.inv) (hY (u ≫ e.hom))

/-- **The two sides of local duality at a prime `𝔮`, as an equivalence of vanishings.** For a
Noetherian ring `A` with a dualizing complex `ω`, a finite module `M`, an ideal `I` and a prime
`𝔮`, the transition map

`H^i_{𝔮A_𝔮}((IᵏM)_𝔮) ⟶ H^i_{𝔮A_𝔮}((IᵐM)_𝔮)`

vanishes exactly when the localization at `𝔮` of the transition map

`Ext^{-δ(𝔮)-i}_A(IᵐM, ω) ⟶ Ext^{-δ(𝔮)-i}_A(IᵏM, ω)`

of the direct system `Dualizing.extIdealPowerTower` vanishes.

The left-to-right direction is the local duality theorem in the direction the source uses first;
the right-to-left direction is its use "again (in the opposite direction)". The Ext degree is
`-δ(𝔮) - i` because `ω_𝔮⟦-δ(𝔮)⟧` is the normalized dualizing complex of `A_𝔮`, and the two
transports are stated at a normalized complex. Both are applied through their bounded forms, so
the finiteness side condition is discharged from the boundedness and finite cohomology of a
module in degree zero and of a dualizing complex. -/
theorem localized_localCohomology_map_eq_zero_iff_localized_ext_map_eq_zero
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : ModuleCat.{u} A) [Module.Finite A M]
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : Dualizing.IsDualizingComplex ω)
    (q : PrimeSpectrum A) (i : ℤ) {m k : ℕ} (h : m ≤ k) :
    ((idealPowerTower.{u, u} I M ⋙
        ModuleCat.localizedModuleFunctor.{u} q.asIdeal.primeCompl ⋙
        localCohomologyModuleFunctor (Localization q.asIdeal.primeCompl) i).map
          (homOfLE h).op = 0) ↔
      (Dualizing.extIdealPowerTower A I M ω
          (-Dualizing.dualizingDimension.{u, u} ω q - i) ⋙
        ModuleCat.localizedModuleFunctor.{u} q.asIdeal.primeCompl).map (homOfLE h) = 0 := by
  classical
  let : IsNoetherianRing (Localization q.asIdeal.primeCompl) :=
    IsLocalization.isNoetherianRing q.asIdeal.primeCompl _ inferInstance
  -- a finite generating family of the maximal ideal of `A_𝔮`, and an injective hull of its
  -- residue field
  obtain ⟨r, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.1
    (Ideal.fg_of_isNoetherianRing
      (IsLocalRing.maximalIdeal (Localization q.asIdeal.primeCompl)))
  obtain ⟨E, ιE, hmono, hhull⟩ := Module.exists_isInjectiveHull
    (Localization q.asIdeal.primeCompl)
    ((ModuleCat.uliftFunctor.{u} (Localization q.asIdeal.primeCompl)).obj
      (ModuleCat.of (Localization q.asIdeal.primeCompl)
        (IsLocalRing.ResidueField (Localization q.asIdeal.primeCompl))))
  let : Mono ιE := hmono
  -- the normalized dualizing complex of `A_𝔮`
  have hω' := Dualizing.isNormalizedDualizingComplex_localizedModuleFunctor_shift_dualizingDimension
    A ω hω q
  obtain ⟨b, hb⟩ := exists_isGE_of_isDualizingComplex _ hω'.1
  have : (((ModuleCat.localizedModuleFunctor.{u} q.asIdeal.primeCompl).mapDerivedCategory.obj
      ω)⟦-Dualizing.dualizingDimension.{u, u} ω q⟧).IsGE b := hb
  have hbshift : ((((ModuleCat.localizedModuleFunctor.{u}
      q.asIdeal.primeCompl).mapDerivedCategory.obj
      ω)⟦-Dualizing.dualizingDimension.{u, u} ω q⟧)⟦-i⟧).IsGE (b + i) :=
    (DerivedCategory.TStructure.t).isGE_shift _ b (-i) (b + i) (by ring)
  -- the two modules in play are finite over `A_𝔮`
  have hfin (n : ℕ) : Module.Finite (Localization q.asIdeal.primeCompl)
      ((ModuleCat.localizedModuleFunctor.{u} q.asIdeal.primeCompl).obj
        ((idealPowerTower.{u, u} I M).obj (op n))) := by
    have := finite_idealPowerTower_obj I M (op n)
    change Module.Finite (Localization q.asIdeal.primeCompl)
      (((idealPowerTower.{u, u} I M).obj (op n)).localizedModule q.asIdeal.primeCompl)
    exact Module.Finite.of_isLocalizedModule q.asIdeal.primeCompl
      (((idealPowerTower.{u, u} I M).obj (op n)).localizedModuleMkLinearMap
        q.asIdeal.primeCompl)
  have := hfin m
  have := hfin k
  -- the shift comparison `ω_𝔮⟦-δ-i⟧ ≅ (ω_𝔮⟦-δ⟧)⟦-i⟧`
  have hshiftIso := (shiftFunctorAdd'
    (DerivedCategory (ModuleCat.{u} (Localization q.asIdeal.primeCompl)))
    (-Dualizing.dualizingDimension.{u, u} ω q) (-i)
    (-Dualizing.dualizingDimension.{u, u} ω q - i) (by ring)).app
    ((ModuleCat.localizedModuleFunctor.{u} q.asIdeal.primeCompl).mapDerivedCategory.obj ω)
  rw [show (idealPowerTower.{u, u} I M ⋙
        ModuleCat.localizedModuleFunctor.{u} q.asIdeal.primeCompl ⋙
        localCohomologyModuleFunctor (Localization q.asIdeal.primeCompl) i).map
          (homOfLE h).op =
      (DerivedCategory.homologyFunctor
          (ModuleCat.{u} (Localization q.asIdeal.primeCompl)) i).map
        ((CechFormula.localCohomologyEndofunctor (Localization q.asIdeal.primeCompl)
          (IsLocalRing.maximalIdeal (Localization q.asIdeal.primeCompl))
          (IsNoetherian.noetherian _)).map
          ((DerivedCategory.singleFunctor
            (ModuleCat.{u} (Localization q.asIdeal.primeCompl)) 0).map
            ((ModuleCat.localizedModuleFunctor.{u} q.asIdeal.primeCompl).map
              ((idealPowerTower.{u, u} I M).map (homOfLE h).op)))) from rfl,
    Dualizing.localized_extIdealPowerTower_map_eq_zero_iff A I M ω
      (exists_isGE_of_isDualizingComplex _ hω) _ q h,
    forall_comp_eq_zero_iff_of_iso _ hshiftIso]
  exact ⟨Dualizing.LocalDuality.comp_eq_zero_of_homologyMap_localCohomology_eq_zero_of_bounded
      (Localization q.asIdeal.primeCompl) f hf _ hω' ιE hhull i _ 0 (b + i) inferInstance
      hbshift (Dualizing.finite_homology_single _)
      (Dualizing.finite_homology_shift _ hω'.1.finiteCohomology (-i)),
    Dualizing.LocalDuality.homologyMap_localCohomology_eq_zero_of_forall_comp_eq_zero_of_bounded
      (Localization q.asIdeal.primeCompl) f hf _ hω' ιE hhull i _ 0 (b + i) inferInstance
      hbshift (Dualizing.finite_homology_single _)
      (Dualizing.finite_homology_shift _ hω'.1.finiteCohomology (-i))⟩

/-! ### The δ-stratification, and the uniform bound -/

/-- **The claim of the last two paragraphs of the proof of [Stacks, Tag 0EFX]: the per-prime
bound can be chosen independently of `𝔮 ∈ T`.** In Situation [Stacks, Tag 0EFU], for every
degree `i ≤ s` and every `m` there is a `k₀ ≥ m` such that for all `k ≥ k₀` and **all** `𝔮 ∈ T`
the transition map

`H^i_{𝔮A_𝔮}((IᵏM)_𝔮) ⟶ H^i_{𝔮A_𝔮}((IᵐM)_𝔮)`

vanishes.

*Proof.* Fix a dualizing complex `ω` and let `δ` be its dimension function. By
`Stacks.Algebraization.localized_localCohomology_map_eq_zero_iff_localized_ext_map_eq_zero` the
vanishing above is, at a prime `𝔮` with `δ(𝔮) = d`, the vanishing of the localization at `𝔮` of a
transition map of the direct system `Dualizing.extIdealPowerTower A I M ω (-d-i)` of **finite**
`A`-modules. For a fixed `d` the ascending chain condition in the single Noetherian module
`E(m, -d-i)` therefore produces one index serving every `𝔮` of the level set `T ∩ δ⁻¹(d)`
(`Stacks.LocalCohomology.exists_forall_localized_map_eq_zero`); the per-prime vanishing feeding
it is `Stacks.Algebraization.exists_localized_localCohomology_idealPowerTower_map_eq_zero`. The
Ext degree depends on `𝔮` only through `δ(𝔮)`, which takes finitely many values because `A` has
finite Krull dimension (`Stacks.Algebraization.finite_range_dimensionFunction`), so the finitely
many indices have a maximum. -/
theorem exists_forall_localized_localCohomology_map_eq_zero
    (S : BootstrapSituation.{u, u, u}) (i : ℤ) (hi : i ≤ S.s) (m : ℕ) :
    ∃ (k₀ : ℕ) (h₀ : m ≤ k₀), ∀ (k : ℕ) (hk : k₀ ≤ k), ∀ q ∈ S.T,
      (idealPowerTower.{u, u} S.I (ModuleCat.of S.A S.M) ⋙
        ModuleCat.localizedModuleFunctor.{u} q.asIdeal.primeCompl ⋙
        localCohomologyModuleFunctor (Localization q.asIdeal.primeCompl) i).map
          (homOfLE (h₀.trans hk)).op = 0 := by
  classical
  obtain ⟨ω, hω⟩ := S.dualizing
  have hδfin : (Set.range (Dualizing.dualizingDimension.{u, u} ω)).Finite :=
    finite_range_dimensionFunction_of_ringKrullDim_lt_top
      (Dualizing.dualizingDimensionFunction.{u, u} ω hω) S.ringKrullDim_lt_top
  -- one bound per value of `δ`, from the chain condition in the Ext system of that degree
  have key : ∀ d : ℤ, ∃ (k₀ : ℕ) (h₀ : m ≤ k₀), ∀ (k : ℕ) (hk : k₀ ≤ k), ∀ q ∈ S.T,
      Dualizing.dualizingDimension.{u, u} ω q = d →
      (idealPowerTower.{u, u} S.I (ModuleCat.of S.A S.M) ⋙
        ModuleCat.localizedModuleFunctor.{u} q.asIdeal.primeCompl ⋙
        localCohomologyModuleFunctor (Localization q.asIdeal.primeCompl) i).map
          (homOfLE (h₀.trans hk)).op = 0 := by
    intro d
    have := Dualizing.finite_extIdealPowerTower_obj S.A S.I (ModuleCat.of S.A S.M) ω hω
      (-d - i) m
    obtain ⟨k₀, h₀, hk₀⟩ := exists_forall_localized_map_eq_zero.{u, u}
      (Dualizing.extIdealPowerTower S.A S.I (ModuleCat.of S.A S.M) ω (-d - i)) m
      (isNoetherian_of_isNoetherianRing_of_finite S.A _)
      {q : PrimeSpectrum S.A | q ∈ S.T ∧ Dualizing.dualizingDimension.{u, u} ω q = d}
      (fun q hq => by
        obtain ⟨c, hmc, hc⟩ :=
          exists_localized_localCohomology_idealPowerTower_map_eq_zero S q hq.1 i hi m
        refine ⟨c, hmc, ?_⟩
        rw [← hq.2]
        exact (localized_localCohomology_map_eq_zero_iff_localized_ext_map_eq_zero
          S.I (ModuleCat.of S.A S.M) ω hω q i hmc).1 hc)
    refine ⟨k₀, h₀, fun k hk q hqT hqd => ?_⟩
    refine (localized_localCohomology_map_eq_zero_iff_localized_ext_map_eq_zero
      S.I (ModuleCat.of S.A S.M) ω hω q i (h₀.trans hk)).2 ?_
    rw [hqd]
    exact hk₀ k hk q ⟨hqT, hqd⟩
  choose k₀ h₀ hk₀ using key
  refine ⟨max m (hδfin.toFinset.sup k₀), le_max_left _ _, fun k hk q hqT => ?_⟩
  exact hk₀ (Dualizing.dualizingDimension.{u, u} ω q) k
    (le_trans (le_trans (Finset.le_sup (f := k₀)
      (hδfin.mem_toFinset.2 ⟨q, rfl⟩)) (le_max_right _ _)) hk) q hqT rfl

/-! ### Tag 0EFX at a general specialization-stable locus -/

/-- **Stacks Project, Tag 0EFX**, the pro-zero assertion, at a general specialization-stable `T`.
In Situation [Stacks, Tag 0EFU] the inverse system `{H^i_T(IⁿM)}` is pro-zero for every `i ≤ s`:
for every `m` some transition map `H^i_T(IᵏM) ⟶ H^i_T(IᵐM)` vanishes.

This is the source's proof carried out in full. The per-prime assertion at each `𝔮 ∈ T` is
`Stacks.Algebraization.exists_localized_localCohomology_idealPowerTower_map_eq_zero`; its bound
is made independent of `𝔮` by
`Stacks.Algebraization.exists_forall_localized_localCohomology_map_eq_zero`, which is the
local-duality paragraph; and the passage from the uniform per-prime statement to the global one
is `Stacks.Algebraization.exists_map_idealPowerTower_eq_zero_of_uniform`, i.e. Lemma
[Stacks, Tag 0EF9]. Nothing is assumed beyond the data of Situation [Stacks, Tag 0EFU]. -/
@[stacks 0EFX "the pro-zero assertion in degrees 0 ≤ i ≤ s at a general specialization-stable T \
in Situation 0EFU"]
theorem exists_map_idealPowerTower_eq_zero (S : BootstrapSituation.{u, u, u}) (i : ℕ)
    (hi : (i : ℤ) ≤ S.s) (m : ℕ) :
    ∃ k : ℕ, ∃ h : m ≤ k,
      (localCohomologyWithSupportInModuleFunctor.{u, u} S.A S.T (i : ℤ)).map
        ((idealPowerTower.{u, u} S.I (ModuleCat.of S.A S.M)).map (homOfLE h).op) = 0 := by
  choose m' hm' hu using fun n : ℕ =>
    exists_forall_localized_localCohomology_map_eq_zero S (i : ℤ) hi n
  exact exists_map_idealPowerTower_eq_zero_of_uniform S i m' hm' hu m

/-- **Stacks Project, Tag 0EFX**, the pro-zero assertion, in **every** degree `i ≤ s` and at a
general specialization-stable `T`. In Situation [Stacks, Tag 0EFU] the inverse system
`{H^i_T(IⁿM)}` is pro-zero for every `i ≤ s`: for every `m` some transition map
`H^i_T(IᵏM) ⟶ H^i_T(IᵐM)` vanishes.

In negative degrees the system vanishes term by term
(`Stacks.LocalCohomology.exists_map_idealPowerTower_eq_zero_of_neg`); in degrees `0 ≤ i ≤ s`
this is `Stacks.Algebraization.exists_map_idealPowerTower_eq_zero`, whose proof is the source's
own, the local-duality paragraph included. This is also the form in which the consequences of
[Stacks, Tag 0EFY] consume the assertion. -/
@[stacks 0EFX "the pro-zero assertion in every degree i ≤ s at a general \
specialization-stable T in Situation 0EFU"]
theorem isProZeroIdealPowerCohomology (S : BootstrapSituation.{u, u, u}) (i : ℤ)
    (hi : i ≤ S.s) :
    IsProZeroIdealPowerCohomology.{u, u} S.T S.I (ModuleCat.of S.A S.M) i := by
  intro m
  by_cases hneg : i < 0
  · exact exists_map_idealPowerTower_eq_zero_of_neg.{u, u} S.T S.I
      (ModuleCat.of S.A S.M) i hneg m
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = (j : ℤ) :=
      ⟨i.toNat, (Int.toNat_of_nonneg (not_lt.mp hneg)).symm⟩
    exact exists_map_idealPowerTower_eq_zero S j hi m

/-! ### Parts (1), (2) and (4) of Tag 0EFY at a general specialization-stable locus -/

/-- **Stacks Project, Tag 0EFY, part (1)**, at a general specialization-stable `T`. In Situation
[Stacks, Tag 0EFU] there is an `m₀` such that `H^i_T(M) ⟶ H^i_T(M/IⁿM)` is injective for every
`i ≤ s` and every `n ≥ m₀`.

This is `Stacks.LocalCohomology.exists_forall_injective_localCohomologyAdicProjection_of_proZero`
with its hypothesis discharged by
`Stacks.Algebraization.isProZeroIdealPowerCohomology`. -/
theorem exists_forall_injective_localCohomologyAdicProjection
    (S : BootstrapSituation.{u, u, u}) :
    ∃ m₀ : ℕ, ∀ i ≤ S.s, ∀ n : ℕ, m₀ ≤ n →
      Function.Injective ((localCohomologyAdicCone.{u, u} S.A S.T S.I i
        (ModuleCat.of S.A S.M)).π.app (op n)).hom :=
  exists_forall_injective_localCohomologyAdicProjection_of_proZero.{u, u} S.T S.I
    (ModuleCat.of S.A S.M) S.s (fun i hi => isProZeroIdealPowerCohomology S i hi 0)

/-- **Stacks Project, Tag 0EFY, part (2)**, at a general specialization-stable `T`. In Situation
[Stacks, Tag 0EFU] the inverse system `{H^i_T(M/IⁿM)}` satisfies the Mittag-Leffler condition
for `i < s`.

This is `Stacks.LocalCohomology.isMittagLefflerCategorical_localCohomologyAdicTower_of_proZero`
with its hypothesis — pro-zero-ness in degree `i + 1`, which is `≤ s` exactly when `i < s` —
discharged by `Stacks.Algebraization.isProZeroIdealPowerCohomology`. -/
theorem isMittagLefflerCategorical_localCohomologyAdicTower
    (S : BootstrapSituation.{u, u, u}) (i : ℤ) (hi : i + 1 ≤ S.s) :
    IsMittagLefflerCategorical (localCohomologyAdicTower.{u, u} S.A S.T S.I i
      (ModuleCat.of S.A S.M)) :=
  isMittagLefflerCategorical_localCohomologyAdicTower_of_proZero.{u, u} S.T S.I
    (ModuleCat.of S.A S.M) i (isProZeroIdealPowerCohomology S (i + 1) hi)

/-- **Stacks Project, Tag 0EFY, part (4)**, at a general specialization-stable `T`. In Situation
[Stacks, Tag 0EFU] the canonical map `H^i_T(M) ⟶ lim H^i_T(M/IⁿM)` is an isomorphism for
`i < s`.

This is `Stacks.LocalCohomology.isIso_limitLift_localCohomologyAdicCone_of_proZero` with both of
its hypotheses — pro-zero-ness in degrees `i` and `i + 1`, both `≤ s` exactly when `i < s` —
discharged by `Stacks.Algebraization.isProZeroIdealPowerCohomology`. -/
theorem isIso_limitLift_localCohomologyAdicCone
    (S : BootstrapSituation.{u, u, u}) (i : ℤ) (hi : i + 1 ≤ S.s) :
    IsIso (limit.lift (localCohomologyAdicTower.{u, u} S.A S.T S.I i (ModuleCat.of S.A S.M))
      (localCohomologyAdicCone.{u, u} S.A S.T S.I i (ModuleCat.of S.A S.M))) :=
  isIso_limitLift_localCohomologyAdicCone_of_proZero.{u, u} S.T S.I (ModuleCat.of S.A S.M) i
    (isProZeroIdealPowerCohomology S i (by omega))
    (isProZeroIdealPowerCohomology S (i + 1) hi)

end Stacks.Algebraization

end
