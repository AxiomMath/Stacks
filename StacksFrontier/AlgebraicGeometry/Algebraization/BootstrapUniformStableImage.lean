module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapUniformProZero
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.LocalizedStableImageTransport
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.UniformLocalizedStableImage
public import StacksFrontier.RingTheory.LocalCohomology.IdealPowerProZeroLowDegree

/-!
# The stable-image half of Tag 0EFX at a general specialization-stable locus

`StacksFrontier/AlgebraicGeometry/Algebraization/BootstrapUniformProZero.lean` carries out the
uniformity paragraph of [Stacks, Tag 0EFX] for the **pro-zero** half, in degrees `i ≤ s`. This
module does the same for the remaining, degree `s + 1`, assertion: the image of
`H^{s+1}_T(IᵏM) ⟶ H^{s+1}_T(IᵐM)` maps injectively into `H^{s+1}_T(I^{m₀}M)` for all large `k`.

## The shape of the assertion, and why it is not a vanishing

The hypothesis `hloc` of the globalization lemma [Stacks, Tag 0EFA] asks, at every `𝔮 ∈ T`, for a
containment of **kernels**

`ker(H^{s+1}_{𝔮A_𝔮}((IᵏM)_𝔮) ⟶ H^{s+1}_{𝔮A_𝔮}(M_𝔮))
  ⊆ ker(H^{s+1}_{𝔮A_𝔮}((IᵏM)_𝔮) ⟶ H^{s+1}_{𝔮A_𝔮}((IᵐM)_𝔮))`

(that the transition image inject into the zeroth term is this containment, the zeroth term of the
ideal-power tower being `M` itself). Neither of the two available local-duality transports speaks of a
kernel: both carry the vanishing of a map on local cohomology to and from the vanishing of a map of
Ext modules. The containment above is nevertheless **reformulated as one vanishing**, and that is
the content of `Dualizing.LocalDuality.ker_le_ker_localCohomologyModuleFunctor_iff_range_le_range`:
the long exact sequence turns the left-hand kernel into the image of the connecting morphism of
`0 → IᵏM → M → M/IᵏM → 0`, so the containment is the vanishing of **one** morphism of `D(A_𝔮)`,
and the same distinguished triangle read through `Hom(−, ω⟦-i⟧)` turns that vanishing into a
containment of images of Ext. No new duality theorem is needed.

## The uniformity

With the assertion on the Ext side it is, at a prime `𝔮` with `δ(𝔮) = d` and `j = -d-s-1`,

`im(E(m, j)_𝔮 ⟶ E(k, j)_𝔮) ⊆ im(E(0, j)_𝔮 ⟶ E(k, j)_𝔮)`,  `E(n, j) = Ext^j_A(IⁿM, ω)`,

and `E(0, j) ⟶ E(k, j)` factors through `E(m, j) ⟶ E(k, j)`, so the containment says exactly that
`E(m, j)_𝔮` is the sum of the image of `E(0, j)_𝔮` and the kernel of `E(m, j)_𝔮 ⟶ E(k, j)_𝔮`.
Those kernels form an ascending chain in the single **finite** module `E(m, j)`, hence are
constant from one index on — globally, at an index depending on neither `𝔮` nor the point of the
chain. That is `Stacks.Algebraization.exists_forall_localized_stableImage`, and it replaces the
source's spreading-out over a neighbourhood of `𝔮` together with the quasi-compactness of the
locus, exactly as in the pro-zero half. As there, the Ext degree depends on `𝔮` through `δ(𝔮)`,
which takes finitely many values, so the engine is run once per value and the bounds are
maximised.

## Main results

* `Stacks.Algebraization.exists_localized_ker_le_ker_idealPowerTower` — the per-prime assertion at
  an arbitrary `𝔮 ∈ T`, from the closed-point case over `A_𝔮`.
* `Stacks.Algebraization.exists_forall_localized_ker_le_ker_idealPowerTower` — the same with one
  index serving every `𝔮 ∈ T`.
* `Stacks.Algebraization.exists_hasStableImageIdealPowerCohomology` — the stable-image assertion
  of [Stacks, Tag 0EFX] at a general specialization-stable `T`.
* `Stacks.Algebraization.isProZero_and_hasStableImage_idealPowerCohomology` — **both assertions of
  [Stacks, Tag 0EFX]** at a general specialization-stable `T`.
* `Stacks.Algebraization.exists_injective_limitLift_and_smul_mem_range` — part (6) of
  [Stacks, Tag 0EFY] at a general specialization-stable `T`.

## References

* [Stacks Project, Tag 0EFX](https://stacks.math.columbia.edu/tag/0EFX)
* [Stacks Project, Tag 0EFY](https://stacks.math.columbia.edu/tag/0EFY)
* [Stacks Project, Tag 0EFU](https://stacks.math.columbia.edu/tag/0EFU)
* [Stacks Project, Tag 0EFA](https://stacks.math.columbia.edu/tag/0EFA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Opposite

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

/-! ### The per-prime assertion at an arbitrary point of the locus -/

/-- **The per-prime stable-image assertion of [Stacks, Tag 0EFX] at an arbitrary `𝔮 ∈ T`.** In
Situation [Stacks, Tag 0EFU], for every `𝔮 ∈ T` and every `m` there is a `c ≥ m` such that for all
`k ≥ c` a class of `H^{s+1}_{𝔮A_𝔮}((IᵏM)_𝔮)` dying in `H^{s+1}_{𝔮A_𝔮}(M_𝔮)` already dies in
`H^{s+1}_{𝔮A_𝔮}((IᵐM)_𝔮)`.

This is the first paragraph of the proof of [Stacks, Tag 0EFX] at the prime `𝔮`: over `A_𝔮` the
locus becomes the closed point, where the assertion is
`Stacks.Algebraization.hasStableImageIdealPowerCohomology_closedPoint` for the situation
`Stacks.Algebraization.BootstrapSituation.localizeClosedPoint`. What is done here is the
bookkeeping between the three spellings of the same system, as in
`Stacks.Algebraization.exists_localized_localCohomology_idealPowerTower_map_eq_zero`, with
`Stacks.LocalCohomology.natIso_ker_le_ker_iff` in place of
`Stacks.LocalCohomology.natIso_map_eq_zero_iff`.

*What this does not give.* The bound `c` depends on `𝔮`. -/
theorem exists_localized_ker_le_ker_idealPowerTower (S : BootstrapSituation.{u, u, u})
    (q : PrimeSpectrum S.A) (hq : q ∈ S.T) (m : ℕ) :
    ∃ (c : ℕ) (hmc : m ≤ c), ∀ (k : ℕ) (hck : c ≤ k),
      LinearMap.ker ((idealPowerTower.{u, u} S.I (ModuleCat.of S.A S.M) ⋙
            ModuleCat.localizedModuleFunctor.{u} q.asIdeal.primeCompl ⋙
            localCohomologyModuleFunctor (Localization q.asIdeal.primeCompl) (S.s + 1)).map
          (homOfLE (Nat.zero_le k)).op).hom ≤
        LinearMap.ker ((idealPowerTower.{u, u} S.I (ModuleCat.of S.A S.M) ⋙
            ModuleCat.localizedModuleFunctor.{u} q.asIdeal.primeCompl ⋙
            localCohomologyModuleFunctor (Localization q.asIdeal.primeCompl) (S.s + 1)).map
          (homOfLE (hmc.trans hck)).op).hom := by
  have : IsNoetherianRing (Localization q.asIdeal.primeCompl) :=
    IsLocalization.isNoetherianRing q.asIdeal.primeCompl _ inferInstance
  have : IsLocalRing (BootstrapSituation.localizeClosedPoint S q hq).A :=
    inferInstanceAs (IsLocalRing (Localization q.asIdeal.primeCompl))
  obtain ⟨c, hmc, hc⟩ := hasStableImageIdealPowerCohomology_closedPoint
    (BootstrapSituation.localizeClosedPoint S q hq) rfl m (Nat.zero_le m)
  refine ⟨c, hmc, fun k hck => ?_⟩
  -- the closed-point assertion, read as a containment of kernels
  have hker : LinearMap.ker ((idealPowerTower.{u, u}
            (S.I.map (algebraMap S.A (Localization q.asIdeal.primeCompl)))
            (ModuleCat.of (Localization q.asIdeal.primeCompl)
              (LocalizedModule q.asIdeal.primeCompl S.M)) ⋙
          localCohomologyWithSupportInModuleFunctor.{u, u}
            (Localization q.asIdeal.primeCompl)
            {closedPoint (Localization q.asIdeal.primeCompl)} (S.s + 1)).map
        (homOfLE (Nat.zero_le k)).op).hom ≤
      LinearMap.ker ((idealPowerTower.{u, u}
            (S.I.map (algebraMap S.A (Localization q.asIdeal.primeCompl)))
            (ModuleCat.of (Localization q.asIdeal.primeCompl)
              (LocalizedModule q.asIdeal.primeCompl S.M)) ⋙
          localCohomologyWithSupportInModuleFunctor.{u, u}
            (Localization q.asIdeal.primeCompl)
            {closedPoint (Localization q.asIdeal.primeCompl)} (S.s + 1)).map
        (homOfLE (hmc.trans hck)).op).hom := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    refine hc k hck x ?_
    rw [LinearMap.mem_ker]
    exact (inverseSystem_transition_comp_apply.{u, u} _ (Nat.zero_le m) (hmc.trans hck) x).trans hx
  -- the three spellings of the same inverse system
  refine (natIso_ker_le_ker_iff (localizedIdealPowerTowerLocalCohomologyIso.{u, u}
    q.asIdeal.primeCompl S.I (ModuleCat.of S.A S.M) (S.s + 1))
    (homOfLE (Nat.zero_le k)).op (homOfLE (hmc.trans hck)).op).2 ?_
  refine (natIso_ker_le_ker_iff (Functor.isoWhiskerRight
    (idealPowerTowerIsoOfIso.{u, u}
      (S.I.map (algebraMap S.A (Localization q.asIdeal.primeCompl)))
      (localizedModuleShrinkIso S q.asIdeal.primeCompl))
    (localCohomologyModuleFunctor (Localization q.asIdeal.primeCompl) (S.s + 1)))
    (homOfLE (Nat.zero_le k)).op (homOfLE (hmc.trans hck)).op).2 ?_
  refine (natIso_ker_le_ker_iff
    (localCohomologyWithSupportInModuleFunctorIso (Localization q.asIdeal.primeCompl)
      (maximalIdeal (Localization q.asIdeal.primeCompl)) (IsNoetherian.noetherian _) (S.s + 1))
    ((idealPowerTower.{u, u}
        (S.I.map (algebraMap S.A (Localization q.asIdeal.primeCompl)))
        (ModuleCat.of (Localization q.asIdeal.primeCompl)
          (LocalizedModule q.asIdeal.primeCompl S.M))).map (homOfLE (Nat.zero_le k)).op)
    ((idealPowerTower.{u, u}
        (S.I.map (algebraMap S.A (Localization q.asIdeal.primeCompl)))
        (ModuleCat.of (Localization q.asIdeal.primeCompl)
          (LocalizedModule q.asIdeal.primeCompl S.M))).map
      (homOfLE (hmc.trans hck)).op)).1 ?_
  rw [show PrimeSpectrum.zeroLocus
      ((maximalIdeal (Localization q.asIdeal.primeCompl) :
        Ideal (Localization q.asIdeal.primeCompl)) :
        Set (Localization q.asIdeal.primeCompl)) =
      {closedPoint (Localization q.asIdeal.primeCompl)} from zeroLocus_maximalIdeal]
  exact hker

/-! ### The per-prime assertion made uniform -/

/-- The localization of a transition map of the ideal-power tower is injective: the map is an
inclusion of submodules, and localization is exact. -/
theorem injective_localized_idealPowerTower_map {A : Type u} [CommRing A] [IsNoetherianRing A]
    (T : Submonoid A) (I : Ideal A) (M : ModuleCat.{u} A) {m k : ℕ} (h : m ≤ k) :
    Function.Injective ((ModuleCat.localizedModuleFunctor.{u} T).map
      ((idealPowerTower.{u, u} I M).map (homOfLE h).op)).hom :=
  injective_localizedModuleFunctor_map T _ fun _ _ hab =>
    Subtype.ext (congrArg (fun z : ↥(I ^ m • (⊤ : Submodule A M)) => (z : M)) hab)

/-- **The claim of the last two paragraphs of the proof of [Stacks, Tag 0EFX] for the degree
`s + 1` assertion: the per-prime bound can be chosen independently of `𝔮 ∈ T`.** In Situation
[Stacks, Tag 0EFU], for every `m` there is a `k₀ ≥ m` such that for all `k ≥ k₀` and **all**
`𝔮 ∈ T` a class of `H^{s+1}_{𝔮A_𝔮}((IᵏM)_𝔮)` dying in `H^{s+1}_{𝔮A_𝔮}(M_𝔮)` already dies in
`H^{s+1}_{𝔮A_𝔮}((IᵐM)_𝔮)`.

*Proof.* Fix a dualizing complex `ω` and let `δ` be its dimension function. By
`Stacks.Algebraization.localized_ker_le_ker_localCohomology_iff_exists_localized_ext` the
containment above is, at a prime `𝔮` with `δ(𝔮) = d`, the statement that every value of the
localization at `𝔮` of `E(m, j) ⟶ E(k, j)` is a value of `E(0, j) ⟶ E(k, j)`, where
`E(n, j) = Ext^j_A(IⁿM, ω)` and `j = -d-s-1` — a statement about maps of **finite** `A`-modules.
For a fixed `d` the ascending chain condition in the single Noetherian module `E(m, j)` therefore
produces one index serving every `𝔮` of the level set `T ∩ δ⁻¹(d)`
(`Stacks.Algebraization.exists_forall_localized_stableImage`); the per-prime containment feeding it
is `Stacks.Algebraization.exists_localized_ker_le_ker_idealPowerTower`. The Ext degree depends on
`�` only through `δ(𝔮)`, which takes finitely many values because `A` has finite Krull dimension
(`Stacks.Algebraization.finite_range_dimensionFunction`), so the finitely many indices have a
maximum. -/
theorem exists_forall_localized_ker_le_ker_idealPowerTower (S : BootstrapSituation.{u, u, u})
    (j : ℤ) (hj : j = S.s + 1) (m : ℕ) :
    ∃ (k₀ : ℕ) (h₀ : m ≤ k₀), ∀ (k : ℕ) (hk : k₀ ≤ k), ∀ q ∈ S.T,
      LinearMap.ker ((idealPowerTower.{u, u} S.I (ModuleCat.of S.A S.M) ⋙
            ModuleCat.localizedModuleFunctor.{u} q.asIdeal.primeCompl ⋙
            localCohomologyModuleFunctor (Localization q.asIdeal.primeCompl) j).map
          (homOfLE (Nat.zero_le k)).op).hom ≤
        LinearMap.ker ((idealPowerTower.{u, u} S.I (ModuleCat.of S.A S.M) ⋙
            ModuleCat.localizedModuleFunctor.{u} q.asIdeal.primeCompl ⋙
            localCohomologyModuleFunctor (Localization q.asIdeal.primeCompl) j).map
          (homOfLE (h₀.trans hk)).op).hom := by
  classical
  subst hj
  obtain ⟨ω, hω⟩ := S.dualizing
  have hδfin : (Set.range (Dualizing.dualizingDimension.{u, u} ω)).Finite :=
    finite_range_dimensionFunction_of_ringKrullDim_lt_top
      (Dualizing.dualizingDimensionFunction.{u, u} ω hω) S.ringKrullDim_lt_top
  -- one bound per value of `δ`, from the chain condition in the Ext system of that degree
  have key : ∀ d : ℤ, ∃ (k₀ : ℕ) (h₀ : m ≤ k₀), ∀ (k : ℕ) (hk : k₀ ≤ k), ∀ q ∈ S.T,
      Dualizing.dualizingDimension.{u, u} ω q = d →
      LinearMap.ker ((idealPowerTower.{u, u} S.I (ModuleCat.of S.A S.M) ⋙
            ModuleCat.localizedModuleFunctor.{u} q.asIdeal.primeCompl ⋙
            localCohomologyModuleFunctor (Localization q.asIdeal.primeCompl) (S.s + 1)).map
          (homOfLE (Nat.zero_le k)).op).hom ≤
        LinearMap.ker ((idealPowerTower.{u, u} S.I (ModuleCat.of S.A S.M) ⋙
            ModuleCat.localizedModuleFunctor.{u} q.asIdeal.primeCompl ⋙
            localCohomologyModuleFunctor (Localization q.asIdeal.primeCompl) (S.s + 1)).map
          (homOfLE (h₀.trans hk)).op).hom := by
    intro d
    -- the containment of kernels at `𝔮`, in terms of Ext, for the transition `IⁿM ⟶ M`
    have iff := fun (q : PrimeSpectrum S.A) (n : ℕ) (hn : m ≤ n) => by
      have := finite_idealPowerTower_obj S.I (ModuleCat.of S.A S.M) (op n)
      have := finite_idealPowerTower_obj S.I (ModuleCat.of S.A S.M) (op 0)
      have := finite_idealPowerTower_obj S.I (ModuleCat.of S.A S.M) (op m)
      exact localized_ker_le_ker_localCohomology_iff_exists_localized_ext ω hω q (S.s + 1)
        ((idealPowerTower.{u, u} S.I (ModuleCat.of S.A S.M)).map (homOfLE (Nat.zero_le n)).op)
        (injective_localized_idealPowerTower_map.{u} q.asIdeal.primeCompl S.I
          (ModuleCat.of S.A S.M) (Nat.zero_le n))
        ((idealPowerTower.{u, u} S.I (ModuleCat.of S.A S.M)).map (homOfLE hn).op)
    have := Dualizing.finite_extIdealPowerTower_obj S.A S.I (ModuleCat.of S.A S.M) ω hω
      (-d - (S.s + 1)) m
    obtain ⟨k₀, h₀, hk₀⟩ := exists_forall_localized_stableImage.{u}
      (Dualizing.extIdealPowerTower S.A S.I (ModuleCat.of S.A S.M) ω (-d - (S.s + 1))) m
      (isNoetherian_of_isNoetherianRing_of_finite S.A _)
      {q : PrimeSpectrum S.A | q ∈ S.T ∧ Dualizing.dualizingDimension.{u, u} ω q = d}
      (fun q hq => by
        obtain ⟨c, hmc, hc⟩ := exists_localized_ker_le_ker_idealPowerTower S q hq.1 m
        refine ⟨c, hmc, ?_⟩
        rw [← hq.2]
        exact (iff q c hmc).1 (hc c le_rfl))
    refine ⟨k₀, h₀, fun k hk q hqT hqd => ?_⟩
    refine (iff q k (h₀.trans hk)).2 ?_
    rw [hqd]
    exact hk₀ k hk q ⟨hqT, hqd⟩
  choose k₀ h₀ hk₀ using key
  exact ⟨max m (hδfin.toFinset.sup k₀), le_max_left _ _, fun k hk q hqT =>
    hk₀ _ k (((Finset.le_sup (f := k₀) (hδfin.mem_toFinset.2 ⟨q, rfl⟩)).trans
      (le_max_right _ _)).trans hk) q hqT rfl⟩

/-! ### Tag 0EFX at a general specialization-stable locus -/

/-- **Stacks Project, Tag 0EFX**, the stable-image assertion, at a general specialization-stable
`T`. In Situation [Stacks, Tag 0EFU] there is an `m₀` such that for every `m ≥ m₀` there is an
`m'(m) ≥ m` with: for `k ≥ m'(m)` the image of `H^{s+1}_T(IᵏM) ⟶ H^{s+1}_T(IᵐM)` maps injectively
into `H^{s+1}_T(I^{m₀}M)`.

This is the source's proof carried out in full. The per-prime assertion at each `𝔮 ∈ T` is
`Stacks.Algebraization.exists_localized_ker_le_ker_idealPowerTower`; its bound is made independent
of `𝔮` by `Stacks.Algebraization.exists_forall_localized_ker_le_ker_idealPowerTower`, which is the
local-duality paragraph in the degree the tag states this assertion in; and the passage from the
uniform per-prime statement to the global one is Lemma [Stacks, Tag 0EFA]. In negative degrees the
system vanishes term by term. Nothing is assumed beyond the data of Situation
[Stacks, Tag 0EFU]. -/
@[stacks 0EFX "the stable-image assertion in degree s + 1 at a general specialization-stable T \
in Situation 0EFU"]
theorem exists_hasStableImageIdealPowerCohomology (S : BootstrapSituation.{u, u, u}) :
    ∃ m₀ : ℕ, HasStableImageIdealPowerCohomology.{u, u} S.T S.I (ModuleCat.of S.A S.M)
      (S.s + 1) m₀ := by
  by_cases hneg : S.s + 1 < 0
  · exact exists_eventually_injective_image_idealPowerTower_of_neg.{u, u} S.T S.I
      (ModuleCat.of S.A S.M) (S.s + 1) hneg
  obtain ⟨i, hi⟩ : ∃ i : ℕ, S.s + 1 = (i : ℤ) :=
    ⟨(S.s + 1).toNat, (Int.toNat_of_nonneg (not_lt.mp hneg)).symm⟩
  rw [hi]
  refine exists_eventually_injective_image_idealPowerTower_of_local_image_injective.{u, u}
    S.ringKrullDim_lt_top S.T S.stableUnderSpecialization S.I (ModuleCat.of S.A S.M) i ?_
  intro n
  obtain ⟨c₁, h₁, hc₁⟩ := exists_forall_localized_localCohomology_map_eq_zero S ((i : ℤ) - 1)
    (by omega) n
  obtain ⟨c₂, h₂, hc₂⟩ := exists_forall_localized_ker_le_ker_idealPowerTower S (i : ℤ)
    hi.symm n
  refine ⟨max c₁ c₂, h₁.trans (le_max_left _ _), fun p hp k hck =>
    ⟨hc₁ k ((le_max_left c₁ c₂).trans hck) p hp, fun x hx => ?_⟩⟩
  refine hc₂ k ((le_max_right c₁ c₂).trans hck) p hp ?_
  rw [LinearMap.mem_ker] at hx ⊢
  exact (inverseSystem_transition_comp_apply.{u, u} _ (Nat.zero_le n)
    ((h₁.trans (le_max_left c₁ c₂)).trans hck) x).symm.trans hx

/-- **Stacks Project, Tag 0EFX** at a general specialization-stable `T`: both assertions. In
Situation [Stacks, Tag 0EFU] the inverse systems `{H^i_T(IⁿM)}` are pro-zero for `i ≤ s`, and
there is an `m₀` such that for every `m ≥ m₀` there is an `m'(m) ≥ m` with: for `k ≥ m'(m)` the
image of `H^{s+1}_T(IᵏM) ⟶ H^{s+1}_T(IᵐM)` maps injectively into `H^{s+1}_T(I^{m₀}M)`.

The first assertion is `Stacks.Algebraization.isProZeroIdealPowerCohomology` and the second
`Stacks.Algebraization.exists_hasStableImageIdealPowerCohomology`. Both are the source's own
proof, the local-duality paragraph included; nothing beyond the data of Situation
[Stacks, Tag 0EFU] is assumed. -/
@[stacks 0EFX]
theorem isProZero_and_hasStableImage_idealPowerCohomology (S : BootstrapSituation.{u, u, u}) :
    (∀ i ≤ S.s, IsProZeroIdealPowerCohomology.{u, u} S.T S.I (ModuleCat.of S.A S.M) i) ∧
      ∃ m₀ : ℕ, HasStableImageIdealPowerCohomology.{u, u} S.T S.I (ModuleCat.of S.A S.M)
        (S.s + 1) m₀ :=
  ⟨fun i hi => isProZeroIdealPowerCohomology S i hi,
    exists_hasStableImageIdealPowerCohomology S⟩

/-! ### Part (6) of Tag 0EFY at a general specialization-stable locus -/

/-- **Stacks Project, Tag 0EFY, part (6)**, at a general specialization-stable `T`. In Situation
[Stacks, Tag 0EFU] there is an `m₀` such that `H^s_T(M) ⟶ lim H^s_T(M/IⁿM)` is injective with
cokernel killed by `I^{m₀}`.

This is `Stacks.LocalCohomology.exists_injective_limitLift_and_smul_mem_range` with both of its
hypotheses — the two assertions of [Stacks, Tag 0EFX] — discharged by
`Stacks.Algebraization.isProZeroIdealPowerCohomology` and
`Stacks.Algebraization.exists_hasStableImageIdealPowerCohomology`. -/
@[stacks 0EFY "part (6) at a general specialization-stable T in Situation 0EFU: Hˢ_T(M) ⟶ \
lim Hˢ_T(M/IⁿM) is injective with cokernel killed by I^{m₀}"]
theorem exists_injective_limitLift_and_smul_mem_range (S : BootstrapSituation.{u, u, u}) :
    ∃ m₀ : ℕ,
      Function.Injective (limit.lift
          (localCohomologyAdicTower.{u, u} S.A S.T S.I S.s (ModuleCat.of S.A S.M))
          (localCohomologyAdicCone.{u, u} S.A S.T S.I S.s (ModuleCat.of S.A S.M))).hom ∧
        ∀ a ∈ S.I ^ m₀, ∀ z : (limit (localCohomologyAdicTower.{u, u} S.A S.T S.I S.s
            (ModuleCat.of S.A S.M)) : ModuleCat.{u} S.A),
          a • z ∈ LinearMap.range (limit.lift
            (localCohomologyAdicTower.{u, u} S.A S.T S.I S.s (ModuleCat.of S.A S.M))
            (localCohomologyAdicCone.{u, u} S.A S.T S.I S.s (ModuleCat.of S.A S.M))).hom :=
  Stacks.LocalCohomology.exists_injective_limitLift_and_smul_mem_range.{u, u} S.T S.I
    (ModuleCat.of S.A S.M) S.s (isProZeroIdealPowerCohomology S S.s le_rfl)
    (exists_hasStableImageIdealPowerCohomology S)

end Stacks.Algebraization

end
