module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChernClassDualTensorOfProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChernCapFlatPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChernCapVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.WhitneyOfSplitting
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackFlatExact
public import StacksFrontier.RingTheory.PowerSeries.SumCoeffMul

/-!
# The Whitney formula, granted Stacks 0ES8

In Situation 0EDT let `X/B` be good and `0 ⟶ ℰ₁ ⟶ ℰ ⟶ ℰ₂ ⟶ 0` a short exact sequence of finite
locally free `𝒪_X`-modules of ranks `r₁`, `r₂`. Then `c(ℰ) = c(ℰ₁) c(ℰ₂)` (Stacks 0ES9), granted
Stacks 0ES8 degree by degree on every good space: `c_{n+1}(ℰ') = c_{n+1}(ℱ) + c₁(ℒ) c_n(ℱ)` for
`0 ⟶ ℒ ⟶ ℰ' ⟶ ℱ ⟶ 0` with `ℒ` invertible.

The proof is the splitting principle (Stacks 0ESC). Along the projective bundle tower
`π : P ⟶ X` splitting `ℰ₁` and `ℰ₂`, which is flat, the sequence pulls back to a short exact
sequence whose outer terms have filtrations with invertible quotients; there the formula is the
product formula of Stacks 0ESA for the concatenated filtration of `π^*ℰ`. It descends to `X`
along the flat pullback `π^* : CH_*(X) ⟶ CH_*(P)`, which is injective and commutes with the
Chern classes
(`AlgebraicGeometry.Space.PrivateChern.chernCap_spaceModulePullback_flatPullbackChow`).
For the total Chern classes the Chern classes vanish above the rank.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.shortExact_map_modulePullback_of_isFlat`: inverse images
  along flat morphisms preserve short exact sequences of modules.
* `AlgebraicGeometry.Space.PrivateChern.mk_chernCap_eq_mul_of_succ`: `c(ℰ) = c(ℰ₁) c(ℰ₂)` as power
  series of operations on `CH_*(X)`, granted Stacks 0ES8.
* `AlgebraicGeometry.Space.PrivateChern.chernCap_shortExact_of_succ`: the same, degree by degree.
* `AlgebraicGeometry.Space.PrivateChern.totalChernCap_shortExact_of_succ`: the same for the total
  Chern classes.

## References

* [Stacks Project, Tag 0ES9](https://stacks.math.columbia.edu/tag/0ES9)
* [Stacks Project, Tag 0ES8](https://stacks.math.columbia.edu/tag/0ES8)
* [Stacks Project, Tag 0ESA](https://stacks.math.columbia.edu/tag/0ESA)
* [Stacks Project, Tag 0ESC](https://stacks.math.columbia.edu/tag/0ESC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Subobject

universe u

namespace AlgebraicGeometry.Space.PrivateChern

/-- **The inverse image along a flat morphism carries short exact sequences of modules to short
exact sequences**: it is right exact, being a left adjoint, and left exact by flatness. -/
theorem shortExact_map_modulePullback_of_isFlat {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {X X' : AlgebraicSpaces B S hS} (g : X' ⟶ X) (hg : IsFlat B S hS g.hom)
    {T : ShortComplex (Modules.{u, u} B S hS X.1 X.2)} (hT : T.ShortExact) :
    (T.map (modulePullback B S hS g)).ShortExact :=
  have := preservesZeroMorphisms_modulePullback B S hS g
  have := preservesFiniteColimits_modulePullback B S hS g
  have := preservesFiniteLimits_modulePullback_of_isFlat_hom B S hS g hg
  hT.map_of_exact _

variable {D : BaseSpaceDimensionSituation.{u}}

/-- **The Whitney formula, granted Stacks 0ES8 degree by degree on every good space**: for a short
exact sequence `0 ⟶ ℰ₁ ⟶ ℰ ⟶ ℰ₂ ⟶ 0` of finite locally free modules of ranks `r₁`, `r₂` on a good
`X/B`, `c(ℰ) = c(ℰ₁) c(ℰ₂)` as power series of operations on `CH_*(X)`. -/
theorem mk_chernCap_eq_mul_of_succ
    (h8 : ∀ {P : D.Ambient} {sP : P ⟶ D.space} (hP : D.IsGood sP) (r : ℕ)
      (T : ShortComplex (Modules.{u, u} D.site D.base D.base_mem P hP.1))
      (_ : T.ShortExact) (h₁ : IsInvertibleModule (goodSpace hP) T.X₁)
      (h₂ : IsFiniteLocallyFreeOfRank D sP hP T.X₂ (r + 1))
      (h₃ : IsFiniteLocallyFreeOfRank D sP hP T.X₃ r) (n : ℕ),
      chernCap.{u, u + 1} T.X₂ (r + 1) h₂ (n + 1) =
        chernCap.{u, u + 1} T.X₃ r h₃ (n + 1) +
          chernCap.{u, u + 1} T.X₁ 1
            (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hP) h₁) 1 *
            chernCap.{u, u + 1} T.X₃ r h₃ n)
    {X : D.Ambient} {sX : X ⟶ D.space} (hX : D.IsGood sX)
    {T : ShortComplex (Modules.{u, u} D.site D.base D.base_mem X hX.1)} (hT : T.ShortExact)
    {r₁ r₂ : ℕ} (h₁ : IsFiniteLocallyFreeOfRank D sX hX T.X₁ r₁)
    (h₂ : IsFiniteLocallyFreeOfRank D sX hX T.X₂ (r₁ + r₂))
    (h₃ : IsFiniteLocallyFreeOfRank D sX hX T.X₃ r₂) :
    PowerSeries.mk (chernCap.{u, u + 1} T.X₂ (r₁ + r₂) h₂) =
      PowerSeries.mk (chernCap.{u, u + 1} T.X₁ r₁ h₁) *
        PowerSeries.mk (chernCap.{u, u + 1} T.X₃ r₂ h₃) := by
  obtain ⟨P, sP, hP, π, hπ, d, hflat, hd, -, hinj, hfil⟩ :=
    isSplitting_projectiveBundleTower hX ![T.X₁, T.X₃] ![r₁, r₂]
      (fun i => by fin_cases i <;> assumption)
  have hfil₁ := hfil 0
  have hfil₃ := hfil 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hfil₁ hfil₃
  let πs : (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X, hX.1⟩ :=
    ObjectProperty.homMk π
  have hT' := shortExact_map_modulePullback_of_isFlat πs hflat hT
  have h₁' := isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem πs h₁
  have h₂' := isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem πs h₂
  have h₃' := isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem πs h₃
  have := isClosedUnderIsomorphisms_invertibleModules D.site D.base D.base_mem
    (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)
  obtain ⟨F₁, hF₁, h₁0, h₁a, hq₁⟩ := hfil₁.exists_subobject
  obtain ⟨F₃, hF₃, h₃0, h₃b, hq₃⟩ := hfil₃.exists_subobject
  have hW := mk_chernCap_eq_mul_of_filtrations (hX := hP)
    (fun L hL ↦ chernCap.{u, u + 1} L 1
      (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hP) hL) 1)
    (fun r T hT h₁ h₂ h₃ n ↦ h8 hP r T hT h₁ h₂ h₃ n) hT' h₁' h₂' h₃' _ hq₁ F₁ hF₁ h₁0 h₁a
    (fun _ ↦ Iso.refl _) _ hq₃ F₃ hF₃ h₃0 h₃b (fun _ ↦ Iso.refl _)
  have hinj' := flatPullbackChow_injective.{u, 0} D sP hP sX hX π hπ d hflat hd
    (hinj.hasInjectiveChowPullbacks D hX hP hπ hflat hd sX hX (𝟙 X) (Category.id_comp sX)
      sP hP (𝟙 P) π IsPullback.of_id_fst hπ)
  have hc := chernCap_spaceModulePullback_flatPullbackChow hX hP π hπ d hflat hd
  exact mk_chernCap_eq_mul_of_injective _ hinj' h₂ h₁ h₃ h₂' h₁' h₃'
    (hc _ _ h₂ h₂') (hc _ _ h₁ h₁') (hc _ _ h₃ h₃') hW
/-- **The Whitney formula degree by degree, granted Stacks 0ES8**:
`c_n(ℰ) = ∑_{i + j = n} c_i(ℰ₁) c_j(ℰ₂)`. -/
theorem chernCap_shortExact_of_succ
    (h8 : ∀ {P : D.Ambient} {sP : P ⟶ D.space} (hP : D.IsGood sP) (r : ℕ)
      (T : ShortComplex (Modules.{u, u} D.site D.base D.base_mem P hP.1))
      (_ : T.ShortExact) (h₁ : IsInvertibleModule (goodSpace hP) T.X₁)
      (h₂ : IsFiniteLocallyFreeOfRank D sP hP T.X₂ (r + 1))
      (h₃ : IsFiniteLocallyFreeOfRank D sP hP T.X₃ r) (n : ℕ),
      chernCap.{u, u + 1} T.X₂ (r + 1) h₂ (n + 1) =
        chernCap.{u, u + 1} T.X₃ r h₃ (n + 1) +
          chernCap.{u, u + 1} T.X₁ 1
            (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hP) h₁) 1 *
            chernCap.{u, u + 1} T.X₃ r h₃ n)
    {X : D.Ambient} {sX : X ⟶ D.space} (hX : D.IsGood sX)
    {T : ShortComplex (Modules.{u, u} D.site D.base D.base_mem X hX.1)} (hT : T.ShortExact)
    {r₁ r₂ : ℕ} (h₁ : IsFiniteLocallyFreeOfRank D sX hX T.X₁ r₁)
    (h₂ : IsFiniteLocallyFreeOfRank D sX hX T.X₂ (r₁ + r₂))
    (h₃ : IsFiniteLocallyFreeOfRank D sX hX T.X₃ r₂) (n : ℕ) :
    chernCap.{u, u + 1} T.X₂ (r₁ + r₂) h₂ n =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) n,
        chernCap.{u, u + 1} T.X₁ r₁ h₁ p.1 * chernCap.{u, u + 1} T.X₃ r₂ h₃ p.2 := by
  have h := congrArg (PowerSeries.coeff n) (mk_chernCap_eq_mul_of_succ h8 hX hT h₁ h₂ h₃)
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul] at h
  simpa only [PowerSeries.coeff_mk] using h

/-- **The Whitney formula for total Chern classes, granted Stacks 0ES8**:
`c(ℰ) = c(ℰ₁) c(ℰ₂)`. -/
theorem totalChernCap_shortExact_of_succ
    (h8 : ∀ {P : D.Ambient} {sP : P ⟶ D.space} (hP : D.IsGood sP) (r : ℕ)
      (T : ShortComplex (Modules.{u, u} D.site D.base D.base_mem P hP.1))
      (_ : T.ShortExact) (h₁ : IsInvertibleModule (goodSpace hP) T.X₁)
      (h₂ : IsFiniteLocallyFreeOfRank D sP hP T.X₂ (r + 1))
      (h₃ : IsFiniteLocallyFreeOfRank D sP hP T.X₃ r) (n : ℕ),
      chernCap.{u, u + 1} T.X₂ (r + 1) h₂ (n + 1) =
        chernCap.{u, u + 1} T.X₃ r h₃ (n + 1) +
          chernCap.{u, u + 1} T.X₁ 1
            (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hP) h₁) 1 *
            chernCap.{u, u + 1} T.X₃ r h₃ n)
    {X : D.Ambient} {sX : X ⟶ D.space} (hX : D.IsGood sX)
    {T : ShortComplex (Modules.{u, u} D.site D.base D.base_mem X hX.1)} (hT : T.ShortExact)
    {r₁ r₂ : ℕ} (h₁ : IsFiniteLocallyFreeOfRank D sX hX T.X₁ r₁)
    (h₂ : IsFiniteLocallyFreeOfRank D sX hX T.X₂ (r₁ + r₂))
    (h₃ : IsFiniteLocallyFreeOfRank D sX hX T.X₃ r₂) :
    totalChernCap.{u, u + 1} T.X₂ (r₁ + r₂) h₂ =
      totalChernCap.{u, u + 1} T.X₁ r₁ h₁ * totalChernCap.{u, u + 1} T.X₃ r₂ h₃ := by
  have hS : HasIntertwiningSplittings.{u, u + 1} D := hasIntertwiningSplittings_of_flatPullbackChow
    chernCap_spaceModulePullback_flatPullbackChow
  have h := PowerSeries.sum_range_coeff_mul_of_coeff_eq_zero
    (PowerSeries.mk (chernCap.{u, u + 1} T.X₁ r₁ h₁))
    (PowerSeries.mk (chernCap.{u, u + 1} T.X₃ r₂ h₃))
    (fun i hi => by
      rw [PowerSeries.coeff_mk]
      exact chernCap_eq_zero_of_lt_of_hasIntertwiningSplittings h8 hS hX _ _ h₁ hi)
    (fun j hj => by
      rw [PowerSeries.coeff_mk]
      exact chernCap_eq_zero_of_lt_of_hasIntertwiningSplittings h8 hS hX _ _ h₃ hj)
  rw [← mk_chernCap_eq_mul_of_succ h8 hX hT h₁ h₂ h₃] at h
  simpa only [PowerSeries.coeff_mk, totalChernCap] using h

end AlgebraicGeometry.Space.PrivateChern

end
