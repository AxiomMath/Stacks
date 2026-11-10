module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChernClassTensorFiltered
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackChowInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.SplittingPrinciple
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.SplittingInduction
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackMonoidal
public import StacksFrontier.RingTheory.PowerSeries.ListProdOneAddCMulX

/-!
# Chern classes of duals and tensor products from the properties of Chern classes

In Situation 0EDT let `X/B` be good. This file assembles the proofs of Stacks 0ESD,
`c_i(ℰ^∨) = (-1)^i c_i(ℰ)`, and Stacks 0ESE, the formulas for `c₁(ℰ ⊗ ℱ)` and `c₂(ℰ ⊗ ℱ)`, from the
properties of the Chern classes of chapter 82 which the source's proofs use: vanishing above
the rank, the Whitney formula (Stacks 0ES9), additivity of `c₁` on invertible modules
(Stacks 0EQK), invariance under isomorphism, commutativity of the first Chern classes of
invertible modules (Stacks 0EQZ), and the splitting
principle (Stacks 0ESC) in the form of an injective map of Chow homologies intertwining the
Chern classes with those of the pulled back modules.

The reduction is the source's: on a good `Y` pull the modules back along a splitting
`π : P ⟶ Y`, where they acquire filtrations with invertible successive quotients; there the
identities are the computations of
`AlgebraicGeometry.Space.PrivateChern.chernCap_dual_of_hasFiltrationOfLength` and
`AlgebraicGeometry.Space.PrivateChern.chernCap_tensorObj_of_hasFiltrationOfLength`, and they
descend to `Y` along the injective map `π^* : CH_*(Y) ⟶ CH_*(P)`, the inverse image of a dual,
resp. of a tensor product, being the dual, resp. the tensor product, of the inverse images.

## Main definitions

* `AlgebraicGeometry.Space.PrivateChern.ChernCapProperties`: the properties of the Chern
  classes on every good space which the computations use.
* `AlgebraicGeometry.Space.PrivateChern.HasIntertwiningSplittings`: every pair of finite locally
  free modules on a good space has a splitting with an injective map of Chow homologies
  intertwining the Chern classes.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.hasIntertwiningSplittings_of_isSplitting`: the flat
  pullback along a splitting is an injective intertwining map, given that the Chern classes commute
  with flat pullback.
* `AlgebraicGeometry.Space.PrivateChern.isSplitting_projectiveBundleTower`: the splitting
  principle (Stacks 0ESC) for a finite family of modules.
* `AlgebraicGeometry.Space.PrivateChern.hasIntertwiningSplittings_of_flatPullbackChow`: the
  intertwining splittings, from the splitting principle and the compatibility of the Chern classes
  with flat pullback.
* `AlgebraicGeometry.Space.PrivateChern.eq_of_intertwines`: descent of an identity along an
  injective intertwining map.
* `AlgebraicGeometry.Space.PrivateChern.chernCap_dual_of_chernCapProperties`: Stacks 0ESD.
* `AlgebraicGeometry.Space.PrivateChern.chernCap_tensorObj_of_chernCapProperties`: Stacks 0ESE,
  the identities for `c₁` and `c₂`.
* `exists_totalChernCap_tensorObj_eq_prod_of_chernCapProperties`:
  Stacks 0ESE, the product formula of the proof on a splitting.

## References

* [Stacks Project, Tag 0ESD](https://stacks.math.columbia.edu/tag/0ESD)
* [Stacks Project, Tag 0ESE](https://stacks.math.columbia.edu/tag/0ESE)
* [Stacks Project, Tag 0ESC](https://stacks.math.columbia.edu/tag/0ESC)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u v

namespace AlgebraicGeometry.Space.PrivateChern

attribute [local instance] modulesMonoidalCategory modulesMonoidalClosed

attribute [local instance 10000] smallEtaleModulesAbelian

/-- The abelian structure of the `𝒪_X`-modules at the universe of the schemes; given as a term,
instance search otherwise stopping on a universe constraint once the Chern class API is
imported. -/
local instance (priority := high) instAbelianModulesOfProperties
    {D : BaseSpaceDimensionSituation.{u}} {X : D.Ambient}
    (hX₁ : IsAlgebraicSpace D.site D.base D.base_mem X) :
    Abelian (Modules.{u, u} D.site D.base D.base_mem X hX₁) :=
  SheafOfModules.instAbelian _

/-- Cokernels of `𝒪_X`-modules, from the abelian structure at the universe of the schemes. -/
local instance (priority := high) instHasCokernelsModulesOfProperties
    {D : BaseSpaceDimensionSituation.{u}} {X : D.Ambient}
    (hX₁ : IsAlgebraicSpace D.site D.base D.base_mem X) :
    CategoryTheory.Limits.HasCokernels (Modules.{u, u} D.site D.base D.base_mem X hX₁) :=
  letI : Abelian (Modules.{u, u} D.site D.base D.base_mem X hX₁) := SheafOfModules.instAbelian _
  inferInstance

variable (D : BaseSpaceDimensionSituation.{u})

/-- **The properties of the Chern classes used in Stacks 0ESD and 0ESE**, on every good algebraic
space `P/B`: vanishing above the rank, the Whitney formula (Stacks 0ES9), additivity of `c₁` on
tensor products of invertible modules and `c₁(𝒪_P) = 0` (Stacks 0EQK), invariance under
isomorphism, and commutativity of the first Chern classes of modules of rank one (Stacks 0EQZ;
after the splitting principle every Chern class involved is a product of these). -/
structure ChernCapProperties : Prop where
  /-- The Chern classes `c_n(ℰ)` of a finite locally free module of rank `r` vanish for `n > r`. -/
  chernCap_eq_zero_of_lt : ∀ {P : D.Ambient} {sP : P ⟶ D.space} (hP : D.IsGood sP)
    (E : Modules.{u, u} D.site D.base D.base_mem P hP.1) r h n, r < n →
      chernCap.{u, v} (hX := hP) E r h n = 0
  /-- The Whitney formula: for a short exact sequence `0 → ℰ₁ → ℰ₂ → ℰ₃ → 0` of finite locally free
  modules, `c_n(ℰ₂) = ∑_{i+j=n} c_i(ℰ₁) c_j(ℰ₃)`. -/
  chernCap_shortExact : ∀ {P : D.Ambient} {sP : P ⟶ D.space} (hP : D.IsGood sP)
    (T : ShortComplex (Modules.{u, u} D.site D.base D.base_mem P hP.1)),
      T.ShortExact → ∀ (r₁ r₃ : ℕ) h₁ h₂ h₃ (n : ℕ),
        chernCap.{u, v} (hX := hP) T.X₂ (r₁ + r₃) h₂ n =
          ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) n,
            chernCap.{u, v} (hX := hP) T.X₁ r₁ h₁ p.1 *
              chernCap.{u, v} (hX := hP) T.X₃ r₃ h₃ p.2
  /-- For invertible modules `ℒ`, `ℳ`, `c₁(ℒ ⊗ ℳ) = c₁(ℒ) + c₁(ℳ)`. -/
  chernCap_one_tensorObj : ∀ {P : D.Ambient} {sP : P ⟶ D.space} (hP : D.IsGood sP)
    (L M : Modules.{u, u} D.site D.base D.base_mem P hP.1) hL hM hLM,
      chernCap.{u, v} (hX := hP) (L ⊗ M) 1 hLM 1 =
        chernCap.{u, v} (hX := hP) L 1 hL 1 + chernCap.{u, v} (hX := hP) M 1 hM 1
  /-- Isomorphic finite locally free modules have the same Chern classes. -/
  chernCap_congr_iso : ∀ {P : D.Ambient} {sP : P ⟶ D.space} (hP : D.IsGood sP)
    (E E' : Modules.{u, u} D.site D.base D.base_mem P hP.1) r h h' n,
      Nonempty (E ≅ E') →
        chernCap.{u, v} (hX := hP) E r h n = chernCap.{u, v} (hX := hP) E' r h' n
  /-- The first Chern class of the structure sheaf vanishes: `c₁(𝒪_P) = 0`. -/
  chernCap_one_tensorUnit : ∀ {P : D.Ambient} {sP : P ⟶ D.space} (hP : D.IsGood sP) h,
    chernCap.{u, v} (hX := hP) (𝟙_ (Modules.{u, u} D.site D.base D.base_mem P hP.1)) 1 h 1 = 0
  /-- The first Chern classes of two invertible modules commute. -/
  chernCap_one_commute : ∀ {P : D.Ambient} {sP : P ⟶ D.space} (hP : D.IsGood sP)
    (L M : Modules.{u, u} D.site D.base D.base_mem P hP.1) hL hM,
      Commute (chernCap.{u, v} (hX := hP) L 1 hL 1) (chernCap.{u, v} (hX := hP) M 1 hM 1)

/-- **Splittings with an intertwining injection** (the splitting principle, Stacks 0ESC, with the
compatibility of Chern classes with flat pullback): for every pair of finite locally free modules
`𝒢₁`, `𝒢₂` of ranks `r₁`, `r₂` on a good algebraic space `Z/B` there is a good `π : P ⟶ Z` along
which both acquire filtrations with invertible successive quotients, and an injective map
`g : CH_*(Z) ⟶ CH_*(P)` with `c_n(π^*ℳ) ∘ g = g ∘ c_n(ℳ)` for every finite locally free `ℳ` on
`Z`. -/
def HasIntertwiningSplittings : Prop :=
  ∀ {Z : D.Ambient} {sZ : Z ⟶ D.space} (hZ : D.IsGood sZ)
    (G₁ G₂ : Modules.{u, u} D.site D.base D.base_mem Z hZ.1) (r₁ r₂ : ℕ),
    IsFiniteLocallyFreeOfRank D sZ hZ G₁ r₁ → IsFiniteLocallyFreeOfRank D sZ hZ G₂ r₂ →
    ∃ (P : D.Ambient) (sP : P ⟶ D.space) (hP : D.IsGood sP) (π : P ⟶ Z)
      (g : chowHomology.{u, v} D sZ hZ →+ chowHomology.{u, v} D sP hP),
      Function.Injective g ∧
      (invertibleModules D.site D.base D.base_mem (goodSpace hP)).HasFiltrationOfLength r₁
        ((spaceModulePullback D hZ.1 hP.1 π).obj G₁) ∧
      (invertibleModules D.site D.base D.base_mem (goodSpace hP)).HasFiltrationOfLength r₂
        ((spaceModulePullback D hZ.1 hP.1 π).obj G₂) ∧
      ∀ (M : Modules.{u, u} D.site D.base D.base_mem Z hZ.1) (r : ℕ) hM hM' (n : ℕ)
        (α : chowHomology.{u, v} D sZ hZ),
        chernCap.{u, v} (hX := hP) ((spaceModulePullback D hZ.1 hP.1 π).obj M) r hM' n (g α) =
          g (chernCap.{u, v} (hX := hZ) M r hM n α)

variable {D} {X : D.Ambient} {sX : X ⟶ D.space} {hX : D.IsGood sX}

/-- **Splittings with an intertwining injection from the splitting principle**: if every pair of
finite locally free modules on a good space has a splitting (Stacks 0ESC) and the Chern classes
commute with flat pullback, then the flat pullback along the splitting is an injective
intertwining map. -/
theorem hasIntertwiningSplittings_of_isSplitting
    (hsplit : ∀ {Z : D.Ambient} {sZ : Z ⟶ D.space} (hZ : D.IsGood sZ)
      (G₁ G₂ : Modules.{u, u} D.site D.base D.base_mem Z hZ.1) (r₁ r₂ : ℕ),
      IsFiniteLocallyFreeOfRank D sZ hZ G₁ r₁ → IsFiniteLocallyFreeOfRank D sZ hZ G₂ r₂ →
      ∃ Q, IsSplitting.{max v (u + 1)} D Q sZ hZ ![G₁, G₂] ![r₁, r₂])
    (hnat : ∀ {Z P : D.Ambient} {sZ : Z ⟶ D.space} {sP : P ⟶ D.space} (hZ : D.IsGood sZ)
      (hP : D.IsGood sP) (π : P ⟶ Z) (hπ : π ≫ sZ = sP) (d : ℕ)
      (hflat : IsFlat D.site D.base D.base_mem π)
      (hd : HasRelativeDimension d D.site D.base D.base_mem π)
      (M : Modules.{u, u} D.site D.base D.base_mem Z hZ.1) (r : ℕ) hM hM' (n : ℕ)
      (α : chowHomology.{u, max v (u + 1)} D sZ hZ),
      chernCap.{u, max v (u + 1)} (hX := hP) ((spaceModulePullback D hZ.1 hP.1 π).obj M) r hM' n
          (flatPullbackChow.{u, max v (u + 1)} D sP hP sZ hZ π hπ d hflat hd α) =
        flatPullbackChow.{u, max v (u + 1)} D sP hP sZ hZ π hπ d hflat hd
          (chernCap.{u, max v (u + 1)} (hX := hZ) M r hM n α)) :
    HasIntertwiningSplittings.{u, max v (u + 1)} D := by
  intro Z sZ hZ G₁ G₂ r₁ r₂ h₁ h₂
  obtain ⟨Q, P, sP, hP, π, hπ, d, hflat, hd, -, hinj, hfil⟩ := hsplit hZ G₁ G₂ r₁ r₂ h₁ h₂
  have hfil₁ := hfil 0
  have hfil₂ := hfil 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hfil₁ hfil₂
  refine ⟨P, sP, hP, π, flatPullbackChow.{u, max v (u + 1)} D sP hP sZ hZ π hπ d hflat hd,
    flatPullbackChow_injective.{u, v} D sP hP sZ hZ π hπ d hflat hd
      (hinj.hasInjectiveChowPullbacks D hZ hP hπ hflat hd sZ hZ (𝟙 Z) (Category.id_comp sZ)
        sP hP (𝟙 P) π IsPullback.of_id_fst hπ), hfil₁, hfil₂, ?_⟩
  intro M r hM hM' n α
  exact hnat hZ hP π hπ d hflat hd M r hM hM' n α

/-- **Every finite family of finite locally free modules has a splitting by a projective bundle
tower** (the splitting principle, Stacks 0ESC, in the form of
`AlgebraicGeometry.Space.PrivateChern.IsSplitting`). -/
theorem isSplitting_projectiveBundleTower {ι : Type*} [Finite ι] {Z : D.Ambient}
    {sZ : Z ⟶ D.space} (hZ : D.IsGood sZ) (G : ι → Modules.{u, u} D.site D.base D.base_mem Z hZ.1)
    (r : ι → ℕ) (hG : ∀ i, IsFiniteLocallyFreeOfRank D sZ hZ (G i) (r i)) :
    IsSplitting.{u + 1} D IsProjectiveBundleTower sZ hZ G r :=
  isSplitting_of_hasSplittingStep.{u + 1} D IsProjectiveBundleTower
    (fun _ _ E s hE => hasSplittingStep_projectiveBundle D E s hE
      (hasInjectiveChowBaseChange_projectiveBundleDatum D E s hE)) sZ hZ G r hG

/-- **Splittings with an intertwining injection from the compatibility of the Chern classes with
flat pullback**: the splitting principle (Stacks 0ESC) provides the splittings, at the Chow groups
whose rational equivalences are indexed in the universe `u + 1`. -/
theorem hasIntertwiningSplittings_of_flatPullbackChow
    (hnat : ∀ {Z P : D.Ambient} {sZ : Z ⟶ D.space} {sP : P ⟶ D.space} (hZ : D.IsGood sZ)
      (hP : D.IsGood sP) (π : P ⟶ Z) (hπ : π ≫ sZ = sP) (d : ℕ)
      (hflat : IsFlat D.site D.base D.base_mem π)
      (hd : HasRelativeDimension d D.site D.base D.base_mem π)
      (M : Modules.{u, u} D.site D.base D.base_mem Z hZ.1) (r : ℕ) hM hM' (n : ℕ)
      (α : chowHomology.{u, u + 1} D sZ hZ),
      chernCap.{u, u + 1} (hX := hP) ((spaceModulePullback D hZ.1 hP.1 π).obj M) r hM' n
          (flatPullbackChow.{u, u + 1} D sP hP sZ hZ π hπ d hflat hd α) =
        flatPullbackChow.{u, u + 1} D sP hP sZ hZ π hπ d hflat hd
          (chernCap.{u, u + 1} (hX := hZ) M r hM n α)) :
    HasIntertwiningSplittings.{u, u + 1} D :=
  hasIntertwiningSplittings_of_isSplitting.{u, 0}
    (fun hZ G₁ G₂ r₁ r₂ h₁ h₂ => ⟨_, isSplitting_projectiveBundleTower hZ ![G₁, G₂] ![r₁, r₂]
      (fun i => by fin_cases i <;> assumption)⟩) hnat

/-- **Stacks 0ESD from the properties of the Chern classes and the splitting principle**: for a
finite locally free `ℰ` on `X` and a good `f : Y ⟶ X` along which `ℰ` pulls back to rank `r`,
`c_i(f^*ℰ^∨) = (-1)^i c_i(f^*ℰ)` as operations on `CH_*(Y)`. -/
theorem chernCap_dual_of_chernCapProperties (hC : ChernCapProperties.{u, v} D)
    (hS : HasIntertwiningSplittings.{u, v} D)
    (E : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hE : SheafOfModules.IsFiniteLocallyFreeOnSite E) {Y : D.Ambient} (f : Y ⟶ X)
    (hY : D.IsGood (f ≫ sX)) (r : ℕ)
    (hr : IsFiniteLocallyFreeOfRank D (f ≫ sX) hY ((spaceModulePullback D hX.1 hY.1 f).obj E) r)
    (i : ℕ) :
    chernCap.{u, v} (hX := hY) ((spaceModulePullback D hX.1 hY.1 f).obj ((ihom E).obj (𝟙_ _))) r
        (isFiniteLocallyFreeOfRank_modulePullback_dual
          (ObjectProperty.homMk f : (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
            ⟨X, hX.1⟩) E hE hr) i =
      (-1 : ℤ) ^ i • chernCap.{u, v} (hX := hY) ((spaceModulePullback D hX.1 hY.1 f).obj E) r hr i
    := by
  have hGd := isFiniteLocallyFreeOfRank_modulePullback_dual
    (ObjectProperty.homMk f : (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
      ⟨X, hX.1⟩) E hE hr
  obtain ⟨P, sP, hP, π, g, hg, hfil, -, hnat⟩ := hS hY _ _ r r hr hr
  have hfree : SheafOfModules.IsFiniteLocallyFreeOnSite
      ((spaceModulePullback D hX.1 hY.1 f).obj E) := isFiniteLocallyFreeOnSite_of_rank _ hr
  have e := (spaceModulePullback D hY.1 hP.1 π).mapIso (modulePullbackDualIso
      (ObjectProperty.homMk f : (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
        ⟨X, hX.1⟩) E hE) ≪≫ modulePullbackDualIso
      (ObjectProperty.homMk π : (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
        ⟨Y, hY.1⟩) _ hfree
  have hPd := isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem
    (ObjectProperty.homMk π : (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
      ⟨Y, hY.1⟩) hGd
  have key := chernCap_dual_of_hasFiltrationOfLength (hC.chernCap_eq_zero_of_lt hP)
    (hC.chernCap_shortExact hP) (hC.chernCap_one_tensorObj hP) (hC.chernCap_congr_iso hP)
    (hC.chernCap_one_tensorUnit hP) (hC.chernCap_one_commute hP) hfil i
  refine AddMonoidHom.ext fun α => hg ?_
  refine (hnat _ r hGd hPd i α).symm.trans ?_
  refine (congrArg (fun φ : AddMonoid.End (chowHomology.{u, v} D sP hP) => φ (g α))
    (hC.chernCap_congr_iso hP _ _ r hPd
      (isFiniteLocallyFreeOfRank_dual D.site D.base D.base_mem P hP.1 _
        (isFiniteLocallyFreeOfRank_of_hasFiltrationOfLength hfil)) i ⟨e⟩)).trans ?_
  refine (congrArg (fun φ : AddMonoid.End (chowHomology.{u, v} D sP hP) => φ (g α)) key).trans ?_
  exact (congrArg (fun y => (-1 : ℤ) ^ i • y) (hnat _ r hr
    (isFiniteLocallyFreeOfRank_of_hasFiltrationOfLength hfil) i α)).trans (map_zsmul g _ _).symm

/-! ### Descent of identities along an injective intertwining map -/

section Intertwining

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] (g : M →+ N)

/-- Sums of intertwined operations are intertwined. -/
theorem intertwines_add {φ ψ : AddMonoid.End M} {φ' ψ' : AddMonoid.End N}
    (hφ : ∀ α, φ' (g α) = g (φ α)) (hψ : ∀ α, ψ' (g α) = g (ψ α)) (α : M) :
    (φ' + ψ') (g α) = g ((φ + ψ) α) := by
  change φ' (g α) + ψ' (g α) = g (φ α + ψ α)
  rw [hφ, hψ, map_add]

/-- Integer multiples of intertwined operations are intertwined. -/
theorem intertwines_zsmul {φ : AddMonoid.End M} {φ' : AddMonoid.End N}
    (hφ : ∀ α, φ' (g α) = g (φ α)) (n : ℤ) (α : M) :
    (n • φ') (g α) = g ((n • φ) α) :=
  (congrArg (n • ·) (hφ α)).trans (map_zsmul g n _).symm

/-- Composites of intertwined operations are intertwined. -/
theorem intertwines_mul {φ ψ : AddMonoid.End M} {φ' ψ' : AddMonoid.End N}
    (hφ : ∀ α, φ' (g α) = g (φ α)) (hψ : ∀ α, ψ' (g α) = g (ψ α)) (α : M) :
    (φ' * ψ') (g α) = g ((φ * ψ) α) :=
  (congrArg φ' (hψ α)).trans (hφ (ψ α))

/-- Powers of an intertwined operation are intertwined. -/
theorem intertwines_pow {φ : AddMonoid.End M} {φ' : AddMonoid.End N}
    (hφ : ∀ α, φ' (g α) = g (φ α)) : ∀ (k : ℕ) (α : M), (φ' ^ k) (g α) = g ((φ ^ k) α)
  | 0, _ => rfl
  | k + 1, α => by
    rw [pow_succ, pow_succ]
    exact intertwines_mul g (intertwines_pow hφ k) hφ α

/-- **Descent along an injective intertwining map**: if `g` is injective and intertwines `φ` with
`φ'` and `ψ` with `ψ'`, then `φ' = ψ'` implies `φ = ψ`. -/
theorem eq_of_intertwines {g : M →+ N} (hg : Function.Injective g)
    {φ ψ : AddMonoid.End M} {φ' ψ' : AddMonoid.End N}
    (hφ : ∀ α, φ' (g α) = g (φ α)) (hψ : ∀ α, ψ' (g α) = g (ψ α)) (h : φ' = ψ') : φ = ψ :=
  AddMonoidHom.ext fun α => hg ((hφ α).symm.trans ((congrArg (· (g α)) h).trans (hψ α)))

end Intertwining

/-- **Stacks 0ESE, the identities for `c₁` and `c₂`, from the properties of the Chern classes and
the splitting principle**: for finite locally free `ℰ`, `ℱ` on `X` of ranks `r`, `s` and a good
`f : Y ⟶ X`, as operations on `CH_*(Y)`,
`c₁(f^*(ℰ ⊗ ℱ)) = r c₁(f^*ℱ) + s c₁(f^*ℰ)` and
`c₂(f^*(ℰ ⊗ ℱ)) = r c₂(f^*ℱ) + s c₂(f^*ℰ) + C(r,2) c₁(f^*ℱ)² + (r s - 1) c₁(f^*ℱ) c₁(f^*ℰ) +
C(s,2) c₁(f^*ℰ)²`. -/
theorem chernCap_tensorObj_of_chernCapProperties (hC : ChernCapProperties.{u, v} D)
    (hS : HasIntertwiningSplittings.{u, v} D)
    (E F : Modules.{u, u} D.site D.base D.base_mem X hX.1) (r s : ℕ)
    (hr : IsFiniteLocallyFreeOfRank D sX hX E r) (hs : IsFiniteLocallyFreeOfRank D sX hX F s)
    {Y : D.Ambient} (f : Y ⟶ X) (hY : D.IsGood (f ≫ sX)) :
    let hrY := isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem
      (ObjectProperty.homMk f : (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
        ⟨X, hX.1⟩) hr
    let hsY := isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem
      (ObjectProperty.homMk f : (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
        ⟨X, hX.1⟩) hs
    let hrsY := isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem
      (ObjectProperty.homMk f : (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
        ⟨X, hX.1⟩) (isFiniteLocallyFreeOfRank_tensorObj D.site D.base D.base_mem X hX.1 hr hs)
    chernCap.{u, v} (hX := hY) ((spaceModulePullback D hX.1 hY.1 f).obj (E ⊗ F)) (r * s) hrsY 1 =
        (r : ℤ) • chernCap.{u, v} (hX := hY) ((spaceModulePullback D hX.1 hY.1 f).obj F) s hsY 1 +
          (s : ℤ) • chernCap.{u, v} (hX := hY) ((spaceModulePullback D hX.1 hY.1 f).obj E) r hrY 1 ∧
      chernCap.{u, v} (hX := hY) ((spaceModulePullback D hX.1 hY.1 f).obj (E ⊗ F)) (r * s) hrsY 2 =
        (r : ℤ) • chernCap.{u, v} (hX := hY) ((spaceModulePullback D hX.1 hY.1 f).obj F) s hsY 2 +
          (s : ℤ) • chernCap.{u, v} (hX := hY) ((spaceModulePullback D hX.1 hY.1 f).obj E) r hrY 2 +
          (r.choose 2 : ℤ) •
            chernCap.{u, v} (hX := hY) ((spaceModulePullback D hX.1 hY.1 f).obj F) s hsY 1 ^ 2 +
          ((r : ℤ) * s - 1) •
            (chernCap.{u, v} (hX := hY) ((spaceModulePullback D hX.1 hY.1 f).obj F) s hsY 1 *
              chernCap.{u, v} (hX := hY) ((spaceModulePullback D hX.1 hY.1 f).obj E) r hrY 1) +
          (s.choose 2 : ℤ) •
            chernCap.{u, v} (hX := hY) ((spaceModulePullback D hX.1 hY.1 f).obj E) r hrY 1 ^ 2 := by
  intro hrY hsY hrsY
  obtain ⟨P, sP, hP, π, g, hg, hfilE, hfilF, hnat⟩ := hS hY _ _ r s hrY hsY
  have key := chernCap_tensorObj_of_hasFiltrationOfLength (hC.chernCap_eq_zero_of_lt hP)
    (hC.chernCap_shortExact hP) (hC.chernCap_one_tensorObj hP) (hC.chernCap_one_commute hP)
    hfilE hfilF
  have e := (spaceModulePullback D hY.1 hP.1 π).mapIso
      (@Functor.Monoidal.μIso _ _ _ _ _ _ _ (modulePullbackMonoidal
        (ObjectProperty.homMk f : (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
          ⟨X, hX.1⟩)) E F).symm ≪≫
    (@Functor.Monoidal.μIso _ _ _ _ _ _ _ (modulePullbackMonoidal
        (ObjectProperty.homMk π : (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
          ⟨Y, hY.1⟩)) ((spaceModulePullback D hX.1 hY.1 f).obj E)
        ((spaceModulePullback D hX.1 hY.1 f).obj F)).symm
  have hrsP := isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem
    (ObjectProperty.homMk π : (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
      ⟨Y, hY.1⟩) hrsY
  have hrP := isFiniteLocallyFreeOfRank_of_hasFiltrationOfLength hfilE
  have hsP := isFiniteLocallyFreeOfRank_of_hasFiltrationOfLength hfilF
  have hiso : ∀ n, chernCap.{u, v} (hX := hP) ((spaceModulePullback D hY.1 hP.1 π).obj
      ((spaceModulePullback D hX.1 hY.1 f).obj (E ⊗ F))) (r * s) hrsP n =
      chernCap.{u, v} (hX := hP) ((spaceModulePullback D hY.1 hP.1 π).obj
        ((spaceModulePullback D hX.1 hY.1 f).obj E) ⊗ (spaceModulePullback D hY.1 hP.1 π).obj
          ((spaceModulePullback D hX.1 hY.1 f).obj F)) (r * s)
        (isFiniteLocallyFreeOfRank_tensorObj D.site D.base D.base_mem P hP.1 hrP hsP) n :=
    fun n => hC.chernCap_congr_iso hP _ _ _ _ _ n ⟨e⟩
  have hE1 := hnat _ r hrY hrP 1
  have hE2 := hnat _ r hrY hrP 2
  have hF1 := hnat _ s hsY hsP 1
  have hF2 := hnat _ s hsY hsP 2
  refine ⟨eq_of_intertwines hg (fun α => (congrArg (· (g α)) (hiso 1).symm).trans
      (hnat _ (r * s) hrsY hrsP 1 α))
    (intertwines_add g (intertwines_zsmul g hF1 _) (intertwines_zsmul g hE1 _)) key.1,
    eq_of_intertwines hg (fun α => (congrArg (· (g α)) (hiso 2).symm).trans
      (hnat _ (r * s) hrsY hrsP 2 α))
    (intertwines_add g (intertwines_add g (intertwines_add g (intertwines_add g
      (intertwines_zsmul g hF2 _) (intertwines_zsmul g hE2 _))
      (intertwines_zsmul g (intertwines_pow g hF1 2) _))
      (intertwines_zsmul g (intertwines_mul g hF1 hE1) _))
      (intertwines_zsmul g (intertwines_pow g hE1 2) _)) key.2⟩

section Lists

variable {α β R : Type*} [Ring R] (l : List α) (m : List β) (x : α → R) (y : β → R)

/-- The list of the `x a + y b` over the pairs `(a, b)` in lexicographic order has length
`|l| |m|`. -/
theorem length_flatMap_map_add :
    (l.flatMap fun a => m.map fun b => x a + y b).length = l.length * m.length := by
  simp [List.length_flatMap, List.sum_replicate]

/-- The factors `1 + (x a + y b) X` over the pairs `(a, b)`. -/
theorem map_flatMap_map_add_one_add_C_mul_X :
    ((l.flatMap fun a => m.map fun b => x a + y b).map
      fun z => 1 + PowerSeries.C z * PowerSeries.X) =
      l.flatMap fun a => m.map fun b => 1 + PowerSeries.C (x a + y b) * PowerSeries.X := by
  simp [List.map_flatMap, Function.comp_def]

/-- The factors `1 + (x a + y b)` over the pairs `(a, b)`, indexed by positions. -/
theorem map_flatMap_map_add_one_add :
    ((l.flatMap fun a => m.map fun b => x a + y b).map fun z => 1 + z) =
      (List.finRange l.length).flatMap fun i => (List.finRange m.length).map fun j =>
        1 + (x (l.get i) + y (m.get j)) := by
  conv_lhs => rw [← List.map_get_finRange l, ← List.map_get_finRange m]
  simp only [List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def]

/-- The factors `1 + x a`, indexed by positions. -/
theorem map_map_one_add : ((l.map x).map fun z => 1 + z) =
    (List.finRange l.length).map fun i => 1 + x (l.get i) := by
  conv_lhs => rw [← List.map_get_finRange l]
  simp only [List.map_map, Function.comp_def]

end Lists

/-- The total Chern class of a module whose Chern series is `∏ (1 + x_i X)`, over a list of `r`
operations, is `∏ (1 + x_i)`. -/
theorem totalChernCap_eq_prod_of_mk_eq {P : D.Ambient} {sP : P ⟶ D.space} {hP : D.IsGood sP}
    (M : Modules.{u, u} D.site D.base D.base_mem P hP.1) (r : ℕ)
    (h : IsFiniteLocallyFreeOfRank D sP hP M r)
    (l : List (AddMonoid.End (chowHomology.{u, v} D sP hP))) (hl : l.length = r)
    (hmk : PowerSeries.mk (chernCap.{u, v} M r h) =
      (l.map fun x => 1 + PowerSeries.C x * PowerSeries.X).prod) :
    totalChernCap.{u, v} M r h = (l.map fun x => 1 + x).prod := by
  subst hl
  rw [totalChernCap, ← PowerSeries.sum_coeff_list_prod_one_add_C_mul_X, ← hmk]
  simp only [PowerSeries.coeff_mk]

/-- The total Chern class of a module whose Chern series is `∏ (1 + c₁(ℒ_i) X)` for a list `Ls` of
invertible modules is `∏ (1 + c₁(ℒ_i))`, indexed by positions. -/
private theorem totalChernCap_eq_prod_get_of_mk_eq {P : D.Ambient} {sP : P ⟶ D.space}
    {hP : D.IsGood sP} (M : Modules.{u, u} D.site D.base D.base_mem P hP.1)
    (Ls : List {L : Modules.{u, u} D.site D.base D.base_mem P hP.1 //
      IsInvertibleModule (goodSpace hP) L})
    (h : IsFiniteLocallyFreeOfRank D sP hP M Ls.length)
    (hmk : PowerSeries.mk (chernCap.{u, v} M Ls.length h) =
      (Ls.map fun L => 1 + PowerSeries.C (chernCap.{u, v} (hX := hP) L.1 1
        (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hP) L.2) 1) *
          PowerSeries.X).prod) :
    totalChernCap.{u, v} M Ls.length h = ((List.finRange Ls.length).map fun i =>
      1 + chernCap.{u, v} (hX := hP) (Ls.get i).1 1
        (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hP)
          (Ls.get i).2) 1).prod := by
  rw [totalChernCap_eq_prod_of_mk_eq _ _ _ (Ls.map fun L => chernCap.{u, v} L.1 1
    (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hP) L.2) 1)
    (List.length_map _) (hmk.trans (by rw [List.map_map]; rfl)), map_map_one_add]

/-- **Stacks 0ESE, the product formula of the proof, from the properties of the Chern classes and a
splitting.** If `π : P ⟶ X` splits finite locally free `ℰ`, `ℱ` of ranks `r`, `s`, then there are
invertible `𝒪_P`-modules `ℒ_1, …, ℒ_r`, `𝒩_1, …, 𝒩_s` with, for `x_i = c₁(ℒ_i)`, `y_j = c₁(𝒩_j)`,
`c(π^*ℰ) = ∏ (1 + x_i)`, `c(π^*ℱ) = ∏ (1 + y_j)` and `c(π^*(ℰ ⊗ ℱ)) = ∏_{i,j} (1 + x_i + y_j)`. -/
theorem exists_totalChernCap_tensorObj_eq_prod_of_chernCapProperties
    (hC : ChernCapProperties.{u, v} D)
    (Q : MorphismProperty ((BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u))
    (E F : Modules.{u, u} D.site D.base D.base_mem X hX.1) (r s : ℕ)
    (hr : IsFiniteLocallyFreeOfRank D sX hX E r) (hs : IsFiniteLocallyFreeOfRank D sX hX F s)
    (hsplit : IsSplitting.{v} D Q sX hX ![E, F] ![r, s]) :
    ∃ (P : D.Ambient) (π : P ⟶ X) (hP : D.IsGood (π ≫ sX))
      (d : ℕ) (_ : IsFlat D.site D.base D.base_mem π)
      (_ : HasRelativeDimension d D.site D.base D.base_mem π),
      HasInjectiveChowBaseChange.{v} D sX π d ∧
      ∃ (L : Fin r → Modules.{u, u} D.site D.base D.base_mem P hP.1)
        (N : Fin s → Modules.{u, u} D.site D.base D.base_mem P hP.1)
        (hL : ∀ i, IsFiniteLocallyFreeOfRank D (π ≫ sX) hP (L i) 1)
        (hN : ∀ j, IsFiniteLocallyFreeOfRank D (π ≫ sX) hP (N j) 1),
        (∀ i, IsInvertibleModule ⟨P, hP.1⟩ (L i)) ∧ (∀ j, IsInvertibleModule ⟨P, hP.1⟩ (N j)) ∧
        totalChernCap.{u, v} ((spaceModulePullback D hX.1 hP.1 π).obj E) r
            (isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem
              (ObjectProperty.homMk π : (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
                ⟨X, hX.1⟩) hr) =
          ((List.finRange r).map fun i => 1 + chernCap.{u, v} (L i) 1 (hL i) 1).prod ∧
        totalChernCap.{u, v} ((spaceModulePullback D hX.1 hP.1 π).obj F) s
            (isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem
              (ObjectProperty.homMk π : (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
                ⟨X, hX.1⟩) hs) =
          ((List.finRange s).map fun j => 1 + chernCap.{u, v} (N j) 1 (hN j) 1).prod ∧
        totalChernCap.{u, v} ((spaceModulePullback D hX.1 hP.1 π).obj (E ⊗ F)) (r * s)
            (isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem
              (ObjectProperty.homMk π : (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
                ⟨X, hX.1⟩) (isFiniteLocallyFreeOfRank_tensorObj D.site D.base D.base_mem X hX.1
                  hr hs)) =
          ((List.finRange r).flatMap fun i => (List.finRange s).map fun j =>
            1 + (chernCap.{u, v} (L i) 1 (hL i) 1 + chernCap.{u, v} (N j) 1 (hN j) 1)).prod := by
  obtain ⟨P, sP, hP, π, rfl, d, hflat, hd, -, hinj, hfil⟩ := hsplit
  have hfilE := hfil 0
  have hfilF := hfil 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hfilE hfilF
  obtain ⟨Ls, Ns, hLlen, hNlen, hcE, hcF, hcEF⟩ := exists_chernSeries_tensorObj_eq_prod
    (hC.chernCap_eq_zero_of_lt hP) (hC.chernCap_shortExact hP) (hC.chernCap_one_tensorObj hP)
    hfilE hfilF
  subst hLlen hNlen
  refine ⟨P, π, hP, d, hflat, hd, hinj, fun i => (Ls.get i).1, fun j => (Ns.get j).1,
    fun i => isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hP) (Ls.get i).2,
    fun j => isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hP) (Ns.get j).2,
    fun i => (Ls.get i).2, fun j => (Ns.get j).2, ?_, ?_, ?_⟩
  · exact totalChernCap_eq_prod_get_of_mk_eq _ Ls _ hcE
  · exact totalChernCap_eq_prod_get_of_mk_eq _ Ns _ hcF
  · have hiso := Finset.sum_congr rfl fun n (_ : n ∈ Finset.range (Ls.length * Ns.length + 1)) =>
      hC.chernCap_congr_iso hP ((spaceModulePullback D hX.1 hP.1 π).obj (E ⊗ F))
        ((spaceModulePullback D hX.1 hP.1 π).obj E ⊗ (spaceModulePullback D hX.1 hP.1 π).obj F)
        (Ls.length * Ns.length)
        (isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem
          (ObjectProperty.homMk π : (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
            ⟨X, hX.1⟩) (isFiniteLocallyFreeOfRank_tensorObj D.site D.base D.base_mem X hX.1
              hr hs))
        (isFiniteLocallyFreeOfRank_tensorObj D.site D.base D.base_mem P hP.1
          (isFiniteLocallyFreeOfRank_of_hasFiltrationOfLength hfilE)
          (isFiniteLocallyFreeOfRank_of_hasFiltrationOfLength hfilF)) n
        ⟨(@Functor.Monoidal.μIso _ _ _ _ _ _ _ (modulePullbackMonoidal
          (ObjectProperty.homMk π : (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
            ⟨X, hX.1⟩)) E F).symm⟩
    refine hiso.trans ?_
    rw [← totalChernCap, totalChernCap_eq_prod_of_mk_eq _ _ _ _
      (length_flatMap_map_add Ls Ns
        (fun L => chernCap.{u, v} L.1 1
          (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hP) L.2) 1)
        (fun L => chernCap.{u, v} L.1 1
          (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hP) L.2) 1))
      (hcEF.trans (congrArg List.prod (map_flatMap_map_add_one_add_C_mul_X Ls Ns
        (fun L => chernCap.{u, v} L.1 1
          (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hP) L.2) 1)
        (fun L => chernCap.{u, v} L.1 1
          (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hP) L.2) 1)).symm)),
      map_flatMap_map_add_one_add]

end AlgebraicGeometry.Space.PrivateChern

end
