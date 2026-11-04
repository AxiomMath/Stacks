module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBasicOpenLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CoherentSheafCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingIdealGeometricStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedMinimalSupport

/-!
# Localizing a geometric stalk at the germ of a regular function

Let `X` be an algebraic space, `x̄` a geometric point, `N₀` a small étale neighbourhood of `x̄`
and `g` a regular function on its chart, with germ `ḡ ∈ 𝒪_{X, x̄}`.  For a map `φ : K → K'` of
quasi-coherent `𝒪_X`-modules this file reads the localization at `ḡ` of the stalk map
`K_x̄ → K'_x̄` off the sections of `φ` over the basic-open charts `D(g)`: if `φ` is bijective on
`D(g|_M)` for every affine neighbourhood `M` over `N₀`, then `(K_x̄)_ḡ → (K'_x̄)_ḡ` is bijective.

## Main results

* `AlgebraicGeometry.Space.exists_pow_smul_eq_zero_of_geometricModuleStalkMap_eq_zero`: the
  injectivity half — an element killed by `φ_x̄` is killed by a power of `ḡ`.
* `AlgebraicGeometry.Space.exists_pow_smul_eq_geometricModuleStalkMap`: the surjectivity half —
  every element of `K'_x̄` times a power of `ḡ` is in the image of `φ_x̄`.
* `AlgebraicGeometry.Space.bijective_localizedMap_geometricModuleStalkLinearMap`: the two
  together, as bijectivity of `LocalizedModule.map`.

## Implementation notes

Both halves are germ chases.  A germ is represented over an affine neighbourhood `M` lying over
`N₀` (`AlgebraicGeometry.Space.exists_affine_smallEtaleNeighborhood_over_two`), the hypothesis is
applied on the basic-open chart of `g|_M`, and the conclusion is carried back to `M` by Stacks
0859 (2) in the form `AlgebraicGeometry.Space.chartRestrictLinear_openChart_basicOpen_eq_zero_iff`
and by the localization property
`AlgebraicGeometry.Space.isLocalizedModule_chartRestrictLinear_openChart_basicOpen` of sections
of a quasi-coherent module over a basic open.  Quasi-coherence enters only there, through
Stacks 03DX (2).

## References

* [Stacks Project, Tag 0AF0](https://stacks.math.columbia.edu/tag/0AF0)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS) (x : GeometricPoint B S hS X.1)

/-- Two small étale neighbourhoods of a geometric point have a common refinement whose chart is
affine. -/
theorem exists_affine_smallEtaleNeighborhood_over_two (N N₀ : SmallEtaleNeighborhood x) :
    ∃ (M : SmallEtaleNeighborhood x) (_ : M ⟶ N) (_ : M ⟶ N₀),
      IsAffine (chartScheme M.chart) := by
  have := isCofiltered_smallEtaleNeighborhood B S hS X.1 X.2 x
  obtain ⟨M₀, a, b, -⟩ := IsCofilteredOrEmpty.cone_objs N N₀
  obtain ⟨M, g, hM⟩ := exists_smallEtaleNeighborhoodHom_isAffine B S hS X x M₀
  exact ⟨M, g ≫ a, g ≫ b, hM⟩

variable {K K' : Modules.{u, u} B S hS X.1 X.2} (φ : K ⟶ K') (N₀ : SmallEtaleNeighborhood x)
  (g : chartRing B S hS X.1 X.2 N₀.chart)

/-- The basic-open chart of the restriction of `g` to a neighbourhood over `N₀`. -/
noncomputable abbrev basicOpenChartOver {M : SmallEtaleNeighborhood x} (d : M ⟶ N₀) :
    SmallEtale B S hS X.1 :=
  openChart B S hS X.1 M.chart ((chartScheme M.chart).basicOpen (chartRestrict (hF := X.2) d.hom g))

/-- The inclusion of `basicOpenChartOver` into the chart of the neighbourhood. -/
noncomputable abbrev basicOpenChartOverInclusion {M : SmallEtaleNeighborhood x} (d : M ⟶ N₀) :
    basicOpenChartOver B S hS X x N₀ g d ⟶ M.chart :=
  openChartInclusion B S hS X.1 M.chart
    ((chartScheme M.chart).basicOpen (chartRestrict (hF := X.2) d.hom g))

/-- The germ at `x̄` of `(g|_M)ᵏ • s` is `ḡᵏ` times the germ of `s`, where `ḡ` is the germ of
`g`. -/
theorem germ_pow_smul_germ {M : SmallEtaleNeighborhood x} (d : M ⟶ N₀) (k : ℕ)
    (s : K.val.obj (op M.chart)) :
    geometricModuleStalkGerm B S hS X x K M ((chartRestrict (hF := X.2) d.hom g) ^ k • s) =
      (etaleLocalRingGerm B S hS X.1 x (op N₀) g) ^ k •
        geometricModuleStalkGerm B S hS X x K M s := by
  rw [geometricModuleStalkGerm_smul]
  have h : etaleLocalRingGerm B S hS X.1 x (op M) ((chartRestrict (hF := X.2) d.hom g) ^ k) =
      (etaleLocalRingGerm B S hS X.1 x (op M) (chartRestrict (hF := X.2) d.hom g)) ^ k :=
    map_pow (etaleLocalRingGerm B S hS X.1 x (op M)) _ k
  rw [h, etaleLocalRingGerm_chartRestrict]

/-- A map of presheaves of modules sends the restriction of a section it kills to zero. -/
private theorem app_map_eq_zero_of_app_eq_zero {A A' : SmallEtale B S hS X.1} (f : A ⟶ A')
    (s : K.val.obj (op A')) (h : φ.val.app (op A') s = 0) :
    φ.val.app (op A) (K.val.map f.op s) = 0 :=
  ((PresheafOfModules.naturality_apply φ.val f.op s).trans (congrArg (K'.val.map f.op) h)).trans
    (map_zero _)

/-- **Injectivity half.**  If `φ` is injective on the basic-open charts of `g` over affine
neighbourhoods, then an element of `K_x̄` killed by `φ` is killed by a power of the germ of `g`. -/
theorem exists_pow_smul_eq_zero_of_geometricModuleStalkMap_eq_zero
    (hK : K.IsQuasicoherentOnSite)
    (hφ : ∀ (M : SmallEtaleNeighborhood x) (d : M ⟶ N₀), IsAffine (chartScheme M.chart) →
      Function.Injective (φ.val.app (op (basicOpenChartOver B S hS X x N₀ g d))))
    (z : geometricModuleStalk B S hS X x K) (hz : geometricModuleStalkMap B S hS X x φ z = 0) :
    ∃ k : ℕ, (etaleLocalRingGerm B S hS X.1 x (op N₀) g) ^ k • z = 0 := by
  obtain ⟨N, s, rfl⟩ := geometricModuleStalkGerm_jointly_surjective B S hS X x K z
  rw [geometricModuleStalkMap_germ] at hz
  obtain ⟨M, m, hm⟩ := (geometricModuleStalkGerm_eq_zero_iff B S hS X x K' N _).1 hz
  obtain ⟨M₁, c, d, hM₁⟩ := exists_affine_smallEtaleNeighborhood_over_two B S hS X x M N₀
  let s₂ : K.val.obj (op M₁.chart) := K.val.map c.hom.op (K.val.map m.hom.op s)
  have hs₂ : φ.val.app (op M₁.chart) s₂ = 0 :=
    app_map_eq_zero_of_app_eq_zero B S hS X φ c.hom _
      ((PresheafOfModules.naturality_apply φ.val m.hom.op s).trans hm)
  have hD : K.val.map (basicOpenChartOverInclusion B S hS X x N₀ g d).op s₂ = 0 :=
    hφ M₁ d hM₁ ((app_map_eq_zero_of_app_eq_zero B S hS X φ _ _ hs₂).trans (map_zero _).symm)
  obtain ⟨k, hk⟩ := (chartRestrictLinear_openChart_basicOpen_eq_zero_iff B S hS X.2 K
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 K hK) M₁.chart hM₁
    (chartRestrict (hF := X.2) d.hom g) s₂).1 hD
  have hgerm : geometricModuleStalkGerm B S hS X x K M₁ s₂ =
      geometricModuleStalkGerm B S hS X x K N s :=
    (geometricModuleStalkGerm_map B S hS X x K c _).trans
      (geometricModuleStalkGerm_map B S hS X x K m s)
  exact ⟨k, by rw [← hgerm, ← germ_pow_smul_germ B S hS X x N₀ g d k, hk, map_zero]⟩

/-- **Surjectivity half.**  If `φ` is surjective on the basic-open charts of `g` over affine
neighbourhoods, then every element of `K'_x̄` times some power of the germ of `g` is in the image
of `φ`. -/
theorem exists_pow_smul_eq_geometricModuleStalkMap
    (hK : K.IsQuasicoherentOnSite) (hK' : K'.IsQuasicoherentOnSite)
    (hφ : ∀ (M : SmallEtaleNeighborhood x) (d : M ⟶ N₀), IsAffine (chartScheme M.chart) →
      Function.Surjective (φ.val.app (op (basicOpenChartOver B S hS X x N₀ g d))))
    (z' : geometricModuleStalk B S hS X x K') :
    ∃ (k : ℕ) (z : geometricModuleStalk B S hS X x K),
      (etaleLocalRingGerm B S hS X.1 x (op N₀) g) ^ k • z' =
        geometricModuleStalkMap B S hS X x φ z := by
  obtain ⟨N, t, rfl⟩ := geometricModuleStalkGerm_jointly_surjective B S hS X x K' z'
  obtain ⟨M, c, d, hM⟩ := exists_affine_smallEtaleNeighborhood_over_two B S hS X x N N₀
  let t₁ : K'.val.obj (op M.chart) := K'.val.map c.hom.op t
  let g₁ := chartRestrict (hF := X.2) d.hom g
  let ι := basicOpenChartOverInclusion B S hS X x N₀ g d
  obtain ⟨u, hu⟩ := hφ M d hM (K'.val.map ι.op t₁)
  have hloc := isLocalizedModule_chartRestrictLinear_openChart_basicOpen B S hS X.2 K
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 K hK) M.chart hM g₁
  let := chartSectionsModule K ι
  obtain ⟨⟨v, ⟨_, k, rfl⟩⟩, hv⟩ := IsLocalizedModule.surj (Submonoid.powers g₁)
    (chartRestrictLinear K ι) u
  have hv' : chartRestrict (hF := X.2) ι (g₁ ^ k) • u = K.val.map ι.op v := hv
  let r := chartRestrict (hF := X.2) ι (g₁ ^ k)
  let tD : K'.val.obj (op (basicOpenChartOver B S hS X x N₀ g d)) := K'.val.map ι.op t₁
  have e1 : K'.val.map ι.op (φ.val.app (op M.chart) v) = r • tD :=
    (PresheafOfModules.naturality_apply φ.val ι.op v).symm.trans
      ((congrArg (φ.val.app (op (basicOpenChartOver B S hS X x N₀ g d))) hv'.symm).trans
        ((map_smul (ConcreteCategory.hom (φ.val.app (op (basicOpenChartOver B S hS X x N₀ g d))))
          r u).trans (congrArg (r • ·) hu)))
  have e2 : K'.val.map ι.op (g₁ ^ k • t₁) = r • tD :=
    PresheafOfModules.map_smul K'.val ι.op (g₁ ^ k) t₁
  have hφv : K'.val.map ι.op (φ.val.app (op M.chart) v - g₁ ^ k • t₁) = 0 :=
    (map_sub (ConcreteCategory.hom (K'.val.map ι.op)) _ _).trans
      ((congrArg₂ (· - ·) e1 e2).trans (sub_self _))
  obtain ⟨l, hl⟩ := (chartRestrictLinear_openChart_basicOpen_eq_zero_iff B S hS X.2 K'
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 K' hK') M.chart hM
    g₁ _).1 hφv
  have hl' : g₁ ^ l • φ.val.app (op M.chart) v = g₁ ^ l • g₁ ^ k • t₁ := by
    rwa [smul_sub, sub_eq_zero] at hl
  refine ⟨l + k, (etaleLocalRingGerm B S hS X.1 x (op N₀) g) ^ l •
    geometricModuleStalkGerm B S hS X x K M v, ?_⟩
  refine Eq.symm ((geometricModuleStalkMap_smul B S hS X x φ _ _).trans ?_)
  refine (congrArg (_ • ·) (geometricModuleStalkMap_germ B S hS X x φ M v)).trans ?_
  refine (germ_pow_smul_germ B S hS X x N₀ g d l _).symm.trans ?_
  refine (congrArg (geometricModuleStalkGerm B S hS X x K' M) hl').trans ?_
  refine (germ_pow_smul_germ B S hS X x N₀ g d l _).trans ?_
  refine (congrArg (_ • ·) (germ_pow_smul_germ B S hS X x N₀ g d k _)).trans ?_
  rw [← mul_smul, ← pow_add]
  exact congrArg (_ • ·) (geometricModuleStalkGerm_map B S hS X x K' c t)

/-- **Localizing a map of geometric stalks.**  Let `φ : K → K'` be a map of quasi-coherent
`𝒪_X`-modules, `N₀` a small étale neighbourhood of `x̄` and `g` a regular function on its chart.
If `φ` is bijective on the basic-open chart of (the restriction of) `g` over every affine
neighbourhood lying over `N₀`, then the map `K_x̄ → K'_x̄` becomes bijective after inverting the
germ of `g`. -/
theorem bijective_localizedMap_geometricModuleStalkLinearMap
    (hK : K.IsQuasicoherentOnSite) (hK' : K'.IsQuasicoherentOnSite)
    (hφ : ∀ (M : SmallEtaleNeighborhood x) (d : M ⟶ N₀), IsAffine (chartScheme M.chart) →
      Function.Bijective (φ.val.app (op (basicOpenChartOver B S hS X x N₀ g d)))) :
    Function.Bijective (LocalizedModule.map
      (Submonoid.powers (etaleLocalRingGerm B S hS X.1 x (op N₀) g))
      (geometricModuleStalkLinearMap B S hS X x φ)) := by
  set germ₀ := etaleLocalRingGerm B S hS X.1 x (op N₀) g
  have hmem : ∀ n : ℕ, germ₀ ^ n ∈ Submonoid.powers germ₀ :=
    fun n ↦ (Submonoid.mem_powers_iff _ _).2 ⟨n, rfl⟩
  constructor
  · rw [injective_iff_map_eq_zero]
    intro y hy
    induction y using LocalizedModule.induction_on with
    | h z c =>
      rw [LocalizedModule.map_mk] at hy
      obtain ⟨⟨_, j, rfl⟩, hj⟩ := (LocalizedModule.mk_eq (m := geometricModuleStalkLinearMap
        B S hS X x φ z) (m' := 0) (s := c) (s' := 1)).1 (hy.trans (LocalizedModule.zero_mk 1).symm)
      rw [one_smul, smul_zero, smul_zero] at hj
      have hj' : geometricModuleStalkMap B S hS X x φ (germ₀ ^ j • z) = 0 := by
        rwa [geometricModuleStalkMap_smul]
      obtain ⟨k, hk⟩ := exists_pow_smul_eq_zero_of_geometricModuleStalkMap_eq_zero B S hS X x φ N₀
        g hK (fun M d hM ↦ (hφ M d hM).1) _ hj'
      refine (LocalizedModule.mk_eq.2 ⟨⟨germ₀ ^ (k + j), hmem (k + j)⟩, ?_⟩).trans
        (LocalizedModule.zero_mk c)
      rw [smul_zero, smul_zero, smul_comm]
      show c • (germ₀ ^ (k + j) • z) = 0
      rw [pow_add, mul_smul, hk, smul_zero]
  · intro y
    induction y using LocalizedModule.induction_on with
    | h z' c =>
      obtain ⟨k, z, hz⟩ := exists_pow_smul_eq_geometricModuleStalkMap B S hS X x φ N₀ g hK hK'
        (fun M d hM ↦ (hφ M d hM).2) z'
      refine ⟨LocalizedModule.mk z (⟨germ₀ ^ k, hmem k⟩ * c), ?_⟩
      rw [LocalizedModule.map_mk]
      have h1 : geometricModuleStalkLinearMap B S hS X x φ z = germ₀ ^ k • z' := hz.symm
      rw [h1]
      exact LocalizedModule.mk_cancel_common_left ⟨germ₀ ^ k, hmem k⟩ c z'

end AlgebraicGeometry.Space

end
