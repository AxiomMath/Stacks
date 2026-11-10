module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedComparisonOfLevels
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelComparisonTaylor
public import StacksFrontier.RingTheory.AdicCompletion.InverseLimitTensor

/-!
# The last two fields of the comparison datum of [Stacks, Tag 07JG], from the levels

`Crystalline.GlobalCrystallineSituation.SmallSite.LevelComparison07JG` is the datum the functor of
[Stacks, Lemma 60.17.3, Tag 07JG] is built from.  Four of its six fields are proved —
`isPAdicallyComplete` in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/LevelSectionsPAdicComplete.lean` and
`hasCoordinateOperators`, `isIntegrable`, `isTopologicallyQuasiNilpotent` in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/LevelComparisonTaylor.lean` — and the two
that remain, `comparison` and `comparison_naturality`, are stated over the *limit* module
`M = lim_e Γ(T_e, ℱ)` and the ring `firstOrderExtension D Ω`, while everything the site offers
about a crystal lives at one object of `Cris(X/S)`.  The step from a level-by-level datum to the
datum on `M` is an interchange — the first-order extension against the inverse limit over the
levels — and **this module is that interchange**.

The content is the algebraic lemma of
`StacksFrontier/RingTheory/AdicCompletion/InverseLimitTensor.lean`: base change along a module free
of finite rank commutes with the limit of an inverse system,
`bijective_invLimitTensorMap`.  Here the module is `D ⊕ Ω`, which is free of finite rank over `D`
as soon as `Ω` is — `Crystalline.firstOrderExtensionBasis` — so the hypothesis the interchange
costs is exactly the basis `b : Module.Basis ι D Ω` on the chosen differentials that
`...SmallSite.levelComparison07JGWholeSpaceOfTaylor` already carries, plus the finiteness of `ι`
that the basis is only available for anyway (`Ω_D` of [Stacks, Tag 07J9] is a completed direct
sum; see the module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/LevelComparisonTaylor.lean`).  Neither half
of the hypothesis can be dropped: for `Ω` free on an infinite basis the comparison map is not
surjective, the support of a compatible family being allowed to grow with the level.

With the interchange in hand, `comparison` and `comparison_naturality` are **derived** from a
level-by-level comparison datum: `...SmallSite.LevelScalars07JG.comparisonOfLevels` and
`...comparisonOfLevels_naturality`.  So
`...SmallSite.levelComparison07JGOfLevelwise` assembles a whole
`...SmallSite.LevelComparison07JG` from data at the objects `T_e` of the site alone, and
`...SmallSite.levelComparison07JGWholeSpaceOfLevelwise` does it at the system of levels of
[Stacks, Proposition 60.21.1, Tag 07JN].

The exponents are not shifted here but the shift is present: the annihilation
`...SmallSite.pow_smul_eq_zero_wholeSpaceLevelSections` that discharges item (07JB) at that
system is by `p^{N + e}` with `N = Crystalline.uniformLevel`, and the whole-space producer below
passes it through unchanged.

## Main definitions

* `Crystalline.firstOrderExtensionBasis` — a basis of `D ⊕ Ω` over `D`, from a basis of `Ω`: the
  unit of `D` together with the given basis of the square-zero summand.
* `Crystalline.levelTensorProj` — the level-`e` projection of the base change
  `(D ⊕ Ω) ⊗_D M` of a module identified with the limit of a tower.
* `Crystalline.levelTensorEquiv` — **the interchange**
  `(D ⊕ Ω) ⊗_D M ≅ lim_e ((D ⊕ Ω) ⊗_D M_e)`.
* `Crystalline.levelComparisonFun` — the comparison map on `M` assembled from a compatible family
  of comparison maps on the levels.
* `Crystalline.FirstOrderComparison.ofLevels` — **the comparison datum on `M`**, the three clauses
  checked level by level.
* `...SmallSite.LevelScalars07JG.levelSectionsMap` — a morphism of crystals read at one level, as
  a `D`-linear map.
* `...SmallSite.LevelScalars07JG.comparisonOfLevels` — the field `comparison` of
  `...SmallSite.LevelComparison07JG` from the levels.
* `...SmallSite.levelComparison07JGOfLevelwise` and
  `...SmallSite.levelComparison07JGWholeSpaceOfLevelwise` — the datum of [Stacks, Tag 07JG]
  assembled from level-by-level comparison data.

## Main results

* `Crystalline.eq_of_levelTensorProj_eq` — two elements of `(D ⊕ Ω) ⊗_D M` agreeing at every
  level are equal.  This is where the finite basis is used, and it is what makes the three
  clauses of a comparison datum checkable level by level.
* `Crystalline.levelComparisonFun_naturality` — **the naturality of the interchange**: a map of
  towers compatible with the level data induces the naturality of the limit data.
* `...SmallSite.LevelScalars07JG.comparisonOfLevels_naturality` — the field
  `comparison_naturality` from the levels.

## What is and is not proved

**No `@[stacks]` attribute is placed in this module.**  [Stacks, Tag 07JG],
[Stacks, Proposition 60.17.4, Tag 07JH] and [Stacks, Proposition 60.21.3, Tag 07LG] are
`...SmallSite.crystalPairFunctor`, `...SmallSite.crystalPairFunctor_isEquivalence` and
`...SmallSite.crystalPairDeRhamComplex_computesCohomology`, built directly from the whole-space
system and not through the level datum of this module.
What is settled is that `comparison` and `comparison_naturality` are no longer statements about
the limit: they follow from the comparison datum of a crystal at the single objects `T_e`,
natural in the crystal and compatible with the restrictions `T_e ⟶ T_{e+1}`.

That level-by-level datum is still an input, and it is a genuine one.  At a single object of the
site it is equivalent to bijectivity of one base-change map, by
`...GlobalCrystallineSituation.bijective_firstOrderSectionsMap_iff_bijective_extensionSectionsMap`
of `StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderIdealAffine.lean`, and that bijectivity
is proved nowhere in the tree; every level of `...SmallSite.wholeSpaceSystem` is affine, by
`...SmallSite.isAffine_wholeSpaceSystem_target`, which is what makes the question an affine one.
Reading that bijectivity as a `Crystalline.FirstOrderComparison` over `D` and `Ω` needs in
addition the ring map `firstOrderExtension D Ω ⟶ Γ(T'_e, 𝒪)` of the field
`...SmallSite.LevelReduction07JG.thickeningRingHom` and the identification of
`Ω ⊗_D Γ(T_e, ℱ)` with `Γ(T_e, Ω_{T_e/S,δ}) ⊗_{Γ(T_e,𝒪)} Γ(T_e, ℱ)`, neither of which is in the
tree either.  **Both are outside this module**, which takes the level-by-level
`Crystalline.FirstOrderComparison` whole.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07J9](https://stacks.math.columbia.edu/tag/07J9)
* [Stacks Project, Proposition 60.21.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct

universe u uI w

noncomputable section

namespace Crystalline

/-! ### A basis of the first-order thickening -/

section ExtensionBasis

variable {D : DividedPowerRing.{u}} {Omega : Type u} [AddCommGroup Omega]
  [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega] {ι : Type uI}

/-- **A basis of the first-order thickening `D ⊕ Ω` over `D`, from a basis of `Ω`.**  The
thickening is `TrivSqZeroExt D Ω`, which is `D × Ω` with the product `D`-action, so the unit of
`D` together with a basis of `Ω` is a basis of it.

This is what makes `bijective_invLimitTensorMap` applicable to the base change along
`D ⊕ Ω`, and it is the only use of the basis of `Ω` in this module. -/
def firstOrderExtensionBasis (b : Module.Basis ι (D : Type u) Omega) :
    Module.Basis (Unit ⊕ ι) (D : Type u) (firstOrderExtension D Omega) :=
  ((Module.Basis.singleton Unit (D : Type u)).prod b).map (LinearEquiv.refl _ _)

end ExtensionBasis

/-! ### The interchange: the first-order extension against the limit over the levels -/

section Interchange

variable {A : Type u} [CommRing A] {D : DividedPowerRing.{u}} {g : A →+* D} {Omega : Type u}
  [AddCommGroup Omega] [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
  {d : DividedPowerDerivation A D g Omega} {ι : Type uI} [Fintype ι]
  (M₀ : Type w) [AddCommGroup M₀] [Module (D : Type u) M₀]
  (lev : ℕ → Type w) [∀ n, AddCommGroup (lev n)] [∀ n, Module (D : Type u) (lev n)]
  (trans : ∀ n, lev (n + 1) →ₗ[(D : Type u)] lev n)
  (eqv : M₀ ≃ₗ[(D : Type u)] ↥(invLimit lev trans))

/-- **The level-`n` projection of the base change `(D ⊕ Ω) ⊗_D M`**, for a module `M` identified
with the limit of the tower `(M_n)`: the base change of the composite `M ≅ lim_n M_n ⟶ M_n`. -/
def levelTensorProj (n : ℕ) :
    firstOrderExtension D Omega ⊗[D] M₀ →ₗ[(D : Type u)]
      firstOrderExtension D Omega ⊗[D] lev n :=
  LinearMap.lTensor (firstOrderExtension D Omega)
    ((invLimit.proj lev trans n).comp (eqv : M₀ →ₗ[(D : Type u)] ↥(invLimit lev trans)))

/-- The level-`n` projection of the base change is the base change of the composite
`M ≅ lim_n M_n ⟶ M_n`. -/
theorem levelTensorProj_apply (n : ℕ) (z : firstOrderExtension D Omega ⊗[D] M₀) :
    levelTensorProj M₀ lev trans eqv n z =
      LinearMap.lTensor (firstOrderExtension D Omega)
        ((invLimit.proj lev trans n).comp (eqv : M₀ →ₗ[(D : Type u)] ↥(invLimit lev trans))) z :=
  rfl

/-- **The level projections of the base change are `D ⊕ Ω`-linear**, the action being on the left
factor and the projection on the right one. -/
theorem levelTensorProj_smul (n : ℕ) (a : firstOrderExtension D Omega)
    (z : firstOrderExtension D Omega ⊗[D] M₀) :
    levelTensorProj M₀ lev trans eqv n (a • z) =
      a • levelTensorProj M₀ lev trans eqv n z :=
  lTensor_smul_firstOrderExtension
    ((invLimit.proj lev trans n).comp (eqv : M₀ →ₗ[(D : Type u)] ↥(invLimit lev trans))) a z

/-- **The interchange `(D ⊕ Ω) ⊗_D M ≅ lim_n ((D ⊕ Ω) ⊗_D M_n)`**: the first-order extension of
[Stacks, Tag 07J2] commutes with the inverse limit over the levels.

This is `invLimitTensorEquiv` for the base change along `D ⊕ Ω`, which is free of
finite rank over `D` by `Crystalline.firstOrderExtensionBasis`, carried across the given
identification of `M` with the limit. -/
def levelTensorEquiv (b : Module.Basis ι (D : Type u) Omega) :
    firstOrderExtension D Omega ⊗[D] M₀ ≃ₗ[(D : Type u)]
      ↥(invLimitTensor (firstOrderExtension D Omega) lev trans) :=
  (TensorProduct.congr (LinearEquiv.refl (D : Type u) (firstOrderExtension D Omega)) eqv).trans
    (invLimitTensorEquiv (firstOrderExtension D Omega) lev trans (firstOrderExtensionBasis b))

/-- The level-`n` component of the interchange `Crystalline.levelTensorEquiv` is the level-`n`
projection `Crystalline.levelTensorProj`. -/
@[simp] theorem levelTensorEquiv_val (b : Module.Basis ι (D : Type u) Omega)
    (z : firstOrderExtension D Omega ⊗[D] M₀) (n : ℕ) :
    (levelTensorEquiv M₀ lev trans eqv b z).val n = levelTensorProj M₀ lev trans eqv n z := by
  have hcongr : (TensorProduct.congr
        (LinearEquiv.refl (D : Type u) (firstOrderExtension D Omega)) eqv) z =
      LinearMap.lTensor (firstOrderExtension D Omega)
        (eqv : M₀ →ₗ[(D : Type u)] ↥(invLimit lev trans)) z := by
    induction z using TensorProduct.inductionOn with
    | tmul a m => rw [TensorProduct.congr_tmul, LinearMap.lTensor_tmul]; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  change LinearMap.lTensor (firstOrderExtension D Omega) (invLimit.proj lev trans n)
      ((TensorProduct.congr
        (LinearEquiv.refl (D : Type u) (firstOrderExtension D Omega)) eqv) z) = _
  rw [hcongr, levelTensorProj_apply, LinearMap.lTensor_comp, LinearMap.comp_apply]

omit [Fintype ι] in
/-- **Two elements of the base change `(D ⊕ Ω) ⊗_D M` that agree at every level are equal.**  This
is injectivity of the interchange `Crystalline.levelTensorEquiv`, and it is what lets the three
clauses of a comparison datum on `M` be checked one level at a time. -/
theorem eq_of_levelTensorProj_eq [Finite ι] (b : Module.Basis ι (D : Type u) Omega)
    {z w : firstOrderExtension D Omega ⊗[D] M₀}
    (h : ∀ n, levelTensorProj M₀ lev trans eqv n z = levelTensorProj M₀ lev trans eqv n w) :
    z = w :=
  have := Fintype.ofFinite ι
  (levelTensorEquiv M₀ lev trans eqv b).injective
    (Subtype.ext (funext fun n ↦ by
      rw [levelTensorEquiv_val, levelTensorEquiv_val, h n]))

variable (c : ∀ n, FirstOrderComparison A D g Omega d (lev n))
  (hc : ∀ (n : ℕ) (x : lev (n + 1)),
    LinearMap.lTensor (firstOrderExtension D Omega) (trans n) (c (n + 1) x) = c n (trans n x))

/-- **The comparison map on `M = lim_n M_n`**, the level-by-level comparison values read back
across the interchange `Crystalline.levelTensorEquiv`. -/
def levelComparisonFun (b : Module.Basis ι (D : Type u) Omega) (m : M₀) :
    firstOrderExtension D Omega ⊗[D] M₀ :=
  (levelTensorEquiv M₀ lev trans eqv b).symm
    (levelComparisonTower M₀ lev trans
        (fun n ↦ (invLimit.proj lev trans n).comp (eqv : M₀ →ₗ[(D : Type u)] ↥(invLimit lev trans)))
        (fun n ↦ LinearMap.ext fun x ↦ invLimit.proj_comp_transition lev trans n (eqv x)) c hc m)

/-- The comparison map on `M` is the inverse of the interchange applied to the compatible family
of level comparison values. -/
theorem levelComparisonFun_def (b : Module.Basis ι (D : Type u) Omega) (m : M₀) :
    levelComparisonFun M₀ lev trans eqv c hc b m =
      (levelTensorEquiv M₀ lev trans eqv b).symm
        (levelComparisonTower M₀ lev trans
          (fun n ↦ (invLimit.proj lev trans n).comp
            (eqv : M₀ →ₗ[(D : Type u)] ↥(invLimit lev trans)))
          (fun n ↦ LinearMap.ext fun x ↦ invLimit.proj_comp_transition lev trans n (eqv x))
          c hc m) :=
  rfl

/-- **The comparison map on `M` is the one with the prescribed values at the levels.**  This is
the only property of `Crystalline.levelComparisonFun` the rest of the module uses, and with
`Crystalline.eq_of_levelTensorProj_eq` it determines it. -/
@[simp] theorem levelTensorProj_levelComparisonFun (b : Module.Basis ι (D : Type u) Omega)
    (m : M₀) (n : ℕ) :
    levelTensorProj M₀ lev trans eqv n (levelComparisonFun M₀ lev trans eqv c hc b m) =
      c n (invLimit.proj lev trans n (eqv m)) := by
  rw [← levelTensorEquiv_val M₀ lev trans eqv b, levelComparisonFun_def,
    LinearEquiv.apply_symm_apply, levelComparisonTower_val]
  rfl

/-- At every level, the reduction modulo `Ω` of the comparison map on `M = lim_n M_n` is the
identity: the level-`n` projection of the reduction of `Crystalline.levelComparisonFun` at `m` is
the level-`n` projection of `m`. -/
theorem proj_firstOrderReduction_levelComparisonFun
    (b : Module.Basis ι (D : Type u) Omega) (m : M₀) (n : ℕ) :
    invLimit.proj lev trans n
        (eqv (firstOrderReduction D Omega M₀
          (levelComparisonFun M₀ lev trans eqv c hc b m))) =
      invLimit.proj lev trans n (eqv m) := by
  rw [show invLimit.proj lev trans n
        (eqv (firstOrderReduction D Omega M₀
          (levelComparisonFun M₀ lev trans eqv c hc b m))) =
      firstOrderReduction D Omega (lev n)
        (levelTensorProj M₀ lev trans eqv n
          (levelComparisonFun M₀ lev trans eqv c hc b m)) from
    (firstOrderReduction_lTensor D Omega M₀ (lev n)
      ((invLimit.proj lev trans n).comp (eqv : M₀ →ₗ[(D : Type u)] ↥(invLimit lev trans)))
      (levelComparisonFun M₀ lev trans eqv c hc b m)).symm,
    levelTensorProj_levelComparisonFun, (c n).reduction']

/-- **A first-order comparison datum on `M = lim_n M_n` from comparison data on the levels.**

This is the interchange of the module documentation: the datum of
`Crystalline.FirstOrderComparison` is stated over the base change `(D ⊕ Ω) ⊗_D M`, the data
available are stated over `(D ⊕ Ω) ⊗_D M_n`, and
`Crystalline.levelTensorEquiv` identifies the first with the limit of the second.  All three
clauses — additivity, reduction to the identity modulo `Ω`, and semilinearity for `p₁` — are
checked level by level, by `Crystalline.eq_of_levelTensorProj_eq`; nothing about the tower is
assumed beyond the compatibility `hc` of the data with its transition maps. -/
def FirstOrderComparison.ofLevels (b : Module.Basis ι (D : Type u) Omega) :
    FirstOrderComparison A D g Omega d M₀ where
  toFun := levelComparisonFun M₀ lev trans eqv c hc b
  map_add' m m' :=
    eq_of_levelTensorProj_eq M₀ lev trans eqv b fun n ↦ by
      rw [_root_.map_add (levelTensorProj M₀ lev trans eqv n),
        levelTensorProj_levelComparisonFun, levelTensorProj_levelComparisonFun,
        levelTensorProj_levelComparisonFun, _root_.map_add eqv,
        _root_.map_add (invLimit.proj lev trans n), (c n).map_add']
  reduction' m :=
    eqv.injective (Subtype.ext (funext fun n ↦
      proj_firstOrderReduction_levelComparisonFun M₀ lev trans eqv c hc b m n))
  semilinear' f m :=
    eq_of_levelTensorProj_eq M₀ lev trans eqv b fun n ↦ by
      rw [levelTensorProj_levelComparisonFun, levelTensorProj_smul,
        levelTensorProj_levelComparisonFun, map_smul, map_smul, (c n).semilinear']

/-- The comparison datum `Crystalline.FirstOrderComparison.ofLevels` is given by
`Crystalline.levelComparisonFun`. -/
@[simp] theorem FirstOrderComparison.ofLevels_apply (b : Module.Basis ι (D : Type u) Omega)
    (m : M₀) :
    FirstOrderComparison.ofLevels M₀ lev trans eqv c hc b m =
      levelComparisonFun M₀ lev trans eqv c hc b m :=
  rfl

end Interchange

/-! ### Naturality of the interchange -/

section Naturality

variable {A : Type u} [CommRing A] {D : DividedPowerRing.{u}} {g : A →+* D} {Omega : Type u}
  [AddCommGroup Omega] [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
  {d : DividedPowerDerivation A D g Omega} {ι : Type uI} [Fintype ι]
  (M₀ : Type w) [AddCommGroup M₀] [Module (D : Type u) M₀]
  (M₁ : Type w) [AddCommGroup M₁] [Module (D : Type u) M₁]
  (lev : ℕ → Type w) [∀ n, AddCommGroup (lev n)] [∀ n, Module (D : Type u) (lev n)]
  (trans : ∀ n, lev (n + 1) →ₗ[(D : Type u)] lev n)
  (lev' : ℕ → Type w) [∀ n, AddCommGroup (lev' n)] [∀ n, Module (D : Type u) (lev' n)]
  (trans' : ∀ n, lev' (n + 1) →ₗ[(D : Type u)] lev' n)
  (eqv : M₀ ≃ₗ[(D : Type u)] ↥(invLimit lev trans))
  (eqv' : M₁ ≃ₗ[(D : Type u)] ↥(invLimit lev' trans'))

/-- **The interchange is natural.**  Given a `D`-linear map `M ⟶ M'` which at every level is a
`D`-linear map `M_n ⟶ M'_n` (the hypothesis `hphi`), and comparison data on the two towers that
the level maps carry into one another (the hypothesis `hnat`), the comparison maps on the two
limits are carried into one another too.

This is the clause `comparison_naturality` of
`Crystalline.GlobalCrystallineSituation.SmallSite.LevelComparison07JG` reduced to its level-by-
level form, and like the three clauses of
`Crystalline.FirstOrderComparison.ofLevels` it is proved by comparing the two sides at each
level. -/
theorem levelComparisonFun_naturality
    (phi : M₀ →ₗ[(D : Type u)] M₁) (philev : ∀ n, lev n →ₗ[(D : Type u)] lev' n)
    (hphi : ∀ (n : ℕ) (m : M₀), invLimit.proj lev' trans' n (eqv' (phi m)) =
      philev n (invLimit.proj lev trans n (eqv m)))
    (c : ∀ n, FirstOrderComparison A D g Omega d (lev n))
    (hc : ∀ (n : ℕ) (x : lev (n + 1)),
      LinearMap.lTensor (firstOrderExtension D Omega) (trans n) (c (n + 1) x) = c n (trans n x))
    (c' : ∀ n, FirstOrderComparison A D g Omega d (lev' n))
    (hc' : ∀ (n : ℕ) (x : lev' (n + 1)),
      LinearMap.lTensor (firstOrderExtension D Omega) (trans' n) (c' (n + 1) x) =
        c' n (trans' n x))
    (hnat : ∀ (n : ℕ) (x : lev n),
      c' n (philev n x) = LinearMap.lTensor (firstOrderExtension D Omega) (philev n) (c n x))
    (b : Module.Basis ι (D : Type u) Omega) (m : M₀) :
    levelComparisonFun M₁ lev' trans' eqv' c' hc' b (phi m) =
      LinearMap.lTensor (firstOrderExtension D Omega) phi
        (levelComparisonFun M₀ lev trans eqv c hc b m) :=
  eq_of_levelTensorProj_eq M₁ lev' trans' eqv' b fun n ↦ by
    have hcomp : ((invLimit.proj lev' trans' n).comp
          (eqv' : M₁ →ₗ[(D : Type u)] ↥(invLimit lev' trans'))).comp phi =
        (philev n).comp ((invLimit.proj lev trans n).comp
          (eqv : M₀ →ₗ[(D : Type u)] ↥(invLimit lev trans))) :=
      LinearMap.ext fun x ↦ hphi n x
    rw [levelTensorProj_levelComparisonFun, hphi n m, hnat n,
      levelTensorProj_apply M₁ lev' trans' eqv' n, ← LinearMap.comp_apply,
      ← LinearMap.lTensor_comp, hcomp, LinearMap.lTensor_comp, LinearMap.comp_apply,
      ← levelTensorProj_apply M₀ lev trans eqv n, levelTensorProj_levelComparisonFun]

end Naturality

namespace GlobalCrystallineSituation.SmallSite

/-! ### A morphism of crystals at one level -/

variable {S : GlobalCrystallineSituation.{u}} {A : Type u} [CommRing A]
  {D : DividedPowerRing.{u}} {g : A →+* D} {Omega : Type u} [AddCommGroup Omega]
  [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
  {d : DividedPowerDerivation A D g Omega} {p : ℕ} {ι : Type uI} {dx : ι → Omega}

namespace LevelScalars07JG

variable (L : LevelScalars07JG S D)

/-- **A morphism of crystals read at one level, as a `D`-linear map.**  It is the component of the
induced morphism of presheaves of modules at the level `e`, which is linear over the section ring
`Γ(T_e, 𝒪_{T_e})`; `D` acts on both sides through one and the same reduction
`...SmallSite.LevelScalars07JG.levelRingHom`, so the semilinearity becomes linearity.

This is `...SmallSite.LevelScalars07JG.sectionsMap` one level down: the limit of these maps is
that one, by `...LevelScalars07JG.sectionsMap_val`. -/
def levelSectionsMap {F G : QuasiCoherentCrystal S} (psi : F ⟶ G) (e : ℕ) :
    L.levelSections F e →ₗ[(D : Type u)] L.levelSections G e where
  toFun x := (PresheafOfModules.Hom.app ((quasiCoherentCrystalι S).map psi).val
    (op (L.levelSystem.obj e))).hom x
  map_add' x y := map_add _ x y
  map_smul' a x :=
    map_smul (PresheafOfModules.Hom.app ((quasiCoherentCrystalι S).map psi).val
      (op (L.levelSystem.obj e))).hom ((L.ringEquiv a).val e) x

/-- The level map of a morphism of crystals is the component at the level `e` of the induced
morphism of presheaves of modules. -/
@[simp] theorem levelSectionsMap_apply {F G : QuasiCoherentCrystal S} (psi : F ⟶ G) (e : ℕ)
    (x : L.levelSections F e) :
    L.levelSectionsMap psi e x =
      (PresheafOfModules.Hom.app ((quasiCoherentCrystalι S).map psi).val
        (op (L.levelSystem.obj e))).hom x :=
  rfl

/-- **The map of the limit modules induced by a morphism of crystals is the limit of the maps of
the levels.**  Both are the level-by-level application of the induced morphism of presheaves of
modules, so this holds by construction of
`...SmallSite.LevelScalars07JG.sectionsMap`. -/
theorem proj_sectionsInvLimitEquiv_sectionsMap {F G : QuasiCoherentCrystal S} (psi : F ⟶ G)
    (e : ℕ) (m : L.sections F) :
    invLimit.proj (L.levelSections G) (L.levelRestrict G) e
        (L.sectionsInvLimitEquiv G (L.sectionsMap psi m)) =
      L.levelSectionsMap psi e
        (invLimit.proj (L.levelSections F) (L.levelRestrict F) e (L.sectionsInvLimitEquiv F m)) :=
  rfl

variable [Fintype ι]

/-- **The field `comparison` of
`Crystalline.GlobalCrystallineSituation.SmallSite.LevelComparison07JG`, from comparison data at
the single levels.**

The module `M = lim_e Γ(T_e, ℱ)` of [Stacks, Lemma 60.17.3, Tag 07JG] *is* the limit of the
tower of level sections, by `...SmallSite.LevelScalars07JG.sectionsInvLimitEquiv`, so
`Crystalline.FirstOrderComparison.ofLevels` applies: the first-order extension `D ⊕ Ω` of
[Stacks, Tag 07J2] is free of finite rank over `D`, and base change along it commutes with the
limit over the levels.

What is consumed is a comparison datum at each level, compatible with the restrictions of the
system.  **The hypothesis beyond that is the basis `b` of `Ω`**, which
`...SmallSite.levelComparison07JGWholeSpaceOfTaylor` already carries for items (07JD) and
(07JE), together with the finiteness of its index. -/
def comparisonOfLevels (F : QuasiCoherentCrystal S)
    (c : ∀ e : ℕ, FirstOrderComparison A D g Omega d (L.levelSections F e))
    (hc : ∀ (e : ℕ) (x : L.levelSections F (e + 1)),
      LinearMap.lTensor (firstOrderExtension D Omega) (L.levelRestrict F e) (c (e + 1) x) =
        c e (L.levelRestrict F e x))
    (b : Module.Basis ι (D : Type u) Omega) :
    FirstOrderComparison A D g Omega d (L.sections F) :=
  FirstOrderComparison.ofLevels (L.sections F) (L.levelSections F) (L.levelRestrict F)
    (L.sectionsInvLimitEquiv F) c hc b

/-- **The field `comparison_naturality` of
`Crystalline.GlobalCrystallineSituation.SmallSite.LevelComparison07JG`, from the naturality of
the comparison data at the single levels.**

The map of the limit modules induced by a morphism of crystals is the limit of the maps of the
levels, by `...SmallSite.LevelScalars07JG.proj_sectionsInvLimitEquiv_sectionsMap`, so this is
`Crystalline.levelComparisonFun_naturality`. -/
theorem comparisonOfLevels_naturality {F G : QuasiCoherentCrystal S} (psi : F ⟶ G)
    (c : ∀ e : ℕ, FirstOrderComparison A D g Omega d (L.levelSections F e))
    (hc : ∀ (e : ℕ) (x : L.levelSections F (e + 1)),
      LinearMap.lTensor (firstOrderExtension D Omega) (L.levelRestrict F e) (c (e + 1) x) =
        c e (L.levelRestrict F e x))
    (c' : ∀ e : ℕ, FirstOrderComparison A D g Omega d (L.levelSections G e))
    (hc' : ∀ (e : ℕ) (x : L.levelSections G (e + 1)),
      LinearMap.lTensor (firstOrderExtension D Omega) (L.levelRestrict G e) (c' (e + 1) x) =
        c' e (L.levelRestrict G e x))
    (hnat : ∀ (e : ℕ) (x : L.levelSections F e),
      c' e (L.levelSectionsMap psi e x) =
        LinearMap.lTensor (firstOrderExtension D Omega) (L.levelSectionsMap psi e) (c e x))
    (b : Module.Basis ι (D : Type u) Omega) (m : L.sections F) :
    L.comparisonOfLevels G c' hc' b (L.sectionsMap psi m) =
      LinearMap.lTensor (firstOrderExtension D Omega) (L.sectionsMap psi)
        (L.comparisonOfLevels F c hc b m) :=
  levelComparisonFun_naturality (L.sections F) (L.sections G) (L.levelSections F)
    (L.levelRestrict F) (L.levelSections G) (L.levelRestrict G) (L.sectionsInvLimitEquiv F)
    (L.sectionsInvLimitEquiv G) (L.sectionsMap psi) (L.levelSectionsMap psi)
    (fun e m ↦ L.proj_sectionsInvLimitEquiv_sectionsMap psi e m) c hc c' hc' hnat b m

end LevelScalars07JG

/-! ### The datum of [Stacks, Tag 07JG] from level-by-level comparison data -/

variable [Fintype ι]

/-- **A term of `Crystalline.GlobalCrystallineSituation.SmallSite.LevelComparison07JG` built from
data at the single objects `T_e` of the site.**

This is `...SmallSite.levelComparison07JGOfTaylor` with its two remaining fields — `comparison`
and `comparison_naturality` — supplied by the interchange: a comparison datum at each level,
compatible with the restrictions of the system and natural in the crystal, gives the datum on the
limit module `M = lim_e Γ(T_e, ℱ)` and its naturality, by
`...SmallSite.LevelScalars07JG.comparisonOfLevels` and `...comparisonOfLevels_naturality`.

So the six fields of the record are accounted for as follows.  `isPAdicallyComplete` is item
(07JB), from the annihilation `hann`.  `hasCoordinateOperators`, `isIntegrable` and
`isTopologicallyQuasiNilpotent` are items (07JD), (07JE) and the non-vacuity of the two, from the
source's own coefficient computations over `D(1)` and `D(2)`.  `comparison` and
`comparison_naturality` are now level-by-level inputs.

**No `@[stacks]` attribute follows from this**: it is a term of a record of hypotheses, over a
system of levels about which nothing is assumed beyond the annihilation, and the level-by-level
comparison datum is still carried. -/
def levelComparison07JGOfLevelwise (L : LevelScalars07JG S D) (N : ℕ)
    (c : ∀ (F : QuasiCoherentCrystal S) (e : ℕ),
      FirstOrderComparison A D g Omega d (L.levelSections F e))
    (hc : ∀ (F : QuasiCoherentCrystal S) (e : ℕ) (x : L.levelSections F (e + 1)),
      LinearMap.lTensor (firstOrderExtension D Omega) (L.levelRestrict F e) (c F (e + 1) x) =
        c F e (L.levelRestrict F e x))
    (hnat : ∀ {F G : QuasiCoherentCrystal S} (psi : F ⟶ G) (e : ℕ) (x : L.levelSections F e),
      c G e (L.levelSectionsMap psi e x) =
        LinearMap.lTensor (firstOrderExtension D Omega) (L.levelSectionsMap psi e) (c F e x))
    (b : Module.Basis ι (D : Type u) Omega) (hdx : ∀ i, dx i = b i)
    (theta : ∀ F : QuasiCoherentCrystal S, ι → (L.sections F → L.sections F))
    (thetaPow : ∀ F : QuasiCoherentCrystal S, (ι →₀ ℕ) → (L.sections F → L.sections F))
    (hfam : ∀ F : QuasiCoherentCrystal S,
      IsThetaMonomialFamily (L.sections F) (theta F) (thetaPow F))
    (hco : ∀ F : QuasiCoherentCrystal S, IsCoordinateExpansion p (D : Type u) Omega dx
      ((L.comparisonOfLevels F (c F) (hc F) b).completedConnection p) (theta F))
    (hfin : ∀ (F : QuasiCoherentCrystal S) (m : L.sections F),
      {K : ι →₀ ℕ | thetaPow F K m ∉ pSmul p (D : Type u) (L.sections F)}.Finite)
    (hann : ∀ (F : QuasiCoherentCrystal S) (e : ℕ) (x : L.levelSections F e),
      ((p : (D : Type u)) ^ (N + e)) • x = 0) :
    LevelComparison07JG S A D g Omega d p dx L :=
  levelComparison07JGOfTaylor L N (fun F ↦ L.comparisonOfLevels F (c F) (hc F) b)
    (fun psi m ↦ L.comparisonOfLevels_naturality psi _ _ _ _ (hnat psi) b m)
    theta thetaPow hfam hco hfin hann b hdx

section WholeSpace

variable (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  [WholeSpacePresentation S hp] [IsAffine S.X] [IsAffine S.S.scheme]

section Comparison

variable {A : Type u} [CommRing A] (n : ℕ)
  {g : A →+* (wholeSpaceSystemEnvelope hp n).ring}
  {Omega : Type u} [AddCommGroup Omega]
  [Module (wholeSpaceSystemEnvelope hp n).ring Omega]
  [Module ((wholeSpaceSystemEnvelope hp n).ring)ᵐᵒᵖ Omega]
  [IsCentralScalar (wholeSpaceSystemEnvelope hp n).ring Omega]
  {d : DividedPowerDerivation A (wholeSpaceSystemEnvelope hp n).ring g Omega}
  {ι : Type uI} [Fintype ι] {dx : ι → Omega}

/-- **A term of `Crystalline.GlobalCrystallineSituation.SmallSite.LevelComparison07JG` over the
scalars of [Stacks, Proposition 60.21.1, Tag 07JN], built from data at the single levels.**

Here the annihilation of the levels is not a hypothesis: it is
`...SmallSite.pow_smul_eq_zero_wholeSpaceLevelSections`, with the shift
`N = Crystalline.uniformLevel (...affineSituation S hp)` — the exponent is `p^{N + e}` and not
`p^e`, matching `Crystalline.isPAdicallyComplete_invLimit_of_shift`.

Every level of `...SmallSite.wholeSpaceSystem` is affine, by
`...SmallSite.isAffine_wholeSpaceSystem_target`, which is why a comparison datum at the single
levels is the affine question that
`StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderIdealAffine.lean` reduces to bijectivity of
`...GlobalCrystallineSituation.extensionSectionsMap`.  **That bijectivity is not proved anywhere
in the tree and is not proved here**; what this module removes is the further step of passing a
datum at the levels through the limit.  No `@[stacks]` attribute is placed. -/
def levelComparison07JGWholeSpaceOfLevelwise
    (c : ∀ (Fr : QuasiCoherentCrystal S) (e : ℕ),
      FirstOrderComparison A (wholeSpaceSystemEnvelope hp n).ring g Omega d
        ((wholeSpaceLevelScalars hp n).levelSections Fr e))
    (hc : ∀ (Fr : QuasiCoherentCrystal S) (e : ℕ)
      (x : (wholeSpaceLevelScalars hp n).levelSections Fr (e + 1)),
      LinearMap.lTensor (firstOrderExtension (wholeSpaceSystemEnvelope hp n).ring Omega)
          ((wholeSpaceLevelScalars hp n).levelRestrict Fr e) (c Fr (e + 1) x) =
        c Fr e ((wholeSpaceLevelScalars hp n).levelRestrict Fr e x))
    (hnat : ∀ {Fr Gr : QuasiCoherentCrystal S} (psi : Fr ⟶ Gr) (e : ℕ)
      (x : (wholeSpaceLevelScalars hp n).levelSections Fr e),
      c Gr e ((wholeSpaceLevelScalars hp n).levelSectionsMap psi e x) =
        LinearMap.lTensor (firstOrderExtension (wholeSpaceSystemEnvelope hp n).ring Omega)
          ((wholeSpaceLevelScalars hp n).levelSectionsMap psi e) (c Fr e x))
    (b : Module.Basis ι ((wholeSpaceSystemEnvelope hp n).ring : Type u) Omega)
    (hdx : ∀ i, dx i = b i)
    (theta : ∀ Fr : QuasiCoherentCrystal S, ι → ((wholeSpaceLevelScalars hp n).sections Fr →
      (wholeSpaceLevelScalars hp n).sections Fr))
    (thetaPow : ∀ Fr : QuasiCoherentCrystal S, (ι →₀ ℕ) →
      ((wholeSpaceLevelScalars hp n).sections Fr → (wholeSpaceLevelScalars hp n).sections Fr))
    (hfam : ∀ Fr : QuasiCoherentCrystal S,
      IsThetaMonomialFamily ((wholeSpaceLevelScalars hp n).sections Fr) (theta Fr) (thetaPow Fr))
    (hco : ∀ Fr : QuasiCoherentCrystal S,
      IsCoordinateExpansion S.p ((wholeSpaceSystemEnvelope hp n).ring : Type u) Omega dx
        (((wholeSpaceLevelScalars hp n).comparisonOfLevels Fr (c Fr) (hc Fr)
          b).completedConnection S.p) (theta Fr))
    (hfin : ∀ (Fr : QuasiCoherentCrystal S) (m : (wholeSpaceLevelScalars hp n).sections Fr),
      {K : ι →₀ ℕ | thetaPow Fr K m ∉ pSmul S.p
        ((wholeSpaceSystemEnvelope hp n).ring : Type u)
        ((wholeSpaceLevelScalars hp n).sections Fr)}.Finite) :
    LevelComparison07JG S A (wholeSpaceSystemEnvelope hp n).ring g Omega d S.p dx
      (wholeSpaceLevelScalars hp n) :=
  levelComparison07JGOfLevelwise (wholeSpaceLevelScalars hp n)
    (_root_.Crystalline.uniformLevel (affineSituation S hp)) c hc hnat b hdx
    theta thetaPow hfam hco hfin
    fun Fr e ↦ pow_smul_eq_zero_wholeSpaceLevelSections hp n e Fr

end Comparison

end WholeSpace

end GlobalCrystallineSituation.SmallSite

end Crystalline

end

end
