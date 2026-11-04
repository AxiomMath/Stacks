module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupTwistedModuleSituation
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.DivisibleMaps
import StacksCore.Tactic.StacksAttribute

/-!
# The evaluation dictionary of Remark 0GAB on the blowup

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `p : X ⟶ Spec(A)` the blowup of `Spec(A)` in
`I`. This file builds, on that blowup, the first and the third of the three fields that
`Stacks.LocalCohomology.UniformityIII.DualSituation` adds to
`Stacks.LocalCohomology.UniformityIII.TwistedModuleSituation`: the evaluation dictionary `ev` of
[Stacks, Remark 0GAB] and its compatibility `ev_secM` with the canonical sections.

## The construction

For `z ∈ M` the source forms the evaluation `e_z : M^∨ ⟶ A ⧸ Iⁿ`, `λ ↦ λ(z)`, pulls it back and
twists it, and evaluates a section of `𝒪_X(q) ⊗ p^*(M^∨)~` against it. So `ev` is the composite
of three maps that are already in hand:

* `Hⁱ(X, 𝒪_X(q) ⊗ p^*(-))` applied to `e_z`, landing in
  `H⁰(X, 𝒪_X(q) ⊗ p^*((A ⧸ Iⁿ)~))`;
* `Stacks.LocalCohomology.UniformityIII.blowupHmodTwistedPullbackQuotientEquiv`, which identifies
  that with `H⁰(X, 𝒪_{Yₙ}(q))`, the field `Hdiv` of the Situation;
* the inverse of the field `cdiv`, which is bijective for `n ≥ 1` and `q ≥ q₀` by [Stacks,
  Tag 0GA7] (2) — `Stacks.LocalCohomology.UniformityIII.Situation.bijective_cdiv`. That
  restriction to `q ≥ q(S)` is exactly what makes the target `I^q/I^{q+n}` rather than
  `H⁰(X, 𝒪_{Yₙ}(q))`, as the field `ev` of `DualSituation` demands.

Nothing geometric is added. `e_z` is the mirror image of
`Stacks.LocalCohomology.UniformityIII.resSmulHom`, the map `A ⧸ Iⁿ ⟶ M`, `x ↦ x·m`, out of which
`Stacks.LocalCohomology.UniformityIII.twistedPullbackSecM` is built, and the two are composed in
the proof of `blowupEv_twistedPullbackSecM` below. As there, what has to be checked is that the
assignment is *bilinear*, and `A`-linearity rather than additivity of `N ↦ Hⁱ(X, 𝒪_X(q) ⊗ p^*Ñ)` —
`Stacks.LocalCohomology.UniformityIII.linear_twistedPullbackCohomologyFunctor` — is what the
scalars need.

At `n = 0` the field `cdiv` is the zero map and is not bijective, so the inverse is taken only
for `n ≥ 1`; at `n = 0` the target `I^q/I^{q+0}` is the zero module
(`subsingleton_powQuot_zero`), so the zero map serves and
`Stacks.LocalCohomology.UniformityIII.cdivInv_cdiv` holds for every `n`. This is the same
degenerate case `twistedPullbackSecM` records.

## `ev_secM` is a statement about scalars

`ev_secM` asks that on the canonical section attached to `x ⊗ λ` the dictionary be the evaluation
pairing `dualHom`. Unfolding both canonical maps, the composite
`A ⧸ Iⁿ ⟶ M^∨ ⟶ A ⧸ Iⁿ`, `r ↦ (r·λ)(z)`, is multiplication by `λ(z)`, i.e. `a · 𝟙` for any lift
`a ∈ A` of `λ(z)` — that is `resSmulHom_comp_resEvalHom`. An `A`-linear functor carries `a · 𝟙`
to `a · 𝟙`, so the section is multiplied by `a` and `cdiv` is `A`-linear; `dualHom` of `x` at `λ`
evaluated on `z` is `a · x` by `powQuotScalar_apply_mk`. So the field holds with no geometric
input beyond the linearity already proved.

## What is still missing for a `DualSituation`, precisely

The remaining field is `ev_Htr`, the naturality of the dictionary in the twist. Half of it is
here: `blowupHtr_naturality` says the twisting-down maps on cohomology are natural in the module
argument, which is all that is needed to move `e_z` past them. What the other half needs is
recorded as the hypothesis of `blowupEv_blowupHtr_of_cdiv_twistDown`, namely that the canonical
map `I^q/I^{q+n} ⟶ H⁰(X, 𝒪_X(q) ⊗ p^*((A ⧸ Iⁿ)~))` intertwines the algebraic twisting-down map
`powQuotLe` with the geometric one `blowupHtr`. That theorem shows the hypothesis is not merely
sufficient but equivalent to `ev_Htr` holding at the construction below, so it is the exact
remaining gap.

That compatibility is not in the library. It reduces in turn to three steps, none of them
present: a twisting-down map `𝒪_{Yₙ}(q) ⟶ 𝒪_{Yₙ}(q')` (which is
`Stacks.Blowup.twistDownMap` whiskered into `thickeningSheaf I n`); the naturality of
`twistedPullbackQuotientIsoThickeningTwist` against it and
`Stacks.Blowup.twistDownFactorMap`; and finally
`Γ(twistDownMap I q q')(ambientSections I q y) = ambientSections I q' y`, of which only the
one-step case `q = q' + 1` is proved, as
`Stacks.LocalCohomology.UniformityIII.app_top_ambientTwistMap_ambientSections`.

## Main definitions

* `Stacks.LocalCohomology.UniformityIII.resEvalHom`: `M^∨ ⟶ A ⧸ Iⁿ`, `λ ↦ λ(z)`, over `A`.
* `Stacks.LocalCohomology.UniformityIII.cdivInv`: the inverse of the field `cdiv` for `q ≥ q₀`.
* `Stacks.LocalCohomology.UniformityIII.blowupEv`: **the field `ev`** of
  `Stacks.LocalCohomology.UniformityIII.DualSituation`, at the blowup's `ModuleSituation`.

## Main results

* `Stacks.LocalCohomology.UniformityIII.blowupEv_twistedPullbackSecM`: **the field `ev_secM`** on
  the blowup.
* `Stacks.LocalCohomology.UniformityIII.blowupHtr_naturality`: the twisting-down maps on the
  cohomology of the twisted pullbacks are natural in the module.
* `Stacks.LocalCohomology.UniformityIII.blowupEv_blowupHtr_of_cdiv_twistDown`: the field `ev_Htr`
  on the blowup, from the compatibility of `cdiv` with the two twisting-down maps, which is the
  one remaining gap.

## References

* [Stacks Project, Remark 0GAB](https://stacks.math.columbia.edu/tag/0GAB)
* [Stacks Project, Tag 0GAA](https://stacks.math.columbia.edu/tag/0GAA)
* [Stacks Project, Tag 0GA7](https://stacks.math.columbia.edu/tag/0GA7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Stacks.LocalCohomology.UniformityIII

attribute [local instance] modulesMonoidal modulesMonoidal' modulesEnoughInjectives
attribute [local instance] sheafSectionsPreservesFiniteLimits secFPreservesFiniteLimits
attribute [local instance] HasDerivedCategory.standard
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {A : Type u} [CommRing A] (I : Ideal A)

/-! ### An element of `M` read as a map `M^∨ ⟶ A ⧸ Iⁿ` -/

section Eval

variable (n : ℕ) (M : ModuleCat.{u} (A ⧸ I ^ n))

/-- **An element `z` of an `A ⧸ Iⁿ`-module read as the map `M^∨ ⟶ A ⧸ Iⁿ`, `λ ↦ λ(z)`**, over
`A`.

This is the left-hand factor of the evaluation dictionary of [Stacks, Remark 0GAB]: pushing it
through `𝒪_X(q) ⊗ p^*(-)` turns a section of `𝒪_X(q) ⊗ p^*(M^∨)~` into a section of
`𝒪_{Yₙ}(q)`. It is `A`-linear because it is `A ⧸ Iⁿ`-linear, the `A`-action on both sides being
the one along `A → A ⧸ Iⁿ`. -/
def resEvalLin (z : resModule I n M) :
    resModule I n (ModuleCat.of (A ⧸ I ^ n) (Module.Dual (A ⧸ I ^ n) M)) →ₗ[A] (A ⧸ I ^ n) where
  toFun lam := asDual I n lam z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `resEvalLin` as a morphism of `A`-modules. -/
def resEvalHom (z : resModule I n M) :
    resModule I n (ModuleCat.of (A ⧸ I ^ n) (Module.Dual (A ⧸ I ^ n) M)) ⟶
      ModuleCat.of A (A ⧸ I ^ n) :=
  ConcreteCategory.ofHom (resEvalLin I n M z)

/-- The map `resEvalHom` on an element: it is evaluation at `z`. -/
theorem resEvalHom_hom_apply (z : resModule I n M)
    (lam : resModule I n (ModuleCat.of (A ⧸ I ^ n) (Module.Dual (A ⧸ I ^ n) M))) :
    (resEvalHom I n M z).hom lam = asDual I n lam z := rfl

/-- `λ ↦ λ(z)` is additive in `z`. -/
theorem resEvalHom_add (z w : resModule I n M) :
    resEvalHom I n M (z + w) = resEvalHom I n M z + resEvalHom I n M w :=
  ModuleCat.hom_ext (LinearMap.ext fun lam => map_add (asDual I n lam) _ _)

/-- `λ ↦ λ(z)` is `A`-linear in `z`: the scalar passes through the functional because the
`A`-action on `M` is the one along `A → A ⧸ Iⁿ`. -/
theorem resEvalHom_smul (a : A) (z : resModule I n M) :
    resEvalHom I n M (a • z) = a • resEvalHom I n M z :=
  ModuleCat.hom_ext (LinearMap.ext fun lam =>
    map_smul (asDual I n lam) (Ideal.Quotient.mk (I ^ n) a) _)

/-- **Multiplying by `λ` and then evaluating at `z` is multiplication by `λ(z)`.** The composite
`A ⧸ Iⁿ ⟶ M^∨ ⟶ A ⧸ Iⁿ` is `r ↦ (r·λ)(z) = r·λ(z)`, which is `a · 𝟙` for any lift `a ∈ A` of
`λ(z)`.

This is the one computation behind `blowupEv_twistedPullbackSecM`: an `A`-linear functor carries
`a · 𝟙` to `a · 𝟙`, so after pushing the composite through `Hⁱ(X, 𝒪_X(q) ⊗ p^*(-))` the section is
simply multiplied by `a`. -/
theorem resSmulHom_comp_resEvalHom
    (lam : resModule I n (ModuleCat.of (A ⧸ I ^ n) (Module.Dual (A ⧸ I ^ n) M)))
    (z : resModule I n M) {a : A}
    (ha : Ideal.Quotient.mk (I ^ n) a = asDual I n lam z) :
    resSmulHom I n (ModuleCat.of (A ⧸ I ^ n) (Module.Dual (A ⧸ I ^ n) M)) lam ≫
        resEvalHom I n M z =
      a • (𝟙 (ModuleCat.of A (A ⧸ I ^ n))) :=
  ModuleCat.hom_ext (LinearMap.ext fun r => by
    have hl : (resSmulHom I n (ModuleCat.of (A ⧸ I ^ n) (Module.Dual (A ⧸ I ^ n) M)) lam ≫
          resEvalHom I n M z).hom r = r * asDual I n lam z := rfl
    have hr : (a • (𝟙 (ModuleCat.of A (A ⧸ I ^ n)))).hom r =
        Ideal.Quotient.mk (I ^ n) a * r := rfl
    exact hl.trans
      (((congrArg (fun t => r * t) ha.symm).trans (mul_comm r _)).trans hr.symm))

end Eval

/-! ### The inverse of the canonical map `I^q/I^{q+n} ⟶ H⁰(X, 𝒪_{Yₙ}(q))` -/

section CdivInv

variable [IsNoetherianRing A]

/-- **The inverse of the canonical map `I^q/I^{q+n} ⟶ H⁰(X, 𝒪_{Yₙ}(q))` for `q ≥ q₀`**, which is
bijective by [Stacks, Tag 0GA7] (2) as soon as `n ≥ 1`
(`Stacks.LocalCohomology.UniformityIII.Situation.bijective_cdiv`).

At `n = 0` the canonical map is zero and not bijective; there the target `I^q/I^{q+0}` of the
inverse vanishes, so the zero map is taken and `cdivInv_cdiv` still holds. -/
def cdivInv (q₀ : ℕ) (h : IsBaseThreshold I q₀) (n : ℕ) {q : ℕ} (hq : q₀ ≤ q) :
    (blowupSituationOf I q₀ h).Hdiv n 0 q →ₗ[A] powQuot I q n :=
  if hn : 1 ≤ n then
    (LinearEquiv.ofBijective ((blowupSituationOf I q₀ h).cdiv n q)
      ((blowupSituationOf I q₀ h).bijective_cdiv hn hq)).symm.toLinearMap
  else 0

/-- **`cdivInv` undoes `cdiv`**, for every `n` and every `q ≥ q₀`: for `n ≥ 1` because `cdiv` is
bijective, and for `n = 0` because the common source vanishes. -/
theorem cdivInv_cdiv (q₀ : ℕ) (h : IsBaseThreshold I q₀) (n : ℕ) {q : ℕ} (hq : q₀ ≤ q)
    (x : powQuot I q n) :
    cdivInv I q₀ h n hq ((blowupSituationOf I q₀ h).cdiv n q x) = x := by
  rw [cdivInv]
  split
  · exact (LinearEquiv.ofBijective ((blowupSituationOf I q₀ h).cdiv n q)
      ((blowupSituationOf I q₀ h).bijective_cdiv ‹1 ≤ n› hq)).symm_apply_apply x
  · obtain rfl : n = 0 := by lia
    exact @Subsingleton.elim _ (subsingleton_powQuot_zero I q) _ _

/-- **`cdiv` undoes `cdivInv`**, for every `n` and every `q ≥ q₀`: for `n ≥ 1` because `cdiv` is
bijective, and for `n = 0` because the common target `H⁰(X, 𝒪_{Y₀}(q))` vanishes. -/
theorem cdiv_cdivInv (q₀ : ℕ) (h : IsBaseThreshold I q₀) (n : ℕ) {q : ℕ} (hq : q₀ ≤ q)
    (y : (blowupSituationOf I q₀ h).Hdiv n 0 q) :
    (blowupSituationOf I q₀ h).cdiv n q (cdivInv I q₀ h n hq y) = y := by
  obtain rfl | hn := Nat.eq_zero_or_pos n
  · exact @Subsingleton.elim _ (subsingleton_blowupHmod_thickeningTwist_zero I 0 q) _ _
  · obtain ⟨x, rfl⟩ := ((blowupSituationOf I q₀ h).bijective_cdiv hn hq).2 y
    rw [cdivInv_cdiv]

end CdivInv

/-! ### The field `ev` -/

section Ev

variable [IsNoetherianRing A]

/-- **`z ↦ Hⁱ(X, 𝒪_X(q) ⊗ p^*(λ ↦ λ(z)))` as an `A`-linear map**, the first factor of the
evaluation dictionary of [Stacks, Remark 0GAB].

This is the mirror image of `Stacks.LocalCohomology.UniformityIII.blowupSecEval`: additivity in
`z` is `resEvalHom_add` with additivity of the functor, and `A`-linearity in `z` is
`resEvalHom_smul` with `linear_twistedPullbackCohomologyFunctor`. -/
def blowupEvPush (n : ℕ) (M : ModuleCat.{u} (A ⧸ I ^ n)) (q : ℤ) :
    resModule I n M →ₗ[A]
      (blowupHmodTwistedPullback I
          (resModule I n (ModuleCat.of (A ⧸ I ^ n) (Module.Dual (A ⧸ I ^ n) M))) 0 q →ₗ[A]
        blowupHmodTwistedPullback I (ModuleCat.of A (A ⧸ I ^ n)) 0 q) where
  toFun z := ((twistedPullbackCohomologyFunctor I 0 q).map (resEvalHom I n M z)).hom
  map_add' z w := by
    rw [resEvalHom_add, CategoryTheory.Functor.map_add]
    rfl
  map_smul' a z := by
    let := linear_twistedPullbackCohomologyFunctor I 0 q
    rw [resEvalHom_smul, Functor.Linear.map_smul]
    rfl

/-- The evaluation dictionary with its two arguments in the order that makes it `A`-bilinear in
`z` and in the section; `blowupEv` is this map flipped. -/
def blowupEvHom (q₀ : ℕ) (h : IsBaseThreshold I q₀) (n : ℕ) (M : ModuleCat.{u} (A ⧸ I ^ n))
    {q : ℕ} (hq : q₀ ≤ q) :
    resModule I n M →ₗ[A]
      (blowupHmodTwistedPullback I
          (resModule I n (ModuleCat.of (A ⧸ I ^ n) (Module.Dual (A ⧸ I ^ n) M))) 0 (q : ℤ) →ₗ[A]
        powQuot I q n) where
  toFun z := (cdivInv I q₀ h n hq).comp
    ((blowupHmodTwistedPullbackQuotientEquiv I n 0 q).toLinearMap.comp
      (blowupEvPush I n M (q : ℤ) z))
  map_add' z w := by
    refine LinearMap.ext fun y => ?_
    have h1 : blowupEvPush I n M (q : ℤ) (z + w) y =
        blowupEvPush I n M (q : ℤ) z y + blowupEvPush I n M (q : ℤ) w y :=
      LinearMap.congr_fun (map_add (blowupEvPush I n M (q : ℤ)) z w) y
    exact (congrArg (fun t => cdivInv I q₀ h n hq
        ((blowupHmodTwistedPullbackQuotientEquiv I n 0 q) t)) h1).trans
      ((congrArg (cdivInv I q₀ h n hq)
        (map_add (blowupHmodTwistedPullbackQuotientEquiv I n 0 q) _ _)).trans
        (map_add (cdivInv I q₀ h n hq) _ _))
  map_smul' a z := by
    refine LinearMap.ext fun y => ?_
    have h1 : blowupEvPush I n M (q : ℤ) (a • z) y =
        a • blowupEvPush I n M (q : ℤ) z y :=
      LinearMap.congr_fun (map_smul (blowupEvPush I n M (q : ℤ)) a z) y
    exact (congrArg (fun t => cdivInv I q₀ h n hq
        ((blowupHmodTwistedPullbackQuotientEquiv I n 0 q) t)) h1).trans
      ((congrArg (cdivInv I q₀ h n hq)
        (map_smul (blowupHmodTwistedPullbackQuotientEquiv I n 0 q) a _)).trans
        (map_smul (cdivInv I q₀ h n hq) a _))

/-- **The field `ev` of `Stacks.LocalCohomology.UniformityIII.DualSituation`, on the blowup**:
the evaluation dictionary of [Stacks, Remark 0GAB],

`H⁰(X, 𝒪_X(q) ⊗ p^*(M^∨)~) ⟶ Hom_A(M, I^q/I^{q+n})`,

defined for `q ≥ q₀`. On a section `σ'` and an element `z` of `M` it is the section evaluated
against `λ ↦ λ(z)`, read back into `I^q/I^{q+n}` through [Stacks, Tag 0GA7] (2). -/
def blowupEv (q₀ : ℕ) (h : IsBaseThreshold I q₀) (n c : ℕ) (hcn : c ≤ n) (M : ANCModule I n c)
    (q : ℕ) (hq : q₀ ≤ q) :
    (blowupModuleSituationOf I q₀ h n c hcn).H M.dual 0 (q : ℤ) →ₗ[A]
      (resModule I n M.1 →ₗ[A] powQuot I q n) :=
  (blowupEvHom I q₀ h n M.1 hq).flip

/-- **`blowupEv` on an element**: the definition unfolded, which is what
`blowupEv_twistedPullbackSecM` is proved from. -/
theorem blowupEv_apply (q₀ : ℕ) (h : IsBaseThreshold I q₀) (n c : ℕ) (hcn : c ≤ n)
    (M : ANCModule I n c) (q : ℕ) (hq : q₀ ≤ q)
    (y : (blowupModuleSituationOf I q₀ h n c hcn).H M.dual 0 (q : ℤ))
    (z : resModule I n M.1) :
    blowupEv I q₀ h n c hcn M q hq y z =
      cdivInv I q₀ h n hq ((blowupHmodTwistedPullbackQuotientEquiv I n 0 q)
        ((twistedPullbackCohomologyFunctor I 0 (q : ℤ)).map (resEvalHom I n M.1 z) y)) := rfl

end Ev

/-! ### The field `ev_secM` -/

section EvSecM

variable [IsNoetherianRing A]

/-- **The field `ev_secM` of `Stacks.LocalCohomology.UniformityIII.DualSituation`, on the
blowup**: on the canonical section attached to `x ⊗ λ` the evaluation dictionary is the
evaluation pairing, `z ↦ λ(z)·x`.

Unfolding `twistedPullbackSecM` and `blowupEv`, the composite that is pushed through
`H⁰(X, 𝒪_X(q) ⊗ p^*(-))` is `A ⧸ Iⁿ ⟶ M^∨ ⟶ A ⧸ Iⁿ`, `r ↦ (r·λ)(z)`, which is `a · 𝟙` for a
lift `a ∈ A` of `λ(z)` by `resSmulHom_comp_resEvalHom`. An `A`-linear functor carries that to
`a · 𝟙`, so the section is multiplied by `a`; `cdiv` is `A`-linear and `cdivInv` undoes it, and
`powQuotScalar_apply_mk` identifies `a · x` with the value of `dualHom`. -/
theorem blowupEv_twistedPullbackSecM (q₀ : ℕ) (h : IsBaseThreshold I q₀) (n c : ℕ) (hcn : c ≤ n)
    (M : ANCModule I n c) (q : ℕ) (hq : q₀ ≤ q) (x : powQuot I q n)
    (lam : resModule I n (M.dual).1) :
    blowupEv I q₀ h n c hcn M q hq
        (twistedPullbackSecM I q₀ h n c hcn M.dual q (x ⊗ₜ[A] lam)) =
      dualHom I n q (asDual I n lam) x := by
  refine LinearMap.ext fun z => ?_
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (asDual I n lam z)
  let := linear_twistedPullbackCohomologyFunctor I 0 (q : ℤ)
  have hmor : (twistedPullbackCohomologyFunctor I 0 (q : ℤ)).map
        (resSmulHom I n (M.dual).1 lam) ≫
      (twistedPullbackCohomologyFunctor I 0 (q : ℤ)).map (resEvalHom I n M.1 z) =
        a • (𝟙 ((twistedPullbackCohomologyFunctor I 0 (q : ℤ)).obj
          (ModuleCat.of A (A ⧸ I ^ n)))) := by
    refine (Functor.map_comp _ _ _).symm.trans ((congrArg _
      (resSmulHom_comp_resEvalHom I n M.1 lam z ha)).trans ?_)
    rw [Functor.Linear.map_smul, CategoryTheory.Functor.map_id]
  calc blowupEv I q₀ h n c hcn M q hq
          (twistedPullbackSecM I q₀ h n c hcn M.dual q (x ⊗ₜ[A] lam)) z
      = cdivInv I q₀ h n hq ((blowupHmodTwistedPullbackQuotientEquiv I n 0 q)
          ((twistedPullbackCohomologyFunctor I 0 (q : ℤ)).map (resEvalHom I n M.1 z)
            ((twistedPullbackCohomologyFunctor I 0 (q : ℤ)).map
              (resSmulHom I n (M.dual).1 lam)
              ((blowupHmodTwistedPullbackQuotientEquiv I n 0 q).symm
                ((blowupSituationOf I q₀ h).cdiv n q x))))) := rfl
    _ = cdivInv I q₀ h n hq ((blowupHmodTwistedPullbackQuotientEquiv I n 0 q)
          (a • ((blowupHmodTwistedPullbackQuotientEquiv I n 0 q).symm
            ((blowupSituationOf I q₀ h).cdiv n q x)))) :=
        congrArg (fun w => cdivInv I q₀ h n hq
          ((blowupHmodTwistedPullbackQuotientEquiv I n 0 q) w))
          (ConcreteCategory.congr_hom hmor ((blowupHmodTwistedPullbackQuotientEquiv I n 0 q).symm
            ((blowupSituationOf I q₀ h).cdiv n q x)))
    _ = a • x :=
        (congrArg (cdivInv I q₀ h n hq)
          (((map_smul (blowupHmodTwistedPullbackQuotientEquiv I n 0 q) a _).trans
              (congrArg (fun t => a • t)
                ((blowupHmodTwistedPullbackQuotientEquiv I n 0 q).apply_symm_apply _))).trans
            (map_smul ((blowupSituationOf I q₀ h).cdiv n q) a x).symm)).trans
          (cdivInv_cdiv I q₀ h n hq (a • x))
    _ = dualHom I n q (asDual I n lam) x z :=
        (((powQuotScalar_apply_mk I n q x a).symm.trans
          (congrArg (powQuotScalar I n q x) ha)).trans
          (dualHom_apply I n q (asDual I n lam) x z).symm)

end EvSecM

/-! ### What `ev_Htr` reduces to -/

section EvHtr

/-- **The twisting-down maps on the cohomology of the twisted pullbacks are natural in the
module.**

`Stacks.LocalCohomology.UniformityIII.blowupHtr` is `Hⁱ(X, -)` applied to a component of the
natural transformation `Stacks.LocalCohomology.UniformityIII.twistedPullbackTwistDown`, so this
is that transformation's naturality square pushed through the derived functor. It is the half of
`ev_Htr` that moves `λ ↦ λ(z)` past the twisting-down maps. -/
theorem blowupHtr_naturality {N N' : ModuleCat.{u} A} (φ : N ⟶ N') (i : ℕ) (q q' : ℤ)
    (hq : q' ≤ q) :
    (twistedPullbackCohomologyFunctor I i q).map φ ≫ blowupHtr I N' i q q' hq =
      blowupHtr I N i q q' hq ≫ (twistedPullbackCohomologyFunctor I i q').map φ :=
  (((blowupΓmod I).rightDerived i).map_comp ((twistedPullbackFunctor I q).map φ)
        ((twistedPullbackTwistDown I q q' hq).app N')).symm.trans
    ((congrArg (fun ψ => ((blowupΓmod I).rightDerived i).map ψ)
        ((twistedPullbackTwistDown I q q' hq).naturality φ)).trans
      (((blowupΓmod I).rightDerived i).map_comp ((twistedPullbackTwistDown I q q' hq).app N)
        ((twistedPullbackFunctor I q').map φ)))

variable [IsNoetherianRing A]

/-- **The field `ev_Htr` of `Stacks.LocalCohomology.UniformityIII.DualSituation` on the blowup,
from the one compatibility the library does not have.**

The hypothesis `hcdiv` says that the canonical map `I^q/I^{q+n} ⟶ H⁰(X, 𝒪_X(q) ⊗ p^*((A ⧸ Iⁿ)~))`
intertwines the algebraic twisting-down map `powQuotLe` with the geometric one `blowupHtr`. Given
it, `ev_Htr` is `blowupHtr_naturality` — which moves `λ ↦ λ(z)` past the twisting-down map — and
then `hcdiv` transported across the bijection of [Stacks, Tag 0GA7] (2).

The conclusion is stated on elements and against `blowupHtr` rather than against the field
`Htr` of `blowupTwistedModuleSituationOf`; the two are the same map, since that field *is*
`blowupHtr` at `resModule I n M.1`. So this is `ev_Htr` pointwise, and `hcdiv` is exactly what
is still owed. The module docstring records the three steps it decomposes into. -/
theorem blowupEv_blowupHtr_of_cdiv_twistDown (q₀ : ℕ) (h : IsBaseThreshold I q₀) (n c : ℕ)
    (hcn : c ≤ n)
    (hcdiv : ∀ (r r' : ℕ) (_hr : q₀ ≤ r) (hr' : q₀ ≤ r') (hrr : r' ≤ r)
        (hrr' : (r' : ℤ) ≤ (r : ℤ)) (u : powQuot I r n),
      cdivInv I q₀ h n hr'
          ((blowupHmodTwistedPullbackQuotientEquiv I n 0 r')
            (blowupHtr I (ModuleCat.of A (A ⧸ I ^ n)) 0 (r : ℤ) (r' : ℤ) hrr'
              ((blowupHmodTwistedPullbackQuotientEquiv I n 0 r).symm
                ((blowupSituationOf I q₀ h).cdiv n r u)))) =
        powQuotLe I hrr u)
    (M : ANCModule I n c) (q q' : ℕ) (hq : q₀ ≤ q) (hq' : q₀ ≤ q') (hle : q' ≤ q)
    (hle' : (q' : ℤ) ≤ (q : ℤ))
    (y : (blowupModuleSituationOf I q₀ h n c hcn).H M.dual 0 (q : ℤ))
    (z : resModule I n M.1) :
    blowupEv I q₀ h n c hcn M q' hq'
        (blowupHtr I (resModule I n (M.dual).1) 0 (q : ℤ) (q' : ℤ) hle' y) z =
      powQuotLe I hle (blowupEv I q₀ h n c hcn M q hq y z) := by
  have hnat : blowupHtr I (ModuleCat.of A (A ⧸ I ^ n)) 0 (q : ℤ) (q' : ℤ) hle'
        ((twistedPullbackCohomologyFunctor I 0 (q : ℤ)).map (resEvalHom I n M.1 z) y) =
      (twistedPullbackCohomologyFunctor I 0 (q' : ℤ)).map (resEvalHom I n M.1 z)
        (blowupHtr I (resModule I n (M.dual).1) 0 (q : ℤ) (q' : ℤ) hle' y) :=
    ConcreteCategory.congr_hom
      (blowupHtr_naturality I (resEvalHom I n M.1 z) 0 (q : ℤ) (q' : ℤ) hle') y
  have hinner : (blowupHmodTwistedPullbackQuotientEquiv I n 0 q).symm
        ((blowupSituationOf I q₀ h).cdiv n q
          (cdivInv I q₀ h n hq ((blowupHmodTwistedPullbackQuotientEquiv I n 0 q)
            ((twistedPullbackCohomologyFunctor I 0 (q : ℤ)).map (resEvalHom I n M.1 z) y)))) =
      (twistedPullbackCohomologyFunctor I 0 (q : ℤ)).map (resEvalHom I n M.1 z) y :=
    (congrArg (blowupHmodTwistedPullbackQuotientEquiv I n 0 q).symm
        (cdiv_cdivInv I q₀ h n hq _)).trans
      ((blowupHmodTwistedPullbackQuotientEquiv I n 0 q).symm_apply_apply _)
  calc blowupEv I q₀ h n c hcn M q' hq'
          (blowupHtr I (resModule I n (M.dual).1) 0 (q : ℤ) (q' : ℤ) hle' y) z
      = cdivInv I q₀ h n hq' ((blowupHmodTwistedPullbackQuotientEquiv I n 0 q')
          (blowupHtr I (ModuleCat.of A (A ⧸ I ^ n)) 0 (q : ℤ) (q' : ℤ) hle'
            ((twistedPullbackCohomologyFunctor I 0 (q : ℤ)).map (resEvalHom I n M.1 z) y))) :=
        congrArg (fun w => cdivInv I q₀ h n hq'
          ((blowupHmodTwistedPullbackQuotientEquiv I n 0 q') w)) hnat.symm
    _ = cdivInv I q₀ h n hq' ((blowupHmodTwistedPullbackQuotientEquiv I n 0 q')
          (blowupHtr I (ModuleCat.of A (A ⧸ I ^ n)) 0 (q : ℤ) (q' : ℤ) hle'
            ((blowupHmodTwistedPullbackQuotientEquiv I n 0 q).symm
              ((blowupSituationOf I q₀ h).cdiv n q
                (cdivInv I q₀ h n hq ((blowupHmodTwistedPullbackQuotientEquiv I n 0 q)
                  ((twistedPullbackCohomologyFunctor I 0 (q : ℤ)).map
                    (resEvalHom I n M.1 z) y))))))) :=
        congrArg (fun w => cdivInv I q₀ h n hq'
          ((blowupHmodTwistedPullbackQuotientEquiv I n 0 q')
            (blowupHtr I (ModuleCat.of A (A ⧸ I ^ n)) 0 (q : ℤ) (q' : ℤ) hle' w)))
          hinner.symm
    _ = powQuotLe I hle (cdivInv I q₀ h n hq
          ((blowupHmodTwistedPullbackQuotientEquiv I n 0 q)
            ((twistedPullbackCohomologyFunctor I 0 (q : ℤ)).map (resEvalHom I n M.1 z) y))) :=
        hcdiv q q' hq hq' hle hle' _
    _ = powQuotLe I hle (blowupEv I q₀ h n c hcn M q hq y z) := rfl

end EvHtr

end Stacks.LocalCohomology.UniformityIII

end
