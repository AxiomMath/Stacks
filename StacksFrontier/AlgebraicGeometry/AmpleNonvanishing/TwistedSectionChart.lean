module

public import StacksFrontier.AlgebraicGeometry.ModuleSectionExtension.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleTheory.Basic
public import StacksFrontier.AlgebraicGeometry.OneDimensionalLocal.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.VanishingLocal
public import StacksFrontier.AlgebraicGeometry.SectionProduct.MulSecInjective
public import StacksCore.Tactic.StacksAttribute

/-!
# A nonzero quasi-coherent module is seen by a twisted global section on an ample chart

Let `X` be a scheme carrying an ample invertible `𝒪_X`-module `L` and let `F` be a nonzero
quasi-coherent `𝒪_X`-module. This file produces an exponent `p`, a global section `σ` of
`L ^⊗ p` whose nonvanishing open `X_σ` is affine, a nonzero section `t` of `F` over `X_σ`, and a
**nonzero** global section `τ` of `F ⊗ L ^⊗ p` restricting on `X_σ` to the product
`t ⊗ σ|_{X_σ}`. In particular `Γ(X, F ⊗ L ^⊗ p) ≠ 0`.

This is the module-level run of [Stacks, Tag 0BQR]'s argument: a nonzero sheaf has a point with
nonzero stalk, ampleness puts that point in an affine chart `X_s`, a quasi-coherent module with
no sections on an affine open has no stalks there, the surjectivity half of
[Stacks, Tag 01PW] for an ample `L` turns the resulting nonzero local section into the
restriction of a twisted global section, and the whiskered clause 2 of [Stacks, Tag 01CY] —
over an open inside `X_σ` the product with `σ` kills no section of `F` — makes that twisted
global section nonzero.

## Main results

* `Stacks.AmpleNonvanishingChart.exists_point_not_isZero_stalk`: a nonzero sheaf of modules on a
  scheme has a point with nonzero stalk.
* `Stacks.AmpleNonvanishingChart.exists_section_ne_zero_of_isAffineOpen`: a quasi-coherent module
  with a nonzero stalk at a point of an affine open has a nonzero section on that open.
* `Stacks.AmpleNonvanishingChart.exists_twistedSection_restrict_eq_tensorSection`:
  **[Stacks, Tag 0BQR] for a module.** The nonzero twisted global section above, together with
  the nonzero local section it restricts to.
* `Stacks.AmpleNonvanishingChart.exists_tensorPow_globalSection_ne_zero`: the conclusion the tag
  asks for at a module, `Γ(X, F ⊗ L ^⊗ p) ≠ 0`.

The injectivity that makes `τ` nonzero is
`Stacks.SectionProduct.eq_zero_of_tensorSection_eq_zero`
(`StacksFrontier/AlgebraicGeometry/SectionProduct/MulSecInjective.lean`), which composes the two
proved halves of clause 2 of [Stacks, Tag 01CY] —
`Stacks.SectionProduct.bijective_mapFun_mulRight_of_app_bijective` and
`Stacks.SectionProduct.app_bijective_of_le_nonvanishingLocus` — across the monoidal-unit
comparison of `StacksFrontier/AlgebraicGeometry/SectionProduct/MonoidalUnitBridge.lean` and the
section-level formula of `StacksFrontier/AlgebraicGeometry/SectionProduct/MulSecFormula.lean`.

## The derived-category form

The derived-category statement of [Stacks, Tag 0BQR], in `Hom` shape — the negative tensor powers
of `L` detect the zero object of `D_QCoh(𝒪_X)` — is
`Stacks.AmpleNonvanishingChart.isZero_of_forall_hom_tensorPowModule_neg_eq_zero`
(`StacksFrontier/AlgebraicGeometry/AmpleNonvanishing/DerivedQCohDetection.lean`), whose lifting step
reruns the argument below on an epimorphism of quasi-coherent modules.

At the module level nothing is left over: the injectivity of `t ↦ t ⊗ σ|_U` on `Γ(F, U)` for `U`
inside the nonvanishing open of `σ` is proved in
`StacksFrontier/AlgebraicGeometry/SectionProduct/MulSecInjective.lean` and used below.

## References

* [Stacks Project, Tag 0BQR](https://stacks.math.columbia.edu/tag/0BQR)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MonoidalCategory
open Stacks.Ample Stacks.NonvanishingOpen
open Stacks.SectionExtension (resTop)
open Stacks.SectionTensorFormula (tensorSection)

universe u

namespace Stacks.AmpleNonvanishingChart

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

/-! ### The two local steps -/

/-- **A nonzero sheaf of modules on a scheme has a point with nonzero stalk.** The
contrapositive of `AlgebraicGeometry.isZero_of_forall_isZero_stalk`. -/
theorem exists_point_not_isZero_stalk {X : Scheme.{u}} (F : X.Modules) (hF : ¬ IsZero F) :
    ∃ x : X, ¬ IsZero (F.presheaf.stalk x) := by
  by_contra h
  exact hF (AlgebraicGeometry.isZero_of_forall_isZero_stalk F
    fun x => not_not.mp fun hx => h ⟨x, hx⟩)

/-- **A quasi-coherent module with a nonzero stalk at a point of an affine open has a nonzero
section there.** Were every section of `F` on the affine open `V` zero, the restriction of `F` to
`V` would be a zero object, hence every stalk of `F` at a point of `V` would vanish. -/
theorem exists_section_ne_zero_of_isAffineOpen {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] (V : X.Opens) (hV : IsAffineOpen V) (x : X) (hx : x ∈ V)
    (hFx : ¬ IsZero (F.presheaf.stalk x)) :
    ∃ t : Γ(F, V), t ≠ 0 := by
  have hVa : IsAffine (V : Scheme) := hV
  by_contra hno
  rw [not_exists] at hno
  have hsub : Subsingleton Γ(F, V) :=
    ⟨fun a b => by rw [not_not.mp (hno a), not_not.mp (hno b)]⟩
  have hsub' : Subsingleton
      (((Scheme.Modules.restrictFunctor V.ι).obj F).val.obj (op (⊤ : (V : Scheme).Opens))) := by
    dsimp [Scheme.Modules.restrictFunctor, SheafOfModules.pushforward,
      PresheafOfModules.pushforward, PresheafOfModules.pushforward₀,
      PresheafOfModules.pushforward₀Obj]
    change Subsingleton (F.val.obj (op (V.ι ''ᵁ (⊤ : (V : Scheme).Opens))))
    rw [Scheme.Opens.ι_image_top]
    exact hsub
  exact hFx (Stacks.AlgebraicGeometry.SchemeHigherDirectImage.isZero_stalk_of_isZero_restrict
    V F x hx (Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_of_isZero_sections_of_isAffine
      ((Scheme.Modules.restrictFunctor V.ι).obj F)
      (ModuleCat.isZero_iff_subsingleton.mpr hsub')))

/-! ### The chart step of Stacks Tag 0BQR -/

/-- **[Stacks, Tag 0BQR] for a quasi-coherent module.** For `L` an ample invertible `𝒪_X`-module
and `F` a nonzero quasi-coherent `𝒪_X`-module there are an exponent `p`, a global section `σ` of
`L ^⊗ p` with affine nonvanishing open `U = X_σ`, a **nonzero** section `t` of `F` over `U`, and a
**nonzero** global section `τ` of `F ⊗ L ^⊗ p` with `τ|_U = t ⊗ σ|_U`.

These are the five steps of the source argument run on a module instead of on a complex: the
point with nonzero stalk, the affine chart of ampleness, the nonzero section on it, the
surjectivity half of [Stacks, Tag 01PW], and — for `τ ≠ 0` — the whiskered clause 2 of
[Stacks, Tag 01CY] in the form
`Stacks.SectionProduct.eq_zero_of_tensorSection_eq_zero`: over an open inside `X_σ` the product
with `σ` kills no section of `F`, so `τ|_U = t ⊗ σ|_U` with `t ≠ 0` forces `τ ≠ 0`. -/
@[stacks 0BQR "run at a quasi-coherent module rather than at an object of D_QCoh(O_X) in a \
degree: Gamma(X, F tensor L^p) is nonzero, witnessed by an explicit tau. The derived-category \
form is a separate assertion; see the module docstring"]
theorem exists_twistedSection_restrict_eq_tensorSection {X : Scheme.{u}} (L : X.Modules)
    [IsInvertibleModule X L] (hL : IsAmple X L) (F : X.Modules) [F.IsQuasicoherent]
    (hF : ¬ IsZero F) :
    ∃ (p : ℕ) (σ : Γ(tensorPowModule X L (p : ℤ), ⊤)) (U : X.Opens)
      (τ : Γ(F ⊗ tensorPowModule X L (p : ℤ), ⊤)) (t : Γ(F, U)),
      U = Stacks.AmpleTheory.powNonvanishingOpen X L p σ ∧ IsAffineOpen U ∧ t ≠ 0 ∧ τ ≠ 0 ∧
        resTop U τ = tensorSection F (tensorPowModule X L (p : ℤ)) t (resTop U σ) := by
  obtain ⟨x, hx⟩ := exists_point_not_isZero_stalk F hF
  obtain ⟨n, hn, s, haff, hxs⟩ :=
    Stacks.AmpleTheory.IsAmple.exists_affine_nonvanishingOpen X L hL x
  obtain ⟨t, ht⟩ := exists_section_ne_zero_of_isAffineOpen F _ haff x hxs hx
  obtain ⟨p, σ, τ, hopen, heq⟩ :=
    Stacks.ModuleSectionExtension.exists_tensorPow_tensorSection_of_isAmple L hL F hn s t
  refine ⟨p, σ, Stacks.AmpleTheory.powNonvanishingOpen X L n s, τ, t, hopen, haff, ht, ?_, heq⟩
  intro hτ
  refine ht (Stacks.SectionProduct.eq_zero_of_tensorSection_eq_zero F
    (tensorPowModule X L (p : ℤ)) σ (fun y hy => ?_) ?_)
  · rw [hopen] at hy
    exact hy
  · rw [← heq, hτ]
    simp

/-- **A nonzero twisted global section, on the injectivity of multiplication by a nonvanishing
section.** With the hypothesis `hinj` — whiskered clause 2 of [Stacks, Tag 01CY]: over an open
inside the nonvanishing open of `σ`, the product with `σ` kills no section of `F` — the twisted
global section of
`Stacks.AmpleNonvanishingChart.exists_twistedSection_restrict_eq_tensorSection` is itself
nonzero, which is the conclusion [Stacks, Tag 0BQR] asks for at a module.

The hypothesis is quantified over all data rather than at the `p` the previous theorem produces,
because that `p` is not available before the theorem is applied. -/
theorem exists_tensorPow_globalSection_ne_zero {X : Scheme.{u}} (L : X.Modules)
    [IsInvertibleModule X L] (hL : IsAmple X L) (F : X.Modules) [F.IsQuasicoherent]
    (hF : ¬ IsZero F)
    (hinj : ∀ (p : ℕ) (σ : Γ(tensorPowModule X L (p : ℤ), ⊤)) (U : X.Opens),
      U = Stacks.AmpleTheory.powNonvanishingOpen X L p σ → ∀ t : Γ(F, U),
        tensorSection F (tensorPowModule X L (p : ℤ)) t (resTop U σ) = 0 → t = 0) :
    ∃ (p : ℕ) (τ : Γ(F ⊗ tensorPowModule X L (p : ℤ), ⊤)), τ ≠ 0 := by
  obtain ⟨p, σ, U, τ, t, hU, -, ht, -, heq⟩ :=
    exists_twistedSection_restrict_eq_tensorSection L hL F hF
  refine ⟨p, τ, fun hτ => ht (hinj p σ U hU t ?_)⟩
  rw [← heq, hτ]
  simp

end Stacks.AmpleNonvanishingChart

end
