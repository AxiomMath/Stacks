module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartPullbackCotensorator
public import StacksFrontier.AlgebraicGeometry.TensorPowerDivision.Basic

/-!
# Dividing a section of a tensor power across degrees commutes with pullback

Let `j : Y' ⟶ Y` be a morphism of schemes, `L` an invertible `𝒪_Y`-module, `t` a global section of
`L ^⊗ k` not vanishing on an open `V ⊆ Y`, and `x` a global section of `L ^⊗ (k + n)`. Dividing
gives `x / t ∈ Γ(L ^⊗ n, V)`, which is `Stacks.TensorPowerDivision.divTop`. This file proves that
forming it **commutes with pulling back along `j`**: over any open `V' ≤ j^{-1}(V)`,

  `(j^*x) / (j^*t) = j^*(x / t)`,

where the pullback of a global section is
`Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullSection` and the pullback of a section over
`V` is `pullSectionOn` below.

`Stacks.AlgebraicGeometry.ProjChartRatioPullback.ratioOf_pullback` is the case `n = 0` read
through the ratio of two sections of a *single* power, whose quotient is a function; here the
quotient is a section of `L ^⊗ n` and the two sides are compared in that module rather than in the
structure sheaf.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjChartDivisionPullback.pullSectionOn`: the pullback of a section of
  `L ^⊗ n` over `V` to a section of `(j^*L) ^⊗ n` over `V' ≤ j^{-1}(V)`, read through the
  comparison `Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullbackNatTensorPowIso`.

## Main results

* `Stacks.AlgebraicGeometry.ProjChartDivisionPullback.app_pullbackSectionHom`: **pulling a section
  back is natural in the module.** For `φ : M ⟶ N` on `Y`, the pullback of `φ a` is `j^*φ` applied
  to the pullback of `a`.
* `Stacks.AlgebraicGeometry.ProjChartDivisionPullback.pullSectionOn_app_mulMap`: **`pullSectionOn`
  intertwines multiplication by `t` with multiplication by `j^*t`.**
* `Stacks.AlgebraicGeometry.ProjChartDivisionPullback.divTop_pullSection`: **division across
  degrees commutes with pullback.**

## Implementation notes

The quotient is characterized by `(x/t) · t = x|_V` and the uniqueness of that factor
(`Stacks.TensorPowerDivision.divOf_eq_of_mul_eq`), so the proof is the defining identity pushed
along pullback of sections. Two inputs do that pushing, and neither needs multiplicativity of
`pullSection` on *sections*:

* `app_pullbackSectionHom`, the naturality of `AlgebraicGeometry.pullbackSectionHom` in the module
  variable, which is the naturality of the unit of the pullback-pushforward adjunction read on
  sections and then restricted; and
* `Stacks.AlgebraicGeometry.ProjChartPullbackCotensorator.mulMap_comp_pullbackNatTensorPowIso_inv`,
  the unconditional identity of **morphisms**
  `j^*(mulMap σ n) ≫ c (k + n) = c n ≫ mulMap σ' n`
  behind multiplicativity, evaluated on the sections over `V'`.

Because the second input is already stated for `Stacks.GradedSections.mulMap` over
`Stacks.TensorPowers.natTensorPow` — the very family `Stacks.TensorPowerDivision.divTop` divides in
— no comparison between the left-iterated powers and the integer powers of Stacks Tag 01CU enters,
and in particular `Stacks.AlgebraicGeometry.ProjChartPullbackCotensorator.pullSection_mulSections`
is not used.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (mulMap)
open Stacks.TensorPowerTrivialize (resTop)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.AlgebraicGeometry.ProjChartFromRatios (secOf)
open Stacks.AlgebraicGeometry.ProjChartRatioPullback (pullSection pullbackNatTensorPowIso
  app_map resTop_pullSection)
open Stacks.AlgebraicGeometry.ProjChartPullbackCotensorator
  (mulMap_comp_pullbackNatTensorPowIso_inv)
open Stacks.TensorPowerDivision (divTop divOf_eq_of_mul_eq mul_divTop)

universe u

namespace Stacks.AlgebraicGeometry.ProjChartDivisionPullback

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {Y Y' : Scheme.{u}} (j : Y' ⟶ Y)

/-- Pulling a section back, spelled out as the unit of the adjunction followed by one
restriction. -/
theorem pullbackSectionHom_eq {M : Y.Modules} (U : Y.Opens) (V : Y'.Opens) (h : V ≤ j ⁻¹ᵁ U)
    (a : Γ(M, U)) :
    pullbackSectionHom j M U V h a
      = ((Scheme.Modules.pullback j).obj M).presheaf.map (homOfLE h).op
          (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M).app U a) := rfl

/-- Equal morphisms of modules agree on sections. -/
private theorem app_apply_congr {X : Scheme} {M N : X.Modules} {f g : M ⟶ N} (h : f = g)
    (U : X.Opens) (a : Γ(M, U)) : f.app U a = g.app U a := by
  rw [h]

/-- **The unit of the pullback-pushforward adjunction is natural in the module**, on sections over
an open of the target. -/
theorem app_unit_app {M N : Y.Modules} (φ : M ⟶ N) (U : Y.Opens) (a : Γ(M, U)) :
    ((Scheme.Modules.pullback j).map φ).app (j ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M).app U a)
      = ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app N).app U (φ.app U a) := by
  have hnat := (Scheme.Modules.pullbackPushforwardAdjunction j).unit.naturality φ
  have h1 := app_apply_congr hnat U a
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at h1
  exact h1.symm

/-- **Pulling a section back is natural in the module.** -/
theorem app_pullbackSectionHom {M N : Y.Modules} (φ : M ⟶ N) (U : Y.Opens) (V : Y'.Opens)
    (h : V ≤ j ⁻¹ᵁ U) (a : Γ(M, U)) :
    ((Scheme.Modules.pullback j).map φ).app V (pullbackSectionHom j M U V h a)
      = pullbackSectionHom j N U V h (φ.app U a) :=
  ((app_map ((Scheme.Modules.pullback j).map φ) (homOfLE h) _).trans
    (congrArg (fun z => ((Scheme.Modules.pullback j).obj N).presheaf.map (homOfLE h).op z)
      (app_unit_app j φ U a)))

variable (L : Y.Modules) [Stacks.Ample.IsInvertibleModule Y L]

/-! ### Pulling back a section over an open -/

/-- **The pullback of a section of `L ^⊗ n` over `V`**, as a section of `(j^*L) ^⊗ n` over an open
`V' ≤ j^{-1}(V)`: the pullback of the section, read through the comparison
`Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullbackNatTensorPowIso`. The counterpart over
`⊤` is `Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullSection`. -/
def pullSectionOn (n : ℕ) {V : Y.Opens} {V' : Y'.Opens} (hVV' : V' ≤ j ⁻¹ᵁ V)
    (a : Γ(natTensorPow L n, V)) :
    Γ(natTensorPow ((Scheme.Modules.pullback j).obj L) n, V') :=
  (pullbackNatTensorPowIso j L n).inv.app V'
    (pullbackSectionHom j (natTensorPow L n) V V' hVV' a)

/-- **Restricting the pullback of a global section is the pullback of its restriction.** This is
`Stacks.AlgebraicGeometry.ProjChartRatioPullback.resTop_pullSection` at the spelling
`pullSectionOn`. -/
theorem resTop_pullSection_eq {n : ℕ} {V : Y.Opens} {V' : Y'.Opens} (hVV' : V' ≤ j ⁻¹ᵁ V)
    (x : Γ(natTensorPow L n, ⊤)) :
    resTop (natTensorPow ((Scheme.Modules.pullback j).obj L) n) (pullSection j L n x) V'
      = pullSectionOn j L n hVV' (resTop (natTensorPow L n) x V) :=
  resTop_pullSection j L hVV' x

/-! ### Pulling back intertwines the two multiplications -/

/-- **`pullSectionOn` intertwines multiplication by `t` with multiplication by `j^*t`.** The
identity of morphisms
`Stacks.AlgebraicGeometry.ProjChartPullbackCotensorator.mulMap_comp_pullbackNatTensorPowIso_inv`
read on the sections over `V'`, with the naturality `app_pullbackSectionHom` of the pullback of a
section used to move `j^*(mulMap σ n)` across. -/
theorem pullSectionOn_app_mulMap {k : ℕ} (t : Γ(natTensorPow L k, ⊤)) (n : ℕ) {V : Y.Opens}
    {V' : Y'.Opens} (hVV' : V' ≤ j ⁻¹ᵁ V) (a : Γ(natTensorPow L n, V)) :
    (mulMap (secOf ((Scheme.Modules.pullback j).obj L) (pullSection j L k t)) n).app V'
        (pullSectionOn j L n hVV' a)
      = pullSectionOn j L (k + n) hVV' ((mulMap (secOf L t) n).app V a) := by
  have hmor := app_apply_congr (mulMap_comp_pullbackNatTensorPowIso_inv j L t n).symm V'
    (pullbackSectionHom j (natTensorPow L n) V V' hVV' a)
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at hmor
  exact hmor.trans (congrArg (fun z => (pullbackNatTensorPowIso j L (k + n)).inv.app V' z)
    (app_pullbackSectionHom j (mulMap (secOf L t) n) V V' hVV' a))

/-! ### The coherence -/

/-- **Division across degrees commutes with pullback.** For a morphism of schemes `j : Y' ⟶ Y`, an
invertible module `L` on `Y`, a global section `t` of `L ^⊗ k` not vanishing on `V`, a global
section `x` of `L ^⊗ (k + n)`, and an open `V' ≤ j^{-1}(V)` on which the pullback of `t` does not
vanish, the quotient `(j^*x)/(j^*t)` over `V'` is the pullback of the quotient `x/t` over `V`.

The quotient is the unique section whose product with `t` is `x|_V`, so it suffices to check that
the pullback of `x/t` has that property for `j^*t`: multiplying it by `j^*t` is
`pullSectionOn_app_mulMap` the pullback of multiplying `x/t` by `t`, which is `x|_V` by
`Stacks.TensorPowerDivision.mul_divTop`, whose pullback is the restriction of `j^*x` by
`resTop_pullSection_eq`. -/
theorem divTop_pullSection {k n : ℕ} (t : Γ(natTensorPow L k, ⊤)) {V : Y.Opens}
    (hV : V ≤ nonvanishingOpen Y (natTensorPow L k) t) (x : Γ(natTensorPow L (k + n), ⊤))
    {V' : Y'.Opens} (hVV' : V' ≤ j ⁻¹ᵁ V)
    (hV' : V' ≤ nonvanishingOpen Y' (natTensorPow ((Scheme.Modules.pullback j).obj L) k)
      (pullSection j L k t)) :
    divTop ((Scheme.Modules.pullback j).obj L) (pullSection j L k t) hV' n
        (pullSection j L (k + n) x)
      = pullSectionOn j L n hVV' (divTop L t hV n x) :=
  divOf_eq_of_mul_eq _ _ hV' n le_rfl
    ((pullSectionOn_app_mulMap j L t n hVV' _).trans
      ((congrArg (pullSectionOn j L (k + n) hVV') (mul_divTop L t hV n x)).trans
        (resTop_pullSection_eq j L hVV' x).symm))

end Stacks.AlgebraicGeometry.ProjChartDivisionPullback

end
