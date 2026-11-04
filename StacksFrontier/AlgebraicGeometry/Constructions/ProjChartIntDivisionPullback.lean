module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartDivisionPullback
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.HyperplaneTwistSequence
public import StacksFrontier.AlgebraicGeometry.TensorPowerDivision.Integer

/-!
# Dividing across integer degrees commutes with pullback

`StacksFrontier.AlgebraicGeometry.Constructions.ProjChartDivisionPullback` proves that
`Stacks.TensorPowerDivision.divTop` commutes with pullback, for the left-iterated powers
`Stacks.TensorPowers.natTensorPow`. This file does the same for
`Stacks.TensorPowerDivision.intDivTop`, the division across **integer** degrees in the family
`Stacks.AmpleProjectiveImmersion.tensorPowerModule` of [Stacks, Tag 01CU], which is the family the
chart sections of Tag 01NK's `θ` are built in
(`Stacks.AlgebraicGeometry.ProjChartGradedIntegerValues.intChartSectionOf`).

## The shape of the statement

In nonnegative degree the comparison `j^*(L ^⊗ n) ⟶ (j^*L) ^⊗ n` is
`Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullbackNatTensorPowIso`, and the identity of
morphisms that makes it intertwine the two multiplications is proved with **no hypothesis**, as
`Stacks.AlgebraicGeometry.ProjChartPullbackCotensorator.mulMap_comp_pullbackNatTensorPowIso_inv`.
No such unconditional identity exists for the integer powers: the multiplication there is
`Stacks.TensorPowerDivision.intMulIso`, coming from the coherent multiplication datum of Tag
01CU, and nothing in the repository says that a pullback comparison respects it in bidegrees that
are not both nonnegative.

So everything here is stated against an **arbitrary** family of comparison morphisms `c`, with
the intertwining carried as a hypothesis — the same discipline as
`Stacks.AlgebraicGeometry.ProjChartSectionPullback.pullSection_mulSections_of_mulMap`, which
carries the nonnegative-degree identity before the cotensorator discharges it. What this file
establishes is that the intertwining is the *only* thing the division coherence needs: given it,
the coherence is the defining identity of the quotient pushed along pullback of sections, exactly
as in the nonnegative case.

## Main definitions

* `…IntCompare`: a family of comparison morphisms `j^*(L ^⊗ d) ⟶ (j^*L) ^⊗ d`, `d : ℤ`.
* `…intPullbackCompare`: one such family, an isomorphism in every degree —
  `…HyperplaneTwistSequence.pullbackTensorPowModuleIntIso` conjugated by
  `Stacks.PowerFamilyBridge.tensorPowerModuleIso` on each side. **Not** the family to use: its
  multiplicativity is not proved, for the reason its own docstring gives.
* `…intPullSection` and `…intPullSectionOn`: the pullback of a global section of `L ^⊗ n`, and of
  a section over an open `V`, read through such a family.

## Main results

* `…resTop_intPullSection`: **restricting the pullback of a global section is the pullback of its
  restriction**, for any comparison family.
* `…intPullSectionOn_app_intMulMap`: the intertwining identity of morphisms, read on the sections
  over `V'`.
* `…intDivTop_intPullSection`: **division across integer degrees commutes with pullback.**

## `hmul` is discharged, for the canonical family

The hypothesis `hmul` is **discharged**:
`StacksFrontier.AlgebraicGeometry.Constructions.ProjChartIntMulMapPullback` proves it with no
hypothesis, for the family `…ProjChartIntMulMapPullback.intCompare` built from
`…ProjChartIntPullbackMul.intPullIso`, and restates both results of this file with it discharged
(`…ProjChartIntMulMapPullback.intPullSectionOn_app_intMulMap` and
`…ProjChartIntMulMapPullback.intDivTop_intPullSection`). The statements here are kept against an
arbitrary `c` because that is what the chart assembly instantiates.

The multiplicativity that discharges it is
`Stacks.TensorPowerPullback.pullbackIntPowIso_coherentMulIso`, proved in every pair of integer
degrees and with no hypothesis, carried to this vocabulary by
`…ProjChartIntPullbackMul.intPullIso_intMulIso`. It is a statement about that family and not
about `intPullbackCompare`, which is built from
`Stacks.PowerFamilyBridge.tensorPowerModuleIso` and has no multiplicativity; nothing below uses
`intPullbackCompare`.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.TensorPowerTrivialize (resTop)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.TensorPowerDivision (intMulMap intSecOf intDivTop intDivOf_eq_of_mul_eq
  mul_intDivTop)
open Stacks.AlgebraicGeometry.ProjChartRatioPullback (app_map top_le_preimage_top
  map_pullbackSectionHom)
open Stacks.AlgebraicGeometry.ProjChartDivisionPullback (app_pullbackSectionHom)
open Stacks.PullbackUnitSection (unitPullback pullbackSectionHom_globalSection)
open Stacks.SectionProduct (globalSection)

universe u

namespace Stacks.AlgebraicGeometry.ProjChartIntDivisionPullback

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {Y Y' : Scheme.{u}} (j : Y' ⟶ Y) (L : Y.Modules)
  [Stacks.Ample.IsInvertibleModule Y L]

/-- **A comparison of the integer tensor powers of `L` with those of `j^*L`**, as a family of
morphisms `j^*(L ^⊗ d) ⟶ (j^*L) ^⊗ d` indexed by the integer degree. Everything below is stated
against an arbitrary such family; the one to instantiate it at is
`Stacks.AlgebraicGeometry.ProjChartIntMulMapPullback.intCompare`, whose multiplicativity is
proved with no hypothesis. -/
abbrev IntCompare : Type _ :=
  (d : ℤ) → (Scheme.Modules.pullback j).obj (tensorPowerModule Y L d) ⟶
    tensorPowerModule Y' ((Scheme.Modules.pullback j).obj L) d

/-- **The canonical comparison of the integer tensor powers under pullback**, in every integer
degree: the comparison
`Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pullbackTensorPowModuleIntIso` for the ampleness
theory's family `Stacks.Ample.tensorPowModule`, conjugated on each side by
`Stacks.PowerFamilyBridge.tensorPowerModuleIso`, which identifies that family with [Stacks, Tag
01CU]'s `Stacks.AmpleProjectiveImmersion.tensorPowerModule` in every integer degree.

**Not the family to use.** Its multiplicativity — the hypothesis `hmul` below — is not proved,
and cannot be: `Stacks.PowerFamilyBridge.tensorPowerModuleIso` has no multiplicativity. The
family to use is `Stacks.AlgebraicGeometry.ProjChartIntMulMapPullback.intCompare`, built from
`…ProjChartIntPullbackMul.intPullIso` instead, for which `hmul` is proved unconditionally. This
definition is kept only because it is the comparison the ampleness theory's own twist family
supplies. -/
def intPullbackCompare : IntCompare j L := fun d =>
  (((Scheme.Modules.pullback j).mapIso (Stacks.PowerFamilyBridge.tensorPowerModuleIso Y L d)) ≪≫
    Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pullbackTensorPowModuleIntIso j L d ≪≫
    (Stacks.PowerFamilyBridge.tensorPowerModuleIso Y'
      ((Scheme.Modules.pullback j).obj L) d).symm).hom

/-- `intPullbackCompare` is an isomorphism in every degree, being a composite of three. -/
instance isIso_intPullbackCompare (d : ℤ) : IsIso (intPullbackCompare j L d) :=
  inferInstanceAs (IsIso (Iso.hom _))

variable (c : IntCompare j L)

/-! ### Pulling a section back -/

/-- **The pullback of a global section of `L ^⊗ n`** in integer degree `n`, as a global section of
`(j^*L) ^⊗ n`: the pullback of the section, read through the comparison `c`. The counterpart in
nonnegative degree, for the left-iterated powers, is
`Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullSection`. -/
def intPullSection (n : ℤ) (x : Γ(tensorPowerModule Y L n, ⊤)) :
    Γ(tensorPowerModule Y' ((Scheme.Modules.pullback j).obj L) n, ⊤) :=
  (c n).app ⊤ (pullbackSectionHom j (tensorPowerModule Y L n) ⊤ ⊤ (top_le_preimage_top j) x)

/-- **The pullback of a section of `L ^⊗ n` over `V`**, as a section of `(j^*L) ^⊗ n` over an open
`V' ≤ j^{-1}(V)`, read through the comparison `c`. -/
def intPullSectionOn (n : ℤ) {V : Y.Opens} {V' : Y'.Opens} (hVV' : V' ≤ j ⁻¹ᵁ V)
    (a : Γ(tensorPowerModule Y L n, V)) :
    Γ(tensorPowerModule Y' ((Scheme.Modules.pullback j).obj L) n, V') :=
  (c n).app V' (pullbackSectionHom j (tensorPowerModule Y L n) V V' hVV' a)

/-- **Restricting the pullback of a global section is the pullback of its restriction.** Both
sides are the comparison applied to one pullback of `x`, and the two pullbacks agree because the
homomorphisms of a poset are unique. -/
theorem resTop_intPullSection (n : ℤ) {V : Y.Opens} {V' : Y'.Opens} (hVV' : V' ≤ j ⁻¹ᵁ V)
    (x : Γ(tensorPowerModule Y L n, ⊤)) :
    resTop (tensorPowerModule Y' ((Scheme.Modules.pullback j).obj L) n)
        (intPullSection j L c n x) V'
      = intPullSectionOn j L c n hVV' (resTop (tensorPowerModule Y L n) x V) :=
  (app_map (c n) (homOfLE (le_top : V' ≤ ⊤)) _).symm.trans
    (congrArg (fun z => (c n).app V' z)
      ((map_pullbackSectionHom j (tensorPowerModule Y L n) ⊤ ⊤ V'
            (homOfLE (le_top : V' ≤ ⊤)) (top_le_preimage_top j)
            (le_top.trans (top_le_preimage_top j)) x).trans
        (pullbackSectionHom_map j (tensorPowerModule Y L n) ⊤ V le_top V' hVV'
          (le_top.trans (top_le_preimage_top j)) x).symm))

/-- **The pullback of a global section of `L ^⊗ k`, read as a morphism out of the monoidal
unit**: the image under `j^*` of the original such morphism, preceded by the morphism
`Stacks.PullbackUnitSection.unitPullback` through which `j^*` takes a morphism out of the unit
again to a morphism out of the unit, and followed by the comparison `c`.

The integer-degree counterpart of
`Stacks.AlgebraicGeometry.ProjChartSectionPullback.secOf_pullSection`, with the same proof: both
sides are global sections of the same module, and the left one is pushed to the right by
`Stacks.SectionProduct.globalSection_comp` and
`Stacks.PullbackUnitSection.pullbackSectionHom_globalSection`. -/
theorem intSecOf_intPullSection (k : ℤ) (t : Γ(tensorPowerModule Y L k, ⊤)) :
    intSecOf ((Scheme.Modules.pullback j).obj L) (intPullSection j L c k t)
      = unitPullback j ≫ (Scheme.Modules.pullback j).map (intSecOf L t) ≫ c k := by
  refine (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y'
    (tensorPowerModule Y' ((Scheme.Modules.pullback j).obj L) k)).symm_apply_eq.mpr ?_
  show intPullSection j L c k t = globalSection Y' _ _
  rw [← Category.assoc, Stacks.SectionProduct.globalSection_comp _ _
      (unitPullback j ≫ (Scheme.Modules.pullback j).map (intSecOf L t)) (c k),
    ← pullbackSectionHom_globalSection j (tensorPowerModule Y L k) (intSecOf L t),
    Stacks.TensorPowerDivision.globalSection_intSecOf]
  rfl

/-! ### The intertwining hypothesis, and the coherence it gives -/

/-- **The comparison intertwines multiplication by `t` with multiplication by `j^*t`**, on the
sections over `V'`, given the corresponding identity of morphisms. This is the integer-degree
counterpart of
`Stacks.AlgebraicGeometry.ProjChartDivisionPullback.pullSectionOn_app_mulMap`, whose hypothesis is
discharged unconditionally by the cotensorator; here it is carried, and discharged for the
canonical family by
`Stacks.AlgebraicGeometry.ProjChartIntMulMapPullback.intPullSectionOn_app_intMulMap`. -/
theorem intPullSectionOn_app_intMulMap {k : ℤ} (t : Γ(tensorPowerModule Y L k, ⊤)) (n : ℤ)
    (hmul : (Scheme.Modules.pullback j).map (intMulMap L (intSecOf L t) n) ≫ c (k + n)
      = c n ≫ intMulMap ((Scheme.Modules.pullback j).obj L)
          (intSecOf ((Scheme.Modules.pullback j).obj L) (intPullSection j L c k t)) n)
    {V : Y.Opens} {V' : Y'.Opens} (hVV' : V' ≤ j ⁻¹ᵁ V) (a : Γ(tensorPowerModule Y L n, V)) :
    (intMulMap ((Scheme.Modules.pullback j).obj L)
          (intSecOf ((Scheme.Modules.pullback j).obj L) (intPullSection j L c k t)) n).app V'
        (intPullSectionOn j L c n hVV' a)
      = intPullSectionOn j L c (k + n) hVV' ((intMulMap L (intSecOf L t) n).app V a) := by
  have hmor := ConcreteCategory.congr_hom
    (congrArg (fun z : (Scheme.Modules.pullback j).obj (tensorPowerModule Y L n) ⟶
        tensorPowerModule Y' ((Scheme.Modules.pullback j).obj L) (k + n) => z.app V') hmul.symm)
    (pullbackSectionHom j (tensorPowerModule Y L n) V V' hVV' a)
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at hmor
  exact hmor.trans (congrArg (fun z => (c (k + n)).app V' z)
    (app_pullbackSectionHom j (intMulMap L (intSecOf L t) n) V V' hVV' a))

/-- **Division across integer degrees commutes with pullback**, given that the comparison `c`
intertwines the two multiplications by `t`.

The quotient is the unique section whose product with `t` is `x|_V`, so it suffices to check that
the pullback of `x/t` has that property for the pullback of `t`: multiplying it by `j^*t` is, by
`intPullSectionOn_app_intMulMap`, the pullback of multiplying `x/t` by `t`, which is `x|_V` by
`Stacks.TensorPowerDivision.mul_intDivTop`, whose pullback is the restriction of `j^*x` by
`resTop_intPullSection`.

For the canonical family the hypothesis is discharged:
`Stacks.AlgebraicGeometry.ProjChartIntMulMapPullback.intDivTop_intPullSection` is this statement
with no hypothesis at all. -/
theorem intDivTop_intPullSection {k : ℤ} (t : Γ(tensorPowerModule Y L k, ⊤)) (n : ℤ)
    (hmul : (Scheme.Modules.pullback j).map (intMulMap L (intSecOf L t) n) ≫ c (k + n)
      = c n ≫ intMulMap ((Scheme.Modules.pullback j).obj L)
          (intSecOf ((Scheme.Modules.pullback j).obj L) (intPullSection j L c k t)) n)
    {V : Y.Opens} (hV : V ≤ nonvanishingOpen Y (tensorPowerModule Y L k) t)
    (x : Γ(tensorPowerModule Y L (k + n), ⊤)) {V' : Y'.Opens} (hVV' : V' ≤ j ⁻¹ᵁ V)
    (hV' : V' ≤ nonvanishingOpen Y'
      (tensorPowerModule Y' ((Scheme.Modules.pullback j).obj L) k)
      (intPullSection j L c k t)) :
    intDivTop ((Scheme.Modules.pullback j).obj L) (intPullSection j L c k t) hV' n
        (intPullSection j L c (k + n) x)
      = intPullSectionOn j L c n hVV' (intDivTop L t hV n x) :=
  intDivOf_eq_of_mul_eq _ _ hV' n le_rfl
    ((intPullSectionOn_app_intMulMap j L c t n hmul hVV' _).trans
      ((congrArg (intPullSectionOn j L c (k + n) hVV') (mul_intDivTop L t hV n x)).trans
        (resTop_intPullSection j L c (k + n) hVV' x).symm))

end Stacks.AlgebraicGeometry.ProjChartIntDivisionPullback

end
