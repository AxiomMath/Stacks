module

public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Trivialize
public import StacksFrontier.AlgebraicGeometry.SectionProduct.MonoidalUnitBridge
public import StacksFrontier.AlgebraicGeometry.SheafInternalHom.SliceUnitSections
public import StacksFrontier.AlgebraicGeometry.TwistedSectionModule.MonoidalFunctor
public import StacksFrontier.AlgebraicGeometry.SectionRingGeometric.UnitScalarSupplement

/-!
# Stacks Tag 0B5L's comparison map on a scheme, with no hypothesis

`StacksFrontier/AlgebraicGeometry/TwistedSectionModule/MonoidalFunctor.lean` builds Stacks Tag
0B5L's map
`Γ_*(X, ℱ, L)_{(s)} ⟶ Γ(G ℱ)` out of the degree-zero localization of the global twisted sections,
for a monoidal functor `G` after which the degree-one section `s` becomes invertible. **This file
discharges both hypotheses on a scheme**, taking `G` to be restriction to an open inside the
nonvanishing locus of `s`:

* `G` is monoidal for the monoidal structure the twisted sections are stated over, which is
  `Stacks.SheafInternalHom.SliceRestriction.schemeOverFunctorMonoidal`;
* `G s` is an isomorphism, which is the trivialization clause of Stacks Tag 01CY.

The result, `Stacks.TwistedSections.localizationLiftOverOpen`, carries **no hypothesis beyond
`V ≤ X_s`**, which is the hypothesis Tag 0B5L itself has.

## Main results

* `Stacks.TwistedSections.isIso_openRestriction_map_of_le_nonvanishingOpen`: **Tag 01CY's
  trivialization clause at the monoidal-unit spelling.** A morphism `𝟙_ X.Modules ⟶ M` out of the
  tensor unit of `Stacks.SheafInternalHom.schemeMonoidalCategory`, with `M` invertible, restricts
  to an isomorphism on every open inside the nonvanishing open of its global section.
* `Stacks.TwistedSections.isIso_mapPowSections_openRestriction`: the hypothesis of Tag 0B5L's map,
  for a global section of any tensor power of `L`.
* `Stacks.TwistedSections.localizationLiftOverOpen`: **Tag 0B5L's comparison map on a scheme.**
* `Stacks.TwistedSections.shiftPow_localizationLiftOverOpen_mk`: its value on a fraction `t / sⁿ`
  is the section whose `n`-fold product with `s|_V` is `t|_V`, which is Tag 0B5L's own description
  of the map and what makes the construction faithful rather than arbitrary.
* `Stacks.TwistedSections.localizationLiftSections`: **the same map landing in `Γ(ℱ, V)`.** Tag
  0B5L's map lands in `twistSections (ℱ|_V) (L|_V) 0`, a morphism out of the monoidal unit of the
  modules on the slice site over `V`, while Tag 0B5I's local data asks for a section of `ℱ` over
  `V`; the two are identified by
  `Stacks.SheafInternalHom.SliceRestriction.schemeOpenUnitHomAddEquiv`.
* `Stacks.TwistedSections.shiftPow_schemeOpenUnitHomAddEquiv_symm_localizationLiftSections_mk`:
  the value on `t / sⁿ` of that composite, read back through the identification.
* `Stacks.TwistedSections.openDivision` and `isPowerInvariant_openDivision`: the divisions by the
  powers of `s`, with the quotient read as a section of `ℱ` over `V`.
* `Stacks.TwistedSections.localizationLiftSections_eq`: **the composite is the lift of those
  divisions.** This is what puts the map in the shape
  `Stacks.TwistedSections.localizationLiftOfDegree_smul` consumes, its target `Γ(ℱ, V)` being a
  module over `Γ(X, V)`; see *What is still owed*.

## Implementation notes

**The monoidal unit is the obstacle, and the bridge for it is already available.** `powSections L n`
is `𝟙_ X.Modules ⟶ L ^⊗ n`, out of the tensor unit of
`Stacks.SheafInternalHom.schemeMonoidalCategory`, which is the sheafification of the presheaf
unit; Tag 01CY is stated for a morphism out of `SheafOfModules.unit`. The comparison between the
two is `Stacks.SectionProduct.ofUnitHom`/`toUnitHom`, and
`Stacks.SectionProduct.globalSection X M f` is the global section of such an `f` read through it,
so `Stacks.NonvanishingOpen.nonvanishingOpen X M (globalSection X M f)` is `X_f` with no further
bridge. Only the factorization `f = unitIso.hom ≫ toUnitHom f` is used, which is
`Stacks.SectionProduct.ofUnitHom_toUnitHom`.

**The slice site's monoidal unit is bridged, not worked around.** The bridge is
`Stacks.SheafInternalHom.SliceRestriction.schemeOpenUnitHomAddEquiv`, which is
`Stacks.SectionRingGeometric.tensorUnitHomAddEquiv` — already stated for an arbitrary site and an
arbitrary terminal object — supplied with `CategoryTheory.Over.mkIdTerminal`, the terminal object
of `Over V` being `V` over itself.

**Every statement here is at the `X.Modules` spelling.** The restriction functor is
`Stacks.SheafInternalHom.SliceRestriction.schemeOpenRestriction`, whose source is written
`X.Modules` rather than `SheafOfModules (structureSheaf X.presheaf _)`. This is not cosmetic:
with the other spelling the type `Γ_*(X, ℱ, L)_{(s)} →+ Γ(ℱ|_V)` inferred for the map is built
from instances of the one spelling and the type written down from instances of the other, and
unifying the two exhausts the heartbeat budget inside `isDefEq` instead of failing.

## What is still owed

**Piece (iii) of Stacks Tag 0B5I's local datum — the 𝒪-linearity — is now one identity.**
`Stacks.TwistedSections.localizationLiftOfDegree_smul` turns semilinearity of the lift into a
statement about the division family: for `a` a global section of `L ^⊗ (m • d)` and `t` one of
`ℱ ⊙ (d * n)`,

`openDivision (m + n) (a · t) = φ (a / sᵐ) • openDivision n t`.

The ring map `φ` is **not** missing. It is `Stacks.SectionRingChartMap.chartRingMap L s hV`, whose
source is `Stacks.TwistedSections.ringAtNonvanishingOpenOfDegree s` — the two gradings agree by
`rfl` (`Stacks.TwistedSections.sectionGrading_eq_ampleGrading`) and
`Stacks.AmpleFiniteAvoidance.nvOpen L s` is the open this file's `hV` names — and whose target is
`Γ(X, V)`; it is checked to elaborate at exactly that type.

**The two inputs.** `Stacks.SectionRingGeometric.unitScalar` and `globalSection_unitComp` are
stated not only for a scheme and its terminal open but for an arbitrary terminal object
of an arbitrary ringed site, in the binder shape of
`Stacks.SectionRingGeometric.tensorUnitHomAddEquiv`, with the scheme forms re-derived from them.
And the multiplicativity of the division is
`Stacks.TwistedSections.openDivision_gsmul_unitComp`
(`StacksFrontier/AlgebraicGeometry/TwistedSectionModule/DivisionMultiplicativity.lean`): the division
over `V` of `(e · sᵐ) · t` by `s ^ (n + m)` is `Stacks.TwistedSections.sliceUnitScalar L V e`
times the division of `t` by `sⁿ`, and that scalar is an honest function on `V` rather than an
endomorphism of the slice site's monoidal unit.

**Passing to an arbitrary numerator.** The identity is
proved for a numerator *presented* as `e · sᵐ` with `e` of degree zero, with the scalar
`sliceUnitScalar L V e`; the hypothesis `hφ` quantifies over every `a` of degree `m • d` and names
the scalar `chartRingMap L s hV (a / sᵐ)`. Two steps close the gap.

* `sliceUnitScalar L V e` is the restriction to `V` of the global function
  `Stacks.SectionRingGeometric.schemeUnitScalar X e`, by
  `Stacks.TwistedSections.sliceUnitScalar_eq`
  (`StacksFrontier/AlgebraicGeometry/TwistedSectionModule/SliceSectionBridge.lean`), so it is a
  value of `Stacks.SectionRingChartMap.numMap` by that lemma's defining identity
  `numMap_unique` together with
  `Stacks.SectionRingGeometric.schemeGlobalSection_unitComp`, which is how `chartRingMap`
  computes (`Stacks.SectionRingChartMap.chartRingMap_mk_eq_numMap`).

  **The identification uses a coherence for the lax unit `ε`** of
  `Stacks.SheafInternalHom.SliceRestriction.overFunctorMonoidal`, namely that
  `schemeOpenUnitHomAddEquiv V M` applied to `mapTwistSections (schemeOpenRestriction X V) t` is
  `resTop M (globalSection X M t) V`; this is
  `Stacks.TwistedSections.schemeOpenUnitHomAddEquiv_mapTwistSections`, with no factor. The lax
  unit contributes a function `Stacks.TwistedSections.sliceUnitRatio X V` on `V`, depending on
  neither `M` nor `t`, and `Stacks.TwistedSections.sliceUnitRatio_eq_one` computes it to be `1`
  — a short chase through
  `CategoryTheory.Localization.Monoidal.functorMonoidalOfComp_ε`, two of whose three factors are
  identities because both monoidal structures localize at the unit comparison `Iso.refl _`; see
  the implementation notes of
  `StacksFrontier/AlgebraicGeometry/TwistedSectionModule/SliceSectionBridge.lean`.

* For an arbitrary `a`
  the factorisation `a = e · sᵐ` does exist only *after restriction to `V`*, because
  `mapPowSections (schemeOpenRestriction X V) s` is invertible there, and the degree-zero factor
  it produces does live on the slice site, where
  `Stacks.SectionRingGeometric.schemeUnitScalar` — a global function on `X` — does not apply, so
  `sliceUnitScalar_eq` does not reach it. **But no division at `F := 𝟙_` is involved and the
  object identity `twistPow (𝟙_ C) L k = natTensorPow L k` is not used.** A power of an
  invertible section is invertible (`Stacks.TwistedSections.isIso_sectionPow`), so the factor is
  simply `a|_V ≫ (sᵐ|_V)⁻¹`, a morphism `𝟙_ ⟶ 𝟙_` on the nose
  (`Stacks.TwistedSections.exists_sliceFactor`); the identity above remains true and remains not
  definitional, and nothing consumes it. The resulting identity is
  `Stacks.TwistedSections.openDivision_gsmul_chartRingMap`, and piece (iii) itself is
  `Stacks.TwistedSections.localizationLiftSections_smul`
  (`StacksFrontier/AlgebraicGeometry/TwistedSectionModule/ChartLinearity.lean`): the scalar is
  identified with `Stacks.SectionRingChartMap.chartFamily` by multiplying the slice relation
  through by `s` — which makes the generator `s · sᵐ`, nonvanishing on `V` for every `m` — and
  then `Stacks.SectionRingChartMap.ratio_unique`.

## References

* [Stacks Project, Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0B5I](https://stacks.math.columbia.edu/tag/0B5I)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite DirectSum
open Stacks.GradedSections (powSections)
open Stacks.TensorPowers (natTensorPow)

universe u

namespace Stacks.TwistedSections

open Stacks.SheafInternalHom.SliceRestriction (schemeOpenRestriction schemeOverFunctorMonoidal
  schemeOpenUnitHomAddEquiv)
open Stacks.SectionProduct (toUnitHom monoidalUnitHomEquiv globalSection)
open Stacks.NonvanishingSpelling (toSheafOfModules)
open scoped Stacks.NonvanishingSpelling

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive
  Stacks.SectionRingGeometric.presheafMonoidalPreadditiveStructure
  Stacks.SectionRingGeometric.sheafifyAdditive
  Stacks.SectionRingGeometric.tensorLeftAdditive
  Stacks.SectionRingGeometric.tensorRightAdditive
  Stacks.SheafInternalHom.SliceRestriction.schemeOverFunctorMonoidal

variable {X : Scheme.{u}}

/-- **The trivialization clause of Stacks Tag 01CY, for a morphism out of the monoidal unit.**
A morphism `f : 𝟙_ X.Modules ⟶ M` into an invertible module restricts to an isomorphism on every
open inside the nonvanishing open of its global section. Tag 01CY is available for a morphism out
of `SheafOfModules.unit`; the two units differ, and `Stacks.SectionProduct.ofUnitHom_toUnitHom`
factors `f` as the comparison isomorphism followed by such a morphism. -/
theorem isIso_openRestriction_map_of_le_nonvanishingOpen (M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M] (f : 𝟙_ X.Modules ⟶ M) {V : X.Opens}
    (hV : V ≤ Stacks.NonvanishingOpen.nonvanishingOpen X M (globalSection X M f)) :
    IsIso ((schemeOpenRestriction X V).map f) := by
  let hA : IsIso ((schemeOpenRestriction X V).map
      (M.unitHomEquiv.symm (monoidalUnitHomEquiv M f))) :=
    Stacks.NonvanishingTrivialize.isIso_over_of_le (X := X.toRingedSpace)
      (L := toSheafOfModules X M) (monoidalUnitHomEquiv M f) hV
  have h1 : toUnitHom f = M.unitHomEquiv.symm (monoidalUnitHomEquiv M f) :=
    (M.unitHomEquiv.symm_apply_apply (toUnitHom f)).symm
  have hfac : f = (_root_.AlgebraicGeometry.SheafOfModules.unitIso X.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)).hom ≫
      M.unitHomEquiv.symm (monoidalUnitHomEquiv M f) := by
    rw [← h1]
    exact (Stacks.SectionProduct.ofUnitHom_toUnitHom f).symm
  rw [(congrArg (schemeOpenRestriction X V).map hfac).trans
    ((schemeOpenRestriction X V).map_comp _ _)]
  exact (((schemeOpenRestriction X V).mapIso
      (_root_.AlgebraicGeometry.SheafOfModules.unitIso X.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X))) ≪≫
    @asIso _ _ _ _ _ hA).isIso_hom

/-- **The hypothesis of Stacks Tag 0B5L's comparison map, discharged.** Carrying a global section
of `L ^⊗ n` along restriction to an open inside its nonvanishing open gives an isomorphism: this
is `Stacks.TwistedSections.isIso_mapPowSections` fed with the previous theorem. -/
theorem isIso_mapPowSections_openRestriction (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {n : ℕ} (s : powSections L n) {V : X.Opens}
    (hV : V ≤ Stacks.NonvanishingOpen.nonvanishingOpen X (natTensorPow L n)
      (globalSection X _ s)) :
    IsIso (mapPowSections (schemeOpenRestriction X V) s) := by
  have h := isIso_openRestriction_map_of_le_nonvanishingOpen (natTensorPow L n) s hV
  exact @isIso_mapPowSections _ _ _ _ _ _ (schemeOpenRestriction X V) _ _ _ s h

/-- **Stacks Tag 0B5L's comparison map on a scheme, with no hypothesis beyond `V ≤ X_s`.** For
`L` an invertible `𝒪_X`-module, `s` a global section of `L` and `V` an open on which `s` does not
vanish, the degree-zero localization `Γ_*(X, ℱ, L)_{(s)}` of the graded module of twisted
sections maps to the sections of `ℱ` over `V`, by restricting a numerator and dividing by the
power of `s` in the denominator. -/
def localizationLiftOverOpen (F L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    {d : ℕ} (s : powSections L d) (V : X.Opens)
    (hV : V ≤ Stacks.NonvanishingOpen.nonvanishingOpen X (natTensorPow L d)
      (globalSection X _ s)) :
    sectionAtNonvanishingOpenOfDegree F L s →+
      twistSections ((schemeOpenRestriction X V).obj F)
        ((schemeOpenRestriction X V).obj L) 0 :=
  haveI := isIso_mapPowSections_openRestriction L s hV
  localizationLiftOfMonoidal (schemeOpenRestriction X V) (F := F) s

/-- **The value of Tag 0B5L's map on a fraction `t / sⁿ`**: it is the section of `ℱ|_V` whose
`n`-fold product with `s|_V` is the restriction of `t`. This is Tag 0B5L's own description of the
map, and it is what makes the construction the comparison rather than an arbitrary morphism. -/
theorem shiftPow_localizationLiftOverOpen_mk (F L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {d : ℕ} (s : powSections L d) (V : X.Opens)
    (hV : V ≤ Stacks.NonvanishingOpen.nonvanishingOpen X (natTensorPow L d)
      (globalSection X _ s))
    (n : ℕ) (t : twistSections F L (d * n)) :
    shiftPow (mapPowSections (schemeOpenRestriction X V) s) n
        (localizationLiftOverOpen F L s V hV
          (⟨LocalizedModule.mk (DirectSum.of (twistSections F L) (d * n) t)
              (⟨homogeneousSectionOfDegree s ^ n, ⟨n, rfl⟩⟩ :
                Submonoid.powers (homogeneousSectionOfDegree s)),
            mk_mem_sectionAtNonvanishingOpenOfDegree s n t⟩ :
              sectionAtNonvanishingOpenOfDegree F L s)) =
      mapTwistSections (schemeOpenRestriction X V) t :=
  have := isIso_mapPowSections_openRestriction L s hV
  shiftPow_localizationLiftOfMonoidal_mk (schemeOpenRestriction X V) s n t

/-- **Stacks Tag 0B5L's comparison map, landing in the sections over `V`.**
`localizationLiftOverOpen` lands in `twistSections (ℱ|_V) (L|_V) 0`, which is a morphism out of
the monoidal unit of the modules on the slice site over `V`; the local data of Stacks Tag 0B5I
asks instead for a section of `ℱ` over `V`. The two are identified by
`Stacks.SheafInternalHom.SliceRestriction.schemeOpenUnitHomAddEquiv`, and this is the composite. -/
def localizationLiftSections (F L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    {d : ℕ} (s : powSections L d) (V : X.Opens)
    (hV : V ≤ Stacks.NonvanishingOpen.nonvanishingOpen X (natTensorPow L d)
      (globalSection X _ s)) :
    sectionAtNonvanishingOpenOfDegree F L s →+ Γ(F, V) :=
  (schemeOpenUnitHomAddEquiv V F).toAddMonoidHom.comp
    (localizationLiftOverOpen F L s V hV)

/-- **The divisions by the powers of `s`, landing in the sections over `V`.** The `n`-th member
divides a twisted section of degree `d * n` by `sⁿ`, the quotient being read as a section of `ℱ`
over `V` rather than as a morphism out of the slice site's monoidal unit. -/
def openDivision (F L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    {d : ℕ} (s : powSections L d) (V : X.Opens)
    (hV : V ≤ Stacks.NonvanishingOpen.nonvanishingOpen X (natTensorPow L d)
      (globalSection X _ s))
    (n : ℕ) : twistSections F L (d * n) →+ Γ(F, V) :=
  haveI := isIso_mapPowSections_openRestriction L s hV
  (schemeOpenUnitHomAddEquiv V F).toAddMonoidHom.comp
    (monoidalDivision (schemeOpenRestriction X V) s n)

/-- **The divisions over `V` are power-invariant**: re-seating the quotient as a section of `ℱ`
does not disturb the invariance, which is
`Stacks.TwistedSections.isPowerInvariant_monoidalDivision`. -/
theorem isPowerInvariant_openDivision (F L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {d : ℕ} (s : powSections L d) (V : X.Opens)
    (hV : V ≤ Stacks.NonvanishingOpen.nonvanishingOpen X (natTensorPow L d)
      (globalSection X _ s)) :
    IsPowerInvariantOfDegree s (openDivision F L s V hV) := by
  have := isIso_mapPowSections_openRestriction L s hV
  exact fun n k t => congrArg (schemeOpenUnitHomAddEquiv V F)
    (isPowerInvariant_monoidalDivision (schemeOpenRestriction X V) s n k t)

/-- **Tag 0B5L's map over `V` is the lift of the divisions over `V`.** So it is in the shape
`Stacks.TwistedSections.localizationLiftOfDegree_smul` consumes: its target `Γ(ℱ, V)` is a module
over `Γ(X, V)`, and semilinearity over a ring map out of `Γ_*(X, L)_{(s)}` — piece (iii) of Stacks
Tag 0B5I's local datum, the 𝒪-linearity — is now a statement about this family. The ring map is
`Stacks.SectionRingChartMap.chartRingMap`, whose source is `ringAtNonvanishingOpenOfDegree s` and
whose target is `Γ(X, V)` for exactly this `hV`. -/
theorem localizationLiftSections_eq (F L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {d : ℕ} (s : powSections L d) (V : X.Opens)
    (hV : V ≤ Stacks.NonvanishingOpen.nonvanishingOpen X (natTensorPow L d)
      (globalSection X _ s)) :
    localizationLiftSections F L s V hV =
      localizationLiftOfDegree s (openDivision F L s V hV)
        (isPowerInvariant_openDivision F L s V hV) :=
  have := isIso_mapPowSections_openRestriction L s hV
  (localizationLift_comp (schemeOpenUnitHomAddEquiv V F).toAddMonoidHom s
    (monoidalDivision (schemeOpenRestriction X V) s)
    (isPowerInvariant_monoidalDivision (schemeOpenRestriction X V) s)).symm

/-- **The value of `localizationLiftSections` on a fraction `t / sⁿ`**, read back through the
identification of sections over `V` with morphisms out of the slice site's monoidal unit: the
section it produces is the one whose `n`-fold product with `s|_V` is the restriction of `t`. This
is `shiftPow_localizationLiftOverOpen_mk` carried across
`Stacks.SheafInternalHom.SliceRestriction.schemeOpenUnitHomAddEquiv`, which is a bijection, so the
description still pins the section down. -/
theorem shiftPow_schemeOpenUnitHomAddEquiv_symm_localizationLiftSections_mk
    (F L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] {d : ℕ} (s : powSections L d)
    (V : X.Opens)
    (hV : V ≤ Stacks.NonvanishingOpen.nonvanishingOpen X (natTensorPow L d)
      (globalSection X _ s))
    (n : ℕ) (t : twistSections F L (d * n)) :
    shiftPow (mapPowSections (schemeOpenRestriction X V) s) n
        ((schemeOpenUnitHomAddEquiv V F).symm
          (localizationLiftSections F L s V hV
            (⟨LocalizedModule.mk (DirectSum.of (twistSections F L) (d * n) t)
                (⟨homogeneousSectionOfDegree s ^ n, ⟨n, rfl⟩⟩ :
                  Submonoid.powers (homogeneousSectionOfDegree s)),
              mk_mem_sectionAtNonvanishingOpenOfDegree s n t⟩ :
                sectionAtNonvanishingOpenOfDegree F L s))) =
      mapTwistSections (schemeOpenRestriction X V) t :=
  (congrArg (shiftPow (mapPowSections (schemeOpenRestriction X V) s) n)
      ((schemeOpenUnitHomAddEquiv V F).symm_apply_apply _)).trans
    (shiftPow_localizationLiftOverOpen_mk F L s V hV n t)

end Stacks.TwistedSections

end
