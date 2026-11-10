module

public import StacksFrontier.AlgebraicGeometry.TwistedSectionModule.NestedOpenRestriction
public import StacksFrontier.AlgebraicGeometry.TwistedSectionModule.SliceSectionBridge

/-!
# Stacks Tag 0B5L's comparison map over a smaller open, read as a section

`StacksFrontier/AlgebraicGeometry/TwistedSectionModule/NestedOpenRestriction.lean` builds Stacks Tag
0B5L's comparison map over an arbitrary open `V' ≤ V`, as a map into the degree-zero twisted
sections on the **iterated** slice site — the slice site of `(X.Opens)/V` over the object
`Over.mk (homOfLE hV')`. The local data of Stacks Tag 0B5I asks instead for a section of `ℱ` over
`V'`. This file supplies the identification and the resulting compatibility.

Nothing new is proved about the lax unit.
`Stacks.TwistedSections.overTensorUnitHomAddEquiv_eps_comp` is stated for a restriction to the
slice site over an arbitrary object of an arbitrary ringed site, so it applies at the site
`(X.Opens)/V` verbatim: its terminal object is `V` over itself
(`CategoryTheory.Over.mkIdTerminal`), its "global sections over the terminal object" are the
sections over `V`, and its "sections over `U`" at `U = Over.mk (homOfLE hV')` are the sections
over `V'`. So the bridge one level down reads the twice-restricted twisted section as a section
over `V'`, and says it is the restriction of the section over `V`.

## Main definitions

* `Stacks.TwistedSections.nestedUnitHomAddEquiv`: **the bridge at the iterated slice** —
  morphisms out of the monoidal unit of the modules on the iterated slice site into the
  twice-restricted `ℱ` are the sections of `ℱ` over `V'`.
* `Stacks.TwistedSections.localizationLiftNestedSections`: **Tag 0B5L's comparison map over `V'`,
  landing in `Γ(ℱ, V')`**.

## Main results

* `Stacks.TwistedSections.nestedUnitHomAddEquiv_mapTwistSections`: carrying a degree-zero twisted
  section on the slice site over `V` along the second restriction and reading the result as a
  section over `V'` gives the restriction to `V'` of the section over `V`.
* `Stacks.TwistedSections.localizationLiftNestedSections_apply`: **the compatibility Stacks Tag
  0B5I's field `app_restrict` needs for a fixed section** — the comparison map over `V'`, read as
  a section of `ℱ`, is the restriction to `V'` of the comparison map over `V`. This holds for
  every element of the degree-zero localization, not only for the fractions, because
  `Stacks.TwistedSections.localizationLiftOverNestedOpen_eq` is an identity of maps.

## Implementation notes

**Both sides of the identification are definitional, and that is why the instantiation is a
one-liner.** The sections of the twice-restricted `ℱ` over the terminal object of the iterated
slice site are `Γ(ℱ, V')`, and the restriction along the unique arrow to that terminal object is
the restriction along `homOfLE hV'`, both because restriction to a slice site is pushforward
along `CategoryTheory.Over.forget` and therefore only reindexes components. No transport is
written down anywhere in this file.

**What this does *not* supply, and what superseded it.** Tag 0B5I's `app_restrict` compares the
comparison maps at two *different* homogeneous elements `p` and `q` of possibly different degrees
with `D₊(q) ≤ D₊(p)`. Shrinking the open is only half of that; the other half — the module
analogue of `Stacks.SectionRingChartOpen.chartRingMap_comp_awayMap` — is now
`Stacks.TwistedSections.openDivision_gsmul_changeGenerator`
(`StacksFrontier/AlgebraicGeometry/TwistedSectionModule/DivisionGeneratorChange.lean`).

The shrink proved here lands on the **iterated** slice site over `(V, V')`, while the local map
at a second generator lives on the slice site over `V'`, and nothing identifies the two monoidal
restrictions. That is why `Stacks.TwistedSections.openDivision_restrict`
(`StacksFrontier/AlgebraicGeometry/TwistedSectionModule/OpenRestrictionShrink.lean`) proves the
shrink again, in the
single-slice spelling the local datum consumes, by taking the multiplication out of the slice
site altogether: it is the morphism `Stacks.TwistedSections.twistMul` of `𝒪_X`-modules, and a
morphism commutes with every restriction by naturality. The statement here is kept because it is
the honest reading of `Stacks.TwistedSections.localizationLiftOverNestedOpen_eq` on sections and
because the generality of `overTensorUnitHomAddEquiv_eps_comp` it exercises is what makes the
slice-unit bridge available at an iterated slice.

## References

* [Stacks Project, Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L)
* [Stacks Project, Tag 0B5I](https://stacks.math.columbia.edu/tag/0B5I)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite DirectSum
open Stacks.GradedSections (powSections)
open Stacks.TensorPowers (natTensorPow)
open Stacks.SheafOfModules.TensorSheafification

universe u

namespace Stacks.TwistedSections

open Stacks.SheafInternalHom.SliceRestriction (schemeOpenRestriction schemeOverFunctorMonoidal
  schemeOpenUnitHomAddEquiv overTensorUnitHomAddEquiv)
open Stacks.SheafOfModules.SliceRestriction (sliceRingPresheaf sliceStructureSheaf
  isSheaf_sliceRingPresheaf)
open Stacks.SheafInternalHom (isSheaf_structureRingPresheaf)
open Stacks.SectionProduct (globalSection)

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
  schemeOpenRestrictionNestedMonoidal

variable {X : Scheme.{u}}

/-- **The slice-unit bridge at the iterated slice site:** a morphism out of the monoidal unit of
the modules on the slice site of `(X.Opens)/V` over `Over.mk (homOfLE hV')`, into the
twice-restricted `ℱ`, is a section of `ℱ` over `V'`. This is
`Stacks.SheafInternalHom.SliceRestriction.overTensorUnitHomAddEquiv` at that site, with no new
sheaf theory. -/
def nestedUnitHomAddEquiv {V V' : X.Opens} (hV' : V' ≤ V) (F : X.Modules) :
    ((𝟙_ (SheafOfModules.{u} (sliceStructureSheaf (sliceRingPresheaf X.presheaf V)
        (isSheaf_sliceRingPresheaf X.presheaf (isSheaf_structureRingPresheaf X) V)
        (Over.mk (homOfLE hV'))))) ⟶
      (schemeOpenRestrictionNested hV').obj ((schemeOpenRestriction X V).obj F)) ≃+ Γ(F, V') :=
  overTensorUnitHomAddEquiv (sliceRingPresheaf X.presheaf V)
    (isSheaf_sliceRingPresheaf X.presheaf (isSheaf_structureRingPresheaf X) V)
    (Over.mk (homOfLE hV')) ((schemeOpenRestriction X V).obj F)

/-- **Carrying a degree-zero twisted section to the smaller open restricts its section.** For `t`
a morphism out of the monoidal unit of the modules on the slice site over `V`, carrying `t` along
the second restriction and reading the result as a section of `ℱ` over `V'` gives the restriction
to `V'` of the section of `ℱ` over `V` that `t` reads as.

This is `Stacks.TwistedSections.overTensorUnitHomAddEquiv_eps_comp` at the site `(X.Opens)/V`,
whose terminal object is `CategoryTheory.Over.mkIdTerminal`; the degree-zero twisted section is
turned into the composite of the lax unit with the image exactly as in
`schemeOpenUnitHomAddEquiv_mapTwistSections` one level up. -/
theorem nestedUnitHomAddEquiv_mapTwistSections {V V' : X.Opens} (hV' : V' ≤ V) (F L : X.Modules)
    (t : twistSections ((schemeOpenRestriction X V).obj F)
      ((schemeOpenRestriction X V).obj L) 0) :
    nestedUnitHomAddEquiv hV' F (mapTwistSections (schemeOpenRestrictionNested hV') t)
      = F.val.map (homOfLE hV').op (schemeOpenUnitHomAddEquiv V F t) := by
  rw [show mapTwistSections (schemeOpenRestrictionNested hV') t
        = Functor.LaxMonoidal.ε (schemeOpenRestrictionNested hV') ≫
          (schemeOpenRestrictionNested hV').map t from
      congrArg (fun z => Functor.LaxMonoidal.ε (schemeOpenRestrictionNested hV') ≫ z)
        (Category.comp_id ((schemeOpenRestrictionNested hV').map t))]
  exact overTensorUnitHomAddEquiv_eps_comp (sliceRingPresheaf X.presheaf V)
    (isSheaf_sliceRingPresheaf X.presheaf (isSheaf_structureRingPresheaf X) V)
    (Over.mk (homOfLE hV')) Over.mkIdTerminal ((schemeOpenRestriction X V).obj F) t

/-- **Stacks Tag 0B5L's comparison map over the smaller open, landing in `Γ(ℱ, V')`.** This is
`Stacks.TwistedSections.localizationLiftOverNestedOpen` read through the bridge
`nestedUnitHomAddEquiv`, the shape Stacks Tag 0B5I's local data asks for. -/
def localizationLiftNestedSections (F L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    {d : ℕ} (s : powSections L d) {V V' : X.Opens}
    (hV : V ≤ Stacks.NonvanishingOpen.nonvanishingOpen X (natTensorPow L d)
      (globalSection X _ s)) (hV' : V' ≤ V) :
    sectionAtNonvanishingOpenOfDegree F L s →+ Γ(F, V') :=
  (nestedUnitHomAddEquiv hV' F).toAddMonoidHom.comp
    (localizationLiftOverNestedOpen F L s hV hV')

/-- **The compatibility with shrinking the open, at the level of sections.** The comparison map
over `V'` applied to any element of the degree-zero localization is the restriction to `V'` of the
comparison map over `V` applied to it. This is the content of Stacks Tag 0B5I's field
`Stacks.AlgebraicGeometry.ProjTwistComparison.StandardOpenHomData.app_restrict` for a fixed
section `s`, and it holds for every element and not only for the fractions, because
`Stacks.TwistedSections.localizationLiftOverNestedOpen_eq` is an identity of maps. -/
theorem localizationLiftNestedSections_apply (F L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {d : ℕ} (s : powSections L d) {V V' : X.Opens}
    (hV : V ≤ Stacks.NonvanishingOpen.nonvanishingOpen X (natTensorPow L d)
      (globalSection X _ s)) (hV' : V' ≤ V) (x : sectionAtNonvanishingOpenOfDegree F L s) :
    localizationLiftNestedSections F L s hV hV' x
      = F.val.map (homOfLE hV').op (localizationLiftSections F L s V hV x) :=
  (congrArg (fun z => nestedUnitHomAddEquiv hV' F z)
      (DFunLike.congr_fun (localizationLiftOverNestedOpen_eq F L s hV hV') x)).trans
    (nestedUnitHomAddEquiv_mapTwistSections hV' F L (localizationLiftOverOpen F L s V hV x))

end Stacks.TwistedSections

end
