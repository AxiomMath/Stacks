module

public import StacksFrontier.AlgebraicGeometry.TwistedSectionModule.OpenRestriction

/-!
# Shrinking the open on which Stacks Tag 0B5L's comparison map is defined

`StacksFrontier/AlgebraicGeometry/TwistedSectionModule/OpenRestriction.lean` builds Stacks Tag
0B5L's comparison map `Γ_*(X, ℱ, L)_{(s)} ⟶ Γ(V, ℱ)` for an open `V` inside the nonvanishing open
of a global section `s` of `L ^⊗ d`. The local data of Stacks Tag 0B5I asks for that map on every
positive-degree standard open of `Proj Γ_*(X, L)` **together with its compatibility under passing
to a smaller standard open**, and the smaller open is where the construction has to be re-run.
This file supplies the re-run and the compatibility.

The point is that the second restriction needs no new sheaf theory. For `V' ≤ V` the composite

```
X.Modules ⥤ (modules on the slice site over V)
  ⥤ (modules on the slice site over Over.mk (V' ≤ V))
```

is a composite of two restrictions **of the same kind**: the second is
`Stacks.SheafOfModules.SliceRestriction.overFunctor` at the site `(X.Opens)/V` and the object
`Over.mk (homOfLE hV')`, so `Stacks.SheafInternalHom.SliceRestriction.overFunctorMonoidal`
applies to it verbatim and makes it monoidal, and the composite is monoidal because a composite
of monoidal functors is. Nothing has to be said about the tensorator of either factor, and in
particular `Stacks.SheafOfModules.overMap` — restriction along an arrow of the site, which is
what one reaches for first and for which no monoidal structure exists in this repository — is not
used.

The whole twisted-section construction is then carried along the composite by the four
composition laws of
`StacksFrontier/AlgebraicGeometry/TwistedSectionModule/MonoidalFunctor.lean`
(`Stacks.TwistedSections.mapNatTensorPow_comp` and its three companions), and the division by the
powers of `s` by `Stacks.TwistedSections.monoidalDivision_comp` and
`localizationLiftOfMonoidal_comp`.

## Main definitions

* `Stacks.TwistedSections.schemeOpenRestrictionNested`: restriction from the slice site over `V`
  to the slice site over `V' ≤ V`, read as an object of `(X.Opens)/V`.
* `Stacks.TwistedSections.schemeOpenRestrictionNestedMonoidal` and
  `schemeOpenRestrictionNestedAdditive`: that restriction is monoidal and additive, by
  instantiation of the statements already proved for a restriction to a slice site.
* `Stacks.TwistedSections.localizationLiftOverNestedOpen`: **Stacks Tag 0B5L's comparison map
  over the smaller open**, with no geometric hypothesis beyond the one already made for `V`.

## Main results

* `Stacks.TwistedSections.isIso_mapPowSections_nestedOpenRestriction`: the section `s` stays
  invertible after the composite. This needs no nonvanishing hypothesis at `V'`: `s` is already
  an isomorphism after restriction to `V`, and a functor carries an isomorphism to an
  isomorphism.
* `Stacks.TwistedSections.shiftPow_localizationLiftOverNestedOpen_mk`: Tag 0B5L's own description
  of the map over the smaller open — the value on `t / sⁿ` is the section whose `n`-fold product
  with the image of `s` is the image of `t`.
* `Stacks.TwistedSections.localizationLiftOverNestedOpen_eq`: **the compatibility** — the
  comparison map over `V'` *is* the comparison map over `V` followed by restriction to `V'`, as
  an identity of maps on the whole degree-zero localization. This is the content of Tag 0B5I's
  compatibility field
  `Stacks.AlgebraicGeometry.ProjTwistComparison.StandardOpenHomData.app_restrict` for a fixed
  section `s`.

## Implementation notes

**The compatibility is an identity of maps, and needs no surjectivity of the fractions.**
`Stacks.TwistedSections.localizationLiftOfDegree` depends on its division family and on a
`Prop`-valued power-invariance witness only, so an identity between two families —
`Stacks.TwistedSections.monoidalDivision_comp`, proved degreewise — lifts to an identity between
the comparison maps by `Stacks.TwistedSections.localizationLift_congr`. Nothing is said about
`LocalizedModule`.

**The invertibility of `s` after the composite is passed explicitly, twice.** Instance search
does not find `Stacks.TwistedSections.isIso_mapPowSections` for the second restriction even with
the hypothesis `letI`-bound in context — the same failure that
`Stacks.TwistedSections.isIso_mapPowSections_openRestriction` already works around — so that
lemma is applied with its arguments given by `@`. The facts introduced that way are `Prop`-valued,
so `have` registers them as local instances and no `haveI` is needed. For the same reason no
statement in this file carries an `IsIso` instance argument whose subject mentions the second
restriction: each is phrased through `Stacks.TwistedSections.localizationLiftOverNestedOpen` or
`Stacks.TwistedSections.mapTwistSectionsHom`, which need none, rather than through
`Stacks.TwistedSections.monoidalDivision`, which does and would therefore have to be synthesized
while the *statement* is elaborated, before any tactic can introduce it.

## References

* [Stacks Project, Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L)
* [Stacks Project, Tag 0B5I](https://stacks.math.columbia.edu/tag/0B5I)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite DirectSum
open Stacks.GradedSections (powSections)
open Stacks.TensorPowers (natTensorPow)

universe u

namespace Stacks.TwistedSections

open Stacks.SheafInternalHom.SliceRestriction (schemeOpenRestriction schemeOverFunctorMonoidal)
open Stacks.SheafOfModules.SliceRestriction (sliceRingPresheaf sliceStructureSheaf
  isSheaf_sliceRingPresheaf)
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

variable {X : Scheme.{u}}

/-- **Restriction from the slice site over `V` to the slice site over a smaller open `V'`**,
read as restriction to the object `Over.mk (homOfLE hV')` of the site `(X.Opens)/V`. This is
`Stacks.SheafOfModules.SliceRestriction.overFunctor` at that site, which is why everything proved
for a restriction to a slice site applies to it unchanged. -/
abbrev schemeOpenRestrictionNested {V V' : X.Opens} (hV' : V' ≤ V) :
    SheafOfModules.{u} (sliceStructureSheaf X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) V) ⥤
    SheafOfModules.{u} (sliceStructureSheaf (sliceRingPresheaf X.presheaf V)
      (isSheaf_sliceRingPresheaf X.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) V) (Over.mk (homOfLE hV'))) :=
  Stacks.SheafOfModules.SliceRestriction.overFunctor (sliceRingPresheaf X.presheaf V)
    (isSheaf_sliceRingPresheaf X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) V) (Over.mk (homOfLE hV'))

/-- **The second restriction is monoidal**, by
`Stacks.SheafInternalHom.SliceRestriction.overFunctorMonoidal` at the site `(X.Opens)/V`. No new
sheaf theory: the hypotheses of that statement — that the restricted structure presheaf is a
sheaf, and the two sheafification hypotheses on the site and its slice — are satisfied at the
slice site by `Stacks.SheafOfModules.SliceRestriction.isSheaf_sliceRingPresheaf` and by instance
search. -/
@[instance_reducible]
def schemeOpenRestrictionNestedMonoidal {V V' : X.Opens} (hV' : V' ≤ V) :
    (schemeOpenRestrictionNested hV').Monoidal :=
  Stacks.SheafInternalHom.SliceRestriction.overFunctorMonoidal
    (sliceRingPresheaf X.presheaf V)
    (isSheaf_sliceRingPresheaf X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) V)
    (Over.mk (homOfLE hV'))

/-- The second restriction is additive: it reindexes the components of a morphism. -/
instance schemeOpenRestrictionNestedAdditive {V V' : X.Opens} (hV' : V' ≤ V) :
    (schemeOpenRestrictionNested hV').Additive :=
  Stacks.SheafOfModules.SliceFinite.additive_overFunctor
    (Rs := Stacks.SheafOfModules.TensorSheafification.structureSheaf
      (sliceRingPresheaf X.presheaf V)
      (isSheaf_sliceRingPresheaf X.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) V))
    (Over.mk (homOfLE hV'))

attribute [local instance] schemeOpenRestrictionNestedMonoidal

/-- **The hypothesis of Stacks Tag 0B5L's comparison map for the composite of two restrictions,
discharged with no nonvanishing hypothesis at the smaller open.** After restriction to `V` the
section `s` is already an isomorphism
(`Stacks.TwistedSections.isIso_mapPowSections_openRestriction`), a functor carries an isomorphism
to an isomorphism, and `Stacks.TwistedSections.isIso_mapPowSections_comp` transfers the
conclusion from the second factor to the composite. -/
theorem isIso_mapPowSections_nestedOpenRestriction (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {n : ℕ} (s : powSections L n) {V V' : X.Opens}
    (hV : V ≤ Stacks.NonvanishingOpen.nonvanishingOpen X (natTensorPow L n)
      (globalSection X _ s)) (hV' : V' ≤ V) :
    IsIso (mapPowSections (schemeOpenRestriction X V ⋙ schemeOpenRestrictionNested hV') s) := by
  have := isIso_mapPowSections_openRestriction L s hV
  have h₂ : IsIso ((schemeOpenRestrictionNested hV').map
      (mapPowSections (schemeOpenRestriction X V) s)) := Functor.map_isIso _ _
  have := @isIso_mapPowSections _ _ _ _ _ _ (schemeOpenRestrictionNested hV') _ _ _
    (mapPowSections (schemeOpenRestriction X V) s) h₂
  exact isIso_mapPowSections_comp (schemeOpenRestriction X V)
    (schemeOpenRestrictionNested hV') s

/-- **Stacks Tag 0B5L's comparison map over an open smaller than the one it was built on.** The
degree-zero localization `Γ_*(X, ℱ, L)_{(s)}` maps to the degree-zero twisted sections of `ℱ`
restricted twice, for every `V' ≤ V` with `V` inside the nonvanishing open of `s`. -/
def localizationLiftOverNestedOpen (F L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    {d : ℕ} (s : powSections L d) {V V' : X.Opens}
    (hV : V ≤ Stacks.NonvanishingOpen.nonvanishingOpen X (natTensorPow L d)
      (globalSection X _ s)) (hV' : V' ≤ V) :
    sectionAtNonvanishingOpenOfDegree F L s →+
      twistSections ((schemeOpenRestriction X V ⋙ schemeOpenRestrictionNested hV').obj F)
        ((schemeOpenRestriction X V ⋙ schemeOpenRestrictionNested hV').obj L) 0 :=
  haveI := isIso_mapPowSections_nestedOpenRestriction L s hV hV'
  localizationLiftOfMonoidal (schemeOpenRestriction X V ⋙ schemeOpenRestrictionNested hV')
    (F := F) s

/-- **Stacks Tag 0B5L's description of its map, over the smaller open:** the value on `t / sⁿ` is
the twisted section whose `n`-fold product with the twice-restricted `s` is the twice-restricted
`t`. -/
theorem shiftPow_localizationLiftOverNestedOpen_mk (F L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {d : ℕ} (s : powSections L d) {V V' : X.Opens}
    (hV : V ≤ Stacks.NonvanishingOpen.nonvanishingOpen X (natTensorPow L d)
      (globalSection X _ s)) (hV' : V' ≤ V)
    (n : ℕ) (t : twistSections F L (d * n)) :
    shiftPow (mapPowSections (schemeOpenRestriction X V ⋙ schemeOpenRestrictionNested hV') s) n
        (localizationLiftOverNestedOpen F L s hV hV'
          (⟨LocalizedModule.mk (DirectSum.of (twistSections F L) (d * n) t)
              (⟨homogeneousSectionOfDegree s ^ n, ⟨n, rfl⟩⟩ :
                Submonoid.powers (homogeneousSectionOfDegree s)),
            mk_mem_sectionAtNonvanishingOpenOfDegree s n t⟩ :
              sectionAtNonvanishingOpenOfDegree F L s)) =
      mapTwistSections (schemeOpenRestriction X V ⋙ schemeOpenRestrictionNested hV') t :=
  have := isIso_mapPowSections_nestedOpenRestriction L s hV hV'
  shiftPow_localizationLiftOfMonoidal_mk
    (schemeOpenRestriction X V ⋙ schemeOpenRestrictionNested hV') s n t

/-- **The compatibility under shrinking the open:** Tag 0B5L's comparison map over `V'` *is* the
comparison map over `V` followed by restriction to `V'` — as an identity of maps on the whole
degree-zero localization, not only on the fractions. This is the content of the field
`Stacks.AlgebraicGeometry.ProjTwistComparison.StandardOpenHomData.app_restrict` of Tag 0B5I's
local data, for a fixed section `s`.

It is `Stacks.TwistedSections.localizationLiftOfMonoidal_comp` with `G` the restriction to `V`
and `H` the second slice restriction, so no tensorator component is touched: the two divisions
agree degreewise by `Stacks.TwistedSections.monoidalDivision_comp`, and
`Stacks.TwistedSections.localizationLift_congr` promotes that to the lifts. -/
theorem localizationLiftOverNestedOpen_eq (F L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {d : ℕ} (s : powSections L d) {V V' : X.Opens}
    (hV : V ≤ Stacks.NonvanishingOpen.nonvanishingOpen X (natTensorPow L d)
      (globalSection X _ s)) (hV' : V' ≤ V) :
    localizationLiftOverNestedOpen F L s hV hV'
      = (mapTwistSectionsHom (schemeOpenRestrictionNested hV')
          (F := (schemeOpenRestriction X V).obj F)
          (L := (schemeOpenRestriction X V).obj L) 0).comp
        (localizationLiftOverOpen F L s V hV) := by
  have := isIso_mapPowSections_openRestriction L s hV
  have := isIso_mapPowSections_nestedOpenRestriction L s hV hV'
  exact localizationLiftOfMonoidal_comp (schemeOpenRestriction X V)
    (schemeOpenRestrictionNested hV') s

end Stacks.TwistedSections

end
