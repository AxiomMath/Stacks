module

public import StacksFrontier.AlgebraicGeometry.TwistedSectionModule.SectionMultiplication
public import StacksFrontier.AlgebraicGeometry.TwistedSectionModule.SliceSectionBridge

/-!
# Shrinking the open, in the spelling the local map over the smaller open is written in

Stacks Tag 0B5I's local datum is a family of maps indexed by the standard opens of `Proj`,
together with the compatibility
`Stacks.AlgebraicGeometry.ProjTwistComparison.StandardOpenHomData.app_restrict` under passing to
a smaller standard open. Half of that compatibility is: at a *fixed* generator `s`, the
comparison map over a smaller open `V' ≤ V` is the comparison map over `V` followed by
restriction. **This file proves it.**

`StacksFrontier/AlgebraicGeometry/TwistedSectionModule/NestedOpenRestriction.lean` proves the same
statement with the map over `V'` built on the **iterated** slice site — the slice of
`(X.Opens)/V` over `Over.mk (homOfLE hV')` — because that is where
`Stacks.TwistedSections.monoidalDivision_comp` puts it. The local datum, and the local map at a
second generator, live instead on the slice site over `V'`, and **nothing in the tree identifies
the two monoidal restrictions**: the comparison of the two sites is
`CategoryTheory.Over.iteratedSliceBackward`, along which
`Stacks.SheafOfModules.overFunctor_comp_sliceBackward` is an equality of functors by `rfl`, but
`Stacks.TwistedSections.shiftPow` and `monoidalDivision` are defined from the *monoidal*
structure of the restriction and the two monoidal structures are not identified. That was
recorded as the obstruction to Tag 0B5I's morphism, and it is the obstruction to *that route*.

**The route here does not cross two sites at all.** Multiplication by `sⁿ` is a morphism
`Stacks.TwistedSections.twistMul ℱ sⁿ : ℱ ⟶ ℱ ⊙ (d n)` of `𝒪_X`-modules
(`StacksFrontier/AlgebraicGeometry/TwistedSectionModule/SectionMultiplication.lean`), and
`twistMul_app_openDivision` says the division over `V` is its inverse on the sections over `V`.
A morphism of `𝒪_X`-modules commutes with every restriction map by naturality, and over `V'` the
multiplication is still injective — because `Stacks.TwistedSections.bijective_shiftPow` applies
on the one slice site over `V'`. Those three facts give the compatibility with no comparison of
sites, no iterated slice, and no formula for any tensorator.

## Main results

* `Stacks.TwistedSections.schemeOpenUnitHomAddEquiv_comp`: the slice-unit bridge is natural in
  the module; by `rfl`.
* `Stacks.TwistedSections.twistMul_app_openDivision`: **the division over `V` is the inverse of
  the `X`-level multiplication by `sⁿ`, on the sections over `V`.**
* `Stacks.TwistedSections.openDivision_restrict`: **the division over a smaller open is the
  restriction of the division**, with both maps on the slice site over the open they live on.
* `Stacks.TwistedSections.localizationLiftSections_restrict`: the same for Stacks Tag 0B5L's
  comparison map, on the whole degree-zero localization rather than on the numerators.

## Implementation notes

**What this leaves for `app_restrict`.** Together with
`Stacks.TwistedSections.openDivision_gsmul_changeGenerator`
(`StacksFrontier/AlgebraicGeometry/TwistedSectionModule/DivisionGeneratorChange.lean`), which compares the divisions at two
generators over a common open, the division side of Tag 0B5I's compatibility field is complete.
What is not here is the *source* side: the degree-zero restriction map
`Γ_*(X, ℱ, L)_{(p)} ⟶ Γ_*(X, ℱ, L)_{(q)}` of Stacks Tag 01M4 has to be computed on a fraction,
and the relation `qᴺ = y · p` that `openDivision_gsmul_changeGenerator` takes as a hypothesis has
to be produced from `D₊(q) ≤ D₊(p)`.

**The degree reductions.** `ℱ|_V ⊙ 0` and `ℱ|_V` are equal by `rfl` and not syntactically, so
the crossing is made explicitly, by `Stacks.TwistedSections.twistZeroIso`; see the implementation
notes of `StacksFrontier/AlgebraicGeometry/TwistedSectionModule/SectionMultiplication.lean`. The degree-zero section the
division produces is introduced by `obtain` at the reduced type, so that
`shiftPow_eq_comp_twistMul` matches it.

## References

* [Stacks Project, Tag 0B5I](https://stacks.math.columbia.edu/tag/0B5I)
* [Stacks Project, Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L)
* [Stacks Project, Tag 01M4](https://stacks.math.columbia.edu/tag/01M4)
-/
@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite DirectSum
open Stacks.GradedSections (powSections)
open Stacks.TensorPowers (natTensorPow)
open Stacks.TensorPowerTrivialize (resTop res_resTop)

universe u

namespace Stacks.TwistedSections

open Stacks.SheafInternalHom.SliceRestriction (schemeOpenRestriction schemeOverFunctorMonoidal
  schemeOpenUnitHomAddEquiv)
open Stacks.SheafOfModules.SliceRestriction (sliceRingPresheaf isSheaf_sliceRingPresheaf
  sliceStructureSheaf)
open Stacks.SectionProduct (globalSection)
open Stacks.AmpleFiniteAvoidance (nvOpen)

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

/-- **The slice-unit bridge is natural in the module.** Post-composing a morphism out of the
slice site's monoidal unit with the restriction of a morphism of `X.Modules` is, on the sections
over `V`, that morphism applied to the section. Both sides are the value at the terminal object
of a composite of morphisms of presheaves of modules, so this is `rfl`. -/
theorem schemeOpenUnitHomAddEquiv_comp (V : X.Opens) {M N : X.Modules} (φ : M ⟶ N)
    (w : 𝟙_ (SheafOfModules.{u} (sliceStructureSheaf X.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) V)) ⟶
      (schemeOpenRestriction X V).obj M) :
    schemeOpenUnitHomAddEquiv V N (w ≫ (schemeOpenRestriction X V).map φ) =
      Scheme.Modules.Hom.app φ V (schemeOpenUnitHomAddEquiv V M w) := rfl

/-- The explicit crossing `ℱ|_V ⊙ 0 = ℱ|_V` of `Stacks.TwistedSections.twistZeroIso` is
invisible to the slice-unit bridge: it is an `eqToHom` on a pair of objects that are equal by
`rfl`, so composing with it is composing with the identity. -/
theorem schemeOpenUnitHomAddEquiv_twistZeroIso_inv (V : X.Opens) (F L : X.Modules)
    (w : twistSections ((schemeOpenRestriction X V).obj F)
      ((schemeOpenRestriction X V).obj L) 0) :
    schemeOpenUnitHomAddEquiv V F
        (w ≫ (twistZeroIso ((schemeOpenRestriction X V).obj F)
          ((schemeOpenRestriction X V).obj L)).inv) =
      schemeOpenUnitHomAddEquiv V F w :=
  congrArg (schemeOpenUnitHomAddEquiv V F) (Category.comp_id w)

/-- A degree-zero section `z` is the division of `t` by `sⁿ` on the slice site over `V` exactly
when `z` followed by the restricted multiplication by `sⁿ` is the restricted section `t`. -/
private theorem comp_twistMul_iff_shiftPow (F L : X.Modules) {d : ℕ} (s : powSections L d)
    (V : X.Opens) (n : ℕ) (t : twistSections F L (d * n))
    (z : twistSections ((schemeOpenRestriction X V).obj F)
      ((schemeOpenRestriction X V).obj L) 0) :
    (z ≫ (twistZeroIso ((schemeOpenRestriction X V).obj F)
          ((schemeOpenRestriction X V).obj L)).inv) ≫
        (schemeOpenRestriction X V).map (twistMul F (sectionPowOfDegree s n)) =
      Functor.LaxMonoidal.ε (schemeOpenRestriction X V) ≫
        (schemeOpenRestriction X V).map t ↔
    shiftPow (mapPowSections (schemeOpenRestriction X V) s) n z =
      mapTwistSections (schemeOpenRestriction X V) t := by
  rw [shiftPow_eq_comp_twistMul, ← mapPowSections_sectionPow, ← map_twistMul, mapTwistSections,
    ← cancel_mono (mapTwistPow (schemeOpenRestriction X V) F L (d * n))]
  simp only [Category.assoc]

/-- **The division over `V` is the inverse of the `X`-level multiplication by `sⁿ`, on the
sections over `V`.** The morphism `Stacks.TwistedSections.twistMul` is built on `X`, so it has a
value on the sections over *every* open and is compatible with every restriction; this identity
is what transfers the description of the division — stated inside the modules on the slice site
over `V` — to that morphism. -/
theorem twistMul_app_openDivision (F L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    {d : ℕ} (s : powSections L d) (V : X.Opens)
    (hV : V ≤ Stacks.NonvanishingOpen.nonvanishingOpen X (natTensorPow L d)
      (globalSection X _ s))
    (n : ℕ) (t : twistSections F L (d * n)) :
    Scheme.Modules.Hom.app (twistMul F (sectionPowOfDegree s n)) V
        (openDivision F L s V hV n t) =
      resTop (twistPow F L (d * n)) (globalSection X _ t) V := by
  have hiso := isIso_mapPowSections_openRestriction L s hV
  have hcomp : (monoidalDivision (schemeOpenRestriction X V) s n t ≫
        (twistZeroIso ((schemeOpenRestriction X V).obj F)
          ((schemeOpenRestriction X V).obj L)).inv) ≫
      (schemeOpenRestriction X V).map (twistMul F (sectionPowOfDegree s n)) =
        Functor.LaxMonoidal.ε (schemeOpenRestriction X V) ≫
          (schemeOpenRestriction X V).map t := by
    exact (comp_twistMul_iff_shiftPow F L s V n t _).mpr (shiftPow_monoidalDivision _ s n t)
  calc Scheme.Modules.Hom.app (twistMul F (sectionPowOfDegree s n)) V
          (openDivision F L s V hV n t)
      = Scheme.Modules.Hom.app (twistMul F (sectionPowOfDegree s n)) V
          (schemeOpenUnitHomAddEquiv V F
            (monoidalDivision (schemeOpenRestriction X V) s n t ≫
              (twistZeroIso ((schemeOpenRestriction X V).obj F)
                ((schemeOpenRestriction X V).obj L)).inv)) :=
        congrArg (Scheme.Modules.Hom.app (twistMul F (sectionPowOfDegree s n)) V)
          (schemeOpenUnitHomAddEquiv_twistZeroIso_inv V F L _).symm
    _ = schemeOpenUnitHomAddEquiv V (twistPow F L (d * n))
          ((monoidalDivision (schemeOpenRestriction X V) s n t ≫
              (twistZeroIso ((schemeOpenRestriction X V).obj F)
                ((schemeOpenRestriction X V).obj L)).inv) ≫
            (schemeOpenRestriction X V).map (twistMul F (sectionPowOfDegree s n))) :=
        (schemeOpenUnitHomAddEquiv_comp V (twistMul F (sectionPowOfDegree s n)) _).symm
    _ = resTop (twistPow F L (d * n)) (globalSection X _ t) V := by
        rw [hcomp]
        exact schemeOpenUnitHomAddEquiv_eps_comp V (twistPow F L (d * n)) t

/-- **The division over a smaller open is the restriction of the division**, at a fixed
generator and with *both* maps built on the slice site over the open they live on.

This is the half of Stacks Tag 0B5I's field
`Stacks.AlgebraicGeometry.ProjTwistComparison.StandardOpenHomData.app_restrict` that shrinks the
open. `Stacks.TwistedSections.localizationLiftNestedSections_apply` is the same statement with
the map over `V'` built on the *iterated* slice site over `(V, V')`; nothing identifies those two
monoidal restrictions, and this avoids the question entirely by comparing the two divisions
through the morphism `Stacks.TwistedSections.twistMul` of `X.Modules`, whose compatibility with
restriction is naturality and nothing else. -/
theorem openDivision_restrict (F L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    {d : ℕ} (s : powSections L d) {V V' : X.Opens}
    (hV : V ≤ Stacks.NonvanishingOpen.nonvanishingOpen X (natTensorPow L d)
      (globalSection X _ s))
    (hV' : V' ≤ V) (n : ℕ) (t : twistSections F L (d * n)) :
    openDivision F L s V' (hV'.trans hV) n t =
      F.presheaf.map (homOfLE hV').op (openDivision F L s V hV n t) := by
  have hiso := isIso_mapPowSections_openRestriction L s (hV'.trans hV)
  have hnat : Scheme.Modules.Hom.app (twistMul F (sectionPowOfDegree s n)) V'
        (F.presheaf.map (homOfLE hV').op (openDivision F L s V hV n t)) =
      (twistPow F L (d * n)).presheaf.map (homOfLE hV').op
        (Scheme.Modules.Hom.app (twistMul F (sectionPowOfDegree s n)) V
          (openDivision F L s V hV n t)) :=
    PresheafOfModules.naturality_apply (twistMul F (sectionPowOfDegree s n)).val (homOfLE hV').op
      (openDivision F L s V hV n t)
  have hsec : Scheme.Modules.Hom.app (twistMul F (sectionPowOfDegree s n)) V'
        (F.presheaf.map (homOfLE hV').op (openDivision F L s V hV n t)) =
      resTop (twistPow F L (d * n)) (globalSection X _ t) V' :=
    hnat.trans ((congrArg ((twistPow F L (d * n)).presheaf.map (homOfLE hV').op)
        (twistMul_app_openDivision F L s V hV n t)).trans
      (res_resTop (twistPow F L (d * n)) (globalSection X _ t) (homOfLE hV')))
  obtain ⟨z, hz⟩ : ∃ z : twistSections ((schemeOpenRestriction X V').obj F)
        ((schemeOpenRestriction X V').obj L) 0,
      schemeOpenUnitHomAddEquiv V' F z =
        F.presheaf.map (homOfLE hV').op (openDivision F L s V hV n t) :=
    ⟨(schemeOpenUnitHomAddEquiv V' F).symm _,
      (schemeOpenUnitHomAddEquiv V' F).apply_symm_apply _⟩
  have hcomp : (z ≫ (twistZeroIso ((schemeOpenRestriction X V').obj F)
          ((schemeOpenRestriction X V').obj L)).inv) ≫
      (schemeOpenRestriction X V').map (twistMul F (sectionPowOfDegree s n)) =
        Functor.LaxMonoidal.ε (schemeOpenRestriction X V') ≫
          (schemeOpenRestriction X V').map t := by
    refine (schemeOpenUnitHomAddEquiv V' (twistPow F L (d * n))).injective ?_
    rw [schemeOpenUnitHomAddEquiv_comp V' (twistMul F (sectionPowOfDegree s n)),
      schemeOpenUnitHomAddEquiv_twistZeroIso_inv V' F L z, hz, hsec,
      schemeOpenUnitHomAddEquiv_eps_comp V' (twistPow F L (d * n)) t]
  have hmd : monoidalDivision (schemeOpenRestriction X V') s n t = z :=
    (bijective_shiftPow (mapPowSections (schemeOpenRestriction X V') s)
      (F := (schemeOpenRestriction X V').obj F) n).injective
      ((shiftPow_monoidalDivision (schemeOpenRestriction X V') s n t).trans
        ((comp_twistMul_iff_shiftPow F L s V' n t z).mp hcomp).symm)
  exact (congrArg (schemeOpenUnitHomAddEquiv V' F) hmd).trans hz

/-- **Stacks Tag 0B5L's comparison map over a smaller open is the restriction of the comparison
map over the larger one**, as an identity on the whole degree-zero localization and with both
maps on the slice site over the open they live on. The two division families agree by
`openDivision_restrict`, and `Stacks.TwistedSections.localizationLift_congr` together with
`localizationLift_comp` promotes that to the maps. -/
theorem localizationLiftSections_restrict (F L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {d : ℕ} (s : powSections L d) {V V' : X.Opens}
    (hV : V ≤ Stacks.NonvanishingOpen.nonvanishingOpen X (natTensorPow L d)
      (globalSection X _ s))
    (hV' : V' ≤ V) :
    localizationLiftSections F L s V' (hV'.trans hV) =
      (F.presheaf.map (homOfLE hV').op).hom.comp
        (localizationLiftSections F L s V hV) := by
  rw [localizationLiftSections_eq F L s V' (hV'.trans hV),
    localizationLiftSections_eq F L s V hV]
  refine Eq.trans ?_ (localizationLift_comp
    (F.presheaf.map (homOfLE hV').op).hom s (openDivision F L s V hV)
    (isPowerInvariant_openDivision F L s V hV))
  exact localizationLift_congr s _ _
    fun n => AddMonoidHom.ext fun t => openDivision_restrict F L s hV hV' n t

end Stacks.TwistedSections

end
