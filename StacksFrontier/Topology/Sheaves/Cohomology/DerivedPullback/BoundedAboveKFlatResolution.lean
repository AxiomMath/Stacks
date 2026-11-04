module

public import StacksFrontier.Deformation.ToposThickening.FlatRepresentative
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.TensorProductCompatibility
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.OnARingedSpace

/-!
# A bounded above K-flat resolution, and the derived pullback of a complex in degrees `≤ a`

Let `(Y, 𝒪_Y)` be a ringed space. A complex of `𝒪_Y`-modules whose cohomology vanishes above `a`
receives a quasi-isomorphism from a K-flat complex of flat modules which is zero above `a`
([Stacks, Tag 05T7] and [Stacks, Tag 06YQ]). Consequently, for `g : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` and a
complex `K` of `𝒪_Y`-modules with `H^i(K) = 0` for `i > a`, the derived pullback `Lg^*K` of
[Stacks, Tag 06YJ] again has `H^i = 0` for `i > a`.

## Main results

* `Stacks.Cohomology.KFlatDerivedPullback.exists_boundedAbove_kFlatResolution`: a complex with
  no cohomology above `a` receives a quasi-isomorphism from a K-flat complex with no *terms*
  above `a`.
* `Stacks.Cohomology.KFlatDerivedPullback.isStrictlyLE_mapHomologicalComplex`: the degreewise
  pullback of a complex with no terms above `a` has no terms above `a`.
* `Stacks.Cohomology.KFlatDerivedPullback.isLE_derivedPullback_Q_obj`: **`Lg^*` carries an
  object of `D(𝒪_Y)` living in cohomological degrees `≤ a` to one living in degrees `≤ a`.**

## References

* [Stacks Project, Tag 05T7](https://stacks.math.columbia.edu/tag/05T7), resolutions by a class
  of objects, with bounds
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ), a bounded above complex
  of flat modules is K-flat
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ), the derived pullback
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace Stacks.Cohomology.KFlatDerivedPullback

attribute [local instance] HasDerivedCategory.standard

section Space

variable (Y : RingedSpace.{u, u})

/-- **A complex of `𝒪_Y`-modules with no cohomology above `a` has a K-flat resolution with no
terms above `a`**: there is a quasi-isomorphism `L ⟶ K` from a K-flat complex `L` which is zero
in every degree above `a`. -/
theorem exists_boundedAbove_kFlatResolution (a : ℤ)
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) [K.IsLE a] :
    ∃ (L : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) (l : L ⟶ K),
      QuasiIso l ∧ L.IsStrictlyLE a ∧ KFlatComplex Y L := by
  have : CochainComplex.IsLE
      (show CochainComplex (Deformation.ComplexLift.SheafMod.{u, u, u} Y.sheaf) ℤ from K) a :=
    inferInstanceAs (CochainComplex.IsLE K a)
  obtain ⟨L, l, hl, hPL, hLE⟩ :=
    Deformation.ComplexLift.exists_isFlat_quasiIso_isStrictlyLE_of_isLE.{u, u, u} Y.sheaf a K
  exact ⟨L, l, hl, hLE,
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.kFlat_of_boundedAbove_of_flat Y L
      ⟨a, hLE⟩ hPL⟩

end Space

variable {X Y : RingedSpace.{u, u}} (g : X ⟶ Y)

/-- The degreewise pullback of a complex with no terms above `a` has no terms above `a`. -/
theorem isStrictlyLE_mapHomologicalComplex (a : ℤ)
    (L : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) [L.IsStrictlyLE a] :
    CochainComplex.IsStrictlyLE
      (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj L) a := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact (modulePullback g).map_isZero (L.isZero_of_isStrictlyLE a i hi)

/-- **The derived pullback preserves "living in cohomological degrees `≤ a`".**  If `K` has no
cohomology above `a` then neither has `Lg^*K`. -/
theorem isLE_derivedPullback_Q_obj (a : ℤ)
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) [K.IsLE a] :
    ((derivedPullback g).obj (DerivedCategory.Q.obj K)).IsLE a := by
  obtain ⟨L, l, hl, hLE, hKF⟩ := exists_boundedAbove_kFlatResolution Y a K
  have := hl
  have := hLE
  have : IsIso (DerivedCategory.Q.map l) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ l).2 hl
  have := isStrictlyLE_mapHomologicalComplex g a L
  have e : (derivedPullback g).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj
        (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj L) :=
    (derivedPullback g).mapIso (asIso (DerivedCategory.Q.map l)).symm ≪≫
      Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackIsoOfKFlat g L hKF
  refine (DerivedCategory.isLE_iff _ a).2 fun i hi => ?_
  exact ((DerivedCategory.isLE_iff (DerivedCategory.Q.obj
    (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) a).1
      inferInstance i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e)

end Stacks.Cohomology.KFlatDerivedPullback

end
