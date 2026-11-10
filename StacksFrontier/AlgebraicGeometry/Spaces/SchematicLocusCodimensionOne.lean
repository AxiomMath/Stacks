module

public import StacksCore.Tactic.StacksAttribute
public import StacksCore.Topology.Maps.SubmersiveClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.GenericPointsAndDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.LocalRingDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence

/-!
# Inputs for the schematic locus of a separated space in codimension one

Three steps of the proof of [Stacks, Tag 0ADD] — that a point of an algebraic space which is
separated, locally Noetherian and of local dimension at most one has an open neighbourhood
which is a scheme — are assembled here, following the source's route. No tag is registered in
this file: each declaration is one step of that route. Tag 0ADD itself is proved, by a different
route that avoids [Stacks, Tag 09YC] and [Stacks, Tag 07VP], as
`AlgebraicGeometry.Space.exists_isOpenSubspace_isRepresentable_of_localRingDimension_le_one`
(`StacksFrontier/AlgebraicGeometry/Spaces/CodimensionOneSchematicLocus.lean`), and
[Stacks, Tag 0E7R] as
`AlgebraicGeometry.Space.exists_isProjective_algebraization_of_dimension_le_one`
(`StacksFrontier/AlgebraicGeometry/FormalGeometry/FormalCurve/SpaceAlgebraization.lean`).

The source argues as follows. Replace the space `X` by a quasi-compact neighbourhood of the
point `x`, so that `X` is quasi-compact, separated and Noetherian. Choose a scheme `U` and a
finite surjective morphism `g : U ⟶ X` ([Stacks, Tag 09YC]) and let `R = U ×_X U`, a groupoid
scheme `(U, R, s, t, c)` with `s` and `t` finite and `U` Noetherian and separated. The fibre
of `|U| → |X|` over `x` consists of points whose local rings have dimension at most one
([Stacks, Tag 0ABW]), so [Stacks, Tag 0ABI] puts that fibre inside an `R`-invariant affine
open `W ⊆ U`. Because `g` is finite and surjective the map `|U| → |X|` is closed and
surjective, hence submersive ([Stacks, Tag 0AAU]), so the image of `W` is open and cuts out an
open subspace `X' ⊆ X` with `W → X'` finite surjective; then `X'` is an affine scheme by
[Stacks, Tag 07VP].

## Main results

* `AlgebraicGeometry.Space.krullDimLE_one_stalk_of_localRingDimension_le_one` is the
  dimension step: for a finite morphism `g` from (the functor of points of) a scheme `U` and a
  point `x` of the target of local dimension at most one, the stalk of `U` at any point over
  `x` has Krull dimension at most one. This is exactly the hypothesis that
  `AlgebraicGeometry.GroupoidScheme.exists_isInvariantOpen_isAffineOpen_mem_of_krullDimLE_one`
  ([Stacks, Tag 0ABI]) asks for, so it is what connects 0ABI to 0ADD.
* `AlgebraicGeometry.Space.isOpen_image_pointsMap_of_isFinite_of_isSurjective` is the
  submersivity step: along a finite surjective morphism of algebraic spaces, a saturated open
  subset of the space of points of the source has open image.
* `AlgebraicGeometry.Space.isPullback_of_isOpenImmersion_of_preimage_range` is the step which
  recognises the open subspace cut out by a saturated open as a base change: an open immersion
  whose range is the full preimage of an open subspace sits in a cartesian square over that
  open subspace. It is what transports finiteness of `g` to finiteness of the restricted
  morphism.

## Implementation notes

The dimension step is stated for a point `y` of the source together with the identification of
its image, rather than for a fibre, because that is the form in which the orbit hypothesis of
0ABI is discharged: the orbit of a point of `U` over `x` is contained in the fibre of
`|U| → |X|` over `x`. Local dimension is `AlgebraicGeometry.Space.localRingDimension`
([Stacks, Tag 04NA]) and the comparison along the finite — hence locally quasi-finite —
morphism `g` is `AlgebraicGeometry.Space.localRingDimension_le_of_isLocallyQuasiFinite`
([Stacks, Tag 0ABW]). The passage from that to `Ring.KrullDimLE 1` on a stalk of the scheme
`U` goes through `AlgebraicGeometry.Space.hasChartLocalRingDimension_iff_ringKrullDim_stalk`
read at the identity chart of `U`, which is the spelling 0ABI uses.

The submersivity step is 0AAU in the form in which Mathlib has it: a surjective continuous
closed map is a quotient map, and for a quotient map a set is open exactly when its preimage
is. Closedness of the map on points comes from finiteness through
`AlgebraicGeometry.Space.isFinite_iff_isAffineHom_and_isProper` ([Stacks, Tag 04NZ]) and
`AlgebraicGeometry.Space.isClosed_of_universallyClosed`; continuity is part of the point
topology of [Stacks, Tag 03BX]. Saturation is the hypothesis that the open set is its own
preimage under the image map, which for the invariant open of 0ABI is exactly invariance.

### The source's route and the route taken

A tag counts as formalized in this repository only on a declaration which proves it under the
source's own hypotheses, so none of the three steps below carries a registration. Along the
source's route the steps would be completed by [Stacks, Tag 09YC] part (1), the finite
surjective cover of a quasi-compact quasi-separated space by a scheme, and [Stacks, Tag 07VP],
the affineness criterion for a Noetherian space receiving a finite surjective morphism from an
affine scheme. The proof of Tag 0ADD in
`StacksFrontier/AlgebraicGeometry/Spaces/CodimensionOneSchematicLocus.lean` produces the finite
cover only near the point, by an induction on the degree of an étale chart at the
codimension-zero points
(`StacksFrontier/AlgebraicGeometry/Spaces/CodimensionOneChartInduction.lean`),
and so needs neither input. The first line of the proof of [Stacks, Tag 0E7R] is Tag 0ADD applied
to `X₁`; the remaining steps of 0E7R are the scheme form of the algebraization of formal curves,
`Stacks.FormalCurve.exists_isProjectiveMorphism_of_topologicalKrullDim_le_one`.

## References

* [Stacks Project, Tag 0ADD](https://stacks.math.columbia.edu/tag/0ADD)
* [Stacks Project, Tag 0ABI](https://stacks.math.columbia.edu/tag/0ABI)
* [Stacks Project, Tag 0ABW](https://stacks.math.columbia.edu/tag/0ABW)
* [Stacks Project, Tag 0AAU](https://stacks.math.columbia.edu/tag/0AAU)
* [Stacks Project, Tag 04NA](https://stacks.math.columbia.edu/tag/04NA)
* [Stacks Project, Tag 09YC](https://stacks.math.columbia.edu/tag/09YC)
* [Stacks Project, Tag 07VP](https://stacks.math.columbia.edu/tag/07VP)
* [Stacks Project, Tag 0E7R](https://stacks.math.columbia.edu/tag/0E7R)
* [Stacks Project, Tag 0A26](https://stacks.math.columbia.edu/tag/0A26)
* [Stacks Project, Tag 089A](https://stacks.math.columbia.edu/tag/089A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
private instance (priority := high) hasPullback_presheaf_schematicLocusCodimensionOne
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- The dimension step of [Stacks, Tag 0ADD]. Let `g` be a finite morphism from the functor of
points of a scheme `U` to an algebraic space `X`, and let `x` be a point of `X` whose local
ring has dimension at most one. Then the stalk of `U` at any point lying over `x` has Krull
dimension at most one.

This is [Stacks, Tag 0ABW] read through the identity chart of `U`, and it is the orbit
hypothesis of [Stacks, Tag 0ABI]. No tag is registered: see the module documentation. -/
theorem krullDimLE_one_stalk_of_localRingDimension_le_one
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (U : BigFppfOver B S hS) (g : yoneda.obj U ⟶ X) (hg : IsFinite B S hS g)
    (x : points B S hS X) (hdim : localRingDimension B S hS x ≤ 1)
    (y : points B S hS (yoneda.obj U))
    (hy : pointsMap B S hS (yoneda.obj U) g y = x) :
    Ring.KrullDimLE 1
      (((BigFppfOver.toScheme B S hS).obj U).presheaf.stalk
        (pointsToScheme B S hS U y)) := by
  have hUalg : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have hqf : IsQuasiFinite B S hS g := isQuasiFinite_of_isFinite B S hS g hUalg hX hg
  have hle : localRingDimension B S hS y ≤ 1 := by
    have h := localRingDimension_le_of_isLocallyQuasiFinite B S hS hUalg hX g hqf.1 y
    rw [hy] at h
    exact h.trans hdim
  have hchart : ChartPoint B S hS U (𝟙 (yoneda.obj U)) (pointsToScheme B S hS U y) y := by
    have h := chartPoint_pointsToScheme B S hS U (𝟙 (yoneda.obj U)) y
    rwa [pointsMap_id, id_eq] at h
  have hhas : HasChartLocalRingDimension B S hS y (localRingDimension B S hS y) :=
    (localRingDimension_eq_iff_hasChartLocalRingDimension B S hS hUalg y
      (localRingDimension B S hS y)).mp rfl
  have hring := (hasChartLocalRingDimension_iff_ringKrullDim_stalk B S hS U
    (pointsToScheme B S hS U y) y hchart (localRingDimension B S hS y)).mp hhas
  rw [Ring.krullDimLE_iff, hring]
  exact_mod_cast hle

/-- The submersivity step of [Stacks, Tag 0ADD]. Along a finite surjective morphism of
algebraic spaces the map on points is closed and surjective, hence a quotient map by
[Stacks, Tag 0AAU], so a saturated open subset of the space of points of the source has open
image. The saturation of the open set is the hypothesis `hsat`, which for the `R`-invariant
affine open of [Stacks, Tag 0ABI] is its invariance. No tag is registered: see the module
documentation. -/
@[sga "1 IX 2.2" "special case"]
theorem isOpen_image_pointsMap_of_isFinite_of_isSurjective
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (g : Y ⟶ X) (hgfin : IsFinite B S hS g)
    (hgsurj : IsSurjective B S hS g) (A : Set (points B S hS Y)) (hA : IsOpen A)
    (hsat : pointsMap B S hS Y g ⁻¹' (pointsMap B S hS Y g '' A) = A) :
    IsOpen (pointsMap B S hS Y g '' A) := by
  have hproper : IsProper B S hS g :=
    ((isFinite_iff_isAffineHom_and_isProper B S hS hY hX g).mp hgfin).2
  have hclosed : IsClosedMorphism B S hS g :=
    isClosed_of_universallyClosed B S hS hX g hproper.universallyClosed
  have hquot := IsClosedMap.isQuotientMap hclosed (continuous_pointsMap B S hS g) hgsurj
  rw [← hquot.isCoinducing.isOpen_preimage, hsat]
  exact hA

/-- The base-change step of [Stacks, Tag 0ADD]. An open immersion `j : W ⟶ U` of algebraic
spaces whose range in the points of the target of `g : U ⟶ V` is the full preimage of an open
subspace `H ⊆ V`, together with a factorisation `t` of `j ≫ g` through `H`, sits in a
cartesian square. So any property of `g` stable under base change passes to `t`. This is what
carries finiteness of `g` across to the restricted morphism in the clause "there is an open
subspace `X'` of `X` with `W → X'` a surjective finite morphism" of the proof of
[Stacks, Tag 0ADD]. No tag is registered: see the module documentation. -/
theorem isPullback_of_isOpenImmersion_of_preimage_range
    {W U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W)
    (hU : IsAlgebraicSpace B S hS U) (hV : IsAlgebraicSpace B S hS V)
    (j : W ⟶ U) (hj : IsOpenImmersion B S hS j) (g : U ⟶ V) (H : Subfunctor V)
    (hH : IsOpenSubspace B S hS H) (t : W ⟶ H.toFunctor) (ht : j ≫ g = t ≫ H.ι)
    (hrange : pointsMap B S hS U g ⁻¹'
        Set.range (pointsMap B S hS H.toFunctor H.ι) =
      Set.range (pointsMap B S hS W j)) :
    IsPullback j t g H.ι := by
  let : Mono j := mono_of_isOpenImmersion B S hS j hj
  have hP : IsAlgebraicSpace B S hS (pullback g H.ι) :=
    isAlgebraicSpace_pullback B S hS g H.ι hU hH.1 hV
  have hR : IsOpenSubspace B S hS (Subfunctor.range j) :=
    isOpenSubspace_subfunctorRange B S hS hW hj
  obtain ⟨l₀, hl₀⟩ := (factorsThrough_openSubspace_iff_points B S hS hU hP
      (Subfunctor.range j) hR (pullback.fst g H.ι)).2 (by
    rw [range_pointsMap_ι_range, ← hrange]
    rintro _ ⟨z, rfl⟩
    refine ⟨pointsMap B S hS (pullback g H.ι) (pullback.snd g H.ι) z, ?_⟩
    have h₁ := congrFun (pointsMap_comp B S hS (pullback g H.ι)
      (pullback.fst g H.ι) g) z
    have h₂ := congrFun (pointsMap_comp B S hS (pullback g H.ι)
      (pullback.snd g H.ι) H.ι) z
    have hc : pullback.fst g H.ι ≫ g = pullback.snd g H.ι ≫ H.ι := pullback.condition
    simp only [Function.comp_apply] at h₁ h₂
    rw [← h₂, ← hc]
    exact h₁)
  have hinv : inv (Subfunctor.toRange j) ≫ j = (Subfunctor.range j).ι :=
    calc inv (Subfunctor.toRange j) ≫ j
        = inv (Subfunctor.toRange j) ≫
            (Subfunctor.toRange j ≫ (Subfunctor.range j).ι) := by
          rw [Subfunctor.toRange_ι]
      _ = (Subfunctor.range j).ι := by rw [IsIso.inv_hom_id_assoc]
  have hl : (l₀ ≫ inv (Subfunctor.toRange j)) ≫ j = pullback.fst g H.ι := by
    rw [Category.assoc, hinv, hl₀]
  have hk : pullback.lift j t ht ≫ pullback.fst g H.ι = j := pullback.lift_fst _ _ _
  have hkl : pullback.lift j t ht ≫ (l₀ ≫ inv (Subfunctor.toRange j)) = 𝟙 W := by
    apply (cancel_mono j).1
    simp [Category.assoc, hl]
  have hlk : (l₀ ≫ inv (Subfunctor.toRange j)) ≫ pullback.lift j t ht =
      𝟙 (pullback g H.ι) := by
    apply (cancel_mono (pullback.fst g H.ι)).1
    rw [Category.assoc, hk, Category.id_comp]
    exact hl
  exact IsPullback.of_iso_pullback ⟨ht⟩ ⟨pullback.lift j t ht,
    l₀ ≫ inv (Subfunctor.toRange j), hkl, hlk⟩ hk (pullback.lift_snd _ _ _)

end AlgebraicGeometry.Space

end
