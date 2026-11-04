module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesPrestableOpen
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesOpenLocusRelative
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesPrestableGenus
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSemistable

/-!
# The open substack `Curves^{semistable}` (towards Stacks 0E70)

Stacks 0E70 produces the open substack `Curves^{semistable} ⊂ Curves` of semistable families of
curves (Stacks 0E6Z): the classifying morphism of a family factors through it exactly when the
family is semistable (part (1)), and a proper scheme of dimension at most one over a field lies in
it exactly when it is at-worst-nodal, of dimension one, with `H⁰ = k`, of genus at least one and
without rational tails (part (2)).

This file proves part (1) unconditionally: the strictly full subcategory of semistable families,
`AlgebraicGeometry.C1590Private.curvesSemistable`, is a category fibred in groupoids over the big
fppf site, and the classifying morphism of a family factors through it exactly when the family is
semistable (`AlgebraicGeometry.C1590Private.factors_curvesSemistable_iff`), since semistability
passes to base changes. It then proves the openness of `Curves^{semistable}` from explicit inputs,
following the source proof: by Section 0E0E it suffices to look at prestable families, prestability
satisfying condition (o) by the inputs `hopen` and `hpush` of Stacks 0E6I
(`AlgebraicGeometry.isOpenCurvesLocus_isPrestableCurveFamily_of` applied to
`AlgebraicGeometry.isOpenCurvesLocus_isH01CurveFamily_of`), and over a
prestable family the locus of points whose fibre has genus at least one and no rational tail is
open, with formation commuting with base change — the input `hss`.

## Main definitions

* `AlgebraicGeometry.C1590Private.HasSemistableFibres`: every fibre has genus at least one and
  no rational tail.
* `AlgebraicGeometry.C1590Private.PrestableSemistableFibresOpen`: the input `hss`.
* `AlgebraicGeometry.C1590Private.curvesSemistable`: `Curves^{semistable}` as a category fibred
  in groupoids over the big fppf site of `Spec(ℤ)`, with inclusion
  `AlgebraicGeometry.C1590Private.curvesSemistableInclusion` into `Curves`.

## Main results

* `AlgebraicGeometry.C1590Private.factors_curvesSemistable_iff`: part (1) of Stacks 0E70, the
  characterization of the families whose classifying morphism factors through
  `Curves^{semistable}`.
* `AlgebraicGeometry.C1590Private.isOpenCurvesLocus_isSemistableCurveFamily_of`: condition (o) of
  Stacks 0E0E for semistability, from the inputs `hopen`, `hpush` and `hss`.
* `AlgebraicGeometry.C1590Private.curvesSemistable_isOpenSubstack_of`: `Curves^{semistable}` is an
  open substack of `Curves`, from the same inputs.

## Implementation notes

These are unregistered helpers (Stacks 0E70 is not registered here). The inputs:

* `hopen`, `hpush` are those of `AlgebraicGeometry.isOpenCurvesLocus_isH01CurveFamily_of`:
  Stacks 0E0R at `i = 0` and Stacks 0E6B (a), in curve-family form;
* `hss : PrestableSemistableFibresOpen B hZ` is the content of the second paragraph of the source
  proof: over a prestable family the points whose fibre has genus `≥ 1` and no rational tail form
  an open subset of the base, by the local constancy of the genus (Stacks 0E6V, from Stacks 0E1J)
  and by Stacks 0E6Y, and the formation of that open commutes with base change by the base field
  compatibility of Stacks 0E3L. Stacks 0E6Y is about the relative dualizing sheaf `ω_{X/S}` of a
  family of curves (Section 0E6N), which is not available, so its surjectivity condition cannot be
  stated; `hss` records its consequence for the locus.

## References

* [Stacks Project, Tag 0E70](https://stacks.math.columbia.edu/tag/0E70)
* [Stacks Project, Tag 0E6Z](https://stacks.math.columbia.edu/tag/0E6Z)
* [Stacks Project, Tag 0E6Y](https://stacks.math.columbia.edu/tag/0E6Y)
* [Stacks Project, Tag 0E6V](https://stacks.math.columbia.edu/tag/0E6V)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
* [Stacks Project, Tag 0E3L](https://stacks.math.columbia.edu/tag/0E3L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.C1590Private

attribute [local instance] Space.pointTopology

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- Every fibre of a family of curves, at every field-valued point of the base, is presented by a
scheme over the field of the point which has genus at least one and no rational tail: the
fibrewise condition (2) of Stacks 0E6Z. -/
abbrev HasSemistableFibres (X : CurveFamily B hZ) : Prop :=
  ∀ p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj,
    X.HasFibreSatisfying B hZ (fun k _ _ f => HasPositiveGenusNoRationalTail k f) p

/-- Semistability is prestability together with the fibrewise condition. -/
theorem isSemistableCurveFamily_iff (X : CurveFamily B hZ) :
    IsSemistableCurveFamily B hZ X ↔
      IsPrestableCurveFamily B hZ X ∧ HasSemistableFibres B hZ X :=
  Iff.rfl

/-- **Input: the semistable fibre locus of a prestable family.** For every prestable family of
curves `G`, the points of its base whose fibre has genus at least one and no rational tail form
an open set `Ω`, and a family mapping to `G` has all its fibres of that kind exactly when its
morphism of bases lands in `Ω`. This is the consequence of Stacks 0E6V and 0E6Y used in the proof
of Stacks 0E70, with the base field compatibility of Stacks 0E3L. -/
def PrestableSemistableFibresOpen : Prop :=
  ∀ G : CurveFamily B hZ, IsPrestableCurveFamily B hZ G →
    ∃ Ω : Set ((BigFppfOver.toScheme B integerBase hZ).obj G.base), IsOpen Ω ∧
      ∀ (F : CurveFamily B hZ) (a : F ⟶ G), HasSemistableFibres B hZ F ↔
        Set.range ((BigFppfOver.toScheme B integerBase hZ).map a.baseMap) ⊆ Ω

/-- `Curves^{semistable}`: the strictly full subcategory of semistable families of curves, as a
category fibred in groupoids over the big fppf site of `Spec(ℤ)`. -/
def curvesSemistable :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B integerBase hZ) :=
  curvesSubstack B hZ (IsSemistableCurveFamily B hZ)
    (CurveFamily.isSemistableCurveFamily_of_hom B hZ)

/-- The inclusion `Curves^{semistable} ⟶ Curves`. -/
def curvesSemistableInclusion : curvesSemistable B hZ ⟶ curvesFiberedCategory B hZ :=
  curvesSubstackInclusion B hZ (IsSemistableCurveFamily B hZ)
    (CurveFamily.isSemistableCurveFamily_of_hom B hZ)

/-- **Part (1) of Stacks 0E70.** The classifying morphism of a family of curves factors through
`Curves^{semistable}` exactly when the family is semistable: a scheme-valued point `y` of `Curves`
over `U` lifts to the subcategory of semistable families exactly when the family `y(U)` it
classifies is semistable. Every `y(T)` is a base change of `y(U)`, and semistability passes to
base changes. -/
theorem factors_curvesSemistable_iff (U : BigFppfOver B integerBase hZ)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ)
    (_hy : y ⋙ curvesProjectionOver B hZ = Over.map U.hom) :
    (∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
        ObjectProperty.FullSubcategory (IsSemistableCurveFamily B hZ),
        z ⋙ ObjectProperty.ι (IsSemistableCurveFamily B hZ) = y) ↔
      IsSemistableCurveFamily B hZ (y.obj (Over.mk (𝟙 U.left))) := by
  constructor
  · rintro ⟨z, rfl⟩
    exact (z.obj _).property
  · intro h
    exact ⟨ObjectProperty.lift (IsSemistableCurveFamily B hZ) y fun T =>
      CurveFamily.isSemistableCurveFamily_of_hom B hZ (y.map (Over.homMk T.hom (by simp))) h, rfl⟩

variable {B hZ}

variable (hopen : IsOpenCurvesLocus B hZ
    (CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ))
  (hpush : ∀ X : CurveFamily B hZ, CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ X →
    HasUniversallyBijectiveGlobalFunctions B hZ X)
  (hss : PrestableSemistableFibresOpen B hZ)

include hopen hpush hss

/-- **Condition (o) of Stacks 0E0E for semistability**, from the inputs `hopen`, `hpush` (Stacks
0E6I) and `hss` (Stacks 0E6V, 0E6Y). As in the source proof, it suffices to look at prestable
families, prestability satisfying condition (o); over a prestable family the semistable locus is
the open given by `hss`. -/
theorem isOpenCurvesLocus_isSemistableCurveFamily_of :
    IsOpenCurvesLocus B hZ (IsSemistableCurveFamily B hZ) := by
  refine IsOpenCurvesLocus.of_le
    (isOpenCurvesLocus_isPrestableCurveFamily_of
      (isOpenCurvesLocus_isH01CurveFamily_of hopen hpush))
    (fun _ h => h.1) fun G hG => ?_
  obtain ⟨Ω, hΩ, hchar⟩ := hss G hG
  refine ⟨Space.schemePointsHomeomorph B integerBase hZ G.base ⁻¹' Ω,
    hΩ.preimage (Space.schemePointsHomeomorph B integerBase hZ G.base).continuous,
    fun F a => ?_⟩
  refine Iff.trans ?_ (range_pointsMap_subset_preimage_iff a.baseMap Ω).symm
  exact ⟨fun h => (hchar F a).1 h.2,
    fun h => ⟨CurveFamily.isPrestableCurveFamily_of_hom a hG, (hchar F a).2 h⟩⟩

/-- **Stacks 0E70, the open substack, from its inputs.** `Curves^{semistable} ⊂ Curves` is an
open substack: semistability is invariant under isomorphism, and the inclusion is representable
by algebraic spaces and an open immersion. -/
theorem curvesSemistable_isOpenSubstack_of :
    ObjectProperty.IsClosedUnderIsomorphisms (IsSemistableCurveFamily B hZ) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ _
          (isOpenCurvesLocus_isSemistableCurveFamily_of hopen hpush hss).prop_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ _
          (isOpenCurvesLocus_isSemistableCurveFamily_of hopen hpush hss).prop_of_hom) :=
  isOpenImmersion_curvesSubstackInclusion
    (isOpenCurvesLocus_isSemistableCurveFamily_of hopen hpush hss)

end AlgebraicGeometry.C1590Private

end
