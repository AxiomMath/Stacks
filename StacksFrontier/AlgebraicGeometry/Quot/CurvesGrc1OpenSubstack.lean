module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesGrc1OfComponentCount
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.GeometricComponentsConnectedOpen

/-!
# The open substack `Curves^{grc,1}` of the stack of curves (Stacks 0E1I)

Stacks 0E1I produces the open substack `Curves^{grc,1} ⊂ Curves` of families of curves whose
geometric fibres are reduced, connected and of dimension `1`
(`AlgebraicGeometry.IsGrc1CurveFamily`), and identifies the points of it coming from a proper
scheme of dimension at most one over a field.

The source's proof shows that over the open locus `E` of the base where the fibres are
geometrically reduced (Stacks 0E0G), the locus where the geometric fibres are moreover connected
is open, by the Stein factorization of the family being étale (Stacks 0E0D) and the decomposition
of a finite locally free morphism by degree (Stacks 04MH). Here that openness is
`AlgebraicGeometry.Space.isOpen_setOf_isGeometricallyReducedFibreAt_and_eq_one_of_scheme`: the set
of points of the base at which the fibre is geometrically reduced and the geometric fibre has
exactly one connected component is open. Its formation commutes with arbitrary base change
(Stacks 0E09 and 0E1B), so the method of Section 0E0E applies, as in the source.

## Main results

* `AlgebraicGeometry.isOpenCurvesLocus_geometricallyReduced_and_connected`: condition (o) of
  Section 0E0E for "geometrically reduced and geometrically connected fibres".
* `AlgebraicGeometry.isOpenCurvesLocus_isGrc1CurveFamily`: condition (o) for `Curves^{grc,1}`.
* `AlgebraicGeometry.curvesGrc1_isOpenSubstack`, `AlgebraicGeometry.factors_curvesGrc1_iff`,
  `AlgebraicGeometry.factors_curvesGrc1_over_field_iff` and
  `AlgebraicGeometry.curvesGrc1_isOpenSubstack_and_factors_iff`: **Stacks 0E1I**, the open
  substack, its parts (1) and (2), and the whole statement.

## Implementation notes

As in the rest of this library's open substacks of `Curves` (Section 0E0E), an open substack is a
strictly full subcategory of the category of families of curves whose inclusion is representable
by algebraic spaces and an open immersion. Condition (1)(b), "the geometric fibres are reduced,
connected and of dimension `1`", is `AlgebraicGeometry.IsGrc1CurveFamily`: the fibres are
geometrically reduced (equivalently the geometric fibres are reduced, Stacks 0E07), every geometric
fibre has exactly one connected component (Stacks 0E1B), and the fibres have dimension `1`.

## References

* [Stacks Project, Tag 0E1I](https://stacks.math.columbia.edu/tag/0E1I)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
* [Stacks Project, Tag 0E0G](https://stacks.math.columbia.edu/tag/0E0G)
* [Stacks Project, Tag 0E1B](https://stacks.math.columbia.edu/tag/0E1B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **Condition (o) of Section 0E0E for geometrically reduced and connected fibres.** A family of
curves `F` mapping to a family `G` has geometrically reduced fibres with connected geometric
fibres exactly when its morphism of base schemes sends every point into the set of points of the
base of `G` at which the fibre is geometrically reduced and the geometric fibre has one connected
component; that set is open
(`AlgebraicGeometry.Space.isOpen_setOf_isGeometricallyReducedFibreAt_and_eq_one_of_scheme`), and
its formation commutes with base change (Stacks 0E09 and 0E1B). -/
theorem isOpenCurvesLocus_geometricallyReduced_and_connected :
    IsOpenCurvesLocus B hZ (fun X : CurveFamily B hZ =>
      (∀ y, Space.IsGeometricallyReducedFibreAt B integerBase hZ X.toBase.hom X.total.property
        (schemeSpace X.base).property y) ∧ CurveFamily.HasGeometricallyConnectedFibres B hZ X) := by
  refine IsOpenCurvesLocus.of_points fun G => ⟨{y | Space.IsGeometricallyReducedFibreAt B
      integerBase hZ G.toBase.hom G.total.property (schemeSpace G.base).property y ∧
        Space.numberGeometricConnectedComponents B integerBase hZ G.toBase.hom y = 1},
    Space.isOpen_setOf_isGeometricallyReducedFibreAt_and_eq_one_of_scheme B hZ G.base
      G.toBase.hom G.total.property G.proper G.flat G.finitePresentation, fun F a => ?_⟩
  have hred := CurveFamily.preimage_geometricallyReducedBaseLocus B hZ a
  have hn := CurveFamily.numberGeometricConnectedComponents_toBase_of_hom a
  rw [Set.range_subset_iff]
  exact ⟨fun h s => ⟨(Set.ext_iff.1 hred s).2 (h.1 s), (congrFun hn s).symm.trans (h.2 s)⟩,
    fun h => ⟨fun s => (Set.ext_iff.1 hred s).1 (h s).1, fun s => (congrFun hn s).trans (h s).2⟩⟩

/-- **Condition (o) of Section 0E0E for `Curves^{grc,1}`.** It is the conjunction of condition (o)
for geometrically reduced and connected fibres with condition (o) for fibres of dimension `1`
(Stacks 0D4R, `AlgebraicGeometry.isOpenCurvesLocus_hasFibresOfDimensionOne`). -/
theorem isOpenCurvesLocus_isGrc1CurveFamily : IsOpenCurvesLocus B hZ (IsGrc1CurveFamily B hZ) := by
  intro G
  obtain ⟨W, hW, hchar⟩ := (isOpenCurvesLocus_geometricallyReduced_and_connected.and
    isOpenCurvesLocus_hasFibresOfDimensionOne) G
  exact ⟨W, hW, fun F a => and_assoc.symm.trans (hchar F a)⟩

variable (B hZ)

/-- **Stacks 0E1I, the open substack.** `Curves^{grc,1}`, the strictly full subcategory of
families of curves whose geometric fibres are reduced, connected and of dimension `1`, is an open
substack of `Curves`: its inclusion is representable by algebraic spaces and an open
immersion. -/
@[stacks 0E1I "the open substack Curves^{grc,1} of Curves"]
theorem curvesGrc1_isOpenSubstack :
    ObjectProperty.IsClosedUnderIsomorphisms (IsGrc1CurveFamily B hZ) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ (IsGrc1CurveFamily B hZ)
          isOpenCurvesLocus_isGrc1CurveFamily.prop_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ (IsGrc1CurveFamily B hZ)
          isOpenCurvesLocus_isGrc1CurveFamily.prop_of_hom) :=
  isOpenImmersion_curvesSubstackInclusion isOpenCurvesLocus_isGrc1CurveFamily

/-- **Stacks 0E1I, part (1).** The classifying morphism of a family of curves `X ⟶ S` factors
through `Curves^{grc,1}` exactly when the geometric fibres of `X ⟶ S` are reduced, connected and
of dimension `1`. -/
@[stacks 0E1I "part (1): the classifying morphism of a family of curves factors through \
Curves^{grc,1} iff its geometric fibres are reduced, connected and of dimension 1"]
theorem factors_curvesGrc1_iff (U : BigFppfOver B integerBase hZ)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ)
    (hy : y ⋙ curvesProjectionOver B hZ = Over.map U.hom) :
    (∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
        ObjectProperty.FullSubcategory (IsGrc1CurveFamily B hZ),
        z ⋙ ObjectProperty.ι (IsGrc1CurveFamily B hZ) = y) ↔
      IsGrc1CurveFamily B hZ (y.obj (Over.mk (𝟙 U.left))) :=
  factors_curvesSubstack_iff isOpenCurvesLocus_isGrc1CurveFamily U y hy

/-- **Stacks 0E1I, part (2).** Let `X` be a proper scheme of dimension at most one over a field
`k` (with `Spec k` in the site, so that the classifying morphism `Spec k ⟶ Curves` of `X`
exists), and let `y` be a scheme-valued point of `Curves` over `U` classifying the family of
curves of `X`. Then `y` factors through `Curves^{grc,1}` exactly when `X` is geometrically
reduced over `k`, geometrically connected over `k`, and of dimension `1`. -/
@[stacks 0E1I "part (2): for a proper scheme of dimension at most one over a field, the \
classifying morphism factors through Curves^{grc,1} iff the scheme is geometrically reduced, \
geometrically connected and of dimension 1"]
theorem factors_curvesGrc1_over_field_iff (k : Type u) [Field k]
    (hk : B.Contains (Spec (.of k))) (X : Over (Spec (.of k))) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (U : BigFppfOver B integerBase hZ)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ)
    (hy : y ⋙ curvesProjectionOver B hZ = Over.map U.hom)
    (e : y.obj (Over.mk (𝟙 U.left)) ≅ curveFamilyOfScheme X B hZ hk hdim) :
    (∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
        ObjectProperty.FullSubcategory (IsGrc1CurveFamily B hZ),
        z ⋙ ObjectProperty.ι (IsGrc1CurveFamily B hZ) = y) ↔
      GeometricallyReduced X.hom ∧ GeometricallyConnected X.hom ∧
        topologicalKrullDim X.left = 1 := by
  rw [factors_curvesSubstack_iff_of_iso isOpenCurvesLocus_isGrc1CurveFamily U y hy _ e]
  exact isGrc1CurveFamily_curveFamilyOfSchemeMorphism_iff_geometricallyReduced
    (t := specULiftZIsTerminal.from _)
    (integerSiteMap B hZ (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact X.hom hk) hk
      X.hom) (inferInstance : Flat X.hom) ‹_› (inferInstance : LocallyOfFinitePresentation X.hom)
    (Space.isQuasiCompact_yoneda_map_of_quasiCompact B integerBase hZ _
      (inferInstanceAs (QuasiCompact X.hom)))
    ((Space.isSeparated_yoneda_map_iff B integerBase hZ _).2 (inferInstanceAs (IsSeparated X.hom)))
    ((Space.isQuasiSeparated_yoneda_map_iff B integerBase hZ _).2
      (inferInstanceAs (QuasiSeparated X.hom))) hdim

/-- **Stacks 0E1I.** There is an open substack `Curves^{grc,1} ⊂ Curves` — the strictly full
subcategory of families of curves whose geometric fibres are reduced, connected and of dimension
`1`, whose inclusion is representable by algebraic spaces and an open immersion — such that
(1) the classifying morphism of a family of curves `X ⟶ S` factors through it exactly when the
geometric fibres of `X ⟶ S` are reduced, connected and of dimension `1`, and (2) for a proper
scheme `X` of dimension at most one over a field `k`, the classifying morphism of `X` factors
through it exactly when `X` is geometrically reduced, geometrically connected and of
dimension `1`. -/
@[stacks 0E1I "the whole statement: the open substack Curves^{grc,1} and parts (1) and (2)"]
theorem curvesGrc1_isOpenSubstack_and_factors_iff :
    (ObjectProperty.IsClosedUnderIsomorphisms (IsGrc1CurveFamily B hZ) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ (IsGrc1CurveFamily B hZ)
          isOpenCurvesLocus_isGrc1CurveFamily.prop_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ (IsGrc1CurveFamily B hZ)
          isOpenCurvesLocus_isGrc1CurveFamily.prop_of_hom)) ∧
    (∀ (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsGrc1CurveFamily B hZ),
          z ⋙ ObjectProperty.ι (IsGrc1CurveFamily B hZ) = y) ↔
        IsGrc1CurveFamily B hZ (y.obj (Over.mk (𝟙 U.left))))) ∧
    (∀ (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (X : Over (Spec (.of k)))
      [IsProper X.hom] (hdim : topologicalKrullDim X.left ≤ 1) (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      (y.obj (Over.mk (𝟙 U.left)) ≅ curveFamilyOfScheme X B hZ hk hdim) →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsGrc1CurveFamily B hZ),
          z ⋙ ObjectProperty.ι (IsGrc1CurveFamily B hZ) = y) ↔
        GeometricallyReduced X.hom ∧ GeometricallyConnected X.hom ∧
          topologicalKrullDim X.left = 1)) :=
  ⟨curvesGrc1_isOpenSubstack B hZ, fun U y hy => factors_curvesGrc1_iff B hZ U y hy,
    fun k _ hk X _ hdim U y hy e => factors_curvesGrc1_over_field_iff B hZ k hk X hdim U y hy e⟩

end AlgebraicGeometry

end
