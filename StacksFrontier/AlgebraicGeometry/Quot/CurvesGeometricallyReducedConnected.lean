module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricComponentCount
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.GeometricallyReduced
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented

/-!
# The defining condition of the open substack `Curves^{grc,1}` (towards Stacks 0E1I)

Stacks 0E1I cuts out of the stack of curves the open substack `Curves^{grc,1}` of families of
curves whose geometric fibres are reduced, connected and of dimension `1`.

## Main definitions

* `AlgebraicGeometry.CurveFamily.HasGeometricallyConnectedFibres`: every geometric fibre of the
  family is connected, that is it has exactly one connected component (Stacks 0E1B).
* `AlgebraicGeometry.IsGrc1CurveFamily`: condition (1)(b) of Stacks 0E1I.

## Main results

* `AlgebraicGeometry.Space.numberGeometricConnectedComponents_iso_comp`: the number of geometric
  connected components of the fibres does not change under precomposition with an isomorphism.
* `AlgebraicGeometry.CurveFamily.numberGeometricConnectedComponents_toBase_of_hom`: for a
  morphism of families of curves, the count of the source is the count of the target composed
  with the map of base schemes (Stacks 0E1B on the cartesian square of the morphism).

The open substack itself and Stacks 0E1I are in
`StacksFrontier.AlgebraicGeometry.Quot.CurvesGrc1OpenSubstack`.

## References

* [Stacks Project, Tag 0E1I](https://stacks.math.columbia.edu/tag/0E1I)
* [Stacks Project, Tag 0E1E](https://stacks.math.columbia.edu/tag/0E1E)
* [Stacks Project, Tag 0E1B](https://stacks.math.columbia.edu/tag/0E1B)
* [Stacks Project, Tag 0E0G](https://stacks.math.columbia.edu/tag/0E0G)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The number of geometric connected components of the fibres does not change when the
morphism is precomposed with an isomorphism of the source: the fibres over every field-valued
point are isomorphic. -/
theorem numberGeometricConnectedComponents_iso_comp {W X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : W ≅ X) (f : X ⟶ Y) :
    numberGeometricConnectedComponents B S hS (e.hom ≫ f) =
      numberGeometricConnectedComponents B S hS f := by
  have hcount : ∀ p : FieldValuedPoint B S hS Y,
      geometricFiberComponentCount B S hS (e.hom ≫ f) p =
        geometricFiberComponentCount B S hS f p := by
    intro p
    let σ := yonedaEquiv.symm p.value
    have hiso := pullback.map_isIso (e.hom ≫ f) σ f σ e.hom (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])
    unfold geometricFiberComponentCount
    rw [cardinalMk_connectedComponents_eq_of_iso B S hS (@asIso _ _ _ _ _ hiso)]
  funext y
  unfold numberGeometricConnectedComponents
  simp only [hcount]

end Space

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

namespace CurveFamily

/-- **The geometric fibres of a family of curves are connected.** At every point `s` of the
base the geometric fibre has exactly one connected component (the function of Stacks 0E1B takes
the value `1`); in particular no fibre is empty. -/
def HasGeometricallyConnectedFibres (X : CurveFamily B hZ) : Prop :=
  ∀ s : Space.points B integerBase hZ (schemeSpace X.base).obj,
    Space.numberGeometricConnectedComponents B integerBase hZ X.toBase.hom s = 1

variable {B hZ}

/-- **Stacks 0E1B for families of curves.** For a morphism of families of curves `F ⟶ G`, the
number of geometric connected components of the fibre of `F` over a point `t` of its base is that
of the fibre of `G` over the image of `t`: the square of the morphism is cartesian. -/
theorem numberGeometricConnectedComponents_toBase_of_hom {F G : CurveFamily B hZ} (a : F ⟶ G) :
    Space.numberGeometricConnectedComponents B integerBase hZ F.toBase.hom =
      Space.numberGeometricConnectedComponents B integerBase hZ G.toBase.hom ∘
        Space.pointsMap B integerBase hZ (schemeSpace F.base).obj
          (schemeSpaceMap a.baseMap).hom := by
  have sq := AlgebraicSpaces.isPullback_hom B integerBase hZ a.cartesian
  rw [← sq.isoPullback_hom_snd, Space.numberGeometricConnectedComponents_iso_comp,
    Space.numberGeometricConnectedComponents_baseChange B integerBase hZ G.total.property
      (schemeSpace G.base).property (schemeSpace F.base).property]

end CurveFamily

/-- **Condition (1)(b) of Stacks 0E1I.** A family of curves `f : X → S` whose geometric fibres
are reduced (equivalently, whose fibres are geometrically reduced, Stacks 0E07 and 0E08),
connected, and of dimension `1`. -/
def IsGrc1CurveFamily (X : CurveFamily B hZ) : Prop :=
  (∀ y, Space.IsGeometricallyReducedFibreAt B integerBase hZ X.toBase.hom X.total.property
      (schemeSpace X.base).property y) ∧
    CurveFamily.HasGeometricallyConnectedFibres B hZ X ∧
    CurveFamily.HasFibresOfDimensionOne B hZ X

variable {B hZ}

end AlgebraicGeometry

end
