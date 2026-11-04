module

public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleToposMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableEquivalence

/-!
# The étale topos of a representable algebraic space is the small étale topos of the scheme

Let `T` be an object of the big fppf site of `S` and `T'` its underlying scheme. The algebraic
space `h_T` represented by `T` has a spaces-étale site (Stacks 03G0), and `T'` has a small étale
site in the big étale site carried by the same category of schemes (Stacks 03ED,
`AlgebraicGeometry.associatedBigEtaleSite`). This file identifies the two categories of sheaves.

The identification is restriction along the *chart functor* `c_T`, which sends an étale scheme
`V ⟶ T'` of the small étale site to the algebraic space `h_V` étale over `h_T`. That functor is
the composite of the inverse of `AlgebraicGeometry.Space.representedSmallEtaleEquivalence` — an
equivalence of sites — with the comparison functor of Stacks 03G1, a dense subsite inclusion; so
it is a dense subsite inclusion, and restriction along it is an equivalence of sheaf categories.

## Main definitions

* `AlgebraicGeometry.Space.representedChartFunctor`: the chart functor `c_T`.
* `AlgebraicGeometry.Space.representedSpacesEtaleSheafEquiv`: the equivalence
  `Sh((h_T)_{spaces-étale}) ≌ Sh(T'_{étale})`, whose functor is restriction along `c_T`.

## Main results

* `AlgebraicGeometry.Space.representedSpacesEtaleSheafEquiv_functor_iso`: the functor of the
  equivalence is restriction along `c_T`, `CategoryTheory.Functor.sheafPushforwardContinuous`.
* `AlgebraicGeometry.Space.representedSpacesEtaleSheafEquiv_functor_obj_val_obj`: on sections, the
  functor is evaluation at the image under `c_T`, by definition.

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (T : BigFppfOver B S hS)

/-- The small étale site of the scheme underlying an object `T` of the big fppf site of `S`,
taken in the big étale site carried by the same category of schemes. -/
abbrev representedSchemeSmallEtale :=
  _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj T) T.left.property

/-- The small étale topology of the scheme underlying `T`. -/
abbrev representedSchemeTopology : GrothendieckTopology (representedSchemeSmallEtale B S hS T) :=
  _root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj T) T.left.property

/-- **The chart functor of a representable algebraic space.** An étale scheme over the scheme
underlying `T` is sent to the algebraic space it represents, étale over `h_T`. -/
abbrev representedChartFunctor :
    representedSchemeSmallEtale B S hS T ⥤ SpacesEtale B S hS (yonedaSpace B S hS T) :=
  (representedSmallEtaleEquivalence B S hS T).inverse ⋙
    comparisonFunctor B S hS (yonedaSpace B S hS T)

/-- The inverse of the identification of the small étale site of `h_T` with that of the scheme
underlying `T` is a dense subsite inclusion for `representedSchemeTopology`, the two topologies
corresponding. -/
instance representedSmallEtaleEquivalence_inverse_isDenseSubsite_representedSchemeTopology :
    (representedSmallEtaleEquivalence B S hS T).inverse.IsDenseSubsite
      (representedSchemeTopology B S hS T) (SmallEtale.topology B S hS (yoneda.obj T)) := by
  rw [← representedSmallEtaleEquivalence_topology B S hS T]
  exact inferInstanceAs ((representedSmallEtaleEquivalence B S hS T).symm.functor.IsDenseSubsite
    (representedSchemeTopology B S hS T)
    ((representedSmallEtaleEquivalence B S hS T).symm.inverse.inducedTopology
      (representedSchemeTopology B S hS T)))

/-- The chart functor is continuous. -/
instance representedChartFunctor_isContinuous :
    (representedChartFunctor B S hS T).IsContinuous (representedSchemeTopology B S hS T)
      (SpacesEtale.topology B S hS (yonedaSpace B S hS T)) :=
  letI : (comparisonFunctor B S hS (yonedaSpace B S hS T)).IsContinuous
      (SmallEtale.topology B S hS (yoneda.obj T))
      (SpacesEtale.topology B S hS (yonedaSpace B S hS T)) :=
    comparisonFunctor_isContinuous B S hS (yonedaSpace B S hS T)
  Functor.isContinuous_comp _ _ (representedSchemeTopology B S hS T)
    (SmallEtale.topology B S hS (yoneda.obj T))
    (SpacesEtale.topology B S hS (yonedaSpace B S hS T))

/-- **The spaces-étale topos of a representable algebraic space is the small étale topos of the
underlying scheme.** The functor restricts a sheaf on the spaces-étale site of `h_T` along the
chart functor; it is the comparison equivalence of Stacks 03G1 followed by the equivalence of
sheaf categories induced by `AlgebraicGeometry.Space.representedSmallEtaleEquivalence`. -/
def representedSpacesEtaleSheafEquiv :
    Sheaf (SpacesEtale.topology B S hS (yonedaSpace B S hS T)) (Type (u + 1)) ≌
      Sheaf (representedSchemeTopology B S hS T) (Type (u + 1)) :=
  (smallEtaleToposEquiv B S hS (yonedaSpace B S hS T)).trans
    ((representedSmallEtaleEquivalence B S hS T).sheafCongr
      (SmallEtale.topology B S hS (yoneda.obj T)) (representedSchemeTopology B S hS T)
      (Type (u + 1)))

/-- The functor of `AlgebraicGeometry.Space.representedSpacesEtaleSheafEquiv` is restriction
along the chart functor. -/
def representedSpacesEtaleSheafEquiv_functor_iso :
    (representedSpacesEtaleSheafEquiv B S hS T).functor ≅
      (representedChartFunctor B S hS T).sheafPushforwardContinuous (Type (u + 1))
        (representedSchemeTopology B S hS T)
        (SpacesEtale.topology B S hS (yonedaSpace B S hS T)) :=
  Iso.refl _

/-- On sections, the functor of `AlgebraicGeometry.Space.representedSpacesEtaleSheafEquiv` is
evaluation at the image of the chart functor. -/
theorem representedSpacesEtaleSheafEquiv_functor_obj_val_obj
    (F : Sheaf (SpacesEtale.topology B S hS (yonedaSpace B S hS T)) (Type (u + 1)))
    (V : representedSchemeSmallEtale B S hS T) :
    ((representedSpacesEtaleSheafEquiv B S hS T).functor.obj F).obj.obj (op V) =
      F.obj.obj (op ((representedChartFunctor B S hS T).obj V)) :=
  rfl

end AlgebraicGeometry.Space

end
