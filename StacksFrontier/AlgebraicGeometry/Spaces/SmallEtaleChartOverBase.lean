module

public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.ArbitraryBaseChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SpecOfGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheaf

/-!
# The chart morphisms of the morphism of ringed topoi of a morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`.  The morphism of small
étale ringed topoi `(f_small, f♯)` of Stacks 03G8 has chart morphisms over `S`
(`AlgebraicGeometry.Space.IsChartOverBase`): for every affine étale scheme chart `V` of `Y`,
every étale chart `U` of `X` and every section `s` of `f_small⁻¹h_V` over `U`, the morphism of
schemes `f_s : U ⟶ V` commutes with the structure morphisms of the two charts to `S`.

No representability hypothesis is needed.  By
`AlgebraicGeometry.Space.chartSchemeHom_chartFiberToInvRep` the assertion holds for the sections
coming from a chart map over `f`, those being morphisms of the big fppf site of `S` and hence
over `S` already; and by `AlgebraicGeometry.Space.W_chartFiberToInvRep` the presheaf map from
the chart maps to `f_small⁻¹h_V` is a local isomorphism, so an equality of two maps from
`f_small⁻¹h_V` into a *sheaf* may be checked on the chart maps.  The sheaf used is the one of
morphisms of schemes from the étale charts of `X` into a fixed scheme
(`AlgebraicGeometry.Space.chartPointsSheaf`), which is a sheaf because the fppf-representable
presheaf `AlgebraicGeometry.Space.schemePoints` is one on the big fppf site and restriction
along `AlgebraicGeometry.Space.SmallEtale.toOver` preserves sheaves.

## Main definitions

* `AlgebraicGeometry.Space.chartPointsSheaf`: the sheaf on the small étale site of `X` of
  morphisms of schemes from the étale charts of `X` into a fixed scheme.
* `AlgebraicGeometry.Space.chartSchemeHomOverMap` and
  `AlgebraicGeometry.Space.chartStructureMap`: the two maps from `f_small⁻¹h_V` into it whose
  equality is the assertion.

## Main results

* `AlgebraicGeometry.Space.isChartOverBase_smallEtaleRingedToposHom`: the chart morphisms of
  `(f_small, f♯)` are over the base.

## Implementation notes

`AlgebraicGeometry.Space.isChartOverBase_of_isTerminal` gives the same conclusion for *every*
morphism of the small étale ringed topoi, but only over a terminal base scheme; the point here is
that for the morphism of ringed topoi *of a morphism of algebraic spaces* it holds over any base.
The argument avoids identifying `f_s` with a chart map of `f` through the inverse image of a
chart sheaf, which the direct-image description of Stacks 03G8 supplies only for a representable
`f`.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS}

attribute [local instance] smallEtaleTopology_subcanonical

/-- **The sheaf of morphisms of schemes from the étale charts of `X` into a fixed scheme `T`.**
The presheaf of such morphisms on the big fppf site of `S` is a sheaf
(`AlgebraicGeometry.Space.isSheaf_schemePoints`), and restriction along the inclusion of the
small étale site of `X` into the big fppf site preserves sheaves
(`AlgebraicGeometry.Space.SmallEtale.isSheaf_comp_toOver`). -/
abbrev chartPointsSheaf (X : AlgebraicSpaces B S hS) (T : Scheme.{u}) :
    Sheaf (SmallEtale.topology B S hS X.1) (Type u) :=
  ⟨(SmallEtale.toOver B S hS X.1).op ⋙ schemePoints B S hS T,
    SmallEtale.isSheaf_comp_toOver B S hS X.1 (isSheaf_schemePoints B S hS T)⟩

variable (f : X ⟶ Y)

/-- The chart morphism `f_s : U ⟶ V` of `(f_small, f♯)` followed by the structure morphism of
`V` to the base, as a map from `f_small⁻¹h_V` into
`AlgebraicGeometry.Space.chartPointsSheaf`. -/
def chartSchemeHomOverMap (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)] :
    (invRep (smallEtaleRingedToposHom B S hS f) V).obj ⟶
      (chartPointsSheaf X (B.inclusion.obj (B.obj hS))).obj where
  app U := ↾fun s ↦ chartSchemeHom (smallEtaleRingedToposHom B S hS f) V U.unop s ≫
    B.inclusion.map V.obj.left.hom
  naturality U U' i := by
    ext s
    exact (congrArg (fun m ↦ m ≫ B.inclusion.map V.obj.left.hom)
      (chartSchemeHom_restrict (smallEtaleRingedToposHom B S hS f) V i.unop s)).trans
      (Category.assoc _ _ _)

/-- The structure morphism of the chart `U` of `X` to the base, as a map from `f_small⁻¹h_V`
into `AlgebraicGeometry.Space.chartPointsSheaf`; it does not depend on the section. -/
def chartStructureMap (V : SmallEtale B S hS Y.1) :
    (invRep (smallEtaleRingedToposHom B S hS f) V).obj ⟶
      (chartPointsSheaf X (B.inclusion.obj (B.obj hS))).obj where
  app U := ↾fun _ ↦ B.inclusion.map U.unop.obj.left.hom
  naturality U U' i := by
    ext s
    exact (congrArg B.inclusion.map (Over.w i.unop.hom.left)).symm.trans
      (B.inclusion.map_comp _ _)

/-- The value of `AlgebraicGeometry.Space.chartSchemeHomOverMap` at a section `s` over `U` is
`f_s` followed by the structure morphism of `V` to the base. -/
theorem chartSchemeHomOverMap_app (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    (U : SmallEtale B S hS X.1)
    (s : (invRep (smallEtaleRingedToposHom B S hS f) V).obj.obj (op U)) :
    (chartSchemeHomOverMap f V).app (op U) s =
      chartSchemeHom (smallEtaleRingedToposHom B S hS f) V U s ≫
        B.inclusion.map V.obj.left.hom :=
  rfl

/-- The value of `AlgebraicGeometry.Space.chartStructureMap` at any section over `U` is the
structure morphism of `U` to the base. -/
theorem chartStructureMap_app (V : SmallEtale B S hS Y.1) (U : SmallEtale B S hS X.1)
    (s : (invRep (smallEtaleRingedToposHom B S hS f) V).obj.obj (op U)) :
    (chartStructureMap f V).app (op U) s = B.inclusion.map U.obj.left.hom :=
  rfl

/-- `AlgebraicGeometry.Space.chartSchemeHomOverMap` and
`AlgebraicGeometry.Space.chartStructureMap` agree on the sections coming from chart maps over
`f`. -/
theorem chartFiberToInvRep_comp_chartSchemeHomOverMap (V : SmallEtale B S hS Y.1)
    [IsAffine (chartSch V)] :
    chartFiberToInvRep f V ≫ chartSchemeHomOverMap f V =
      chartFiberToInvRep f V ≫ chartStructureMap f V := by
  ext U c
  refine (congrArg (fun m ↦ m ≫ B.inclusion.map V.obj.left.hom)
    (chartSchemeHom_chartFiberToInvRep f V U.unop c)).trans ?_
  exact (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map (Over.w c.val))

/-- `AlgebraicGeometry.Space.chartSchemeHomOverMap` and
`AlgebraicGeometry.Space.chartStructureMap` are equal. -/
theorem chartSchemeHomOverMap_eq_chartStructureMap (V : SmallEtale B S hS Y.1)
    [IsAffine (chartSch V)] :
    chartSchemeHomOverMap f V = chartStructureMap f V :=
  ((W_chartFiberToInvRep f V).homEquiv
      (chartPointsSheaf X (B.inclusion.obj (B.obj hS))).obj
      (chartPointsSheaf X (B.inclusion.obj (B.obj hS))).property).injective
    (chartFiberToInvRep_comp_chartSchemeHomOverMap f V)

/-- **The chart morphisms of `(f_small, f♯)` are over the base.** For a morphism `f : X ⟶ Y` of
algebraic spaces over a scheme `S` — *not* assumed representable — every morphism of schemes
`f_s : U ⟶ V` attached to an affine étale chart `V` of `Y`, an étale chart `U` of `X` and a
section `s` over `U` of `f_small⁻¹h_V` commutes with the structure morphisms of the two charts
to `S`. -/
theorem isChartOverBase_smallEtaleRingedToposHom :
    IsChartOverBase (smallEtaleRingedToposHom B S hS f) := by
  intro V _ U s
  rw [← chartSchemeHomOverMap_app f V U s, ← chartStructureMap_app f V U s,
    chartSchemeHomOverMap_eq_chartStructureMap]

end AlgebraicGeometry.Space

end
