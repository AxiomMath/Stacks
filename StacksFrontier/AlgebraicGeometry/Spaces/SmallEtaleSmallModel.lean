module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteModules
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleEquiUniverseModel
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.Topology.Dimension.KrullSupplement

/-!
# A `Type u`-presented model of the small étale ringed topos of an algebraic space

The small étale site of an algebraic space `X` over a scheme `S : Scheme.{u}` has its objects in
`Type (u + 1)` and its morphisms in `Type u`, so `AlgebraicGeometry.Space.smallEtaleRingedTopos`
is a `RingedTopos.{u, u + 1, u}`.

The site is essentially small at `u` (`AlgebraicGeometry.Space.SmallEtale.instEssentiallySmall`),
so it is equivalent to its small model `SmallModel.{u} (SmallEtale B S hS X.1) : Type u`.
Transporting the étale topology and the structure sheaf along that equivalence gives a
`RingedTopos.{u, u, u}` whose sheaves of modules are equivalent to the `𝒪_X`-modules.

## Main definitions

The étale topology on the model is `AlgebraicGeometry.Space.smallEtaleModelTopology` of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleEquiUniverseModel.lean`, evaluated at `X.1`.

* `AlgebraicGeometry.Space.smallEtaleModelEquiv`: the comparison of the small étale site of `X`
  with its small model.
* `AlgebraicGeometry.Space.smallEtaleModelStructureSheaf`: the structure sheaf of the model, the
  restriction of `𝒪_X` along the comparison.
* `AlgebraicGeometry.Space.smallEtaleModelRingedTopos`: **the model**, a `RingedTopos.{u, u, u}`.
* `AlgebraicGeometry.Space.toSmallEtaleHom` and `AlgebraicGeometry.Space.fromSmallEtaleHom`: the
  two comparisons between the model and `(X_étale, 𝒪_X)` as morphisms of ringed topoi.
* `AlgebraicGeometry.Space.smallEtaleModelModuleRestriction` and
  `AlgebraicGeometry.Space.smallEtaleModelModulesEquiv`: restriction of `𝒪_X`-modules to the
  model, and the Comparison Lemma saying it is an equivalence.

## Main results

* `AlgebraicGeometry.Space.isIso_toSmallEtaleHom_fSharp`: the structure map of the comparison
  `(model) ⟶ (X_étale, 𝒪_X)` is an isomorphism.
* `AlgebraicGeometry.Space.smallEtaleModelModulesEquiv_functor`: the functor of the Comparison
  Lemma equivalence is restriction of `𝒪_X`-modules to the model, on the nose.

## Implementation notes

This is the algebraic-space counterpart of `AlgebraicGeometry.SmallEtale.smallModelRingedTopos`,
built the same way.

Statements are phrased with `AlgebraicGeometry.Space.smallEtaleModelTopology` and
`AlgebraicGeometry.Space.smallEtaleModelStructureSheaf` rather than with the projections of
`AlgebraicGeometry.Space.smallEtaleModelRingedTopos`, which do not unfold at instance
transparency.

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
* [Stacks Project, Tag 0D3Q](https://stacks.math.columbia.edu/tag/0D3Q)
* [Stacks Project, Tag 00XU](https://stacks.math.columbia.edu/tag/00XU), the Comparison Lemma
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.DenseSubsiteModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-! ### The model site -/

/-- The comparison of the small étale site of `X` with its small model in `Type u`, which exists
because the small étale site is essentially small at `u`. -/
abbrev smallEtaleModelEquiv :
    SmallEtale B S hS X.1 ≌ SmallModel.{u} (SmallEtale B S hS X.1) :=
  equivSmallModel.{u} (SmallEtale B S hS X.1)

/-- The structure sheaf of the model: the restriction of `𝒪_X` along the comparison. -/
abbrev smallEtaleModelStructureSheaf :
    Sheaf (smallEtaleModelTopology B S hS X.1) CommRingCat.{u} :=
  ((smallEtaleModelEquiv B S hS X).inverse.sheafPushforwardContinuous CommRingCat.{u}
    (smallEtaleModelTopology B S hS X.1) (SmallEtale.topology B S hS X.1)).obj
      (structureSheaf B S hS X.1 X.2)

/-- **The `Type u`-presented model of the small étale ringed topos of `X`.**  Its site is the
small model of the small étale site of `X`, with the induced topology, and its structure sheaf is
the restriction of `𝒪_X`.  Unlike `AlgebraicGeometry.Space.smallEtaleRingedTopos`, a
`RingedTopos.{u, u + 1, u}`, this is a `RingedTopos.{u, u, u}`. -/
def smallEtaleModelRingedTopos : RingedTopos.{u, u, u} where
  C := SmallModel.{u} (SmallEtale B S hS X.1)
  J := smallEtaleModelTopology B S hS X.1
  O := smallEtaleModelStructureSheaf B S hS X

/-- The site of `AlgebraicGeometry.Space.smallEtaleModelRingedTopos` is the small model of the
small étale site. -/
@[simp]
theorem smallEtaleModelRingedTopos_C :
    (smallEtaleModelRingedTopos B S hS X).C = SmallModel.{u} (SmallEtale B S hS X.1) := rfl

/-- The topology of `AlgebraicGeometry.Space.smallEtaleModelRingedTopos` is the induced topology
on the small model. -/
@[simp]
theorem smallEtaleModelRingedTopos_J :
    (smallEtaleModelRingedTopos B S hS X).J = smallEtaleModelTopology B S hS X.1 := rfl

/-- The structure sheaf of `AlgebraicGeometry.Space.smallEtaleModelRingedTopos` is the restriction
of `𝒪_X`. -/
@[simp]
theorem smallEtaleModelRingedTopos_O :
    (smallEtaleModelRingedTopos B S hS X).O = smallEtaleModelStructureSheaf B S hS X := rfl

/-! ### The comparison with the small étale ringed topos -/

/-- The identification of `𝒪_X` with the restriction, back along the comparison, of the
structure sheaf of the model: the unit isomorphism of Mathlib's equivalence of sheaf categories
`CategoryTheory.Equivalence.sheafCongr`, evaluated at `𝒪_X`. -/
def toSmallEtaleStructureIso :
    (smallEtaleRingedTopos B S hS X).O ≅
      ((smallEtaleModelEquiv B S hS X).functor.sheafPushforwardContinuous CommRingCat.{u}
        (SmallEtale.topology B S hS X.1) (smallEtaleModelTopology B S hS X.1)).obj
          (smallEtaleModelRingedTopos B S hS X).O :=
  (Equivalence.sheafCongr (SmallEtale.topology B S hS X.1) (smallEtaleModelTopology B S hS X.1)
    (smallEtaleModelEquiv B S hS X) CommRingCat.{u}).unitIso.app
      (structureSheaf B S hS X.1 X.2)

/-- **The comparison of the model with the small étale ringed topos of `X`, as a morphism of
ringed topoi `(model) ⟶ (X_étale, 𝒪_X)`.**  Its underlying continuous functor is the comparison
of the small étale site with its model, and its structure map is
`AlgebraicGeometry.Space.toSmallEtaleStructureIso`. -/
def toSmallEtaleHom :
    RingedToposSiteHom (smallEtaleModelRingedTopos B S hS X) (smallEtaleRingedTopos B S hS X) where
  u := (smallEtaleModelEquiv B S hS X).functor
  isContinuous := inferInstanceAs ((smallEtaleModelEquiv B S hS X).functor.IsContinuous
    (SmallEtale.topology B S hS X.1) (smallEtaleModelTopology B S hS X.1))
  fSharp := (toSmallEtaleStructureIso B S hS X).hom

/-- The underlying functor of `AlgebraicGeometry.Space.toSmallEtaleHom` is the comparison functor
of the small étale site with its model. -/
@[simp]
theorem toSmallEtaleHom_u :
    (toSmallEtaleHom B S hS X).u = (smallEtaleModelEquiv B S hS X).functor := rfl

/-- The structure map of `AlgebraicGeometry.Space.toSmallEtaleHom` is the forward map of
`AlgebraicGeometry.Space.toSmallEtaleStructureIso`. -/
@[simp]
theorem toSmallEtaleHom_fSharp :
    (toSmallEtaleHom B S hS X).fSharp = (toSmallEtaleStructureIso B S hS X).hom := rfl

/-- The comparison `(model) ⟶ (X_étale, 𝒪_X)` is an equivalence of ringed topoi: its structure
map is a component of the unit isomorphism of an equivalence of sheaf categories. -/
theorem isIso_toSmallEtaleHom_fSharp : IsIso (toSmallEtaleHom B S hS X).fSharp :=
  (toSmallEtaleStructureIso B S hS X).isIso_hom

/-- **The comparison in the other direction, as a morphism of ringed topoi
`(X_étale, 𝒪_X) ⟶ (model)`.**  Its underlying continuous functor is the comparison read from the
model to the small étale site, and its structure map is the identity: the structure sheaf of the
model is by definition the restriction of `𝒪_X` along that functor. -/
def fromSmallEtaleHom :
    RingedToposSiteHom (smallEtaleRingedTopos B S hS X) (smallEtaleModelRingedTopos B S hS X) where
  u := (smallEtaleModelEquiv B S hS X).inverse
  isContinuous := inferInstanceAs ((smallEtaleModelEquiv B S hS X).inverse.IsContinuous
    (smallEtaleModelTopology B S hS X.1) (SmallEtale.topology B S hS X.1))
  fSharp := 𝟙 _

/-- The underlying functor of `AlgebraicGeometry.Space.fromSmallEtaleHom` is the inverse of the
comparison of the small étale site with its model. -/
@[simp]
theorem fromSmallEtaleHom_u :
    (fromSmallEtaleHom B S hS X).u = (smallEtaleModelEquiv B S hS X).inverse := rfl

/-- The structure map of `AlgebraicGeometry.Space.fromSmallEtaleHom` is the identity of the
structure sheaf of the model. -/
@[simp]
theorem fromSmallEtaleHom_fSharp :
    (fromSmallEtaleHom B S hS X).fSharp = 𝟙 (smallEtaleModelStructureSheaf B S hS X) := rfl

/-! ### Sheaves of modules on the model -/

/-- The comma categories indexing the right Kan extension along the comparison of the small
étale site of `X` with its model have the limits of a complete category in the universe shape of
`AddCommGrpCat.{u}`: they are essentially small at `u`. -/
instance hasLimitsOfShape_structuredArrow_smallEtaleModelEquiv_inverse_op
    (W : (SmallEtale B S hS X.1)ᵒᵖ) (A : Type (u + 1)) [Category.{u} A] [HasLimits A] :
    HasLimitsOfShape (StructuredArrow W (smallEtaleModelEquiv B S hS X).inverse.op) A :=
  have : EssentiallySmall.{u}
      (StructuredArrow W (smallEtaleModelEquiv B S hS X).inverse.op) := inferInstance
  hasLimitsOfShape_of_essentiallySmall _ _

/-- **Restriction of `𝒪_X`-modules to the model.**  A sheaf of `𝒪_X`-modules is sent to its
sections over the objects of the model, as a sheaf of modules over the restricted structure
sheaf. -/
abbrev smallEtaleModelModuleRestriction :
    Modules.{u, u} B S hS X.1 X.2 ⥤
      SheafOfModules.{u} (ringRestriction (smallEtaleModelTopology B S hS X.1)
        (SmallEtale.topology B S hS X.1) (smallEtaleModelEquiv B S hS X).inverse
        (structureRingSheaf B S hS X)) :=
  moduleRestriction.{u} (smallEtaleModelTopology B S hS X.1) (SmallEtale.topology B S hS X.1)
    (smallEtaleModelEquiv B S hS X).inverse (structureRingSheaf B S hS X)

/-- **The Comparison Lemma for `𝒪_X`-modules and the model.**  Restriction of sheaves of
`𝒪_X`-modules to the model is an equivalence of categories. -/
def smallEtaleModelModulesEquiv :
    Modules.{u, u} B S hS X.1 X.2 ≌
      SheafOfModules.{u} (ringRestriction (smallEtaleModelTopology B S hS X.1)
        (SmallEtale.topology B S hS X.1) (smallEtaleModelEquiv B S hS X).inverse
        (structureRingSheaf B S hS X)) :=
  moduleRestrictionEquivalence.{u} (smallEtaleModelTopology B S hS X.1)
    (SmallEtale.topology B S hS X.1) (smallEtaleModelEquiv B S hS X).inverse
    (structureRingSheaf B S hS X)

/-- The functor of `AlgebraicGeometry.Space.smallEtaleModelModulesEquiv` is restriction of
modules to the model. -/
theorem smallEtaleModelModulesEquiv_functor :
    (smallEtaleModelModulesEquiv B S hS X).functor =
      smallEtaleModelModuleRestriction B S hS X := rfl

end AlgebraicGeometry.Space

end
