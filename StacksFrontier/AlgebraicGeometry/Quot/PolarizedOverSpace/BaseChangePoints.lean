module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedOverSpace.RepresentedPolarized
public import StacksFrontier.CategoryTheory.Bicategory.CoGrothendieckInverseImage
public import StacksFrontier.CategoryTheory.Comma.LiftConst

/-!
# The base changes of a polarized family of algebraic spaces along the points of the base

Let `(X ⟶ T, L)` be a polarized family of algebraic spaces over `T` (the left-hand side of
Stacks 0E94). Its structure morphism is representable (Stacks 0D34), so for every point
`(U, t)` of `T` the fibre product `U ×_T X` is represented by a scheme `Z_{(U,t)}` of the site,
with projections `Z_{(U,t)} ⟶ U` and `yoneda Z_{(U,t)} ⟶ X`. A morphism of points induces the
morphism of fibre products, and an isomorphism `X ≅ X'` over `T` induces one on every fibre
product.

This file packages these as objects and morphisms of the comma category
`Comma arrowSpace (forget modulesPseudofunctor)`: a triple of the arrow `Z_{(U,t)} ⟶ U`, the pair
`(X, L)` and the projection `yoneda Z_{(U,t)} ⟶ X`. Taking inverse images of `L`
(`CategoryTheory.Pseudofunctor.CoGrothendieck.inverseImage`) then gives the polarized families
of Stacks 0E94.

## Main definitions

* `AlgebraicGeometry.PolarizedOverSpace.fibreScheme`: the scheme `Z_{(U,t)}`.
* `AlgebraicGeometry.PolarizedOverSpace.fibreComma`: the functor from the points of `T` to the
  comma category attached to one polarized family.
* `AlgebraicGeometry.PolarizedOverSpace.fibreCommaFunctor`: the same, functorial in the family.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Pseudofunctor.CoGrothendieck

universe u

namespace AlgebraicGeometry.PolarizedOverSpace

-- The points category is a plain `def`; its morphisms are morphisms of a Grothendieck construction
-- only once it unfolds at `implicit` transparency, which rewriting with their bases needs.
attribute [local implicit_reducible] Stack.fibredCategory BasedCategory.ofFunctor schemeSpace
  Functor.toPseudofunctor' pseudofunctorOfIsLocallyDiscrete typeToGrpd Grpd.forgetToCat
  MorphismProperty

variable {B : BigFppfSite.{u}} {T : AlgebraicSpaces B integerBase (hZ B)}

/-- The category of points of `T` (Stacks 0458). -/
abbrev Points (T : AlgebraicSpaces B integerBase (hZ B)) :=
  SpacesOverSpace.pointsCategory B integerBase (hZ B) T

variable (B T) in
/-- A polarized family over `T` as an object of the Grothendieck construction of all modules on
algebraic spaces: `(X, L)`. -/
def familyPair : PolarizedSpacesOver B T ⥤
    Pseudofunctor.CoGrothendieck (Space.modulesPseudofunctor B integerBase (hZ B)) :=
  Core.inclusion _ ⋙ ObjectProperty.ι _ ⋙
    forgetComp (Space.modulesPseudofunctor B integerBase (hZ B)) (familyFunctor B T)

section Family

variable (ξ : PolarizedSpacesOver B T)

/-- The structure morphism `X ⟶ T` of a polarized family. -/
abbrev familyMap : ((familyPair B T).obj ξ).base ⟶ T := ξ.of.obj.base.obj.of.hom

/-- The structure morphism of a polarized family is representable (Stacks 0D34). -/
theorem relativelyRepresentable_familyMap :
    yoneda.relativelyRepresentable (familyMap ξ).hom :=
  ξ.of.property.2.relativelyRepresentable

/-- The scheme representing the fibre product `U ×_T X` at a point `(U, t)` of `T`. -/
def fibreScheme (a : (Points T).obj) : Site B :=
  (relativelyRepresentable_familyMap ξ).pullback (SpacesOverSpace.pointMap a).hom

/-- The projection `Z_{(U,t)} ⟶ U`. -/
def fibreProj (a : (Points T).obj) : fibreScheme ξ a ⟶ a.base :=
  (relativelyRepresentable_familyMap ξ).snd (SpacesOverSpace.pointMap a).hom

/-- The projection `yoneda Z_{(U,t)} ⟶ X`. -/
def fibreFst (a : (Points T).obj) :
    yoneda.obj (fibreScheme ξ a) ⟶ ((familyPair B T).obj ξ).base.obj :=
  (relativelyRepresentable_familyMap ξ).fst (SpacesOverSpace.pointMap a).hom

/-- The fibre product square at a point. -/
theorem isPullback_fibre (a : (Points T).obj) :
    IsPullback (fibreFst ξ a) (yoneda.map (fibreProj ξ a)) (familyMap ξ).hom
      (SpacesOverSpace.pointMap a).hom :=
  (relativelyRepresentable_familyMap ξ).isPullback _

/-- The morphism of fibre products induced by a morphism of points. -/
def fibreMap {a' a : (Points T).obj} (u : a' ⟶ a) : fibreScheme ξ a' ⟶ fibreScheme ξ a :=
  (relativelyRepresentable_familyMap ξ).lift (fibreFst ξ a') (fibreProj ξ a' ≫ u.base) (by
    rw [(isPullback_fibre ξ a').w, Functor.map_comp, Category.assoc,
      SpacesOverSpace.yoneda_map_comp_pointMap_hom u])

/-- The morphism `fibreMap ξ u` commutes with the projections to `X`. -/
@[reassoc]
theorem fibreMap_fst {a' a : (Points T).obj} (u : a' ⟶ a) :
    yoneda.map (fibreMap ξ u) ≫ fibreFst ξ a = fibreFst ξ a' :=
  (relativelyRepresentable_familyMap ξ).lift_fst _ _ _

/-- The morphism `fibreMap ξ u` lies over the base morphism of `u`. -/
@[reassoc]
theorem fibreMap_proj {a' a : (Points T).obj} (u : a' ⟶ a) :
    fibreMap ξ u ≫ fibreProj ξ a = fibreProj ξ a' ≫ u.base :=
  (relativelyRepresentable_familyMap ξ).lift_snd _ _ _

/-- Two morphisms into a fibre product agree when their two projections do. -/
theorem fibre_hom_ext {W : Site B} {a : (Points T).obj} {k k' : W ⟶ fibreScheme ξ a}
    (h₁ : yoneda.map k ≫ fibreFst ξ a = yoneda.map k' ≫ fibreFst ξ a)
    (h₂ : k ≫ fibreProj ξ a = k' ≫ fibreProj ξ a) : k = k' :=
  (relativelyRepresentable_familyMap ξ).hom_ext h₁ h₂

/-- The identity of a point induces the identity of its fibre product. -/
theorem fibreMap_id (a : (Points T).obj) : fibreMap ξ (𝟙 a) = 𝟙 _ :=
  fibre_hom_ext ξ (by rw [fibreMap_fst, CategoryTheory.Functor.map_id, Category.id_comp])
    (by rw [fibreMap_proj, Category.id_comp]; exact Category.comp_id _)

/-- The morphism of fibre products induced by a composite of points is the composite. -/
theorem fibreMap_comp {a'' a' a : (Points T).obj} (v : a'' ⟶ a') (u : a' ⟶ a) :
    fibreMap ξ (v ≫ u) = fibreMap ξ v ≫ fibreMap ξ u :=
  fibre_hom_ext ξ (by rw [fibreMap_fst, Functor.map_comp, Category.assoc, fibreMap_fst,
      fibreMap_fst])
    (by rw [fibreMap_proj, Category.assoc, fibreMap_proj, fibreMap_proj_assoc]; rfl)

/-- The arrow `Z_{(U,t)} ⟶ U` of the site. -/
abbrev fibreArrow (a : (Points T).obj) : Arrow (Site B) := Arrow.mk (fibreProj ξ a)

/-- The morphism of arrows induced by a morphism of points. -/
def fibreArrowMap {a' a : (Points T).obj} (u : a' ⟶ a) :
    @Quiver.Hom (Arrow (Site B)) CategoryStruct.toQuiver (fibreArrow ξ a') (fibreArrow ξ a) :=
  Arrow.homMk (fibreMap ξ u) u.base (fibreMap_proj ξ u)

/-- The arrows `Z_{(U,t)} ⟶ U`, functorially in the point. -/
def fibreArrowFunctor : (Points T).obj ⥤ Arrow (Site B) where
  obj := fibreArrow ξ
  map := fibreArrowMap ξ
  map_id a := Arrow.hom_ext _ _ (fibreMap_id ξ a) rfl
  map_comp v u := Arrow.hom_ext _ _ (fibreMap_comp ξ v u) rfl

/-- The projection `yoneda Z_{(U,t)} ⟶ X`, as a morphism of algebraic spaces. -/
abbrev fibreSpaceMap (a : (Points T).obj) :
    (arrowSpace B).obj ((fibreArrowFunctor ξ).obj a) ⟶
      (forget (Space.modulesPseudofunctor B integerBase (hZ B))).obj ((familyPair B T).obj ξ) :=
  ObjectProperty.homMk (fibreFst ξ a)

/-- The projections `yoneda Z_{(U,t)} ⟶ X` are natural in the point. -/
theorem fibreSpaceMap_naturality {a' a : (Points T).obj} (u : a' ⟶ a) :
    (arrowSpace B).map ((fibreArrowFunctor ξ).map u) ≫ fibreSpaceMap ξ a = fibreSpaceMap ξ a' :=
  ObjectProperty.hom_ext _ (fibreMap_fst ξ u)

/-- **The base changes of a polarized family along the points of `T`**, as triples
`(Z_{(U,t)} ⟶ U, (X, L), yoneda Z_{(U,t)} ⟶ X)`. -/
abbrev fibreComma : (Points T).obj ⥤
    Comma (arrowSpace B) (forget (Space.modulesPseudofunctor B integerBase (hZ B))) :=
  Comma.liftConst (fibreArrowFunctor ξ) ((familyPair B T).obj ξ) (fibreSpaceMap ξ)
    (fibreSpaceMap_naturality ξ)

end Family

section Morphism

variable {ξ ξ' : PolarizedSpacesOver B T} (e : ξ ⟶ ξ')

/-- An isomorphism of polarized families lies over `T`. -/
@[reassoc]
theorem familyPair_map_base_comp : ((familyPair B T).map e).base ≫ familyMap ξ' = familyMap ξ :=
  Over.w e.iso.hom.hom.base.hom.iso.hom

/-- An isomorphism of polarized families lies over `T`, as morphisms of presheaves. -/
@[reassoc]
theorem familyPair_map_base_hom_comp :
    ((familyPair B T).map e).base.hom ≫ (familyMap ξ').hom = (familyMap ξ).hom :=
  congrArg InducedCategory.Hom.hom (familyPair_map_base_comp e)

/-- The morphism of fibre products induced by an isomorphism of polarized families. -/
def fibreHomMap (a : (Points T).obj) : fibreScheme ξ a ⟶ fibreScheme ξ' a :=
  (relativelyRepresentable_familyMap ξ').lift (fibreFst ξ a ≫ ((familyPair B T).map e).base.hom)
    (fibreProj ξ a) (by
      rw [Category.assoc, familyPair_map_base_hom_comp]
      exact (isPullback_fibre ξ a).w)

/-- The morphism `fibreHomMap e a` is compatible with the projections to `X` and `X'`. -/
@[reassoc]
theorem fibreHomMap_fst (a : (Points T).obj) :
    yoneda.map (fibreHomMap e a) ≫ fibreFst ξ' a =
      fibreFst ξ a ≫ ((familyPair B T).map e).base.hom :=
  (relativelyRepresentable_familyMap ξ').lift_fst _ _ _

/-- The morphism `fibreHomMap e a` lies over `U`. -/
@[reassoc]
theorem fibreHomMap_proj (a : (Points T).obj) :
    fibreHomMap e a ≫ fibreProj ξ' a = fibreProj ξ a :=
  (relativelyRepresentable_familyMap ξ').lift_snd _ _ _

/-- The morphisms `fibreHomMap e a` are natural in the point `a`. -/
theorem fibreHomMap_naturality {a' a : (Points T).obj} (u : a' ⟶ a) :
    fibreMap ξ u ≫ fibreHomMap e a = fibreHomMap e a' ≫ fibreMap ξ' u :=
  fibre_hom_ext ξ' (by
      rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, fibreHomMap_fst,
        fibreMap_fst, fibreMap_fst_assoc, fibreHomMap_fst])
    (by rw [Category.assoc, Category.assoc, fibreHomMap_proj, fibreMap_proj, fibreMap_proj,
      fibreHomMap_proj_assoc])

/-- The morphisms of arrows induced by an isomorphism of polarized families. -/
def fibreArrowNatTrans : fibreArrowFunctor ξ ⟶ fibreArrowFunctor ξ' where
  app a := Arrow.homMk (fibreHomMap e a) (𝟙 a.base)
    ((fibreHomMap_proj e a).trans (Category.comp_id _).symm)
  naturality a' a u := Arrow.hom_ext _ _ (fibreHomMap_naturality e u)
    ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- The morphisms of arrows induced by `e` are compatible with the projections to `X` and `X'`. -/
theorem fibreArrowNatTrans_compat (a : (Points T).obj) :
    (arrowSpace B).map ((fibreArrowNatTrans e).app a) ≫ fibreSpaceMap ξ' a =
      fibreSpaceMap ξ a ≫
        (forget (Space.modulesPseudofunctor B integerBase (hZ B))).map ((familyPair B T).map e) :=
  ObjectProperty.hom_ext _ (fibreHomMap_fst e a)

/-- The natural transformation of triples induced by an isomorphism of polarized families. -/
abbrev fibreCommaNatTrans : fibreComma ξ ⟶ fibreComma ξ' :=
  Comma.liftConstHom (fibreSpaceMap_naturality ξ) (fibreSpaceMap_naturality ξ')
    (fibreArrowNatTrans e) ((familyPair B T).map e) (fibreArrowNatTrans_compat e)

end Morphism

/-- The identity of a polarized family induces the identity on every fibre product. -/
theorem fibreHomMap_id (ξ : PolarizedSpacesOver B T) (a : (Points T).obj) :
    fibreHomMap (𝟙 ξ) a = 𝟙 _ :=
  fibre_hom_ext ξ (by
      simp only [fibreHomMap_fst, CategoryTheory.Functor.map_id, Category.id_comp]
      exact Category.comp_id _)
    (by rw [fibreHomMap_proj, Category.id_comp])

/-- The morphism of fibre products induced by a composite of isomorphisms is the composite. -/
theorem fibreHomMap_comp {ξ ξ' ξ'' : PolarizedSpacesOver B T} (e : ξ ⟶ ξ') (e' : ξ' ⟶ ξ'')
    (a : (Points T).obj) : fibreHomMap (e ≫ e') a = fibreHomMap e a ≫ fibreHomMap e' a :=
  fibre_hom_ext ξ'' (by
      rw [fibreHomMap_fst, yoneda.map_comp, Category.assoc, fibreHomMap_fst,
        fibreHomMap_fst_assoc, (familyPair B T).map_comp]
      rfl)
    (by rw [fibreHomMap_proj, Category.assoc, fibreHomMap_proj, fibreHomMap_proj])

/-- The identity of a polarized family induces the identity natural transformation. -/
theorem fibreArrowNatTrans_id (ξ : PolarizedSpacesOver B T) :
    fibreArrowNatTrans (𝟙 ξ) = 𝟙 _ :=
  NatTrans.ext (funext fun a => Arrow.hom_ext _ _ (fibreHomMap_id ξ a) rfl)

/-- The natural transformation induced by a composite of isomorphisms is the composite. -/
theorem fibreArrowNatTrans_comp {ξ ξ' ξ'' : PolarizedSpacesOver B T} (e : ξ ⟶ ξ') (e' : ξ' ⟶ ξ'') :
    fibreArrowNatTrans (e ≫ e') = fibreArrowNatTrans e ≫ fibreArrowNatTrans e' :=
  NatTrans.ext (funext fun a => Arrow.hom_ext _ _ (fibreHomMap_comp e e' a)
    (Category.comp_id _).symm)

variable (B T) in
/-- **The base changes of polarized families along the points of `T`, functorially in the
family.** -/
def fibreCommaFunctor : PolarizedSpacesOver B T ⥤ ((Points T).obj ⥤
    Comma (arrowSpace B) (forget (Space.modulesPseudofunctor B integerBase (hZ B)))) where
  obj := fibreComma
  map := fibreCommaNatTrans
  map_id ξ := Comma.liftConstHom_id _ _ _ _ (fibreArrowNatTrans_id ξ) ((familyPair B T).map_id ξ)
  map_comp e e' := Comma.liftConstHom_comp _ _ _ _ _ _ _ _ _ _ _ _
    (fibreArrowNatTrans_comp e e') ((familyPair B T).map_comp e e')

end AlgebraicGeometry.PolarizedOverSpace

end
