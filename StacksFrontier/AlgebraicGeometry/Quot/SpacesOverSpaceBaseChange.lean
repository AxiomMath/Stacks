module

public import Mathlib.CategoryTheory.Core
public import StacksFrontier.AlgebraicGeometry.Quot.CartesianFamilies
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategory
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.VaryingBase.SheafGlueing

/-!
# Base change of a family of algebraic spaces along the points of an algebraic space

Let `T` be an algebraic space over the base scheme `S` of a big fppf site, and let `𝒮_T` be the
category fibred in groupoids attached to it (Stacks 0458): its objects are the pairs `(U, t)` of a
scheme `U` of the site and a point `t ∈ T(U)`. For a property `P` of morphisms of algebraic spaces
stable under base change, a morphism `X ⟶ T` with property `P` defines a functor over the site from
`𝒮_T` to the category of families of algebraic spaces with property `P` over varying schemes, with
cartesian squares as morphisms: it sends `(U, t)` to the base change `U ×_T X ⟶ U`. An isomorphism
of such morphisms over `T` induces a 2-isomorphism of the attached functors.

This is the construction of Stacks 0E93 for every such `P`, which covers the two cases there:
finite type, and finite presentation together with flatness and properness.

## Main definitions

* `AlgebraicGeometry.SpacesOverSpace.familyProperty`: the families of algebraic spaces over a
  scheme whose structure morphism has a property `P`.
* `AlgebraicGeometry.SpacesOverSpace.CartesianFamilies`: those families with cartesian squares as
  morphisms, and `AlgebraicGeometry.SpacesOverSpace.cartesianProjection` the projection to the
  base.
* `AlgebraicGeometry.SpacesOverSpace.SpacesOver`: the groupoid of algebraic spaces `X ⟶ T` whose
  structure morphism has `P`, with isomorphisms over `T` as morphisms.
* `AlgebraicGeometry.SpacesOverSpace.baseChangeFunctor`: the functor from `SpacesOver P T` to the
  category of functors over the site from `𝒮_T` to `CartesianFamilies P`.

## Implementation notes

For the property of finite type, `CartesianFamilies P` is the category
`AlgebraicGeometry.CartesianFiniteTypeSpaces` of Stacks 0D1D, and for finite presentation, flatness
and properness it is `AlgebraicGeometry.CartesianProperFlatSpaces`; both agree by definition, as
the family properties `AlgebraicGeometry.isFiniteTypeSpace` and
`AlgebraicGeometry.isProperFlatSpace` are the property of the structure morphism read as a morphism
of algebraic spaces.

The base change of `x : X ⟶ T` along a point `t` is the presheaf fibre product
`AlgebraicGeometry.AlgebraicSpaces.fiberProduct` of the morphism `yoneda U ⟶ T` naming `t` with
`x`, so the projection to `U` is the first projection.

## References

* [Stacks Project, Tag 0E93](https://stacks.math.columbia.edu/tag/0E93)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.SpacesOverSpace

universe u

-- The points category is `Stack.fibredCategory`, a plain `def`; morphisms of it are only
-- recognised as morphisms of the Grothendieck construction once it unfolds at `implicit`
-- transparency, which every rewrite with `CategoryTheory.Pseudofunctor.CoGrothendieck.Hom.base`
-- needs. Likewise the category structure of `BasedCategory.ofFunctor` is that of its total
-- category only once `BasedCategory.ofFunctor` unfolds, which the simp lemmas for identities and
-- composites in a wide subcategory need, and the presheaf underlying
-- `AlgebraicGeometry.AlgebraicSpaces.fiberProduct` is the presheaf pullback only once that
-- definition unfolds, which the extensionality lemmas for pullbacks need.
attribute [local implicit_reducible] Stack.fibredCategory BasedCategory.ofFunctor
  AlgebraicSpaces.fiberProduct schemeSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Families of algebraic spaces over a scheme of the site whose structure morphism, read as a
morphism of algebraic spaces, has the property `P`. -/
abbrev familyProperty (P : MorphismProperty (AlgebraicSpaces B S hS)) :
    ObjectProperty (Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :=
  fun X => P (ObjectProperty.homMk X.hom : X.left ⟶ schemeSpace X.right)

/-- Families of algebraic spaces over varying schemes of the site whose structure morphism has
the property `P`, with only the cartesian squares as morphisms. -/
abbrev CartesianFamilies (P : MorphismProperty (AlgebraicSpaces B S hS)) :=
  WideSubcategory
    ((stronglyCartesianOver (spacesProjection B S hS)).inverseImage (familyProperty B S hS P).ι)

/-- The projection taking a family in `CartesianFamilies P` to its base scheme. -/
abbrev cartesianProjection (P : MorphismProperty (AlgebraicSpaces B S hS)) :
    CartesianFamilies B S hS P ⥤ BigFppfOver B S hS :=
  wideSubcategoryInclusion _ ⋙ (familyProperty B S hS P).ι ⋙ spacesProjection B S hS

/-- Algebraic spaces over `T` whose structure morphism has the property `P`, with isomorphisms
over `T` as morphisms. -/
abbrev SpacesOver (P : MorphismProperty (AlgebraicSpaces B S hS)) (T : AlgebraicSpaces B S hS) :=
  ObjectProperty.FullSubcategory (fun X : Core (Over T) => P X.of.hom)

/-- The category fibred in groupoids attached to an algebraic space `T` (Stacks 0458), whose
objects are the points `t ∈ T(U)` of `T` with values in the schemes `U` of the site. -/
abbrev pointsCategory (T : AlgebraicSpaces B S hS) : BasedCategory (BigFppfOver B S hS) :=
  (Stack.fibredCategory B S hS T.obj).val

variable {B S hS}

/-- The morphism of algebraic spaces from a scheme of the site to `T` naming a point of `T`. -/
def pointMap {T : AlgebraicSpaces B S hS} (a : (pointsCategory B S hS T).obj) :
    schemeSpace a.base ⟶ T :=
  ObjectProperty.homMk (yonedaEquiv.symm a.fiber.as)

/-- A morphism of points of `T` is a restriction of points. -/
theorem fiber_as_eq {T : AlgebraicSpaces B S hS} {a' a : (pointsCategory B S hS T).obj}
    (u : a' ⟶ a) : a'.fiber.as = T.obj.map u.base.op a.fiber.as :=
  Discrete.eq_of_hom u.fiber

/-- The base of the identity of a point of `T` is the identity. -/
@[simp]
theorem id_base {T : AlgebraicSpaces B S hS} (a : (pointsCategory B S hS T).obj) :
    (𝟙 a : a ⟶ a).base = 𝟙 a.base :=
  rfl

/-- The base of a composite of morphisms of points of `T` is the composite of the bases. -/
@[simp]
theorem comp_base {T : AlgebraicSpaces B S hS} {a'' a' a : (pointsCategory B S hS T).obj}
    (v : a'' ⟶ a') (u : a' ⟶ a) : (v ≫ u).base = v.base ≫ u.base :=
  rfl

/-- The morphism naming a point restricts along a morphism of points. -/
@[reassoc]
theorem yoneda_map_comp_pointMap_hom {T : AlgebraicSpaces B S hS}
    {a' a : (pointsCategory B S hS T).obj} (u : a' ⟶ a) :
    yoneda.map u.base ≫ (pointMap a).hom = (pointMap a').hom := by
  show yoneda.map u.base ≫ yonedaEquiv.symm a.fiber.as = yonedaEquiv.symm a'.fiber.as
  rw [fiber_as_eq u]
  exact (yonedaEquiv_symm_map u.base.op a.fiber.as).symm

variable {P : MorphismProperty (AlgebraicSpaces B S hS)} {T : AlgebraicSpaces B S hS}

/-- The base change `U ×_T X ⟶ U` of a morphism `X ⟶ T` along a point `(U, t)` of `T`, as a
family of algebraic spaces over `U`. -/
abbrev baseChangeComma (X : Over T) (a : (pointsCategory B S hS T).obj) :
    Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  ⟨AlgebraicSpaces.fiberProduct B S hS (pointMap a) X.hom, a.base,
    pullback.fst (pointMap a).hom X.hom.hom⟩

/-- The base change of a morphism with a property stable under base change has the property. -/
theorem familyProperty_baseChangeComma [P.IsStableUnderBaseChange] (X : Over T) (hX : P X.hom)
    (a : (pointsCategory B S hS T).obj) :
    familyProperty B S hS P (baseChangeComma X a) :=
  P.of_isPullback (AlgebraicSpaces.isPullback_fiberProduct B S hS (pointMap a) X.hom).flip hX

/-- The cartesian square of base changes along a morphism of points of `T`. -/
abbrev baseChangeCommaMap (X : Over T) {a' a : (pointsCategory B S hS T).obj} (u : a' ⟶ a) :
    baseChangeComma X a' ⟶ baseChangeComma X a where
  left := ObjectProperty.homMk (pullback.map (pointMap a').hom X.hom.hom (pointMap a).hom
    X.hom.hom (yoneda.map u.base) (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id]; exact (yoneda_map_comp_pointMap_hom u).symm) (by simp))
  right := u.base
  w := pullback.lift_fst _ _ _

/-- The first component of the map of base changes along a morphism of points. -/
@[reassoc]
theorem baseChangeCommaMap_left_fst (X : Over T) {a' a : (pointsCategory B S hS T).obj}
    (u : a' ⟶ a) :
    (baseChangeCommaMap X u).left.hom ≫ pullback.fst (pointMap a).hom X.hom.hom =
      pullback.fst (pointMap a').hom X.hom.hom ≫ yoneda.map u.base :=
  pullback.lift_fst _ _ _

/-- The second component of the map of base changes along a morphism of points. -/
@[reassoc]
theorem baseChangeCommaMap_left_snd (X : Over T) {a' a : (pointsCategory B S hS T).obj}
    (u : a' ⟶ a) :
    (baseChangeCommaMap X u).left.hom ≫ pullback.snd (pointMap a).hom X.hom.hom =
      pullback.snd (pointMap a').hom X.hom.hom :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The map of base changes along an identity of points is the identity. -/
theorem baseChangeCommaMap_id_left (X : Over T) (a : (pointsCategory B S hS T).obj) :
    (baseChangeCommaMap X (𝟙 a)).left.hom = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [baseChangeCommaMap_left_fst, Category.id_comp, id_base, CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  · rw [baseChangeCommaMap_left_snd, Category.id_comp]

/-- The map of base changes along a composite of points is the composite. -/
theorem baseChangeCommaMap_comp_left (X : Over T) {a'' a' a : (pointsCategory B S hS T).obj}
    (u : a'' ⟶ a') (v : a' ⟶ a) :
    (baseChangeCommaMap X (u ≫ v)).left.hom =
      (baseChangeCommaMap X u).left.hom ≫ (baseChangeCommaMap X v).left.hom := by
  apply pullback.hom_ext
  · rw [baseChangeCommaMap_left_fst, Category.assoc, baseChangeCommaMap_left_fst,
      baseChangeCommaMap_left_fst_assoc, comp_base, CategoryTheory.Functor.map_comp]
  · rw [baseChangeCommaMap_left_snd, Category.assoc, baseChangeCommaMap_left_snd,
      baseChangeCommaMap_left_snd]

/-- The square of base changes along a morphism of points of `T` is cartesian. -/
theorem isPullback_baseChangeCommaMap (X : Over T) {a' a : (pointsCategory B S hS T).obj}
    (u : a' ⟶ a) :
    IsPullback (baseChangeCommaMap X u).left.hom (pullback.fst (pointMap a').hom X.hom.hom)
      (pullback.fst (pointMap a).hom X.hom.hom) (yoneda.map u.base) := by
  refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback _ _).flip
  have key : ∀ g : yoneda.obj a'.base ⟶ T.obj, (pointMap a').hom = g →
      IsPullback (pullback.snd (pointMap a').hom X.hom.hom)
        (pullback.fst (pointMap a').hom X.hom.hom) X.hom.hom g := by
    rintro g rfl
    exact (IsPullback.of_hasPullback (pointMap a').hom X.hom.hom).flip
  rw [baseChangeCommaMap_left_snd]
  exact key _ (yoneda_map_comp_pointMap_hom u).symm

/-- A morphism of families over the site whose square of presheaves over its base map is
cartesian is strongly cartesian. -/
private theorem isStronglyCartesian_of_isPullback_right
    {A C : Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)} (m : A ⟶ C)
    (h : IsPullback m.left.hom A.hom C.hom (yoneda.map m.right)) :
    (spacesProjection B S hS).IsStronglyCartesian m.right m :=
  SpacesDescent.isStronglyCartesian_of_isPullback m.right m rfl rfl (by simp)
    (by simp only [eqToHom_refl, CategoryTheory.Functor.map_id]; exact Category.comp_id _)
    (by simp only [eqToHom_refl, CategoryTheory.Functor.map_id]; exact Category.comp_id _) h

/-- The square of base changes along a morphism of points of `T` is strongly cartesian over the
site. -/
theorem isStronglyCartesian_baseChangeCommaMap (X : Over T)
    {a' a : (pointsCategory B S hS T).obj} (u : a' ⟶ a) :
    (spacesProjection B S hS).IsStronglyCartesian (baseChangeCommaMap X u).right
      (baseChangeCommaMap X u) :=
  isStronglyCartesian_of_isPullback_right _ (isPullback_baseChangeCommaMap X u)

/-- The map of base changes along a point `(U, t)` induced by a morphism over `T`. -/
abbrev baseChangeCommaHom {X Y : Over T} (e : X ⟶ Y) (a : (pointsCategory B S hS T).obj) :
    baseChangeComma X a ⟶ baseChangeComma Y a where
  left := ObjectProperty.homMk (pullback.map (pointMap a).hom X.hom.hom (pointMap a).hom
    Y.hom.hom (𝟙 _) e.left.hom (𝟙 _) (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id]; exact (congrArg (fun k => k.hom) (Over.w e)).symm))
  right := 𝟙 a.base
  w := (pullback.lift_fst _ _ _).trans (by
    rw [CategoryTheory.Functor.map_id]
    exact (Category.comp_id _).trans (Category.comp_id _).symm)

/-- The first component of the map of base changes induced by a morphism over `T`. -/
@[reassoc]
theorem baseChangeCommaHom_left_fst {X Y : Over T} (e : X ⟶ Y)
    (a : (pointsCategory B S hS T).obj) :
    (baseChangeCommaHom e a).left.hom ≫ pullback.fst (pointMap a).hom Y.hom.hom =
      pullback.fst (pointMap a).hom X.hom.hom :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- The second component of the map of base changes induced by a morphism over `T`. -/
@[reassoc]
theorem baseChangeCommaHom_left_snd {X Y : Over T} (e : X ⟶ Y)
    (a : (pointsCategory B S hS T).obj) :
    (baseChangeCommaHom e a).left.hom ≫ pullback.snd (pointMap a).hom Y.hom.hom =
      pullback.snd (pointMap a).hom X.hom.hom ≫ e.left.hom :=
  pullback.lift_snd _ _ _

/-- The map of base changes induced by an isomorphism over `T` is strongly cartesian. -/
theorem isStronglyCartesian_baseChangeCommaHom {X Y : Over T} (e : X ⟶ Y) [IsIso e]
    (a : (pointsCategory B S hS T).obj) :
    (spacesProjection B S hS).IsStronglyCartesian (baseChangeCommaHom e a).right
      (baseChangeCommaHom e a) := by
  have : IsIso e.left := inferInstanceAs (IsIso ((Over.forget T).map e))
  have : IsIso e.left.hom :=
    inferInstanceAs (IsIso ((ObjectProperty.ι fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
      IsAlgebraicSpace B S hS F).map e.left))
  have : IsIso (baseChangeCommaHom e a).left.hom := by
    dsimp only [baseChangeCommaHom, ObjectProperty.homMk]
    infer_instance
  exact isStronglyCartesian_of_isPullback_right _
    (IsPullback.of_horiz_isIso ⟨(baseChangeCommaHom e a).w⟩)

/-- The maps of base changes induced by a morphism over `T` are natural in the point. -/
theorem baseChangeCommaMap_comp_baseChangeCommaHom_left {X Y : Over T} (e : X ⟶ Y)
    {a' a : (pointsCategory B S hS T).obj} (u : a' ⟶ a) :
    (baseChangeCommaMap X u).left.hom ≫ (baseChangeCommaHom e a).left.hom =
      (baseChangeCommaHom e a').left.hom ≫ (baseChangeCommaMap Y u).left.hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, baseChangeCommaHom_left_fst, baseChangeCommaMap_left_fst,
      baseChangeCommaMap_left_fst, baseChangeCommaHom_left_fst_assoc]
  · rw [Category.assoc, Category.assoc, baseChangeCommaHom_left_snd, baseChangeCommaMap_left_snd,
      baseChangeCommaMap_left_snd_assoc, baseChangeCommaHom_left_snd]

/-- The map of base changes induced by the identity over `T` is the identity. -/
theorem baseChangeCommaHom_id_left (X : Over T) (a : (pointsCategory B S hS T).obj) :
    (baseChangeCommaHom (𝟙 X) a).left.hom = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [baseChangeCommaHom_left_fst, Category.id_comp]
  · rw [baseChangeCommaHom_left_snd, Category.id_comp]
    exact Category.comp_id _

/-- The map of base changes induced by a composite over `T` is the composite. -/
theorem baseChangeCommaHom_comp_left {X Y Z : Over T} (e : X ⟶ Y) (e' : Y ⟶ Z)
    (a : (pointsCategory B S hS T).obj) :
    (baseChangeCommaHom (e ≫ e') a).left.hom =
      (baseChangeCommaHom e a).left.hom ≫ (baseChangeCommaHom e' a).left.hom := by
  apply pullback.hom_ext
  · rw [baseChangeCommaHom_left_fst, Category.assoc, baseChangeCommaHom_left_fst,
      baseChangeCommaHom_left_fst]
  · rw [baseChangeCommaHom_left_snd, Category.assoc, baseChangeCommaHom_left_snd,
      baseChangeCommaHom_left_snd_assoc]
    rfl

variable [P.IsStableUnderBaseChange]

/-- The family `U ×_T X ⟶ U` attached to a point `(U, t)` of `T`. -/
abbrev baseChangeObj (X : SpacesOver B S hS P T) (a : (pointsCategory B S hS T).obj) :
    CartesianFamilies B S hS P :=
  ⟨⟨baseChangeComma X.1.of a, familyProperty_baseChangeComma X.1.of X.2 a⟩⟩

/-- The functor over the site from `𝒮_T` to the families with property `P` attached to an
algebraic space over `T` with property `P`: it sends a point `(U, t)` to `U ×_T X ⟶ U`. -/
def baseChangeBased (X : SpacesOver B S hS P T) :
    pointsCategory B S hS T ⥤ᵇ BasedCategory.ofFunctor (cartesianProjection B S hS P) where
  toFunctor :=
    { obj a := baseChangeObj X a
      map u := ⟨ObjectProperty.homMk (baseChangeCommaMap X.1.of u),
        isStronglyCartesian_baseChangeCommaMap X.1.of u⟩
      map_id a := by
        apply WideSubcategory.hom_ext
        apply ObjectProperty.hom_ext
        apply Comma.hom_ext
        · apply ObjectProperty.hom_ext
          exact baseChangeCommaMap_id_left X.1.of a
        · rfl
      map_comp u v := by
        apply WideSubcategory.hom_ext
        apply ObjectProperty.hom_ext
        apply Comma.hom_ext
        · apply ObjectProperty.hom_ext
          exact baseChangeCommaMap_comp_left X.1.of u v
        · rfl }
  w := rfl

/-- The 2-morphism between the base-change functors induced by an isomorphism over `T`. -/
def baseChangeBasedHom {X Y : SpacesOver B S hS P T} (e : X ⟶ Y) :
    baseChangeBased X ⟶ baseChangeBased Y where
  app a := ⟨ObjectProperty.homMk (baseChangeCommaHom e.hom.iso.hom a),
    isStronglyCartesian_baseChangeCommaHom e.hom.iso.hom a⟩
  naturality a' a u := by
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · apply ObjectProperty.hom_ext
      exact baseChangeCommaMap_comp_baseChangeCommaHom_left e.hom.iso.hom u
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
  isHomLift' a := IsHomLift.map (p := cartesianProjection B S hS P)
    (⟨ObjectProperty.homMk (baseChangeCommaHom e.hom.iso.hom a),
      isStronglyCartesian_baseChangeCommaHom e.hom.iso.hom a⟩ :
        baseChangeObj X a ⟶ baseChangeObj Y a)

/-- The functor sending an algebraic space `X` over `T` whose structure morphism has the property
`P` to the functor over the site from `𝒮_T` to the families with property `P` sending a point
`(U, t)` to the base change `U ×_T X ⟶ U`; an isomorphism over `T` goes to the induced
2-isomorphism. -/
def baseChangeFunctor :
    SpacesOver B S hS P T ⥤
      (pointsCategory B S hS T ⥤ᵇ BasedCategory.ofFunctor (cartesianProjection B S hS P)) where
  obj := baseChangeBased
  map := baseChangeBasedHom
  map_id X := by
    apply BasedNatTrans.ext
    ext a
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · apply ObjectProperty.hom_ext
      exact baseChangeCommaHom_id_left X.1.of a
    · rfl
  map_comp e e' := by
    apply BasedNatTrans.ext
    ext a
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · apply ObjectProperty.hom_ext
      exact baseChangeCommaHom_comp_left e.hom.iso.hom e'.hom.iso.hom a
    · exact (Category.comp_id _).symm

end AlgebraicGeometry.SpacesOverSpace

end
