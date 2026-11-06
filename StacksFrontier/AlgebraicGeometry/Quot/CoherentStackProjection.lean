module

public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStack

/-!
# The projection of the stack of coherent sheaves to its base (Stacks 08LP)

Let `f : X ⟶ Y` be a finitely presented morphism of algebraic spaces over a scheme `S` of a big
fppf site, the standing data of Stacks 08KB, and let `Coh_{X/Y}` be the category of coherent
sheaves with proper support of that tag.  Stacks 08LP observes that the rule which forgets the
module,

`(T, g, ℱ) ↦ (T, g)`,

is a 1-morphism `Coh_{X/Y} ⟶ 𝒮_Y` of categories over `(Sch/S)_fppf`, where `𝒮_Y` is the category
fibred in sets attached to `Y` — in the alternative notation of the source, the category of
schemes of the site over `Y`.

## Main definitions

* `AlgebraicGeometry.Space.baseBasedCategory`: `𝒮_Y`, the test schemes of the site over an
  algebraic space `Y`, as a category over the big fppf site of `S`.
* `AlgebraicGeometry.Space.coherentBasedCategory`: `Coh_{X/Y}` as a category over the big fppf
  site of `S`.
* `AlgebraicGeometry.Space.coherentToBase`: **Stacks 08LP**, the 1-morphism
  `Coh_{X/Y} ⟶ 𝒮_Y` which forgets the module.
* `AlgebraicGeometry.Space.baseBasedMap`: the 1-morphism `𝒮_{Y'} ⟶ 𝒮_Y` induced by a morphism
  `Y' ⟶ Y` of algebraic spaces, which is the bottom row of the square of Stacks 08LP.

## Main results

* `AlgebraicGeometry.Space.coherentToBase_toFunctor`: the underlying functor of the 1-morphism
  is the projection of Stacks 08KB, so the 1-morphism really is the rule that forgets the module.
* `AlgebraicGeometry.Space.baseBasedCategory_faithful`: the structure functor of `𝒮_Y` is
  faithful, `𝒮_Y` being fibred in sets.

## Implementation notes

`𝒮_Y` is `AlgebraicGeometry.Space.SchemesOver`, the costructured arrows of the inclusion of the
schemes of the site as algebraic spaces, whose objects are exactly the pairs `(T, g)` of the
source and whose morphisms are the morphisms of schemes over `Y`.  By the Yoneda lemma a morphism
`g : T ⟶ Y` of algebraic spaces with `T` a scheme of the site is an element of `Y` over `T`, so
this is the category of elements of the functor of points of `Y`, that is the category fibred in
sets attached to `Y`.

The hom-sets of `Coh_{X/Y}` live one universe above those of `𝒮_Y`: a morphism of `Coh_{X/Y}`
carries a morphism of modules, and the modules are sheaves on a site.  The 2-category of
categories over a base in which the square of Stacks 08LP is formed has a single hom universe,
so the hom-sets of `𝒮_Y` are raised to that universe with `CategoryTheory.ULiftHom`; this changes
neither the objects nor the isomorphism class of the category over the site.

The category structure on `Coh_{X/Y}` is the specification
`AlgebraicGeometry.Space.CoherentCategoryData` of Stacks 08KB, supplied as a parameter, as it is
for Stacks 08W5: that tag names `Coh_{X/Y}` a category by designation, and the specification pins
its hom-sets, identities, composition and projection, so a statement about the projection below
is a statement about the functor of the source.

## References

* [Stacks Project, Tag 08LP](https://stacks.math.columbia.edu/tag/08LP)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 04ZZ](https://stacks.math.columbia.edu/tag/04ZZ)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The underlying morphism of schemes of a composite of morphisms of test schemes.  This is
`CategoryTheory.Comma.comp_left` for the category structure that
`CategoryTheory.CostructuredArrow` carries in its own right. -/
@[simp]
theorem schemesOver_comp_left {Y : AlgebraicSpaces B S hS} {T T' T'' : SchemesOver Y}
    (m : T ⟶ T') (n : T' ⟶ T'') : (m ≫ n).left = m.left ≫ n.left :=
  rfl

/-! ### The base category `𝒮_Y` -/

/-- The underlying category of `𝒮_Y`: the test schemes of the site over the algebraic space `Y`,
with their hom-sets raised to the universe of the hom-sets of `Coh_{X/Y}`. -/
abbrev BaseObjects (Y : AlgebraicSpaces B S hS) : Type (u + 1) :=
  ULiftHom.{u + 1} (SchemesOver Y)

/-- `𝒮_Y`, the category fibred in sets attached to an algebraic space `Y`, as a category over the
big fppf site of `S`: its objects are the pairs `(T, g)` of a scheme `T` of the site and a
morphism `g : T ⟶ Y`, and it projects `(T, g)` to `T`. -/
def baseBasedCategory (Y : AlgebraicSpaces B S hS) :
    BasedCategory.{u + 1, u + 1} (BigFppfOver B S hS) where
  obj := BaseObjects Y
  p := ULiftHom.down ⋙ CostructuredArrow.proj (schemeSpaceFunctor B S hS) Y

/-- The objects of `𝒮_Y` are the test schemes over `Y`. -/
theorem baseBasedCategory_obj (Y : AlgebraicSpaces B S hS) :
    (baseBasedCategory Y).obj = BaseObjects Y :=
  rfl

/-- **The structure functor of `𝒮_Y` is faithful.**  A morphism of `𝒮_Y` is a morphism of test
schemes together with the commutation with the two morphisms to `Y`, so it is determined by that
morphism of schemes; this is the shape in which the fibres of `𝒮_Y` being sets is used. -/
theorem baseBasedCategory_faithful (Y : AlgebraicSpaces B S hS) :
    (baseBasedCategory Y).p.Faithful where
  map_injective {_ _} m n h := ULift.ext (CostructuredArrow.hom_ext m.down n.down h)

/-- The 1-morphism `𝒮_{Y'} ⟶ 𝒮_Y` attached to a morphism `g : Y' ⟶ Y` of algebraic spaces: it
sends a test scheme `(T, h)` over `Y'` to the test scheme `(T, h ≫ g)` over `Y`, and is the
identity on the underlying morphisms of test schemes. -/
def baseBasedMap {Y' Y : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) :
    baseBasedCategory Y' ⥤ᵇ baseBasedCategory Y where
  toFunctor :=
    (ULiftHom.down ⋙ CostructuredArrow.map g ⋙ ULiftHom.up : BaseObjects Y' ⥤ BaseObjects Y)
  w := rfl

/-- The 1-morphism `𝒮_{Y'} ⟶ 𝒮_Y` postcomposes the morphism to the base with `g`. -/
theorem baseBasedMap_obj {Y' Y : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) (T : BaseObjects Y') :
    (baseBasedMap g).obj T = ULiftHom.objUp ((CostructuredArrow.map g).obj T.objDown) :=
  rfl

/-! ### `Coh_{X/Y}` as a category over the site, and the projection -/

variable {D : CoherentSituation B S hS} {hc : ModulePushforwardCoherence B S hS}

/-- **The projection of `Coh_{X/Y}` to the schemes of the site, written out.**  It sends an
object `(T, g, ℱ)` to the scheme `T` and a morphism to the morphism of schemes its base map
carries. -/
def coherentSiteProjection (cd : CoherentCategoryData hc D) :
    letI : Category.{u + 1} (CoherentObject D) := cd.category
    CoherentObject D ⥤ BigFppfOver B S hS :=
  letI : Category.{u + 1} (CoherentObject D) := cd.category
  { obj := fun A => A.T.left
    map := fun {A A'} m => ((Equiv.cast (cd.hom_type A A')) m).base.left
    map_id := fun A => by rw [cd.identity]; rfl
    map_comp := fun {A A' A''} m n => by rw [cd.composition]; rfl }

/-- **The written-out projection is the projection of Stacks 08KB followed by the projection of
the test schemes to the schemes of the site.** -/
theorem coherentSiteProjection_eq (cd : CoherentCategoryData hc D) :
    letI : Category.{u + 1} (CoherentObject D) := cd.category
    cd.projection ⋙ CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y =
      coherentSiteProjection cd := by
  let _ : Category.{u + 1} (CoherentObject D) := cd.category
  refine CategoryTheory.Functor.ext
    (fun A => congrArg CostructuredArrow.left (cd.projection_obj A)) (fun A A' m => ?_)
  change (cd.projection.map m).left = _
  rw [cd.projection_map m]
  change (eqToHom (cd.projection_obj A)).left ≫ _ ≫ (eqToHom (cd.projection_obj A').symm).left = _
  rw [CostructuredArrow.eqToHom_left, CostructuredArrow.eqToHom_left]
  rfl

/-- `Coh_{X/Y}` as a category over the big fppf site of `S`: the category of Stacks 08KB,
projecting an object `(T, g, ℱ)` to the scheme `T`. -/
def coherentBasedCategory (cd : CoherentCategoryData hc D) :
    BasedCategory.{u + 1, u + 1} (BigFppfOver B S hS) where
  obj := CoherentObject D
  category := cd.category
  p := coherentSiteProjection cd

/-- The objects of `Coh_{X/Y}` as a category over the site are the objects of Stacks 08KB. -/
theorem coherentBasedCategory_obj (cd : CoherentCategoryData hc D) :
    (coherentBasedCategory cd).obj = CoherentObject D :=
  rfl

/-- **The rule `(T, g, ℱ) ↦ (T, g)` as a functor.**  It sends an object of `Coh_{X/Y}` to its
test scheme over `Y` and a morphism to its base map. -/
def coherentToBaseFunctor (cd : CoherentCategoryData hc D) :
    letI : Category.{u + 1} (CoherentObject D) := cd.category
    CoherentObject D ⥤ BaseObjects D.Y :=
  letI : Category.{u + 1} (CoherentObject D) := cd.category
  { obj := fun A => ULiftHom.objUp A.T
    map := fun {A A'} m => ULift.up ((Equiv.cast (cd.hom_type A A')) m).base
    map_id := fun A => by rw [cd.identity]; rfl
    map_comp := fun {A A' A''} m n => by rw [cd.composition]; rfl }

/-- **Stacks 08LP, the projection to the base.**  The rule `(T, g, ℱ) ↦ (T, g)` which forgets the
module is a 1-morphism `Coh_{X/Y} ⟶ 𝒮_Y` of categories over the big fppf site of `S`: it lands in
the test schemes over `Y` by construction, and the scheme it names is the one `Coh_{X/Y}` already
projects to. -/
@[stacks 08LP "the projection to the base"]
def coherentToBase (cd : CoherentCategoryData hc D) :
    coherentBasedCategory cd ⥤ᵇ baseBasedCategory D.Y where
  toFunctor := coherentToBaseFunctor cd
  w := rfl

/-- The projection to the base sends an object of `Coh_{X/Y}` to its test scheme over `Y`. -/
@[simp]
theorem coherentToBase_obj (cd : CoherentCategoryData hc D) (A : CoherentObject D) :
    (coherentToBase cd).obj A = ULiftHom.objUp A.T :=
  rfl

/-- The projection to the base sends a morphism of `Coh_{X/Y}` to its base map. -/
@[simp]
theorem coherentToBase_map (cd : CoherentCategoryData hc D) {A A' : CoherentObject D}
    (m : letI : Category.{u + 1} (CoherentObject D) := cd.category; A ⟶ A') :
    (coherentToBase cd).map m = ULift.up ((Equiv.cast (cd.hom_type A A')) m).base :=
  rfl

/-- **The projection to the base is the projection of Stacks 08KB.**  Composing it with the
projection of the test schemes over `Y` to the schemes of the site gives the structure functor of
`Coh_{X/Y}`, which is the projection of Stacks 08KB followed by that same projection; so the
1-morphism above is the one the source names. -/
theorem coherentToBase_comp_projection (cd : CoherentCategoryData hc D) :
    letI : Category.{u + 1} (CoherentObject D) := cd.category
    coherentToBaseFunctor cd ⋙ ULiftHom.down ⋙
        CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y =
      cd.projection ⋙ CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y :=
  (coherentSiteProjection_eq cd).symm

end AlgebraicGeometry.Space

end
