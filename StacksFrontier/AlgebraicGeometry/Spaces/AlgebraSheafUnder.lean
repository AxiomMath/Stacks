module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAlgebraColimits
public import StacksFrontier.CategoryTheory.Images.Sheaf

/-!
# Algebra sheaves on an algebraic space as objects under the structure sheaf

An algebra sheaf on the small étale site of an algebraic space `F` whose sections live in the
universe of the schemes is the same thing as a sheaf of commutative rings equipped with a
morphism from the structure sheaf, that is, an object of
`CategoryTheory.Under (AlgebraicGeometry.Space.structureSheaf B S hS F hF)`.  Along this
equivalence, images and binary coproducts — which a category of objects under a fixed object of a
category with images, pullbacks and pushouts has — transport to the category of algebra
sheaves.

## Main definitions

* `AlgebraicGeometry.Space.AlgebraSheaf.toUnder` and
  `AlgebraicGeometry.Space.AlgebraSheaf.ofUnder` are the two functors, and
  `AlgebraicGeometry.Space.AlgebraSheaf.underEquivalence` is the equivalence
  `AlgebraSheaf.{u, u} B S hS F hF ≌ Under (structureSheaf B S hS F hF)`.

## Main results

* `AlgebraicGeometry.Space.hasImages_algebraSheaf` and
  `AlgebraicGeometry.Space.hasBinaryCoproducts_algebraSheaf`: the category of algebra sheaves with
  sections in the universe of the schemes has images and binary coproducts.
* `AlgebraicGeometry.Space.algebraSheaf_exists_sup`: two subobjects of an algebra sheaf have an
  upper bound, namely their join as subobjects.

## Implementation notes

The equivalence exists only for `AlgebraSheaf.{u, u}`, where the sections of the algebra and the
sections of the structure sheaf lie in the same universe: the structure-algebra map of an algebra
sheaf is a *sectionwise* family of ring homomorphisms precisely so that the two universes may
differ, and `AlgebraicGeometry.Space.AlgebraSheaf.hom` — the identification of such a family with
a morphism of sheaves of rings — is available only in the single-universe case.  The same
restriction is forced from the other side, sheafification of `CommRingCat.{m}`-valued presheaves
on the small étale site being available for `m = u`.

Both composites of the two functors are the identity *definitionally*, so the unit and the counit
are `CategoryTheory.Iso.refl`.  This is not an accident of the implementation: an algebra sheaf is
a sheaf of rings together with its structure-algebra maps, `CategoryTheory.Under.mk` records a
morphism and nothing else, and the round trip through
`AlgebraicGeometry.Space.AlgebraSheaf.hom` and `AlgebraicGeometry.Space.AlgebraSheaf.ofHom`
rebuilds each field from itself.  The proofs are `rfl` by η for structures, exactly as
`CategoryTheory.Under.mk_surjective` and `CategoryTheory.Under.homMk_eta` are in Mathlib.

The site-level inputs for images and pullbacks are recorded as separate named theorems rather
than left to instance search at the point of use, and the pullbacks are stated for a *generic*
universe `m` of sections.  That is not cosmetic: `CategoryTheory.Limits.HasLimitsOfShape
CategoryTheory.Limits.WalkingCospan (CategoryTheory.Sheaf (SmallEtale.topology B S hS F)
CommRingCat.{m})` is synthesized in two seconds for a universe variable `m` and exhausts memory
when `m` is literally the universe `u` of the schemes, so the instance is elaborated once at
generic `m` and instantiated at `m = u`, where it is read from the environment rather than
searched for again.  Pushouts and images need no such care.

## References

* [Stacks Project, Tag 082B](https://stacks.math.columbia.edu/tag/082B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F)

/-! ### The site-level input

Images and pullbacks of sheaves of commutative rings on the small étale site of `F`; pushouts are
left to instance search.
-/

/-- Sheaves of commutative rings on the small étale site of `F` have images: the presheaf
category does, and sheafification exists. -/
theorem hasImages_sheafSmallEtale :
    HasImages (Sheaf (SmallEtale.topology B S hS F) CommRingCat.{u}) :=
  Stacks.SheafImages.hasImages _ _

/-- Sheaves of commutative rings on the small étale site of `F` have pullbacks, stated as limits
of shape `CategoryTheory.Limits.WalkingCospan` and for a generic universe of sections. -/
theorem hasLimitsOfShape_walkingCospan_sheafSmallEtale :
    HasLimitsOfShape WalkingCospan (Sheaf (SmallEtale.topology B S hS F) CommRingCat.{m}) :=
  inferInstance

namespace AlgebraSheaf

variable {B S hS F hF}

/-! ### The equivalence with objects under the structure sheaf -/

/-- An algebra sheaf whose sections lie in the universe of the schemes, read as a sheaf of rings
under the structure sheaf. -/
def toUnder : AlgebraSheaf.{u, u} B S hS F hF ⥤ Under (structureSheaf B S hS F hF) where
  obj A := Under.mk A.hom
  map {A C} f := Under.homMk f.right
    (Sheaf.hom_ext (NatTrans.ext (funext fun U =>
      CommRingCat.hom_ext (RingHom.ext fun r => f.comm U r))))

/-- A sheaf of rings under the structure sheaf, read as an algebra sheaf. -/
def ofUnder : Under (structureSheaf B S hS F hF) ⥤ AlgebraSheaf.{u, u} B S hS F hF where
  obj X := ofHom X.hom
  map {X Y} g :=
    { right := g.right
      comm := fun U r =>
        congrArg (fun t : structureSheaf B S hS F hF ⟶ Y.right => (t.hom.app U).hom r)
          (Under.w g) }

/-- The sheaf of rings underlying `toUnder.obj A` is that of `A`. -/
@[simp]
theorem toUnder_obj_right (A : AlgebraSheaf.{u, u} B S hS F hF) :
    (toUnder.obj A).right = A.right :=
  rfl

/-- The structure morphism of `toUnder.obj A` is `A.hom`. -/
@[simp]
theorem toUnder_obj_hom (A : AlgebraSheaf.{u, u} B S hS F hF) :
    (toUnder.obj A).hom = A.hom :=
  rfl

/-- The morphism of sheaves of rings underlying `toUnder.map f` is that of `f`. -/
@[simp]
theorem toUnder_map_right {A C : AlgebraSheaf.{u, u} B S hS F hF} (f : A ⟶ C) :
    (toUnder.map f).right = f.right :=
  rfl

/-- The algebra sheaf `ofUnder.obj X` has underlying sheaf of rings `X.right`. -/
@[simp]
theorem ofUnder_obj_right (X : Under (structureSheaf B S hS F hF)) :
    (ofUnder.obj X).right = X.right :=
  rfl

/-- The structure-algebra map of `ofUnder.obj X` over `U` is the component of `X.hom` at `U`. -/
@[simp]
theorem ofUnder_obj_algebraMap (X : Under (structureSheaf B S hS F hF))
    (U : (SmallEtale B S hS F)ᵒᵖ) :
    (ofUnder.obj X).algebraMap U = (X.hom.hom.app U).hom :=
  rfl

/-- The morphism of sheaves of rings underlying `ofUnder.map g` is that of `g`. -/
@[simp]
theorem ofUnder_map_right {X Y : Under (structureSheaf B S hS F hF)} (g : X ⟶ Y) :
    (ofUnder.map g).right = g.right :=
  rfl

/-- `ofUnder` undoes `toUnder` on objects. -/
@[simp]
theorem ofUnder_obj_toUnder_obj (A : AlgebraSheaf.{u, u} B S hS F hF) :
    ofUnder.obj (toUnder.obj A) = A :=
  rfl

/-- `toUnder` undoes `ofUnder` on objects. -/
@[simp]
theorem toUnder_obj_ofUnder_obj (X : Under (structureSheaf B S hS F hF)) :
    toUnder.obj (ofUnder.obj X) = X :=
  rfl

/-- `ofUnder` undoes `toUnder` on morphisms. -/
@[simp]
theorem ofUnder_map_toUnder_map {A C : AlgebraSheaf.{u, u} B S hS F hF} (f : A ⟶ C) :
    ofUnder.map (toUnder.map f) = f :=
  rfl

/-- `toUnder` undoes `ofUnder` on morphisms. -/
@[simp]
theorem toUnder_map_ofUnder_map {X Y : Under (structureSheaf B S hS F hF)} (g : X ⟶ Y) :
    toUnder.map (ofUnder.map g) = g :=
  rfl

/-- Forgetting the structure morphism of an object under the structure sheaf and forgetting the
algebra structure of an algebra sheaf are the same functor, read along
`AlgebraicGeometry.Space.AlgebraSheaf.toUnder`. -/
theorem toUnder_comp_forget :
    toUnder (B := B) (S := S) (hS := hS) (F := F) (hF := hF) ⋙
        Under.forget (structureSheaf B S hS F hF) =
      forget :=
  rfl

/-- **An algebra sheaf with sections in the universe of the schemes is a sheaf of rings under the
structure sheaf.**  Both composites are the identity definitionally, the two functors rebuilding
each field of their argument from itself. -/
def underEquivalence :
    AlgebraSheaf.{u, u} B S hS F hF ≌ Under (structureSheaf B S hS F hF) where
  functor := toUnder
  inverse := ofUnder
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by simp)

/-- The functor of `underEquivalence` is `toUnder`. -/
@[simp]
theorem underEquivalence_functor :
    (underEquivalence (B := B) (S := S) (hS := hS) (F := F) (hF := hF)).functor = toUnder :=
  rfl

/-- The inverse of `underEquivalence` is `ofUnder`. -/
@[simp]
theorem underEquivalence_inverse :
    (underEquivalence (B := B) (S := S) (hS := hS) (F := F) (hF := hF)).inverse = ofUnder :=
  rfl

/-- The unit of `underEquivalence` is the identity on underlying sheaves of rings. -/
@[simp]
theorem underEquivalence_unitIso_hom_app_right (A : AlgebraSheaf.{u, u} B S hS F hF) :
    (underEquivalence.unitIso.hom.app A).right = 𝟙 A.right :=
  rfl

/-- The counit of `underEquivalence` is the identity on underlying sheaves of rings. -/
@[simp]
theorem underEquivalence_counitIso_hom_app_right (X : Under (structureSheaf B S hS F hF)) :
    (underEquivalence.counitIso.hom.app X).right = 𝟙 X.right :=
  rfl

/-- The equivalence `underEquivalence` as an adjunction `toUnder ⊣ ofUnder`. -/
def toUnderAdjunction :
    toUnder (B := B) (S := S) (hS := hS) (F := F) (hF := hF) ⊣ ofUnder :=
  underEquivalence.toAdjunction

/-- The equivalence as an adjunction `ofUnder ⊣ toUnder`, which exhibits algebra sheaves as a
reflective subcategory of the sheaves of rings under the structure sheaf. -/
def ofUnderAdjunction :
    ofUnder (B := B) (S := S) (hS := hS) (F := F) (hF := hF) ⊣ toUnder :=
  underEquivalence.symm.toAdjunction

/-- `toUnder` is an equivalence of categories. -/
instance toUnder_isEquivalence :
    (toUnder (B := B) (S := S) (hS := hS) (F := F) (hF := hF)).IsEquivalence :=
  underEquivalence.isEquivalence_functor

/-- `ofUnder` is an equivalence of categories. -/
instance ofUnder_isEquivalence :
    (ofUnder (B := B) (S := S) (hS := hS) (F := F) (hF := hF)).IsEquivalence :=
  underEquivalence.isEquivalence_inverse

/-- `ofUnder` preserves monomorphisms. -/
instance ofUnder_preservesMonomorphisms :
    (ofUnder (B := B) (S := S) (hS := hS) (F := F) (hF := hF)).PreservesMonomorphisms :=
  Stacks.ReflectiveImages.preservesMonomorphisms_of_isRightAdjoint toUnderAdjunction

end AlgebraSheaf

/-! ### Images and binary coproducts of algebra sheaves

The category of objects under a fixed object has images as soon as the ambient category has
images and pullbacks, and binary coproducts as soon as it has pushouts; both transport along
`AlgebraicGeometry.Space.AlgebraSheaf.underEquivalence`.
-/

/-- Sheaves of rings under the structure sheaf of `F` have images. -/
theorem hasImages_underStructureSheaf : HasImages (Under (structureSheaf B S hS F hF)) :=
  @Stacks.UnderImages.hasImages _ _ (hasImages_sheafSmallEtale B S hS F)
    (hasLimitsOfShape_walkingCospan_sheafSmallEtale.{u, u} B S hS F) _

/-- Sheaves of rings under the structure sheaf of `F` have binary coproducts: the coproduct is
the pushout of the two structure morphisms, that is, the tensor product over the structure
sheaf. -/
theorem hasBinaryCoproducts_underStructureSheaf :
    HasBinaryCoproducts (Under (structureSheaf B S hS F hF)) :=
  Stacks.UnderCoproducts.hasBinaryCoproducts

/-- **Algebra sheaves with sections in the universe of the schemes have images.**  The equivalence
with sheaves of rings under the structure sheaf carries the image factorisation across; on
underlying sheaves of rings the image is the sheafification of the image presheaf. -/
instance hasImages_algebraSheaf : HasImages (AlgebraSheaf.{u, u} B S hS F hF) :=
  haveI : HasImages (Under (structureSheaf B S hS F hF)) :=
    hasImages_underStructureSheaf B S hS F hF
  Stacks.ReflectiveImages.hasImages_of_reflective AlgebraSheaf.ofUnderAdjunction

/-- **Algebra sheaves with sections in the universe of the schemes have binary coproducts.**  On
underlying sheaves of rings the coproduct is the pushout of the two structure-algebra maps, that
is, the tensor product over the structure sheaf. -/
instance hasBinaryCoproducts_algebraSheaf :
    HasBinaryCoproducts (AlgebraSheaf.{u, u} B S hS F hF) :=
  haveI : HasColimitsOfShape (Discrete WalkingPair) (Under (structureSheaf B S hS F hF)) :=
    hasBinaryCoproducts_underStructureSheaf B S hS F hF
  Adjunction.hasColimitsOfShape_of_equivalence
    (AlgebraSheaf.toUnder (B := B) (S := S) (hS := hS) (F := F) (hF := hF))

/-- **Two subobjects of an algebra sheaf have an upper bound.**  The join is the image of the
morphism out of their coproduct, which exists since algebra sheaves have images and binary
coproducts. -/
theorem algebraSheaf_exists_sup (A : AlgebraSheaf.{u, u} B S hS F hF) (C D : Subobject A) :
    ∃ E : Subobject A, C ≤ E ∧ D ≤ E :=
  ⟨C ⊔ D, le_sup_left, le_sup_right⟩

end AlgebraicGeometry.Space

end
