module

public import Mathlib.CategoryTheory.Comma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModules
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackQuasicoherence

/-!
# Formal glueing data for quasi-coherent modules

In the formal glueing situation `f : Y ⟶ X`, `Z ⊆ X` of Stacks 0AEV, with `U = X ∖ Z` and
`V = Y ∖ f⁻¹(Z)`, the category `QCoh(Y → X, Z)` has as objects the triples `(H, G, φ)`
consisting of a quasi-coherent `𝒪_U`-module `H`, a quasi-coherent `𝒪_Y`-module `G` and an
isomorphism `φ : (f|_V)^*H ≅ G|_V` of `𝒪_V`-modules, and as morphisms the pairs of module maps
commuting with the overlap isomorphisms.

A quasi-coherent `𝒪_X`-module `M` gives such a triple: restrict it to `U`, pull it back to `Y`,
and compare the two resulting `𝒪_V`-modules by the composition isomorphism of Stacks 03LU read
through the commutativity `(f|_V) ∘ j = j' ∘ f` of the glueing square.  This is the functor of
Stacks 0AEW.

## Main definitions

* `CategoryTheory.Functor.toComma`: the functor into a comma category determined by a pair of
  functors and a natural transformation between the two composites.
* `AlgebraicGeometry.Space.FormalGlueingSituation.spaceX`,
  `AlgebraicGeometry.Space.FormalGlueingSituation.spaceY`,
  `AlgebraicGeometry.Space.FormalGlueingSituation.spaceU` and
  `AlgebraicGeometry.Space.FormalGlueingSituation.spaceV`: the four spaces of the situation, as
  objects of the category of algebraic spaces of Stacks 02X2.
* `AlgebraicGeometry.Space.FormalGlueingSituation.openImmersion` (`j : U ⟶ X`),
  `AlgebraicGeometry.Space.FormalGlueingSituation.openImmersionOver` (`j' : V ⟶ Y`),
  `AlgebraicGeometry.Space.FormalGlueingSituation.ambientMorphism` (`f : Y ⟶ X`) and
  `AlgebraicGeometry.Space.FormalGlueingSituation.overlapRestriction` (`f|_V : V ⟶ U`): the four
  morphisms of the glueing square.
* `AlgebraicGeometry.Space.FormalGlueingSituation.overlapPullbackComparison`: the canonical
  identification `(f|_V)^* ∘ j^* ≅ (j')^* ∘ f^*` of the two ways of transporting an
  `𝒪_X`-module to the overlap `V`, and
  `AlgebraicGeometry.Space.FormalGlueingSituation.quasicoherentOverlapComparison`: the same read
  on the quasi-coherent modules, along
  `AlgebraicGeometry.Space.FormalGlueingSituation.ambientInclusion`.
* `AlgebraicGeometry.Space.FormalGlueingSituation.moduleGlueingData`: **the category
  `QCoh(Y → X, Z)`** of triples.
* `AlgebraicGeometry.Space.FormalGlueingSituation.glueingDiagram` and
  `AlgebraicGeometry.Space.FormalGlueingSituation.quasicoherentGlueingDiagram`: the triple
  attached to an `𝒪_X`-module, with no quasi-coherence asked of it respectively of a
  quasi-coherent one, as an object of the comma category.
* `AlgebraicGeometry.Space.FormalGlueingSituation.glueingModules`: **the functor of
  Stacks 0AEW**, `QCoh(𝒪_X) ⥤ QCoh(Y → X, Z)`.

## Main results

* `AlgebraicGeometry.Space.FormalGlueingSituation.overlapRestriction_comp_openImmersion`: the
  glueing square commutes, as a square of morphisms of algebraic spaces.
* `AlgebraicGeometry.Space.FormalGlueingSituation.glueingDiagram_obj_left`,
  `AlgebraicGeometry.Space.FormalGlueingSituation.glueingDiagram_obj_right`,
  `AlgebraicGeometry.Space.FormalGlueingSituation.glueingDiagram_obj_hom`,
  `AlgebraicGeometry.Space.FormalGlueingSituation.glueingDiagram_map_left` and
  `AlgebraicGeometry.Space.FormalGlueingSituation.glueingDiagram_map_right`: the components of
  the triple are the restriction to `U`, the pullback to `Y` and the canonical comparison on
  `V`, on objects and on morphisms.  Together with
  `AlgebraicGeometry.Space.FormalGlueingSituation.glueingModules_obj_obj` and
  `AlgebraicGeometry.Space.FormalGlueingSituation.glueingModules_map_hom` they pin the functor
  of Stacks 0AEW down: a functor with these components is this one.
* `AlgebraicGeometry.Space.FormalGlueingSituation.isIso_glueingDiagram_obj_hom` and
  `AlgebraicGeometry.Space.FormalGlueingSituation.isIso_quasicoherentGlueingDiagram_obj_hom`:
  the structure arrow of the triple of a module is an isomorphism, so the triple satisfies the
  condition of Stacks 0AEX on the overlap.
* `isQuasicoherentOnSite_quasicoherentGlueingDiagram_obj_left` and
  `isQuasicoherentOnSite_quasicoherentGlueingDiagram_obj_right`, in the namespace
  `AlgebraicGeometry.Space.FormalGlueingSituation`: the two components of the triple of a
  quasi-coherent module are quasi-coherent; this is Stacks 03GA for `j` and for `f`, under the
  hypothesis discussed below.

## Implementation notes

A triple `(H, G, φ)` is an object of the comma category of the two functors `(f|_V)^*` and
`(j')^*` into the `𝒪_V`-modules, cut down by invertibility of its structure arrow and by
quasi-coherence of its two outer components.  This is the same pattern as
`AlgebraicGeometry.Space.FormalGlueingSituation.glueingData`, which does it for algebraic spaces
over `X` in Stacks 0AF3, and it buys the category structure and the morphisms — a pair of module
maps making the obvious square commute, which is exactly a morphism of triples — from
`CategoryTheory.Comma`.

Quasi-coherence is carried as a property of the comma object rather than by taking the two
components in the categories `QCoh(𝒪_U)` and `QCoh(𝒪_Y)` of Stacks 03G9, so that the structure
arrow of a triple is a morphism of `𝒪_V`-modules on the nose; with the full subcategories of
Stacks 03G9 as components it would be a morphism between two pullbacks of
`CategoryTheory.InducedCategory` objects, and the functor laws below — identities between
morphisms of sheaves of modules on the small étale site of an algebraic space, where the
structure sheaf depends on the proof that the space is algebraic — exhaust the kernel.

For the same reason the functor of Stacks 0AEW is assembled entirely from constructions whose
functor laws are proved in a context of abstract categories, namely
`CategoryTheory.Functor.toComma`, `CategoryTheory.Functor.comp` and
`CategoryTheory.ObjectProperty.lift`: nothing below proves a functor law at the concrete
categories of modules.  `CategoryTheory.Functor.toComma` is the universal property of the comma
category in the only direction this file needs, and is stated for arbitrary categories.

The four spaces and the four morphisms of the glueing square are definitions and not
abbreviations, again to keep the proof witnessing the algebraicity of `V` out of the types:
it is obtained from the identification of `V` with the complement of `f⁻¹(Z)`, and the
structure sheaf of an algebraic space takes that proof as an argument.

`AlgebraicGeometry.Space.FormalGlueingSituation.overlapPullbackComparison` is built from
`AlgebraicGeometry.Space.modulePullbackCompIso`, the inverse-image half of Stacks 03LU, at the
two legs of the glueing square, interpolated by the transport along
`AlgebraicGeometry.Space.FormalGlueingSituation.overlapRestriction_comp_openImmersion`.

**The functor carries two hypotheses, and they are the inverse-image factor of Stacks 03DO, not
anything about formal glueing.**  Stacks 0AEW needs the restriction `j^*M` and the pullback
`f^*M` of a quasi-coherent module to be quasi-coherent, which is Stacks 03GA.  In this
development Stacks 03GA is available only as
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback`, conditional on
`AlgebraicGeometry.Space.HasLocalInverseImagePresentations` for the morphism in question — the
one clause of Stacks 03DO that is not proved here, for the reason recorded in the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackQuasicoherence.lean`.  The two
hypotheses are taken in exactly the shape that file's named predicate provides, so that the day
Stacks 03GA becomes unconditional they discharge by one application each and nothing below
changes.  No hypothesis about `Z`, about quasi-compactness or about quasi-separatedness of `f`
is used: the functor of Stacks 0AEW uses none of the hypotheses of the formal glueing situation
beyond the openness of `U` and of `V`, which
`AlgebraicGeometry.Space.FormalGlueingSituation.isOpenSubspace_U` and
`AlgebraicGeometry.Space.FormalGlueingSituation.isOpenSubspace_V` supply.

The module universe is the universe `u` of the schemes, because
`AlgebraicGeometry.Space.modulePullback` exists only there; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullback.lean`.

## References

* [Stacks Project, Tag 0AEW](https://stacks.math.columbia.edu/tag/0AEW)
* [Stacks Project, Tag 0AEV](https://stacks.math.columbia.edu/tag/0AEV)
* [Stacks Project, Tag 03G9](https://stacks.math.columbia.edu/tag/03G9)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0AF3](https://stacks.math.columbia.edu/tag/0AF3)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    {T : Type u₃} [Category.{v₃} T] {E : Type u₄} [Category.{v₄} E]

/-- The functor into the comma category of `L` and `R` determined by a functor `F` to the source
of `L`, a functor `G` to the source of `R`, and a natural transformation `F ⋙ L ⟶ G ⋙ R`: an
object goes to the triple of its two images and the component of the transformation, and a
morphism to the pair of its two images, the commutative square being naturality. -/
def toComma {L : A ⥤ T} {R : B ⥤ T} (F : E ⥤ A) (G : E ⥤ B) (α : F ⋙ L ⟶ G ⋙ R) :
    E ⥤ Comma L R where
  obj X := { left := F.obj X, right := G.obj X, hom := α.app X }
  map g := { left := F.map g, right := G.map g, w := α.naturality g }
  map_id X := by ext <;> simp
  map_comp g h := by ext <;> simp

/-- The left component of the image of an object under `toComma F G α` is its image under `F`. -/
@[simp]
theorem toComma_obj_left {L : A ⥤ T} {R : B ⥤ T} (F : E ⥤ A) (G : E ⥤ B)
    (α : F ⋙ L ⟶ G ⋙ R) (X : E) : ((toComma F G α).obj X).left = F.obj X := rfl

/-- The right component of the image of an object under `toComma F G α` is its image under `G`. -/
@[simp]
theorem toComma_obj_right {L : A ⥤ T} {R : B ⥤ T} (F : E ⥤ A) (G : E ⥤ B)
    (α : F ⋙ L ⟶ G ⋙ R) (X : E) : ((toComma F G α).obj X).right = G.obj X := rfl

/-- The structure arrow of the image of an object `X` under `toComma F G α` is `α.app X`. -/
@[simp]
theorem toComma_obj_hom {L : A ⥤ T} {R : B ⥤ T} (F : E ⥤ A) (G : E ⥤ B)
    (α : F ⋙ L ⟶ G ⋙ R) (X : E) : ((toComma F G α).obj X).hom = α.app X := rfl

/-- The left component of the image of a morphism under `toComma F G α` is its image under
`F`. -/
@[simp]
theorem toComma_map_left {L : A ⥤ T} {R : B ⥤ T} (F : E ⥤ A) (G : E ⥤ B)
    (α : F ⋙ L ⟶ G ⋙ R) {X Y : E} (g : X ⟶ Y) :
    ((toComma F G α).map g).left = F.map g := rfl

/-- The right component of the image of a morphism under `toComma F G α` is its image under
`G`. -/
@[simp]
theorem toComma_map_right {L : A ⥤ T} {R : B ⥤ T} (F : E ⥤ A) (G : E ⥤ B)
    (α : F ⋙ L ⟶ G ⋙ R) {X Y : E} (g : X ⟶ Y) :
    ((toComma F G α).map g).right = G.map g := rfl

/-- If the transformation is an isomorphism then every structure arrow of the resulting functor
into the comma category is an isomorphism. -/
instance isIso_toComma_obj_hom {L : A ⥤ T} {R : B ⥤ T} (F : E ⥤ A) (G : E ⥤ B)
    (α : F ⋙ L ≅ G ⋙ R) (X : E) : IsIso ((toComma F G α.hom).obj X).hom :=
  NatIso.hom_app_isIso α X

end CategoryTheory.Functor

universe u

namespace AlgebraicGeometry.Space.FormalGlueingSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (D : FormalGlueingSituation B S hS)

/-! ### The glueing square -/

/-- The ambient space `X` of the situation, as an algebraic space. -/
def spaceX : AlgebraicSpaces B S hS := ⟨D.X, D.algebraicSpace_X⟩

/-- The space `Y` mapping to `X`, as an algebraic space. -/
def spaceY : AlgebraicSpaces B S hS := ⟨D.Y, D.algebraicSpace_Y⟩

/-- The open complement `U = X ∖ Z`, as an algebraic space. -/
def spaceU : AlgebraicSpaces B S hS := ⟨D.U.toFunctor, D.isOpenSubspace_U.1⟩

/-- The open complement `V = Y ∖ f⁻¹(Z)`, as an algebraic space. -/
def spaceV : AlgebraicSpaces B S hS := ⟨D.V.toFunctor, D.isOpenSubspace_V.1⟩

/-- The open immersion `j : U ⟶ X` of the complement of `Z`. -/
def openImmersion : D.spaceU ⟶ D.spaceX := ObjectProperty.homMk D.U.ι

/-- The open immersion `j' : V ⟶ Y` of the complement of `f⁻¹(Z)`. -/
def openImmersionOver : D.spaceV ⟶ D.spaceY := ObjectProperty.homMk D.V.ι

/-- The morphism `f : Y ⟶ X` being glued along. -/
def ambientMorphism : D.spaceY ⟶ D.spaceX := ObjectProperty.homMk D.f

/-- The restriction `f|_V : V ⟶ U` of `f` to the two open complements. -/
def overlapRestriction : D.spaceV ⟶ D.spaceU :=
  ObjectProperty.homMk (D.U.fromPreimage D.f)

/-- The glueing square commutes: restricting `f` to the complements and then including the
complement of `Z` is including the complement of `f⁻¹(Z)` and then applying `f`. -/
theorem overlapRestriction_comp_openImmersion :
    D.overlapRestriction ≫ D.openImmersion = D.openImmersionOver ≫ D.ambientMorphism :=
  ObjectProperty.hom_ext _ (Subfunctor.fromPreimage_ι D.U D.f)

/-- The canonical identification `(f|_V)^* ∘ j^* ≅ (j')^* ∘ f^*` of the two ways of
transporting an `𝒪_X`-module to the overlap `V`: both are the inverse image along the common
composite `V ⟶ X` of the glueing square, by the inverse-image half of Stacks 03LU. -/
@[stacks 0AEW "the comparison over the overlap"]
def overlapPullbackComparison :
    modulePullback B S hS D.openImmersion ⋙ modulePullback B S hS D.overlapRestriction ≅
      modulePullback B S hS D.ambientMorphism ⋙ modulePullback B S hS D.openImmersionOver :=
  modulePullbackCompIso B S hS D.overlapRestriction D.openImmersion ≪≫
    eqToIso (congrArg (fun g : D.spaceV ⟶ D.spaceX => modulePullback B S hS g)
      D.overlapRestriction_comp_openImmersion) ≪≫
    (modulePullbackCompIso B S hS D.openImmersionOver D.ambientMorphism).symm

/-! ### The category of glueing triples -/

/-- **The category `QCoh(Y → X, Z)` of formal glueing data for quasi-coherent modules**: the
triples `(H, G, φ)` of a quasi-coherent `𝒪_U`-module `H`, a quasi-coherent `𝒪_Y`-module `G` and
an isomorphism `φ : (f|_V)^*H ≅ G|_V`, with the pairs of module maps commuting with the overlap
isomorphisms as morphisms.

The category is introduced in the prose of the source immediately before equation (0AEX); it is
the target of the functor of Stacks 0AEW and the source of the functor of Stacks 0AEX. -/
@[stacks 0AEW "the category of glueing data"]
abbrev moduleGlueingData :=
  (show ObjectProperty (Comma (modulePullback B S hS D.overlapRestriction)
      (modulePullback B S hS D.openImmersionOver)) from
    fun t ↦ IsIso t.hom ∧ t.left.IsQuasicoherentOnSite ∧
      t.right.IsQuasicoherentOnSite).FullSubcategory

/-- The triple attached to an arbitrary `𝒪_X`-module: its restriction to the open complement
`U`, its pullback to `Y`, and the canonical comparison of the two on the overlap `V`. -/
def glueingDiagram :
    Modules.{u, u} B S hS D.spaceX.1 D.spaceX.2 ⥤
      Comma (modulePullback B S hS D.overlapRestriction)
        (modulePullback B S hS D.openImmersionOver) :=
  Functor.toComma (modulePullback B S hS D.openImmersion)
    (modulePullback B S hS D.ambientMorphism) D.overlapPullbackComparison.hom

/-- The first entry of the triple attached to an `𝒪_X`-module is its restriction to `U`. -/
@[simp]
theorem glueingDiagram_obj_left (M : Modules.{u, u} B S hS D.spaceX.1 D.spaceX.2) :
    (D.glueingDiagram.obj M).left = (modulePullback B S hS D.openImmersion).obj M := rfl

/-- The second entry of the triple attached to an `𝒪_X`-module is its pullback to `Y`. -/
@[simp]
theorem glueingDiagram_obj_right (M : Modules.{u, u} B S hS D.spaceX.1 D.spaceX.2) :
    (D.glueingDiagram.obj M).right = (modulePullback B S hS D.ambientMorphism).obj M := rfl

/-- The structure arrow of the triple attached to an `𝒪_X`-module is the component at it of
`overlapPullbackComparison`. -/
@[simp]
theorem glueingDiagram_obj_hom (M : Modules.{u, u} B S hS D.spaceX.1 D.spaceX.2) :
    (D.glueingDiagram.obj M).hom = D.overlapPullbackComparison.hom.app M := rfl

/-- The first component of the map of triples induced by a module map is its restriction to
`U`. -/
@[simp]
theorem glueingDiagram_map_left {M N : Modules.{u, u} B S hS D.spaceX.1 D.spaceX.2}
    (a : M ⟶ N) :
    (D.glueingDiagram.map a).left = (modulePullback B S hS D.openImmersion).map a := rfl

/-- The second component of the map of triples induced by a module map is its pullback to
`Y`. -/
@[simp]
theorem glueingDiagram_map_right {M N : Modules.{u, u} B S hS D.spaceX.1 D.spaceX.2}
    (a : M ⟶ N) :
    (D.glueingDiagram.map a).right = (modulePullback B S hS D.ambientMorphism).map a := rfl

/-! ### The functor of Stacks 0AEW -/

/-- The structure arrow of the triple attached to an `𝒪_X`-module is the canonical comparison on
the overlap, and is therefore an isomorphism. -/
instance isIso_glueingDiagram_obj_hom
    (M : Modules.{u, u} B S hS D.spaceX.1 D.spaceX.2) :
    IsIso (D.glueingDiagram.obj M).hom :=
  Functor.isIso_toComma_obj_hom _ _ D.overlapPullbackComparison M

/-- The inclusion of the quasi-coherent `𝒪_X`-modules into all `𝒪_X`-modules. -/
def ambientInclusion :
    QuasicoherentSheaves.{u, u} B S hS D.spaceX.1 D.spaceX.2 ⥤
      Modules.{u, u} B S hS D.spaceX.1 D.spaceX.2 :=
  ObjectProperty.ι _

/-- The overlap comparison, read on the quasi-coherent `𝒪_X`-modules. -/
def quasicoherentOverlapComparison :
    (D.ambientInclusion ⋙ modulePullback B S hS D.openImmersion) ⋙
        modulePullback B S hS D.overlapRestriction ≅
      (D.ambientInclusion ⋙ modulePullback B S hS D.ambientMorphism) ⋙
        modulePullback B S hS D.openImmersionOver :=
  Functor.isoWhiskerLeft D.ambientInclusion D.overlapPullbackComparison

/-- The triple attached to a quasi-coherent `𝒪_X`-module, as an object of the comma category of
the two pullbacks to the overlap. -/
def quasicoherentGlueingDiagram :
    QuasicoherentSheaves.{u, u} B S hS D.spaceX.1 D.spaceX.2 ⥤
      Comma (modulePullback B S hS D.overlapRestriction)
        (modulePullback B S hS D.openImmersionOver) :=
  Functor.toComma (D.ambientInclusion ⋙ modulePullback B S hS D.openImmersion)
    (D.ambientInclusion ⋙ modulePullback B S hS D.ambientMorphism)
    D.quasicoherentOverlapComparison.hom

/-- The structure arrow of the triple attached to a quasi-coherent `𝒪_X`-module is an
isomorphism. -/
instance isIso_quasicoherentGlueingDiagram_obj_hom
    (M : QuasicoherentSheaves.{u, u} B S hS D.spaceX.1 D.spaceX.2) :
    IsIso (D.quasicoherentGlueingDiagram.obj M).hom :=
  Functor.isIso_toComma_obj_hom _ _ D.quasicoherentOverlapComparison M

/-- **Stacks 03GA for `j`.**  The restriction to the open complement `U` of a quasi-coherent
`𝒪_X`-module is quasi-coherent, granted the inverse-image factor of Stacks 03DO for `j`. -/
theorem isQuasicoherentOnSite_quasicoherentGlueingDiagram_obj_left
    (hj : HasLocalInverseImagePresentations B S hS D.openImmersion)
    (M : QuasicoherentSheaves.{u, u} B S hS D.spaceX.1 D.spaceX.2) :
    (D.quasicoherentGlueingDiagram.obj M).left.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePullback B S hS D.openImmersion hj M.obj M.property

/-- **Stacks 03GA for `f`.**  The pullback to `Y` of a quasi-coherent `𝒪_X`-module is
quasi-coherent, granted the inverse-image factor of Stacks 03DO for `f`. -/
theorem isQuasicoherentOnSite_quasicoherentGlueingDiagram_obj_right
    (hf : HasLocalInverseImagePresentations B S hS D.ambientMorphism)
    (M : QuasicoherentSheaves.{u, u} B S hS D.spaceX.1 D.spaceX.2) :
    (D.quasicoherentGlueingDiagram.obj M).right.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePullback B S hS D.ambientMorphism hf M.obj M.property

/-- **Stacks 0AEW.**  The functor `QCoh(𝒪_X) ⥤ QCoh(Y → X, Z)` of formal glueing: a
quasi-coherent `𝒪_X`-module goes to its restriction to the open complement `U`, its pullback to
`Y`, and the canonical comparison of the two on the overlap `V`.

The two hypotheses are the inverse-image factor of Stacks 03DO for `j` and for `f`, under which
Stacks 03GA is available in this development; see the implementation notes. -/
def glueingModules (hj : HasLocalInverseImagePresentations B S hS D.openImmersion)
    (hf : HasLocalInverseImagePresentations B S hS D.ambientMorphism) :
    QuasicoherentSheaves.{u, u} B S hS D.spaceX.1 D.spaceX.2 ⥤ D.moduleGlueingData :=
  ObjectProperty.lift _ D.quasicoherentGlueingDiagram fun M ↦
    ⟨D.isIso_quasicoherentGlueingDiagram_obj_hom M,
      D.isQuasicoherentOnSite_quasicoherentGlueingDiagram_obj_left hj M,
      D.isQuasicoherentOnSite_quasicoherentGlueingDiagram_obj_right hf M⟩

variable (hj : HasLocalInverseImagePresentations B S hS D.openImmersion)
    (hf : HasLocalInverseImagePresentations B S hS D.ambientMorphism)

/-- The underlying triple of the glueing datum attached to a quasi-coherent `𝒪_X`-module is its
image under `quasicoherentGlueingDiagram`. -/
@[simp]
theorem glueingModules_obj_obj
    (M : QuasicoherentSheaves.{u, u} B S hS D.spaceX.1 D.spaceX.2) :
    ((D.glueingModules hj hf).obj M).obj = D.quasicoherentGlueingDiagram.obj M := rfl

/-- The underlying map of triples of the image of a module map under `glueingModules` is its
image under `quasicoherentGlueingDiagram`. -/
@[simp]
theorem glueingModules_map_hom
    {M N : QuasicoherentSheaves.{u, u} B S hS D.spaceX.1 D.spaceX.2} (a : M ⟶ N) :
    InducedCategory.Hom.hom ((D.glueingModules hj hf).map a) =
      D.quasicoherentGlueingDiagram.map a :=
  rfl

end AlgebraicGeometry.Space.FormalGlueingSituation

end
