module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.OpenRestriction
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiCartesianModule
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiComponentConservative
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiQuasicoherentComponents
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiSliceSheafify
public import StacksFrontier.CategoryTheory.Sites.SlicePost.Pushforward
public import StacksFrontier.Topology.Simplicial.ComponentSliceSite

/-!
# The component functors on a slice of the total Zariski site

Let `X` be a simplicial scheme and `(a, W)` an object of its total Zariski site. An object of the
slice at `(a, W)` is an object `(b, V)` of the total site together with an arrow into `(a, W)`,
that is: a simplex map `φ : b ⟶ a` together with an open `V` of `X_b` contained in `(X φ)⁻¹W`.
The slice therefore has one component site for every simplex map `φ : b ⟶ a`, namely the slice of
the open-set site of `X_b` at `(X φ)⁻¹W`, and the degree-`a` component is the one at `φ = 𝟙`.

This file constructs the restriction functors to those components and records their properties:
the one at `φ = 𝟙` is the localization at `W` of the degree-`a` component functor
`AlgebraicGeometry.SimplicialScheme.componentModule`, they preserve colimits, and the family of
all of them is jointly conservative.

## Main definitions

* `AlgebraicGeometry.SimplicialScheme.sliceComponentModule`: the restriction of a sheaf of
  modules on the slice at `(a, W)` to the slice of the degree-`a` site at `W`.
* `AlgebraicGeometry.SimplicialScheme.sliceComponentModuleAt`: the same at a simplex map
  `φ : b ⟶ a`, landing on the slice of the degree-`b` site at `(X φ)⁻¹W`.

## Main results

* `AlgebraicGeometry.SimplicialScheme.sliceComponentModuleOverFunctorIso` and
  `.sliceComponentModuleAtOverIso`: restricting a module on the total site to the slice at
  `(a, W)` and then taking a component is restricting the corresponding component of the module
  to the corresponding open.
* `AlgebraicGeometry.SimplicialScheme.sliceComponentModule_preservesColimitsOfSize` and
  `.sliceComponentModuleAt_preservesColimitsOfSize`: the component functors on the slice preserve
  colimits.
* `AlgebraicGeometry.SimplicialScheme.isIso_of_forall_isIso_sliceComponentModuleAt`: they are
  jointly conservative.

## Implementation notes

The component inclusion of the slice is `Over.post` of the level inclusion followed by `Over.map`
of the arrow over `φ`, and all the facts about it are Mathlib's or the development's facts about
those two: `Stacks.Topology.Simplicial.levelFunctor_overPost_isContinuous` and Mathlib's
instances for continuity and cocontinuity, and
`Stacks.SheafOfModules.pushforward_preservesColimits` for the colimits.

The structure map is "just the restriction of the structure map", as in Stacks 04J0; it is
`SheafOfModules.overComparison` of the identification `componentStructureHom` of the degree-`a`
component of `𝒪_X` with the structure sheaf of `X_a`. Its target typechecks with no comparison
map inserted because clause (d) of Stacks 03CF
(`CategoryTheory.sheafPushforwardContinuous_overPost_eq`) is a strict equality of functors: the
restriction to the slice of the direct image of `𝒪_X` along the level inclusion *is* the direct
image along `Over.post` of the restriction of `𝒪_X`. That strictness is also what makes the two
comparisons of a component of a slice with a slice of a component the identity.

Two spellings of a site are in play throughout and both are needed. The site of a simplicial
degree is `Opens ((zariskiSpace X).obj a)` through the underlying simplicial space, which is what
the inclusion of the degree is a functor out of and what its continuity is stated for, and
`Opens ↥(X.obj a)` through the scheme, which is what the structure sheaf
`(X.obj a).ringCatSheaf` and all of `AlgebraicGeometry.Scheme.Modules` live on. The two are
definitionally equal but not syntactically, and instance synthesis runs at a transparency that
unfolds neither `Scheme.forgetToTop` nor a plain `def`, so an instance stated in one spelling is
never found for a goal in the other. Everything here is therefore stated through the scheme, and
the two facts about the level inclusion that are stated through the simplicial space —
cocontinuity and that `componentStructureHom` is invertible — are repeated in that spelling.

The same friction for the slice of the *total* site is removed at the source rather than worked
around: `AlgebraicGeometry.SimplicialScheme.zariskiRingedTopos` is now reducible, so that the
topology carried by `𝒪_X` restricted to a slice, which is spelled through its projections, is
seen by instance search as the `zariskiTopology X` that `ZariskiSliceSheafify` and
`Stacks.Topology.Simplicial.levelFunctor_overPost_isContinuous` speak about. Without that, a
category of sheaves of modules on a slice has no `Category` instance that search can find, and
nothing in this file can even be stated.

One elaboration order has to be forced by hand: in `SheafOfModules.{u} R` the instance argument
for the category of the site comes before `R`, so with the site left implicit it is searched
before `R` fixes it and the search fails. A category of sheaves of modules on a slice is
therefore written `@SheafOfModules.{u} (Over _) _ _ R`.

## References

* [Stacks Project, Tag 03CF](https://stacks.math.columbia.edu/tag/03CF)
* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
* [Stacks Project, Tag 09VL](https://stacks.math.columbia.edu/tag/09VL)
* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Topology.Simplicial
open Stacks.Sheaves.RingedToposModules

universe u

namespace Stacks.CategoryTheory

universe v₁ u₁ v₂ u₂

/-- A natural transformation of presheaves invertible on sections over an object is invertible on
sections over every isomorphic object. -/
public theorem isIso_app_of_objIso {D : Type u₁} [Category.{v₁} D] {B : Type u₂} [Category.{v₂} B]
    {P Q : Dᵒᵖ ⥤ B} (β : P ⟶ Q) {T₁ T₂ : D} (e : T₁ ≅ T₂) [IsIso (β.app (op T₁))] :
    IsIso (β.app (op T₂)) := by
  have key : β.app (op T₂) = P.map e.hom.op ≫ β.app (op T₁) ≫ inv (Q.map e.hom.op) := by
    rw [← Category.assoc, β.naturality e.hom.op, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  rw [key]
  infer_instance

end Stacks.CategoryTheory

namespace AlgebraicGeometry.SimplicialScheme

variable (X : SimplicialObject Scheme.{u}) (a : SimplexCategoryᵒᵖ)
  (W : Opens ↥(X.obj a))

/-- The object `(a, W)` of the total Zariski site, written as the image of the open `W` under the
inclusion of the degree-`a` site, so that the slice comparisons typecheck on the nose. -/
public abbrev sliceObj : ZariskiOpen X := (levelFunctor (zariskiSpace X) a).obj W

/-- Every slice of the open-set site of a scheme is essentially small in the universe of the
scheme. -/
public instance essentiallySmall_over_opens (S : Scheme.{u}) (V : Opens S) :
    EssentiallySmall.{u} (Over V) :=
  essentiallySmall_of_small_of_locallySmall (Over V)

/-- Abelian sheafification exists on every slice of the open-set site of a scheme. -/
public instance opensOver_hasSheafify (S : Scheme.{u}) (V : Opens S) :
    HasSheafify ((Opens.grothendieckTopology ↥S).over V) AddCommGrpCat.{u} := by
  let : CategoryTheory.Limits.PreservesLimits (forget AddCommGrpCat.{u}) :=
    AddCommGrpCat.forget_preservesLimits
  exact hasSheafifyEssentiallySmallSite ((Opens.grothendieckTopology ↥S).over V)
    AddCommGrpCat.{u}

/-- Abelian sheafification on a slice of the open-set site of a scheme inverts exactly the
locally bijective morphisms. -/
public instance opensOver_wEqualsLocallyBijective (S : Scheme.{u}) (V : Opens S) :
    ((Opens.grothendieckTopology ↥S).over V).WEqualsLocallyBijective AddCommGrpCat.{u} := by
  let : CategoryTheory.Limits.PreservesLimits (forget AddCommGrpCat.{u}) :=
    AddCommGrpCat.forget_preservesLimits
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
    (A := AddCommGrpCat.{u}) ((Opens.grothendieckTopology ↥S).over V)

/-- The inclusion of one simplicial degree into the total Zariski site is cocontinuous, in the
spelling of the degree site that goes through the scheme. -/
public instance levelFunctor_isCocontinuous_opens (k : SimplexCategoryᵒᵖ) :
    @Functor.IsCocontinuous (Opens ↥(X.obj k)) _ (ZariskiOpen X) _
      (levelFunctor (zariskiSpace X) k)
      (Opens.grothendieckTopology ↥(X.obj k)) (zariskiTopology X) :=
  levelFunctor_isCocontinuous (zariskiSpace X) k

/-- The identification of the degree-`k` component of `𝒪_X` with the structure sheaf of `X_k` is
an isomorphism, in the spelling of the degree site that goes through the scheme. -/
public instance isIso_componentStructureHom_opens (k : SimplexCategoryᵒᵖ) :
    @IsIso (Sheaf (Opens.grothendieckTopology ↥(X.obj k)) RingCat.{u}) _ _ _
      (componentStructureHom X k) :=
  isIso_componentStructureHom X k

/-- The inclusion of the degree-`a` component site into the slice of the total Zariski site at
`(a, W)`: it sends an open `V ≤ W` of `X_a` to the object `(a, V)` over `(a, W)`. -/
public abbrev sliceComponentFunctor : Over W ⥤ Over (sliceObj X a W) :=
  Over.post (X := W) (levelFunctor (zariskiSpace X) a)

/-- The inclusion of the degree-`a` component site into the slice at `(a, W)` is continuous. -/
public instance sliceComponentFunctor_isContinuous :
    (sliceComponentFunctor X a W).IsContinuous
      ((Opens.grothendieckTopology ↥(X.obj a)).over W)
      ((zariskiTopology X).over (sliceObj X a W)) :=
  levelFunctor_overPost_isContinuous (zariskiSpace X) a W

/-- The inclusion of the degree-`a` component site into the slice at `(a, W)` is cocontinuous. -/
public instance sliceComponentFunctor_isCocontinuous :
    (sliceComponentFunctor X a W).IsCocontinuous
      ((Opens.grothendieckTopology ↥(X.obj a)).over W)
      ((zariskiTopology X).over (sliceObj X a W)) :=
  inferInstance

/-- The structure sheaf of the slice of the total Zariski site at `(a, W)`: the restriction of
`𝒪_X` to the slice. -/
public noncomputable abbrev sliceStructureRingSheaf :=
  (Stacks.SheafOfModules.Tensor.ringSheaf (zariskiRingedTopos X).O).over (sliceObj X a W)

/-- The structure sheaf of the slice of the degree-`a` site at `W`. -/
public noncomputable abbrev sliceDegreeRingSheaf := ((X.obj a).ringCatSheaf).over W

/-- The degree-`a` component of a sheaf of modules on the slice of the total Zariski site at
`(a, W)`: a sheaf of modules on the slice of the open-set site of `X_a` at `W`. -/
public noncomputable abbrev sliceComponentModule :=
  SheafOfModules.pushforward.{u} (SheafOfModules.overComparison (componentStructureHom X a) W)

/-- The sections of the degree-`a` component of a module on the slice at `(a, W)` over an open
`V ≤ W` are the sections of the module over the object `(a, V)` of the slice. -/
public theorem sliceComponentModule_obj_val_obj
    (M : @SheafOfModules.{u} (Over (sliceObj X a W)) _ _ (sliceStructureRingSheaf X a W))
    (V : (Over W)ᵒᵖ) :
    (((sliceComponentModule X a W).obj M).val.obj V : Type u) =
      M.val.obj (op ((sliceComponentFunctor X a W).obj V.unop)) :=
  rfl

/-- **The component of the slice is the slice of the component.** Restricting a sheaf of modules
on the total Zariski site to the slice at `(a, W)` and then taking its degree-`a` component is
restricting its degree-`a` component to `W`: both are the restriction along the functor of sites
`V ↦ (a, V)` from the slice of the degree-`a` site at `W` to the total site. -/
public noncomputable def sliceComponentModuleOverFunctorIso :
    SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (zariskiRingedTopos X).O)
        (sliceObj X a W) ⋙ sliceComponentModule X a W ≅
      componentModule X a ⋙ SheafOfModules.overFunctor.{u} ((X.obj a).ringCatSheaf) W :=
  Iso.refl _

/-- The degree-`a` component functor on the slice at `(a, W)` preserves colimits. -/
public noncomputable instance sliceComponentModule_preservesColimitsOfSize :
    PreservesColimitsOfSize.{u, u} (sliceComponentModule X a W) :=
  Stacks.SheafOfModules.pushforward_preservesColimits (sliceComponentFunctor X a W)
    (SheafOfModules.overComparison (componentStructureHom X a) W)

section At

variable {a}

/-- The open `(X φ)⁻¹W` of `X_b`, for a simplex map `φ : b ⟶ a`: the degree-`b` part of the
object `(a, W)` of the total Zariski site. -/
public abbrev slicePreimage {b : SimplexCategoryᵒᵖ} (φ : b ⟶ a) : Opens ↥(X.obj b) :=
  (Opens.map (X.map φ).base).obj W

/-- The arrow `(b, (X φ)⁻¹W) ⟶ (a, W)` of the total Zariski site lying over `φ`. -/
public abbrev sliceTransitionHom {b : SimplexCategoryᵒᵖ} (φ : b ⟶ a) :
    sliceObj X b (slicePreimage X W φ) ⟶ sliceObj X a W :=
  SimplicialSheafSystem.transitionHom (X := zariskiSpace X) φ W

/-- The inclusion of the degree-`φ` component site into the slice of the total Zariski site at
`(a, W)`, for a simplex map `φ : b ⟶ a`: it sends an open `V ≤ (X φ)⁻¹W` of `X_b` to the object
`(b, V)` of the total site, with its arrow over `φ` to `(a, W)`. -/
public abbrev sliceComponentFunctorAt {b : SimplexCategoryᵒᵖ} (φ : b ⟶ a) :
    Over (slicePreimage X W φ) ⥤ Over (sliceObj X a W) :=
  sliceComponentFunctor X b (slicePreimage X W φ) ⋙ Over.map (sliceTransitionHom X W φ)

/-- The inclusion of the degree-`φ` component site into the slice at `(a, W)` is continuous. -/
public instance sliceComponentFunctorAt_isContinuous {b : SimplexCategoryᵒᵖ} (φ : b ⟶ a) :
    (sliceComponentFunctorAt X W φ).IsContinuous
      ((Opens.grothendieckTopology ↥(X.obj b)).over (slicePreimage X W φ))
      ((zariskiTopology X).over (sliceObj X a W)) :=
  inferInstance

/-- The inclusion of the degree-`φ` component site into the slice at `(a, W)` is cocontinuous. -/
public instance sliceComponentFunctorAt_isCocontinuous {b : SimplexCategoryᵒᵖ} (φ : b ⟶ a) :
    (sliceComponentFunctorAt X W φ).IsCocontinuous
      ((Opens.grothendieckTopology ↥(X.obj b)).over (slicePreimage X W φ))
      ((zariskiTopology X).over (sliceObj X a W)) :=
  isCocontinuous_comp
    (J := (Opens.grothendieckTopology ↥(X.obj b)).over (slicePreimage X W φ))
    (K := (zariskiTopology X).over (sliceObj X b (slicePreimage X W φ)))
    (L := (zariskiTopology X).over (sliceObj X a W))
    (G := sliceComponentFunctor X b (slicePreimage X W φ))
    (G' := Over.map (sliceTransitionHom X W φ))

/-- The structure map of the degree-`φ` component inclusion of the slice at `(a, W)`: the
structure map of the degree-`b` component inclusion of the slice at `(b, (X φ)⁻¹W)`, followed by
restriction of `𝒪_X` along the arrow over `φ`. -/
public noncomputable def sliceComponentStructureHomAt {b : SimplexCategoryᵒᵖ} (φ : b ⟶ a) :
    ((X.obj b).ringCatSheaf).over (slicePreimage X W φ) ⟶
      ((sliceComponentFunctorAt X W φ).sheafPushforwardContinuous RingCat.{u}
          ((Opens.grothendieckTopology ↥(X.obj b)).over (slicePreimage X W φ))
          (((zariskiRingedTopos X).J).over
            (sliceObj X a W))).obj
        ((Stacks.SheafOfModules.Tensor.ringSheaf (zariskiRingedTopos X).O).over (sliceObj X a W)) :=
  SheafOfModules.overComparison (componentStructureHom X b) (slicePreimage X W φ) ≫
    ((sliceComponentFunctor X b (slicePreimage X W φ)).sheafPushforwardContinuous RingCat.{u}
      ((Opens.grothendieckTopology ↥(X.obj b)).over (slicePreimage X W φ))
      (((zariskiRingedTopos X).J).over
        (sliceObj X b (slicePreimage X W φ)))).map
      (Sheaf.pushforwardOverMapIso (Stacks.SheafOfModules.Tensor.ringSheaf (zariskiRingedTopos X).O)
        (sliceTransitionHom X W φ)).inv

/-- The degree-`φ` component of a sheaf of modules on the slice of the total Zariski site at
`(a, W)`, for a simplex map `φ : b ⟶ a`: a sheaf of modules on the slice of the open-set site of
`X_b` at `(X φ)⁻¹W`.

It is the restriction along the arrow over `φ` followed by the degree-`b` component of the slice
at `(b, (X φ)⁻¹W)`, which is the same functor, because both are the restriction along the
inclusion `V ↦ (b, V)`. -/
public noncomputable abbrev sliceComponentModuleAt {b : SimplexCategoryᵒᵖ} (φ : b ⟶ a) :=
  SheafOfModules.pushforward.{u} (sliceComponentStructureHomAt X W φ)

/-- The degree-`φ` component functor on the slice at `(a, W)` preserves colimits. -/
public noncomputable instance sliceComponentModuleAt_preservesColimitsOfSize
    {b : SimplexCategoryᵒᵖ} (φ : b ⟶ a) :
    PreservesColimitsOfSize.{u, u} (sliceComponentModuleAt X W φ) :=
  Stacks.SheafOfModules.pushforward_preservesColimits (sliceComponentFunctorAt X W φ)
    (sliceComponentStructureHomAt X W φ)

/-- **The degree-`φ` component of the restriction to the slice is the restriction of the
degree-`b` component.** -/
public noncomputable def sliceComponentModuleAtOverIso (F : Modules X) {b : SimplexCategoryᵒᵖ}
    (φ : b ⟶ a) :
    (sliceComponentModuleAt X W φ).obj (F.over (sliceObj X a W)) ≅
      ((componentModule X b).obj F).over (slicePreimage X W φ) :=
  Iso.refl _

/-- Every object of the slice of the total Zariski site at `(a, W)` is isomorphic to one in the
image of the degree-`φ` component inclusion, for `φ` the simplex map underlying its own structure
arrow: an object of the slice is an open `V` of `X_b` contained in `(X φ)⁻¹W`. -/
public def sliceComponentFunctorAtObjIso (T : Over (sliceObj X a W)) :
    (sliceComponentFunctorAt X W (SimplicialOpen.Hom.base T.hom)).obj
        (Over.mk (homOfLE (SimplicialOpen.Hom.le T.hom))) ≅ T :=
  Over.isoMk (Iso.refl _) (by
    apply SimplicialOpen.Hom.ext
    change 𝟙 _ ≫ (SimplicialOpen.Hom.base T.hom) = 𝟙 _ ≫ (SimplicialOpen.Hom.base T.hom)
    rfl)

/-- **Joint conservativity of the component functors on a slice of the total Zariski site.** A
morphism of sheaves of modules on the slice at `(a, W)` whose degree-`φ` component is invertible
for every simplex map `φ : b ⟶ a` is invertible: every object of the slice lies, up to
isomorphism, in the image of one of the component inclusions, and the sections of the degree-`φ`
component over such an object are the sections of the module itself. -/
public theorem isIso_of_forall_isIso_sliceComponentModuleAt
    {M N : @SheafOfModules.{u} (Over (sliceObj X a W)) _ _ (sliceStructureRingSheaf X a W)}
    (α : M ⟶ N)
    (h : ∀ (b : SimplexCategoryᵒᵖ) (φ : b ⟶ a), IsIso ((sliceComponentModuleAt X W φ).map α)) :
    IsIso α := by
  refine Stacks.SheafOfModules.isIso_of_forall_isIso_forget_app α fun A => ?_
  have := h A.unop.left.degree (SimplicialOpen.Hom.base A.unop.hom)
  have : IsIso ((SheafOfModules.forget (((X.obj A.unop.left.degree).ringCatSheaf).over
      (slicePreimage X W (SimplicialOpen.Hom.base A.unop.hom))) ⋙
      PresheafOfModules.toPresheaf _).map
      ((sliceComponentModuleAt X W (SimplicialOpen.Hom.base A.unop.hom)).map α)) :=
    Functor.map_isIso _ _
  have : IsIso (((SheafOfModules.forget
      ((Stacks.SheafOfModules.Tensor.ringSheaf (zariskiRingedTopos X).O).over
      (sliceObj X a W)) ⋙
      PresheafOfModules.toPresheaf _).map α).app
      (op ((sliceComponentFunctorAt X W (SimplicialOpen.Hom.base A.unop.hom)).obj
        (Over.mk (homOfLE (SimplicialOpen.Hom.le A.unop.hom)))))) :=
    NatIso.isIso_app_of_isIso ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
      ((sliceComponentModuleAt X W (SimplicialOpen.Hom.base A.unop.hom)).map α))
      (op (Over.mk (homOfLE (SimplicialOpen.Hom.le A.unop.hom))))
  have key := Stacks.CategoryTheory.isIso_app_of_objIso
    ((SheafOfModules.forget ((Stacks.SheafOfModules.Tensor.ringSheaf (zariskiRingedTopos X).O).over
      (sliceObj X a W)) ⋙ PresheafOfModules.toPresheaf _).map α)
    (sliceComponentFunctorAtObjIso X W A.unop)
  rw [← Opposite.op_unop A]
  exact key

end At

end AlgebraicGeometry.SimplicialScheme

end
