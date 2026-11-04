module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.SmoothQuotientStackModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.TrivialActionSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SmoothActionGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.ActionGroupoidComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.FunctorialityProjectionCell
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeFlatFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationDescentComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties

/-!
# Classifying stacks of group algebraic spaces and the 1-morphisms between them

Let `S` be a scheme of a big fppf site and let `G` be a group algebraic space over `S`, read as a
group algebraic space over the final algebraic space `AlgebraicGeometry.Space.terminalSpace`. The
classifying stack `BG = [S/G]` is the quotient stack of the action groupoid of Stacks 0444 of the
trivial action of `G` on `S`. This file builds `BG` as an object of the 2-category of algebraic
stacks when `G` is smooth over `S`, and the 1-morphism `BG₁ ⟶ BG₂` induced by a homomorphism
`G₁ ⟶ G₂` of group algebraic spaces.

## Main definitions

* `AlgebraicGeometry.Stack.trivialActionGroupoid`: the action groupoid `(S, G ×_S S, s, t, c)` of
  the trivial action.
* `AlgebraicGeometry.Stack.classifyingAlgebraicStack`: for `G` smooth over `S`, the model of
  `[S/G]` in `AlgebraicGeometry.Stack.AlgebraicStacks`.
* `AlgebraicGeometry.Stack.trivialActionGroupoidHom`: the morphism of groupoids induced by a
  homomorphism `φ : G₁ ⟶ G₂`, the identity on objects and `φ × id` on arrows.
* `AlgebraicGeometry.Stack.classifyingMap`: the induced 1-morphism `BG₁ ⟶ BG₂`, the 1-morphism of
  quotient stacks of Stacks 046Q conjugated by the two model equivalences.
* `AlgebraicGeometry.Stack.classifyingAtlas`: the atlas `S ⟶ BG` of Stacks 044R.
* `AlgebraicGeometry.Stack.classifyingAtlasCompIso`: the 2-isomorphism between the atlas of `BG₁`
  followed by `classifyingMap φ` and the atlas of `BG₂`.

## Main results

* `AlgebraicGeometry.Stack.isSmooth_trivialActionGroupoid`: the trivial action groupoid of a
  smooth group algebraic space is smooth.
* `AlgebraicGeometry.Stack.isSeparated_classifyingMap_comp_structureMorphism`: the composite of
  `classifyingMap φ` with the structure morphism of `BG₂` is separated when `G₁ ⟶ S` is proper,
  flat and locally of finite presentation.
* `AlgebraicGeometry.Stack.not_isSeparatedOver_classifyingAlgebraicStack`: `BG` is not separated
  over `S` when `G ⟶ S` is not separated.
* `AlgebraicGeometry.Stack.isSurjective_classifyingMap`,
  `AlgebraicGeometry.Stack.isFlat_classifyingMap` and
  `AlgebraicGeometry.Stack.isLocallyOfFinitePresentation_classifyingMap`: `classifyingMap φ` is
  surjective, flat and locally of finite presentation.

## Implementation notes

The action of `G` on the monoidal unit `𝟙_ (Over S)` is the instance
`AlgebraicGeometry.Space.modObjTensorUnit`, whose action morphism is the unique morphism to the
final object. It is the trivial action, and it is the instance the separatedness results of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/Quotient/TrivialActionSeparated.lean` are stated
for, which is why it is used here.

The object space of the trivial action groupoid is `S` itself for every `G`, by definition, so the
atlases of `BG₁` and of `BG₂` have the same source, and the 2-isomorphism between `S ⟶ BG₁ ⟶ BG₂`
and `S ⟶ BG₂` is the 2-isomorphism of Stacks 046Q restricted along the inclusion of the object
points (`AlgebraicGeometry.Stack.quotientStackProjectionCell`), conjugated by the unit of the
first model equivalence.

## References

* [Stacks Project, Tag 0444](https://stacks.math.columbia.edu/tag/0444)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
* [Stacks Project, Tag 04TK](https://stacks.math.columbia.edu/tag/04TK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u w v₀ u₀ v₁ u₁ v₂ u₂ v₃ u₃

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-! ### The trivial action groupoid and the classifying stack -/

section ClassifyingStack

variable (G : Space.GroupAlgebraicSpace C S hS (Space.terminalSpace C S hS).obj
  (Space.terminalSpace C S hS).property)

/-- **The groupoid of the trivial action.** For a group algebraic space `G` over `S`, the action
groupoid of Stacks 0444 of the trivial action of `G` on `S`, read as the monoidal unit of the
slice over the final algebraic space: its object space is `S` and its arrow space is `G ×_S S`.
Its quotient stack is the classifying stack `[S/G]`. -/
noncomputable def trivialActionGroupoid :
    GroupoidInAlgebraicSpaces C S hS (Space.terminalSpace C S hS) :=
  (Space.groupoidOfAction (Space.terminalSpace C S hS) G.obj.X
    (𝟙_ (Over (Space.terminalSpace C S hS).obj)) G.property
    (Space.terminalSpace C S hS).property).groupoid

/-- The trivial action groupoid is the action groupoid of the trivial action, on the nose. -/
theorem trivialActionGroupoid_eq :
    trivialActionGroupoid G =
      (Space.groupoidOfAction (Space.terminalSpace C S hS) G.obj.X
        (𝟙_ (Over (Space.terminalSpace C S hS).obj)) G.property
        (Space.terminalSpace C S hS).property).groupoid :=
  rfl

/-- **The trivial action groupoid of a smooth group algebraic space is smooth.** If `G ⟶ S` is
smooth, then the source and the target of the trivial action groupoid are smooth: this is
`AlgebraicGeometry.Space.isSmooth_groupoidOfAction` for the trivial action. -/
theorem isSmooth_trivialActionGroupoid (hG : Space.IsSmooth C S hS G.obj.X.hom) :
    GroupoidInAlgebraicSpaces.IsSmooth C S hS (trivialActionGroupoid G) :=
  Space.isSmooth_groupoidOfAction _ _ _ _ _ hG

/-- **The classifying stack `BG = [S/G]` of a smooth group algebraic space**, as an object of
the 2-category of algebraic stacks: the model
`AlgebraicGeometry.Stack.smoothQuotientAlgebraicStack` of the quotient stack of the trivial
action groupoid, which is algebraic by Stacks 04TK. -/
noncomputable def classifyingAlgebraicStack (hG : Space.IsSmooth C S hS G.obj.X.hom) :
    AlgebraicStacks.{u, w} C S hS :=
  smoothQuotientAlgebraicStack.{u, w} (isSmooth_trivialActionGroupoid G hG)

/-- The classifying stack is equivalent over the site to the quotient stack of the trivial
action groupoid. -/
noncomputable def classifyingAlgebraicStackEquivalenceOver
    (hG : Space.IsSmooth C S hS G.obj.X.hom) :
    StacksRepresentableCFG.EquivalenceOver (quotientStack (trivialActionGroupoid G)).p
      (classifyingAlgebraicStack.{u, w} G hG).val.val.p :=
  smoothQuotientAlgebraicStackEquivalenceOver.{u, w} (isSmooth_trivialActionGroupoid G hG)

end ClassifyingStack

/-! ### The morphism of trivial action groupoids induced by a homomorphism -/

section GroupoidHom

/-- **An element of a fibre product of presheaves is determined by its two projections.** -/
theorem pullback_app_ext {F G H : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ H)
    (g : G ⟶ H) {T : BigFppfOver C S hS} {y₁ y₂ : (pullback f g).obj (Opposite.op T)}
    (h₁ : (pullback.fst f g).app (Opposite.op T) y₁ = (pullback.fst f g).app (Opposite.op T) y₂)
    (h₂ : (pullback.snd f g).app (Opposite.op T) y₁ = (pullback.snd f g).app (Opposite.op T) y₂) :
    y₁ = y₂ := by
  refine yonedaEquiv.symm.injective (pullback.hom_ext ?_ ?_) <;>
    simp only [yonedaEquiv_symm_naturality_right, h₁, h₂]

variable {G₁ G₂ : Space.GroupAlgebraicSpace C S hS (Space.terminalSpace C S hS).obj
  (Space.terminalSpace C S hS).property}

/-- **The map on arrow spaces induced by a homomorphism `φ : G₁ ⟶ G₂`**: the morphism
`φ × id : G₁ ×_S S ⟶ G₂ ×_S S`. -/
noncomputable def trivialActionArrowsMap (φ : G₁ ⟶ G₂) :
    (trivialActionGroupoid G₁).arrows.obj ⟶ (trivialActionGroupoid G₂).arrows.obj :=
  (φ.hom.hom.hom ▷ 𝟙_ (Over (Space.terminalSpace C S hS).obj)).left

/-- The second component of `φ × id` is the second component. -/
theorem trivialActionArrowsMap_snd_app (φ : G₁ ⟶ G₂) (T : (BigFppfOver C S hS)ᵒᵖ)
    (a : (trivialActionGroupoid G₁).arrows.obj.obj T) :
    (snd G₂.obj.X (𝟙_ (Over (Space.terminalSpace C S hS).obj))).left.app T
        ((trivialActionArrowsMap φ).app T a) =
      (snd G₁.obj.X (𝟙_ (Over (Space.terminalSpace C S hS).obj))).left.app T a :=
  Space.appApplyCongr (congrArg Over.Hom.left (whiskerRight_snd φ.hom.hom.hom _)) T a

/-- The first component of `φ × id` is `φ` applied to the first component. -/
theorem trivialActionArrowsMap_fst_app (φ : G₁ ⟶ G₂) (T : (BigFppfOver C S hS)ᵒᵖ)
    (a : (trivialActionGroupoid G₁).arrows.obj.obj T) :
    (fst G₂.obj.X (𝟙_ (Over (Space.terminalSpace C S hS).obj))).left.app T
        ((trivialActionArrowsMap φ).app T a) =
      φ.hom.hom.hom.left.app T
        ((fst G₁.obj.X (𝟙_ (Over (Space.terminalSpace C S hS).obj))).left.app T a) :=
  Space.appApplyCongr (congrArg Over.Hom.left (whiskerRight_fst φ.hom.hom.hom _)) T a

/-- `φ × id` commutes with the sources of the two trivial action groupoids. -/
theorem trivialActionArrowsMap_source (φ : G₁ ⟶ G₂) (T : (BigFppfOver C S hS)ᵒᵖ)
    (a : (trivialActionGroupoid G₁).arrows.obj.obj T) :
    (trivialActionGroupoid G₂).source.hom.app T ((trivialActionArrowsMap φ).app T a) =
      (trivialActionGroupoid G₁).source.hom.app T a :=
  trivialActionArrowsMap_snd_app φ T a

/-- `φ × id` commutes with the targets of the two trivial action groupoids: both targets are
the unique morphism to the final object of the slice. -/
theorem trivialActionArrowsMap_target (φ : G₁ ⟶ G₂) (T : (BigFppfOver C S hS)ᵒᵖ)
    (a : (trivialActionGroupoid G₁).arrows.obj.obj T) :
    (trivialActionGroupoid G₂).target.hom.app T ((trivialActionArrowsMap φ).app T a) =
      (trivialActionGroupoid G₁).target.hom.app T a :=
  Space.appApplyCongr (congrArg Over.Hom.left
    (toUnit_unique ((φ.hom.hom.hom ▷ 𝟙_ (Over (Space.terminalSpace C S hS).obj)) ≫
      γ[G₂.obj.X, 𝟙_ (Over (Space.terminalSpace C S hS).obj)])
      γ[G₁.obj.X, 𝟙_ (Over (Space.terminalSpace C S hS).obj)])) T a

/-- `φ × id` commutes with the compositions of the two trivial action groupoids, `φ` being a
homomorphism. -/
theorem trivialActionArrowsMap_compose (φ : G₁ ⟶ G₂) (T : (BigFppfOver C S hS)ᵒᵖ)
    (a b : (trivialActionGroupoid G₁).arrows.obj.obj T)
    (h : (trivialActionGroupoid G₁).source.hom.app T a =
      (trivialActionGroupoid G₁).target.hom.app T b)
    (h' : (trivialActionGroupoid G₂).source.hom.app T ((trivialActionArrowsMap φ).app T a) =
      (trivialActionGroupoid G₂).target.hom.app T ((trivialActionArrowsMap φ).app T b)) :
    (trivialActionGroupoid G₂).toGroupoidInFunctors.compose T
        ((trivialActionArrowsMap φ).app T a) ((trivialActionArrowsMap φ).app T b) h' =
      (trivialActionArrowsMap φ).app T
        ((trivialActionGroupoid G₁).toGroupoidInFunctors.compose T a b h) := by
  let f := φ.hom.hom.hom
  let X := 𝟙_ (Over (Space.terminalSpace C S hS).obj)
  -- the pair of group components of the composable pair `(φ a, φ b)` is `(φ × φ)` of the one of
  -- `(a, b)`
  have hpair : (Space.actionComposeFstPair (Space.terminalSpace C S hS) G₂.obj.X X G₂.property
        (Space.terminalSpace C S hS).property).app T
          ⟨((trivialActionArrowsMap φ).app T a, (trivialActionArrowsMap φ).app T b), h'⟩ =
      (f ⊗ₘ f).left.app T ((Space.actionComposeFstPair (Space.terminalSpace C S hS) G₁.obj.X X
        G₁.property (Space.terminalSpace C S hS).property).app T ⟨(a, b), h⟩) := by
    refine pullback_app_ext G₂.obj.X.hom G₂.obj.X.hom (T := T.unop) ?_ ?_
    · refine (Space.actionComposeFstPair_fst_app T _).trans ?_
      refine (trivialActionArrowsMap_fst_app φ T a).trans ?_
      refine Eq.trans ?_ (Space.appApplyCongr (congrArg Over.Hom.left (tensorHom_fst f f)) T
        _).symm
      exact congrArg (f.left.app T) (Space.actionComposeFstPair_fst_app T ⟨(a, b), h⟩).symm
    · refine (Space.actionComposeFstPair_snd_app T _).trans ?_
      refine (trivialActionArrowsMap_fst_app φ T b).trans ?_
      refine Eq.trans ?_ (Space.appApplyCongr (congrArg Over.Hom.left (tensorHom_snd f f)) T
        _).symm
      exact congrArg (f.left.app T) (Space.actionComposeFstPair_snd_app T ⟨(a, b), h⟩).symm
  refine pullback_app_ext G₂.obj.X.hom X.hom (T := T.unop) ?_ ?_
  · refine (Space.groupoidOfAction_fst_compose T _ _ h').trans ?_
    refine Eq.trans ?_ (trivialActionArrowsMap_fst_app φ T _).symm
    refine Eq.trans ?_ (congrArg (f.left.app T) (Space.groupoidOfAction_fst_compose T a b h)).symm
    refine Eq.trans ?_ (Space.appApplyCongr (congrArg Over.Hom.left (IsMonHom.mul_hom f)) T
      _).symm
    exact congrArg (μ[G₂.obj.X].left.app T) hpair
  · refine (Space.groupoidOfAction_snd_compose T _ _ h').trans ?_
    refine (trivialActionArrowsMap_snd_app φ T b).trans ?_
    refine Eq.trans ?_ (trivialActionArrowsMap_snd_app φ T _).symm
    exact (Space.groupoidOfAction_snd_compose T a b h).symm

/-- **The morphism of trivial action groupoids induced by a homomorphism `φ : G₁ ⟶ G₂`** of
group algebraic spaces over `S`: the identity on the common object space `S` and
`φ × id : G₁ ×_S S ⟶ G₂ ×_S S` on arrow spaces. -/
noncomputable def trivialActionGroupoidHom (φ : G₁ ⟶ G₂) :
    GroupoidInAlgebraicSpaces.Hom (trivialActionGroupoid G₁) (trivialActionGroupoid G₂) where
  toGroupoidHom :=
    { mapObjects := 𝟙 _
      mapArrows := trivialActionArrowsMap φ
      map_source := trivialActionArrowsMap_source φ
      map_target := trivialActionArrowsMap_target φ
      map_comp := fun T a b h => trivialActionArrowsMap_compose φ T a b h _
      map_id := Space.mapIdentityOfMapComp
        (G := (trivialActionGroupoid G₁).toGroupoidInFunctors)
        (H := (trivialActionGroupoid G₂).toGroupoidInFunctors)
        (𝟙 _) (trivialActionArrowsMap φ) (trivialActionArrowsMap_source φ)
        (trivialActionArrowsMap_target φ)
        (fun T a b h => trivialActionArrowsMap_compose φ T a b h _) }
  mapObjects_over := Category.id_comp _
  mapArrows_over := Over.w (φ.hom.hom.hom ▷ 𝟙_ (Over (Space.terminalSpace C S hS).obj))

/-- The map on object spaces of `AlgebraicGeometry.Stack.trivialActionGroupoidHom` is the
identity. -/
theorem trivialActionGroupoidHom_mapObjects (φ : G₁ ⟶ G₂) :
    (trivialActionGroupoidHom φ).toGroupoidHom.mapObjects = 𝟙 _ :=
  rfl

/-- The map on arrow spaces of `AlgebraicGeometry.Stack.trivialActionGroupoidHom` is `φ × id`. -/
theorem trivialActionGroupoidHom_mapArrows (φ : G₁ ⟶ G₂) :
    (trivialActionGroupoidHom φ).toGroupoidHom.mapArrows = trivialActionArrowsMap φ :=
  rfl

end GroupoidHom

/-! ### Whiskering 2-isomorphisms of based functors -/

section Whiskering

variable {𝒮 : Type u₀} [Category.{v₀} 𝒮] {𝒳 : BasedCategory.{v₁, u₁} 𝒮}
  {𝒴 : BasedCategory.{v₂, u₂} 𝒮} {𝒵 : BasedCategory.{v₃, u₃} 𝒮}

/-- A 2-isomorphism of based functors whiskered on the left by a based functor, between based
categories of possibly different universes. -/
noncomputable def basedIsoWhiskerLeft (F : 𝒳 ⥤ᵇ 𝒴) {G H : 𝒴 ⥤ᵇ 𝒵} (β : G ≅ H) :
    BasedFunctor.comp F G ≅ BasedFunctor.comp F H :=
  BasedNatIso.mkNatIso
    (Functor.isoWhiskerLeft F.toFunctor ((BasedNatTrans.forgetful 𝒴 𝒵).mapIso β))
    (fun a => β.hom.isHomLift (F.w_obj a))

/-- A 2-isomorphism of based functors whiskered on the right by a based functor, between based
categories of possibly different universes. -/
noncomputable def basedIsoWhiskerRight {F G : 𝒳 ⥤ᵇ 𝒴} (β : F ≅ G) (H : 𝒴 ⥤ᵇ 𝒵) :
    BasedFunctor.comp F H ≅ BasedFunctor.comp G H :=
  BasedNatIso.mkNatIso
    (Functor.isoWhiskerRight ((BasedNatTrans.forgetful 𝒳 𝒴).mapIso β) H.toFunctor)
    (fun a => by
      change 𝒵.p.IsHomLift (𝟙 (𝒳.p.obj a)) (H.map (β.hom.toNatTrans.app a))
      infer_instance)

/-- A component of a natural isomorphism lying over an identity still lies over that identity
after a transport along an equality of target functors. -/
theorem isHomLift_trans_eqToIso_hom_app {F X Y : 𝒳.obj ⥤ 𝒴.obj} (α : F ≅ X) (h : X = Y)
    (a : 𝒳.obj) (ha : 𝒴.p.IsHomLift (𝟙 (𝒳.p.obj a)) (α.hom.app a)) :
    𝒴.p.IsHomLift (𝟙 (𝒳.p.obj a)) ((α ≪≫ eqToIso h).hom.app a) := by
  subst h
  simpa using ha

/-- The forward 1-morphism of an equivalence over the site, as a based functor. -/
abbrev equivalenceOverHomBased
    (e : StacksRepresentableCFG.EquivalenceOver 𝒳.p 𝒴.p) : 𝒳 ⥤ᵇ 𝒴 :=
  ⟨e.hom.functor, e.hom.w⟩

/-- The backward 1-morphism of an equivalence over the site, as a based functor. -/
abbrev equivalenceOverInvBased
    (e : StacksRepresentableCFG.EquivalenceOver 𝒳.p 𝒴.p) : 𝒴 ⥤ᵇ 𝒳 :=
  ⟨e.inv.functor, e.inv.w⟩

/-- The unit of an equivalence over the site, as a 2-isomorphism of based functors. -/
noncomputable def equivalenceOverUnitBasedIso
    (e : StacksRepresentableCFG.EquivalenceOver 𝒳.p 𝒴.p) :
    BasedFunctor.comp (equivalenceOverHomBased e) (equivalenceOverInvBased e) ≅
      BasedFunctor.id 𝒳 :=
  BasedNatIso.mkNatIso e.unitIso.symm (fun a => e.isHomLift_unitIso_inv_app a)

end Whiskering

/-! ### The induced 1-morphism of classifying stacks -/

section ClassifyingMap

variable {G₁ G₂ : Space.GroupAlgebraicSpace C S hS (Space.terminalSpace C S hS).obj
  (Space.terminalSpace C S hS).property}

/-- **The inclusion of the object points intertwines the two trivial action groupoids.** Since
the map on object spaces of `AlgebraicGeometry.Stack.trivialActionGroupoidHom` is the identity,
the inclusion of the object points of the first groupoid followed by the pointwise map of
Stacks 046Q is the inclusion of the object points of the second. -/
theorem pointwiseObjectInclusion_comp_trivialActionPointwiseMap (φ : G₁ ⟶ G₂) :
    pointwiseObjectInclusion (trivialActionGroupoid G₁) ⋙
        (quotientPointwiseMap (trivialActionGroupoidHom φ)).toFunctor =
      pointwiseObjectInclusion (trivialActionGroupoid G₂) := by
  have h : (associatedMap C S hS (trivialActionGroupoidHom φ).toGroupoidHom.mapObjects).1 =
      𝟙 _ :=
    hom_ext_of_obj C S hS (fun x => by rw [associatedMap_obj]; rfl)
  rw [pointwiseObjectInclusion_comp_quotientPointwiseMap, objectSpaceMap, h]
  rfl

/-- The projection of the second trivial action groupoid, read through the pointwise map of
Stacks 046Q out of the first. -/
theorem pointwiseObjectInclusion_comp_trivialActionPointwiseMap_comp (φ : G₁ ⟶ G₂) :
    pointwiseObjectInclusion (trivialActionGroupoid G₁) ⋙
        (quotientPointwiseMap (trivialActionGroupoidHom φ)).toFunctor ⋙
          pointwiseToQuotientStack (trivialActionGroupoid G₂) =
      (quotientStackProjection (trivialActionGroupoid G₂)).toFunctor := by
  rw [← Functor.assoc, pointwiseObjectInclusion_comp_trivialActionPointwiseMap]
  rfl

/-- **The projection of Stacks 044R against the induced 1-morphism of Stacks 046Q, for trivial
action groupoids.** The projection `S ⟶ [S/G₁]` followed by `[S/G₁] ⟶ [S/G₂]` is 2-isomorphic,
over the site, to the projection `S ⟶ [S/G₂]`. This is
`AlgebraicGeometry.Stack.quotientStackProjectionCell` composed with the equality
`AlgebraicGeometry.Stack.pointwiseObjectInclusion_comp_trivialActionPointwiseMap_comp`. -/
noncomputable def trivialActionProjectionIso (φ : G₁ ⟶ G₂) :
    BasedFunctor.comp (quotientStackProjection (trivialActionGroupoid G₁))
        (quotientStackMap (trivialActionGroupoidHom φ)) ≅
      quotientStackProjection (trivialActionGroupoid G₂) :=
  BasedNatIso.mkNatIso
    (quotientStackProjectionCell (trivialActionGroupoidHom φ) ≪≫
      eqToIso (pointwiseObjectInclusion_comp_trivialActionPointwiseMap_comp φ))
    (fun a => isHomLift_trans_eqToIso_hom_app _ _ a
      (quotientStackProjectionCell_isHomLift (trivialActionGroupoidHom φ) a))

/-- The underlying natural isomorphism of
`AlgebraicGeometry.Stack.trivialActionProjectionIso` is the 2-isomorphism of Stacks 046Q
restricted along the inclusion of the object points, followed by a transport along an equality
of functors. -/
theorem trivialActionProjectionIso_toNatIso (φ : G₁ ⟶ G₂) :
    (BasedNatTrans.forgetful _ _).mapIso (trivialActionProjectionIso φ) =
      quotientStackProjectionCell (trivialActionGroupoidHom φ) ≪≫
        eqToIso (pointwiseObjectInclusion_comp_trivialActionPointwiseMap_comp φ) :=
  rfl

variable (h₁ : Space.IsSmooth C S hS G₁.obj.X.hom) (h₂ : Space.IsSmooth C S hS G₂.obj.X.hom)

/-- **The 1-morphism `BG₁ ⟶ BG₂` of classifying stacks induced by a homomorphism `φ : G₁ ⟶ G₂`**
of smooth group algebraic spaces over `S`. It is the 1-morphism `[S/G₁] ⟶ [S/G₂]` of quotient
stacks of Stacks 046Q induced by `AlgebraicGeometry.Stack.trivialActionGroupoidHom`, conjugated by
the two model equivalences: the inverse of the first, then the forward one of the second. -/
noncomputable def classifyingMap (φ : G₁ ⟶ G₂) :
    classifyingAlgebraicStack.{u, w} G₁ h₁ ⟶ classifyingAlgebraicStack.{u, w} G₂ h₂ :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    { toFunctor := (classifyingAlgebraicStackEquivalenceOver.{u, w} G₁ h₁).inv.functor ⋙
        (quotientStackMap (trivialActionGroupoidHom φ)).toFunctor ⋙
          (classifyingAlgebraicStackEquivalenceOver.{u, w} G₂ h₂).hom.functor
      w := by
        rw [Functor.assoc, Functor.assoc,
          (classifyingAlgebraicStackEquivalenceOver.{u, w} G₂ h₂).hom.w,
          (quotientStackMap (trivialActionGroupoidHom φ)).w,
          (classifyingAlgebraicStackEquivalenceOver.{u, w} G₁ h₁).inv.w] })

/-- `AlgebraicGeometry.Stack.classifyingMap` as a based functor: the inverse of the first model
equivalence, the 1-morphism of quotient stacks of Stacks 046Q, and the second model
equivalence. -/
theorem classifyingMap_hom_hom (φ : G₁ ⟶ G₂) :
    (classifyingMap.{u, w} h₁ h₂ φ).hom.hom =
      BasedFunctor.comp
        (equivalenceOverInvBased (classifyingAlgebraicStackEquivalenceOver.{u, w} G₁ h₁))
        (BasedFunctor.comp (quotientStackMap (trivialActionGroupoidHom φ))
          (equivalenceOverHomBased (classifyingAlgebraicStackEquivalenceOver.{u, w} G₂ h₂))) :=
  rfl

/-- The underlying functor of `AlgebraicGeometry.Stack.classifyingMap`. -/
theorem classifyingMap_toFunctor (φ : G₁ ⟶ G₂) :
    (classifyingMap.{u, w} h₁ h₂ φ).hom.hom.toFunctor =
      (classifyingAlgebraicStackEquivalenceOver.{u, w} G₁ h₁).inv.functor ⋙
        (quotientStackMap (trivialActionGroupoidHom φ)).toFunctor ⋙
          (classifyingAlgebraicStackEquivalenceOver.{u, w} G₂ h₂).hom.functor :=
  rfl

variable (G₁) in
/-- **The atlas `S ⟶ BG` of Stacks 044R**: the canonical projection of the object space `S` of
the trivial action groupoid to its quotient stack, followed by the model equivalence. -/
noncomputable def classifyingAtlas :
    algebraicSpaceStack.{u, w} C S hS (Space.terminalSpace C S hS).obj
        (Space.terminalSpace C S hS).property ⟶
      classifyingAlgebraicStack.{u, w} G₁ h₁ :=
  quotientStackModelProjection.{u, w} C S hS (Space.terminalSpace C S hS)
    (trivialActionGroupoid G₁) (classifyingAlgebraicStack.{u, w} G₁ h₁)
    (classifyingAlgebraicStackEquivalenceOver.{u, w} G₁ h₁)

/-- **The atlas of `BG₁` followed by `classifyingMap φ` is 2-isomorphic to the atlas of `BG₂`**,
as 1-morphisms of categories fibred in groupoids over the site. The 2-isomorphism is the unit of
the first model equivalence followed by `AlgebraicGeometry.Stack.trivialActionProjectionIso`
whiskered by the second model equivalence. -/
noncomputable def classifyingAtlasCompIsoHom (φ : G₁ ⟶ G₂) :
    (classifyingAtlas.{u, w} G₁ h₁ ≫ classifyingMap.{u, w} h₁ h₂ φ).hom ≅
      (classifyingAtlas.{u, w} G₂ h₂).hom :=
  Bicategory.InducedBicategory.isoMk
    (basedIsoWhiskerLeft (quotientStackProjection (trivialActionGroupoid G₁))
        (basedIsoWhiskerRight
          (equivalenceOverUnitBasedIso (classifyingAlgebraicStackEquivalenceOver.{u, w} G₁ h₁))
          (BasedFunctor.comp (quotientStackMap (trivialActionGroupoidHom φ))
            (equivalenceOverHomBased
              (classifyingAlgebraicStackEquivalenceOver.{u, w} G₂ h₂)))) ≪≫
      basedIsoWhiskerRight (trivialActionProjectionIso φ)
        (equivalenceOverHomBased (classifyingAlgebraicStackEquivalenceOver.{u, w} G₂ h₂)))

/-- **The atlas of `BG₁` followed by `classifyingMap φ` is 2-isomorphic to the atlas of `BG₂`**,
in the 2-category of algebraic stacks. -/
noncomputable def classifyingAtlasCompIso (φ : G₁ ⟶ G₂) :
    classifyingAtlas.{u, w} G₁ h₁ ≫ classifyingMap.{u, w} h₁ h₂ φ ≅
      classifyingAtlas.{u, w} G₂ h₂ :=
  Bicategory.InducedBicategory.isoMk (classifyingAtlasCompIsoHom.{u, w} h₁ h₂ φ)

end ClassifyingMap

/-! ### Separatedness -/

section Separation

variable {G₁ G₂ : Space.GroupAlgebraicSpace C S hS (Space.terminalSpace C S hS).obj
  (Space.terminalSpace C S hS).property}
  (h₁ : Space.IsSmooth C S hS G₁.obj.X.hom) (h₂ : Space.IsSmooth C S hS G₂.obj.X.hom)

/-- `classifyingMap φ` followed by the structure morphism of `BG₂` is the structure morphism of
`BG₁`: every 1-morphism of algebraic stacks over `S` commutes with the structure morphisms. -/
theorem classifyingMap_comp_structureMorphism (φ : G₁ ⟶ G₂) :
    classifyingMap.{u, w} h₁ h₂ φ ≫
        structureMorphism.{u, w} C S hS (classifyingAlgebraicStack.{u, w} G₂ h₂) =
      structureMorphism.{u, w} C S hS (classifyingAlgebraicStack.{u, w} G₁ h₁) :=
  comp_structureMorphism C S hS _

/-- **`BG` is separated over `S` when `G ⟶ S` is proper, flat and locally of finite
presentation.** This is `AlgebraicGeometry.Stack.isSeparatedOver_quotientStack_trivialAction`
(Stacks 0DTY part (6) for the trivial action) at the model equivalence. -/
theorem isSeparatedOver_classifyingAlgebraicStack
    (G : Space.GroupAlgebraicSpace C S hS (Space.terminalSpace C S hS).obj
      (Space.terminalSpace C S hS).property)
    (hG : Space.IsSmooth C S hS G.obj.X.hom)
    (hproper : Space.IsProper C S hS G.obj.X.hom) (hflat : Space.IsFlat C S hS G.obj.X.hom)
    (hlfp : Space.IsLocallyOfFinitePresentation C S hS G.obj.X.hom) :
    IsSeparatedOver.{u, w} C S hS (classifyingAlgebraicStack.{u, w} G hG) :=
  isSeparatedOver_quotientStack_trivialAction.{u, w} G.obj.X G.property
    (Space.groupoidOfAction (Space.terminalSpace C S hS) G.obj.X
      (𝟙_ (Over (Space.terminalSpace C S hS).obj)) G.property
      (Space.terminalSpace C S hS).property)
    (classifyingAlgebraicStack.{u, w} G hG) ⟨classifyingAlgebraicStackEquivalenceOver.{u, w} G hG⟩
    hproper hflat hlfp

/-- **The composite of `classifyingMap φ` with the structure morphism of `BG₂` is separated**
when `G₁ ⟶ S` is proper, flat and locally of finite presentation: the composite is the structure
morphism of `BG₁` (`AlgebraicGeometry.Stack.classifyingMap_comp_structureMorphism`), which is
separated by `AlgebraicGeometry.Stack.isSeparatedOver_classifyingAlgebraicStack`. -/
theorem isSeparated_classifyingMap_comp_structureMorphism (φ : G₁ ⟶ G₂)
    (hproper : Space.IsProper C S hS G₁.obj.X.hom) (hflat : Space.IsFlat C S hS G₁.obj.X.hom)
    (hlfp : Space.IsLocallyOfFinitePresentation C S hS G₁.obj.X.hom) :
    AlgebraicStacks.IsSeparated C S hS (classifyingMap.{u, w} h₁ h₂ φ ≫
      structureMorphism.{u, w} C S hS (classifyingAlgebraicStack.{u, w} G₂ h₂)) := by
  rw [classifyingMap_comp_structureMorphism]
  exact isSeparatedOver_classifyingAlgebraicStack G₁ h₁ hproper hflat hlfp

/-- **If `BG` is separated over `S`, then `G ⟶ S` is separated.** Separatedness of `BG` over `S`
is properness of its diagonal relative to the base, which by Stacks 04M9
(`AlgebraicGeometry.Stack.hasRelativeProperty_diagonal_iff_sourceTarget`) is properness of
`(t, s) : G ×_S S ⟶ S ×_S S`. A proper morphism is separated, the structure morphism of
`S ×_S S` is an isomorphism, and the structure morphism `G ×_S S ⟶ S` of the arrow space is
`G ⟶ S` precomposed with the isomorphism `G ×_S S ≅ G`. -/
theorem isSeparated_of_isSeparatedOver_classifyingAlgebraicStack
    (G : Space.GroupAlgebraicSpace C S hS (Space.terminalSpace C S hS).obj
      (Space.terminalSpace C S hS).property)
    (hG : Space.IsSmooth C S hS G.obj.X.hom)
    (hsep : IsSeparatedOver.{u, w} C S hS (classifyingAlgebraicStack.{u, w} G hG)) :
    Space.IsSeparated C S hS G.obj.X.hom := by
  have : (Space.properProperty C S hS).IsStableUnderBaseChange :=
    Space.isProper_isStableUnderBaseChange C S hS
  have : (Space.properProperty C S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} C S hS) :=
    Space.proper_isLocalAtTarget_fppf C S hS
  have hj : Space.IsProper C S hS
      (GroupoidInAlgebraicSpaces.sourceTarget (trivialActionGroupoid G)).hom :=
    (hasRelativeProperty_diagonal_iff_sourceTarget (trivialActionGroupoid G)
      (classifyingAlgebraicStack.{u, w} G hG) (Space.properProperty C S hS)
      ⟨classifyingAlgebraicStackEquivalenceOver.{u, w} G hG⟩).mp
      ((relativeProperty_diagonal_iff_relativeDiagonal_structureMorphism.{u, w} C S hS
        (classifyingAlgebraicStack.{u, w} G hG) (Space.properProperty C S hS)).mpr hsep)
  have hiso : IsIso ((GroupoidInAlgebraicSpaces.objectPairsTarget
      (trivialActionGroupoid G)).hom ≫ (trivialActionGroupoid G).objectsToBase.hom) := by
    show IsIso (pullback.fst (𝟙 (Space.terminalSpace C S hS).obj)
      (𝟙 (Space.terminalSpace C S hS).obj) ≫ 𝟙 (Space.terminalSpace C S hS).obj)
    infer_instance
  have hR : Space.IsSeparated C S hS (trivialActionGroupoid G).arrowsToBase.hom := by
    rw [← sourceTarget_comp_objectPairs_toBase (trivialActionGroupoid G)]
    exact Space.isSeparated_comp C S hS _ _ (Space.IsProper.isSeparated C S hS hj)
      (Space.isSeparated_of_isIso C S hS _)
  have hR' : Space.IsSeparated C S hS
      (pullback.fst G.obj.X.hom (𝟙 (Space.terminalSpace C S hS).obj) ≫ G.obj.X.hom) := hR
  have h := Space.isSeparated_comp C S hS
    (inv (pullback.fst G.obj.X.hom (𝟙 (Space.terminalSpace C S hS).obj))) _
    (Space.isSeparated_of_isIso C S hS _) hR'
  rwa [IsIso.inv_hom_id_assoc] at h

/-- **`BG` is not separated over `S` when `G ⟶ S` is not separated.** The contrapositive of
`AlgebraicGeometry.Stack.isSeparated_of_isSeparatedOver_classifyingAlgebraicStack`; equivalently,
the structure morphism of `BG` is not a separated 1-morphism of algebraic stacks. -/
theorem not_isSeparatedOver_classifyingAlgebraicStack
    (G : Space.GroupAlgebraicSpace C S hS (Space.terminalSpace C S hS).obj
      (Space.terminalSpace C S hS).property)
    (hG : Space.IsSmooth C S hS G.obj.X.hom)
    (hnsep : ¬ Space.IsSeparated C S hS G.obj.X.hom) :
    ¬ AlgebraicStacks.IsSeparated C S hS
      (structureMorphism.{u, w} C S hS (classifyingAlgebraicStack.{u, w} G hG)) :=
  fun hsep => hnsep (isSeparated_of_isSeparatedOver_classifyingAlgebraicStack G hG hsep)

end Separation

/-! ### Surjectivity, flatness and local finite presentation of the induced 1-morphism -/

section Fppf

variable {G₁ G₂ : Space.GroupAlgebraicSpace C S hS (Space.terminalSpace C S hS).obj
  (Space.terminalSpace C S hS).property}
  (h₁ : Space.IsSmooth C S hS G₁.obj.X.hom) (h₂ : Space.IsSmooth C S hS G₂.obj.X.hom)

/-- **The atlas `S ⟶ BG` is representable by algebraic spaces, surjective, flat and locally of
finite presentation** (Stacks 06FH): the source and the target of the trivial action groupoid of
a smooth group algebraic space are smooth, hence flat and locally of finite presentation. -/
theorem classifyingAtlas_fppf
    (G : Space.GroupAlgebraicSpace C S hS (Space.terminalSpace C S hS).obj
      (Space.terminalSpace C S hS).property)
    (hG : Space.IsSmooth C S hS G.obj.X.hom) :
    IsRepresentableByAlgebraicSpaces C S hS (classifyingAtlas.{u, w} G hG).hom.hom ∧
      IsSurjective C S hS (classifyingAtlas.{u, w} G hG) ∧
      AlgebraicStacks.IsFlat C S hS (classifyingAtlas.{u, w} G hG) ∧
      AlgebraicStacks.IsLocallyOfFinitePresentation C S hS (classifyingAtlas.{u, w} G hG) :=
  have ⟨hs, ht⟩ := isSmooth_trivialActionGroupoid G hG
  quotientModelAtlasFppf (trivialActionGroupoid G) (classifyingAlgebraicStack.{u, w} G hG)
    (classifyingAlgebraicStackEquivalenceOver.{u, w} G hG)
    (Space.isFlat_of_isSmooth C S hS _ hs) (Space.isFlat_of_isSmooth C S hS _ ht)
    (Space.isLocallyOfFinitePresentation_of_isSmooth C S hS hs)
    (Space.isLocallyOfFinitePresentation_of_isSmooth C S hS ht)

/-- The atlas of `BG₁` followed by `classifyingMap φ` is surjective, flat and locally of finite
presentation, being 2-isomorphic to the atlas of `BG₂`. -/
theorem classifyingAtlas_comp_classifyingMap_fppf (φ : G₁ ⟶ G₂) :
    IsSurjective C S hS (classifyingAtlas.{u, w} G₁ h₁ ≫ classifyingMap.{u, w} h₁ h₂ φ) ∧
      AlgebraicStacks.IsFlat C S hS
        (classifyingAtlas.{u, w} G₁ h₁ ≫ classifyingMap.{u, w} h₁ h₂ φ) ∧
      AlgebraicStacks.IsLocallyOfFinitePresentation C S hS
        (classifyingAtlas.{u, w} G₁ h₁ ≫ classifyingMap.{u, w} h₁ h₂ φ) := by
  obtain ⟨-, hsurj, hflat, hlfp⟩ := classifyingAtlas_fppf.{u, w} G₂ h₂
  refine ⟨?_, (AlgebraicStacks.isFlat_iff_of_twoIso C S hS _ _
      (classifyingAtlasCompIsoHom.{u, w} h₁ h₂ φ)).2 hflat,
    (AlgebraicStacks.isLocallyOfFinitePresentation_iff_of_twoIso C S hS _ _
      (classifyingAtlasCompIsoHom.{u, w} h₁ h₂ φ)).2 hlfp⟩
  show Function.Surjective (AlgebraicStacks.pointsMap C S hS _)
  rw [AlgebraicStacks.pointsMap_eq_of_hom₂ C S hS (classifyingAtlasCompIso.{u, w} h₁ h₂ φ).hom]
  exact hsurj

/-- **`classifyingMap φ` is surjective** (Stacks 06PN): its precomposition with the atlas of
`BG₁` is surjective. -/
theorem isSurjective_classifyingMap (φ : G₁ ⟶ G₂) :
    IsSurjective C S hS (classifyingMap.{u, w} h₁ h₂ φ) :=
  isSurjective_of_isSurjective_comp C S hS (classifyingAtlas.{u, w} G₁ h₁) _
    (classifyingAtlas_comp_classifyingMap_fppf.{u, w} h₁ h₂ φ).1

/-- **`classifyingMap φ` is flat** (Stacks 06Q0): its precomposition with the atlas of `BG₁`,
which is surjective and flat, is flat. -/
theorem isFlat_classifyingMap (φ : G₁ ⟶ G₂) :
    AlgebraicStacks.IsFlat C S hS (classifyingMap.{u, w} h₁ h₂ φ) :=
  AlgebraicStacks.isFlat_of_isSurjective_of_isFlat_comp C S hS
    (classifyingAtlas.{u, w} G₁ h₁) _
    (classifyingAtlas_comp_classifyingMap_fppf.{u, w} h₁ h₂ φ).2.1
    (classifyingAtlas_fppf.{u, w} G₁ h₁).2.1 (classifyingAtlas_fppf.{u, w} G₁ h₁).2.2.1

/-- **`classifyingMap φ` is locally of finite presentation** (Stacks 06Q9): its precomposition
with the atlas of `BG₁`, which is surjective, flat and locally of finite presentation, is locally
of finite presentation. -/
theorem isLocallyOfFinitePresentation_classifyingMap (φ : G₁ ⟶ G₂) :
    AlgebraicStacks.IsLocallyOfFinitePresentation C S hS (classifyingMap.{u, w} h₁ h₂ φ) :=
  AlgebraicStacks.isLocallyOfFinitePresentation_of_comp_of_fppf C S hS
    (classifyingAtlas.{u, w} G₁ h₁) _
    (classifyingAtlas_comp_classifyingMap_fppf.{u, w} h₁ h₂ φ).2.2
    (classifyingAtlas_fppf.{u, w} G₁ h₁).2.1 (classifyingAtlas_fppf.{u, w} G₁ h₁).2.2.1
    (classifyingAtlas_fppf.{u, w} G₁ h₁).2.2.2

end Fppf

end AlgebraicGeometry.Stack

end
