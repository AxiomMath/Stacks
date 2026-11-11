module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.AbstractGroupQuotientStackConstantData
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ActionGroupoidPointwisePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.TorsorsWithEquivariantMap
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.IsomorphismSheaf
public import StacksFrontier.CategoryTheory.FiberedCategory.Rigidification

/-!
# The presentation of a classifying stack is rigidified by the points of the group

Let `G` be a group algebraic space over a scheme `S` of a big fppf site, and let `[S/G]` be the
quotient stack of the trivial action of `G` on `S` (Stacks 044Q). Its presentation, the
pointwise groupoid fibration of the action groupoid `(S, G ×_S S, pr₂, a, m)` of Stacks 0444,
has over every test object `T` a single object, the unique point `T ⟶ S`, and its arrows over a
morphism `f : T ⟶ T'` are the points of `G` over `T`. This file records that description as a
rigidification of the presentation by the presheaf of groups of points of `G`
(`CategoryTheory.Functor.Rigidification`), so that descent data for the presentation can be
built from, and compared through, Čech cocycles with values in `G`.

## Main definitions

* `AlgebraicGeometry.Space.baseTrivialActionGroupoid`: the action groupoid of the trivial action of
  `G` on `S`, whose quotient stack is `[S/G]`.
* `AlgebraicGeometry.Space.GroupAlgebraicSpace.pointsGrpPresheaf`: the presheaf of groups
  `T ↦ Hom_S(T, G)` on the big fppf site of `S`.
* `AlgebraicGeometry.Space.trivialActionRigidification`: the rigidification of the presentation
  of `[S/G]` by the points of `G`; the element of an arrow is the inverse of its `G`-component.
* `AlgebraicGeometry.Space.trivialActionPoint`: the object of the presentation over `T` given by
  the unique point `T ⟶ S`.
* `AlgebraicGeometry.Space.trivialStackObjectIsomEquiv`: **Stacks 044V** for the trivial object
  of `[S/G]` over `T`: the automorphisms of its pullback to `V ⟶ T` are the points of `G` over
  `V`, canonically (`AlgebraicGeometry.Space.trivialStackObjectIsomEquiv_pointwiseArrowSection`).

## Implementation notes

An arrow of the pointwise action groupoid has its `G`-component
(`AlgebraicGeometry.Space.actionPointwiseGroupElement`), and the component of a composite
`φ ≫ χ` is the product `f^* g_χ · g_φ` of the restricted component of the second arrow with the
component of the first (`AlgebraicGeometry.Space.actionPointwiseGroupElement_comp`). The
convention of `CategoryTheory.Functor.Rigidification` is the opposite one, so the element of an
arrow is the inverse of its component.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Space

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_QuotientStackTrivialActionRigidification
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_QuotientStackTrivialActionRigidification
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) : HasLimit (cospan f g) :=
  hasPullbacks_presheaf_QuotientStackTrivialActionRigidification.has_limit _

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  (G : GroupAlgebraicSpace 𝒞 S hS (baseS 𝒞 S hS) (isAlgebraicSpace_baseS 𝒞 S hS))

/-- The action groupoid of the trivial action of a group algebraic space `G` over `S` on `S`
itself. Its quotient stack is the classifying stack `[S/G]`, that is
`AlgebraicGeometry.Stack.quotientStackOfAction` of the trivial action. -/
abbrev baseTrivialActionGroupoid :
    GroupoidInAlgebraicSpaces 𝒞 S hS ⟨baseS 𝒞 S hS, isAlgebraicSpace_baseS 𝒞 S hS⟩ :=
  (groupoidOfAction ⟨baseS 𝒞 S hS, isAlgebraicSpace_baseS 𝒞 S hS⟩ G.obj.X
    (𝟙_ (Over (baseS 𝒞 S hS))) G.property (isAlgebraicSpace_baseS 𝒞 S hS)).groupoid

variable (𝒞 S hS) in
/-- An object of the big fppf site of `S`, as a presheaf over `S`. -/
abbrev yonedaOverBaseS : BigFppfOver 𝒞 S hS ⥤ Over (baseS 𝒞 S hS) :=
  yoneda.toOver (baseS 𝒞 S hS) (fun Y => toBaseS (yoneda.obj Y)) (fun _ => baseS_ext _ _)

/-- The presheaf of groups of points of a group algebraic space `G` over `S`: its value at an
object `T` of the big fppf site of `S` is the group of morphisms `T ⟶ G` over `S`. -/
abbrev GroupAlgebraicSpace.pointsGrpPresheaf : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ GrpCat.{u + 1} :=
  (yonedaOverBaseS 𝒞 S hS).op ⋙ yonedaGrpObj G.obj.X

/-- The `G`-component of an arrow of the presentation of `[S/G]`, as a point of `G` over the
source of the arrow. -/
def trivialActionComponent {x y : (Stack.quotientPrestack (baseTrivialActionGroupoid G)).obj}
    (φ : x ⟶ y) :
    (yonedaOverBaseS 𝒞 S hS).obj ((Stack.quotientPrestack (baseTrivialActionGroupoid G)).p.obj x) ⟶
      G.obj.X :=
  Over.homMk (actionPointwiseGroupElement (isAlgebraicSpace_baseS 𝒞 S hS) G
    (𝟙_ (Over (baseS 𝒞 S hS))) (isAlgebraicSpace_baseS 𝒞 S hS) φ.down) (baseS_ext _ _)

/-- The component of a composite. -/
lemma trivialActionComponent_comp
    {x y z : (Stack.quotientPrestack (baseTrivialActionGroupoid G)).obj}
    (φ : x ⟶ y) (χ : y ⟶ z) :
    trivialActionComponent G (φ ≫ χ) =
      (yonedaOverBaseS 𝒞 S hS).map
          ((Stack.quotientPrestack (baseTrivialActionGroupoid G)).p.map φ) ≫
          trivialActionComponent G χ * trivialActionComponent G φ := by
  ext1
  refine (actionPointwiseGroupElement_comp (isAlgebraicSpace_baseS 𝒞 S hS) G
    (𝟙_ (Over (baseS 𝒞 S hS))) (isAlgebraicSpace_baseS 𝒞 S hS) φ.down χ.down).trans ?_
  rw [Hom.mul_def]
  simp [trivialActionComponent]
  rfl

/-- Over every test object the evaluated trivial action groupoid has a single object, the unique
point of `S`. -/
instance subsingleton_baseTrivialActionGroupoid_objects (T : (BigFppfOver 𝒞 S hS)ᵒᵖ) :
    Subsingleton ((baseTrivialActionGroupoid G).toGroupoidInFunctors.objects.obj T) :=
  ⟨fun a b => (Over.mkIdTerminal (X := 𝒞.obj hS)).hom_ext
    (show T.unop ⟶ Over.mk (𝟙 (𝒞.obj hS)) from a) b⟩

/-- The arrow of the presentation of `[S/G]` over a given morphism of the site with a given
`G`-component. -/
def trivialActionArrow {x y : (Stack.quotientPrestack (baseTrivialActionGroupoid G)).obj}
    (f : (Stack.quotientPrestack (baseTrivialActionGroupoid G)).p.obj x ⟶
      (Stack.quotientPrestack (baseTrivialActionGroupoid G)).p.obj y)
    (a : (yonedaOverBaseS 𝒞 S hS).obj
        ((Stack.quotientPrestack (baseTrivialActionGroupoid G)).p.obj x) ⟶ G.obj.X) : x ⟶ y :=
  ⟨{ base := f
     fiber := ((baseTrivialActionGroupoid G).toGroupoidInFunctors.evaluationArrowEquiv _ _ _).symm
      ⟨yonedaEquiv (pullback.lift a.left (toBaseS _) (baseS_ext _ _)), Subsingleton.elim _ _,
        Subsingleton.elim _ _⟩ }⟩

@[simp]
lemma trivialActionArrow_base {x y : (Stack.quotientPrestack (baseTrivialActionGroupoid G)).obj}
    (f : (Stack.quotientPrestack (baseTrivialActionGroupoid G)).p.obj x ⟶
      (Stack.quotientPrestack (baseTrivialActionGroupoid G)).p.obj y)
    (a : (yonedaOverBaseS 𝒞 S hS).obj
        ((Stack.quotientPrestack (baseTrivialActionGroupoid G)).p.obj x) ⟶ G.obj.X) :
    (Stack.quotientPrestack (baseTrivialActionGroupoid G)).p.map (trivialActionArrow G f a) = f :=
  rfl

@[simp]
lemma trivialActionComponent_trivialActionArrow
    {x y : (Stack.quotientPrestack (baseTrivialActionGroupoid G)).obj}
    (f : (Stack.quotientPrestack (baseTrivialActionGroupoid G)).p.obj x ⟶
      (Stack.quotientPrestack (baseTrivialActionGroupoid G)).p.obj y)
    (a : (yonedaOverBaseS 𝒞 S hS).obj
        ((Stack.quotientPrestack (baseTrivialActionGroupoid G)).p.obj x) ⟶ G.obj.X) :
    trivialActionComponent G (trivialActionArrow G f a) = a := by
  ext1
  have hr : ((baseTrivialActionGroupoid G).toGroupoidInFunctors.evaluationArrowEquiv
      _ _ ((baseTrivialActionGroupoid G).toGroupoidInFunctors.objects.map (op f) _)
      (trivialActionArrow G f a).down.fiber).1 =
        yonedaEquiv (pullback.lift a.left (toBaseS _) (baseS_ext _ _)) :=
    congrArg Subtype.val (Equiv.apply_symm_apply _ _)
  change yonedaEquiv.symm ((pullback.fst G.obj.X.hom (𝟙_ (Over (baseS 𝒞 S hS))).hom).app _
    (cast rfl ((baseTrivialActionGroupoid G).toGroupoidInFunctors.evaluationArrowEquiv
      _ _ ((baseTrivialActionGroupoid G).toGroupoidInFunctors.objects.map (op f) _)
      (trivialActionArrow G f a).down.fiber).1)) = a.left
  rw [hr]
  change yonedaEquiv.symm ((pullback.fst G.obj.X.hom (𝟙_ (Over (baseS 𝒞 S hS))).hom).app _
    (yonedaEquiv (pullback.lift a.left (toBaseS _) (baseS_ext _ _)))) = a.left
  rw [← yonedaEquiv_comp, Equiv.symm_apply_apply]
  exact pullback.lift_fst _ _ _

/-- An arrow of the presentation of `[S/G]` is determined by its base and its component. -/
lemma trivialActionArrow_ext {x y : (Stack.quotientPrestack (baseTrivialActionGroupoid G)).obj}
    {φ φ' : x ⟶ y}
    (hb : (Stack.quotientPrestack (baseTrivialActionGroupoid G)).p.map φ =
      (Stack.quotientPrestack (baseTrivialActionGroupoid G)).p.map φ')
    (hc : trivialActionComponent G φ = trivialActionComponent G φ') : φ = φ' :=
  ULift.ext (actionPointwiseMorphism_ext (isAlgebraicSpace_baseS 𝒞 S hS) G
    (𝟙_ (Over (baseS 𝒞 S hS))) (isAlgebraicSpace_baseS 𝒞 S hS) φ.down φ'.down hb
    (congrArg Over.Hom.left hc))

/-- The restriction maps of the presheaf of points of `G` are precomposition. -/
lemma GroupAlgebraicSpace.pointsGrpPresheaf_map_apply {T T' : BigFppfOver 𝒞 S hS} (g : T ⟶ T')
    (a : (yonedaOverBaseS 𝒞 S hS).obj T' ⟶ G.obj.X) :
    (GroupAlgebraicSpace.pointsGrpPresheaf G).map g.op a = (yonedaOverBaseS 𝒞 S hS).map g ≫ a :=
  rfl

/-- **The presentation of `[S/G]` is rigidified by the points of `G`.** The element of an arrow
over `f : T ⟶ T'` is the inverse of its `G`-component, a point of `G` over `T`; every point of `G`
over `T` is the element of exactly one arrow over `f` between any two given objects. -/
def trivialActionRigidification :
    (Stack.quotientPrestack (baseTrivialActionGroupoid G)).p.Rigidification
      (GroupAlgebraicSpace.pointsGrpPresheaf G) where
  elt φ := (trivialActionComponent G φ)⁻¹
  elt_comp φ χ := by
    change (trivialActionComponent G (φ ≫ χ))⁻¹ = (trivialActionComponent G φ)⁻¹ *
      ((yonedaOverBaseS 𝒞 S hS).map
          ((Stack.quotientPrestack (baseTrivialActionGroupoid G)).p.map φ) ≫
        (trivialActionComponent G χ)⁻¹)
    rw [trivialActionComponent_comp, mul_inv_rev, GrpObj.comp_inv]
  existsUnique x y f a := by
    let a' : (yonedaOverBaseS 𝒞 S hS).obj
        ((Stack.quotientPrestack (baseTrivialActionGroupoid G)).p.obj x) ⟶ G.obj.X := a
    refine ⟨trivialActionArrow G f a'⁻¹, ⟨rfl, ?_⟩, fun φ ⟨hφ, he⟩ => ?_⟩
    · change (trivialActionComponent G (trivialActionArrow G f a'⁻¹))⁻¹ = a'
      rw [trivialActionComponent_trivialActionArrow, inv_inv]
    · change (trivialActionComponent G φ)⁻¹ = a' at he
      refine trivialActionArrow_ext G hφ ?_
      rw [trivialActionComponent_trivialActionArrow, ← he, inv_inv]

/-- The element of an arrow of the presentation of `[S/G]` is the inverse of its
`G`-component. -/
lemma trivialActionRigidification_elt
    {x y : (Stack.quotientPrestack (baseTrivialActionGroupoid G)).obj}
    (φ : x ⟶ y) : (trivialActionRigidification G).elt φ = (trivialActionComponent G φ)⁻¹ :=
  rfl

/-- The object of the presentation of `[S/G]` over `T` given by the unique point `T ⟶ S`. -/
def trivialActionPoint (T : BigFppfOver 𝒞 S hS) :
    (Stack.quotientPrestack (baseTrivialActionGroupoid G)).p.Fiber T :=
  ⟨ULiftHom.objUp.{u + 1, u + 1}
    { base := T
      fiber := show T ⟶ Over.mk (𝟙 (𝒞.obj hS)) from (Over.mkIdTerminal (X := 𝒞.obj hS)).from T },
    rfl⟩

/-! ### Automorphisms of the trivial object of `[S/G]` -/

section Automorphisms

variable (T : BigFppfOver 𝒞 S hS)

/-- The unique point of `S` over `T`, as a point of the object space of the trivial action
groupoid. -/
abbrev trivialActionObjectPoint :
    (baseTrivialActionGroupoid G).objects.obj.obj (op T) :=
  show T ⟶ Over.mk (𝟙 (𝒞.obj hS)) from (Over.mkIdTerminal (X := 𝒞.obj hS)).from T

/-- **The trivial object of `[S/G]` over `T`**: the image in the quotient stack of the unique
point of `S` over `T`. -/
abbrev trivialStackObject :
    (Stack.quotientStack (baseTrivialActionGroupoid G)).p.Fiber T :=
  (Stack.pointwiseToQuotientStackFiber (baseTrivialActionGroupoid G) T).obj
    (trivialActionObjectPoint G T)

/-- The arrow underlying a section of the slice fibre product given by a morphism into the
fibre product. -/
lemma arrowFiberOverSectionArrow_yonedaEquiv (V : Over T)
    (L : yoneda.obj V.left ⟶ pullback
      (prod.lift (yonedaEquiv.symm (trivialActionObjectPoint G T))
        (yonedaEquiv.symm (trivialActionObjectPoint G T)))
      (prod.lift (baseTrivialActionGroupoid G).target.hom
        (baseTrivialActionGroupoid G).source.hom))
    (hL) :
    yonedaEquiv.symm (Stack.arrowFiberOverSectionArrow (baseTrivialActionGroupoid G) T _ _ V
      ⟨yonedaEquiv L, hL⟩) =
      L ≫ pullback.snd
        (prod.lift (yonedaEquiv.symm (trivialActionObjectPoint G T))
          (yonedaEquiv.symm (trivialActionObjectPoint G T)))
        (prod.lift (baseTrivialActionGroupoid G).target.hom
          (baseTrivialActionGroupoid G).source.hom) := by
  change yonedaEquiv.symm ((pullback.snd
      (prod.lift (yonedaEquiv.symm (trivialActionObjectPoint G T))
        (yonedaEquiv.symm (trivialActionObjectPoint G T)))
      (prod.lift (baseTrivialActionGroupoid G).target.hom
        (baseTrivialActionGroupoid G).source.hom)).app
        (op V.left) (yonedaEquiv L)) = _
  rw [← yonedaEquiv_comp, Equiv.symm_apply_apply]

/-- The sections over `V ⟶ T` of the slice fibre product `R ×_{U × U} T` of the trivial action
groupoid along the trivial point are the points of `G` over `V`. -/
def arrowFiberOverTrivialEquiv (V : Over T) :
    (Stack.arrowFiberOver (baseTrivialActionGroupoid G) T (trivialActionObjectPoint G T)
      (trivialActionObjectPoint G T)).obj (op V) ≃
      ((yonedaOverBaseS 𝒞 S hS).obj V.left ⟶ G.obj.X) where
  toFun s := Over.homMk (yonedaEquiv.symm (Stack.arrowFiberOverSectionArrow
    (baseTrivialActionGroupoid G) T _ _ V s) ≫ pullback.fst G.obj.X.hom
      (𝟙_ (Over (baseS 𝒞 S hS))).hom) (baseS_ext _ _)
  invFun a := ⟨yonedaEquiv (pullback.lift (yoneda.map V.hom)
      (pullback.lift a.left (toBaseS _) (baseS_ext _ _) :
        yoneda.obj V.left ⟶ (baseTrivialActionGroupoid G).arrows.obj)
      (prod.hom_ext (baseS_ext _ _) (baseS_ext _ _))), by
    change yonedaEquiv (pullback.lift _ _ _ ≫ pullback.fst _ _) = yonedaEquiv (yoneda.map V.hom)
    exact congrArg yonedaEquiv (pullback.lift_fst _ _ _)⟩
  left_inv s := by
    apply Stack.arrowFiberOverSectionArrow_injective (baseTrivialActionGroupoid G) T _ _ V
    apply yonedaEquiv.symm.injective
    refine (arrowFiberOverSectionArrow_yonedaEquiv G T V _ _).trans
      ((pullback.lift_snd _ _ _).trans ?_)
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact baseS_ext _ _
  right_inv a := Over.OverMorphism.ext (by
    change yonedaEquiv.symm (Stack.arrowFiberOverSectionArrow (baseTrivialActionGroupoid G) T _ _ V
      ⟨yonedaEquiv _, _⟩) ≫ _ = _
    refine (congrArg (· ≫ pullback.fst G.obj.X.hom (𝟙_ (Over (baseS 𝒞 S hS))).hom)
      ((arrowFiberOverSectionArrow_yonedaEquiv G T V _ _).trans
        (pullback.lift_snd _ _ _))).trans ?_
    exact pullback.lift_fst _ _ _)

/-- **The automorphisms of the trivial object of `[S/G]` are the points of `G`** (Stacks 044V):
for `V ⟶ T`, the isomorphisms between the pullbacks to `V` of the trivial object over `T` are in
bijection with the points of `G` over `V`. The bijection is the canonical identification of
`Isom(x, x)` with the slice fibre product of the arrow space along the trivial point,
`AlgebraicGeometry.Stack.isomPresheafPullbackIso`, followed by the description of that fibre
product for the trivial action. -/
def trivialStackObjectIsomEquiv (V : Over T) :
    ((Stack.quotientStack (baseTrivialActionGroupoid G)).p.isomPresheaf (trivialStackObject G T)
      (trivialStackObject G T)).obj (op V) ≃
      ((yonedaOverBaseS 𝒞 S hS).obj V.left ⟶ G.obj.X) :=
  ((Stack.isomPresheafPullbackIso (baseTrivialActionGroupoid G) T (trivialActionObjectPoint G T)
    (trivialActionObjectPoint G T) (trivialStackObject G T) (trivialStackObject G T) rfl rfl).app
    (op V)).toEquiv.symm.trans (Equiv.ulift.trans (arrowFiberOverTrivialEquiv G T V))

/-- The bijection `trivialStackObjectIsomEquiv` is the canonical one: it sends the isomorphism
induced by an arrow of the evaluated trivial action groupoid to the `G`-component of that
arrow. -/
lemma trivialStackObjectIsomEquiv_pointwiseArrowSection (V : Over T)
    (r : (show (baseTrivialActionGroupoid G).toGroupoidInFunctors.Evaluation (op V.left) from
        (baseTrivialActionGroupoid G).objects.obj.map V.hom.op (trivialActionObjectPoint G T)) ⟶
      (baseTrivialActionGroupoid G).objects.obj.map V.hom.op (trivialActionObjectPoint G T)) :
    (trivialStackObjectIsomEquiv G T V (Stack.pointwiseArrowSection _ T
      (trivialActionObjectPoint G T) (trivialActionObjectPoint G T) (trivialStackObject G T)
      (trivialStackObject G T) rfl rfl V r)).left =
      yonedaEquiv.symm ((baseTrivialActionGroupoid G).toGroupoidInFunctors.evaluationArrowEquiv
        (op V.left) _ _ r).1 ≫ pullback.fst G.obj.X.hom (𝟙_ (Over (baseS 𝒞 S hS))).hom := by
  change yonedaEquiv.symm (Stack.arrowFiberOverSectionArrow (baseTrivialActionGroupoid G) T _ _ V
    ((Stack.isomPresheafPullbackIso (baseTrivialActionGroupoid G) T (trivialActionObjectPoint G T)
      (trivialActionObjectPoint G T) (trivialStackObject G T) (trivialStackObject G T) rfl
      rfl).inv.app (op V) (Stack.pointwiseArrowSection _ T (trivialActionObjectPoint G T)
        (trivialActionObjectPoint G T) (trivialStackObject G T) (trivialStackObject G T) rfl rfl
        V r)).down) ≫ _ = _
  exact congrArg (fun t => yonedaEquiv.symm t ≫ pullback.fst G.obj.X.hom
    (𝟙_ (Over (baseS 𝒞 S hS))).hom) (Stack.isomPresheafPullbackIso_inv_app
      (baseTrivialActionGroupoid G) T (trivialActionObjectPoint G T) (trivialActionObjectPoint G T)
      (trivialStackObject G T) (trivialStackObject G T) rfl rfl V r)

end Automorphisms

end AlgebraicGeometry.Space

end
