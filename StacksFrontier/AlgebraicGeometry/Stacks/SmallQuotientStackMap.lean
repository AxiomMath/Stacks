module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.OpenSubgroupoidQuotientStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FaithfulRepresentableUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackShrinkHoms
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtaleComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleLocalStructureQuasiSplittingChart
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocus

/-!
# The small model of a quotient stack and the 1-morphisms between small models

The quotient stack `[U/R]` of a groupoid in algebraic spaces has its morphisms one universe up
from those of the 2-category of algebraic stacks, so it is not itself an object of
`AlgebraicGeometry.Stack.AlgebraicStacks`. Its small model
`AlgebraicGeometry.Stack.smallQuotientStackCFG` is, once `[U/R]` is algebraic. This file packages
the small model as an algebraic stack, the 1-morphism between small models induced by a morphism
of groupoids, and the transport to that 1-morphism of representability (Stacks 04Y5) and of the
relative properties (Stacks 0457) of the 1-morphism of quotient stacks of Stacks 046Q.

## Main definitions

* `AlgebraicGeometry.Stack.smallAlgebraicQuotientStack`: the small model of an algebraic quotient
  stack, as an algebraic stack.
* `AlgebraicGeometry.Stack.smallQuotientStackMap`: the 1-morphism of algebraic stacks between
  small models induced by a morphism of groupoids in algebraic spaces.

## Main results

* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_quotientStackMap_of_faithful`: a
  faithful 1-morphism of algebraic quotient stacks is representable by algebraic spaces.
* `AlgebraicGeometry.Stack.isRelativelyEtale_smallQuotientStackMap`: the 1-morphism between small
  models is étale in the sense of Stacks 04XB as soon as the 1-morphism of quotient stacks is.
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S} {A : AlgebraicSpaces C S hS}

/-- **The small model of an algebraic quotient stack, as an algebraic stack.** It is equivalent
over the site to `[U/R]` (`AlgebraicGeometry.Stack.smallQuotientStackEquivalence`), and an
algebraic stack because `[U/R]` is (Stacks 03YQ). -/
noncomputable abbrev smallAlgebraicQuotientStack (G : GroupoidInAlgebraicSpaces C S hS A)
    (hG : IsAlgebraicStack.{u, w} C S hS (quotientStack G)) : AlgebraicStacks.{u, w} C S hS :=
  ⟨smallQuotientStackCFG G,
    isAlgebraicStack_of_equivalence'.{u, w} C S hS (smallQuotientStackEquivalence G).symm hG⟩

/-- The inverse of the comparison between `[U/R]` and its small model is an equivalence of
categories. -/
instance isEquivalence_smallQuotientStackEquivalence_inverse
    (G : GroupoidInAlgebraicSpaces C S hS A) :
    (smallQuotientStackEquivalence G).inverse.toFunctor.IsEquivalence :=
  (smallQuotientStackEquivalence G).equiv.isEquivalence_inverse

variable {G H : GroupoidInAlgebraicSpaces C S hS A} (φ : GroupoidInAlgebraicSpaces.Hom G H)
  (hG : IsAlgebraicStack.{u, w} C S hS (quotientStack G))
  (hH : IsAlgebraicStack.{u, w} C S hS (quotientStack H))

/-- **The 1-morphism between small models of quotient stacks induced by a morphism of
groupoids**: the 1-morphism `[φ]` of Stacks 046Q conjugated by the comparisons with the small
models. -/
noncomputable def smallQuotientStackMap :
    smallAlgebraicQuotientStack.{u, w} G hG ⟶ smallAlgebraicQuotientStack.{u, w} H hH :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    (BasedFunctor.comp (smallQuotientStackEquivalence G).functor
      (BasedFunctor.comp (quotientStackMap φ) (smallQuotientStackEquivalence H).inverse)))

/-- The underlying based functor of the 1-morphism between small models. -/
theorem smallQuotientStackMap_hom_hom :
    (smallQuotientStackMap.{u, w} φ hG hH).hom.hom =
      BasedFunctor.comp (smallQuotientStackEquivalence G).functor
        (BasedFunctor.comp (quotientStackMap φ) (smallQuotientStackEquivalence H).inverse) :=
  rfl

/-- **The comparison square** between the 1-morphism of quotient stacks and the 1-morphism between
their small models: the counit of the comparison of `[U'/R']` with its small model. -/
noncomputable def smallQuotientStackMapSquare :
    BasedFunctor.comp (smallQuotientStackEquivalence G).functor (quotientStackMap φ) ≅
      BasedFunctor.comp (smallQuotientStackMap.{u, w} φ hG hH).hom.hom
        (smallQuotientStackEquivalence H).functor where
  hom := BasedCategory.whiskerLeft
    (BasedFunctor.comp (smallQuotientStackEquivalence G).functor (quotientStackMap φ))
    (smallQuotientStackEquivalence H).counitIso.inv
  inv := BasedCategory.whiskerLeft
    (BasedFunctor.comp (smallQuotientStackEquivalence G).functor (quotientStackMap φ))
    (smallQuotientStackEquivalence H).counitIso.hom
  hom_inv_id := by
    ext a
    exact congrArg (fun k => k.toNatTrans.app
      ((BasedFunctor.comp (smallQuotientStackEquivalence G).functor (quotientStackMap φ)).obj a))
      (smallQuotientStackEquivalence H).counitIso.inv_hom_id
  inv_hom_id := by
    ext a
    exact congrArg (fun k => k.toNatTrans.app
      ((BasedFunctor.comp (smallQuotientStackEquivalence G).functor (quotientStackMap φ)).obj a))
      (smallQuotientStackEquivalence H).counitIso.hom_inv_id

/-- The 1-morphism between small models is faithful when the 1-morphism of quotient stacks is. -/
theorem faithful_smallQuotientStackMap (hfaith : (quotientStackMap φ).toFunctor.Faithful) :
    (CatFiberedInGroupoids.homFunctor (smallQuotientStackMap.{u, w} φ hG hH).hom).Faithful := by
  show ((smallQuotientStackEquivalence G).functor.toFunctor ⋙
    (quotientStackMap φ).toFunctor ⋙ (smallQuotientStackEquivalence H).inverse.toFunctor).Faithful
  infer_instance

include hG hH in
/-- **Stacks 04Y5 for a 1-morphism of algebraic quotient stacks.** A 1-morphism `[φ]` of
quotient stacks whose underlying functor is faithful is representable by algebraic spaces, as
soon as both quotient stacks are algebraic: its conjugate between the small models is a faithful
1-morphism of algebraic stacks, hence representable by algebraic spaces, and representability
transports along the comparisons (Stacks 0457). -/
theorem isRepresentableByAlgebraicSpaces_quotientStackMap_of_faithful
    (hfaith : (quotientStackMap φ).toFunctor.Faithful) :
    IsRepresentableByAlgebraicSpaces C S hS (quotientStackMap φ) := by
  have hsmall := AlgebraicStacks.isRepresentableByAlgebraicSpaces_of_faithful C S hS
    (smallQuotientStackMap.{u, w} φ hG hH) (faithful_smallQuotientStackMap φ hG hH hfaith)
  exact (isRepresentableByAlgebraicSpaces_iff_of_equivalences C S hS
    (smallQuotientStackMap.{u, w} φ hG hH).hom.hom (quotientStackMapCFGHom φ).hom
    (smallQuotientStackEquivalence G).functor (smallQuotientStackEquivalence H).functor
    (smallQuotientStackMapSquare φ hG hH)).2 hsmall

/-- **The 1-morphism between small models is étale in the sense of Stacks 04XB** when the
1-morphism of quotient stacks has the relative property of being étale (Stacks 0457). -/
theorem isRelativelyEtale_smallQuotientStackMap
    (hrep : IsRepresentableByAlgebraicSpaces C S hS (quotientStackMap φ))
    (het : HasRelativeProperty.{u, u + 1, u + 1, u} C S hS (Space.etaleMorphisms C S hS)
      (quotientStackMapCFGHom φ) hrep) :
    IsRelativelyEtale C S hS (smallQuotientStackMap.{u, w} φ hG hH).hom := by
  have hsmall : IsRepresentableByAlgebraicSpaces C S hS
      (smallQuotientStackMap.{u, w} φ hG hH).hom.hom :=
    (isRepresentableByAlgebraicSpaces_iff_of_equivalences C S hS
      (smallQuotientStackMap.{u, w} φ hG hH).hom.hom (quotientStackMapCFGHom φ).hom
      (smallQuotientStackEquivalence G).functor (smallQuotientStackEquivalence H).functor
      (smallQuotientStackMapSquare φ hG hH)).1 hrep
  exact ⟨hsmall, hasRelativeProperty_of_equivalences.{u, u, u + 1, u + 1, u + 1, u} C S hS
    (Space.etaleMorphisms C S hS)
    (smallQuotientStackMap.{u, w} φ hG hH).hom (quotientStackMapCFGHom φ)
    (smallQuotientStackEquivalence G).functor (smallQuotientStackEquivalence H).functor
    (smallQuotientStackMapSquare φ hG hH) hrep hsmall het⟩

/-! ### Points of the small models -/

/-- The point of the small model of a quotient stack attached to a point of the object space: the
image of the canonical point of the fibred category of the object space under the projection of
Stacks 044R. -/
noncomputable def smallQuotientStackPoint (G : GroupoidInAlgebraicSpaces C S hS A)
    (hG : IsAlgebraicStack.{u, w} C S hS (quotientStack G))
    (z : Space.points C S hS G.objects.obj) :
    AlgebraicStacks.points C S hS (smallAlgebraicQuotientStack.{u, w} G hG) :=
  pointsMap C S hS (fibredCategory C S hS G.objects.obj).val
    (fibredCategory C S hS G.objects.obj).property (smallQuotientStackCFG G).property
    (smallQuotientStackProjection G).hom
    (spacePointMap C S hS G.objects.obj (fibredCategory C S hS G.objects.obj) (BasedFunctor.id _) z)

/-- On points, the projection to the small model and the projection to the quotient stack agree,
inside any further 1-morphism out of the quotient stack. -/
theorem pointsMap_smallQuotientStackProjection_comp (G : GroupoidInAlgebraicSpaces C S hS A)
    (𝒵 : BasedCategory.{u, u + 1} (BigFppfOver C S hS)) (h𝒵 : 𝒵.p.IsFiberedInGroupoids)
    (X : quotientStack G ⥤ᵇ 𝒵) :
    pointsMap C S hS (fibredCategory C S hS G.objects.obj).val
        (fibredCategory C S hS G.objects.obj).property h𝒵
        (BasedFunctor.comp (smallQuotientStackProjection G).hom
          (BasedFunctor.comp (smallQuotientStackEquivalence G).functor X)) =
      pointsMap C S hS (fibredCategory C S hS G.objects.obj).val
        (fibredCategory C S hS G.objects.obj).property h𝒵
        (BasedFunctor.comp (quotientStackProjection G) X) :=
  pointsMap_congr_of_obj_eq _ _ _ _ fun _ => rfl

/-- **The 1-morphism between small models acts on the points of the object spaces as the map of
object spaces.** -/
theorem pointsMap_smallQuotientStackMap_point (z : Space.points C S hS G.objects.obj) :
    AlgebraicStacks.pointsMap C S hS (smallQuotientStackMap.{u, w} φ hG hH)
        (smallQuotientStackPoint G hG z) =
      smallQuotientStackPoint H hH
        (Space.pointsMap C S hS _ φ.toGroupoidHom.mapObjects z) := by
  have h1 := pointsMap_comp C S hS _ (fibredCategory C S hS G.objects.obj).property
    (smallQuotientStackCFG G).property (smallQuotientStackCFG H).property
    (smallQuotientStackProjection G).hom (smallQuotientStackMap.{u, w} φ hG hH).hom.hom
    (spacePointMap C S hS G.objects.obj (fibredCategory C S hS G.objects.obj) (BasedFunctor.id _) z)
  have h3 := pointsMap_smallQuotientStackProjection_comp G
    (smallQuotientStackCFG H).val (smallQuotientStackCFG H).property
    (BasedFunctor.comp (quotientStackMap φ) (smallQuotientStackEquivalence H).inverse)
  have h4 := pointsMap_quotientStackProjection_comp_quotientStackMap_point φ
    (smallQuotientStackCFG H).val (smallQuotientStackCFG H).property
    (smallQuotientStackEquivalence H).inverse z
  have h5 : pointsMap C S hS (fibredCategory C S hS H.objects.obj).val
        (fibredCategory C S hS H.objects.obj).property (smallQuotientStackCFG H).property
        (BasedFunctor.comp (quotientStackProjection H) (smallQuotientStackEquivalence H).inverse) =
      pointsMap C S hS (fibredCategory C S hS H.objects.obj).val
        (fibredCategory C S hS H.objects.obj).property (smallQuotientStackCFG H).property
        (smallQuotientStackProjection H).hom :=
    pointsMap_congr_of_obj_eq _ _ _ _ fun _ => rfl
  show pointsMap C S hS _ _ _ (smallQuotientStackMap.{u, w} φ hG hH).hom.hom
      (pointsMap C S hS _ _ _ (smallQuotientStackProjection G).hom _) = pointsMap C S hS _ _ _ _ _
  rw [h1]
  refine (congrFun h3 _).trans ?_
  rw [h4, h5]

/-- **The 1-morphism out of the small model induced by a 1-morphism out of the quotient
stack.** -/
noncomputable def smallQuotientStackLift (G : GroupoidInAlgebraicSpaces C S hS A)
    (hG : IsAlgebraicStack.{u, w} C S hS (quotientStack G)) {𝒳 : AlgebraicStacks.{u, w} C S hS}
    (X : quotientStack G ⥤ᵇ 𝒳.val.val) : smallAlgebraicQuotientStack.{u, w} G hG ⟶ 𝒳 :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    (BasedFunctor.comp (smallQuotientStackEquivalence G).functor X))

/-- The underlying functor of the lift is the comparison with the quotient stack followed by the
given functor. -/
theorem homFunctor_smallQuotientStackLift (G : GroupoidInAlgebraicSpaces C S hS A)
    (hG : IsAlgebraicStack.{u, w} C S hS (quotientStack G)) {𝒳 : AlgebraicStacks.{u, w} C S hS}
    (X : quotientStack G ⥤ᵇ 𝒳.val.val) :
    CatFiberedInGroupoids.homFunctor (smallQuotientStackLift.{u, w} G hG X).hom =
      (smallQuotientStackEquivalence G).functor.toFunctor ⋙ X.toFunctor := rfl

/-- The lift of an equivalence is an equivalence. -/
theorem isEquivalence_smallQuotientStackLift (G : GroupoidInAlgebraicSpaces C S hS A)
    (hG : IsAlgebraicStack.{u, w} C S hS (quotientStack G)) {𝒳 : AlgebraicStacks.{u, w} C S hS}
    (X : quotientStack G ⥤ᵇ 𝒳.val.val) [X.toFunctor.IsEquivalence] :
    (CatFiberedInGroupoids.homFunctor
      (smallQuotientStackLift.{u, w} G hG X).hom).IsEquivalence := by
  rw [homFunctor_smallQuotientStackLift]
  infer_instance

/-- The points of the small model attached to points of the object space are sent by the lift to
the images of the canonical points under the projection followed by the given functor. -/
theorem pointsMap_smallQuotientStackLift_point (G : GroupoidInAlgebraicSpaces C S hS A)
    (hG : IsAlgebraicStack.{u, w} C S hS (quotientStack G)) {𝒳 : AlgebraicStacks.{u, w} C S hS}
    (X : quotientStack G ⥤ᵇ 𝒳.val.val) (z : Space.points C S hS G.objects.obj) :
    AlgebraicStacks.pointsMap C S hS (smallQuotientStackLift.{u, w} G hG X)
        (smallQuotientStackPoint G hG z) =
      pointsMap C S hS (fibredCategory C S hS G.objects.obj).val
        (fibredCategory C S hS G.objects.obj).property 𝒳.val.property
        (BasedFunctor.comp (quotientStackProjection G) X)
        (spacePointMap C S hS G.objects.obj (fibredCategory C S hS G.objects.obj)
          (BasedFunctor.id _) z) := by
  show pointsMap C S hS _ _ _ (smallQuotientStackLift.{u, w} G hG X).hom.hom
      (pointsMap C S hS _ _ _ (smallQuotientStackProjection G).hom _) = _
  rw [pointsMap_comp]
  exact congrFun (pointsMap_smallQuotientStackProjection_comp G 𝒳.val.val 𝒳.val.property X) _

/-- The underlying functor of the 1-morphism between small models. -/
theorem homFunctor_smallQuotientStackMap :
    CatFiberedInGroupoids.homFunctor (smallQuotientStackMap.{u, w} φ hG hH).hom =
      (smallQuotientStackEquivalence G).functor.toFunctor ⋙ (quotientStackMap φ).toFunctor ⋙
        (smallQuotientStackEquivalence H).inverse.toFunctor := rfl

/-- The 1-morphism between small models is fully faithful when the 1-morphism of quotient stacks
is. -/
theorem nonempty_fullyFaithful_smallQuotientStackMap
    (hφ : Nonempty (quotientStackMap φ).toFunctor.FullyFaithful) :
    Nonempty (CatFiberedInGroupoids.homFunctor
      (smallQuotientStackMap.{u, w} φ hG hH).hom).FullyFaithful := by
  obtain ⟨hφ⟩ := hφ
  rw [homFunctor_smallQuotientStackMap]
  exact ⟨(Functor.FullyFaithful.ofFullyFaithful
    (smallQuotientStackEquivalence G).functor.toFunctor).comp (hφ.comp
      (Functor.FullyFaithful.ofFullyFaithful (smallQuotientStackEquivalence H).inverse.toFunctor))⟩

end AlgebraicGeometry.Stack

end
