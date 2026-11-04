module

public import StacksFrontier.CategoryTheory.Sites.Stack.SlicePointIsomPresheaf

/-!
# `Isom(x, y)` is invariant under isomorphism of `x` and of `y` in the fibre

Let `p : 𝒳 ⥤ 𝒮` be a fibred category, `U` an object of `𝒮` and `x`, `x'` objects of the fibre of
`p` over `U`. The presheaf `Isom(x, y)` of Stacks 02ZB is built from the *chosen* pullbacks of
`x` and of `y`, so an isomorphism `x ≅ x'` of the fibre does not make the two presheaves equal;
this file produces the comparison isomorphism between them.

Everything rests on one construction: the chosen pullback of `x` along `g` and the chosen
pullback of `x'` along `g` are the domains of two cartesian lifts of `g` with the same target —
the second of the two chosen lifts, and the first followed by `x ≅ x'` — so they are canonically
isomorphic, by `CategoryTheory.Functor.IsCartesian.domainUniqueUpToIso`. The comparison is
vertical, and it is natural in `g` by the uniqueness half of the same universal property, so the
chosen-pullback 1-morphisms `CategoryTheory.Functor.pullbackSliceFunctor` of `x` and of `x'` are
naturally isomorphic through vertical morphisms.

The consequence drawn here is stated in the form the criteria of Stacks 045G consume: the
isomorphism presheaf read on the slice `𝒮/U.left` of a slice `𝒮 = 𝒟/X`, which is where
`CategoryTheory.Functor.vertHomPresheafIsoIsomPresheafOfPoint` leaves the value of an arbitrary
scheme-valued point at the terminal object. That value is only isomorphic to a prescribed object
of the fibre, not equal to it, and this is what bridges the two.

## Main definitions

* `CategoryTheory.Functor.pullbackFiberIsoOfIso`: the comparison between the chosen pullbacks of
  two isomorphic objects of a fibre.
* `CategoryTheory.Functor.pullbackSliceFunctorNatIso`: the chosen-pullback 1-morphisms of two
  isomorphic objects of a fibre are naturally isomorphic.
* `CategoryTheory.Functor.backwardIsomPresheafIsoOfIso`: the comparison of the two isomorphism
  presheaves, read on the slice at `U.left`.

## Main results

* `CategoryTheory.Functor.pullbackFiberIsoOfIso_fac`: the defining factorisation.
* `CategoryTheory.Functor.isHomLift_pullbackFiberIsoOfIso` and
  `CategoryTheory.Functor.isHomLift_pullbackFiberIsoOfIso_inv`: the comparison is vertical, in
  both directions, which is what
  `CategoryTheory.TwoFibreProductOver.DiagonalFibre.VertHom.presheafIsoOfIso` asks for.

## References

* [Stacks Project, Tag 02ZB](https://stacks.math.columbia.edu/tag/02ZB)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
-/

@[expose] public section

open CategoryTheory Opposite

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Functor

-- As in `StacksFrontier.CategoryTheory.Sites.Stack.IsomPresheaf`: `Fiber` and its inclusion must
-- unfold for the endpoints of the composites below to be seen as equal at `implicit`
-- transparency.
attribute [local implicit_reducible] Fiber Fiber.fiberInclusion

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
variable (p : 𝒳 ⥤ 𝒮) [p.IsFibered] {U : 𝒮}

section FiberIso

variable {x x' : p.Fiber U}

/-- The chosen cartesian lift of `g` at `x`, followed by an isomorphism `x ≅ x'` of the fibre,
is a lift of `g` with target `x'`. -/
lemma isHomLift_pullbackMap_comp_fiberInclusion (α : x ⟶ x') (g : Over U) :
    p.IsHomLift g.hom
      (IsPreFibered.pullbackMap x.2 g.hom ≫ Fiber.fiberInclusion.map α) := by
  infer_instance

/-- The chosen cartesian lift at an object of a fibre is strongly cartesian, in a fibred
category in groupoids. -/
private lemma isStronglyCartesian_pullbackMap (hp : p.IsFiberedInGroupoids) (y : p.Fiber U)
    (g : Over U) : p.IsStronglyCartesian g.hom (IsPreFibered.pullbackMap y.2 g.hom) :=
  hp.isStronglyCartesian_homLift _ _

/-- In a fibred category in groupoids, the chosen cartesian lift at `x` followed by a morphism
`x ⟶ x'` of the fibre is strongly cartesian. -/
private lemma isStronglyCartesian_pullbackMap_comp_fiberInclusion (hp : p.IsFiberedInGroupoids)
    (α : x ⟶ x') (g : Over U) :
    p.IsStronglyCartesian g.hom
      (IsPreFibered.pullbackMap x.2 g.hom ≫ Fiber.fiberInclusion.map α) :=
  have := isHomLift_pullbackMap_comp_fiberInclusion p α g
  hp.isStronglyCartesian_homLift _ _

/-- **The chosen pullbacks of two isomorphic objects of a fibre are isomorphic.** Both are
domains of a cartesian lift of `g` with target `x'`: the chosen lift at `x'`, and the chosen lift
at `x` followed by the given isomorphism. -/
noncomputable def pullbackFiberIsoOfIso (hp : p.IsFiberedInGroupoids) (α : x ≅ x') (g : Over U) :
    (pullbackFiber p x g.hom).1 ≅ (pullbackFiber p x' g.hom).1 :=
  have := isHomLift_pullbackMap_comp_fiberInclusion p α.hom g
  have _h1 : p.IsStronglyCartesian g.hom (IsPreFibered.pullbackMap x'.2 g.hom) :=
    hp.isStronglyCartesian_homLift _ _
  have _h2 : p.IsStronglyCartesian g.hom
      (IsPreFibered.pullbackMap x.2 g.hom ≫ Fiber.fiberInclusion.map α.hom) :=
    hp.isStronglyCartesian_homLift _ _
  IsCartesian.domainUniqueUpToIso p g.hom (IsPreFibered.pullbackMap x'.2 g.hom)
    (IsPreFibered.pullbackMap x.2 g.hom ≫ Fiber.fiberInclusion.map α.hom)

/-- The defining factorisation of the comparison: following it with the chosen lift at `x'` is
the chosen lift at `x` followed by the given isomorphism. -/
lemma pullbackFiberIsoOfIso_fac (hp : p.IsFiberedInGroupoids) (α : x ≅ x') (g : Over U) :
    (pullbackFiberIsoOfIso p hp α g).hom ≫ IsPreFibered.pullbackMap x'.2 g.hom =
      IsPreFibered.pullbackMap x.2 g.hom ≫ Fiber.fiberInclusion.map α.hom :=
  have _h1 := isStronglyCartesian_pullbackMap p hp x' g
  have _h2 := isStronglyCartesian_pullbackMap_comp_fiberInclusion p hp α.hom g
  IsCartesian.fac p g.hom (IsPreFibered.pullbackMap x'.2 g.hom)
    (IsPreFibered.pullbackMap x.2 g.hom ≫ Fiber.fiberInclusion.map α.hom)

/-- The comparison is vertical. -/
lemma isHomLift_pullbackFiberIsoOfIso (hp : p.IsFiberedInGroupoids) (α : x ≅ x') (g : Over U) :
    p.IsHomLift (𝟙 g.left) (pullbackFiberIsoOfIso p hp α g).hom :=
  have _h1 := isStronglyCartesian_pullbackMap p hp x' g
  have _h2 := isStronglyCartesian_pullbackMap_comp_fiberInclusion p hp α.hom g
  IsCartesian.domainUniqueUpToIso_inv_isHomLift p g.hom
    (IsPreFibered.pullbackMap x'.2 g.hom)
    (IsPreFibered.pullbackMap x.2 g.hom ≫ Fiber.fiberInclusion.map α.hom)

/-- The inverse of the comparison is vertical. -/
lemma isHomLift_pullbackFiberIsoOfIso_inv (hp : p.IsFiberedInGroupoids) (α : x ≅ x')
    (g : Over U) :
    p.IsHomLift (𝟙 g.left) (pullbackFiberIsoOfIso p hp α g).inv :=
  have := isHomLift_pullbackFiberIsoOfIso p hp α g
  IsHomLift.lift_id_inv p g.left (pullbackFiberIsoOfIso p hp α g)

/-- **The chosen-pullback 1-morphisms of two isomorphic objects of a fibre are naturally
isomorphic.** -/
noncomputable def pullbackSliceFunctorNatIso (hp : p.IsFiberedInGroupoids) (α : x ≅ x') :
    pullbackSliceFunctor p x ≅ pullbackSliceFunctor p x' :=
  NatIso.ofComponents (pullbackFiberIsoOfIso p hp α) (by
    intro g₁ g₂ h
    change pullbackFiberMap p x h ≫ (pullbackFiberIsoOfIso p hp α g₂).hom =
      (pullbackFiberIsoOfIso p hp α g₁).hom ≫ pullbackFiberMap p x' h
    have := isHomLift_pullbackMap_comp_fiberInclusion p α.hom g₂
    have _h1 : p.IsStronglyCartesian g₂.hom (IsPreFibered.pullbackMap x'.2 g₂.hom) :=
      hp.isStronglyCartesian_homLift _ _
    have hl : p.IsHomLift h.left
        (pullbackFiberMap p x h ≫ (pullbackFiberIsoOfIso p hp α g₂).hom) := by
      have := isHomLift_pullbackFiberIsoOfIso p hp α g₂
      have h0 : p.IsHomLift (h.left ≫ 𝟙 g₂.left)
          (pullbackFiberMap p x h ≫ (pullbackFiberIsoOfIso p hp α g₂).hom) := inferInstance
      rwa [Category.comp_id] at h0
    have hr : p.IsHomLift h.left
        ((pullbackFiberIsoOfIso p hp α g₁).hom ≫ pullbackFiberMap p x' h) := by
      have := isHomLift_pullbackFiberIsoOfIso p hp α g₁
      have h0 : p.IsHomLift (𝟙 g₁.left ≫ h.left)
          ((pullbackFiberIsoOfIso p hp α g₁).hom ≫ pullbackFiberMap p x' h) := inferInstance
      rwa [Category.id_comp] at h0
    refine IsStronglyCartesian.ext p g₂.hom (IsPreFibered.pullbackMap x'.2 g₂.hom) h.left ?_
    rw [Category.assoc, pullbackFiberIsoOfIso_fac, ← Category.assoc, pullbackFiberMap_fac,
      Category.assoc, pullbackFiberMap_fac]
    exact (pullbackFiberIsoOfIso_fac p hp α g₁).symm)

/-- The components of the natural isomorphism are vertical. -/
lemma isHomLift_pullbackSliceFunctorNatIso_hom_app (hp : p.IsFiberedInGroupoids) (α : x ≅ x')
    (g : Over U) :
    p.IsHomLift (𝟙 g.left) ((pullbackSliceFunctorNatIso p hp α).hom.app g) :=
  isHomLift_pullbackFiberIsoOfIso p hp α g

/-- The components of the inverse of the natural isomorphism are vertical. -/
lemma isHomLift_pullbackSliceFunctorNatIso_inv_app (hp : p.IsFiberedInGroupoids) (α : x ≅ x')
    (g : Over U) :
    p.IsHomLift (𝟙 g.left) ((pullbackSliceFunctorNatIso p hp α).inv.app g) :=
  isHomLift_pullbackFiberIsoOfIso_inv p hp α g

end FiberIso

section Backward

open CategoryTheory.TwoFibreProductOver.DiagonalFibre

variable {D : Type u₁} [Category.{v₁} D] {X : D} {Z : Type u₂} [Category.{v₂} Z]

/-- **The isomorphism presheaf is invariant under isomorphism of the two objects of the fibre.**
Read on the slice `𝒟/U.left`, the presheaf `Isom(x, y)` of two objects of the fibre of `p` over
`U` is isomorphic to `Isom(x', y')` as soon as `x ≅ x'` and `y ≅ y'` in that fibre. -/
noncomputable def backwardIsomPresheafIsoOfIso (p : Z ⥤ Over X) [p.IsFibered]
    (hp : p.IsFiberedInGroupoids) (U : Over X) {x x' y y' : p.Fiber U} (α : x ≅ x')
    (β : y ≅ y') :
    (Over.iteratedSliceBackward U).op ⋙ p.isomPresheaf x y ≅
      (Over.iteratedSliceBackward U).op ⋙ p.isomPresheaf x' y' :=
  (vertHomPresheafIsoIsomPresheaf p U x y hp).symm.trans
    ((VertHom.presheafIsoOfIso hp
        (backward_pullbackSliceFunctor_comp p U x)
        (backward_pullbackSliceFunctor_comp p U x')
        (backward_pullbackSliceFunctor_comp p U y)
        (backward_pullbackSliceFunctor_comp p U y')
        (Functor.isoWhiskerLeft (Over.iteratedSliceBackward U)
          (pullbackSliceFunctorNatIso p hp α)).symm
        (fun a => isHomLift_pullbackFiberIsoOfIso_inv p hp α
          ((Over.iteratedSliceBackward U).obj a))
        (fun a => isHomLift_pullbackFiberIsoOfIso p hp α
          ((Over.iteratedSliceBackward U).obj a))
        (Functor.isoWhiskerLeft (Over.iteratedSliceBackward U)
          (pullbackSliceFunctorNatIso p hp β))
        (fun a => isHomLift_pullbackFiberIsoOfIso p hp β
          ((Over.iteratedSliceBackward U).obj a))
        (fun a => isHomLift_pullbackFiberIsoOfIso_inv p hp β
          ((Over.iteratedSliceBackward U).obj a))).trans
      (vertHomPresheafIsoIsomPresheaf p U x' y' hp))

end Backward

end CategoryTheory.Functor

end
