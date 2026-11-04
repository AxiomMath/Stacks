module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square
public import StacksFrontier.AlgebraicGeometry.Groupoids.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Global quotients of finite locally free equivalence relations

A *finite flat quotient* of a groupoid scheme over a base scheme `S` is a scheme over `S`
together with a surjective finite locally free morphism from the object scheme whose kernel
pair is the given pair of source and target maps and which represents the fppf quotient sheaf
of the associated pre-relation.

## Main definitions

* `Stacks.Groupoids.FiniteFlatQuotient` packages a quotient scheme, its quotient map, and
  their universal properties.

## Main results

* `Stacks.Groupoids.FiniteFlatQuotient.target_comp_quotientMap` says that the quotient map
  identifies the target and the source of an arrow.
* `Stacks.Groupoids.FiniteFlatQuotient.isPullback_left` transports the kernel-pair square to
  underlying schemes.
* `Stacks.Groupoids.FiniteFlatQuotient.exists_iso` says that a finite flat quotient is unique:
  two of them are isomorphic over `S` by an isomorphism carrying the one quotient map to the
  other.

## References

* [Stacks Project, Tag 07S6](https://stacks.math.columbia.edu/tag/07S6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Groupoids

/-- A scheme quotient of a groupoid scheme over `S`, with its surjective finite locally free
quotient map, kernel-pair square, and fppf sheaf universal property. -/
structure FiniteFlatQuotient {S : Scheme.{u}} (G : GroupoidScheme S) where
  /-- The quotient scheme over `S`. -/
  space : Over S
  /-- The quotient map. -/
  quotientMap : G.objects ⟶ space
  /-- The quotient map is finite locally free. -/
  finiteLocallyFree : Stacks.Morphisms.IsFiniteLocallyFree quotientMap.left
  /-- The quotient projection is surjective. -/
  surjective : Surjective quotientMap.left
  /-- The given arrows form the kernel pair of the quotient map. -/
  kernelPair : IsPullback G.target G.source quotientMap quotientMap
  /-- On each sufficiently large big fppf site, the quotient sheaf is naturally represented by
  `space`, compatibly with `quotientMap`. -/
  represents : ∀ (B : BigFppfSite.{u}) (hS : B.Contains S)
      (_hU : B.Contains G.objects.left) (_hR : B.Contains G.arrows.left)
      (_hM : B.Contains space.left),
    let F : BigFppfOver B S hS ⥤ Over S := Over.post B.inclusion
    let J := BigFppfOver.topology B S hS
    let j : PreRelation G.arrows G.objects :=
      prod.lift G.target G.source
    let P := quotientPresheaf F j ⋙ uliftFunctor.{u + 1}
    ∃ e : sheafify J P ≅ points F space ⋙ uliftFunctor.{u + 1},
      Functor.whiskerRight (toQuotientPresheaf F j) uliftFunctor ≫
        toSheafify J P ≫ e.hom =
          Functor.whiskerRight (F.op.whiskerLeft (yoneda.map quotientMap)) uliftFunctor

namespace FiniteFlatQuotient

variable {S : Scheme.{u}} {G : GroupoidScheme S}

/-- The quotient map of a finite flat quotient identifies the target and the source of an
arrow. -/
theorem target_comp_quotientMap (Q : FiniteFlatQuotient G) :
    G.target ≫ Q.quotientMap = G.source ≫ Q.quotientMap :=
  Q.kernelPair.w

/-- The kernel-pair square of a finite flat quotient is Cartesian already as a square of
schemes, not only of schemes over `S`. -/
theorem isPullback_left (Q : FiniteFlatQuotient G) :
    IsPullback G.target.left G.source.left Q.quotientMap.left Q.quotientMap.left :=
  Q.kernelPair.map (Over.forget S)

/-- The quotient map of a finite flat quotient is an affine morphism. -/
theorem isAffineHom_quotientMap (Q : FiniteFlatQuotient G) :
    IsAffineHom Q.quotientMap.left :=
  Q.finiteLocallyFree.toIsAffineHom

section Uniqueness

/-- An object of the big fppf site of `S` whose underlying scheme over `S` is a prescribed
one. -/
private abbrev siteOver (B : BigFppfSite.{u}) (hS : B.Contains S) (M : Over S)
    (hM : B.Contains M.left) : BigFppfOver B S hS :=
  Over.mk (X := B.obj hS) (Y := (⟨M.left, hM⟩ : B.Schemes)) (ObjectProperty.homMk M.hom)

/-- Naturality of a morphism between lifted restricted functors of points, read on elements:
the component at `X` of a morphism factoring through `F.map h` is the factored image of the
component at `Y`. -/
private theorem app_up_comp {C : Type*} [Category C] (F : C ⥤ Over S) {A A' : Over S}
    (α : points F A ⋙ uliftFunctor.{u + 1} ⟶ points F A' ⋙ uliftFunctor.{u + 1})
    {X Y : C} (h : X ⟶ Y) (v : F.obj Y ⟶ A) :
    α.app (op X) (ULift.up (F.map h ≫ v)) =
      ULift.up (F.map h ≫ (α.app (op Y) (ULift.up v)).down) :=
  types_congr_hom (α.naturality h.op) (ULift.up v)

/-- A morphism between the lifted restricted functors of points of two objects of the big fppf
site is given on every object of the site by composition with a single morphism of schemes
over `S`, namely the image of the identity. -/
private theorem comp_eq_of_app (B : BigFppfSite.{u}) (hS : B.Contains S) {M M' : Over S}
    (hM : B.Contains M.left)
    (α : points (Over.post (X := B.obj hS) B.inclusion) M ⋙ uliftFunctor.{u + 1} ⟶
      points (Over.post (X := B.obj hS) B.inclusion) M' ⋙ uliftFunctor.{u + 1})
    {N : Over S} (hN : B.Contains N.left) (k : N ⟶ M) :
    α.app (op (siteOver B hS N hN)) (ULift.up k) =
      ULift.up (k ≫ (α.app (op (siteOver B hS M hM)) (ULift.up (𝟙 M))).down) := by
  obtain ⟨h, rfl⟩ := (Over.post (X := B.obj hS) B.inclusion).map_surjective
    (X := siteOver B hS N hN) (Y := siteOver B hS M hM) k
  have h0 := app_up_comp (A := (Over.post (X := B.obj hS) B.inclusion).obj
      (siteOver B hS M hM)) (Over.post (X := B.obj hS) B.inclusion) α h
    (𝟙 ((Over.post (X := B.obj hS) B.inclusion).obj (siteOver B hS M hM)))
  rw [Category.comp_id] at h0
  exact h0

/-- If two morphisms between lifted restricted functors of points compose to the identity, the
morphisms of schemes they send the identity to compose to the identity. -/
private theorem comp_eq_id_of_comp_eq_id (B : BigFppfSite.{u}) (hS : B.Contains S)
    {M M' : Over S} (hM : B.Contains M.left)
    (f : points (Over.post (X := B.obj hS) B.inclusion) M ⋙ uliftFunctor.{u + 1} ⟶
      points (Over.post (X := B.obj hS) B.inclusion) M' ⋙ uliftFunctor.{u + 1})
    (g : points (Over.post (X := B.obj hS) B.inclusion) M' ⋙ uliftFunctor.{u + 1} ⟶
      points (Over.post (X := B.obj hS) B.inclusion) M ⋙ uliftFunctor.{u + 1})
    (hM' : B.Contains M'.left) (h : f ≫ g = 𝟙 _) :
    (f.app (op (siteOver B hS M hM)) (ULift.up (𝟙 M))).down ≫
      (g.app (op (siteOver B hS M' hM')) (ULift.up (𝟙 M'))).down = 𝟙 M := by
  have h1 := comp_eq_of_app B hS hM' g hM
    (f.app (op (siteOver B hS M hM)) (ULift.up (𝟙 M))).down
  have h2 := types_congr_hom (NatTrans.congr_app h (op (siteOver B hS M hM)))
    (ULift.up (𝟙 M))
  exact ULift.up_injective (h1.symm.trans h2)

/-- Two objects of the big fppf site of `S` with isomorphic lifted restricted functors of
points are isomorphic over `S`, by an isomorphism inducing the given one by composition. -/
private theorem exists_iso_of_points (B : BigFppfSite.{u}) (hS : B.Contains S) {M M' : Over S}
    (hM : B.Contains M.left) (hM' : B.Contains M'.left)
    (β : points (Over.post (X := B.obj hS) B.inclusion) M ⋙ uliftFunctor.{u + 1} ≅
      points (Over.post (X := B.obj hS) B.inclusion) M' ⋙ uliftFunctor.{u + 1}) :
    ∃ e : M ≅ M', ∀ (N : Over S) (hN : B.Contains N.left) (k : N ⟶ M),
      β.hom.app (op (siteOver B hS N hN)) (ULift.up k) = ULift.up (k ≫ e.hom) :=
  ⟨⟨_, _, comp_eq_id_of_comp_eq_id B hS hM β.hom β.inv hM' β.hom_inv_id,
    comp_eq_id_of_comp_eq_id B hS hM' β.inv β.hom hM β.inv_hom_id⟩,
    fun _ hN k ↦ comp_eq_of_app B hS hM β.hom hN k⟩

/-- **Uniqueness of a finite flat quotient.** Two finite flat quotients of one groupoid
scheme, both visible in a big fppf site containing the base, the objects and the arrows, are
isomorphic over `S` by an isomorphism carrying the one quotient map to the other. -/
theorem exists_iso (Q Q' : FiniteFlatQuotient G) (B : BigFppfSite.{u}) (hS : B.Contains S)
    (hU : B.Contains G.objects.left) (hR : B.Contains G.arrows.left)
    (hM : B.Contains Q.space.left)
    (hM' : B.Contains Q'.space.left) :
    ∃ e : Q.space ≅ Q'.space, Q.quotientMap ≫ e.hom = Q'.quotientMap := by
  obtain ⟨e, w⟩ := Q.represents B hS hU hR hM
  obtain ⟨e', w'⟩ := Q'.represents B hS hU hR hM'
  obtain ⟨iso, hiso⟩ := exists_iso_of_points B hS hM hM' (e.symm.trans e')
  refine ⟨iso, ?_⟩
  have hw : Functor.whiskerRight ((Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft
        (yoneda.map Q.quotientMap)) uliftFunctor.{u + 1} ≫ (e.symm.trans e').hom =
      Functor.whiskerRight ((Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft
        (yoneda.map Q'.quotientMap)) uliftFunctor.{u + 1} := by
    rw [← w, ← w']
    simp
  have hq : (e.symm.trans e').hom.app (op (siteOver B hS G.objects hU))
        (ULift.up (𝟙 G.objects ≫ Q.quotientMap)) =
      ULift.up (𝟙 G.objects ≫ Q'.quotientMap) :=
    types_congr_hom (NatTrans.congr_app hw (op (siteOver B hS G.objects hU)))
      (ULift.up (𝟙 G.objects))
  have key : (𝟙 G.objects ≫ Q.quotientMap) ≫ iso.hom = 𝟙 G.objects ≫ Q'.quotientMap :=
    ULift.up_injective ((hiso G.objects hU (𝟙 G.objects ≫ Q.quotientMap)).symm.trans hq)
  simpa using key

end Uniqueness

end FiniteFlatQuotient

end Stacks.Groupoids

end
