module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceBaseChangeTransport

/-!
# The base change of a weighted trace map, on geometric stalks

Consider a cartesian square of a big étale site with horizontal morphisms `p : X' ⟶ X`,
`g : Y' ⟶ Y` and vertical morphisms `f : X ⟶ Y`, `f' : X' ⟶ Y'`, with `f` locally quasi-finite,
let `w` be an integer-valued function on `X` and let `F` be an abelian sheaf on the small étale
site of `Y`. A trace map `τ : f_! f^{-1}F ⟶ F` for `(f, w)` gives, through the base-change
isomorphism `g^{-1}f_!F ≅ f'_!p^{-1}F` of Stacks 0F5J, a morphism

`f_!^{\,\prime} p^{-1} f^{-1} F ⟶ g^{-1} F`.

This file computes its effect on geometric stalks: on the summand of the decomposition of
Stacks 0F5F indexed by a point `x` of the geometric fibre of `f'` above a geometric point `t` of
`Y'`, it is multiplication by the weight of the image of `x` in `X`, followed by the canonical
identifications of stalks. That is the weighted sum belonging to `(f', w ∘ p)`, written in terms
of the sheaf `p^{-1}f^{-1}F` rather than `f'^{-1}g^{-1}F`.

## Main results

* `AlgebraicGeometry.SmallEtale.etaleStalkSmallEtalePullObjIso_inv_naturality_apply` — the
  inverse form of the naturality of Stacks 03Q1 in the sheaf, on an element.
* `AlgebraicGeometry.SmallEtale.baseChangeTrace_fiberStalkOf` — the base change of a trace map
  is, on the summand indexed by a point `x` of the geometric fibre of `f'`, multiplication by
  the weight of the image of `x`.

## References

* [Stacks Project, Tag 0GKH](https://stacks.math.columbia.edu/tag/0GKH)
* [Stacks Project, Tag 0GKG](https://stacks.math.columbia.edu/tag/0GKG)
* [Stacks Project, Tag 0F5J](https://stacks.math.columbia.edu/tag/0F5J)
* [Stacks Project, Tag 0F5F](https://stacks.math.columbia.edu/tag/0F5F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum

universe u uA vA

namespace AlgebraicGeometry.SmallEtale

section PullbackNaturality

/-- Applying the inverse of an isomorphism of abelian groups undoes it. -/
public theorem iso_inv_hom_apply {M N : AddCommGrpCat.{uA}} (e : M ≅ N) (a : M) :
    e.inv (e.hom a) = a := by
  simp

/-- Applying an isomorphism of abelian groups undoes its inverse. -/
public theorem iso_hom_inv_apply {M N : AddCommGrpCat.{uA}} (e : M ≅ N) (b : N) :
    e.hom (e.inv b) = b := by
  simp

/-- The inverse form of the naturality of Stacks 03Q1 in the sheaf, on an element: the stalk of
`q^{-1}φ` applied to an element transported by the inverse of the identification of the stalk of
an inverse image is the transport of the stalk of `φ`. -/
public theorem etaleStalkSmallEtalePullObjIso_inv_naturality_apply (B : BigEtaleSite.{u})
    {S T : B.Scheme} (q : T ⟶ S) (x : GeometricPoint T.obj)
    {F G : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1}} (φ : F ⟶ G)
    (z : ↑(etaleStalk B S.obj S.property (x.map (B.inclusion.map q)) F.obj)) :
    ((etaleStalkPresheafFunctor B T.obj T.property x AddCommGrpCat.{u + 1}).map
        ((((smallEtaleBaseChange B q).sheafPullback AddCommGrpCat.{u + 1}
          (SmallEtale.topology B S.obj S.property)
          (SmallEtale.topology B T.obj T.property)).map φ).hom))
      ((etaleStalkSmallEtalePullObjIso B q x AddCommGrpCat.{u + 1} F).inv z) =
      (etaleStalkSmallEtalePullObjIso B q x AddCommGrpCat.{u + 1} G).inv
        ((etaleStalkPresheafFunctor B S.obj S.property (x.map (B.inclusion.map q))
          AddCommGrpCat.{u + 1}).map φ.hom z) := by
  have h := ConcreteCategory.congr_hom
    (etaleStalkSmallEtalePullObjIso_natural B q x AddCommGrpCat.{u + 1} φ)
    ((etaleStalkSmallEtalePullObjIso B q x AddCommGrpCat.{u + 1} F).inv z)
  have h' := (ConcreteCategory.comp_apply _ _ _).symm.trans
    (h.trans (ConcreteCategory.comp_apply _ _ _))
  have h'' := h'.trans (congrArg (fun m => ((etaleStalkPresheafFunctor B S.obj S.property
      (x.map (B.inclusion.map q)) AddCommGrpCat.{u + 1}).map φ.hom) m)
    (iso_hom_inv_apply (etaleStalkSmallEtalePullObjIso B q x AddCommGrpCat.{u + 1} F) z))
  exact (iso_inv_hom_apply
      (etaleStalkSmallEtalePullObjIso B q x AddCommGrpCat.{u + 1} G) _).symm.trans
    (congrArg (fun m =>
      (etaleStalkSmallEtalePullObjIso B q x AddCommGrpCat.{u + 1} G).inv m) h'')

end PullbackNaturality

section Core

variable (B : BigEtaleSite.{u}) {X Y X' Y' : B.Scheme}
  (p : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : IsPullback p f' f g)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map f')] [LocallyQuasiFinite (B.inclusion.map f')]

/-- The base change of a weighted trace map on a summand of a geometric stalk. Let `τ` be a
morphism `f_! f^{-1}F ⟶ F` with the behaviour on geometric stalks which characterises the trace
map of Stacks 0GKG for `(f, w)`. Transporting `g^{-1}τ` along the base-change isomorphism of
Stacks 0F5J gives a morphism `f'_! p^{-1}f^{-1}F ⟶ g^{-1}F`; on the summand of the stalk
decomposition of Stacks 0F5F at a geometric point `t` of `Y'` indexed by a point `x` of the
geometric fibre of `f'`, it is multiplication by the weight of the image of `x` in `X`, read
through the identifications of stalks of Stacks 03Q1. -/
public theorem baseChangeTrace_fiberStalkOf (w : X.obj → ℤ)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1})
    {τ : (fShriekFunctor.{u, u + 1} B f).obj ((abPullback.{u, u + 1} B f).obj F) ⟶ F}
    (hτ : HasWeightedTraceStalks.{u, u + 1} B f w F τ)
    (t : GeometricPoint Y'.obj) (x : GeometricFiberPoint B f' t)
    (ζ : ↑(etaleStalk B X'.obj X'.property (x.toGeometricPoint B f' t)
      ((abPullback.{u, u + 1} B p).obj ((abPullback.{u, u + 1} B f).obj F)).obj)) :
    ((etaleStalkPresheafFunctor B Y'.obj Y'.property t AddCommGrpCat.{u + 1}).map
        (((fShriekBaseChangeNatIso.{u} B p f' f g sq).inv.app
            ((abPullback.{u, u + 1} B f).obj F) ≫
          (abPullback.{u, u + 1} B g).map τ).hom))
      ((fShriekStalkIso.{u, u + 1} B f' t
          ((abPullback.{u, u + 1} B p).obj ((abPullback.{u, u + 1} B f).obj F))).inv
        (fiberStalkOf.{u, u + 1} B f' t
          ((abPullback.{u, u + 1} B p).obj ((abPullback.{u, u + 1} B f).obj F)) x ζ)) =
      w ((fiberPointBaseChange B p f' f g sq t x).1 default) •
        (etaleStalkSmallEtalePullObjIso B g t AddCommGrpCat.{u + 1} F).inv
          ((fiberPointPullbackStalkIso.{u, u + 1} B f (t.map (B.inclusion.map g)) F
              (fiberPointBaseChange B p f' f g sq t x)).hom
            ((fiberStalkBaseChangeIso.{u, u + 1} B p f' f g sq t
              ((abPullback.{u, u + 1} B f).obj F) x).inv ζ)) := by
  have hbc := fShriekBaseChangeNatIso_inv_fiberStalkOf.{u} B p f' f g sq t
    ((abPullback.{u, u + 1} B f).obj F) x ζ
  have hnat := etaleStalkSmallEtalePullObjIso_inv_naturality_apply B g t τ
    ((fShriekStalkIso.{u, u + 1} B f (t.map (B.inclusion.map g))
        ((abPullback.{u, u + 1} B f).obj F)).inv
      (fiberStalkOf.{u, u + 1} B f (t.map (B.inclusion.map g))
        ((abPullback.{u, u + 1} B f).obj F)
        (fiberPointBaseChange B p f' f g sq t x)
        ((fiberStalkBaseChangeIso.{u, u + 1} B p f' f g sq t
          ((abPullback.{u, u + 1} B f).obj F) x).inv ζ)))
  have hw := hasWeightedTraceStalks_fiberStalkOf.{u, u + 1} B f w F hτ
    (t.map (B.inclusion.map g)) (fiberPointBaseChange B p f' f g sq t x)
    ((fiberStalkBaseChangeIso.{u, u + 1} B p f' f g sq t
      ((abPullback.{u, u + 1} B f).obj F) x).inv ζ)
  have hsplit := congrArg
    (fun m => (ConcreteCategory.hom m)
      ((fShriekStalkIso.{u, u + 1} B f' t
          ((abPullback.{u, u + 1} B p).obj ((abPullback.{u, u + 1} B f).obj F))).inv
        (fiberStalkOf.{u, u + 1} B f' t
          ((abPullback.{u, u + 1} B p).obj ((abPullback.{u, u + 1} B f).obj F)) x ζ)))
    ((etaleStalkPresheafFunctor B Y'.obj Y'.property t AddCommGrpCat.{u + 1}).map_comp
      ((fShriekBaseChangeNatIso.{u} B p f' f g sq).inv.app
        ((abPullback.{u, u + 1} B f).obj F)).hom
      (((abPullback.{u, u + 1} B g).map τ).hom))
  refine hsplit.trans ((ConcreteCategory.comp_apply _ _ _).trans ?_)
  refine (congrArg (fun z => ((etaleStalkPresheafFunctor B Y'.obj Y'.property t
      AddCommGrpCat.{u + 1}).map (((abPullback.{u, u + 1} B g).map τ).hom)) z) hbc).trans ?_
  refine hnat.trans ?_
  refine (congrArg
    (fun z => (etaleStalkSmallEtalePullObjIso B g t AddCommGrpCat.{u + 1} F).inv z) hw).trans ?_
  exact map_zsmul _ _ _

end Core

end AlgebraicGeometry.SmallEtale

end
