module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceBaseChangeStalks

/-!
# Transporting a germ across the base-change isomorphism of `f_!`

Consider a cartesian square of a big étale site with horizontal morphisms `p : X' ⟶ X`,
`g : Y' ⟶ Y` and vertical morphisms `f : X ⟶ Y`, `f' : X' ⟶ Y'`, with `f` locally quasi-finite.
Stacks 0F5J provides the isomorphism `g^{-1}f_!F ≅ f'_!p^{-1}F`, and
`AlgebraicGeometry.SmallEtale.fShriekBaseChangeNatIso_stalk` says what it does on the stalk at a
geometric point `t` of `Y'`: read through the stalk decompositions of Stacks 0F5F it is the
comparison of the two direct sums of stalks over the geometric fibres. This file derives from it
the inverse of the isomorphism on stalks, and its effect on a single summand of the
decomposition, together with the naturality of the inverse-image comparison of Stacks 03Q1 in
the sheaf.

## Main results

* `AlgebraicGeometry.SmallEtale.etaleStalkSmallEtalePullObjIso_natural` — the identification of
  the stalk of an inverse image with the stalk at the image point is natural in the sheaf.
* `AlgebraicGeometry.SmallEtale.stalkMap_fShriekBaseChangeNatIso_inv` — the stalk of the inverse
  of the base-change isomorphism of Stacks 0F5J is the inverse of the stalkwise base-change
  comparison.
* `AlgebraicGeometry.SmallEtale.fShriekBaseChangeNatIso_inv_fiberStalkOf` — the summandwise
  form: the inverse of the base-change isomorphism carries the germ placed in the summand of the
  decomposition of `f'_!p^{-1}F` indexed by a point `x` of the geometric fibre of `f'` to the
  corresponding germ placed in the summand of the decomposition of `f_!F` indexed by the image of
  `x` in the geometric fibre of `f`.

## References

* [Stacks Project, Tag 0F5J](https://stacks.math.columbia.edu/tag/0F5J)
* [Stacks Project, Tag 0F5F](https://stacks.math.columbia.edu/tag/0F5F)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum

universe u uA vA

namespace AlgebraicGeometry.SmallEtale

section PullbackNaturality

/-- Stacks 03Q1 is natural in the sheaf: the identification of the stalk of `q^{-1}F` at a
geometric point `x` with the stalk of `F` at the image point intertwines the map induced by
`q^{-1}φ` on the first with the map induced by `φ` on the second. -/
public theorem etaleStalkSmallEtalePullObjIso_natural (B : BigEtaleSite.{u}) {S T : B.Scheme}
    (q : T ⟶ S) (x : GeometricPoint T.obj)
    (A : Type uA) [Category.{vA} A] [HasColimitsOfSize.{u, u} A] [HasProducts.{u} A]
    [((smallEtaleBaseChange B q).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    {F G : Sheaf (SmallEtale.topology B S.obj S.property) A} (φ : F ⟶ G) :
    (etaleStalkPresheafFunctor B T.obj T.property x A).map
          ((((smallEtaleBaseChange B q).sheafPullback A
            (SmallEtale.topology B S.obj S.property)
            (SmallEtale.topology B T.obj T.property)).map φ).hom) ≫
        (etaleStalkSmallEtalePullObjIso B q x A G).hom =
      (etaleStalkSmallEtalePullObjIso B q x A F).hom ≫
        (etaleStalkPresheafFunctor B S.obj S.property (x.map (B.inclusion.map q)) A).map φ.hom :=
  (smallEtalePullbackSheafFiberIso B q x A).hom.naturality φ

end PullbackNaturality

section BaseChange

variable (B : BigEtaleSite.{u}) {X Y X' Y' : B.Scheme}
  (p : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : IsPullback p f' f g)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map f')] [LocallyQuasiFinite (B.inclusion.map f')]
  (t : GeometricPoint Y'.obj)
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})

/-- The stalk of the base-change isomorphism of Stacks 0F5J is the stalkwise base-change
comparison. -/
public theorem stalkMap_fShriekBaseChangeNatIso_hom :
    (etaleStalkPresheafFunctor B Y'.obj Y'.property t AddCommGrpCat.{u + 1}).map
        ((fShriekBaseChangeNatIso.{u} B p f' f g sq).hom.app F).hom =
      (fShriekStalkBaseChangeIso.{u, u + 1} B p f' f g sq t F).hom :=
  fShriekBaseChangeMap_stalk_eq.{u} B p f' f g sq t F

/-- The stalk of the inverse of the base-change isomorphism of Stacks 0F5J is the inverse of the
stalkwise base-change comparison. -/
public theorem stalkMap_fShriekBaseChangeNatIso_inv :
    (etaleStalkPresheafFunctor B Y'.obj Y'.property t AddCommGrpCat.{u + 1}).map
        ((fShriekBaseChangeNatIso.{u} B p f' f g sq).inv.app F).hom =
      (fShriekStalkBaseChangeIso.{u, u + 1} B p f' f g sq t F).inv := by
  have hcomp : (fShriekStalkBaseChangeIso.{u, u + 1} B p f' f g sq t F).hom ≫
      (etaleStalkPresheafFunctor B Y'.obj Y'.property t AddCommGrpCat.{u + 1}).map
        ((fShriekBaseChangeNatIso.{u} B p f' f g sq).inv.app F).hom = 𝟙 _ := by
    have h := congrArg
      (sheafToPresheaf (SmallEtale.topology B Y'.obj Y'.property) AddCommGrpCat.{u + 1} ⋙
        etaleStalkPresheafFunctor B Y'.obj Y'.property t AddCommGrpCat.{u + 1}).map
      ((fShriekBaseChangeNatIso.{u} B p f' f g sq).hom_inv_id_app F)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at h
    rw [← stalkMap_fShriekBaseChangeNatIso_hom.{u} B p f' f g sq t F]
    exact h
  exact (Iso.inv_hom_id_assoc _ _).symm.trans
    ((congrArg (fun m => (fShriekStalkBaseChangeIso.{u, u + 1} B p f' f g sq t F).inv ≫ m)
        hcomp).trans (Category.comp_id _))

/-- The summandwise form of base change for `f_!`: the inverse of the base-change isomorphism of
Stacks 0F5J carries an element placed, through the decomposition of Stacks 0F5F, in the summand of
the stalk of `f'_!p^{-1}F` at `t` indexed by a point `x` of the geometric fibre of `f'`, to the
corresponding element placed in the summand of the stalk of `f_!F` at the image of `t` indexed by
the image of `x` in the geometric fibre of `f`, read through the identification of the stalk of an
inverse image. -/
public theorem fShriekBaseChangeNatIso_inv_fiberStalkOf (x : GeometricFiberPoint B f' t)
    (ζ : ↑(etaleStalk B X'.obj X'.property (x.toGeometricPoint B f' t)
      ((abPullback.{u, u + 1} B p).obj F).obj)) :
    ((etaleStalkPresheafFunctor B Y'.obj Y'.property t AddCommGrpCat.{u + 1}).map
        ((fShriekBaseChangeNatIso.{u} B p f' f g sq).inv.app F).hom)
      ((fShriekStalkIso.{u, u + 1} B f' t ((abPullback.{u, u + 1} B p).obj F)).inv
        (fiberStalkOf.{u, u + 1} B f' t ((abPullback.{u, u + 1} B p).obj F) x ζ)) =
      (etaleStalkSmallEtalePullObjIso B g t AddCommGrpCat.{u + 1}
          ((fShriekFunctor.{u, u + 1} B f).obj F)).inv
        ((fShriekStalkIso.{u, u + 1} B f (t.map (B.inclusion.map g)) F).inv
          (fiberStalkOf.{u, u + 1} B f (t.map (B.inclusion.map g)) F
            (fiberPointBaseChange B p f' f g sq t x)
            ((fiberStalkBaseChangeIso.{u, u + 1} B p f' f g sq t F x).inv ζ))) := by
  have hE := fiberStalksBaseChangeEquiv_symm_fiberStalkOf.{u, u + 1} B p f' f g sq t F x ζ
  have hmor : (fShriekStalkIso.{u, u + 1} B f' t ((abPullback.{u, u + 1} B p).obj F)).inv ≫
      (fShriekStalkBaseChangeIso.{u, u + 1} B p f' f g sq t F).inv =
      (AddEquiv.toAddCommGrpIso (fiberStalksBaseChangeEquiv.{u, u + 1}
          B p f' f g sq t F)).inv ≫
        (fShriekStalkIso.{u, u + 1} B f (t.map (B.inclusion.map g)) F).inv ≫
        (etaleStalkSmallEtalePullObjIso B g t AddCommGrpCat.{u + 1}
          ((fShriekFunctor.{u, u + 1} B f).obj F)).inv := by
    simp only [fShriekStalkBaseChangeIso, Iso.trans_inv, Iso.symm_inv, Category.assoc]
    exact Iso.inv_hom_id_assoc _ _
  have h2 := ConcreteCategory.congr_hom hmor
    (fiberStalkOf.{u, u + 1} B f' t ((abPullback.{u, u + 1} B p).obj F) x ζ)
  simp only [ConcreteCategory.comp_apply] at h2
  rw [stalkMap_fShriekBaseChangeNatIso_inv.{u} B p f' f g sq t F]
  exact h2.trans (congrArg (fun m =>
    (etaleStalkSmallEtalePullObjIso B g t AddCommGrpCat.{u + 1}
        ((fShriekFunctor.{u, u + 1} B f).obj F)).inv
      ((fShriekStalkIso.{u, u + 1} B f (t.map (B.inclusion.map g)) F).inv m)) hE)

end BaseChange

end AlgebraicGeometry.SmallEtale

end
