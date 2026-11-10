module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.CoefficientsGerm
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.CompGerm
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointStalkMap

/-!
# The stalk of an inverse image is compatible with automorphisms of the geometric point

Let `f : T ⟶ S` be a morphism of a big étale site, `x` a geometric point of `T` and `a` an
endomorphism of `x` (a morphism `x.source ⟶ x.source` over `T`). Then `a` is also an
endomorphism of the image geometric point `f(x)`, and the identification of Stacks 03Q1,
`(f⁻¹ F)_x ≅ F_{f(x)}` (`AlgebraicGeometry.etaleStalkSmallEtalePullObjIso`), intertwines the
canonical maps of stalks of Stacks 04FN along `a` on both sides.

Combined with `AlgebraicGeometry.etaleStalkSmul_eq_geometricPointStalkMap` this transports the
Galois action on the stalk of the pullback of a sheaf to the spectrum of a field to the action of
automorphisms of the geometric point on the stalk of the sheaf itself.

## Main definitions

* `AlgebraicGeometry.GeometricPoint.Hom.mapHom` — the endomorphism of `f(x)` induced by `a`.

## Main results

* `AlgebraicGeometry.geometricPointStalkMap_comp_etaleStalkSmallEtalePullObjIso_hom` — the
  compatibility.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u uA vA

namespace AlgebraicGeometry

/-- An endomorphism of a geometric point is an endomorphism of its image under any morphism of
schemes. -/
def GeometricPoint.Hom.mapHom {X Y : Scheme.{u}} {x : GeometricPoint X} (a : GeometricPoint.Hom x x)
    (g : X ⟶ Y) : GeometricPoint.Hom (x.map g) (x.map g) where
  hom := a.hom
  comm := by
    change a.hom ≫ x.hom ≫ g = x.hom ≫ g
    rw [← Category.assoc, a.comm]

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S) (x : GeometricPoint T.obj)
  (A : Type uA) [Category.{vA} A] [HasColimitsOfSize.{u, u} A] [HasProducts.{u} A]
  [((smallEtaleBaseChange B f).sheafPushforwardContinuous A
    (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]

/-- **The stalk of an inverse image intertwines the automorphisms of the geometric point.** -/
theorem geometricPointStalkMap_comp_etaleStalkSmallEtalePullObjIso_hom
    (a : GeometricPoint.Hom x x) (F : Sheaf (SmallEtale.topology B S.obj S.property) A) :
    (geometricPointStalkMap B T.obj T.property a A).app
        (((smallEtaleBaseChange B f).sheafPullback A
          (SmallEtale.topology B S.obj S.property)
          (SmallEtale.topology B T.obj T.property)).obj F).obj ≫
        (etaleStalkSmallEtalePullObjIso B f x A F).hom =
      (etaleStalkSmallEtalePullObjIso B f x A F).hom ≫
        (geometricPointStalkMap B S.obj S.property (a.mapHom (B.inclusion.map f)) A).app
          F.obj := by
  refine (cancel_epi (etaleStalkSmallEtalePullObjIso B f x A F).inv).1 ?_
  refine Eq.trans ?_ (Iso.inv_hom_id_assoc (etaleStalkSmallEtalePullObjIso B f x A F) _).symm
  refine colimit.hom_ext (fun V ↦ ?_)
  obtain ⟨@⟨V, w⟩⟩ := V
  let u := geometricPointFiberBaseChangeEquiv B f x V w
  let eU : (geometricPointFiber B T.obj T.property x).Elements := ⟨u⟩
  let eV : (geometricPointFiber B S.obj S.property (x.map (B.inclusion.map f))).Elements :=
    ⟨w⟩
  have hg := etaleStalkSmallEtalePullObjIso_germ B f x A F eU eV (𝟙 _)
    (geometricPointFiberBaseChangeEquiv_ha B f x V w)
  have hinv := (Iso.comp_inv_eq (etaleStalkSmallEtalePullObjIso B f x A F)).2
    (hg.symm.trans (Category.assoc _ _ _).symm)
  let eU' : (geometricPointFiber B T.obj T.property x).Elements :=
    ⟨(geometricPointFiberMap B T.obj T.property a).app _ u⟩
  let eV' : (geometricPointFiber B S.obj S.property (x.map (B.inclusion.map f))).Elements :=
    ⟨(geometricPointFiberMap B S.obj S.property (a.mapHom (B.inclusion.map f))).app V w⟩
  have hg' := etaleStalkSmallEtalePullObjIso_germ B f x A F eU' eV'
    (𝟙 _) ((Category.assoc _ _ _).trans
      (congrArg (a.hom ≫ ·) (geometricPointFiberBaseChangeEquiv_ha B f x V w)))
  have h1 := colimit.ι_pre ((Functor.Elements.π (geometricPointFiber B T.obj T.property x)).op ⋙
    (((smallEtaleBaseChange B f).sheafPullback A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).obj F).obj)
    (neighborhoodFunctor B T.obj T.property a).op (op eU)
  have h2 := colimit.ι_pre ((Functor.Elements.π (geometricPointFiber B S.obj S.property
    (x.map (B.inclusion.map f)))).op ⋙ F.obj)
    (neighborhoodFunctor B S.obj S.property (a.mapHom (B.inclusion.map f))).op (op eV)
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hinv).trans ?_)
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h1))).trans ?_
  refine Eq.trans ?_ h2.symm
  exact hg'

end AlgebraicGeometry

end
