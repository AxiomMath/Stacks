module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimit.Basic
public import StacksFrontier.CategoryTheory.Bicategory.LeftAdjointPseudofunctor
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimit.Coherence
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The pseudofunctor of small étale inverse images, for any coefficient category

Let `B` be a big étale site and `A` a category such that the direct image along every small étale
base change functor has a left adjoint. The categories of `A`-valued sheaves on the small étale
sites of the schemes of `B`, together with the inverse images along the morphisms of `B`, form a
pseudofunctor on `LocallyDiscrete B.Schemeᵒᵖ` whose composition constraint is the canonical
comparison `AlgebraicGeometry.smallEtaleSheafPullbackCompIso` (inverted).

The construction is `CategoryTheory.LocallyDiscrete.mkPseudofunctorOfLeftAdjoints`: the direct
images compose up to the comparison of iterated fibre products, and their three coherences
reduce to identities between iterated fibre products. The same pseudofunctor for sheaves of sets
is `AlgebraicGeometry.smallEtaleSheafPullbackSystem`, built there by passing through the
bicategory of adjunctions; the coherences on the sites are the ones proved there, together with
`AlgebraicGeometry.smallEtaleBaseChange_compIso_comp_id` and
`AlgebraicGeometry.smallEtaleBaseChange_compIso_id_comp` for the identity comparison
`AlgebraicGeometry.smallEtaleBaseChange_idIso`.

## Main definitions

* `AlgebraicGeometry.SmallEtaleGluing.pushforwardComp` — the composition comparison of the
  direct images.
* `AlgebraicGeometry.SmallEtaleGluing.pseudofunctor` — the pseudofunctor of inverse images.

## Main results

* `AlgebraicGeometry.SmallEtaleGluing.pseudofunctor_mapComp'_hom_app` and
  `AlgebraicGeometry.SmallEtaleGluing.pseudofunctor_mapComp'_inv_app` — its flexible composition
  constraint is the comparison `AlgebraicGeometry.smallEtaleSheafPullbackCompIso'`.

## References

* [Stacks Project, Tag 021J](https://stacks.math.columbia.edu/tag/021J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t v u

namespace AlgebraicGeometry

namespace SmallEtaleGluing

-- Base change is defined by lifting slice pullback along a full subcategory inclusion, so
-- recognizing a base-changed object as the corresponding slice pullback is a round trip through
-- structure projections, which instance-level definitional unfolding has to see through.
attribute [local implicit_reducible] smallEtaleBaseChange

variable (B : BigEtaleSite.{u}) (A : Type t) [Category.{v} A]

/-- The direct image of `A`-valued sheaves along small étale base change. -/
public abbrev pushforward {X Y : B.Scheme} (f : X ⟶ Y) :
    Sheaf (SmallEtale.topology B X.1 X.property) A ⥤
      Sheaf (SmallEtale.topology B Y.1 Y.property) A :=
  (smallEtaleBaseChange B f).sheafPushforwardContinuous A
    (SmallEtale.topology B Y.1 Y.property) (SmallEtale.topology B X.1 X.property)

/-- The identity comparison of the direct images. -/
public def pushforwardId (X : B.Scheme) : pushforward B A (𝟙 X) ≅ 𝟭 _ :=
  Functor.sheafPushforwardContinuousId' (smallEtaleBaseChange_idIso B X) A _

/-- The composition comparison of the direct images, in the orientation
`CategoryTheory.LocallyDiscrete.mkPseudofunctorOfLeftAdjoints` asks for. -/
public def pushforwardComp {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pushforward B A (f ≫ g) ≅ pushforward B A f ⋙ pushforward B A g :=
  (Functor.sheafPushforwardContinuousComp' (smallEtaleBaseChange_compIso B X Y Z f g).val A
    (SmallEtale.topology B Z.1 Z.property) (SmallEtale.topology B Y.1 Y.property)
    (SmallEtale.topology B X.1 X.property)).symm

/-- The direct image of a sheaf acts on sections by evaluation at the base change. -/
public theorem pushforward_obj_obj_map {X Y : B.Scheme} (f : X ⟶ Y)
    (M : Sheaf (SmallEtale.topology B X.1 X.property) A)
    {U V : (SmallEtale B Y.1 Y.property)ᵒᵖ} (a : U ⟶ V) :
    ((pushforward B A f).obj M).obj.map a = M.obj.map ((smallEtaleBaseChange B f).map a.unop).op :=
  rfl

/-- The composition comparison of the direct images acts on sections by restriction along the
composition comparison of the base changes. -/
public theorem pushforwardComp_hom_app_hom_app {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Sheaf (SmallEtale.topology B X.1 X.property) A) (U : (SmallEtale B Z.1 Z.property)ᵒᵖ) :
    ((pushforwardComp B A f g).hom.app M).hom.app U =
      M.obj.map ((smallEtaleBaseChange_compIso B X Y Z f g).val.hom.app U.unop).op :=
  Category.comp_id _

/-- The inverse of the composition comparison of the direct images acts on sections by
restriction along the inverse composition comparison of the base changes. -/
public theorem pushforwardComp_inv_app_hom_app {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Sheaf (SmallEtale.topology B X.1 X.property) A) (U : (SmallEtale B Z.1 Z.property)ᵒᵖ) :
    ((pushforwardComp B A f g).inv.app M).hom.app U =
      M.obj.map ((smallEtaleBaseChange_compIso B X Y Z f g).val.inv.app U.unop).op :=
  Category.id_comp _

/-- The direct image of a morphism of sheaves acts on sections by evaluation at the base
change. -/
public theorem pushforward_map_hom_app {X Y : B.Scheme} (f : X ⟶ Y)
    {M N : Sheaf (SmallEtale.topology B X.1 X.property) A} (α : M ⟶ N)
    (U : (SmallEtale B Y.1 Y.property)ᵒᵖ) :
    ((pushforward B A f).map α).hom.app U =
      α.hom.app (op ((smallEtaleBaseChange B f).obj U.unop)) :=
  rfl

/-- Two morphisms of functors between categories of sheaves are equal when they agree on sections
over every object. -/
private theorem sheaf_natTrans_ext {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {S T : Sheaf J A ⥤ Sheaf K A}
    {α β : S ⟶ T} (h : ∀ M U, (α.app M).hom.app U = (β.app M).hom.app U) : α = β :=
  NatTrans.ext (funext fun M => ObjectProperty.hom_ext _ (NatTrans.ext (funext (h M))))

/-- **The associativity coherence of the direct images.** -/
public theorem pushforwardComp_assoc {X Y Z W : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Z ⟶ W) :
    (pushforwardComp B A (f ≫ g) h).hom ≫
        Functor.whiskerRight (pushforwardComp B A f g).hom (pushforward B A h) ≫
        (Functor.associator (pushforward B A f) (pushforward B A g) (pushforward B A h)).hom ≫
          Functor.whiskerLeft (pushforward B A f) (pushforwardComp B A g h).inv ≫
            (pushforwardComp B A f (g ≫ h)).inv =
      eqToHom (congrArg (fun k : X ⟶ W => pushforward B A k) (Category.assoc f g h)) := by
  refine Eq.trans (sheaf_natTrans_ext A fun M U => ?_) (eqToHom_refl _ _).symm
  have hc := baseChangeCompIso_assoc B f g h U.unop
  simp only [NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, NatTrans.id_app,
    ObjectProperty.FullSubcategory.id_hom, pushforwardComp_hom_app_hom_app,
    pushforwardComp_inv_app_hom_app, pushforward_map_hom_app, pushforward_obj_obj_map,
    Quiver.Hom.unop_op, Category.id_comp]
  refine Eq.trans ?_ ((congrArg (fun a => M.obj.map a.op) hc).trans (M.obj.map_id _))
  simp only [op_comp, Functor.map_comp, Category.assoc]
  rfl

/-- The inverse of the identity comparison of the direct images acts on sections by
restriction along the identity comparison of base change. -/
public theorem pushforwardId_inv_app_hom_app (X : B.Scheme)
    (M : Sheaf (SmallEtale.topology B X.1 X.property) A) (U : (SmallEtale B X.1 X.property)ᵒᵖ) :
    ((pushforwardId B A X).inv.app M).hom.app U =
      M.obj.map ((smallEtaleBaseChange_idIso B X).hom.app U.unop).op :=
  Category.id_comp _

/-- **The first unit coherence of the direct images.** -/
public theorem pushforwardComp_comp_id {X Y : B.Scheme} (p : X ⟶ Y) :
    (Functor.rightUnitor (pushforward B A p)).inv ≫
        Functor.whiskerLeft (pushforward B A p) (pushforwardId B A Y).inv ≫
          (pushforwardComp B A p (𝟙 Y)).inv =
      eqToHom (congrArg (fun k : X ⟶ Y => pushforward B A k) (Category.comp_id p).symm) := by
  refine Eq.trans (sheaf_natTrans_ext A fun M U => ?_) (eqToHom_refl _ _).symm
  have hc := smallEtaleBaseChange_compIso_comp_id B p U.unop
  simp only [NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_inv_app, NatTrans.id_app,
    ObjectProperty.FullSubcategory.id_hom, pushforwardId_inv_app_hom_app,
    pushforwardComp_inv_app_hom_app, pushforward_obj_obj_map, Quiver.Hom.unop_op,
    Category.id_comp]
  refine Eq.trans ?_ ((congrArg (fun a => M.obj.map a.op) hc).trans (M.obj.map_id _))
  simp only [op_comp, Functor.map_comp]
  rfl

/-- **The second unit coherence of the direct images.** -/
public theorem pushforwardComp_id_comp {X Y : B.Scheme} (p : X ⟶ Y) :
    (Functor.leftUnitor (pushforward B A p)).inv ≫
        Functor.whiskerRight (pushforwardId B A X).inv (pushforward B A p) ≫
          (pushforwardComp B A (𝟙 X) p).inv =
      eqToHom (congrArg (fun k : X ⟶ Y => pushforward B A k) (Category.id_comp p).symm) := by
  refine Eq.trans (sheaf_natTrans_ext A fun M U => ?_) (eqToHom_refl _ _).symm
  have hc := smallEtaleBaseChange_compIso_id_comp B p U.unop
  simp only [NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom, Functor.whiskerRight_app,
    Functor.leftUnitor_inv_app, NatTrans.id_app,
    ObjectProperty.FullSubcategory.id_hom, pushforwardId_inv_app_hom_app,
    pushforwardComp_inv_app_hom_app, pushforward_map_hom_app, Category.id_comp]
  refine Eq.trans ?_ ((congrArg (fun a => M.obj.map a.op) hc).trans (M.obj.map_id _))
  simp only [op_comp, Functor.map_comp]
  rfl

variable [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]

/-- **The pseudofunctor of small étale inverse images.** Its fibre over a scheme of `B` is the
category of `A`-valued sheaves on its small étale site and its transition functor along a
morphism `f` is the inverse image `AlgebraicGeometry.smallEtaleSheafPullback B A f`, both on the
nose; its composition constraint is the inverse of
`AlgebraicGeometry.smallEtaleSheafPullbackCompIso`. -/
@[sga "4 VIII 3.4" "more general"]
public def pseudofunctor : Pseudofunctor (LocallyDiscrete B.Schemeᵒᵖ) Cat :=
  LocallyDiscrete.mkPseudofunctorOfLeftAdjoints
    (fun X : B.Scheme => Cat.of (Sheaf (SmallEtale.topology B X.1 X.property) A))
    (fun f => smallEtaleSheafPullback B A f) (fun f => pushforward B A f)
    (fun f => (smallEtaleBaseChange B f).sheafAdjunctionContinuous A _ _)
    (pushforwardId B A) (fun f g => pushforwardComp B A f g)
    (pushforwardComp_assoc B A) (pushforwardComp_comp_id B A) (pushforwardComp_id_comp B A)

/-- The transition functor of `AlgebraicGeometry.SmallEtaleGluing.pseudofunctor` along `f` is
the inverse image along `f`. -/
public theorem pseudofunctor_map {X Y : B.Scheme} (f : X ⟶ Y) :
    (pseudofunctor B A).map f.op.toLoc = (smallEtaleSheafPullback B A f).toCatHom :=
  rfl

/-- **The flexible composition constraint is the comparison along a named composite**, on
components. -/
public theorem pseudofunctor_mapComp'_hom_app {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (e : f ≫ g = h) (hc : g.op.toLoc ≫ f.op.toLoc = h.op.toLoc)
    (M : Sheaf (SmallEtale.topology B Z.1 Z.property) A) :
    ((pseudofunctor B A).mapComp' g.op.toLoc f.op.toLoc h.op.toLoc hc).hom.toNatTrans.app M =
      (smallEtaleSheafPullbackCompIso' B A f g h e).inv.app M := by
  subst e
  rw [smallEtaleSheafPullbackCompIso'_rfl]
  change ((pseudofunctor B A).mapComp' g.op.toLoc f.op.toLoc (g.op.toLoc ≫ f.op.toLoc)
    rfl).hom.toNatTrans.app M = _
  rw [Pseudofunctor.mapComp'_eq_mapComp]
  rfl

/-- **The flexible composition constraint is the comparison along a named composite**, on
components of the inverse. -/
public theorem pseudofunctor_mapComp'_inv_app {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (e : f ≫ g = h) (hc : g.op.toLoc ≫ f.op.toLoc = h.op.toLoc)
    (M : Sheaf (SmallEtale.topology B Z.1 Z.property) A) :
    ((pseudofunctor B A).mapComp' g.op.toLoc f.op.toLoc h.op.toLoc hc).inv.toNatTrans.app M =
      (smallEtaleSheafPullbackCompIso' B A f g h e).hom.app M := by
  subst e
  rw [smallEtaleSheafPullbackCompIso'_rfl]
  change ((pseudofunctor B A).mapComp' g.op.toLoc f.op.toLoc (g.op.toLoc ≫ f.op.toLoc)
    rfl).inv.toNatTrans.app M = _
  rw [Pseudofunctor.mapComp'_eq_mapComp]
  rfl

end SmallEtaleGluing

end AlgebraicGeometry

end
