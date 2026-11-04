module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangePasting
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeRestriction
public import StacksFrontier.AlgebraicGeometry.Topologies.BigFppfInternalHom
public import StacksFrontier.CategoryTheory.Representable.PullbackComposition
public import StacksFrontier.CategoryTheory.Sites.PushforwardContinuousCalculus

/-!
# Base change of étale scheme charts along a composite

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of algebraic spaces over `S` whose underlying
morphisms of presheaves are representable, and let a representability witness for the
composite be given as well.  Base change of étale scheme charts,
`AlgebraicGeometry.Space.smallBaseChange` of Stacks 03G2, part (4), is then defined along all
three, and this file compares base change along the composite with the composite of the two
base changes, and compares the structure maps `f♯` that go with them.

## Main definitions

* `AlgebraicGeometry.Space.smallBaseChange_comp`: the canonical isomorphism
  `smallBaseChange g ⋙ smallBaseChange f ≅ smallBaseChange (f ≫ g)` of functors of small
  étale sites, with `AlgebraicGeometry.Space.smallBaseChangeCompIso` its component at a chart.

## Main results

* `AlgebraicGeometry.Space.smallBaseChange_comp_projection`: the comparison is compatible with
  the cartesian projections to the original chart, which pins it down.
* `AlgebraicGeometry.Space.smallBaseChangeSharp_comp`: the structure map of small-chart base
  change along the composite is the composite of the two structure maps, read through the
  comparison.  The commutative-ring form is
  `AlgebraicGeometry.Space.smallBaseChangeSharpCommRingCat_comp`.

## Implementation notes

The comparison itself carries no geometry: the two charts `V ×_Z X` and `(V ×_Z Y) ×_Y X` are
both *chosen* fibre products supplied by representability, and the comparison between them is
the formal one built in `StacksFrontier.CategoryTheory.Representable.PullbackComposition` from
`CategoryTheory.Functor.relativelyRepresentable.lift` alone.  Every step here is an
instantiation of a lemma there, with no argument restated:
`AlgebraicGeometry.Space.smallBaseChange_map_pullbackMap` and
`AlgebraicGeometry.Space.smallBaseChange_comp_map_pullbackMap` exhibit the action of
`AlgebraicGeometry.Space.smallBaseChange` on morphisms as the generic
`CategoryTheory.Functor.relativelyRepresentable.pullbackMap`, by `rfl`, after which naturality
of the comparison is one application of the generic naturality lemma.

The generic base change of a morphism of charts is
`AlgebraicGeometry.Space.representablePullbackMap`, by `rfl`
(`AlgebraicGeometry.Space.representablePullbackMap_eq_pullbackMap`), so this file introduces no
second notion of it: what is new is only that it is an instance of a construction available for
an arbitrary fully faithful functor, which is what carries the naturality.

The witness of representability of the composite is a *separate* argument rather than one
produced from the other two: `CategoryTheory.Functor.relativelyRepresentable.pullback` is a
choice, so a consumer that already holds a witness for `f ≫ g` — every consumer of Stacks
03G2, part (4) does — must be able to compare *its* chosen fibre products, not the ones a
multiplicativity argument would choose.  The generic engine is likewise stated for a composite
given together with an identification `f.hom ≫ g.hom = (f ≫ g).hom`, which here is `rfl`.

The structure maps are compared on sections of a single presheaf of rings on the big fppf
site, `AlgebraicGeometry.Space.bigFppfRingSections`: each of the four morphisms involved is
its action on a morphism of the big fppf site, by `rfl`, so the identity to be proved is the
identity of morphisms of the big fppf site
`CategoryTheory.Functor.relativelyRepresentable.pullbackCompInv_snd`.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Z : AlgebraicSpaces B S hS}

/-! ### Small-chart base change through the generic base-change calculus -/

/-- The underlying scheme chart of a base-changed chart is the chosen fibre product, and its
structure morphism is the chosen first projection. -/
theorem smallBaseChange_obj_hom (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
    (V : SmallEtale B S hS Y.1) :
    ((smallBaseChange B S hS f hf).obj V).1.hom = hf.fst V.1.hom :=
  rfl

/-- The base change of a morphism of étale charts named in
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangePasting` is the generic base change
of a morphism of charts of a relatively representable morphism. -/
theorem representablePullbackMap_eq_pullbackMap (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) {V W : SmallEtale B S hS Y.1} (k : V ⟶ W) :
    representablePullbackMap B S hS f hf k =
      Functor.relativelyRepresentable.pullbackMap hf V.1.hom W.1.hom k.hom.left
        (CostructuredArrow.w k.hom) :=
  rfl

/-- Small-chart base change acts on morphisms by the generic base change of a morphism of
charts. -/
theorem smallBaseChange_map_pullbackMap (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) {V W : SmallEtale B S hS Y.1} (k : V ⟶ W) :
    ((smallBaseChange B S hS f hf).map k).hom.left =
      Functor.relativelyRepresentable.pullbackMap hf V.1.hom W.1.hom k.hom.left
        (CostructuredArrow.w k.hom) :=
  rfl

/-- The composite of two small-chart base changes acts on morphisms by the iterated generic
base change of a morphism of charts. -/
theorem smallBaseChange_comp_map_pullbackMap (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom)
    {V W : SmallEtale B S hS Z.1} (k : V ⟶ W) :
    ((smallBaseChange B S hS g hg ⋙ smallBaseChange B S hS f hf).map k).hom.left =
      Functor.relativelyRepresentable.pullbackMap hf (hg.fst V.1.hom) (hg.fst W.1.hom)
        (Functor.relativelyRepresentable.pullbackMap hg V.1.hom W.1.hom k.hom.left
          (CostructuredArrow.w k.hom))
        (Functor.relativelyRepresentable.pullbackMap_fst hg V.1.hom W.1.hom k.hom.left
          (CostructuredArrow.w k.hom)) :=
  rfl

/-! ### The composition comparison -/

/-- The comparison, at a single étale chart `V` of `Z`, of the base change of `V` along the
composite with the iterated base change: both are chosen fibre products of `V` and `X` over
`Z`, the second by pasting the two chosen cartesian squares. -/
noncomputable def smallBaseChangeCompIso (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom)
    (hfg : yoneda.relativelyRepresentable (f ≫ g).hom) (V : SmallEtale B S hS Z.1) :
    (smallBaseChange B S hS g hg ⋙ smallBaseChange B S hS f hf).obj V ≅
      (smallBaseChange B S hS (f ≫ g) hfg).obj V :=
  (IsEtaleChart B S hS X.1).isoMk (CostructuredArrow.isoMk
    (Functor.relativelyRepresentable.pullbackCompIso hf hg hfg rfl V.1.hom)
    (Functor.relativelyRepresentable.map_pullbackCompHom_fst hf hg hfg rfl V.1.hom))

/-- The comparison at a chart is the generic comparison of chosen base changes. -/
theorem smallBaseChangeCompIso_hom_hom_left (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom)
    (hfg : yoneda.relativelyRepresentable (f ≫ g).hom) (V : SmallEtale B S hS Z.1) :
    (smallBaseChangeCompIso B S hS f g hf hg hfg V).hom.hom.left =
      Functor.relativelyRepresentable.pullbackCompHom hf hg hfg rfl V.1.hom :=
  rfl

/-- The inverse of the comparison at a chart is the generic inverse comparison. -/
theorem smallBaseChangeCompIso_inv_hom_left (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom)
    (hfg : yoneda.relativelyRepresentable (f ≫ g).hom) (V : SmallEtale B S hS Z.1) :
    (smallBaseChangeCompIso B S hS f g hf hg hfg V).inv.hom.left =
      Functor.relativelyRepresentable.pullbackCompInv hf hg hfg rfl V.1.hom :=
  rfl

/-- Base change of étale scheme charts along a composite is canonically isomorphic to the
composite of the two base changes.  This is the analogue, on the small étale sites, of
`AlgebraicGeometry.Space.spacesBaseChange_comp`. -/
noncomputable def smallBaseChange_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom)
    (hfg : yoneda.relativelyRepresentable (f ≫ g).hom) :
    smallBaseChange B S hS g hg ⋙ smallBaseChange B S hS f hf ≅
      smallBaseChange B S hS (f ≫ g) hfg :=
  NatIso.ofComponents (smallBaseChangeCompIso B S hS f g hf hg hfg) (fun {V W} k => by
    refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ ?_)
    rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
      CostructuredArrow.comp_left, CostructuredArrow.comp_left,
      smallBaseChange_comp_map_pullbackMap B S hS f g hf hg k,
      smallBaseChangeCompIso_hom_hom_left B S hS f g hf hg hfg W,
      smallBaseChangeCompIso_hom_hom_left B S hS f g hf hg hfg V,
      smallBaseChange_map_pullbackMap B S hS (f ≫ g) hfg k]
    exact Functor.relativelyRepresentable.pullbackMap_pullbackCompHom hf hg hfg rfl
      V.1.hom W.1.hom k.hom.left (CostructuredArrow.w k.hom))

/-- The composition comparison is compatible with the cartesian projections to the original
chart, which is what pins it down. -/
theorem smallBaseChange_comp_projection (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom)
    (hfg : yoneda.relativelyRepresentable (f ≫ g).hom) (V : SmallEtale B S hS Z.1) :
    (SmallEtale.toOver B S hS X.1).map
          ((smallBaseChange_comp B S hS f g hf hg hfg).hom.app V) ≫
        (smallBaseChangeProjection B S hS (f ≫ g) hfg).app V =
      (smallBaseChangeProjection B S hS f hf).app ((smallBaseChange B S hS g hg).obj V) ≫
        (smallBaseChangeProjection B S hS g hg).app V :=
  Functor.relativelyRepresentable.pullbackCompHom_snd hf hg hfg rfl V.1.hom

/-- The same compatibility for the inverse of the composition comparison. -/
theorem smallBaseChange_comp_inv_projection (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom)
    (hfg : yoneda.relativelyRepresentable (f ≫ g).hom) (V : SmallEtale B S hS Z.1) :
    (SmallEtale.toOver B S hS X.1).map
          ((smallBaseChange_comp B S hS f g hf hg hfg).inv.app V) ≫
        ((smallBaseChangeProjection B S hS f hf).app
            ((smallBaseChange B S hS g hg).obj V) ≫
          (smallBaseChangeProjection B S hS g hg).app V) =
      (smallBaseChangeProjection B S hS (f ≫ g) hfg).app V :=
  Functor.relativelyRepresentable.pullbackCompInv_snd hf hg hfg rfl V.1.hom

/-- The inverse of the composition comparison, read at a chart. -/
theorem smallBaseChange_comp_inv_app_hom_left (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom)
    (hfg : yoneda.relativelyRepresentable (f ≫ g).hom) (V : SmallEtale B S hS Z.1) :
    ((smallBaseChange_comp B S hS f g hf hg hfg).inv.app V).hom.left =
      Functor.relativelyRepresentable.pullbackCompInv hf hg hfg rfl V.1.hom :=
  rfl

/-! ### Compatibility with the structure maps -/

/-- `AlgebraicGeometry.BigFppfOver.commStructurePresheaf` as a presheaf of not necessarily
commutative rings, the form in which sheaves of modules consume it. -/
noncomputable abbrev bigFppfRingSections : (BigFppfOver B S hS)ᵒᵖ ⥤ RingCat.{u} :=
  BigFppfOver.commStructurePresheaf B S hS ⋙ forget₂ CommRingCat.{u} RingCat.{u}

/-- The structure map of small-chart base change on a chart is pullback of regular functions
along the cartesian projection. -/
theorem smallBaseChangeSharpCommRingCat_app (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : (SmallEtale B S hS Y.1)ᵒᵖ) :
    (smallBaseChangeSharpCommRingCat B S hS f hf).hom.app V =
      (BigFppfOver.commStructurePresheaf B S hS).map (hf.snd V.unop.1.hom).op :=
  rfl

/-- `AlgebraicGeometry.Space.smallBaseChangeSharpCommRingCat_app` in the form in which sheaves
of modules consume it. -/
theorem smallBaseChangeSharp_app (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
    (V : (SmallEtale B S hS Y.1)ᵒᵖ) :
    (smallBaseChangeSharp B S hS f hf).hom.app V =
      (bigFppfRingSections B S hS).map (hf.snd V.unop.1.hom).op :=
  rfl

/-- Restriction in the structure sheaf of a small étale site is restriction of regular
functions along the underlying morphism of the big fppf site. -/
theorem structureSheaf_map_eq (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) {V W : SmallEtale B S hS F} (k : V ⟶ W) :
    (structureSheaf B S hS F hF).obj.map k.op =
      (BigFppfOver.commStructurePresheaf B S hS).map k.hom.left.op :=
  rfl

/-- `AlgebraicGeometry.Space.structureSheaf_map_eq` for the sheaf of not necessarily
commutative rings. -/
theorem smallEtaleRingSheaf_map (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) {V W : SmallEtale B S hS F} (k : V ⟶ W) :
    (smallEtaleRingSheaf B S hS F hF).obj.map k.op =
      (bigFppfRingSections B S hS).map k.hom.left.op :=
  rfl

/-- The structure map of the inner base change, pushed forward along the outer one, read on a
chart of `Z`: it is pullback of regular functions along the inner cartesian projection over
the outer base-changed chart. -/
theorem smallBaseChangeSharpCommRingCat_pushforward_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom)
    (V : (SmallEtale B S hS Z.1)ᵒᵖ) :
    (((smallBaseChange B S hS g hg).sheafPushforwardContinuous CommRingCat.{u}
            (SmallEtale.topology B S hS Z.1) (SmallEtale.topology B S hS Y.1)).map
          (smallBaseChangeSharpCommRingCat B S hS f hf)).hom.app V =
      (BigFppfOver.commStructurePresheaf B S hS).map (hf.snd (hg.fst V.unop.1.hom)).op :=
  rfl

/-- `AlgebraicGeometry.Space.smallBaseChangeSharpCommRingCat_pushforward_app` for the sheaves
of not necessarily commutative rings. -/
theorem smallBaseChangeSharp_pushforward_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom)
    (V : (SmallEtale B S hS Z.1)ᵒᵖ) :
    (((smallBaseChange B S hS g hg).sheafPushforwardContinuous RingCat.{u}
            (SmallEtale.topology B S hS Z.1) (SmallEtale.topology B S hS Y.1)).map
          (smallBaseChangeSharp B S hS f hf)).hom.app V =
      (bigFppfRingSections B S hS).map (hf.snd (hg.fst V.unop.1.hom)).op :=
  rfl

/-- The projection of the composite base change factors through the two projections and the
inverse comparison, after applying any functor on the big fppf site. -/
private theorem map_snd_comp_eq_map_comp {C : Type*} [Category C]
    (P : (BigFppfOver B S hS)ᵒᵖ ⥤ C) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom)
    (hfg : yoneda.relativelyRepresentable (f ≫ g).hom) (V : SmallEtale B S hS Z.1) :
    P.map (hfg.snd V.1.hom).op =
      P.map (hg.snd V.1.hom).op ≫ P.map (hf.snd (hg.fst V.1.hom)).op ≫
        P.map (Functor.relativelyRepresentable.pullbackCompInv hf hg hfg rfl V.1.hom).op := by
  rw [← Category.assoc, ← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp]
  exact congrArg P.map (congrArg Quiver.Hom.op
    (Functor.relativelyRepresentable.pullbackCompInv_snd hf hg hfg rfl V.1.hom).symm)

/-- The composite of the two base changes is continuous for the small étale topologies. -/
private theorem isContinuous_smallBaseChange_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom) :
    (smallBaseChange B S hS g hg ⋙ smallBaseChange B S hS f hf).IsContinuous
      (SmallEtale.topology B S hS Z.1) (SmallEtale.topology B S hS X.1) :=
  Functor.isContinuous_comp (smallBaseChange B S hS g hg) (smallBaseChange B S hS f hf)
    (SmallEtale.topology B S hS Z.1) (SmallEtale.topology B S hS Y.1)
    (SmallEtale.topology B S hS X.1)

/-- The structure map of small-chart base change along a composite is the composite of the two
structure maps, read through the composition comparison
`AlgebraicGeometry.Space.smallBaseChange_comp`, as morphisms of sheaves of commutative
rings. -/
theorem smallBaseChangeSharpCommRingCat_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom)
    (hfg : yoneda.relativelyRepresentable (f ≫ g).hom) :
    smallBaseChangeSharpCommRingCat B S hS (f ≫ g) hfg =
      smallBaseChangeSharpCommRingCat B S hS g hg ≫
        ((smallBaseChange B S hS g hg).sheafPushforwardContinuous CommRingCat.{u}
              (SmallEtale.topology B S hS Z.1) (SmallEtale.topology B S hS Y.1)).map
            (smallBaseChangeSharpCommRingCat B S hS f hf) ≫
          (Functor.sheafPushforwardContinuousComp'
              (smallBaseChange_comp B S hS f g hf hg hfg) CommRingCat.{u}
              (SmallEtale.topology B S hS Z.1) (SmallEtale.topology B S hS Y.1)
              (SmallEtale.topology B S hS X.1)).hom.app
            (structureSheaf B S hS X.1 X.2) := by
  have := isContinuous_smallBaseChange_comp B S hS f g hf hg
  rw [Functor.sheafPushforwardContinuousComp'_hom_eq]
  exact Sheaf.hom_ext (NatTrans.ext (funext fun V =>
    map_snd_comp_eq_map_comp B S hS (BigFppfOver.commStructurePresheaf B S hS) f g hf hg hfg
      V.unop))

/-- The structure map `AlgebraicGeometry.Space.smallBaseChangeSharp` of small-chart base change
along a composite is the composite of the two structure maps, read through the composition
comparison `AlgebraicGeometry.Space.smallBaseChange_comp`. -/
theorem smallBaseChangeSharp_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom)
    (hfg : yoneda.relativelyRepresentable (f ≫ g).hom) :
    smallBaseChangeSharp B S hS (f ≫ g) hfg =
      smallBaseChangeSharp B S hS g hg ≫
        ((smallBaseChange B S hS g hg).sheafPushforwardContinuous RingCat.{u}
              (SmallEtale.topology B S hS Z.1) (SmallEtale.topology B S hS Y.1)).map
            (smallBaseChangeSharp B S hS f hf) ≫
          (Functor.sheafPushforwardContinuousComp'
              (smallBaseChange_comp B S hS f g hf hg hfg) RingCat.{u}
              (SmallEtale.topology B S hS Z.1) (SmallEtale.topology B S hS Y.1)
              (SmallEtale.topology B S hS X.1)).hom.app
            (smallEtaleRingSheaf B S hS X.1 X.2) := by
  have := isContinuous_smallBaseChange_comp B S hS f g hf hg
  rw [Functor.sheafPushforwardContinuousComp'_hom_eq]
  exact Sheaf.hom_ext (NatTrans.ext (funext fun V =>
    map_snd_comp_eq_map_comp B S hS (bigFppfRingSections B S hS) f g hf hg hfg V.unop))

end AlgebraicGeometry.Space

end
