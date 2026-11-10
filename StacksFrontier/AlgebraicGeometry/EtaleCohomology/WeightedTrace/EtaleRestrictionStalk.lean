module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroStalk
public import StacksFrontier.AlgebraicGeometry.Etale.FiniteSupportStalk
public import StacksCore.Tactic.StacksAttribute

/-!
# Pushing a stalk on an étale cover down to the base

Let `j : U ⟶ X` be an étale morphism, viewed as an object of the small étale site of `X`, let
`s` be a geometric point of `X` and let `p` be a lift of `s` to `U`. An étale neighbourhood
`W ⟶ U` of the geometric point of `U` determined by `p` is an étale neighbourhood of `s` in
`X`, by composition with `j`, and the lift is unchanged: this is
`AlgebraicGeometry.liftNeighborhoods`, on objects `AlgebraicGeometry.pushLift`. Consequently a
morphism of sheaves `α : G ⟶ j^{-1}H` — equivalently, by Stacks 03S3, a family of maps
`G(W) ⟶ H(W)` for `W` étale over `U` — induces a map on stalks

`G_p ⟶ H_s`,  `germ_{W, w}(a) ↦ germ_{jW, w}(α(a))`,

with no comparison of neighbourhoods needed in either direction. This file constructs that map
and records its two properties: it is functorial in `H`, and for the unit of the
extension-by-zero adjunction it composes with the counit to the map induced by the identity.

The second of these is the germ-level form of the triangle identity of `j_! ⊣ j^{-1}`, and it
is the half of Stacks 0GL4 which says that the counit *acts as the identity on each summand* of
the stalk decomposition of Stacks 03S5.

## Main definitions

* `AlgebraicGeometry.pushStalkMap` — the induced map on stalks `G_p ⟶ H_s`.
* `AlgebraicGeometry.extensionUnitStalkMap` — the case of the unit of `j_! ⊣ j^{-1}`: the map
  `G_p ⟶ (j_!G)_s` sending a germ to the germ of its image in the extension by zero. This is
  the inclusion of the summand indexed by `p` in the stalk decomposition of Stacks 03S5.
* `AlgebraicGeometry.restrictionStalkMap` — the case of the identity of `j^{-1}H`: the
  comparison `(j^{-1}H)_p ⟶ H_s`.

## Main results

* `AlgebraicGeometry.pushStalkMap_germ` — the germ formula, which characterises the map.
* `AlgebraicGeometry.pushStalkMap_comp` — functoriality in the sheaf on `X`.
* `AlgebraicGeometry.extensionUnitStalkMap_comp_counit` — **the triangle identity on stalks.**
  The composite of the unit map `(j^{-1}H)_p ⟶ (j_! j^{-1} H)_s` with the stalk map of the
  counit of `j_! ⊣ j^{-1}` is the comparison `(j^{-1}H)_p ⟶ H_s`.

## Implementation notes

The map is built as a `CategoryTheory.Limits.colimit.desc`, the cocone being the family of
germs at the pushed-forward neighbourhoods; its naturality is the naturality of `α` followed by
the transition of the colimit computing `H_s`, the two lifts being compatible by
`AlgebraicGeometry.pushLift_map`. It is *not* built as `CategoryTheory.Limits.colimit.pre` along
`AlgebraicGeometry.liftNeighborhoods`, which would land in the stalk at the geometric point
`p ∘ j` of `X` rather than at `s`; those two geometric points are equal, but only
propositionally, and carrying the resulting `eqToHom` through every germ computation is worse
than proving one cocone naturality.

No hypothesis beyond étaleness of `j` enters, and in particular the map is not claimed to be an
isomorphism here; that it is one for `α` the identity is the content of Stacks 03Q1 for `j^{-1}`
and is proved elsewhere.

## References

* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
* [Stacks Project, Tag 03S5](https://stacks.math.columbia.edu/tag/03S5)
* [Stacks Project, Tag 0GL4](https://stacks.math.columbia.edu/tag/0GL4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (U : SmallEtale B X hX)
  (s : GeometricPoint X) (p : geometricPointLifts B X hX U s)

section PushStalk

variable (H : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1})
  (G : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1})

/-- The cocone of germs at the pushed-forward étale neighbourhoods, whose colimit map is
`AlgebraicGeometry.pushStalkMap`. -/
public def pushStalkCocone (α : G ⟶ (abelianRestriction B X hX U).obj H) :
    Cocone (SmallEtale.etaleStalkDiagram B U.obj.left.1 U.obj.left.property
      (geometricPointOfLift B X hX U s p) G.obj) where
  pt := etaleStalk B X hX s H.obj
  ι :=
    { app := fun N => α.hom.app (op N.unop.1) ≫
        colimit.ι (SmallEtale.etaleStalkDiagram B X hX s H.obj)
          (op (Functor.elementsMk _ ((smallEtalePostcompose B X hX U).obj N.unop.1)
            (pushLift B X hX U s N.unop.1 p N.unop.2)))
      naturality := by
        intro N M f
        let AM : (geometricPointFiber B X hX s).Elements :=
          Functor.elementsMk _ ((smallEtalePostcompose B X hX U).obj M.unop.1)
            (pushLift B X hX U s M.unop.1 p M.unop.2)
        let AN : (geometricPointFiber B X hX s).Elements :=
          Functor.elementsMk _ ((smallEtalePostcompose B X hX U).obj N.unop.1)
            (pushLift B X hX U s N.unop.1 p N.unop.2)
        let m : AM ⟶ AN :=
          ⟨(smallEtalePostcompose B X hX U).map f.unop.1,
            (pushLift_map B X hX U s f.unop.1 p M.unop.2).trans
              (congrArg (pushLift B X hX U s N.unop.1 p) f.unop.2)⟩
        have hw := colimit.w (SmallEtale.etaleStalkDiagram B X hX s H.obj) m.op
        have hα := α.hom.naturality (f.unop.1).op
        refine Eq.trans ?_ (Category.comp_id _).symm
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (fun z => z ≫ colimit.ι
              (SmallEtale.etaleStalkDiagram B X hX s H.obj) (op AM)) hα).trans
            ((Category.assoc _ _ _).trans
              (congrArg (fun z => α.hom.app (op N.unop.1) ≫ z) hw))) }

/-- **The stalk map induced by a morphism `G ⟶ j^{-1}H` along a lift of a geometric point.**
An étale neighbourhood of the lift `p` of `s` is an étale neighbourhood of `s`, so the germ at
`p` of a section of `G` has a germ at `s` of its image in `H`. -/
public def pushStalkMap (α : G ⟶ (abelianRestriction B X hX U).obj H) :
    etaleStalk B U.obj.left.1 U.obj.left.property
        (geometricPointOfLift B X hX U s p) G.obj ⟶
      etaleStalk B X hX s H.obj :=
  colimit.desc _ (pushStalkCocone B X hX U s p H G α)

/-- The germ formula characterising `AlgebraicGeometry.pushStalkMap`: the germ at the lift of a
section of `G` over an étale neighbourhood `W ⟶ U` goes to the germ at `s` of its image under
`α`, over `W` viewed as an étale neighbourhood of `s` in `X`. -/
public theorem pushStalkMap_germ (α : G ⟶ (abelianRestriction B X hX U).obj H)
    (W : SmallEtale B U.obj.left.1 U.obj.left.property)
    (w : (geometricPointFiber B U.obj.left.1 U.obj.left.property
      (geometricPointOfLift B X hX U s p)).obj W) :
    colimit.ι (SmallEtale.etaleStalkDiagram B U.obj.left.1 U.obj.left.property
          (geometricPointOfLift B X hX U s p) G.obj) (op (Functor.elementsMk _ W w)) ≫
        pushStalkMap B X hX U s p H G α =
      α.hom.app (op W) ≫
        colimit.ι (SmallEtale.etaleStalkDiagram B X hX s H.obj)
          (op (Functor.elementsMk _ ((smallEtalePostcompose B X hX U).obj W)
            (pushLift B X hX U s W p w))) :=
  colimit.ι_desc (pushStalkCocone B X hX U s p H G α) (op (Functor.elementsMk _ W w))

/-- The germ formula of `AlgebraicGeometry.pushStalkMap`, read on an individual germ. -/
public theorem pushStalkMap_etaleGerm (α : G ⟶ (abelianRestriction B X hX U).obj H)
    (W : SmallEtale B U.obj.left.1 U.obj.left.property)
    (w : (geometricPointFiber B U.obj.left.1 U.obj.left.property
      (geometricPointOfLift B X hX U s p)).obj W) (a : G.obj.obj (op W)) :
    pushStalkMap B X hX U s p H G α
        (SmallEtale.etaleGerm B U.obj.left.1 U.obj.left.property
          (geometricPointOfLift B X hX U s p) G.obj W w a) =
      SmallEtale.etaleGerm B X hX s H.obj ((smallEtalePostcompose B X hX U).obj W)
        (pushLift B X hX U s W p w) (α.hom.app (op W) a) :=
  (ConcreteCategory.comp_apply _ _ a).symm.trans
    ((ConcreteCategory.congr_hom (pushStalkMap_germ B X hX U s p H G α W w) a).trans
      (ConcreteCategory.comp_apply _ _ a))

end PushStalk

section Functoriality

variable {H H' : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}}
  (G : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1})

/-- **Functoriality of the induced stalk map in the sheaf on `X`.** Composing with the map
induced on the stalk at `s` by `β : H ⟶ H'` is the same as composing `α` with the restriction
of `β`. -/
public theorem pushStalkMap_comp (α : G ⟶ (abelianRestriction B X hX U).obj H) (β : H ⟶ H') :
    pushStalkMap B X hX U s p H G α ≫
        colim.map (Functor.whiskerLeft
          (Functor.Elements.π (geometricPointFiber B X hX s)).op β.1) =
      pushStalkMap B X hX U s p H' G
        (α ≫ (abelianRestriction B X hX U).map β) := by
  refine colimit.hom_ext fun N => ?_
  have hleft := pushStalkMap_germ B X hX U s p H G α N.unop.1 N.unop.2
  have hright := pushStalkMap_germ B X hX U s p H' G
    (α ≫ (abelianRestriction B X hX U).map β) N.unop.1 N.unop.2
  have hι := colimit.ι_map (Functor.whiskerLeft
      (Functor.Elements.π (geometricPointFiber B X hX s)).op β.1)
    (op (Functor.elementsMk _ ((smallEtalePostcompose B X hX U).obj N.unop.1)
      (pushLift B X hX U s N.unop.1 p N.unop.2) :
      (geometricPointFiber B X hX s).Elements))
  refine Eq.trans ?_ hright.symm
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ colim.map (Functor.whiskerLeft
        (Functor.Elements.π (geometricPointFiber B X hX s)).op β.1)) hleft).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun z => α.hom.app (op N.unop.1) ≫ z) hι).trans
          (Category.assoc _ _ _).symm)))

end Functoriality

section Special

variable (H : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1})
  (G : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1})

/-- **The inclusion of a summand of the stalk decomposition of Stacks 03S5.** The map from the
stalk of `G` at a lift `p` of `s` to the stalk of the extension by zero `j_!G` at `s`, sending a
germ to the germ of its image under the unit of `j_! ⊣ j^{-1}`. -/
public def extensionUnitStalkMap :
    etaleStalk B U.obj.left.1 U.obj.left.property
        (geometricPointOfLift B X hX U s p) G.obj ⟶
      etaleStalk B X hX s ((abelianExtensionByZero B X hX U).obj G).obj :=
  pushStalkMap B X hX U s p ((abelianExtensionByZero B X hX U).obj G) G
    ((abelianExtensionByZeroAdjunction B X hX U).unit.app G)

/-- **Stacks 03Q1 for the restriction along an étale morphism, as a map.** The comparison from
the stalk of `j^{-1}H` at a lift `p` of `s` to the stalk of `H` at `s`: an étale neighbourhood
of `p` in `U` is an étale neighbourhood of `s` in `X`, on which the sections of `j^{-1}H` are
the sections of `H`. -/
public def restrictionStalkMap :
    etaleStalk B U.obj.left.1 U.obj.left.property (geometricPointOfLift B X hX U s p)
        ((abelianRestriction B X hX U).obj H).obj ⟶
      etaleStalk B X hX s H.obj :=
  pushStalkMap B X hX U s p H ((abelianRestriction B X hX U).obj H) (𝟙 _)

/-- The germ formula for the comparison `(j^{-1}H)_p ⟶ H_s`: the germ of a section of `H` over
an étale neighbourhood `W ⟶ U` of `p`, read as a germ of `j^{-1}H` at `p`, is its germ at `s`
over `W` viewed as étale over `X`. -/
public theorem restrictionStalkMap_germ
    (W : SmallEtale B U.obj.left.1 U.obj.left.property)
    (w : (geometricPointFiber B U.obj.left.1 U.obj.left.property
      (geometricPointOfLift B X hX U s p)).obj W) :
    colimit.ι (SmallEtale.etaleStalkDiagram B U.obj.left.1 U.obj.left.property
          (geometricPointOfLift B X hX U s p)
          ((abelianRestriction B X hX U).obj H).obj) (op (Functor.elementsMk _ W w)) ≫
        restrictionStalkMap B X hX U s p H =
      colimit.ι (SmallEtale.etaleStalkDiagram B X hX s H.obj)
        (op (Functor.elementsMk _ ((smallEtalePostcompose B X hX U).obj W)
          (pushLift B X hX U s W p w))) :=
  (pushStalkMap_germ B X hX U s p H ((abelianRestriction B X hX U).obj H) (𝟙 _) W w).trans
    (Category.id_comp _)

/-- **The triangle identity of `j_! ⊣ j^{-1}` on stalks — the summandwise half of Stacks
0GL4.** The stalk map of the counit `j_! j^{-1}H ⟶ H` carries the summand of the stalk
decomposition of Stacks 03S5 indexed by a lift `p` of `s` to the stalk of `H` at `s` by the
comparison of Stacks 03Q1, i.e. by the identity on each summand. -/
public theorem extensionUnitStalkMap_comp_counit :
    extensionUnitStalkMap B X hX U s p ((abelianRestriction B X hX U).obj H) ≫
        colim.map (Functor.whiskerLeft
          (Functor.Elements.π (geometricPointFiber B X hX s)).op
          ((abelianExtensionByZeroAdjunction B X hX U).counit.app H).1) =
      restrictionStalkMap B X hX U s p H :=
  (pushStalkMap_comp B X hX U s p ((abelianRestriction B X hX U).obj H)
    ((abelianExtensionByZeroAdjunction B X hX U).unit.app
      ((abelianRestriction B X hX U).obj H))
    ((abelianExtensionByZeroAdjunction B X hX U).counit.app H)).trans <|
    congrArg (pushStalkMap B X hX U s p H ((abelianRestriction B X hX U).obj H))
      ((abelianExtensionByZeroAdjunction B X hX U).right_triangle_components H)

end Special

end AlgebraicGeometry

end
