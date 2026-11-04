module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.ProjectionTwoArrow
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.ReverseEffective
public import StacksFrontier.CategoryTheory.Sites.Stackification.UniversalPropertyGroupoid

/-!
# The quotient stack is a two-coequalizer of its presentation (Stacks 044U)

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `B` over a
scheme `S` of a big fppf site, let `[U/R]` be its quotient stack and let `π : 𝒮_U ⟶ [U/R]` be the
canonical projection of Stacks 044R. Stacks 044S makes the square

    𝒮_R ---s---> 𝒮_U
     |            |
     t            π
     v            v
    𝒮_U ---π---> [U/R]

2-commute. Stacks 044U is the universal property of that 2-commutative square: given a stack in
groupoids `X` over the big fppf site, a 1-morphism `f : 𝒮_U ⟶ X` and a 2-morphism
`β : s ∘ f ⟶ t ∘ f`, if `β` satisfies the composition cocycle on the arrows of `R` then `f`
*descends*: there are a 1-morphism `g : [U/R] ⟶ X` and a 2-isomorphism `α : π ∘ g ≅ f` which carry
the canonical 2-morphism of Stacks 044S to `β`.

## Main definitions

* `AlgebraicGeometry.Stack.IsCocycle`: the composition cocycle condition on a 2-morphism
  `s ∘ f ⟶ t ∘ f`, evaluated on the algebraic space of composable pairs of arrows.

## Main results

* `AlgebraicGeometry.Stack.quotientStack_desc`: **Stacks 044U**, the descent — a cocyclic
  2-morphism out of the object space yields a 1-morphism from the quotient stack, a comparison
  2-isomorphism on the object space, and compatibility with the canonical 2-morphism of
  Stacks 044S.
* `AlgebraicGeometry.Stack.quotientStack_desc_of_extendsAlongStackification`: the same descent on
  the hypothesis that 1-morphisms out of the presentation of the quotient extend along the
  stackification, which asks only that `X` be fibered in groupoids and leaves its universes
  unconstrained.

## Implementation notes

The cocycle condition is evaluated on the algebraic space of composable pairs of arrows, through
the comparison `AlgebraicGeometry.composableToPullback` with the presheaf fibre product. The three
equalities of endpoints that it carries are recorded explicitly, as existentials inside the
condition, because the 1-morphisms attached to the structure maps by Stacks 0458 are given
abstractly and their values on objects are pinned only up to the equalities that
`AlgebraicGeometry.Stack.associatedMap` records; they are the usual source, intermediate and
target identifications for a composable pair.

The construction is in three steps. First, the 2-morphism `β` is read as an action of the arrows
of `R` on the fibres of `f` (`arrowImage` below); the cocycle condition makes that action
functorial on each evaluated groupoid, and naturality of `β` makes it compatible with base change,
which together assemble a 1-morphism out of the *pointwise* groupoid fibration of `G` — and hence,
along the universe lift of its morphisms, out of the presentation
`AlgebraicGeometry.Stack.quotientPrestack` that the quotient stack is the stackification of.
Second, that 1-morphism is extended along `AlgebraicGeometry.Stack.toQuotientStack` to a
1-morphism out of the quotient stack, with a 2-isomorphism on the presentation whose components
are vertical. Third, the comparison on the object space is read off that 2-isomorphism through the
pointwise description of the projection (Stacks 044R) and of the canonical 2-morphism
(Stacks 044S).

The second step is the universal property of the stackification, **Stacks 0436**, for the pair
`AlgebraicGeometry.Stack.toQuotientStack` and `X`; it is
`CategoryTheory.Functor.Stackification.extendGroupoid` with
`CategoryTheory.Functor.Stackification.extendGroupoid_comp_eq`,
`CategoryTheory.Functor.Stackification.unitGroupoid` and
`CategoryTheory.Functor.Stackification.isHomLift_unitGroupoid_app`, at the two clauses of
Stacks 02ZN which exhibit the quotient as the stackification of its presentation. The descent
condition they consume is `CategoryTheory.Functor.IsStack`, and the hypothesis `X.p` is a stack in
groupoids in the sense of Stacks 02ZI supplies it through
`CategoryTheory.Functor.isStack_of_isStackInGroupoids` at the index universe `u + 1`, which is
`max u₁ v₁` for the big fppf category over `S`: its objects lie in `Type (u + 1)` and its
morphisms in `Type u`.

The universes of `X` are unconstrained. That takes some arranging, because the quotient stack is
the stackification of a fibration whose morphisms were raised one universe by
`CategoryTheory.ULiftHom`, so its total category has morphisms in `Type (u + 1)` while those of
`X` lie in an unrelated universe; the hom universe of the target of the extension is therefore
independent of the hom universe shared by the stackification and its presentation, which is where
the map of morphism presheaves of Stacks 042V ties them together.

Only that second step uses the stack hypothesis on `X`, so the descent is also recorded in the
form `AlgebraicGeometry.Stack.quotientStack_desc_of_extendsAlongStackification`, which takes the
extension as a hypothesis and asks of `X` only that it be fibered in groupoids; the unconditional
statement is that one applied to
`AlgebraicGeometry.Stack.exists_extension_along_toQuotientStack`.

The conclusion keeps the comparison 2-isomorphism as data rather than asserting only that some
1-morphism exists, since the compatibility with the 2-morphism of Stacks 044S is a statement
about that comparison.

## References

* [Stacks Project, Tag 02ZI](https://stacks.math.columbia.edu/tag/02ZI)
* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 0436](https://stacks.math.columbia.edu/tag/0436)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 044S](https://stacks.math.columbia.edu/tag/044S)
* [Stacks Project, Tag 044U](https://stacks.math.columbia.edu/tag/044U)
* [Stacks Project, Tag 0458](https://stacks.math.columbia.edu/tag/0458)
* [Stacks Project, Tag 06K3](https://stacks.math.columbia.edu/tag/06K3)
* [Stacks Project, Tag 06KB](https://stacks.math.columbia.edu/tag/06KB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- The 1-morphism attached to a map of presheaves by Stacks 0458 takes a point of the fibred
category of the source to the point of the fibred category of the target with the same base and
with fibre the value of the map there. The subtype of `AlgebraicGeometry.Stack.associatedMap`
records that value only up to `HEq`; the equality over the base comes from the based-functor
condition, and together they upgrade it to an equality of objects. -/
private theorem associatedMap_obj_eq
    {F H : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (a : F ⟶ H) (x : (fibredCategory C S hS F).val.obj) :
    ((associatedMap C S hS a).1.hom).obj x =
      ⟨x.base, Discrete.mk (a.app (Opposite.op x.base) (Discrete.as x.fiber))⟩ := by
  let K := (associatedMap C S hS a).1.hom
  cases x with
  | mk base fiber =>
    generalize hy : K.obj ⟨base, fiber⟩ = y
    cases y with
    | mk base' fiber' =>
      have hb : base' = base := by
        have hh := BasedFunctor.w_obj K ⟨base, fiber⟩
        rw [hy] at hh
        exact hh
      subst base'
      have hf := (associatedMap C S hS a).property ⟨base, fiber⟩
      rw [hy] at hf
      change HEq fiber' (Discrete.mk (a.app (Opposite.op base) (Discrete.as fiber))) at hf
      cases eq_of_heq hf
      rfl

/-- **Stacks 044U**, the cocycle condition. A 2-morphism `β : s ∘ f ⟶ t ∘ f` out of the fibred
category of the object space of a groupoid in algebraic spaces *respects composition* when, at
every point of the algebraic space of composable pairs of arrows, the component of `β` at the
composite is the composite of its components at the two factors.

The three equalities of endpoints are part of the condition rather than derived from it, because
the 1-morphisms attached to the structure maps by Stacks 0458 are given abstractly: they are the
source, intermediate and target identifications for a composable pair. -/
public def IsCocycle
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (X : BasedCategory (BigFppfOver C S hS))
    (f : BasedFunctor (fibredCategory C S hS G.objects.obj).val X)
    (β : BasedFunctor.comp
      (associatedMap C S hS G.source.hom).1.hom f ⟶
      BasedFunctor.comp
        (associatedMap C S hS G.target.hom).1.hom f) : Prop :=
  let P := AlgebraicSpaces.fiberProduct C S hS G.source G.target
  let a₀ := (associatedMap C S hS
    (pullback.fst G.source.hom G.target.hom)).1.hom
  let a₁ := (associatedMap C S hS
    (pullback.snd G.source.hom G.target.hom)).1.hom
  let ac := (associatedMap C S hS G.comp.hom).1.hom
  let Fs := BasedFunctor.comp
    (associatedMap C S hS G.source.hom).1.hom f
  let Ft := BasedFunctor.comp
    (associatedMap C S hS G.target.hom).1.hom f
  ∀ x : (fibredCategory C S hS P.obj).val.obj,
    ∃ (h₁ : (BasedFunctor.comp ac Fs).obj x =
        (BasedFunctor.comp a₁ Fs).obj x)
      (h₂ : (BasedFunctor.comp a₁ Ft).obj x =
        (BasedFunctor.comp a₀ Fs).obj x)
      (h₃ : (BasedFunctor.comp a₀ Ft).obj x =
        (BasedFunctor.comp ac Ft).obj x),
      (BasedCategory.whiskerLeft ac β).app x =
        eqToHom h₁ ≫ (BasedCategory.whiskerLeft a₁ β).app x ≫
          eqToHom h₂ ≫ (BasedCategory.whiskerLeft a₀ β).app x ≫
            eqToHom h₃

section CocycleFunctor

/- The fibres of `fibredCategory` are discrete groupoids reached through
`CategoryTheory.typeToGrpd`, and the Grothendieck construction indexing them goes through
`CategoryTheory.Functor.toPseudofunctor'` and `CategoryTheory.BasedCategory.ofFunctor`; none of
these is unfolded at `implicit` transparency, so a goal naming both a point and its `base` or
`fiber` is not type-correct there and `rw` and `simp` decline it. Naming that chain — the same
idiom as in `Quotient/ProjectionTwoArrow.lean` and
`StacksFrontier/CategoryTheory/Sites/Stack/IsomPresheaf.lean` — is what lets the ordinary tactics
see through it. -/
attribute [local implicit_reducible] fibredCategory typeToGrpd
  Bicategory.InducedBicategory BasedCategory.ofFunctor
  CategoryTheory.Functor.toPseudofunctor'
  CategoryTheory.pseudofunctorOfIsLocallyDiscrete Quiver.Hom.toLoc
  CategoryTheory.Functor.Fiber CategoryTheory.Functor.Fiber.fiberInclusion
  Grpd.forgetToCat Grpd.of Pseudofunctor.CoGrothendieck.forget
  BasedFunctor.comp BasedCategory.whiskerLeft BasedCategory.whiskerRight
  AlgebraicSpaces.fiberProduct GroupoidInAlgebraicSpaces.toGroupoidInFunctors
  Pseudofunctor.CoGrothendieck.category Pseudofunctor.CoGrothendieck.categoryStruct

/-- A point of the fibred category attached to a presheaf: a test object of the site together with
an element of the value of the presheaf there. -/
private abbrev point
    (F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u)
    (T : BigFppfOver C S hS) (x : F.obj (Opposite.op T)) :
    (fibredCategory C S hS F).val.obj := ⟨T, Discrete.mk x⟩

/-- The 1-morphism attached to a map of presheaves takes a point to the point named by the value
of the map there. -/
private lemma associatedMap_point
    {F H : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (a : F ⟶ H) (T : BigFppfOver C S hS) (x : F.obj (Opposite.op T)) :
    (associatedMap C S hS a).1.hom.obj (point F T x) =
      point H T (a.app (Opposite.op T) x) := associatedMap_obj_eq a _

/-- The 1-morphism attached to a map of presheaves takes a point to the point named by any value
equal to the value of the map there. -/
private lemma associatedMap_point_eq
    {F H : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (a : F ⟶ H) (T : BigFppfOver C S hS) {x : F.obj (Opposite.op T)}
    {y : H.obj (Opposite.op T)} (h : a.app (Opposite.op T) x = y) :
    (associatedMap C S hS a).1.hom.obj (point F T x) = point H T y :=
  (associatedMap_point a T x).trans (congrArg (point H T) h)

/-- The arrow of points of a presheaf lying over a given arrow of the site, between a point and a
point restricting to it. -/
private def pointHom
    (F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u)
    {T T' : BigFppfOver C S hS} (k : T ⟶ T')
    {x : F.obj (Opposite.op T)} {y : F.obj (Opposite.op T')}
    (h : x = F.map k.op y) : point F T x ⟶ point F T' y where
  base := k
  fiber := eqToHom (congrArg Discrete.mk h)

/-- Between two points of the fibred category attached to a presheaf, an arrow is determined by
its base component: the fibres are discrete. -/
private lemma pointHom_ext
    {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    {x y : (fibredCategory C S hS F).val.obj}
    (a b : x ⟶ y) (h : a.base = b.base) : a = b := by
  apply Pseudofunctor.CoGrothendieck.Hom.ext a b h
  apply @Subsingleton.elim _
    (inferInstanceAs (Subsingleton ((show Discrete (F.obj (Opposite.op x.base)) from x.fiber) ⟶
      Discrete.mk (F.map a.base.op (Discrete.as y.fiber)))))

/-- The canonical arrow between points lies over the arrow of the site it was built from. -/
private lemma pointHom_lift
    (F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u)
    {T T' : BigFppfOver C S hS} (k : T ⟶ T')
    {x : F.obj (Opposite.op T)} {y : F.obj (Opposite.op T')}
    (h : x = F.map k.op y) :
    (fibredCategory C S hS F).val.p.IsHomLift k (pointHom F k h) :=
  IsHomLift.of_fac _ _ _ rfl rfl (by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl)

/-- Two arrows of the fibred category attached to a presheaf lying over the same arrow of the site
are equal. -/
private lemma pointHom_ext_of_lift
    {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    {T T' : BigFppfOver C S hS} (k : T ⟶ T')
    {x y : (fibredCategory C S hS F).val.obj} (a b : x ⟶ y)
    [(fibredCategory C S hS F).val.p.IsHomLift k a]
    [(fibredCategory C S hS F).val.p.IsHomLift k b] : a = b :=
  pointHom_ext a b <| (IsHomLift.fac' (fibredCategory C S hS F).val.p k a).trans
    (IsHomLift.fac' (fibredCategory C S hS F).val.p k b).symm

/-- A 1-morphism over the site carries the canonical arrow between points to the canonical arrow
between their images, conjugated by the identifications of those images. -/
private lemma basedMap_pointHom
    {F H : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (K : BasedFunctor (fibredCategory C S hS F).val
      (fibredCategory C S hS H).val)
    {T T' : BigFppfOver C S hS} (k : T ⟶ T')
    {x : F.obj (Opposite.op T)} {y : F.obj (Opposite.op T')}
    (h : x = F.map k.op y) {x' : H.obj (Opposite.op T)}
    {y' : H.obj (Opposite.op T')}
    (hx : K.obj (point F T x) = point H T x')
    (hy : K.obj (point F T' y) = point H T' y') (h' : x' = H.map k.op y') :
    K.map (pointHom F k h) = eqToHom hx ≫ pointHom H k h' ≫ eqToHom hy.symm := by
  have := pointHom_lift F k h
  have := pointHom_lift H k h'
  exact pointHom_ext _ _ <| (IsHomLift.fac' (fibredCategory C S hS H).val.p k
    (K.map (pointHom F k h))).trans
      (IsHomLift.fac' (fibredCategory C S hS H).val.p k
        (eqToHom hx ≫ pointHom H k h' ≫ eqToHom hy.symm)).symm

variable (G : GroupoidInAlgebraicSpaces C S hS B)
  (X : BasedCategory (BigFppfOver C S hS))
  (f : BasedFunctor (fibredCategory C S hS G.objects.obj).val X)
  (β : BasedFunctor.comp
    (associatedMap C S hS G.source.hom).1.hom f ⟶
    BasedFunctor.comp (associatedMap C S hS G.target.hom).1.hom f)

/-- The action of an arrow of the arrow space on the fibres of `f`: the component of the
2-morphism `β` there, with its source and target transported to the fibres of `f` at the two
prescribed points of the object space. -/
private noncomputable def arrowImage (T : BigFppfOver C S hS)
    {x y : G.objects.obj.obj (Opposite.op T)} (a : G.arrows.obj.obj (Opposite.op T))
    (hs : G.source.hom.app (Opposite.op T) a = x)
    (ht : G.target.hom.app (Opposite.op T) a = y) :
    f.obj (point G.objects.obj T x) ⟶ f.obj (point G.objects.obj T y) :=
  eqToHom (congrArg f.obj (associatedMap_point_eq G.source.hom T hs)).symm ≫
    β.app (point G.arrows.obj T a) ≫
    eqToHom (congrArg f.obj (associatedMap_point_eq G.target.hom T ht))

/-- Naturality of the 2-morphism intertwines this action with restriction along an arrow of the
site. -/
private lemma arrowImage_naturality
    {T T' : BigFppfOver C S hS} (k : T ⟶ T')
    {x y : G.objects.obj.obj (Opposite.op T')}
    (a : G.arrows.obj.obj (Opposite.op T'))
    (hs : G.source.hom.app (Opposite.op T') a = x)
    (ht : G.target.hom.app (Opposite.op T') a = y) :
    arrowImage G X f β T (G.arrows.obj.map k.op a)
        ((NatTrans.naturality_apply G.source.hom k.op a).trans
          (congrArg (G.objects.obj.map k.op) hs))
        ((NatTrans.naturality_apply G.target.hom k.op a).trans
          (congrArg (G.objects.obj.map k.op) ht)) ≫
        f.map (pointHom G.objects.obj k (y := y) rfl) =
      f.map (pointHom G.objects.obj k (y := x) rfl) ≫
        arrowImage G X f β T' a hs ht := by
  let es := associatedMap_point_eq G.source.hom T
    ((NatTrans.naturality_apply G.source.hom k.op a).trans
      (congrArg (G.objects.obj.map k.op) hs))
  let et := associatedMap_point_eq G.target.hom T
    ((NatTrans.naturality_apply G.target.hom k.op a).trans
      (congrArg (G.objects.obj.map k.op) ht))
  let es' := associatedMap_point_eq G.source.hom T' hs
  let et' := associatedMap_point_eq G.target.hom T' ht
  have hn := β.naturality (pointHom G.arrows.obj k (y := a) rfl)
  change f.map (_) ≫ _ = _ ≫ f.map (_) at hn
  rw [basedMap_pointHom _ k rfl es es' rfl,
    basedMap_pointHom _ k rfl et et' rfl] at hn
  simpa only [arrowImage, Functor.map_comp, eqToHom_map, Category.assoc,
    eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Category.id_comp,
    Category.comp_id] using congrArg
      (fun m => eqToHom (congrArg f.obj es).symm ≫ m ≫ eqToHom (congrArg f.obj et')) hn.symm

/-- The cocycle condition makes the action multiplicative: the action of a composite of two arrows
of an evaluated groupoid is the composite of their actions. -/
private lemma arrowImage_comp (hβ : IsCocycle G X f β)
    (T : BigFppfOver C S hS)
    {x y z : G.toGroupoidInFunctors.Evaluation (Opposite.op T)}
    (a : x ⟶ y) (b : y ⟶ z) :
    let e := G.toGroupoidInFunctors.evaluationArrowEquiv (Opposite.op T)
    arrowImage G X f β T (e x z (a ≫ b)).1 (e x z (a ≫ b)).2.1
        (e x z (a ≫ b)).2.2 =
      arrowImage G X f β T (e x y a).1 (e x y a).2.1 (e x y a).2.2 ≫
        arrowImage G X f β T (e y z b).1 (e y z b).2.1 (e y z b).2.2 := by
  let e := G.toGroupoidInFunctors.evaluationArrowEquiv (Opposite.op T)
  let p : (Deformation.composableArrows G.objects.obj G.arrows.obj
      G.source.hom G.target.hom).obj (Opposite.op T) :=
    ⟨((e y z b).1, (e x y a).1), (e y z b).2.1.trans (e x y a).2.2.symm⟩
  let q := (composableToPullback
    G.source.hom G.target.hom).app (Opposite.op T) p
  have hq₀ : (pullback.fst G.source.hom G.target.hom).app (Opposite.op T) q =
      (e y z b).1 := by
    show ((composableToPullback
      G.source.hom G.target.hom ≫ pullback.fst _ _).app (Opposite.op T)) p = _
    simp only [composableToPullback, pullback.lift_fst]
    rfl
  have hq₁ : (pullback.snd G.source.hom G.target.hom).app (Opposite.op T) q =
      (e x y a).1 := by
    show ((composableToPullback
      G.source.hom G.target.hom ≫ pullback.snd _ _).app (Opposite.op T)) p = _
    simp only [composableToPullback, pullback.lift_snd]
    rfl
  have hqc : G.comp.hom.app (Opposite.op T) q = (e x z (a ≫ b)).1 :=
    (G.toGroupoidInFunctors.evaluationArrowEquiv_comp _ a b).symm
  obtain ⟨h₁, h₂, h₃, h⟩ := hβ (point _ T q)
  dsimp only [BasedFunctor.comp, Functor.comp_obj, BasedCategory.whiskerLeft,
    Functor.whiskerLeft, BasedNatTrans.toNatTrans] at h₁ h₂ h₃ h
  have ec := associatedMap_point_eq G.comp.hom T hqc
  have e₀ := associatedMap_point_eq (pullback.fst G.source.hom G.target.hom) T hq₀
  have e₁ := associatedMap_point_eq (pullback.snd G.source.hom G.target.hom) T hq₁
  let Fs := (BasedFunctor.comp
    (associatedMap C S hS G.source.hom).1.hom f).toFunctor
  let Ft := (BasedFunctor.comp
    (associatedMap C S hS G.target.hom).1.hom f).toFunctor
  have es := (congrArg Fs.obj ec).trans (congrArg f.obj
    (associatedMap_point_eq G.source.hom T (e x z (a ≫ b)).2.1))
  have et := (congrArg Ft.obj ec).trans (congrArg f.obj
    (associatedMap_point_eq G.target.hom T (e x z (a ≫ b)).2.2))
  have hh := congrArg (fun k => eqToHom es.symm ≫ k ≫ eqToHom et) h
  rw [β.toNatTrans.congr ec, β.toNatTrans.congr e₁, β.toNatTrans.congr e₀] at hh
  simpa only [arrowImage, eqToHom_map, Category.assoc,
    eqToHom_trans_assoc, eqToHom_trans] using hh

/-- The action of an arrow is invertible: its component of `β` lies over an identity of the site,
and a vertical arrow of a category fibred in groupoids is an isomorphism. -/
private lemma arrowImage_isIso (hX : X.p.IsFiberedInGroupoids)
    (T : BigFppfOver C S hS)
    {x y : G.objects.obj.obj (Opposite.op T)} (a : G.arrows.obj.obj (Opposite.op T))
    (hs : G.source.hom.app (Opposite.op T) a = x)
    (ht : G.target.hom.app (Opposite.op T) a = y) :
    IsIso (arrowImage G X f β T a hs ht) := by
  have hlift : X.p.IsHomLift (𝟙 T) (β.app (point G.arrows.obj T a)) :=
    β.isHomLift' (point G.arrows.obj T a)
  have := hX.isStronglyCartesian_homLift (𝟙 T) (β.app (point G.arrows.obj T a))
  have : IsIso (β.app (point G.arrows.obj T a)) :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso (p := X.p) (f := 𝟙 T) _
  unfold arrowImage
  infer_instance

/-- The action preserves identity arrows: an invertible idempotent is an identity. -/
private lemma arrowImage_id (hX : X.p.IsFiberedInGroupoids) (hβ : IsCocycle G X f β)
    (T : BigFppfOver C S hS)
    (x : G.toGroupoidInFunctors.Evaluation (Opposite.op T)) :
    let e := G.toGroupoidInFunctors.evaluationArrowEquiv (Opposite.op T)
    arrowImage G X f β T (e x x (𝟙 x)).1 (e x x (𝟙 x)).2.1
      (e x x (𝟙 x)).2.2 = 𝟙 _ := by
  dsimp only
  have := arrowImage_isIso G X f β hX T _
    (G.toGroupoidInFunctors.evaluationArrowEquiv _ x x (𝟙 x)).2.1
    (G.toGroupoidInFunctors.evaluationArrowEquiv _ x x (𝟙 x)).2.2
  have hh := arrowImage_comp G X f β hβ T (𝟙 x) (𝟙 x)
  dsimp only at hh
  simp only [Category.id_comp] at hh
  simpa [Category.assoc] using (congrArg (fun k => k ≫ inv (arrowImage G X f β T
    (G.toGroupoidInFunctors.evaluationArrowEquiv _ x x (𝟙 x)).1
    (G.toGroupoidInFunctors.evaluationArrowEquiv _ x x (𝟙 x)).2.1
    (G.toGroupoidInFunctors.evaluationArrowEquiv _ x x (𝟙 x)).2.2)) hh).symm

/-- The action of the arrows, read as a functor out of the evaluated groupoid at a test object of
the site. -/
private noncomputable def fibreCocycleFunctor (hX : X.p.IsFiberedInGroupoids)
    (hβ : IsCocycle G X f β) (T : BigFppfOver C S hS) :
    G.toGroupoidInFunctors.Evaluation (Opposite.op T) ⥤ X.obj where
  obj x := f.obj (point G.objects.obj T x)
  map {x y} a := arrowImage G X f β T
    (G.toGroupoidInFunctors.evaluationArrowEquiv _ x y a).1
    (G.toGroupoidInFunctors.evaluationArrowEquiv _ x y a).2.1
    (G.toGroupoidInFunctors.evaluationArrowEquiv _ x y a).2.2
  map_id := arrowImage_id G X f β hX hβ T
  map_comp := arrowImage_comp G X f β hβ T

/-- These fibrewise functors are compatible with restriction along an arrow of the site. -/
private lemma fibreCocycleFunctor_baseChange (hX : X.p.IsFiberedInGroupoids)
    (hβ : IsCocycle G X f β)
    {T T' : BigFppfOver C S hS} (k : T ⟶ T')
    {x y : G.toGroupoidInFunctors.Evaluation (Opposite.op T')} (a : x ⟶ y) :
    (fibreCocycleFunctor G X f β hX hβ T).map
        ((Deformation.evaluationMap G.toGroupoidInFunctors k.op).map a) ≫
        f.map (pointHom G.objects.obj k (y := y) rfl) =
      f.map (pointHom G.objects.obj k (y := x) rfl) ≫
        (fibreCocycleFunctor G X f β hX hβ T').map a := by
  simpa only [fibreCocycleFunctor, Deformation.evaluationMap, Equiv.apply_symm_apply,
    GroupoidInAlgebraicSpaces.toGroupoidInFunctors] using
    arrowImage_naturality G X f β k
      (G.toGroupoidInFunctors.evaluationArrowEquiv _ x y a).1
      (G.toGroupoidInFunctors.evaluationArrowEquiv _ x y a).2.1
      (G.toGroupoidInFunctors.evaluationArrowEquiv _ x y a).2.2

/-- The pointwise groupoid fibration of `G`, the presentation the quotient stack stackifies. -/
private noncomputable abbrev presentation :=
  presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)

/-- The base component of an identity of the presentation. -/
private lemma presentation_id_base (x : (presentation G).obj) :
    (𝟙 x : x ⟶ x).base = 𝟙 x.base := rfl

/-- The base component of a composite in the presentation. -/
private lemma presentation_comp_base {x y z : (presentation G).obj}
    (a : x ⟶ y) (b : y ⟶ z) : (a ≫ b).base = a.base ≫ b.base := rfl

/-- The fibre component of an identity of the presentation. -/
private lemma presentation_id_fiber (x : (presentation G).obj) :
    (𝟙 x : x ⟶ x).fiber =
      @eqToHom (G.toGroupoidInFunctors.Evaluation (Opposite.op x.base)) _ _ _
        (G.objects.obj.map_id_apply (Opposite.op x.base) x.fiber).symm := by
  dsimp only [presentation, presheafOfGroupoids, presheafOfCategories,
    BasedCategory.ofFunctor] at x ⊢
  simp only [Pseudofunctor.CoGrothendieck.categoryStruct_id_fiber,
    Functor.toPseudofunctor'_mapId, eqToIso.inv, Cat.eqToHom_app]
  rfl

/-- The fibre component of a composite in the presentation. -/
private lemma presentation_comp_fiber {x y z : (presentation G).obj}
    (a : x ⟶ y) (b : y ⟶ z) :
    (a ≫ b).fiber = a.fiber ≫
      (Deformation.evaluationMap G.toGroupoidInFunctors a.base.op).map b.fiber ≫
        eqToHom (G.objects.obj.map_comp_apply b.base.op a.base.op z.fiber).symm :=
  PresheafOfCategories.comp_fiber _ a b

/-- The value on an arrow of the presentation of the 1-morphism the cocycle defines: first the
action of its fibre arrow, then the image under `f` of the canonical arrow over its base. -/
private noncomputable def cocycleMap (hX : X.p.IsFiberedInGroupoids)
    (hβ : IsCocycle G X f β) {x y : (presentation G).obj} (a : x ⟶ y) :
    f.obj (point G.objects.obj x.base x.fiber) ⟶
      f.obj (point G.objects.obj y.base y.fiber) :=
  (fibreCocycleFunctor G X f β hX hβ x.base).map a.fiber ≫
    f.map (pointHom G.objects.obj a.base (y := y.fiber) rfl)

/-- It preserves identities. -/
private lemma cocycleMap_id (hX : X.p.IsFiberedInGroupoids)
    (hβ : IsCocycle G X f β) (x : (presentation G).obj) :
    cocycleMap G X f β hX hβ (𝟙 x) = 𝟙 _ := by
  simp only [cocycleMap, presentation_id_base, presentation_id_fiber]
  rw [eqToHom_map]
  show eqToHom (congrArg f.obj (congrArg (point G.objects.obj x.base)
    (G.objects.obj.map_id_apply (Opposite.op x.base) x.fiber).symm)) ≫ f.map _ = _
  rw [← eqToHom_map f.toFunctor (congrArg (point G.objects.obj x.base)
    (G.objects.obj.map_id_apply (Opposite.op x.base) x.fiber).symm), ← Functor.map_comp]
  have hh : (eqToHom (congrArg (point G.objects.obj x.base)
    (G.objects.obj.map_id_apply (Opposite.op x.base) x.fiber).symm) ≫
      pointHom G.objects.obj (𝟙 x.base) (y := x.fiber) rfl) =
      𝟙 (point G.objects.obj x.base x.fiber) := by
    have := pointHom_lift G.objects.obj (𝟙 x.base) (y := x.fiber) rfl
    have : (fibredCategory C S hS G.objects.obj).val.p.IsHomLift
        (𝟙 x.base) (𝟙 (point G.objects.obj x.base x.fiber)) := IsHomLift.id rfl
    apply pointHom_ext_of_lift (𝟙 x.base)
  rw [hh]
  exact f.map_id _

/-- It preserves composition. -/
private lemma cocycleMap_comp (hX : X.p.IsFiberedInGroupoids)
    (hβ : IsCocycle G X f β) {x y z : (presentation G).obj}
    (a : x ⟶ y) (b : y ⟶ z) :
    cocycleMap G X f β hX hβ (a ≫ b) =
      cocycleMap G X f β hX hβ a ≫ cocycleMap G X f β hX hβ b := by
  simp only [cocycleMap]
  have hfib : (fibreCocycleFunctor G X f β hX hβ x.base).map (a ≫ b).fiber =
      (fibreCocycleFunctor G X f β hX hβ x.base).map (a.fiber ≫
        (Deformation.evaluationMap G.toGroupoidInFunctors a.base.op).map b.fiber ≫
          eqToHom (G.objects.obj.map_comp_apply b.base.op a.base.op z.fiber).symm) :=
    congrArg _ (presentation_comp_fiber G a b)
  rw [hfib, Functor.map_comp (fibreCocycleFunctor G X f β hX hβ x.base),
    Functor.map_comp (fibreCocycleFunctor G X f β hX hβ x.base)]
  show _ ≫ f.map (pointHom G.objects.obj (a.base ≫ b.base) (y := z.fiber) rfl) = _
  rw [eqToHom_map]
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun m => (fibreCocycleFunctor G X f β hX hβ x.base).map a.fiber ≫ m)
    (Category.assoc _ _ _)).trans ?_
  show _ ≫ _ ≫ eqToHom (congrArg f.obj (congrArg (point G.objects.obj x.base)
    (G.objects.obj.map_comp_apply b.base.op a.base.op z.fiber).symm)) ≫ f.map _ = _
  rw [← eqToHom_map f.toFunctor (congrArg (point G.objects.obj x.base)
    (G.objects.obj.map_comp_apply b.base.op a.base.op z.fiber).symm), ← Functor.map_comp]
  have hh : eqToHom (congrArg (point G.objects.obj x.base)
    (G.objects.obj.map_comp_apply b.base.op a.base.op z.fiber).symm) ≫
      pointHom G.objects.obj (a.base ≫ b.base) (y := z.fiber) rfl =
      pointHom G.objects.obj a.base (y := G.objects.obj.map b.base.op z.fiber) rfl ≫
        pointHom G.objects.obj b.base (y := z.fiber) rfl := by
    have := pointHom_lift G.objects.obj a.base
      (y := G.objects.obj.map b.base.op z.fiber) rfl
    have := pointHom_lift G.objects.obj b.base (y := z.fiber) rfl
    have := pointHom_lift G.objects.obj (a.base ≫ b.base) (y := z.fiber) rfl
    apply pointHom_ext_of_lift (a.base ≫ b.base)
  rw [hh, Functor.map_comp]
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine congrArg (fun m => (fibreCocycleFunctor G X f β hX hβ x.base).map a.fiber ≫ m) ?_
  refine Eq.trans ((Category.assoc _ _ _).symm.trans ?_) (Category.assoc _ _ _)
  exact congrArg (fun m => m ≫ f.map (pointHom G.objects.obj b.base (y := z.fiber) rfl))
    (fibreCocycleFunctor_baseChange G X f β hX hβ a.base b.fiber)

/-- The functor out of the pointwise groupoid presentation that the cocycle defines. -/
private noncomputable def cocycleFunctor (hX : X.p.IsFiberedInGroupoids)
    (hβ : IsCocycle G X f β) : (presentation G).obj ⥤ X.obj where
  obj x := f.obj (point G.objects.obj x.base x.fiber)
  map := cocycleMap G X f β hX hβ
  map_id := cocycleMap_id G X f β hX hβ
  map_comp := cocycleMap_comp G X f β hX hβ

/- The three definitions just made are the ones the remaining proofs have to see through: the
value of the functor on an object and on an arrow is read back off `f` and off the action of the
arrows, and at `implicit` transparency neither reduction happens. -/
attribute [local implicit_reducible] cocycleFunctor fibreCocycleFunctor cocycleMap

/-- The action of an arrow of the arrow space lies over an identity of the site. -/
private lemma arrowImage_lift
    (T : BigFppfOver C S hS)
    {x y : G.objects.obj.obj (Opposite.op T)} (a : G.arrows.obj.obj (Opposite.op T))
    (hs : G.source.hom.app (Opposite.op T) a = x)
    (ht : G.target.hom.app (Opposite.op T) a = y) :
    X.p.IsHomLift (𝟙 T) (arrowImage G X f β T a hs ht) := by
  have hlift : X.p.IsHomLift (𝟙 T) (β.app (point G.arrows.obj T a)) :=
    β.isHomLift' (point G.arrows.obj T a)
  unfold arrowImage
  infer_instance

/-- The functor the cocycle defines lies over the site on arrows. -/
private lemma cocycleMap_lift (hX : X.p.IsFiberedInGroupoids)
    (hβ : IsCocycle G X f β) {x y : (presentation G).obj} (a : x ⟶ y) :
    X.p.IsHomLift a.base (cocycleMap G X f β hX hβ a) := by
  have := pointHom_lift G.objects.obj a.base (y := y.fiber) rfl
  have := arrowImage_lift G X f β x.base
    (G.toGroupoidInFunctors.evaluationArrowEquiv _ _ _ a.fiber).1
    (G.toGroupoidInFunctors.evaluationArrowEquiv _ _ _ a.fiber).2.1
    (G.toGroupoidInFunctors.evaluationArrowEquiv _ _ _ a.fiber).2.2
  dsimp only [cocycleMap, fibreCocycleFunctor]
  infer_instance

/-- The functor the cocycle defines commutes strictly with the projections to the site. -/
private lemma cocycleFunctor_over (hX : X.p.IsFiberedInGroupoids)
    (hβ : IsCocycle G X f β) :
    cocycleFunctor G X f β hX hβ ⋙ X.p = (presentation G).p := by
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro x
    exact f.w_obj (point G.objects.obj x.base x.fiber)
  case h_map =>
    intro x y a
    have := cocycleMap_lift G X f β hX hβ a
    exact IsHomLift.fac' X.p a.base (cocycleMap G X f β hX hβ a)

/-- The 1-morphism over the site from the pointwise groupoid presentation to `X` that the cocycle
defines. -/
private noncomputable def cocycleBasedFunctor (hX : X.p.IsFiberedInGroupoids)
    (hβ : IsCocycle G X f β) : BasedFunctor (presentation G) X where
  toFunctor := cocycleFunctor G X f β hX hβ
  w := cocycleFunctor_over G X f β hX hβ

/-- On the arrows coming from the object space — those which are identities in their fibre — the
functor the cocycle defines agrees with `f`. -/
private lemma cocycleFunctor_map_projectionArrow (hX : X.p.IsFiberedInGroupoids)
    (hβ : IsCocycle G X f β)
    {x y : (fibredCategory C S hS G.objects.obj).val.obj} (a : x ⟶ y)
    (b : (⟨x.base, Discrete.as x.fiber⟩ : (presentation G).obj) ⟶
      ⟨y.base, Discrete.as y.fiber⟩)
    (hb : b.base = a.base)
    (hb' : (G.toGroupoidInFunctors.evaluationArrowEquiv _ _ _ b.fiber).1 =
      G.toGroupoidInFunctors.identity (Opposite.op x.base) (Discrete.as x.fiber)) :
    (cocycleFunctor G X f β hX hβ).map b = f.map a := by
  rcases b with ⟨k, b⟩
  dsimp only at hb
  subst k
  have ha : Discrete.as x.fiber = G.objects.obj.map a.base.op (Discrete.as y.fiber) :=
    Discrete.eq_of_hom a.fiber
  obtain ⟨_, hb''⟩ := evaluationArrow_eqToHom_of_identity G.toGroupoidInFunctors
    (Opposite.op x.base) b hb'
  show (fibreCocycleFunctor G X f β hX hβ x.base).map b ≫
    f.map (pointHom G.objects.obj a.base (y := Discrete.as y.fiber) rfl) = _
  rw [hb'', eqToHom_map]
  show eqToHom (congrArg f.obj (congrArg (point G.objects.obj x.base) ha)) ≫ _ = _
  rw [← eqToHom_map f.toFunctor (congrArg (point G.objects.obj x.base) ha),
    ← Functor.map_comp]
  apply congrArg f.map
  have := pointHom_lift G.objects.obj a.base (y := Discrete.as y.fiber) rfl
  have : (fibredCategory C S hS G.objects.obj).val.p.IsHomLift a.base a :=
    IsHomLift.map _ a
  exact pointHom_ext_of_lift a.base _ _

/-- Two arrows of an evaluated groupoid out of the same object whose underlying elements of the
arrow space agree are identified by the transport between their targets. -/
private lemma evaluation_hom_ext_transport
    (T : BigFppfOver C S hS)
    {x y y' : G.toGroupoidInFunctors.Evaluation (Opposite.op T)}
    (h : y = y') (a : x ⟶ y) (b : x ⟶ y')
    (hab : (G.toGroupoidInFunctors.evaluationArrowEquiv _ _ _ a).1 =
      (G.toGroupoidInFunctors.evaluationArrowEquiv _ _ _ b).1) :
    a ≫ eqToHom h = b := by
  subst y'
  simp only [eqToHom_refl, Category.comp_id]
  exact (G.toGroupoidInFunctors.evaluationArrowEquiv _ _ _).injective (Subtype.ext hab)

/-- On a vertical arrow of the presentation whose underlying element of the arrow space is a given
arrow, the functor the cocycle defines has precisely the prescribed action as its value. -/
private lemma cocycleFunctor_map_verticalArrow (hX : X.p.IsFiberedInGroupoids)
    (hβ : IsCocycle G X f β) (T : BigFppfOver C S hS)
    (a : G.arrows.obj.obj (Opposite.op T))
    (b : (⟨T, G.source.hom.app (Opposite.op T) a⟩ : (presentation G).obj) ⟶
      ⟨T, G.target.hom.app (Opposite.op T) a⟩)
    (hb : b.base = 𝟙 T)
    (hb' : (G.toGroupoidInFunctors.evaluationArrowEquiv _ _ _ b.fiber).1 = a) :
    (cocycleFunctor G X f β hX hβ).map b = arrowImage G X f β T a rfl rfl := by
  rcases b with ⟨k, b⟩
  dsimp only at hb
  subst k
  let : Groupoid (G.objects.obj.obj (Opposite.op T)) :=
    G.toGroupoidInFunctors.evaluationGroupoid (Opposite.op T)
  let q : (G.source.hom.app (Opposite.op T) a :
      G.toGroupoidInFunctors.Evaluation (Opposite.op T)) ⟶
      G.target.hom.app (Opposite.op T) a :=
    (G.toGroupoidInFunctors.evaluationArrowEquiv _ _ _).symm ⟨a, rfl, rfl⟩
  have hq : b = q ≫ eqToHom
      (G.objects.obj.map_id_apply (Opposite.op T)
        (G.target.hom.app (Opposite.op T) a)).symm := by
    symm
    apply evaluation_hom_ext_transport G T
    change (G.toGroupoidInFunctors.evaluationArrowEquiv (Opposite.op T)
      (G.source.hom.app (Opposite.op T) a)
      (G.objects.obj.map (𝟙 (Opposite.op T)) (G.target.hom.app (Opposite.op T) a)) b).1 = a
      at hb'
    simpa only [q, Equiv.apply_symm_apply] using hb'.symm
  show (fibreCocycleFunctor G X f β hX hβ T).map b ≫
    f.map (pointHom G.objects.obj (𝟙 T)
      (y := G.target.hom.app (Opposite.op T) a) rfl) = _
  rw [hq]
  simp only [Functor.map_comp, Category.assoc]
  have hi := cocycleMap_id G X f β hX hβ ⟨T, G.target.hom.app (Opposite.op T) a⟩
  simp only [cocycleMap, presentation_id_base, presentation_id_fiber] at hi
  rw [hi]
  simpa only [fibreCocycleFunctor, q, Equiv.apply_symm_apply] using
    Category.comp_id ((fibreCocycleFunctor G X f β hX hβ T).map q)

/-- A comparison on the presentation restricts, along the projection of Stacks 044R, to a
comparison on the object space. -/
private noncomputable def projectionComparison (hX : X.p.IsFiberedInGroupoids)
    (hβ : IsCocycle G X f β) (g : BasedFunctor (quotientStack G) X)
    (η : pointwiseToQuotientStack G ⋙ g.toFunctor ≅
      cocycleFunctor G X f β hX hβ) :
    (quotientStackProjection G).toFunctor ⋙ g.toFunctor ≅ f.toFunctor :=
  NatIso.ofComponents (fun x =>
    eqToIso (congrArg g.obj (quotientStackProjection_obj G x)) ≪≫
      η.app ⟨x.base, Discrete.as x.fiber⟩) (by
    intro x y a
    obtain ⟨b, hb, hb', hp⟩ := quotientStackProjection_map G a
    simp only [CategoryTheory.Functor.comp_map, Iso.trans_hom, eqToIso.hom, Iso.app_hom]
    rw [hp, g.map_comp, g.map_comp, eqToHom_map, eqToHom_map]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    have hn := η.hom.naturality b
    change g.map ((pointwiseToQuotientStack G).map b) ≫ _ =
      _ ≫ (cocycleFunctor G X f β hX hβ).map b at hn
    rw [cocycleFunctor_map_projectionArrow G X f β hX hβ a b hb hb'] at hn
    rw [hn])

/-- That comparison, as a 2-isomorphism over the site. -/
private noncomputable def projectionBasedComparison (hX : X.p.IsFiberedInGroupoids)
    (hβ : IsCocycle G X f β) (g : BasedFunctor (quotientStack G) X)
    (η : pointwiseToQuotientStack G ⋙ g.toFunctor ≅
      cocycleFunctor G X f β hX hβ)
    (hη : ∀ x : (presentation G).obj, X.p.IsHomLift (𝟙 x.base) (η.hom.app x)) :
    BasedFunctor.comp (quotientStackProjection G) g ≅ f :=
  BasedNatIso.mkNatIso (projectionComparison G X f β hX hβ g η) (by
    intro x
    have := hη ⟨x.base, Discrete.as x.fiber⟩
    change X.p.IsHomLift (𝟙 x.base)
      (eqToHom (congrArg g.obj (quotientStackProjection_obj G x)) ≫
        η.hom.app ⟨x.base, Discrete.as x.fiber⟩)
    infer_instance)

/-- The functor the cocycle defines, on the universe-lifted presentation that the stackification
construction consumes. -/
private noncomputable def quotientPrestackCocycleFunctor (hX : X.p.IsFiberedInGroupoids)
    (hβ : IsCocycle G X f β) : BasedFunctor (quotientPrestack G) X where
  toFunctor := ULiftHom.down.{u, u + 1, u + 1} (C := (presentation G).obj) ⋙
    cocycleFunctor G X f β hX hβ
  w := by
    rw [CategoryTheory.Functor.assoc, cocycleFunctor_over]
    rfl

/-- Restricting it along the universe lift returns the original functor. -/
private lemma quotientPrestackCocycleFunctor_comp_equivalence
    (hX : X.p.IsFiberedInGroupoids) (hβ : IsCocycle G X f β) :
    (quotientPrestackEquivalence G).functor ⋙
        (quotientPrestackCocycleFunctor G X f β hX hβ).toFunctor =
      cocycleFunctor G X f β hX hβ := rfl

/-- The components of the comparison on the object space. -/
private lemma projectionBasedComparison_app (hX : X.p.IsFiberedInGroupoids)
    (hβ : IsCocycle G X f β) (g : BasedFunctor (quotientStack G) X)
    (η : pointwiseToQuotientStack G ⋙ g.toFunctor ≅
      cocycleFunctor G X f β hX hβ)
    (hη : ∀ x : (presentation G).obj, X.p.IsHomLift (𝟙 x.base) (η.hom.app x))
    (x : (fibredCategory C S hS G.objects.obj).val.obj) :
    (projectionBasedComparison G X f β hX hβ g η hη).hom.app x =
      eqToHom (congrArg g.obj (quotientStackProjection_obj G x)) ≫
        η.hom.app ⟨x.base, Discrete.as x.fiber⟩ := rfl

/-- An equality of objects transports the component of a morphism of functors. -/
private lemma natTrans_app_transport {D : Type*} [Category D]
    {E : Type*} [Category E] {F H : D ⥤ E} (η : F ⟶ H)
    {x y : D} (h : x = y) :
    η.app x = eqToHom (congrArg F.obj h) ≫ η.app y ≫
      eqToHom (congrArg H.obj h).symm := by
  subst y
  simp

/-- Naturality of a morphism of functors out of a composite, with the source and target of the
first functor identified explicitly and the arrow between them only heterogeneously equal to an
image. -/
private lemma naturality_of_heq {D : Type*} [Category D]
    {E : Type*} [Category E] {H : Type*} [Category H]
    (F : D ⥤ E) (g : E ⥤ H) (K : D ⥤ H) (η : F ⋙ g ⟶ K)
    {x y : D} {a b : E} (ha : a = F.obj x) (hb : b = F.obj y)
    (m : a ⟶ b) (n : x ⟶ y) (hm : HEq m (F.map n)) :
    (eqToHom (congrArg g.obj ha) ≫ η.app x) ≫ K.map n =
      g.map m ≫ (eqToHom (congrArg g.obj hb) ≫ η.app y) := by
  subst a; subst b
  cases eq_of_heq hm
  simpa using (η.naturality n).symm

/-- The comparison on the object space carries the canonical 2-morphism of Stacks 044S to the
prescribed cocycle. -/
private lemma projectionBasedComparison_twoArrow (hX : X.p.IsFiberedInGroupoids)
    (hβ : IsCocycle G X f β) (g : BasedFunctor (quotientStack G) X)
    (η : pointwiseToQuotientStack G ⋙ g.toFunctor ≅
      cocycleFunctor G X f β hX hβ)
    (hη : ∀ x : (presentation G).obj, X.p.IsHomLift (𝟙 x.base) (η.hom.app x)) :
    BasedCategory.whiskerLeft
        (associatedMap C S hS G.source.hom).1.hom
        (projectionBasedComparison G X f β hX hβ g η hη).hom ≫ β =
      BasedCategory.whiskerRight (quotientStackTwoArrow G) g ≫
        BasedCategory.whiskerLeft
          (associatedMap C S hS G.target.hom).1.hom
          (projectionBasedComparison G X f β hX hβ g η hη).hom := by
  ext x
  rcases x with ⟨T, a⟩
  change Discrete (G.arrows.obj.obj (Opposite.op T)) at a
  rcases a with ⟨a⟩
  let x := point G.arrows.obj T a
  obtain ⟨b, hb, hb', hq⟩ := quotientStackTwoArrow_app G x
  let sx := (associatedMap C S hS G.source.hom).1.hom.obj x
  let tx := (associatedMap C S hS G.target.hom).1.hom.obj x
  have hs := associatedMap_obj_eq G.source.hom x
  have ht := associatedMap_obj_eq G.target.hom x
  have hp : ∀ m : G.arrows.obj ⟶ G.objects.obj,
      (quotientStackProjection G).obj ((associatedMap C S hS m).1.hom.obj x) =
        (pointwiseToQuotientStack G).obj
          ⟨x.base, m.app (Opposite.op x.base) (Discrete.as x.fiber)⟩ := fun m => by
    rw [associatedMap_obj_eq m x]
    exact quotientStackProjection_obj G _
  have hn := naturality_of_heq (pointwiseToQuotientStack G) g.toFunctor
    (cocycleFunctor G X f β hX hβ) η.hom (hp G.source.hom) (hp G.target.hom)
    ((quotientStackTwoArrow G).app x) b hq
  rw [cocycleFunctor_map_verticalArrow G X f β hX hβ _ _ b hb hb'] at hn
  show (projectionBasedComparison G X f β hX hβ g η hη).hom.app sx ≫ β.app x =
    g.map ((quotientStackTwoArrow G).app x) ≫
      (projectionBasedComparison G X f β hX hβ g η hη).hom.app tx
  have hα : ∀ m : G.arrows.obj ⟶ G.objects.obj,
      (projectionBasedComparison G X f β hX hβ g η hη).hom.app
        ((associatedMap C S hS m).1.hom.obj x) = _ := fun m =>
    natTrans_app_transport (projectionComparison G X f β hX hβ g η).hom
      (associatedMap_obj_eq m x)
  rw [hα G.source.hom, hα G.target.hom]
  simp only [projectionComparison, NatIso.ofComponents_hom_app,
    Iso.trans_hom, eqToIso.hom, Iso.app_hom, Category.assoc,
    eqToHom_trans_assoc]
  dsimp only [arrowImage] at hn
  simp only [Category.assoc] at hn
  refine (cancel_mono (eqToHom (congrArg f.obj ht))).1 ?_
  simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using hn

/-- **The universal property of the stackification for the quotient stack, Stacks 0436.** Every
1-morphism out of the presentation `AlgebraicGeometry.Stack.quotientPrestack` into a stack in
groupoids `X` over the big fppf site extends along
`AlgebraicGeometry.Stack.toQuotientStack` to a 1-morphism out of the quotient stack, with a
2-isomorphism on the presentation all of whose components are vertical.

This is `CategoryTheory.Functor.Stackification.extendGroupoid` and its companions at the two
clauses of Stacks 02ZN which exhibit the quotient as the stackification of its presentation,
`AlgebraicGeometry.Stack.isLocallyBijective_toQuotientStack` and
`AlgebraicGeometry.Stack.essImage_toQuotientStack`. -/
private theorem exists_extension_along_toQuotientStack
    (hX : X.p.IsStackInGroupoids.{u + 1} (BigFppfOver.topology C S hS))
    (g₀ : BasedFunctor (quotientPrestack G) X) :
    ∃ (g : BasedFunctor (quotientStack G) X)
      (η : toQuotientStack G ⋙ g.toFunctor ≅ g₀.toFunctor),
      ∀ x : (quotientPrestack G).obj,
        X.p.IsHomLift (𝟙 ((quotientPrestack G).p.obj x)) (η.hom.app x) := by
  have hqfib : X.p.IsFibered := hX.isFiberedInGroupoids.isFibered
  have hsq : X.p.IsStack (BigFppfOver.topology C S hS) :=
    Functor.isStack_of_isStackInGroupoids hX
  have hp := isFiberedInGroupoids_quotientPrestack G
  have hp' := isFiberedInGroupoids_quotientStack G
  have hsp' := isStack_quotientStack G
  have hGc := (isFibredOneMorphism_toQuotientStack G).comp_eq
  refine ⟨⟨Functor.Stackification.extendGroupoid hp hp' hsp' hX.isFiberedInGroupoids hsq
      hGc g₀.w (isLocallyBijective_toQuotientStack G) (essImage_toQuotientStack G),
      Functor.Stackification.extendGroupoid_comp_eq hp hp' hsp' hX.isFiberedInGroupoids hsq
        hGc g₀.w (isLocallyBijective_toQuotientStack G) (essImage_toQuotientStack G)⟩,
    Functor.Stackification.unitGroupoid hp hp' hsp' hX.isFiberedInGroupoids hsq
      hGc g₀.w (isLocallyBijective_toQuotientStack G) (essImage_toQuotientStack G),
    fun x => Functor.Stackification.isHomLift_unitGroupoid_app hp hp' hsp'
      hX.isFiberedInGroupoids hsq hGc g₀.w (isLocallyBijective_toQuotientStack G)
      (essImage_toQuotientStack G) x⟩

/-- **Stacks 044U**, on the hypothesis that 1-morphisms into `X` extend along the stackification.
The quotient stack is a 2-coequalizer of the 2-commutative square of Stacks 044S: a 1-morphism `f`
out of the object space together with a 2-morphism `β : s ∘ f ⟶ t ∘ f` satisfying the composition
cocycle descends to a 1-morphism `g` out of the quotient stack, with a 2-isomorphism
`α : π ∘ g ≅ f` carrying the canonical 2-morphism of Stacks 044S to `β`.

`hext` is the universal property of the stackification, Stacks 0436, for the pair
`AlgebraicGeometry.Stack.toQuotientStack` and `X`; it is discharged for a stack in groupoids by
`AlgebraicGeometry.Stack.exists_extension_along_toQuotientStack`, and the unconditional form is
`AlgebraicGeometry.Stack.quotientStack_desc`.  Leaving it a hypothesis costs nothing and leaves
the universes of `X` unconstrained. -/
public theorem quotientStack_desc_of_extendsAlongStackification
    (hX : X.p.IsFiberedInGroupoids) (hβ : IsCocycle G X f β)
    (hext : ∀ g₀ : BasedFunctor (quotientPrestack G) X,
      ∃ (g : BasedFunctor (quotientStack G) X)
        (η : toQuotientStack G ⋙ g.toFunctor ≅ g₀.toFunctor),
        ∀ x : (quotientPrestack G).obj,
          X.p.IsHomLift (𝟙 ((quotientPrestack G).p.obj x)) (η.hom.app x)) :
    ∃ (g : BasedFunctor (quotientStack G) X)
      (α : BasedFunctor.comp (quotientStackProjection G) g ≅ f),
      BasedCategory.whiskerLeft
          (associatedMap C S hS G.source.hom).1.hom α.hom ≫ β =
        BasedCategory.whiskerRight (quotientStackTwoArrow G) g ≫
          BasedCategory.whiskerLeft
            (associatedMap C S hS G.target.hom).1.hom α.hom := by
  obtain ⟨g, η₀, hη₀⟩ := hext (quotientPrestackCocycleFunctor G X f β hX hβ)
  refine ⟨g, projectionBasedComparison G X f β hX hβ g
      (Functor.isoWhiskerLeft (quotientPrestackEquivalence G).functor η₀)
      (fun x => hη₀ ((quotientPrestackEquivalence G).functor.obj x)),
    projectionBasedComparison_twoArrow G X f β hX hβ g _ _⟩

end CocycleFunctor

/-- **Stacks 044U.** The quotient stack is a 2-coequalizer of the 2-commutative square of
Stacks 044S in the 2-category of stacks in groupoids over the big fppf site: given a stack in
groupoids `X`, a 1-morphism `f : 𝒮_U ⟶ X` out of the object space of a groupoid in algebraic
spaces and a 2-morphism `β : s ∘ f ⟶ t ∘ f` satisfying the composition cocycle on the arrows,
there are a 1-morphism `g : [U/R] ⟶ X` out of the quotient stack and a 2-isomorphism
`α : π ∘ g ≅ f` on the object space which carry the canonical 2-morphism of Stacks 044S to `β`.

The comparison 2-isomorphism is kept as data rather than replaced by the bare existence of some
1-morphism, since the compatibility with the 2-morphism of Stacks 044S is a statement about
it. -/
@[stacks 044U]
public theorem quotientStack_desc
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (X : BasedCategory (BigFppfOver C S hS))
    (hX : X.p.IsStackInGroupoids.{u + 1} (BigFppfOver.topology C S hS))
    (f : BasedFunctor (fibredCategory C S hS G.objects.obj).val X)
    (β : BasedFunctor.comp
      (associatedMap C S hS G.source.hom).1.hom f ⟶
      BasedFunctor.comp (associatedMap C S hS G.target.hom).1.hom f)
    (hβ : IsCocycle G X f β) :
    ∃ (g : BasedFunctor (quotientStack G) X)
      (α : BasedFunctor.comp (quotientStackProjection G) g ≅ f),
      BasedCategory.whiskerLeft
          (associatedMap C S hS G.source.hom).1.hom α.hom ≫ β =
        BasedCategory.whiskerRight (quotientStackTwoArrow G) g ≫
          BasedCategory.whiskerLeft
            (associatedMap C S hS G.target.hom).1.hom α.hom :=
  quotientStack_desc_of_extendsAlongStackification G X f β hX.isFiberedInGroupoids hβ
    (exists_extension_along_toQuotientStack G X hX)

end AlgebraicGeometry.Stack

end
