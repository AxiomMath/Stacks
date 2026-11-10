module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.FullFaithfulness
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientPrestackPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.RestrictionArrows
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FppfCoverings
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.FullyFaithfulEquivalence
public import StacksFrontier.CategoryTheory.Sites.Stack.LocallyEssSurjOnFibersComp

/-!
# When a morphism of quotient stacks is an equivalence

Let `f : (U, R, s, t, c) ⟶ (U', R', s', t', c')` be a morphism of groupoids in algebraic spaces
over an algebraic space `B` over a scheme `S` of a big fppf site, and let `[f] : [U/R] ⟶ [U'/R']`
be the induced morphism of quotient stacks of Stacks 046Q. Pulling the target morphism of the
arrow space of `(U', R', s', t', c')` back along the map that `f` induces on objects produces the
algebraic space of pairs consisting of an object of `(U, R, s, t, c)` and an arrow of
`(U', R', s', t', c')` whose target is the image of that object; sending such a pair to the source
of its arrow gives the *saturation map* `h : U ×_{f, U', t'} R' ⟶ U'` to the object space of
`(U', R', s', t', c')`.

Following Stacks 046T, `[f]` is an equivalence over the big fppf site exactly when

1. `(U, R, s, t, c)` is the restriction of `(U', R', s', t', c')` along `f : U ⟶ U'`, and
2. the saturation map is a surjection of fppf sheaves.

The source also records three sufficient conditions for (2): it holds as soon as the map on
objects is surjective as a map of fppf sheaves, in particular whenever the map on objects is an
fppf covering, and of course whenever the saturation map is itself an fppf covering.

## Main results

* `AlgebraicGeometry.Stack.quotientStackMap_isEquivalenceOver_iff`: **Stacks 046T**, the criterion
  itself.
* `AlgebraicGeometry.Space.isLocallySurjective_source_pullback_snd`: **Stacks 046T**, local
  surjectivity of the saturation map follows from local surjectivity of the map on objects.
* `AlgebraicGeometry.Space.isLocallySurjective_source_pullback_of_isFppfCovering_mapObjects`:
  **Stacks 046T**, the same conclusion from the hypothesis that the map on objects is an fppf
  covering.
* `AlgebraicGeometry.Space.isLocallySurjective_source_pullback_of_isFppfCovering_self`:
  **Stacks 046T**, the same conclusion from the hypothesis that the saturation map is itself an
  fppf covering.

## Implementation notes

An algebraic space over `S` is a presheaf on the big fppf site of `S`, so surjectivity of a map
of algebraic spaces as a map of fppf sheaves is `CategoryTheory.Presheaf.IsLocallySurjective` for
`AlgebraicGeometry.BigFppfOver.topology`, and the fibre product appearing in the saturation map is
the presheaf pullback, which by **Stacks 02X2** is the fibre product of algebraic spaces. The
criterion states the saturation map with the chosen fibre product of algebraic spaces,
`AlgebraicGeometry.AlgebraicSpaces.fiberProduct`; it is the same natural transformation as the
`pullback.snd _ _ ≫ H.source.hom` of the three sufficient conditions.

Condition (1) is the cartesian source–target square of the presheaves of points, in the shape that
`AlgebraicGeometry.Stack.fullyFaithful_quotientStackMap_iff_isPullback` (**Stacks 046S**) uses, and
it is exactly full faithfulness of `[f]`. "Equivalence" is equivalence in the 2-category of fibred
categories over the site, `CategoryTheory.Functor.IsEquivalenceOver`, which is data, hence the
`Nonempty`.

Given (1), **Stacks 046N** reduces the criterion to local essential surjectivity on fibres of
`[f]`, and the work is to identify that condition with (2). Both quotient stacks are reached from
their presentations, so the identification is made along the presentations: the composite from the
presentation of `[U/R]` to `[U'/R']` is `AlgebraicGeometry.Stack.quotientMapUnderlying`, which is
2-isomorphic over the site to the presentation of `[U/R]` followed by `[f]`, and local essential
surjectivity is invariant under such a 2-isomorphism (`locallyEssSurjOnFibers_congr`) and can be
cancelled against the presentation, which is itself locally essentially surjective
(`locallyEssSurjOnFibers_comp_iff`). What is then left is a statement about points of the object
spaces: a section of the saturation map over a test object is a point of `U` together with an
arrow of `R'` from its image to the given point of `U'`, which is precisely a local preimage of
that point in the fibre of `[U/R]`. The arrow is recovered from an isomorphism of presented
objects through the isomorphism sheaf of **Stacks 044V**.

The first of the three sufficient conditions is proved by exhibiting, over each member of the
covering sieve witnessing local surjectivity of the map on objects, the identity arrow of the
evaluated groupoid of `(U', R', s', t', c')` at the given object: that arrow has the required
target by construction, and its source is the object one started from.

The two fppf hypotheses are singleton covering families, indexed by `PUnit`, and both results are
deduced from **Stacks 0469** applied to such a family. The coproduct of a one-member family of
fppf sheaves is the sheaf itself, with the identity as the inclusion, so the map out of the
coproduct which Stacks 0469 shows to be surjective is the single member of the family.

## References

* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 03Y8](https://stacks.math.columbia.edu/tag/03Y8)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 044V](https://stacks.math.columbia.edu/tag/044V)
* [Stacks Project, Tag 044X](https://stacks.math.columbia.edu/tag/044X)
* [Stacks Project, Tag 0469](https://stacks.math.columbia.edu/tag/0469)
* [Stacks Project, Tag 046N](https://stacks.math.columbia.edu/tag/046N)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
* [Stacks Project, Tag 046S](https://stacks.math.columbia.edu/tag/046S)
* [Stacks Project, Tag 046T](https://stacks.math.columbia.edu/tag/046T)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Space

/-- A one-member fppf covering is surjective as a map of fppf sheaves: the coproduct of a
one-member family is the member itself, so **Stacks 0469** applies to the member. -/
private theorem isLocallySurjective_of_isFppfCovering_punit
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {X Y : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (g : X ⟶ Y)
    (hf : IsFppfCovering C S hS (fun _ : PUnit => X) (fun _ => g)) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS) g := by
  let J := BigFppfOver.topology C S hS
  let Xsh : Sheaf J (Type u) := ⟨X, (hf.source_isAlgebraicSpace PUnit.unit).isSheaf⟩
  let Ysh : Sheaf J (Type u) := ⟨Y, hf.target_isAlgebraicSpace.isSheaf⟩
  let φ : Xsh ⟶ Ysh := (Sheaf.homEquiv (X := Xsh) (Y := Ysh)).symm g
  let hc : IsColimit (Cofan.mk Xsh fun _ : PUnit => 𝟙 Xsh) :=
    Cofan.isColimitMkOfUnique (Iso.refl Xsh) PUnit
  have hdesc : hc.desc (Cofan.mk Ysh fun _ => φ) = φ := by
    simpa using hc.fac (Cofan.mk Ysh fun _ => φ) ⟨PUnit.unit⟩
  have hsurj : Sheaf.IsLocallySurjective φ := hdesc ▸
    isLocallySurjective_coproductDesc_of_isFppfCovering C S hS _ _ hf Xsh _ hc
  exact hsurj

/-- **Stacks 046T.** A map on objects which is surjective as a map of fppf sheaves stays
surjective after passing to the arrows of the target groupoid whose target lifts through it and
taking their sources. -/
@[stacks 046T "surjective_object_map"]
theorem isLocallySurjective_source_pullback_snd
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS} {G H : GroupoidInAlgebraicSpaces C S hS B}
    (f : GroupoidInAlgebraicSpaces.Hom G H)
    (hf : Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
      f.toGroupoidHom.mapObjects) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
      (pullback.snd f.toGroupoidHom.mapObjects H.target.hom ≫ H.source.hom) := by
  let J := BigFppfOver.topology C S hS
  refine ⟨?_⟩
  intro T y
  apply J.superset_covering ?_ (hf.imageSieve_mem y)
  rintro V i ⟨a, ha⟩
  let K := H.toGroupoidInFunctors
  let yV : K.Evaluation (Opposite.op V) := K.objects.map i.op y
  let e := K.identity (Opposite.op V) yV
  refine ⟨pbSection f.toGroupoidHom.mapObjects K.target (Opposite.op V) a e (by
    rw [ha]
    exact (K.evaluationArrowEquiv (Opposite.op V) yV yV (𝟙 yV)).2.2.symm), ?_⟩
  change K.source.app (Opposite.op V)
    ((pullback.snd f.toGroupoidHom.mapObjects K.target).app (Opposite.op V)
      (pbSection f.toGroupoidHom.mapObjects K.target (Opposite.op V) a e _)) =
    K.objects.map i.op y
  rw [pbSection_snd]
  exact (K.evaluationArrowEquiv (Opposite.op V) yV yV (𝟙 yV)).2.1

/-- **Stacks 046T.** If the map on objects of a morphism of groupoids in algebraic spaces is an
fppf covering, then every object of the target groupoid is fppf-locally the source of an arrow
whose target lifts to the source groupoid. -/
@[stacks 046T "fppf_object_map"]
theorem isLocallySurjective_source_pullback_of_isFppfCovering_mapObjects
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G H : GroupoidInAlgebraicSpaces C S hS B)
    (f : GroupoidInAlgebraicSpaces.Hom G H)
    (hf : IsFppfCovering C S hS (fun _ : PUnit => G.objects.obj)
      (fun _ => f.toGroupoidHom.mapObjects)) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
      (pullback.snd f.toGroupoidHom.mapObjects H.target.hom ≫ H.source.hom) := by
  exact isLocallySurjective_source_pullback_snd f
    (isLocallySurjective_of_isFppfCovering_punit _ hf)

/-- **Stacks 046T.** If the arrows of the target groupoid whose target lifts to the source
groupoid form an fppf covering of the object space of the target through their sources, then that
saturation map is surjective as a map of fppf sheaves. -/
@[stacks 046T "fppf_saturation"]
theorem isLocallySurjective_source_pullback_of_isFppfCovering_self
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS} {G H : GroupoidInAlgebraicSpaces C S hS B}
    (f : GroupoidInAlgebraicSpaces.Hom G H)
    (hf : IsFppfCovering C S hS
      (fun _ : PUnit => pullback f.toGroupoidHom.mapObjects H.target.hom)
      (fun _ => pullback.snd f.toGroupoidHom.mapObjects H.target.hom ≫ H.source.hom)) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
      (pullback.snd f.toGroupoidHom.mapObjects H.target.hom ≫ H.source.hom) := by
  exact isLocallySurjective_of_isFppfCovering_punit _ hf

end AlgebraicGeometry.Space


namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}}
  {hS : C.Contains S} {B : AlgebraicSpaces C S hS}

/-- The presentation functor on fibres sends `prestackPoint` to the image of the point under the
pointwise presentation. -/
private lemma presented_eq_image
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (U : BigFppfOver C S hS) (a : G.objects.obj.obj (Opposite.op U)) :
    (Functor.fiberFunctorOfCompEq
      (isFibredOneMorphism_toQuotientStack G).comp_eq U).obj (prestackPoint G U a) =
      (pointwiseToQuotientStackFiber G U).obj a :=
  Subtype.ext rfl

/-- The composite from the presentation of `[U/R]` to `[U'/R']` sends the object presented by a
point of `U` to the object presented by its image in `U'`. -/
private lemma quotientMapUnderlying_point
    {G H : GroupoidInAlgebraicSpaces C S hS B}
    (f : GroupoidInAlgebraicSpaces.Hom G H)
    (U : BigFppfOver C S hS) (a : G.objects.obj.obj (Opposite.op U)) :
    (Functor.fiberFunctorOfCompEq (quotientMapUnderlying_comp f) U).obj (prestackPoint G U a) =
      (pointwiseToQuotientStackFiber H U).obj
        (f.toGroupoidHom.mapObjects.app (Opposite.op U) a) := by
  apply Subtype.ext
  change (pointwiseToQuotientStack H).obj
    ⟨U, ((quotientPointwiseMapData f).val.app ⟨Opposite.op U⟩).toFunctor.obj a⟩ = _
  rw [(quotientPointwiseMapData f).property.1 U]
  rfl

/-- An isomorphism between two presented objects of a fibre of `[U/R]` comes from an arrow of the
arrow space with the given source and target: the isomorphism sheaf of Stacks 044V identifies the
morphisms of the fibre with the sections of the arrow space. -/
private lemma exists_arrow_of_presented_iso
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (U : BigFppfOver C S hS) (a b : G.objects.obj.obj (Opposite.op U))
    (e : (pointwiseToQuotientStackFiber G U).obj a ≅ (pointwiseToQuotientStackFiber G U).obj b) :
    ∃ r : G.arrows.obj.obj (Opposite.op U),
      G.source.hom.app (Opposite.op U) r = a ∧ G.target.hom.app (Opposite.op U) r = b := by
  let x := prestackPoint G U a
  let y := prestackPoint G U b
  let hF := isFibredOneMorphism_toQuotientStack G
  let F := Functor.fiberFunctorOfCompEq hF.comp_eq U
  have := isomPresheaf_equiv_arrowFiber C S hS G U x y
  let e' : F.obj x ≅ F.obj y :=
    eqToIso (presented_eq_image G U a) ≪≫ e ≪≫ (eqToIso (presented_eq_image G U b)).symm
  let m := (Functor.pullbackFiberIdIso (F.obj x)).hom ≫ e'.hom ≫
    (Functor.pullbackFiberIdIso (F.obj y)).inv
  let n := (inv (hF.morPresheafMap x y)).app (Opposite.op (Over.mk (𝟙 U))) m
  let k : x ⟶ y :=
    (Functor.pullbackFiberIdIso x).inv ≫ n ≫ (Functor.pullbackFiberIdIso y).hom
  let g := k.1.down
  have hg : g.base = 𝟙 U := by
    change (quotientPrestack G).p.map k.1 = 𝟙 U
    exact (@IsHomLift.eq_of_isHomLift _ _ _ _ (quotientPrestack G).p x.1 y.1 (𝟙 U) k.1 k.2).symm
  have ga : (show G.toGroupoidInFunctors.Evaluation (Opposite.op U) from a) ⟶ b := by
    have h := g.fiber
    rw [hg] at h
    change (show G.toGroupoidInFunctors.Evaluation (Opposite.op U) from a) ⟶
      ((evaluationGroupoidFunctor G.toGroupoidInFunctors).map (𝟙 _)).obj b at h
    rw [(evaluationGroupoidFunctor G.toGroupoidInFunctors).map_id] at h
    exact h
  exact ⟨_, (G.toGroupoidInFunctors.evaluationArrowEquiv (Opposite.op U) a b ga).2⟩

/-- A point of `U` together with an arrow of `R'` whose target is its image assemble into a
section of the chosen fibre product `U ×_{f, U', t'} R'`, and the saturation map sends that
section to the source of the arrow. -/
private lemma exists_pullback_section
    {G H : GroupoidInAlgebraicSpaces C S hS B}
    (g : G.objects ⟶ H.objects) (U : BigFppfOver C S hS)
    (a : G.objects.obj.obj (Opposite.op U)) (r : H.arrows.obj.obj (Opposite.op U))
    (h : g.hom.app (Opposite.op U) a = H.target.hom.app (Opposite.op U) r) :
    ∃ z : (AlgebraicSpaces.fiberProduct C S hS g H.target).obj.obj (Opposite.op U),
      ((GroupoidInAlgebraicSpaces.fiberProductSnd g H.target ≫ H.source).hom).app
          (Opposite.op U) z =
        H.source.hom.app (Opposite.op U) r := by
  refine ⟨yonedaEquiv (pullback.lift (yonedaEquiv.symm a) (yonedaEquiv.symm r) (by
    apply yonedaEquiv.injective
    simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply] using h)), ?_⟩
  change H.source.hom.app (Opposite.op U)
    ((pullback.snd g.hom H.target.hom).app (Opposite.op U) (yonedaEquiv _)) = _
  rw [← yonedaEquiv_comp, pullback.lift_snd, Equiv.apply_symm_apply]

/-- The induced morphism of quotient stacks is a 1-morphism of fibred categories. -/
private lemma isFibredOneMorphism_quotientStackMap
    {G H : GroupoidInAlgebraicSpaces C S hS B} (f : GroupoidInAlgebraicSpaces.Hom G H) :
    (quotientStack G).p.IsFibredOneMorphism (quotientStack H).p
      (quotientStackMap f).toFunctor where
  comp_eq := (quotientStackMap f).w
  map_isStronglyCartesian := by
    intro R T g a b φ _
    have hlift := Functor.isHomLift_map_of_comp_eq (quotientStackMap f).w g φ
    exact (isFiberedInGroupoids_quotientStack H).isStronglyCartesian_homLift g
      ((quotientStackMap f).toFunctor.map φ)

/-- The inverse of `quotientPrestackEquivalence` as a functor over the site. -/
private noncomputable def quotientPrestackInverseBased (G : GroupoidInAlgebraicSpaces C S hS B) :
    BasedFunctor (quotientPrestack G)
      (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)) :=
  ⟨(quotientPrestackEquivalence G).inverse, rfl⟩

/-- The functor of `quotientPrestackEquivalence` as a functor over the site. -/
private noncomputable def quotientPrestackFunctorBased (G : GroupoidInAlgebraicSpaces C S hS B) :
    BasedFunctor (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors))
      (quotientPrestack G) :=
  ⟨(quotientPrestackEquivalence G).functor, quotientPrestackEquivalence_comp G⟩

/-- The counit of `quotientPrestackEquivalence` as a based natural isomorphism. -/
private noncomputable def quotientPrestackCounitBased (G : GroupoidInAlgebraicSpaces C S hS B) :
    (quotientPrestackInverseBased G).comp (quotientPrestackFunctorBased G) ≅
      BasedFunctor.id (quotientPrestack G) :=
  BasedNatIso.mkNatIso (quotientPrestackEquivalence G).counitIso (by
    intro x
    have hobj : (quotientPrestackEquivalence G).functor.obj
        ((quotientPrestackEquivalence G).inverse.obj x) = x := by
      dsimp [quotientPrestackEquivalence, ULiftHom.equiv]
      rfl
    rw [show (quotientPrestackEquivalence G).counitIso.hom.app x = eqToHom hobj from rfl]
    exact IsHomLift.eqToHom_domain_lift_id hobj rfl)

/-- Local essential surjectivity on fibres of the presentation of `[U/R]` followed by `[f]` is
that of `quotientMapUnderlying`, to which it is 2-isomorphic over the site. -/
private lemma locallyEssSurjOnFibers_toQuotientStack_comp_iff
    {G H : GroupoidInAlgebraicSpaces C S hS B} (f : GroupoidInAlgebraicSpaces.Hom G H) :
    Functor.LocallyEssSurjOnFibers (isFiberedInGroupoids_quotientStack H).isFibered
        ((isFibredOneMorphism_toQuotientStack G).comp
          (isFibredOneMorphism_quotientStackMap f)).comp_eq (BigFppfOver.topology C S hS) ↔
      Functor.LocallyEssSurjOnFibers (isFiberedInGroupoids_quotientStack H).isFibered
        (quotientMapUnderlying_comp f) (BigFppfOver.topology C S hS) := by
  let P := quotientPrestack G
  let bF := quotientStackMap f
  let bInv := quotientPrestackInverseBased G
  let bEFun := quotientPrestackFunctorBased G
  let eCounit := quotientPrestackCounitBased G
  let bU : BasedFunctor P (quotientStack H) :=
    bInv.comp ((quotientPointwiseMap f).comp (pointwiseToQuotientStackBased H))
  let bToQG : BasedFunctor P (quotientStack G) :=
    ⟨toQuotientStack G, (isFibredOneMorphism_toQuotientStack G).comp_eq⟩
  let bPtQG := bEFun.comp bToQG
  let eComm := quotientStackMap_commutes f
  let e₁Ord := Functor.isoWhiskerLeft bInv.toFunctor (asIso eComm.hom.toNatTrans)
  let e₁ : bU ≅ bInv.comp (bPtQG.comp bF) :=
    BasedNatIso.mkNatIso e₁Ord fun x => eComm.hom.isHomLift (a := bInv.obj x) (bInv.w_obj x)
  let e₂Ord := Functor.isoWhiskerLeft bInv.toFunctor
    (Functor.associator bEFun.toFunctor bToQG.toFunctor bF.toFunctor)
  let e₂ : bInv.comp (bPtQG.comp bF) ≅ bInv.comp (bEFun.comp (bToQG.comp bF)) :=
    BasedNatIso.mkNatIso e₂Ord fun x => IsHomLift.id ((bInv.comp (bPtQG.comp bF)).w_obj x)
  let e₃Ord := (Functor.associator bInv.toFunctor bEFun.toFunctor
    (bToQG.toFunctor ⋙ bF.toFunctor)).symm
  let e₃ : bInv.comp (bEFun.comp (bToQG.comp bF)) ≅
      (bInv.comp bEFun).comp (bToQG.comp bF) :=
    BasedNatIso.mkNatIso e₃Ord fun x =>
      IsHomLift.id (((bInv.comp bEFun).comp (bToQG.comp bF)).w_obj x)
  let e₄Ord := Functor.isoWhiskerRight (asIso eCounit.hom.toNatTrans)
    (bToQG.toFunctor ⋙ bF.toFunctor)
  let e₄ : (bInv.comp bEFun).comp (bToQG.comp bF) ≅
      (BasedFunctor.id P).comp (bToQG.comp bF) :=
    BasedNatIso.mkNatIso e₄Ord (by
      intro x
      have hc := eCounit.hom.isHomLift (a := x) rfl
      have : P.p.IsHomLift (𝟙 (P.p.obj x)) (eCounit.hom.app x) := hc
      have hm := Functor.isHomLift_map_of_comp_eq (bToQG.comp bF).w
        (𝟙 (P.p.obj x)) (eCounit.hom.app x)
      change (quotientStack H).p.IsHomLift (𝟙 (P.p.obj x))
        (bF.map (bToQG.map (eCounit.hom.app x)))
      exact hm)
  let e₅Ord := Functor.leftUnitor (bToQG.toFunctor ⋙ bF.toFunctor)
  let e₅ : (BasedFunctor.id P).comp (bToQG.comp bF) ≅ bToQG.comp bF :=
    BasedNatIso.mkNatIso e₅Ord (by
      intro x
      rw [Functor.leftUnitor_hom_app]
      exact IsHomLift.id ((bToQG.comp bF).w_obj x))
  let e : bU ≅ bToQG.comp bF := e₁.trans (e₂.trans (e₃.trans (e₄.trans e₅)))
  exact (Functor.locallyEssSurjOnFibers_congr (X := P) (Y := quotientStack H) (F := bU)
    (G := bToQG.comp bF) (isFiberedInGroupoids_quotientStack H).isFibered
    (e₁Ord.trans (e₂Ord.trans (e₃Ord.trans (e₄Ord.trans e₅Ord))))
    (fun x {T} hx => e.hom.isHomLift (a := x) hx) _).symm

/-- If the saturation map is surjective as a map of fppf sheaves, then the pullback of every
presented object of `[U'/R']` along the members of a covering sieve is in the essential image of
`quotientMapUnderlying` on fibres. -/
private lemma exists_sieve_essImage_of_isLocallySurjective
    {G H : GroupoidInAlgebraicSpaces C S hS B} (f : GroupoidInAlgebraicSpaces.Hom G H)
    (hsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
      ((GroupoidInAlgebraicSpaces.fiberProductSnd
          (ObjectProperty.homMk f.toGroupoidHom.mapObjects : G.objects ⟶ H.objects)
          H.target ≫ H.source).hom))
    (U : BigFppfOver C S hS) (b : H.objects.obj.obj (Opposite.op U)) :
    ∃ R ∈ BigFppfOver.topology C S hS U, ∀ ⦃V⦄ (k : V ⟶ U), R.arrows k →
      (Functor.fiberFunctorOfCompEq (quotientMapUnderlying_comp f) V).essImage
        (Functor.pullbackFiber (quotientStack H).p
          ((pointwiseToQuotientStackFiber H U).obj b) k) := by
  let J := BigFppfOver.topology C S hS
  let g : G.objects ⟶ H.objects := ObjectProperty.homMk f.toGroupoidHom.mapObjects
  let φ := (GroupoidInAlgebraicSpaces.fiberProductSnd g H.target ≫ H.source).hom
  refine ⟨Presheaf.imageSieve φ b, Presheaf.imageSieve_mem J φ b, ?_⟩
  rintro V k ⟨z, hz⟩
  let a := (pullback.fst g.hom H.target.hom).app (Opposite.op V) z
  let r := (pullback.snd g.hom H.target.hom).app (Opposite.op V) z
  have hs : H.source.hom.app (Opposite.op V) r = H.objects.obj.map k.op b := hz
  have ht : H.target.hom.app (Opposite.op V) r =
      f.toGroupoidHom.mapObjects.app (Opposite.op V) a :=
    (congrArg (fun t => t.app (Opposite.op V) z)
      (pullback.condition (f := g.hom) (g := H.target.hom))).symm
  let ar : (show H.toGroupoidInFunctors.Evaluation (Opposite.op V) from
      H.objects.obj.map k.op b) ⟶ f.toGroupoidHom.mapObjects.app (Opposite.op V) a :=
    (H.toGroupoidInFunctors.evaluationArrowEquiv (Opposite.op V)
      (H.objects.obj.map k.op b)
      (f.toGroupoidHom.mapObjects.app (Opposite.op V) a)).symm ⟨r, hs, ht⟩
  exact ⟨prestackPoint G V a, ⟨eqToIso (quotientMapUnderlying_point f V a) ≪≫
    ((pointwiseToQuotientStackFiber H V).mapIso (asIso ar)).symm ≪≫
    (presentedPullbackIso H U b _ rfl (Over.mk k)).symm⟩⟩

/-- Surjectivity of the saturation map as a map of fppf sheaves gives local essential
surjectivity on fibres of `quotientMapUnderlying`. -/
private lemma locallyEssSurjOnFibers_of_isLocallySurjective
    {G H : GroupoidInAlgebraicSpaces C S hS B} (f : GroupoidInAlgebraicSpaces.Hom G H)
    (hsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
      ((GroupoidInAlgebraicSpaces.fiberProductSnd
          (ObjectProperty.homMk f.toGroupoidHom.mapObjects : G.objects ⟶ H.objects)
          H.target ≫ H.source).hom)) :
    Functor.LocallyEssSurjOnFibers (isFiberedInGroupoids_quotientStack H).isFibered
      (quotientMapUnderlying_comp f) (BigFppfOver.topology C S hS) := by
  let J := BigFppfOver.topology C S hS
  let QH := quotientStack H
  intro U y
  obtain ⟨R, hR, hRrep⟩ := essImage_toQuotientStack H U y
  have hLocal : ∀ ⦃V⦄ (k : V ⟶ U), R.arrows k →
      ∃ T ∈ J V, ∀ ⦃W⦄ (l : W ⟶ V), T.arrows l →
        (Functor.fiberFunctorOfCompEq (quotientMapUnderlying_comp f) W).essImage
          (Functor.pullbackFiber QH.p (Functor.pullbackFiber QH.p y k) l) := by
    intro V k hk
    obtain ⟨z, ⟨ez⟩⟩ := hRrep hk
    obtain ⟨b, rfl⟩ := exists_prestackPoint H V z
    obtain ⟨T, hT, hTrep⟩ := exists_sieve_essImage_of_isLocallySurjective f hsurj V b
    refine ⟨T, hT, fun W l hl => ?_⟩
    obtain ⟨a, ⟨ea⟩⟩ := hTrep l hl
    exact ⟨a, ⟨ea ≪≫ Functor.pullbackFiberIso
      ((eqToIso (presented_eq_image H V b)).symm ≪≫ ez) l⟩⟩
  let T : ∀ ⦃V⦄ (k : V ⟶ U), R.arrows k → Sieve V := fun {V} k hk => (hLocal k hk).choose
  refine ⟨Sieve.bind R T, J.transitive hR _ ?_, ?_⟩
  · intro V k hk
    exact J.superset_covering (Sieve.le_pullback_bind R T k hk) (hLocal k hk).choose_spec.1
  · intro W m hm
    obtain ⟨V, l, k, hk, hl, rfl⟩ := hm
    obtain ⟨a, ⟨ea⟩⟩ := (hLocal k hk).choose_spec.2 l hl
    exact ⟨a, ⟨ea ≪≫ Functor.pullbackFiberCompIso y k l⟩⟩

/-- Local essential surjectivity on fibres of `quotientMapUnderlying` gives surjectivity of the
saturation map as a map of fppf sheaves. -/
private lemma isLocallySurjective_of_locallyEssSurjOnFibers
    {G H : GroupoidInAlgebraicSpaces C S hS B} (f : GroupoidInAlgebraicSpaces.Hom G H)
    (hess : Functor.LocallyEssSurjOnFibers (isFiberedInGroupoids_quotientStack H).isFibered
      (quotientMapUnderlying_comp f) (BigFppfOver.topology C S hS)) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
      ((GroupoidInAlgebraicSpaces.fiberProductSnd
          (ObjectProperty.homMk f.toGroupoidHom.mapObjects : G.objects ⟶ H.objects)
          H.target ≫ H.source).hom) := by
  let J := BigFppfOver.topology C S hS
  let g : G.objects ⟶ H.objects := ObjectProperty.homMk f.toGroupoidHom.mapObjects
  refine ⟨?_⟩
  intro U b
  obtain ⟨R, hR, hRrep⟩ := hess U ((pointwiseToQuotientStackFiber H U).obj b)
  apply J.superset_covering ?_ hR
  intro V k hk
  obtain ⟨z, ⟨ez⟩⟩ := hRrep k hk
  obtain ⟨a, rfl⟩ := exists_prestackPoint G V z
  let e : (pointwiseToQuotientStackFiber H V).obj (H.objects.obj.map k.op b) ≅
      (pointwiseToQuotientStackFiber H V).obj
        (f.toGroupoidHom.mapObjects.app (Opposite.op V) a) :=
    (presentedPullbackIso H U b _ rfl (Over.mk k)).symm ≪≫
      ez.symm ≪≫ eqToIso (quotientMapUnderlying_point f V a)
  obtain ⟨r, hs, ht⟩ := exists_arrow_of_presented_iso H V _ _ e
  obtain ⟨z, hz⟩ := exists_pullback_section g V a r ht.symm
  exact ⟨z, hz.trans hs⟩

/-- Surjectivity of the saturation map as a map of fppf sheaves is exactly local essential
surjectivity on fibres of the induced morphism of quotient stacks. -/
private theorem locallySurjective_iff_locallyEssSurjOnFibers
    {G H : GroupoidInAlgebraicSpaces C S hS B}
    (f : GroupoidInAlgebraicSpaces.Hom G H) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
        ((GroupoidInAlgebraicSpaces.fiberProductSnd
            (ObjectProperty.homMk f.toGroupoidHom.mapObjects : G.objects ⟶ H.objects)
            H.target ≫ H.source).hom) ↔
      Functor.LocallyEssSurjOnFibers (isFibered_quotientStack H) (quotientStackMap f).w
        (BigFppfOver.topology C S hS) := by
  have hEssα : Functor.LocallyEssSurjOnFibers (isFiberedInGroupoids_quotientStack G).isFibered
      (isFibredOneMorphism_toQuotientStack G).comp_eq (BigFppfOver.topology C S hS) :=
    fun U x => essImage_toQuotientStack G U x
  have hCompIff := Functor.locallyEssSurjOnFibers_comp_iff
    (isFiberedInGroupoids_quotientStack G).isFibered
    (isFiberedInGroupoids_quotientStack H).isFibered (isFibredOneMorphism_toQuotientStack G)
    (isFibredOneMorphism_quotientStackMap f) _ hEssα
  exact (Iff.intro (locallyEssSurjOnFibers_of_isLocallySurjective f)
    (isLocallySurjective_of_locallyEssSurjOnFibers f)).trans
      (hCompIff.symm.trans (locallyEssSurjOnFibers_toQuotientStack_comp_iff f)).symm

/-- **Stacks 046T.** The induced morphism of quotient stacks `[f] : [U/R] ⟶ [U'/R']` is an
equivalence over the big fppf site if and only if (1) `(U, R, s, t, c)` is the restriction of
`(U', R', s', t', c')` along `f : U ⟶ U'`, i.e. the square formed by the arrow map of `f` and the
two source–target maps is cartesian, and (2) the saturation map
`U ×_{f, U', t'} R' ⟶ R' ⟶ U'` is a surjection of fppf sheaves. -/
@[stacks 046T "equivalence_criterion"]
public theorem quotientStackMap_isEquivalenceOver_iff
    {G H : GroupoidInAlgebraicSpaces C S hS B}
    (f : GroupoidInAlgebraicSpaces.Hom G H) :
    Nonempty (Functor.IsEquivalenceOver (quotientStack G).p (quotientStack H).p
      (quotientStackMap f).toFunctor) ↔
      (IsPullback f.toGroupoidHom.mapArrows
          (prod.lift G.toGroupoidInFunctors.source G.toGroupoidInFunctors.target)
          (prod.lift H.toGroupoidInFunctors.source H.toGroupoidInFunctors.target)
          (prod.map f.toGroupoidHom.mapObjects f.toGroupoidHom.mapObjects) ∧
        Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
          ((GroupoidInAlgebraicSpaces.fiberProductSnd
              (ObjectProperty.homMk f.toGroupoidHom.mapObjects : G.objects ⟶ H.objects)
              H.target ≫ H.source).hom)) := by
  let F := (quotientStackMap f).toFunctor
  have hFf := isFibredOneMorphism_quotientStackMap f
  have hstackG := isStack_quotientStack G
  have hstackH := isStack_quotientStack H
  have hFF := fullyFaithful_quotientStackMap_iff_isPullback f
  constructor
  · rintro ⟨heData⟩
    let e : (quotientStack G).obj ≌ (quotientStack H).obj :=
      CategoryTheory.Equivalence.mk F heData.inv heData.unitIso.symm heData.counitIso
    let hff := e.fullyFaithfulFunctor
    have : F.Full := hff.full
    have : F.Faithful := hff.faithful
    exact ⟨hFF.mp ⟨hff⟩, (locallySurjective_iff_locallyEssSurjOnFibers f).2
      ((Functor.isEquivalenceOver_iff_locallyEssSurjOnFibers hstackG hstackH hFf).mp ⟨heData⟩)⟩
  · rintro ⟨hpull, hsurj⟩
    let hff := (hFF.mpr hpull).some
    have : F.Full := hff.full
    have : F.Faithful := hff.faithful
    exact (Functor.isEquivalenceOver_iff_locallyEssSurjOnFibers hstackG hstackH hFf).mpr
      ((locallySurjective_iff_locallyEssSurjOnFibers f).1 hsurj)

end AlgebraicGeometry.Stack

end
