module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackProjection
public import StacksFrontier.CategoryTheory.Sites.Stack.IsomPresheaf
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverRepresentable
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal

/-!
# The sheaf of isomorphisms between two presented objects of a quotient stack

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `B` over a
scheme `S` of a big fppf site, and let `[U/R]` be its quotient stack. Two points `x`, `y` of the
object space `U` over a test object `T` present two objects of `[U/R]` over `T`, and Stacks 044V
computes the sheaf `Isom(x, y)` on the fppf slice site over `T`: it is the fibre product

    R ×_{(t, s), U × U} T,

the sheaf whose sections over `V ⟶ T` are the arrows of `R` whose target is the restriction of
`x` and whose source is the restriction of `y`.

Two forms of the identification are proved. The first says that the canonical comparison map out
of the morphism presheaf of the pointwise groupoid fibration — the map induced by
`AlgebraicGeometry.Stack.toQuotientStack` — is already an isomorphism, so nothing is lost by
passing to the stackification. The second transports that along the description of the pointwise
morphism presheaf as the above fibre product, and is accompanied by lemmas pinning down the
identification on every arrow of the pointwise groupoid, in both directions.

## Main definitions

* `AlgebraicGeometry.Stack.arrowFiber` and `AlgebraicGeometry.Stack.arrowFiberOver`: the fibre
  product `R ×_{U × U} T`, as a sheaf on the whole site and as a sheaf on the slice over `T`.
* `AlgebraicGeometry.Stack.pointwiseToQuotientStackFiber`: the evaluated groupoid at `T` mapping
  to the fibre of the quotient stack over `T`.
* `AlgebraicGeometry.Stack.presentedPullbackIso`: the chosen pullback of a presented object along
  `V ⟶ T` is the object presented by the restricted point.
* `AlgebraicGeometry.Stack.pointwiseArrowSection`: the section of `Isom(x, y)` named by an arrow
  of the evaluated groupoid.
* `AlgebraicGeometry.Stack.IsCanonicalArrowFiberIso`: the property that an identification of
  `Isom(x, y)` with the slice fibre product is the canonical one, namely that it recovers each
  arrow of the evaluated groupoid from the isomorphism that arrow induces.
* `AlgebraicGeometry.Stack.isomPresheafPullbackIso`: the identification itself.

## Main results

* `AlgebraicGeometry.Stack.isomPresheaf_equiv_arrowFiber`: **Stacks 044V** — the canonical map
  from the morphism presheaf of the pointwise groupoid fibration to that of the quotient stack is
  an isomorphism.
* `AlgebraicGeometry.Stack.isomPresheaf_iso_pullback`: **Stacks 044V** — `Isom(x, y)` is the
  slice fibre product of the arrow space along the two points, by a canonical identification.
* `AlgebraicGeometry.Stack.isomPresheafPullbackIso_hom_app` and
  `AlgebraicGeometry.Stack.isomPresheafPullbackIso_inv_app`: **Stacks 044V** — the two directions
  of that identification on an arrow of the evaluated groupoid.

## Implementation notes

The first form is proved by exhibiting the morphism presheaf of the pointwise groupoid fibration
as a *sheaf*: by Stacks 02ZN the comparison with the stackification is locally bijective, and a
locally bijective map between sheaves is an isomorphism. Sheafiness in turn comes from the
description of that morphism presheaf as `arrowFiberOver`, which is a fibre product of sheaves.

The comparison used throughout is the *canonical* one, not an arbitrary natural bijection: it is
`CategoryTheory.Functor.IsFibredOneMorphism.morPresheafMap` for the first form and, for the
pullback description, `pointwiseArrowSection`, which applies
`AlgebraicGeometry.Stack.pointwiseToQuotientStack` to an arrow of the evaluated groupoid and
conjugates by the canonical comparisons with the chosen cartesian pullbacks. The component lemmas
therefore specify the identification over every object of the slice, including the identities, and
so rule out translating it by a nonidentity automorphism.

The first section below is general: for a presheaf of categories `F` on a base `D` whose
Grothendieck construction maps to a fibred category `p : E ⥤ D` by a fibred 1-morphism `H`, it
compares the morphism presheaf of `F` at a pair of points of a fibre with the morphism presheaf of
`p` at their images, and shows the comparison is an isomorphism when `H` is fully faithful. Only
the quotient stack uses it here, but nothing in it is about algebraic spaces.

## References

* [Stacks Project, Tag 02ZB](https://stacks.math.columbia.edu/tag/02ZB)
* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 044V](https://stacks.math.columbia.edu/tag/044V)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Pseudofunctor Opposite

namespace AlgebraicGeometry.Stack

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}}
  {hS : C.Contains S} {B : AlgebraicSpaces C S hS}

/-- The fibre product of the arrow space with a presented pair of points. -/
noncomputable abbrev arrowFiber
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (x y : G.objects.obj.obj (Opposite.op T)) :
    (BigFppfOver C S hS)ᵒᵖ ⥤ Type u :=
  pullback
    (prod.lift (yonedaEquiv.symm y) (yonedaEquiv.symm x))
    (prod.lift G.target.hom G.source.hom)

/-- The slice presheaf represented by the arrow-space fibre product: a section
over `V ⟶ T` is an arrow whose endpoints are the restrictions of `x` and `y`
along that particular map `V ⟶ T`. -/
noncomputable abbrev arrowFiberOver
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (x y : G.objects.obj.obj (Opposite.op T)) :
    (Over T)ᵒᵖ ⥤ Type u :=
  OverShriek.fiber (𝟙 (yoneda.obj T))
    (pullback.fst
      (prod.lift (yonedaEquiv.symm y) (yonedaEquiv.symm x))
      (prod.lift G.target.hom G.source.hom))

attribute [local implicit_reducible] Bicategory.InducedBicategory fibredCategory
  CategoryTheory.Functor.toPseudofunctor'
  CategoryTheory.pseudofunctorOfIsLocallyDiscrete Quiver.Hom.toLoc
  BasedCategory.ofFunctor Grpd.forgetToCat Grpd.of typeToGrpd
  Pseudofunctor.CoGrothendieck.forget Pseudofunctor.CoGrothendieck.ι
  AlgebraicSpaces.fiberProduct GroupoidInAlgebraicSpaces.toGroupoidInFunctors
  CategoryTheory.Functor.Fiber CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.Fiber.inducedFunctor

section
universe baseObj baseHom fiberObj fiberHom targetObj targetHom
variable {D : Type baseObj} [Category.{baseHom} D]
  (F : Dᵒᵖ ⥤ Cat.{fiberHom, fiberObj})
  {E : Type targetObj} [Category.{max fiberHom targetHom} E] (p : E ⥤ D) [p.IsFibered]
  (H : CoGrothendieck F.toPseudofunctor' ⥤ E)
  (hH : (CoGrothendieck.forget F.toPseudofunctor').IsFibredOneMorphism p H)

private noncomputable abbrev imageFiber (T : D) : F.obj (op T) ⥤ p.Fiber T :=
  Functor.Fiber.inducedFunctor (F := CoGrothendieck.ι F.toPseudofunctor' T ⋙ H)
    (by rw [Functor.assoc, hH.comp_eq]; exact CoGrothendieck.comp_const _ T)

private noncomputable def liftIso (T : D) (point : F.obj (op T)) (V : Over T) :
    Functor.pullbackFiber p ((imageFiber F p H hH T).obj point) V.hom ≅
      (imageFiber F p H hH V.left).obj ((F.map V.hom.op).toFunctor.obj point) := by
  have hc := CoGrothendieck.isStronglyCartesian_homCartesianLift
    (F := F.toPseudofunctor') (a := point) V.hom
  have hcart := hH.map_isStronglyCartesian V.hom
    (CoGrothendieck.cartesianLift (F := F.toPseudofunctor') point V.hom) hc
  exact Functor.fiberIsoOfCartesian V.hom
    (Functor.IsPreFibered.pullbackMap ((imageFiber F p H hH T).obj point).2 V.hom)
    (H.map (CoGrothendieck.cartesianLift (F := F.toPseudofunctor') point V.hom))
    inferInstance inferInstance

/-- The comparison `liftIso` composed with the image of the cartesian lift is the chosen pullback
map. -/
private lemma liftIso_hom_fac (T : D) (point : F.obj (op T)) (V : Over T) :
    Functor.Fiber.fiberInclusion.map (liftIso F p H hH T point V).hom ≫
      H.map (CoGrothendieck.cartesianLift (F := F.toPseudofunctor') point V.hom) =
      Functor.IsPreFibered.pullbackMap ((imageFiber F p H hH T).obj point).2 V.hom :=
  Functor.fiberIsoOfCartesian_hom_fac (p := p) _ _ _ _ _

/-- The inverse of `liftIso` composed with the chosen pullback map is the image of the cartesian
lift. -/
private lemma liftIso_inv_fac (T : D) (point : F.obj (op T)) (V : Over T) :
    Functor.Fiber.fiberInclusion.map (liftIso F p H hH T point V).inv ≫
      Functor.IsPreFibered.pullbackMap ((imageFiber F p H hH T).obj point).2 V.hom =
      H.map (CoGrothendieck.cartesianLift (F := F.toPseudofunctor') point V.hom) :=
  Functor.fiberIsoOfCartesian_inv_fac (p := p) _ _ _ _ _

/- Reading an arrow of the fibre over `T` as an arrow of `E` undoes the passage to the fibre: it
is the image under `H` of the corresponding arrow of the Grothendieck construction. The two sides
are definitionally equal, but `CategoryTheory.Functor.Fiber` is not unfolded at `implicit`
transparency, so the equation has to be named for `rw` to see it. -/
omit [p.IsFibered] in
private lemma fiberInclusion_map_imageFiber_map (T : D) {first second : F.obj (op T)}
    (arrow : first ⟶ second) :
    Functor.Fiber.fiberInclusion.map ((imageFiber F p H hH T).map arrow) =
      H.map ((CoGrothendieck.ι F.toPseudofunctor' T).map arrow) := rfl

private noncomputable def rawRestriction (T : D) (point : F.obj (op T))
    {V W : Over T} (morphism : V ⟶ W) :
    CoGrothendieck.domainCartesianLift (F := F.toPseudofunctor') point V.hom ⟶
      CoGrothendieck.domainCartesianLift (F := F.toPseudofunctor') point W.hom :=
  { base := morphism.left
    fiber := eqToHom (by
      change (F.map V.hom.op).toFunctor.obj point =
        (F.map morphism.left.op).toFunctor.obj ((F.map W.hom.op).toFunctor.obj point)
      rw [← Cat.Hom.comp_obj, ← F.map_comp, ← op_comp, Over.w]) }

private lemma rawRestriction_fac (T : D) (point : F.obj (op T))
    {V W : Over T} (morphism : V ⟶ W) :
    rawRestriction F T point morphism ≫
      CoGrothendieck.cartesianLift (F := F.toPseudofunctor') point W.hom =
      CoGrothendieck.cartesianLift (F := F.toPseudofunctor') point V.hom := by
  apply CoGrothendieck.Hom.ext _ _ (Over.w morphism)
  simp [rawRestriction, Functor.toPseudofunctor'_mapComp]

private lemma rawRestriction_naturality (T : D) (first second : F.obj (op T))
    {V W : Over T} (morphism : V ⟶ W)
    (arrow : (F.toPseudofunctor'.presheafHom first second).obj (op W)) :
    (CoGrothendieck.ι F.toPseudofunctor' V.left).map
        ((F.toPseudofunctor'.presheafHom first second).map morphism.op arrow) ≫
      rawRestriction F T second morphism =
    rawRestriction F T first morphism ≫
      (CoGrothendieck.ι F.toPseudofunctor' W.left).map arrow := by
  apply CoGrothendieck.Hom.ext _ _ (by simp [rawRestriction, CoGrothendieck.ι])
  simp only [presheafHom, LocallyDiscreteOpToCat.pullHom, Cat.Hom.comp_toFunctor,
    Functor.comp_obj, mapComp', Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom, Iso.trans_inv,
    Functor.mapIso_inv, eqToIso.inv, Quiver.Hom.unop_op, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk,
    rawRestriction, CoGrothendieck.categoryStruct_comp_base, op_comp, Quiver.Hom.comp_toLoc,
    CoGrothendieck.categoryStruct_comp_fiber, CoGrothendieck.ι_map_fiber, op_id,
    Quiver.Hom.id_toLoc, PrelaxFunctor.mapFunctor_map, PrelaxFunctor.map₂_eqToHom,
    Functor.toPseudofunctor'_mapComp, eqToHom_trans, Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app,
    Cat.Hom.id_toFunctor, Functor.toPseudofunctor'_mapId, Functor.id_obj, Category.assoc,
    eqToHom_map, Functor.map_comp]
  congr 1
  congr 1
  exact (eqToHom_trans _ _).symm

private lemma liftIso_naturality (T : D) (point : F.obj (op T))
    {V W : Over T} (morphism : V ⟶ W) :
    Functor.pullbackFiberMap p ((imageFiber F p H hH T).obj point) morphism ≫
      Functor.Fiber.fiberInclusion.map (liftIso F p H hH T point W).hom =
    Functor.Fiber.fiberInclusion.map (liftIso F p H hH T point V).hom ≫
      H.map (rawRestriction F T point morphism) := by
  have hl : p.IsHomLift morphism.left
      (Functor.pullbackFiberMap p ((imageFiber F p H hH T).obj point) morphism ≫
        Functor.Fiber.fiberInclusion.map (liftIso F p H hH T point W).hom) := by
    simpa using (inferInstance : p.IsHomLift (morphism.left ≫ 𝟙 W.left) _)
  have hm : (CoGrothendieck.forget F.toPseudofunctor').IsHomLift morphism.left
      (rawRestriction F T point morphism) := by
    show (CoGrothendieck.forget F.toPseudofunctor').IsHomLift
      ((CoGrothendieck.forget F.toPseudofunctor').map (rawRestriction F T point morphism)) _
    infer_instance
  have hh := hH.map_isHomLift morphism.left (rawRestriction F T point morphism)
  have hr : p.IsHomLift morphism.left
      (Functor.Fiber.fiberInclusion.map (liftIso F p H hH T point V).hom ≫
        H.map (rawRestriction F T point morphism)) := by
    simpa using (inferInstance : p.IsHomLift (𝟙 V.left ≫ morphism.left) _)
  have hc := hH.map_isStronglyCartesian W.hom
    (CoGrothendieck.cartesianLift (F := F.toPseudofunctor') point W.hom)
    (CoGrothendieck.isStronglyCartesian_homCartesianLift (F := F.toPseudofunctor') point W.hom)
  apply Functor.IsStronglyCartesian.ext p W.hom
    (H.map (CoGrothendieck.cartesianLift (F := F.toPseudofunctor') point W.hom))
    morphism.left
  simp only [Category.assoc, liftIso_hom_fac]
  rw [Functor.pullbackFiberMap_fac, ← H.map_comp, rawRestriction_fac, liftIso_hom_fac]

private noncomputable def homToMor (T : D) (first second : F.obj (op T)) :
    (F.toPseudofunctor'.presheafHom first second ⋙ uliftFunctor.{targetHom}) ⟶
      Functor.morPresheaf p ((imageFiber F p H hH T).obj first)
        ((imageFiber F p H hH T).obj second) where
  app V := ↾fun arrow => (liftIso F p H hH T first V.unop).hom ≫
    (imageFiber F p H hH V.unop.left).map arrow.down ≫
      (liftIso F p H hH T second V.unop).inv
  naturality := by
    intro V W morphism
    ext arrow
    dsimp only [TypeCat.Fun.toFun_apply, types_comp_apply]
    apply Functor.morRestrict_uniq
    change Functor.Fiber.fiberInclusion.map
        ((liftIso F p H hH T first W.unop).hom ≫
          (imageFiber F p H hH W.unop.left).map
            ((F.toPseudofunctor'.presheafHom first second).map morphism arrow.down) ≫
          (liftIso F p H hH T second W.unop).inv) ≫ _ =
        Functor.pullbackFiberMap p ((imageFiber F p H hH T).obj first) morphism.unop ≫
          Functor.Fiber.fiberInclusion.map
            ((liftIso F p H hH T first V.unop).hom ≫
              (imageFiber F p H hH V.unop.left).map arrow.down ≫
              (liftIso F p H hH T second V.unop).inv) ≫ _
    simp only [Functor.Fiber.fiberInclusion.map_comp, Category.assoc]
    rw [liftIso_inv_fac, liftIso_inv_fac]
    change _ = Functor.pullbackFiberMap p ((imageFiber F p H hH T).obj first)
      morphism.unop ≫ Functor.Fiber.fiberInclusion.map (liftIso F p H hH T first V.unop).hom ≫
        H.map ((CoGrothendieck.ι F.toPseudofunctor' V.unop.left).map arrow.down) ≫ _
    rw [← Category.assoc, ← Category.assoc, liftIso_naturality]
    simp only [Category.assoc]
    rw [fiberInclusion_map_imageFiber_map, ← H.map_comp, ← H.map_comp, ← H.map_comp]
    congr 2
    rw [← rawRestriction_fac F T second morphism.unop, ← Category.assoc]
    have comparison := rawRestriction_naturality F T first second morphism.unop arrow.down
    simpa only [Quiver.Hom.op_unop, Category.assoc] using
      congrArg (fun raw => raw ≫ CoGrothendieck.cartesianLift
        (F := F.toPseudofunctor') second V.unop.hom) comparison

private noncomputable def imageFiberFullyFaithful (full : H.FullyFaithful) (T : D) :
    (imageFiber F p H hH T).FullyFaithful := by
  let inclusion := Functor.Fiber.inducedFunctor
    (CoGrothendieck.comp_const F.toPseudofunctor' T)
  letI : (imageFiber F p H hH T).Faithful := {
    map_injective := fun {first second} left right comparison => by
      apply inclusion.map_injective
      apply Functor.Fiber.hom_ext
      apply full.map_injective
      exact Functor.Fiber.fiberInclusion.congr_map comparison }
  letI : (imageFiber F p H hH T).Full := {
    map_surjective := fun {first second} arrow => by
      obtain ⟨raw, hraw⟩ := full.map_surjective (Functor.Fiber.fiberInclusion.map arrow)
      have hl : (CoGrothendieck.forget F.toPseudofunctor').IsHomLift (𝟙 T) raw := by
        rw [← hH.comp_eq]
        apply (Functor.isHomLift_comp_iff H p _ raw).2
        rw [hraw]
        exact arrow.2
      let lifted : inclusion.obj first ⟶ inclusion.obj second := ⟨raw, hl⟩
      obtain ⟨preimage, hpreimage⟩ := inclusion.map_surjective lifted
      refine ⟨preimage, ?_⟩
      apply Functor.Fiber.hom_ext
      change H.map (Functor.Fiber.fiberInclusion.map (inclusion.map preimage)) = _
      rw [hpreimage]
      exact hraw }
  exact Functor.FullyFaithful.ofFullyFaithful _

private lemma homToMor_isIso (full : H.FullyFaithful) (T : D)
    (first second : F.obj (op T)) : IsIso (homToMor F p H hH T first second) := by
  apply (NatTrans.isIso_iff_isIso_app _).2
  intro V
  apply (CategoryTheory.isIso_iff_bijective _).2
  exact (Equiv.ulift.trans
    ((imageFiberFullyFaithful F p H hH full V.unop.left).homEquiv.trans
      (Iso.homCongr (liftIso F p H hH T first V.unop).symm
        (liftIso F p H hH T second V.unop).symm))).bijective

variable {E' : Type targetObj} [Category.{max fiberHom targetHom} E']
  (q : E' ⥤ D) [q.IsFibered] (K : E ⥤ E') (hK : p.IsFibredOneMorphism q K)

private lemma liftIso_comp (T : D) (point : F.obj (op T)) (V : Over T) :
    liftIso F q (H ⋙ K) (hH.comp hK) T point V =
      hK.mapPullbackFiberIso ((imageFiber F p H hH T).obj point) V.hom ≪≫
        (Functor.fiberFunctorOfCompEq hK.comp_eq V.left).mapIso
          (liftIso F p H hH T point V) := by
  apply Iso.ext
  apply Functor.Fiber.hom_ext
  have hc := (hH.comp hK).map_isStronglyCartesian V.hom
    (CoGrothendieck.cartesianLift (F := F.toPseudofunctor') point V.hom)
    (CoGrothendieck.isStronglyCartesian_homCartesianLift (F := F.toPseudofunctor') point V.hom)
  have hleft : q.IsHomLift (𝟙 V.left)
      (Functor.Fiber.fiberInclusion.map (liftIso F q (H ⋙ K) (hH.comp hK) T point V).hom) :=
    inferInstance
  have hright : q.IsHomLift (𝟙 V.left)
      (Functor.Fiber.fiberInclusion.map
        (hK.mapPullbackFiberIso ((imageFiber F p H hH T).obj point) V.hom ≪≫
          (Functor.fiberFunctorOfCompEq hK.comp_eq V.left).mapIso
            (liftIso F p H hH T point V)).hom) := inferInstance
  apply Functor.IsStronglyCartesian.ext q V.hom
    ((H ⋙ K).map (CoGrothendieck.cartesianLift (F := F.toPseudofunctor') point V.hom))
    (𝟙 V.left)
  simp only [Iso.trans_hom, Functor.Fiber.fiberInclusion.map_comp,
    Functor.mapIso_hom, Functor.fiberInclusion_map_fiberFunctorOfCompEq_map, Functor.comp_map,
    Category.assoc]
  have hfac := liftIso_hom_fac F q (H ⋙ K) (hH.comp hK) T point V
  rw [Functor.comp_map] at hfac
  rw [hfac, ← K.map_comp, liftIso_hom_fac F p H hH]
  exact (hK.mapPullbackFiberIso_hom_fac ((imageFiber F p H hH T).obj point) V.hom).symm

private lemma homToMor_comp (T : D) (first second : F.obj (op T)) :
    homToMor F q (H ⋙ K) (hH.comp hK) T first second =
      homToMor F p H hH T first second ≫
        hK.morPresheafMap ((imageFiber F p H hH T).obj first)
          ((imageFiber F p H hH T).obj second) := by
  ext V arrow
  show (liftIso F q (H ⋙ K) (hH.comp hK) T first V.unop).hom ≫
    (imageFiber F q (H ⋙ K) (hH.comp hK) V.unop.left).map arrow.down ≫
    (liftIso F q (H ⋙ K) (hH.comp hK) T second V.unop).inv = _
  rw [liftIso_comp F p H hH q K hK T first V.unop,
    liftIso_comp F p H hH q K hK T second V.unop]
  show _ = (hK.morPresheafMap ((imageFiber F p H hH T).obj first)
    ((imageFiber F p H hH T).obj second)).app V
      ((liftIso F p H hH T first V.unop).hom ≫
        (imageFiber F p H hH V.unop.left).map arrow.down ≫
        (liftIso F p H hH T second V.unop).inv)
  rw [Functor.IsFibredOneMorphism.morPresheafMap_app]
  simp only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.map_comp, Category.assoc]
  rfl


end

/-- The equivalent description of a section of the arrow-space fibre as an arrow
in `G.arrows` with the prescribed source and target. -/
private noncomputable abbrev arrowSections
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (x y : G.objects.obj.obj (Opposite.op T)) : (Over T)ᵒᵖ ⥤ Type u :=
  let A : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u := {
    obj := fun X => G.objects.obj.obj X × G.objects.obj.obj X
    map := fun {X Y} (f : X ⟶ Y) => ↾fun p =>
      (G.objects.obj.map f p.1, G.objects.obj.map f p.2)
    map_id := by intro X; ext p <;> simp
    map_comp := by intro X Y Z f g; ext p <;> simp }
  let φ : G.arrows.obj ⟶ A := {
    app := fun X => ↾fun a => (G.target.hom.app X a, G.source.hom.app X a)
    naturality := by intro X Y f; ext a <;> dsimp [A] <;> simp [NatTrans.naturality_apply] }
  let ρ : yoneda.obj T ⟶ A := {
    app := fun X => ↾fun f =>
      ((yonedaEquiv.symm y).app X f, (yonedaEquiv.symm x).app X f)
    naturality := by intro X Y f; ext g <;> dsimp [A] <;> simp }
  OverShriek.fiber ρ φ

section
open MonoidalCategory
/-- The sheaf of arrow sections with specified endpoints is the fibre of the
arrow-space sheaf over the pair of object-space sections. -/
private lemma arrowSections_isSheaf
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (x y : G.objects.obj.obj (Opposite.op T)) :
    Presieve.IsSheaf ((BigFppfOver.topology C S hS).over T)
      (arrowSections G T x y) := by
  let J := BigFppfOver.topology C S hS
  let A := G.objects.obj ⊗ G.objects.obj
  have hArrow : Presieve.IsSheaf J G.arrows.obj :=
    (isSheaf_iff_isSheaf_of_type J G.arrows.obj).1 G.arrows.property.isSheaf
  have hF : Presieve.IsSheaf (J.over T) ((Over.forget T).op ⋙ G.arrows.obj) :=
    Functor.op_comp_isSheaf_of_isSheaf_type (Over.forget T) (J.over T) hArrow
  have hO : Presieve.IsSheaf J A := by
    let X : Sheaf J (Type u) := ⟨G.objects.obj, G.objects.property.isSheaf⟩
    exact (isSheaf_iff_isSheaf_of_type J A).1 (Sheaf.tensorProd_isSheaf J X X)
  have hA : Presieve.IsSeparated (J.over T) ((Over.forget T).op ⋙ A) :=
    (Functor.op_comp_isSheaf_of_isSheaf_type (Over.forget T) (J.over T) hO).isSeparated
  unfold arrowSections
  exact OverShriek.isSheaf_fiber _ _ hF hA
end

/-- A locally bijective map on morphism presheaves is an isomorphism when both
presheaves satisfy descent. -/
private lemma isIso_morPresheafMap_of_isMorSheaf
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (x y : (quotientPrestack G).p.Fiber T)
    (hsrc : Functor.IsMorSheaf (quotientPrestack G).p
      (BigFppfOver.topology C S hS) T x y) :
    IsIso ((isFibredOneMorphism_toQuotientStack G).morPresheafMap x y) := by
  let J := BigFppfOver.topology C S hS
  let hG := isFibredOneMorphism_toQuotientStack G
  let x' := (Functor.fiberFunctorOfCompEq hG.comp_eq T).obj x
  let y' := (Functor.fiberFunctorOfCompEq hG.comp_eq T).obj y
  have htgt : Functor.IsMorSheaf (quotientStack G).p J T x' y' :=
    (isStack_quotientStack G).isMorSheaf T x' y'
  let src : Sheaf (J.over T) (Type (u + 1)) :=
    ⟨Functor.morPresheaf (quotientPrestack G).p x y, hsrc⟩
  let tgt : Sheaf (J.over T) (Type (u + 1)) :=
    ⟨Functor.morPresheaf (quotientStack G).p x' y', htgt⟩
  let θ : src ⟶ tgt := ⟨hG.morPresheafMap x y⟩
  have : IsIso θ :=
    (Sheaf.isLocallyBijective_iff_isIso θ).1 (isLocallyBijective_toQuotientStack G T x y)
  exact (sheafToPresheaf (J.over T) (Type (u + 1))).map_isIso θ

private noncomputable abbrev pointwiseCategoryFunctor
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (BigFppfOver C S hS)ᵒᵖ ⥤ Cat.{u, u} :=
  evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙ Grpd.forgetToCat

private lemma evaluationArrowEquiv_conjugate
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    {first first' second second' : G.toGroupoidInFunctors.Evaluation (op T)}
    (hfirst : first = first') (hsecond : second' = second) (arrow : first' ⟶ second') :
    (G.toGroupoidInFunctors.evaluationArrowEquiv (op T) first second
      (eqToHom hfirst ≫ arrow ≫ eqToHom hsecond)).1 =
      (G.toGroupoidInFunctors.evaluationArrowEquiv (op T) first' second' arrow).1 := by
  cases hfirst
  cases hsecond
  simp

private noncomputable def pointwiseHomArrowIso
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (first second : G.objects.obj.obj (op T)) :
    (pointwiseCategoryFunctor G).toPseudofunctor'.presheafHom first second ≅
      arrowSections G T first second := by
  refine NatIso.ofComponents (fun V => (Equiv.trans
    (G.toGroupoidInFunctors.evaluationArrowEquiv (op V.unop.left) _ _)
    { toFun := fun arrow => ⟨arrow.1, Prod.ext arrow.2.2 arrow.2.1⟩
      invFun := fun arrow => ⟨arrow.1,
        congrArg Prod.snd arrow.2, congrArg Prod.fst arrow.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }).toIso) ?_
  intro V W morphism
  ext arrow
  apply Subtype.ext
  change (G.toGroupoidInFunctors.evaluationArrowEquiv (op W.unop.left) _ _
    (((pointwiseCategoryFunctor G).toPseudofunctor'.presheafHom first second).map
      morphism arrow)).1 =
      G.arrows.obj.map morphism.unop.left.op
        (G.toGroupoidInFunctors.evaluationArrowEquiv (op V.unop.left) _ _ arrow).1
  dsimp only [pointwiseCategoryFunctor, evaluationGroupoidFunctor,
    Functor.toPseudofunctor'_obj, Functor.toPseudofunctor'_map, Grpd.forgetToCat,
    Functor.comp_obj, Functor.comp_map] at arrow ⊢
  dsimp only [Pseudofunctor.presheafHom, TypeCat.Fun.toFun_apply]
  simp only [LocallyDiscreteOpToCat.pullHom, Pseudofunctor.mapComp',
    PrelaxFunctor.map₂Iso_hom, PrelaxFunctor.map₂Iso_inv, PrelaxFunctor.map₂_eqToHom,
    Functor.toPseudofunctor'_mapComp, eqToIso.hom, eqToIso.inv,
    Iso.trans_hom, Iso.trans_inv, Cat.Hom₂.comp_app, Cat.eqToHom_app]
  simp only [TypeCat.ofHom_apply, eqToHom_trans]
  rw [evaluationArrowEquiv_conjugate]
  exact Deformation.evaluationMap_map_arrow G.toGroupoidInFunctors _ _

private lemma isFibredOneMorphism_presentationEquivalence
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (CoGrothendieck.forget (pointwiseCategoryFunctor G).toPseudofunctor').IsFibredOneMorphism
      (quotientPrestack G).p (quotientPrestackEquivalence G).functor where
  comp_eq := quotientPrestackEquivalence_comp G
  map_isStronglyCartesian := by
    intro R T morphism first second arrow hcart
    exact (quotientPrestackEquivalence G).isStronglyCartesian_map_functor
      (quotientPrestack G).p
      (quotientPrestackEquivalence_comp G) morphism arrow hcart

private lemma quotientPrestack_mor_isSheaf
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (first second : (quotientPrestack G).p.Fiber T) :
    Functor.IsMorSheaf (quotientPrestack G).p
      (BigFppfOver.topology C S hS) T first second := by
  let equivalence := quotientPrestackEquivalence G
  let hEquiv := isFibredOneMorphism_presentationEquivalence G
  let image := imageFiber.{u + 1, u, u, u, u + 1, u + 1}
    (pointwiseCategoryFunctor G) (quotientPrestack G).p
    equivalence.functor hEquiv T
  have surjective : Function.Surjective image.obj := by
    rintro ⟨point, hpoint⟩
    change point.base = T at hpoint
    cases hpoint
    exact ⟨point.fiber, rfl⟩
  obtain ⟨first', rfl⟩ := surjective first
  obtain ⟨second', rfl⟩ := surjective second
  have hHom : Presheaf.IsSheaf
      ((BigFppfOver.topology C S hS).over T)
      ((pointwiseCategoryFunctor G).toPseudofunctor'.presheafHom first' second') :=
    (Presheaf.isSheaf_of_iso_iff (pointwiseHomArrowIso G T first' second')).2
      ((isSheaf_iff_isSheaf_of_type _ _).2 (arrowSections_isSheaf G T first' second'))
  have hIso := homToMor_isIso.{u + 1, u, u, u, u + 1, u + 1} (pointwiseCategoryFunctor G)
    (quotientPrestack G).p equivalence.functor hEquiv
    equivalence.fullyFaithfulFunctor T first' second'
  exact (Presheaf.isSheaf_of_iso_iff (asIso
    (homToMor.{u + 1, u, u, u, u + 1, u + 1} (pointwiseCategoryFunctor G)
    (quotientPrestack G).p equivalence.functor hEquiv T first' second'))).1
      ((isSheaf_iff_isSheaf_of_type _ _).2
        ((Presieve.isSheaf_comp_uliftFunctor_iff _).2
          ((isSheaf_iff_isSheaf_of_type _ _).1 hHom)))

/-- The canonical map from pointwise groupoid arrows to isomorphisms between
their images in the quotient stack is an isomorphism of presheaves on the
fppf slice site. The pointwise-groupoid morphism presheaf is the fibre of
the arrow space over the chosen pair of object-space points. -/
@[stacks 044V]
theorem isomPresheaf_equiv_arrowFiber
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (x y : (quotientPrestack G).p.Fiber T) :
    IsIso ((isFibredOneMorphism_toQuotientStack G).morPresheafMap x y) :=
  isIso_morPresheafMap_of_isMorSheaf G T x y (quotientPrestack_mor_isSheaf G T x y)

/- The evaluated groupoid and the fibre of its Grothendieck construction carry definitionally
equal category structures, and the comparisons below are built by unfolding that equality. -/
open Opposite Pseudofunctor

/-- The pointwise groupoid maps to the fibre of the quotient stack by the canonical
`pointwiseToQuotientStack`, including its action on arrows. -/
noncomputable abbrev pointwiseToQuotientStackFiber
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS) :
    G.toGroupoidInFunctors.Evaluation (op T) ⥤ (quotientStack G).p.Fiber T :=
  Functor.Fiber.inducedFunctor
    (F := CoGrothendieck.ι
      (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
        Grpd.forgetToCat).toPseudofunctor' T ⋙ pointwiseToQuotientStack G)
    (by
      rw [Functor.assoc,
        (isFibredOneMorphism_pointwiseToQuotientStack G).comp_eq]
      exact CoGrothendieck.comp_const _ T)

/-- The chosen pullback of a presented stack object is canonically isomorphic to
the image of the restricted point. The comparison uses the pointwise cartesian
arrow `(V.hom, identity)` and its image under `pointwiseToQuotientStack`. -/
noncomputable def presentedPullbackIso
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (x' : G.objects.obj.obj (op T))
    (x : (quotientStack G).p.Fiber T)
    (hx : x.1 = (pointwiseToQuotientStack G).obj ⟨T, x'⟩)
    (V : Over T) :
    Functor.pullbackFiber (quotientStack G).p x V.hom ≅
      (pointwiseToQuotientStackFiber G V.left).obj (G.objects.obj.map V.hom.op x') := by
  let F := pointwiseToQuotientStack G
  let c := CoGrothendieck.cartesianLift
    (F := (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
      Grpd.forgetToCat).toPseudofunctor') x' V.hom
  have hc := CoGrothendieck.isStronglyCartesian_homCartesianLift
    (F := (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
      Grpd.forgetToCat).toPseudofunctor') (a := x') V.hom
  have hFc := (isFibredOneMorphism_pointwiseToQuotientStack G).map_isStronglyCartesian
    V.hom c hc
  refine Functor.pullbackFiberIso (eqToIso (show x =
    (pointwiseToQuotientStackFiber G T).obj x' from Subtype.ext hx)) V.hom ≪≫ ?_
  exact Functor.fiberIsoOfCartesian V.hom
    (Functor.IsPreFibered.pullbackMap ((pointwiseToQuotientStackFiber G T).obj x').2 V.hom)
    (F.map c) inferInstance inferInstance

/-- A pointwise prestack arrow gives a section of the isomorphism presheaf by
applying `pointwiseToQuotientStack` and the canonical pullback comparisons. -/
noncomputable def pointwiseArrowSection
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (x' y' : G.objects.obj.obj (op T))
    (x y : (quotientStack G).p.Fiber T)
    (hx : x.1 = (pointwiseToQuotientStack G).obj ⟨T, x'⟩)
    (hy : y.1 = (pointwiseToQuotientStack G).obj ⟨T, y'⟩)
    (V : Over T)
    (r : (show G.toGroupoidInFunctors.Evaluation (op V.left) from
        G.objects.obj.map V.hom.op x') ⟶ G.objects.obj.map V.hom.op y') :
    ((quotientStack G).p.isomPresheaf x y).obj (op V) := by
  let e : (show G.toGroupoidInFunctors.Evaluation (op V.left) from
      G.objects.obj.map V.hom.op x') ≅ G.objects.obj.map V.hom.op y' := asIso r
  exact ⟨((presentedPullbackIso G T x' x hx V) ≪≫
    (pointwiseToQuotientStackFiber G V.left).mapIso e ≪≫
    (presentedPullbackIso G T y' y hy V).symm).hom, (by change IsIso _; infer_instance)⟩

/-- The section of the arrow space underlying a section of the slice fibre. -/
noncomputable def arrowFiberOverSectionArrow
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (x' y' : G.objects.obj.obj (op T)) (V : Over T)
    (s : (arrowFiberOver G T x' y').obj (op V)) :
    G.arrows.obj.obj (op V.left) :=
  (pullback.snd
    (prod.lift (yonedaEquiv.symm y') (yonedaEquiv.symm x'))
    (prod.lift G.target.hom G.source.hom)).app (op V.left) s.1

/-- In the slice fibre, the structure map is fixed, so the arrow-space section
determines the whole section. -/
lemma arrowFiberOverSectionArrow_injective
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (x' y' : G.objects.obj.obj (op T)) (V : Over T) :
    Function.Injective (arrowFiberOverSectionArrow G T x' y' V) := by
  intro a b h
  apply Subtype.ext
  apply yonedaEquiv.symm.injective
  apply pullback.hom_ext
  · apply yonedaEquiv.injective
    simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply] using a.2.trans b.2.symm
  · apply yonedaEquiv.injective
    simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply, arrowFiberOverSectionArrow] using h

/-- The canonical map on pointwise arrows sends an identity to the identity
isomorphism of the chosen pullback. -/
@[simp]
lemma pointwiseArrowSection_id
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (x' : G.objects.obj.obj (op T))
    (x : (quotientStack G).p.Fiber T)
    (hx : x.1 = (pointwiseToQuotientStack G).obj ⟨T, x'⟩)
    (V : Over T) :
    pointwiseArrowSection G T x' x' x x hx hx V (𝟙 _) =
      ⟨𝟙 (Functor.pullbackFiber (quotientStack G).p x V.hom),
        (by change IsIso (𝟙 _); infer_instance)⟩ := by
  apply Subtype.ext
  simp [pointwiseArrowSection]

private noncomputable def arrowFiberSectionsMap
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (first second : G.objects.obj.obj (op T)) :
    arrowFiberOver G T first second ⟶ arrowSections G T first second where
  app V := ↾fun element => ⟨arrowFiberOverSectionArrow G T first second V.unop element, by
    have condition := congrArg (fun map => map.app (op V.unop.left) element.1)
      (pullback.condition
        (f := prod.lift (yonedaEquiv.symm second) (yonedaEquiv.symm first))
        (g := prod.lift G.target.hom G.source.hom))
    have target := congrArg (fun value => (prod.fst (X := G.objects.obj) (Y := G.objects.obj)).app
      (op V.unop.left) value) condition
    have source := congrArg (fun value => (prod.snd (X := G.objects.obj) (Y := G.objects.obj)).app
      (op V.unop.left) value) condition
    refine Prod.ext ?_ ?_
    · change G.target.hom.app (op V.unop.left)
        (arrowFiberOverSectionArrow G T first second V.unop element) =
          (yonedaEquiv.symm second).app (op V.unop.left) V.unop.hom
      simp only [← NatTrans.comp_app_apply, Category.assoc, prod.lift_fst] at target
      simpa only [NatTrans.comp_app_apply, arrowFiberOverSectionArrow,
        element.2, NatTrans.id_app, types_id_apply] using target.symm
    · change G.source.hom.app (op V.unop.left)
        (arrowFiberOverSectionArrow G T first second V.unop element) =
          (yonedaEquiv.symm first).app (op V.unop.left) V.unop.hom
      simp only [← NatTrans.comp_app_apply, Category.assoc, prod.lift_snd] at source
      simpa only [NatTrans.comp_app_apply, arrowFiberOverSectionArrow,
        element.2, NatTrans.id_app, types_id_apply] using source.symm⟩
  naturality := by
    intro V W morphism
    ext element
    apply Subtype.ext
    exact NatTrans.naturality_apply
      (pullback.snd
        (prod.lift (yonedaEquiv.symm second) (yonedaEquiv.symm first))
        (prod.lift G.target.hom G.source.hom)) morphism.unop.left.op element.1

private lemma arrowFiberSectionsMap_bijective
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (first second : G.objects.obj.obj (op T)) (V : Over T) :
    Function.Bijective ((arrowFiberSectionsMap G T first second).app (op V)) := by
  constructor
  · intro left right comparison
    exact arrowFiberOverSectionArrow_injective G T first second V
      (congrArg Subtype.val comparison)
  · intro element
    let pair := prod.lift (yonedaEquiv.symm second) (yonedaEquiv.symm first)
    let endpoints := prod.lift G.target.hom G.source.hom
    have condition : yoneda.map V.hom ≫ pair = yonedaEquiv.symm element.1 ≫ endpoints := by
      dsimp only [pair, endpoints]
      apply prod.hom_ext
      all_goals simp only [Category.assoc, prod.lift_fst, prod.lift_snd]
      all_goals apply yonedaEquiv.injective
      all_goals rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
      · simpa [pair, endpoints, yonedaEquiv_comp, yonedaEquiv_yoneda_map] using
          (congrArg Prod.fst element.2).symm
      · simpa [pair, endpoints, yonedaEquiv_comp, yonedaEquiv_yoneda_map] using
          (congrArg Prod.snd element.2).symm
    let lift := pullback.lift (yoneda.map V.hom) (yonedaEquiv.symm element.1) condition
    let result : (arrowFiberOver G T first second).obj (op V) :=
      ⟨yonedaEquiv lift, by
        show (pullback.fst pair endpoints).app (op V.left) (yonedaEquiv lift) = V.hom
        rw [← yonedaEquiv_comp, pullback.lift_fst]
        exact yonedaEquiv_yoneda_map _⟩
    refine ⟨result, Subtype.ext ?_⟩
    show (pullback.snd pair endpoints).app (op V.left) (yonedaEquiv lift) = element.1
    rw [← yonedaEquiv_comp, pullback.lift_snd]
    exact yonedaEquiv.apply_symm_apply _

private noncomputable def arrowFiberSectionsIso
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (first second : G.objects.obj.obj (op T)) :
    arrowFiberOver G T first second ≅ arrowSections G T first second := by
  haveI : IsIso (arrowFiberSectionsMap G T first second) :=
    (NatTrans.isIso_iff_isIso_app _).2 fun V =>
      (CategoryTheory.isIso_iff_bijective _).2
        (arrowFiberSectionsMap_bijective G T first second V.unop)
  exact asIso (arrowFiberSectionsMap G T first second)

private noncomputable abbrev pointwiseHomToStackMor
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (first second : G.objects.obj.obj (op T)) :=
  homToMor.{u + 1, u, u, u, u + 1, u + 1} (pointwiseCategoryFunctor G)
    (quotientStack G).p (pointwiseToQuotientStack G)
    (isFibredOneMorphism_pointwiseToQuotientStack G) T first second

private lemma pointwiseHomToStackMor_isIso
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (first second : G.objects.obj.obj (op T)) :
    IsIso (pointwiseHomToStackMor G T first second) := by
  let equivalence := quotientPrestackEquivalence G
  let hEquiv := isFibredOneMorphism_presentationEquivalence G
  let hStack := isFibredOneMorphism_toQuotientStack G
  show IsIso (homToMor.{u + 1, u, u, u, u + 1, u + 1}
    (pointwiseCategoryFunctor G) (quotientStack G).p
    (equivalence.functor ⋙ toQuotientStack G) (hEquiv.comp hStack)
    T first second)
  rw [homToMor_comp (pointwiseCategoryFunctor G) (quotientPrestack G).p
    equivalence.functor hEquiv (quotientStack G).p
    (toQuotientStack G) hStack]
  have := homToMor_isIso.{u + 1, u, u, u, u + 1, u + 1}
    (pointwiseCategoryFunctor G) (quotientPrestack G).p
    equivalence.functor hEquiv equivalence.fullyFaithfulFunctor T first second
  have := isomPresheaf_equiv_arrowFiber C S hS G T
    ((imageFiber.{u + 1, u, u, u, u + 1, u + 1}
      (pointwiseCategoryFunctor G) (quotientPrestack G).p
      equivalence.functor hEquiv T).obj first)
    ((imageFiber.{u + 1, u, u, u, u + 1, u + 1}
      (pointwiseCategoryFunctor G) (quotientPrestack G).p
      equivalence.functor hEquiv T).obj second)
  infer_instance

private noncomputable def stackMorIsomIso
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (first second : (quotientStack G).p.Fiber T) :
    Functor.morPresheaf (quotientStack G).p first second ≅
      Functor.isomPresheaf (quotientStack G).p first second := by
  have htop : ((quotientStack G).p.isomSubpresheaf first second) = ⊤ := by
    apply le_antisymm le_top
    intro V arrow _
    have := (isFiberedInGroupoids_quotientStack G).fiber_isGroupoid V.unop.left
    change IsIso arrow
    infer_instance
  haveI := ((quotientStack G).p.isomSubpresheaf first second).eq_top_iff_isIso.1 htop
  exact (asIso ((quotientStack G).p.isomSubpresheaf first second).ι).symm

private noncomputable def presentedArrowFiberIso
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (first second : G.objects.obj.obj (op T)) :
    (arrowFiberOver G T first second ⋙ uliftFunctor.{u + 1, u}) ≅
      (quotientStack G).p.isomPresheaf
        ((pointwiseToQuotientStackFiber G T).obj first)
        ((pointwiseToQuotientStackFiber G T).obj second) := by
  haveI := pointwiseHomToStackMor_isIso G T first second
  exact Functor.isoWhiskerRight
    (arrowFiberSectionsIso G T first second ≪≫ (pointwiseHomArrowIso G T first second).symm)
    uliftFunctor ≪≫ asIso (pointwiseHomToStackMor G T first second) ≪≫
      stackMorIsomIso G T _ _

/-- The forward map of `presentedArrowFiberIso`, evaluated on a lifted section of the
arrow-space fibre product, is the explicit composite of its three constituent comparisons.
This is true by definition, and stating it separately keeps the main computation below from
having to unfold `presentedArrowFiberIso` inside a tactic goal. -/
private lemma presentedArrowFiberIso_hom_app_eq
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (first second : G.objects.obj.obj (op T)) (V : Over T)
    (element : (arrowFiberOver G T first second).obj (op V)) :
    (presentedArrowFiberIso G T first second).hom.app (op V) (ULift.up element) =
      (stackMorIsomIso G T ((pointwiseToQuotientStackFiber G T).obj first)
          ((pointwiseToQuotientStackFiber G T).obj second)).hom.app (op V)
        ((pointwiseHomToStackMor G T first second).app (op V)
          (ULift.up ((pointwiseHomArrowIso G T first second).inv.app (op V)
            ((arrowFiberSectionsIso G T first second).hom.app (op V) element)))) :=
  rfl

private lemma presentedArrowFiberIso_hom_app
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (first second : G.objects.obj.obj (op T)) (V : Over T)
    (arrow : (show G.toGroupoidInFunctors.Evaluation (op V.left) from
      G.objects.obj.map V.hom.op first) ⟶ G.objects.obj.map V.hom.op second)
    (element : (arrowFiberOver G T first second).obj (op V))
    (helement : arrowFiberOverSectionArrow G T first second V element =
      (G.toGroupoidInFunctors.evaluationArrowEquiv (op V.left) _ _ arrow).1) :
    (presentedArrowFiberIso G T first second).hom.app (op V) (ULift.up element) =
      pointwiseArrowSection G T first second
        ((pointwiseToQuotientStackFiber G T).obj first)
        ((pointwiseToQuotientStackFiber G T).obj second) rfl rfl V arrow := by
  have hsection : (arrowFiberSectionsIso G T first second).hom.app (op V) element =
      (pointwiseHomArrowIso G T first second).hom.app (op V) arrow :=
    Subtype.ext helement
  have hinverse : (pointwiseHomArrowIso G T first second).inv.app (op V)
      ((arrowFiberSectionsIso G T first second).hom.app (op V) element) = arrow := by
    rw [hsection]
    exact (pointwiseHomArrowIso G T first second).hom_inv_id_app_apply (op V) arrow
  refine (presentedArrowFiberIso_hom_app_eq G T first second V element).trans ?_
  rw [hinverse]
  apply Subtype.ext
  have hforget := (stackMorIsomIso G T
    ((pointwiseToQuotientStackFiber G T).obj first)
    ((pointwiseToQuotientStackFiber G T).obj second)).hom_inv_id_app_apply (op V)
      ((pointwiseHomToStackMor G T first second).app (op V) (ULift.up arrow))
  change ((stackMorIsomIso G T
    ((pointwiseToQuotientStackFiber G T).obj first)
    ((pointwiseToQuotientStackFiber G T).obj second)).hom.app (op V)
      ((pointwiseHomToStackMor G T first second).app (op V) (ULift.up arrow))).1 = _ at hforget
  rw [hforget]
  simp [pointwiseHomToStackMor, homToMor, pointwiseArrowSection,
    presentedPullbackIso, liftIso, Iso.trans_hom]


/-- The pullback identification recovers every pointwise prestack arrow from
its canonical image in the quotient stack, over every object of the slice.
Together with `arrowFiberOverSectionArrow_injective`, this specifies the
forward comparison on all arrow-space sections as well. -/
def IsCanonicalArrowFiberIso
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (x' y' : G.objects.obj.obj (op T))
    (x y : (quotientStack G).p.Fiber T)
    (hx : x.1 = (pointwiseToQuotientStack G).obj ⟨T, x'⟩)
    (hy : y.1 = (pointwiseToQuotientStack G).obj ⟨T, y'⟩)
    (e : (arrowFiberOver G T x' y' ⋙ uliftFunctor.{u + 1, u}) ≅
      (quotientStack G).p.isomPresheaf x y) : Prop :=
  ∀ (V : Over T)
    (r : (show G.toGroupoidInFunctors.Evaluation (op V.left) from
        G.objects.obj.map V.hom.op x') ⟶ G.objects.obj.map V.hom.op y'),
    arrowFiberOverSectionArrow G T x' y' V
      (e.inv.app (op V) (pointwiseArrowSection G T x' y' x y hx hy V r)).down =
      (G.toGroupoidInFunctors.evaluationArrowEquiv (op V.left) _ _ r).1

/-- The isomorphism sheaf of two presented objects is canonically the slice
pullback of the arrow space along their two points. The identification sends
pointwise prestack arrows to their images under `pointwiseToQuotientStack`. -/
@[stacks 044V "pullback description of the isomorphism sheaf"]
theorem isomPresheaf_iso_pullback
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (x' y' : G.objects.obj.obj (Opposite.op T))
    (x y : (quotientStack G).p.Fiber T)
    (hx : x.1 = (pointwiseToQuotientStack G).obj ⟨T, x'⟩)
    (hy : y.1 = (pointwiseToQuotientStack G).obj ⟨T, y'⟩) :
    ∃ e : (arrowFiberOver G T x' y' ⋙ uliftFunctor.{u + 1, u}) ≅
        (quotientStack G).p.isomPresheaf x y,
      IsCanonicalArrowFiberIso G T x' y' x y hx hy e := by
  obtain rfl : x = (pointwiseToQuotientStackFiber G T).obj x' := Subtype.ext hx
  obtain rfl : y = (pointwiseToQuotientStackFiber G T).obj y' := Subtype.ext hy
  refine ⟨presentedArrowFiberIso G T x' y', ?_⟩
  intro V arrow
  obtain ⟨element, helement⟩ := (arrowFiberSectionsMap_bijective G T x' y' V).2
    ((pointwiseHomArrowIso G T x' y').hom.app (op V) arrow)
  have harrow : arrowFiberOverSectionArrow G T x' y' V element =
      (G.toGroupoidInFunctors.evaluationArrowEquiv (op V.left) _ _ arrow).1 :=
    congrArg Subtype.val helement
  have hforward := presentedArrowFiberIso_hom_app G T x' y' V arrow element harrow
  have hinv : (presentedArrowFiberIso G T x' y').inv.app (op V)
      ((presentedArrowFiberIso G T x' y').hom.app (op V) (ULift.up element)) =
      ULift.up element :=
    (presentedArrowFiberIso G T x' y').hom_inv_id_app_apply (op V) _
  rw [← hforward, hinv]
  exact harrow

variable (G : GroupoidInAlgebraicSpaces C S hS B)
  (T : BigFppfOver C S hS)
  (x' y' : G.objects.obj.obj (op T))
  (x y : (quotientStack G).p.Fiber T)
  (hx : x.1 = (pointwiseToQuotientStack G).obj ⟨T, x'⟩)
  (hy : y.1 = (pointwiseToQuotientStack G).obj ⟨T, y'⟩)

/-- The specified natural isomorphism from the slice arrow fibre to the
isomorphism presheaf of the presented quotient-stack objects. -/
noncomputable def isomPresheafPullbackIso :
    (arrowFiberOver G T x' y' ⋙ uliftFunctor.{u + 1, u}) ≅
      (quotientStack G).p.isomPresheaf x y :=
  (isomPresheaf_iso_pullback C S hS G T x' y' x y hx hy).choose

/-- The inverse comparison recovers the arrow-space section of each pointwise
prestack arrow from its canonical image in the quotient stack. -/
@[stacks 044V "canonical inverse comparison on prestack arrows"]
theorem isomPresheafPullbackIso_inv_app (V : Over T)
    (r : (show G.toGroupoidInFunctors.Evaluation (op V.left) from
        G.objects.obj.map V.hom.op x') ⟶ G.objects.obj.map V.hom.op y') :
    arrowFiberOverSectionArrow G T x' y' V
      ((isomPresheafPullbackIso G T x' y' x y hx hy).inv.app (op V)
        (pointwiseArrowSection G T x' y' x y hx hy V r)).down =
      (G.toGroupoidInFunctors.evaluationArrowEquiv (op V.left) _ _ r).1 :=
  (isomPresheaf_iso_pullback C S hS G T x' y' x y hx hy).choose_spec V r

/-- The forward comparison sends an arrow-space section to the isomorphism
induced by that very prestack arrow. This rules out translating the identification
by a nonidentity automorphism. -/
@[stacks 044V "canonical forward comparison on prestack arrows"]
theorem isomPresheafPullbackIso_hom_app (V : Over T)
    (r : (show G.toGroupoidInFunctors.Evaluation (op V.left) from
        G.objects.obj.map V.hom.op x') ⟶ G.objects.obj.map V.hom.op y')
    (s : (arrowFiberOver G T x' y').obj (op V))
    (hs : arrowFiberOverSectionArrow G T x' y' V s =
      (G.toGroupoidInFunctors.evaluationArrowEquiv (op V.left) _ _ r).1) :
    (isomPresheafPullbackIso G T x' y' x y hx hy).hom.app (op V) (ULift.up s) =
      pointwiseArrowSection G T x' y' x y hx hy V r := by
  let e := isomPresheafPullbackIso G T x' y' x y hx hy
  have h : e.inv.app (op V) (pointwiseArrowSection G T x' y' x y hx hy V r) =
      ULift.up s := by
    apply ULift.ext
    apply arrowFiberOverSectionArrow_injective G T x' y' V
    exact (isomPresheafPullbackIso_inv_app G T x' y' x y hx hy V r).trans hs.symm
  show e.hom.app (op V) (ULift.up s) = _
  rw [← h]
  exact e.inv_hom_id_app_apply (op V) _

end AlgebraicGeometry.Stack

end
