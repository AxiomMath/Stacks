module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuotientStackChartExtension
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuotientStackChartedPoints

/-!
# Arrows of the pointwise groupoid fibration of a groupoid in algebraic spaces

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces and let `[U/_pR]` be its pointwise
groupoid fibration (`AlgebraicGeometry.Stack.PointwiseFibration`, the category of Stacks 044Q
before stackification): an object over `T` is a `T`-point `a` of `U`, and a morphism
`(T, a) ⟶ (T', a')` is a morphism `h : T ⟶ T'` together with an arrow of the groupoid of
`T`-points from `a` to `h^*a'`, that is a `T`-point `r` of `R` with `s(r) = a` and
`t(r) = h^*a'`.  This file records the calculus of the arrow `r` of a morphism.

## Main definitions

* `AlgebraicGeometry.Stack.pointwiseArrow`: the `T`-point of `R` underlying a morphism; its
  source and target are computed here.
* `AlgebraicGeometry.Stack.vertHom`: the morphism over an identity attached to a `T`-point of `R`.
* `AlgebraicGeometry.Stack.objPt`, `AlgebraicGeometry.Stack.objHom`: objects and morphisms of the
  category fibred in groupoids of the object space `U` (Stacks 0458), which
  `AlgebraicGeometry.Stack.pointwiseObjectInclusion` carries into the pointwise fibration.

## Main results

* `AlgebraicGeometry.Stack.pointwiseArrow_hom_ext`: a morphism is determined by its base and its
  arrow.
* `AlgebraicGeometry.Stack.pointwiseArrow_id`,
  `AlgebraicGeometry.Stack.pointwiseArrow_comp_eq_compose`: the arrow of an identity is a unit
  arrow and the arrow of a composite is the composite of the arrows.
* `AlgebraicGeometry.Stack.vertHom_comp_objHom`: every morphism is a morphism over the identity
  followed by the image of a morphism of the category of the object space.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)

/-! ### The arrow of a morphism -/

/-- The source of the arrow of a morphism `m : x ⟶ y` is the fibre of `x`. -/
theorem source_pointwiseArrow {x y : PointwiseFibration G} (m : x ⟶ y) :
    G.source.hom.app (op x.base) (pointwiseArrow G m) = x.fiber :=
  (G.toGroupoidInFunctors.evaluationArrowEquiv (op x.base) _ _ m.fiber).2.1

/-- The target of the arrow of a morphism `m : x ⟶ y` over `h` is the pullback `h^*` of the
fibre of `y`. -/
theorem target_pointwiseArrow {x y : PointwiseFibration G} (m : x ⟶ y) :
    G.target.hom.app (op x.base) (pointwiseArrow G m) = G.objects.obj.map m.base.op y.fiber :=
  (G.toGroupoidInFunctors.evaluationArrowEquiv (op x.base) _ _ m.fiber).2.2

/-- **A morphism of the pointwise groupoid fibration is determined by its base and its arrow.** -/
theorem pointwiseArrow_hom_ext {x y : PointwiseFibration G} (m m' : x ⟶ y)
    (hb : m.base = m'.base) (ha : pointwiseArrow G m = pointwiseArrow G m') : m = m' :=
  pointwiseHom_ext G.toGroupoidInFunctors hb ha

/-- The fibre component of an identity morphism is the transport along `h^*a = a` for
`h = 𝟙`. -/
theorem fiber_id (x : PointwiseFibration G) :
    Pseudofunctor.CoGrothendieck.Hom.fiber (𝟙 x) = eqToHom (by
      exact (G.objects.obj.map_id_apply (op x.base) x.fiber).symm) := by
  show ((evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
    Grpd.forgetToCat).toPseudofunctor'.mapId ⟨op x.base⟩).inv.toNatTrans.app x.fiber = _
  simp only [Cat.Hom.id_toFunctor, Functor.id_obj, Functor.toPseudofunctor'_mapId, Functor.comp_obj,
    Functor.comp_map, eqToIso.inv, Cat.Hom₂.eqToHom_toNatTrans]
  exact CategoryTheory.eqToHom_app _ _

/-- The arrow of an identity morphism is the unit arrow. -/
theorem pointwiseArrow_id (x : PointwiseFibration G) :
    pointwiseArrow G (𝟙 x) = G.toGroupoidInFunctors.identity (op x.base) x.fiber := by
  unfold pointwiseArrow
  rw [fiber_id]
  exact evaluationArrow_eqToHom_identity G.toGroupoidInFunctors _ _

/-- The arrow of `f ≫ g ≫ eqToHom h` in an evaluated groupoid is the composite of the arrows of
`f` and `g`. -/
theorem evaluationArrow_comp_comp_eqToHom (T : (BigFppfOver C S hS)ᵒᵖ)
    {a b c c' : G.toGroupoidInFunctors.Evaluation T} (f : a ⟶ b) (g : b ⟶ c) (h : c = c') :
    (G.toGroupoidInFunctors.evaluationArrowEquiv T a c' (f ≫ g ≫ eqToHom h)).1 =
      G.toGroupoidInFunctors.compose T (G.toGroupoidInFunctors.evaluationArrowEquiv T b c g).1
        (G.toGroupoidInFunctors.evaluationArrowEquiv T a b f).1
        ((G.toGroupoidInFunctors.evaluationArrowEquiv T b c g).2.1.trans
          (G.toGroupoidInFunctors.evaluationArrowEquiv T a b f).2.2.symm) := by
  subst h
  simp only [eqToHom_refl, Category.comp_id]
  exact Deformation.GroupoidInFunctors.evaluationArrowEquiv_comp _ _ _ _

/-- The fibre component of a composite. -/
theorem fiber_comp {x y z : PointwiseFibration G} (m : x ⟶ y) (m' : y ⟶ z) :
    Pseudofunctor.CoGrothendieck.Hom.fiber (m ≫ m') = m.fiber ≫
      (Deformation.evaluationMap G.toGroupoidInFunctors m.base.op).map m'.fiber ≫
        eqToHom (by
          change G.objects.obj.map m.base.op (G.objects.obj.map m'.base.op z.fiber) =
            G.objects.obj.map (m.base ≫ m'.base).op z.fiber
          rw [op_comp]; exact (Functor.map_comp_apply _ _ _ _).symm) := by
  show m.fiber ≫ _ ≫ ((evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
    Grpd.forgetToCat).toPseudofunctor'.mapComp m'.base.op.toLoc
      m.base.op.toLoc).inv.toNatTrans.app z.fiber = _
  simp only [Cat.Hom.comp_toFunctor, Functor.comp_obj, Functor.toPseudofunctor'_mapComp,
    Functor.comp_map, eqToIso.inv, Cat.Hom₂.eqToHom_toNatTrans]
  congr 2
  exact CategoryTheory.eqToHom_app _ _

/-- **The arrow of a composite is the composite of the arrows**: for `m : x ⟶ y` over
`h : T ⟶ T'` and `m' : y ⟶ z`, the arrow of `m ≫ m'` is `h^*r' ∘ r` in the groupoid of
`T`-points, `r` and `r'` the arrows of `m` and `m'`. -/
theorem pointwiseArrow_comp_eq_compose {x y z : PointwiseFibration G} (m : x ⟶ y) (m' : y ⟶ z) :
    pointwiseArrow G (m ≫ m') = G.toGroupoidInFunctors.compose (op x.base)
      (G.arrows.obj.map m.base.op (pointwiseArrow G m')) (pointwiseArrow G m) (by
        have h1 := congrArg (G.objects.obj.map m.base.op) (source_pointwiseArrow G m')
        have h2 := target_pointwiseArrow G m
        refine (Eq.trans ?_ h1).trans h2.symm
        exact (NatTrans.naturality_apply G.source.hom m.base.op _)) := by
  unfold pointwiseArrow
  rw [fiber_comp]
  exact (evaluationArrow_comp_comp_eqToHom G (op x.base) m.fiber
    ((Deformation.evaluationMap G.toGroupoidInFunctors m.base.op).map m'.fiber) _).trans
      (congrArg (G.toGroupoidInFunctors.comp.app _)
        (Subtype.ext (Prod.ext (Deformation.evaluationMap_map_arrow _ _ _) rfl)))

/-! ### Morphisms over an identity -/

/-- The morphism of the pointwise groupoid fibration over the identity of `T` attached to a
`T`-point `r` of the arrow space with source `a` and target `b`. -/
def vertHom (T : BigFppfOver C S hS) {a b : G.objects.obj.obj (op T)}
    (r : G.arrows.obj.obj (op T)) (hs : G.source.hom.app (op T) r = a)
    (ht : G.target.hom.app (op T) r = b) :
    (⟨T, a⟩ : PointwiseFibration G) ⟶ ⟨T, b⟩ :=
  ⟨𝟙 T, (G.toGroupoidInFunctors.evaluationArrowEquiv (op T) _ _).symm
    ⟨r, hs, ht.trans (G.objects.obj.map_id_apply (op T) b).symm⟩⟩

/-- The base of `vertHom G T r hs ht` is the identity of `T`. -/
@[simp]
theorem vertHom_base (T : BigFppfOver C S hS) {a b : G.objects.obj.obj (op T)}
    (r : G.arrows.obj.obj (op T)) (hs : G.source.hom.app (op T) r = a)
    (ht : G.target.hom.app (op T) r = b) :
    (vertHom G T r hs ht).base = 𝟙 T := rfl

/-- The arrow of `vertHom G T r hs ht` is `r`. -/
@[simp]
theorem pointwiseArrow_vertHom (T : BigFppfOver C S hS) {a b : G.objects.obj.obj (op T)}
    (r : G.arrows.obj.obj (op T)) (hs : G.source.hom.app (op T) r = a)
    (ht : G.target.hom.app (op T) r = b) :
    pointwiseArrow G (vertHom G T r hs ht) = r := by
  unfold pointwiseArrow vertHom
  exact congrArg Subtype.val (Equiv.apply_symm_apply _ _)

/-! ### The category of the object space inside the pointwise fibration -/

/-- The objects of the category fibred in groupoids of the object space of `G`. -/
abbrev ObjFib := (fibredCategory C S hS G.objects.obj).val.obj

/-- The object of the category of the object space attached to a `T`-point of `U`. -/
abbrev objPt (T : BigFppfOver C S hS) (a : G.objects.obj.obj (op T)) : ObjFib G := ⟨T, ⟨a⟩⟩

variable {G} in
/-- The morphism `(T, a) ⟶ (T', a')` of the category of the object space attached to
`h : T ⟶ T'` with `h^*a' = a`. -/
def objHom {T T' : BigFppfOver C S hS} (h : T ⟶ T') {a : G.objects.obj.obj (op T)}
    {a' : G.objects.obj.obj (op T')} (e : G.objects.obj.map h.op a' = a) :
    objPt G T a ⟶ objPt G T' a' :=
  ⟨h, eqToHom (congrArg Discrete.mk e.symm)⟩

variable {G} in
/-- A morphism of the category of the object space is determined by its base. -/
theorem objFib_hom_ext {X Y : ObjFib G} (f g : X ⟶ Y) (h : f.base = g.base) : f = g :=
  Pseudofunctor.CoGrothendieck.Hom.ext f g h ((Discrete.instSubsingletonDiscreteHom _ _).elim _ _)

variable {G} in
/-- The composite of `objHom h e` and `objHom h' e'` is the morphism attached to `h ≫ h'`. -/
theorem objHom_comp {T T' T'' : BigFppfOver C S hS} (h : T ⟶ T') (h' : T' ⟶ T'')
    {a a' a''} (e : G.objects.obj.map h.op a' = a) (e' : G.objects.obj.map h'.op a'' = a') :
    objHom h e ≫ objHom h' e' = objHom (h ≫ h') (by
      rw [op_comp, Functor.map_comp_apply, e', e]) :=
  objFib_hom_ext _ _ rfl

/-- The arrow of the image of a morphism of the category of the object space is a unit
arrow. -/
theorem pointwiseArrow_pointwiseObjectInclusion_map {X Y : ObjFib G} (g : X ⟶ Y) :
    pointwiseArrow G ((pointwiseObjectInclusion G).map g) =
      G.toGroupoidInFunctors.identity (op X.base) X.fiber.as :=
  evaluationArrow_eqToHom_identity G.toGroupoidInFunctors (op X.base) (Discrete.eq_of_hom g.fiber)

/-- Composition of arrows depends only on the two arrows. -/
theorem compose_congr' (T : (BigFppfOver C S hS)ᵒᵖ) {a a' b b' : G.arrows.obj.obj T}
    (w : G.source.hom.app T a = G.target.hom.app T b)
    (w' : G.source.hom.app T a' = G.target.hom.app T b') (ha : a = a') (hb : b = b') :
    G.toGroupoidInFunctors.compose T a b w = G.toGroupoidInFunctors.compose T a' b' w' := by
  subst ha hb
  rfl

/-- Composing with a unit arrow on the left does nothing. -/
theorem compose_identity_left (T : (BigFppfOver C S hS)ᵒᵖ) (r : G.arrows.obj.obj T)
    {b : G.objects.obj.obj T} (hb : G.target.hom.app T r = b)
    (h : G.source.hom.app T (G.toGroupoidInFunctors.identity T b) = G.target.hom.app T r) :
    G.toGroupoidInFunctors.compose T (G.toGroupoidInFunctors.identity T b) r h = r := by
  subst hb
  let := G.toGroupoidInFunctors.evaluationGroupoid T
  let g := (G.toGroupoidInFunctors.evaluationArrowEquiv T _ _).symm
    (⟨r, rfl, rfl⟩ : { a : G.arrows.obj.obj T // G.source.hom.app T a = G.source.hom.app T r ∧
      G.target.hom.app T a = G.target.hom.app T r })
  have hg : (G.toGroupoidInFunctors.evaluationArrowEquiv T _ _ g).1 = r :=
    congrArg Subtype.val (Equiv.apply_symm_apply _ _)
  have hc := Deformation.GroupoidInFunctors.evaluationArrowEquiv_comp G.toGroupoidInFunctors T g
    (𝟙 _)
  rw [show (G.toGroupoidInFunctors.evaluationArrowEquiv T _ _ (g ≫ 𝟙 _)).1 =
    (G.toGroupoidInFunctors.evaluationArrowEquiv T _ _ g).1 from
      congrArg (fun k => (G.toGroupoidInFunctors.evaluationArrowEquiv T _ _ k).1)
        (Category.comp_id g)] at hc
  refine Eq.trans ?_ (hc.symm.trans hg)
  exact congrArg (G.toGroupoidInFunctors.comp.app T) (Subtype.ext (Prod.ext rfl hg.symm))

/-- **Every morphism of the pointwise fibration factors as a morphism over the identity followed
by the image of a morphism of the category of the object space.** -/
theorem vertHom_comp_objHom {x y : PointwiseFibration G} (m : x ⟶ y) :
    vertHom G x.base (pointwiseArrow G m) (source_pointwiseArrow G m)
        (target_pointwiseArrow G m) ≫
      (pointwiseObjectInclusion G).map (objHom (G := G) (a' := y.fiber) m.base rfl) = m := by
  refine pointwiseArrow_hom_ext G _ _ (Category.id_comp _) ?_
  refine (pointwiseArrow_comp_eq_compose G _ _).trans ?_
  have h1 : G.arrows.obj.map (vertHom G x.base (pointwiseArrow G m) (source_pointwiseArrow G m)
      (target_pointwiseArrow G m)).base.op (pointwiseArrow G
        ((pointwiseObjectInclusion G).map (objHom (G := G) (a' := y.fiber) m.base rfl))) =
      G.toGroupoidInFunctors.identity (op x.base) (G.objects.obj.map m.base.op y.fiber) :=
    (G.arrows.obj.map_id_apply _ _).trans (pointwiseArrow_pointwiseObjectInclusion_map G _)
  refine (compose_congr' G _ _
    ((G.toGroupoidInFunctors.evaluationArrowEquiv (op x.base) _ _ (𝟙 _)).2.1.trans
      (target_pointwiseArrow G m).symm) h1 (pointwiseArrow_vertHom G _ _ _ _)).trans ?_
  exact compose_identity_left G _ _ (target_pointwiseArrow G m) _

/-- Two morphisms over the identity compose to the morphism of the composite arrow. -/
theorem vertHom_comp_vertHom (T : BigFppfOver C S hS) {a b c : G.objects.obj.obj (op T)}
    (r r' : G.arrows.obj.obj (op T)) (hs : G.source.hom.app (op T) r = a)
    (ht : G.target.hom.app (op T) r = b) (hs' : G.source.hom.app (op T) r' = b)
    (ht' : G.target.hom.app (op T) r' = c)
    (hs'' : G.source.hom.app (op T)
      (G.toGroupoidInFunctors.compose (op T) r' r (hs'.trans ht.symm)) = a)
    (ht'' : G.target.hom.app (op T)
      (G.toGroupoidInFunctors.compose (op T) r' r (hs'.trans ht.symm)) = c) :
    vertHom G T r hs ht ≫ vertHom G T r' hs' ht' =
      vertHom G T (G.toGroupoidInFunctors.compose (op T) r' r (hs'.trans ht.symm)) hs'' ht'' := by
  refine pointwiseArrow_hom_ext G _ _ (Category.id_comp _) ?_
  refine (pointwiseArrow_comp_eq_compose G _ _).trans ?_
  have h1 : G.arrows.obj.map (vertHom G T r hs ht).base.op
      (pointwiseArrow G (vertHom G T r' hs' ht')) = r' :=
    (G.arrows.obj.map_id_apply _ _).trans (pointwiseArrow_vertHom G _ _ _ _)
  exact (compose_congr' G _ _ (hs'.trans ht.symm) h1 (pointwiseArrow_vertHom G _ _ _ _)).trans
    (pointwiseArrow_vertHom G _ _ _ _).symm

/-- Precomposing a morphism over the identity with the transport along `a' = a` changes only
its source. -/
theorem eqToHom_comp_vertHom (T : BigFppfOver C S hS) {a a' b : G.objects.obj.obj (op T)}
    (e : a' = a) (r : G.arrows.obj.obj (op T)) (hs : G.source.hom.app (op T) r = a)
    (ht : G.target.hom.app (op T) r = b) :
    eqToHom (congrArg (fun z => (⟨T, z⟩ : PointwiseFibration G)) e) ≫ vertHom G T r hs ht =
      vertHom G T r (hs.trans e.symm) ht := by
  subst e
  simp

/-- Postcomposing a morphism over the identity with the transport along `b = b'` changes only
its target. -/
theorem vertHom_comp_eqToHom (T : BigFppfOver C S hS) {a b b' : G.objects.obj.obj (op T)}
    (e : b = b') (r : G.arrows.obj.obj (op T)) (hs : G.source.hom.app (op T) r = a)
    (ht : G.target.hom.app (op T) r = b) :
    vertHom G T r hs ht ≫ eqToHom (congrArg (fun z => (⟨T, z⟩ : PointwiseFibration G)) e) =
      vertHom G T r hs (ht.trans e) := by
  subst e
  simp

/-- The morphism over the identity attached to a unit arrow is an identity, transported. -/
theorem vertHom_identity (T : BigFppfOver C S hS) {a b : G.objects.obj.obj (op T)}
    (x : G.objects.obj.obj (op T))
    (hs : G.source.hom.app (op T) (G.toGroupoidInFunctors.identity (op T) x) = a)
    (ht : G.target.hom.app (op T) (G.toGroupoidInFunctors.identity (op T) x) = b)
    (e : a = b) :
    vertHom G T (G.toGroupoidInFunctors.identity (op T) x) hs ht =
      eqToHom (congrArg (fun z => (⟨T, z⟩ : PointwiseFibration G)) e) := by
  subst e
  refine pointwiseArrow_hom_ext G _ _ rfl ?_
  refine (pointwiseArrow_vertHom G _ _ _ _).trans ?_
  refine Eq.trans ?_ (pointwiseArrow_id G _).symm
  obtain rfl : x = a := ((G.toGroupoidInFunctors.evaluationArrowEquiv (op T) x x
    (𝟙 (show G.toGroupoidInFunctors.Evaluation (op T) from x))).2.1).symm.trans hs
  rfl

/-- Composing with a unit arrow on the right does nothing. -/
theorem compose_identity_right (T : (BigFppfOver C S hS)ᵒᵖ) (r : G.arrows.obj.obj T)
    {b : G.objects.obj.obj T} (hb : G.source.hom.app T r = b)
    (h : G.source.hom.app T r = G.target.hom.app T (G.toGroupoidInFunctors.identity T b)) :
    G.toGroupoidInFunctors.compose T r (G.toGroupoidInFunctors.identity T b) h = r := by
  subst hb
  let := G.toGroupoidInFunctors.evaluationGroupoid T
  let g := (G.toGroupoidInFunctors.evaluationArrowEquiv T _ _).symm
    (⟨r, rfl, rfl⟩ : { a : G.arrows.obj.obj T // G.source.hom.app T a = G.source.hom.app T r ∧
      G.target.hom.app T a = G.target.hom.app T r })
  have hg : (G.toGroupoidInFunctors.evaluationArrowEquiv T _ _ g).1 = r :=
    congrArg Subtype.val (Equiv.apply_symm_apply _ _)
  have hc := Deformation.GroupoidInFunctors.evaluationArrowEquiv_comp G.toGroupoidInFunctors T
    (𝟙 _) g
  rw [show (G.toGroupoidInFunctors.evaluationArrowEquiv T _ _ (𝟙 _ ≫ g)).1 =
    (G.toGroupoidInFunctors.evaluationArrowEquiv T _ _ g).1 from
      congrArg (fun k => (G.toGroupoidInFunctors.evaluationArrowEquiv T _ _ k).1)
        (Category.id_comp g)] at hc
  refine Eq.trans ?_ (hc.symm.trans hg)
  exact congrArg (G.toGroupoidInFunctors.comp.app T) (Subtype.ext (Prod.ext hg.symm rfl))

end AlgebraicGeometry.Stack

end
