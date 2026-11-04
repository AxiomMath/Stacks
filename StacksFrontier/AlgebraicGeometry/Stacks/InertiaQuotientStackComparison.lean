module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.InertiaGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.Functoriality
public import StacksFrontier.CategoryTheory.FiberedCategory.EquivalenceInvariance
public import StacksFrontier.CategoryTheory.FiberedCategory.InertiaStackification
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackStackCongruence
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.FibrewiseEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.InertiaPresentationSquare
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackProjectionRepresentable

/-!
# The inertia of a quotient stack is the quotient by the inertia groupoid (Stacks 06PB)

Let `B → S` and let `(U, R, s, t, c)` be a groupoid in algebraic spaces over `B`, with stabilizer
group algebraic space `G/U` (Stacks 0448) and inertia groupoid `(G, R', s', t', c')` of
Stacks 06PB. This file proves the second assertion of Stacks 06PB,

```
ℐ_{[U/R]} = [G/R'],
```

in the form of a comparison 1-morphism `[G/R'] ⟶ ℐ_{[U/R]}` over the big fppf site whose
underlying functor is an equivalence of categories, and which is compatible with the two
1-morphisms down to `[U/R]` — the forgetful 1-morphism of the inertia on one side and the
1-morphism of Stacks 046Q induced by the forgetful morphism of groupoids on the other.

## Main definitions

* `AlgebraicGeometry.Stack.inertiaComparison`: the comparison `[G/R'] ⟶ ℐ_{[U/R]}`, a
  1-morphism of categories over the big fppf site.
* `AlgebraicGeometry.Stack.inertiaQuotientStackEquivalence`: the equivalence
  `[G/R'] ≌ ℐ_{[U/R]}` over the site.

## Main results

* `AlgebraicGeometry.Stack.inertiaComparison_comp_toBase`: the comparison is strictly over the
  site.
* `AlgebraicGeometry.Stack.isEquivalence_inertiaComparison`: the comparison is an equivalence of
  categories.
* `AlgebraicGeometry.Stack.inertiaComparisonForgetfulIso` and
  `AlgebraicGeometry.Stack.inertiaComparisonForgetfulIso_vertical`: the comparison carries the
  forgetful 1-morphism of the inertia to the 1-morphism `[G/R'] ⟶ [U/R]` of Stacks 046Q, by an
  isomorphism all of whose components lie over identities of the site.

## References

* [Stacks Project, Tag 0448](https://stacks.math.columbia.edu/tag/0448)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
* [Stacks Project, Tag 06PB](https://stacks.math.columbia.edu/tag/06PB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u u₁ u₂ u₃ v₁ v₂ v₃

namespace AlgebraicGeometry.Stack

open AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

section Pointwise

attribute [local implicit_reducible] BasedCategory.ofFunctor Functor.toPseudofunctor'
  pseudofunctorOfIsLocallyDiscrete Quiver.Hom.toLoc toGroupoidInFunctors
  Grpd.forgetToCat Grpd.of inertiaGroupoid inertiaForgetful Functor.copyObj
  stabilizerToObjects stabilizerToElements

/-- The pointwise groupoid fibration `[U/_p R]` of a groupoid in algebraic spaces: the Grothendieck
construction of the presheaf of groupoids `T ↦ G(T)`. -/
noncomputable abbrev pointwisePresentation (G : GroupoidInAlgebraicSpaces C S hS B) :=
  presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)

/-- The loop at a generalized point of the stabilizer, read as an automorphism of the underlying
point of the object space in the groupoid of generalized points. -/
noncomputable def stabilizerLoopIso (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (x : (inertiaGroupoid G).toGroupoidInFunctors.Evaluation T) :
    Aut (((inertiaForgetful G).toGroupoidHom.evaluation T).obj x) :=
  asIso ((G.toGroupoidInFunctors.evaluationArrowEquiv T _ _).symm
    ⟨(stabilizerArrow G).app T x,
      stabilizerArrow_source_app G T x, stabilizerArrow_target_app G T x⟩)

/-- The arrow of the groupoid underlying the loop of a generalized point of the stabilizer is the
arrow that point carries. -/
lemma stabilizerLoopIso_arrow (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (x : (inertiaGroupoid G).toGroupoidInFunctors.Evaluation T) :
    (G.toGroupoidInFunctors.evaluationArrowEquiv T _ _ (stabilizerLoopIso G T x).hom).1 =
      (stabilizerArrow G).app T x :=
  congrArg Subtype.val (Equiv.apply_symm_apply _ _)

/-- Transporting a morphism of a fibre along equalities of its endpoints does not change the
arrow of the groupoid underlying it. -/
lemma evaluationArrowEquiv_transport {D : Type*} [Category D]
    (K : Deformation.GroupoidInFunctors D) (T : D)
    {x x' y y' : K.Evaluation T} (hx : x = x') (hy : y = y') (f : x' ⟶ y) :
    (K.evaluationArrowEquiv T x y' (eqToHom hx ≫ f ≫ eqToHom hy)).1 =
      (K.evaluationArrowEquiv T x' y f).1 := by
  subst x' y'
  simp

/-- Composing a morphism of a fibre with an `eqToHom` does not change the arrow of the groupoid
underlying it. -/
lemma evaluationArrowEquiv_comp_eqToHom {D : Type*} [Category D]
    (K : Deformation.GroupoidInFunctors D) (T : D)
    {x y z : K.Evaluation T} (f : x ⟶ y) (h : y = z) :
    (K.evaluationArrowEquiv T x z (f ≫ eqToHom h)).1 =
      (K.evaluationArrowEquiv T x y f).1 := by
  subst z
  simp

/-- The arrow of the groupoid underlying the inverse of a morphism of a fibre is the inverse of
the arrow underlying it. -/
lemma evaluationArrowEquiv_inv {D : Type*} [Category D]
    (K : Deformation.GroupoidInFunctors D) (T : D)
    {x y : K.Evaluation T} (f : x ⟶ y) :
    (K.evaluationArrowEquiv T y x (Groupoid.inv f)).1 =
      Deformation.inverseArrow K T (K.evaluationArrowEquiv T x y f).1 := by
  let a := K.evaluationArrowEquiv T x y f
  have hf : f = (K.evaluationArrowEquiv T x y).symm a := (Equiv.symm_apply_apply _ _).symm
  rw [hf]
  generalize ha : a.1 = r
  have hs : K.source.app T r = x := ha ▸ a.2.1
  have ht : K.target.app T r = y := ha ▸ a.2.2
  have he : a = ⟨r, hs, ht⟩ := Subtype.ext ha
  rw [he]
  cases hs
  cases ht
  simp only [Equiv.apply_symm_apply]
  rfl

/-- A morphism of the fibre of the inertia groupoid conjugates the loop at its source into the loop
at its target: `t'(r, g) = c(r, c(g, i(r)))`. -/
lemma stabilizerLoopIso_naturality (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    {x y : (inertiaGroupoid G).toGroupoidInFunctors.Evaluation T} (f : x ⟶ y) :
    ((inertiaForgetful G).toGroupoidHom.evaluation T).map f ≫ (stabilizerLoopIso G T y).hom =
      (stabilizerLoopIso G T x).hom ≫
        ((inertiaForgetful G).toGroupoidHom.evaluation T).map f := by
  let K := G.toGroupoidInFunctors
  let L := (inertiaGroupoid G).toGroupoidInFunctors
  let a := L.evaluationArrowEquiv T x y f
  let r : K.arrows.obj T := (inertiaOriginalArrow G).app T a.1
  let g : K.arrows.obj T := (inertiaLoopArrow G).app T a.1
  let ρ := ((inertiaForgetful G).toGroupoidHom.evaluation T).map f
  let α := (stabilizerLoopIso G T x).hom
  let β := (stabilizerLoopIso G T y).hom
  have hρ : (K.evaluationArrowEquiv T _ _ ρ).1 = r :=
    Deformation.GroupoidInFunctors.Hom.evaluation_map_arrow
      (inertiaForgetful G).toGroupoidHom T f
  have hloop : (inertiaLoopArrow G).app T a.1 =
      (stabilizerArrow G).app T ((inertiaSourceMap G).hom.app T a.1) := rfl
  have hα : (K.evaluationArrowEquiv T _ _ α).1 = g :=
    (stabilizerLoopIso_arrow G T x).trans
      (hloop.trans (congrArg ((stabilizerArrow G).app T) a.2.1)).symm
  have hβ : (K.evaluationArrowEquiv T _ _ β).1 =
      (stabilizerArrow G).app T ((inertiaTargetMap G).hom.app T a.1) :=
    (stabilizerLoopIso_arrow G T y).trans
      (congrArg ((stabilizerArrow G).app T) a.2.2).symm
  obtain ⟨w₁, w₂, hw⟩ := inertiaTargetMap_conjugate_formula G T a.1
  have hi : (K.evaluationArrowEquiv T _ _ (Groupoid.inv ρ)).1 =
      Deformation.inverseArrow K T r :=
    (evaluationArrowEquiv_inv K T ρ).trans (congrArg (Deformation.inverseArrow K T) hρ)
  have hinner : (K.evaluationArrowEquiv T _ _ (Groupoid.inv ρ ≫ α)).1 =
      K.compose T g (Deformation.inverseArrow K T r) w₁ :=
    (K.evaluationArrowEquiv_comp T _ _).trans
      (Deformation.GroupoidInFunctors.compose_congr K T _ _ hα hi)
  have houter : (K.evaluationArrowEquiv T _ _ ((Groupoid.inv ρ ≫ α) ≫ ρ)).1 =
      K.compose T r (K.compose T g (Deformation.inverseArrow K T r) w₁) w₂ :=
    (K.evaluationArrowEquiv_comp T _ _).trans
      (Deformation.GroupoidInFunctors.compose_congr K T _ _ hρ hinner)
  have h : β = Groupoid.inv ρ ≫ α ≫ ρ := by
    apply (K.evaluationArrowEquiv T _ _).injective
    apply Subtype.ext
    refine hβ.trans (hw.trans ?_)
    rw [← Category.assoc]
    exact houter.symm
  show ρ ≫ β = α ≫ ρ
  rw [h]
  simp

/-- The point of the pointwise quotient presentation of `(U, R, s, t, c)` underlying a point of
the pointwise quotient presentation of the inertia groupoid: the same test object, carrying the
point of the object space that the given point of the stabilizer lies over. -/
@[implicit_reducible]
noncomputable def underlyingPoint (G : GroupoidInAlgebraicSpaces C S hS B)
    (x : (pointwisePresentation (inertiaGroupoid G)).obj) :
    (pointwisePresentation G).obj :=
  ⟨x.base, (stabilizerToObjects G).hom.app (Opposite.op x.base) x.fiber⟩

/-- The loop carried by a point of the pointwise presentation of the inertia groupoid, read as an
automorphism of the underlying point of the pointwise presentation of `(U, R, s, t, c)`. -/
noncomputable def presentationLoop (G : GroupoidInAlgebraicSpaces C S hS B)
    (x : (pointwisePresentation (inertiaGroupoid G)).obj) :
    Aut (underlyingPoint G x) :=
  (Pseudofunctor.CoGrothendieck.ι
    (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
      Grpd.forgetToCat).toPseudofunctor' x.base).mapIso
    (stabilizerLoopIso G (Opposite.op x.base) x.fiber)

/-- The loop of a point of the pointwise presentation of the inertia groupoid is the image of the
loop in the fibre under the inclusion of that fibre. -/
lemma presentationLoop_hom (G : GroupoidInAlgebraicSpaces C S hS B)
    (x : (pointwisePresentation (inertiaGroupoid G)).obj) :
    (presentationLoop G x).hom =
      (Pseudofunctor.CoGrothendieck.ι
        (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
          Grpd.forgetToCat).toPseudofunctor' x.base).map
        (stabilizerLoopIso G (Opposite.op x.base) x.fiber).hom := rfl

/-- The loop of a point of the pointwise presentation of the inertia groupoid lies over the
identity of the test object. -/
lemma presentationLoop_base (G : GroupoidInAlgebraicSpaces C S hS B)
    (x : (pointwisePresentation (inertiaGroupoid G)).obj) :
    (presentationLoop G x).hom.base = 𝟙 x.base := rfl

/-- The arrow of a morphism of the pointwise presentation, read through the identification of the
morphisms of an evaluated groupoid with the generalized points of the arrow space. -/
noncomputable def presentationArrow (G : GroupoidInAlgebraicSpaces C S hS B)
    {x y : (pointwisePresentation G).obj} (f : x ⟶ y) : G.toGroupoidInFunctors.arrows.obj
      (Opposite.op x.base) :=
  (G.toGroupoidInFunctors.evaluationArrowEquiv (Opposite.op x.base) x.fiber
    (G.toGroupoidInFunctors.objects.map f.base.op y.fiber) f.fiber).1

/-- The arrow underlying the loop of a point of the pointwise presentation of the inertia
groupoid is the arrow of `R` that point carries as a point of the stabilizer. -/
lemma presentationLoop_spec (G : GroupoidInAlgebraicSpaces C S hS B)
    (x : (pointwisePresentation (inertiaGroupoid G)).obj) :
    let K := G.toGroupoidInFunctors
    let y := (underlyingPoint G x).fiber
    let α := (presentationLoop G x).hom.fiber ≫
      eqToHom (by rw [presentationLoop_base]; exact K.objects.map_id_apply _ y)
    (K.evaluationArrowEquiv (Opposite.op x.base) y y α).1 =
      (stabilizerArrow G).app (Opposite.op x.base) x.fiber := by
  dsimp only
  simp only [presentationLoop_hom, Pseudofunctor.CoGrothendieck.ι_map_fiber,
    Functor.toPseudofunctor'_mapId, eqToIso.inv, Cat.eqToHom_app]
  refine Eq.trans (evaluationArrowEquiv_comp_eqToHom _ _ _ _) ?_
  refine Eq.trans (evaluationArrowEquiv_comp_eqToHom _ _ _ _) ?_
  exact stabilizerLoopIso_arrow G _ x.fiber

/-- The arrow of the loop of a point of the pointwise presentation of the inertia groupoid. -/
lemma presentationLoop_arrow (G : GroupoidInAlgebraicSpaces C S hS B)
    (x : (pointwisePresentation (inertiaGroupoid G)).obj) :
    presentationArrow G (presentationLoop G x).hom =
      (stabilizerArrow G).app (Opposite.op x.base) x.fiber := by
  have h := presentationLoop_spec G x
  dsimp only at h
  exact (evaluationArrowEquiv_comp_eqToHom _ _ _ _).symm.trans h

/-- The 1-morphism of Stacks 046Q on the pointwise presentations sends a point to the point of
the object space its point of the object space maps to. -/
lemma quotientPointwiseMap_obj {G H : GroupoidInAlgebraicSpaces C S hS B}
    (f : GroupoidInAlgebraicSpaces.Hom G H) (x : (pointwisePresentation G).obj) :
    (quotientPointwiseMap f).toFunctor.obj x =
      ⟨x.base, f.toGroupoidHom.mapObjects.app (Opposite.op x.base) x.fiber⟩ := by
  show (⟨x.base, ((quotientPointwiseMapData f).1.app
    ⟨Opposite.op x.base⟩).toFunctor.obj x.fiber⟩ : (pointwisePresentation H).obj) = _
  rw [(quotientPointwiseMapData f).2.1 x.base]
  rfl

/-- On the pointwise presentations, the 1-morphism induced by the forgetful morphism of the
inertia groupoid is the passage to the underlying point. -/
lemma quotientPointwiseMap_forgetful_obj (G : GroupoidInAlgebraicSpaces C S hS B)
    (x : (pointwisePresentation (inertiaGroupoid G)).obj) :
    (quotientPointwiseMap (inertiaForgetful G)).toFunctor.obj x = underlyingPoint G x := by
  rw [quotientPointwiseMap_obj]
  rfl

/-- The passage to the underlying point, as a functor from the pointwise presentation of the
inertia groupoid to the pointwise presentation of `(U, R, s, t, c)`. It is the 1-morphism of
Stacks 046Q induced by the forgetful morphism of groupoids, with its value on objects rewritten
to `AlgebraicGeometry.Stack.underlyingPoint`. -/
@[implicit_reducible]
noncomputable def underlyingPointFunctor (G : GroupoidInAlgebraicSpaces C S hS B) :
    (pointwisePresentation (inertiaGroupoid G)).obj ⥤ (pointwisePresentation G).obj :=
  (quotientPointwiseMap (inertiaForgetful G)).toFunctor.copyObj
    (underlyingPoint G) (fun x => eqToIso (quotientPointwiseMap_forgetful_obj G x))

/-- The passage to the underlying point does not change the test object a morphism lies over. -/
lemma underlyingPointFunctor_map_base (G : GroupoidInAlgebraicSpaces C S hS B)
    {x y : (pointwisePresentation (inertiaGroupoid G)).obj} (f : x ⟶ y) :
    ((underlyingPointFunctor G).map f).base = f.base := by
  show (pointwisePresentation G).p.map
    (eqToHom (quotientPointwiseMap_forgetful_obj G x).symm ≫
      (quotientPointwiseMap (inertiaForgetful G)).toFunctor.map f ≫
      eqToHom (quotientPointwiseMap_forgetful_obj G y)) = f.base
  rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
  show eqToHom (show x.base = x.base from rfl) ≫ f.base ≫
    eqToHom (show y.base = y.base from rfl) = f.base
  simp

/-- The point of the object space underlying the image of a point under the 1-morphism of
Stacks 046Q on the pointwise presentations. -/
lemma quotientPointwiseMap_obj_fiber {G H : GroupoidInAlgebraicSpaces C S hS B}
    (f : GroupoidInAlgebraicSpaces.Hom G H) (x : (pointwisePresentation G).obj) :
    ((quotientPointwiseMap f).toFunctor.obj x).fiber =
      f.toGroupoidHom.mapObjects.app (Opposite.op x.base) x.fiber := by
  show ((quotientPointwiseMapData f).1.app
    ⟨Opposite.op x.base⟩).toFunctor.obj x.fiber = _
  rw [(quotientPointwiseMapData f).2.1 x.base]
  rfl

/-- The fibre component of the image of a morphism under the 1-morphism of Stacks 046Q on the
pointwise presentations is the image of its fibre component under the evaluated morphism of
groupoids. -/
lemma quotientPointwiseMap_map_fiber {G H : GroupoidInAlgebraicSpaces C S hS B}
    (a : GroupoidInAlgebraicSpaces.Hom G H)
    {x y : (pointwisePresentation G).obj} (f : x ⟶ y) :
    let Q := (quotientPointwiseMap a).toFunctor
    let h₁ : (Q.obj x).fiber =
        a.toGroupoidHom.mapObjects.app (Opposite.op x.base) x.fiber := by
      exact quotientPointwiseMap_obj_fiber a x
    (Q.map f).fiber = eqToHom h₁ ≫
      (a.toGroupoidHom.evaluation (Opposite.op x.base)).map f.fiber ≫
        eqToHom (by
          change a.toGroupoidHom.mapObjects.app (Opposite.op x.base)
              (G.toGroupoidInFunctors.objects.map f.base.op y.fiber) =
            H.toGroupoidInFunctors.objects.map f.base.op (Q.obj y).fiber
          rw [NatTrans.naturality_apply]
          exact congrArg (H.toGroupoidInFunctors.objects.map f.base.op)
            (quotientPointwiseMap_obj_fiber a y).symm) := by
  dsimp only
  simp only [quotientPointwiseMap, Pseudofunctor.CoGrothendieck.map_map_fiber]
  obtain ⟨h, hh⟩ := (quotientPointwiseMapData a).2.2 f.base.op.toLoc
  rw [hh]
  simp only [eqToIso.hom, Cat.eqToHom_app]
  rw [Functor.congr_hom ((quotientPointwiseMapData a).2.1 x.base) f.fiber]
  simp only [Category.assoc, eqToHom_trans]
  rfl

/-- Transporting a morphism of the pointwise presentation along equalities of its endpoints
transports its arrow along the induced equality of test objects. -/
lemma presentationArrow_transport (G : GroupoidInAlgebraicSpaces C S hS B)
    {x x' y y' : (pointwisePresentation G).obj}
    (hx : x = x') (hy : y = y') (f : x' ⟶ y) :
    presentationArrow G (eqToHom hx ≫ f ≫ eqToHom hy) =
      G.toGroupoidInFunctors.arrows.map
        (eqToHom (congrArg (fun z => Opposite.op z.base) hx).symm)
        (presentationArrow G f) := by
  subst x' y'
  simp

/-- A morphism of the pointwise presentation is determined by the test object it lies over
together with its arrow. -/
lemma presentationHom_ext (G : GroupoidInAlgebraicSpaces C S hS B)
    {x y : (pointwisePresentation G).obj} (f g : x ⟶ y)
    (hb : f.base = g.base)
    (ha : presentationArrow G f = presentationArrow G g) : f = g := by
  apply Pseudofunctor.CoGrothendieck.Hom.ext _ _ hb
  apply (G.toGroupoidInFunctors.evaluationArrowEquiv _ _ _).injective
  apply Subtype.ext
  rwa [evaluationArrowEquiv_comp_eqToHom]

/-- The arrow of a composite of morphisms of the pointwise presentation is the composite of the
arrows, the first being pulled back along the test object of the second. -/
lemma presentationArrow_comp (G : GroupoidInAlgebraicSpaces C S hS B)
    {x y z : (pointwisePresentation G).obj} (f : x ⟶ y) (g : y ⟶ z) :
    presentationArrow G (f ≫ g) = G.toGroupoidInFunctors.compose (Opposite.op x.base)
      (G.toGroupoidInFunctors.arrows.map f.base.op (presentationArrow G g))
      (presentationArrow G f)
      (by
        rw [NatTrans.naturality_apply]
        exact (congrArg (G.toGroupoidInFunctors.objects.map f.base.op)
          (G.toGroupoidInFunctors.evaluationArrowEquiv _ _ _ g.fiber).2.1).trans
          (G.toGroupoidInFunctors.evaluationArrowEquiv _ _ _ f.fiber).2.2.symm) := by
  unfold presentationArrow
  rw [PresheafOfCategories.comp_fiber, ← Category.assoc]
  refine Eq.trans (evaluationArrowEquiv_comp_eqToHom _ _ _ _) ?_
  rw [Deformation.GroupoidInFunctors.evaluationArrowEquiv_comp]
  exact Deformation.GroupoidInFunctors.compose_congr G.toGroupoidInFunctors _ _ _
    (Deformation.evaluationMap_map_arrow _ _ _) rfl

/-- The arrow of the image of a morphism under the passage to the underlying point is the arrow
of `R` underlying its arrow of `R'`. -/
lemma underlyingPointFunctor_map_arrow (G : GroupoidInAlgebraicSpaces C S hS B)
    {x y : (pointwisePresentation (inertiaGroupoid G)).obj} (f : x ⟶ y) :
    presentationArrow G ((underlyingPointFunctor G).map f) =
      (inertiaForgetful G).toGroupoidHom.mapArrows.app (Opposite.op x.base)
        (presentationArrow (inertiaGroupoid G) f) := by
  show presentationArrow G (eqToHom (quotientPointwiseMap_forgetful_obj G x).symm ≫
    (quotientPointwiseMap (inertiaForgetful G)).toFunctor.map f ≫
      eqToHom (quotientPointwiseMap_forgetful_obj G y)) = _
  rw [presentationArrow_transport]
  show G.toGroupoidInFunctors.arrows.map (𝟙 _) _ = _
  rw [G.toGroupoidInFunctors.arrows.map_id_apply]
  unfold presentationArrow
  rw [quotientPointwiseMap_map_fiber]
  refine Eq.trans (evaluationArrowEquiv_transport _ _ _ _ _) ?_
  exact (inertiaForgetful G).toGroupoidHom.evaluation_map_arrow _ f.fiber

/-- A morphism of the pointwise presentation of the inertia groupoid intertwines the loops at its
two endpoints. -/
lemma presentationLoop_naturality (G : GroupoidInAlgebraicSpaces C S hS B)
    {x y : (pointwisePresentation (inertiaGroupoid G)).obj} (f : x ⟶ y) :
    (underlyingPointFunctor G).map f ≫ (presentationLoop G y).hom =
      (presentationLoop G x).hom ≫ (underlyingPointFunctor G).map f := by
  let K := G.toGroupoidInFunctors
  let T := Opposite.op x.base
  let ρ := ((inertiaForgetful G).toGroupoidHom.evaluation T).map f.fiber
  have hρ : (K.evaluationArrowEquiv T _ _ ρ).1 =
      presentationArrow G ((underlyingPointFunctor G).map f) := by
    rw [Deformation.GroupoidInFunctors.Hom.evaluation_map_arrow,
      underlyingPointFunctor_map_arrow]
    rfl
  have hn := congrArg (fun a => (K.evaluationArrowEquiv T _ _ a).1)
    (stabilizerLoopIso_naturality G T f.fiber)
  simp only [K.evaluationArrowEquiv_comp] at hn
  apply presentationHom_ext G
  · show ((underlyingPointFunctor G).map f).base ≫ 𝟙 _ =
      𝟙 _ ≫ ((underlyingPointFunctor G).map f).base
    simp
  · refine ((presentationArrow_comp G _ _).trans ?_).trans (presentationArrow_comp G _ _).symm
    refine (Deformation.GroupoidInFunctors.compose_congr K T _ _ ?_ hρ.symm).trans
      (hn.trans (Deformation.GroupoidInFunctors.compose_congr K T _ _ ?_ ?_))
    · rw [stabilizerLoopIso_arrow]
      refine Eq.trans (congrArg (G.toGroupoidInFunctors.arrows.map
        ((underlyingPointFunctor G).map f).base.op) (presentationLoop_arrow G y)) ?_
      rw [underlyingPointFunctor_map_base]
      exact (NatTrans.naturality_apply (stabilizerArrow G) f.base.op y.fiber).symm
    · rw [presentationLoop_base]
      show _ = K.arrows.map (𝟙 T) _
      exact hρ.trans (G.toGroupoidInFunctors.arrows.map_id_apply T _).symm
    · rw [stabilizerLoopIso_arrow]
      exact (presentationLoop_arrow G x).symm

/-- A functor into the relative inertia built from a functor together with a natural family of
automorphisms of its values lying over identities. -/
def inertiaFunctorOfAutomorphisms {A D E : Type*} [Category A] [Category D] [Category E]
    (p : D ⥤ E) (F : A ⥤ D) (α : ∀ x, F.obj x ≅ F.obj x)
    (hα : ∀ x, p.map (α x).hom = 𝟙 (p.obj (F.obj x)))
    (hcomm : ∀ {x y} (f : x ⟶ y), F.map f ≫ (α y).hom = (α x).hom ≫ F.map f) :
    A ⥤ RelativeInertia p where
  obj x := ⟨F.obj x, α x, hα x⟩
  map f := ⟨F.map f, hcomm f⟩
  map_id x := RelativeInertiaHom.ext (F.map_id x)
  map_comp f g := RelativeInertiaHom.ext (F.map_comp f g)

/-- The pointwise comparison: the functor from the pointwise presentation of the inertia groupoid
to the inertia of the pointwise presentation of `(U, R, s, t, c)` sending a point of the stabilizer
to its underlying point of the object space together with its loop, read as an automorphism there.
-/
noncomputable def presentationInertiaFunctor (G : GroupoidInAlgebraicSpaces C S hS B) :
    (pointwisePresentation (inertiaGroupoid G)).obj ⥤
      RelativeInertia (pointwisePresentation G).p :=
  inertiaFunctorOfAutomorphisms (pointwisePresentation G).p
    (underlyingPointFunctor G) (presentationLoop G) (fun _ => rfl)
    (presentationLoop_naturality G)

/-- The pointwise comparison is strictly over the site. -/
lemma presentationInertiaFunctor_over (G : GroupoidInAlgebraicSpaces C S hS B) :
    presentationInertiaFunctor G ⋙ RelativeInertia.toBase (pointwisePresentation G).p =
      (pointwisePresentation (inertiaGroupoid G)).p := by
  apply CategoryTheory.Functor.ext
  · intro x y f
    show ((underlyingPointFunctor G).map f).base =
      eqToHom (by rfl) ≫ f.base ≫ eqToHom (by rfl)
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using
      underlyingPointFunctor_map_base G f

/-- The pointwise comparison followed into the inertia of the quotient stack `[U/R]`. -/
noncomputable def localInertiaComparison (G : GroupoidInAlgebraicSpaces C S hS B) :
    (pointwisePresentation (inertiaGroupoid G)).obj ⥤
      RelativeInertia (quotientStack G).p :=
  presentationInertiaFunctor G ⋙ RelativeInertia.functoriality
    (pointwisePresentation G).p (quotientStack G).p
    (pointwiseToQuotientStack G)
    (isFibredOneMorphism_pointwiseToQuotientStack G).comp_eq

/-- The pointwise comparison is faithful. -/
lemma presentationInertiaFunctor_faithful (G : GroupoidInAlgebraicSpaces C S hS B) :
    (presentationInertiaFunctor G).Faithful where
  map_injective {x y} f g h := by
    have he : (underlyingPointFunctor G).map f = (underlyingPointFunctor G).map g :=
      congrArg RelativeInertiaHom.hom h
    apply presentationHom_ext _ f g
    · simpa only [underlyingPointFunctor_map_base] using congrArg (fun a => a.base) he
    · apply inertiaArrow_ext G (Opposite.op x.base)
      · have ha := congrArg (presentationArrow G) he
        rwa [underlyingPointFunctor_map_arrow, underlyingPointFunctor_map_arrow] at ha
      · exact ((inertiaGroupoid G).toGroupoidInFunctors.evaluationArrowEquiv
          _ _ _ f.fiber).2.1.trans
            ((inertiaGroupoid G).toGroupoidInFunctors.evaluationArrowEquiv
              _ _ _ g.fiber).2.1.symm

/-- An arrow of the groupoid of generalized points that intertwines two loops of the stabilizer
conjugates the first into the second. -/
lemma conjugateLoopMap_eq_of_comm (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    {x y : (inertiaGroupoid G).toGroupoidInFunctors.Evaluation T}
    (f : (stabilizerToElements G T x).1 ⟶ (stabilizerToElements G T y).1)
    (hf : f ≫ (stabilizerLoopIso G T y).hom = (stabilizerLoopIso G T x).hom ≫ f) :
    G.toGroupoidInFunctors.conjugateLoopMap T f (stabilizerToElements G T x).2 =
      (stabilizerToElements G T y).2 := by
  apply Subtype.ext
  have he : Groupoid.inv f ≫ (stabilizerLoopIso G T x).hom ≫ f =
      (stabilizerLoopIso G T y).hom :=
    (congrArg (fun k => Groupoid.inv f ≫ k) hf.symm).trans (by simp)
  show (G.toGroupoidInFunctors.evaluationArrowEquiv T _ _
    (Groupoid.inv f ≫ (stabilizerLoopIso G T x).hom ≫ f)).1 = _
  rw [he]
  exact stabilizerLoopIso_arrow G T y

/-- A morphism of the inertia of the pointwise presentation, read in the fibre over its test
object, intertwines the two loops of the stabilizer it connects. -/
lemma presentationComm_fiber (G : GroupoidInAlgebraicSpaces C S hS B)
    {x y : (pointwisePresentation (inertiaGroupoid G)).obj}
    (f : underlyingPoint G x ⟶ underlyingPoint G y)
    (hf : f ≫ (presentationLoop G y).hom = (presentationLoop G x).hom ≫ f) :
    let T := Opposite.op x.base
    let z := (inertiaGroupoid G).objects.obj.map f.base.op y.fiber
    let h : G.toGroupoidInFunctors.objects.map f.base.op (underlyingPoint G y).fiber =
        (stabilizerToObjects G).hom.app T z :=
      (NatTrans.naturality_apply (stabilizerToObjects G).hom f.base.op y.fiber).symm
    let ρ := f.fiber ≫ eqToHom h
    ρ ≫ (stabilizerLoopIso G T z).hom = (stabilizerLoopIso G T x.fiber).hom ≫ ρ := by
  dsimp only
  let K := G.toGroupoidInFunctors
  apply (K.evaluationArrowEquiv (Opposite.op x.base) _ _).injective
  apply Subtype.ext
  have ha := congrArg (presentationArrow G) hf
  refine Eq.trans ?_ (Eq.trans ((presentationArrow_comp G _ _).symm.trans
    (ha.trans (presentationArrow_comp G _ _))) ?_)
  · rw [K.evaluationArrowEquiv_comp]
    apply Deformation.GroupoidInFunctors.compose_congr K _ _ _
    · refine (stabilizerLoopIso_arrow G _ _).trans ?_
      refine Eq.trans ?_ (congrArg (G.toGroupoidInFunctors.arrows.map f.base.op)
        (presentationLoop_arrow G y)).symm
      exact NatTrans.naturality_apply (stabilizerArrow G) f.base.op y.fiber
    · exact evaluationArrowEquiv_comp_eqToHom K _ _ _
  · rw [K.evaluationArrowEquiv_comp]
    apply Deformation.GroupoidInFunctors.compose_congr K _ _ _
    · rw [evaluationArrowEquiv_comp_eqToHom, presentationLoop_base]
      exact K.arrows.map_id_apply _ _
    · exact (presentationLoop_arrow G x).trans (stabilizerLoopIso_arrow G _ x.fiber).symm

/-- The pointwise comparison is full. -/
lemma presentationInertiaFunctor_full (G : GroupoidInAlgebraicSpaces C S hS B) :
    (presentationInertiaFunctor G).Full where
  map_surjective {x y} f := by
    let T := Opposite.op x.base
    let z := (inertiaGroupoid G).objects.obj.map f.hom.base.op y.fiber
    let h : G.toGroupoidInFunctors.objects.map f.hom.base.op (underlyingPoint G y).fiber =
        (stabilizerToObjects G).hom.app T z :=
      (NatTrans.naturality_apply (stabilizerToObjects G).hom f.hom.base.op y.fiber).symm
    let ρ := f.hom.fiber ≫ eqToHom h
    let φ : @Quiver.Hom _ (pointwiseInertiaGroupoid G T).toCategory.toQuiver x.fiber z :=
      ⟨⟨ρ, conjugateLoopMap_eq_of_comm G T ρ (presentationComm_fiber G f.hom f.comm)⟩⟩
    let a := inertiaHomEquiv G T x.fiber z φ
    let ψ : x ⟶ y := ⟨f.hom.base,
      ((inertiaGroupoid G).toGroupoidInFunctors.evaluationArrowEquiv T x.fiber z).symm a⟩
    refine ⟨ψ, ?_⟩
    apply RelativeInertiaHom.ext
    apply presentationHom_ext G
    · exact underlyingPointFunctor_map_base G ψ
    · show presentationArrow G ((underlyingPointFunctor G).map ψ) = _
      rw [underlyingPointFunctor_map_arrow]
      show (inertiaOriginalArrow G).app T
        (((inertiaGroupoid G).toGroupoidInFunctors.evaluationArrowEquiv T _ _
          (((inertiaGroupoid G).toGroupoidInFunctors.evaluationArrowEquiv
            T _ _).symm a)).1) = _
      rw [Equiv.apply_symm_apply]
      show (inertiaOriginalArrow G).app T (inertiaHomArrow G T φ) = _
      exact (inertiaHomArrow_original G T φ).trans
        (evaluationArrowEquiv_comp_eqToHom G.toGroupoidInFunctors T f.hom.fiber h)

/-- The pointwise comparison is surjective on objects. -/
lemma presentationInertiaFunctor_surjective (G : GroupoidInAlgebraicSpaces C S hS B) :
    Function.Surjective (presentationInertiaFunctor G).obj := by
  intro A
  let K := G.toGroupoidInFunctors
  let T := Opposite.op A.obj.base
  have hb : A.auto.hom.base = 𝟙 A.obj.base := A.cond
  let α : A.obj.fiber ⟶ A.obj.fiber :=
    A.auto.hom.fiber ≫ eqToHom (by rw [hb]; exact K.objects.map_id_apply _ _)
  let a := K.evaluationArrowEquiv T _ _ α
  let z := (stabilizerElementsEquiv G T).symm ⟨A.obj.fiber, a⟩
  have hz := (stabilizerElementsEquiv G T).apply_symm_apply ⟨A.obj.fiber, a⟩
  have hz₁ : (stabilizerToObjects G).hom.app T z = A.obj.fiber := congrArg Sigma.fst hz
  have hz₂ : (stabilizerArrow G).app T z = a.1 := congrArg (fun e => e.2.1) hz
  let x : (pointwisePresentation (inertiaGroupoid G)).obj := ⟨A.obj.base, z⟩
  have ho : underlyingPoint G x = A.obj := by
    show (⟨A.obj.base, (stabilizerToObjects G).hom.app T z⟩ :
      (pointwisePresentation G).obj) = A.obj
    rw [hz₁]
    rfl
  refine ⟨x, RelativeInertia.obj_ext ho ?_⟩
  show (presentationLoop G x).hom = eqToHom ho ≫ A.auto.hom ≫ eqToHom ho.symm
  apply presentationHom_ext G
  · show (presentationLoop G x).hom.base =
      (pointwisePresentation G).p.map (eqToHom ho ≫ A.auto.hom ≫ eqToHom ho.symm)
    rw [presentationLoop_base, Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
    show 𝟙 _ = (𝟙 _) ≫ A.auto.hom.base ≫ (𝟙 _)
    rw [hb]
    simp
  · refine (presentationLoop_arrow G x).trans ?_
    refine Eq.trans ?_ (presentationArrow_transport G ho ho.symm A.auto.hom).symm
    show (stabilizerArrow G).app T z = K.arrows.map (𝟙 T) _
    rw [K.arrows.map_id_apply, hz₂]
    exact evaluationArrowEquiv_comp_eqToHom K T A.auto.hom.fiber _

/-- The pointwise comparison is an equivalence of categories over the big fppf site:
`[G/_p R'] = ℐ_{[U/_p R]}`. -/
noncomputable def presentationInertiaEquivalenceOver
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    Functor.IsEquivalenceOver
      (pointwisePresentation (inertiaGroupoid G)).p
      (RelativeInertia.toBase (pointwisePresentation G).p)
      (presentationInertiaFunctor G) := by
  let F := presentationInertiaFunctor G
  letI : F.Full := presentationInertiaFunctor_full G
  letI : F.Faithful := presentationInertiaFunctor_faithful G
  apply Functor.isEquivalenceOver_of_exists_vertical_iso
    (presentationInertiaFunctor_over G)
  intro A
  obtain ⟨x, hx⟩ := presentationInertiaFunctor_surjective G A
  have hbase :
      (pointwisePresentation (inertiaGroupoid G)).p.obj x =
        (RelativeInertia.toBase (pointwisePresentation G).p).obj A := by
    rw [← hx]
    exact (Functor.congr_obj (presentationInertiaFunctor_over G) x).symm
  exact ⟨x, hbase, eqToIso hx.symm, IsHomLift.eqToHom_domain_lift_id hx.symm rfl⟩


end Pointwise


section Stackification

/-- If every object of the target of a 1-morphism `F` of fibred categories is, locally on the base,
the target of a strongly cartesian morphism from an object in the image of `F`, then locally on the
base every pullback of an object of a fibre lies in the essential image of the functor induced by
`F` on fibres. -/
theorem localPreimage_mem_essImage
    {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₃} 𝒳]
    {𝒴 : Type u₃} [Category.{v₃} 𝒴]
    {p : 𝒳 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} [p.IsFibered] [q.IsFibered]
    {F : 𝒳 ⥤ 𝒴} (hF : p.IsFibredOneMorphism q F)
    {J : GrothendieckTopology 𝒞}
    (hobj : ∀ y : 𝒴, ∃ R ∈ J (q.obj y),
      ∀ ⦃V : 𝒞⦄ (f : V ⟶ q.obj y), R f →
        ∃ (x : 𝒳) (φ : F.obj x ⟶ y), q.IsStronglyCartesian f φ) :
    ∀ (U : 𝒞) (y : q.Fiber U), ∃ R ∈ J U,
      ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
        (Functor.fiberFunctorOfCompEq hF.comp_eq V).essImage
          (Functor.pullbackFiber q y f) := by
  intro U ⟨y, hy⟩
  subst U
  obtain ⟨R, hR, hloc⟩ := hobj y
  refine ⟨R, hR, fun V f hf => ?_⟩
  obtain ⟨x, φ, hφ⟩ := hloc f hf
  have hqx : q.obj (F.obj x) = V := IsHomLift.domain_eq q f φ
  have hpx : p.obj x = V := (Functor.congr_obj hF.comp_eq x).symm.trans hqx
  let x' : p.Fiber V := ⟨x, hpx⟩
  have hc : q.IsCartesian f φ := by have := hφ; infer_instance
  exact ⟨x', ⟨Functor.fiberIsoOfCartesian f φ
    (Functor.IsPreFibered.pullbackMap (show q.Fiber (q.obj y) from ⟨y, rfl⟩).2 f)
    hc (Functor.IsPreFibered.pullbackMap.IsCartesian _ _)⟩⟩

end Stackification

section QuotientStack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- Clause (2) of Stacks 02ZN for the quotient stack, in the object-indexed form: every object of
`[U/R]` has a cartesian morphism from the image of the pointwise presentation, locally on the
base. -/
theorem quotientStack_localPresentation (G : GroupoidInAlgebraicSpaces C S hS B) :
    ∀ x' : (quotientStack G).obj,
      ∃ R ∈ BigFppfOver.topology C S hS ((quotientStack G).p.obj x'),
        ∀ ⦃V : BigFppfOver C S hS⦄ (f : V ⟶ (quotientStack G).p.obj x'), R f →
          ∃ (y : (quotientPrestack G).obj) (φ : (toQuotientStack G).obj y ⟶ x'),
            (quotientStack G).p.IsStronglyCartesian f φ := by
  intro x'
  let p := (quotientStack G).p
  let x : p.Fiber (p.obj x') := ⟨x', rfl⟩
  obtain ⟨R, hR, hloc⟩ := essImage_toQuotientStack G _ x
  refine ⟨R, hR, fun V f hf => ?_⟩
  obtain ⟨y, ⟨e⟩⟩ := hloc hf
  let φ : (toQuotientStack G).obj y.1 ⟶ x' :=
    e.hom.1 ≫ (Functor.IsPreFibered.pullbackMap x.2 f)
  refine ⟨y.1, φ, ?_⟩
  have hφ : p.IsHomLift f φ := by
    dsimp [φ]
    have he : p.IsHomLift (𝟙 V) e.hom.1 := e.hom.2
    have hpull : p.IsHomLift f (Functor.IsPreFibered.pullbackMap x.2 f) :=
      (Functor.IsPreFibered.pullbackMap.IsCartesian x.2 f).toIsHomLift
    have h₀ : p.IsHomLift ((𝟙 V) ≫ f)
        (e.hom.1 ≫ Functor.IsPreFibered.pullbackMap x.2 f) :=
      IsHomLift.comp p (𝟙 V) f e.hom.1 (Functor.IsPreFibered.pullbackMap x.2 f)
    simpa only [Category.id_comp] using h₀
  exact (isFiberedInGroupoids_quotientStack G).isStronglyCartesian_homLift f φ

/-- The inertia of a quotient stack is a stack. -/
theorem inertiaQuotient_isStack (G : GroupoidInAlgebraicSpaces C S hS B) :
    (RelativeInertia.toBase (quotientStack G).p).IsStack
      (BigFppfOver.topology C S hS) :=
  (RelativeInertia.isStackification_functoriality
    (isFibredOneMorphism_toQuotientStack G) (isStack_quotientStack G)
    (isLocallyBijective_toQuotientStack G) (quotientStack_localPresentation G)).1

/-- The inertia of a quotient stack is fibred in groupoids. -/
theorem inertiaQuotient_isFiberedInGroupoids (G : GroupoidInAlgebraicSpaces C S hS B) :
    (RelativeInertia.toBase (quotientStack G).p).IsFiberedInGroupoids := by
  let := (inertiaQuotient_isStack G).isFibered
  exact Functor.IsFiberedInGroupoids.mk' (fun U =>
    RelativeInertia.fiber_isGroupoid _ _ U
      ((isFiberedInGroupoids_quotientStack G).fiber_isGroupoid U))

/-- The pointwise comparison into the inertia of `[U/R]` is strictly over the site. -/
theorem localInertiaComparison_over (G : GroupoidInAlgebraicSpaces C S hS B) :
    localInertiaComparison G ⋙ RelativeInertia.toBase (quotientStack G).p =
      (pointwisePresentation (inertiaGroupoid G)).p := by
  rw [localInertiaComparison, Functor.assoc, RelativeInertia.functoriality_comp_toBase]
  exact presentationInertiaFunctor_over G

/-- The pointwise comparison into the inertia of `[U/R]`, read on the universe-lifted pointwise
presentation of the inertia groupoid and bundled as a 1-morphism of fibred categories. -/
noncomputable def localInertiaPrestackComparison
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    Functor.FibredMor (quotientPrestack (inertiaGroupoid G)).p
      (RelativeInertia.toBase (quotientStack G).p) := by
  let E := inertiaGroupoid G
  let F : (quotientPrestack E).obj ⥤ RelativeInertia (quotientStack G).p :=
    (ULiftHom.down : ULiftHom.{u + 1} (pointwisePresentation E).obj ⥤
      (pointwisePresentation E).obj) ⋙ localInertiaComparison G
  have hF : F ⋙ RelativeInertia.toBase (quotientStack G).p = (quotientPrestack E).p := by
    change ((ULiftHom.down : ULiftHom.{u + 1} (pointwisePresentation E).obj ⥤
      (pointwisePresentation E).obj) ⋙ localInertiaComparison G) ⋙ _ = _
    rw [Functor.assoc, localInertiaComparison_over]
    rfl
  exact ⟨F, (inertiaQuotient_isFiberedInGroupoids G).isFibredOneMorphism hF⟩

/-- The comparison 1-morphism `[G/R'] ⟶ ℐ_{[U/R]}`, as a 1-morphism of fibred categories over the
big fppf site: the extension of the pointwise comparison along the stackification
`[G/_p R'] ⟶ [G/R']`. -/
noncomputable def inertiaExtension (G : GroupoidInAlgebraicSpaces C S hS B) :
    Functor.FibredMor (quotientStack (inertiaGroupoid G)).p
      (RelativeInertia.toBase (quotientStack G).p) := by
  let E := inertiaGroupoid G
  haveI : (Functor.restrictMor (q := RelativeInertia.toBase (quotientStack G).p)
      (isFibredOneMorphism_toQuotientStack E)).IsEquivalence :=
    Functor.restrictMor_toStageThree_isEquivalence.{u} (quotientPrestack E).p
      (BigFppfOver.topology C S hS) (inertiaQuotient_isStack G)
  exact (Functor.restrictMor (q := RelativeInertia.toBase (quotientStack G).p)
    (isFibredOneMorphism_toQuotientStack E)).objPreimage
    (localInertiaPrestackComparison G)

/-- The comparison restricts to the pointwise comparison along the stackification, up to a
2-isomorphism of 1-morphisms of fibred categories. -/
noncomputable def inertiaExtension_restrictIso (G : GroupoidInAlgebraicSpaces C S hS B) :
    (toQuotientStack (inertiaGroupoid G) ⋙ (inertiaExtension G).functor) ≅
      (localInertiaPrestackComparison G).functor := by
  let E := inertiaGroupoid G
  haveI : (Functor.restrictMor (q := RelativeInertia.toBase (quotientStack G).p)
      (isFibredOneMorphism_toQuotientStack E)).IsEquivalence :=
    Functor.restrictMor_toStageThree_isEquivalence.{u} (quotientPrestack E).p
      (BigFppfOver.topology C S hS) (inertiaQuotient_isStack G)
  let e := (Functor.restrictMor (q := RelativeInertia.toBase (quotientStack G).p)
    (isFibredOneMorphism_toQuotientStack E)).objObjPreimageIso
      (localInertiaPrestackComparison G)
  refine ⟨e.hom.trans, e.inv.trans, ?_, ?_⟩
  · change (e.hom ≫ e.inv).trans = 𝟙 _
    rw [e.hom_inv_id]
    rfl
  · change (e.inv ≫ e.hom).trans = 𝟙 _
    rw [e.inv_hom_id]
    rfl

/-- Every component of that 2-isomorphism lies over an identity of the site. -/
theorem inertiaExtension_restrictIso_vertical (G : GroupoidInAlgebraicSpaces C S hS B)
    (A : (quotientPrestack (inertiaGroupoid G)).obj) :
    (RelativeInertia.toBase (quotientStack G).p).IsHomLift
      (𝟙 ((quotientPrestack (inertiaGroupoid G)).p.obj A))
      ((inertiaExtension_restrictIso G).hom.app A) := by
  let E := inertiaGroupoid G
  have : (Functor.restrictMor (q := RelativeInertia.toBase (quotientStack G).p)
      (isFibredOneMorphism_toQuotientStack E)).IsEquivalence :=
    Functor.restrictMor_toStageThree_isEquivalence.{u} (quotientPrestack E).p
      (BigFppfOver.topology C S hS) (inertiaQuotient_isStack G)
  let e := (Functor.restrictMor (q := RelativeInertia.toBase (quotientStack G).p)
    (isFibredOneMorphism_toQuotientStack E)).objObjPreimageIso
      (localInertiaPrestackComparison G)
  exact e.hom.isHomLift A

/-- The comparison restricts to the pointwise comparison on the original, unlifted pointwise
presentation of the inertia groupoid. -/
noncomputable def inertiaExtension_pointwiseIso (G : GroupoidInAlgebraicSpaces C S hS B) :
    (pointwiseToQuotientStack (inertiaGroupoid G) ⋙ (inertiaExtension G).functor) ≅
      localInertiaComparison G :=
  Functor.isoWhiskerLeft
    (ULiftHom.up : (pointwisePresentation (inertiaGroupoid G)).obj ⥤
      (quotientPrestack (inertiaGroupoid G)).obj)
    (inertiaExtension_restrictIso G)

/-- Every component of that 2-isomorphism lies over an identity of the site. -/
theorem inertiaExtension_pointwiseIso_vertical (G : GroupoidInAlgebraicSpaces C S hS B)
    (x : (pointwisePresentation (inertiaGroupoid G)).obj) :
    (RelativeInertia.toBase (quotientStack G).p).IsHomLift
      (𝟙 x.base) ((inertiaExtension_pointwiseIso G).hom.app x) :=
  inertiaExtension_restrictIso_vertical G
    ((quotientPrestackEquivalence (inertiaGroupoid G)).functor.obj x)


/-- Restriction along the stackification `ℐ_{[U/_p R]} ⟶ ℐ_{[U/R]}` of Stacks 06NS is an
equivalence of morphism categories into the quotient stack `[G/R']`. -/
theorem inertiaStackification_restrictEquivalence
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    letI : (quotientStack G).p.IsFibered := (isStack_quotientStack G).isFibered
    letI : (RelativeInertia.toBase (quotientPrestack G).p).IsFibered :=
      RelativeInertia.isFibered (quotientPrestack G).p (quotientPrestack G).p (𝟭 _)
        inferInstance (Functor.isFibredOneMorphism_id (quotientPrestack G).p)
    letI : (RelativeInertia.toBase (quotientStack G).p).IsFibered :=
      RelativeInertia.isFibered (quotientStack G).p (quotientStack G).p (𝟭 _)
        inferInstance (Functor.isFibredOneMorphism_id (quotientStack G).p)
    ∃ hF : (RelativeInertia.toBase (quotientPrestack G).p).IsFibredOneMorphism
        (RelativeInertia.toBase (quotientStack G).p)
        (RelativeInertia.functoriality (quotientPrestack G).p (quotientStack G).p
          (toQuotientStack G) (isFibredOneMorphism_toQuotientStack G).comp_eq),
      (Functor.restrictMor (q := (quotientStack (inertiaGroupoid G)).p) hF).IsEquivalence := by
  let : (quotientStack G).p.IsFibered := (isStack_quotientStack G).isFibered
  let : (RelativeInertia.toBase (quotientPrestack G).p).IsFibered :=
    RelativeInertia.isFibered (quotientPrestack G).p (quotientPrestack G).p (𝟭 _)
      inferInstance (Functor.isFibredOneMorphism_id (quotientPrestack G).p)
  let : (RelativeInertia.toBase (quotientStack G).p).IsFibered :=
    RelativeInertia.isFibered (quotientStack G).p (quotientStack G).p (𝟭 _)
      inferInstance (Functor.isFibredOneMorphism_id (quotientStack G).p)
  obtain ⟨-, hF, hmor, hobj⟩ := RelativeInertia.isStackification_functoriality
    (isFibredOneMorphism_toQuotientStack G) (isStack_quotientStack G)
    (isLocallyBijective_toQuotientStack G) (quotientStack_localPresentation G)
  let hq := isStack_quotientStack (inertiaGroupoid G)
  exact ⟨hF, Functor.Stackification.restrict_isEquivalence hF hmor
    hq.isMorSheaf (localPreimage_mem_essImage hF hobj) hq.hasEffectiveDescent⟩

/-- Restriction along the stackification `ℐ_{[U/_p R]} ⟶ ℐ_{[U/R]}` of Stacks 06NS is an
equivalence of morphism categories into `ℐ_{[U/R]}`. -/
theorem inertiaStackification_restrictSelfEquivalence
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    letI : (quotientStack G).p.IsFibered := (isStack_quotientStack G).isFibered
    letI : (RelativeInertia.toBase (quotientPrestack G).p).IsFibered :=
      RelativeInertia.isFibered (quotientPrestack G).p (quotientPrestack G).p (𝟭 _)
        inferInstance (Functor.isFibredOneMorphism_id (quotientPrestack G).p)
    letI : (RelativeInertia.toBase (quotientStack G).p).IsFibered :=
      RelativeInertia.isFibered (quotientStack G).p (quotientStack G).p (𝟭 _)
        inferInstance (Functor.isFibredOneMorphism_id (quotientStack G).p)
    let hF := Classical.choose (inertiaStackification_restrictEquivalence G)
    (Functor.restrictMor (q := RelativeInertia.toBase (quotientStack G).p) hF).IsEquivalence := by
  let : (quotientStack G).p.IsFibered := (isStack_quotientStack G).isFibered
  let : (RelativeInertia.toBase (quotientPrestack G).p).IsFibered :=
    RelativeInertia.isFibered (quotientPrestack G).p (quotientPrestack G).p (𝟭 _)
      inferInstance (Functor.isFibredOneMorphism_id (quotientPrestack G).p)
  let : (RelativeInertia.toBase (quotientStack G).p).IsFibered :=
    RelativeInertia.isFibered (quotientStack G).p (quotientStack G).p (𝟭 _)
      inferInstance (Functor.isFibredOneMorphism_id (quotientStack G).p)
  obtain ⟨-, hF, hmor, hobj⟩ := RelativeInertia.isStackification_functoriality
    (isFibredOneMorphism_toQuotientStack G) (isStack_quotientStack G)
    (isLocallyBijective_toQuotientStack G) (quotientStack_localPresentation G)
  exact Functor.Stackification.restrict_isEquivalence hF hmor
    (inertiaQuotient_isStack G).isMorSheaf
    (localPreimage_mem_essImage hF hobj)
    (inertiaQuotient_isStack G).hasEffectiveDescent

/-- A morphism over an identity of the base, followed by the image of such a morphism under a
functor over the base, lies over that identity. -/
private theorem isHomLift_map_comp_of_lift_id {𝒮 𝒳 𝒴 : Type*} [Category 𝒮] [Category 𝒳]
    [Category 𝒴] {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} {F : 𝒳 ⥤ 𝒴} (hF : F ⋙ q = p) {X : 𝒮}
    {a b : 𝒳} {c : 𝒴} {φ : a ⟶ b} {ψ : F.obj b ⟶ c} (hφ : p.IsHomLift (𝟙 X) φ)
    (hψ : q.IsHomLift (𝟙 X) ψ) : q.IsHomLift (𝟙 X) (F.map φ ≫ ψ) :=
  have : q.IsHomLift (𝟙 X) (F.map φ) :=
    (BasedFunctor.isHomLift_iff (⟨F, hF⟩ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
      _ _).2 hφ
  IsHomLift.comp_of_lift_id q X _ ψ

/-- The image under a functor over the base of a morphism over an identity of the base, preceded
by a morphism over the same identity, lies over that identity. -/
private theorem isHomLift_comp_map_of_lift_id {𝒮 𝒳 𝒴 : Type*} [Category 𝒮] [Category 𝒳]
    [Category 𝒴] {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} {F : 𝒳 ⥤ 𝒴} (hF : F ⋙ q = p) {X : 𝒮}
    {a b : 𝒳} {c : 𝒴} {ψ : c ⟶ F.obj a} {φ : a ⟶ b} (hψ : q.IsHomLift (𝟙 X) ψ)
    (hφ : p.IsHomLift (𝟙 X) φ) : q.IsHomLift (𝟙 X) (ψ ≫ F.map φ) :=
  have : q.IsHomLift (𝟙 X) (F.map φ) :=
    (BasedFunctor.isHomLift_iff (⟨F, hF⟩ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
      _ _).2 hφ
  IsHomLift.comp_of_lift_id q X ψ _

/-- The pointwise comparison read backwards: a quasi-inverse of the pointwise comparison followed
by the stackification `[G/_p R'] ⟶ [G/R']`. -/
noncomputable def pointwiseInverseComparison (G : GroupoidInAlgebraicSpaces C S hS B) :
    RelativeInertia (pointwisePresentation G).p ⥤ (quotientStack (inertiaGroupoid G)).obj :=
  (presentationInertiaEquivalenceOver G).inv ⋙
    pointwiseToQuotientStack (inertiaGroupoid G)

/-- The inertia of the universe-lifted pointwise presentation, read on the original one. -/
noncomputable def inertiaPrestackToPointwise (G : GroupoidInAlgebraicSpaces C S hS B) :
    RelativeInertia (quotientPrestack G).p ⥤ RelativeInertia (pointwisePresentation G).p :=
  RelativeInertia.functoriality (quotientPrestack G).p (pointwisePresentation G).p
    (ULiftHom.down : ULiftHom.{u + 1} (pointwisePresentation G).obj ⥤
      (pointwisePresentation G).obj) rfl

/-- The backwards pointwise comparison is strictly over the site. -/
theorem pointwiseInverseComparison_over (G : GroupoidInAlgebraicSpaces C S hS B) :
    pointwiseInverseComparison G ⋙ (quotientStack (inertiaGroupoid G)).p =
      RelativeInertia.toBase (pointwisePresentation G).p := by
  rw [pointwiseInverseComparison, Functor.assoc,
    (isFibredOneMorphism_pointwiseToQuotientStack (inertiaGroupoid G)).comp_eq]
  exact (presentationInertiaEquivalenceOver G).inv_over

/-- Reading the inertia of the universe-lifted pointwise presentation on the original one is
strictly over the site. -/
theorem inertiaPrestackToPointwise_over (G : GroupoidInAlgebraicSpaces C S hS B) :
    inertiaPrestackToPointwise G ⋙ RelativeInertia.toBase (pointwisePresentation G).p =
      RelativeInertia.toBase (quotientPrestack G).p :=
  RelativeInertia.functoriality_comp_toBase _ _ _ rfl

/-- The backwards comparison on the inertia of the universe-lifted pointwise presentation,
bundled as a 1-morphism of fibred categories. -/
noncomputable def inversePrestackComparison (G : GroupoidInAlgebraicSpaces C S hS B) :
    Functor.FibredMor (RelativeInertia.toBase (quotientPrestack G).p)
      (quotientStack (inertiaGroupoid G)).p := by
  let E := inertiaGroupoid G
  let F := inertiaPrestackToPointwise G ⋙ pointwiseInverseComparison G
  have hF : F ⋙ (quotientStack E).p =
      RelativeInertia.toBase (quotientPrestack G).p := by
    change (inertiaPrestackToPointwise G ⋙ pointwiseInverseComparison G) ⋙ _ = _
    rw [Functor.assoc, pointwiseInverseComparison_over, inertiaPrestackToPointwise_over]
  exact ⟨F, (isFiberedInGroupoids_quotientStack E).isFibredOneMorphism hF⟩

/-- The comparison 1-morphism `ℐ_{[U/R]} ⟶ [G/R']`: the extension of the backwards pointwise
comparison along the stackification `ℐ_{[U/_p R]} ⟶ ℐ_{[U/R]}` of Stacks 06NS. -/
noncomputable def inverseInertiaExtension (G : GroupoidInAlgebraicSpaces C S hS B) :
    Functor.FibredMor (RelativeInertia.toBase (quotientStack G).p)
      (quotientStack (inertiaGroupoid G)).p := by
  letI : (quotientStack G).p.IsFibered := (isStack_quotientStack G).isFibered
  letI : (RelativeInertia.toBase (quotientPrestack G).p).IsFibered :=
    RelativeInertia.isFibered (quotientPrestack G).p (quotientPrestack G).p (𝟭 _)
      inferInstance (Functor.isFibredOneMorphism_id (quotientPrestack G).p)
  letI : (RelativeInertia.toBase (quotientStack G).p).IsFibered :=
    RelativeInertia.isFibered (quotientStack G).p (quotientStack G).p (𝟭 _)
      inferInstance (Functor.isFibredOneMorphism_id (quotientStack G).p)
  let hF := Classical.choose (inertiaStackification_restrictEquivalence G)
  letI := Classical.choose_spec (inertiaStackification_restrictEquivalence G)
  exact (Functor.restrictMor (q := (quotientStack (inertiaGroupoid G)).p) hF).objPreimage
    (inversePrestackComparison G)

/-- The backwards comparison restricts to the backwards pointwise comparison along the
stackification of Stacks 06NS. -/
noncomputable def inverseInertiaExtension_restrictIso
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (RelativeInertia.functoriality (quotientPrestack G).p (quotientStack G).p
      (toQuotientStack G) (isFibredOneMorphism_toQuotientStack G).comp_eq ⋙
      (inverseInertiaExtension G).functor) ≅ (inversePrestackComparison G).functor := by
  letI : (quotientStack G).p.IsFibered := (isStack_quotientStack G).isFibered
  letI : (RelativeInertia.toBase (quotientPrestack G).p).IsFibered :=
    RelativeInertia.isFibered (quotientPrestack G).p (quotientPrestack G).p (𝟭 _)
      inferInstance (Functor.isFibredOneMorphism_id (quotientPrestack G).p)
  letI : (RelativeInertia.toBase (quotientStack G).p).IsFibered :=
    RelativeInertia.isFibered (quotientStack G).p (quotientStack G).p (𝟭 _)
      inferInstance (Functor.isFibredOneMorphism_id (quotientStack G).p)
  let hF := Classical.choose (inertiaStackification_restrictEquivalence G)
  letI := Classical.choose_spec (inertiaStackification_restrictEquivalence G)
  let e := (Functor.restrictMor (q := (quotientStack (inertiaGroupoid G)).p)
    hF).objObjPreimageIso (inversePrestackComparison G)
  refine ⟨e.hom.trans, e.inv.trans, ?_, ?_⟩
  · change (e.hom ≫ e.inv).trans = 𝟙 _
    rw [e.hom_inv_id]
    rfl
  · change (e.inv ≫ e.hom).trans = 𝟙 _
    rw [e.inv_hom_id]
    rfl

/-- Every component of that 2-isomorphism lies over an identity of the site. -/
theorem inverseInertiaExtension_restrictIso_vertical
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (A : RelativeInertia (quotientPrestack G).p) :
    (quotientStack (inertiaGroupoid G)).p.IsHomLift
      (𝟙 ((RelativeInertia.toBase (quotientPrestack G).p).obj A))
      ((inverseInertiaExtension_restrictIso G).hom.app A) := by
  let : (quotientStack G).p.IsFibered := (isStack_quotientStack G).isFibered
  let : (RelativeInertia.toBase (quotientPrestack G).p).IsFibered :=
    RelativeInertia.isFibered (quotientPrestack G).p (quotientPrestack G).p (𝟭 _)
      inferInstance (Functor.isFibredOneMorphism_id (quotientPrestack G).p)
  let : (RelativeInertia.toBase (quotientStack G).p).IsFibered :=
    RelativeInertia.isFibered (quotientStack G).p (quotientStack G).p (𝟭 _)
      inferInstance (Functor.isFibredOneMorphism_id (quotientStack G).p)
  let hF := Classical.choose (inertiaStackification_restrictEquivalence G)
  let := Classical.choose_spec (inertiaStackification_restrictEquivalence G)
  let e := (Functor.restrictMor (q := (quotientStack (inertiaGroupoid G)).p)
    hF).objObjPreimageIso (inversePrestackComparison G)
  exact e.hom.isHomLift A

/-- Composing the backwards pointwise comparison with the forward comparison gives back the
functoriality of the inertia along the stackification `[U/_p R] ⟶ [U/R]`. -/
noncomputable def pointwiseInverseComparison_extensionIso
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (pointwiseInverseComparison G ⋙ (inertiaExtension G).functor) ≅
      RelativeInertia.functoriality (pointwisePresentation G).p (quotientStack G).p
        (pointwiseToQuotientStack G)
        (isFibredOneMorphism_pointwiseToQuotientStack G).comp_eq := by
  let e := presentationInertiaEquivalenceOver G
  let F := RelativeInertia.functoriality (pointwisePresentation G).p (quotientStack G).p
    (pointwiseToQuotientStack G)
    (isFibredOneMorphism_pointwiseToQuotientStack G).comp_eq
  change (e.inv ⋙ pointwiseToQuotientStack (inertiaGroupoid G) ⋙
    (inertiaExtension G).functor) ≅ F
  exact Functor.isoWhiskerLeft e.inv (inertiaExtension_pointwiseIso G) ≪≫
    Functor.isoWhiskerRight e.counitIso F

/-- Every component of that 2-isomorphism lies over an identity of the site. -/
theorem pointwiseInverseComparison_extensionIso_vertical
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (A : RelativeInertia (pointwisePresentation G).p) :
    (RelativeInertia.toBase (quotientStack G).p).IsHomLift
      (𝟙 ((RelativeInertia.toBase (pointwisePresentation G).p).obj A))
      ((pointwiseInverseComparison_extensionIso G).hom.app A) := by
  let e := presentationInertiaEquivalenceOver G
  have hb : (e.inv.obj A).base = (RelativeInertia.toBase (pointwisePresentation G).p).obj A :=
    Functor.congr_obj e.inv_over A
  have hb₂ := (Functor.congr_obj (presentationInertiaFunctor_over G) (e.inv.obj A)).trans hb
  exact isHomLift_comp_map_of_lift_id
    (RelativeInertia.functoriality_comp_toBase _ _ _
      (isFibredOneMorphism_pointwiseToQuotientStack G).comp_eq)
    (hb ▸ inertiaExtension_pointwiseIso_vertical G (e.inv.obj A))
    (hb₂ ▸ e.counit_vertical A)

/-- The backwards comparison followed by the forward comparison, read on the inertia of the
universe-lifted pointwise presentation. -/
noncomputable def inversePrestackComparison_extensionIso
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    ((inversePrestackComparison G).functor ⋙ (inertiaExtension G).functor) ≅
      RelativeInertia.functoriality (quotientPrestack G).p (quotientStack G).p
        (toQuotientStack G) (isFibredOneMorphism_toQuotientStack G).comp_eq := by
  change (inertiaPrestackToPointwise G ⋙
    pointwiseInverseComparison G ⋙ (inertiaExtension G).functor) ≅ _
  exact Functor.isoWhiskerLeft (inertiaPrestackToPointwise G)
    (pointwiseInverseComparison_extensionIso G)

/-- Every component of that 2-isomorphism lies over an identity of the site. -/
theorem inversePrestackComparison_extensionIso_vertical
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (A : RelativeInertia (quotientPrestack G).p) :
    (RelativeInertia.toBase (quotientStack G).p).IsHomLift
      (𝟙 ((RelativeInertia.toBase (quotientPrestack G).p).obj A))
      ((inversePrestackComparison_extensionIso G).hom.app A) :=
  pointwiseInverseComparison_extensionIso_vertical G
    ((inertiaPrestackToPointwise G).obj A)

/-- The two comparisons compose to the identity of `ℐ_{[U/R]}` after restriction along the
stackification of Stacks 06NS. -/
noncomputable def inverseForwardPrestackIso (G : GroupoidInAlgebraicSpaces C S hS B) :
    (RelativeInertia.functoriality (quotientPrestack G).p (quotientStack G).p
      (toQuotientStack G) (isFibredOneMorphism_toQuotientStack G).comp_eq ⋙
      (inverseInertiaExtension G).functor ⋙ (inertiaExtension G).functor) ≅
      RelativeInertia.functoriality (quotientPrestack G).p (quotientStack G).p
        (toQuotientStack G) (isFibredOneMorphism_toQuotientStack G).comp_eq :=
  Functor.isoWhiskerRight (inverseInertiaExtension_restrictIso G)
    (inertiaExtension G).functor ≪≫ inversePrestackComparison_extensionIso G

/-- Every component of that 2-isomorphism lies over an identity of the site. -/
theorem inverseForwardPrestackIso_vertical (G : GroupoidInAlgebraicSpaces C S hS B)
    (A : RelativeInertia (quotientPrestack G).p) :
    (RelativeInertia.toBase (quotientStack G).p).IsHomLift
      (𝟙 ((RelativeInertia.toBase (quotientPrestack G).p).obj A))
      ((inverseForwardPrestackIso G).hom.app A) := by
  have hc := isHomLift_map_comp_of_lift_id (inertiaExtension G).isFibredOneMorphism.comp_eq
    (inverseInertiaExtension_restrictIso_vertical G A)
    (inversePrestackComparison_extensionIso_vertical G A)
  convert hc using 1 <;> simp [inverseForwardPrestackIso]

/-- The backwards comparison followed by the forward comparison is the identity of `ℐ_{[U/R]}`, by
a 2-isomorphism all of whose components lie over identities of the site. -/
noncomputable def inverseForwardQuotientIsoData
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    { e : ((inverseInertiaExtension G).functor ⋙ (inertiaExtension G).functor) ≅
        𝟭 (RelativeInertia (quotientStack G).p) //
      ∀ A, (RelativeInertia.toBase (quotientStack G).p).IsHomLift
        (𝟙 ((RelativeInertia.toBase (quotientStack G).p).obj A)) (e.hom.app A) } := by
  let p := RelativeInertia.toBase (quotientPrestack G).p
  let p' := RelativeInertia.toBase (quotientStack G).p
  let hF := Classical.choose (inertiaStackification_restrictEquivalence G)
  let R := Functor.restrictMor (q := p') hF
  letI : R.IsEquivalence := inertiaStackification_restrictSelfEquivalence G
  letI : R.Full := inferInstance
  letI : R.Faithful := inferInstance
  let K : Functor.FibredMor p' p' :=
    ⟨(inverseInertiaExtension G).functor ⋙ (inertiaExtension G).functor,
      (inverseInertiaExtension G).isFibredOneMorphism.comp
        (inertiaExtension G).isFibredOneMorphism⟩
  let I : Functor.FibredMor p' p' :=
    ⟨𝟭 _, (inertiaQuotient_isFiberedInGroupoids G).isFibredOneMorphism rfl⟩
  let η : (R.obj K).functor ≅ (R.obj I).functor := inverseForwardPrestackIso G
  have hη (A : RelativeInertia (quotientPrestack G).p) :
      p'.IsHomLift (𝟙 (p.obj A)) (η.hom.app A) := inverseForwardPrestackIso_vertical G A
  let β : R.obj K ≅ R.obj I :=
    { hom := ⟨η.hom, hη⟩
      inv := ⟨η.inv, fun A => by
        let : p'.IsHomLift (𝟙 (p.obj A)) (η.app A).hom := by
          change p'.IsHomLift (𝟙 (p.obj A)) (η.hom.app A)
          exact hη A
        exact IsHomLift.lift_id_inv p' (p.obj A) (η.app A)⟩
      hom_inv_id := Functor.FibredMor.Hom.ext' η.hom_inv_id
      inv_hom_id := Functor.FibredMor.Hom.ext' η.inv_hom_id }
  let ε := (Functor.FullyFaithful.ofFullyFaithful R).preimageIso β
  refine ⟨⟨ε.hom.trans, ε.inv.trans, ?_, ?_⟩, fun A => ε.hom.isHomLift A⟩
  · change (ε.hom ≫ ε.inv).trans = 𝟙 _
    rw [ε.hom_inv_id]
    rfl
  · change (ε.inv ≫ ε.hom).trans = 𝟙 _
    rw [ε.inv_hom_id]
    rfl

/-- The backwards comparison followed by the forward comparison is the identity of
`ℐ_{[U/R]}`. -/
noncomputable def inverseForwardQuotientIso (G : GroupoidInAlgebraicSpaces C S hS B) :
    ((inverseInertiaExtension G).functor ⋙ (inertiaExtension G).functor) ≅
      𝟭 (RelativeInertia (quotientStack G).p) :=
  (inverseForwardQuotientIsoData G).1

/-- Every component of that 2-isomorphism lies over an identity of the site. -/
theorem inverseForwardQuotientIso_vertical (G : GroupoidInAlgebraicSpaces C S hS B)
    (A : RelativeInertia (quotientStack G).p) :
    (RelativeInertia.toBase (quotientStack G).p).IsHomLift
      (𝟙 ((RelativeInertia.toBase (quotientStack G).p).obj A))
      ((inverseForwardQuotientIso G).hom.app A) :=
  (inverseForwardQuotientIsoData G).2 A


/-- The inertia of the pointwise presentation, read on its universe lift. -/
noncomputable def pointwiseInertiaToPrestack (G : GroupoidInAlgebraicSpaces C S hS B) :
    RelativeInertia (pointwisePresentation G).p ⥤ RelativeInertia (quotientPrestack G).p :=
  RelativeInertia.functoriality (pointwisePresentation G).p (quotientPrestack G).p
    (quotientPrestackEquivalence G).functor (quotientPrestackEquivalence_comp G)

/-- The backwards comparison restricts to the backwards pointwise comparison on the original,
unlifted pointwise presentation. -/
noncomputable def pointwiseInverseExtensionIso
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (RelativeInertia.functoriality (pointwisePresentation G).p (quotientStack G).p
      (pointwiseToQuotientStack G)
      (isFibredOneMorphism_pointwiseToQuotientStack G).comp_eq ⋙
      (inverseInertiaExtension G).functor) ≅ pointwiseInverseComparison G := by
  change (pointwiseInertiaToPrestack G ⋙
    (RelativeInertia.functoriality (quotientPrestack G).p (quotientStack G).p
      (toQuotientStack G) (isFibredOneMorphism_toQuotientStack G).comp_eq ⋙
      (inverseInertiaExtension G).functor)) ≅ _
  exact Functor.isoWhiskerLeft (pointwiseInertiaToPrestack G)
    (inverseInertiaExtension_restrictIso G)

/-- Every component of that 2-isomorphism lies over an identity of the site. -/
theorem pointwiseInverseExtensionIso_vertical (G : GroupoidInAlgebraicSpaces C S hS B)
    (A : RelativeInertia (pointwisePresentation G).p) :
    (quotientStack (inertiaGroupoid G)).p.IsHomLift
      (𝟙 ((RelativeInertia.toBase (pointwisePresentation G).p).obj A))
      ((pointwiseInverseExtensionIso G).hom.app A) :=
  inverseInertiaExtension_restrictIso_vertical G ((pointwiseInertiaToPrestack G).obj A)

/-- The forward comparison followed by the backwards comparison restricts to the stackification
`[G/_p R'] ⟶ [G/R']` on the pointwise presentation of the inertia groupoid. -/
noncomputable def localComparison_inverseExtensionIso
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (localInertiaComparison G ⋙ (inverseInertiaExtension G).functor) ≅
      pointwiseToQuotientStack (inertiaGroupoid G) :=
  Functor.isoWhiskerLeft (presentationInertiaFunctor G)
      (pointwiseInverseExtensionIso G) ≪≫
    Functor.isoWhiskerRight (presentationInertiaEquivalenceOver G).unitIso
      (pointwiseToQuotientStack (inertiaGroupoid G))

/-- Every component of that 2-isomorphism lies over an identity of the site. -/
theorem localComparison_inverseExtensionIso_vertical
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (x : (pointwisePresentation (inertiaGroupoid G)).obj) :
    (quotientStack (inertiaGroupoid G)).p.IsHomLift
      (𝟙 x.base) ((localComparison_inverseExtensionIso G).hom.app x) := by
  let e := presentationInertiaEquivalenceOver G
  have hx : (RelativeInertia.toBase (pointwisePresentation G).p).obj
      ((presentationInertiaFunctor G).obj x) = x.base :=
    Functor.congr_obj (presentationInertiaFunctor_over G) x
  have hb : (pointwisePresentation (inertiaGroupoid G)).p.obj
      ((presentationInertiaFunctor G ⋙ e.inv).obj x) = x.base :=
    (Functor.congr_obj e.inv_over ((presentationInertiaFunctor G).obj x)).trans hx
  exact isHomLift_comp_map_of_lift_id
    (isFibredOneMorphism_pointwiseToQuotientStack (inertiaGroupoid G)).comp_eq
    (hx ▸ pointwiseInverseExtensionIso_vertical G ((presentationInertiaFunctor G).obj x))
    (hb ▸ e.unit_vertical x)

/-- The forward comparison followed by the backwards comparison is the identity of `[G/R']`
after restriction along the stackification `[G/_p R'] ⟶ [G/R']`. -/
noncomputable def forwardInversePrestackIso (G : GroupoidInAlgebraicSpaces C S hS B) :
    (toQuotientStack (inertiaGroupoid G) ⋙
      (inertiaExtension G).functor ⋙ (inverseInertiaExtension G).functor) ≅
      toQuotientStack (inertiaGroupoid G) :=
  Functor.isoWhiskerRight (inertiaExtension_restrictIso G)
      (inverseInertiaExtension G).functor ≪≫
    Functor.isoWhiskerLeft
      (ULiftHom.down : ULiftHom.{u + 1}
        (pointwisePresentation (inertiaGroupoid G)).obj ⥤
        (pointwisePresentation (inertiaGroupoid G)).obj)
      (localComparison_inverseExtensionIso G)

/-- Every component of that 2-isomorphism lies over an identity of the site. -/
theorem forwardInversePrestackIso_vertical (G : GroupoidInAlgebraicSpaces C S hS B)
    (A : (quotientPrestack (inertiaGroupoid G)).obj) :
    (quotientStack (inertiaGroupoid G)).p.IsHomLift
      (𝟙 ((quotientPrestack (inertiaGroupoid G)).p.obj A))
      ((forwardInversePrestackIso G).hom.app A) := by
  exact isHomLift_map_comp_of_lift_id (inverseInertiaExtension G).isFibredOneMorphism.comp_eq
    (inertiaExtension_restrictIso_vertical G A)
    (localComparison_inverseExtensionIso_vertical G _)

/-- The forward comparison followed by the backwards comparison is the identity of `[G/R']`, by a
2-isomorphism all of whose components lie over identities of the site. -/
noncomputable def forwardInverseQuotientIsoData
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    { e : ((inertiaExtension G).functor ⋙ (inverseInertiaExtension G).functor) ≅
        𝟭 (quotientStack (inertiaGroupoid G)).obj //
      ∀ A, (quotientStack (inertiaGroupoid G)).p.IsHomLift
        (𝟙 ((quotientStack (inertiaGroupoid G)).p.obj A)) (e.hom.app A) } := by
  let E := inertiaGroupoid G
  let p := (quotientPrestack E).p
  let p' := (quotientStack E).p
  let R := Functor.restrictMor (q := p') (isFibredOneMorphism_toQuotientStack E)
  haveI : R.IsEquivalence :=
    Functor.restrictMor_toStageThree_isEquivalence.{u} (quotientPrestack E).p
      (BigFppfOver.topology C S hS) (isStack_quotientStack E)
  letI : R.Full := inferInstance
  letI : R.Faithful := inferInstance
  let K : Functor.FibredMor p' p' :=
    ⟨(inertiaExtension G).functor ⋙ (inverseInertiaExtension G).functor,
      (inertiaExtension G).isFibredOneMorphism.comp
        (inverseInertiaExtension G).isFibredOneMorphism⟩
  let I : Functor.FibredMor p' p' :=
    ⟨𝟭 _, (isFiberedInGroupoids_quotientStack E).isFibredOneMorphism rfl⟩
  let η : (R.obj K).functor ≅ (R.obj I).functor := forwardInversePrestackIso G
  have hη (A : (quotientPrestack E).obj) :
      p'.IsHomLift (𝟙 (p.obj A)) (η.hom.app A) := forwardInversePrestackIso_vertical G A
  let β : R.obj K ≅ R.obj I :=
    { hom := ⟨η.hom, hη⟩
      inv := ⟨η.inv, fun A => by
        let : p'.IsHomLift (𝟙 (p.obj A)) (η.app A).hom := hη A
        exact IsHomLift.lift_id_inv p' (p.obj A) (η.app A)⟩
      hom_inv_id := Functor.FibredMor.Hom.ext' η.hom_inv_id
      inv_hom_id := Functor.FibredMor.Hom.ext' η.inv_hom_id }
  let ε := (Functor.FullyFaithful.ofFullyFaithful R).preimageIso β
  refine ⟨⟨ε.hom.trans, ε.inv.trans, ?_, ?_⟩, fun A => ε.hom.isHomLift A⟩
  · change (ε.hom ≫ ε.inv).trans = 𝟙 _
    rw [ε.hom_inv_id]
    rfl
  · change (ε.inv ≫ ε.hom).trans = 𝟙 _
    rw [ε.inv_hom_id]
    rfl


/-! ### Compatibility with the two 1-morphisms down to `[U/R]` -/

/-- On the pointwise presentations, the comparison carries the forgetful 1-morphism of the
inertia to the 1-morphism of Stacks 046Q induced by the forgetful morphism of groupoids. -/
noncomputable def inertiaForgetfulPointwiseIso
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (localInertiaComparison G ⋙ RelativeInertia.π (quotientStack G).p) ≅
      (pointwiseToQuotientStack (inertiaGroupoid G) ⋙
        (quotientStackMap (inertiaForgetful G)).toFunctor) := by
  let f := inertiaForgetful G
  let i := (quotientPointwiseMap f).toFunctor.isoCopyObj
    (underlyingPoint G) (fun x => eqToIso (quotientPointwiseMap_forgetful_obj G x))
  let j := (BasedNatTrans.forgetful _ _).mapIso (quotientStackMap_commutes f)
  exact Functor.isoWhiskerRight i.symm (pointwiseToQuotientStack G) ≪≫ j

/-- Every component of that 2-isomorphism lies over an identity of the site. -/
theorem inertiaForgetfulPointwiseIso_vertical
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (x : (pointwisePresentation (inertiaGroupoid G)).obj) :
    (quotientStack G).p.IsHomLift (𝟙 x.base)
      ((inertiaForgetfulPointwiseIso G).hom.app x) := by
  exact isHomLift_map_comp_of_lift_id (F := pointwiseToQuotientStack G)
    (isFibredOneMorphism_pointwiseToQuotientStack G).comp_eq
    (φ := eqToHom (quotientPointwiseMap_forgetful_obj G x).symm)
    (IsHomLift.eqToHom_domain_lift_id _ rfl)
    ((quotientStackMap_commutes (inertiaForgetful G)).hom.isHomLift' x)

/-- The same compatibility, restricted along the stackification `[G/_p R'] ⟶ [G/R']`. -/
noncomputable def inertiaForgetfulPrestackIso
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (toQuotientStack (inertiaGroupoid G) ⋙
      (inertiaExtension G).functor ⋙ RelativeInertia.π (quotientStack G).p) ≅
      (toQuotientStack (inertiaGroupoid G) ⋙
        (quotientStackMap (inertiaForgetful G)).toFunctor) :=
  Functor.isoWhiskerRight (inertiaExtension_restrictIso G)
      (RelativeInertia.π (quotientStack G).p) ≪≫
    Functor.isoWhiskerLeft
      (ULiftHom.down : ULiftHom.{u + 1}
        (pointwisePresentation (inertiaGroupoid G)).obj ⥤
        (pointwisePresentation (inertiaGroupoid G)).obj)
      (inertiaForgetfulPointwiseIso G)

/-- Every component of that 2-isomorphism lies over an identity of the site. -/
theorem inertiaForgetfulPrestackIso_vertical
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (A : (quotientPrestack (inertiaGroupoid G)).obj) :
    (quotientStack G).p.IsHomLift
      (𝟙 ((quotientPrestack (inertiaGroupoid G)).p.obj A))
      ((inertiaForgetfulPrestackIso G).hom.app A) := by
  exact isHomLift_map_comp_of_lift_id (F := RelativeInertia.π (quotientStack G).p) rfl
    (inertiaExtension_restrictIso_vertical G A)
    (inertiaForgetfulPointwiseIso_vertical G _)

/-- The forgetful 1-morphism of the inertia of `[U/R]`, read through the comparison, is the
1-morphism `[G/R'] ⟶ [U/R]` of Stacks 046Q induced by the forgetful morphism of groupoids
`(G, R', s', t', c') ⟶ (U, R, s, t, c)`; the 2-isomorphism lies over identities of the site. -/
noncomputable def inertiaForgetfulQuotientIsoData
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    { e : ((inertiaExtension G).functor ⋙ RelativeInertia.π (quotientStack G).p) ≅
        (quotientStackMap (inertiaForgetful G)).toFunctor //
      ∀ A, (quotientStack G).p.IsHomLift
        (𝟙 ((quotientStack (inertiaGroupoid G)).p.obj A)) (e.hom.app A) } := by
  let E := inertiaGroupoid G
  let p := (quotientPrestack E).p
  let p' := (quotientStack E).p
  let q := (quotientStack G).p
  let R := Functor.restrictMor (q := q) (isFibredOneMorphism_toQuotientStack E)
  haveI : R.IsEquivalence :=
    Functor.restrictMor_toStageThree_isEquivalence.{u} (quotientPrestack E).p
      (BigFppfOver.topology C S hS) (isStack_quotientStack G)
  letI : R.Full := inferInstance
  letI : R.Faithful := inferInstance
  let K : Functor.FibredMor p' q :=
    ⟨(inertiaExtension G).functor ⋙ RelativeInertia.π q,
      (isFiberedInGroupoids_quotientStack G).isFibredOneMorphism
        (inertiaExtension G).isFibredOneMorphism.comp_eq⟩
  let I : Functor.FibredMor p' q :=
    ⟨(quotientStackMap (inertiaForgetful G)).toFunctor,
      (isFiberedInGroupoids_quotientStack G).isFibredOneMorphism
        (quotientStackMap (inertiaForgetful G)).w⟩
  let η : (R.obj K).functor ≅ (R.obj I).functor := inertiaForgetfulPrestackIso G
  have hη (A : (quotientPrestack E).obj) :
      q.IsHomLift (𝟙 (p.obj A)) (η.hom.app A) := inertiaForgetfulPrestackIso_vertical G A
  let β : R.obj K ≅ R.obj I :=
    { hom := ⟨η.hom, hη⟩
      inv := ⟨η.inv, fun A => by
        let : q.IsHomLift (𝟙 (p.obj A)) (η.app A).hom := hη A
        exact IsHomLift.lift_id_inv q (p.obj A) (η.app A)⟩
      hom_inv_id := Functor.FibredMor.Hom.ext' η.hom_inv_id
      inv_hom_id := Functor.FibredMor.Hom.ext' η.inv_hom_id }
  let ε := (Functor.FullyFaithful.ofFullyFaithful R).preimageIso β
  refine ⟨⟨ε.hom.trans, ε.inv.trans, ?_, ?_⟩, fun A => ε.hom.isHomLift A⟩
  · change (ε.hom ≫ ε.inv).trans = 𝟙 _
    rw [ε.hom_inv_id]
    rfl
  · change (ε.inv ≫ ε.hom).trans = 𝟙 _
    rw [ε.inv_hom_id]
    rfl

/-! ### The second assertion of Stacks 06PB -/

/-- The comparison 1-morphism `[G/R'] ⟶ ℐ_{[U/R]}`, as a 1-morphism of categories over the big fppf
site: the quotient stack of the inertia groupoid `(G, R', s', t', c')` maps to the inertia of the
quotient stack `[U/R]`, sending a `T`-point `(x, g)` of the stabilizer to the `T`-point `x` of
`[U/R]` equipped with the automorphism `g`. -/
noncomputable def inertiaComparison (G : GroupoidInAlgebraicSpaces C S hS B) :
    quotientStack (inertiaGroupoid G) ⥤ᵇ
      BasedCategory.ofFunctor (RelativeInertia.toBase (quotientStack G).p) :=
  ⟨(inertiaExtension G).functor, (inertiaExtension G).isFibredOneMorphism.comp_eq⟩

/-- The comparison `[G/R'] ⟶ ℐ_{[U/R]}` composed with the structure functor of the inertia of
`[U/R]` is the structure functor of `[G/R']`: it is a 1-morphism of categories over the big fppf
site. -/
@[stacks 06PB "second assertion: the comparison [G/R'] ⟶ I_{[U/R]} is over the site"]
theorem inertiaComparison_comp_toBase (G : GroupoidInAlgebraicSpaces C S hS B) :
    (inertiaComparison G).toFunctor ⋙ RelativeInertia.toBase (quotientStack G).p =
      (quotientStack (inertiaGroupoid G)).p :=
  (inertiaExtension G).isFibredOneMorphism.comp_eq

/-- Composing the comparison `[G/R'] ⟶ ℐ_{[U/R]}` with the forgetful 1-morphism `ℐ_{[U/R]} ⟶ [U/R]`
gives the 1-morphism `[G/R'] ⟶ [U/R]` of Stacks 046Q induced by the forgetful morphism of groupoids
`(G, R', s', t', c') ⟶ (U, R, s, t, c)`, by an isomorphism of functors. -/
@[stacks 06PB "second assertion: the comparison is a 1-morphism over [U/R]"]
noncomputable def inertiaComparisonForgetfulIso
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    ((inertiaComparison G).toFunctor ⋙ RelativeInertia.π (quotientStack G).p) ≅
      (quotientStackMap (inertiaForgetful G)).toFunctor :=
  (inertiaForgetfulQuotientIsoData G).1

/-- Every component of that isomorphism lies over an identity of the site, so it is a 2-morphism
over the big fppf site. -/
theorem inertiaComparisonForgetfulIso_vertical
    (G : GroupoidInAlgebraicSpaces C S hS B) (A : (quotientStack (inertiaGroupoid G)).obj) :
    (quotientStack G).p.IsHomLift
      (𝟙 ((quotientStack (inertiaGroupoid G)).p.obj A))
      ((inertiaComparisonForgetfulIso G).hom.app A) :=
  (inertiaForgetfulQuotientIsoData G).2 A

/-- The underlying functor of the comparison `[G/R'] ⟶ ℐ_{[U/R]}` is an equivalence of categories:
the quotient stack of the inertia groupoid `(G, R', s', t', c')` is the inertia stack of `[U/R]`.
-/
@[stacks 06PB "second assertion: I_{[U/R]} = [G/R'], the comparison is an equivalence"]
theorem isEquivalence_inertiaComparison (G : GroupoidInAlgebraicSpaces C S hS B) :
    (inertiaComparison G).toFunctor.IsEquivalence :=
  (CategoryTheory.Equivalence.mk (inertiaComparison G).toFunctor
    (inverseInertiaExtension G).functor (forwardInverseQuotientIsoData G).1.symm
    (inverseForwardQuotientIso G)).isEquivalence_functor

/-- The equivalence `[G/R'] ≌ ℐ_{[U/R]}` of categories over the big fppf site: the comparison and
its quasi-inverse, with two 2-isomorphisms all of whose components lie over identities of the site.
-/
noncomputable def inertiaQuotientStackEquivalence
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    BasedCategory.Equivalence (quotientStack (inertiaGroupoid G))
      (BasedCategory.ofFunctor (RelativeInertia.toBase (quotientStack G).p)) where
  functor := inertiaComparison G
  inverse := ⟨(inverseInertiaExtension G).functor,
    (inverseInertiaExtension G).isFibredOneMorphism.comp_eq⟩
  unitIso := BasedNatIso.mkNatIso (forwardInverseQuotientIsoData G).1
    (forwardInverseQuotientIsoData G).2
  counitIso := BasedNatIso.mkNatIso (inverseForwardQuotientIso G)
    (inverseForwardQuotientIso_vertical G)


/-! ### The comparison in the 2-category of categories fibred in groupoids -/

/-- The comparison 1-morphism `[G/R'] ⟶ ℐ_{[U/R]}`, read in the 2-category of categories fibred in
groupoids over the big fppf site. -/
noncomputable def inertiaQuotientStackCompare (G : GroupoidInAlgebraicSpaces C S hS B) :
    quotientStackCFG C S hS (inertiaGroupoid G) ⟶
      inertia C S hS (quotientStackCFG C S hS G) :=
  Bicategory.InducedBicategory.mkHom (inertiaComparison G)

/-- The comparison of Stacks 06PB, read in the 2-category of categories fibred in groupoids, is
a 1-morphism over `[U/R]`: composing it with the forgetful 1-morphism of the inertia gives the
1-morphism `[G/R'] ⟶ [U/R]` of Stacks 046Q induced by the forgetful morphism of groupoids. -/
noncomputable def inertiaQuotientStackCompareOver
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    inertiaQuotientStackCompare G ≫ inertiaCatProjection C S hS (quotientStackCFG C S hS G) ≅
      (Bicategory.InducedBicategory.mkHom (quotientStackMap (inertiaForgetful G)) :
        quotientStackCFG C S hS (inertiaGroupoid G) ⟶ quotientStackCFG C S hS G) :=
  Bicategory.InducedBicategory.isoMk
    (BasedNatIso.mkNatIso (inertiaComparisonForgetfulIso G)
      (inertiaComparisonForgetfulIso_vertical G))

/-- The comparison of Stacks 06PB, read in the 2-category of categories fibred in groupoids, has
an equivalence of categories as its underlying functor. -/
theorem isEquivalence_inertiaQuotientStackCompare
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (inertiaQuotientStackCompare G).hom.toFunctor.IsEquivalence :=
  isEquivalence_inertiaComparison G

end QuotientStack

end AlgebraicGeometry.Stack

end
