module

public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import StacksFrontier.CategoryTheory.Sites.Point.LocalizedPoint
public import StacksFrontier.CategoryTheory.Sites.Point.Topos

/-! # Points of a localized site above a given point: the one-to-one correspondence (Stacks 04H3)

Let `(C, J)` be a site, let `p` be a point of `C` with fibre functor `u = p.fiber`, and let `U` be
an object of `C`.  Stacks 04H2 attaches to every `x ∈ u(U)` a point `q_x` of the localized site
`C/U` lying above `p`, whose fibre functor is
```
  v_x : (φ : V ⟶ U) ↦ {y ∈ u(V) | u(φ)(y) = x} ;
```
this is Mathlib's `CategoryTheory.GrothendieckTopology.Point.over`, built from the subfunctor
`FunctorToTypes.fromOverSubfunctor u x` of `Over.forget U ⋙ u`, and the identification
`j_U ∘ q_x = p` is `Point.sheafFiberOverIso`.  Stacks 04H3 asserts that `x ↦ q_x` is a *one-to-one
correspondence* between `u(U)` and the points of `C/U` lying over `p`.

## Points lying over `p`

A point of `C/U` lying over `p` is `Point.OverPoint p U`: a point `q` of `C/U` together with an
isomorphism `j_U⁻¹ ⋙ q⁻¹ ≅ p⁻¹` of stalk functors on sheaves of sets, i.e. an identification
`j_U ∘ q = p` of morphisms of topoi (the stalk functor of a point is the inverse image of its
morphism of topoi, Stacks 00YA (1)).  Points over `p` form a category, a morphism being a morphism
of points compatible with the identifications.  The correspondence is between `u(U)` and the
isomorphism classes of points over `p`.  The identification is part of the data: two points
`q_x`, `q_{x'}` can be isomorphic as points of `C/U` for `x ≠ x'` (for instance when `C/U` is
equivalent to the final category), and they are told apart by the identification
`j_U ∘ q_x = p`, which takes the germ at `(U/U, ∗)` of the tautological section of `j_U⁻¹(h_U^#)`
to the germ of the tautological section of `h_U^#` at `(U, x)`.

## The proof

Let `q` be a point over `p` with fibre functor `v`.  For `W = (φ : V ⟶ U)` and `e ∈ v(W)` the map
`θ = OverPoint.toFiber : v(W) → u(V)` sends `e` to the element of `u(V) = p⁻¹(h_V^#)` (Stacks
00YA, `PointOfTopos.fiberToSheafYoneda`) which `j_U ∘ q = p` assigns to the germ at `(W, e)` of the
tautological section of `j_U⁻¹(h_V^#)`.  It is natural in `W`, so its value on the unique element
of `v(U/U)` (`U/U` is final in `C/U`) is an element `x = OverPoint.baseElement q` of `u(U)`, and
`θ` lands in `{y ∈ u(V) | y ↦ x}`.  It is a bijection onto that set: this is the cartesian square
```
  v(V/U) ---> u(V)
    |           | u(φ)
  v(U/U) ---> u(U)
```
of Stacks' proof.  It is proved on germs: the stalk of `q` is a filtered colimit, and the
restriction `j_U^p(h_V ⟶ h_V^#)` of the sheafification map is locally bijective on `C/U`
(`Presheaf.isLocallyInjective_whisker`, `Presheaf.isLocallySurjective_whisker`), which is the
identification `(j_U^p h_V)^# = j_U⁻¹(h_V^#)` of Stacks 00XM, so that `q⁻¹(j_U⁻¹ h_V^#)` is the
stalk of the presheaf `W ↦ Mor(W.left, V)`.  The resulting isomorphism `v ≅ v_x` is compatible
with the identifications, giving `OverPoint.isoOfFiber : q ≅ q_x`, and `x` is recovered from
`q_x` (`OverPoint.baseElement_ofFiber`) and depends only on the isomorphism class of `q`
(`OverPoint.baseElement_eq_of_hom`).  Stacks' proof derives the square from the exactness of
sheafification (Stacks 00WJ) and of `q⁻¹`; on germs that exactness is the commutation of filtered
colimits of sets with finite limits, used here through `Point.toPresheafFiber_eq_iff'`.

The subfunctor form of the correspondence, `x ↦ v_x` onto the subfunctors of
`Over.forget U ⋙ u` satisfying `FunctorToTypes.IsFromOver`, is in
`StacksFrontier/CategoryTheory/Sites/Point/OverBijection.lean`.

## Main results

* `CategoryTheory.GrothendieckTopology.Point.OverPoint`: points of `C/U` lying over `p`, and their
  category.
* `CategoryTheory.GrothendieckTopology.Point.OverPoint.isoOfFiber`: every point `q` over `p` is
  isomorphic over `p` to `q_x` for `x = OverPoint.baseElement q`.
* `CategoryTheory.GrothendieckTopology.Point.OverPoint.existsUnique_nonempty_iso_ofFiber`
  (Stacks 04H3): every point of `C/U` over `p` is isomorphic over `p` to `q_x` for exactly one
  `x ∈ u(U)`.
* `CategoryTheory.GrothendieckTopology.Point.OverPoint.fiberEquivOverPoint` (Stacks 04H3): the
  bijection `u(U) ≃ {points of C/U over p}/≅`, `x ↦ [q_x]`.
* `CategoryTheory.GrothendieckTopology.Point.OverPoint.fiberEquivOverPoint_symm_mk`: its inverse
  is `[q] ↦ baseElement q`.

Tags covered: 04H3.
-/

@[expose] public section

namespace CategoryTheory.GrothendieckTopology.Point

open Limits Opposite

universe v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A point of the localized site `C/U` lying over the point `Φ` of `C`: a point `q` of
`(Over U, J.over U)` together with an isomorphism `j_U⁻¹ ⋙ q⁻¹ ≅ p⁻¹` of the stalk functors on
sheaves of sets.  The stalk functor of a point is the inverse image of the associated morphism of
topoi (Stacks 00YA (1)), `j_U⁻¹` is `J.overPullback`, and a morphism of topoi is determined up to
unique isomorphism by its inverse image functor; so this is a point `q` of `C/U` together with an
identification `j_U ∘ q = p` of morphisms of topoi. -/
structure OverPoint (Φ : Point.{max u v} J) (U : C) where
  /-- the point `q` of `C/U` -/
  point : Point.{max u v} (J.over U)
  /-- the identification `j_U ∘ q = p`, as an isomorphism of inverse image functors -/
  iso : J.overPullback (Type max u v) U ⋙ point.sheafFiber ≅ Φ.sheafFiber

namespace OverPoint

variable {Φ : Point.{max u v} J} {U : C}

/-- A morphism of points of `C/U` lying over `Φ`: a morphism of points of `C/U` compatible with
the identifications `j_U ∘ q = p`. -/
@[ext]
structure Hom (q₁ q₂ : OverPoint Φ U) where
  /-- the underlying morphism of points of `C/U` -/
  hom : q₁.point ⟶ q₂.point
  comm : Functor.whiskerLeft (J.overPullback (Type max u v) U)
      (Point.Hom.sheafFiber (A := Type max u v) hom) ≫ q₁.iso.hom = q₂.iso.hom

instance : Category (OverPoint Φ U) where
  Hom := Hom
  id q := ⟨𝟙 q.point, by simp⟩
  comp f g := ⟨f.hom ≫ g.hom, by
    rw [Point.Hom.sheafFiber_comp, Functor.whiskerLeft_comp, Category.assoc, f.comm, g.comm]⟩
  id_comp f := Hom.ext (Category.id_comp (Hom.hom f))
  comp_id f := Hom.ext (Category.comp_id (Hom.hom f))
  assoc f g h := Hom.ext (Category.assoc (Hom.hom f) (Hom.hom g) (Hom.hom h))

/-- An isomorphism of points of `C/U` whose underlying morphism is compatible with the
identifications `j_U ∘ q = p` is an isomorphism of points of `C/U` lying over `Φ`. -/
def isoMk {q₁ q₂ : OverPoint Φ U} (e : q₁.point ≅ q₂.point)
    (he : Functor.whiskerLeft (J.overPullback (Type max u v) U)
      (Point.Hom.sheafFiber (A := Type max u v) e.hom) ≫ q₁.iso.hom = q₂.iso.hom) :
    q₁ ≅ q₂ where
  hom := ⟨e.hom, he⟩
  inv := ⟨e.inv, by
    rw [← he, ← Category.assoc, ← Functor.whiskerLeft_comp, ← Point.Hom.sheafFiber_comp,
      e.hom_inv_id, Point.Hom.sheafFiber_id, Functor.whiskerLeft_id', Category.id_comp]⟩
  hom_inv_id := Hom.ext e.hom_inv_id
  inv_hom_id := Hom.ext e.inv_hom_id

/-- The point `q_x = Φ.over x` of `C/U` of Stacks 04H2, with the identification
`j_U ∘ q_x = p` of `Point.sheafFiberOverIso`. -/
noncomputable abbrev ofFiber (x : Φ.fiber.obj U) : OverPoint Φ U where
  point := Φ.over x
  iso := Φ.sheafFiberOverIso x (Type max u v)

/-- The unique element of the fibre of `q` at the final object `U/U` of `C/U`. -/
noncomputable def finalElement (q : OverPoint Φ U) : q.point.fiber.obj (Over.mk (𝟙 U)) :=
  (q.point.uniqueFiberObj _ Over.mkIdTerminal).default

lemma eq_finalElement (q : OverPoint Φ U) (e : q.point.fiber.obj (Over.mk (𝟙 U))) :
    e = q.finalElement :=
  (q.point.uniqueFiberObj _ Over.mkIdTerminal).uniq e

/-- The germ at the neighbourhood `(W, e)` of `q` of a section `s` of a sheaf `F` on `C` over
`W.left`, as an element of the stalk at `q` of the restriction `j_U⁻¹F`. -/
noncomputable def germ (q : OverPoint Φ U) (F : Sheaf J (Type max u v)) {W : Over U}
    (e : q.point.fiber.obj W) (s : F.obj.obj (op W.left)) :
    (J.overPullback (Type max u v) U ⋙ q.point.sheafFiber).obj F :=
  q.point.toPresheafFiber W e ((J.overPullback (Type max u v) U).obj F).obj s

lemma map_germ (q : OverPoint Φ U) {F G : Sheaf J (Type max u v)} (σ : F ⟶ G) {W : Over U}
    (e : q.point.fiber.obj W) (s : F.obj.obj (op W.left)) :
    (J.overPullback (Type max u v) U ⋙ q.point.sheafFiber).map σ (q.germ F e s) =
      q.germ G e (σ.hom.app (op W.left) s) :=
  q.point.toPresheafFiber_naturality_apply ((J.overPullback (Type max u v) U).map σ).hom W e s

lemma germ_map (q : OverPoint Φ U) (F : Sheaf J (Type max u v)) {W₁ W₂ : Over U} (g : W₁ ⟶ W₂)
    (e : q.point.fiber.obj W₁) (s : F.obj.obj (op W₂.left)) :
    q.germ F e (F.obj.map g.left.op s) = q.germ F (q.point.fiber.map g e) s :=
  q.point.toPresheafFiber_w_apply g e ((J.overPullback (Type max u v) U).obj F).obj s

/-- For a point `q` of `C/U` lying over `Φ`, with fibre functor `v`, the map
`v(V/U) → u(V)` of Stacks 04H3: `e ∈ v(V/U)` goes to the element of `u(V) = p⁻¹(h_V^#)`
(Stacks 00YA) corresponding, under `j_U ∘ q = p`, to the germ at `(V/U, e)` of the
tautological section of `j_U⁻¹(h_V^#)`. -/
noncomputable def toFiber (q : OverPoint Φ U) (W : Over U) (e : q.point.fiber.obj W) :
    Φ.fiber.obj W.left :=
  (PointOfTopos.fiberToSheafYoneda Φ W.left).inv
    (q.iso.hom.app ((Sheaf.sheafifiedYoneda J).obj W.left)
      (q.germ _ e (Sheaf.tautologicalSection J W.left)))

lemma fiberToSheafYoneda_hom_toFiber (q : OverPoint Φ U) (W : Over U)
    (e : q.point.fiber.obj W) :
    (PointOfTopos.fiberToSheafYoneda Φ W.left).hom (q.toFiber W e) =
      q.iso.hom.app ((Sheaf.sheafifiedYoneda J).obj W.left)
        (q.germ _ e (Sheaf.tautologicalSection J W.left)) := by
  have h := ConcreteCategory.congr_hom (PointOfTopos.fiberToSheafYoneda Φ W.left).inv_hom_id
    (q.iso.hom.app ((Sheaf.sheafifiedYoneda J).obj W.left)
      (q.germ _ e (Sheaf.tautologicalSection J W.left)))
  rw [CategoryTheory.comp_apply, CategoryTheory.id_apply] at h
  exact h

lemma toFiber_injective_aux {V : C} {y₁ y₂ : Φ.fiber.obj V}
    (h : (PointOfTopos.fiberToSheafYoneda Φ V).hom y₁ =
      (PointOfTopos.fiberToSheafYoneda Φ V).hom y₂) : y₁ = y₂ :=
  (mono_iff_injective (PointOfTopos.fiberToSheafYoneda Φ V).hom).1 inferInstance h

lemma iso_hom_app_injective (q : OverPoint Φ U) (F : Sheaf J (Type max u v)) :
    Function.Injective (q.iso.hom.app F) :=
  (mono_iff_injective (q.iso.hom.app F)).1 inferInstance

lemma iso_hom_app_iso_inv_app (q : OverPoint Φ U) (F : Sheaf J (Type max u v))
    (x : Φ.sheafFiber.obj F) : q.iso.hom.app F (q.iso.inv.app F x) = x := by
  have h := ConcreteCategory.congr_hom (q.iso.inv_hom_id_app F) x
  rwa [CategoryTheory.comp_apply, CategoryTheory.id_apply] at h

/-- The identification `j_U ∘ q = p` sends the germ at `(V/U, e)` of a section `s` of a sheaf
`F` over `V` to the germ of `s` at `(V, θ(e))`, where `θ = toFiber`. -/
lemma iso_hom_app_germ (q : OverPoint Φ U) (F : Sheaf J (Type max u v))
    {W : Over U} (e : q.point.fiber.obj W) (s : F.obj.obj (op W.left)) :
    q.iso.hom.app F (q.germ F e s) = Φ.toPresheafFiber W.left (q.toFiber W e) F.obj s := by
  set σ := (Sheaf.sectionEquiv J).symm s
  have hs : σ.hom.app (op W.left) (Sheaf.tautologicalSection J W.left) = s := by
    rw [← Sheaf.sectionEquiv_comp, Category.id_comp]
    exact Equiv.apply_symm_apply _ _
  have h1 : q.germ F e s = (J.overPullback (Type max u v) U ⋙ q.point.sheafFiber).map σ
      (q.germ _ e (Sheaf.tautologicalSection J W.left)) := by
    rw [map_germ, hs]
  rw [h1, NatTrans.naturality_apply, ← fiberToSheafYoneda_hom_toFiber,
    PointOfTopos.fiberToSheafYoneda_hom_apply, ← hs]
  exact Φ.toPresheafFiber_naturality_apply σ.hom _ _ _

/-- `θ = toFiber` is natural: for `g : W₁ ⟶ W₂` in `C/U`, `θ(v(g)(e)) = u(g)(θ(e))`. -/
lemma toFiber_naturality (q : OverPoint Φ U) {W₁ W₂ : Over U} (g : W₁ ⟶ W₂)
    (e : q.point.fiber.obj W₁) :
    q.toFiber W₂ (q.point.fiber.map g e) = Φ.fiber.map g.left (q.toFiber W₁ e) := by
  apply toFiber_injective_aux
  rw [fiberToSheafYoneda_hom_toFiber, ← germ_map, iso_hom_app_germ,
    PointOfTopos.fiberToSheafYoneda_hom_apply]
  exact Φ.toPresheafFiber_w_apply g.left (q.toFiber W₁ e) _ _

/-- The element `x ∈ u(U)` attached to a point `q` of `C/U` lying over `Φ`: the image under
`θ = toFiber` of the unique element of `v(U/U)`. -/
noncomputable def baseElement (q : OverPoint Φ U) : Φ.fiber.obj U :=
  q.toFiber (Over.mk (𝟙 U)) q.finalElement

/-- `θ` maps `v(V/U)` into the elements of `u(V)` lying over `x = baseElement q`. -/
lemma map_hom_toFiber (q : OverPoint Φ U) (W : Over U) (e : q.point.fiber.obj W) :
    Φ.fiber.map W.hom (q.toFiber W e) = q.baseElement := by
  have h := q.toFiber_naturality (Over.homMk W.hom : W ⟶ Over.mk (𝟙 U)) e
  rw [q.eq_finalElement (q.point.fiber.map _ e)] at h
  exact h.symm

/-! #### The presheaf `j_U^p h_V` -/

/-- The restriction `j_U^p h_V : (W ⟶ U) ↦ Mor(W, V)` of the presheaf represented by `V` to
`C/U`. -/
abbrev forgetYoneda (V : C) : (Over U)ᵒᵖ ⥤ Type max u v :=
  (Over.forget U).op ⋙ CategoryTheory.uliftYoneda.{u}.obj V

/-- The sections of `j_U^p h_V` over `W` are the morphisms `W.left ⟶ V`. -/
def forgetYonedaEquiv {V : C} {W : Over U} :
    (forgetYoneda (U := U) V).obj (op W) ≃ (W.left ⟶ V) :=
  Equiv.ulift

/-- The restriction `j_U^p(h_V ⟶ h_V^#)` of the sheafification map. -/
noncomputable abbrev forgetToSheafify (V : C) :
    forgetYoneda (U := U) V ⟶
      (Over.forget U).op ⋙ CategoryTheory.sheafify J (CategoryTheory.uliftYoneda.{u}.obj V) :=
  Functor.whiskerLeft (Over.forget U).op
    (CategoryTheory.toSheafify J (CategoryTheory.uliftYoneda.{u}.obj V))

/-- The germ at `(W, e)` of the section `g : W.left ⟶ V` of `j_U^p h_V`. -/
noncomputable def presheafGerm (q : OverPoint Φ U) (V : C) {W : Over U}
    (e : q.point.fiber.obj W) (g : W.left ⟶ V) :
    q.point.presheafFiber.obj (forgetYoneda V) :=
  q.point.toPresheafFiber W e (forgetYoneda V) (forgetYonedaEquiv.symm g)

/-- The map `q⁻¹(j_U^p h_V) ⟶ q⁻¹(j_U⁻¹(h_V^#))` induced by the sheafification map. -/
noncomputable def toSheafFiber (q : OverPoint Φ U) (V : C) :
    q.point.presheafFiber.obj (forgetYoneda V) →
      (J.overPullback (Type max u v) U ⋙ q.point.sheafFiber).obj
        ((Sheaf.sheafifiedYoneda J).obj V) :=
  fun z => q.point.presheafFiber.map (forgetToSheafify (J := J) V) z

lemma toSheafFiber_presheafGerm (q : OverPoint Φ U) {V : C} {W : Over U}
    (e : q.point.fiber.obj W) (g : W.left ⟶ V) :
    q.toSheafFiber V (q.presheafGerm V e g) =
      q.germ _ e (((Sheaf.sheafifiedYoneda J).obj V).obj.map g.op
        (Sheaf.tautologicalSection J V)) := by
  have hg : (forgetToSheafify (J := J) V).app (op W) (forgetYonedaEquiv.symm g) =
      ((Sheaf.sheafifiedYoneda J).obj V).obj.map g.op (Sheaf.tautologicalSection J V) :=
    (Sheaf.sectionEquiv_sheafifiedYoneda_map J g).symm.trans
      ((congrArg (Sheaf.sectionEquiv J) (Category.comp_id _).symm).trans
        (Sheaf.sectionEquiv_map_comp J g _))
  exact (q.point.toPresheafFiber_naturality_apply (forgetToSheafify (J := J) V) W e _).trans
    (congrArg _ hg)

/-- Stacks 00XM on stalks: the map `q⁻¹(j_U^p h_V) ⟶ q⁻¹(j_U⁻¹(h_V^#))` is injective, because
`j_U^p(h_V ⟶ h_V^#)` is locally injective. -/
lemma toSheafFiber_injective (q : OverPoint Φ U) (V : C) :
    Function.Injective (q.toSheafFiber V) := by
  have := Presheaf.isLocallyInjective_whisker (J.over U) J (Over.forget U)
    (CategoryTheory.toSheafify J (CategoryTheory.uliftYoneda.{u}.obj V))
  exact q.point.toPresheafFiber_map_injective (forgetToSheafify (J := J) V)

/-- Stacks 00XM on stalks: the map `q⁻¹(j_U^p h_V) ⟶ q⁻¹(j_U⁻¹(h_V^#))` is surjective, because
`j_U^p(h_V ⟶ h_V^#)` is locally surjective. -/
lemma toSheafFiber_surjective (q : OverPoint Φ U) (V : C) :
    Function.Surjective (q.toSheafFiber V) := by
  have := Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U)
    (CategoryTheory.toSheafify J (CategoryTheory.uliftYoneda.{u}.obj V))
  exact q.point.toPresheafFiber_map_surjective (forgetToSheafify (J := J) V)

/-- The germ at `(W, e)` of a morphism `g : W.left ⟶ V`, carried to `Φ` by `j_U ∘ q = p`, is
the element `u(g)(θ(e))` of `u(V) = p⁻¹(h_V^#)`. -/
lemma iso_hom_app_toSheafFiber_presheafGerm (q : OverPoint Φ U) {V : C} (W : Over U)
    (e : q.point.fiber.obj W) (g : W.left ⟶ V) :
    q.iso.hom.app ((Sheaf.sheafifiedYoneda J).obj V) (q.toSheafFiber V (q.presheafGerm V e g)) =
      (PointOfTopos.fiberToSheafYoneda Φ V).hom (Φ.fiber.map g (q.toFiber W e)) := by
  rw [toSheafFiber_presheafGerm, iso_hom_app_germ, PointOfTopos.fiberToSheafYoneda_hom_apply]
  exact Φ.toPresheafFiber_w_apply g (q.toFiber W e) _ _

/-- The inclusion `h_{V/U} ⟶ j_U^p h_V` of presheaves on `C/U`, `g ↦ g.left`. -/
noncomputable def shrinkYonedaToForget (W : Over U) :
    shrinkYoneda.{max u v}.obj W ⟶ forgetYoneda (U := U) W.left where
  app W' := ↾fun g => forgetYonedaEquiv.symm (shrinkYonedaObjObjEquiv g).left
  naturality W₁ W₂ h := by
    ext g
    apply forgetYonedaEquiv.injective
    change (shrinkYonedaObjObjEquiv ((shrinkYoneda.{max u v}.obj W).map h g)).left =
      h.unop.left ≫ (shrinkYonedaObjObjEquiv g).left
    rw [shrinkYonedaObjObjEquiv_obj_map, Over.comp_left]

lemma shrinkYonedaToForget_app_injective (W : Over U) (W' : (Over U)ᵒᵖ) :
    Function.Injective ((shrinkYonedaToForget W).app W') := fun g₁ g₂ h => by
  apply shrinkYonedaObjObjEquiv.injective
  have h' : (shrinkYonedaObjObjEquiv g₁).left = (shrinkYonedaObjObjEquiv g₂).left :=
    congrArg forgetYonedaEquiv h
  exact Over.OverMorphism.ext h'

lemma presheafGerm_id_eq (q : OverPoint Φ U) (W : Over U) (e : q.point.fiber.obj W) :
    q.presheafGerm W.left e (𝟙 W.left) =
      q.point.presheafFiber.map (shrinkYonedaToForget W)
        (q.point.shrinkYonedaCompPresheafFiberIso.inv.app W e) := by
  have hm : (shrinkYonedaToForget W).app (op W) (shrinkYonedaObjObjEquiv.symm (𝟙 W)) =
      forgetYonedaEquiv.symm (𝟙 W.left) := by
    change forgetYonedaEquiv.symm (shrinkYonedaObjObjEquiv (shrinkYonedaObjObjEquiv.symm
      (𝟙 W))).left = _
    rw [Equiv.apply_symm_apply]
    rfl
  rw [shrinkYonedaCompPresheafFiberIso_inv_app_toPresheafFiber,
    toPresheafFiber_naturality_apply, hm]
  rfl

/-- `θ : v(V/U) → u(V)` is injective. -/
lemma toFiber_injective (q : OverPoint Φ U) (W : Over U) : Function.Injective (q.toFiber W) := by
  intro e₁ e₂ h
  have h₃ : q.presheafGerm W.left e₁ (𝟙 W.left) = q.presheafGerm W.left e₂ (𝟙 W.left) := by
    apply q.toSheafFiber_injective W.left
    apply q.iso_hom_app_injective
    rw [q.iso_hom_app_toSheafFiber_presheafGerm, q.iso_hom_app_toSheafFiber_presheafGerm, h]
  rw [q.presheafGerm_id_eq W e₁, q.presheafGerm_id_eq W e₂] at h₃
  have := Presheaf.isLocallyInjective_of_injective (J.over U) (shrinkYonedaToForget W)
    (shrinkYonedaToForget_app_injective W)
  exact (mono_iff_injective (q.point.shrinkYonedaCompPresheafFiberIso.inv.app W)).1 inferInstance
    (q.point.toPresheafFiber_map_injective (shrinkYonedaToForget W) h₃)

/-- `θ` maps `v(V/U)` onto the elements of `u(V)` lying over `x = baseElement q`.  This is where
Stacks' cartesian square `v(V/U) = u(V) ×_{u(U)} v(U/U)` is used, in the following form: an
element `y ∈ u(V)` over `x` comes from the germ of a map `t : V' ⟶ V` at a neighbourhood
`(V'/U, e')` of `q`; the germs of `t ≫ φ` and of the structure map `V' ⟶ U` agree, since both are
carried to `x` by `j_U ∘ q = p`; so `t` is a morphism over `U` on a smaller neighbourhood. -/
lemma exists_toFiber_eq (q : OverPoint Φ U) (W : Over U) (y : Φ.fiber.obj W.left)
    (hy : Φ.fiber.map W.hom y = q.baseElement) : ∃ e, q.toFiber W e = y := by
  obtain ⟨z, hz⟩ := q.toSheafFiber_surjective W.left
    (q.iso.inv.app ((Sheaf.sheafifiedYoneda J).obj W.left)
      ((PointOfTopos.fiberToSheafYoneda Φ W.left).hom y))
  obtain ⟨W', e', t, rfl⟩ :=
    q.point.toPresheafFiber_jointly_surjective (P := forgetYoneda W.left) z
  obtain ⟨t, rfl⟩ := forgetYonedaEquiv.symm.surjective t
  change q.toSheafFiber W.left (q.presheafGerm W.left e' t) = _ at hz
  have ht : Φ.fiber.map t (q.toFiber W' e') = y := by
    apply toFiber_injective_aux
    rw [← q.iso_hom_app_toSheafFiber_presheafGerm W' e' t, hz, iso_hom_app_iso_inv_app]
  have hgerm : q.presheafGerm U e' (t ≫ W.hom) = q.presheafGerm U e' W'.hom := by
    apply q.toSheafFiber_injective U
    apply q.iso_hom_app_injective
    rw [q.iso_hom_app_toSheafFiber_presheafGerm, q.iso_hom_app_toSheafFiber_presheafGerm,
      Functor.map_comp, CategoryTheory.comp_apply, ht, hy, map_hom_toFiber]
  unfold presheafGerm at hgerm
  obtain ⟨W'', f, e'', hf, hfg⟩ := (q.point.toPresheafFiber_eq_iff' W' e' _ _).1 hgerm
  have h : f.left ≫ t ≫ W.hom = f.left ≫ W'.hom := congrArg forgetYonedaEquiv hfg
  have hk : (f.left ≫ t) ≫ W.hom = W''.hom := by rw [Category.assoc, h, Over.w f]
  refine ⟨q.point.fiber.map (Over.homMk (f.left ≫ t) hk : W'' ⟶ W) e'', ?_⟩
  rw [toFiber_naturality]
  change Φ.fiber.map (f.left ≫ t) (q.toFiber W'' e'') = y
  rw [Functor.map_comp, CategoryTheory.comp_apply, ← toFiber_naturality, hf, ht]

/-- The isomorphism `v ≅ v_x` of Stacks 04H3 between the fibre functor of a point `q` of `C/U`
lying over `Φ` and the fibre functor of `q_x`, `x = baseElement q`: on `V/U` it is `θ`, a
bijection from `v(V/U)` onto `{y ∈ u(V) | y ↦ x}`. -/
noncomputable def fiberIso (q : OverPoint Φ U) :
    q.point.fiber ≅ (Φ.over q.baseElement).fiber :=
  NatIso.ofComponents
    (fun W => (Equiv.ofBijective
      (fun e => (⟨q.toFiber W e, (FunctorToTypes.mem_fromOverSubfunctor_iff _ _ _).2
        (q.map_hom_toFiber W e)⟩ : (Φ.over q.baseElement).fiber.obj W))
      ⟨fun e₁ e₂ h => q.toFiber_injective W (congrArg Subtype.val h), fun y => by
        obtain ⟨e, he⟩ := q.exists_toFiber_eq W y.1
          ((FunctorToTypes.mem_fromOverSubfunctor_iff _ _ _).1 y.2)
        exact ⟨e, Subtype.ext he⟩⟩).toIso)
    (fun g => by
      ext e
      exact Subtype.ext (q.toFiber_naturality g e))

lemma fiberIso_hom_app_val (q : OverPoint Φ U) (W : Over U) (e : q.point.fiber.obj W) :
    ((q.fiberIso.hom.app W) e).val = q.toFiber W e :=
  rfl

lemma toFiber_fiberIso_inv_app (q : OverPoint Φ U) (W : Over U)
    (e : (Φ.over q.baseElement).fiber.obj W) :
    q.toFiber W (q.fiberIso.inv.app W e) = e.val := by
  have h := ConcreteCategory.congr_hom (q.fiberIso.inv_hom_id_app W) e
  rw [CategoryTheory.comp_apply, CategoryTheory.id_apply] at h
  rw [← fiberIso_hom_app_val, h]

/-- A morphism of points of `C/U` sends the germ at `(W, e)` to the germ at `(W, f(e))`. -/
lemma sheafFiber_app_germ {q₁ q₂ : OverPoint Φ U} (f : q₁.point ⟶ q₂.point)
    (F : Sheaf J (Type max u v)) {W : Over U} (e : q₂.point.fiber.obj W)
    (s : F.obj.obj (op W.left)) :
    (Functor.whiskerLeft (J.overPullback (Type max u v) U)
        (Point.Hom.sheafFiber (A := Type max u v) f)).app F (q₂.germ F e s) =
      q₁.germ F (f.hom.app W e) s :=
  ConcreteCategory.congr_hom (q₂.point.toPresheafFiber_presheafFiberDesc
    (fun X x => q₁.point.toPresheafFiber X (f.hom.app X x)
      ((J.overPullback (Type max u v) U).obj F).obj) _ W e) s

/-- The identification `j_U ∘ q_x = p` of Stacks 04H2 on germs. -/
lemma ofFiber_iso_hom_app_germ (x : Φ.fiber.obj U) (F : Sheaf J (Type max u v))
    {W : Over U} (e : (Φ.over x).fiber.obj W) (s : F.obj.obj (op W.left)) :
    (ofFiber x).iso.hom.app F ((ofFiber x).germ F e s) =
      Φ.toPresheafFiber W.left e.val F.obj s :=
  ConcreteCategory.congr_hom (Functor.Final.ι_colimitIso_hom (overElements Φ x).op
    ((Functor.Elements.π Φ.fiber).op ⋙ F.obj) (op ((Φ.over x).fiber.elementsMk W e))) s

/-- **Stacks 04H3**, existence: a point `q` of `C/U` lying over `Φ` is isomorphic, compatibly
with the identifications `j_U ∘ q = p` and `j_U ∘ q_x = p`, to the point `q_x` of Stacks 04H2
for `x = baseElement q`. -/
noncomputable def isoOfFiber (q : OverPoint Φ U) : q ≅ ofFiber q.baseElement :=
  isoMk
    { hom := ⟨q.fiberIso.inv⟩
      inv := ⟨q.fiberIso.hom⟩
      hom_inv_id := Point.hom_ext q.fiberIso.hom_inv_id
      inv_hom_id := Point.hom_ext q.fiberIso.inv_hom_id }
    (by
      ext F : 2
      refine (Φ.over q.baseElement).presheafFiber_hom_ext (fun W e => ?_)
      ext s
      exact (congrArg (q.iso.hom.app F) (sheafFiber_app_germ (q₁ := q)
          (q₂ := ofFiber q.baseElement) ⟨q.fiberIso.inv⟩ F e s)).trans
        ((q.iso_hom_app_germ F (q.fiberIso.inv.app W e) s).trans
          ((congrArg (fun y => Φ.toPresheafFiber W.left y F.obj s)
            (q.toFiber_fiberIso_inv_app W e)).trans
            (ofFiber_iso_hom_app_germ q.baseElement F e s).symm)))

/-- The element `x` attached to `q` depends only on `q` up to morphisms of points over `Φ`. -/
lemma baseElement_eq_of_hom {q₁ q₂ : OverPoint Φ U} (f : q₁ ⟶ q₂) :
    q₁.baseElement = q₂.baseElement := by
  have h : q₂.iso.hom.app ((Sheaf.sheafifiedYoneda J).obj U)
        (q₂.germ _ q₂.finalElement (Sheaf.tautologicalSection J U)) =
      q₁.iso.hom.app ((Sheaf.sheafifiedYoneda J).obj U)
        (q₁.germ _ q₁.finalElement (Sheaf.tautologicalSection J U)) := by
    rw [← Hom.comm f, NatTrans.comp_app, CategoryTheory.comp_apply, sheafFiber_app_germ,
      ← q₁.eq_finalElement ((Hom.hom f).hom.app (Over.mk (𝟙 U)) q₂.finalElement)]
  have h₁ := fiberToSheafYoneda_hom_toFiber q₁ (Over.mk (𝟙 U)) q₁.finalElement
  have h₂ := fiberToSheafYoneda_hom_toFiber q₂ (Over.mk (𝟙 U)) q₂.finalElement
  exact toFiber_injective_aux (h₁.trans (h.symm.trans h₂.symm))

/-- `θ` for the point `q_x` of Stacks 04H2 is the inclusion `v_x(V/U) ⊆ u(V)`. -/
lemma ofFiber_toFiber (x : Φ.fiber.obj U) (W : Over U) (e : (Φ.over x).fiber.obj W) :
    (ofFiber x).toFiber W e = e.val := by
  apply toFiber_injective_aux
  rw [fiberToSheafYoneda_hom_toFiber, ofFiber_iso_hom_app_germ,
    PointOfTopos.fiberToSheafYoneda_hom_apply]

/-- **Stacks 04H3**, injectivity: the element attached to `q_x` is `x`. -/
lemma baseElement_ofFiber (x : Φ.fiber.obj U) : (ofFiber x).baseElement = x := by
  rw [baseElement, ofFiber_toFiber]
  simpa using ((FunctorToTypes.mem_fromOverSubfunctor_iff _ _ _).1
    ((ofFiber x).finalElement).2)

/-- **Stacks 04H3.** Let `p` be a point of the site `C` with fibre functor `u`, and `U` an object
of `C`.  Every point `q` of `C/U` lying over `p` (a point of `C/U` with an identification
`j_U ∘ q = p`) is isomorphic over `p` to the point `q_x` of Stacks 04H2 for exactly one
`x ∈ u(U)`. -/
@[stacks 04H3]
theorem existsUnique_nonempty_iso_ofFiber (q : OverPoint Φ U) :
    ∃! x : Φ.fiber.obj U, Nonempty (q ≅ ofFiber x) :=
  ⟨q.baseElement, ⟨q.isoOfFiber⟩, fun x ⟨e⟩ =>
    ((baseElement_eq_of_hom e.hom).trans (baseElement_ofFiber x)).symm⟩

/-- **Stacks 04H3.** Let `p` be a point of the site `C` with fibre functor `u`, and `U` an object
of `C`.  The construction `x ↦ q_x` of Stacks 04H2 is a one to one correspondence between the
elements `x ∈ u(U)` and the points `q` of `C/U` lying over `p`, up to isomorphism of points over
`p`. -/
@[stacks 04H3]
noncomputable def fiberEquivOverPoint :
    Φ.fiber.obj U ≃ _root_.Quotient (isIsomorphicSetoid (OverPoint Φ U)) where
  toFun x := _root_.Quotient.mk _ (ofFiber x)
  invFun := _root_.Quotient.lift baseElement fun _ _ ⟨e⟩ => baseElement_eq_of_hom e.hom
  left_inv x := baseElement_ofFiber x
  right_inv := _root_.Quotient.ind fun q => _root_.Quotient.sound ⟨q.isoOfFiber.symm⟩

lemma fiberEquivOverPoint_apply (x : Φ.fiber.obj U) :
    fiberEquivOverPoint x = _root_.Quotient.mk (isIsomorphicSetoid _) (ofFiber (Φ := Φ) x) :=
  rfl

/-- The inverse of the correspondence of Stacks 04H3 sends the class of a point `q` of `C/U` lying
over `Φ` to the element `x = baseElement q` of `u(U)` with `q ≅ q_x`. -/
lemma fiberEquivOverPoint_symm_mk (q : OverPoint Φ U) :
    fiberEquivOverPoint.symm (_root_.Quotient.mk (isIsomorphicSetoid _) q) = q.baseElement :=
  rfl

end OverPoint

end CategoryTheory.GrothendieckTopology.Point
