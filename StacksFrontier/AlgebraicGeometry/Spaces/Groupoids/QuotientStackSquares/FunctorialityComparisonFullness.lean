module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FunctorialitySourceCartesianPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.PresentedFibreArrows

/-!
# Fullness of the comparison 1-morphism of Stacks 04ZN

Let `φ : (U, R, s, t, c) ⟶ (U', R', s', t', c')` be a morphism of groupoids in algebraic spaces
over an algebraic space `B` over a scheme `S` of a big fppf site, and assume the **source square**

```
R ---f---> R'
|          |
s          s'
v          v
U ---f---> U'
```

is cartesian, which is the hypothesis of Stacks 04ZN. This file proves that the comparison
1-morphism `c : 𝒮_U ⟶ [U/R] ×_{[U'/R']} 𝒮_{U'}` of
`AlgebraicGeometry.Stack.functorialityComparison` is then **full**. Together with
`AlgebraicGeometry.Stack.functorialityComparison_faithful`, which needs no hypothesis, this is one
of the two halves into which `AlgebraicGeometry.Stack.isTwoFibreProduct_functorialitySquare`
splits Stacks 04ZN; the other half is local essential surjectivity on fibres.

## Main results

* `AlgebraicGeometry.Stack.functorialityComparison_full`: **the comparison 1-morphism of
  Stacks 04ZN is full as soon as the source square of `φ` is cartesian.**
* `AlgebraicGeometry.Stack.pointwiseObjectInclusion_map_eq_ι`: a vertical morphism between two
  presented points of the object space is carried by the inclusion of the object points of
  Stacks 044R to the image under the fibre inclusion of an `eqToHom`; in particular the two points
  are equal. This is the shape in which the `𝒮_{U'}`-leg of the square contributes an *identity*
  arrow of `R'`.
* `AlgebraicGeometry.Stack.quotientPointwiseMap_map_ι`: the map of pointwise groupoid fibrations
  of Stacks 046Q commutes with the fibre inclusions, its effect on an arrow of the evaluated
  groupoid `G(T)` being the evaluated functor of `φ`.
* `CategoryTheory.Pseudofunctor.CoGrothendieck.map_ι`,
  `CategoryTheory.Pseudofunctor.CoGrothendieck.ι_faithful`,
  `CategoryTheory.Pseudofunctor.CoGrothendieck.hom_ext_heq` and
  `CategoryTheory.Pseudofunctor.CoGrothendieck.isHomLift_of_base_eq_id`: the four facts about the
  fibre inclusion `F(T) ⥤ ∫ᶜ F` of a contravariant pseudofunctor that the proof needs.
* `CategoryTheory.Functor.toPseudofunctor'_mapId_inv_app` and its companions: the unity
  constraint of the pseudofunctor attached to an honest functor into `Cat` is an `eqToHom` on
  every component.
* `AlgebraicGeometry.Stack.map_eq_eqToHom_of_isHomLift`: the structure map of a morphism lying
  over an identity is that identity.

## Implementation notes

*The argument.* Fullness is checked fibrewise, by Stacks 003Z (1) in the form
`CategoryTheory.Functor.IsFiberedInGroupoids.full_and_faithful_iff_forall_fiber`; faithfulness on
each fibre is free, since `c` is faithful and the fibre inclusions are. On the fibre over a test
object `T` a morphism `Φ : c(u₁) ⟶ c(u₂)` between the images of two points of `U` has a
`[U/R]`-component which, by Stacks 044X (2) in the form
`AlgebraicGeometry.Stack.exists_evaluationArrow`, is the image of an arrow `r` of the evaluated
groupoid `G(T)`, i.e. of a `T`-point of `R` with source `u₁` and target `u₂`. The commuting square
of `Φ`, transported to the pointwise presentation of `[U'/R']` by
`AlgebraicGeometry.Stack.squarePointwise` and made an equation of `T`-points of `R'` by
`AlgebraicGeometry.Stack.pointwiseToQuotientStack_map_inj`, says that `f(r)` is the identity arrow
at `f(u₁)` — the `𝒮_{U'}`-component of `Φ` contributes an identity because the fibres of the
object-space fibration are discrete. The cartesian source square then forces `r` itself to be an
identity arrow
(`AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.eq_identityArrow_of_isPullback_source`) and
`u₁ = u₂`
(`AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.target_eq_source_of_isPullback_source`), so
`Φ` is the identity and is the image of the identity.

*Why the generic helpers.* Both sides of the transported square are read off through the fibre
inclusion `CategoryTheory.Pseudofunctor.CoGrothendieck.ι`, whose action on an arrow has the arrow
itself in a **dependent index**: the `fiber` component of a morphism of a `CoGrothendieck`
category lives in a type indexed by its `base` component. Consequently `rw` and `simp only` fail
on any of these goals — `Lean.Meta.kabstract` declines to abstract over a goal that is not
type-correct at `implicit` transparency, which these are not. Every step is therefore a lemma
stated over **plain variables** and then instantiated with `exact`, which checks definitional
equality at the default transparency level; nothing is restated inline over the concrete terms.
The same device replaces the `CoGrothendieck.Hom.ext` of Mathlib, whose `eqToHom` witness is not
type-correct at that transparency either, by
`CategoryTheory.Pseudofunctor.CoGrothendieck.hom_ext_heq`, which takes a heterogeneous equality of
the `fiber` components and so mentions no `eqToHom` at all.

*The point constructor.* `AlgebraicGeometry.Stack.liftedFibredCategory` is a
`CategoryTheory.ULiftHom`, hence *definitionally* the un-enlarged fibred category, so writing a
point of it as a pair `⟨T, u⟩` makes the elaborator choose the un-enlarged `Category` instance and
the morphisms come out one universe too low. `AlgebraicGeometry.Stack.enlargedPoint` names the pair
at the enlarged type, which is what makes the hom-types come out right.

## References

* [Stacks Project, Tag 003Z](https://stacks.math.columbia.edu/tag/003Z)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 044V](https://stacks.math.columbia.edu/tag/044V)
* [Stacks Project, Tag 044X](https://stacks.math.columbia.edu/tag/044X)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
* [Stacks Project, Tag 04ZN](https://stacks.math.columbia.edu/tag/04ZN)
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Pseudofunctor Bicategory
open scoped CategoryTheory.Pseudofunctor.StrongTrans

namespace CategoryTheory.Pseudofunctor.CoGrothendieck

universe v₁ v₂ u₁ u₂

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {F F' : LocallyDiscrete 𝒮ᵒᵖ ⥤ᵖ Cat.{v₂, u₂}}

/-- **Two parallel morphisms of a `CoGrothendieck` category agree as soon as their `base`
components are equal and their `fiber` components are heterogeneously equal.**

This is `CategoryTheory.Pseudofunctor.CoGrothendieck.Hom.ext` with the transport of the `fiber`
component along the equality of the `base` components replaced by a heterogeneous equality. The
`eqToHom` that `Hom.ext` carries is not type-correct at `implicit` transparency for the
pseudofunctors of this development, so goals produced by it are inaccessible to `rw` and
`simp only`; this version mentions no `eqToHom`. -/
theorem hom_ext_heq {a b : CoGrothendieck F} (f g : a ⟶ b) (hbase : f.base = g.base)
    (hfiber : HEq f.fiber g.fiber) : f = g := by
  obtain ⟨fb, ff⟩ := f
  obtain ⟨gb, gf⟩ := g
  cases hbase
  cases hfiber
  rfl

/-- **A morphism of a `CoGrothendieck` category between two objects over a test object `T` whose
`base` component is the identity of `T` is vertical over `T`.** -/
theorem isHomLift_of_base_eq_id (T : 𝒮) {x y : F.obj ⟨op T⟩}
    (f : (⟨T, x⟩ : CoGrothendieck F) ⟶ ⟨T, y⟩) (h : f.base = 𝟙 T) :
    (CoGrothendieck.forget F).IsHomLift (𝟙 T) f := by
  have hm := IsHomLift.map (CoGrothendieck.forget F) f
  rwa [show (CoGrothendieck.forget F).map f = f.base from rfl, h] at hm

/-- **The functor induced by a strong transformation of pseudofunctors commutes with the fibre
inclusions**: the square

```
F(T) ----ι----> ∫ᶜ F
 |               |
α_T            map α
 v               v
F'(T) ---ι----> ∫ᶜ F'
```

commutes on morphisms. On the `fiber` components this is the unity coherence
`CategoryTheory.Pseudofunctor.StrongTrans.naturality_id_hom_app` of the strong transformation. -/
theorem map_ι (α : F ⟶ F') (T : 𝒮) {a b : F.obj ⟨op T⟩} (arr : a ⟶ b) :
    (CoGrothendieck.map α).map ((CoGrothendieck.ι F T).map arr) =
      (CoGrothendieck.ι F' T).map ((α.app ⟨op T⟩).toFunctor.map arr) := by
  refine hom_ext_heq _ _ rfl (heq_of_eq ?_)
  change (α.app ⟨op T⟩).toFunctor.map (arr ≫ (F.mapId ⟨op T⟩).inv.toNatTrans.app b) ≫
      (α.naturality (𝟙 (⟨op T⟩ : LocallyDiscrete 𝒮ᵒᵖ))).hom.toNatTrans.app b =
    (α.app ⟨op T⟩).toFunctor.map arr ≫
      (F'.mapId ⟨op T⟩).inv.toNatTrans.app ((α.app ⟨op T⟩).toFunctor.obj b)
  rw [StrongTrans.naturality_id_hom_app, Functor.map_comp, Category.assoc,
    ← Category.assoc ((α.app ⟨op T⟩).toFunctor.map ((F.mapId ⟨op T⟩).inv.toNatTrans.app b)),
    ← Functor.map_comp, ← Cat.Hom₂.comp_app, Iso.inv_hom_id]
  simp

/-- **The fibre inclusion of a contravariant pseudofunctor is faithful.** It factors as the
equivalence onto the fibre of the projection followed by the inclusion of that fibre, and both are
faithful. -/
theorem ι_faithful (T : 𝒮) : (CoGrothendieck.ι F T).Faithful := by
  have h : (Functor.Fiber.inducedFunctor (CoGrothendieck.comp_const F T) ⋙
      Functor.Fiber.fiberInclusion).Faithful := Functor.Faithful.comp _ _
  exact h

end CategoryTheory.Pseudofunctor.CoGrothendieck

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

/-- The pseudofunctor attached to an honest functor into `Cat` is strictly unital. -/
theorem toPseudofunctor'_map_id {I : Type u₁} [Category.{v₁} I] (K : I ⥤ Cat.{v₂, u₂})
    (x : LocallyDiscrete I) :
    K.toPseudofunctor'.map (𝟙 x) = 𝟙 (K.toPseudofunctor'.obj x) :=
  K.map_id x.as

/-- The unity constraint of the pseudofunctor attached to an honest functor into `Cat` is the
`eqToHom` of `CategoryTheory.Functor.toPseudofunctor'_map_id`. -/
theorem toPseudofunctor'_mapId_inv {I : Type u₁} [Category.{v₁} I] (K : I ⥤ Cat.{v₂, u₂})
    (x : LocallyDiscrete I)
    (h : K.toPseudofunctor'.map (𝟙 x) = 𝟙 (K.toPseudofunctor'.obj x)) :
    (K.toPseudofunctor'.mapId x).inv = eqToHom h.symm := by
  rw [Functor.toPseudofunctor'_mapId]
  rfl

/-- Every component of the unity constraint of the pseudofunctor attached to an honest functor
into `Cat` is an `eqToHom`. -/
theorem toPseudofunctor'_mapId_inv_app {I : Type u₁} [Category.{v₁} I] (K : I ⥤ Cat.{v₂, u₂})
    (x : LocallyDiscrete I) (y : K.toPseudofunctor'.obj x) :
    (K.toPseudofunctor'.mapId x).inv.toNatTrans.app y =
      eqToHom (Functor.congr_obj
        (congrArg (fun k => Cat.Hom.toFunctor k) (toPseudofunctor'_map_id K x).symm) y) := by
  rw [toPseudofunctor'_mapId_inv K x (toPseudofunctor'_map_id K x), Cat.eqToHom_app]

/-- The pseudofunctor attached to an honest functor into `Cat` fixes every object of every fibre
along an identity of the base. -/
theorem toPseudofunctor'_map_id_obj {I : Type u₁} [Category.{v₁} I] (K : I ⥤ Cat.{v₂, u₂})
    (x : LocallyDiscrete I) (y : K.toPseudofunctor'.obj x) :
    (K.toPseudofunctor'.map (𝟙 x)).toFunctor.obj y = y :=
  Functor.congr_obj
    (congrArg (fun k => Cat.Hom.toFunctor k) (toPseudofunctor'_map_id K x)) y

/-- An `eqToHom` into the value of the pseudofunctor attached to an honest functor into `Cat` at
an identity of the base factors through the unity constraint. This is the step that identifies the
`fiber` component of the image of a vertical morphism of a discrete fibration with the `fiber`
component of the image of an `eqToHom` under the fibre inclusion. -/
theorem eqToHom_eq_comp_mapId_inv {I : Type u₁} [Category.{v₁} I] (K : I ⥤ Cat.{v₂, u₂})
    (x : LocallyDiscrete I) {a b : K.toPseudofunctor'.obj x} (h₁ : a = b)
    (h₂ : a = (K.toPseudofunctor'.map (𝟙 x)).toFunctor.obj b) :
    eqToHom h₂ = eqToHom h₁ ≫ (K.toPseudofunctor'.mapId x).inv.toNatTrans.app b := by
  rw [toPseudofunctor'_mapId_inv_app, eqToHom_trans]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Stack

universe u

open AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} {G G' : GroupoidInAlgebraicSpaces C S hS B}

/-! ### The two legs of the square on the pointwise presentation -/

/-- **A vertical morphism of the fibred category of the object space between two presented points
identifies the two points, and the inclusion of the object points of Stacks 044R carries it to
the image under the fibre inclusion of the corresponding `eqToHom`.**

The fibres of the object-space fibration are discrete, so a vertical morphism between the points
`v₁` and `v₂` of `U` over a test object `T` is an equality `v₁ = v₂`; this records what the
inclusion into the pointwise groupoid fibration of Stacks 044Q does with it. In the proof of
Stacks 04ZN this is the `𝒮_{U'}`-leg of the square: it makes the `R'`-point coming from that leg
an identity arrow. -/
theorem pointwiseObjectInclusion_map_eq_ι
    (G : GroupoidInAlgebraicSpaces C S hS B) (T : BigFppfOver C S hS)
    {v₁ v₂ : G.objects.obj.obj (op T)}
    (g : (⟨T, Discrete.mk v₁⟩ : (fibredCategory C S hS G.objects.obj).based.obj) ⟶
      ⟨T, Discrete.mk v₂⟩) (hg : g.base = 𝟙 T) :
    ∃ h : v₁ = v₂,
      (pointwiseObjectInclusion G).map g =
        (CoGrothendieck.ι (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
          Grpd.forgetToCat).toPseudofunctor' T).map (eqToHom h) := by
  obtain ⟨gb, gf⟩ := g
  cases hg
  refine ⟨(Discrete.eq_of_hom gf).trans (Functor.toPseudofunctor'_map_id_obj
    (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙ Grpd.forgetToCat) ⟨op T⟩ v₂), ?_⟩
  refine CoGrothendieck.hom_ext_heq _ _ rfl (heq_of_eq ?_)
  exact Functor.eqToHom_eq_comp_mapId_inv
    (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙ Grpd.forgetToCat) ⟨op T⟩ _
    (Discrete.eq_of_hom gf)

/-- **Stacks 046Q on the arrows of an evaluated groupoid**: the map of pointwise groupoid
fibrations induced by a morphism of groupoids in algebraic spaces commutes with the fibre
inclusions, and on an arrow of `G(T)` it is the evaluated functor of `φ` at `T`. This is the
`[U/R]`-leg of the square of Stacks 04ZN read on the presentation. -/
theorem quotientPointwiseMap_map_ι (φ : Hom G G') (T : BigFppfOver C S hS)
    {u₁ u₂ : G.toGroupoidInFunctors.Evaluation (op T)}
    (arr : u₁ ⟶ u₂) :
    (quotientPointwiseMap φ).map ((CoGrothendieck.ι
        (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
          Grpd.forgetToCat).toPseudofunctor' T).map arr) =
      (CoGrothendieck.ι (evaluationGroupoidFunctor G'.toGroupoidInFunctors ⋙
        Grpd.forgetToCat).toPseudofunctor' T).map
        ((φ.toGroupoidHom.evaluation (op T)).map arr) :=
  CoGrothendieck.map_ι (quotientPointwiseMapData φ).val T arr

/-! ### Points of the enlarged object-space fibration -/

/-- A point of the object space, as an object of the universe-enlarged fibred category. -/
def enlargedPoint (G : GroupoidInAlgebraicSpaces C S hS B) (T : BigFppfOver C S hS)
    (u : G.objects.obj.obj (op T)) : (liftedFibredCategory G.objects).obj :=
  ⟨T, Discrete.mk u⟩

/-! ### Fullness -/

/-- **The structure map of a morphism lying over an identity is that identity**, stated over
plain variables, since `CategoryTheory.IsHomLift.fac'` carries the morphism of the site in the
instance argument as well as in the conclusion, so rewriting the conclusion alone leaves an
ill-typed motive. -/
theorem map_eq_eqToHom_of_isHomLift {𝒞 : Type*} [Category* 𝒞] {𝒳 : Type*} [Category* 𝒳]
    (p : 𝒳 ⥤ 𝒞) {T : 𝒞} {a b : 𝒳} (f : a ⟶ b) (g : T ⟶ T) (hg : p.IsHomLift g f)
    (hgid : g = 𝟙 T) (ha : p.obj a = T) (hbb : p.obj b = T) :
    p.map f = eqToHom (ha.trans hbb.symm) := by
  subst hgid
  have := hg
  rw [IsHomLift.fac' p (𝟙 T) f]
  simp

/-- **The vertical half of fullness**: a vertical morphism of the 2-fibre product between the
images of two points of the object space over a test object is the identity, and in particular is
in the image of the comparison 1-morphism. This is where the cartesian source square is used. -/
private theorem exists_hom_of_hbase_eq_id (φ : Hom G G')
    (hφ : IsPullback φ.toGroupoidHom.mapArrows G.source.hom G'.source.hom
      φ.toGroupoidHom.mapObjects)
    (T : BigFppfOver C S hS) (u₁ u₂ : G.objects.obj.obj (op T))
    (Φ : (functorialityComparison φ).obj (enlargedPoint G T u₁) ⟶
      (functorialityComparison φ).obj (enlargedPoint G T u₂))
    (hb : Φ.hbase = 𝟙 T) :
    ∃ χ : enlargedPoint G T u₁ ⟶ enlargedPoint G T u₂,
      (functorialityComparison φ).map χ = Φ := by
  have hΦa : (quotientStack G).p.IsHomLift (𝟙 T) Φ.a := by
    rw [← hb]; exact Φ.ha
  obtain ⟨arr, harr⟩ := exists_evaluationArrow G T u₁ u₂ Φ.a hΦa
  have hbbase : (liftedFibredCategory G'.objects).p.map Φ.b = 𝟙 T :=
    (map_eq_eqToHom_of_isHomLift (liftedFibredCategory G'.objects).p Φ.b Φ.hbase Φ.hb hb rfl
      rfl).trans (eqToHom_refl T _)
  have hsq := squarePointwise φ Φ _ harr
  have hsq' : (pointwiseToQuotientStack G').map ((quotientPointwiseMap φ).map
        ((CoGrothendieck.ι (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
          Grpd.forgetToCat).toPseudofunctor' T).map arr)) =
      (pointwiseToQuotientStack G').map ((pointwiseObjectInclusion G').map Φ.b.down) := hsq
  have h₁ := CoGrothendieck.isHomLift_of_base_eq_id T
    ((quotientPointwiseMap φ).map
      ((CoGrothendieck.ι (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
        Grpd.forgetToCat).toPseudofunctor' T).map arr)) rfl
  have h₂ := CoGrothendieck.isHomLift_of_base_eq_id T
    ((pointwiseObjectInclusion G').map Φ.b.down) hbbase
  have heq := pointwiseToQuotientStack_map_inj G' T _ _ h₁ h₂ hsq'
  obtain ⟨hv, hbe⟩ := pointwiseObjectInclusion_map_eq_ι G' T Φ.b.down hbbase
  have hmid : (CoGrothendieck.ι (evaluationGroupoidFunctor G'.toGroupoidInFunctors ⋙
        Grpd.forgetToCat).toPseudofunctor' T).map
        ((φ.toGroupoidHom.evaluation (op T)).map arr) =
      (CoGrothendieck.ι (evaluationGroupoidFunctor G'.toGroupoidInFunctors ⋙
        Grpd.forgetToCat).toPseudofunctor' T).map (eqToHom hv) :=
    (quotientPointwiseMap_map_ι φ T arr).symm.trans (heq.trans hbe)
  have := CoGrothendieck.ι_faithful
    (F := (evaluationGroupoidFunctor G'.toGroupoidInFunctors ⋙
      Grpd.forgetToCat).toPseudofunctor') T
  have harr2 := Functor.Faithful.map_injective hmid
  have hev := Deformation.GroupoidInFunctors.Hom.evaluation_map_arrow φ.toGroupoidHom (op T) arr
  have hid := evaluationArrow_eqToHom_identity G'.toGroupoidInFunctors (op T) hv
  set e := G.toGroupoidInFunctors.evaluationArrowEquiv (op T) u₁ u₂ arr with he
  have hs := e.2.1
  have ht := e.2.2
  have hyp : φ.toGroupoidHom.mapArrows.app (op T) e.1 =
      (identityArrow G').hom.app (op T)
        (φ.toGroupoidHom.mapObjects.app (op T) (G.source.hom.app (op T) e.1)) :=
    (hev.symm.trans ((congrArg (fun k => ((G'.toGroupoidInFunctors.evaluationArrowEquiv (op T)
      (φ.toGroupoidHom.mapObjects.app (op T) u₁)
      (φ.toGroupoidHom.mapObjects.app (op T) u₂)) k).1) harr2).trans hid)).trans
      ((congrArg (fun y => G'.toGroupoidInFunctors.identity (op T)
        (φ.toGroupoidHom.mapObjects.app (op T) y)) hs.symm).trans
      (identityArrow_hom_app G' (op T) _).symm)
  have hu : u₂ = u₁ :=
    ht.symm.trans ((Hom.target_eq_source_of_isPullback_source φ hφ _ hyp).trans hs)
  subst hu
  have hrid := (Hom.eq_identityArrow_of_isPullback_source φ hφ _ hyp).trans
    ((identityArrow_hom_app G (op T) _).trans
      (congrArg (G.toGroupoidInFunctors.identity (op T)) hs))
  have harrid : arr = 𝟙 _ :=
    (G.toGroupoidInFunctors.evaluationArrowEquiv (op T) u₂ u₂).injective
      (Subtype.ext (hrid.trans (Deformation.GroupoidInFunctors.evaluationArrowEquiv_id
        G.toGroupoidInFunctors (op T) u₂).symm))
  have hΦa' : Φ.a = 𝟙 _ := by
    rw [← harr, harrid]
    exact (congrArg (fun k => (pointwiseToQuotientStack G).map k)
      (CategoryTheory.Functor.map_id _ _)).trans (CategoryTheory.Functor.map_id _ _)
  have hΦb' : Φ.b = 𝟙 _ :=
    ULift.ext (Pseudofunctor.CoGrothendieck.Hom.ext _ _ hbbase Discrete.hom_eq)
  exact ⟨𝟙 _, (CategoryTheory.Functor.map_id (functorialityComparison φ) _).trans
    (TwoFibreProductOver.Hom.ext' hΦa'.symm hΦb'.symm)⟩

/-- **Stacks 003Z (1) for fullness of the comparison 1-morphism, on one fibre.** -/
private theorem full_fiber_functorialityComparison (φ : Hom G G')
    (hφ : IsPullback φ.toGroupoidHom.mapArrows G.source.hom G'.source.hom
      φ.toGroupoidHom.mapObjects)
    (T : BigFppfOver C S hS) :
    (Functor.Fiber.mapOfComp (liftedFibredCategory G.objects).p
      (functorialityTwoFibreProduct φ) (functorialityComparison φ)
      (functorialityComparison_comp φ) T).Full := by
  constructor
  intro W₁ W₂ Ψ
  obtain ⟨⟨b₁, ⟨u₁⟩⟩, h₁⟩ := W₁
  obtain ⟨⟨b₂, ⟨u₂⟩⟩, h₂⟩ := W₂
  have e₁ : b₁ = T := h₁
  subst e₁
  have e₂ : b₂ = b₁ := h₂
  subst e₂
  have hlift : (functorialityTwoFibreProduct φ).IsHomLift (𝟙 b₂)
    (Functor.Fiber.fiberInclusion.map Ψ) := Ψ.2
  have hb : (Functor.Fiber.fiberInclusion.map Ψ).hbase = 𝟙 b₂ :=
    (map_eq_eqToHom_of_isHomLift (functorialityTwoFibreProduct φ)
      (Functor.Fiber.fiberInclusion.map Ψ) (𝟙 b₂) hlift rfl rfl rfl).trans
      (eqToHom_refl b₂ _)
  obtain ⟨χ, hχ⟩ := exists_hom_of_hbase_eq_id φ hφ b₂ u₁ u₂
    (Functor.Fiber.fiberInclusion.map Ψ) hb
  have hχlift : (liftedFibredCategory G.objects).p.IsHomLift (𝟙 b₂) χ :=
    (Functor.isHomLift_map_iff_of_comp_eq (liftedFibredCategory G.objects).p
      (functorialityTwoFibreProduct φ) (functorialityComparison φ)
      (functorialityComparison_comp φ) (𝟙 b₂) χ).mp (by rw [hχ]; exact hlift)
  refine ⟨Functor.Fiber.homMk (liftedFibredCategory G.objects).p b₂ χ, Functor.Fiber.hom_ext ?_⟩
  exact (Functor.Fiber.fiberInclusion_map_mapOfComp_map (liftedFibredCategory G.objects).p
    (functorialityTwoFibreProduct φ) (functorialityComparison φ)
    (functorialityComparison_comp φ) b₂ _).trans
    ((congrArg (fun k => (functorialityComparison φ).map k)
      (Functor.Fiber.fiberInclusion_homMk (liftedFibredCategory G.objects).p b₂ χ)).trans hχ)

/-- **Stacks 003Z (1) for faithfulness of the comparison 1-morphism, on one fibre**: free from
`AlgebraicGeometry.Stack.functorialityComparison_faithful`, because the fibre functor followed by
the inclusion of the fibre is the inclusion of the fibre followed by the comparison. -/
private theorem faithful_fiber_functorialityComparison (φ : Hom G G')
    (T : BigFppfOver C S hS) :
    (Functor.Fiber.mapOfComp (liftedFibredCategory G.objects).p
      (functorialityTwoFibreProduct φ) (functorialityComparison φ)
      (functorialityComparison_comp φ) T).Faithful := by
  have := functorialityComparison_faithful φ
  have : (Functor.Fiber.fiberInclusion (p := (liftedFibredCategory G.objects).p) (S := T) ⋙
      functorialityComparison φ).Faithful := Functor.Faithful.comp _ _
  exact Functor.Faithful.of_comp_eq (Functor.Fiber.mapOfComp_comp_fiberInclusion
    (liftedFibredCategory G.objects).p (functorialityTwoFibreProduct φ)
    (functorialityComparison φ) (functorialityComparison_comp φ) T)

/-- **The comparison 1-morphism of Stacks 04ZN is full when the source square of `φ` is
cartesian.**

This is one of the two halves into which
`AlgebraicGeometry.Stack.isTwoFibreProduct_functorialitySquare` splits Stacks 04ZN; it is checked
fibrewise by Stacks 003Z (1), and on a fibre it is the statement that a vertical morphism of the
2-fibre product between the images of two points of the object space is an identity. That is where
the cartesian source square enters: by Stacks 044X (2) such a morphism comes from a `T`-point `r`
of the arrow space, the commuting square of the 2-fibre product forces the image of `r` in `R'` to
be an identity arrow, and the cartesian square forces `r` itself to be one. -/
theorem functorialityComparison_full (φ : Hom G G')
    (hφ : IsPullback φ.toGroupoidHom.mapArrows G.source.hom G'.source.hom
      φ.toGroupoidHom.mapObjects) :
    (functorialityComparison φ).Full :=
  ((Functor.IsFiberedInGroupoids.full_and_faithful_iff_forall_fiber
    (liftedFibredCategory G.objects).p (functorialityTwoFibreProduct φ)
    (isFiberedInGroupoids_uliftHom _ (fibredCategory C S hS G.objects.obj).property)
    (isFiberedInGroupoids_functorialityTwoFibreProduct φ)
    (functorialityComparison φ) (functorialityComparison_comp φ)).mpr
    (fun T => ⟨full_fiber_functorialityComparison φ hφ T,
      faithful_fiber_functorialityComparison φ T⟩)).1

end AlgebraicGeometry.Stack

end
