module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.ProjectionTwoArrow
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import StacksFrontier.CategoryTheory.FiberedCategory.IsoOver
import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.LocalStructure.GeometricStalkRetractions
import StacksFrontier.AlgebraicGeometry.Stacks.NormalizationGroupoidConstruction

/-!
# The cocycle identity for the canonical quotient-stack 2-morphism (Stacks 044T)

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `B` over a
scheme `S` of a big fppf site, let `π : 𝒮_U ⟶ [U/R]` be the canonical projection of Stacks 044R,
and let `α : π ∘ s ⟶ π ∘ t` be the 2-morphism of Stacks 044S making the quotient-stack square
2-commutative. Over the space `R ×_{s, U, t} R` of composable pairs of arrows there are three
ways of restricting `α`: along the first projection, along the second projection, and along the
composition morphism of the groupoid. Stacks 044T is the resulting *cocycle identity*: the
2-morphism attached to a composite arrow is the vertical composite of the two 2-morphisms
attached to its factors.

Stating the identity needs the three identifications of endpoints that make the two sides
parallel. These are equalities of entire 1-morphisms of fibred categories, not merely of their
values at one object, so they are proved first; the cocycle identity is then an equality of
2-morphisms transported along them.

## Main results

* `AlgebraicGeometry.Stack.quotientStackTwoArrow_source_comp_eq`: **Stacks 044T** — the composite
  arrow and the second arrow of a composable pair have the same source in the quotient stack.
* `AlgebraicGeometry.Stack.quotientStackTwoArrow_middle_comp_eq`: **Stacks 044T** — the target of
  the second arrow is the source of the first.
* `AlgebraicGeometry.Stack.quotientStackTwoArrow_target_comp_eq`: **Stacks 044T** — the first
  arrow and the composite arrow have the same target.
* `AlgebraicGeometry.Stack.quotientStackTwoArrow_cocycle`: **Stacks 044T** — the vertical
  composition law for the canonical 2-morphism.

## Implementation notes

The three endpoint equalities all come from one observation: the 1-morphism attached by
Stacks 0458 to a composite of maps of presheaves is the composite of the attached 1-morphisms
(`associatedMap_comp_hom` below). Granted that, each endpoint equality is the equality of maps
of presheaves obtained from the cartesian square defining the space of composable pairs — for
the middle one this is literally `CategoryTheory.Limits.pullback.condition`, and for the two
outer ones it is the statement that composition of arrows preserves the source of the second
factor and the target of the first, which is the pointwise groupoid law
`Deformation.PointwiseGroupoid.source_comp` read at every test object.

The cocycle identity itself is checked componentwise. At a point of the space of composable
pairs the three components of `AlgebraicGeometry.Stack.quotientStackTwoArrow` are images under
`AlgebraicGeometry.Stack.pointwiseToQuotientStack` of three arrows of the pointwise groupoid
fibration, each lying over an identity of the site and each named by the corresponding element of
the arrow space. An arrow of the pointwise groupoid fibration lying over an identity comes from
an arrow of the fibre (`vertical_rep`), and two such arrows compose to the one named by the
composite element of the arrow space, because that is what the composition morphism of the
groupoid computes; this is `quotient_arrows_comp`. Everything else is `eqToHom` bookkeeping
between the endpoints that `AlgebraicGeometry.Stack.associatedMap` actually produces and the
endpoints named by the source and target maps, which are only heterogeneously equal.

## References

* [Stacks Project, Tag 0458](https://stacks.math.columbia.edu/tag/0458)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 044S](https://stacks.math.columbia.edu/tag/044S)
* [Stacks Project, Tag 044T](https://stacks.math.columbia.edu/tag/044T)
* [Stacks Project, Tag 06K3](https://stacks.math.columbia.edu/tag/06K3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u v w

/- A point of `fibredCategory` or of the pointwise groupoid fibration is an object of a
Grothendieck construction indexed through `Functor.toPseudofunctor'`, reached through
`BasedCategory.ofFunctor`, and a category fibred in groupoids is a `Bicategory.InducedBicategory`
over a subtype; none of these is unfolded at `implicit` transparency, so a goal naming such an
object together with its `base` or `fiber`, or naming the underlying based category of a fibred
category, is not type-correct there and `rw`, `simp` and even `rfl` decline it. Naming that
unfolding chain is what lets the ordinary tactics see through it. -/
attribute [local implicit_reducible] Bicategory.InducedBicategory fibredCategory
  CategoryTheory.Functor.toPseudofunctor'
  CategoryTheory.pseudofunctorOfIsLocallyDiscrete Quiver.Hom.toLoc
  BasedCategory.ofFunctor Grpd.forgetToCat Grpd.of typeToGrpd
  Pseudofunctor.CoGrothendieck.forget Pseudofunctor.CoGrothendieck.ι
  AlgebraicSpaces.fiberProduct GroupoidInAlgebraicSpaces.toGroupoidInFunctors

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_TwoArrowCocycle :
    HasPullbacks ((BigFppfOver C S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_TwoArrowCocycle
    {X Y Z : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

local instance (priority := high) hasPullback_types_TwoArrowCocycle
    {X Y Z : Type u} (f : X ⟶ Z) (g : Y ⟶ Z) : HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

-- A based functor is determined by its underlying functor:
-- `CategoryTheory.BasedCategory.BasedFunctor.ext'`, public in
-- `StacksFrontier.CategoryTheory.FiberedCategory.IsoOver`. A `private` re-declaration,
-- one of ten across the library, stood here.

/-- Two heterogeneously equal points of discrete categories on equal types have, after transport,
the same underlying element. -/
private theorem discrete_as_eq_of_heq {α β : Type u} (hα : α = β)
    {x : Discrete α} {y : Discrete β} (h : HEq x y) :
    cast hα x.as = y.as := by
  cases hα
  simpa using congrArg Discrete.as (eq_of_heq h)

/-- The 1-morphism attached to a composite of maps of presheaves agrees on objects with the
composite of the attached 1-morphisms. -/
private theorem associatedMap_comp_obj
    {F G H : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (a : F ⟶ G) (b : G ⟶ H) :
    ∀ x : (fibredCategory C S hS F).val.obj,
      ((associatedMap C S hS (a ≫ b)).1.hom).obj x =
        ((associatedMap C S hS b).1.hom).obj
          (((associatedMap C S hS a).1.hom).obj x) := by
  intro x
  apply (PresheafOfCategories.objEquiv
    ((H ⋙ typeToGrpd) ⋙ Grpd.forgetToCat)).injective
  apply Sigma.ext
  · show ((associatedMap C S hS (a ≫ b)).1.hom.obj x).base = _
    calc
      _ = x.base := BasedFunctor.w_obj
        (associatedMap C S hS (a ≫ b)).1.hom x
      _ = ((associatedMap C S hS b).1.hom.obj
        ((associatedMap C S hS a).1.hom.obj x)).base :=
          ((BasedFunctor.w_obj (associatedMap C S hS b).1.hom
            ((associatedMap C S hS a).1.hom.obj x)).trans
              (BasedFunctor.w_obj (associatedMap C S hS a).1.hom x)).symm
  · let xa := (associatedMap C S hS a).1.hom.obj x
    let xc := (associatedMap C S hS (a ≫ b)).1.hom.obj x
    let xr := (associatedMap C S hS b).1.hom.obj xa
    show xc.fiber ≍ xr.fiber
    have hxa : xa.base = x.base := BasedFunctor.w_obj (associatedMap C S hS a).1.hom x
    have hxc : xc.base = x.base := BasedFunctor.w_obj (associatedMap C S hS (a ≫ b)).1.hom x
    have hxr : xr.base = x.base :=
      (show xr.base = xa.base from BasedFunctor.w_obj (associatedMap C S hS b).1.hom xa).trans hxa
    have h₁ : xa.fiber ≍ Discrete.mk (a.app (Opposite.op x.base) x.fiber.as) :=
      (associatedMap C S hS a).property x
    have h₂ : xr.fiber ≍ Discrete.mk (b.app (Opposite.op xa.base) xa.fiber.as) :=
      (associatedMap C S hS b).property xa
    have h₃ : xc.fiber ≍ Discrete.mk ((a ≫ b).app (Opposite.op x.base) x.fiber.as) :=
      (associatedMap C S hS (a ≫ b)).property x
    rcases xa with ⟨xaBase, xaFiber⟩
    change xaBase = x.base at hxa
    subst xaBase
    rcases xc with ⟨xcBase, xcFiber⟩
    change xcBase = x.base at hxc
    subst xcBase
    rcases xr with ⟨xrBase, xrFiber⟩
    change xrBase = x.base at hxr
    subst xrBase
    have h₁' : xaFiber.as = a.app (Opposite.op x.base) x.fiber.as :=
      discrete_as_eq_of_heq rfl h₁
    have h₂' : xrFiber.as = b.app (Opposite.op x.base) xaFiber.as :=
      discrete_as_eq_of_heq rfl h₂
    have hcalc : (a ≫ b).app (Opposite.op x.base) x.fiber.as =
        b.app (Opposite.op x.base) xaFiber.as := by simp [h₁']
    exact h₃.trans ((heq_of_eq (congrArg Discrete.mk hcalc)).trans h₂.symm)

/-- The base component of an arrow of a split fibration coming from an equality of its
endpoints. -/
private theorem presheaf_eqToHom_base
    {D : (BigFppfOver C S hS)ᵒᵖ ⥤ Cat}
    {x y : (presheafOfCategories D).obj} (h : x = y) :
    (eqToHom h).base = eqToHom (congrArg (fun z => z.base) h) := by
  cases h
  rfl

/-- The base component of an arrow of a split fibration conjugated by equalities of its
endpoints. -/
private theorem presheaf_conj_base
    {D : (BigFppfOver C S hS)ᵒᵖ ⥤ Cat}
    {x x' y y' : (presheafOfCategories D).obj} (hx : x = x') (hy : y' = y) (m : x' ⟶ y') :
    (eqToHom hx ≫ m ≫ eqToHom hy).base =
      eqToHom (congrArg (fun z => z.base) hx) ≫ m.base ≫
        eqToHom (congrArg (fun z => z.base) hy) := by
  cases hx
  cases hy
  simp

/-- Two 1-morphisms into the fibred category attached to a presheaf which agree on objects are
equal: the fibres are discrete, so the fibre components of their values on arrows agree
automatically and the base components are forced by compatibility with the projection. -/
private theorem basedFunctor_eq_of_obj_eq_discrete
    {𝒳 : BasedCategory (BigFppfOver C S hS)}
    {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    {f g : 𝒳 ⥤ᵇ (fibredCategory C S hS F).val}
    (hobj : ∀ x, f.obj x = g.obj x) : f = g := by
  apply BasedCategory.BasedFunctor.ext'
  refine CategoryTheory.Functor.ext hobj ?_
  intro x y φ
  apply Pseudofunctor.CoGrothendieck.Hom.ext
  · apply Discrete.hom_eq
  · have hbx : (f.obj x).base = (g.obj x).base := congrArg (fun z => z.base) (hobj x)
    have hby : (f.obj y).base = (g.obj y).base := congrArg (fun z => z.base) (hobj y)
    have hf := Functor.congr_hom f.w φ
    have hg := Functor.congr_hom g.w φ
    change (f.map φ).base = _ at hf
    change (g.map φ).base = _ at hg
    have hsplit : (eqToHom (hobj x) ≫ g.map φ ≫ eqToHom (hobj y).symm).base =
        eqToHom hbx ≫ (g.map φ).base ≫ eqToHom hby.symm :=
      presheaf_conj_base (hobj x) (hobj y).symm (g.map φ)
    refine hf.trans (Eq.trans ?_ hsplit.symm)
    rw [hg]
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

/-- Two sections of a presheaf pullback over the same test object with the same two projections
are equal: evaluation preserves the pullback. -/
private theorem pullback_eval_ext
    {F G H : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ H) (g : G ⟶ H) (i : (BigFppfOver C S hS)ᵒᵖ)
    {a b : (pullback f g).obj i}
    (h₁ : (pullback.fst f g).app i a = (pullback.fst f g).app i b)
    (h₂ : (pullback.snd f g).app i a = (pullback.snd f g).app i b) : a = b := by
  let E := (CategoryTheory.evaluation (BigFppfOver C S hS)ᵒᵖ (Type u)).obj i
  let e := PreservesPullback.iso E f g
  have key {X : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (k : pullback f g ⟶ X)
      (k' : pullback (f.app i) (g.app i) ⟶ X.obj i) (hk : e.hom ≫ k' = k.app i)
      (h : k.app i a = k.app i b) : k' (e.hom a) = k' (e.hom b) := by
    have hka (z) : k' (e.hom z) = k.app i z := congrArg (· z) hk
    rw [hka, hka, h]
  have heq : e.hom a = e.hom b :=
    PullbackCone.IsLimit.type_ext (pullback.isLimit (f.app i) (g.app i))
      (key _ _ (PreservesPullback.iso_hom_fst E f g) h₁)
      (key _ _ (PreservesPullback.iso_hom_snd E f g) h₂)
  simpa using congrArg e.inv heq

/-- The 1-morphism of Stacks 0458 attached to a composite of maps of presheaves is the composite
of the attached 1-morphisms. -/
private theorem associatedMap_comp_hom
    {F G H : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (a : F ⟶ G) (b : G ⟶ H) :
    (associatedMap C S hS (a ≫ b)).1.hom =
      BasedFunctor.comp (associatedMap C S hS a).1.hom
        (associatedMap C S hS b).1.hom :=
  basedFunctor_eq_of_obj_eq_discrete (fun x => associatedMap_comp_obj a b x)

/-- Two factorisations of a map of presheaves give equal composites of attached 1-morphisms, after
any further 1-morphism. -/
private theorem comp_associatedMap_eq
    {F G G' H : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} {𝒴 : BasedCategory (BigFppfOver C S hS)}
    (a : F ⟶ G) (b : G ⟶ H) (a' : F ⟶ G') (b' : G' ⟶ H) (h : a ≫ b = a' ≫ b')
    (P : (fibredCategory C S hS H).val ⥤ᵇ 𝒴) :
    BasedFunctor.comp (associatedMap C S hS a).1.hom
      (BasedFunctor.comp (associatedMap C S hS b).1.hom P) =
    BasedFunctor.comp (associatedMap C S hS a').1.hom
      (BasedFunctor.comp (associatedMap C S hS b').1.hom P) := by
  rw [← BasedFunctor.comp_assoc, ← BasedFunctor.comp_assoc, ← associatedMap_comp_hom,
    ← associatedMap_comp_hom, h]

/-- The fibre component of the value of the 1-morphism attached to a map of presheaves is the
value of that map, up to the transport along the comparison of bases. -/
private theorem associatedMap_fiber_as
    {F H : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (a : F ⟶ H)
    (x : (fibredCategory C S hS F).val.obj) :
    HEq (Discrete.as (((associatedMap C S hS a).1.hom.obj x).fiber))
      (a.app (Opposite.op x.base) (Discrete.as x.fiber)) := by
  let y := ((associatedMap C S hS a).1.hom).obj x
  show HEq (Discrete.as y.fiber)
    (a.app (Opposite.op x.base) (Discrete.as x.fiber))
  have hybase : y.base = x.base := BasedFunctor.w_obj (associatedMap C S hS a).1.hom x
  have hyprop : y.fiber ≍ Discrete.mk
      (a.app (Opposite.op x.base) (Discrete.as x.fiber)) :=
    (associatedMap C S hS a).property x
  rcases y with ⟨ybase, yfiber⟩
  change ybase = x.base at hybase
  subst ybase
  show HEq (Discrete.as yfiber) (a.app (Opposite.op x.base) (Discrete.as x.fiber))
  have hdisc : yfiber ≍ Discrete.mk
      (a.app (Opposite.op x.base) (Discrete.as x.fiber)) := by
    simpa using hyprop
  exact heq_of_eq (discrete_as_eq_of_heq rfl hdisc)

/-- The value of the 1-morphism attached to a map of presheaves, as a point of the total space
of the target presheaf, is the value of that map. -/
private theorem associatedMap_obj_sigma
    {F H : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (a : F ⟶ H)
    (x : (fibredCategory C S hS F).val.obj) :
    (⟨((associatedMap C S hS a).1.hom.obj x).base,
        ((associatedMap C S hS a).1.hom.obj x).fiber.as⟩ :
        Σ T : BigFppfOver C S hS, H.obj (Opposite.op T)) =
      ⟨x.base, a.app (Opposite.op x.base) x.fiber.as⟩ :=
  Sigma.ext (BasedFunctor.w_obj (associatedMap C S hS a).1.hom x) (associatedMap_fiber_as a x)

/-- Following the 1-morphism attached to a map into the object space by the projection to the
quotient stack gives the point of the quotient stack presented by the value of that map. -/
private theorem associatedMap_obj_quotient
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (a : F ⟶ G.objects.obj)
    (x : (fibredCategory C S hS F).val.obj) :
    (BasedFunctor.comp (associatedMap C S hS a).1.hom
      (quotientStackProjection G)).obj x =
      (pointwiseToQuotientStack G).obj
        ⟨x.base, a.app (Opposite.op x.base) (Discrete.as x.fiber)⟩ := by
  let y := ((associatedMap C S hS a).1.hom).obj x
  have hybase : y.base = x.base := BasedFunctor.w_obj (associatedMap C S hS a).1.hom x
  have hv := associatedMap_fiber_as a x
  dsimp [BasedFunctor.comp]
  show (quotientStackProjection G).obj y = _
  rw [quotientStackProjection_obj]
  have hobj : (⟨y.base, Discrete.as y.fiber⟩ :
      (presheafOfGroupoids
        (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj) =
      ⟨x.base, a.app (Opposite.op x.base) (Discrete.as x.fiber)⟩ :=
    Pseudofunctor.CoGrothendieck.ext_iff.mpr ⟨hybase, hv⟩
  exact congrArg (fun z => (pointwiseToQuotientStack G).obj z) hobj

/-- The component at a point of a 2-morphism coming from an equality of 1-morphisms. -/
private theorem based_eqToHom_app
    {D : Type*} [Category D] {𝒳 𝒴 : BasedCategory D} {F H : 𝒳 ⥤ᵇ 𝒴}
    (h : F = H) (x : 𝒳.obj) :
    (eqToHom h).toNatTrans.app x = eqToHom (congrArg (fun f => f.obj x) h) := by
  cases h
  rfl

/-- The two projections of a section of the presheaf fibre product of the source and target maps
form a composable pair of arrows. -/
private theorem source_fst_eq_target_snd
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (p : (pullback G.source.hom G.target.hom).obj (Opposite.op T)) :
    G.source.hom.app (Opposite.op T)
        ((pullback.fst G.source.hom G.target.hom).app (Opposite.op T) p) =
      G.target.hom.app (Opposite.op T)
        ((pullback.snd G.source.hom G.target.hom).app (Opposite.op T) p) := by
  have hc := congrArg (fun α : pullback G.source.hom G.target.hom ⟶ G.objects.obj =>
      (α.app (Opposite.op T)) p)
    (pullback.condition (f := G.source.hom) (g := G.target.hom))
  simpa [NatTrans.comp_app] using hc

/-- Every section of the presheaf fibre product of the source and target maps is the image of the
composable pair formed by its two projections. -/
private theorem composableToPullback_app_projections
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (p : (pullback G.source.hom G.target.hom).obj (Opposite.op T)) :
    (composableToPullback G.source.hom G.target.hom).app (Opposite.op T)
        ⟨((pullback.fst G.source.hom G.target.hom).app (Opposite.op T) p,
            (pullback.snd G.source.hom G.target.hom).app (Opposite.op T) p),
          source_fst_eq_target_snd G T p⟩ = p := by
  let a := (pullback.fst G.source.hom G.target.hom).app (Opposite.op T) p
  let b := (pullback.snd G.source.hom G.target.hom).app (Opposite.op T) p
  have h : G.source.hom.app (Opposite.op T) a = G.target.hom.app (Opposite.op T) b :=
    source_fst_eq_target_snd G T p
  show (composableToPullback G.source.hom G.target.hom).app (Opposite.op T) ⟨(a, b), h⟩ = p
  apply pullback_eval_ext G.source.hom G.target.hom (Opposite.op T)
  · show ((composableToPullback G.source.hom G.target.hom ≫
      pullback.fst G.source.hom G.target.hom).app (Opposite.op T) ⟨(a, b), h⟩) = a
    unfold composableToPullback
    rw [pullback.lift_fst]
    rfl
  · show ((composableToPullback G.source.hom G.target.hom ≫
      pullback.snd G.source.hom G.target.hom).app (Opposite.op T) ⟨(a, b), h⟩) = b
    unfold composableToPullback
    rw [pullback.lift_snd]
    rfl

/-- The composition morphism of a groupoid in algebraic spaces, read at a test object, is the
composition of the pointwise groupoid applied to the two projections of a composable pair. -/
private theorem comp_app_eq_pointwise
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (p : (pullback G.source.hom G.target.hom).obj (Opposite.op T)) :
    G.comp.hom.app (Opposite.op T) p =
      G.toGroupoidInFunctors.comp.app (Opposite.op T)
        ⟨((pullback.fst G.source.hom G.target.hom).app (Opposite.op T) p,
            (pullback.snd G.source.hom G.target.hom).app (Opposite.op T) p),
          source_fst_eq_target_snd G T p⟩ :=
  congrArg (G.comp.hom.app (Opposite.op T)) (composableToPullback_app_projections G T p).symm

/-- The composite of a composable pair of arrows of a groupoid in algebraic spaces has the source
of the second factor, read at a test object. -/
private theorem quotientComp_source_app
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (p : (pullback G.source.hom G.target.hom).obj (Opposite.op T)) :
    G.source.hom.app (Opposite.op T)
      (G.comp.hom.app (Opposite.op T) p) =
    G.source.hom.app (Opposite.op T)
      ((pullback.snd G.source.hom G.target.hom).app (Opposite.op T) p) := by
  rw [comp_app_eq_pointwise G T p]
  exact (G.toGroupoidInFunctors.pointwiseData (Opposite.op T)).source_comp _ _ _

/-- The composite of a composable pair of arrows of a groupoid in algebraic spaces has the target
of the first factor, read at a test object. -/
private theorem quotientComp_target_app
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (p : (pullback G.source.hom G.target.hom).obj (Opposite.op T)) :
    G.target.hom.app (Opposite.op T)
      (G.comp.hom.app (Opposite.op T) p) =
    G.target.hom.app (Opposite.op T)
      ((pullback.fst G.source.hom G.target.hom).app (Opposite.op T) p) := by
  rw [comp_app_eq_pointwise G T p]
  exact (G.toGroupoidInFunctors.pointwiseData (Opposite.op T)).target_comp _ _ _

/-- Alias of `AlgebraicGeometry.GroupoidInAlgebraicSpaces.comp_hom_comp_source`. -/
private alias quotientComp_source_eq := GroupoidInAlgebraicSpaces.comp_hom_comp_source

/-- Alias of `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Normalized.comp_hom_target`. -/
private alias quotientComp_target_eq := GroupoidInAlgebraicSpaces.Normalized.comp_hom_target

/-- **Stacks 044T.** The composite arrow and the second arrow of a composable pair have the same
source in the quotient stack. -/
@[stacks 044T "source endpoint equality"]
theorem quotientStackTwoArrow_source_comp_eq
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    let a₁ := (associatedMap C S hS
      (pullback.snd G.source.hom G.target.hom)).1.hom
    let ac := (associatedMap C S hS G.comp.hom).1.hom
    let Fs := BasedFunctor.comp
      (associatedMap C S hS G.source.hom).1.hom
      (quotientStackProjection G)
  BasedFunctor.comp ac Fs = BasedFunctor.comp a₁ Fs := by
  exact comp_associatedMap_eq _ _ _ _ (quotientComp_source_eq G) _

/-- **Stacks 044T.** The target of the second arrow is the source of the first arrow of a
composable pair, as 1-morphisms to the quotient stack. -/
@[stacks 044T "middle endpoint equality"]
theorem quotientStackTwoArrow_middle_comp_eq
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    let a₀ := (associatedMap C S hS
      (pullback.fst G.source.hom G.target.hom)).1.hom
    let a₁ := (associatedMap C S hS
      (pullback.snd G.source.hom G.target.hom)).1.hom
    let Fs := BasedFunctor.comp
      (associatedMap C S hS G.source.hom).1.hom
      (quotientStackProjection G)
    let Ft := BasedFunctor.comp
      (associatedMap C S hS G.target.hom).1.hom
      (quotientStackProjection G)
  BasedFunctor.comp a₁ Ft = BasedFunctor.comp a₀ Fs := by
  exact comp_associatedMap_eq _ _ _ _ pullback.condition.symm _

/-- **Stacks 044T.** The first arrow of a composable pair and the composite arrow have the same
target in the quotient stack. -/
@[stacks 044T "target endpoint equality"]
theorem quotientStackTwoArrow_target_comp_eq
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    let a₀ := (associatedMap C S hS
      (pullback.fst G.source.hom G.target.hom)).1.hom
    let ac := (associatedMap C S hS G.comp.hom).1.hom
    let Ft := BasedFunctor.comp
      (associatedMap C S hS G.target.hom).1.hom
      (quotientStackProjection G)
  BasedFunctor.comp a₀ Ft = BasedFunctor.comp ac Ft := by
  exact (comp_associatedMap_eq _ _ _ _ (quotientComp_target_eq G) _).symm

/-- An arrow of a split fibration lying over an identity of the site comes from an arrow of the
fibre. -/
private theorem vertical_rep
    {D : Type u} [Category.{v} D] (F : Dᵒᵖ ⥤ Cat.{w, w})
    (T : D) {a b : F.obj (Opposite.op T)}
    (g : (⟨T, a⟩ : (presheafOfCategories F).obj) ⟶ ⟨T, b⟩)
    (hg : g.base = 𝟙 T) :
    ∃ f : a ⟶ b, (Pseudofunctor.CoGrothendieck.ι F.toPseudofunctor' T).map f = g := by
  rcases g with ⟨base, fiber⟩
  change base = 𝟙 T at hg
  subst base
  have hb : (F.map (𝟙 T).op).toFunctor.obj b = b := by simp
  refine ⟨fiber ≫ eqToHom hb, ?_⟩
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ ?_ ?_
  · rfl
  · simp only [op_id, Quiver.Hom.id_toLoc, Pseudofunctor.CoGrothendieck.ι_map_fiber,
      Cat.Hom.id_toFunctor, Functor.toPseudofunctor'_mapId, eqToIso.inv,
      Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app, Functor.id_obj, Category.assoc, eqToHom_trans,
      eqToHom_refl, Category.comp_id]

/-- The inclusion of a fibre into the pointwise groupoid fibration does not change the underlying
element of the arrow space. -/
private theorem inclusion_arrow
    {D : Type*} [Category D] (G : Deformation.GroupoidInFunctors Dᵒᵖ)
    (T : D) {a b : G.Evaluation (Opposite.op T)} (f : a ⟶ b) :
    (G.evaluationArrowEquiv (Opposite.op T) _ _
      ((Pseudofunctor.CoGrothendieck.ι
        ((evaluationGroupoidFunctor G) ⋙ Grpd.forgetToCat).toPseudofunctor'
        T).map f).fiber).val = (G.evaluationArrowEquiv (Opposite.op T) _ _ f).val := by
  simp only [Pseudofunctor.CoGrothendieck.ι_map_fiber,
    Functor.toPseudofunctor'_mapId, eqToIso.inv, Cat.eqToHom_app]
  apply evaluationArrow_comp_eqToHom

/-- An arrow of the pointwise groupoid fibration lying over an identity of the site comes from an
arrow of the evaluated groupoid, with the same underlying element of the arrow space. -/
private theorem vertical_rep_value
    {D : Type*} [Category D] (G : Deformation.GroupoidInFunctors Dᵒᵖ)
    (T : D) {a b : G.Evaluation (Opposite.op T)}
    (g : (⟨T, a⟩ : (presheafOfGroupoids (evaluationGroupoidFunctor G)).obj) ⟶ ⟨T, b⟩)
    (hg : g.base = 𝟙 T) :
    ∃ f : a ⟶ b,
      (Pseudofunctor.CoGrothendieck.ι
          ((evaluationGroupoidFunctor G) ⋙ Grpd.forgetToCat).toPseudofunctor' T).map f = g ∧
      (G.evaluationArrowEquiv (Opposite.op T) _ _ f).val =
        (G.evaluationArrowEquiv (Opposite.op T) _ _ g.fiber).val := by
  obtain ⟨f, rfl⟩ := vertical_rep
    ((evaluationGroupoidFunctor G) ⋙ Grpd.forgetToCat) T g hg
  exact ⟨f, rfl, (inclusion_arrow G T f).symm⟩

/-- A point of the fibred category attached to a presheaf is determined by the test object and
the element of the presheaf it names. -/
private theorem arrow_object_eq
    {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (x : (fibredCategory C S hS F).val.obj)
    (T : BigFppfOver C S hS) (r : F.obj (Opposite.op T))
    (h : (⟨x.base, x.fiber.as⟩ : Σ T, F.obj (Opposite.op T)) = ⟨T, r⟩) :
    x = ⟨T, Discrete.mk r⟩ := by
  rcases x with ⟨base, fiber⟩
  have hb := congrArg Sigma.fst h
  change base = T at hb
  subst base
  have hf := eq_of_heq (Sigma.mk.inj h).2
  cases fiber
  cases hf
  rfl

/-- The arrow of the pointwise groupoid fibration named by the composite of a composable pair is
the composite of the arrows named by its two factors, conjugated by the identifications of their
endpoints. -/
private theorem quotient_arrows_comp
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (p : (pullback G.source.hom G.target.hom).obj (Opposite.op T))
    (xc x₁ x₀ : (fibredCategory C S hS G.arrows.obj).val.obj)
    (hc : (⟨xc.base, xc.fiber.as⟩ : Σ T, G.arrows.obj.obj (Opposite.op T)) =
      ⟨T, G.comp.hom.app (Opposite.op T) p⟩)
    (h₁ : (⟨x₁.base, x₁.fiber.as⟩ : Σ T, G.arrows.obj.obj (Opposite.op T)) =
      ⟨T, (pullback.snd G.source.hom G.target.hom).app (Opposite.op T) p⟩)
    (h₀ : (⟨x₀.base, x₀.fiber.as⟩ : Σ T, G.arrows.obj.obj (Opposite.op T)) =
      ⟨T, (pullback.fst G.source.hom G.target.hom).app (Opposite.op T) p⟩)
    (gc : (⟨xc.base, G.source.hom.app (Opposite.op xc.base) xc.fiber.as⟩ :
      (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj) ⟶
      ⟨xc.base, G.target.hom.app (Opposite.op xc.base) xc.fiber.as⟩)
    (g₁ : (⟨x₁.base, G.source.hom.app (Opposite.op x₁.base) x₁.fiber.as⟩ :
      (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj) ⟶
      ⟨x₁.base, G.target.hom.app (Opposite.op x₁.base) x₁.fiber.as⟩)
    (g₀ : (⟨x₀.base, G.source.hom.app (Opposite.op x₀.base) x₀.fiber.as⟩ :
      (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj) ⟶
      ⟨x₀.base, G.target.hom.app (Opposite.op x₀.base) x₀.fiber.as⟩)
    (hgc : gc.base = 𝟙 xc.base) (hg₁ : g₁.base = 𝟙 x₁.base) (hg₀ : g₀.base = 𝟙 x₀.base)
    (hvc : (G.toGroupoidInFunctors.evaluationArrowEquiv
      (Opposite.op xc.base) _ _ gc.fiber).val = xc.fiber.as)
    (hv₁ : (G.toGroupoidInFunctors.evaluationArrowEquiv
      (Opposite.op x₁.base) _ _ g₁.fiber).val = x₁.fiber.as)
    (hv₀ : (G.toGroupoidInFunctors.evaluationArrowEquiv
      (Opposite.op x₀.base) _ _ g₀.fiber).val = x₀.fiber.as)
    (hs : (⟨xc.base, G.source.hom.app (Opposite.op xc.base) xc.fiber.as⟩ :
      (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj) =
      ⟨x₁.base, G.source.hom.app (Opposite.op x₁.base) x₁.fiber.as⟩)
    (hm : (⟨x₁.base, G.target.hom.app (Opposite.op x₁.base) x₁.fiber.as⟩ :
      (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj) =
      ⟨x₀.base, G.source.hom.app (Opposite.op x₀.base) x₀.fiber.as⟩)
    (ht : (⟨x₀.base, G.target.hom.app (Opposite.op x₀.base) x₀.fiber.as⟩ :
      (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj) =
      ⟨xc.base, G.target.hom.app (Opposite.op xc.base) xc.fiber.as⟩) :
    gc = eqToHom hs ≫ g₁ ≫ eqToHom hm ≫ g₀ ≫ eqToHom ht := by
  cases arrow_object_eq xc T _ hc
  cases arrow_object_eq x₁ T _ h₁
  cases arrow_object_eq x₀ T _ h₀
  obtain ⟨fc, rfl, hfc⟩ := vertical_rep_value G.toGroupoidInFunctors T gc hgc
  obtain ⟨f₁, rfl, hf₁⟩ := vertical_rep_value G.toGroupoidInFunctors T g₁ hg₁
  obtain ⟨f₀, rfl, hf₀⟩ := vertical_rep_value G.toGroupoidInFunctors T g₀ hg₀
  have hs' := eq_of_heq (Pseudofunctor.CoGrothendieck.ext_iff.mp hs).2
  have hm' := eq_of_heq (Pseudofunctor.CoGrothendieck.ext_iff.mp hm).2
  have ht' := eq_of_heq (Pseudofunctor.CoGrothendieck.ext_iff.mp ht).2
  let f₁' := eqToHom hs' ≫ f₁ ≫ eqToHom hm'
  let f₀' := f₀ ≫ eqToHom ht'
  have hfc' := hfc.trans hvc
  have hf₁' : (G.toGroupoidInFunctors.evaluationArrowEquiv (Opposite.op T) _ _ f₁').val =
      (pullback.snd G.source.hom G.target.hom).app (Opposite.op T) p := by
    dsimp only [f₁']
    rw [evaluationArrow_eqToHom_comp, evaluationArrow_comp_eqToHom]
    exact hf₁.trans hv₁
  have hf₀' : (G.toGroupoidInFunctors.evaluationArrowEquiv (Opposite.op T) _ _ f₀').val =
      (pullback.fst G.source.hom G.target.hom).app (Opposite.op T) p := by
    dsimp only [f₀']
    rw [evaluationArrow_comp_eqToHom]
    exact hf₀.trans hv₀
  have heq : fc = f₁' ≫ f₀' := by
    apply (G.toGroupoidInFunctors.evaluationArrowEquiv (Opposite.op T) _ _).injective
    apply Subtype.ext
    rw [hfc', Deformation.GroupoidInFunctors.evaluationArrowEquiv_comp]
    unfold Deformation.GroupoidInFunctors.compose
    simp only [hf₀', hf₁']
    exact comp_app_eq_pointwise G T p
  have hi := congrArg
    (Pseudofunctor.CoGrothendieck.ι
      ((evaluationGroupoidFunctor G.toGroupoidInFunctors) ⋙
        Grpd.forgetToCat).toPseudofunctor' T).map heq
  simpa only [f₁', f₀', Functor.map_comp, eqToHom_map, Category.assoc] using hi

/-- For three points of the attached fibred category naming the composite of a composable pair of
arrows and its two factors, the source of the composite is the source of the second factor, the
target of the second factor is the source of the first, and the target of the first is the target
of the composite — as objects of the pointwise groupoid fibration. These are the three
identifications along which the two sides of the cocycle identity are compared. -/
private theorem quotientTwoArrow_endpoint_obj_eq
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (p : (pullback G.source.hom G.target.hom).obj (Opposite.op T))
    (xc x₁ x₀ : (fibredCategory C S hS G.arrows.obj).val.obj)
    (hc : (⟨xc.base, xc.fiber.as⟩ : Σ T, G.arrows.obj.obj (Opposite.op T)) =
      ⟨T, G.comp.hom.app (Opposite.op T) p⟩)
    (h₁ : (⟨x₁.base, x₁.fiber.as⟩ : Σ T, G.arrows.obj.obj (Opposite.op T)) =
      ⟨T, (pullback.snd G.source.hom G.target.hom).app (Opposite.op T) p⟩)
    (h₀ : (⟨x₀.base, x₀.fiber.as⟩ : Σ T, G.arrows.obj.obj (Opposite.op T)) =
      ⟨T, (pullback.fst G.source.hom G.target.hom).app (Opposite.op T) p⟩) :
    ((⟨xc.base, G.source.hom.app (Opposite.op xc.base) xc.fiber.as⟩ :
          (presheafOfGroupoids
            (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj) =
        ⟨x₁.base, G.source.hom.app (Opposite.op x₁.base) x₁.fiber.as⟩) ∧
      ((⟨x₁.base, G.target.hom.app (Opposite.op x₁.base) x₁.fiber.as⟩ :
          (presheafOfGroupoids
            (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj) =
        ⟨x₀.base, G.source.hom.app (Opposite.op x₀.base) x₀.fiber.as⟩) ∧
      ((⟨x₀.base, G.target.hom.app (Opposite.op x₀.base) x₀.fiber.as⟩ :
          (presheafOfGroupoids
            (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj) =
        ⟨xc.base, G.target.hom.app (Opposite.op xc.base) xc.fiber.as⟩) := by
  let ArrowSigma := Σ T : BigFppfOver C S hS, G.arrows.obj.obj (Opposite.op T)
  let ObjectSigma := Σ T : BigFppfOver C S hS, G.objects.obj.obj (Opposite.op T)
  let toSource : ArrowSigma → ObjectSigma := fun z =>
    ⟨z.1, G.source.hom.app (Opposite.op z.1) z.2⟩
  let toTarget : ArrowSigma → ObjectSigma := fun z =>
    ⟨z.1, G.target.hom.app (Opposite.op z.1) z.2⟩
  have mk (x y : G.objects.obj.obj (Opposite.op T)) (h : x = y) :
      (⟨T, x⟩ : ObjectSigma) = ⟨T, y⟩ := by rw [h]
  exact ⟨Pseudofunctor.CoGrothendieck.ext_iff.mpr (Sigma.ext_iff.mp
      ((congrArg toSource hc).trans
        ((mk _ _ (quotientComp_source_app G T p)).trans (congrArg toSource h₁).symm))),
    Pseudofunctor.CoGrothendieck.ext_iff.mpr (Sigma.ext_iff.mp
      ((congrArg toTarget h₁).trans
        ((mk _ _ (source_fst_eq_target_snd G T p).symm).trans (congrArg toSource h₀).symm))),
    Pseudofunctor.CoGrothendieck.ext_iff.mpr (Sigma.ext_iff.mp
      ((congrArg toTarget h₀).trans
        ((mk _ _ (quotientComp_target_app G T p).symm).trans (congrArg toTarget hc).symm)))⟩

/-- Two arrows with transports inserted at and between their endpoints give the same composite
however the transports are distributed, since a transport is determined by its endpoints. Stated
in an abstract category because that is where `eqToHom` bookkeeping is routine; in the quotient
stack the category is a field of an opaque definition and the associativity and `eqToHom` simp
lemmas no longer key-match. -/
private theorem eqToHom_conj_two_eq
    {𝒞 : Type*} [Category 𝒞] {A A₁ X Y Y₁ Z₁ Z W W₁ V : 𝒞}
    (m₁ : X ⟶ Y) (m₀ : Z ⟶ W)
    (p : A = X) (q : Y = Z) (r : W = V)
    (a₁ : A = A₁) (a₂ : A₁ = X) (a₃ : Y = Y₁) (a₄ : Y₁ = Z₁) (a₅ : Z₁ = Z)
    (a₆ : W = W₁) (a₇ : W₁ = V) :
    eqToHom p ≫ m₁ ≫ eqToHom q ≫ m₀ ≫ eqToHom r =
      eqToHom a₁ ≫ (eqToHom a₂ ≫ m₁ ≫ eqToHom a₃) ≫ eqToHom a₄ ≫
        (eqToHom a₅ ≫ m₀ ≫ eqToHom a₆) ≫ eqToHom a₇ := by
  cases a₁
  cases a₂
  cases a₃
  cases a₄
  cases a₅
  cases a₆
  cases a₇
  simp

/-- The component of the canonical 2-morphism at a point of the arrow space, written between the
two points of the quotient stack that the source and target maps actually produce there: it is
the image of an arrow of the pointwise groupoid fibration which lies over the identity of the
site and whose underlying element of the arrow space is the given point. -/
private theorem exists_quotientStackTwoArrow_app_eq
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (y : (fibredCategory C S hS G.arrows.obj).val.obj) :
    ∃ g : (⟨y.base, G.source.hom.app (Opposite.op y.base) y.fiber.as⟩ :
          (presheafOfGroupoids
            (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj) ⟶
        ⟨y.base, G.target.hom.app (Opposite.op y.base) y.fiber.as⟩,
      g.base = 𝟙 y.base ∧
      (G.toGroupoidInFunctors.evaluationArrowEquiv
        (Opposite.op y.base) _ _ g.fiber).val = y.fiber.as ∧
      (quotientStackTwoArrow G).app y =
        eqToHom (associatedMap_obj_quotient G G.source.hom y) ≫
          (pointwiseToQuotientStack G).map g ≫
            eqToHom (associatedMap_obj_quotient G G.target.hom y).symm := by
  obtain ⟨g, hb, hv, hα⟩ := quotientStackTwoArrow_app G y
  exact ⟨g, hb, hv, (conj_eqToHom_iff_heq _ _ (associatedMap_obj_quotient G G.source.hom y)
    (associatedMap_obj_quotient G G.target.hom y)).2 hα⟩

/-- **Stacks 044T.** The canonical 2-morphism of a quotient stack sends composition of groupoid
arrows to vertical composition of 2-morphisms. -/
@[stacks 044T "vertical-composition identity"]
theorem quotientStackTwoArrow_cocycle
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    let a₀ := (associatedMap C S hS
      (pullback.fst G.source.hom G.target.hom)).1.hom
    let a₁ := (associatedMap C S hS
      (pullback.snd G.source.hom G.target.hom)).1.hom
    let ac := (associatedMap C S hS G.comp.hom).1.hom
    let α := quotientStackTwoArrow G
    BasedCategory.whiskerLeft ac α =
      eqToHom (quotientStackTwoArrow_source_comp_eq G) ≫
        BasedCategory.whiskerLeft a₁ α ≫
          eqToHom (quotientStackTwoArrow_middle_comp_eq G) ≫
            BasedCategory.whiskerLeft a₀ α ≫
              eqToHom (quotientStackTwoArrow_target_comp_eq G) := by
  dsimp only
  apply BasedNatTrans.ext
  apply NatTrans.ext
  funext x
  show (quotientStackTwoArrow G).app
      (((associatedMap C S hS G.comp.hom).1.hom).obj x) = _
  simp only [BasedCategory.whiskerLeft]
  let ac := (associatedMap C S hS G.comp.hom).1.hom
  let a₁ := (associatedMap C S hS
    (pullback.snd G.source.hom G.target.hom)).1.hom
  let a₀ := (associatedMap C S hS
    (pullback.fst G.source.hom G.target.hom)).1.hom
  let xc := ac.obj x
  let x₁ := a₁.obj x
  let x₀ := a₀.obj x
  obtain ⟨gc, hgc, hgcval, hc⟩ := exists_quotientStackTwoArrow_app_eq G xc
  obtain ⟨g₁, hg₁, hg₁val, h₁⟩ := exists_quotientStackTwoArrow_app_eq G x₁
  obtain ⟨g₀, hg₀, hg₀val, h₀⟩ := exists_quotientStackTwoArrow_app_eq G x₀
  let p : (pullback G.source.hom G.target.hom).obj (Opposite.op x.base) :=
    x.fiber.as
  have hinputC := associatedMap_obj_sigma G.comp.hom x
  have hinput₁ := associatedMap_obj_sigma (pullback.snd G.source.hom G.target.hom) x
  have hinput₀ := associatedMap_obj_sigma (pullback.fst G.source.hom G.target.hom) x
  obtain ⟨hqsrc, hqmid, hqtgt⟩ :=
    quotientTwoArrow_endpoint_obj_eq G x.base p xc x₁ x₀ hinputC hinput₁ hinput₀
  let gcomp := eqToHom hqsrc ≫ g₁ ≫ eqToHom hqmid ≫ g₀ ≫ eqToHom hqtgt
  have hgccomp : gc = gcomp :=
    quotient_arrows_comp G x.base p xc x₁ x₀ hinputC hinput₁ hinput₀
      gc g₁ g₀ hgc hg₁ hg₀ hgcval hg₁val hg₀val hqsrc hqmid hqtgt
  rw [hc]
  show _ =
    (eqToHom (quotientStackTwoArrow_source_comp_eq G)).toNatTrans.app x ≫
      (quotientStackTwoArrow G).toNatTrans.app (a₁.obj x) ≫
      (eqToHom (quotientStackTwoArrow_middle_comp_eq G)).toNatTrans.app x ≫
      (quotientStackTwoArrow G).toNatTrans.app (a₀.obj x) ≫
      (eqToHom (quotientStackTwoArrow_target_comp_eq G)).toNatTrans.app x
  rw [h₁, h₀]
  rw [based_eqToHom_app, based_eqToHom_app, based_eqToHom_app, hgccomp]
  simp only [gcomp, Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans,
    eqToHom_trans_assoc]
  apply eqToHom_conj_two_eq

end AlgebraicGeometry.Stack

end
