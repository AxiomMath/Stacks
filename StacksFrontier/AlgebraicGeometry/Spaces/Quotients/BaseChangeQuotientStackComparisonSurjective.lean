module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.FunctorialityComparisonSurjectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.BaseChangeQuotientStackPresented

/-!
# Local essential surjectivity on fibres of the Stacks 0DTG comparison

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `B` over a
scheme `S` of a big fppf site, let `φ : U ⟶ X` be an `R`-invariant morphism of algebraic spaces
over `B`, let `g : X' ⟶ X` be a morphism of algebraic spaces over `B` and let `(U', R', s', t',
c')` be the base change of Stacks 048G. This file proves that the comparison 1-morphism
`c : [U'/R'] ⟶ [U/R] ×_{𝒮_X} 𝒮_{X'}` of
`AlgebraicGeometry.Stack.baseChangeQuotientStackComparison` is **locally essentially surjective on
fibres**, which is the third and last hypothesis of
`AlgebraicGeometry.Stack.isTwoFibreProduct_baseChangeQuotientStackSquare` after faithfulness
(`AlgebraicGeometry.Stack.faithful_comparison`) and fullness.

## Main results

* `AlgebraicGeometry.Stack.quotientPointwiseMap_obj_mk`: the map of pointwise groupoid fibrations
  of Stacks 046Q sends the point named by a `T`-point of the object space to the point named by
  its image.
* `AlgebraicGeometry.Stack.locallyEssSurjOnFibers_baseChangeQuotientStackComparison`: **the
  comparison 1-morphism of Stacks 0DTG is locally essentially surjective on fibres.**
* `AlgebraicGeometry.Stack.isHomLift_id_comp`: a vertical morphism followed by one over `f` lies
  over `f`.
* `AlgebraicGeometry.Stack.eq_of_fibredObj_eq`: a point of a presheaf is determined by the object
  of the fibred category of Stacks 0043 it names.

## Implementation notes

*The argument.* Let `P₀ = (T, x, y, α)` be an object of the 2-fibre product over a test object
`T`, with `x` an object of `[U/R]_T`, `y` a `T`-point of `X'` and `α : π(x) ≅ g(y)` vertical. By
Stacks 044X (1), `AlgebraicGeometry.Stack.essImage_toQuotientStack`, there is a covering sieve of
`T` along each member `f : V ⟶ T` of which the pullback of `x` is isomorphic in `[U/R]_V` to the
object presented by a `V`-point `u` of `U`; the sieve produced is that one, and all the work is
over a single `f`.

Over such an `f` one has a morphism `α₀ : π(u) ⟶ x` of `[U/R]` lying over `f`. A cartesian lift
`β : v' ⟶ y` of `f` in the enlarged object-space fibration of `X'` names a `V`-point `v'` of `X'`,
and the two composites `π(u) ⟶ g(y)` — through `α₀` and the filler, and through `β` — lie over
one and the same `f` into the fibred category of `X`, which is fibred in **sets**; so their
sources agree (`AlgebraicGeometry.Stack.obj_eq_of_isHomLift_lifted`), and reading that equality
through `AlgebraicGeometry.Stack.liftedQuotientStackToBase_obj_presented` and
`AlgebraicGeometry.Stack.liftedAssociatedMap_obj_mk` it says `φ(u) = g(v')` in `X(V)`. The
cartesian square `U' = X' ×_X U` of the base change then produces the `V`-point `u'` of `U'` with
`u' ↦ u` and `u' ↦ v'`, by
`AlgebraicGeometry.Space.exists_baseChangeObjectSection`.

The object of `[U'/R']_V` wanted is the one presented by `u'`, and the morphism of the 2-fibre
product out of its image under `c` has `β` for its `𝒮_{X'}`-component and, for its
`[U/R]`-component, `α₀` transported along the 2-isomorphism of Stacks 046Q at `u'`
(`AlgebraicGeometry.Stack.quotientStackMap_commutes`). Its comparison square is **free**: the
2-fibre product is taken over a category fibred in sets, which is exactly what
`AlgebraicGeometry.Stack.baseChangeTwoFibreProductHom` records. Being a morphism over `f` into a
category fibred in groupoids it is strongly cartesian, so
`CategoryTheory.Functor.fiberIsoPullbackFiber` turns it into the datum that
`CategoryTheory.Functor.LocallyEssSurjOnFibers` asks for.

*Why the generic helpers.* As in the corresponding step of Stacks 04ZN
(`AlgebraicGeometry.Stack.locallyEssSurjOnFibers_functorialityComparison`),
typeclass resolution does not see through the semireducible definitions in play — `IsPreFibered`
and `IsHomLift` for the quotient stacks fail to resolve at the spellings this file needs them at,
whereas in a generic context, where the instance is a variable, they resolve syntactically. The
transport of `α₀` is likewise isolated in a lemma stated for an arbitrary morphism of groupoids,
which keeps the reading of the base change through
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.overBase` out of the main argument.

*The vacuous universe.* `AlgebraicGeometry.Stack.liftedQuotientStackToBase_obj_presented`,
`AlgebraicGeometry.Stack.liftedAssociatedMap_obj_mk` and
`AlgebraicGeometry.Stack.baseChangeQuotientStackComparison` each carry a second universe
parameter that their statements do not constrain: `CategoryTheory.ULiftHom.{w} C` is an alias for
`C`, so `w` cannot be read off a type. Every use below instantiates it explicitly, since
otherwise the elaborator leaves a universe metavariable and rejects the declaration.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 044X](https://stacks.math.columbia.edu/tag/044X)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
* [Stacks Project, Tag 048G](https://stacks.math.columbia.edu/tag/048G)
* [Stacks Project, Tag 06DV](https://stacks.math.columbia.edu/tag/06DV)
* [Stacks Project, Tag 0DTG](https://stacks.math.columbia.edu/tag/0DTG)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-! ### Generic helpers -/

/-- **A vertical morphism followed by one over `f` lies over `f`.** -/
theorem isHomLift_id_comp {𝒞 : Type*} [Category* 𝒞] {𝒳 : Type*} [Category* 𝒳]
    (p : 𝒳 ⥤ 𝒞) {U V : 𝒞} (f : V ⟶ U) {a b c : 𝒳} (k : a ⟶ b) (l : b ⟶ c)
    (hk : p.IsHomLift (𝟙 V) k) (hl : p.IsHomLift f l) : p.IsHomLift f (k ≫ l) := by
  have := hk
  have := hl
  infer_instance

/- Every morphism of a category fibred in groupoids lying over `f` is strongly cartesian
over `f`. -/
private theorem isStronglyCartesian_of_isHomLift {𝒞 : Type*} [Category* 𝒞] {𝒳 : Type*}
    [Category* 𝒳] (p : 𝒳 ⥤ 𝒞) (hp : p.IsFiberedInGroupoids) {U V : 𝒞} (f : V ⟶ U) {a b : 𝒳}
    (α : a ⟶ b) (hα : p.IsHomLift f α) : p.IsStronglyCartesian f α := by
  have := hα
  exact hp.isStronglyCartesian_homLift f α

/- **A morphism of a 2-fibre product whose first component lies over `f` lies over `f`.** The
base morphism of a morphism of the 2-fibre product is the one its first component induces. -/
private theorem isHomLift_structureFunctor_of_a {𝒞 : Type*} [Category* 𝒞] {𝒳 : Type*}
    [Category* 𝒳] {𝒴 : Type*} [Category* 𝒴] {𝒵 : Type*} [Category* 𝒵]
    {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒵 : 𝒵 ⥤ 𝒞} {K : 𝒳 ⥤ 𝒵} {L : 𝒴 ⥤ 𝒵}
    {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒵 K L} (Φ : P ⟶ Q) {R T : 𝒞} (f : R ⟶ T)
    (ha : p𝒳.IsHomLift f Φ.a) :
    (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒵 K L).IsHomLift f Φ := by
  have := ha
  have hdom : p𝒳.obj P.x = R := IsHomLift.domain_eq p𝒳 f Φ.a
  have hcod : p𝒳.obj Q.x = T := IsHomLift.codomain_eq p𝒳 f Φ.a
  have hbase : Φ.hbase =
      eqToHom (P.hx.symm.trans hdom) ≫ f ≫ eqToHom (Q.hx.symm.trans hcod).symm := by
    rw [TwoFibreProductOver.Hom.hbase_eq Φ, IsHomLift.fac' p𝒳 f Φ.a]
    simp
  refine IsHomLift.of_fac' _ f Φ (P.hx.symm.trans hdom) (Q.hx.symm.trans hcod) ?_
  rw [TwoFibreProductOver.structureFunctor_map]
  exact hbase

/- **The base-morphism condition on the two components of a morphism of a 2-fibre product.** Two
components lying over one and the same morphism of the base induce the same base morphism. Stated
over plain variables, since `CategoryTheory.IsHomLift.fac'` has to be rewritten with, and the
concrete composites below are not type-correct at the `implicit` transparency level. -/
private theorem base_eq_of_isHomLift {𝒞 : Type*} [Category* 𝒞] {𝒳 : Type*} [Category* 𝒳]
    {𝒴 : Type*} [Category* 𝒴] {𝒵 : Type*} [Category* 𝒵]
    {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒵 : 𝒵 ⥤ 𝒞} {K : 𝒳 ⥤ 𝒵} {L : 𝒴 ⥤ 𝒵}
    (P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒵 K L) {R T : 𝒞} (f : R ⟶ T)
    (a : P.x ⟶ Q.x) (b : P.y ⟶ Q.y) (ha : p𝒳.IsHomLift f a) (hb : p𝒴.IsHomLift f b) :
    eqToHom P.hy.symm ≫ p𝒴.map b ≫ eqToHom Q.hy
      = eqToHom P.hx.symm ≫ p𝒳.map a ≫ eqToHom Q.hx := by
  have := ha
  have := hb
  rw [IsHomLift.fac' p𝒴 f b, IsHomLift.fac' p𝒳 f a]
  simp

/-- **A point of a presheaf is determined by the object of the fibred category it names.** The
fibres of `AlgebraicGeometry.Stack.fibredCategory` are discrete, so an object over a test object
`V` is a `V`-point of the presheaf; this is the injectivity of that reading. -/
theorem eq_of_fibredObj_eq {Y : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    {V : BigFppfOver C S hS} {a b : Y.obj (op V)}
    (h : (⟨V, Discrete.mk a⟩ : (fibredCategory C S hS Y).val.obj) = ⟨V, Discrete.mk b⟩) :
    a = b := by
  have hs : ∀ {P Q : Σ W : BigFppfOver C S hS, Y.obj (op W)}, P = Q → HEq P.2 Q.2 := by
    intro P Q hPQ
    subst hPQ
    rfl
  exact eq_of_heq (hs (congrArg (fun z : (fibredCategory C S hS Y).val.obj =>
    (⟨z.base, z.fiber.as⟩ : Σ W : BigFppfOver C S hS, Y.obj (op W))) h))

/-! ### Stacks 046Q on a presented point -/

/-- **The map of pointwise groupoid fibrations of Stacks 046Q on a presented point.** It sends the
point of the presentation named by a `V`-point `u` of the object space to the one named by the
image of `u`. -/
theorem quotientPointwiseMap_obj_mk {G H : GroupoidInAlgebraicSpaces C S hS B}
    (h : GroupoidInAlgebraicSpaces.Hom G H) (V : BigFppfOver C S hS)
    (a : G.objects.obj.obj (op V)) :
    (quotientPointwiseMap h).obj
        (⟨V, a⟩ : (presheafOfGroupoids
          (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj) =
      ⟨V, h.toGroupoidHom.mapObjects.app (op V) a⟩ := by
  refine Pseudofunctor.CoGrothendieck.ext rfl (heq_of_eq ?_)
  change ((quotientPointwiseMapData h).val.app ⟨op V⟩).toFunctor.obj a =
    h.toGroupoidHom.mapObjects.app (op V) a
  rw [(quotientPointwiseMapData h).property.1 V]
  rfl

/-- **A morphism out of the image under the 1-morphism of Stacks 046Q of a presented object**,
from one out of the object presented by the image point. The 2-isomorphism of Stacks 046Q
identifies the two, and its components are vertical, so the morphism produced lies over the same
morphism of the site. -/
theorem exists_quotientStackMap_hom {G H : GroupoidInAlgebraicSpaces C S hS B}
    (h : GroupoidInAlgebraicSpaces.Hom G H) (V : BigFppfOver C S hS)
    (u' : G.objects.obj.obj (op V)) (u : H.objects.obj.obj (op V))
    (hu : h.toGroupoidHom.mapObjects.app (op V) u' = u)
    {x : (quotientStack H).obj} {T : BigFppfOver C S hS} (f : V ⟶ T)
    (α₀ : (pointwiseToQuotientStack H).obj
        (⟨V, u⟩ : (presheafOfGroupoids
          (evaluationGroupoidFunctor H.toGroupoidInFunctors)).obj) ⟶ x)
    (hα₀ : (quotientStack H).p.IsHomLift f α₀) :
    ∃ a : (quotientStackMap h).obj ((pointwiseToQuotientStack G).obj
        (⟨V, u'⟩ : (presheafOfGroupoids
          (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj)) ⟶ x,
      (quotientStack H).p.IsHomLift f a := by
  have hcong : (pointwiseToQuotientStack H).obj ((quotientPointwiseMap h).obj ⟨V, u'⟩) =
      (pointwiseToQuotientStack H).obj ⟨V, u⟩ :=
    congrArg (pointwiseToQuotientStack H).obj
      ((quotientPointwiseMap_obj_mk h V u').trans
        (congrArg (fun t => (⟨V, t⟩ : (presheafOfGroupoids
          (evaluationGroupoidFunctor H.toGroupoidInFunctors)).obj)) hu))
  have := hα₀
  have h₂ : (quotientStack H).p.IsHomLift f (eqToHom hcong ≫ α₀) :=
    IsHomLift.comp_eqToHom_lift (quotientStack H).p f α₀ hcong
  have hv : (quotientStack H).p.IsHomLift (𝟙 V)
      ((quotientStackMap_commutes h).inv.toNatTrans.app
        (⟨V, u'⟩ : (presheafOfGroupoids
          (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj)) :=
    (quotientStackMap_commutes h).inv.isHomLift' ⟨V, u'⟩
  exact ⟨(quotientStackMap_commutes h).inv.toNatTrans.app ⟨V, u'⟩ ≫ eqToHom hcong ≫ α₀,
    isHomLift_id_comp (quotientStack H).p f _ _ hv h₂⟩

/-! ### The local preimage -/

section BaseChange

variable (G : GroupoidInAlgebraicSpaces C S hS B) {X X' : AlgebraicSpaces C S hS}
  (XtoB : X ⟶ B) (X'toB : X' ⟶ B) (g : X' ⟶ X) (hg : g ≫ XtoB = X'toB)
  (φ : G.objects ⟶ X) (hφB : φ ≫ XtoB = G.objectsToBase)
  (hφ : Space.IsInvariant (Space.groupoidPreRelation G) φ.hom)

/- **The step of Stacks 0DTG that produces the local preimage.** Given an object `P₀` of the
2-fibre product over a test object, a morphism `f` of the site into the test object, a `V`-point
`u` of `U` and a morphism of `[U/R]` over `f` from the object it presents to the `[U/R]`-component
of `P₀`, the cartesian square of the base change produces a `V`-point `u'` of `U'` and a morphism
of the 2-fibre product over `f` out of the image under the comparison 1-morphism of the object
`u'` presents. -/
private theorem exists_hom_of_presented
    (P₀ : baseChangeTwoFibreProductObj G XtoB g φ hφB hφ) {V : BigFppfOver C S hS}
    (f : V ⟶ P₀.base)
    (u : (invariantTargetGroupoid G XtoB φ hφB hφ).objects.obj.obj (op V))
    (α₀ : (pointwiseToQuotientStack (invariantTargetGroupoid G XtoB φ hφB hφ)).obj
        (⟨V, u⟩ : (presheafOfGroupoids (evaluationGroupoidFunctor
          (invariantTargetGroupoid G XtoB φ hφB hφ).toGroupoidInFunctors)).obj) ⟶ P₀.x)
    (hα₀ : (quotientStack (invariantTargetGroupoid G XtoB φ hφB hφ)).p.IsHomLift f α₀) :
    ∃ (u' : (invariantBaseChangeGroupoid G XtoB g φ hφB hφ).objects.obj.obj (op V))
      (Φ : (baseChangeQuotientStackComparison.{u, w} G XtoB X'toB g hg φ hφB hφ).obj
          ((pointwiseToQuotientStack
            (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).obj ⟨V, u'⟩) ⟶ P₀),
      (baseChangeTwoFibreProduct G XtoB g φ hφB hφ).IsHomLift f Φ := by
  -- the cartesian lift of `f` at the `𝒮_{X'}`-component of `P₀`, and the `V`-point of `X'` it
  -- names
  obtain ⟨y₀, β, hβ⟩ := (isFiberedInGroupoids_liftedFibredCategory X').exists_lift f P₀.y P₀.hy
  obtain ⟨Vc, dpt⟩ := y₀
  obtain ⟨v'⟩ := dpt
  have hVc : V = Vc := (IsHomLift.domain_eq (liftedFibredCategory X').p f β).symm
  subst hVc
  -- the two legs over `f` into the image of `P₀.y` in the fibred category of `X`
  have h₁ : (liftedFibredCategory X).p.IsHomLift f
      ((liftedQuotientStackToBase (invariantTargetGroupoid G XtoB φ hφB hφ)).toFunctor.map α₀ ≫
        P₀.iso.hom) := by
    have := hα₀
    have := Functor.isHomLift_map_of_comp_eq
      (liftedQuotientStackToBase (invariantTargetGroupoid G XtoB φ hφB hφ)).w f α₀
    have := P₀.vertical
    infer_instance
  have h₂ : (liftedFibredCategory X).p.IsHomLift f ((liftedAssociatedMap g).toFunctor.map β) :=
    Functor.isHomLift_map_of_comp_eq (liftedAssociatedMap g).w f β
  -- the fibred category of `X` is fibred in sets, so the two sources agree: `φ(u) = g(v')`
  have hdom := obj_eq_of_isHomLift_lifted f _ _ h₁ h₂
  have hsec : (invariantTargetGroupoid G XtoB φ hφB hφ).objectsToBase.hom.app (op V) u =
      g.hom.app (op V) v' :=
    eq_of_fibredObj_eq (congrArg (liftedFibredCategoryDown X).obj
      ((liftedQuotientStackToBase_obj_presented.{u, u}
          (invariantTargetGroupoid G XtoB φ hφB hφ) V u).symm.trans
        (hdom.trans (liftedAssociatedMap_obj_mk.{u, u, u} g V v'))))
  -- the `V`-point of `U' = X' ×_X U`
  obtain ⟨u', hu₁, hu₂⟩ := Space.exists_baseChangeObjectSection
    (invariantTargetGroupoid G XtoB φ hφB hφ) g V u v' hsec
  -- the `[U/R]`-component, transported along the 2-isomorphism of Stacks 046Q
  obtain ⟨a, ha⟩ := exists_quotientStackMap_hom
    (invariantBaseChangeGroupoidHom (G := G) (XtoB := XtoB) (X'toB := X'toB)
      (g := g) (hg := hg) (φ := φ) (hφB := hφB) (hφ := hφ)) V u' u hu₁ f α₀ hα₀
  -- the `𝒮_{X'}`-component, which is the cartesian lift read through the presentation
  obtain ⟨b, hb⟩ :
      ∃ b : ((baseChangeQuotientStackComparison.{u, w} G XtoB X'toB g hg φ hφB hφ).obj
          ((pointwiseToQuotientStack
            (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).obj ⟨V, u'⟩)).y ⟶ P₀.y,
        (liftedFibredCategory X').p.IsHomLift f b := by
    refine ⟨eqToHom ?_ ≫ β, ?_⟩
    · exact (liftedQuotientStackToBase_obj_presented.{u, u}
          (invariantBaseChangeGroupoid G XtoB g φ hφB hφ) V u').trans
        (congrArg (fun t => (liftedFibredCategoryUp X').obj
          (⟨V, Discrete.mk t⟩ : (fibredCategory C S hS X'.obj).val.obj)) hu₂)
    · have := hβ
      exact IsHomLift.comp_eqToHom_lift (liftedFibredCategory X').p f β _
  -- the morphism of the 2-fibre product; its comparison square is free
  have ha' : (quotientStack (invariantTargetGroupoid G XtoB φ hφB hφ)).p.IsHomLift f a := ha
  refine ⟨u', baseChangeTwoFibreProductHom G XtoB g φ hφB hφ a b ?_, ?_⟩
  · exact base_eq_of_isHomLift
      ((baseChangeQuotientStackComparison.{u, w} G XtoB X'toB g hg φ hφB hφ).obj
        ((pointwiseToQuotientStack
          (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).obj ⟨V, u'⟩)) P₀ f a b ha' hb
  · exact isHomLift_structureFunctor_of_a _ f ha'

/-! ### Local essential surjectivity on fibres -/

/-- **The comparison 1-morphism of Stacks 0DTG is locally essentially surjective on fibres.**

For every object `P₀` of the 2-fibre product `[U/R] ×_{𝒮_X} 𝒮_{X'}` over a test object `T` there
is a covering sieve of `T` such that along each member `f : V ⟶ T` the pullback of `P₀` is
isomorphic, in the fibre over `V`, to the image under the comparison 1-morphism of an object of
`[U'/R']_V`. The sieve is the one Stacks 044X (1) supplies for the `[U/R]`-component of `P₀`, and
the object is the one presented by the `V`-point of `U' = X' ×_X U` that the cartesian square of
the base change produces.

This discharges the third hypothesis of
`AlgebraicGeometry.Stack.isTwoFibreProduct_baseChangeQuotientStackSquare`; the second is
`AlgebraicGeometry.Stack.faithful_comparison`. -/
theorem locallyEssSurjOnFibers_baseChangeQuotientStackComparison :
    Functor.LocallyEssSurjOnFibers (isFibered_baseChangeTwoFibreProduct G XtoB g φ hφB hφ)
      (isFibredOneMorphism_baseChangeQuotientStackComparison.{u, w}
        G XtoB X'toB g hg φ hφB hφ).comp_eq (BigFppfOver.topology C S hS) := by
  intro T x
  obtain ⟨P₀, hP₀⟩ := x
  subst hP₀
  obtain ⟨R₀, hR₀, hess⟩ := essImage_toQuotientStack
    (invariantTargetGroupoid G XtoB φ hφB hφ) _ ⟨P₀.x, P₀.hx⟩
  refine ⟨R₀, hR₀, ?_⟩
  intro V f hf
  obtain ⟨wfib, ⟨e⟩⟩ := hess hf
  obtain ⟨w₀, hw₀⟩ := wfib
  obtain ⟨Vb, upt⟩ := w₀
  have hVb : V = Vb := hw₀.symm
  subst hVb
  obtain ⟨u', Φ, hΦ⟩ := exists_hom_of_presented.{u, w} G XtoB X'toB g hg φ hφB hφ P₀ f upt
    (Functor.Fiber.fiberInclusion.map e.hom ≫ Functor.IsPreFibered.pullbackMap P₀.hx f)
    (isHomLift_id_comp (quotientStack (invariantTargetGroupoid G XtoB φ hφB hφ)).p f _ _
      e.hom.2 (isHomLift_pullbackMap _ P₀.hx f))
  have hfib := isFibered_baseChangeTwoFibreProduct G XtoB g φ hφB hφ
  have hzbase : (quotientStack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).p.obj
      ((pointwiseToQuotientStack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).obj
        ⟨V, u'⟩) = V :=
    BasedFunctor.w_obj (pointwiseToQuotientStackBased _) _
  exact ⟨⟨_, hzbase⟩, ⟨Functor.fiberIsoPullbackFiber
    (baseChangeTwoFibreProduct G XtoB g φ hφB hφ) ⟨P₀, rfl⟩ f _ Φ
    (isStronglyCartesian_of_isHomLift _
      (isFiberedInGroupoids_baseChangeTwoFibreProduct G XtoB g φ hφB hφ) f Φ hΦ)⟩⟩

end BaseChange

end AlgebraicGeometry.Stack

end
