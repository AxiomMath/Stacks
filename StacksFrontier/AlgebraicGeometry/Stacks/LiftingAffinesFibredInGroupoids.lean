module

public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesCategory
public import StacksFrontier.CategoryTheory.Bicategory.TwoOneCategory
public import StacksFrontier.CategoryTheory.FiberedCategory.ChoiceOfPullbacks
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.LocallyGroupoid

/-!
# The category of smooth lifts of étale opens is fibred in groupoids (Stacks 0CJT)

Fix a thickening `ι : 𝒳 ⟶ 𝒳'` of algebraic stacks over `S`, an algebraic space `W` over `S` and
a smooth 1-morphism `x : W ⟶ 𝒳`, and consider the category
`AlgebraicGeometry.Stack.EtaleSmoothLift` of smooth lifts of étale opens of `W` along `ι`
together with its projection `AlgebraicGeometry.Stack.EtaleSmoothLift.proj` to the spaces-étale
site of `W` (**Stacks 0CJP**). Stacks 0CJT says that projection is fibred in groupoids.

The source's proof has two halves. The first is that the fibre categories are groupoids: a
morphism `(f, f', γ)` whose base component `f` is an isomorphism has `f'` an isomorphism by
**Stacks 0CJC**, and then the triple is an isomorphism. The second is that the projection is a
fibred category (**Stacks 02XM**): the pullback of an object along a morphism `f : V ⟶ U` of the
site is built from the étale morphism `f' : V' ⟶ U'` restricting to `f` along the thickening
`i : U ⟶ U'`, which is **Stacks 07VW**, and the resulting morphisms are strongly cartesian
(**Stacks 02XK**) — a verification the source explicitly omits. The two halves give the
conclusion by **Stacks 003V**.

What is proved here with no hypotheses is the step that turns invertibility of the two space
components of a morphism into invertibility of the morphism itself: the inverse morphism of the
category is constructed, comparison 2-morphism and coherence condition included. The two inputs
the source draws from elsewhere are carried as hypotheses; see the implementation notes.

## Main definitions

* `AlgebraicGeometry.Stack.EtaleSmoothLift.invComm`: the comparison 2-morphism of the inverse of
  a morphism of smooth lifts whose ambient component is invertible.
* `AlgebraicGeometry.Stack.EtaleSmoothLift.invHom`: the inverse morphism itself.

## Main results

* `AlgebraicGeometry.Stack.EtaleSmoothLift.inv_coherence`: the candidate inverse satisfies the
  coherence condition of Stacks 0CJP, so it is a morphism of the category.
* `AlgebraicGeometry.Stack.EtaleSmoothLift.isIso_of_isIso_components`: a morphism of smooth lifts
  whose two space components are isomorphisms is an isomorphism. This is the step the source
  states as "and hence `(f, f', γ')` is an isomorphism", and it is proved here outright.
* `AlgebraicGeometry.Stack.EtaleSmoothLift.fiber_isGroupoid`: **Stacks 0CJT**, the fibre
  categories of the projection are groupoids.
* `AlgebraicGeometry.Stack.EtaleSmoothLift.isFiberedInGroupoids`: **Stacks 0CJT**, the projection
  is fibred in groupoids.

## Implementation notes

**The carried hypothesis `hiso`, and what it is.** `hiso` is the isomorphism clause of
**Stacks 0CJC** — item (2) of its list, the sub-tag **0CJE** — for the thickening `ι`, written out
for the category of smooth lifts: if the base component `f : U ⟶ V` of a morphism of smooth lifts
is an isomorphism then so is its ambient component `f' : U' ⟶ V'`. It says nothing about lifting
or cartesianness, so it is not part of the conclusion. **Stacks 0CJC** is the tag that would
discharge it, and it is carried because that clause is not available in this repository:

* the clauses proved in
  `StacksFrontier.AlgebraicGeometry.Stacks.ThickeningDeformationProperties` are flatness, smoothness
  and syntomicity, and no `@[stacks 0CJE]` attribute exists anywhere in the tree;
* the general engine behind those three,
  `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_iff_of_flatDeformation`, cannot produce
  it: its first hypothesis is `Space.IsSmoothLocalOnSourceAndTarget B S hS P`, and being an
  isomorphism is not a property smooth local on the source-and-target;
* the source proves item (2) by a different route — representability by algebraic spaces
  (**Stacks 0CJ9**), descent along a smooth chart (**Stacks 04XD**), and then the
  algebraic-spaces isomorphism clause, which is item (3) of **Stacks 0CGX**. That clause is
  itself not formalized: `StacksFrontier.AlgebraicGeometry.Spaces.Deformations.FlatDeformation`
  proves items (2), (9), (12), (15), (16), (17) and (18) of 0CGX and no isomorphism item.

The companion file `StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesEtaleMorphism` carries the
étale clause of the same lemma for the same reason.

**The carried hypothesis `hfib`, and what it is.** `hfib` is the statement that the projection is
a fibred category — **Stacks 02XM**, stated as
`CategoryTheory.Functor.IsFibredCategory`: every morphism of the spaces-étale site of `W` has a
strongly cartesian lift. It is carried because its substantive input is the topological
invariance of the small étale site along the thickening `i : U ⟶ U'`, **Stacks 07VW**, in a form
this repository does not have. Every available form of that invariance asks the thickening to be
*first order* —
`AlgebraicGeometry.Space.isEquivalence_spacesBaseChange_of_isFirstOrderThickening` and
`AlgebraicGeometry.Space.essSurj_spacesBaseChange_of_isFirstOrderThickening` (**Stacks 05ZH**),
and `AlgebraicGeometry.Space.fullyFaithfulSpacesBaseChangeOfIsFirstOrderThickening` — whereas the
thickening attached to an object of Stacks 0CJP is an arbitrary one. Building the pullback object
also needs the 2-fibre product condition `V = 𝒳 ×_{𝒳'} V'` transported along the cartesian square
`V = U ×_{U'} V'`, and the strongly cartesian verification is the one the source omits.
**Stacks 07VW** is the tag that would discharge it.

The two carried hypotheses have one root cause. `hiso` is the full-faithfulness half of that same
invariance read off at `ι`: full faithfulness of base change along `ι` makes `f ↦ f'` a bijection
on morphisms, under which an isomorphism on one side is an isomorphism on the other. So both
hypotheses fall as soon as **Stacks 07VW** is available for a thickening that is not first order.

`hfib` is not the conclusion in disguise. It supplies existence of strongly cartesian lifts; the
conclusion `CategoryTheory.Functor.IsFiberedInGroupoids` (**Stacks 003S**) additionally demands
that fill-ins be unique, and that is exactly what the groupoid-fibre half proved here provides,
through `CategoryTheory.Functor.IsFiberedInGroupoids.mk'` (**Stacks 003V**).

**Term mode and strictness.** As in
`StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesCategory`, the purely categorical bookkeeping
is isolated as lemmas about an arbitrary category or bicategory, where the rewriting tactics
work. Inside the 2-category `AlgebraicGeometry.Stack.AlgebraicStacks` the reassociation of a
composite of 1-morphisms and the exchange of `(p ≫ q) ◁ θ` with `p ◁ (q ◁ θ)` are definitional,
because that 2-category is a strict bicategory, so those steps are left to definitional equality
rather than rewritten.

**Invertibility of 2-morphisms.** The comparison 2-morphism of a morphism of smooth lifts is
inverted without any hypothesis: `AlgebraicGeometry.Stack.AlgebraicStacks` is a full
sub-2-category of the 2-category of categories fibred in groupoids, whose hom-categories are
groupoids by `CategoryTheory.CatFiberedInGroupoids.homGroupoid`, and
`CategoryTheory.Bicategory.InducedBicategory.homGroupoid` carries that to the sub-2-category.

**Direction convention.** The covariant labelling of
`StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesCategory` is inherited: a morphism out of the
object carrying `U` carries `f : U ⟶ V`, and the projection sends it to `f`.

## References

* [Stacks Project, Tag 003S](https://stacks.math.columbia.edu/tag/003S)
* [Stacks Project, Tag 003V](https://stacks.math.columbia.edu/tag/003V)
* [Stacks Project, Tag 02XK](https://stacks.math.columbia.edu/tag/02XK)
* [Stacks Project, Tag 02XM](https://stacks.math.columbia.edu/tag/02XM)
* [Stacks Project, Tag 04XD](https://stacks.math.columbia.edu/tag/04XD)
* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 07VW](https://stacks.math.columbia.edu/tag/07VW)
* [Stacks Project, Tag 0CGX](https://stacks.math.columbia.edu/tag/0CGX)
* [Stacks Project, Tag 0CJ9](https://stacks.math.columbia.edu/tag/0CJ9)
* [Stacks Project, Tag 0CJC](https://stacks.math.columbia.edu/tag/0CJC)
* [Stacks Project, Tag 0CJE](https://stacks.math.columbia.edu/tag/0CJE)
* [Stacks Project, Tag 0CJP](https://stacks.math.columbia.edu/tag/0CJP)
* [Stacks Project, Tag 0CJT](https://stacks.math.columbia.edu/tag/0CJT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Bicategory

namespace CategoryTheory

/-- **Cancelling an inverse at the end of a two-step composite.** If `b ≫ e` factors as `r ≫ t`
through an invertible `t`, then composing `b` with `e` and the inverse of `t` is `r`. -/
theorem comp_comp_inv_eq {C : Type*} [Category C] {A A' D E : C} (b : A ⟶ A') (e : A' ⟶ D)
    {t : E ⟶ D} [IsIso t] {r : A ⟶ E} (h : b ≫ e = r ≫ t) : b ≫ (e ≫ inv t) = r := by
  rw [← Category.assoc, h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- **Three commuting squares of transports compose to one.** This is the transport bookkeeping
behind the coherence condition of the inverse of a morphism of smooth lifts: `r1` is the coherence
of the given morphism whiskered by the inverse base component, `r2` relates the two ways of
whiskering the comparison 2-morphism, and `r3` collapses the whiskering by the composite of the
base component and its inverse. All objects are 1-morphisms of a 2-category and all morphisms are
2-morphisms, so the statement is one about an arbitrary category. -/
theorem comp_eqToHom_cancel {C : Type*} [Category C]
    {Q JY gLP gLIX JgAX gLIfAY JgAfAY gLfLQ gLfLJY : C}
    {hq : Q = gLP} {hc3 : gLIX = JgAX} {hc : JY = JgAfAY}
    {hc1 : gLP = gLfLQ} {hc2 : gLfLJY = gLIfAY} {hc4 : gLIfAY = JgAfAY}
    {hE1 : gLfLQ = Q} {hE2 : gLfLJY = JY}
    {b : Q ⟶ JY} {a : gLP ⟶ gLIX} {g : gLIX ⟶ gLIfAY} {t : JgAX ⟶ JgAfAY}
    {w : gLfLQ ⟶ gLfLJY}
    (r1 : a ≫ g = eqToHom hc1 ≫ w ≫ eqToHom hc2)
    (r2 : eqToHom hc3 ≫ t = g ≫ eqToHom hc4)
    (r3 : eqToHom hE1 ≫ b = w ≫ eqToHom hE2) :
    b ≫ eqToHom hc = (eqToHom hq ≫ a ≫ eqToHom hc3) ≫ t := by
  subst hq
  subst hc1
  subst hE2
  subst hc2
  subst hc
  subst hc3
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at r1 r2 r3 ⊢
  rw [r3, r2, r1]

/-- **A morphism followed by a transported inverse of itself is a transport.** If `iw` is the
inverse of `g` up to the two transports of `r`, then `g` followed by `iw`, flanked by transports,
is the transport between the outer objects. -/
theorem comp_eqToHom_comp_inv {C : Type*} [Category C]
    {X fAY fAgAfAY fAgAX T : C}
    {c : fAY = fAgAfAY} {hE : fAgAX = X} {hD : fAgAfAY = fAY}
    {h : fAgAX = T} {h0 : X = T}
    {g : X ⟶ fAY} [IsIso g] {iw : fAgAfAY ⟶ fAgAX}
    (r : iw ≫ eqToHom hE = eqToHom hD ≫ inv g) :
    (g ≫ (eqToHom c ≫ iw)) ≫ eqToHom h = eqToHom h0 := by
  subst c
  subst hE
  subst h0
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at r ⊢
  simp [r]

/-- **A morphism with a right inverse that itself has a right inverse is invertible.** From
`f ≫ g = 𝟙` and `g ≫ k = 𝟙` one gets `f = k`, hence `g` is a two-sided inverse of `f`. -/
theorem isIso_of_comp_id_of_comp_id {C : Type*} [Category C] {A A' : C}
    (f : A ⟶ A') (g : A' ⟶ A) (k : A ⟶ A')
    (h1 : f ≫ g = 𝟙 A) (h2 : g ≫ k = 𝟙 A') : IsIso f := by
  have hfk : f = k := by
    rw [← Category.comp_id f, ← h2, ← Category.assoc, h1, Category.id_comp]
  exact ⟨g, h1, by rw [hfk]; exact h2⟩

/-- **Two morphisms whose codomains agree up to an equality are heterogeneously equal** as soon as
one is the other followed by the transport along that equality. -/
theorem heq_of_comp_eqToHom {C : Type*} [Category C] {A U V : C} (h : U = V)
    (t : A ⟶ U) (t' : A ⟶ V) (e : t ≫ eqToHom h = t') : HEq t t' := by
  subst h
  simp only [eqToHom_refl, Category.comp_id] at e
  exact heq_of_eq e

namespace Bicategory

/-- **Left whiskering commutes with inverting a 2-morphism.** -/
theorem whiskerLeft_inv {Bc : Type*} [Bicategory Bc] {A C D : Bc} (p : A ⟶ C) {v v' : C ⟶ D}
    (t : v ⟶ v') [IsIso t] : p ◁ inv t = inv (p ◁ t) := by simp

end Bicategory

end CategoryTheory

namespace AlgebraicGeometry.Space.SpacesEtale

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} {U V : SpacesEtale B S hS X}

/-- **The underlying morphism of algebraic spaces of an invertible morphism of the spaces-étale
site is invertible.** The inverse is the underlying morphism of the inverse, since the two
identities are read off componentwise. -/
theorem isIso_hom_left (f : U ⟶ V) [IsIso f] : IsIso f.hom.left :=
  ⟨(inv f).hom.left, congrArg (fun k : U ⟶ U => k.hom.left) (IsIso.hom_inv_id f),
    congrArg (fun k : V ⟶ V => k.hom.left) (IsIso.inv_hom_id f)⟩

/-- **Taking the underlying morphism of algebraic spaces commutes with inverting.** -/
theorem inv_hom_left (f : U ⟶ V) [IsIso f] :
    letI := isIso_hom_left f
    (inv f).hom.left = inv f.hom.left := by
  let := isIso_hom_left f
  exact (IsIso.inv_eq_of_hom_inv_id
    (congrArg (fun k : U ⟶ U => k.hom.left) (IsIso.hom_inv_id f))).symm

/-- **The underlying morphisms of algebraic spaces of an inverse and of the morphism compose to
the identity.** -/
theorem inv_hom_left_comp (f : U ⟶ V) [IsIso f] : (inv f).hom.left ≫ f.hom.left = 𝟙 _ :=
  congrArg (fun k : V ⟶ V => k.hom.left) (IsIso.inv_hom_id f)

end AlgebraicGeometry.Space.SpacesEtale

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} {ι : 𝒳 ⟶ 𝒳'} {hι : IsThickening ι}
  {W : AlgebraicSpaces B S hS}
  {x : (algebraicSpaceStackFunctor B S hS).obj W ⟶ 𝒳}
  {hx : AlgebraicStacks.IsSmooth B S hS x}

namespace EtaleSmoothLift

variable {ξ η : EtaleSmoothLift B S hS ι hι W x hx}

/-- **The base component of a morphism of smooth lifts and its inverse compose to the identity**,
read in the 2-category of algebraic stacks. -/
theorem map_inv_hom_left_comp (m : ξ ⟶ η) [IsIso (Hom.base m)] :
    (algebraicSpaceStackFunctor B S hS).map (inv (Hom.base m)).hom.left ≫
        (algebraicSpaceStackFunctor B S hS).map (Hom.base m).hom.left = 𝟙 _ := by
  rw [← CategoryTheory.Functor.map_comp, Space.SpacesEtale.inv_hom_left_comp,
    CategoryTheory.Functor.map_id]

/-- **The inverse of the ambient component followed by the ambient component is the identity**,
read in the 2-category of algebraic stacks. -/
theorem map_inv_ambient_comp (m : ξ ⟶ η) [IsIso (Hom.ambient m)] :
    (algebraicSpaceStackFunctor B S hS).map (inv (Hom.ambient m)) ≫
        (algebraicSpaceStackFunctor B S hS).map (Hom.ambient m) = 𝟙 _ := by
  rw [← CategoryTheory.Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id]

/-- **The ambient component followed by its inverse is the identity**, read in the 2-category of
algebraic stacks. -/
theorem map_ambient_inv_comp (m : ξ ⟶ η) [IsIso (Hom.ambient m)] :
    (algebraicSpaceStackFunctor B S hS).map (Hom.ambient m) ≫
        (algebraicSpaceStackFunctor B S hS).map (inv (Hom.ambient m)) = 𝟙 _ := by
  rw [← CategoryTheory.Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id]

/-- **The target's ambient 1-morphism factors through the inverse of the ambient component.**
This is the equality of 1-morphisms along which the comparison 2-morphism of the inverse is
transported. -/
theorem ambientMap_eq_inv_comp (m : ξ ⟶ η) [IsIso (Hom.ambient m)] :
    η.ambientMap =
      (algebraicSpaceStackFunctor B S hS).map (inv (Hom.ambient m)) ≫
        ((algebraicSpaceStackFunctor B S hS).map (Hom.ambient m) ≫ η.ambientMap) :=
  (congrArg (· ≫ η.ambientMap) (map_inv_ambient_comp m)).symm

/-- **The restriction equation for the inverse of a morphism of smooth lifts.** If `f' : U' ⟶ V'`
restricts to `f : U ⟶ V` and both are invertible, then the inverse of `f'` restricts to the
inverse of `f`. -/
theorem inv_inclusion_comp (m : ξ ⟶ η) [IsIso (Hom.base m)] [IsIso (Hom.ambient m)] :
    η.inclusion ≫ inv (Hom.ambient m) = (inv (Hom.base m)).hom.left ≫ ξ.inclusion := by
  let := Space.SpacesEtale.isIso_hom_left (Hom.base m)
  rw [Space.SpacesEtale.inv_hom_left, IsIso.eq_inv_comp, ← Category.assoc,
    ← Hom.inclusion_comp m, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- **The comparison 2-morphism of the inverse of a morphism of smooth lifts.** It is the inverse
of the given comparison 2-morphism `γ`, whiskered by the inverse of the ambient component and
transported along `AlgebraicGeometry.Stack.EtaleSmoothLift.ambientMap_eq_inv_comp`. The
2-morphism `γ` is invertible because the 2-category of algebraic stacks is locally groupoidal. -/
def invComm (m : ξ ⟶ η) [IsIso (Hom.ambient m)] :
    η.ambientMap ⟶
      (algebraicSpaceStackFunctor B S hS).map (inv (Hom.ambient m)) ≫ ξ.ambientMap :=
  eqToHom (ambientMap_eq_inv_comp m) ≫
    ((algebraicSpaceStackFunctor B S hS).map (inv (Hom.ambient m)) ◁ inv (Hom.comm m))

/-- **The candidate inverse of a morphism of smooth lifts satisfies the coherence condition of
Stacks 0CJP.** The coherence of the given morphism, whiskered by the inverse of its base
component, becomes the coherence of the inverse once the whiskering by the composite of the base
component and its inverse is collapsed and the comparison 2-morphism is cancelled against its
inverse. -/
theorem inv_coherence (m : ξ ⟶ η) [IsIso (Hom.base m)] [IsIso (Hom.ambient m)] :
    η.comm.hom ≫ ((algebraicSpaceStackFunctor B S hS).map η.inclusion ◁ invComm m) =
      eqToHom (left_leg η ξ (inv (Hom.base m))) ≫
        ((algebraicSpaceStackFunctor B S hS).map (inv (Hom.base m)).hom.left ◁ ξ.comm.hom) ≫
          eqToHom (right_leg η ξ (inv (Hom.base m)) (inv (Hom.ambient m))
            (inv_inclusion_comp m)) := by
  have r1 :
      ((algebraicSpaceStackFunctor B S hS).map (inv (Hom.base m)).hom.left ◁ ξ.comm.hom) ≫
          ((algebraicSpaceStackFunctor B S hS).map (inv (Hom.base m)).hom.left ◁
            ((algebraicSpaceStackFunctor B S hS).map ξ.inclusion ◁ Hom.comm m)) =
        eqToHom (congrArg
            (fun p => (algebraicSpaceStackFunctor B S hS).map (inv (Hom.base m)).hom.left ≫ p)
            (left_leg ξ η (Hom.base m))) ≫
          (((algebraicSpaceStackFunctor B S hS).map (inv (Hom.base m)).hom.left ≫
            (algebraicSpaceStackFunctor B S hS).map (Hom.base m).hom.left) ◁ η.comm.hom) ≫
            eqToHom (congrArg
              (fun p => (algebraicSpaceStackFunctor B S hS).map (inv (Hom.base m)).hom.left ≫ p)
              (right_leg ξ η (Hom.base m) (Hom.ambient m) (Hom.inclusion_comp m))) :=
    (Bicategory.whiskerLeft_comp _ ξ.comm.hom _).symm.trans
      ((congrArg
          (fun tt =>
            (algebraicSpaceStackFunctor B S hS).map (inv (Hom.base m)).hom.left ◁ tt)
          (Hom.coherence m)).trans
        (Bicategory.whiskerLeft_eqToHom_comp_eqToHom _ (left_leg ξ η (Hom.base m)) _
          (right_leg ξ η (Hom.base m) (Hom.ambient m) (Hom.inclusion_comp m))))
  have r2 := Bicategory.eqToHom_whiskerLeft_naturality
    (lift_leg η ξ (inv (Hom.base m)) (inv (Hom.ambient m)) (inv_inclusion_comp m)) (Hom.comm m)
  have r3 := Bicategory.eqToHom_whiskerLeft_naturality (map_inv_hom_left_comp m) η.comm.hom
  rw [invComm, Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom,
    Bicategory.whiskerLeft_inv, Bicategory.whiskerLeft_inv]
  exact comp_comp_inv_eq _ _ (comp_eqToHom_cancel r1 r2 r3)

/-- **The inverse of a morphism of smooth lifts whose two space components are invertible.** Its
space components are the inverses of theirs and its comparison 2-morphism is
`AlgebraicGeometry.Stack.EtaleSmoothLift.invComm`. -/
def invHom (m : ξ ⟶ η) [IsIso (Hom.base m)] [IsIso (Hom.ambient m)] : η ⟶ ξ where
  base := inv (Hom.base m)
  ambient := inv (Hom.ambient m)
  inclusion_comp := inv_inclusion_comp m
  comm := invComm m
  coherence := inv_coherence m

/-- **The comparison 2-morphism of a morphism composed with its inverse is the one of the
identity.** The whiskered inverse cancels the comparison 2-morphism, leaving a composite of
transports. -/
theorem comp_invComm (m : ξ ⟶ η) [IsIso (Hom.ambient m)] :
    (Hom.comm m ≫ ((algebraicSpaceStackFunctor B S hS).map (Hom.ambient m) ◁ invComm m)) ≫
        eqToHom (congrArg
          (fun k => (algebraicSpaceStackFunctor B S hS).map k ≫ ξ.ambientMap)
          (IsIso.hom_inv_id (Hom.ambient m))) =
      eqToHom (ambientMap_eq_map_id_comp ξ) := by
  have r := (Bicategory.eqToHom_whiskerLeft_naturality (map_ambient_inv_comp m)
    (inv (Hom.comm m))).symm
  rw [invComm, Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom]
  exact comp_eqToHom_comp_inv r

/-- **A morphism of smooth lifts composed with its inverse is the identity.** The three
components agree with those of the identity morphism, so
`AlgebraicGeometry.Stack.EtaleSmoothLift.hom_congr` applies. -/
theorem comp_invHom (m : ξ ⟶ η) [IsIso (Hom.base m)] [IsIso (Hom.ambient m)] :
    m ≫ invHom m = 𝟙 ξ :=
  hom_congr _ _ (IsIso.hom_inv_id (Hom.base m)) (IsIso.hom_inv_id (Hom.ambient m))
    (heq_of_comp_eqToHom _ _ _ (comp_invComm m))

/-- **A morphism of smooth lifts whose two space components are isomorphisms is an
isomorphism.** This is the step the source states as "and hence `(f, f', γ')` is an isomorphism".
The inverse is `AlgebraicGeometry.Stack.EtaleSmoothLift.invHom`; the second identity comes from
the first one applied to that inverse, whose own components are invertible. -/
theorem isIso_of_isIso_components (m : ξ ⟶ η) [IsIso (Hom.base m)] [IsIso (Hom.ambient m)] :
    IsIso m := by
  have h1 : IsIso (Hom.base (invHom m)) := inferInstanceAs (IsIso (inv (Hom.base m)))
  have h2 : IsIso (Hom.ambient (invHom m)) := inferInstanceAs (IsIso (inv (Hom.ambient m)))
  exact isIso_of_comp_id_of_comp_id m (invHom m) (invHom (invHom m)) (comp_invHom m)
    (comp_invHom (invHom m))

/-- **A morphism of smooth lifts lying over an identity of the spaces-étale site has an
invertible base component.** The base component is the image of the morphism under the
projection, which lies over the identity and is therefore a composite of transports. -/
theorem isIso_base_of_isHomLift {U : Space.SpacesEtale B S hS W} (m : ξ ⟶ η)
    (hm : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsHomLift (𝟙 U) m) :
    IsIso (Hom.base m) := by
  have := hm
  have hdom : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).obj ξ = U :=
    IsHomLift.domain_eq _ (𝟙 U) m
  have hcod : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).obj η = U :=
    IsHomLift.codomain_eq _ (𝟙 U) m
  have hfac : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).map m =
      eqToHom hdom ≫ 𝟙 U ≫ eqToHom hcod.symm := IsHomLift.fac' _ (𝟙 U) m
  have h : IsIso ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).map m) := by
    rw [hfac]; infer_instance
  exact h

/-- **Stacks 0CJT, the fibre categories are groupoids.** A morphism of the fibre over an étale
open `U` of `W` lies over the identity of `U`, so its base component is invertible; its ambient
component is then invertible by `hiso`, and
`AlgebraicGeometry.Stack.EtaleSmoothLift.isIso_of_isIso_components` makes the morphism itself
invertible.

The hypothesis `hiso` is the isomorphism clause of **Stacks 0CJC** for the thickening `ι`,
written out for this category: if the base component of a morphism of smooth lifts is an
isomorphism then so is its ambient component. It is carried because that clause of 0CJC is not
available here — see the implementation notes — and **Stacks 0CJC** is the tag that would
discharge it. -/
@[stacks 0CJT "the fibre categories are groupoids"]
theorem fiber_isGroupoid
    (hiso : ∀ (ζ ζ' : EtaleSmoothLift B S hS ι hι W x hx) (n : ζ ⟶ ζ'),
      IsIso (Hom.base n) → IsIso (Hom.ambient n))
    (U : Space.SpacesEtale B S hS W) :
    IsGroupoid ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) where
  all_isIso {a b} f := by
    set φ : (Functor.Fiber.fiberInclusion
        (p := (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _)) (S := U)).obj a ⟶
        (Functor.Fiber.fiberInclusion
          (p := (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _)) (S := U)).obj b :=
      Functor.Fiber.fiberInclusion.map f with hφ
    have hb : IsIso (Hom.base φ) := isIso_base_of_isHomLift φ f.2
    have ha : IsIso (Hom.ambient φ) := hiso _ _ φ hb
    have hf : IsIso φ := isIso_of_isIso_components φ
    have hinv : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsHomLift (𝟙 U) (inv φ) := by
      simpa using IsHomLift.inv
        (p := (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _)) (f := 𝟙 U) (φ := φ)
    refine ⟨⟨⟨_, hinv⟩, ?_, ?_⟩⟩ <;> apply Functor.Fiber.fiberInclusion.map_injective
    · exact IsIso.hom_inv_id φ
    · exact IsIso.inv_hom_id φ

/-- **Stacks 0CJT.** The category of smooth lifts of the étale opens of `W` along the thickening
`ι`, projected to the spaces-étale site of `W`, is fibred in groupoids. The fibre categories are
groupoids by `AlgebraicGeometry.Stack.EtaleSmoothLift.fiber_isGroupoid`, and that together with
the fibred-category half gives the conclusion by **Stacks 003V**.

Two hypotheses are carried. The first, `hiso`, is the isomorphism clause of **Stacks 0CJC** for
`ι`; see `AlgebraicGeometry.Stack.EtaleSmoothLift.fiber_isGroupoid`. The second, `hfib`, is that
the projection is a fibred category, which is **Stacks 02XM** in the source's own words, stated
here as `CategoryTheory.Functor.IsFibredCategory` and converted to Mathlib's class by
`CategoryTheory.Functor.isFibredCategory_iff_isFibered`: every morphism of the spaces-étale site
of `W` has a strongly cartesian lift. It is carried because its substantive input is the
topological invariance of the small étale site along an arbitrary thickening, **Stacks 07VW**,
which is not available here — every available form of it asks the thickening to be first order — and
because the source omits the strongly cartesian verification itself. **Stacks 07VW** is the tag
that would discharge it; see the implementation notes for the full evidence. What `hfib` supplies
is existence of strongly cartesian lifts; the uniqueness of fill-ins demanded by **Stacks 003S**
is supplied by the groupoid-fibre half proved here. -/
@[stacks 0CJT "fibred in groupoids, granted the fibred-category half"]
theorem isFiberedInGroupoids
    (hiso : ∀ (ζ ζ' : EtaleSmoothLift B S hS ι hι W x hx) (n : ζ ⟶ ζ'),
      IsIso (Hom.base n) → IsIso (Hom.ambient n))
    (hfib : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsFibredCategory) :
    (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsFiberedInGroupoids :=
  letI := (Functor.isFibredCategory_iff_isFibered _).mp hfib
  Functor.IsFiberedInGroupoids.mk' (fiber_isGroupoid hiso)

end EtaleSmoothLift

end AlgebraicGeometry.Stack

end
