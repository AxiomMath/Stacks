module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionAssociativity
import StacksCore.Tactic.StacksAttribute

/-!
# Pasting of derived base change maps

Two commutative squares of ringed spaces sharing an edge paste to a rectangle, and the derived
base change map of Tag 08HY for the rectangle is the composite of the base change maps of the two
squares.  Both arrangements are proved here.

Stacked vertically,

```
X' --k--> X
|f'       |f
Y' --l--> Y
|g'       |g
Z' --m--> Z
```

the two base change maps compose through the composition isomorphisms of Tag 079W for derived
pushforward along `f ≫ g` and along `f' ≫ g'`.  This is Tag 0ATL.

Placed side by side,

```
X'' --g'--> X' --g--> X
|f''        |f'       |f
Y'' --h'--> Y' --h--> Y
```

they compose through the composition isomorphisms of Tag 0D5S for derived pullback along
`h' ≫ h` and along `g' ≫ g`.  This is Tag 0ATM.

## Main results

* `Stacks.Cohomology.DerivedBaseChange.derivedPullbackSquare_paste`: the comparison of iterated
  derived pullbacks around the outer rectangle is the vertical composite of the comparisons for
  the two squares, whiskered with the composition isomorphisms of Tag 0D5S.  This is the
  geometric input, and it is the first pasting statement of its kind here.
* `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeSquare_paste`: the same for the derived
  base change morphisms of functors, as an identity of 2-squares.
* `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_comp`: **Tag 0ATL**, the identity at
  an object of the unbounded derived category.
* `Stacks.Cohomology.DerivedBaseChange.derivedPullbackSquare_hpaste`: for two horizontally
  composable squares, the comparison of iterated derived pullbacks around the outer rectangle is
  the horizontal composite of the comparisons for the two squares, whiskered at the top and at
  the bottom with the composition isomorphisms of Tag 0D5S.
* `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeSquare_hpaste`: the same for the derived
  base change morphisms of functors, as an identity of 2-squares.
* `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_comp_horizontal`: **Tag 0ATM**, the
  identity at an object of the unbounded derived category.

## Route

For the vertical pasting, the derived base change morphism is the mate of
`derivedPullbackSquare` under the two derived adjunctions of Tag 079W, so the statement about
base change maps is Mathlib's
`CategoryTheory.mateEquiv_hcomp` — mates turn vertical composition of squares of left adjoints
into horizontal composition of squares of right adjoints — once the derived adjunction for
`f ≫ g` has been traded for the composite of the derived adjunctions for `f` and for `g`.  That
trade is `CategoryTheory.mateEquiv_conjugateEquiv_vcomp` and
`CategoryTheory.conjugateEquiv_mateEquiv_vcomp`, which replace a whiskering of a 2-square by a
whiskering of its mate with the conjugate transformation; the two conjugates in question are
computed by `conjugateEquiv_derivedPullbackCompIsoCanonical_inv` of
`Stacks.Cohomology.DerivedPushforwardAssociativity` and, in the other direction, by
`conjugateEquiv_derivedPullbackCompIsoCanonical_hom` below.

`derivedPullbackSquare_paste` is the one step with genuine content.  Both bracketings of the
threefold iterated derived pullback around the rectangle are compared with the derived pullback
along the common composite, and the two comparisons agree by the cocycle identity
`Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackCompIsoCanonical_assoc` of Tag
0D5S, used three times.  Unlike on the derived pushforward side, transports along equalities of
morphisms do appear: `derivedPullbackCompIsoLeft` carries one for each square, and the identity
holds because the three transports compose.

The horizontal pasting needs no such trade of adjunctions: horizontal composition of 2-squares
shares the middle vertical leg instead of composing it, so the three derived adjunctions along
`f`, `f'` and `f''` enter unchanged and the mate step is Mathlib's
`CategoryTheory.mateEquiv_vcomp` together with `mateEquiv_whiskerTopBottom`, which says that
whiskering a 2-square at its top and bottom — the two legs the mates correspondence carries over
unchanged — whiskers its mate at the right and at the left.  Again the content is on the derived
pullback side, in `derivedPullbackSquare_hpaste`: the cocycle identity of Tag 0D5S for
`f'' ≫ h' ≫ h`, for `g' ≫ f' ≫ h` and for `g' ≫ g ≫ f`, and the two transports along the
commutativity of the squares contracting into the transport for the rectangle.

## Implementation notes

*Why the chase is hoisted.*  Every morphism occurring in the component identity is a derived
functor evaluated on an unbounded derived category, and reassociating such a composite inside
the goal exhausts the elaborator: the object between two neighbouring factors is spelled as a
composite functor applied to an object on one side and as the iterated application on the other.
The abstract chase lemmas therefore carry out the whole rearrangement with every subterm a
variable, and the unifier reconciles the two spellings at the application site.

*Why the transports are read at a complex.*  `derivedPullbackCompIsoLeft` is built from
`eqToIso (congrArg derivedPullback _)`, a transport between two *functors*, and
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback` is a reducible abbreviation
over a total derived functor: deciding such an equality of functors makes the kernel unfold the
abbreviation, and one occurrence exhausts its budget.  `eqToIso_derivedPullback_hom_app` turns
each transport into an `eqToHom` between objects of the derived category once and for all, and
the chase then runs on objects, where the comparison is immediate.

## References

* [Stacks Project, Tag 0ATL](https://stacks.math.columbia.edu/tag/0ATL)
* [Stacks Project, Tag 0ATM](https://stacks.math.columbia.edu/tag/0ATM)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.TwoSquare
open RingedSpaceModuleAdjunction
open Stacks.DerivedPullback.Composition
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedPushforwardAssociativity
  (derivedPullbackCompIsoCanonical_assoc derivedPullbackCompIsoCanonical_assoc_app
    conjugateEquiv_derivedPullbackCompIsoCanonical_inv)

namespace Stacks.Cohomology.DerivedBaseChange

universe u

attribute [local instance] HasDerivedCategory.standard

noncomputable section

/-! ### Abstract bookkeeping -/

/-- Pasting of 2-squares, reduced to one identity of morphisms at each object.

An identity between an outer 2-square and the vertical composite of two inner ones, whiskered
with comparisons of the two composite legs, is componentwise exactly the factorization of the
outer square's component into the four factors on the right. -/
private theorem twoSquare_paste_of_app {A B C D E F : Type*} [Category A] [Category B]
    [Category C] [Category D] [Category E] [Category F]
    {Tl : A ⥤ B} {Ll : A ⥤ C} {Rl : B ⥤ D} {Tu : C ⥤ D} {Lu : C ⥤ E} {Ru : D ⥤ F}
    {Bu : E ⥤ F} {Lo : A ⥤ E} {Ro : B ⥤ F} {Cl Pl : A ⥤ D} {Cu Pu : C ⥤ F} {Co Po : A ⥤ F}
    (ego₁ : Tl ⋙ Ro ⟶ Po) (ego₂ : Po ⟶ Co) (efo : Co ⟶ Lo ⋙ Bu) (eg₂₁ : Tl ⋙ Rl ⟶ Pl)
    (eg₂₂ : Pl ⟶ Cl) (ef₂ : Cl ⟶ Ll ⋙ Tu) (eg₁₁ : Tu ⋙ Ru ⟶ Pu) (eg₁₂ : Pu ⟶ Cu)
    (ef₁ : Cu ⟶ Lu ⋙ Bu) (cL : Ll ⋙ Lu ⟶ Lo) (cR : Ro ⟶ Rl ⋙ Ru)
    (d₀ : ∀ M, Po.obj M ⟶ Co.obj M) (hd₀ : ∀ M, ego₂.app M = d₀ M)
    (d₂ : ∀ M, Pl.obj M ⟶ Cl.obj M) (hd₂ : ∀ M, eg₂₂.app M = d₂ M)
    (d₁ : ∀ N, Pu.obj N ⟶ Cu.obj N) (hd₁ : ∀ N, eg₁₂.app N = d₁ N)
    (h : ∀ M, ego₁.app M ≫ d₀ M ≫ efo.app M = cR.app (Tl.obj M) ≫
      Ru.map (eg₂₁.app M) ≫ Ru.map (d₂ M) ≫ Ru.map (ef₂.app M) ≫
      eg₁₁.app (Ll.obj M) ≫ d₁ (Ll.obj M) ≫ ef₁.app (Ll.obj M) ≫ Bu.map (cL.app M)) :
    TwoSquare.mk Tl Lo Ro Bu ((ego₁ ≫ ego₂) ≫ efo) =
      ((TwoSquare.mk Tl Ll Rl Tu ((eg₂₁ ≫ eg₂₂) ≫ ef₂) ≫ᵥ
        TwoSquare.mk Tu Lu Ru Bu ((eg₁₁ ≫ eg₁₂) ≫ ef₁)).whiskerLeft cL).whiskerRight cR := by
  refine TwoSquare.ext _ _ fun M => ?_
  have hM := h M
  rw [← hd₀ M, ← hd₂ M, ← hd₁ (Ll.obj M)] at hM
  simpa [TwoSquare.vComp, TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
    Category.assoc] using hM

/-- Reading an identity `A ≫ B = C ≫ D` with `A` and `D` invertible as `A⁻¹ ≫ C = B ≫ D⁻¹`.

Stated on variables: the morphisms it is applied to are components of comparison isomorphisms
between composites of derived functors, and the rearrangement is unaffordable in place. -/
private theorem inv_comp_eq_comp_inv {E : Type*} [Category E] {V₁ V₂ V₃ V₄ : E} {A : V₁ ⟶ V₂}
    {A' : V₂ ⟶ V₁} {B : V₂ ⟶ V₃} {C : V₁ ⟶ V₄} {D : V₄ ⟶ V₃} {D' : V₃ ⟶ V₄}
    (hA : A' ≫ A = 𝟙 V₂) (hD : D ≫ D' = 𝟙 V₄) (h : A ≫ B = C ≫ D) :
    A' ≫ C = B ≫ D' := by
  calc A' ≫ C = A' ≫ (C ≫ D) ≫ D' := by
        rw [Category.assoc, hD, Category.comp_id]
    _ = A' ≫ (A ≫ B) ≫ D' := by rw [h]
    _ = (A' ≫ A) ≫ B ≫ D' := by simp only [Category.assoc]
    _ = B ≫ D' := by rw [hA, Category.id_comp]

/-- **The upper-square half of the component chase**: the cocycle identity for the upper
square's horizontal composite, read against the transport of its identification. -/
private theorem paste_chase_upper {E : Type*} [Category E] {O₃ O₄ O₅ O₆ N₃ Cm : E}
    {v : O₃ ⟶ O₄} {w : O₄ ⟶ O₅} {τ₁ : O₅ ⟶ O₆} {x : O₆ ⟶ N₃} {x' : O₅ ⟶ Cm}
    {σ₁ : Cm ⟶ N₃} {z₂ : O₃ ⟶ Cm}
    (G₂ : τ₁ ≫ x = x' ≫ σ₁) (G₃ : v ≫ w ≫ x' = z₂) :
    v ≫ w ≫ τ₁ ≫ x = z₂ ≫ σ₁ := by
  rw [G₂, ← G₃]
  simp only [Category.assoc]

/-- **Pushing the upper half forward past the lower square's transport.** -/
private theorem paste_chase_push {E : Type*} [Category E] {O₂ O₃ N₂ N₃ Cm : E} {τ₂ : O₂ ⟶ O₃}
    {q : O₃ ⟶ N₃} {z₁ : O₂ ⟶ N₂} {z₂ : O₃ ⟶ Cm} {σ₂ : N₂ ⟶ Cm} {σ₁ : Cm ⟶ N₃}
    (G₄ : τ₂ ≫ z₂ = z₁ ≫ σ₂) (hq : q = z₂ ≫ σ₁) :
    τ₂ ≫ q = z₁ ≫ σ₂ ≫ σ₁ := by
  rw [hq, ← Category.assoc τ₂ z₂ σ₁, G₄, Category.assoc]

/-- **Contracting the two transports into the transport for the rectangle.** -/
private theorem paste_chase_trans {E : Type*} [Category E] {O₂ N₂ N₃ Cm : E} {s : O₂ ⟶ N₃}
    {z₁ : O₂ ⟶ N₂} {σ₂ : N₂ ⟶ Cm} {σ₁ : Cm ⟶ N₃} {τ : N₂ ⟶ N₃}
    (G₅ : σ₂ ≫ σ₁ = τ) (h : s = z₁ ≫ σ₂ ≫ σ₁) :
    s = z₁ ≫ τ := by
  rw [h, ← G₅]

/-- **Prepending the lower square's cocycle identity.** -/
private theorem paste_chase_head {E : Type*} [Category E] {O₀ O₁ O₂ N₂ N₃ : E} {p : O₁ ⟶ O₀}
    {u : O₁ ⟶ O₂} {y : O₀ ⟶ N₂} {z₁ : O₂ ⟶ N₂} {τ : N₂ ⟶ N₃} {s : O₂ ⟶ N₃}
    (G₁ : p ≫ y = u ≫ z₁) (h : s = z₁ ≫ τ) :
    u ≫ s = p ≫ y ≫ τ := by
  rw [h, ← Category.assoc u z₁ τ, ← G₁, Category.assoc]

/-- **The outer half of the component chase**: the inner identity, cancelled against the
comparison for `f' ≫ g'` on the left and read through the cocycle identity for the rectangle's
left leg on the right. -/
private theorem paste_chase_outer {E : Type*} [Category E]
    {O₀ O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ N₂ N₃ : E} {cRinv : O₀ ⟶ O₁} {p : O₁ ⟶ O₀} {u : O₁ ⟶ O₂}
    {τ₂ : O₂ ⟶ O₃} {v : O₃ ⟶ O₄} {w : O₄ ⟶ O₅} {τ₁ : O₅ ⟶ O₆} {x : O₆ ⟶ N₃}
    {ef₁inv : O₆ ⟶ O₇} {n : O₇ ⟶ O₈} {y : O₀ ⟶ N₂} {τ : N₂ ⟶ N₃} {efoinv : N₃ ⟶ O₈}
    (G₀ : cRinv ≫ p = 𝟙 O₀) (G₆ : ef₁inv ≫ n = x ≫ efoinv)
    (mid : u ≫ τ₂ ≫ v ≫ w ≫ τ₁ ≫ x = p ≫ y ≫ τ) :
    y ≫ τ ≫ efoinv = cRinv ≫ u ≫ τ₂ ≫ v ≫ w ≫ τ₁ ≫ ef₁inv ≫ n := by
  simp only [G₆, reassoc_of% mid, reassoc_of% G₀]

/-! ### The cocycle and the transports, at a complex -/

variable {X' X Y' Y Z' Z W : RingedSpace.{u, u}}

/-- Cancelling a functor's image of an inverse against its image of the morphism, on
variables. -/
private theorem map_inv_comp_cancel {C E : Type*} [Category C] [Category E] (F : C ⥤ E)
    {V₁ V₂ : C} {A : V₁ ⟶ V₂} {A' : V₂ ⟶ V₁} (hA : A' ≫ A = 𝟙 V₂) {T : E}
    (B : F.obj V₂ ⟶ T) : F.map A' ≫ F.map A ≫ B = B := by
  rw [← Category.assoc, ← F.map_comp, hA, F.map_id, Category.id_comp]

/-- The cocycle identity of Tag 0D5S with the first factor inverted, which is the form in which
the upper square's comparison is absorbed. -/
private theorem compIsoCanonical_inv_map_comp_assoc (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing W))) :
    (derivedPullback f).map ((derivedPullbackCompIsoCanonical g h).inv.app M) ≫
        (derivedPullbackCompIsoCanonical f g).hom.app ((derivedPullback h).obj M) ≫
        (derivedPullbackCompIsoCanonical (f ≫ g) h).hom.app M =
      (derivedPullbackCompIsoCanonical f (g ≫ h)).hom.app M := by
  rw [derivedPullbackCompIsoCanonical_assoc_app f g h M]
  exact map_inv_comp_cancel (derivedPullback f)
    (Iso.inv_hom_id_app (derivedPullbackCompIsoCanonical g h) M) _

/-- **The transport of derived pullback along an equality of morphisms, read at a complex.**

`derivedPullback` is a reducible abbreviation over a total derived functor, and the kernel cannot
decide an equality of two such functors along an equality of morphisms inside its budget: it
unfolds the abbreviation.  At a complex the two objects are compared instead, which is immediate.
Every transport below is therefore an `eqToHom` between objects, and this is the only place where
the functor-level transport appears. -/
private theorem eqToIso_derivedPullback_hom_app {A C : RingedSpace.{u, u}} {a b : A ⟶ C}
    (e : a = b) (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing C))) :
    (eqToIso (congrArg (fun q : A ⟶ C => derivedPullback q) e)).hom.app M =
      eqToHom (congrArg (fun q : A ⟶ C => (derivedPullback q).obj M) e) := by
  subst e
  simp

/-- Changing the second argument of the composition isomorphism of Tag 0D5S along an equality of
morphisms. -/
private theorem compIsoCanonical_hom_app_congr_right {A B C : RingedSpace.{u, u}} (a : A ⟶ B)
    {b b' : B ⟶ C} (e : b = b')
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing C))) :
    (derivedPullback a).map
          (eqToHom (congrArg (fun q : B ⟶ C => (derivedPullback q).obj M) e)) ≫
        (derivedPullbackCompIsoCanonical a b').hom.app M =
      (derivedPullbackCompIsoCanonical a b).hom.app M ≫
        eqToHom (congrArg (fun q : A ⟶ C => (derivedPullback q).obj M)
          (congrArg (fun q : B ⟶ C => a ≫ q) e)) := by
  subst e
  simp

/-- Changing the first argument of the composition isomorphism of Tag 0D5S along an equality of
morphisms. -/
private theorem compIsoCanonical_hom_app_congr_left {A B C : RingedSpace.{u, u}}
    {a a' : A ⟶ B} (e : a = a') (c : B ⟶ C)
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing C))) :
    eqToHom (congrArg (fun q : A ⟶ B => (derivedPullback q).obj ((derivedPullback c).obj M)) e) ≫
        (derivedPullbackCompIsoCanonical a' c).hom.app M =
      (derivedPullbackCompIsoCanonical a c).hom.app M ≫
        eqToHom (congrArg (fun q : A ⟶ C => (derivedPullback q).obj M)
          (congrArg (fun q : A ⟶ B => q ≫ c) e)) := by
  subst e
  simp

/-- Two transports of derived pullback along equalities of morphisms compose to the transport
along the composed equality. -/
private theorem eqToHom_derivedPullback_obj_trans {A C : RingedSpace.{u, u}}
    {a b c : A ⟶ C} (e₁ : a = b) (e₂ : b = c) (e : a = c)
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing C))) :
    eqToHom (congrArg (fun q : A ⟶ C => (derivedPullback q).obj M) e₁) ≫
        eqToHom (congrArg (fun q : A ⟶ C => (derivedPullback q).obj M) e₂) =
      eqToHom (congrArg (fun q : A ⟶ C => (derivedPullback q).obj M) e) := by
  subst e₁
  subst e₂
  simp

/-- The comparison of two iterated derived pullbacks, as a 2-square, with the two identifications
left as variables.  Unfolding it with the identifications instantiated confronts the kernel with
a component of a comparison of derived functors and exhausts its budget; here the reduction stops
at a variable. -/
private theorem mate_pullbackSquare_eq_mk {X' X S' S : RingedSpace.{u, u}}
    {Lf : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    {Lg : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing S'))}
    {Lf' : DerivedCategory (SheafOfModules.{u} (structureSheafRing S')) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
    {Lg' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
    {Lc : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
    (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc) :
    Mate.derivedPullbackSquare eg ef = TwoSquare.mk Lg Lf Lf' Lg' (eg.hom ≫ ef.inv) :=
  rfl

/-- The comparison down the left and along the bottom, as a composite of isomorphisms.  One
unfolding step, with the two factors left unreduced. -/
private theorem derivedPullbackCompIsoLeft_eq {X' X S' S : RingedSpace.{u, u}} (g' : X' ⟶ X)
    (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (sq : g' ≫ f = f' ≫ g) :
    derivedPullbackCompIsoLeft g' f' f g sq =
      derivedPullbackCompIsoCanonical f' g ≪≫
        eqToIso (congrArg (fun q : X' ⟶ S => derivedPullback q) sq.symm) :=
  rfl

/-- The comparison down the left and along the bottom, split into the composition isomorphism of
Tag 0D5S and the transport along the commutativity of the square. -/
private theorem derivedPullbackCompIsoLeft_hom {X' X S' S : RingedSpace.{u, u}} (g' : X' ⟶ X)
    (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (sq : g' ≫ f = f' ≫ g) :
    (derivedPullbackCompIsoLeft g' f' f g sq).hom =
      (derivedPullbackCompIsoCanonical f' g).hom ≫
        (eqToIso (congrArg (fun q : X' ⟶ S => derivedPullback q) sq.symm)).hom := by
  rw [derivedPullbackCompIsoLeft_eq, Iso.trans_hom]

/-- The comparison of iterated derived pullbacks around a commutative square, as a 2-square on
three explicit factors: the composition isomorphism of Tag 0D5S down the left and along the
bottom, the transport along the commutativity of the square, and the inverse of the composition
isomorphism along the top and down the right. -/
private theorem derivedPullbackSquare_eq_mk {X' X S' S : RingedSpace.{u, u}} (g' : X' ⟶ X)
    (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (sq : g' ≫ f = f' ≫ g) :
    derivedPullbackSquare g' f' f g sq =
      TwoSquare.mk _ _ _ _ (((derivedPullbackCompIsoCanonical f' g).hom ≫
          (eqToIso (congrArg (fun q : X' ⟶ S => derivedPullback q) sq.symm)).hom) ≫
        (derivedPullbackCompIsoCanonical g' f).inv) := by
  rw [← derivedPullbackCompIsoLeft_hom]
  exact mate_pullbackSquare_eq_mk _ _

/-! ### Pasting on the derived pullback side -/

variable (k : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (l : Y' ⟶ Y) (g' : Y' ⟶ Z') (g : Y ⟶ Z)
  (m : Z' ⟶ Z)

/-- The outer rectangle of two vertically composable commutative squares commutes. -/
theorem comp_square (sq₁ : k ≫ f = f' ≫ l) (sq₂ : l ≫ g = g' ≫ m) :
    k ≫ f ≫ g = (f' ≫ g') ≫ m := by
  simp only [Category.assoc, reassoc_of% sq₁, sq₂]

/-- **The component identity behind the pasting of two derived pullback squares.**

The comparison around the outer rectangle, at a complex, factors as the inverse comparison for
`f' ≫ g'`, the derived pullback along `f'` of the lower square's comparison, the upper square's
comparison, and the derived pullback along `k` of the comparison for `f ≫ g`.  Everything is
routed through the five abstract chase lemmas above, whose inputs are the cocycle identity of
Tag 0D5S at the three bracketings and the three transports.

Split into five steps on purpose, each carrying the accumulated composite as a variable with its
type written out.  Every junction of the chain identifies an object spelled as a composite
functor applied to a complex on one side and as the iterated application on the other, and the
kernel has to reconcile the two spellings; a declaration can afford about five of those, and the
whole chase has twenty. -/
private theorem derivedPullbackSquare_paste_upper (sq₁ : k ≫ f = f' ≫ l)
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z))) :
    (derivedPullback f').map ((derivedPullbackCompIsoCanonical l g).inv.app M) ≫
        (derivedPullbackCompIsoCanonical f' l).hom.app ((derivedPullback g).obj M) ≫
        eqToHom (congrArg (fun r : X' ⟶ Y =>
          (derivedPullback r).obj ((derivedPullback g).obj M)) sq₁.symm) ≫
        (derivedPullbackCompIsoCanonical (k ≫ f) g).hom.app M =
      (derivedPullbackCompIsoCanonical f' (l ≫ g)).hom.app M ≫
        eqToHom (congrArg (fun r : X' ⟶ Z => (derivedPullback r).obj M)
          (congrArg (fun r : X' ⟶ Y => r ≫ g) sq₁.symm)) :=
  paste_chase_upper (compIsoCanonical_hom_app_congr_left sq₁.symm g M)
    (compIsoCanonical_inv_map_comp_assoc f' l g M)

/-- The upper half, pushed past the lower square's transport. -/
private theorem derivedPullbackSquare_paste_push (sq₁ : k ≫ f = f' ≫ l)
    (sq₂ : l ≫ g = g' ≫ m) (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z)))
    {q : (derivedPullback f').obj ((derivedPullback (l ≫ g)).obj M) ⟶
      (derivedPullback ((k ≫ f) ≫ g)).obj M}
    (hq : q = (derivedPullbackCompIsoCanonical f' (l ≫ g)).hom.app M ≫
      eqToHom (congrArg (fun r : X' ⟶ Z => (derivedPullback r).obj M)
        (congrArg (fun r : X' ⟶ Y => r ≫ g) sq₁.symm))) :
    (derivedPullback f').map
          (eqToHom (congrArg (fun r : Y' ⟶ Z => (derivedPullback r).obj M) sq₂.symm)) ≫ q =
      (derivedPullbackCompIsoCanonical f' (g' ≫ m)).hom.app M ≫
        eqToHom (congrArg (fun r : X' ⟶ Z => (derivedPullback r).obj M)
          (congrArg (fun r : Y' ⟶ Z => f' ≫ r) sq₂.symm)) ≫
        eqToHom (congrArg (fun r : X' ⟶ Z => (derivedPullback r).obj M)
          (congrArg (fun r : X' ⟶ Y => r ≫ g) sq₁.symm)) :=
  paste_chase_push (compIsoCanonical_hom_app_congr_right f' sq₂.symm M) hq

/-- The two transports contracted into the transport along the commutativity of the
rectangle. -/
private theorem derivedPullbackSquare_paste_trans (sq₁ : k ≫ f = f' ≫ l)
    (sq₂ : l ≫ g = g' ≫ m) (sq : k ≫ f ≫ g = (f' ≫ g') ≫ m)
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z)))
    {s : (derivedPullback f').obj ((derivedPullback (g' ≫ m)).obj M) ⟶
      (derivedPullback ((k ≫ f) ≫ g)).obj M}
    (h : s = (derivedPullbackCompIsoCanonical f' (g' ≫ m)).hom.app M ≫
      eqToHom (congrArg (fun r : X' ⟶ Z => (derivedPullback r).obj M)
        (congrArg (fun r : Y' ⟶ Z => f' ≫ r) sq₂.symm)) ≫
      eqToHom (congrArg (fun r : X' ⟶ Z => (derivedPullback r).obj M)
        (congrArg (fun r : X' ⟶ Y => r ≫ g) sq₁.symm))) :
    s = (derivedPullbackCompIsoCanonical f' (g' ≫ m)).hom.app M ≫
      eqToHom (congrArg (fun r : X' ⟶ Z => (derivedPullback r).obj M) sq.symm) :=
  paste_chase_trans
    (eqToHom_derivedPullback_obj_trans (congrArg (fun r : Y' ⟶ Z => f' ≫ r) sq₂.symm)
      (congrArg (fun r : X' ⟶ Y => r ≫ g) sq₁.symm) sq.symm M) h

/-- The lower square's cocycle identity prepended. -/
private theorem derivedPullbackSquare_paste_mid (sq : k ≫ f ≫ g = (f' ≫ g') ≫ m)
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z)))
    {s : (derivedPullback f').obj ((derivedPullback (g' ≫ m)).obj M) ⟶
      (derivedPullback ((k ≫ f) ≫ g)).obj M}
    (h : s = (derivedPullbackCompIsoCanonical f' (g' ≫ m)).hom.app M ≫
      eqToHom (congrArg (fun r : X' ⟶ Z => (derivedPullback r).obj M) sq.symm)) :
    (derivedPullback f').map ((derivedPullbackCompIsoCanonical g' m).hom.app M) ≫ s =
      (derivedPullbackCompIsoCanonical f' g').hom.app ((derivedPullback m).obj M) ≫
        (derivedPullbackCompIsoCanonical (f' ≫ g') m).hom.app M ≫
        eqToHom (congrArg (fun r : X' ⟶ Z => (derivedPullback r).obj M) sq.symm) :=
  paste_chase_head (derivedPullbackCompIsoCanonical_assoc_app f' g' m M) h

/-- **The component identity behind the pasting of two derived pullback squares.** -/
private theorem derivedPullbackSquare_paste_app (sq₁ : k ≫ f = f' ≫ l) (sq₂ : l ≫ g = g' ≫ m)
    (sq : k ≫ f ≫ g = (f' ≫ g') ≫ m)
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z))) :
    (derivedPullbackCompIsoCanonical (f' ≫ g') m).hom.app M ≫
        eqToHom (congrArg (fun r : X' ⟶ Z => (derivedPullback r).obj M) sq.symm) ≫
        (derivedPullbackCompIsoCanonical k (f ≫ g)).inv.app M =
      (derivedPullbackCompIsoCanonical f' g').inv.app ((derivedPullback m).obj M) ≫
        (derivedPullback f').map ((derivedPullbackCompIsoCanonical g' m).hom.app M) ≫
        (derivedPullback f').map
          (eqToHom (congrArg (fun r : Y' ⟶ Z => (derivedPullback r).obj M) sq₂.symm)) ≫
        (derivedPullback f').map ((derivedPullbackCompIsoCanonical l g).inv.app M) ≫
        (derivedPullbackCompIsoCanonical f' l).hom.app ((derivedPullback g).obj M) ≫
        eqToHom (congrArg (fun r : X' ⟶ Y =>
          (derivedPullback r).obj ((derivedPullback g).obj M)) sq₁.symm) ≫
        (derivedPullbackCompIsoCanonical k f).inv.app ((derivedPullback g).obj M) ≫
        (derivedPullback k).map ((derivedPullbackCompIsoCanonical f g).hom.app M) :=
  paste_chase_outer (Iso.inv_hom_id_app (derivedPullbackCompIsoCanonical f' g') _)
    (inv_comp_eq_comp_inv (Iso.inv_hom_id_app (derivedPullbackCompIsoCanonical k f) _)
      (Iso.hom_inv_id_app (derivedPullbackCompIsoCanonical k (f ≫ g)) M)
      (derivedPullbackCompIsoCanonical_assoc_app k f g M))
    (derivedPullbackSquare_paste_mid k f' f g' g m sq M
      (derivedPullbackSquare_paste_trans k f' f l g' g m sq₁ sq₂ sq M
        (derivedPullbackSquare_paste_push k f' f l g' g m sq₁ sq₂ M
          (derivedPullbackSquare_paste_upper k f' f l g sq₁ M))))

/-- **Pasting of the comparisons of iterated derived pullbacks.**  For two vertically composable
commutative squares of ringed spaces, the comparison of the two iterated derived pullbacks
around the outer rectangle is the vertical composite of the comparisons for the two squares,
whiskered with the composition isomorphisms of Tag 0D5S for `f ≫ g` and for `f' ≫ g'`.

This is the geometric input to Tag 0ATL, stated for reuse: it says that the two-dimensional
datum attached to a rectangle of ringed spaces is determined by the data of its two squares,
and the only ingredient is the cocycle identity
`Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackCompIsoCanonical_assoc` of
Tag 0D5S, applied to the three ways the rectangle's threefold composite can be bracketed. -/
theorem derivedPullbackSquare_paste (sq₁ : k ≫ f = f' ≫ l) (sq₂ : l ≫ g = g' ≫ m)
    (sq : k ≫ f ≫ g = (f' ≫ g') ≫ m) :
    derivedPullbackSquare k (f' ≫ g') (f ≫ g) m sq =
      ((derivedPullbackSquare l g' g m sq₂ ≫ᵥ
          derivedPullbackSquare k f' f l sq₁).whiskerLeft
            (derivedPullbackCompIsoCanonical f g).hom).whiskerRight
        (derivedPullbackCompIsoCanonical f' g').inv := by
  rw [derivedPullbackSquare_eq_mk k (f' ≫ g') (f ≫ g) m, derivedPullbackSquare_eq_mk l g' g m,
    derivedPullbackSquare_eq_mk k f' f l]
  exact twoSquare_paste_of_app (derivedPullbackCompIsoCanonical (f' ≫ g') m).hom
    (eqToIso (congrArg (fun q : X' ⟶ Z => derivedPullback q) sq.symm)).hom
    (derivedPullbackCompIsoCanonical k (f ≫ g)).inv
    (derivedPullbackCompIsoCanonical g' m).hom
    (eqToIso (congrArg (fun q : Y' ⟶ Z => derivedPullback q) sq₂.symm)).hom
    (derivedPullbackCompIsoCanonical l g).inv (derivedPullbackCompIsoCanonical f' l).hom
    (eqToIso (congrArg (fun q : X' ⟶ Y => derivedPullback q) sq₁.symm)).hom
    (derivedPullbackCompIsoCanonical k f).inv (derivedPullbackCompIsoCanonical f g).hom
    (derivedPullbackCompIsoCanonical f' g').inv
    (fun M => eqToHom (congrArg (fun r : X' ⟶ Z => (derivedPullback r).obj M) sq.symm))
    (fun M => eqToIso_derivedPullback_hom_app sq.symm M)
    (fun M => eqToHom (congrArg (fun r : Y' ⟶ Z => (derivedPullback r).obj M) sq₂.symm))
    (fun M => eqToIso_derivedPullback_hom_app sq₂.symm M)
    (fun N => eqToHom (congrArg (fun r : X' ⟶ Y => (derivedPullback r).obj N) sq₁.symm))
    (fun N => eqToIso_derivedPullback_hom_app sq₁.symm N)
    (derivedPullbackSquare_paste_app k f' f l g' g m sq₁ sq₂ sq)

/-! ### Pasting of the derived base change morphism -/

/-- The derived base change map is the component of the derived base change 2-square. -/
private theorem derivedBaseChangeMap_eq_app {X' X S' S : RingedSpace.{u, u}} (g' : X' ⟶ X)
    (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (sq : g' ≫ f = f' ≫ g)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    derivedBaseChangeMap g' f' f g sq K =
      (derivedBaseChangeSquare g' f' f g sq).natTrans.app K :=
  rfl

/-- **The conjugate of the composition isomorphism for derived pullback, in the direction that
produces the inverse composition isomorphism for derived pushforward.**

This is the statement dual to `conjugateEquiv_derivedPullbackCompIsoCanonical_inv` of
`Stacks.Cohomology.DerivedPushforwardAssociativity`, and it is what replaces the derived
adjunction for `f ≫ g` by the composite of the derived adjunctions in the top leg of a mate. -/
theorem conjugateEquiv_derivedPullbackCompIsoCanonical_hom (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv (derivedAdjunction (f ≫ g))
        ((derivedAdjunction g).comp (derivedAdjunction f))
        (derivedPullbackCompIsoCanonical f g).hom =
      (derivedPushforwardCompIso f g).inv := by
  have h := conjugateEquiv_comm (derivedAdjunction (f ≫ g))
    ((derivedAdjunction g).comp (derivedAdjunction f))
    (α := (derivedPullbackCompIsoCanonical f g).hom)
    (β := (derivedPullbackCompIsoCanonical f g).inv) (Iso.inv_hom_id _)
  rw [conjugateEquiv_derivedPullbackCompIsoCanonical_inv] at h
  exact (Iso.comp_hom_eq_id _).1 h

/-- **Pasting of mates, with every functor and adjunction a variable.**

If an outer 2-square is the vertical composite of two inner ones whiskered with comparisons `cL`,
`cR` of the two composite legs, then its mate is the horizontal composite of the two inner mates
whiskered with the conjugates `dL`, `dR` of those comparisons.  This is Mathlib's
`CategoryTheory.mateEquiv_hcomp` with the two adjunctions of the outer square traded for the
composite adjunctions by `CategoryTheory.mateEquiv_conjugateEquiv_vcomp` and
`CategoryTheory.conjugateEquiv_mateEquiv_vcomp`.

Kept on variables: run on the derived pullbacks and pushforwards of six ringed spaces at once,
the rewrites confront the unifier with four total derived functors per step and do not
terminate. -/
private theorem mate_twoSquare_paste {A B C D E F : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E] [Category F]
    {Tl : A ⥤ B} {Ll : A ⥤ C} {Rl : B ⥤ D} {Tu : C ⥤ D} {Lu : C ⥤ E} {Ru : D ⥤ F}
    {Bu : E ⥤ F} {Lo : A ⥤ E} {Ro : B ⥤ F} {RLl : C ⥤ A} {RRl : D ⥤ B} {RLu : E ⥤ C}
    {RRu : F ⥤ D} {RLo : E ⥤ A} {RRo : F ⥤ B} (adjLl : Ll ⊣ RLl) (adjRl : Rl ⊣ RRl)
    (adjLu : Lu ⊣ RLu) (adjRu : Ru ⊣ RRu) (adjLo : Lo ⊣ RLo) (adjRo : Ro ⊣ RRo)
    (Sl : TwoSquare Tl Ll Rl Tu) (Su : TwoSquare Tu Lu Ru Bu) (So : TwoSquare Tl Lo Ro Bu)
    (cL : Ll ⋙ Lu ⟶ Lo) (cR : Ro ⟶ Rl ⋙ Ru) (dL : RLo ⟶ RLu ⋙ RLl) (dR : RRu ⋙ RRl ⟶ RRo)
    (hSo : So = ((Sl ≫ᵥ Su).whiskerLeft cL).whiskerRight cR)
    (hdL : conjugateEquiv adjLo (adjLl.comp adjLu) cL = dL)
    (hdR : conjugateEquiv (adjRl.comp adjRu) adjRo cR = dR) :
    mateEquiv adjLo adjRo So =
      ((mateEquiv adjLu adjRu Su ≫ₕ
        mateEquiv adjLl adjRl Sl).whiskerTop dL).whiskerBottom dR := by
  subst hSo
  subst hdL
  subst hdR
  rw [mateEquiv_conjugateEquiv_vcomp adjLo (adjRl.comp adjRu) adjRo,
    conjugateEquiv_mateEquiv_vcomp adjLo (adjLl.comp adjLu) (adjRl.comp adjRu), mateEquiv_hcomp]

/-- **Pasting of the derived base change morphisms of functors.**  For two vertically composable
commutative squares of ringed spaces, the derived base change 2-square of the outer rectangle is
the horizontal composite of the 2-squares of the two squares, whiskered with the composition
isomorphisms of Tag 079W for derived pushforward along `f ≫ g` and along `f' ≫ g'`.

Stated for reuse: this is Tag 0ATL as an identity of morphisms of functors, so it carries the
naturality of all four factors in the complex. -/
theorem derivedBaseChangeSquare_paste (sq₁ : k ≫ f = f' ≫ l) (sq₂ : l ≫ g = g' ≫ m)
    (sq : k ≫ f ≫ g = (f' ≫ g') ≫ m) :
    derivedBaseChangeSquare k (f' ≫ g') (f ≫ g) m sq =
      ((derivedBaseChangeSquare k f' f l sq₁ ≫ₕ
          derivedBaseChangeSquare l g' g m sq₂).whiskerTop
            (derivedPushforwardCompIso f g).inv).whiskerBottom
        (derivedPushforwardCompIso f' g').hom := by
  rw [derivedBaseChangeSquare_eq_mateEquiv k (f' ≫ g') (f ≫ g) m,
    derivedBaseChangeSquare_eq_mateEquiv k f' f l,
    derivedBaseChangeSquare_eq_mateEquiv l g' g m]
  exact mate_twoSquare_paste (derivedAdjunction g) (derivedAdjunction g') (derivedAdjunction f)
    (derivedAdjunction f') (derivedAdjunction (f ≫ g)) (derivedAdjunction (f' ≫ g'))
    (derivedPullbackSquare l g' g m sq₂) (derivedPullbackSquare k f' f l sq₁)
    (derivedPullbackSquare k (f' ≫ g') (f ≫ g) m sq)
    (derivedPullbackCompIsoCanonical f g).hom (derivedPullbackCompIsoCanonical f' g').inv
    (derivedPushforwardCompIso f g).inv (derivedPushforwardCompIso f' g').hom
    (derivedPullbackSquare_paste k f' f l g' g m sq₁ sq₂ sq)
    (conjugateEquiv_derivedPullbackCompIsoCanonical_hom f g)
    (conjugateEquiv_derivedPullbackCompIsoCanonical_inv f' g')

/-- **Tag 0ATL.**  Derived base change for an outer rectangle is the composite of derived base
change for its two constituent squares.

For two vertically composable commutative squares of ringed spaces, the composite of the derived
pullback along the lower horizontal morphism of the inverse composition isomorphism of Tag 079W,
the derived base change map of the lower square, the derived pushforward along the upper
square's right-hand vertical of the derived base change map of the upper square, and the
composition isomorphism of Tag 079W for the rectangle's left-hand verticals, is the derived base
change map of the rectangle. -/
@[stacks 0ATL]
theorem derivedBaseChangeMap_comp (sq₁ : k ≫ f = f' ≫ l) (sq₂ : l ≫ g = g' ≫ m)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (derivedPullback m).map ((derivedPushforwardCompIso f g).inv.app K) ≫
        derivedBaseChangeMap l g' g m sq₂ ((derivedPushforward f).obj K) ≫
        (derivedPushforward g').map (derivedBaseChangeMap k f' f l sq₁ K) ≫
        (derivedPushforwardCompIso f' g').hom.app ((derivedPullback k).obj K) =
      derivedBaseChangeMap k (f' ≫ g') (f ≫ g) m (comp_square k f' f l g' g m sq₁ sq₂) K := by
  have h := congr_app
    (derivedBaseChangeSquare_paste k f' f l g' g m sq₁ sq₂
      (comp_square k f' f l g' g m sq₁ sq₂)) K
  rw [derivedBaseChangeMap_eq_app, derivedBaseChangeMap_eq_app, derivedBaseChangeMap_eq_app]
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.assoc] at h
  exact h.symm

end

/-! ### Horizontal pasting -/

noncomputable section

/-! #### Abstract bookkeeping -/

/-- A 2-square is the mate of a square whose adjoint transposes agree with its own.

The adjoint transpose under `adj₂` of a component is injective, and `mateEquiv_counit`
computes the transpose of a mate, so the displayed identity pins the mate down. -/
private theorem mateEquiv_eq_of_counit {A B C D : Type*} [Category A] [Category B] [Category C]
    [Category D] {G : A ⥤ C} {H : B ⥤ D} {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : TwoSquare G L₁ L₂ H) (β : TwoSquare R₁ H G R₂)
    (h : ∀ d, L₂.map (β.app d) ≫ adj₂.counit.app (H.obj d) =
      α.app (R₁.obj d) ≫ H.map (adj₁.counit.app d)) :
    mateEquiv adj₁ adj₂ α = β := by
  refine TwoSquare.ext _ _ fun d => ?_
  apply (adj₂.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, mateEquiv_counit, h d]

/-- **Whiskering a 2-square at the top and at the bottom whiskers its mate at the right and at
the left.**

The top and the bottom are the two legs of a square that the mates correspondence carries over
unchanged, so — unlike for the left and right legs, where a conjugate transformation intervenes —
the whiskered transformations are reused verbatim. -/
private theorem mateEquiv_whiskerTopBottom {A B C D : Type*} [Category A] [Category B]
    [Category C] [Category D] {G G' : A ⥤ C} {H H' : B ⥤ D} {L₁ : A ⥤ B} {R₁ : B ⥤ A}
    {L₂ : C ⥤ D} {R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (w : TwoSquare G' L₁ L₂ H')
    (cT : G ⟶ G') (cB : H' ⟶ H) :
    mateEquiv adj₁ adj₂ ((w.whiskerTop cT).whiskerBottom cB) =
      ((mateEquiv adj₁ adj₂ w).whiskerRight cT).whiskerLeft cB := by
  refine mateEquiv_eq_of_counit adj₁ adj₂ _ _ fun d => ?_
  have hw := mateEquiv_counit adj₁ adj₂ w d
  have hc := adj₂.counit_naturality (cB.app d)
  have hb := cB.naturality (adj₁.counit.app d)
  simp only [Functor.id_obj, Functor.comp_obj] at hb
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.whiskerLeft,
    TwoSquare.whiskerRight, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  rw [hc, reassoc_of% hw, hb]

/-- Horizontal pasting of 2-squares, reduced to one identity of morphisms at each object.

An identity between an outer 2-square and the horizontal composite of two inner ones, whiskered
at the top and at the bottom with comparisons of the two composite legs, is componentwise exactly
the factorization of the outer square's component into the eight factors on the right. -/
private theorem twoSquare_hpaste_of_app {A B C D E F : Type*} [Category A] [Category B]
    [Category C] [Category D] [Category E] [Category F]
    {Tr : A ⥤ B} {Lr : A ⥤ C} {Rr : B ⥤ D} {Br : C ⥤ D} {Tl : B ⥤ E} {Rl : E ⥤ F} {Bl : D ⥤ F}
    {To : A ⥤ E} {Bo : C ⥤ F} {Cr Pr : A ⥤ D} {Cl Pl : B ⥤ F} {Co Po : A ⥤ F}
    (ego₁ : To ⋙ Rl ⟶ Po) (ego₂ : Po ⟶ Co) (efo : Co ⟶ Lr ⋙ Bo)
    (egr₁ : Tr ⋙ Rr ⟶ Pr) (egr₂ : Pr ⟶ Cr) (efr : Cr ⟶ Lr ⋙ Br)
    (egl₁ : Tl ⋙ Rl ⟶ Pl) (egl₂ : Pl ⟶ Cl) (efl : Cl ⟶ Rr ⋙ Bl)
    (cT : To ⟶ Tr ⋙ Tl) (cB : Br ⋙ Bl ⟶ Bo)
    (d₀ : ∀ M, Po.obj M ⟶ Co.obj M) (hd₀ : ∀ M, ego₂.app M = d₀ M)
    (dr : ∀ M, Pr.obj M ⟶ Cr.obj M) (hdr : ∀ M, egr₂.app M = dr M)
    (dl : ∀ N, Pl.obj N ⟶ Cl.obj N) (hdl : ∀ N, egl₂.app N = dl N)
    (h : ∀ M, ego₁.app M ≫ d₀ M ≫ efo.app M =
      Rl.map (cT.app M) ≫ egl₁.app (Tr.obj M) ≫ dl (Tr.obj M) ≫ efl.app (Tr.obj M) ≫
        Bl.map (egr₁.app M) ≫ Bl.map (dr M) ≫ Bl.map (efr.app M) ≫ cB.app (Lr.obj M)) :
    TwoSquare.mk To Lr Rl Bo ((ego₁ ≫ ego₂) ≫ efo) =
      ((TwoSquare.mk Tr Lr Rr Br ((egr₁ ≫ egr₂) ≫ efr) ≫ₕ
        TwoSquare.mk Tl Rr Rl Bl ((egl₁ ≫ egl₂) ≫ efl)).whiskerTop cT).whiskerBottom cB := by
  refine TwoSquare.ext _ _ fun M => ?_
  have hM := h M
  rw [← hd₀ M, ← hdr M, ← hdl (Tr.obj M)] at hM
  simpa [TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    Category.assoc] using hM

/-- **The component chase for horizontal pasting**, with every object and morphism a variable.

Reading the chain from `A₁` to `A₈`: the two identifications of threefold iterated derived
pullbacks are absorbed by the cocycle identity of Tag 0D5S at the head (`H₁`) and at the tail
(`H₅`), the two cocycle identities for the inner squares' legs (`H₂`, `H₃`) move the transports
of the squares' commutativity to the right, and `H₆` contracts the two transports into the
transport along the commutativity of the rectangle. -/
private theorem hpaste_chase {E : Type*} [Category E]
    {O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ O₉ N₁ N₂ N₃ : E}
    {A₁ : O₁ ⟶ O₂} {A₂ : O₂ ⟶ O₃} {A₃ : O₃ ⟶ O₄} {A₄ : O₄ ⟶ O₅} {A₅ : O₅ ⟶ O₆}
    {A₆ : O₆ ⟶ O₇} {A₇ : O₇ ⟶ O₈} {A₈ : O₈ ⟶ O₉} {B₁ : O₁ ⟶ N₁} {B₂ : N₁ ⟶ N₃} {B₃ : N₃ ⟶ O₉}
    {Z : O₃ ⟶ N₁} {Z' : O₄ ⟶ N₂} {W : O₆ ⟶ N₂} {V : O₇ ⟶ N₃} {Y : O₉ ⟶ N₃}
    {T₂ : N₁ ⟶ N₂} {T₁ : N₂ ⟶ N₃} {A₄' : O₅ ⟶ O₄}
    (H₁ : A₁ ≫ A₂ ≫ Z = B₁) (H₂ : A₃ ≫ Z' = Z ≫ T₂) (H₃ : A₄' ≫ Z' = A₅ ≫ W)
    (H₃' : A₄ ≫ A₄' = 𝟙 O₄) (H₄ : A₆ ≫ V = W ≫ T₁) (H₅ : A₇ ≫ A₈ ≫ Y = V)
    (H₆ : T₂ ≫ T₁ = B₂) (H₇ : Y ≫ B₃ = 𝟙 O₉) :
    B₁ ≫ B₂ ≫ B₃ = A₁ ≫ A₂ ≫ A₃ ≫ A₄ ≫ A₅ ≫ A₆ ≫ A₇ ≫ A₈ := by
  have key : A₃ ≫ A₄ ≫ A₅ ≫ A₆ ≫ A₇ ≫ A₈ ≫ Y = Z ≫ B₂ :=
    calc A₃ ≫ A₄ ≫ A₅ ≫ A₆ ≫ A₇ ≫ A₈ ≫ Y = A₃ ≫ A₄ ≫ A₅ ≫ A₆ ≫ V := by rw [H₅]
      _ = A₃ ≫ A₄ ≫ A₅ ≫ W ≫ T₁ := by rw [H₄]
      _ = A₃ ≫ A₄ ≫ A₄' ≫ Z' ≫ T₁ := by
            rw [← Category.assoc A₅ W T₁, ← H₃, Category.assoc]
      _ = A₃ ≫ Z' ≫ T₁ := by rw [← Category.assoc A₄ A₄' _, H₃', Category.id_comp]
      _ = Z ≫ T₂ ≫ T₁ := by rw [← Category.assoc A₃ Z' T₁, H₂, Category.assoc]
      _ = Z ≫ B₂ := by rw [H₆]
  rw [← H₁]
  simp only [Category.assoc, ← reassoc_of% key, H₇, Category.comp_id]

/-! #### Pasting on the derived pullback side -/

variable {X'' X' X Y'' Y' Y : RingedSpace.{u, u}} (g' : X'' ⟶ X') (g : X' ⟶ X)
  (f'' : X'' ⟶ Y'') (f' : X' ⟶ Y') (f : X ⟶ Y) (h' : Y'' ⟶ Y') (h : Y' ⟶ Y)

/-- The outer rectangle of two horizontally composable commutative squares commutes. -/
theorem hcomp_square (sq₁ : g ≫ f = f' ≫ h) (sq₂ : g' ≫ f' = f'' ≫ h') :
    (g' ≫ g) ≫ f = f'' ≫ h' ≫ h := by
  simp only [Category.assoc, sq₁, reassoc_of% sq₂]

/-- **The component identity behind the horizontal pasting of two derived pullback squares.**

The comparison around the outer rectangle, at a complex, factors into the derived pullback along
`f''` of the comparison for `h' ≫ h`, the lower square's comparison, the upper square's
comparison pushed forward along `g'`, and the comparison for `g' ≫ g`.  The only inputs are the
cocycle identity of Tag 0D5S at the three bracketings involved and the three transports. -/
private theorem derivedPullbackSquare_hpaste_app (sq₁ : g ≫ f = f' ≫ h)
    (sq₂ : g' ≫ f' = f'' ≫ h') (sq : (g' ≫ g) ≫ f = f'' ≫ h' ≫ h)
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    (derivedPullbackCompIsoCanonical f'' (h' ≫ h)).hom.app M ≫
        eqToHom (congrArg (fun r : X'' ⟶ Y => (derivedPullback r).obj M) sq.symm) ≫
        (derivedPullbackCompIsoCanonical (g' ≫ g) f).inv.app M =
      (derivedPullback f'').map ((derivedPullbackCompIsoCanonical h' h).inv.app M) ≫
        (derivedPullbackCompIsoCanonical f'' h').hom.app ((derivedPullback h).obj M) ≫
        eqToHom (congrArg (fun r : X'' ⟶ Y' =>
          (derivedPullback r).obj ((derivedPullback h).obj M)) sq₂.symm) ≫
        (derivedPullbackCompIsoCanonical g' f').inv.app ((derivedPullback h).obj M) ≫
        (derivedPullback g').map ((derivedPullbackCompIsoCanonical f' h).hom.app M) ≫
        (derivedPullback g').map
          (eqToHom (congrArg (fun r : X' ⟶ Y => (derivedPullback r).obj M) sq₁.symm)) ≫
        (derivedPullback g').map ((derivedPullbackCompIsoCanonical g f).inv.app M) ≫
        (derivedPullbackCompIsoCanonical g' g).hom.app ((derivedPullback f).obj M) :=
  hpaste_chase (compIsoCanonical_inv_map_comp_assoc f'' h' h M)
    (compIsoCanonical_hom_app_congr_left sq₂.symm h M)
    (derivedPullbackCompIsoCanonical_assoc_app g' f' h M)
    (Iso.inv_hom_id_app (derivedPullbackCompIsoCanonical g' f') _)
    (compIsoCanonical_hom_app_congr_right g' sq₁.symm M)
    (compIsoCanonical_inv_map_comp_assoc g' g f M)
    (eqToHom_derivedPullback_obj_trans (congrArg (fun r : X'' ⟶ Y' => r ≫ h) sq₂.symm)
      (congrArg (fun r : X' ⟶ Y => g' ≫ r) sq₁.symm) sq.symm M)
    (Iso.hom_inv_id_app (derivedPullbackCompIsoCanonical (g' ≫ g) f) M)

/-- **Horizontal pasting of the comparisons of iterated derived pullbacks.**  For two
horizontally composable commutative squares of ringed spaces, the comparison of the two iterated
derived pullbacks around the outer rectangle is the horizontal composite of the comparisons for
the two squares, whiskered at the top and at the bottom with the composition isomorphisms of Tag
0D5S for `h' ≫ h` and for `g' ≫ g`.

This is the geometric input to Tag 0ATM; the only ingredient is the cocycle identity
`Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackCompIsoCanonical_assoc` of
Tag 0D5S, applied to the three ways the rectangle's threefold composites can be bracketed. -/
theorem derivedPullbackSquare_hpaste (sq₁ : g ≫ f = f' ≫ h) (sq₂ : g' ≫ f' = f'' ≫ h')
    (sq : (g' ≫ g) ≫ f = f'' ≫ h' ≫ h) :
    derivedPullbackSquare (g' ≫ g) f'' f (h' ≫ h) sq =
      ((derivedPullbackSquare g f' f h sq₁ ≫ₕ
          derivedPullbackSquare g' f'' f' h' sq₂).whiskerTop
            (derivedPullbackCompIsoCanonical h' h).inv).whiskerBottom
        (derivedPullbackCompIsoCanonical g' g).hom := by
  rw [derivedPullbackSquare_eq_mk (g' ≫ g) f'' f (h' ≫ h), derivedPullbackSquare_eq_mk g f' f h,
    derivedPullbackSquare_eq_mk g' f'' f' h']
  exact twoSquare_hpaste_of_app (derivedPullbackCompIsoCanonical f'' (h' ≫ h)).hom
    (eqToIso (congrArg (fun q : X'' ⟶ Y => derivedPullback q) sq.symm)).hom
    (derivedPullbackCompIsoCanonical (g' ≫ g) f).inv
    (derivedPullbackCompIsoCanonical f' h).hom
    (eqToIso (congrArg (fun q : X' ⟶ Y => derivedPullback q) sq₁.symm)).hom
    (derivedPullbackCompIsoCanonical g f).inv
    (derivedPullbackCompIsoCanonical f'' h').hom
    (eqToIso (congrArg (fun q : X'' ⟶ Y' => derivedPullback q) sq₂.symm)).hom
    (derivedPullbackCompIsoCanonical g' f').inv
    (derivedPullbackCompIsoCanonical h' h).inv (derivedPullbackCompIsoCanonical g' g).hom
    (fun M => eqToHom (congrArg (fun r : X'' ⟶ Y => (derivedPullback r).obj M) sq.symm))
    (fun M => eqToIso_derivedPullback_hom_app sq.symm M)
    (fun M => eqToHom (congrArg (fun r : X' ⟶ Y => (derivedPullback r).obj M) sq₁.symm))
    (fun M => eqToIso_derivedPullback_hom_app sq₁.symm M)
    (fun N => eqToHom (congrArg (fun r : X'' ⟶ Y' => (derivedPullback r).obj N) sq₂.symm))
    (fun N => eqToIso_derivedPullback_hom_app sq₂.symm N)
    (derivedPullbackSquare_hpaste_app g' g f'' f' f h' h sq₁ sq₂ sq)

/-! #### Horizontal pasting of the derived base change morphism -/

/-- **Horizontal pasting of mates, with every functor and adjunction a variable.**

If an outer 2-square is the horizontal composite of two inner ones whiskered at the top and at
the bottom with comparisons `cT`, `cB` of the two composite legs, then its mate is the vertical
composite of the two inner mates whiskered at the right and at the left with the same two
comparisons.  This is `CategoryTheory.mateEquiv_vcomp` together with
`mateEquiv_whiskerTopBottom`; no adjunction has to be traded for a composite, because horizontal
composition shares the middle vertical leg rather than composing it.

Kept on variables: run on the derived pullbacks and pushforwards of six ringed spaces at once,
the rewrites confront the unifier with four total derived functors per step and do not
terminate. -/
private theorem mate_twoSquare_hpaste {A B C D E F : Type*} [Category A] [Category B]
    [Category C] [Category D] [Category E] [Category F]
    {G₁ : A ⥤ C} {G₂ : C ⥤ E} {H₁ : B ⥤ D} {H₂ : D ⥤ F} {Go : A ⥤ E} {Ho : B ⥤ F}
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C} {L₃ : E ⥤ F} {R₃ : F ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)
    (Sr : TwoSquare G₁ L₁ L₂ H₁) (Sl : TwoSquare G₂ L₂ L₃ H₂) (So : TwoSquare Go L₁ L₃ Ho)
    (cT : Go ⟶ G₁ ⋙ G₂) (cB : H₁ ⋙ H₂ ⟶ Ho)
    (hSo : So = ((Sr ≫ₕ Sl).whiskerTop cT).whiskerBottom cB) :
    mateEquiv adj₁ adj₃ So =
      ((mateEquiv adj₁ adj₂ Sr ≫ᵥ mateEquiv adj₂ adj₃ Sl).whiskerRight cT).whiskerLeft cB := by
  subst hSo
  rw [mateEquiv_whiskerTopBottom adj₁ adj₃ (Sr ≫ₕ Sl) cT cB,
    mateEquiv_vcomp adj₁ adj₂ adj₃ Sr Sl]

/-- **Horizontal pasting of the derived base change morphisms of functors.**  For two
horizontally composable commutative squares of ringed spaces, the derived base change 2-square of
the outer rectangle is the vertical composite of the 2-squares of the two squares, whiskered with
the composition isomorphisms of Tag 0D5S for derived pullback along `h' ≫ h` and along `g' ≫ g`.

Stated for reuse: this is Tag 0ATM as an identity of morphisms of functors, so it carries the
naturality of all four factors in the complex. -/
theorem derivedBaseChangeSquare_hpaste (sq₁ : g ≫ f = f' ≫ h) (sq₂ : g' ≫ f' = f'' ≫ h')
    (sq : (g' ≫ g) ≫ f = f'' ≫ h' ≫ h) :
    derivedBaseChangeSquare (g' ≫ g) f'' f (h' ≫ h) sq =
      ((derivedBaseChangeSquare g f' f h sq₁ ≫ᵥ
          derivedBaseChangeSquare g' f'' f' h' sq₂).whiskerRight
            (derivedPullbackCompIsoCanonical h' h).inv).whiskerLeft
        (derivedPullbackCompIsoCanonical g' g).hom := by
  rw [derivedBaseChangeSquare_eq_mateEquiv (g' ≫ g) f'' f (h' ≫ h),
    derivedBaseChangeSquare_eq_mateEquiv g f' f h,
    derivedBaseChangeSquare_eq_mateEquiv g' f'' f' h']
  exact mate_twoSquare_hpaste (derivedAdjunction f) (derivedAdjunction f')
    (derivedAdjunction f'') (derivedPullbackSquare g f' f h sq₁)
    (derivedPullbackSquare g' f'' f' h' sq₂)
    (derivedPullbackSquare (g' ≫ g) f'' f (h' ≫ h) sq)
    (derivedPullbackCompIsoCanonical h' h).inv (derivedPullbackCompIsoCanonical g' g).hom
    (derivedPullbackSquare_hpaste g' g f'' f' f h' h sq₁ sq₂ sq)

/-- **Tag 0ATM.**  Derived base change for an outer rectangle is the composite of derived base
change for its two constituent squares.

For two horizontally composable commutative squares of ringed spaces, the composite of the
inverse composition isomorphism of Tag 0D5S for `h' ≫ h`, the derived pullback along `h'` of the
derived base change map of the right-hand square, the derived base change map of the left-hand
square, and the derived pushforward along `f''` of the composition isomorphism of Tag 0D5S for
`g' ≫ g`, is the derived base change map of the rectangle. -/
@[stacks 0ATM]
theorem derivedBaseChangeMap_comp_horizontal (sq₁ : g ≫ f = f' ≫ h)
    (sq₂ : g' ≫ f' = f'' ≫ h')
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (derivedPullbackCompIsoCanonical h' h).inv.app ((derivedPushforward f).obj K) ≫
        (derivedPullback h').map (derivedBaseChangeMap g f' f h sq₁ K) ≫
        derivedBaseChangeMap g' f'' f' h' sq₂ ((derivedPullback g).obj K) ≫
        (derivedPushforward f'').map ((derivedPullbackCompIsoCanonical g' g).hom.app K) =
      derivedBaseChangeMap (g' ≫ g) f'' f (h' ≫ h)
        (hcomp_square g' g f'' f' f h' h sq₁ sq₂) K := by
  have h₀ := congr_app
    (derivedBaseChangeSquare_hpaste g' g f'' f' f h' h sq₁ sq₂
      (hcomp_square g' g f'' f' f h' h sq₁ sq₂)) K
  simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.assoc] at h₀
  exact h₀.symm

end

end Stacks.Cohomology.DerivedBaseChange

end
