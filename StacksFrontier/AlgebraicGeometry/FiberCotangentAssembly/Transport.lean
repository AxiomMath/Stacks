module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Transporting a stalk along an equality of morphisms

`AlgebraicGeometry.Scheme.Hom.stalkMap` and `AlgebraicGeometry.Scheme.stalkClosedPointTo` are
indexed by a morphism, and their types mention the action of that morphism on a point.  This
file compares them along an equality of morphisms, or of points, through the comparison
`TopCat.Presheaf.stalkCongr` of the stalks at the two points, and collapses chains of such
comparisons.

## Main results

* `Stacks.FiberCotangentAssembly.stalkMap_eq_of_eq`: an equality of morphisms transported through
  `AlgebraicGeometry.Scheme.Hom.stalkMap`.
* `Stacks.FiberCotangentAssembly.stalkClosedPointTo_eq_of_eq`: an equality of morphisms out of
  the spectrum of a local ring, transported through
  `AlgebraicGeometry.Scheme.stalkClosedPointTo`.
* `Stacks.FiberCotangentAssembly.stalkCongr_hom_comp` and
  `stalkCongr_hom_comp_three`: chains of comparisons collapse.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.FiberCotangentAssembly

/-- **An equality of morphisms of schemes transported through
`AlgebraicGeometry.Scheme.Hom.stalkMap`.**  If `a = a'` then the two stalk maps at `x` agree,
after the comparison of the stalks at `a x` and `a' x`. -/
public theorem stalkMap_eq_of_eq {X Y : Scheme.{u}} {a a' : X ⟶ Y} (e : a = a') (x : X)
    (h : Inseparable (a x) (a' x)) :
    Scheme.Hom.stalkMap a x =
      (Y.presheaf.stalkCongr h).hom ≫ Scheme.Hom.stalkMap a' x := by
  subst e
  simp

/-- **An equality of morphisms out of the spectrum of a local ring transported through
`AlgebraicGeometry.Scheme.stalkClosedPointTo`.**  If `g = g'` then the two induced local
homomorphisms agree, after the comparison of the stalks at the images of the closed point. -/
public theorem stalkClosedPointTo_eq_of_eq {X : Scheme.{u}} {K : CommRingCat.{u}} [IsLocalRing K]
    {g g' : Spec K ⟶ X} (e : g = g')
    (h : Inseparable (g (IsLocalRing.closedPoint K)) (g' (IsLocalRing.closedPoint K))) :
    Scheme.stalkClosedPointTo g =
      (X.presheaf.stalkCongr h).hom ≫ Scheme.stalkClosedPointTo g' := by
  subst e
  simp

/-- **An equality of points transported through `AlgebraicGeometry.Scheme.Hom.stalkMap`.**  The
stalk maps of one morphism at two equal points agree, after the comparisons of the stalks at
both ends. -/
public theorem stalkMap_eq_of_point_eq {X Y : Scheme.{u}} (a : X ⟶ Y) {p q : X} (e : p = q)
    (hX : Inseparable q p) (hY : Inseparable (a p) (a q)) :
    Scheme.Hom.stalkMap a p =
      (Y.presheaf.stalkCongr hY).hom ≫ Scheme.Hom.stalkMap a q ≫
        (X.presheaf.stalkCongr hX).hom := by
  subst e
  simp

/-- **Two stalk comparisons compose to the comparison of the composite.** -/
@[reassoc]
public theorem stalkCongr_hom_comp {T : TopCat.{u}} (F : T.Presheaf CommRingCat.{u}) {p q r : T}
    (h₁ : Inseparable p q) (h₂ : Inseparable q r) :
    (F.stalkCongr h₁).hom ≫ (F.stalkCongr h₂).hom = (F.stalkCongr (h₁.trans h₂)).hom :=
  F.stalkSpecializes_comp h₂.ge h₁.ge

/-- **A stalk comparison between a point and itself is the identity.** -/
public theorem stalkCongr_hom_refl {T : TopCat.{u}} (F : T.Presheaf CommRingCat.{u}) {p : T}
    (h : Inseparable p p) : (F.stalkCongr h).hom = 𝟙 _ :=
  F.stalkSpecializes_refl p

/-- **A round trip of three stalk comparisons is the identity.** -/
public theorem stalkCongr_hom_comp_three {T : TopCat.{u}} (F : T.Presheaf CommRingCat.{u})
    {p q r : T} (h₁ : Inseparable p q) (h₂ : Inseparable q r) (h₃ : Inseparable r p)
    {Z : CommRingCat.{u}} (k : F.stalk p ⟶ Z) :
    (F.stalkCongr h₁).hom ≫ (F.stalkCongr h₂).hom ≫ (F.stalkCongr h₃).hom ≫ k = k := by
  rw [stalkCongr_hom_comp_assoc, stalkCongr_hom_comp_assoc, stalkCongr_hom_refl,
    Category.id_comp]

/-- **A round trip of two stalk comparisons is the identity.** -/
public theorem stalkCongr_hom_comp_two {T : TopCat.{u}} (F : T.Presheaf CommRingCat.{u})
    {p q : T} (h₁ : Inseparable p q) (h₂ : Inseparable q p) {Z : CommRingCat.{u}}
    (k : F.stalk p ⟶ Z) :
    (F.stalkCongr h₁).hom ≫ (F.stalkCongr h₂).hom ≫ k = k := by
  rw [stalkCongr_hom_comp_assoc, stalkCongr_hom_refl, Category.id_comp]

/-- **A germ followed by a stalk comparison is the germ at the other point.** -/
@[reassoc]
public theorem germ_stalkCongr {T : TopCat.{u}} (F : T.Presheaf CommRingCat.{u})
    {U : Opens T} {p q : T} (hp : p ∈ U) (h : Inseparable p q) (hq : q ∈ U) :
    F.germ U p hp ≫ (F.stalkCongr h).hom = F.germ U q hq :=
  F.germ_stalkSpecializes hp h.ge

/-- **One stalk comparison split as two.** -/
public theorem stalkCongr_hom_eq_comp {T : TopCat.{u}} (F : T.Presheaf CommRingCat.{u})
    {p q r : T} (h : Inseparable p q) (h₁ : Inseparable p r) (h₂ : Inseparable r q)
    {Z : CommRingCat.{u}} (m : F.stalk q ⟶ Z) :
    (F.stalkCongr h).hom ≫ m =
      (F.stalkCongr h₁).hom ≫ (F.stalkCongr h₂).hom ≫ m := by
  rw [stalkCongr_hom_comp_assoc]

end Stacks.FiberCotangentAssembly

end
