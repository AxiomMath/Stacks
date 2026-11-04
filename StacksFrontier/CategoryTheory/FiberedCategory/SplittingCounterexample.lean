module

import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.NormNum.Parity
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.Data.NNRat.Floor
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Field.ZMod

public import StacksFrontier.CategoryTheory.FiberedCategory.Splitting

/-! # The condition of Stacks 02XX does not imply the unit law

Stacks 02XX characterises split fibred categories by the existence of a choice of pullbacks with
`(f ∘ g)^* = g^* ∘ f^*`. That clause alone does not make the fibres into a presheaf of categories,
because it does not give `𝟙^* = 𝟭`, and this file proves that it does not, so that the unit law in
`CategoryTheory.Functor.ChoiceOfPullbacks.IsSplitting` is pinned down as a repair of the statement
rather than a convenience.

The counterexample is as small as it can be. The base `Pt` has one object and one morphism, so
`(𝟙 ∘ 𝟙)^* = 𝟙^* ∘ 𝟙^*` is the *only* instance of the source's clause; the total category `Ob` has
two objects and exactly one morphism between any two of them, so its two objects are isomorphic but
distinct; and `proj : Ob ⥤ Pt` collapses them. Every morphism of `Ob` is then an isomorphism lying
over the unique morphism of `Pt`, hence strongly cartesian, so *any* assignment of an object of
`Ob` to each pair `(f, x)` is a choice of pullbacks. Choose the object with tag `true` always.

The source's clause holds, both sides of its only instance being constant at the object with tag
`true`. But `𝟙^*` is constant too, so it is not the identity functor: it sends the object with tag
`false` to the one with tag `true`. In the language of
`CategoryTheory.Functor.ChoiceOfPullbacks.CompatibleWithComp.pullbackFunctor_id_comp_self` and
`CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctorIdIso`, `𝟙^*` here is an idempotent
endofunctor naturally isomorphic to the identity and different from it — which is all the source's
clause can rule out.

## Main results

* `CategoryTheory.SplittingCounterexample.compatibleWithComp_not_isSplitting`, the two facts
  together.
-/

@[expose] public section

namespace CategoryTheory.SplittingCounterexample

/-- The base: one object and one morphism. Being a structure with no fields it has definitional
eta, which is what makes every object and every morphism of the base literally the same one. -/
structure Pt : Type where

/-- The total category: two objects, and exactly one morphism between any two of them. -/
structure Ob : Type where
  /-- The `Bool` distinguishing the two objects. -/
  tag : Bool

/-- One object, one morphism. So the only composable pair of morphisms of the base is `(𝟙, 𝟙)`, and
the condition of Stacks 02XX has `(𝟙 ∘ 𝟙)^* = 𝟙^* ∘ 𝟙^*` as its only instance. -/
instance categoryPt : Category.{0} Pt where
  Hom _ _ := PUnit
  id _ := ⟨⟩
  comp _ _ := ⟨⟩

/-- Two objects, exactly one morphism between any two of them. -/
instance categoryOb : Category.{0} Ob where
  Hom _ _ := PUnit
  id _ := ⟨⟩
  comp _ _ := ⟨⟩

/-- Every morphism of `Ob` is an isomorphism, there being only one in each direction. -/
instance obIsIso {x y : Ob} (φ : x ⟶ y) : IsIso φ := ⟨⟨⟩, rfl, rfl⟩

/-- The projection collapsing the two objects of `Ob`. -/
def proj : Ob ⥤ Pt where
  obj _ := ⟨⟩
  map _ := ⟨⟩

/-- Since the base has a single morphism, every morphism of `Ob` lies over it. -/
instance isHomLift {R S : Pt} (f : R ⟶ S) {x y : Ob} (φ : x ⟶ y) : proj.IsHomLift f φ :=
  IsHomLift.map proj φ

/-- Every morphism of `Ob` is strongly cartesian over the unique morphism of the base, being an
isomorphism lying over it. -/
instance isStronglyCartesian {R S : Pt} (f : R ⟶ S) {x y : Ob} (φ : x ⟶ y) :
    proj.IsStronglyCartesian f φ :=
  Functor.IsStronglyCartesian.of_isIso proj f φ

/-- The fibres of `proj` have at most one morphism between any two objects, so every equation
between morphisms of a fibre holds. -/
instance fiberHomSubsingleton {U : Pt} (x y : proj.Fiber U) : Subsingleton (x ⟶ y) :=
  ⟨fun _ _ => Functor.Fiber.hom_ext rfl⟩

/-- The choice of pullbacks that always chooses the object with tag `true`, together with the
unique morphism from it. Any assignment at all is a choice of pullbacks here, every morphism of
`Ob` being strongly cartesian. -/
def choice : proj.ChoiceOfPullbacks where
  obj _ _ := ⟨⟨true⟩, rfl⟩
  map _ _ := ⟨⟩
  isStronglyCartesian f _ := isStronglyCartesian f _

/-- `proj` is a fibred category, as the hypothesis of Stacks 02XX requires: it admits a choice of
pullbacks. -/
instance projIsFibered : proj.IsFibered := choice.isFibered

/-- `choice` chooses the object with tag `true`, whatever it is applied to. -/
@[simp]
lemma choice_obj {V U : Pt} (f : V ⟶ U) (x : proj.Fiber U) :
    choice.obj f x = ⟨⟨true⟩, rfl⟩ := rfl

/-- The source's condition of Stacks 02XX holds for `choice`: its only instance is
`(𝟙 ∘ 𝟙)^* = 𝟙^* ∘ 𝟙^*`, and both sides send every object to the object with tag `true` and every
morphism to the unique morphism. -/
lemma choice_compatibleWithComp : choice.CompatibleWithComp := fun _ _ =>
  Functor.ext (fun _ => rfl) fun _ _ _ => Subsingleton.elim _ _

/-- `choice` is not a splitting: `𝟙^*` sends the object with tag `false` to the object with tag
`true`, so it is not the identity functor. -/
lemma choice_not_isSplitting : ¬ choice.IsSplitting := by
  intro h
  have key : (⟨⟨true⟩, rfl⟩ : proj.Fiber ⟨⟩) = ⟨⟨false⟩, rfl⟩ :=
    Functor.congr_obj (h.pullbackFunctor_id ⟨⟩) _
  exact absurd (congrArg (fun z : proj.Fiber ⟨⟩ => z.1.tag) key) (by decide)

/-- **The literal condition of Stacks 02XX does not imply the unit law `𝟙^* = 𝟭`.** `choice` is a
choice of pullbacks for the fibred category `proj` satisfying `(f ∘ g)^* = g^* ∘ f^*` for every
composable pair of morphisms of the base, and it is not a splitting in the sense of
`CategoryTheory.Functor.ChoiceOfPullbacks.IsSplitting`. So the unit law that definition adds to the
source's clause does not follow from it, and Stacks 02XX cannot be formalised with the source's
clause alone. -/
theorem compatibleWithComp_not_isSplitting :
    choice.CompatibleWithComp ∧ ¬ choice.IsSplitting :=
  ⟨choice_compatibleWithComp, choice_not_isSplitting⟩

end CategoryTheory.SplittingCounterexample

/-! ### Repairing the unit law is still not enough

Adding the unit law to the source's clause — that is, passing from
`CategoryTheory.Functor.ChoiceOfPullbacks.CompatibleWithComp` to
`CategoryTheory.Functor.ChoiceOfPullbacks.IsSplitting` — does *not* repair Stacks 02XX. Both
clauses constrain only the pullback *functors*; neither says anything about the chosen cartesian
*lifts* beyond what the functors determine, and splitness constrains the lifts.

Concretely, let `p : 𝒳 ⥤ 𝒮` be the one-object categories attached to the non-split central
extension `ℤ/4 ↠ ℤ/2`: `𝒮` has one object with automorphism group `ℤ/2`, `𝒳` has one object with
automorphism group `ℤ/4`, and `p` is reduction. Every morphism of `𝒳` is invertible, hence strongly
cartesian, so *any* set-theoretic section of `ℤ/4 → ℤ/2` is a choice of pullbacks; and the
extension is central, so conjugation by the chosen lift is trivial and *every* pullback functor is
`𝟭` on the nose. So `IsSplitting` holds. But `𝒮_F` for a genuine functor `F : 𝒮ᵒᵖ ⥤ Cat` has
automorphism group a semidirect product `A ⋊ ℤ/2`, which contains an element of order two over the
generator of `ℤ/2`, and `ℤ/4` contains none; so `p` is not split.

The correct repair therefore has to constrain the lifts, not the functors; see
`CategoryTheory.Functor.ChoiceOfPullbacks.IsSplitCleavage`.
-/

set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.SplitCleavageCounterexample

open Opposite Pseudofunctor Pseudofunctor.CoGrothendieck

/-- `ℤ/4` written multiplicatively: the automorphism group of the total category. -/
abbrev Cyc4 := Multiplicative (ZMod 4)

/-- `ℤ/2` written multiplicatively: the automorphism group of the base. -/
abbrev Cyc2 := Multiplicative (ZMod 2)

/-- Reduction `ℤ/4 → ℤ/2`. -/
abbrev red : ZMod 4 →+ ZMod 2 := (ZMod.castHom (by decide) (ZMod 2)).toAddMonoidHom

/-- Reduction, written multiplicatively. -/
abbrev redMul : Cyc4 →* Cyc2 := AddMonoidHom.toMultiplicative red

/-- The total category: one object, automorphism group `ℤ/4`. -/
abbrev Tot := SingleObj Cyc4

/-- The base: one object, automorphism group `ℤ/2`. -/
abbrev Bse := SingleObj Cyc2

/-- The projection, i.e. the non-split central extension `ℤ/4 ↠ ℤ/2` read as a functor. -/
def proj : Tot ⥤ Bse := SingleObj.mapHom _ _ redMul

/-- `proj` acts on morphisms as the reduction `redMul`. -/
@[simp] lemma proj_map {x y : Tot} (φ : x ⟶ y) : proj.map φ = redMul φ := rfl

/-- The set-theoretic section of reduction sending `i` to `i`. -/
def sec (a : Cyc2) : Cyc4 := Multiplicative.ofAdd ((Multiplicative.toAdd a).val : ZMod 4)

/-- Reduction sends the `ZMod 4` lift of `b : ZMod 2` given by `b.val` back to `b`. -/
lemma red_val (b : ZMod 2) : red ((b.val : ZMod 4)) = b := by revert b; decide +kernel

/-- `sec` is a section of `redMul`. -/
@[simp] lemma redMul_sec (a : Cyc2) : redMul (sec a) = a :=
  congrArg Multiplicative.ofAdd (red_val (Multiplicative.toAdd a))

/-- `sec`, read as a morphism between two prescribed objects of the total category. -/
def secHom {V U : Bse} (f : V ⟶ U) (x y : Tot) : x ⟶ y := sec f

/-- `proj` sends `secHom f x y` to `f`. -/
@[simp] lemma proj_map_secHom {V U : Bse} (f : V ⟶ U) (x y : Tot) :
    proj.map (secHom f x y) = f := redMul_sec f

/-- A morphism of the total category lies over any morphism of the base it is sent to. -/
lemma isHomLift_of_map_eq {V U : Bse} {x y : Tot} (f : V ⟶ U) (φ : x ⟶ y)
    (h : proj.map φ = f) : proj.IsHomLift f φ := by rw [← h]; infer_instance

/-- `CategoryTheory.SplitCleavageCounterexample.secHom f x y` lies over `f`. -/
instance isHomLiftSecHom {V U : Bse} (f : V ⟶ U) (x y : Tot) :
    proj.IsHomLift f (secHom f x y) :=
  isHomLift_of_map_eq f _ (proj_map_secHom f x y)

/-- Every morphism of the total category is invertible, hence strongly cartesian over the morphism
of the base that it lifts. -/
instance isStronglyCartesianSecHom {V U : Bse} (f : V ⟶ U) (x y : Tot) :
    proj.IsStronglyCartesian f (secHom f x y) :=
  Functor.IsStronglyCartesian.of_isIso proj f _

/-- Each fibre of `proj` has at most one object, the total category having only one. -/
instance fiberSubsingleton (U : Bse) : Subsingleton (proj.Fiber U) :=
  ⟨fun _ _ => Subtype.ext (Subsingleton.elim _ _)⟩

/-- The choice of pullbacks given by the section `sec`: since every morphism of the total category
is strongly cartesian, any section at all will do. -/
def cleaving : proj.ChoiceOfPullbacks where
  obj _ _ := ⟨SingleObj.star Cyc4, Subsingleton.elim _ _⟩
  map f _ := secHom f _ _
  isStronglyCartesian f _ := isStronglyCartesianSecHom f _ _

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion
  Functor.ChoiceOfPullbacks.pullbackFunctor cleaving proj

/-- The chosen pullback morphism of `cleaving` over `f` is `secHom f`. -/
@[simp] lemma cleaving_map {V U : Bse} (f : V ⟶ U) (x : proj.Fiber U) :
    cleaving.map f x = secHom f _ _ := rfl

/-- Every pullback functor of `cleaving` is the identity on morphisms: the extension is central, so
conjugation by the chosen lift is trivial. -/
lemma cleaving_homMap_val {V U : Bse} (f : V ⟶ U) {x x' : proj.Fiber U} (α : x ⟶ x') :
    Functor.Fiber.fiberInclusion.map (cleaving.homMap f α) =
      Functor.Fiber.fiberInclusion.map α := by
  have h := cleaving.homMap_fac f α
  simp only [cleaving_map, SingleObj.comp_as_mul, secHom] at h
  exact mul_left_cancel (a := sec f) (by rw [h, mul_comm])

/-- Every object of the total category is `star`, so every `eqToHom` in it is an identity. -/
lemma eqToHom_tot {x y : Tot} (h : x = y) : eqToHom h = 𝟙 x := by subst h; rfl

/-- Likewise in the base. -/
lemma eqToHom_bse {x y : Bse} (h : x = y) : eqToHom h = 𝟙 x := by subst h; rfl

/-- `ℤ/4` has no element of order dividing two above the generator of `ℤ/2`: this is exactly the
non-splitness of the extension. -/
lemma no_order_two_lift : ∀ n : ZMod 4, n + n = 0 → red n ≠ 1 := by decide +kernel

/-- The pullback functors of `cleaving` satisfy the unit law `𝟙^* = 𝟭` on the nose. -/
lemma cleaving_pullbackFunctor_id (U : Bse) :
    cleaving.pullbackFunctor (𝟙 U) = 𝟭 (proj.Fiber U) :=
  Functor.ext (fun _ => rfl) fun _ _ _ =>
    Functor.Fiber.hom_ext (by simp [cleaving_homMap_val])

/-- The pullback functors of `cleaving` satisfy `(f ∘ g)^* = g^* ∘ f^*` on the nose. -/
lemma cleaving_compatibleWithComp : cleaving.CompatibleWithComp := fun _ _ =>
  Functor.ext (fun _ => rfl) fun _ _ _ =>
    Functor.Fiber.hom_ext (by simp [cleaving_homMap_val])

/-- `cleaving` satisfies the unit law and the composition law for pullback functors, i.e. it is a
splitting in the sense of `CategoryTheory.Functor.ChoiceOfPullbacks.IsSplitting`. -/
lemma cleaving_isSplitting : cleaving.IsSplitting :=
  ⟨cleaving_pullbackFunctor_id, cleaving_compatibleWithComp⟩

/-- The generator of the base's automorphism group. -/
def gen : Cyc2 := Multiplicative.ofAdd (1 : ZMod 2)

/-- `gen`, read as an endomorphism of a prescribed object of the base. -/
def baseGenHom (x y : Bse) : x ⟶ y := gen

/-- The generator of `ℤ/2` has order two. -/
lemma gen_mul_gen : gen * gen = 1 :=
  show Multiplicative.ofAdd ((1 : ZMod 2) + 1) = Multiplicative.ofAdd (0 : ZMod 2) from
    congrArg Multiplicative.ofAdd (by decide)

/-- `CategoryTheory.SplitCleavageCounterexample.baseGenHom` composed with itself is the
identity. -/
lemma baseGenHom_comp (x : Bse) : baseGenHom x x ≫ baseGenHom x x = 𝟙 x := by
  rw [SingleObj.comp_as_mul, SingleObj.id_as_one]; exact gen_mul_gen

/-- `proj` is not split: an isomorphism over the base with `𝒮_F` would produce an endomorphism of
order dividing two over the generator of `ℤ/2`, and `ℤ/4` has none. -/
theorem not_isSplitFibered : ¬ proj.IsSplitFibered := by
  rintro ⟨-, F, Gf, Hf, hGH, hHG⟩
  have hTot : Subsingleton (BasedCategory.ofFunctor proj).obj := inferInstanceAs (Subsingleton Tot)
  have hsub : Subsingleton (∫ᶜ F.toPseudofunctor') := ⟨fun X Y =>
    (Functor.congr_obj hHG X).symm.trans <|
      (congrArg Gf.toFunctor.obj (Subsingleton.elim _ _)).trans (Functor.congr_obj hHG Y)⟩
  set X₀ : ∫ᶜ F.toPseudofunctor' := Gf.toFunctor.obj (SingleObj.star Cyc4)
  have hfib (y y' : F.toPseudofunctor'.obj ⟨op X₀.base⟩) : y = y' := by
    simpa using (hsub.elim _ _ : (⟨X₀.base, y⟩ : ∫ᶜ F.toPseudofunctor') = ⟨X₀.base, y'⟩)
  let w : X₀ ⟶ X₀ := { base := baseGenHom X₀.base X₀.base, fiber := eqToHom (hfib _ _) }
  have hw : w ≫ w = 𝟙 X₀ := by
    refine CoGrothendieck.Hom.ext _ _ (baseGenHom_comp X₀.base) ?_
    simp [w, Cat.Hom₂.eqToHom_toNatTrans, eqToHom_map]
  refine no_order_two_lift (Multiplicative.toAdd (Hf.toFunctor.map w)) ?_ ?_
  · have h2 : Hf.toFunctor.map w ≫ Hf.toFunctor.map w = 𝟙 _ := by
      rw [← Hf.toFunctor.map_comp, hw, Hf.toFunctor.map_id]
    rw [SingleObj.comp_as_mul, SingleObj.id_as_one] at h2
    exact congrArg Multiplicative.toAdd h2
  · have hb := Functor.congr_hom Hf.w w
    simp only [Functor.comp_map, eqToHom_bse, Category.id_comp, Category.comp_id] at hb
    exact congrArg Multiplicative.toAdd hb

/-- **The unit law does not repair Stacks 02XX.** `cleaving` is a choice of pullbacks for the
fibred category `proj` whose pullback functors satisfy both the unit law `𝟙^* = 𝟭` and the
composition law `(f ∘ g)^* = g^* ∘ f^*` on the nose, and `proj` is nevertheless not split. So
`CategoryTheory.Functor.ChoiceOfPullbacks.IsSplitting` does not characterise splitness either, and
the repair has to constrain the chosen cartesian lifts; see
`CategoryTheory.Functor.ChoiceOfPullbacks.IsSplitCleavage`. -/
theorem isSplitting_not_isSplitFibered :
    cleaving.IsSplitting ∧ ¬ proj.IsSplitFibered :=
  ⟨cleaving_isSplitting, not_isSplitFibered⟩

end CategoryTheory.SplitCleavageCounterexample
