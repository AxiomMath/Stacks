module

import StacksFrontier.CategoryTheory.FiberedCategory.HomLift
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

public import StacksFrontier.CategoryTheory.Sites.Gerbe.Basic
public import StacksFrontier.CategoryTheory.Sites.Gerbe.Defs
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Factorization

/-! # Being a gerbe is invariant under equivalence over the base

Stacks 06P0 says that two categories over a site `𝒞` that are equivalent *as categories over
`𝒞`* are gerbes over `𝒞` at the same time. The notion of equivalence at play is the one of the
2-category of categories over `𝒞`: the quasi-inverse is again a 1-morphism over `𝒞` and the
unit and counit are vertical. That is `CategoryTheory.Functor.IsEquivalenceOver`, from the
factorization lemma Stacks 06N7; a mere equivalence of the underlying categories does not
suffice, since the inclusion of a one-object skeleton of an indiscrete groupoid `𝒞` into `𝒞`
is an equivalence over `𝒞` in that weaker sense while failing to be fibred in groupoids.

This file proves the invariance of the weaker notion `CategoryTheory.IsGerbeOver J q F`,
relatively to an arbitrary base `q : 𝒴 ⥤ 𝒞`. As `isGerbeOver_id_iff` records,
`IsGerbeOver J (𝟭 𝒞) p` unfolds to the three conditions of Stacks 06NZ with "stack in groupoids"
weakened to "fibred in groupoids", so that invariance alone does not give Stacks 06P0. Stacks 06P0
itself, for `CategoryTheory.Functor.IsGerbe`, is
`CategoryTheory.Functor.isGerbe_iff_of_isEquivalenceOver` in
`StacksFrontier/CategoryTheory/Sites/Gerbe/EquivalenceStack.lean`, which adds the stack clause.

## Main results

* `CategoryTheory.Functor.IsFiberedInGroupoids.of_isEquivalenceOver`: being fibred in
  groupoids transports along an equivalence over the base. This is the "fibred in groupoids"
  counterpart of Stacks 042X, which the proof of 06P0 cites for stacks in groupoids.
* `CategoryTheory.isGerbeOver_id_iff`: `IsGerbeOver J (𝟭 𝒞) p` is the definition Stacks 06NZ
  of a gerbe over the site `(𝒞, J)`, clause by clause, and
  `CategoryTheory.Functor.IsGerbe.isGerbeOver_id`: a gerbe over `(𝒞, J)` is one of these.
* `CategoryTheory.IsGerbeOver.of_isEquivalenceOver` and
  `CategoryTheory.isGerbeOver_iff_of_isEquivalenceOver`: invariance of `IsGerbeOver`, the
  relative notion in which "stack in groupoids" is weakened to "fibred in groupoids".
-/

@[expose] public section

namespace CategoryTheory

universe w v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace Functor

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟]
  {𝒳 : Type u₃} [Category.{v₃} 𝒳] {𝒳' : Type u₄} [Category.{v₄} 𝒳']

/-- A natural transformation that is vertical over `𝒞` stays vertical after composing the
structure functor with a further functor `t : 𝒞 ⥤ 𝒟`. -/
lemma IsVerticalNatTrans.comp_right {s : 𝒳 ⥤ 𝒞} {F G : 𝒳' ⥤ 𝒳} {α : F ⟶ G}
    (h : IsVerticalNatTrans s α) (t : 𝒞 ⥤ 𝒟) : IsVerticalNatTrans (s ⋙ t) α := fun X => by
  obtain ⟨hobj, hmap⟩ := (IsHomLift.id_iff_exists_eqToHom s (α.app X)).1 (h X)
  exact (IsHomLift.id_iff_exists_eqToHom (s ⋙ t) (α.app X)).2
    ⟨congrArg t.obj hobj, by simp [hmap, eqToHom_map]⟩

variable {p : 𝒳 ⥤ 𝒞} {r : 𝒳' ⥤ 𝒞} {a : 𝒳 ⥤ 𝒳'}

/-- The quasi-inverse of an equivalence over `𝒞` is again one, in the other direction. The
1-morphism condition `a ⋙ r = p` on `a`, which `IsEquivalenceOver` does not carry, is what
becomes the 1-morphism condition on the quasi-inverse. -/
def IsEquivalenceOver.symm (e : IsEquivalenceOver p r a) (ha : a ⋙ r = p) :
    IsEquivalenceOver r p e.inv where
  inv := a
  inv_over := ha
  unitIso := e.counitIso
  counitIso := e.unitIso
  unit_vertical := e.counit_vertical
  counit_vertical := e.unit_vertical

/-- An equivalence over `𝒞` induces an equivalence over `𝒟` for any `t : 𝒞 ⥤ 𝒟`, by
composing the structure functors with `t`. -/
def IsEquivalenceOver.compRight (e : IsEquivalenceOver p r a) (t : 𝒞 ⥤ 𝒟) :
    IsEquivalenceOver (p ⋙ t) (r ⋙ t) a where
  inv := e.inv
  inv_over := by rw [← Functor.assoc, e.inv_over]
  unitIso := e.unitIso
  counitIso := e.counitIso
  unit_vertical := e.unit_vertical.comp_right t
  counit_vertical := e.counit_vertical.comp_right t

/-- A functor with a two-sided quasi-inverse is faithful. This is
`CategoryTheory.Equivalence.faithful_inverse` for the unbundled data of an
`IsEquivalenceOver`, so that it stays available after destructuring one. -/
lemma Faithful.of_quasiInverse {b : 𝒳' ⥤ 𝒳} (unitIso : a ⋙ b ≅ 𝟭 𝒳)
    (counitIso : b ⋙ a ≅ 𝟭 𝒳') : b.Faithful :=
  Equivalence.faithful_inverse (.mk a b unitIso.symm counitIso)

/-- A functor with a two-sided quasi-inverse is full. This is
`CategoryTheory.Equivalence.full_inverse` for the unbundled data of an `IsEquivalenceOver`,
so that it stays available after destructuring one. -/
lemma Full.of_quasiInverse {b : 𝒳' ⥤ 𝒳} (unitIso : a ⋙ b ≅ 𝟭 𝒳)
    (counitIso : b ⋙ a ≅ 𝟭 𝒳') : b.Full :=
  Equivalence.full_inverse (.mk a b unitIso.symm counitIso)

/-- A morphism of a category fibred in groupoids lying over an identity is an isomorphism:
the fibres are groupoids. -/
lemma IsFiberedInGroupoids.isIso_of_isHomLift_id (hp : p.IsFiberedInGroupoids) {U : 𝒞}
    {x y : 𝒳} (α : x ⟶ y) (hα : p.IsHomLift (𝟙 U) α) : IsIso α := by
  have := hp.isStronglyCartesian_homLift (𝟙 U) α
  exact IsStronglyCartesian.isIso_of_base_isIso (p := p) (f := 𝟙 U) α

/-- The identity functor exhibits `𝒞` as fibred in groupoids over itself: a base morphism is
its own unique lift. -/
lemma isFiberedInGroupoids_id : (𝟭 𝒞).IsFiberedInGroupoids where
  exists_lift := by
    rintro V U f x rfl
    exact ⟨V, f, IsHomLift.map (p := 𝟭 𝒞) f⟩
  unique_lift := fun φ ψ f hf => ⟨f, ⟨rfl, hf⟩, fun _ hχ => hχ.1⟩

/-- If `χ` lies over `f` after composing with `a`, and `ψ` lies over an identity, then `a.map χ ≫ ψ`
lies over `f`. -/
private lemma isHomLift_map_comp {s : 𝒳' ⥤ 𝒞} {a : 𝒳 ⥤ 𝒳'} {x y : 𝒳} {z : 𝒳'} {U V : 𝒞}
    {f : V ⟶ U} {χ : x ⟶ y} {ψ : a.obj y ⟶ z} (hχ : (a ⋙ s).IsHomLift f χ)
    (hψ : s.IsHomLift (𝟙 U) ψ) : s.IsHomLift f (a.map χ ≫ ψ) := by
  have := (Functor.isHomLift_comp_iff a s f χ).1 hχ
  simpa using IsHomLift.comp s f (𝟙 U) (a.map χ) ψ

/-- **Stacks 042X**, the half about being fibred in groupoids: if `a : 𝒳 ⥤ 𝒳'` is a
1-morphism over `𝒞` which is an equivalence over `𝒞`, and `𝒳` is fibred in groupoids over
`𝒞`, then so is `𝒳'`.

Both axioms are transported through the quasi-inverse `e.inv`: an object of `𝒳'` over `U`
comes from one of `𝒳` over `U` because `e.inv` is strictly over `𝒞`, and the fill-ins
correspond because `e.inv` is fully faithful. -/
lemma IsFiberedInGroupoids.of_isEquivalenceOver (ha : a ⋙ r = p)
    (e : IsEquivalenceOver p r a) (hp : p.IsFiberedInGroupoids) : r.IsFiberedInGroupoids := by
  obtain ⟨b, hb, unitIso, counitIso, -, hcv⟩ := e
  subst hb
  have := Full.of_quasiInverse unitIso counitIso
  have := Faithful.of_quasiInverse unitIso counitIso
  constructor
  · intro V U g A hA
    -- the counit at `A` is a vertical morphism `a (b A) ⟶ A`, so `a (b A)` lies over `U` too
    have hcvA := hcv A
    have hsrc : (b ⋙ p).obj ((b ⋙ a).obj A) = U :=
      (IsHomLift.codomain_eq (b ⋙ p) (𝟙 ((b ⋙ p).obj ((b ⋙ a).obj A)))
        (counitIso.hom.app A)).symm.trans hA
    rw [hsrc] at hcvA
    obtain ⟨x, χ, hχ⟩ := hp.exists_lift g (b.obj A) hA
    exact ⟨a.obj x, a.map χ ≫ counitIso.hom.app A, isHomLift_map_comp (by rwa [ha]) hcvA⟩
  · intro X Y Z φ ψ f hf
    obtain ⟨k, ⟨hk₁, hk₂⟩, hkuniq⟩ := hp.unique_lift (b.map φ) (b.map ψ) f hf
    refine ⟨b.preimage k, ⟨by simpa using hk₁, b.map_injective (by simp [hk₂])⟩, ?_⟩
    rintro χ ⟨hχ₁, hχ₂⟩
    exact b.map_injective ((hkuniq (b.map χ) ⟨hχ₁, by rw [← b.map_comp, hχ₂]⟩).trans
      (b.map_preimage k).symm)

end Functor

variable {𝒞 : Type u₁} {𝒳 : Type u₂} {𝒳' : Type u₃} {𝒴 : Type u₄}
  [Category.{v₁} 𝒞] [Category.{v₂} 𝒳] [Category.{v₃} 𝒳'] [Category.{v₄} 𝒴]

/-- `IsGerbeOver J (𝟭 𝒞) p` is precisely the definition Stacks 06NZ of a *gerbe over the site*
`(𝒞, J)`, clause by clause: it is `CategoryTheory.Functor.LocallyNonempty` (06NZ (2)) and
`CategoryTheory.Functor.LocallyConnected` (06NZ (3)) together with `p` being fibred in
groupoids, which weakens 06NZ (1) — a stack in groupoids — exactly as `IsGerbeOver` does. -/
theorem isGerbeOver_id_iff (J : GrothendieckTopology 𝒞) (p : 𝒳 ⥤ 𝒞) :
    IsGerbeOver J (𝟭 𝒞) p ↔
      p.IsFiberedInGroupoids ∧ p.LocallyNonempty J ∧ p.LocallyConnected J := by
  have hcomp : p ⋙ 𝟭 𝒞 = p := p.comp_id
  constructor
  · intro h
    refine ⟨hcomp ▸ h.isFiberedInGroupoids, fun U => ?_, ?_⟩
    · obtain ⟨S, hS, hcov⟩ := h.locally_essSurj U rfl
      refine ⟨S, hS, fun V f hf => ?_⟩
      obtain ⟨x, ψ, hψ⟩ := hcov f hf
      exact ⟨⟨x, IsHomLift.domain_eq (𝟭 𝒞) f ψ⟩⟩
    · intro U x y hx hy
      have hb : (𝟭 𝒞).IsHomLift (𝟙 U) (eqToHom (hx.trans hy.symm) : p.obj x ⟶ p.obj y) :=
        IsHomLift.of_fac' (𝟭 𝒞) (𝟙 U) _ hx hy (by simp)
      obtain ⟨S, hS, hcov⟩ := h.locally_full (eqToHom (hx.trans hy.symm)) hb
      refine ⟨S, hS, fun V f hf => ?_⟩
      obtain ⟨x₁, y₁, ξ, η, α, hξ, hη, hα, -⟩ := hcov f hf
      have hα' : p.IsHomLift (𝟙 V) α := hcomp ▸ hα
      have := (hcomp ▸ h.isFiberedInGroupoids : p.IsFiberedInGroupoids).isIso_of_isHomLift_id
        α hα'
      exact ⟨x₁, y₁, ξ, η, asIso α, hcomp ▸ hξ, hcomp ▸ hη, hα'⟩
  · rintro ⟨hp, h₂, h₃⟩
    refine ⟨Functor.isFiberedInGroupoids_id, hcomp ▸ hp, ?_, ?_⟩
    · rintro U y rfl
      obtain ⟨S, hS, hcov⟩ := h₂ ((𝟭 𝒞).obj y)
      refine ⟨S, hS, fun V f hf => ?_⟩
      obtain ⟨⟨x, hxV⟩⟩ := hcov f hf
      exact ⟨x, eqToHom hxV ≫ f, IsHomLift.of_fac' (𝟭 𝒞) f _ hxV rfl (by simp)⟩
    · intro U x x' b hb
      have hx : p.obj x = U := IsHomLift.domain_eq (𝟭 𝒞) (𝟙 U) b
      have hx' : p.obj x' = U := IsHomLift.codomain_eq (𝟭 𝒞) (𝟙 U) b
      have hbeq : b = eqToHom hx ≫ eqToHom hx'.symm := by
        simpa using IsHomLift.fac' (𝟭 𝒞) (𝟙 U) b
      obtain ⟨S, hS, hcov⟩ := h₃ x x' hx hx'
      refine ⟨S, hS, fun V f hf => ?_⟩
      obtain ⟨x₁, y₁, ξ, η, α, hξ, hη, hα⟩ := hcov f hf
      refine ⟨x₁, y₁, ξ, η, α.hom, hcomp ▸ hξ, hcomp ▸ hη, hcomp ▸ hα, ?_⟩
      rw [IsHomLift.fac' p (𝟙 V) α.hom, IsHomLift.fac' p f η, IsHomLift.fac' p f ξ, hbeq]
      simp

/-- A gerbe over the site `(𝒞, J)` in the sense of Stacks 06NZ is a gerbe over `𝒞` in the
sense of `CategoryTheory.IsGerbeOver`, whose hypothesis on the total category is being fibred
in groupoids rather than being a stack in groupoids. -/
theorem Functor.IsGerbe.isGerbeOver_id {J : GrothendieckTopology 𝒞} {p : 𝒳 ⥤ 𝒞}
    (h : p.IsGerbe.{w} J) : IsGerbeOver J (𝟭 𝒞) p :=
  (isGerbeOver_id_iff J p).mpr ⟨h.1.isFiberedInGroupoids, h.2.left, h.2.right⟩

namespace IsGerbeOver

variable {J : GrothendieckTopology 𝒞} {q : 𝒴 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒴} {F' : 𝒳' ⥤ 𝒴} {a : 𝒳 ⥤ 𝒳'}

/-- Invariance of `IsGerbeOver`, one direction and in the relative form: if `a : 𝒳 ⥤ 𝒳'` is a
1-morphism over `𝒴` (so `a ⋙ F' = F`) which is an equivalence over `𝒴`, then `F` makes `𝒳` a
gerbe over `𝒴` in the sense of `IsGerbeOver` (with "stack in groupoids" weakened to "fibred in
groupoids") only if `F'` makes `𝒳'` one.

Both local conditions transport along `a`: an object of `𝒳` over a covering member has the
same `F'`-image as its `a`-image, and a morphism between `F'`-images is carried to a morphism
between `F`-images by the counit, whose components are `F'`-vertical. -/
theorem of_isEquivalenceOver (ha : a ⋙ F' = F) (e : Functor.IsEquivalenceOver F F' a)
    (h : IsGerbeOver J q F) : IsGerbeOver J q F' := by
  subst ha
  refine ⟨h.base_isFiberedInGroupoids,
    Functor.IsFiberedInGroupoids.of_isEquivalenceOver (by rw [Functor.assoc])
      (e.compRight q) h.isFiberedInGroupoids, ?_, ?_⟩
  · intro U y hy
    obtain ⟨S, hS, hcov⟩ := h.locally_essSurj y hy
    refine ⟨S, hS, fun V f hf => ?_⟩
    obtain ⟨x, ψ, hψ⟩ := hcov f hf
    exact ⟨a.obj x, ψ, hψ⟩
  · intro U x x' b hb
    -- transport `b` to a morphism between the images of `e.inv x` and `e.inv x'`
    obtain ⟨hcx, hcxeq⟩ :=
      (IsHomLift.id_iff_exists_eqToHom F' (e.counitIso.hom.app x)).1 (e.counit_vertical x)
    obtain ⟨hcx', hcx'eq⟩ :=
      (IsHomLift.id_iff_exists_eqToHom F' (e.counitIso.hom.app x')).1 (e.counit_vertical x')
    have hU : q.obj (F'.obj x) = U := IsHomLift.domain_eq q (𝟙 U) b
    have hverU : ∀ z : 𝒳', ∀ h : F'.obj ((e.inv ⋙ a).obj z) = F'.obj z,
        F'.map (e.counitIso.hom.app z) = eqToHom h → q.obj (F'.obj z) = U →
        (F' ⋙ q).IsHomLift (𝟙 U) (e.counitIso.hom.app z) := fun z h heq hz =>
      IsHomLift.of_fac' (F' ⋙ q) (𝟙 U) _ ((congrArg q.obj h).trans hz) hz
        (by simp [heq, eqToHom_map])
    have hb₁ : q.IsHomLift (𝟙 U) (eqToHom hcx ≫ b ≫ eqToHom hcx'.symm) := inferInstance
    obtain ⟨S, hS, hcov⟩ :=
      h.locally_full (x := e.inv.obj x) (x' := e.inv.obj x')
        (eqToHom hcx ≫ b ≫ eqToHom hcx'.symm) hb₁
    refine ⟨S, hS, fun V f hf => ?_⟩
    obtain ⟨x₁, x₁', ξ, ξ', α, hξ, hξ', hα, heq⟩ := hcov f hf
    have hcU := hverU x hcx hcxeq hU
    have hc'U := hverU x' hcx' hcx'eq (IsHomLift.codomain_eq q (𝟙 U) b)
    refine ⟨a.obj x₁, a.obj x₁', a.map ξ ≫ e.counitIso.hom.app x,
      a.map ξ' ≫ e.counitIso.hom.app x', a.map α, ?_, ?_, ?_, ?_⟩
    · exact Functor.isHomLift_map_comp hξ hcU
    · exact Functor.isHomLift_map_comp hξ' hc'U
    · exact (Functor.isHomLift_comp_iff a (F' ⋙ q) (𝟙 V) α).1 hα
    · rw [F'.map_comp, F'.map_comp, hcxeq, hcx'eq]
      have : F'.map (a.map α) ≫ F'.map (a.map ξ')
          = F'.map (a.map ξ) ≫ eqToHom hcx ≫ b ≫ eqToHom hcx'.symm := heq
      rw [← Category.assoc, this]
      simp

end IsGerbeOver

/-- Invariance of `IsGerbeOver` under equivalence, in the relative form: a 1-morphism over `𝒴`
that is an equivalence over `𝒴` makes `𝒳` a gerbe over `𝒴` in the sense of `IsGerbeOver`
exactly when its target is one. For `𝒴 = 𝒞`, `q = 𝟭 𝒞` this is, by `isGerbeOver_id_iff`, the
invariance of being fibred in groupoids, locally nonempty and locally connected; it is weaker than
Stacks 06P0, whose gerbes are stacks in groupoids. Stacks 06P0 itself is
`CategoryTheory.Functor.isGerbe_iff_of_isEquivalenceOver`. -/
theorem isGerbeOver_iff_of_isEquivalenceOver {J : GrothendieckTopology 𝒞} {q : 𝒴 ⥤ 𝒞}
    {F : 𝒳 ⥤ 𝒴} {F' : 𝒳' ⥤ 𝒴} {a : 𝒳 ⥤ 𝒳'} (ha : a ⋙ F' = F)
    (e : Functor.IsEquivalenceOver F F' a) :
    IsGerbeOver J q F ↔ IsGerbeOver J q F' :=
  ⟨IsGerbeOver.of_isEquivalenceOver ha e,
    IsGerbeOver.of_isEquivalenceOver e.inv_over (e.symm ha)⟩

end CategoryTheory
