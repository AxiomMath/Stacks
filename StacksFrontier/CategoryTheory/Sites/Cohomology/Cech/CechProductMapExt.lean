module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexMapOfARefinement

/-!
# Maps of iterated fibre products are checked factorwise

`Stacks.CechSite.eq_cechProductMap`: a map of iterated fibre products is `cechProductMap` as soon
as it has the right components, so identities between such maps are checked factorwise. (Ported
from the C1103b work, as an addition to `ComplexMapOfARefinement.lean`.)
-/

@[expose] public noncomputable section

universe w w' v v' u u'

namespace Stacks.CechSite

open CategoryTheory CategoryTheory.Limits Opposite

/-- Morphisms into the underlying object of a limit fan over a nonempty family in an
over-category are determined by their composites with the projections. -/
theorem _root_.CategoryTheory.Over.left_hom_ext_of_isLimit {C : Type u} [Category.{v} C] {U : C}
    {κ : Type*} [Nonempty κ] {Y : κ → Over U} {c : Fan Y} (hc : IsLimit c) {T : C}
    {h h' : T ⟶ c.pt.left} (H : ∀ a, h ≫ (c.proj a).left = h' ≫ (c.proj a).left) : h = h' := by
  obtain ⟨a₀⟩ := ‹Nonempty κ›
  have hb : h ≫ c.pt.hom = h' ≫ c.pt.hom := by
    rw [← Over.w (c.proj a₀), ← Category.assoc, H a₀, Category.assoc]
  exact congrArg CommaMorphism.left <|
    hc.hom_ext (f := (Over.homMk h : Over.mk (h ≫ c.pt.hom) ⟶ _)) (f' := Over.homMk h' hb.symm)
      fun ⟨a⟩ ↦ Over.OverMorphism.ext (H a)

/-- Morphisms into an iterated fibre product of a family are determined, on underlying objects,
by their composites with the projections. -/
theorem cechProduct_left_hom_ext
    {C : Type u} [Category.{v} C] {U : C} (E : PreZeroHypercover.{w} U) (n : ℕ)
    (i : Fin (n + 1) → E.I₀) [HasProduct (fun a ↦ Over.mk (E.f (i a)))] {T : C}
    {h h' : T ⟶ (∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left}
    (H : ∀ a, h ≫ (Pi.π (fun a ↦ Over.mk (E.f (i a))) a).left =
      h' ≫ (Pi.π (fun a ↦ Over.mk (E.f (i a))) a).left) : h = h' :=
  Over.left_hom_ext_of_isLimit (limit.isLimit _) H

/-- The map of iterated fibre products induced by a morphism of families lies over the map of
the targets. -/
@[reassoc]
theorem cechProductMap_comp_hom
    {C : Type u} [Category.{v} C] {U V : C}
    (E : PreZeroHypercover.{w} U) (G : PreZeroHypercover.{w'} V) {f : U ⟶ V}
    (φ : E.HomOver G f) (n : ℕ) (i : Fin (n + 1) → E.I₀)
    [∀ i : Fin (n + 1) → E.I₀, HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    [∀ i : Fin (n + 1) → G.I₀, HasProduct (fun a ↦ Over.mk (G.f (i a)))] :
    cechProductMap E G φ n i ≫ (∏ᶜ (fun a ↦ Over.mk (G.f (φ.s₀ (i a))))).hom =
      (∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).hom ≫ f :=
  Over.w _

/-- On underlying objects, the map of iterated fibre products induced by a morphism of
families is, on each factor, the projection followed by the component of the morphism, for families
indexed in any two universes (`Stacks.CechSite.cechProductMap_comp_π_left` is the case of one
universe). -/
@[reassoc]
theorem cechProductMap_comp_π_left_anyUniverses
    {C : Type u} [Category.{v} C] {U V : C}
    (E : PreZeroHypercover.{w} U) (G : PreZeroHypercover.{w'} V) {f : U ⟶ V}
    (φ : E.HomOver G f) (n : ℕ) (i : Fin (n + 1) → E.I₀)
    [∀ i : Fin (n + 1) → E.I₀, HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    [∀ i : Fin (n + 1) → G.I₀, HasProduct (fun a ↦ Over.mk (G.f (i a)))] (b : Fin (n + 1)) :
    cechProductMap E G φ n i ≫ (Pi.π (fun a ↦ Over.mk (G.f (φ.s₀ (i a)))) b).left =
      (Pi.π (fun a ↦ Over.mk (E.f (i a))) b).left ≫ φ.h₀ (i b) := by
  rw [cechProductMap, ← Over.comp_left, Pi.lift_comp_π]
  rfl

/-- A morphism between iterated fibre products which agrees with the components of a morphism
of families on every factor is the induced map `cechProductMap`. -/
theorem eq_cechProductMap
    {C : Type u} [Category.{v} C] {U V : C}
    (E : PreZeroHypercover.{w} U) (G : PreZeroHypercover.{w'} V) {f : U ⟶ V}
    (φ : E.HomOver G f) (n : ℕ) (i : Fin (n + 1) → E.I₀)
    [∀ i : Fin (n + 1) → E.I₀, HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    [∀ i : Fin (n + 1) → G.I₀, HasProduct (fun a ↦ Over.mk (G.f (i a)))]
    (h : (∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left ⟶
      (∏ᶜ (fun a ↦ Over.mk (G.f (φ.s₀ (i a))))).left)
    (H : ∀ b, h ≫ (Pi.π (fun a ↦ Over.mk (G.f (φ.s₀ (i a)))) b).left =
      (Pi.π (fun a ↦ Over.mk (E.f (i a))) b).left ≫ φ.h₀ (i b)) :
    h = cechProductMap E G φ n i :=
  cechProduct_left_hom_ext G n (φ.s₀ ∘ i) fun b ↦
    (H b).trans (cechProductMap_comp_π_left_anyUniverses E G φ n i b).symm

end Stacks.CechSite

end
