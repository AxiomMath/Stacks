module

public import Mathlib.CategoryTheory.Functor.Category
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacking two transported naturality squares, and cancelling one of them

A *transported naturality square* is an equation of the shape

  `u ≫ k = t ≫ a ≫ p`

in which `u` is the inverse image of a comparison isomorphism along the square's left edge, `k`
the square's canonical map, `t` a transport, `a` the image of the other side's canonical map, and
`p` the comparison isomorphism at the square's top row.  Two such squares stacked vertically have
their canonical maps, their transports and their other side's canonical maps each governed by a
composition law; this file turns those three laws into the statement for the outer rectangle, and
— what the reduction of a clause from a general case to a special one needs — back again, solving
for the *lower* square when the outer rectangle and the upper square are known.

Everything is at plain variables in one or two abstract categories, with every composition law
entering as a hypothesis.  That is the discipline the geometric instances require: there the
hypotheses are existing lemmas applied verbatim, nothing is restated, and the kernel never has to
expand a comparison isomorphism built by sheafification.

## Main results

* `Stacks.CategoryTheory.stack_lhs` and `Stacks.CategoryTheory.stack_rhs`: the two sides of the
  outer rectangle's equation, each rewritten through the stack into the image under `F` of a
  composite of the lower square's morphisms.  The two main results are the two ways of reading
  those.
* `Stacks.CategoryTheory.square_transport_comp`: **the outer rectangle's square, from the two
  squares it is stacked from.**
* `Stacks.CategoryTheory.square_transport_of_comp`: **the lower square, from the outer rectangle
  and the upper one.**  The cancellations are explicit one-sided inverses and an explicit
  faithfulness hypothesis, so that an instance supplies exactly the three facts it has and no
  instance search runs.

## Implementation notes

Only one functor appears, the inverse image along the stack's upper left edge: it is the one
whose image of the lower square's equation is taken.  Everything on the other side of the
transport — the image of a Zariski composition law, the transport's own naturality — enters as
plain morphisms of the ambient category together with equations, because at the instance those
are proved equations between morphisms and not images of a functor the kernel would have to
unfold.

Both sides of the outer rectangle's equation are factored through one shared pair of
intermediate statements, so that the forward direction and the cancellation are literally the
same computation read twice; the hypotheses are shared, in the same order, between every
declaration here, so that an instance which has built the arguments for one can pass the same
list to the others.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {C₂ : Type u₂} [Category.{v₂} C₂]

section Stack

variable (F : C₂ ⥤ C)
    {X₂ Y₂ Z₂ W₂ V₂ : C₂}
    {u₂ : X₂ ⟶ Y₂} {k₂ : Y₂ ⟶ Z₂} {t₂ : X₂ ⟶ W₂} {a₂ : W₂ ⟶ V₂} {p₂ : V₂ ⟶ Z₂}
    {Xc Yc Zc Pc Qc Rc Sc : C}
    {u : Xc ⟶ Yc} {k : Yc ⟶ Zc} {t : Xc ⟶ Pc} {a : Pc ⟶ Rc} {p₁ : Rc ⟶ Zc}
    {cinvX : Xc ⟶ F.obj X₂} {chomX : F.obj X₂ ⟶ Xc} {cinvY : Yc ⟶ F.obj Y₂}
    {k₁ : F.obj Z₂ ⟶ Zc} {t₁ : F.obj V₂ ⟶ Qc} {t₁' : F.obj W₂ ⟶ Sc}
    {a₁ : Qc ⟶ Rc} {gr₂ : Sc ⟶ Qc} {gpcHom : Sc ⟶ Pc} {gpcInv : Pc ⟶ Sc}

/-- **The left-hand side of the outer rectangle's equation, read through the stack.**  The
composition law `hk` for the canonical maps and the naturality `hnat` of the comparison of
inverse images put it into the image under `F` of the lower square's left-hand side. -/
theorem stack_lhs (hk : k = cinvY ≫ F.map k₂ ≫ k₁) (hnat : u ≫ cinvY = cinvX ≫ F.map u₂) :
    u ≫ k = cinvX ≫ F.map (u₂ ≫ k₂) ≫ k₁ := by
  rw [hk, reassoc_of% hnat, F.map_comp, Category.assoc]

/-- **The right-hand side of the outer rectangle's equation, read through the stack.**  The upper
square `h₁`, the naturality `hTnat` of the transport, its composition law `hTcomp` and the
composition law `ha` of the other side's canonical maps put it into the image under `F` of the
lower square's right-hand side. -/
theorem stack_rhs (hc : cinvX ≫ chomX = 𝟙 Xc) (hgpc : gpcHom ≫ gpcInv = 𝟙 Sc)
    (h₁ : F.map p₂ ≫ k₁ = t₁ ≫ a₁ ≫ p₁)
    (hTnat : F.map a₂ ≫ t₁ = t₁' ≫ gr₂)
    (hTcomp : F.map t₂ ≫ t₁' ≫ gpcHom = chomX ≫ t)
    (ha : a = gpcInv ≫ gr₂ ≫ a₁) :
    t ≫ a ≫ p₁ = cinvX ≫ F.map (t₂ ≫ a₂ ≫ p₂) ≫ k₁ := by
  have htail : cinvX ≫ F.map t₂ ≫ t₁' = t ≫ gpcInv := by
    rw [← Category.comp_id t₁', ← hgpc, reassoc_of% hTcomp, reassoc_of% hc]
  rw [ha, F.map_comp, F.map_comp]
  simp only [Category.assoc]
  rw [h₁, reassoc_of% hTnat, reassoc_of% htail]

/-- **The transported naturality square of an outer rectangle, from the two squares it is
stacked from.**

Read against the geometric instance: `F` is the inverse image along the upper left edge; `h₂` is
the lower square's statement and `h₁` the upper one's; `hk` is the composition law for the
canonical maps, `hnat` the naturality of the comparison of inverse images, `hTnat` the
naturality of the transport in the module, `hTcomp` the transport's composition law, and `ha` the
composition law of the other side's canonical maps with its leading comparison inverted.  `hc`
and `hgpc` are the two one-sided inverse identities those two comparisons satisfy. -/
theorem square_transport_comp (hc : cinvX ≫ chomX = 𝟙 Xc) (hgpc : gpcHom ≫ gpcInv = 𝟙 Sc)
    (hk : k = cinvY ≫ F.map k₂ ≫ k₁) (hnat : u ≫ cinvY = cinvX ≫ F.map u₂)
    (h₂ : u₂ ≫ k₂ = t₂ ≫ a₂ ≫ p₂)
    (h₁ : F.map p₂ ≫ k₁ = t₁ ≫ a₁ ≫ p₁)
    (hTnat : F.map a₂ ≫ t₁ = t₁' ≫ gr₂)
    (hTcomp : F.map t₂ ≫ t₁' ≫ gpcHom = chomX ≫ t)
    (ha : a = gpcInv ≫ gr₂ ≫ a₁) :
    u ≫ k = t ≫ a ≫ p₁ :=
  ((stack_lhs F hk hnat).trans
      (congrArg (fun m : X₂ ⟶ Z₂ => cinvX ≫ F.map m ≫ k₁) h₂)).trans
    (stack_rhs F hc hgpc h₁ hTnat hTcomp ha).symm

/-- **The lower square, from the outer rectangle and the upper square.**

This is the reduction step: `hD` is the outer rectangle's statement and `h₁` the upper square's,
and what comes out is the lower square's.  The three cancellations are supplied explicitly —
`hc2` inverts the leading comparison of inverse images, `hki` the upper square's canonical map,
and `hfaith` is the faithfulness of `F` at the one pair of morphisms it is used on.

That the upper square's canonical map is cancellable is not an extra geometric input: `h₁`
exhibits it, up to isomorphisms, as the image of the other side's canonical map, and at the
instance that map is an isomorphism. -/
theorem square_transport_of_comp (hc : cinvX ≫ chomX = 𝟙 Xc) (hgpc : gpcHom ≫ gpcInv = 𝟙 Sc)
    (hk : k = cinvY ≫ F.map k₂ ≫ k₁) (hnat : u ≫ cinvY = cinvX ≫ F.map u₂)
    (hD : u ≫ k = t ≫ a ≫ p₁)
    (h₁ : F.map p₂ ≫ k₁ = t₁ ≫ a₁ ≫ p₁)
    (hTnat : F.map a₂ ≫ t₁ = t₁' ≫ gr₂)
    (hTcomp : F.map t₂ ≫ t₁' ≫ gpcHom = chomX ≫ t)
    (ha : a = gpcInv ≫ gr₂ ≫ a₁)
    {k₁inv : Zc ⟶ F.obj Z₂} (hc2 : chomX ≫ cinvX = 𝟙 (F.obj X₂))
    (hki : k₁ ≫ k₁inv = 𝟙 (F.obj Z₂))
    (hfaith : ∀ x y : X₂ ⟶ Z₂, F.map x = F.map y → x = y) :
    u₂ ≫ k₂ = t₂ ≫ a₂ ≫ p₂ := by
  have hkey : cinvX ≫ F.map (u₂ ≫ k₂) ≫ k₁ = cinvX ≫ F.map (t₂ ≫ a₂ ≫ p₂) ≫ k₁ :=
    ((stack_lhs F hk hnat).symm.trans hD).trans (stack_rhs F hc hgpc h₁ hTnat hTcomp ha)
  refine hfaith _ _ ?_
  simpa only [Category.assoc, reassoc_of% hc2, hki, Category.comp_id] using
    (chomX ≫= hkey) =≫ k₁inv

end Stack

end Stacks.CategoryTheory

end
