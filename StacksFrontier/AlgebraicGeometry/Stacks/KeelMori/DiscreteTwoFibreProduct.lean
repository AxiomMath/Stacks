module

public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategory
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Defs

/-!
# 2-fibre products over the category attached to a presheaf of sets

Let `F` be a presheaf of sets on the big fppf site of `S` and let `a : 𝒴 ⟶ F`, `f : 𝒳 ⟶ F` be
1-morphisms of categories fibred in groupoids into the category attached to `F`. Since 2-morphisms
into that category are unique (`AlgebraicGeometry.Stack.subsingleton_hom₂`), the fillers of
2-commutative squares over `(a, f)`, and the compatibility squares of their pre-morphisms, carry no
information. This file records the consequence used in the proof of the Keel–Mori theorem: a
2-fibre product over `(a, f)` stays one over `(a ≫ e, f ≫ e)` for any 1-morphism `e` into the
category attached to another presheaf which can be cancelled on the right, for instance the
1-morphism attached to an isomorphism of presheaves.

## Main results

* `AlgebraicGeometry.Stack.isTwoFibreProduct_postcompose_of_cancel`
* `AlgebraicGeometry.Stack.isTwoFibreProduct_of_eq_of_discrete`: the filler of a 2-fibre product
  over the category attached to a presheaf can be replaced by any other.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {F F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **A 2-fibre product over the category attached to a presheaf stays one after composing the
cospan with a right-cancellable 1-morphism into the category attached to another presheaf.** The
apex and projections are unchanged and the filler is arbitrary. -/
noncomputable def isTwoFibreProduct_postcompose_of_cancel
    {a : 𝒴 ⟶ fibredCategory B S hS F} {f : 𝒳 ⟶ fibredCategory B S hS F}
    (e : fibredCategory B S hS F ⟶ fibredCategory B S hS F')
    (he : ∀ {W : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
      (x y : W ⟶ fibredCategory B S hS F), x ≫ e = y ≫ e → x = y)
    (P : Bicategory.TwoCommSq a f) (hP : Bicategory.IsTwoFibreProduct P)
    (φ : P.fst ≫ (a ≫ e) ≅ P.snd ≫ (f ≫ e)) :
    Bicategory.IsTwoFibreProduct
      (⟨P.pt, P.fst, P.snd, φ⟩ : Bicategory.TwoCommSq (a ≫ e) (f ≫ e)) := by
  classical
  let P' : Bicategory.TwoCommSq (a ≫ e) (f ≫ e) := ⟨P.pt, P.fst, P.snd, φ⟩
  -- a square over `(a ≫ e, f ≫ e)` read over `(a, f)`
  have hdesc : ∀ Q : Bicategory.TwoCommSq (a ≫ e) (f ≫ e), Q.fst ≫ a = Q.snd ≫ f := fun Q =>
    he _ _ ((hom_eq_of_hom₂ B S hS (Bicategory.associator Q.fst a e).hom).trans
      ((hom_eq_of_hom₂ B S hS Q.iso.hom).trans
        (hom_eq_of_hom₂ B S hS (Bicategory.associator Q.snd f e).inv)))
  let low : Bicategory.TwoCommSq (a ≫ e) (f ≫ e) → Bicategory.TwoCommSq a f := fun Q =>
    ⟨Q.pt, Q.fst, Q.snd, eqToIso (hdesc Q)⟩
  -- pre-morphisms into `P` over `(a, f)` and into `P'` over `(a ≫ e, f ≫ e)` carry the same data
  let up : ∀ Q, Bicategory.TwoCommSq.PreHom (low Q) P → Bicategory.TwoCommSq.PreHom Q P' :=
    fun Q p =>
      { hom := p.hom
        isoFst := p.isoFst
        isoSnd := p.isoSnd
        compat := (subsingleton_hom₂ B S hS _ _).elim _ _ }
  let down : ∀ Q, Bicategory.TwoCommSq.PreHom Q P' → Bicategory.TwoCommSq.PreHom (low Q) P :=
    fun Q p =>
      { hom := p.hom
        isoFst := p.isoFst
        isoSnd := p.isoSnd
        compat := (subsingleton_hom₂ B S hS _ _).elim _ _ }
  refine IsTerminal.ofUniqueHom
    (fun Q => _root_.Quotient.mk _ (up Q (Bicategory.twoFibreProductPreHom hP (low Q)))) ?_
  intro Q m
  induction m using _root_.Quotient.inductionOn with
  | h q =>
    apply _root_.Quotient.sound
    obtain ⟨θ, h₁, h₂⟩ := Bicategory.twoFibreProductPreHom_rel hP (down Q q)
      (Bicategory.twoFibreProductPreHom hP (low Q))
    exact ⟨θ, h₁, h₂⟩

/-- **The filler of a 2-fibre product over the category attached to a presheaf can be replaced
by any other**, the apex and the projections being kept. -/
noncomputable def isTwoFibreProduct_of_eq_of_discrete
    {a : 𝒴 ⟶ fibredCategory B S hS F} {f : 𝒳 ⟶ fibredCategory B S hS F}
    (P : Bicategory.TwoCommSq a f) (hP : Bicategory.IsTwoFibreProduct P)
    (φ : P.fst ≫ a ≅ P.snd ≫ f) :
    Bicategory.IsTwoFibreProduct (⟨P.pt, P.fst, P.snd, φ⟩ : Bicategory.TwoCommSq a f) := by
  have : P = ⟨P.pt, P.fst, P.snd, φ⟩ := by
    obtain ⟨pt, fst, snd, iso⟩ := P
    congr 1
    exact Iso.ext ((subsingleton_hom₂ B S hS _ _).elim _ _)
  exact this ▸ hP

end AlgebraicGeometry.Stack

end
