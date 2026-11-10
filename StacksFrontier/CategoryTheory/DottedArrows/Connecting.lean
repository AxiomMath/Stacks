module

public import StacksFrontier.CategoryTheory.DottedArrows.Isomorphism

/-!
# Connecting morphisms between two dotted arrows

Fix a 2-commutative square in the 2-category of categories fibred in groupoids over a base
category `C`, filled by `γ`, and two dotted arrows `a` and `b` for it (Stacks 0H18). A
*connecting morphism over an object `z` of the base of the square* is a morphism
`θ : a.a z ⟶ b.a z` with `b.β z = a.β z ≫ f (θ)`; that is exactly the datum
`CategoryTheory.DottedArrow.nonempty_iso_of_forall_hom` asks for at `z`.

This file produces connecting morphisms where they exist for free. Over an object in the image
of the left edge `j` one is built from the two `α`s, which are invertible; and a connecting
morphism transports along any isomorphism of the base, by the naturality of the two `β`s.
Together: there is a connecting morphism over every object isomorphic to one in the image of
`j`.

## Main results

* `CategoryTheory.DottedArrow.exists_hom_beta_app_image`: a connecting morphism over an object
  in the image of `j`.
* `CategoryTheory.DottedArrow.exists_hom_beta_app_of_iso`: a connecting morphism transports along
  an isomorphism of the base.
* `CategoryTheory.DottedArrow.exists_hom_beta_app_of_iso_image`: a connecting morphism over an
  object isomorphic to one in the image of `j`.
* `CategoryTheory.DottedArrow.isHomLift_of_beta_app_eq`: a connecting morphism lies over an
  identity.

## Implementation notes

The connecting morphism over `j z` is `a.α z ≫ (b.α z)⁻¹`, but the statements below are
existential and mention no inverse. That is deliberate: `CategoryTheory.inv` in a *statement*
needs its `IsIso` instance at statement-elaboration time, and the invertibility here comes from
`CategoryTheory.CatFiberedInGroupoids.isIso_toNatTrans`, which is a theorem rather than an
instance. Keeping the inverse inside the proof also matches how the result is consumed: a
connecting morphism is passed on, never inspected.

`CategoryTheory.DottedArrow.exists_hom_beta_app_image` is the solved form of
`CategoryTheory.DottedArrow.pasting_app_eq`, obtained from it by cancelling `f (b.α z)` against
the inverse of that isomorphism; `CategoryTheory.DottedArrow.pasting_eq` is deliberately *not*
stated in solved form, for the reason just given.

A connecting morphism is automatically vertical, because after `f` it becomes the composite of
the inverse of a component of `a.β` with a component of `b.β`, both of which lie over identities,
and a 1-morphism over `C` reflects `CategoryTheory.Functor.IsHomLift`. That is also the first step
inside `CategoryTheory.DottedArrow.nonempty_iso_of_forall_hom`; it is stated separately here
because a consumer building a morphism of a 2-fibre product out of a connecting morphism needs
the verticality on its own.

The transport along an isomorphism is a chain of `Eq.trans`/`congrArg` steps with no written
intermediate term. A `calc` block does not elaborate here: writing out an intermediate composite
re-elaborates it and the ambient slice unification is retried, which fails to synthesize the
`Trans` instance. `CategoryTheory.DottedArrow.beta_naturality` is used rather than the raw
naturality of `β`, so that each step is an ordinary rewrite.

## References

* [Stacks Project, Tag 0H18](https://stacks.math.columbia.edu/tag/0H18)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
  {S T X Y : CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} C}
  {x : S ⟶ X} {j : S ⟶ T} {f : X ⟶ Y} {y : T ⟶ Y} {γ : (j ≫ y) ⟶ (x ≫ f)}

namespace DottedArrow

/-- **Two dotted arrows are connected over every object in the image of the left edge.** The
connecting morphism is `a.α z` followed by the inverse of `b.α z`; both `α`s are invertible
because every 2-morphism of categories fibred in groupoids is, and the required identity is
`CategoryTheory.DottedArrow.pasting_app_eq` after cancelling `f (b.α z)`. -/
theorem exists_hom_beta_app_image (a b : DottedArrow x j f y γ) (z : S.val.obj) :
    ∃ θ : a.a.hom.toFunctor.obj (j.hom.toFunctor.obj z) ⟶
        b.a.hom.toFunctor.obj (j.hom.toFunctor.obj z),
      b.β.hom.toNatTrans.app (j.hom.toFunctor.obj z) =
        a.β.hom.toNatTrans.app (j.hom.toFunctor.obj z) ≫ f.hom.toFunctor.map θ := by
  have hα : IsIso (X := (j ≫ b.a).hom.toFunctor) b.α.hom.toNatTrans :=
    CatFiberedInGroupoids.isIso_toNatTrans b.α
  let eα := (asIso b.α.hom.toNatTrans).app z
  refine ⟨a.α.hom.toNatTrans.app z ≫ eα.inv, Eq.symm ?_⟩
  -- expand, substitute the pasting identity, and cancel `b.α z` against its inverse
  refine Eq.trans (congrArg (fun t => a.β.hom.toNatTrans.app (j.hom.toFunctor.obj z) ≫ t)
    (f.hom.toFunctor.map_comp (a.α.hom.toNatTrans.app z) eα.inv)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun t => t ≫ f.hom.toFunctor.map eα.inv)
    (pasting_app_eq a b z)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun t => b.β.hom.toNatTrans.app (j.hom.toFunctor.obj z) ≫ t)
    (Iso.hom_inv_id_map eα f.hom.toFunctor)) ?_
  exact Category.comp_id _

/-- **A connecting morphism transports along an isomorphism of the base.** Conjugating by the
isomorphism moves a connecting morphism over `z` to one over `w`; the naturality of the two `β`s
turns the required identity into the statement that the isomorphism composed with its inverse is
an identity. -/
theorem exists_hom_beta_app_of_iso (a b : DottedArrow x j f y γ) {w z : T.val.obj} (e : w ≅ z)
    (h : ∃ θ : a.a.hom.toFunctor.obj z ⟶ b.a.hom.toFunctor.obj z,
      b.β.hom.toNatTrans.app z = a.β.hom.toNatTrans.app z ≫ f.hom.toFunctor.map θ) :
    ∃ θ : a.a.hom.toFunctor.obj w ⟶ b.a.hom.toFunctor.obj w,
      b.β.hom.toNatTrans.app w = a.β.hom.toNatTrans.app w ≫ f.hom.toFunctor.map θ := by
  obtain ⟨θ, hθ⟩ := h
  refine ⟨a.a.hom.toFunctor.map e.hom ≫ θ ≫ b.a.hom.toFunctor.map e.inv, ?_⟩
  refine Eq.symm ?_
  rw [Functor.map_comp, Functor.map_comp]
  -- push `a.β` across `e.hom`, substitute `hθ`, pull `b.β` back across `e.inv`, cancel
  refine Eq.trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ (f.hom.toFunctor.map θ ≫
        f.hom.toFunctor.map (b.a.hom.toFunctor.map e.inv)))
      (beta_naturality a e.hom).symm).trans (Category.assoc _ _ _))) ?_
  refine Eq.trans (congrArg (fun t => y.hom.toFunctor.map e.hom ≫ t)
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun t => t ≫ f.hom.toFunctor.map (b.a.hom.toFunctor.map e.inv))
        hθ.symm))) ?_
  refine Eq.trans (congrArg (fun t => y.hom.toFunctor.map e.hom ≫ t)
    (beta_naturality b e.inv).symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun t => t ≫ b.β.hom.toNatTrans.app w)
    (Iso.hom_inv_id_map e y.hom.toFunctor)) ?_
  exact Category.id_comp _

/-- **A connecting morphism between two dotted arrows lies over an identity.** Its image under
`f` is the inverse of a component of `a.β` followed by a component of `b.β`, both vertical; and
`f` is a 1-morphism over `C`, so it reflects verticality. -/
theorem isHomLift_of_beta_app_eq (a b : DottedArrow x j f y γ) (z : T.val.obj)
    {θ : a.a.hom.toFunctor.obj z ⟶ b.a.hom.toFunctor.obj z}
    (hθ : b.β.hom.toNatTrans.app z = a.β.hom.toNatTrans.app z ≫ f.hom.toFunctor.map θ) :
    X.val.p.IsHomLift (𝟙 (T.val.p.obj z)) θ := by
  have hisoz : IsIso (a.β.hom.toNatTrans.app z) := isIso_beta_app a z
  have hliftA : Y.val.p.IsHomLift (𝟙 (T.val.p.obj z)) (a.β.hom.toNatTrans.app z) :=
    a.β.hom.isHomLift' z
  have hliftB : Y.val.p.IsHomLift (𝟙 (T.val.p.obj z)) (b.β.hom.toNatTrans.app z) :=
    b.β.hom.isHomLift' z
  have hmap : f.hom.toFunctor.map θ =
      inv (a.β.hom.toNatTrans.app z) ≫ b.β.hom.toNatTrans.app z :=
    ((IsIso.inv_comp_eq (a.β.hom.toNatTrans.app z)).mpr hθ).symm
  have hinv : Y.val.p.IsHomLift (𝟙 (T.val.p.obj z)) (inv (a.β.hom.toNatTrans.app z)) :=
    IsHomLift.lift_id_inv_isIso Y.val.p (T.val.p.obj z) (a.β.hom.toNatTrans.app z)
  have hlift : Y.val.p.IsHomLift (𝟙 (T.val.p.obj z)) (f.hom.toFunctor.map θ) := by
    rw [hmap]
    exact IsHomLift.comp_of_lift_id Y.val.p (T.val.p.obj z)
      (inv (a.β.hom.toNatTrans.app z)) (b.β.hom.toNatTrans.app z)
  exact Functor.isHomLift_of_isHomLift_map f.hom.w _ _

/-- **Two dotted arrows are connected over every object isomorphic to one in the image of the
left edge.** -/
theorem exists_hom_beta_app_of_iso_image (a b : DottedArrow x j f y γ) {w : T.val.obj}
    (z : S.val.obj) (e : w ≅ j.hom.toFunctor.obj z) :
    ∃ θ : a.a.hom.toFunctor.obj w ⟶ b.a.hom.toFunctor.obj w,
      b.β.hom.toNatTrans.app w = a.β.hom.toNatTrans.app w ≫ f.hom.toFunctor.map θ :=
  exists_hom_beta_app_of_iso a b e (exists_hom_beta_app_image a b z)

end DottedArrow

end CategoryTheory

end
