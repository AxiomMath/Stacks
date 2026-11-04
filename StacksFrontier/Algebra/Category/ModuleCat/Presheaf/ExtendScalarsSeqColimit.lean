module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ExtendScalarsColimit

/-!
# A sequential cocone of objectwise base changes is colimiting

Let `A` be a presheaf of not necessarily commutative rings on a category `C`, let `M` be a
presheaf of `A`-modules, and let `k ↦ B_k` be a diagram of presheaves of rings indexed by `ℕ`
equipped with compatible morphisms `β_k : A ⟶ B_k`, with colimit `B` and `β∞ : A ⟶ B`. Reading
each objectwise extension of scalars `B_k ⊗_A M` back as a presheaf of `A`-modules — that is,
as `Stacks.NoncommChangeOfRings.Presheaf.restrictExtendObj (β_k) M` — a sequential diagram of
them whose transition morphisms are the base changes along the transitions of `k ↦ B_k`, and a
cocone on it with apex `B ⊗_A M` whose legs are the base changes along the coprojections, is a
**colimit** cocone. This is the last mathematical input of Stacks Tag 0EXB.

## The proof

Colimits of presheaves of modules are objectwise
(`PresheafOfModules.evaluationJointlyReflectsColimits`), and colimits of presheaves of rings
are too, so at each object `V` of `C` the statement becomes the statement of algebra proved in
`StacksFrontier.Algebra.Category.ModuleCat.NoncommExtendScalarsColimit`: extension of scalars
along `A(V) → B_k(V)` commutes with the colimit of the `B_k(V)`. The identification of the
evaluated transitions and legs with the algebraic ones is
`Stacks.NoncommChangeOfRings.Presheaf.baseChangeTo_app_eq_transition` and
`Stacks.NoncommChangeOfRings.Presheaf.baseChangeTo_app_eq_leg`.

## Main definitions

* `Stacks.NoncommChangeOfRings.Presheaf.natSeqDiagram`: the sequential diagram
  `k ↦ B_k ⊗_A M` of presheaves of `A`-modules cut out by a family of transition morphisms.
* `Stacks.NoncommChangeOfRings.Presheaf.natSeqEvalDesc`: the morphism out of the sections at
  `V` of `B ⊗_A M` descending a cocone on the evaluated diagram.

## Main results

* `Stacks.NoncommChangeOfRings.Presheaf.isColimitNatSeqCocone`: **the cocone is colimiting.**

## Implementation notes

The diagram is `CategoryTheory.Functor.ofSequence` of a *given* family of transition morphisms,
and the hypotheses `hφ` and `hι` say only that those transitions and the given legs are the
base change morphisms. Neither is an equality of functors: the transitions are compared one
successor at a time, which is all a consumer whose diagram is `Functor.ofSequence` can supply,
and `CategoryTheory.NatTrans.ofSequence` propagates the comparison to the general morphism of
`ℕ` — so the induction never enters the proof term. For the same reason the cocone is not built
here but taken as its family of legs: a consumer passes `t.ι` of the cocone it already has, and
the conclusion is about that cocone by eta for structures.

The sections at `V` of `restrictExtendObj γ M` and the carrier of the algebraic base change are
definitionally equal but spelled differently, and the kernel pays for that comparison at every
step. Each step is therefore its own declaration — the descent, the two identifications, the
compatibility and the two colimit laws — rather than a single term whose kernel check exceeds
the budget.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits PresheafOfModules

universe v₁ u₁ u

namespace Stacks.NoncommChangeOfRings.Presheaf

section NatSeq

variable {C : Type u₁} [Category.{v₁} C] {A : Cᵒᵖ ⥤ RingCat.{u}}
  {𝔅 : ℕ ⥤ (Cᵒᵖ ⥤ RingCat.{u})} {c : Cocone 𝔅}
  (β : ∀ k, A ⟶ 𝔅.obj k) (hβ : ∀ {k k' : ℕ} (f : k ⟶ k'), β k ≫ 𝔅.map f = β k')
  (γ : A ⟶ c.pt) (hγ : ∀ k, β k ≫ c.ι.app k = γ) (M : PresheafOfModules.{u} A)
  (φ : ∀ k : ℕ, restrictExtendObj (β k) M ⟶ restrictExtendObj (β (k + 1)) M)

/-- **The sequential diagram `k ↦ B_k ⊗_A M`** of presheaves of `A`-modules cut out by a family
of transition morphisms. -/
noncomputable def natSeqDiagram : ℕ ⥤ PresheafOfModules.{u} A :=
  Functor.ofSequence (X := fun k ↦ restrictExtendObj (β k) M) φ

/-- The morphism of `natSeqDiagram β M φ` from `k` to `k + 1` is the transition morphism `φ k`. -/
lemma natSeqDiagram_map_succ (k : ℕ) :
    (natSeqDiagram β M φ).map (homOfLE (k.le_add_right 1)) = φ k :=
  Functor.ofSequence_map_homOfLE_succ _ k

variable (ι : natSeqDiagram β M φ ⟶ (Functor.const ℕ).obj (restrictExtendObj γ M)) (V : Cᵒᵖ)

/-- The evaluation at `V` of the colimit cocone of presheaves of rings is a colimit cocone of
rings: colimits of presheaves are objectwise. -/
noncomputable def isColimitRingCoconeAt (hc : IsColimit c) :
    IsColimit (ringCoconeAt (𝔅 := 𝔅) (c := c) V) :=
  isColimitOfPreserves ((CategoryTheory.evaluation Cᵒᵖ RingCat.{u}).obj V) hc

/-- **The sections at `V` of a transition morphism of the sequential diagram are the transition
morphism of the algebraic diagram of base changes**, one successor at a time. -/
lemma natSeqDiagram_eval_map_succ
    (hφ : ∀ k : ℕ, φ k = baseChangeTo (β k) (𝔅.map (homOfLE (k.le_add_right 1))) M (β (k + 1))
      (hβ (homOfLE (k.le_add_right 1)))) (k : ℕ) :
    (natSeqDiagram β M φ ⋙ PresheafOfModules.evaluation A V).map
        (homOfLE (k.le_add_right 1)) =
      (Colimit.diagram (βAt β V) (hβAt β hβ V) (M.obj V)).map (homOfLE (k.le_add_right 1)) := by
  have key : Hom.app (baseChangeTo (β k) (𝔅.map (homOfLE (k.le_add_right 1))) M (β (k + 1))
        (hβ (homOfLE (k.le_add_right 1)))) V =
      (Colimit.transition (βAt β V) (hβAt β hβ V) (M.obj V) (homOfLE (k.le_add_right 1)) :
        (restrictExtendObj (β k) M).obj V ⟶ (restrictExtendObj (β (k + 1)) M).obj V) := by
    apply baseChangeTo_app_eq_transition
  exact (congrArg (fun q ↦ Hom.app q V)
    ((natSeqDiagram_map_succ β M φ k).trans (hφ k))).trans key

/-- The legs of a cocone on the evaluated sequential diagram are a compatible family over the
algebraic diagram of base changes. The comparison of the transitions is available only at a
successor, and `CategoryTheory.NatTrans.ofSequence` is what carries it to a general morphism
of `ℕ`. -/
lemma natSeqFamily_w
    (hφ : ∀ k : ℕ, φ k = baseChangeTo (β k) (𝔅.map (homOfLE (k.le_add_right 1))) M (β (k + 1))
      (hβ (homOfLE (k.le_add_right 1))))
    (s : Cocone (natSeqDiagram β M φ ⋙ PresheafOfModules.evaluation A V))
    {k k' : ℕ} (g : k ⟶ k') :
    (Colimit.diagram (βAt β V) (hβAt β hβ V) (M.obj V)).map g ≫ s.ι.app k' = s.ι.app k := by
  have hsucc : ∀ m : ℕ,
      (Colimit.diagram (βAt β V) (hβAt β hβ V) (M.obj V)).map
          (homOfLE (m.le_add_right 1)) ≫ s.ι.app (m + 1) =
        s.ι.app m ≫ ((Functor.const ℕ).obj s.pt).map (homOfLE (m.le_add_right 1)) := fun m ↦
    ((congrArg (fun q ↦ q ≫ s.ι.app (m + 1))
      (natSeqDiagram_eval_map_succ β hβ M φ V hφ m)).symm.trans
        (s.w (homOfLE (m.le_add_right 1)))).trans (Category.comp_id _).symm
  exact ((NatTrans.ofSequence (F := Colimit.diagram (βAt β V) (hβAt β hβ V) (M.obj V))
    (G := (Functor.const ℕ).obj s.pt) (fun m ↦ s.ι.app m) hsucc).naturality g).trans
    (Category.comp_id _)

/-- **The descent of a cocone on the evaluated sequential diagram**, out of the sections at `V`
of `B ⊗_A M`. -/
noncomputable def natSeqEvalDesc (hc : IsColimit c)
    (hφ : ∀ k : ℕ, φ k = baseChangeTo (β k) (𝔅.map (homOfLE (k.le_add_right 1))) M (β (k + 1))
      (hβ (homOfLE (k.le_add_right 1))))
    (s : Cocone (natSeqDiagram β M φ ⋙ PresheafOfModules.evaluation A V)) :
    (restrictExtendObj γ M).obj V ⟶ s.pt :=
  Colimit.descOfFamily (βAt β V) (hβAt β hβ V) (γAt γ V) (hγAt β γ hγ V) (M.obj V)
    (isColimitRingCoconeAt V hc) (fun k ↦ s.ι.app k) (natSeqFamily_w β hβ M φ V hφ s)

/-- **The sections at `V` of a leg of the cocone are the corresponding leg of the algebraic
cocone.** -/
lemma natSeqCocone_app_eval
    (hι : ∀ k : ℕ, ι.app k = baseChangeTo (β k) (c.ι.app k) M γ (hγ k)) (k : ℕ) :
    Hom.app (ι.app k) V =
      (Colimit.leg (βAt β V) (hβAt β hβ V) (γAt γ V) (hγAt β γ hγ V) (M.obj V) k :
        (restrictExtendObj (β k) M).obj V ⟶ (restrictExtendObj γ M).obj V) := by
  rw [hι k]
  exact baseChangeTo_app_eq_leg β hβ γ hγ M V k

/-- The descent of a cocone on the evaluated diagram absorbs every leg. -/
lemma natSeqEvalLeg_comp_desc (hc : IsColimit c)
    (hφ : ∀ k : ℕ, φ k = baseChangeTo (β k) (𝔅.map (homOfLE (k.le_add_right 1))) M (β (k + 1))
      (hβ (homOfLE (k.le_add_right 1))))
    (hι : ∀ k : ℕ, ι.app k = baseChangeTo (β k) (c.ι.app k) M γ (hγ k))
    (s : Cocone (natSeqDiagram β M φ ⋙ PresheafOfModules.evaluation A V)) (k : ℕ) :
    Hom.app (ι.app k) V ≫ natSeqEvalDesc β hβ γ hγ M φ V hc hφ s = s.ι.app k :=
  (congrArg (fun q ↦ q ≫ natSeqEvalDesc β hβ γ hγ M φ V hc hφ s)
      (natSeqCocone_app_eval β hβ γ hγ M φ ι V hι k)).trans
    (Colimit.leg_comp_descOfFamily (βAt β V) (hβAt β hβ V) (γAt γ V) (hγAt β γ hγ V) (M.obj V)
      (isColimitRingCoconeAt V hc) (fun k ↦ s.ι.app k) (natSeqFamily_w β hβ M φ V hφ s) k)

/-- The descent of a cocone on the evaluated diagram is the only morphism absorbing every
leg. -/
lemma natSeqEvalDesc_uniq (hc : IsColimit c)
    (hφ : ∀ k : ℕ, φ k = baseChangeTo (β k) (𝔅.map (homOfLE (k.le_add_right 1))) M (β (k + 1))
      (hβ (homOfLE (k.le_add_right 1))))
    (hι : ∀ k : ℕ, ι.app k = baseChangeTo (β k) (c.ι.app k) M γ (hγ k))
    (s : Cocone (natSeqDiagram β M φ ⋙ PresheafOfModules.evaluation A V))
    (t : (restrictExtendObj γ M).obj V ⟶ s.pt)
    (ht : ∀ k : ℕ, Hom.app (ι.app k) V ≫ t = s.ι.app k) :
    t = natSeqEvalDesc β hβ γ hγ M φ V hc hφ s :=
  Colimit.hom_ext_of_leg (βAt β V) (hβAt β hβ V) (γAt γ V) (hγAt β γ hγ V) (M.obj V)
    (isColimitRingCoconeAt V hc) fun k ↦ by
      rw [← natSeqCocone_app_eval β hβ γ hγ M φ ι V hι k]
      exact (ht k).trans (natSeqEvalLeg_comp_desc β hβ γ hγ M φ ι V hc hφ hι s k).symm

/-- The evaluation at `V` of the cocone is colimiting. -/
noncomputable def isColimitNatSeqCoconeAt (hc : IsColimit c)
    (hφ : ∀ k : ℕ, φ k = baseChangeTo (β k) (𝔅.map (homOfLE (k.le_add_right 1))) M (β (k + 1))
      (hβ (homOfLE (k.le_add_right 1))))
    (hι : ∀ k : ℕ, ι.app k = baseChangeTo (β k) (c.ι.app k) M γ (hγ k)) :
    IsColimit ((PresheafOfModules.evaluation A V).mapCocone
      (Cocone.mk (restrictExtendObj γ M) ι)) where
  desc s := natSeqEvalDesc β hβ γ hγ M φ V hc hφ s
  fac s k := natSeqEvalLeg_comp_desc β hβ γ hγ M φ ι V hc hφ hι s k
  uniq s t ht := natSeqEvalDesc_uniq β hβ γ hγ M φ ι V hc hφ hι s t ht

/-- **A sequential cocone of objectwise base changes is colimiting.** The transition morphisms
and the legs are only compared with the base change morphisms, the former one successor at a
time; the cocone itself is given by its family of legs, so that a consumer may pass the `ι` of
the cocone it already has. -/
noncomputable def isColimitNatSeqCocone (hc : IsColimit c)
    (hφ : ∀ k : ℕ, φ k = baseChangeTo (β k) (𝔅.map (homOfLE (k.le_add_right 1))) M (β (k + 1))
      (hβ (homOfLE (k.le_add_right 1))))
    (hι : ∀ k : ℕ, ι.app k = baseChangeTo (β k) (c.ι.app k) M γ (hγ k)) :
    IsColimit (Cocone.mk (restrictExtendObj γ M) ι) :=
  PresheafOfModules.evaluationJointlyReflectsColimits _ _ fun V ↦
    isColimitNatSeqCoconeAt β hβ γ hγ M φ ι V hc hφ hι

end NatSeq

end Stacks.NoncommChangeOfRings.Presheaf

end
