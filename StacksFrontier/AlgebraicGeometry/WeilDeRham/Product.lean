module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupTrace
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DiagonalDualBasis
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.KunnethOfIsPullback
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.WeilCohomologyTheory

/-!
# Products of smooth projective schemes: the fibre-product property and the shuffle

The product `X × Y = X ×_k Y` of two smooth projective schemes over `k` is the base's
`Stacks.WeilCohomology.SmoothProjectiveScheme.prod`, with projections `fst`, `snd`, the diagonal
`diag`, `prodLift` and `prodMap`. This file adds the facts about them that the Weil-chapter
lemmas of this directory use and the base does not state (that `X × Y` with `fst`, `snd` is a
fibre product over `Spec(k)` is `Stacks.WeilDeRham.isPullback_fst_snd`):

* `Stacks.WeilDeRham.prodMap_id`, `Stacks.WeilDeRham.diag_prodMap`;
* `Stacks.WeilDeRham.isPullback_prodMap_fst_snd`: `(X × Y) × (X × Y) = (X × X) × (Y × Y)` along
  `p × p` and `q × q`, the identification used in Lemma 0FIL.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.WeilCohomology

universe u

namespace Stacks.WeilDeRham

open Stacks.WeilCohomology.SmoothProjectiveScheme

variable {k : Type u} [Field k]

section ProdMap

variable {X Y X' : (SmoothProjectiveScheme k).FullSubcategory}

/-- `𝟙 × 𝟙 = 𝟙`. -/
theorem prodMap_id : prodMap (𝟙 X) (𝟙 Y) = 𝟙 (prod X Y) :=
  prod_hom_ext (by simp) (by simp)

/-- `Δ_X ≫ (f × f) = f ≫ Δ_{X'}`. -/
@[reassoc (attr := simp)]
theorem diag_prodMap (f : X ⟶ X') : diag X ≫ prodMap f f = f ≫ diag X' :=
  prod_hom_ext (by simp) (by simp)

end ProdMap

/-! ### The self-product of a product -/

section Shuffle

variable (X Y : (SmoothProjectiveScheme k).FullSubcategory)

/-- **`(X × Y) × (X × Y) = (X × X) × (Y × Y)`**: for `P = X ×_k Y`, the self-product `P ×_k P`
with the maps `p × p : P × P ⟶ X × X` and `q × q : P × P ⟶ Y × Y` induced by the projections is a
fibre product of `X ×_k X` and `Y ×_k Y` over `Spec(k)`. -/
theorem isPullback_prodMap_fst_snd :
    IsPullback ((toScheme k).map (prodMap (fst X Y) (fst X Y)))
      ((toScheme k).map (prodMap (snd X Y) (snd X Y))) (prod X X).obj.hom
      (prod Y Y).obj.hom := by
  set P := prod X Y
  have hP := isPullback_fst_snd X Y
  have hPP := isPullback_fst_snd P P
  have hXX := isPullback_fst_snd X X
  have hYY := isPullback_fst_snd Y Y
  have r1 := congrArg (toScheme k).map (prodMap_fst (fst X Y) (fst X Y))
  have r2 := congrArg (toScheme k).map (prodMap_snd (fst X Y) (fst X Y))
  have s1 := congrArg (toScheme k).map (prodMap_fst (snd X Y) (snd X Y))
  have s2 := congrArg (toScheme k).map (prodMap_snd (snd X Y) (snd X Y))
  rw [Functor.map_comp, Functor.map_comp] at r1 r2 s1 s2
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    ((w (prodMap (fst X Y) (fst X Y))).trans (w (prodMap (snd X Y) (snd X Y))).symm)
    (fun c ↦ hPP.lift
      (hP.lift (c.fst ≫ (toScheme k).map (fst X X)) (c.snd ≫ (toScheme k).map (fst Y Y))
        (by rw [Category.assoc, Category.assoc, w, w, c.condition]))
      (hP.lift (c.fst ≫ (toScheme k).map (snd X X)) (c.snd ≫ (toScheme k).map (snd Y Y))
        (by rw [Category.assoc, Category.assoc, w, w, c.condition]))
      (by rw [← w (snd X Y), IsPullback.lift_snd_assoc, IsPullback.lift_snd_assoc,
        Category.assoc, Category.assoc, w, w]))
    (fun c ↦ ?_) (fun c ↦ ?_) (fun c m hm₁ hm₂ ↦ ?_))
  · refine hXX.hom_ext ?_ ?_
    · rw [Category.assoc, r1, ← Category.assoc, IsPullback.lift_fst, IsPullback.lift_fst]
    · rw [Category.assoc, r2, ← Category.assoc, IsPullback.lift_snd, IsPullback.lift_fst]
  · refine hYY.hom_ext ?_ ?_
    · rw [Category.assoc, s1, ← Category.assoc, IsPullback.lift_fst, IsPullback.lift_snd]
    · rw [Category.assoc, s2, ← Category.assoc, IsPullback.lift_snd, IsPullback.lift_snd]
  · refine hPP.hom_ext (hP.hom_ext ?_ ?_) (hP.hom_ext ?_ ?_)
    · rw [IsPullback.lift_fst, IsPullback.lift_fst, Category.assoc, ← r1, ← Category.assoc, hm₁]
    · rw [IsPullback.lift_fst, IsPullback.lift_snd, Category.assoc, ← s1, ← Category.assoc, hm₂]
    · rw [IsPullback.lift_snd, IsPullback.lift_fst, Category.assoc, ← r2, ← Category.assoc, hm₁]
    · rw [IsPullback.lift_snd, IsPullback.lift_snd, Category.assoc, ← s2, ← Category.assoc, hm₂]

end Shuffle

end Stacks.WeilDeRham

end
