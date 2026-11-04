module

public import StacksFrontier.AlgebraicGeometry.TensorPowerAssoc.IntegerAssoc
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The two inverse laws of an integer tensor power are snake-compatible

Let `L` be an object of a monoidal category with a two-sided tensor inverse, and let `p + q = 0`.
Then `L ^⊗ q` is a tensor inverse of `L ^⊗ p` on both sides, the two inverse laws being
`Stacks.TensorPowers.TensorInverse.addIso` at the bidegrees `(p, q)` and `(q, p)` read into the
degree `0`, where the power is the unit object.  This file proves that those two laws are
*snake-compatible*: cancelling the first two factors of `L ^⊗ p ⊗ L ^⊗ q ⊗ L ^⊗ p` against the
first agrees with cancelling the last two against the second.

For the base object `L` that compatibility is a hypothesis and cannot be anything else — rescaling
one of its two inverse laws by an automorphism of the unit object breaks the equation and leaves
everything else intact, which is why
`StacksFrontier/AlgebraicGeometry/TensorPowerAssoc/IntegerSucc.lean` carries it as a hypothesis and
`AlgebraicGeometry.SheafOfModules.tensorInverse_snake` discharges it for a sheaf of modules.  For
the *powers* it is a consequence: the associativity constraint in the tridegree `(p, q, p)` has
`L ^⊗ (p + q) ⊗ L ^⊗ p` on one side and `L ^⊗ p ⊗ L ^⊗ (q + p)` on the other, and in the degree
`0` the two multiplications are the left and the right unitor.  So all that is needed beyond
`Stacks.TensorPowers.TensorInverse.addIso_assoc` is the two unit laws, and the left one in a
negative degree is proved here.

## Main results

* `Stacks.TensorPowers.TensorInverse.addIso_snake`: **the two inverse laws of `L ^⊗ p` are
  snake-compatible**, for every pair of integers with `p + q = 0`.  This is the hypothesis that
  `Stacks.Monoidal.isoOfTensorInverse_tensorHom_comp` consumes at a tensor power, and the one
  thing a multiplicativity statement crossing the degree zero is not formal without.
* `Stacks.TensorPowers.TensorInverse.addIso_zero_left`: **the left unit law of the addition law,
  in every integer degree.**  The recursion runs on the second exponent and starts from the right
  unitor, so in a negative degree the left unit law is not a statement about the natural-number
  recursion at all.
* `Stacks.TensorPowers.TensorInverse.addIso_zero_left_succ_iff`: its inductive step, again as an
  equivalence, so that the induction over `ℤ` runs in both directions.

## Implementation notes

**Where the spellings are crossed.**  `intTensorPow L h.inv 0` and `𝟙_ C` are the same object and
not the same term, and neither `rw` nor `simp` will cross between them: the proof of the base case
of the left unit law and the statement of its inductive step are therefore written in the `𝟙_ C`
spelling and attached to the goal by `exact` and by `cancel_epi`, both of which work up to
definitional equality.  The degree-zero base case is where
`CategoryTheory.MonoidalCategory.unitors_equal` enters — at the second exponent `0` the recursion
gives the right unitor of the unit object and the left unit law asks for the left one.

**The transports are merged at explicit degrees.**  Both sides of the associativity constraint
end in a chain of transports along equalities of integers, and the chains on the two sides have
the same endpoints; an unguided `simp` collapses the wrong pair, so every merge names its two
equalities.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Stacks.TensorPowers

namespace Stacks.TensorPowers.TensorInverse

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow
  Stacks.TensorPowers.intTensorPow

/-- The left unit law of the addition law in the degree `(0, c)` is equivalent to the one in the
degree `(0, c + 1)`: by the successor equation the second is the first whiskered by `L` and
conjugated by isomorphisms. -/
theorem addIso_zero_left_succ_iff {L : C} (h : TensorInverse L)
    (hs : (α_ L h.inv L).hom ≫ L ◁ h.mulIso'.hom ≫ (ρ_ L).hom =
      h.mulIso.hom ▷ L ≫ (λ_ L).hom) (c c' : ℤ) (hc : c + 1 = c') :
    ((h.addIso 0 c).hom =
        (λ_ (intTensorPow L h.inv c)).hom ≫
          (reindex L h.inv (show c = 0 + c from by omega)).hom) ↔
      ((h.addIso 0 c').hom =
        (λ_ (intTensorPow L h.inv c')).hom ≫
          (reindex L h.inv (show c' = 0 + c' from by omega)).hom) := by
  have hpre : IsIso (𝟙_ C ◁ ((reindex L h.inv hc.symm).hom ≫ (h.succIso c).hom)) :=
    inferInstanceAs (IsIso (MonoidalCategory.whiskerLeftIso (𝟙_ C)
      (asIso ((reindex L h.inv hc.symm).hom ≫ (h.succIso c).hom))).hom)
  have hpost : IsIso ((h.succIso (0 + c)).inv ≫
      (reindex L h.inv (show 0 + c + 1 = 0 + c' from by omega)).hom) := inferInstance
  have hY : (𝟙_ C ◁ ((reindex L h.inv hc.symm).hom ≫ (h.succIso c).hom)) ≫
        (α_ (𝟙_ C) (intTensorPow L h.inv c) L).inv ≫
          (((λ_ (intTensorPow L h.inv c)).hom ≫
            (reindex L h.inv (show c = 0 + c from by omega)).hom) ▷ L) ≫
            (h.succIso (0 + c)).inv ≫
              (reindex L h.inv (show 0 + c + 1 = 0 + c' from by omega)).hom =
      (λ_ (intTensorPow L h.inv c')).hom ≫
        (reindex L h.inv (show c' = 0 + c' from by omega)).hom := by
    rw [MonoidalCategory.comp_whiskerRight]
    simp only [Category.assoc]
    rw [reindex_whiskerRight_succIso h (show c = 0 + c from by omega)
          (show 0 + c + 1 = 0 + c' from by omega) hc
          (show c' = 0 + c' from by omega),
      ← Category.assoc (α_ (𝟙_ C) (intTensorPow L h.inv c) L).inv
        ((λ_ (intTensorPow L h.inv c)).hom ▷ L),
      ← MonoidalCategory.leftUnitor_tensor_hom,
      ← Category.assoc (𝟙_ C ◁ ((reindex L h.inv hc.symm).hom ≫ (h.succIso c).hom))
        (λ_ (intTensorPow L h.inv c ⊗ L)).hom,
      MonoidalCategory.leftUnitor_naturality]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [reindex_comp_reindex_assoc h hc.symm hc,
      reindex_self h (show c' = c' from rfl), Category.id_comp]
  rw [addIso_succ h hs 0 c c' hc]
  refine ⟨fun hX ↦ by rw [hX]; exact hY, fun hbig ↦ ?_⟩
  refine whiskerRight_injective_of_mulIso h.mulIso ?_
  refine (cancel_mono ((h.succIso (0 + c)).inv ≫
    (reindex L h.inv (show 0 + c + 1 = 0 + c' from by omega)).hom)).mp ?_
  refine (cancel_epi (α_ (𝟙_ C) (intTensorPow L h.inv c) L).inv).mp ?_
  refine (cancel_epi (𝟙_ C ◁ ((reindex L h.inv hc.symm).hom ≫ (h.succIso c).hom))).mp ?_
  exact hbig.trans hY.symm

/-- **The left unit law of the addition law, in every integer degree**: multiplication by the
zeroth power on the left is the left unitor, followed by the transport between the two spellings
`c` and `0 + c` of the degree.  The recursion on the second exponent starts from the *right*
unitor, so in a nonnegative degree this is a statement about the natural-number recursion and in a
negative degree it is not; the induction is over `ℤ`. -/
theorem addIso_zero_left {L : C} (h : TensorInverse L)
    (hs : (α_ L h.inv L).hom ≫ L ◁ h.mulIso'.hom ≫ (ρ_ L).hom =
      h.mulIso.hom ▷ L ≫ (λ_ L).hom) (c : ℤ) :
    (h.addIso 0 c).hom =
      (λ_ (intTensorPow L h.inv c)).hom ≫
        (reindex L h.inv (show c = 0 + c from by omega)).hom := by
  induction c using Int.induction_on with
  | zero =>
      refine Eq.trans
        (show (h.addIso 0 (0 : ℤ)).hom =
          (ρ_ (intTensorPow L h.inv 0)).hom ≫
            (reindex L h.inv (show (0 : ℤ) = 0 + 0 from by omega)).hom from rfl) ?_
      exact congrArg
        (fun z ↦ z ≫ (reindex L h.inv (show (0 : ℤ) = 0 + 0 from by omega)).hom)
        MonoidalCategory.unitors_equal.symm
  | succ i ih => exact (addIso_zero_left_succ_iff h hs (i : ℤ) ((i : ℤ) + 1) rfl).mp ih
  | pred i ih =>
      exact (addIso_zero_left_succ_iff h hs (-(i : ℤ) - 1) (-(i : ℤ))
        (show -(i : ℤ) - 1 + 1 = -(i : ℤ) from by omega)).mpr ih

/-- **The two inverse laws of an integer tensor power are snake-compatible.**  Let `p + q = 0`, so
that `L ^⊗ q` is a tensor inverse of `L ^⊗ p` on both sides, the two inverse laws being the
addition law at the bidegrees `(p, q)` and `(q, p)` read into the degree `0`, where the power is
the unit object.  Then cancelling the first two factors of `L ^⊗ p ⊗ L ^⊗ q ⊗ L ^⊗ p` against the
first law agrees with cancelling the last two against the second.

For the base object this is the hypothesis `hs`, and it is not a formal consequence of anything —
rescaling one law by an automorphism of the unit object breaks it.  For the powers it *is* a
consequence, of the associativity constraint in the tridegree `(p, q, p)` together with the two
unit laws, and that is this proof: the associativity constraint has `L ^⊗ (p + q) ⊗ L ^⊗ p` on one
side and `L ^⊗ p ⊗ L ^⊗ (q + p)` on the other, and in the degree `0` the two multiplications are
the left and the right unitor. -/
@[sga "5 VI 1.3.4" "special case"]
theorem addIso_snake {L : C} (h : TensorInverse L)
    (hs : (α_ L h.inv L).hom ≫ L ◁ h.mulIso'.hom ≫ (ρ_ L).hom =
      h.mulIso.hom ▷ L ≫ (λ_ L).hom) (p q : ℤ) (hpq : p + q = 0) :
    (α_ (intTensorPow L h.inv p) (intTensorPow L h.inv q)
          (intTensorPow L h.inv p)).hom ≫
        (intTensorPow L h.inv p ◁
          ((h.addIso q p).hom ≫
            (reindex L h.inv (show q + p = 0 from by omega)).hom)) ≫
          (ρ_ (intTensorPow L h.inv p)).hom =
      (((h.addIso p q).hom ≫
            (reindex L h.inv (show p + q = 0 from by omega)).hom) ▷
          intTensorPow L h.inv p) ≫
        (λ_ (intTensorPow L h.inv p)).hom := by
  have hassoc := addIso_assoc h hs p q p
  rw [addIso_congr_left h (show (0 : ℤ) = p + q from by omega) p, addIso_zero_left h hs p,
    addIso_congr_right h p (show (0 : ℤ) = q + p from by omega), addIso_zero_right h p] at hassoc
  simp only [Category.assoc] at hassoc
  rw [← Category.assoc ((h.addIso p q).hom ▷ intTensorPow L h.inv p)
        ((reindex L h.inv (show p + q = 0 from by omega)).hom ▷ intTensorPow L h.inv p),
    ← MonoidalCategory.comp_whiskerRight,
    ← Category.assoc (intTensorPow L h.inv p ◁ (h.addIso q p).hom)
        (intTensorPow L h.inv p ◁ (reindex L h.inv (show q + p = 0 from by omega)).hom),
    ← MonoidalCategory.whiskerLeft_comp,
    reindex_comp_reindex h (show p = 0 + p from by omega)
      (show (0 : ℤ) + p = p + q + p from by omega),
    reindex_comp_reindex_assoc h (show p = p + 0 from by omega)
      (show p + 0 = p + (q + p) from by omega),
    reindex_comp_reindex h (show p = p + (q + p) from by omega)
      (show p + (q + p) = p + q + p from by omega)] at hassoc
  refine (cancel_mono (reindex L h.inv (show p = p + q + p from by omega)).hom).mp ?_
  simp only [Category.assoc]
  exact hassoc.symm

end Stacks.TensorPowers.TensorInverse

end
