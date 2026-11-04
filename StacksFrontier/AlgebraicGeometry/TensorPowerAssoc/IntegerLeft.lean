module

public import StacksFrontier.AlgebraicGeometry.TensorPowerAssoc.Integer
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The associativity of the integer addition law in a negative first degree

`Stacks.TensorPowers.TensorInverse.addIso` is the addition law
`L ^⊗ n ⊗ L ^⊗ m ≅ L ^⊗ (n + m)` of the integer tensor powers of an object with a two-sided
tensor inverse, and `Stacks.TensorPowers.TensorInverse.addIso_assoc_natCast` is its associativity
constraint with **all three** exponents natural numbers.  That file records negative degrees as
not done, and the consumers of the law have read the restriction as a restriction on the first
exponent too.

It is not one.  The addition law recurses on its **second** exponent only — `addNatIso` climbs
from the right unitor by one factor of `L` at a time, and the first exponent is a passenger that
the recursion never inspects — so the associativity constraint holds for an **arbitrary integer**
first exponent as soon as the second and third are natural numbers, by the same induction on the
third exponent that proves the natural-number case, with the successor comparisons
`Stacks.TensorPowers.TensorInverse.succIso` of the integer powers carried along.  Nothing about
the tensor inverse is used and no sign condition appears.

This matters because the exponent that crosses zero in a graded multiplicativity statement is the
first one: the summands of a Laurent-graded module are indexed by all of `ℤ` while the degrees of
the algebra acting on them are natural numbers, so what such a statement needs of the addition law
is exactly the range proved here.

## Main results

* `Stacks.TensorPowers.TensorInverse.addNatIso_assoc`: **the associativity constraint of the
  integer addition law for an arbitrary integer first exponent** and natural-number second and
  third exponents.
* `Stacks.TensorPowers.TensorInverse.addNatIso_zero` and
  `Stacks.TensorPowers.TensorInverse.addNatIso_succ`: the two clauses of the recursion, restated
  as equations.  `addNatIso` is defined by pattern matching, so its defining clauses are not
  available as rewrite rules until they are restated; each holds by `rfl`.
* `Stacks.TensorPowers.TensorInverse.reindex_whiskerRight_succIso`: the successor comparison
  commutes with the transport along an equality of degrees.  This is the only step of the
  induction that the natural-number proof does not have, and it is needed because `n + ↑b + ↑c`
  and `n + ↑(b + c)` are the same integer but not the same term when `n` is a variable.

## Implementation notes

**The induction is run through free-object helpers.**  `assoc_zero_free` and `assoc_succ_free`
state the base case and the inductive step with every object and morphism a variable, the
transports and the successor comparisons among them, so that the one coherence identity
(`Stacks.GradedSections.coherence_powAdd_assoc_zero`) and the one naturality rewrite
(inside `Stacks.GradedSections.powAdd_assoc_step`) are discharged away from the powers.  At the
powers themselves no `rw` crosses a spelling: the step is closed by `exact`, and the hypotheses
saying that a whiskered successor comparison in a nonnegative degree is an identity are
`MonoidalCategory.whiskerLeft_id` applied at objects that are equal by `rfl`.

**Why `rfl` suffices for the transports.**  `Stacks.TensorPowers.reindex` is an `eqToIso`, and a
proof of an equality whose two sides are definitionally equal is definitionally the reflexivity
proof, so such a transport is the identity by `rfl`.  That is how the two inner transports of the
inductive step are removed.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)

## What is not done

A negative **second** or **third** exponent.  There the recursion genuinely enters the inverse
isomorphisms through `Stacks.TensorPowers.TensorInverse.predIso`, and relating one step down
(`predIso`, built from `TensorInverse.mulIso`) to one step up (`succIso`, built from
`TensorInverse.mulIso'`) is not formal: it is the compatibility of the two inverse laws, which
fails for the odd line in super vector spaces.  Equivalently, what is missing is the successor
equation for `addIso` at a negative integer second exponent; the associativity constraint in any
degree where the second or third exponent is negative is interderivable with it.
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Stacks.GradedSections Stacks.TensorPowers

namespace Stacks.TensorPowers.TensorInverse

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow
  Stacks.TensorPowers.intTensorPow

/-- The zeroth clause of the recursion. -/
theorem addNatIso_zero {L : C} (h : TensorInverse L) (n : ℤ) :
    h.addNatIso n 0 =
      ρ_ (intTensorPow L h.inv n) ≪≫
        reindex L h.inv (show n = n + ((0 : ℕ) : ℤ) from by omega) :=
  rfl

/-- The successor clause of the recursion. -/
theorem addNatIso_succ {L : C} (h : TensorInverse L) (n : ℤ) (k : ℕ) :
    h.addNatIso n (k + 1) =
      whiskerLeftIso (intTensorPow L h.inv n) (h.succIso (k : ℤ)) ≪≫
        (α_ (intTensorPow L h.inv n) (intTensorPow L h.inv (k : ℤ)) L).symm ≪≫
          whiskerRightIso (h.addNatIso n k) L ≪≫
            (h.succIso (n + (k : ℤ))).symm ≪≫
              reindex L h.inv
                (show n + (k : ℤ) + 1 = n + ((k + 1 : ℕ) : ℤ) from by omega) :=
  rfl

/-- The reindexing commutes with the successor comparison. -/
theorem reindex_whiskerRight_succIso {L : C} (h : TensorInverse L) {j k z w : ℤ}
    (hjk : j = k) (h₁ : k + 1 = z) (h₃ : j + 1 = w) (h₄ : w = z) :
    ((reindex L h.inv hjk).hom ▷ L) ≫ (h.succIso k).inv ≫ (reindex L h.inv h₁).hom =
      (h.succIso j).inv ≫ (reindex L h.inv h₃).hom ≫ (reindex L h.inv h₄).hom := by
  subst hjk
  simp only [reindex, eqToIso.hom, eqToHom_trans, eqToHom_refl,
    MonoidalCategory.id_whiskerRight, Category.id_comp]

/-- The base case, with every object and morphism free. -/
private theorem assoc_zero_free {A B P T : C} (f : A ⊗ B ⟶ P) (t : P ⟶ T) (u : B ⟶ B)
    (hu : u = 𝟙 B) :
    (f ▷ 𝟙_ C) ≫ (ρ_ P).hom ≫ t =
      (α_ A B (𝟙_ C)).hom ≫ (A ◁ ((ρ_ B).hom ≫ u)) ≫ f ≫ t := by
  rw [hu, Category.comp_id]
  calc (f ▷ 𝟙_ C) ≫ (ρ_ P).hom ≫ t = ((f ▷ 𝟙_ C) ≫ (ρ_ P).hom) ≫ t := by
        rw [Category.assoc]
    _ = ((α_ A B (𝟙_ C)).hom ≫ (A ◁ (ρ_ B).hom) ≫ f) ≫ t := by
        rw [coherence_powAdd_assoc_zero]
    _ = _ := by simp only [Category.assoc]

/-- The inductive step, with every object and morphism free. -/
private theorem assoc_succ_free {A B K L P Q R Rm V₁ V₃ W Z : C}
    (f : A ⊗ B ⟶ P) (g : B ⊗ K ⟶ Q) (p : P ⊗ K ⟶ R) (m : A ⊗ Q ⟶ Rm)
    (rr : Rm ⟶ R) (s₁ : R ⊗ L ⟶ V₁) (r₁ : V₁ ⟶ Z) (s₃ : Rm ⊗ L ⟶ V₃) (r₃ : V₃ ⟶ W)
    (r' : W ⟶ Z)
    (u₁ : P ⊗ (K ⊗ L) ⟶ P ⊗ (K ⊗ L)) (hu₁ : u₁ = 𝟙 _)
    (u₂ : B ⊗ (K ⊗ L) ⟶ B ⊗ (K ⊗ L)) (hu₂ : u₂ = 𝟙 _)
    (v₂ : Q ⊗ L ⟶ Q ⊗ L) (hv₂ : v₂ = 𝟙 _)
    (w₂ : Q ⊗ L ⟶ Q ⊗ L) (hw₂ : w₂ = 𝟙 _)
    (u₃ : A ⊗ (Q ⊗ L) ⟶ A ⊗ (Q ⊗ L)) (hu₃ : u₃ = 𝟙 _)
    (ih : (f ▷ K) ≫ p = (α_ A B K).hom ≫ (A ◁ g) ≫ m ≫ rr)
    (hcompat : (rr ▷ L) ≫ s₁ ≫ r₁ = s₃ ≫ r₃ ≫ r') :
    (f ▷ (K ⊗ L)) ≫ u₁ ≫ (α_ P K L).inv ≫ (p ▷ L) ≫ s₁ ≫ r₁ =
      (α_ A B (K ⊗ L)).hom ≫ (A ◁ (u₂ ≫ (α_ B K L).inv ≫ (g ▷ L) ≫ v₂ ≫ w₂)) ≫
        u₃ ≫ (α_ A Q L).inv ≫ (m ▷ L) ≫ s₃ ≫ r₃ ≫ r' := by
  subst hu₁; subst hu₂; subst hv₂; subst hw₂; subst hu₃
  simp only [Category.id_comp, Category.comp_id]
  calc (f ▷ (K ⊗ L)) ≫ (α_ P K L).inv ≫ (p ▷ L) ≫ s₁ ≫ r₁
      = ((f ▷ (K ⊗ L)) ≫ (α_ P K L).inv ≫ (p ▷ L)) ≫ s₁ ≫ r₁ := by
        simp only [Category.assoc]
    _ = ((α_ A B (K ⊗ L)).hom ≫ (A ◁ ((α_ B K L).inv ≫ (g ▷ L))) ≫ (α_ A Q L).inv ≫
          ((m ≫ rr) ▷ L)) ≫ s₁ ≫ r₁ := by
        rw [powAdd_assoc_step f g p (m ≫ rr) ih]
    _ = (α_ A B (K ⊗ L)).hom ≫ (A ◁ ((α_ B K L).inv ≫ (g ▷ L))) ≫ (α_ A Q L).inv ≫
          (m ▷ L) ≫ ((rr ▷ L) ≫ s₁ ≫ r₁) := by
        rw [MonoidalCategory.comp_whiskerRight]; simp only [Category.assoc]
    _ = _ := by rw [hcompat]

/-- **The associativity constraint for the integer addition law, with an arbitrary integer first
exponent and nonnegative second and third exponents.** -/
@[sga "5 VI 1.3.4" "partial"]
theorem addNatIso_assoc {L : C} (h : TensorInverse L) (n : ℤ) (b : ℕ) : ∀ c : ℕ,
    ((h.addNatIso n b).hom ▷ intTensorPow L h.inv (c : ℤ)) ≫
        (h.addNatIso (n + (b : ℤ)) c).hom =
      (α_ (intTensorPow L h.inv n) (intTensorPow L h.inv (b : ℤ))
          (intTensorPow L h.inv (c : ℤ))).hom ≫
        (intTensorPow L h.inv n ◁ (h.addNatIso (b : ℤ) c).hom) ≫
          (h.addNatIso n (b + c)).hom ≫
            (reindex L h.inv
              (show n + ((b + c : ℕ) : ℤ) = n + (b : ℤ) + (c : ℤ) from by omega)).hom
  | 0 => by
      rw [addNatIso_zero h (n + (b : ℤ)), addNatIso_zero h (b : ℤ)]
      simp only [Iso.trans_hom]
      exact assoc_zero_free (h.addNatIso n b).hom _ _ rfl
  | c + 1 => by
      rw [addNatIso_succ h (n + (b : ℤ)) c, addNatIso_succ h (b : ℤ) c,
        show h.addNatIso n (b + (c + 1)) = _ from addNatIso_succ h n (b + c)]
      simp only [Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, whiskerRightIso_hom,
        Category.assoc]
      refine assoc_succ_free (h.addNatIso n b).hom (h.addNatIso (b : ℤ) c).hom
        (h.addNatIso (n + (b : ℤ)) c).hom (h.addNatIso n (b + c)).hom _ _ _ _ _ _
        _ ?_ _ ?_ _ ?_ _ ?_ _ ?_ (addNatIso_assoc h n b c)
        (reindex_whiskerRight_succIso h _ _ _ _)
      all_goals first | rfl | exact MonoidalCategory.whiskerLeft_id _ _

end Stacks.TensorPowers.TensorInverse

end
