module

public import StacksFrontier.AlgebraicGeometry.TensorPowerAssoc.IntegerUniform
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The associativity of the integer addition law in an arbitrary integer tridegree

`Stacks.TensorPowers.TensorInverse.addIso` is the addition law
`L ^⊗ n ⊗ L ^⊗ m ≅ L ^⊗ (n + m)` of the integer tensor powers of an object with a two-sided
tensor inverse.  This file proves its associativity constraint with all three exponents arbitrary
integers; `Stacks.TensorPowers.TensorInverse.addIso_assoc_natCast` is the case of three natural
exponents and `Stacks.TensorPowers.TensorInverse.addNatIso_assoc` the case of natural second and
third exponents.

The proof is by induction over `ℤ` in the third exponent, and the step is an **equivalence**:
adding one factor of `L` to the third exponent whiskers the whole constraint by `L` and conjugates
it by comparisons that are isomorphisms, so the constraint in the tridegree `(n, m, c)` and the one
in `(n, m, c+1)` imply each other, right whiskering by `L` being injective because `L` has a tensor
inverse.

## Main results

* `Stacks.TensorPowers.TensorInverse.addIso_assoc`: **the associativity constraint of the integer
  addition law in an arbitrary integer tridegree.**
* `Stacks.TensorPowers.TensorInverse.addIso_assoc_succ_iff`: **the step, as an equivalence**: the
  constraint in the tridegree `(n, m, c)` holds if and only if it holds in `(n, m, c + 1)`.
* `Stacks.TensorPowers.TensorInverse.addIso_assoc_zero`: the base case, the tridegree `(n, m, 0)`,
  which is the right unit law read through naturality of the right unitor.
* `Stacks.TensorPowers.assoc_succ_free_iff`: the equivalence with every object and morphism free.
* `Stacks.TensorPowers.whiskerRight_injective_of_mulIso`: right whiskering by an object with a
  tensor inverse is injective on morphisms.
* `Stacks.TensorPowers.assoc_whiskerRight_free`: the left-hand side of an associativity
  constraint in one more degree is that constraint whiskered by the new factor.
* `Stacks.TensorPowers.TensorInverse.addIso_zero_right`: the right unit law at the spelling
  `n + 0` of the degree.
* `Stacks.TensorPowers.TensorInverse.reindex_comp_reindex_assoc`: the composition of two degree
  transports, reassociated.

## Implementation notes

**Why the step is stated with free objects.**  At the powers a goal naming both `n + (m + c)` and
`n + m + c` — the same integer, not the same term — is rejected by `rw` once part of it has been
rewritten, so the equivalence is proved once in `assoc_succ_free_iff`, where every object and
morphism is a variable, and the two sides of the goal are brought to its shape by `have`s whose
statements are written out.  Within those `have`s every transport composition is moved with
`reindex_comp_reindex_assoc` at explicit degrees rather than by `simp`, because the trailing pair
of transports has the same type as the inner one and an unguided rewrite collapses the wrong pair.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Stacks.GradedSections Stacks.TensorPowers

namespace Stacks.TensorPowers

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- **Right whiskering by an object with a tensor inverse is injective on morphisms**: if
`Z ⊗ Z' ≅ 𝟙_ C` and `u ▷ Z = v ▷ Z`, then `u = v`. -/
theorem whiskerRight_injective_of_mulIso {X Y Z Z' : C} (e : Z ⊗ Z' ≅ 𝟙_ C) {u v : X ⟶ Y}
    (huv : u ▷ Z = v ▷ Z) : u = v := by
  have key : ∀ w : X ⟶ Y,
      (X ◁ e.hom) ≫ (ρ_ X).hom ≫ w =
        (α_ X Z Z').inv ≫ ((w ▷ Z) ▷ Z') ≫ (α_ Y Z Z').hom ≫ (Y ◁ e.hom) ≫
          (ρ_ Y).hom := by
    intro w
    calc (X ◁ e.hom) ≫ (ρ_ X).hom ≫ w
        = (X ◁ e.hom) ≫ (w ▷ 𝟙_ C) ≫ (ρ_ Y).hom := by
          rw [MonoidalCategory.rightUnitor_naturality]
      _ = (w ▷ (Z ⊗ Z')) ≫ (Y ◁ e.hom) ≫ (ρ_ Y).hom := by
          rw [← Category.assoc, MonoidalCategory.whisker_exchange, Category.assoc]
      _ = _ := by rw [MonoidalCategory.whiskerRight_tensor]; simp only [Category.assoc]
  refine (cancel_epi (ρ_ X).hom).mp ((cancel_epi (X ◁ e.hom)).mp ?_)
  rw [key u, key v, huv]

/-- **One factor of the third exponent, moved out of the associativity diagram.**  Adding a
factor `M` to the third slot turns the left-hand side of an associativity constraint into that
constraint whiskered by `M`, conjugated by one associator. -/
theorem assoc_whiskerRight_free {A B K M P R : C} (f : A ⊗ B ⟶ P) (p : P ⊗ K ⟶ R) :
    (f ▷ (K ⊗ M)) ≫ (α_ P K M).inv ≫ (p ▷ M) =
      (α_ (A ⊗ B) K M).inv ≫ (((f ▷ K) ≫ p) ▷ M) := by
  rw [MonoidalCategory.comp_whiskerRight, ← Category.assoc,
    MonoidalCategory.associator_inv_naturality_left, Category.assoc]

/-- **The inductive step of the associativity constraint, as an equivalence**, with every object
and morphism free.  An associativity constraint holds if and only if it holds after whiskering by
a factor `Lb` with a tensor inverse, conjugating by associators and composing with the
comparisons `s₁ ≫ r₁` and `s₃ ≫ r₃ ≫ r'` related by `hcompat`, where `s₁ ≫ r₁` is a split
monomorphism. -/
theorem assoc_succ_free_iff {A B K Lb Lb' P Q R Rm V₁ V₃ W Z : C} (e : Lb ⊗ Lb' ≅ 𝟙_ C)
    (f : A ⊗ B ⟶ P) (g : B ⊗ K ⟶ Q) (p : P ⊗ K ⟶ R) (mm : A ⊗ Q ⟶ Rm) (rr : Rm ⟶ R)
    (s₁ : R ⊗ Lb ⟶ V₁) (r₁ : V₁ ⟶ Z) (s₃ : Rm ⊗ Lb ⟶ V₃) (r₃ : V₃ ⟶ W) (r' : W ⟶ Z)
    (q : Z ⟶ R ⊗ Lb) (hq : s₁ ≫ r₁ ≫ q = 𝟙 (R ⊗ Lb))
    (hcompat : (rr ▷ Lb) ≫ s₁ ≫ r₁ = s₃ ≫ r₃ ≫ r') :
    ((f ▷ K) ≫ p = (α_ A B K).hom ≫ (A ◁ g) ≫ mm ≫ rr) ↔
      ((f ▷ (K ⊗ Lb)) ≫ (α_ P K Lb).inv ≫ (p ▷ Lb) ≫ s₁ ≫ r₁ =
        (α_ A B (K ⊗ Lb)).hom ≫ (A ◁ ((α_ B K Lb).inv ≫ (g ▷ Lb))) ≫
          (α_ A Q Lb).inv ≫ (mm ▷ Lb) ≫ s₃ ≫ r₃ ≫ r') := by
  have hL : (f ▷ (K ⊗ Lb)) ≫ (α_ P K Lb).inv ≫ (p ▷ Lb) ≫ s₁ ≫ r₁ =
      (α_ (A ⊗ B) K Lb).inv ≫ (((f ▷ K) ≫ p) ▷ Lb) ≫ s₁ ≫ r₁ :=
    calc (f ▷ (K ⊗ Lb)) ≫ (α_ P K Lb).inv ≫ (p ▷ Lb) ≫ s₁ ≫ r₁
        = ((f ▷ (K ⊗ Lb)) ≫ (α_ P K Lb).inv ≫ (p ▷ Lb)) ≫ (s₁ ≫ r₁) := by
          simp only [Category.assoc]
      _ = ((α_ (A ⊗ B) K Lb).inv ≫ (((f ▷ K) ≫ p) ▷ Lb)) ≫ (s₁ ≫ r₁) := by
          rw [assoc_whiskerRight_free]
      _ = _ := by simp only [Category.assoc]
  have hR : (α_ A B (K ⊗ Lb)).hom ≫ (A ◁ ((α_ B K Lb).inv ≫ (g ▷ Lb))) ≫
        (α_ A Q Lb).inv ≫ (mm ▷ Lb) ≫ s₃ ≫ r₃ ≫ r' =
      (α_ (A ⊗ B) K Lb).inv ≫
        (((α_ A B K).hom ≫ (A ◁ g) ≫ mm ≫ rr) ▷ Lb) ≫ s₁ ≫ r₁ :=
    calc (α_ A B (K ⊗ Lb)).hom ≫ (A ◁ ((α_ B K Lb).inv ≫ (g ▷ Lb))) ≫
          (α_ A Q Lb).inv ≫ (mm ▷ Lb) ≫ s₃ ≫ r₃ ≫ r'
        = (α_ A B (K ⊗ Lb)).hom ≫ (A ◁ ((α_ B K Lb).inv ≫ (g ▷ Lb))) ≫
            (α_ A Q Lb).inv ≫ (mm ▷ Lb) ≫ (rr ▷ Lb) ≫ s₁ ≫ r₁ := by rw [hcompat]
      _ = ((α_ A B (K ⊗ Lb)).hom ≫ (A ◁ ((α_ B K Lb).inv ≫ (g ▷ Lb))) ≫
            (α_ A Q Lb).inv ≫ ((mm ≫ rr) ▷ Lb)) ≫ (s₁ ≫ r₁) := by
          rw [MonoidalCategory.comp_whiskerRight]; simp only [Category.assoc]
      _ = ((α_ (A ⊗ B) K Lb).inv ≫
            (((α_ A B K).hom ≫ (A ◁ g) ≫ (mm ≫ rr)) ▷ Lb)) ≫ (s₁ ≫ r₁) := by
          rw [← coherence_powAdd_assoc_step]
      _ = _ := by simp only [Category.assoc]
  rw [hL, hR]
  refine ⟨fun hXY ↦ by rw [hXY], fun hbig ↦ ?_⟩
  refine whiskerRight_injective_of_mulIso e ?_
  simpa only [Category.assoc, hq, Category.comp_id] using
    congrArg (fun z ↦ z ≫ q) ((cancel_epi (α_ (A ⊗ B) K Lb).inv).mp hbig)

end Stacks.TensorPowers

namespace Stacks.TensorPowers.TensorInverse

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow
  Stacks.TensorPowers.intTensorPow

/-- `Stacks.TensorPowers.TensorInverse.reindex_comp_reindex`, reassociated: two consecutive degree
transports followed by a morphism `f` are the single transport followed by `f`. -/
theorem reindex_comp_reindex_assoc {L : C} (h : TensorInverse L) {n m k : ℤ} (hnm : n = m)
    (hmk : m = k) {X : C} (f : intTensorPow L h.inv k ⟶ X) :
    (reindex L h.inv hnm).hom ≫ (reindex L h.inv hmk).hom ≫ f =
      (reindex L h.inv (hnm.trans hmk)).hom ≫ f := by
  rw [← Category.assoc, reindex_comp_reindex]

/-- Transporting along `n + 1 = k` and back, between the two comparisons `succIso n`, is the
identity. -/
private theorem succIso_inv_reindex_reindex_succIso {L : C} (h : TensorInverse L) {n : ℤ} {k : ℤ}
    (hnk : n + 1 = k) (hkn : k = n + 1) :
    (h.succIso n).inv ≫ (reindex L h.inv hnk).hom ≫ (reindex L h.inv hkn).hom ≫
      (h.succIso n).hom = 𝟙 _ := by
  rw [reindex_comp_reindex_assoc, reindex_self h (show n + 1 = n + 1 from rfl), Category.id_comp,
    Iso.inv_hom_id]

/-- The base case of the associativity constraint, with every object and morphism free: the
right unitor of a tensor product read through naturality, with the two degree transports of the
integer recursion cancelling against each other. -/
private theorem assoc_zero_free {A B B' P P' T : C} (f : A ⊗ B ⟶ P) (r₁ : P ⟶ T)
    (r₂ : B ⟶ B') (r₂' : B' ⟶ B) (r₄ : P ⟶ P') (r₃ : P' ⟶ T)
    (h₂ : r₂ ≫ r₂' = 𝟙 B) (h₄ : r₄ ≫ r₃ = r₁) :
    (f ▷ 𝟙_ C) ≫ (ρ_ P).hom ≫ r₁ =
      (α_ A B (𝟙_ C)).hom ≫ (A ◁ ((ρ_ B).hom ≫ r₂)) ≫ ((A ◁ r₂') ≫ f ≫ r₄) ≫ r₃ := by
  rw [← h₄, ← Category.assoc (f ▷ 𝟙_ C) (ρ_ P).hom, coherence_powAdd_assoc_zero]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [← Category.assoc (A ◁ r₂) (A ◁ r₂'), ← MonoidalCategory.whiskerLeft_comp, h₂,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]

/-- The right unit law of the addition law, at the spelling `n + 0` of the degree: the addition
isomorphism in the bidegree `(n, 0)` is the right unitor followed by the transport from `n` to
`n + 0`. -/
theorem addIso_zero_right {L : C} (h : TensorInverse L) (n : ℤ) :
    (h.addIso n 0).hom =
      (ρ_ (intTensorPow L h.inv n)).hom ≫
        (reindex L h.inv (show n = n + 0 from by omega)).hom := rfl

/-- **The associativity constraint of the addition law in the tridegree `(n, m, 0)`.** -/
theorem addIso_assoc_zero {L : C} (h : TensorInverse L) (n m : ℤ) :
    ((h.addIso n m).hom ▷ intTensorPow L h.inv 0) ≫ (h.addIso (n + m) 0).hom =
      (α_ (intTensorPow L h.inv n) (intTensorPow L h.inv m) (intTensorPow L h.inv 0)).hom ≫
        (intTensorPow L h.inv n ◁ (h.addIso m 0).hom) ≫
          (h.addIso n (m + 0)).hom ≫
            (reindex L h.inv (show n + (m + 0) = n + m + 0 from by omega)).hom := by
  rw [addIso_zero_right h (n + m), addIso_zero_right h m,
    addIso_congr_right h n (show m = m + 0 from by omega)]
  exact assoc_zero_free (h.addIso n m).hom _ _ _ _ _
    (by rw [reindex_comp_reindex, reindex_self])
    (by rw [reindex_comp_reindex])

/-- **The associativity constraint of the addition law in the tridegree `(n, m, c)` is equivalent
to the one in the tridegree `(n, m, c + 1)`**, for arbitrary integers. -/
theorem addIso_assoc_succ_iff {L : C} (h : TensorInverse L)
    (hs : (α_ L h.inv L).hom ≫ L ◁ h.mulIso'.hom ≫ (ρ_ L).hom =
      h.mulIso.hom ▷ L ≫ (λ_ L).hom) (n m c c' : ℤ) (hc : c + 1 = c') :
    (((h.addIso n m).hom ▷ intTensorPow L h.inv c) ≫ (h.addIso (n + m) c).hom =
        (α_ (intTensorPow L h.inv n) (intTensorPow L h.inv m)
            (intTensorPow L h.inv c)).hom ≫
          (intTensorPow L h.inv n ◁ (h.addIso m c).hom) ≫
            (h.addIso n (m + c)).hom ≫
              (reindex L h.inv (show n + (m + c) = n + m + c from by omega)).hom) ↔
      (((h.addIso n m).hom ▷ intTensorPow L h.inv c') ≫ (h.addIso (n + m) c').hom =
        (α_ (intTensorPow L h.inv n) (intTensorPow L h.inv m)
            (intTensorPow L h.inv c')).hom ≫
          (intTensorPow L h.inv n ◁ (h.addIso m c').hom) ≫
            (h.addIso n (m + c')).hom ≫
              (reindex L h.inv (show n + (m + c') = n + m + c' from by omega)).hom) := by
  have hA : ((h.addIso n m).hom ▷ intTensorPow L h.inv c') ≫ (h.addIso (n + m) c').hom =
      ((intTensorPow L h.inv n ⊗ intTensorPow L h.inv m) ◁
          ((reindex L h.inv hc.symm).hom ≫ (h.succIso c).hom)) ≫
        (((h.addIso n m).hom ▷ (intTensorPow L h.inv c ⊗ L)) ≫
          (α_ (intTensorPow L h.inv (n + m)) (intTensorPow L h.inv c) L).inv ≫
            ((h.addIso (n + m) c).hom ▷ L) ≫
              (h.succIso (n + m + c)).inv ≫
                (reindex L h.inv (show n + m + c + 1 = n + m + c' from by omega)).hom) := by
    rw [addIso_succ h hs (n + m) c c' hc, ← Category.assoc,
      ← MonoidalCategory.whisker_exchange]
    simp only [Category.assoc]
  have hB : (α_ (intTensorPow L h.inv n) (intTensorPow L h.inv m)
          (intTensorPow L h.inv c')).hom ≫
        (intTensorPow L h.inv n ◁ (h.addIso m c').hom) ≫
          (h.addIso n (m + c')).hom ≫
            (reindex L h.inv (show n + (m + c') = n + m + c' from by omega)).hom =
      ((intTensorPow L h.inv n ⊗ intTensorPow L h.inv m) ◁
          ((reindex L h.inv hc.symm).hom ≫ (h.succIso c).hom)) ≫
        ((α_ (intTensorPow L h.inv n) (intTensorPow L h.inv m)
            (intTensorPow L h.inv c ⊗ L)).hom ≫
          (intTensorPow L h.inv n ◁
            ((α_ (intTensorPow L h.inv m) (intTensorPow L h.inv c) L).inv ≫
              ((h.addIso m c).hom ▷ L))) ≫
            (α_ (intTensorPow L h.inv n) (intTensorPow L h.inv (m + c)) L).inv ≫
              ((h.addIso n (m + c)).hom ▷ L) ≫
                (h.succIso (n + (m + c))).inv ≫
                  (reindex L h.inv
                    (show n + (m + c) + 1 = n + (m + c') from by omega)).hom ≫
                    (reindex L h.inv
                      (show n + (m + c') = n + m + c' from by omega)).hom) := by
    rw [addIso_succ h hs m c c' hc,
      addIso_succ h hs n (m + c) (m + c') (show m + c + 1 = m + c' from by omega)]
    simp only [Category.assoc]
    rw [← Category.assoc (intTensorPow L h.inv n ◁ _)
        (intTensorPow L h.inv n ◁ ((reindex L h.inv
          (show m + c' = m + c + 1 from by omega)).hom ≫ (h.succIso (m + c)).hom)),
      ← MonoidalCategory.whiskerLeft_comp]
    simp only [Category.assoc]
    rw [succIso_inv_reindex_reindex_succIso h (show m + c + 1 = m + c' from by omega)
          (show m + c' = m + c + 1 from by omega), Category.comp_id]
    rw [MonoidalCategory.whiskerLeft_comp (intTensorPow L h.inv n)
        (intTensorPow L h.inv m ◁ ((reindex L h.inv hc.symm).hom ≫ (h.succIso c).hom))
        ((α_ (intTensorPow L h.inv m) (intTensorPow L h.inv c) L).inv ≫
          ((h.addIso m c).hom ▷ L))]
    simp only [Category.assoc]
    rw [← Category.assoc (α_ (intTensorPow L h.inv n) (intTensorPow L h.inv m)
          (intTensorPow L h.inv c')).hom
        (intTensorPow L h.inv n ◁ intTensorPow L h.inv m ◁
          ((reindex L h.inv hc.symm).hom ≫ (h.succIso c).hom)),
      ← MonoidalCategory.associator_naturality_right]
    simp only [Category.assoc]
  rw [hA, hB, cancel_epi]
  exact assoc_succ_free_iff h.mulIso (h.addIso n m).hom (h.addIso m c).hom
    (h.addIso (n + m) c).hom (h.addIso n (m + c)).hom _ _ _ _ _ _
    ((reindex L h.inv (show n + m + c' = n + m + c + 1 from by omega)).hom ≫
      (h.succIso (n + m + c)).hom)
    (by
      rw [succIso_inv_reindex_reindex_succIso h
        (show n + m + c + 1 = n + m + c' from by omega)
        (show n + m + c' = n + m + c + 1 from by omega)])
    (reindex_whiskerRight_succIso h
      (show n + (m + c) = n + m + c from by omega)
      (show n + m + c + 1 = n + m + c' from by omega)
      (show n + (m + c) + 1 = n + (m + c') from by omega)
      (show n + (m + c') = n + m + c' from by omega))

/-- **The associativity constraint of the integer addition law, in an arbitrary integer
tridegree.**  Adding the first two exponents and then the third agrees, after reassociating, with
adding the last two and then the first, up to the transport between the two spellings of the total
degree — for all three exponents arbitrary integers. -/
@[sga "5 VI 1.3.4" "more general"]
theorem addIso_assoc {L : C} (h : TensorInverse L)
    (hs : (α_ L h.inv L).hom ≫ L ◁ h.mulIso'.hom ≫ (ρ_ L).hom =
      h.mulIso.hom ▷ L ≫ (λ_ L).hom) (n m c : ℤ) :
    ((h.addIso n m).hom ▷ intTensorPow L h.inv c) ≫ (h.addIso (n + m) c).hom =
      (α_ (intTensorPow L h.inv n) (intTensorPow L h.inv m) (intTensorPow L h.inv c)).hom ≫
        (intTensorPow L h.inv n ◁ (h.addIso m c).hom) ≫
          (h.addIso n (m + c)).hom ≫
            (reindex L h.inv (show n + (m + c) = n + m + c from by omega)).hom := by
  induction c using Int.induction_on with
  | zero => exact addIso_assoc_zero h n m
  | succ i ih =>
      exact (addIso_assoc_succ_iff h hs n m (i : ℤ) ((i : ℤ) + 1) rfl).mp ih
  | pred i ih =>
      exact (addIso_assoc_succ_iff h hs n m (-(i : ℤ) - 1) (-(i : ℤ))
        (show -(i : ℤ) - 1 + 1 = -(i : ℤ) from by omega)).mpr ih

end Stacks.TensorPowers.TensorInverse

end
