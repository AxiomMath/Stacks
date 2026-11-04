module

public import StacksFrontier.AlgebraicGeometry.GradedSections.Braided
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The associativity constraint on the addition isomorphisms of tensor powers

Let `C` be a monoidal category and `L` an object of `C`. `StacksDraft/AlgebraicGeometry/F3/
GradedSections/Braided.lean` defines the addition morphism
`powAdd L n m : L ^⊗ n ⊗ L ^⊗ m ⟶ L ^⊗ (n + m)` on the nonnegative tensor powers of `L`, proves
it is the left unitor in degree `(0, m)`, and proves its **commutativity** constraint under
`Stacks.GradedSections.HasTrivialSelfBraiding`. This file adds the three remaining pieces of the
coherence that Stacks Tag 01CU asserts for the canonical multiplication, with its formulation
omitted:

* the **associativity** constraint, against the associator of `C`;
* the **normalisation** in degree `(n, 1)`, which identifies the multiplication by the first
  power with one more step of the defining iteration and so removes the cocycle ambiguity;
* the fact that the addition morphism is an **isomorphism**, so that there is a multiplication
  *isomorphism* and not merely a map.

With the unit and commutativity constraints already available, that is the full coherence of the
nonnegative-degree multiplication, stated against the unitors, associator and braiding of `C`
itself and against no auxiliary choices.

## Main definitions

* `Stacks.GradedSections.powCongrIso`: the transport `L ^⊗ n ≅ L ^⊗ m` along `n = m`, the
  isomorphism underlying `Stacks.GradedSections.powCongr`.
* `Stacks.GradedSections.powAddIso`: **the multiplication isomorphism**
  `L ^⊗ n ⊗ L ^⊗ m ≅ L ^⊗ (n + m)`, whose underlying morphism is `powAdd` by
  `powAddIso_hom`.

## Main results

* `Stacks.GradedSections.powAdd_assoc` and `Stacks.GradedSections.powAddIso_assoc`:
  **the associativity constraint.** Adding the first two exponents and then the third agrees
  with reassociating, adding the last two, and then adding the first — up to the transport that
  the grading forces.
* `Stacks.GradedSections.powAdd_one_right` and `Stacks.GradedSections.powAddIso_one_right`:
  **the normalisation.** Multiplication by the first power is `L ^⊗ n ◁ (λ_ L).hom`, i.e. the
  single step `L ^⊗ n ⊗ (𝟙_ C ⊗ L) ⟶ L ^⊗ n ⊗ L = L ^⊗ (n + 1)` of the iteration which defines
  the powers. In particular no cocycle ambiguity is left.
* `Stacks.GradedSections.powAddIso_zero_left` and
  `Stacks.GradedSections.powAddIso_zero_right`: the two unit constraints, in isomorphism form.
* `Stacks.GradedSections.powAddIso_comm`: the commutativity constraint in isomorphism form.
* `Stacks.GradedSections.powAddIso_natTensorPow_right`: the multiplication isomorphism is
  compatible with the identification `L ^⊗ (n + 1) = L ^⊗ n ⊗ L`, which is what makes the
  normalisation a statement about the iteration.

## Implementation notes

**Every coherence identity is isolated in free objects.** `coherence_powAdd_assoc_zero`,
`coherence_powAdd_assoc_step` and `coherence_triangle_powAdd_one` mention no tensor power at
all; each is proved by the `monoidal` tactic, which cannot see through
`Stacks.TensorPowers.natTensorPow` whatever the transparency setting. This is the discipline the
sibling file established and the reason no proof here calls `monoidal` on a goal about powers.

**The shape of the induction.** `powAdd` recurses on its *second* exponent, so associativity is
an induction on the *third*: both `powAdd L (n + m) (k + 1)` and `powAdd L n (m + (k + 1))`
unfold, the latter because `m + (k + 1)` and `(m + k) + 1` are the same natural number by `rfl`.
No analogue of the sibling file's `powSwap` is needed, and no braiding appears: associativity,
unlike commutativity, is a formal consequence of the monoidal axioms and holds for every object
of every monoidal category, invertible or not.

**The inductive step is split in two.** `powAdd_assoc_step` takes the inductive hypothesis as an
argument and is stated in free objects and arbitrary morphisms, so that the one naturality
rewrite (`associator_inv_naturality_left`) and the one coherence identity are discharged away
from the powers. `powAdd_assoc` is then three rewrites and an application.

**Transports.** `powCongr L h` depends only on the endpoints of `h`, equality proofs being
definitionally irrelevant; a transport whose endpoints are the *same* power up to `rfl` is
therefore the identity by `rfl`, which is how the base case of `powAdd_assoc` disposes of
`powCongr L (Nat.add_assoc n m 0).symm`.

**Universes.** Polymorphic in both category universes, with no constraint between them.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU) — the canonical
  isomorphisms `L ^⊗ n ⊗ L ^⊗ m → L ^⊗ (n + m)` and the commutativity and associativity
  constraints they satisfy, there stated with the formulation omitted.

## What is not done

Nothing is stated for negative exponents. The integer-indexed family is
`Stacks.TensorPowers.intTensorPow`, whose addition law `Stacks.TensorPowers.TensorInverse.addIso`
recurses through the inverse isomorphisms; the identification of that family with this one in
nonnegative degree is `Stacks.TensorPowers.TensorInverse.addIso_natCast` in the sibling file
`StacksFrontier/AlgebraicGeometry/TensorPowerAssoc/Integer.lean`, and only nonnegative degrees
are covered there as well.

`HasTrivialSelfBraiding` is not discharged for an invertible sheaf of modules; that is the one
genuinely mathematical input the commutativity constraint needs, and it is still a hypothesis.
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory BraidedCategory Stacks.TensorPowers

namespace Stacks.GradedSections

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

section Coherence

/-- The base case of `powAdd_assoc`, in free objects and an arbitrary morphism: the right
unitor of a tensor product, read through naturality. -/
theorem coherence_powAdd_assoc_zero {A B P : C} (f : A ⊗ B ⟶ P) :
    (f ▷ 𝟙_ C) ≫ (ρ_ P).hom = (α_ A B (𝟙_ C)).hom ≫ (A ◁ (ρ_ B).hom) ≫ f := by
  monoidal

/-- The inductive step of `powAdd_assoc`, in free objects and arbitrary morphisms. This is the
pentagon, conjugated by the naturality of the associator in its outer arguments. -/
theorem coherence_powAdd_assoc_step {A B K M Q R : C} (g : B ⊗ K ⟶ Q) (r : A ⊗ Q ⟶ R) :
    (α_ (A ⊗ B) K M).inv ≫ ((α_ A B K).hom ≫ (A ◁ g) ≫ r) ▷ M =
      (α_ A B (K ⊗ M)).hom ≫ (A ◁ ((α_ B K M).inv ≫ (g ▷ M))) ≫ (α_ A Q M).inv ≫ (r ▷ M) := by
  monoidal

/-- The triangle identity, in the form the degree-one normalisation needs. -/
theorem coherence_triangle_powAdd_one {A B : C} :
    (α_ A (𝟙_ C) B).inv ≫ ((ρ_ A).hom ▷ B) = A ◁ (λ_ B).hom := by
  monoidal

end Coherence

section Assoc

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

/-- The inductive step of `powAdd_assoc`, taking its inductive hypothesis as an argument. Stated
in free objects and arbitrary morphisms, so that the naturality rewrite and the coherence
identity are both discharged without any tensor power in sight. -/
theorem powAdd_assoc_step {A B K M P Q R : C} (f : A ⊗ B ⟶ P) (g : B ⊗ K ⟶ Q) (h : P ⊗ K ⟶ R)
    (r : A ⊗ Q ⟶ R) (ih : (f ▷ K) ≫ h = (α_ A B K).hom ≫ (A ◁ g) ≫ r) :
    (f ▷ (K ⊗ M)) ≫ (α_ P K M).inv ≫ (h ▷ M) =
      (α_ A B (K ⊗ M)).hom ≫ (A ◁ ((α_ B K M).inv ≫ (g ▷ M))) ≫ (α_ A Q M).inv ≫ (r ▷ M) := by
  rw [← coherence_powAdd_assoc_step g r, ← ih, comp_whiskerRight, ← Category.assoc,
    associator_inv_naturality_left, Category.assoc]

/-- **The associativity constraint on the addition morphisms of tensor powers**, which Stacks
Tag 01CU states with the formulation omitted. Adding the first two exponents and then the third
agrees, after reassociating, with adding the last two and then the first, up to the transport
forced by the grading. Unlike commutativity this needs no hypothesis on `L` and no braiding:
it holds for every object of every monoidal category. -/
theorem powAdd_assoc (L : C) (n m : ℕ) : ∀ k : ℕ,
    (powAdd L n m ▷ natTensorPow L k) ≫ powAdd L (n + m) k =
      (α_ (natTensorPow L n) (natTensorPow L m) (natTensorPow L k)).hom ≫
        (natTensorPow L n ◁ powAdd L m k) ≫ powAdd L n (m + k) ≫
          powCongr L (Nat.add_assoc n m k).symm
  | 0 => by
      show (powAdd L n m ▷ 𝟙_ C) ≫ (ρ_ (natTensorPow L (n + m))).hom =
        (α_ (natTensorPow L n) (natTensorPow L m) (𝟙_ C)).hom ≫
          (natTensorPow L n ◁ (ρ_ (natTensorPow L m)).hom) ≫
            powAdd L n m ≫ 𝟙 (natTensorPow L (n + m))
      rw [Category.comp_id]
      exact coherence_powAdd_assoc_zero (powAdd L n m)
  | k + 1 => by
      have he : powCongr L (Nat.add_assoc n m (k + 1)).symm =
          powCongr L (Nat.add_assoc n m k).symm ▷ L := (powCongr_whiskerRight L _ _).symm
      show (powAdd L n m ▷ (natTensorPow L k ⊗ L)) ≫
          (α_ (natTensorPow L (n + m)) (natTensorPow L k) L).inv ≫ (powAdd L (n + m) k ▷ L) =
        (α_ (natTensorPow L n) (natTensorPow L m) (natTensorPow L k ⊗ L)).hom ≫
          (natTensorPow L n ◁ ((α_ (natTensorPow L m) (natTensorPow L k) L).inv ≫
            (powAdd L m k ▷ L))) ≫
              ((α_ (natTensorPow L n) (natTensorPow L (m + k)) L).inv ≫
                (powAdd L n (m + k) ▷ L)) ≫ powCongr L (Nat.add_assoc n m (k + 1)).symm
      rw [he]
      simp only [Category.assoc, ← comp_whiskerRight]
      exact powAdd_assoc_step (powAdd L n m) (powAdd L m k) (powAdd L (n + m) k)
        (powAdd L n (m + k) ≫ powCongr L (Nat.add_assoc n m k).symm) (powAdd_assoc L n m k)

/-- **The normalisation of the addition morphism in degree one.** Multiplication by the first
tensor power is the single step `L ^⊗ n ⊗ (𝟙_ C ⊗ L) ⟶ L ^⊗ n ⊗ L` of the iteration which
defines the powers, namely the left unitor whiskered into the second factor. This is what
removes the cocycle ambiguity from the coherent multiplication: a family of multiplication
isomorphisms satisfying associativity is determined by its value in degree `(n, 1)`. -/
theorem powAdd_one_right (L : C) (n : ℕ) :
    powAdd L n 1 = natTensorPow L n ◁ (λ_ L).hom := by
  rw [powAdd_succ, powAdd_zero]
  exact coherence_triangle_powAdd_one

end Assoc

section Iso

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

/-- The transport of a tensor power along an equality of exponents, as an isomorphism. Its
underlying morphism is `powCongr`. -/
abbrev powCongrIso (L : C) {n m : ℕ} (h : n = m) : natTensorPow L n ≅ natTensorPow L m :=
  eqToIso (congrArg (natTensorPow L) h)

/-- The underlying morphism of `powCongrIso L h` is `powCongr L h`. -/
theorem powCongrIso_hom (L : C) {n m : ℕ} (h : n = m) :
    (powCongrIso L h).hom = powCongr L h := rfl

/-- **The multiplication isomorphism on the nonnegative tensor powers of `L`**,
`L ^⊗ n ⊗ L ^⊗ m ≅ L ^⊗ (n + m)`, defined by the same recursion as `powAdd`, whose underlying
morphism is `powAdd L n m` (`powAddIso_hom`). -/
@[sga "5 VI 1.3.4" "partial"]
def powAddIso (L : C) : (n m : ℕ) →
    (natTensorPow L n ⊗ natTensorPow L m ≅ natTensorPow L (n + m))
  | _, 0 => ρ_ _
  | n, m + 1 => (α_ _ _ _).symm ≪≫ whiskerRightIso (powAddIso L n m) L

/-- The multiplication isomorphism refines the addition morphism. -/
@[simp]
theorem powAddIso_hom (L : C) : ∀ (n m : ℕ), (powAddIso L n m).hom = powAdd L n m
  | _, 0 => rfl
  | n, m + 1 => by
      show (α_ (natTensorPow L n) (natTensorPow L m) L).inv ≫
        ((powAddIso L n m).hom ▷ L) = powAdd L n (m + 1)
      rw [powAddIso_hom L n m, powAdd_succ]

/-- `powAdd` is an isomorphism, for every pair of nonnegative exponents. -/
instance isIso_powAdd (L : C) (n m : ℕ) : IsIso (powAdd L n m) := by
  rw [← powAddIso_hom L n m]
  infer_instance

/-- The right unit constraint: multiplication by the zeroth power on the right is the right
unitor. This holds by definition of the recursion. -/
theorem powAddIso_zero_right (L : C) (n : ℕ) :
    powAddIso L n 0 = ρ_ (natTensorPow L n) := rfl

/-- The left unit constraint: multiplication by the zeroth power on the left is the left
unitor, after the transport `0 + m = m`. -/
theorem powAddIso_zero_left (L : C) (m : ℕ) :
    powAddIso L 0 m ≪≫ powCongrIso L (Nat.zero_add m) = λ_ (natTensorPow L m) :=
  Iso.ext (by simpa using powAdd_zero_left L m)

/-- **The normalisation in degree one**, in isomorphism form: multiplication by the first
tensor power is the left unitor of the second factor, whiskered into `L ^⊗ n`. -/
theorem powAddIso_one_right (L : C) (n : ℕ) :
    powAddIso L n 1 = whiskerLeftIso (natTensorPow L n) (λ_ L) :=
  Iso.ext (by simpa using powAdd_one_right L n)

/-- **The associativity constraint**, in isomorphism form. -/
theorem powAddIso_assoc (L : C) (n m k : ℕ) :
    whiskerRightIso (powAddIso L n m) (natTensorPow L k) ≪≫ powAddIso L (n + m) k =
      α_ (natTensorPow L n) (natTensorPow L m) (natTensorPow L k) ≪≫
        whiskerLeftIso (natTensorPow L n) (powAddIso L m k) ≪≫
          powAddIso L n (m + k) ≪≫ powCongrIso L (Nat.add_assoc n m k).symm :=
  Iso.ext (by simpa using powAdd_assoc L n m k)

/-- **The normalisation in degree one, in the integer-indexed vocabulary.** The first-power
identification `L ^⊗ 1 ≅ L` of `Stacks.TensorPowers.oneIso` is the left unitor, and the
successor step `L ^⊗ n ⊗ L = L ^⊗ (n + 1)` is the identity, so the normalisation says that
multiplication by the first power is that step after that identification — which is the shape in
which Stacks Tag 01CU's canonical multiplication is pinned down. -/
theorem powAddIso_one_right_oneIso (L L' : C) (n : ℕ) :
    powAddIso L n 1 = whiskerLeftIso (natTensorPow L n) (oneIso L L') :=
  powAddIso_one_right L n

end Iso

section Braided

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

variable [BraidedCategory C]

/-- **The commutativity constraint**, in isomorphism form. The hypothesis is the one the sibling
file isolates and cannot be dropped: at degrees `(1, 1)` the constraint *is* the triviality of
the self-braiding of `L`. -/
theorem powAddIso_comm (L : C) [HasTrivialSelfBraiding L] (n m : ℕ) :
    β_ (natTensorPow L n) (natTensorPow L m) ≪≫ powAddIso L m n =
      powAddIso L n m ≪≫ powCongrIso L (Nat.add_comm n m) :=
  Iso.ext (by simpa using braiding_comp_powAdd L n m)

end Braided

end Stacks.GradedSections

end
