module

public import StacksFrontier.AlgebraicGeometry.GradedSections.Braided

/-!
# A monoidal functor is multiplicative on the tensor powers

Let `F : C ⥤ D` be an oplax monoidal functor between monoidal categories and `L` an object of
`C`. The cotensorator of `F` assembles, by induction on the exponent, into a comparison
`F(L ^⊗ n) ⟶ (F L) ^⊗ n` between the nonnegative tensor powers
`Stacks.TensorPowers.natTensorPow` of `L` and of `F L`. This file proves that this comparison is
**multiplicative** for the addition law `Stacks.GradedSections.powAdd` of the powers: pulling the
multiplication through `F` and then splitting the powers agrees with splitting first and
multiplying afterwards.

The statement needs no transport: `natTensorPow (F.obj L) (n + m)` is the target of both sides
on the nose, because the addition law is indexed by natural numbers on both sides and no
reindexing of exponents is involved.

## Main definitions

* `Stacks.TensorPowerPullbackMul.natTensorPowComparison`: the comparison
  `F(L ^⊗ n) ⟶ (F L) ^⊗ n`, by induction on `n`. In degree zero it is the counit `η` of the
  oplax structure, and the step is the cotensorator `δ` followed by the comparison in degree `n`
  whiskered by `F L`.
* `Stacks.TensorPowerPullbackMul.natTensorPowComparisonIso`: the same comparison read as an
  isomorphism, for a *monoidal* (not merely oplax monoidal) functor. It is `CategoryTheory.asIso`
  of the comparison, so its forward direction is that comparison on the nose.

## Main results

* `Stacks.TensorPowerPullbackMul.natTensorPowComparison_powAdd`: **the multiplicativity square.**
  `F.map (powAdd L n m) ≫ natTensorPowComparison F L (n + m)` equals
  `δ F (L ^⊗ n) (L ^⊗ m) ≫ (comparison n ⊗ₘ comparison m) ≫ powAdd (F L) n m`.
* `Stacks.TensorPowerPullbackMul.isIso_natTensorPowComparison`: the comparison of a *monoidal*
  functor is invertible, as an instance.
* `Stacks.TensorPowerPullbackMul.natTensorPowComparisonIso_powAdd`: the same square written with
  the isomorphism, which is the shape a consumer that wants to invert the comparison composes
  with.

## Implementation notes

**The induction runs on the second exponent**, because `Stacks.GradedSections.powAdd` does:
`powAdd L n 0` is a right unitor and `powAdd L n (m + 1)` is an associator inverse followed by a
whiskering of `powAdd L n m`. So the base case is exactly the right-unit coherence of `F` and the
step is exactly its associativity coherence, used once each. No braiding and no invertibility of
`L` appear: multiplicativity, like associativity of `powAdd` itself, is a formal consequence of
the monoidal axioms.

**The one identity with arbitrary morphisms is isolated in free objects.**
`coherence_whiskerLeft_associator_inv` mentions no tensor power; it is the naturality of the
associator in its outer arguments, conjugated by the interchange law, and it is what the step of
the induction needs on top of the coherences of `F`. This is the discipline of
`StacksFrontier/AlgebraicGeometry/TensorPowerAssoc/Basic.lean`, and it is needed for the same
reason: no automation sees through `Stacks.TensorPowers.natTensorPow`.

**Only the oplax structure is used for the morphism statement.** `Functor.OplaxMonoidal` suffices
for `natTensorPowComparison` and for the square; `Functor.Monoidal` is required only to package
the comparison as an isomorphism. That split matters for the intended application, where the
cotensorator — the comparison of Stacks Tag 01CD — is the datum with a formula on local sections
and its inverse is not.

**Universes.** Polymorphic in both object and morphism universes of both categories, with no
constraint between them.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU) — the canonical
  multiplication `L ^⊗ n ⊗ L ^⊗ m ≅ L ^⊗ (n + m)` on the tensor powers.
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD) — the comparison
  `f^*(A ⊗ B) ≅ f^*A ⊗ f^*B`, which is the cotensorator in the intended application.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory
open CategoryTheory.Functor.OplaxMonoidal
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powAdd)

namespace Stacks.TensorPowerPullbackMul

/-! ### The one coherence identity, in free objects -/

section Coherence

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- The identity the inductive step needs on top of the coherences of the functor, stated in free
objects and arbitrary morphisms: whiskering a morphism into the right factor, reassociating and
then applying a tensor product of two morphisms to the first two factors is the same as applying
the morphisms first. This is the naturality of the associator in its outer arguments, conjugated
by the interchange law. -/
@[reassoc]
theorem coherence_whiskerLeft_associator_inv {A A' B B' E G : D} (p : A ⟶ A') (q : B ⟶ B')
    (d : E ⟶ B ⊗ G) :
    (A ◁ d) ≫ (α_ A B G).inv ≫ ((p ⊗ₘ q) ▷ G) =
      (p ⊗ₘ (d ≫ (q ▷ G))) ≫ (α_ A' B' G).inv := by
  have key : (α_ A B G).inv ≫ ((p ⊗ₘ q) ▷ G) = (p ⊗ₘ (q ▷ G)) ≫ (α_ A' B' G).inv := by
    rw [← tensorHom_id q G, ← tensorHom_id (p ⊗ₘ q) G, associator_inv_naturality]
  rw [key, tensorHom_def' p (d ≫ (q ▷ G)), MonoidalCategory.whiskerLeft_comp,
    tensorHom_def' p (q ▷ G)]
  simp only [Category.assoc]

end Coherence

/-! ### The comparison and its multiplicativity -/

section Functor

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

section Oplax

variable (F : C ⥤ D) [F.OplaxMonoidal] (L : C)

/-- **The comparison `F(L ^⊗ n) ⟶ (F L) ^⊗ n` of an oplax monoidal functor on the nonnegative
tensor powers.** In degree zero it is the counit `η` of the oplax structure, and the step is the
cotensorator `δ` at `(L ^⊗ n, L)` followed by the comparison in degree `n` whiskered by `F L`;
both `natTensorPow L (n + 1) = natTensorPow L n ⊗ L` and its image under `F.obj` hold on the
nose, which is why no transport appears. -/
def natTensorPowComparison :
    (n : ℕ) → (F.obj (natTensorPow L n) ⟶ natTensorPow (F.obj L) n)
  | 0 => η F
  | n + 1 => δ F (natTensorPow L n) L ≫ (natTensorPowComparison n ▷ F.obj L)

/-- In degree zero the comparison is the counit `η` of the oplax structure. -/
@[simp]
theorem natTensorPowComparison_zero : natTensorPowComparison F L 0 = η F := rfl

/-- In degree `n + 1` the comparison is the cotensorator `δ` at `(L ^⊗ n, L)` followed by the
comparison in degree `n` whiskered by `F L`. -/
@[simp]
theorem natTensorPowComparison_succ (n : ℕ) :
    natTensorPowComparison F L (n + 1) =
      δ F (natTensorPow L n) L ≫ (natTensorPowComparison F L n ▷ F.obj L) := rfl

/-- **An oplax monoidal functor is multiplicative on the tensor powers.** The image under `F` of
the addition law `L ^⊗ n ⊗ L ^⊗ m ⟶ L ^⊗ (n + m)` of Stacks Tag 01CU, followed by the comparison
in degree `n + m`, is the cotensorator followed by the two comparisons and the addition law of
the powers of `F L`. -/
theorem natTensorPowComparison_powAdd (n : ℕ) :
    ∀ m : ℕ, F.map (powAdd L n m) ≫ natTensorPowComparison F L (n + m) =
      δ F (natTensorPow L n) (natTensorPow L m) ≫
        (natTensorPowComparison F L n ⊗ₘ natTensorPowComparison F L m) ≫
          powAdd (F.obj L) n m
  | 0 => by
      have hρ : δ F (natTensorPow L n) (𝟙_ C) ≫ (F.obj (natTensorPow L n) ◁ η F) =
          F.map (ρ_ (natTensorPow L n)).hom ≫ (ρ_ (F.obj (natTensorPow L n))).inv := by
        rw [Functor.OplaxMonoidal.oplax_right_unitality F (natTensorPow L n),
          Iso.hom_inv_id_map_assoc]
      have hgoal : F.map (ρ_ (natTensorPow L n)).hom ≫ natTensorPowComparison F L n =
          δ F (natTensorPow L n) (𝟙_ C) ≫
            (natTensorPowComparison F L n ⊗ₘ η F) ≫ (ρ_ (natTensorPow (F.obj L) n)).hom := by
        rw [tensorHom_def' (natTensorPowComparison F L n) (η F), Category.assoc,
          MonoidalCategory.rightUnitor_naturality (natTensorPowComparison F L n),
          ← Category.assoc (δ F (natTensorPow L n) (𝟙_ C)), hρ]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
      exact hgoal
  | m + 1 => by
      have ih := natTensorPowComparison_powAdd n m
      have hgoal : F.map ((α_ (natTensorPow L n) (natTensorPow L m) L).inv ≫
            (powAdd L n m ▷ L)) ≫
            δ F (natTensorPow L (n + m)) L ≫
              (natTensorPowComparison F L (n + m) ▷ F.obj L) =
          δ F (natTensorPow L n) (natTensorPow L m ⊗ L) ≫
            (natTensorPowComparison F L n ⊗ₘ
                (δ F (natTensorPow L m) L ≫
                  (natTensorPowComparison F L m ▷ F.obj L))) ≫
              (α_ (natTensorPow (F.obj L) n) (natTensorPow (F.obj L) m) (F.obj L)).inv ≫
                (powAdd (F.obj L) n m ▷ F.obj L) := by
        rw [← cancel_epi (F.map (α_ (natTensorPow L n) (natTensorPow L m) L).hom),
          ← coherence_whiskerLeft_associator_inv_assoc (natTensorPowComparison F L n)
            (natTensorPowComparison F L m) (δ F (natTensorPow L m) L)]
        rw [F.map_comp]
        simp only [Category.assoc, Iso.hom_inv_id_map_assoc]
        rw [← Functor.OplaxMonoidal.δ_natural_left_assoc F (powAdd L n m) L,
          ← comp_whiskerRight, ih]
        simp only [comp_whiskerRight]
        rw [← Functor.OplaxMonoidal.associativity_assoc]
        simp only [Iso.hom_inv_id_assoc]
      exact hgoal

end Oplax

section Monoidal

variable (F : C ⥤ D) [F.Monoidal] (L : C)

/-- **The comparison of a monoidal functor on the tensor powers is invertible.** -/
instance isIso_natTensorPowComparison : ∀ n : ℕ, IsIso (natTensorPowComparison F L n)
  | 0 => inferInstanceAs (IsIso (η F))
  | n + 1 => by
      have := isIso_natTensorPowComparison n
      exact inferInstanceAs
        (IsIso (δ F (natTensorPow L n) L ≫ (natTensorPowComparison F L n ▷ F.obj L)))

/-- **The comparison `F(L ^⊗ n) ≅ (F L) ^⊗ n` of a monoidal functor on the nonnegative tensor
powers**, i.e. `Stacks.TensorPowerPullbackMul.natTensorPowComparison` read as an isomorphism. -/
noncomputable def natTensorPowComparisonIso (n : ℕ) :
    F.obj (natTensorPow L n) ≅ natTensorPow (F.obj L) n :=
  asIso (natTensorPowComparison F L n)

/-- The forward direction of `natTensorPowComparisonIso` is `natTensorPowComparison`. -/
@[simp]
theorem natTensorPowComparisonIso_hom (n : ℕ) :
    (natTensorPowComparisonIso F L n).hom = natTensorPowComparison F L n := rfl

/-- **The multiplicativity square of a monoidal functor on the tensor powers**, written with the
isomorphism `Stacks.TensorPowerPullbackMul.natTensorPowComparisonIso`. -/
theorem natTensorPowComparisonIso_powAdd (n m : ℕ) :
    F.map (powAdd L n m) ≫ (natTensorPowComparisonIso F L (n + m)).hom =
      δ F (natTensorPow L n) (natTensorPow L m) ≫
        ((natTensorPowComparisonIso F L n).hom ⊗ₘ (natTensorPowComparisonIso F L m).hom) ≫
          powAdd (F.obj L) n m :=
  natTensorPowComparison_powAdd F L n m

end Monoidal

end Functor

end Stacks.TensorPowerPullbackMul

end
