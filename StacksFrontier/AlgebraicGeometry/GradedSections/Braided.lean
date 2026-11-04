module

public import StacksFrontier.AlgebraicGeometry.GradedSections.Monoidal

/-!
# Commutativity of the graded ring of sections

The sibling file `StacksFrontier/AlgebraicGeometry/GradedSections/Monoidal.lean` makes
`⨁_{n ≥ 0} (𝟙_ C ⟶ L ^⊗ n)` a graded ring with no appeal to monoidal coherence. This file
proves it **commutative**, which does need coherence, and identifies exactly the hypothesis
required: the self-braiding of `L` is trivial.

That hypothesis cannot be dropped. At `n = m = 1` commutativity says precisely that
`β_ L L` is the identity, and in a symmetric monoidal category an invertible object may have
self-braiding `-1`. For sheaves of modules over a sheaf of commutative rings the braiding is the
transposition of local sections, so the hypothesis holds; it is recorded as the class
`Stacks.GradedSections.HasTrivialSelfBraiding`.

## Main definitions

* `Stacks.GradedSections.HasTrivialSelfBraiding`: `β_ L L = 𝟙`.
* `Stacks.GradedSections.powCongr`: transport of a tensor power along an equality of exponents.
* `Stacks.GradedSections.powAdd`: the addition morphism
  `L ^⊗ n ⊗ L ^⊗ m ⟶ L ^⊗ (n + m)`, built by recursion on `m` from associators and the right
  unitor alone. This is the morphism underlying Stacks Tag 01CU's addition isomorphism, in the
  nonnegative range.
* `Stacks.GradedSections.powSwap`: the *structural* morphism `L ⊗ L ^⊗ m ⟶ L ^⊗ m ⊗ L` moving a
  single factor across a power, again built from associators and unitors only.

## Main results

* `Stacks.GradedSections.braiding_eq_powSwap`: **under the hypothesis, the braiding of `L` past
  a power of `L` is the structural morphism.** This is where the hypothesis is used, through the
  forward hexagon.
* `Stacks.GradedSections.braiding_comp_powAdd`: **the commutativity constraint on the addition
  morphisms** that Stacks Tag 01CU states with the formulation omitted, in the nonnegative
  range: braiding the two powers and adding is adding and reindexing.
* `Stacks.GradedSections.mulMap_eq`: the bridge between the coherence-free multiplication of the
  sibling file and `powAdd`.
* `Stacks.GradedSections.instGCommRing`, `Stacks.GradedSections.instCommRing`: **`Γ_*` is a
  commutative graded ring.**

## Implementation notes

**The shape of the induction, and why a left-successor formula is unavoidable.** `powAdd`
recurses on its second exponent, so `powAdd L n (m + 1)` unfolds and `powAdd L (n + 1) m` does
not. Every formulation of commutativity compares degree `n + m` with degree `m + n` and
therefore needs the unfolding on the left as well; that is `powAdd_succ_left`, and it is the
only place where the structural crossing morphism `powSwap` is needed. With it,
`braiding_comp_powAdd` is a single induction on the left exponent whose step is the reverse
hexagon plus one coherence identity.

**How the coherence identities are discharged.** Each is isolated as a lemma in free objects and
arbitrary morphisms and proved by the `monoidal` tactic — `coherence_rightUnitor`,
`coherence_leftUnitor`, `coherence_rightUnitor_swap`, `coherence_powSwap_step`,
`coherence_leftUnitor_mulMap` and `coherence_mulMap_step` below. None of them mentions a tensor
power, which is essential: the
`monoidal` tactic does **not** see through `Stacks.TensorPowers.natTensorPow`, so it cannot
recognise `L ^⊗ 0` as the unit nor `L ^⊗ (n + 1)` as `L ^⊗ n ⊗ L`, whatever the transparency
setting. Those identifications are made instead by `exact` and by `have` statements written in
the spelling the next step needs, both of which unify at default transparency. This is the
reason the file has the shape it has, and the reason no proof here calls `monoidal` on a goal
about powers.

**Transports.** `powCongr L h` depends only on the endpoints of `h`, equality proofs being
definitionally irrelevant, so two transports with the same source and target degree are
interchangeable by `rfl` and the degree bookkeeping never has to be matched up by hand.

**Universes.** Polymorphic in both category universes.

## References

* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU) — the commutativity and
  associativity constraints on the addition isomorphisms, there stated with the formulation
  omitted.

## What is not done

The associativity constraint of Stacks Tag 01CU is not proved for `powAdd`, and is not needed:
associativity of the section ring comes from `Stacks.GradedSections.mulMap_mul` in the sibling
file, which uses no coherence at all. Likewise `powAdd` is not shown to be an isomorphism, which
is irrelevant to everything here.

That second sentence used to add "true when `L` is invertible", and the hypothesis is
unnecessary: `powAdd` **is** an isomorphism unconditionally, since `powAdd L n 0` is a right
unitor and `powAdd L n (m + 1)` is an associator inverse followed by a whiskering of
`powAdd L n m`, all three of which are isomorphisms. It is simply not needed, so it is not
stated.

Nothing is stated for negative exponents, so the graded module of Stacks Tag 01CV is still not
constructed.
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory BraidedCategory Stacks.TensorPowers

open scoped DirectSum

namespace Stacks.GradedSections

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

section Coherence

/-- The right unitor of the monoidal unit is its left unitor. -/
theorem coherence_rightUnitor : (ρ_ (𝟙_ C)).hom = (λ_ (𝟙_ C)).hom := by monoidal

/-- The left unitor of a tensor product, read as a coherence identity. -/
theorem coherence_leftUnitor (Y Z : C) :
    (α_ (𝟙_ C) Y Z).inv ≫ ((λ_ Y).hom ▷ Z) = (λ_ (Y ⊗ Z)).hom := by monoidal

/-- The base case of `powAdd_succ_left`, in free objects. The trailing identity is there so that
the statement matches the goal on the nose, the transport in degree zero being trivial. -/
theorem coherence_rightUnitor_swap (X Y : C) :
    (ρ_ (X ⊗ Y)).hom = (α_ X Y (𝟙_ C)).hom ≫ (X ◁ ((ρ_ Y).hom ≫ (λ_ Y).inv)) ≫
      (α_ X (𝟙_ C) Y).inv ≫ ((ρ_ X).hom ▷ Y) ≫ 𝟙 (X ⊗ Y) := by monoidal

/-- The inductive step of `powAdd_succ_left`, in free objects and arbitrary morphisms. The
trailing `q` is the degree transport. -/
theorem coherence_powSwap_step {A L W V U : C} (w : L ⊗ W ⟶ W ⊗ L) (p : A ⊗ W ⟶ V)
    (q : V ⊗ L ⟶ U) :
    (α_ (A ⊗ L) W L).inv ≫ ((α_ A L W).hom ≫ (A ◁ w) ≫ (α_ A W L).inv ≫ (p ▷ L) ≫ q) ▷ L =
      (α_ A L (W ⊗ L)).hom ≫ (A ◁ ((α_ L W L).inv ≫ (w ▷ L))) ≫ (α_ A (W ⊗ L) L).inv ≫
        (((α_ A W L).inv ≫ (p ▷ L)) ▷ L) ≫ (q ▷ L) := by monoidal

/-- The base case of `mulMap_eq`, in free objects and an arbitrary morphism. -/
theorem coherence_leftUnitor_mulMap {X : C} (s : 𝟙_ C ⟶ X) :
    (λ_ (𝟙_ C)).inv ≫ (s ▷ 𝟙_ C) ≫ (ρ_ X).hom = s := by monoidal

/-- The inductive step of `mulMap_eq`, in free objects and arbitrary morphisms. -/
theorem coherence_mulMap_step {X Y Z W : C} (s : 𝟙_ C ⟶ X) (q : (X ⊗ Y) ⊗ Z ⟶ W) :
    ((λ_ Y).inv ▷ Z) ≫ ((s ▷ Y) ▷ Z) ≫ q =
      (λ_ (Y ⊗ Z)).inv ≫ (s ▷ (Y ⊗ Z)) ≫ (α_ X Y Z).inv ≫ q := by monoidal

/-- The braiding of the monoidal unit with itself is the identity. -/
theorem braiding_tensorUnit_self [BraidedCategory C] :
    (β_ (𝟙_ C) (𝟙_ C)).hom = 𝟙 (𝟙_ C ⊗ 𝟙_ C) := by
  rw [braiding_tensorUnit_left, ← coherence_rightUnitor, Iso.hom_inv_id]

/-- Pulling a section through the left unitor. -/
theorem comp_leftUnitor_inv {X : C} (t : 𝟙_ C ⟶ X) :
    t ≫ (λ_ X).inv = (λ_ (𝟙_ C)).inv ≫ (𝟙_ C ◁ t) := by
  rw [Iso.comp_inv_eq, Category.assoc, leftUnitor_naturality, Iso.inv_hom_id_assoc]

end Coherence

section Add

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

/-- Transport of a tensor power along an equality of exponents. It depends only on the two
exponents, equality proofs being definitionally irrelevant. -/
abbrev powCongr (L : C) {n m : ℕ} (h : n = m) : natTensorPow L n ⟶ natTensorPow L m :=
  eqToHom (congrArg (natTensorPow L) h)

/-- Transport along `n = n` is the identity. -/
@[simp]
theorem powCongr_rfl (L : C) {n : ℕ} (h : n = n) : powCongr L h = 𝟙 _ := rfl

/-- Whiskering the transport along `n = m` on the right by `L` is the transport along
`n + 1 = m + 1`. -/
theorem powCongr_whiskerRight (L : C) {n m : ℕ} (h : n = m) (h' : n + 1 = m + 1) :
    powCongr L h ▷ L = powCongr L h' := eqToHom_whiskerRight _ L

/-- Transports along `n = m` and `m = k` compose to the transport along `n = k`. -/
theorem powCongr_trans (L : C) {n m k : ℕ} (h : n = m) (h' : m = k) (h'' : n = k) :
    powCongr L h ≫ powCongr L h' = powCongr L h'' := eqToHom_trans _ _

/-- **The addition morphism on tensor powers**, `L ^⊗ n ⊗ L ^⊗ m ⟶ L ^⊗ (n + m)`, by recursion
on `m`. Only the right unitor and the associator are used; in particular no braiding and no
transport appear, because `natTensorPow L (n + m)` recurses on `m` just as this does. -/
def powAdd (L : C) : (n m : ℕ) → (natTensorPow L n ⊗ natTensorPow L m ⟶ natTensorPow L (n + m))
  | _, 0 => (ρ_ _).hom
  | n, m + 1 => (α_ _ _ _).inv ≫ (powAdd L n m ▷ L)

/-- In degree `m = 0`, the addition morphism is the right unitor. -/
theorem powAdd_zero (L : C) (n : ℕ) : powAdd L n 0 = (ρ_ (natTensorPow L n)).hom := rfl

/-- The addition morphism in degree `m + 1` is the inverse associator followed by the addition
morphism in degree `m` whiskered on the right by `L`. -/
theorem powAdd_succ (L : C) (n m : ℕ) :
    powAdd L n (m + 1) =
      (α_ (natTensorPow L n) (natTensorPow L m) L).inv ≫ (powAdd L n m ▷ L) := rfl

/-- **The structural crossing morphism** `L ⊗ L ^⊗ m ⟶ L ^⊗ m ⊗ L`, by recursion on `m` from
associators and unitors only. Under `HasTrivialSelfBraiding` it is the braiding
(`braiding_eq_powSwap`), which is what makes the commutativity constraint provable. -/
def powSwap (L : C) : (m : ℕ) → (L ⊗ natTensorPow L m ⟶ natTensorPow L m ⊗ L)
  | 0 => (ρ_ L).hom ≫ (λ_ L).inv
  | m + 1 => (α_ _ _ _).inv ≫ (powSwap L m ▷ L)

/-- In degree `0`, the structural crossing morphism is `(ρ_ L).hom ≫ (λ_ L).inv`. -/
theorem powSwap_zero (L : C) : powSwap L 0 = (ρ_ L).hom ≫ (λ_ L).inv := rfl

/-- The structural crossing morphism in degree `m + 1` is the inverse associator followed by the
structural crossing morphism in degree `m` whiskered on the right by `L`. -/
theorem powSwap_succ (L : C) (m : ℕ) :
    powSwap L (m + 1) = (α_ L (natTensorPow L m) L).inv ≫ (powSwap L m ▷ L) := rfl

/-- Adding on the left in degree `0` is the left unitor. -/
theorem powAdd_zero_left (L : C) (m : ℕ) :
    powAdd L 0 m ≫ powCongr L (Nat.zero_add m) = (λ_ (natTensorPow L m)).hom := by
  induction m with
  | zero =>
    rw [powAdd_zero, powCongr_rfl, Category.comp_id]
    exact coherence_rightUnitor
  | succ m ih =>
    rw [powAdd_succ, ← powCongr_whiskerRight L (Nat.zero_add m), Category.assoc,
      ← comp_whiskerRight, ih]
    exact coherence_leftUnitor _ _

/-- **The left-successor formula for the addition morphism.** Adding `n + 1` on the left is
adding `n` on the left after moving the extra factor of `L` across, by the structural crossing
morphism. This is the identity that `powAdd`'s recursion on the right exponent does not give,
and the reason `powSwap` exists. -/
theorem powAdd_succ_left (L : C) (n : ℕ) : ∀ m : ℕ,
    powAdd L (n + 1) m =
      (α_ (natTensorPow L n) L (natTensorPow L m)).hom ≫ (natTensorPow L n ◁ powSwap L m) ≫
        (α_ (natTensorPow L n) (natTensorPow L m) L).inv ≫ (powAdd L n m ▷ L) ≫
          powCongr L (Nat.succ_add n m).symm
  | 0 => by
      rw [powAdd_zero, powAdd_zero, powSwap_zero, powCongr_rfl]
      exact coherence_rightUnitor_swap _ _
  | m + 1 => by
      rw [powAdd_succ L (n + 1) m, powAdd_succ_left L n m, powSwap_succ, powAdd_succ L n m,
        ← powCongr_whiskerRight L (Nat.succ_add n m).symm]
      exact coherence_powSwap_step (powSwap L m) (powAdd L n m)
        (powCongr L (Nat.succ_add n m).symm)

end Add

section Braided

variable [BraidedCategory C]

/-- An object whose self-braiding is trivial. This holds for an invertible sheaf of modules over
a sheaf of commutative rings, the braiding being the transposition of local sections, and it is
exactly what commutativity of the section ring needs: at degrees `1` and `1` commutativity *is*
this statement. -/
class HasTrivialSelfBraiding (L : C) : Prop where
  /-- The self-braiding is the identity. -/
  braiding_self : (β_ L L).hom = 𝟙 (L ⊗ L)

section

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

variable (L : C)

/-- **Under a trivial self-braiding, the braiding of `L` past a power of `L` is structural.**
This is the one use of the hypothesis, through the forward hexagon. -/
theorem braiding_eq_powSwap [HasTrivialSelfBraiding L] : ∀ m : ℕ,
    (β_ L (natTensorPow L m)).hom = powSwap L m
  | 0 => by
      rw [powSwap_zero, Iso.eq_comp_inv]
      exact braiding_leftUnitor L
  | m + 1 => by
      have h := hexagon_forward L (natTensorPow L m) L
      rw [HasTrivialSelfBraiding.braiding_self, whiskerLeft_id, Category.comp_id,
        ← Category.assoc] at h
      have h' : (α_ L (natTensorPow L m) L).hom ≫ (β_ L (natTensorPow L (m + 1))).hom =
          (β_ L (natTensorPow L m)).hom ▷ L := (cancel_mono _).mp h
      rw [powSwap_succ, ← braiding_eq_powSwap m, ← h', Iso.inv_hom_id_assoc]

/-- **The commutativity constraint on the addition morphisms**, which Stacks Tag 01CU states
with the formulation omitted: braiding the two powers and then adding is adding and then
reindexing. The induction is on the left exponent; the step is the reverse hexagon together with
`powAdd_succ_left` and `braiding_eq_powSwap`. -/
theorem braiding_comp_powAdd [HasTrivialSelfBraiding L] : ∀ (n m : ℕ),
    (β_ (natTensorPow L n) (natTensorPow L m)).hom ≫ powAdd L m n =
      powAdd L n m ≫ powCongr L (Nat.add_comm n m)
  | 0, m => by
      rw [powAdd_zero]
      exact (braiding_rightUnitor (natTensorPow L m)).trans (powAdd_zero_left L m).symm
  | n + 1, m => by
      have hex : (β_ (natTensorPow L (n + 1)) (natTensorPow L m)).hom ≫
            (α_ (natTensorPow L m) (natTensorPow L n) L).inv =
          (α_ (natTensorPow L n) L (natTensorPow L m)).hom ≫
            ((natTensorPow L n ◁ (β_ L (natTensorPow L m)).hom) ≫
              (α_ (natTensorPow L n) (natTensorPow L m) L).inv ≫
                ((β_ (natTensorPow L n) (natTensorPow L m)).hom ▷ L)) :=
        (Iso.inv_comp_eq _).mp (hexagon_reverse (natTensorPow L n) L (natTensorPow L m))
      have key : ((β_ (natTensorPow L n) (natTensorPow L m)).hom ▷ L) ≫ (powAdd L m n ▷ L) =
          (powAdd L n m ▷ L) ≫ powCongr L (Nat.succ_add n m).symm ≫
            powCongr L (Nat.add_comm (n + 1) m) := by
        rw [← comp_whiskerRight, braiding_comp_powAdd n m, comp_whiskerRight,
          powCongr_whiskerRight L (Nat.add_comm n m) (congrArg (· + 1) (Nat.add_comm n m)),
          powCongr_trans]
      rw [powAdd_succ L m n, ← Category.assoc, hex, powAdd_succ_left L n m,
        braiding_eq_powSwap L m]
      simp only [Category.assoc]
      rw [key]

end

end Braided

section CommRing

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

variable {L : C}

/-- **The bridge to `powAdd`.** Multiplication by a section, which the sibling file defines
without any coherence, is the section tensored in and then added. -/
theorem mulMap_eq {n : ℕ} (s : powSections L n) : ∀ m : ℕ,
    mulMap s m = (λ_ (natTensorPow L m)).inv ≫ (s ▷ natTensorPow L m) ≫ powAdd L n m
  | 0 => by
      rw [mulMap_zero, powAdd_zero]
      exact (coherence_leftUnitor_mulMap s).symm
  | m + 1 => by
      rw [mulMap_succ, mulMap_eq s m, powAdd_succ, comp_whiskerRight, comp_whiskerRight]
      exact coherence_mulMap_step s (powAdd L n m ▷ L)

/-- The product of two sections, written through `powAdd`. -/
theorem mul_eq {n m : ℕ} (s : powSections L n) (t : powSections L m) :
    mul s t = (λ_ (𝟙_ C)).inv ≫ (s ⊗ₘ t) ≫ powAdd L n m := by
  rw [mul_def, mulMap_eq s m, ← Category.assoc, comp_leftUnitor_inv t, tensorHom_def' s t]
  simp only [Category.assoc]

variable [BraidedCategory C] [HasTrivialSelfBraiding L]

/-- **The product of sections is commutative**, up to the transport that the grading forces. -/
theorem mul_comm' {n m : ℕ} (s : powSections L n) (t : powSections L m) :
    mul s t ≫ powCongr L (Nat.add_comm n m) = mul t s := by
  have hts : (t ⊗ₘ s) = (s ⊗ₘ t) ≫ (β_ (natTensorPow L n) (natTensorPow L m)).hom := by
    rw [braiding_naturality s t, braiding_tensorUnit_self, Category.id_comp]
  rw [mul_eq s t, mul_eq t s, hts]
  simp only [Category.assoc]
  rw [braiding_comp_powAdd L n m]

variable [Preadditive C] [(tensorRight L).Additive]

/-- **The section ring of `L` is commutative.** -/
noncomputable instance instGCommRing : DirectSum.GCommRing (powSections L) where
  mul_comm a b := by
    obtain ⟨n, s⟩ := a; obtain ⟨m, t⟩ := b
    change (⟨n + m, mul s t⟩ : GradedMonoid (powSections L)) = ⟨m + n, mul t s⟩
    refine (mk_eq (Nat.add_comm n m) _).trans ?_
    congr 1
    exact mul_comm' s t

/-- `Γ_*(X, L)` is a commutative ring. -/
noncomputable instance instCommRing : CommRing (sectionRing L) := inferInstance

end CommRing

end Stacks.GradedSections
