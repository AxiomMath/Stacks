module

public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic
public import Mathlib.Data.Int.Init

/-!
# Integer power systems in a monoidal category

Let `C` be a monoidal category, `Z` an object of `C` such that tensoring on the right by `Z` is
fully faithful, and `P : ℤ → C` a family of objects together with successor comparisons
`p n : P n ⊗ Z ≅ P (n + 1)` and an identification `u : P 0 ≅ 𝟙_ C`. This file builds the
multiplication isomorphisms

  `mul n m : P n ⊗ P m ≅ P (n + m)`

for arbitrary *integer* exponents, and proves that they are associative, and — given the single
non-formal input that the braiding of `P 1` with itself is the identity — commutative.

The intended instance is the family of integer tensor powers of an invertible sheaf of modules,
where the multiplication isomorphisms and their coherence are what
[Stacks, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU) asserts. Nothing here mentions
sheaves: the content is the bookkeeping of a two-sided recursion over `ℤ` together with two
"one more tensor factor" cancellation arguments, so it is stated for an arbitrary monoidal
category.

## Main definitions

* `Stacks.Monoidal.IntPower.intSequence`: the family obtained from a value at `0` by iterating a
  family of equivalences `T n ≃ T (n + 1)` in both directions.
* `Stacks.Monoidal.IntPower.mulStep`: the recursion step, `(P n ⊗ P m ≅ P (n + m))` to
  `(P n ⊗ P (m + 1) ≅ P (n + (m + 1)))`, which is an equivalence because tensoring on the right
  by `Z` is fully faithful.
* `Stacks.Monoidal.IntPower.mul` and `mulAt`: the multiplication isomorphisms, the second with
  the target exponent named by an arbitrary witness of `n + m = t`.
* `Stacks.Monoidal.IntPower.Associative`: associativity of the multiplication isomorphisms at a
  fixed third exponent.

## Main results

* `Stacks.Monoidal.IntPower.assoc_step_iff` and `comm_step_iff`: faithfulness of tensoring on the
  right by `Z` moves an associativity, respectively a commutativity, identity from one exponent
  to the next. The second uses the hexagon.
* `Stacks.Monoidal.IntPower.mulAt_zero` and `mulAt_step`: the two defining properties of the
  multiplication isomorphisms.
* `Stacks.Monoidal.IntPower.mulAt_assoc`: **the multiplication isomorphisms are associative**,
  for all three integer exponents.
* `Stacks.Monoidal.IntPower.mulAt_comm`: **the multiplication isomorphisms are commutative**,
  given left unitality and `β_ (P 1) (P 1) = 𝟙`.
* `Stacks.Monoidal.IntPower.eq_leftUnitor_of_assoc`: a comparison `𝟙_ C ⊗ X ≅ X` satisfying the
  mixed associativity identity against itself is the left unitor. This is what identifies
  `mulAt 0 n` with the left unitor, which `mulAt_comm` takes as a hypothesis.

## Implementation notes

The recursion is on the **second** exponent only, so `mul n m` is defined by `intSequence` in
`m` for each fixed `n`, with the right unitor as the value at `m = 0`. Associativity in the
third exponent then follows by a two-sided induction whose step is `assoc_step_iff`, and
commutativity reduces — again by a two-sided induction, whose step is `comm_step_iff` — to the
diagonal case `(1, 1)`, which is the braiding hypothesis.

`intSequence` is defined by `Int.inductionOn'` and its two characteristic properties are
`intSequence_zero` and `intSequence_step`. The negative half of `intSequence_step` is the only
place where transport along an equality of integers appears, and it is discharged by the two
private `cast` lemmas; everything downstream uses only the two characteristic properties.

The braiding hypothesis of `mulAt_comm` is not a formal consequence of the symmetric monoidal
axioms: an invertible object of a general symmetric monoidal category satisfies only
`β ≫ β = 𝟙`, and the odd line in super vector spaces has `β = -𝟙`.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory

namespace Stacks.Monoidal.IntPower

/-! ### Two-sided recursion over the integers -/

/-- The family of terms of an `ℤ`-indexed family of types obtained from a value at `0` by
iterating a family of equivalences `T n ≃ T (n + 1)` in both directions. -/
noncomputable def intSequence {T : ℤ → Type*}
    (e : ∀ n, T n ≃ T (n + 1)) (z : T 0) (n : ℤ) : T n :=
  n.inductionOn' 0 z (fun k _ => e k) (fun k _ x =>
    (e (k - 1)).symm (by simpa only [Int.sub_add_cancel] using x))

/-- The term of `intSequence e z` at `0` is `z`. -/
theorem intSequence_zero {T : ℤ → Type*}
    (e : ∀ n, T n ≃ T (n + 1)) (z : T 0) : intSequence e z 0 = z :=
  Int.inductionOn'_self ..

private theorem cast_dependent_value {A : Type*} {T : A → Type*} (f : ∀ a, T a)
    {a b : A} (h : a = b) : cast (congrArg T h) (f a) = f b := by
  cases h
  rfl

private theorem cast_step_inverse {T : ℤ → Type*} (e : ∀ n, T n ≃ T (n + 1))
    {a b : ℤ} (h : a = b) (x : T (b + 1)) :
    cast (congrArg T h) ((e a).symm
      (cast (congrArg T (congrArg (fun k : ℤ => k + 1) h).symm) x)) =
        (e b).symm x := by
  cases h
  rfl

/-- The equivalence `e n` sends the `n`-th term of `intSequence e z` to its `(n + 1)`-st term. -/
theorem intSequence_step {T : ℤ → Type*}
    (e : ∀ n, T n ≃ T (n + 1)) (z : T 0) (n : ℤ) :
    e n (intSequence e z n) = intSequence e z (n + 1) := by
  by_cases hn : 0 ≤ n
  · exact (Int.inductionOn'_add_one (zero := z) (succ := fun k _ => e k)
      (pred := fun k _ x => (e (k - 1)).symm
        (by simpa only [Int.sub_add_cancel] using x)) hn).symm
  · have hn' : n + 1 ≤ 0 := by omega
    have h := Int.inductionOn'_sub_one (zero := z) (succ := fun k _ => e k)
      (pred := fun k _ x => (e (k - 1)).symm
        (by simpa only [Int.sub_add_cancel] using x)) hn'
    apply (e n).eq_symm_apply.mp
    have heq : n + 1 - 1 = n := by omega
    have hh := congrArg (cast (congrArg T heq)) h
    change cast (congrArg T heq) (intSequence e z (n + 1 - 1)) =
      cast (congrArg T heq) ((e (n + 1 - 1)).symm
        (cast (congrArg T (congrArg (fun k : ℤ => k + 1) heq).symm)
          (intSequence e z (n + 1)))) at hh
    rwa [cast_dependent_value (intSequence e z) heq, cast_step_inverse e heq] at hh

/-! ### Moving an associativity or a commutativity identity across one exponent -/

/-- Two morphisms into `Y` are equal if they agree after tensoring by `Z` on the right and
composing with an isomorphism, when tensoring on the right by `Z` is faithful. -/
private theorem eq_of_whiskerRight_comp_hom_eq {D : Type u} [Category.{v} D] [MonoidalCategory D]
    {X Y T Z : D} [(tensorRight Z).Faithful] (e : Y ⊗ Z ≅ T) {x y : X ⟶ Y}
    (h : x ▷ Z ≫ e.hom = y ▷ Z ≫ e.hom) : x = y :=
  (tensorRight Z).map_injective ((cancel_mono e.hom).mp h)

section Assoc

variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
variable {A B C AB BC ABC C' BC' ABC' Z : D}
variable (c : C ⊗ Z ≅ C') (bc : BC ⊗ Z ≅ BC') (abc : ABC ⊗ Z ≅ ABC')
variable (f : A ⊗ B ⟶ AB) (g : B ⊗ C ⟶ BC) (h : AB ⊗ C ⟶ ABC)
  (i : A ⊗ BC ⟶ ABC) (g' : B ⊗ C' ⟶ BC') (h' : AB ⊗ C' ⟶ ABC')
  (i' : A ⊗ BC' ⟶ ABC')
variable (hg : g ▷ Z ≫ bc.hom = (α_ B C Z).hom ≫ B ◁ c.hom ≫ g')
  (hh : h ▷ Z ≫ abc.hom = (α_ AB C Z).hom ≫ AB ◁ c.hom ≫ h')
  (hi : i ▷ Z ≫ abc.hom = (α_ A BC Z).hom ≫ A ◁ bc.hom ≫ i')

include c bc abc hg hh hi in
/-- Associativity of a multiplication in the third slot `C` is equivalent to associativity in
the slot `C'` obtained by tensoring once more by `Z`. The three comparison identities `hg`,
`hh`, `hi` carry the pentagon across, and faithfulness of tensoring on the right by `Z` gives
the reverse implication. -/
theorem assoc_step_iff [(tensorRight Z).Faithful] :
    (f ▷ C ≫ h = (α_ A B C).hom ≫ A ◁ g ≫ i) ↔
      (f ▷ C' ≫ h' = (α_ A B C').hom ≫ A ◁ g' ≫ i') := by
  have hl : ((α_ (A ⊗ B) C Z).hom ≫ (A ⊗ B) ◁ c.hom) ≫ (f ▷ C' ≫ h') =
      (f ▷ C ≫ h) ▷ Z ≫ abc.hom := by
    simp only [comp_whiskerRight, Category.assoc]
    rw [hh, whisker_exchange_assoc f c.hom]
    monoidal
  have hr : ((α_ (A ⊗ B) C Z).hom ≫ (A ⊗ B) ◁ c.hom) ≫
      ((α_ A B C').hom ≫ A ◁ g' ≫ i') =
      ((α_ A B C).hom ≫ A ◁ g ≫ i) ▷ Z ≫ abc.hom := by
    symm
    simp only [comp_whiskerRight, Category.assoc]
    rw [hi]
    calc
      _ = (α_ (A ⊗ B) C Z).hom ≫ (α_ A B (C ⊗ Z)).hom ≫
          A ◁ ((α_ B C Z).inv ≫ g ▷ Z ≫ bc.hom) ≫ i' := by monoidal
      _ = _ := by
        rw [hg]
        simp only [Iso.inv_hom_id_assoc, whiskerLeft_comp, Category.assoc]
        monoidal
  constructor
  · intro ha
    apply (cancel_epi ((α_ (A ⊗ B) C Z).hom ≫ (A ⊗ B) ◁ c.hom)).mp
    rw [hl, hr, ha]
  · intro ha
    refine eq_of_whiskerRight_comp_hom_eq abc ?_
    rw [← hl, ← hr, ha]

end Assoc

section Comm

open BraidedCategory

variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  {A B Z AB AZ BZ T : D} [(tensorRight Z).Faithful]

/-- Commutativity of a multiplication at the pair `(A, B)` is equivalent to commutativity at
the pair `(A, B ⊗ Z)`. The hexagon moves the braiding past the comparison `t`, and faithfulness
of tensoring on the right by `Z` gives the reverse implication. -/
theorem comm_step_iff
    (a : A ⊗ B ≅ AB) (b : B ⊗ A ≅ AB)
    (c : A ⊗ Z ≅ AZ) (d : Z ⊗ A ≅ AZ) (t : B ⊗ Z ≅ BZ)
    (e : AB ⊗ Z ≅ T) (g : B ⊗ AZ ≅ T) (f : A ⊗ BZ ≅ T) (l : BZ ⊗ A ≅ T)
    (h₁ : a.hom ▷ Z ≫ e.hom = (α_ A B Z).hom ≫ A ◁ t.hom ≫ f.hom)
    (h₂ : b.hom ▷ Z ≫ e.hom = (α_ B A Z).hom ≫ B ◁ c.hom ≫ g.hom)
    (h₃ : t.hom ▷ A ≫ l.hom = (α_ B Z A).hom ≫ B ◁ d.hom ≫ g.hom)
    (hc : c.hom = (β_ A Z).hom ≫ d.hom) :
    (a.hom = (β_ A B).hom ≫ b.hom) ↔ (f.hom = (β_ A BZ).hom ≫ l.hom) := by
  have hr : ((β_ A B).hom ≫ b.hom) ▷ Z ≫ e.hom =
      ((α_ A B Z).hom ≫ A ◁ t.hom) ≫ ((β_ A BZ).hom ≫ l.hom) := by
    simp only [comp_whiskerRight, Category.assoc]
    rw [h₂, hc, whiskerLeft_comp, Category.assoc, braiding_naturality_right_assoc A t.hom,
      braiding_tensor_right_hom]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [h₃]
    simp only [Iso.inv_hom_id_assoc]
  constructor
  · intro ha
    apply (cancel_epi ((α_ A B Z).hom ≫ A ◁ t.hom)).mp
    calc
      _ = a.hom ▷ Z ≫ e.hom := by simpa only [Category.assoc] using h₁.symm
      _ = _ := by rw [ha, hr]
  · intro hf
    refine eq_of_whiskerRight_comp_hom_eq e ?_
    rw [hr, h₁, hf]
    simp only [Category.assoc]

end Comm

/-! ### The multiplication isomorphisms of an integer power system -/

section PowerMul

variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  (P : ℤ → D) (Z : D) [(tensorRight Z).Full] [(tensorRight Z).Faithful]
  (p : ∀ n, P n ⊗ Z ≅ P (n + 1)) (u : P 0 ≅ 𝟙_ D)

/-- The successor step of the recursion defining the multiplication isomorphisms: a comparison
`P n ⊗ P m ≅ P (n + m)` determines one in degree `(n, m + 1)`, because tensoring on the right
by `Z` is fully faithful. -/
noncomputable def mulStep (n m : ℤ) :
    (P n ⊗ P m ≅ P (n + m)) ≃ (P n ⊗ P (m + 1) ≅ P (n + (m + 1))) :=
  (Functor.FullyFaithful.ofFullyFaithful (tensorRight Z)).isoEquiv.trans
    (Iso.isoCongr ((α_ (P n) (P m) Z) ≪≫ whiskerLeftIso (P n) (p m))
      (p (n + m) ≪≫ eqToIso (congrArg P (Int.add_assoc n m 1))))

/-- The multiplication isomorphism `P n ⊗ P m ≅ P (n + m)`, defined by the recursion `mulStep`
on the second exponent, starting from the right unitor in degree `(n, 0)`. -/
noncomputable def mul (n m : ℤ) : P n ⊗ P m ≅ P (n + m) :=
  intSequence (mulStep P Z p n)
    (whiskerLeftIso (P n) u ≪≫ ρ_ (P n) ≪≫ eqToIso (congrArg P (Int.add_zero n).symm)) m

/-- The multiplication isomorphism, with its target exponent named by an arbitrary witness of
`n + m = t`. This is the form the associativity and commutativity inductions are run in. -/
noncomputable def mulAt (n m t : ℤ) (h : n + m = t) : P n ⊗ P m ≅ P t :=
  mul P Z p u n m ≪≫ eqToIso (congrArg P h)

/-- Tensoring the multiplication isomorphism once more by `Z` and composing with the successor
comparison gives the multiplication isomorphism one exponent further along. -/
theorem mulAt_step (n m t : ℤ) (h : n + m = t) :
    (mulAt P Z p u n m t h).hom ▷ Z ≫ (p t).hom =
      (α_ (P n) (P m) Z).hom ≫ P n ◁ (p m).hom ≫
        (mulAt P Z p u n (m + 1) (t + 1) (by omega)).hom := by
  subst t
  have he := congrArg Iso.hom (intSequence_step (mulStep P Z p n)
    (whiskerLeftIso (P n) u ≪≫ ρ_ (P n) ≪≫ eqToIso (congrArg P (Int.add_zero n).symm)) m)
  change ((mulStep P Z p n m) (mul P Z p u n m)).hom =
    (mul P Z p u n (m + 1)).hom at he
  simp only [mulStep, Equiv.trans_apply, Functor.FullyFaithful.isoEquiv_apply,
    Iso.isoCongr_apply, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.trans_inv, whiskerLeftIso_inv, eqToIso.hom,
    Category.assoc] at he
  simp only [mulAt, Iso.trans_hom, eqToIso.hom, eqToHom_refl, Category.comp_id]
  rw [← he]
  simp only [whiskerLeft_hom_inv_assoc, Iso.hom_inv_id_assoc, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id]
  rfl

/-- In degree `(n, 0)` the multiplication isomorphism is the right unitor, read through the
identification of `P 0` with the tensor unit. -/
theorem mulAt_zero (n : ℤ) :
    mulAt P Z p u n 0 n (Int.add_zero n) = whiskerLeftIso (P n) u ≪≫ ρ_ (P n) := by
  simp only [mulAt, mul, intSequence_zero]
  apply Iso.ext
  simp only [Iso.trans_hom, eqToIso.hom, Category.assoc, eqToHom_trans,
    eqToHom_refl, Category.comp_id]

/-- `mulAt_zero` at the level of the underlying morphism. -/
theorem mulAt_zero_hom (n : ℤ) :
    (mulAt P Z p u n 0 n (Int.add_zero n)).hom = P n ◁ u.hom ≫ (ρ_ (P n)).hom := by
  rw [mulAt_zero]
  simp only [Iso.trans_hom, whiskerLeftIso_hom]

/-- Associativity of the multiplication isomorphisms in the third exponent `k`. -/
def Associative (k : ℤ) : Prop :=
  ∀ (n m nm mk t : ℤ) (hnm : n + m = nm) (hmk : m + k = mk) (ht : nm + k = t),
    (mulAt P Z p u n m nm hnm).hom ▷ P k ≫ (mulAt P Z p u nm k t ht).hom =
      (α_ (P n) (P m) (P k)).hom ≫ P n ◁ (mulAt P Z p u m k mk hmk).hom ≫
        (mulAt P Z p u n mk t (by omega)).hom

/-- The multiplication isomorphisms are associative in the third exponent `k` if and only if they
are associative in the third exponent `k + 1`. -/
theorem associative_step (k : ℤ) : Associative P Z p u k ↔ Associative P Z p u (k + 1) := by
  have key (n m nm mk t : ℤ) (hnm : n + m = nm) (hmk : m + k = mk) (ht : nm + k = t) :
      ((mulAt P Z p u n m nm hnm).hom ▷ P k ≫ (mulAt P Z p u nm k t ht).hom =
        (α_ (P n) (P m) (P k)).hom ≫ P n ◁ (mulAt P Z p u m k mk hmk).hom ≫
          (mulAt P Z p u n mk t (by omega)).hom) ↔
      ((mulAt P Z p u n m nm hnm).hom ▷ P (k + 1) ≫
          (mulAt P Z p u nm (k + 1) (t + 1) (by omega)).hom =
        (α_ (P n) (P m) (P (k + 1))).hom ≫ P n ◁ (mulAt P Z p u m (k + 1) (mk + 1) (by omega)).hom ≫
          (mulAt P Z p u n (mk + 1) (t + 1) (by omega)).hom) :=
    assoc_step_iff (p k) (p mk) (p t)
      (mulAt P Z p u n m nm hnm).hom
      (mulAt P Z p u m k mk hmk).hom
      (mulAt P Z p u nm k t ht).hom
      (mulAt P Z p u n mk t (by omega)).hom
      (mulAt P Z p u m (k + 1) (mk + 1) (by omega)).hom
      (mulAt P Z p u nm (k + 1) (t + 1) (by omega)).hom
      (mulAt P Z p u n (mk + 1) (t + 1) (by omega)).hom
      (mulAt_step P Z p u m k mk hmk)
      (mulAt_step P Z p u nm k t ht)
      (mulAt_step P Z p u n mk t (by omega))
  constructor
  · intro ih n m nm mk t hnm hmk ht
    obtain rfl : mk = m + k + 1 := by omega
    obtain rfl : t = nm + k + 1 := by omega
    exact (key n m nm (m + k) (nm + k) hnm rfl rfl).mp (ih n m nm (m + k) (nm + k) hnm rfl rfl)
  · intro ih n m nm mk t hnm hmk ht
    exact (key n m nm mk t hnm hmk ht).mpr (ih n m nm (mk + 1) (t + 1) hnm (by omega) (by omega))

/-- **The multiplication isomorphisms of an integer power system are associative**, for all
three integer exponents. -/
theorem mulAt_assoc (k : ℤ) : Associative P Z p u k := by
  refine Int.inductionOn' k 0 ?_ (fun k _ hk => (associative_step P Z p u k).mp hk)
    (fun k _ hk => ?_)
  · intro n m nm mk t hnm hmk ht
    obtain rfl : mk = m := by omega
    obtain rfl : t = nm := by omega
    rw [mulAt_zero, mulAt_zero]
    simp only [Iso.trans_hom, whiskerLeftIso_hom, whiskerLeft_comp, Category.assoc]
    rw [← whisker_exchange_assoc _ u.hom]
    monoidal
  · apply (associative_step P Z p u (k - 1)).mpr
    simpa only [Int.sub_add_cancel] using hk

/-- **The multiplication isomorphisms of an integer power system are commutative**, given that
they are left-unital and that the braiding of `P 1` with itself is the identity. The braiding
hypothesis is not formal: it is the commutativity constraint in degree `(1, 1)`. -/
theorem mulAt_comm [SymmetricCategory D] [(tensorRight (P 1)).Faithful]
    (hl : ∀ n, mulAt P Z p u 0 n n (Int.zero_add n) =
      whiskerRightIso u (P n) ≪≫ λ_ (P n))
    (hb : (β_ (P 1) (P 1)) = Iso.refl _)
    (n m t : ℤ) (ht : n + m = t) :
    (mulAt P Z p u n m t ht).hom =
      (β_ (P n) (P m)).hom ≫ (mulAt P Z p u m n t (by omega)).hom := by
  let Q (n m : ℤ) : Prop := ∀ (t : ℤ) (ht : n + m = t),
    (mulAt P Z p u n m t ht).hom =
      (β_ (P n) (P m)).hom ≫ (mulAt P Z p u m n t (by omega)).hom
  have hz (n : ℤ) : Q n 0 := by
    intro t ht
    obtain rfl : t = n := by omega
    rw [mulAt_zero, hl]
    simp only [Iso.trans_hom, whiskerLeftIso_hom, whiskerRightIso_hom]
    rw [← BraidedCategory.braiding_naturality_right_assoc, braiding_leftUnitor]
  have hs (n m : ℤ) (hc : Q n 1) : Q n m ↔ Q n (m + 1) := by
    have he := comm_step_iff
      (mulAt P Z p u n m (n + m) rfl)
      (mulAt P Z p u m n (n + m) (by omega))
      (mulAt P Z p u n 1 (n + 1) rfl)
      (mulAt P Z p u 1 n (n + 1) (by omega))
      (mulAt P Z p u m 1 (m + 1) rfl)
      (mulAt P Z p u (n + m) 1 (n + m + 1) rfl)
      (mulAt P Z p u m (n + 1) (n + m + 1) (by omega))
      (mulAt P Z p u n (m + 1) (n + m + 1) (by omega))
      (mulAt P Z p u (m + 1) n (n + m + 1) (by omega))
      (mulAt_assoc P Z p u 1 n m (n + m) (m + 1) (n + m + 1) rfl rfl rfl)
      (mulAt_assoc P Z p u 1 m n (n + m) (n + 1) (n + m + 1) (by omega) rfl rfl)
      (mulAt_assoc P Z p u n m 1 (m + 1) (n + 1) (n + m + 1)
        rfl (by omega) (by omega))
      (hc (n + 1) rfl)
    constructor
    · intro h t ht
      obtain rfl : t = n + m + 1 := by omega
      exact he.mp (h (n + m) rfl)
    · intro h t ht
      obtain rfl : t = n + m := by omega
      exact he.mpr (h (n + m + 1) (by omega))
  have h11 : Q 1 1 := by
    intro _ _
    rw [hb, Iso.refl_hom, Category.id_comp]
  have ind (n : ℤ) (hc : Q n 1) (m : ℤ) : Q n m := by
    refine Int.inductionOn' m 0 (hz n) (fun k _ hk => (hs n k hc).mp hk)
      (fun k _ hk => (hs n (k - 1) hc).mpr ?_)
    simpa only [Int.sub_add_cancel] using hk
  have hn1 (n : ℤ) : Q n 1 := by
    intro t ht
    have h := ind 1 h11 n t (by omega)
    have hh := congrArg (fun f => (β_ (P n) (P 1)).hom ≫ f) h
    simpa only [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp] using hh.symm
  exact ind n (hn1 n) m t ht

end PowerMul

/-- A left-unit comparison which satisfies the mixed associativity identity against itself is
the left unitor. -/
theorem eq_leftUnitor_of_assoc {D : Type u} [Category.{v} D] [MonoidalCategory D]
    (X : D) (f : 𝟙_ D ⊗ X ≅ X)
    (h : (ρ_ (𝟙_ D)).hom ▷ X ≫ f.hom =
      (α_ (𝟙_ D) (𝟙_ D) X).hom ≫ (𝟙_ D) ◁ f.hom ≫ f.hom) : f = λ_ X := by
  apply Iso.ext
  have h' : (ρ_ (𝟙_ D)).hom ▷ X = (α_ (𝟙_ D) (𝟙_ D) X).hom ≫ (𝟙_ D) ◁ f.hom :=
    (cancel_mono f.hom).mp (by simpa only [Category.assoc] using h)
  apply (cancel_epi ((α_ (𝟙_ D) (𝟙_ D) X).hom ≫ (λ_ (𝟙_ D ⊗ X)).hom)).mp
  calc
    _ = ((α_ (𝟙_ D) (𝟙_ D) X).hom ≫ (𝟙_ D) ◁ f.hom) ≫ (λ_ X).hom := by
      simp only [Category.assoc]
      rw [leftUnitor_naturality]
    _ = (ρ_ (𝟙_ D)).hom ▷ X ≫ (λ_ X).hom := by rw [← h']
    _ = _ := by monoidal

end Stacks.Monoidal.IntPower

end
