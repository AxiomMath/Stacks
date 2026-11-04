module

public import StacksFrontier.AlgebraicGeometry.TensorPowerCoherence.IntPowerSystem

/-!
# Comparing two integer power systems

`StacksFrontier/AlgebraicGeometry/TensorPowerCoherence/IntPowerSystem.lean` builds, for a family
`P : ℤ → C` of objects of a monoidal category equipped with successor comparisons
`p n : P n ⊗ Z ≅ P (n + 1)` and an identification `u : P 0 ≅ 𝟙_ C`, the multiplication
isomorphisms `P n ⊗ P m ≅ P (n + m)` in every integer bidegree, and proves them associative and
commutative. It says nothing about *two* such families.

This file supplies the comparison. Given two integer power systems and a degreewise family of
morphisms `e n : P n ⟶ P' n` which commutes with the successor comparisons, `e` intertwines the
two multiplications in every integer bidegree — both signs at once.

## Main results

* `Stacks.Monoidal.IntPower.comparison_step_iff`: faithfulness of tensoring on the right by `Z`
  moves a comparison identity from one exponent to the next, in both directions. This is the
  analogue of `Stacks.Monoidal.IntPower.assoc_step_iff` for a comparison rather than an
  associativity, and it is an *equivalence*, which is what makes the negative half available.
* `Stacks.Monoidal.IntPower.mul_comparison`: **a degreewise comparison commuting with the
  successor comparisons intertwines the multiplications**, in every integer bidegree. The two
  multiplications are taken as given families satisfying the degree-zero and successor laws
  rather than as `mulAt`, so the statement also applies to a multiplication that is only known
  to satisfy those laws.
* `Stacks.Monoidal.IntPower.mulAt_comparison`: the same for `Stacks.Monoidal.IntPower.mulAt`
  itself, the two laws being `mulAt_zero_hom` and `mulAt_step`.
* `Stacks.Monoidal.IntPower.eq_mulAt_of_zero_of_step`: **the multiplication isomorphisms are the
  unique family satisfying the two laws.** This is `mul_comparison` for one system compared with
  itself along the identity, and it is what identifies a multiplication supplied by other means
  — for instance one chosen by `Classical.choice` from a coherence datum — with `mulAt`.

## Implementation notes

The induction is on the second exponent only, at a fixed first exponent, exactly as the
construction of the multiplication isomorphisms is; the first exponent is a parameter and needs
no induction. So a single two-sided induction over `ℤ`, whose step is `comparison_step_iff` read
in each direction, gives all four sign combinations.

`comparison_step_iff` is proved by evaluating both sides of the degree-`(n, m + 1)` identity
after precomposition with the isomorphism
`(P n ⊗ P m) ⊗ Z ≅ P n ⊗ P (m + 1)`, which turns each of them into a morphism factoring through
`⊗ ζ` and the successor comparison of the target system. Both evaluations are unconditional, so
the forward implication is cancellation of an epimorphism and the backward one is cancellation of
the monomorphism `τ'.hom`, of `_ ◁ ζ.hom`, and finally faithfulness of tensoring by `Z`.

**Only the comparison of the generators has to be invertible.** `ζ : Z ≅ Z'` is an isomorphism
for exactly the cancellation of `_ ◁ ζ.hom` above; the degreewise comparisons `e n` are an
arbitrary family of morphisms, since nothing in either computation inverts one. So
`mul_comparison` applies to a degreewise comparison which is not known to be invertible — a
monoidal natural transformation rather than an isomorphism. `mulAt_comparison` is stated for a
family of isomorphisms only because that is what its consumers hold.

The nonnegative-exponent analogue of this file is
`Stacks.Monoidal.PowerSystem.compare_mul` in
`StacksFrontier/AlgebraicGeometry/GradedSectionRing/PowerSystemComparison.lean`, whose index-free
auxiliaries `compare_mul_aux_zero` and `compare_mul_aux_succ` carry the same two computations for
`ℕ`. They are not reused here: `compare_mul_aux_succ` is an implication rather than an
equivalence, so it cannot run the negative half, and it is stated in the spelling in which the
`ℕ`-indexed multiplication is *defined* rather than in the successor law an `ℤ`-indexed one
satisfies. Importing that file would also put the sheaf-theoretic import closure of
`StacksFrontier/AlgebraicGeometry/GradedSectionRing/Basic.lean` underneath this one, which — like
`IntPowerSystem.lean` — mentions no sheaves.

The intended consumer is property (1) of [Stacks, Tag 01O7], which needs the multiplicativity of
a comparison of two constructions of the integer tensor powers of an invertible sheaf of modules;
the comparison of the two multiplications there is a uniqueness question, which is what
`eq_mulAt_of_zero_of_step` answers.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory

namespace Stacks.Monoidal.IntPower

/-! ### Moving a comparison identity across one exponent -/

/-- A comparison identity between two multiplications in the bidegree `(A, B)` is equivalent to
the one in the bidegree `(A, B₁)` obtained by tensoring the second slot once more by `Z`.

The data are two successor comparisons `σ`, `τ` for the source system, two more `σ'`, `τ'` for
the target system, a comparison `ζ : Z ≅ Z'` of the two generators, the two multiplications `f`,
`f₁` of the source system and `f'`, `f₁'` of the target, and the degreewise comparison morphisms
`a`, `b`, `b₁`, `c`, `c₁`. The hypotheses `hb` and `hc` are the two instances of the successor
square satisfied by the comparison, and `hf`, `hf'` the successor law of each multiplication.

Only the naturality of the structural isomorphisms is used in the forward direction;
faithfulness of tensoring on the right by `Z` gives the reverse implication, which is what makes
the induction over `ℤ` two-sided. -/
theorem comparison_step_iff {D : Type u} [Category.{v} D] [MonoidalCategory D]
    {A B AB B₁ AB₁ A' B' AB' B₁' AB₁' Z Z' : D} [(tensorRight Z).Faithful]
    (σ : B ⊗ Z ≅ B₁) (τ : AB ⊗ Z ≅ AB₁) (σ' : B' ⊗ Z' ≅ B₁') (τ' : AB' ⊗ Z' ≅ AB₁')
    (ζ : Z ≅ Z')
    (f : A ⊗ B ⟶ AB) (f₁ : A ⊗ B₁ ⟶ AB₁) (f' : A' ⊗ B' ⟶ AB') (f₁' : A' ⊗ B₁' ⟶ AB₁')
    (a : A ⟶ A') (b : B ⟶ B') (b₁ : B₁ ⟶ B₁') (c : AB ⟶ AB') (c₁ : AB₁ ⟶ AB₁')
    (hb : (b ⊗ₘ ζ.hom) ≫ σ'.hom = σ.hom ≫ b₁)
    (hc : (c ⊗ₘ ζ.hom) ≫ τ'.hom = τ.hom ≫ c₁)
    (hf : f ▷ Z ≫ τ.hom = (α_ A B Z).hom ≫ A ◁ σ.hom ≫ f₁)
    (hf' : f' ▷ Z' ≫ τ'.hom = (α_ A' B' Z').hom ≫ A' ◁ σ'.hom ≫ f₁') :
    ((a ⊗ₘ b) ≫ f' = f ≫ c) ↔ ((a ⊗ₘ b₁) ≫ f₁' = f₁ ≫ c₁) := by
  have hL : ((α_ A B Z).hom ≫ A ◁ σ.hom) ≫ ((a ⊗ₘ b₁) ≫ f₁') =
      (((a ⊗ₘ b) ≫ f') ⊗ₘ ζ.hom) ≫ τ'.hom := by
    calc ((α_ A B Z).hom ≫ A ◁ σ.hom) ≫ ((a ⊗ₘ b₁) ≫ f₁')
        = (α_ A B Z).hom ≫ (a ⊗ₘ (σ.hom ≫ b₁)) ≫ f₁' := by
          simp only [Category.assoc, whiskerLeft_comp_tensorHom_assoc]
      _ = (α_ A B Z).hom ≫ (a ⊗ₘ (b ⊗ₘ ζ.hom)) ≫ A' ◁ σ'.hom ≫ f₁' := by
          rw [← hb, tensorHom_comp_whiskerLeft_assoc]
      _ = ((a ⊗ₘ b) ⊗ₘ ζ.hom) ≫ (α_ A' B' Z').hom ≫ A' ◁ σ'.hom ≫ f₁' := by
          rw [← associator_naturality_assoc]
      _ = ((a ⊗ₘ b) ⊗ₘ ζ.hom) ≫ f' ▷ Z' ≫ τ'.hom := by rw [← hf']
      _ = (((a ⊗ₘ b) ≫ f') ⊗ₘ ζ.hom) ≫ τ'.hom := by
          rw [tensorHom_comp_whiskerRight_assoc]
  have hR : ((α_ A B Z).hom ≫ A ◁ σ.hom) ≫ (f₁ ≫ c₁) =
      ((f ≫ c) ⊗ₘ ζ.hom) ≫ τ'.hom := by
    calc ((α_ A B Z).hom ≫ A ◁ σ.hom) ≫ (f₁ ≫ c₁)
        = ((α_ A B Z).hom ≫ A ◁ σ.hom ≫ f₁) ≫ c₁ := by simp only [Category.assoc]
      _ = (f ▷ Z ≫ τ.hom) ≫ c₁ := by rw [hf]
      _ = f ▷ Z ≫ (c ⊗ₘ ζ.hom) ≫ τ'.hom := by rw [Category.assoc, ← hc]
      _ = ((f ≫ c) ⊗ₘ ζ.hom) ≫ τ'.hom := by rw [whiskerRight_comp_tensorHom_assoc]
  refine ⟨fun ha => (cancel_epi ((α_ A B Z).hom ≫ A ◁ σ.hom)).mp (by rw [hL, hR, ha]),
    fun ha => ?_⟩
  have key : (((a ⊗ₘ b) ≫ f') ⊗ₘ ζ.hom) ≫ τ'.hom = ((f ≫ c) ⊗ₘ ζ.hom) ≫ τ'.hom := by
    rw [← hL, ← hR, ha]
  have hZ : ((a ⊗ₘ b) ≫ f') ▷ Z = (f ≫ c) ▷ Z := by
    simpa only [tensorHom_comp_whiskerLeft, Iso.hom_inv_id, tensorHom_id] using
      congrArg (· ≫ AB' ◁ ζ.inv) ((cancel_mono τ'.hom).mp key)
  exact (tensorRight Z).map_injective hZ

/-! ### The successor law from associativity -/

/-- **The successor law of a multiplication family is its associativity in the third exponent
`1`**, when the generator is identified with the first power by `v` and the successor comparison
is multiplication by it.

This is the form in which the concrete instances supply the hypothesis `hMs` of
`Stacks.Monoidal.IntPower.mul_comparison`: a coherence datum for the tensor powers of an
invertible sheaf of modules carries an associativity constraint and a normalization identifying
multiplication by the first power with the successor comparison, but no successor law for the
multiplication as such. Only the bidegree `(·, 1)` instance of associativity is used. -/
theorem step_of_assoc {D : Type u} [Category.{v} D] [MonoidalCategory D]
    (P : ℤ → D) (Z : D) (v : Z ≅ P 1) (p : ∀ n, P n ⊗ Z ≅ P (n + 1))
    (M : ∀ n m t : ℤ, n + m = t → (P n ⊗ P m ≅ P t))
    (hp : ∀ n : ℤ, (p n).hom = P n ◁ v.hom ≫ (M n 1 (n + 1) rfl).hom)
    (hassoc : ∀ (n m t : ℤ) (h : n + m = t),
      (M n m t h).hom ▷ P 1 ≫ (M t 1 (t + 1) rfl).hom =
        (α_ (P n) (P m) (P 1)).hom ≫ P n ◁ (M m 1 (m + 1) rfl).hom ≫
          (M n (m + 1) (t + 1) (by omega)).hom)
    (n m t : ℤ) (h : n + m = t) :
    (M n m t h).hom ▷ Z ≫ (p t).hom =
      (α_ (P n) (P m) Z).hom ≫ P n ◁ (p m).hom ≫
        (M n (m + 1) (t + 1) (by omega)).hom := by
  rw [hp, hp, ← whisker_exchange_assoc, hassoc n m t h, associator_naturality_right_assoc,
    whiskerLeft_comp, Category.assoc]

/-! ### The comparison of the multiplication isomorphisms -/

section Comparison

variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  (P P' : ℤ → D) (Z Z' : D) [(tensorRight Z).Faithful]
  (p : ∀ n, P n ⊗ Z ≅ P (n + 1)) (p' : ∀ n, P' n ⊗ Z' ≅ P' (n + 1))
  (u : P 0 ≅ 𝟙_ D) (u' : P' 0 ≅ 𝟙_ D)

/-- **A degreewise comparison of two integer power systems which commutes with the successor
comparisons intertwines their multiplications**, in every integer bidegree.

The comparison `e` is an arbitrary family of morphisms `P n ⟶ P' n`: neither of the two
computations inverts one, so it need not be a family of isomorphisms. Only the comparison `ζ` of
the two generators has to be invertible.

The two multiplications are given as families `M`, `M'` of isomorphisms indexed by a witness of
`n + m = t`, subject to the degree-zero law `hM0`, `hM'0` and the successor law `hMs`, `hM's` —
the two properties `Stacks.Monoidal.IntPower.mulAt_zero_hom` and
`Stacks.Monoidal.IntPower.mulAt_step` of `Stacks.Monoidal.IntPower.mulAt`. Stating them as
hypotheses rather than using `mulAt` is what lets the theorem be applied to a multiplication
obtained by other means; see `Stacks.Monoidal.IntPower.eq_mulAt_of_zero_of_step`.

Only the source system's generator `Z` is required to have fully faithful right-tensoring, and
only faithfully: the induction cancels one factor of `Z` at a time on the source side. -/
theorem mul_comparison
    (M : ∀ n m t : ℤ, n + m = t → (P n ⊗ P m ≅ P t))
    (M' : ∀ n m t : ℤ, n + m = t → (P' n ⊗ P' m ≅ P' t))
    (hM0 : ∀ n : ℤ, (M n 0 n (Int.add_zero n)).hom = P n ◁ u.hom ≫ (ρ_ (P n)).hom)
    (hM'0 : ∀ n : ℤ, (M' n 0 n (Int.add_zero n)).hom = P' n ◁ u'.hom ≫ (ρ_ (P' n)).hom)
    (hMs : ∀ (n m t : ℤ) (h : n + m = t),
      (M n m t h).hom ▷ Z ≫ (p t).hom =
        (α_ (P n) (P m) Z).hom ≫ P n ◁ (p m).hom ≫
          (M n (m + 1) (t + 1) (by omega)).hom)
    (hM's : ∀ (n m t : ℤ) (h : n + m = t),
      (M' n m t h).hom ▷ Z' ≫ (p' t).hom =
        (α_ (P' n) (P' m) Z').hom ≫ P' n ◁ (p' m).hom ≫
          (M' n (m + 1) (t + 1) (by omega)).hom)
    (e : ∀ n, P n ⟶ P' n) (ζ : Z ≅ Z')
    (he : ∀ n : ℤ, (e n ⊗ₘ ζ.hom) ≫ (p' n).hom = (p n).hom ≫ e (n + 1))
    (hu : e 0 ≫ u'.hom = u.hom)
    (n m t : ℤ) (h : n + m = t) :
    (e n ⊗ₘ e m) ≫ (M' n m t h).hom = (M n m t h).hom ≫ e t := by
  let Q (m : ℤ) : Prop := ∀ (t : ℤ) (h : n + m = t),
    (e n ⊗ₘ e m) ≫ (M' n m t h).hom = (M n m t h).hom ≫ e t
  have hzero : Q 0 := by
    intro t h
    obtain rfl : t = n := by omega
    have h0 : e 0 = u.hom ≫ u'.inv := by
      rw [← hu, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [hM0, hM'0, h0, tensorHom_def, Category.assoc, ← whiskerLeft_comp_assoc,
      Category.assoc, Iso.inv_hom_id, Category.comp_id, ← whisker_exchange_assoc,
      rightUnitor_naturality, Category.assoc]
  have hstep (k : ℤ) : Q k ↔ Q (k + 1) := by
    have hiff := comparison_step_iff (p k) (p (n + k)) (p' k) (p' (n + k)) ζ
      (M n k (n + k) rfl).hom (M n (k + 1) (n + k + 1) (by omega)).hom
      (M' n k (n + k) rfl).hom (M' n (k + 1) (n + k + 1) (by omega)).hom
      (e n) (e k) (e (k + 1)) (e (n + k)) (e (n + k + 1))
      (he k) (he (n + k)) (hMs n k (n + k) rfl) (hM's n k (n + k) rfl)
    constructor
    · intro hk t h
      obtain rfl : t = n + k + 1 := by omega
      exact hiff.mp (hk (n + k) rfl)
    · intro hk t h
      obtain rfl : t = n + k := by omega
      exact hiff.mpr (hk (n + k + 1) (by omega))
  have hall : ∀ m : ℤ, Q m := fun m =>
    Int.inductionOn' m 0 hzero (fun k _ hk => (hstep k).mp hk) (fun k _ hk =>
      (hstep (k - 1)).mpr (by simpa only [Int.sub_add_cancel] using hk))
  exact hall m t h

variable [(tensorRight Z).Full] [(tensorRight Z').Full] [(tensorRight Z').Faithful]

/-- **The multiplication isomorphisms of two integer power systems are intertwined by any
degreewise comparison which commutes with the successor comparisons**, in every integer
bidegree. This is `Stacks.Monoidal.IntPower.mul_comparison` at the two systems' own
multiplications, whose two laws are `Stacks.Monoidal.IntPower.mulAt_zero_hom` and
`Stacks.Monoidal.IntPower.mulAt_step`. -/
theorem mulAt_comparison (e : ∀ n, P n ≅ P' n) (ζ : Z ≅ Z')
    (he : ∀ n : ℤ, ((e n).hom ⊗ₘ ζ.hom) ≫ (p' n).hom = (p n).hom ≫ (e (n + 1)).hom)
    (hu : (e 0).hom ≫ u'.hom = u.hom)
    (n m t : ℤ) (h : n + m = t) :
    ((e n).hom ⊗ₘ (e m).hom) ≫ (mulAt P' Z' p' u' n m t h).hom =
      (mulAt P Z p u n m t h).hom ≫ (e t).hom :=
  mul_comparison P P' Z Z' p p' u u' (mulAt P Z p u) (mulAt P' Z' p' u')
    (mulAt_zero_hom P Z p u) (mulAt_zero_hom P' Z' p' u')
    (mulAt_step P Z p u) (mulAt_step P' Z' p' u') (fun n => (e n).hom) ζ he hu n m t h

/-- **The multiplication isomorphisms are the unique family satisfying the degree-zero law and
the successor law.** A family `M` of isomorphisms `P n ⊗ P m ≅ P t` which is the right unitor in
the degree `(n, 0)` and satisfies the successor law against the successor comparisons is
`Stacks.Monoidal.IntPower.mulAt`.

This is the comparison theorem for one system against itself along the identity. It is what
identifies a multiplication supplied by other means — a datum chosen by `Classical.choice`, say,
from a structure asserting the coherence laws — with the one built by the recursion, which is a
genuine uniqueness statement and not a rewrite. -/
theorem eq_mulAt_of_zero_of_step
    (M : ∀ n m t : ℤ, n + m = t → (P n ⊗ P m ≅ P t))
    (hM0 : ∀ n : ℤ, (M n 0 n (Int.add_zero n)).hom = P n ◁ u.hom ≫ (ρ_ (P n)).hom)
    (hMs : ∀ (n m t : ℤ) (h : n + m = t),
      (M n m t h).hom ▷ Z ≫ (p t).hom =
        (α_ (P n) (P m) Z).hom ≫ P n ◁ (p m).hom ≫
          (M n (m + 1) (t + 1) (by omega)).hom)
    (n m t : ℤ) (h : n + m = t) : M n m t h = mulAt P Z p u n m t h := by
  refine Iso.ext ?_
  simpa only [Iso.refl_hom, id_tensorHom_id, Category.id_comp, Category.comp_id] using
    (mul_comparison P P Z Z p p u u M (mulAt P Z p u) hM0 (mulAt_zero_hom P Z p u)
      hMs (mulAt_step P Z p u) (fun n => 𝟙 (P n)) (Iso.refl Z)
      (fun n => by simp) (by simp) n m t h).symm

end Comparison

end Stacks.Monoidal.IntPower

end
