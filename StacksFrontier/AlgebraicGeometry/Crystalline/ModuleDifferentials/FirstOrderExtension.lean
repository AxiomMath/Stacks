module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import StacksFrontier.AlgebraicGeometry.Crystalline.ExplicitDividedPower.Basic

/-!
# The first-order divided power thickening attached to a module

Let `(D, I, γ)` be a divided power ring and let `M` be a `D`-module on which the left and right
actions agree.  The trivial square-zero extension `D ⊕ M` carries a divided power structure on
the ideal `I ⊕ M`, namely the one given on `(d, m)` by `(γ_n d, γ_{n-1} d · m)`.  This is the
case `N = 0` of the second-order extension, so it is read off the explicit second-order formula.

This thickening is the universal recipient of a divided power derivation of `D`: a divided power
derivation `D → M` is exactly a section of `D ⊕ M → D` in the category of divided power rings
over the base, which is how the module of divided power differentials is recognized both for a
coproduct of thickenings and for a divided power envelope.

A ring `B` presented as `A ⊕ M` by an additive equivalence identifying its multiplication is
treated invariantly in the second half of the file, where the same divided power structure is
built as data: `Crystalline.squareZeroDpow` is the explicit operation and
`Crystalline.squareZeroDividedPowers` the structure it carries.

## Main definitions

* `Crystalline.firstOrderExtension` — the trivial square-zero extension `D ⊕ M`.
* `Crystalline.firstOrderExtensionIdeal` — its ideal `I ⊕ M`.
* `Crystalline.squareZeroDpow` — the explicit divided power operation of a square-zero
  extension, `1` in degree zero and `(γ_{k+1} a, γ_k a · m)` in degree `k + 1`.
* `Crystalline.squareZeroDividedPowers` — the divided power structure it defines.

## Main results

* `Crystalline.firstOrderExtension_dividedPowers` — the ideal `I ⊕ M` carries divided powers,
  with both coordinates of `δ_n (d, m)` as displayed, and the structure map `D → D ⊕ M` is a
  divided power morphism.
* `Crystalline.isDPMorphism_squareZero_of_graph` — a ring map into a square-zero extension whose
  module component obeys the divided power chain rule is a divided power morphism; this covers
  both the inclusion `a ↦ (a, 0)` and the graph `a ↦ (a, d a)` of a divided power derivation.
* `Crystalline.isDPMorphism_squareZero_fst` — the projection onto the first coordinate is a
  divided power morphism.
* `Crystalline.squareZero_mul_eq_zero` — the module summand is an ideal of square zero.

## Implementation notes

The divided powers are produced from the second-order formula with `N = PUnit` and the zero
bilinear map, rather than constructed again: the second-order carrier `D × (M × PUnit)` is
additively the square-zero extension, and the correction term of the second-order
multiplication vanishes because the bilinear map does.  Only the two nontrivial coordinates of
the resulting operation are recorded, since the third is in a subsingleton.

The divided power structure is asserted to exist rather than named, because the second-order
construction supplies it through the factorial criterion and the universal comparison, and no
consumer needs more than the two coordinate formulas.

In the invariant half the structure is instead named: `squareZeroDpow` is defined outright and
its axioms are proved by comparing it with the structure the second-order construction supplies,
which the degree-zero, degree-one and degree-at-least-two values determine completely.  The
degree is written `k + 1` rather than `n` with `n ≥ 1`, so the shift `γ_{n-1}` of the source
never becomes a truncated subtraction; degree zero is `1`, as a divided power structure
requires, and is not the degenerate reading of the displayed formula.

## References

* [Stacks Project, Tag 07HI](https://stacks.math.columbia.edu/tag/07HI)
* [Stacks Project, Tag 07HH](https://stacks.math.columbia.edu/tag/07HH)
-/

@[expose] public section

namespace Crystalline

universe u v

/-- The first-order thickening of a divided power ring `D` by a `D`-module `M`: the trivial
square-zero extension `D ⊕ M`. -/
public abbrev firstOrderExtension (D : DividedPowerRing.{u}) (M : Type v)
    [AddCommGroup M] [Module D M] [Module Dᵐᵒᵖ M] [IsCentralScalar D M] :=
  TrivSqZeroExt D M

/-- The distinguished ideal of the first-order thickening: the elements whose first coordinate
lies in the divided power ideal of `D`. -/
public def firstOrderExtensionIdeal (D : DividedPowerRing.{u}) (M : Type v)
    [AddCommGroup M] [Module D M] [Module Dᵐᵒᵖ M] [IsCentralScalar D M] :
    Ideal (firstOrderExtension D M) :=
  Ideal.comap (TrivSqZeroExt.fstHom D D M).toRingHom D.ideal

/-- The second-order construction with `N = PUnit` and the zero bilinear map gives divided powers
on the ideal `J` of any ring `B` presented by `e` as `A ⊕ M` with the square-zero multiplication,
with the displayed coordinate formulas in degrees at least two. -/
private theorem exists_dividedPowers_of_square_zero {A : Type u} [CommRing A] {I : Ideal A}
    (γ : DividedPowers I) {M : Type v} [AddCommGroup M] [Module A M]
    {B : Type*} [CommRing B] (e : B ≃+ A × M) (J : Ideal B) (ι : A →+* B)
    (hι : ∀ a : A, e (ι a) = (a, 0))
    (hmul : ∀ b b' : B,
      e (b * b') = ((e b).1 * (e b').1, (e b).1 • (e b').2 + (e b').1 • (e b).2))
    (hJ : ∀ b : B, b ∈ J ↔ (e b).1 ∈ I) :
    ∃ δ : DividedPowers J,
      (∀ (n : ℕ) (b : B), 2 ≤ n → b ∈ J →
        e (δ.dpow n b) = (γ.dpow n (e b).1, γ.dpow (n - 1) (e b).1 • (e b).2)) ∧
      DividedPowers.IsDPMorphism γ δ ι := by
  classical
  let _ : Algebra A B := ι.toAlgebra
  let e' : B ≃+ A × (M × PUnit.{1}) :=
    { toFun := fun b => ((e b).1, ((e b).2, PUnit.unit))
      invFun := fun x => e.symm (x.1, x.2.1)
      left_inv := fun b => by simp
      right_inv := fun x => by
        obtain ⟨a, m, p⟩ := x
        cases p
        simp
      map_add' := fun b b' => by
        simp only [map_add]
        rfl }
  obtain ⟨δ, hδ, hmor⟩ :=
    exists_dividedPowers_secondOrderExtension I γ (M := M) (N := PUnit.{1}) (q := 0) (B := B) e'
      (fun a => by
        change ((e (ι a)).1, ((e (ι a)).2, PUnit.unit)) = (a, ((0 : M), (0 : PUnit)))
        rw [hι a])
      (fun b b' => by
        refine Prod.ext ?_ (Prod.ext ?_ (Subsingleton.elim _ _))
        · change (e (b * b')).1 = (e b).1 * (e b').1
          rw [hmul b b']
        · change (e (b * b')).2 = (e b).1 • (e b').2 + (e b').1 • (e b).2
          rw [hmul b b'])
      J (fun b => (hJ b).trans (by rfl))
  refine ⟨δ, fun n b hn hb => ?_, hmor⟩
  rw [hδ n b hn hb]
  exact e.apply_symm_apply _

/-- The distinguished ideal of the first-order thickening carries divided powers, given on
`(d, m)` in degrees at least two by `(γ_n d, γ_{n-1} d · m)`, and the structure map of the
thickening is a divided power morphism. -/
public theorem firstOrderExtension_dividedPowers
    (D : DividedPowerRing.{u}) (M : Type v) [AddCommGroup M] [Module D M]
    [Module Dᵐᵒᵖ M] [IsCentralScalar D M] :
    ∃ δ : DividedPowers (firstOrderExtensionIdeal D M),
      (∀ (n : ℕ) (b : firstOrderExtension D M), 2 ≤ n →
        b ∈ firstOrderExtensionIdeal D M →
        (δ.dpow n b).fst = D.dividedPowers.dpow n b.fst ∧
          (δ.dpow n b).snd =
            D.dividedPowers.dpow (n - 1) b.fst • b.snd) ∧
      DividedPowers.IsDPMorphism D.dividedPowers δ
        (algebraMap D (firstOrderExtension D M)) := by
  let e : firstOrderExtension D M ≃+ D × M :=
    { toFun := fun x => (x.1, x.2)
      invFun := fun x => (x.1, x.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  obtain ⟨δ, hδ, hmor⟩ := exists_dividedPowers_of_square_zero D.dividedPowers e
    (firstOrderExtensionIdeal D M) (algebraMap D (firstOrderExtension D M))
    (fun a => by
      rw [TrivSqZeroExt.algebraMap_eq_inl]
      rfl)
    (fun b b' => by
      refine Prod.ext (TrivSqZeroExt.fst_mul b b') ?_
      change (b * b').snd = b.fst • b'.snd + b'.fst • b.snd
      rw [TrivSqZeroExt.snd_mul, op_smul_eq_smul])
    (fun _ => Iff.rfl)
  exact ⟨δ, fun n b hn hb => ⟨congrArg Prod.fst (hδ n b hn hb),
    congrArg Prod.snd (hδ n b hn hb)⟩, hmor⟩

/-! ### The divided powers of a square-zero extension, invariantly and as data -/

section SquareZero

universe w

variable {A : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I)
  {M : Type v} [AddCommGroup M] [Module A M]
  {B : Type w} [CommRing B] (e : B ≃+ A × M) (J : Ideal B)

open scoped Classical in
/-- **The divided power operation of a square-zero extension.**  For a ring `B` presented by `e`
as `A ⊕ M` with `M` an ideal of square zero, this is `1` in degree zero and
`(γ_{k+1} a, γ_k a · m)` in degree `k + 1` on an element `(a, m)` of the ideal, and `0` off the
ideal. -/
public noncomputable def squareZeroDpow : ℕ → B → B :=
  fun n b =>
    if _hb : b ∈ J then
      match n with
      | 0 => 1
      | k + 1 => e.symm (γ.dpow (k + 1) (e b).1, γ.dpow k (e b).1 • (e b).2)
    else 0

/-- The square-zero divided power operation vanishes off the ideal. -/
public theorem squareZeroDpow_of_notMem {n : ℕ} {b : B} (hb : b ∉ J) :
    squareZeroDpow γ e J n b = 0 := by
  classical
  simp only [squareZeroDpow, dite_eq_right hb]

/-- The square-zero divided power operation is `1` in degree zero on the ideal. -/
public theorem squareZeroDpow_zero {b : B} (hb : b ∈ J) :
    squareZeroDpow γ e J 0 b = 1 := by
  classical
  simp only [squareZeroDpow, dite_eq_left hb]

/-- **The square-zero divided power formula in positive degree.**  Writing the degree as `k + 1`
keeps the shift `γ_{n-1}` of the source literal, with no truncated subtraction. -/
public theorem squareZeroDpow_succ (k : ℕ) {b : B} (hb : b ∈ J) :
    squareZeroDpow γ e J (k + 1) b =
      e.symm (γ.dpow (k + 1) (e b).1, γ.dpow k (e b).1 • (e b).2) := by
  classical
  simp only [squareZeroDpow, dite_eq_left hb]

section Structure

variable (ι : A →+* B) (hι : ∀ a : A, e (ι a) = (a, 0))
  (hmul : ∀ b b' : B,
    e (b * b') = ((e b).1 * (e b').1, (e b).1 • (e b').2 + (e b').1 • (e b).2))
  (hJ : ∀ b : B, b ∈ J ↔ (e b).1 ∈ I)

include hι hmul hJ

/-- The explicit square-zero operation is the divided power structure produced by the
second-order construction, which pins down all of its axioms. -/
private theorem exists_squareZeroDividedPowers :
    ∃ δ : DividedPowers J, δ.dpow = squareZeroDpow γ e J ∧
      DividedPowers.IsDPMorphism γ δ ι := by
  obtain ⟨δ, hδ, hmor⟩ := exists_dividedPowers_of_square_zero γ e J ι hι hmul hJ
  refine ⟨δ, funext fun n => funext fun b => ?_, hmor⟩
  by_cases hb : b ∈ J
  · match n with
    | 0 => rw [δ.dpow_zero hb, squareZeroDpow_zero γ e J hb]
    | 1 =>
        rw [δ.dpow_one hb, squareZeroDpow_succ γ e J 0 hb,
          γ.dpow_one ((hJ b).1 hb), γ.dpow_zero ((hJ b).1 hb), one_smul]
        exact (e.symm_apply_apply b).symm
    | k + 2 =>
        rw [squareZeroDpow_succ γ e J (k + 1) hb]
        exact e.injective (by rw [hδ (k + 2) b (by omega) hb, e.apply_symm_apply]; rfl)
  · rw [δ.dpow_null hb, squareZeroDpow_of_notMem γ e J hb]

/-- **The divided powers of a square-zero extension.**  For a ring `B` presented by `e` as
`A ⊕ M` with `M` an ideal of square zero, the ideal `I ⊕ M` carries the divided power structure
whose operation is `squareZeroDpow`. -/
public noncomputable def squareZeroDividedPowers : DividedPowers J where
  dpow := squareZeroDpow γ e J
  dpow_null hb := squareZeroDpow_of_notMem γ e J hb
  dpow_zero hb := squareZeroDpow_zero γ e J hb
  dpow_one := fun {b} hb => by
    rw [squareZeroDpow_succ γ e J 0 hb, γ.dpow_one ((hJ b).1 hb),
      γ.dpow_zero ((hJ b).1 hb), one_smul]
    exact e.symm_apply_apply b
  dpow_mem hn hb := by
    obtain ⟨δ, hδ, -⟩ := exists_squareZeroDividedPowers γ e J ι hι hmul hJ
    rw [← hδ]; exact δ.dpow_mem hn hb
  dpow_add hb hb' := by
    obtain ⟨δ, hδ, -⟩ := exists_squareZeroDividedPowers γ e J ι hι hmul hJ
    rw [← hδ]; exact δ.dpow_add hb hb'
  dpow_mul hb := by
    obtain ⟨δ, hδ, -⟩ := exists_squareZeroDividedPowers γ e J ι hι hmul hJ
    rw [← hδ]; exact δ.dpow_mul hb
  mul_dpow hb := by
    obtain ⟨δ, hδ, -⟩ := exists_squareZeroDividedPowers γ e J ι hι hmul hJ
    rw [← hδ]; exact δ.mul_dpow hb
  dpow_comp hn hb := by
    obtain ⟨δ, hδ, -⟩ := exists_squareZeroDividedPowers γ e J ι hι hmul hJ
    rw [← hδ]; exact δ.dpow_comp hn hb

/-- The divided power operation of a square-zero extension is the explicit one. -/
@[simp]
public theorem squareZeroDividedPowers_dpow :
    (squareZeroDividedPowers γ e J ι hι hmul hJ).dpow = squareZeroDpow γ e J := rfl

/-- **A map into a square-zero extension whose module component obeys the divided power chain
rule is a divided power morphism.**  Both the inclusion `a ↦ (a, 0)` and the graph
`a ↦ (a, d a)` of a divided power derivation are of this form. -/
public theorem isDPMorphism_squareZero_of_graph (g : A →+* B) (dd : A → M)
    (hg : ∀ a : A, e (g a) = (a, dd a))
    (hdd : ∀ (k : ℕ), ∀ a ∈ I, dd (γ.dpow (k + 1) a) = γ.dpow k a • dd a) :
    DividedPowers.IsDPMorphism γ (squareZeroDividedPowers γ e J ι hι hmul hJ) g := by
  have hmem : ∀ a ∈ I, g a ∈ J := fun a ha => (hJ (g a)).2 (by rw [hg a]; exact ha)
  refine ⟨Ideal.map_le_iff_le_comap.mpr fun a ha => hmem a ha, ?_⟩
  intro n a ha
  match n with
  | 0 =>
      rw [show (squareZeroDividedPowers γ e J ι hι hmul hJ).dpow 0 (g a) = 1 from
        squareZeroDpow_zero γ e J (hmem a ha), γ.dpow_zero ha, map_one]
  | k + 1 =>
      rw [show (squareZeroDividedPowers γ e J ι hι hmul hJ).dpow (k + 1) (g a) =
          e.symm (γ.dpow (k + 1) (e (g a)).1, γ.dpow k (e (g a)).1 • (e (g a)).2) from
        squareZeroDpow_succ γ e J k (hmem a ha)]
      refine e.injective ?_
      rw [e.apply_symm_apply, hg (γ.dpow (k + 1) a), hg a, hdd k a ha]

/-- **The projection of a square-zero extension onto its first coordinate is a divided power
morphism.** -/
public theorem isDPMorphism_squareZero_fst (π : B →+* A) (hπ : ∀ b : B, π b = (e b).1) :
    DividedPowers.IsDPMorphism (squareZeroDividedPowers γ e J ι hι hmul hJ) γ π := by
  refine ⟨Ideal.map_le_iff_le_comap.mpr fun b hb => ?_, ?_⟩
  · rw [Ideal.mem_comap, hπ b]
    exact (hJ b).1 hb
  · intro n b hb
    have hπb : π b ∈ I := by rw [hπ b]; exact (hJ b).1 hb
    match n with
    | 0 =>
        rw [show (squareZeroDividedPowers γ e J ι hι hmul hJ).dpow 0 b = 1 from
          squareZeroDpow_zero γ e J hb, map_one, γ.dpow_zero hπb]
    | k + 1 =>
        rw [show (squareZeroDividedPowers γ e J ι hι hmul hJ).dpow (k + 1) b =
            e.symm (γ.dpow (k + 1) (e b).1, γ.dpow k (e b).1 • (e b).2) from
          squareZeroDpow_succ γ e J k hb, hπ b,
          hπ (e.symm (γ.dpow (k + 1) (e b).1, γ.dpow k (e b).1 • (e b).2)),
          e.apply_symm_apply]

omit hι hJ in
/-- **The module summand of a square-zero extension is an ideal of square zero.** -/
public theorem squareZero_mul_eq_zero {x y : B} (hx : (e x).1 = 0) (hy : (e y).1 = 0) :
    x * y = 0 := by
  refine e.injective ?_
  rw [hmul x y, hx, hy, map_zero]
  simp

end Structure

end SquareZero

end Crystalline

end
