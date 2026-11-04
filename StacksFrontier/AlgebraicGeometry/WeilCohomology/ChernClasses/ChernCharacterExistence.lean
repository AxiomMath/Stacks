module

public import Mathlib.RingTheory.PowerSeries.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCharacterKGroup
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.ModuleFacts
public import StacksFrontier.AlgebraicGeometry.CurveDegreeTensor.Cohomological
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.CentralChernEval
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.ChernCharacter
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.ChernCharacterUniqueness
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.InvertibleTensor
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.KZeroRule
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.PullbackTensor
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.RankSetup

/-!
# The Chern character exists, and Stacks Tag 0FI9

In the standing situation of Stacks Section 45.12, with `A(X)` a `𝐐`-algebra for every object `X`
of `𝒞`, there is a unique rule assigning to every `X` a Chern character

`ch^A : K₀(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X)`

which (1) is a ring map, (2) satisfies `f^* ∘ ch^A = ch^A ∘ f^*`, and (3) sends an invertible
module `ℒ` to `exp(c₁^A(ℒ))`. The uniqueness half is
`Stacks.WeilCohomology.eq_of_isChernCharacterOnLocallyFree`; this file constructs the rule and
proves the unique-existence statement.

## Main definitions

* `Stacks.WeilCohomology.chernCharacterOfModule`: the Chern character of a single module,
  `ch^A(ℰ) = r^A(ℰ) + ∑_{i ≥ 1} (1/i!) P_i(c_1^A(ℰ), …, c_i^A(ℰ))`, as a power series over
  `A(X)`, with `P_i` the power-sum polynomials `AlgebraicGeometry.powerSumPolynomial` and `r^A` the
  rank class.

## Main results

* `Stacks.WeilCohomology.exists_isChernCharacter`: a rule with properties (1), (2) and (3) exists
  on all of `K₀(Vect(X))`, with no restriction on the rank.
* `Stacks.WeilCohomology.existsUnique_isChernCharacter`: there is exactly one rule with properties
  (1), (2) and (3), for a `ChernSetup` together with a total Chern class and a rank class.
* `Stacks.WeilCohomology.RationalChernSituation.existsUnique_isChernCharacter`: the same in the
  standing situation of Section 45.12 read with `𝐐`-coefficients, where the total Chern class is
  `Stacks.WeilCohomology.ChernSituation.isTotalChernClass_totalChernClass`.
* `Stacks.WeilCohomology.existsUnique_isChernCharacter_of_source`: the same with the conditions of
  Section 45.12 as hypotheses on a `SourceChernSetup`.

## Implementation notes

The statements over a bare `ChernSetup` assume the total Chern classes on all of `K₀(Vect(X))`,
as `Stacks.WeilCohomology.IsTotalChernClassOnLocallyFree`, and take as the hypothesis `hq` that
`algebraMap ℚ (A X) q` lies in `A^0(X)`. The rank class is
`Stacks.WeilCohomology.SourceChernSetup.rankClass`.

`∏_{i ≥ 0} A^i(X)` is carried as `PowerSeries (𝔄.A X)` for the construction and read back as the
family of components of `Stacks.WeilCohomology.IsChernCharacterOnLocallyFree`.

The universal polynomials `P_i` are integral polynomials in commuting variables, and `A(X)` is
not commutative, so they are evaluated in `Subring.center (𝔄.A X)`, where the Chern classes of
the class of a module lie.

## References

* [Stacks Project, Tag 0FI9](https://stacks.math.columbia.edu/tag/0FI9)
* [Stacks Project, Tag 0FI4](https://stacks.math.columbia.edu/tag/0FI4)
* [Stacks Project, Tag 0FI5](https://stacks.math.columbia.edu/tag/0FI5)
* [Stacks Project, Tag 0FI7](https://stacks.math.columbia.edu/tag/0FI7)
* [Stacks Project, Tag 0F9B](https://stacks.math.columbia.edu/tag/0F9B)
* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
* [Stacks Project, Tag 0FEM](https://stacks.math.columbia.edu/tag/0FEM)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v v₁ w

namespace Stacks.WeilCohomology

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}

/-! ### Two pieces of arithmetic -/

/-- Pullback commutes with the structure maps of `𝐐`. -/
private theorem pull_algebraMap (𝔄 : SourceChernSetup.{u, v, v₁, w} C S)
    [∀ X : C, Algebra ℚ (𝔄.A X)] {X Y : C} (f : X ⟶ Y) (q : ℚ) :
    𝔄.pull f (algebraMap ℚ (𝔄.A Y) q) = algebraMap ℚ (𝔄.A X) q :=
  congrFun (congrArg DFunLike.coe
    (Subsingleton.elim ((𝔄.pull f).comp (algebraMap ℚ (𝔄.A Y))) (algebraMap ℚ (𝔄.A X)))) q

/-- `(1/n!) · C(n, a) = (1/a!) · (1/b!)` when `a + b = n`. -/
theorem algebraMap_factorial_choose {A : Type*} [Ring A] [Algebra ℚ A] {n a b : ℕ}
    (h : a + b = n) :
    algebraMap ℚ A ((n.factorial : ℚ)⁻¹) * (n.choose a : A) =
      algebraMap ℚ A ((a.factorial : ℚ)⁻¹) * algebraMap ℚ A ((b.factorial : ℚ)⁻¹) := by
  subst h
  rw [show ((a + b).choose a : A) = algebraMap ℚ A (((a + b).choose a : ℚ)) by
      rw [map_natCast], ← map_mul, ← map_mul]
  congr 1
  have hfac : ((a + b).choose a : ℚ) * (a.factorial : ℚ) * (b.factorial : ℚ) =
      ((a + b).factorial : ℚ) := by
    rw [Nat.choose_symm_add]
    exact_mod_cast congrArg (Nat.cast : ℕ → ℚ) (Nat.add_choose_mul_factorial_mul_factorial a b)
  have ha : (a.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr a.factorial_ne_zero
  have hb : (b.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr b.factorial_ne_zero
  have hn : (((a + b).factorial : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (a + b).factorial_ne_zero
  field_simp
  linear_combination hfac

/-- For two finite families of central elements, `(1/n!) ∑_{i, j} (x_i + y_j)^n` is the
degree-`n` coefficient of the product of `∑_i exp(x_i)` and `∑_j exp(y_j)`. -/
theorem exp_sum_tensor {A : Type*} [Ring A] [Algebra ℚ A] {ι κ : Type*} [Fintype ι]
    [Fintype κ] (x : ι → Subring.center A) (y : κ → Subring.center A) (n : ℕ) :
    algebraMap ℚ A ((n.factorial : ℚ)⁻¹) *
        ∑ ij : ι × κ, ((x ij.1 : A) + (y ij.2 : A)) ^ n =
      ∑ q ∈ Finset.HasAntidiagonal.antidiagonal n,
        (algebraMap ℚ A ((q.1.factorial : ℚ)⁻¹) * ∑ i, (x i : A) ^ q.1) *
          (algebraMap ℚ A ((q.2.factorial : ℚ)⁻¹) * ∑ j, (y j : A) ^ q.2) := by
  have hcoe : ∑ ij : ι × κ, ((x ij.1 : A) + (y ij.2 : A)) ^ n =
      ∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, ((n.choose q.1 : A)) *
        ((∑ i, (x i : A) ^ q.1) * (∑ j, (y j : A) ^ q.2)) := by
    simpa [powerSumOfRoots] using
      congrArg (fun z : Subring.center A => (z : A)) (powerSumOfRoots_tensorRoots x y n)
  rw [hcoe, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [← mul_assoc, algebraMap_factorial_choose (Finset.HasAntidiagonal.mem_antidiagonal.mp hq)]
  simp only [mul_assoc]
  rw [← mul_assoc (algebraMap ℚ A ((q.2.factorial : ℚ)⁻¹)),
    Algebra.commutes ((q.2.factorial : ℚ)⁻¹) (∑ i, (x i : A) ^ q.1), mul_assoc]

/-! ### The first Chern class as a central element -/

/-- The first Chern class `c₁^A(ℒ)` of an invertible module, as a central element of `A(X)`. -/
def centralFirstChernClass (𝔄 : SourceChernSetup.{u, v, v₁, w} C S) (X : C)
    (L : (S.obj X).picardGroup) : Subring.center (𝔄.A X) :=
  ⟨𝔄.c₁ X L, Subring.mem_center_iff.mpr fun b => (𝔄.c₁_central X L b).symm⟩

/-- The underlying element of `centralFirstChernClass 𝔄 X L` is the first Chern class
`c₁^A(L)`. -/
@[simp] theorem coe_centralFirstChernClass (𝔄 : SourceChernSetup.{u, v, v₁, w} C S) (X : C)
    (L : (S.obj X).picardGroup) :
    (centralFirstChernClass 𝔄 X L : 𝔄.A X) = 𝔄.c₁ X L := rfl

section

variable {𝔄 : SourceChernSetup.{u, v, v₁, w} C S} [∀ X : C, Algebra ℚ (𝔄.A X)]
  {c : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔄.A X}

/-! ### The Chern classes of a sum of classes of invertible modules -/

omit [∀ X : C, Algebra ℚ (𝔄.A X)] in
/-- The total Chern classes of a sum of classes of invertible modules are the elementary
symmetric functions of their first Chern classes. -/
private theorem chernClass_sum_esymm
    (hc : IsTotalChernClassOnLocallyFree 𝔄.toChernSetup c) (P : C) {ι : Type*}
    (L : ι → (S.obj P).Modules)
    (hL : ∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj P).presheaf
      (S.obj P).ringCatSheaf.2 (L j))
    (x : ι → Subring.center (𝔄.A P))
    (hx : ∀ j, (x j : 𝔄.A P) = 𝔄.c₁ P (picardClassOf (S.obj P) (L j) (hL j)))
    (s : Finset ι) : ∀ n : ℕ,
    c P (∑ j ∈ s, VectorBundleKZero.classOf (S.obj P) (L j)) n =
      ((s.val.map x).esymm n : Subring.center (𝔄.A P)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro n
      rw [Finset.sum_empty, hc.map_zero]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · rw [ite_eq_right (by omega : ¬ n = 0), Finset.empty_val, Multiset.map_zero,
          Multiset.esymm_of_card_lt (by simpa using hn)]
        simp
  | insert a s ha ih =>
      intro n
      have hval : ((insert a s).val.map x) = x a ::ₘ (s.val.map x) := by
        rw [Finset.insert_val_of_notMem ha, Multiset.map_cons]
      have hexp : c P (∑ j ∈ insert a s, VectorBundleKZero.classOf (S.obj P) (L j)) n =
          ∑ k ∈ Finset.range (n + 1),
            (if k = 0 then (1 : 𝔄.A P) else if k = 1 then (x a : 𝔄.A P) else 0) *
              (((s.val.map x).esymm (n - k) : Subring.center (𝔄.A P)) : 𝔄.A P) := by
        rw [Finset.sum_insert ha, hc.map_add,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hc.invertible P (L a) (hL a) k, ih (n - k), hx a]
      rw [hexp, hval]
      cases n with
      | zero => simp
      | succ m =>
          have hzero : ∀ k ∈ Finset.range m,
              (if k + 1 + 1 = 0 then (1 : 𝔄.A P)
                else if k + 1 + 1 = 1 then (x a : 𝔄.A P) else 0) *
                (((s.val.map x).esymm (m + 1 - (k + 1 + 1)) :
                  Subring.center (𝔄.A P)) : 𝔄.A P) = 0 := by
            intro k _
            simp
          rw [esymm_cons, Finset.sum_range_succ' _ (m + 1), Finset.sum_range_succ' _ m,
            Finset.sum_congr rfl hzero, Finset.sum_const_zero]
          push_cast
          simp
          abel

/-! ### The Chern classes of a module class are central -/

omit [∀ X : C, Algebra ℚ (𝔄.A X)] in
/-- The Chern classes of the class of a module of constant rank are central in `A(X)`. -/
private theorem chernClass_classOf_mem_center_constantRank
    (hc : IsTotalChernClassOnLocallyFree 𝔄.toChernSetup c) (Y : C)
    (M : (S.obj Y).Modules) (r : ℕ)
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r) (n : ℕ) :
    c Y (VectorBundleKZero.classOf (S.obj Y) M) n ∈ Subring.center (𝔄.A Y) := by
  rw [Subring.mem_center_iff]
  intro b
  obtain ⟨P, p, -, hinj, hfil⟩ :=
    𝔄.exists_injective_hasInvertibleFiltration Y Unit (fun _ => M) (fun _ => r) fun _ => hM
  obtain ⟨-, L, hL, hsum⟩ := (hfil ()).exists_classOf_eq_sum
  refine hinj ?_
  rw [map_mul, map_mul, hc.map_pull p M hM.isFiniteLocallyFree n, hsum,
    chernClass_sum_esymm hc P L hL
      (fun j => centralFirstChernClass 𝔄 P (picardClassOf (S.obj P) (L j) (hL j)))
      (fun j => rfl) Finset.univ n]
  exact (Subring.mem_center_iff.mp (Subtype.property _)) _

omit [∀ X : C, Algebra ℚ (𝔄.A X)] in
/-- The Chern classes of the class of a module are central in `A(X)`. -/
theorem chernClass_classOf_mem_center (hc : IsTotalChernClassOnLocallyFree 𝔄.toChernSetup c) (X : C)
    (M : (S.obj X).Modules) (n : ℕ) :
    c X (VectorBundleKZero.classOf (S.obj X) M) n ∈ Subring.center (𝔄.A X) := by
  by_cases hM : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} M
  · rw [Subring.mem_center_iff]
    intro b
    obtain ⟨ι, -, P, p, r, -, hr, hinj⟩ := 𝔄.exists_clopenRankPieces X M
      ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry M).mp hM)
    refine hinj (funext fun i => ?_)
    dsimp only
    rw [map_mul, map_mul, hc.map_pull (p i) M
      ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry M).mp hM) n]
    exact (Subring.mem_center_iff.mp
      (chernClass_classOf_mem_center_constantRank hc (P i) _ (r i) (hr i) n)) _
  · rw [VectorBundleKZero.classOf_eq_zero_of_not_isFiniteLocallyFree M hM, hc.map_zero]
    split_ifs
    · exact (Subring.center (𝔄.A X)).one_mem
    · exact (Subring.center (𝔄.A X)).zero_mem

/-- The Chern classes of the class of a module, as central elements of `A(X)`. -/
def centralChernClass
    (hc : IsTotalChernClassOnLocallyFree 𝔄.toChernSetup c) (X : C) (M : (S.obj X).Modules)
    (i : ℕ+) :
    Subring.center (𝔄.A X) :=
  ⟨c X (VectorBundleKZero.classOf (S.obj X) M) (i : ℕ),
    chernClass_classOf_mem_center hc X M (i : ℕ)⟩

omit [∀ X : C, Algebra ℚ (𝔄.A X)] in
/-- The underlying element of `centralChernClass hc X M i` is the `i`-th Chern class of the class
of `M`. -/
@[simp] theorem coe_centralChernClass (hc : IsTotalChernClassOnLocallyFree 𝔄.toChernSetup c) (X : C)
    (M : (S.obj X).Modules) (i : ℕ+) :
    (centralChernClass hc X M i : 𝔄.A X) =
      c X (VectorBundleKZero.classOf (S.obj X) M) (i : ℕ) := rfl

/-! ### The Chern character of a module -/

/-- The Chern character of a finite locally free module,
`ch^A(ℰ) = r^A(ℰ) + ∑_{i ≥ 1} (1/i!) P_i(c_1^A(ℰ), …, c_i^A(ℰ))`,
as an element of `PowerSeries (A(X))`: the degree-zero coefficient is the rank class, and in
positive degrees the universal power-sum polynomial of Tag 0F9B is evaluated at the Chern
classes, in the centre of `A(X)`. -/
def chernCharacterOfModule (hc : IsTotalChernClassOnLocallyFree 𝔄.toChernSetup c) (X : C)
    (M : (S.obj X).Modules) : PowerSeries (𝔄.A X) :=
  PowerSeries.mk fun n =>
    if n = 0 then 𝔄.rankClass X M
    else algebraMap ℚ (𝔄.A X) ((n.factorial : ℚ)⁻¹) *
      ((chernClassEval (centralChernClass hc X M) (powerSumPolynomial n)) : 𝔄.A X)

/-- The Chern character of a module depends only on its class in `K₀(Vect(X))` and its rank
class. -/
theorem chernCharacterOfModule_congr (hc : IsTotalChernClassOnLocallyFree 𝔄.toChernSetup c) (X : C)
    (M N : (S.obj X).Modules)
    (hclass : VectorBundleKZero.classOf (S.obj X) M = VectorBundleKZero.classOf (S.obj X) N)
    (hrank : 𝔄.rankClass X M = 𝔄.rankClass X N) :
    chernCharacterOfModule hc X M = chernCharacterOfModule hc X N := by
  have hcc : centralChernClass hc X M = centralChernClass hc X N := by
    funext i
    exact Subtype.ext (by rw [coe_centralChernClass, coe_centralChernClass, hclass])
  rw [chernCharacterOfModule, chernCharacterOfModule, hcc, hrank]

/-- If the class of `ℳ` in `K₀(Vect(X))` is the sum of the classes of a finite family of
invertible modules `ℒ_j` and its rank class is the number of them, then its Chern character is
`∑_j exp(c₁^A(ℒ_j))`, coefficientwise. -/
theorem coeff_chernCharacterOfModule_of_sum_invertible
    (hc : IsTotalChernClassOnLocallyFree 𝔄.toChernSetup c) (X : C)
    (M : (S.obj X).Modules) {ι : Type*} [Fintype ι]
    (L : ι → (S.obj X).Modules)
    (hL : ∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 (L j))
    (hsum : VectorBundleKZero.classOf (S.obj X) M =
      ∑ j, VectorBundleKZero.classOf (S.obj X) (L j))
    (hrank : 𝔄.rankClass X M = (Fintype.card ι : 𝔄.A X)) (n : ℕ) :
    PowerSeries.coeff n (chernCharacterOfModule hc X M) =
      algebraMap ℚ (𝔄.A X) ((n.factorial : ℚ)⁻¹) *
        ∑ j, 𝔄.c₁ X (picardClassOf (S.obj X) (L j) (hL j)) ^ n := by
  classical
  have hroots : centralChernClass hc X M =
      fun i : ℕ+ => esymmOfRoots
        (fun j => centralFirstChernClass 𝔄 X (picardClassOf (S.obj X) (L j) (hL j))) (i : ℕ) := by
    funext i
    refine Subtype.ext ?_
    rw [coe_centralChernClass, hsum,
      chernClass_sum_esymm hc X L hL
        (fun j => centralFirstChernClass 𝔄 X (picardClassOf (S.obj X) (L j) (hL j)))
        (fun j => rfl) Finset.univ (i : ℕ)]
    rfl
  rw [chernCharacterOfModule, PowerSeries.coeff_mk]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hrank]
  · rw [ite_eq_right (by omega : ¬ n = 0), hroots, chernClassEval_powerSumPolynomial _ n hn]
    congr 1
    rw [powerSumOfRoots]
    push_cast
    rfl

/-- The Chern character of a module is compatible with pullback, coefficientwise. -/
theorem pull_coeff_chernCharacterOfModule (hc : IsTotalChernClassOnLocallyFree 𝔄.toChernSetup c)
    {X Y : C} (f : X ⟶ Y) (E : (S.obj Y).Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E) (n : ℕ) :
    𝔄.pull f (PowerSeries.coeff n (chernCharacterOfModule hc Y E)) =
      PowerSeries.coeff n (chernCharacterOfModule hc X
        ((Scheme.Modules.pullback (S.map f)).obj E)) := by
  rw [chernCharacterOfModule, chernCharacterOfModule, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using 𝔄.pull_rankClass f E hE
  · simp only [ite_eq_right (by omega : ¬ n = 0)]
    rw [map_mul, pull_algebraMap,
      map_chernClassEval (𝔄.pull f) (centralChernClass hc Y E)
        (centralChernClass hc X ((Scheme.Modules.pullback (S.map f)).obj E))
        (fun i => hc.map_pull f E hE (i : ℕ))]

/-- The `n`-th coefficient of the Chern character of a module lies in `A^n(X)`. -/
theorem coeff_chernCharacterOfModule_mem_grade
    (hq : ∀ (X : C) (q : ℚ), algebraMap ℚ (𝔄.A X) q ∈ 𝔄.grade X 0)
    (hc : IsTotalChernClassOnLocallyFree 𝔄.toChernSetup c) (X : C) (M : (S.obj X).Modules) (n : ℕ) :
    PowerSeries.coeff n (chernCharacterOfModule hc X M) ∈ 𝔄.grade X n := by
  rw [chernCharacterOfModule, PowerSeries.coeff_mk]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using 𝔄.rankClass_mem_grade X M
  · rw [ite_eq_right (by omega : ¬ n = 0)]
    have h1 : ((chernClassEval (centralChernClass hc X M)
        (powerSumPolynomial n)) : 𝔄.A X) ∈ 𝔄.grade X n :=
      chernClassEval_mem_of_isWeightedHomogeneous (𝔄.grade X) (𝔄.one_mem X)
        (𝔄.mul_mem X) _
        (fun i => hc.mem_grade X _ (i : ℕ)) n _
        (isWeightedHomogeneous_powerSumPolynomial n)
    simpa using 𝔄.mul_mem X 0 n (hq X _) h1

/-! ### The three properties of the Chern character of a module -/

/-- The Chern character of a module that is not finite locally free is zero. -/
theorem chernCharacterOfModule_eq_zero
    (hc : IsTotalChernClassOnLocallyFree 𝔄.toChernSetup c) (X : C)
    (M : (S.obj X).Modules)
    (h : ¬ Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} M) :
    chernCharacterOfModule hc X M = 0 := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_chernCharacterOfModule_of_sum_invertible hc X M
    (ι := Fin 0) (fun j => j.elim0) (fun j => j.elim0)
    (by simp [VectorBundleKZero.classOf_eq_zero_of_not_isFiniteLocallyFree M h])
    (by simp [𝔄.rankClass_eq_zero X M h]) n]
  simp

/-- The Chern character of an invertible module `ℒ` is `exp(c₁^A(ℒ))`. -/
theorem chernCharacterOfModule_invertible
    (hc : IsTotalChernClassOnLocallyFree 𝔄.toChernSetup c) (X : C)
    (L : (S.obj X).Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 L) (n : ℕ) :
    PowerSeries.coeff n (chernCharacterOfModule hc X L) =
      algebraMap ℚ (𝔄.A X) ((n.factorial : ℚ)⁻¹) *
        𝔄.c₁ X (picardClassOf (S.obj X) L hL) ^ n := by
  have := hL
  rw [coeff_chernCharacterOfModule_of_sum_invertible hc X L
    (ι := Fin 1) (fun _ => L) (fun _ => hL) (by simp)
    (by simp [𝔄.rankClass_eq X L 1 inferInstance]) n]
  simp

/-- The Chern character of the structure sheaf is `1`. -/
theorem chernCharacterOfModule_unit (hc : IsTotalChernClassOnLocallyFree 𝔄.toChernSetup c) (X : C) :
    chernCharacterOfModule hc X (SheafOfModules.unit (S.obj X).ringCatSheaf) = 1 := by
  have hinv : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 (SheafOfModules.unit (S.obj X).ringCatSheaf) :=
    AlgebraicGeometry.SheafOfModules.isInvertible_unit (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2
  refine PowerSeries.ext fun n => ?_
  rw [chernCharacterOfModule_invertible hc X _ hinv, picardClassOf_unit, map_zero,
    PowerSeries.coeff_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [ite_eq_right (by omega : ¬ n = 0), zero_pow (by omega), mul_zero]

/-! ### Additivity along a short exact sequence -/

/-- A module of constant rank is finite locally free, in the sense used to build the
Grothendieck ring. -/
theorem stacksIsFiniteLocallyFree_of_rank {Z : Scheme.{u}} (M : Z.Modules) (r : ℕ)
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r) :
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} M :=
  (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry M).mpr
    h.isFiniteLocallyFree

/-- Pulling two modules of constant ranks back to a flat cover on which `A` is injective splits
both into sums of classes of invertible modules. -/
private theorem exists_pull_sum_invertible_pair (𝔄 : SourceChernSetup.{u, v, v₁, w} C S) (Y : C)
    (M N : (S.obj Y).Modules) (r₁ r₂ : ℕ)
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r₁)
    (hN : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N r₂) :
    ∃ (P : C) (p : P ⟶ Y), Flat (S.map p) ∧ Function.Injective (𝔄.pull p) ∧
      ∃ (L₁ : Fin r₁ → (S.obj P).Modules) (L₂ : Fin r₂ → (S.obj P).Modules)
        (_ : ∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj P).presheaf
          (S.obj P).ringCatSheaf.2 (L₁ j))
        (_ : ∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj P).presheaf
          (S.obj P).ringCatSheaf.2 (L₂ j)),
        VectorBundleKZero.classOf (S.obj P) ((Scheme.Modules.pullback (S.map p)).obj M) =
          ∑ j, VectorBundleKZero.classOf (S.obj P) (L₁ j) ∧
        VectorBundleKZero.classOf (S.obj P) ((Scheme.Modules.pullback (S.map p)).obj N) =
          ∑ j, VectorBundleKZero.classOf (S.obj P) (L₂ j) := by
  have hfam : ∀ i : Fin 2, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (![M, N] i) (![r₁, r₂] i) := by
    intro i
    fin_cases i
    · simpa using hM
    · simpa using hN
  obtain ⟨P, p, hpflat, hinj, hfil⟩ :=
    𝔄.exists_injective_hasInvertibleFiltration Y (Fin 2) ![M, N] ![r₁, r₂] hfam
  obtain ⟨-, L₁, hL₁, hsum₁⟩ := (show HasInvertibleFiltration (S.obj P)
      ((Scheme.Modules.pullback (S.map p)).obj M) r₁ by simpa using hfil 0).exists_classOf_eq_sum
  obtain ⟨-, L₂, hL₂, hsum₂⟩ := (show HasInvertibleFiltration (S.obj P)
      ((Scheme.Modules.pullback (S.map p)).obj N) r₂ by simpa using hfil 1).exists_classOf_eq_sum
  exact ⟨P, p, hpflat, hinj, L₁, L₂, hL₁, hL₂, hsum₁, hsum₂⟩

/-- The `n`-th coefficient of the Chern character of a constant-rank module, pulled back to `P`,
where its class is a sum of classes of invertible modules, is the `n`-th power sum of their
first Chern classes. -/
private theorem pull_coeff_chernCharacterOfModule_of_sum_invertible
    (hc : IsTotalChernClassOnLocallyFree 𝔄.toChernSetup c) {P Y : C} (p : P ⟶ Y)
    (E : (S.obj Y).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r)
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = r) (L : ι → (S.obj P).Modules)
    (hL : ∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj P).presheaf
      (S.obj P).ringCatSheaf.2 (L j))
    (hsum : VectorBundleKZero.classOf (S.obj P) ((Scheme.Modules.pullback (S.map p)).obj E) =
      ∑ j, VectorBundleKZero.classOf (S.obj P) (L j)) (n : ℕ) :
    𝔄.pull p (PowerSeries.coeff n (chernCharacterOfModule hc Y E)) =
      algebraMap ℚ (𝔄.A P) ((n.factorial : ℚ)⁻¹) *
        ∑ j, 𝔄.c₁ P (picardClassOf (S.obj P) (L j) (hL j)) ^ n := by
  have := hE
  rw [pull_coeff_chernCharacterOfModule hc p E hE.isFiniteLocallyFree n,
    coeff_chernCharacterOfModule_of_sum_invertible hc P _ L hL hsum
      (by simp [𝔄.rankClass_eq P _ r
        (AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (S.map p) E r), hι]) n]

/-- The Chern character is additive along a short exact sequence whose outer terms have
constant ranks. -/
private theorem chernCharacterOfModule_add_constantRank
    (hc : IsTotalChernClassOnLocallyFree 𝔄.toChernSetup c) (Y : C)
    {E F G : (S.obj Y).Modules}
    (f : E ⟶ F) (g : F ⟶ G) (w : f ≫ g = 0)
    (hS : (ShortComplex.mk f g w).ShortExact) (r₁ r₂ : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r₁)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F (r₁ + r₂))
    (hG : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} G r₂) :
    chernCharacterOfModule hc Y F =
      chernCharacterOfModule hc Y E + chernCharacterOfModule hc Y G := by
  classical
  obtain ⟨P, p, hpflat, hinj, L₁, L₂, hL₁, hL₂, hsum₁, hsum₂⟩ :=
    exists_pull_sum_invertible_pair 𝔄 Y E G r₁ r₂ hE hG
  have : Flat (S.map p) := hpflat
  have hLsum : ∀ j : Fin r₁ ⊕ Fin r₂, AlgebraicGeometry.SheafOfModules.IsInvertible
      (S.obj P).presheaf (S.obj P).ringCatSheaf.2 (Sum.elim L₁ L₂ j) := by
    rintro (i | i)
    · exact hL₁ i
    · exact hL₂ i
  have := hE
  have := hF
  have := hG
  have hrkE := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (S.map p) E r₁
  have hrkF := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (S.map p) F (r₁ + r₂)
  have hrkG := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (S.map p) G r₂
  have hT := shortExact_map_pullback (S.map p) (ShortComplex.mk f g w) hS
  have : Mono ((Scheme.Modules.pullback (S.map p)).map f) := hT.mono_f
  have : Epi ((Scheme.Modules.pullback (S.map p)).map g) := hT.epi_g
  have hw : (Scheme.Modules.pullback (S.map p)).map f ≫
      (Scheme.Modules.pullback (S.map p)).map g = 0 :=
    ((ShortComplex.mk f g w).map (Scheme.Modules.pullback (S.map p))).zero
  have hclassP : VectorBundleKZero.classOf (S.obj P)
        ((Scheme.Modules.pullback (S.map p)).obj F) =
      ∑ j : Fin r₁ ⊕ Fin r₂, VectorBundleKZero.classOf (S.obj P) (Sum.elim L₁ L₂ j) := by
    rw [VectorBundleKZero.classOf_shortExact _ _ hw
      (stacksIsFiniteLocallyFree_of_rank _ _ hrkE) (stacksIsFiniteLocallyFree_of_rank _ _ hrkF)
      (stacksIsFiniteLocallyFree_of_rank _ _ hrkG) hT.exact, hsum₁, hsum₂,
      Fintype.sum_sum_type]
    rfl
  refine PowerSeries.ext fun n => hinj ?_
  rw [map_add, map_add,
    pull_coeff_chernCharacterOfModule_of_sum_invertible hc p F _ hF (by simp) _ hLsum hclassP n,
    pull_coeff_chernCharacterOfModule_of_sum_invertible hc p E _ hE (by simp) _ hL₁ hsum₁ n,
    pull_coeff_chernCharacterOfModule_of_sum_invertible hc p G _ hG (by simp) _ hL₂ hsum₂ n,
    Fintype.sum_sum_type, mul_add]
  rfl

/-- The Chern character is additive along a short exact sequence of finite locally free
modules. -/
theorem chernCharacterOfModule_add_of_shortExact
    (hc : IsTotalChernClassOnLocallyFree 𝔄.toChernSetup c)
    (X : C) {E F G : (S.obj X).Modules} (f : E ⟶ F) (g : F ⟶ G) (w : f ≫ g = 0)
    (hE : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} E)
    (hG : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} G)
    (hmono : Mono f) (hepi : Epi g) (hex : (ShortComplex.mk f g w).Exact) :
    chernCharacterOfModule hc X F =
      chernCharacterOfModule hc X E + chernCharacterOfModule hc X G := by
  classical
  have hS : (ShortComplex.mk f g w).ShortExact := ShortComplex.ShortExact.mk' hex hmono hepi
  have hE' := (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry E).mp hE
  have hG' := (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry G).mp hG
  obtain ⟨ι, -, P, p, rE, rG, hflat, hrE, hrG, hinj⟩ := 𝔄.exists_clopenRankPieces_pair X E G hE' hG'
  have hF' := Stacks.Chow.GenuineChern.isFiniteLocallyFree_of_shortExact _ hS hE' hG'
  refine PowerSeries.ext fun n => hinj (funext fun i => ?_)
  dsimp only
  have : Flat (S.map (p i)) := hflat i
  have hT := shortExact_map_pullback (S.map (p i)) (ShortComplex.mk f g w) hS
  have hw : (Scheme.Modules.pullback (S.map (p i))).map f ≫
      (Scheme.Modules.pullback (S.map (p i))).map g = 0 :=
    ((ShortComplex.mk f g w).map (Scheme.Modules.pullback (S.map (p i)))).zero
  have hrkF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (S.map (p i))).obj F) (rE i + rG i) :=
    Stacks.Chow.GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact _ hT (rE i) (rG i)
      (hrE i) (hrG i)
  rw [map_add, map_add,
    pull_coeff_chernCharacterOfModule hc (p i) F hF' n,
    pull_coeff_chernCharacterOfModule hc (p i) E hE' n,
    pull_coeff_chernCharacterOfModule hc (p i) G hG' n,
    chernCharacterOfModule_add_constantRank hc (P i)
      ((Scheme.Modules.pullback (S.map (p i))).map f)
      ((Scheme.Modules.pullback (S.map (p i))).map g) hw hT
      (rE i) (rG i) (hrE i) hrkF (hrG i),
    map_add]

/-! ### Multiplicativity on tensor products -/

/-- The Chern character is multiplicative on a tensor product of modules of constant ranks. -/
private theorem chernCharacterOfModule_mul_constantRank
    (hc : IsTotalChernClassOnLocallyFree 𝔄.toChernSetup c) (Y : C)
    (M N : (S.obj Y).Modules) (r₁ r₂ : ℕ)
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r₁)
    (hN : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N r₂) :
    chernCharacterOfModule hc Y (Scheme.Modules.tensorObjRingedSpace (S.obj Y) M N) =
      chernCharacterOfModule hc Y M * chernCharacterOfModule hc Y N := by
  classical
  have := hM
  have := hN
  have hMN : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Modules.tensorObjRingedSpace (S.obj Y) M N) (r₁ * r₂) :=
    AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf (S.obj Y) M N r₁ r₂
  obtain ⟨P, p, -, hinj, L₁, L₂, hL₁, hL₂, hsum₁, hsum₂⟩ :=
    exists_pull_sum_invertible_pair 𝔄 Y M N r₁ r₂ hM hN
  have hrkM := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (S.map p) M r₁
  have hrkN := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (S.map p) N r₂
  have hrkMN := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (S.map p)
    (Scheme.Modules.tensorObjRingedSpace (S.obj Y) M N) (r₁ * r₂)
  have hinvL : ∀ ij : Fin r₁ × Fin r₂, AlgebraicGeometry.SheafOfModules.IsInvertible
      (S.obj P).presheaf (S.obj P).ringCatSheaf.2
      (Scheme.Modules.tensorObjRingedSpace (S.obj P) (L₁ ij.1) (L₂ ij.2)) :=
    fun ij => isInvertible_tensorObjRingedSpace _ _ (hL₁ ij.1) (hL₂ ij.2)
  have hflfinv : ∀ L : (S.obj P).Modules,
      AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj P).presheaf
          (S.obj P).ringCatSheaf.2 L →
        Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} L := by
    intro L hLL
    have := hLL
    exact stacksIsFiniteLocallyFree_of_rank L 1 inferInstance
  have hclassP : VectorBundleKZero.classOf (S.obj P)
        ((Scheme.Modules.pullback (S.map p)).obj
          (Scheme.Modules.tensorObjRingedSpace (S.obj Y) M N)) =
      ∑ ij : Fin r₁ × Fin r₂, VectorBundleKZero.classOf (S.obj P)
        (Scheme.Modules.tensorObjRingedSpace (S.obj P) (L₁ ij.1) (L₂ ij.2)) := by
    rw [VectorBundleKZero.classOf_eq_of_iso
      (pullbackTensorObjRingedSpaceIso (S.map p) M N)
      (stacksIsFiniteLocallyFree_of_rank _ _ hrkMN),
      ← VectorBundleKZero.classOf_mul _ _ (stacksIsFiniteLocallyFree_of_rank _ _ hrkM)
        (stacksIsFiniteLocallyFree_of_rank _ _ hrkN), hsum₁, hsum₂,
      Finset.sum_mul_sum, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      VectorBundleKZero.classOf_mul _ _ (hflfinv _ (hL₁ i)) (hflfinv _ (hL₂ j))
  have hroot : ∀ ij : Fin r₁ × Fin r₂,
      𝔄.c₁ P (picardClassOf (S.obj P)
          (Scheme.Modules.tensorObjRingedSpace (S.obj P) (L₁ ij.1) (L₂ ij.2)) (hinvL ij)) =
        (centralFirstChernClass 𝔄 P (picardClassOf (S.obj P) (L₁ ij.1) (hL₁ ij.1)) : 𝔄.A P) +
          (centralFirstChernClass 𝔄 P (picardClassOf (S.obj P) (L₂ ij.2) (hL₂ ij.2)) :
            𝔄.A P) :=
    fun ij => c₁_picardClassOf_tensorObjRingedSpace 𝔄.toChernSetup P (L₁ ij.1) (L₂ ij.2) (hL₁ ij.1)
      (hL₂ ij.2) (hinvL ij)
  refine PowerSeries.ext fun n => hinj ?_
  rw [PowerSeries.coeff_mul, map_sum,
    pull_coeff_chernCharacterOfModule_of_sum_invertible hc p _ _ hMN (by simp) _ hinvL hclassP n,
    Finset.sum_congr rfl fun ij (_ : ij ∈ (Finset.univ : Finset (Fin r₁ × Fin r₂))) =>
      congrArg (fun z : 𝔄.A P => z ^ n) (hroot ij),
    Finset.sum_congr rfl fun q (_ : q ∈ Finset.HasAntidiagonal.antidiagonal n) => by
      rw [map_mul, pull_coeff_chernCharacterOfModule_of_sum_invertible hc p M r₁ hM (by simp) _
          hL₁ hsum₁ q.1,
        pull_coeff_chernCharacterOfModule_of_sum_invertible hc p N r₂ hN (by simp) _
          hL₂ hsum₂ q.2]]
  exact exp_sum_tensor
    (fun i => centralFirstChernClass 𝔄 P (picardClassOf (S.obj P) (L₁ i) (hL₁ i)))
    (fun j => centralFirstChernClass 𝔄 P (picardClassOf (S.obj P) (L₂ j) (hL₂ j))) n

/-- The Chern character is multiplicative on tensor products of finite locally free modules. -/
theorem chernCharacterOfModule_mul (hc : IsTotalChernClassOnLocallyFree 𝔄.toChernSetup c) (X : C)
    (M N : (S.obj X).Modules)
    (hM : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} M)
    (hN : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} N) :
    chernCharacterOfModule hc X (Scheme.Modules.tensorObjRingedSpace (S.obj X) M N) =
      chernCharacterOfModule hc X M * chernCharacterOfModule hc X N := by
  classical
  have hM' := (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry M).mp hM
  have hN' := (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry N).mp hN
  obtain ⟨ι, -, P, p, rM, rN, hflat, hrM, hrN, hinj⟩ := 𝔄.exists_clopenRankPieces_pair X M N hM' hN'
  have hMN' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Scheme.Modules.tensorObjRingedSpace (S.obj X) M N) :=
    @AlgebraicGeometry.isFiniteLocallyFree_tensorObj (S.obj X) M N hM hN
  refine PowerSeries.ext fun n => hinj (funext fun i => ?_)
  dsimp only
  have hiso : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (S.map (p i))).obj
        (Scheme.Modules.tensorObjRingedSpace (S.obj X) M N)) (rM i * rN i) := by
    have := hrM i
    have := hrN i
    exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
      (pullbackTensorObjRingedSpaceIso (S.map (p i)) M N).symm
      (AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf (S.obj (P i)) _ _
        (rM i) (rN i))
  have hclassP : VectorBundleKZero.classOf (S.obj (P i))
        ((Scheme.Modules.pullback (S.map (p i))).obj
          (Scheme.Modules.tensorObjRingedSpace (S.obj X) M N)) =
      VectorBundleKZero.classOf (S.obj (P i))
        (Scheme.Modules.tensorObjRingedSpace (S.obj (P i))
          ((Scheme.Modules.pullback (S.map (p i))).obj M)
          ((Scheme.Modules.pullback (S.map (p i))).obj N)) :=
    VectorBundleKZero.classOf_eq_of_iso (pullbackTensorObjRingedSpaceIso (S.map (p i)) M N)
      (stacksIsFiniteLocallyFree_of_rank _ _ hiso)
  rw [PowerSeries.coeff_mul, map_sum,
    pull_coeff_chernCharacterOfModule hc (p i) _ hMN' n,
    chernCharacterOfModule_congr hc (P i) _ _ hclassP
      (by rw [𝔄.rankClass_eq (P i) _ (rM i * rN i) hiso,
        𝔄.rankClass_eq (P i) _ (rM i * rN i)
          (AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf (S.obj (P i))
            _ _ (rM i) (rN i))]),
    chernCharacterOfModule_mul_constantRank hc (P i) _ _ (rM i) (rN i) (hrM i) (hrN i),
    PowerSeries.coeff_mul]
  exact Finset.sum_congr rfl fun q _ => by
    rw [map_mul,
      pull_coeff_chernCharacterOfModule hc (p i) M hM' q.1,
      pull_coeff_chernCharacterOfModule hc (p i) N hN' q.2]

/-! ### Tag 0FI9 -/

/-- There is a rule assigning to every `X` a Chern character on all of `K₀(Vect(X))`, with no
restriction on the rank, which has properties (1), (2) and (3) of Stacks Tag 0FI9. -/
theorem exists_isChernCharacter
    (hq : ∀ (X : C) (q : ℚ), algebraMap ℚ (𝔄.A X) q ∈ 𝔄.grade X 0)
    (hc : IsTotalChernClassOnLocallyFree 𝔄.toChernSetup c) :
    ∃ ch : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔄.A X,
    IsChernCharacterOnLocallyFree 𝔄.toChernSetup ch := by
  classical
  choose ch hch _huniq using fun X : C =>
    AlgebraicGeometry.VectorBundleKZero.existsUnique_ringHom_of_tensorMultiplicative
      (S.obj X) (chernCharacterOfModule hc X)
      (chernCharacterOfModule_eq_zero hc X)
      (fun f g w hE hF hG hmono hepi hex =>
        chernCharacterOfModule_add_of_shortExact hc X f g w hE hG hmono hepi hex)
      (chernCharacterOfModule_mul hc X)
      (chernCharacterOfModule_unit hc X)
  refine ⟨fun X α n => PowerSeries.coeff n (ch X α),
    { mem_grade := fun X α n => ?_
      map_add := fun X α β n => by simp
      map_mul := fun X α β n => by rw [map_mul, PowerSeries.coeff_mul]
      map_one := fun X n => by rw [map_one, PowerSeries.coeff_one]
      map_pull := fun {X Y} f E hE n => ?_
      invertible := fun X L hL n => ?_ }⟩
  · have key : (QuotientAddGroup.mk' (𝔄.grade X n)).comp
        (((PowerSeries.coeff n).toAddMonoidHom).comp (ch X).toAddMonoidHom) = 0 :=
      VectorBundleKZero.addHom_ext fun M hM => by
        simp only [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply,
          QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
        show PowerSeries.coeff n (ch X (VectorBundleKZero.classOf (S.obj X) M)) ∈
          𝔄.grade X n
        rw [hch X M hM]
        exact coeff_chernCharacterOfModule_mem_grade hq hc X M n
    simpa [QuotientAddGroup.eq_zero_iff] using DFunLike.congr_fun key α
  · rw [hch Y E hE,
      hch X _ ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry _).mpr
        (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback_scheme (S.map f) E
          ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry E).mp hE))),
      pull_coeff_chernCharacterOfModule hc f E
        ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry E).mp hE) n]
  · have := hL
    rw [hch X L (stacksIsFiniteLocallyFree_of_rank L 1 inferInstance),
      chernCharacterOfModule_invertible hc X L hL n]

/-- In the standing situation of Section 45.12, with `A(X)` a graded `𝐐`-algebra for every
object `X` of `𝒞`, there is exactly one rule assigning to every `X` a Chern character
`ch^A : K₀(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X)` such that

1. `ch^A` is a ring map for every `X`;
2. `f^* ∘ ch^A = ch^A ∘ f^*` for every morphism `f : X' ⟶ X` of `𝒞`;
3. `ch^A([ℒ]) = exp(c₁^A(ℒ))` for every `ℒ ∈ Pic(X)`.

Here `hc` is a total Chern class on all of `K₀(Vect(X))`, and `hq` says that the rationals lie in
`A^0(X)`. -/
theorem existsUnique_isChernCharacter
    (hq : ∀ (X : C) (q : ℚ), algebraMap ℚ (𝔄.A X) q ∈ 𝔄.grade X 0)
    (hc : IsTotalChernClassOnLocallyFree 𝔄.toChernSetup c) :
    ∃! ch : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔄.A X,
    IsChernCharacterOnLocallyFree 𝔄.toChernSetup ch := by
  obtain ⟨ch, hch⟩ := exists_isChernCharacter hq hc
  refine ⟨ch, hch, fun ch' hch' => ?_⟩
  funext X α n
  exact eq_of_isChernCharacterOnLocallyFree hch' hch X α n

end

section

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}

/-- In the standing situation of Section 45.12, with `A(X)` a `𝐐`-algebra for every object `X`
of `𝒞`, there is exactly one rule assigning to every `X` a Chern character
`ch^A : K₀(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X)` which is a ring map, is compatible with pullback, and
sends an invertible module `ℒ` to `exp(c₁^A(ℒ))`. -/
theorem RationalChernSituation.existsUnique_isChernCharacter
    (𝔖 : RationalChernSituation.{u, v, v₁, w} C S) :
    ∃! ch : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔖.A X,
      IsChernCharacterOnLocallyFree 𝔖.toChernSetup ch :=
  _root_.Stacks.WeilCohomology.existsUnique_isChernCharacter 𝔖.algebraMap_mem_grade_zero
    𝔖.isTotalChernClass_totalChernClass

/-- In the standing situation of Section 45.12, read with `𝐐`-coefficients, there is exactly one
rule assigning to every object `X` of `𝒞` a Chern character

`ch^A : K₀(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X)`

which is a ring map, is compatible with pullback, and sends an invertible module `ℒ` to
`exp(c₁^A(ℒ))`.

The situation is a `Stacks.WeilCohomology.SourceChernSetup` together with the section's three
remaining conditions as the hypotheses `hpull`, `hcompare` and `hdivisor`
(`Stacks.WeilCohomology.PullbackFirstChernCondition`, `Stacks.WeilCohomology.BundleCompareClause`,
`Stacks.WeilCohomology.DivisorDatumClause`), and the `𝐐`-coefficients are the `ℚ`-algebra
structure together with `hq`, which says that the rationals lie in `A^0(X)`. -/
@[stacks 0FI9 "the unique rule `ch^A : K₀(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X)` with properties (1), \
  (2) and (3), both halves, on all of `K₀(Vect(X))` and with no restriction on the rank, in the \
  standing situation of Section 45.12 read with `𝐐`-coefficients. The standing situation is the \
  structure Stacks.WeilCohomology.ChernSetup -- the data the source fixes, with clause (1), \
  clause (2), clause (3)(a), condition (1), condition (2), condition (4) and the source's \
  grading A(X) = sum of the A^i(X) -- together with the section's three remaining conditions \
  (PullbackFirstChernCondition, BundleCompareClause, DivisorDatumClause), each in the source's \
  own form, and the `𝐐`-coefficients as an algebra structure with the rationals \
  lying in `A^0(X)`. The structures Stacks.WeilCohomology.ChernSituation and \
  RationalChernSituation are built inside the proof and are not arguments. PROVED and not \
  assumed: the total Chern classes of Tag 0FI5, which the source's own proof cites as \
  Proposition 45.12.1 \
  (Stacks.WeilCohomology.ChernSituation.isTotalChernClass_totalChernClass); the rank class \
  `r^A`, which is Stacks.WeilCohomology.SourceChernSetup.rankClass, constructed from condition \
  (2) as \
  the source constructs it, with its membership in `A^0(X)` and its compatibility with pullback \
  along an arbitrary morphism; and the projective bundle with its flat projection, invertible \
  twist and tautological sequence, from clause (3)(a). Property (2) is stated on the generators, \
  which `IsChernCharacterOnLocallyFree.map_pull_kzero` upgrades to the source's form, read \
  against the \
  CONSTRUCTED pullback homomorphism AlgebraicGeometry.VectorBundleKZero.pullbackRingHom of \
  `K₀(Vect(-))`. NO hypothesis is read more strongly than the source states it: \
  BundleCompareClause \
  is clause (3)(b) at f^*E itself, and the invariance of the total Chern class under an \
  isomorphism of modules, together with the pseudofunctoriality coherence isomorphism \
  h^*(g^*E) = (h . g)^*E, are PROVED (chernSeries_eq_of_iso, \
  pull_chernSeries_coeff_of_iso) rather than obtained by asking that clause at every module \
  isomorphic to f^*E"]
theorem existsUnique_isChernCharacter_of_source (𝔄 : SourceChernSetup.{u, v, v₁, w} C S)
    [∀ X : C, Algebra ℚ (𝔄.A X)]
    (hq : ∀ (X : C) (q : ℚ), algebraMap ℚ (𝔄.A X) q ∈ 𝔄.grade X 0)
    (hpull : PullbackFirstChernCondition 𝔄) (hcompare : BundleCompareClause 𝔄)
    (hdivisor : DivisorDatumClause 𝔄) :
    ∃! ch : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔄.A X,
    IsChernCharacterOnLocallyFree 𝔄.toChernSetup ch :=
  _root_.Stacks.WeilCohomology.existsUnique_isChernCharacter hq
    (chernSituationOfSource 𝔄 hpull hcompare hdivisor).isTotalChernClass_totalChernClass

end

end Stacks.WeilCohomology

end
