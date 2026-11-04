module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.ChernCharacterExistence
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.CentralChernEval
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.WeakChernClasses.ChernCharacter
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.WeakChernClasses.InvertibleTensor
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.WeakChernClasses.KZeroRule
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.WeakChernClasses.RankSetup

/-!
# The Chern character exists, and Stacks Tag 0FI9, in the weak standing situation

The results of `StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.ChernCharacterExistence`,
stated for `Stacks.WeilCohomology.Weak.ChernSetup`: the standing situation
of Stacks Section 45.12 in which the projective bundle formula, condition (4), is only asked to be
injective and to resolve the top power `c₁^A(𝒪_P(1))^{r+1}` of the twist class (see
`StacksFrontier.AlgebraicGeometry.WeilCohomology.WeakChernClasses.Situation`, which explains why Tag
0FIE needs this generality). The arguments are those of the original module, which use condition
(4) only through these two properties.

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

namespace Stacks.WeilCohomology.Weak

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}

/-! ### Two pieces of arithmetic -/

/-- Pullback commutes with the structure map of `𝐐`: there is at most one ring map out of `𝐐`
into a given ring, so a ring map between `𝐐`-algebras is automatically one of `𝐐`-algebras. -/
private theorem pull_algebraMap (𝔚 : ChernSetup.{u, v, v₁, w} C S)
    [∀ X : C, Algebra ℚ (𝔚.A X)] {X Y : C} (f : X ⟶ Y) (q : ℚ) :
    𝔚.pull f (algebraMap ℚ (𝔚.A Y) q) = algebraMap ℚ (𝔚.A X) q :=
  congrFun (congrArg DFunLike.coe
    (Subsingleton.elim ((𝔚.pull f).comp (algebraMap ℚ (𝔚.A Y))) (algebraMap ℚ (𝔚.A X)))) q

/-- **The first Chern class of an invertible module, as a central element of `A(X)`.** Condition
(1) of the source's situation says that `c₁^A(ℒ)` is central, which is what lets the universal
polynomials of Tag 0F9B be evaluated at Chern classes. -/
def centralFirstChernClass (𝔚 : ChernSetup.{u, v, v₁, w} C S) (X : C)
    (L : (S.obj X).picardGroup) : Subring.center (𝔚.A X) :=
  ⟨𝔚.c₁ X L, Subring.mem_center_iff.mpr fun b => (𝔚.c₁_central X L b).symm⟩

/-- The element of `A(X)` underlying `centralFirstChernClass 𝔚 X L` is `c₁^A(L)`. -/
@[simp] theorem coe_centralFirstChernClass (𝔚 : ChernSetup.{u, v, v₁, w} C S) (X : C)
    (L : (S.obj X).picardGroup) :
    (centralFirstChernClass 𝔚 X L : 𝔚.A X) = 𝔚.c₁ X L := rfl

section

variable {𝔚 : ChernSetup.{u, v, v₁, w} C S} [∀ X : C, Algebra ℚ (𝔚.A X)]
  {c : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔚.A X}

/-! ### The Chern classes of a sum of classes of invertible modules -/

omit [∀ X : C, Algebra ℚ (𝔚.A X)] in
/-- **The total Chern classes of a sum of classes of invertible modules are the elementary
symmetric functions of their first Chern classes.** Property (1) of Tag 0FI5 turns the sum into a
convolution and property (3) gives each factor as `1 + c₁^A(ℒ)`, which is exactly the recursion
that builds the elementary symmetric functions one root at a time. -/
private theorem chernClass_sum_esymm (hc : IsTotalChernClass 𝔚 c) (P : C) {ι : Type*}
    (L : ι → (S.obj P).Modules)
    (hL : ∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj P).presheaf
      (S.obj P).ringCatSheaf.2 (L j))
    (x : ι → Subring.center (𝔚.A P))
    (hx : ∀ j, (x j : 𝔚.A P) = 𝔚.c₁ P (picardClassOf (S.obj P) (L j) (hL j)))
    (s : Finset ι) : ∀ n : ℕ,
    c P (∑ j ∈ s, VectorBundleKZero.classOf (S.obj P) (L j)) n =
      ((s.val.map x).esymm n : Subring.center (𝔚.A P)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro n
      rw [Finset.sum_empty, hc.map_zero]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · rw [if_neg (by omega : ¬ n = 0), Finset.empty_val, Multiset.map_zero,
          Multiset.esymm_of_card_lt (by simpa using hn)]
        simp
  | insert a s ha ih =>
      intro n
      have hval : ((insert a s).val.map x) = x a ::ₘ (s.val.map x) := by
        rw [Finset.insert_val_of_notMem ha, Multiset.map_cons]
      have hexp : c P (∑ j ∈ insert a s, VectorBundleKZero.classOf (S.obj P) (L j)) n =
          ∑ k ∈ Finset.range (n + 1),
            (if k = 0 then (1 : 𝔚.A P) else if k = 1 then (x a : 𝔚.A P) else 0) *
              (((s.val.map x).esymm (n - k) : Subring.center (𝔚.A P)) : 𝔚.A P) := by
        rw [Finset.sum_insert ha, hc.map_add,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hc.invertible P (L a) (hL a) k, ih (n - k), hx a]
      rw [hexp, hval]
      cases n with
      | zero => simp
      | succ m =>
          have hzero : ∀ k ∈ Finset.range m,
              (if k + 1 + 1 = 0 then (1 : 𝔚.A P)
                else if k + 1 + 1 = 1 then (x a : 𝔚.A P) else 0) *
                (((s.val.map x).esymm (m + 1 - (k + 1 + 1)) :
                  Subring.center (𝔚.A P)) : 𝔚.A P) = 0 := by
            intro k _
            simp
          rw [esymm_cons, Finset.sum_range_succ' _ (m + 1), Finset.sum_range_succ' _ m,
            Finset.sum_congr rfl hzero, Finset.sum_const_zero]
          push_cast
          simp
          abel

/-! ### The Chern classes of a module class are central -/

omit [∀ X : C, Algebra ℚ (𝔚.A X)] in
/-- The Chern classes of the class of a module of **constant** rank are central: after pullback
along the morphism the splitting principle produces they are elementary symmetric functions of
first Chern classes, which condition (1) makes central, and `p^*` is injective. -/
private theorem chernClass_classOf_mem_center_constantRank (hc : IsTotalChernClass 𝔚 c) (Y : C)
    (M : (S.obj Y).Modules) (r : ℕ)
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r) (n : ℕ) :
    c Y (VectorBundleKZero.classOf (S.obj Y) M) n ∈ Subring.center (𝔚.A Y) := by
  rw [Subring.mem_center_iff]
  intro b
  obtain ⟨P, p, -, hinj, hfil⟩ :=
    𝔚.exists_injective_hasInvertibleFiltration Y Unit (fun _ => M) (fun _ => r) fun _ => hM
  obtain ⟨-, L, hL, hsum⟩ := (hfil ()).exists_classOf_eq_sum
  refine hinj ?_
  rw [map_mul, map_mul, hc.map_pull p M hM.isFiniteLocallyFree n, hsum,
    chernClass_sum_esymm hc P L hL
      (fun j => centralFirstChernClass 𝔚 P (picardClassOf (S.obj P) (L j) (hL j)))
      (fun j => rfl) Finset.univ n]
  exact (Subring.mem_center_iff.mp (Subtype.property _)) _

omit [∀ X : C, Algebra ℚ (𝔚.A X)] in
/-- **The Chern classes of the class of a module are central in `A(X)`.** The rank need not be
constant: restricting to the pieces on which it is reduces to the constant-rank case, and a class
is determined by its restrictions. -/
theorem chernClass_classOf_mem_center (hc : IsTotalChernClass 𝔚 c) (X : C)
    (M : (S.obj X).Modules) (n : ℕ) :
    c X (VectorBundleKZero.classOf (S.obj X) M) n ∈ Subring.center (𝔚.A X) := by
  by_cases hM : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} M
  · rw [Subring.mem_center_iff]
    intro b
    obtain ⟨ι, -, P, p, r, -, hr, hinj⟩ := 𝔚.exists_clopenRankPieces X M
      ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry M).mp hM)
    refine hinj (funext fun i => ?_)
    dsimp only
    rw [map_mul, map_mul, hc.map_pull (p i) M
      ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry M).mp hM) n]
    exact (Subring.mem_center_iff.mp
      (chernClass_classOf_mem_center_constantRank hc (P i) _ (r i) (hr i) n)) _
  · rw [VectorBundleKZero.classOf_eq_zero_of_not_isFiniteLocallyFree M hM, hc.map_zero]
    split_ifs
    · exact (Subring.center (𝔚.A X)).one_mem
    · exact (Subring.center (𝔚.A X)).zero_mem

/-- The Chern classes of the class of a module, as central elements of `A(X)`, which is where the
universal polynomials of Tag 0F9B can be evaluated. -/
def centralChernClass (hc : IsTotalChernClass 𝔚 c) (X : C) (M : (S.obj X).Modules) (i : ℕ+) :
    Subring.center (𝔚.A X) :=
  ⟨c X (VectorBundleKZero.classOf (S.obj X) M) (i : ℕ),
    chernClass_classOf_mem_center hc X M (i : ℕ)⟩

omit [∀ X : C, Algebra ℚ (𝔚.A X)] in
/-- The element of `A(X)` underlying `centralChernClass hc X M i` is the `i`-th Chern class of
the class of `M`. -/
@[simp] theorem coe_centralChernClass (hc : IsTotalChernClass 𝔚 c) (X : C)
    (M : (S.obj X).Modules) (i : ℕ+) :
    (centralChernClass hc X M i : 𝔚.A X) =
      c X (VectorBundleKZero.classOf (S.obj X) M) (i : ℕ) := rfl

/-! ### The Chern character of a module -/

/-- **The Chern character of a finite locally free module**, the formula of Tag 0FI9's proof:
`ch^A(ℰ) = r^A(ℰ) + ∑_{i ≥ 1} (1/i!) P_i(c_1^A(ℰ), …, c_i^A(ℰ))`,
as an element of `PowerSeries (A(X))`, which is `∏_{i ≥ 0} A^i(X)` with the convolution product.
The degree-zero coefficient is the rank class; in positive degrees the universal power-sum
polynomial of Tag 0F9B is evaluated at the Chern classes, in the centre of `A(X)`. -/
def chernCharacterOfModule (hc : IsTotalChernClass 𝔚 c) (X : C)
    (M : (S.obj X).Modules) : PowerSeries (𝔚.A X) :=
  PowerSeries.mk fun n =>
    if n = 0 then 𝔚.rankClass X M
    else algebraMap ℚ (𝔚.A X) ((n.factorial : ℚ)⁻¹) *
      ((chernClassEval (centralChernClass hc X M) (powerSumPolynomial n)) : 𝔚.A X)

/-- **The Chern character of a module depends only on its class in `K₀(Vect(X))` and its rank
class.** Both the Chern classes and the rank class the formula consumes are functions of those
two, so this is immediate; it is what lets the pullback of a tensor product be replaced by the
tensor product of the pullbacks, which have the same class by Tag 01CD. -/
theorem chernCharacterOfModule_congr (hc : IsTotalChernClass 𝔚 c) (X : C)
    (M N : (S.obj X).Modules)
    (hclass : VectorBundleKZero.classOf (S.obj X) M = VectorBundleKZero.classOf (S.obj X) N)
    (hrank : 𝔚.rankClass X M = 𝔚.rankClass X N) :
    chernCharacterOfModule hc X M = chernCharacterOfModule hc X N := by
  have hcc : centralChernClass hc X M = centralChernClass hc X N := by
    funext i
    exact Subtype.ext (by rw [coe_centralChernClass, coe_centralChernClass, hclass])
  rw [chernCharacterOfModule, chernCharacterOfModule, hcc, hrank]

/-- **The Chern character of a module whose class splits.** If the class of `ℳ` in `K₀(Vect(X))`
is the sum of the classes of a finite family of invertible modules and its rank class is the
number of them, then its Chern character is `∑_j exp(c₁^A(ℒ_j))`, coefficientwise. This is the
one computation the three properties of the Chern character are read off from. -/
theorem coeff_chernCharacterOfModule_of_sum_invertible (hc : IsTotalChernClass 𝔚 c) (X : C)
    (M : (S.obj X).Modules) {ι : Type*} [Fintype ι]
    (L : ι → (S.obj X).Modules)
    (hL : ∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 (L j))
    (hsum : VectorBundleKZero.classOf (S.obj X) M =
      ∑ j, VectorBundleKZero.classOf (S.obj X) (L j))
    (hrank : 𝔚.rankClass X M = (Fintype.card ι : 𝔚.A X)) (n : ℕ) :
    PowerSeries.coeff n (chernCharacterOfModule hc X M) =
      algebraMap ℚ (𝔚.A X) ((n.factorial : ℚ)⁻¹) *
        ∑ j, 𝔚.c₁ X (picardClassOf (S.obj X) (L j) (hL j)) ^ n := by
  classical
  have hroots : centralChernClass hc X M =
      fun i : ℕ+ => esymmOfRoots
        (fun j => centralFirstChernClass 𝔚 X (picardClassOf (S.obj X) (L j) (hL j))) (i : ℕ) := by
    funext i
    refine Subtype.ext ?_
    rw [coe_centralChernClass, hsum,
      chernClass_sum_esymm hc X L hL
        (fun j => centralFirstChernClass 𝔚 X (picardClassOf (S.obj X) (L j) (hL j)))
        (fun j => rfl) Finset.univ (i : ℕ)]
    rfl
  rw [chernCharacterOfModule, PowerSeries.coeff_mk]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hrank]
  · rw [if_neg (by omega : ¬ n = 0), hroots, chernClassEval_powerSumPolynomial _ n hn]
    congr 1
    rw [powerSumOfRoots]
    push_cast
    rfl

/-- `coeff_chernCharacterOfModule_of_sum_invertible` for a module of known rank, the number of
invertible summands. -/
private theorem coeff_chernCharacterOfModule_of_rank_sum_invertible
    (hc : IsTotalChernClass 𝔚 c) (X : C) (M : (S.obj X).Modules) {ι : Type*} [Fintype ι] (r : ℕ)
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r)
    (hcard : Fintype.card ι = r) (L : ι → (S.obj X).Modules)
    (hL : ∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 (L j))
    (hsum : VectorBundleKZero.classOf (S.obj X) M =
      ∑ j, VectorBundleKZero.classOf (S.obj X) (L j)) (n : ℕ) :
    PowerSeries.coeff n (chernCharacterOfModule hc X M) =
      algebraMap ℚ (𝔚.A X) ((n.factorial : ℚ)⁻¹) *
        ∑ j, 𝔚.c₁ X (picardClassOf (S.obj X) (L j) (hL j)) ^ n :=
  coeff_chernCharacterOfModule_of_sum_invertible hc X M L hL hsum
    (by rw [𝔚.rankClass_eq X M r hM, hcard]) n

/-- Splitting principle for a pair of modules of constant ranks `r₁` and `r₂`: one flat `p` with
`p^*` injective after which both pullbacks are sums of classes of invertible modules. -/
private theorem exists_injective_pull_pair_invertible_sum (𝔚 : ChernSetup.{u, v, v₁, w} C S)
    (Y : C) (M N : (S.obj Y).Modules) (r₁ r₂ : ℕ)
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r₁)
    (hN : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N r₂) :
    ∃ (P : C) (p : P ⟶ Y), Flat (S.map p) ∧ Function.Injective (𝔚.pull p) ∧
      ∃ (L₁ : Fin r₁ → (S.obj P).Modules) (L₂ : Fin r₂ → (S.obj P).Modules),
        (∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj P).presheaf
          (S.obj P).ringCatSheaf.2 (L₁ j)) ∧
        (∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj P).presheaf
          (S.obj P).ringCatSheaf.2 (L₂ j)) ∧
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
    𝔚.exists_injective_hasInvertibleFiltration Y (Fin 2) ![M, N] ![r₁, r₂] hfam
  have hfilM : HasInvertibleFiltration (S.obj P)
      ((Scheme.Modules.pullback (S.map p)).obj M) r₁ := by simpa using hfil 0
  have hfilN : HasInvertibleFiltration (S.obj P)
      ((Scheme.Modules.pullback (S.map p)).obj N) r₂ := by simpa using hfil 1
  obtain ⟨-, L₁, hL₁, hsum₁⟩ := hfilM.exists_classOf_eq_sum
  obtain ⟨-, L₂, hL₂, hsum₂⟩ := hfilN.exists_classOf_eq_sum
  exact ⟨P, p, hpflat, hinj, L₁, L₂, hL₁, hL₂, hsum₁, hsum₂⟩

/-- The Chern character of a module is compatible with pullback, coefficientwise: the rank class
is, by `Stacks.WeilCohomology.Weak.ChernSetup.pull_rankClass`, the Chern classes are by property
(2) of Tag 0FI5, and a ring map commutes with the evaluation of the universal polynomials. -/
theorem pull_coeff_chernCharacterOfModule (hc : IsTotalChernClass 𝔚 c)
    {X Y : C} (f : X ⟶ Y) (E : (S.obj Y).Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E) (n : ℕ) :
    𝔚.pull f (PowerSeries.coeff n (chernCharacterOfModule hc Y E)) =
      PowerSeries.coeff n (chernCharacterOfModule hc X
        ((Scheme.Modules.pullback (S.map f)).obj E)) := by
  rw [chernCharacterOfModule, chernCharacterOfModule, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using 𝔚.pull_rankClass f E hE
  · simp only [if_neg (by omega : ¬ n = 0)]
    rw [map_mul, pull_algebraMap,
      map_chernClassEval (𝔚.pull f) (centralChernClass hc Y E)
        (centralChernClass hc X ((Scheme.Modules.pullback (S.map f)).obj E))
        (fun i => hc.map_pull f E hE (i : ℕ))]

/-- The `n`-th coefficient of the Chern character of a module lies in `A^n(X)`: the rank class
lies in degree zero, `P_n` is weighted homogeneous of degree `n` in variables of weight `i`, and
`c_i^A` lies in degree `i`. -/
theorem coeff_chernCharacterOfModule_mem_grade
    (hq : ∀ (X : C) (q : ℚ), algebraMap ℚ (𝔚.A X) q ∈ 𝔚.grade X 0)
    (hc : IsTotalChernClass 𝔚 c) (X : C) (M : (S.obj X).Modules) (n : ℕ) :
    PowerSeries.coeff n (chernCharacterOfModule hc X M) ∈ 𝔚.grade X n := by
  rw [chernCharacterOfModule, PowerSeries.coeff_mk]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using 𝔚.rankClass_mem_grade X M
  · rw [if_neg (by omega : ¬ n = 0)]
    have h1 : ((chernClassEval (centralChernClass hc X M)
        (powerSumPolynomial n)) : 𝔚.A X) ∈ 𝔚.grade X n :=
      chernClassEval_mem_of_isWeightedHomogeneous (𝔚.grade X) (𝔚.one_mem X)
        (𝔚.mul_mem X) _
        (fun i => hc.mem_grade X _ (i : ℕ)) n _
        (isWeightedHomogeneous_powerSumPolynomial n)
    simpa using 𝔚.mul_mem X 0 n (hq X _) h1

/-! ### The three properties of the Chern character of a module -/

/-- The Chern character vanishes off the finite locally free modules: the class of such a module
is zero and so is its rank class, which is the empty case of the splitting computation. -/
theorem chernCharacterOfModule_eq_zero (hc : IsTotalChernClass 𝔚 c) (X : C)
    (M : (S.obj X).Modules)
    (h : ¬ Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} M) :
    chernCharacterOfModule hc X M = 0 := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_chernCharacterOfModule_of_sum_invertible hc X M
    (ι := Fin 0) (fun j => j.elim0) (fun j => j.elim0)
    (by rw [VectorBundleKZero.classOf_eq_zero_of_not_isFiniteLocallyFree M h]; simp)
    (by rw [𝔚.rankClass_eq_zero X M h]; simp) n]
  simp

/-- The Chern character of an invertible module is `exp(c₁^A(ℒ))`, which is property (3). -/
theorem chernCharacterOfModule_invertible (hc : IsTotalChernClass 𝔚 c) (X : C)
    (L : (S.obj X).Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 L) (n : ℕ) :
    PowerSeries.coeff n (chernCharacterOfModule hc X L) =
      algebraMap ℚ (𝔚.A X) ((n.factorial : ℚ)⁻¹) *
        𝔚.c₁ X (picardClassOf (S.obj X) L hL) ^ n := by
  have := hL
  rw [coeff_chernCharacterOfModule_of_sum_invertible hc X L
    (ι := Fin 1) (fun _ => L) (fun _ => hL) (by simp)
    (by rw [𝔚.rankClass_eq X L 1 inferInstance]; simp) n]
  simp

/-- The Chern character of the structure sheaf is `1`, which is the unit clause of property (1):
`𝒪_X` is invertible with trivial class in `Pic(X)`. -/
theorem chernCharacterOfModule_unit (hc : IsTotalChernClass 𝔚 c) (X : C) :
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
  · rw [if_neg (by omega : ¬ n = 0), zero_pow (by omega), mul_zero]

/-! ### Additivity along a short exact sequence -/

/-- **The Chern character is additive along a short exact sequence whose outer terms have
constant ranks.** The splitting principle of Tag 0FI7 writes the classes of the pullbacks of `ℰ`
and `𝒢` as sums of `r₁` and `r₂` classes of invertible modules; the pullback of the sequence
along the flat `p` is short exact, so the class of the pullback of `ℱ` is the sum of all
`r₁ + r₂` of them. The Chern character of each of the three is then the corresponding sum of
exponentials, and `p^*` is injective. -/
private theorem chernCharacterOfModule_add_constantRank (hc : IsTotalChernClass 𝔚 c) (Y : C)
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
    exists_injective_pull_pair_invertible_sum 𝔚 Y E G r₁ r₂ hE hG
  have : Flat (S.map p) := hpflat
  have hLsum : ∀ j : Fin r₁ ⊕ Fin r₂, AlgebraicGeometry.SheafOfModules.IsInvertible
      (S.obj P).presheaf (S.obj P).ringCatSheaf.2 (Sum.elim L₁ L₂ j) := by
    rintro (i | i)
    · exact hL₁ i
    · exact hL₂ i
  have hrkE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (S.map p)).obj E) r₁ :=
    @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ (S.map p) E r₁ hE
  have hrkF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (S.map p)).obj F) (r₁ + r₂) :=
    @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ (S.map p) F (r₁ + r₂) hF
  have hrkG : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (S.map p)).obj G) r₂ :=
    @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ (S.map p) G r₂ hG
  have hT := shortExact_map_pullback (S.map p) (ShortComplex.mk f g w) hS
  have : Mono ((Scheme.Modules.pullback (S.map p)).map f) := hT.mono_f
  have : Epi ((Scheme.Modules.pullback (S.map p)).map g) := hT.epi_g
  have hw : (Scheme.Modules.pullback (S.map p)).map f ≫
      (Scheme.Modules.pullback (S.map p)).map g = 0 :=
    ((ShortComplex.mk f g w).map (Scheme.Modules.pullback (S.map p))).zero
  have hsplit : VectorBundleKZero.classOf (S.obj P)
        ((Scheme.Modules.pullback (S.map p)).obj F) =
      VectorBundleKZero.classOf (S.obj P) ((Scheme.Modules.pullback (S.map p)).obj E) +
        VectorBundleKZero.classOf (S.obj P) ((Scheme.Modules.pullback (S.map p)).obj G) :=
    VectorBundleKZero.classOf_shortExact _ _ hw
      (stacksIsFiniteLocallyFree_of_rank _ _ hrkE) (stacksIsFiniteLocallyFree_of_rank _ _ hrkF)
      (stacksIsFiniteLocallyFree_of_rank _ _ hrkG) hT.exact
  have hclassP : VectorBundleKZero.classOf (S.obj P)
        ((Scheme.Modules.pullback (S.map p)).obj F) =
      ∑ j : Fin r₁ ⊕ Fin r₂, VectorBundleKZero.classOf (S.obj P) (Sum.elim L₁ L₂ j) := by
    rw [hsplit, hsum₁, hsum₂, Fintype.sum_sum_type]
    rfl
  refine PowerSeries.ext fun n => hinj ?_
  rw [map_add, map_add,
    pull_coeff_chernCharacterOfModule hc p F hF.isFiniteLocallyFree n,
    pull_coeff_chernCharacterOfModule hc p E hE.isFiniteLocallyFree n,
    pull_coeff_chernCharacterOfModule hc p G hG.isFiniteLocallyFree n,
    coeff_chernCharacterOfModule_of_rank_sum_invertible hc P _ _ hrkF (by simp) (Sum.elim L₁ L₂)
      hLsum hclassP n,
    coeff_chernCharacterOfModule_of_rank_sum_invertible hc P _ _ hrkE (by simp) L₁ hL₁ hsum₁ n,
    coeff_chernCharacterOfModule_of_rank_sum_invertible hc P _ _ hrkG (by simp) L₂ hL₂ hsum₂ n,
    Fintype.sum_sum_type, mul_add]
  rfl

/-- **The Chern character is additive along a short exact sequence of finite locally free
modules**, which is the first of the two statements Tag 0FI9's proof says remain, and what makes
the extension to `K₀(Vect(X))` well defined. The ranks are reduced to constant ones by
restriction to the open and closed pieces where they are constant; on a piece the rank of the
middle term is forced to be the sum of the other two. -/
theorem chernCharacterOfModule_add_of_shortExact (hc : IsTotalChernClass 𝔚 c)
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
  obtain ⟨ι, -, P, p, rE, rG, hflat, hrE, hrG, hinj⟩ := 𝔚.exists_clopenRankPieces_pair X E G hE' hG'
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

/-- **The Chern character is multiplicative on a tensor product of modules of constant ranks.**
After pullback the two factors split into `r₁` and `r₂` invertible modules, so the tensor product
splits into the `r₁ r₂` tensor products of those, whose first Chern classes are the sums
`x_j + y_{j'}`; the binomial theorem then turns `(1/n!) ∑ (x_j + y_{j'})^n` into the degree-`n`
coefficient of the product of the two exponential sums. -/
private theorem chernCharacterOfModule_mul_constantRank (hc : IsTotalChernClass 𝔚 c) (Y : C)
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
    exists_injective_pull_pair_invertible_sum 𝔚 Y M N r₁ r₂ hM hN
  have hrkM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (S.map p)).obj M) r₁ :=
    @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ (S.map p) M r₁ hM
  have hrkN : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (S.map p)).obj N) r₂ :=
    @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ (S.map p) N r₂ hN
  have hrkMN : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (S.map p)).obj
        (Scheme.Modules.tensorObjRingedSpace (S.obj Y) M N)) (r₁ * r₂) :=
    @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ (S.map p) _ (r₁ * r₂) hMN
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
      𝔚.c₁ P (picardClassOf (S.obj P)
          (Scheme.Modules.tensorObjRingedSpace (S.obj P) (L₁ ij.1) (L₂ ij.2)) (hinvL ij)) =
        (centralFirstChernClass 𝔚 P (picardClassOf (S.obj P) (L₁ ij.1) (hL₁ ij.1)) : 𝔚.A P) +
          (centralFirstChernClass 𝔚 P (picardClassOf (S.obj P) (L₂ ij.2) (hL₂ ij.2)) :
            𝔚.A P) :=
    fun ij => c₁_picardClassOf_tensorObjRingedSpace 𝔚 P (L₁ ij.1) (L₂ ij.2) (hL₁ ij.1)
      (hL₂ ij.2) (hinvL ij)
  refine PowerSeries.ext fun n => hinj ?_
  rw [PowerSeries.coeff_mul, map_sum,
    pull_coeff_chernCharacterOfModule hc p _ hMN.isFiniteLocallyFree n,
    coeff_chernCharacterOfModule_of_rank_sum_invertible hc P _ _ hrkMN (by simp) _ hinvL hclassP n,
    Finset.sum_congr rfl fun ij (_ : ij ∈ (Finset.univ : Finset (Fin r₁ × Fin r₂))) =>
      congrArg (fun z : 𝔚.A P => z ^ n) (hroot ij),
    Finset.sum_congr rfl fun q (_ : q ∈ Finset.HasAntidiagonal.antidiagonal n) => by
      rw [map_mul, pull_coeff_chernCharacterOfModule hc p M hM.isFiniteLocallyFree q.1,
        pull_coeff_chernCharacterOfModule hc p N hN.isFiniteLocallyFree q.2,
        coeff_chernCharacterOfModule_of_rank_sum_invertible hc P _ _ hrkM (by simp) L₁ hL₁ hsum₁
          q.1,
        coeff_chernCharacterOfModule_of_rank_sum_invertible hc P _ _ hrkN (by simp) L₂ hL₂ hsum₂
          q.2]]
  exact exp_sum_tensor
    (fun i => centralFirstChernClass 𝔚 P (picardClassOf (S.obj P) (L₁ i) (hL₁ i)))
    (fun j => centralFirstChernClass 𝔚 P (picardClassOf (S.obj P) (L₂ j) (hL₂ j))) n

/-- **The Chern character is multiplicative on tensor products of finite locally free modules**,
which is the second of the two statements Tag 0FI9's proof says remain, and what makes the
extension to `K₀(Vect(X))` a ring map. The ranks are reduced to constant ones by restriction to
the open and closed pieces where they are constant. -/
theorem chernCharacterOfModule_mul (hc : IsTotalChernClass 𝔚 c) (X : C)
    (M N : (S.obj X).Modules)
    (hM : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} M)
    (hN : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} N) :
    chernCharacterOfModule hc X (Scheme.Modules.tensorObjRingedSpace (S.obj X) M N) =
      chernCharacterOfModule hc X M * chernCharacterOfModule hc X N := by
  classical
  have hM' := (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry M).mp hM
  have hN' := (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry N).mp hN
  obtain ⟨ι, -, P, p, rM, rN, hflat, hrM, hrN, hinj⟩ := 𝔚.exists_clopenRankPieces_pair X M N hM' hN'
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
    pull_coeff_chernCharacterOfModule hc (p i) _
      (@AlgebraicGeometry.isFiniteLocallyFree_tensorObj (S.obj X) M N hM' hN') n,
    chernCharacterOfModule_congr hc (P i) _ _ hclassP
      (by rw [𝔚.rankClass_eq (P i) _ (rM i * rN i) hiso,
        𝔚.rankClass_eq (P i) _ (rM i * rN i)
          (AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf (S.obj (P i))
            _ _ (rM i) (rN i))]),
    chernCharacterOfModule_mul_constantRank hc (P i) _ _ (rM i) (rN i) (hrM i) (hrN i),
    PowerSeries.coeff_mul]
  exact Finset.sum_congr rfl fun q _ => by
    rw [map_mul,
      pull_coeff_chernCharacterOfModule hc (p i) M hM' q.1,
      pull_coeff_chernCharacterOfModule hc (p i) N hN' q.2]

/-! ### Tag 0FI9 -/

/-- **The existence half of Stacks Tag 0FI9**, on all of `K₀(Vect(X))` and with no restriction on
the rank: there is a rule with properties (1), (2) and (3).

The Chern character of a module is additive along short exact sequences, multiplicative on
tensor products and takes the value `1` on `𝒪_X`, so the universal property of the Grothendieck
ring, Tag 0FEM, extends it to a ring homomorphism `K₀(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X)` — that is
property (1). The grading, property (2) and property (3) are read off the generators: for each
degree, the difference between the two sides is an additive map out of `K₀(Vect(X))` vanishing on
the classes of the finite locally free modules, which generate it. -/
theorem exists_isChernCharacter
    (hq : ∀ (X : C) (q : ℚ), algebraMap ℚ (𝔚.A X) q ∈ 𝔚.grade X 0)
    (hc : IsTotalChernClass 𝔚 c) :
    ∃ ch : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔚.A X, IsChernCharacter 𝔚 ch := by
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
  · have key : (QuotientAddGroup.mk' (𝔚.grade X n)).comp
        (((PowerSeries.coeff n).toAddMonoidHom).comp (ch X).toAddMonoidHom) = 0 :=
      VectorBundleKZero.addHom_ext fun M hM => by
        simp only [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply,
          QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
        show PowerSeries.coeff n (ch X (VectorBundleKZero.classOf (S.obj X) M)) ∈
          𝔚.grade X n
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

/-- **Stacks Project, Tag 0FI9.** In the standing situation of Section 45.12, with `A(X)` a
graded `𝐐`-algebra for every object `X` of `𝒞`, there is **exactly one** rule assigning to every
`X` a Chern character `ch^A : K₀(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X)` such that

1. `ch^A` is a ring map for every `X`;
2. `f^* ∘ ch^A = ch^A ∘ f^*` for every morphism `f : X' ⟶ X` of `𝒞`;
3. `ch^A([ℒ]) = exp(c₁^A(ℒ))` for every `ℒ ∈ Pic(X)`.

Existence is `Stacks.WeilCohomology.exists_isChernCharacter` and uniqueness is
`Stacks.WeilCohomology.eq_of_isChernCharacterOnLocallyFree`; both are on all of `K₀(Vect(X))` with
no restriction on the rank.

The rank class `r^A` is **not** a hypothesis: it is
`Stacks.WeilCohomology.Weak.ChernSetup.rankClass`, constructed from condition (2) as the source
constructs it. What `hq` says is the tag's own hypothesis that `A(X)` is a `𝐐`-algebra, read
compatibly with the grading `A` takes its values in: the rationals lie in `A^0(X)`. Without that
the target `∏_{i ≥ 0} A^i(X)` of the source's statement is not a ring the formula
`r^A + ∑_{i ≥ 1} (1/i!) P_i(c_1^A, …, c_i^A)` lands in.

This form carries **no** attribute for the tag, because `hc` assumes the total Chern classes of
Tag 0FI5 — a result the source proves, and this repository proves, rather than a condition of
the situation. The tag is registered on
`Stacks.WeilCohomology.Weak.RationalChernSituation.existsUnique_isChernCharacter`, which assumes
nothing beyond the situation, and on `Stacks.WeilCohomology.eq_of_isChernCharacterOnLocallyFree`
for the uniqueness half. -/
theorem existsUnique_isChernCharacter
    (hq : ∀ (X : C) (q : ℚ), algebraMap ℚ (𝔚.A X) q ∈ 𝔚.grade X 0)
    (hc : IsTotalChernClass 𝔚 c) :
    ∃! ch : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔚.A X, IsChernCharacter 𝔚 ch := by
  obtain ⟨ch, hch⟩ := exists_isChernCharacter hq hc
  refine ⟨ch, hch, fun ch' hch' => ?_⟩
  funext X α n
  exact eq_of_isChernCharacter' hch' hch X α n

end

section

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}

/-- **Tag 0FI9 over the standing situation as a structure.** In that situation, with `A(X)` a
`𝐐`-algebra for every object `X` of `𝒞`, there is exactly one rule assigning to every `X` a Chern
character `ch^A : K₀(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X)` which is a ring map, is compatible with
pullback, and sends an invertible module `ℒ` to `exp(c₁^A(ℒ))`.

This is `Stacks.WeilCohomology.existsUnique_isChernCharacter` with its total Chern class
discharged instead of assumed: the source's proof of this tag cites Proposition 45.12.1 for the
total Chern classes, and that proposition is Tag 0FI5, proved in this same situation.

The tag sits on `Stacks.WeilCohomology.existsUnique_isChernCharacter_of_source`, which is this
statement with the section's conditions spelled out and the situation built inside the proof. -/
theorem RationalChernSituation.existsUnique_isChernCharacter
    (𝔗 : RationalChernSituation.{u, v, v₁, w} C S) :
    ∃! ch : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔗.A X,
      IsChernCharacter 𝔗.toChernSetup ch :=
  Stacks.WeilCohomology.Weak.existsUnique_isChernCharacter 𝔗.algebraMap_mem_grade_zero
    𝔗.isTotalChernClass_totalChernClass

/-- **Stacks Project, Tag 0FI9.** In the standing situation of Section 45.12, read with
`𝐐`-coefficients, there is exactly one rule assigning to every object `X` of `𝒞` a Chern character

`ch^A : K₀(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X)`

which is a ring map, is compatible with pullback, and sends an invertible module `ℒ` to
`exp(c₁^A(ℒ))`.

**What the situation is.** `Stacks.WeilCohomology.Weak.ChernSetup` is the source's own standing
situation — the data the source fixes, with clause (1), clause (2), clause (3)(a), condition (1),
condition (2), condition (4) and the grading `A(X) = ⨁_{i ≥ 0} A^i(X)`; in particular
`Stacks.WeilCohomology.Weak.ChernSetup.bundleDatum` is a definition and not a field. The section's
three remaining conditions are the hypotheses `hpull`, `hcompare` and `hdivisor`, each in the
source's own form (`Stacks.WeilCohomology.PullbackFirstChernCondition`,
`Stacks.WeilCohomology.BundleCompareClause`, `Stacks.WeilCohomology.DivisorDatumClause`), and the
`𝐐`-coefficients this tag reads the section under are the `ℚ`-algebra structure together with
`hq`, the source's requirement that the rationals lie in `A^0(X)`. The
`Stacks.WeilCohomology.Weak.ChernSituation` is built inside the proof by
`Stacks.WeilCohomology.chernSituationOfSource` and is not an argument.

**All three conditions are in the source's own form.** In particular
`Stacks.WeilCohomology.BundleCompareClause` is clause (3)(b) at `f^*ℰ` itself, and not at every
`ℰ'` carrying an isomorphism `f^*ℰ ≅ ℰ'` — that reading would be a closure property clauses (1),
(2) and (3) do not give, since at `f = 𝟙 X` it is the closure of `𝒞` under the
`𝐏(ℰ') ⟶ 𝐏(ℰ)` induced by an arbitrary `ℰ ≅ ℰ'`. The invariance of the total Chern class under
an isomorphism of modules, which `K₀(Vect(X))` forces on any rule out of it, and the
pseudofunctoriality coherence isomorphism `h^*(g^*ℰ) ≅ (h ∘ g)^*ℰ`, which the source has for
free, are both theorems:
`Stacks.WeilCohomology.Weak.ChernSituation.chernSeries_eq_of_iso` and
`Stacks.WeilCohomology.Weak.ChernSituation.pull_chernSeries_coeff_of_iso`.

The total Chern classes the source's proof cites as Proposition 45.12.1 are not assumed: they are
`Stacks.WeilCohomology.Weak.ChernSituation.isTotalChernClass_totalChernClass` at that constructed
situation. The rank class `r^A` is not assumed either; it is
`Stacks.WeilCohomology.Weak.ChernSetup.rankClass`, built from condition (2). -/
theorem existsUnique_isChernCharacter_of_source (𝔚 : ChernSetup.{u, v, v₁, w} C S)
    [∀ X : C, Algebra ℚ (𝔚.A X)]
    (hq : ∀ (X : C) (q : ℚ), algebraMap ℚ (𝔚.A X) q ∈ 𝔚.grade X 0)
    (hpull : PullbackFirstChernCondition 𝔚) (hcompare : BundleCompareClause 𝔚)
    (hdivisor : DivisorDatumClause 𝔚) :
    ∃! ch : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔚.A X, IsChernCharacter 𝔚 ch :=
  Stacks.WeilCohomology.Weak.existsUnique_isChernCharacter hq
    (chernSituationOfSource 𝔚 hpull hcompare hdivisor).isTotalChernClass_totalChernClass

end

end Stacks.WeilCohomology.Weak

end
