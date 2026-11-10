module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.ChernCommutation
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.DerivedChernClasses
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.NewtonAdditivity

/-!
# `P_p` of a complex is the alternating sum of the `P_p` of its terms

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `Y` be locally of
finite type over `S` and let `ℰ^•` be a locally bounded complex of finite locally free
`𝒪_Y`-modules. The source defines

  `P_p(ℰ^•) = ∑_n (-1)^n P_p(ℰ^n)`

while `Stacks.Chow.complexPowerSum`, the class carrying Stacks 0ESZ, is Newton's recursion of
Stacks 0F9B applied to the components of `c(ℰ^•) = ∏_n c(ℰ^n)^{(-1)^n}` and to the alternating
rank class. The two agree, and this file proves it: the identification is
`Stacks.Chow.newtonPowerSum_complexChernBounded_eq_sum` for a complex bounded with constant
ranks, which is the shape the source displays the formula in, and
`Stacks.Chow.res_complexPowerSum_complexRankLocus` for the class the library actually builds,
read on each piece of the clopen decomposition by rank loci it is glued over.

## Main definitions

* `Stacks.Chow.modulePowerSum` — `P_p(ℰ) ∈ ∏_{q ≥ 0} A^q(Y)` for a single finite locally free
  module of constant rank: the summand the source's formula is built from.

## Main results

* `Stacks.Chow.TotalChowClass.newtonPowerSum_one` — the recursion on the unit class vanishes.
* `Stacks.Chow.TotalChowClass.newtonPowerSum_inv` — `P_p(u⁻¹) = -P_p(u)`, the degree-zero terms
  being negated with it.
* `Stacks.Chow.TotalChowClass.newtonPowerSum_zpow` — the same for an integral power with
  exponent `±1`, which is the shape of a factor `c(ℰ^n)^{(-1)^n}`.
* `Stacks.Chow.TotalChowClass.newtonPowerSum_listProd` — the recursion on an ordered product of
  units with pairwise-commuting components is the sum of the recursions on the factors.
* `Stacks.Chow.newtonPowerSum_complexChernBounded_eq_sum` — **the source's formula**: the
  recursion on `c(ℰ^•)`, with the alternating rank as its degree-zero term, is
  `∑_n (-1)^n P_p(ℰ^n)` for a complex bounded with constant ranks `ρ`, the sums running over any
  finite set of degrees outside which the ranks vanish.
* `Stacks.Chow.res_complexPowerSum_complexRankLocus` — the same for
  `Stacks.Chow.complexPowerSum`, on each rank locus of a locally bounded complex.

## Implementation notes

### Nothing here carries Stacks 0ESZ

These are identifications of the class that carries the tag, not a second carrier of it. The
clause of Stacks 0ESZ is that the three classes depend only on the object of `D(𝒪_Y)`, and it is
registered on `Stacks.Chow.complexPowerSumComponent` and
`Stacks.Chow.complexPowerSumComponent_eq_of_iso` in
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.DerivedChernClasses`. The source's
*defining formula* would be a second clause, but it is not stated globally below: for a complex
whose terms have non-constant rank there is no `P_p(ℰ^n)` on `Y` to sum — the per-module power
sum `Stacks.Chow.modulePowerSum` is defined at a constant rank — so
`Stacks.Chow.res_complexPowerSum_complexRankLocus` states the formula on each rank locus rather
than on `Y`. That is enough to identify the class, the rank loci being a clopen decomposition,
and not enough to state the clause.

The three side conditions of
`Stacks.Chow.TotalChowClass.newtonPowerSum_mul_of_commute_homComponent` — the degree-`0` component
of each factor is `1 ∈ A^0(Y)`, the components of the factors commute (Stacks 02UA), and the
degree-zero terms add — are supplied by
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.ChernCommutation`, where each of them is
proved with the closure properties that the induction over the list of degrees needs.

The negative exponents are handled by `Stacks.Chow.TotalChowClass.newtonPowerSum_inv`, whose
proof is the additivity applied to `u u⁻¹ = 1` together with
`Stacks.Chow.TotalChowClass.newtonPowerSum_one`: the recursion on `1` reads only the components
of `1` in positive degrees, which vanish, and its degree-zero term is `0`.

The ordered product `Stacks.Chow.complexChernProd` is a `List.prod` over the degrees of nonzero
rank in increasing order, so the statement is proved by induction on that list and then
specialised; the order is immaterial to the conclusion, the summands of an alternating sum
commuting, but it is what the definition of `c(ℰ^•)` is given by.

## References

* [Stacks Project, Tag 0ESZ](https://stacks.math.columbia.edu/tag/0ESZ)
* [Stacks Project, Tag 0F9B](https://stacks.math.columbia.edu/tag/0F9B)
* [Stacks Project, Tag 0F9C](https://stacks.math.columbia.edu/tag/0F9C)
* [Stacks Project, Tag 02UA](https://stacks.math.columbia.edu/tag/02UA)
* [Stacks Project, Tag 02UI](https://stacks.math.columbia.edu/tag/02UI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Finset

universe u

namespace Stacks.Chow

namespace TotalChowClass

variable {C : ChowSituation.{u}} {Y : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]

/-- **Newton's recursion on the unit class vanishes.** The components of `1` in positive degrees
are zero, and in degree zero the recursion returns its degree-zero term, here `0`. -/
theorem newtonPowerSum_one (p : ℕ) :
    newtonPowerSum (0 : TotalChowClass C sY)
      (fun i : ℕ+ ↦ homComponent (i : ℕ) (1 : TotalChowClass C sY)) p = 0 := by
  have hc : (fun i : ℕ+ ↦ homComponent (i : ℕ) (1 : TotalChowClass C sY)) =
      fun _ : ℕ+ ↦ (0 : TotalChowClass C sY) := by
    funext i
    rw [homComponent_one, ite_eq_right i.ne_zero]
  rw [hc]
  cases p with
  | zero => rw [newtonPowerSum_zero]
  | succ p => rw [newtonPowerSum_succ]; simp

/-- **`P_p(u⁻¹) = -P_p(u)`**, the degree-zero term being negated with it. Newton's additivity
applied to `u u⁻¹ = 1` gives `P_p(u) + P_p(u⁻¹) = P_p(1) = 0`. -/
theorem newtonPowerSum_inv {u : (TotalChowClass C sY)ˣ}
    (hu : (u : TotalChowClass C sY) 0 = (1 : TotalChowClass C sY) 0)
    (hcomm : CommuteHomComponent (u : TotalChowClass C sY) (u : TotalChowClass C sY))
    (r : TotalChowClass C sY) (p : ℕ) :
    newtonPowerSum (-r) (fun i : ℕ+ ↦ homComponent (i : ℕ)
        ((u⁻¹ : (TotalChowClass C sY)ˣ) : TotalChowClass C sY)) p =
      -newtonPowerSum r (fun i : ℕ+ ↦ homComponent (i : ℕ) (u : TotalChowClass C sY)) p := by
  have key := newtonPowerSum_mul_of_commute_homComponent hu (inv_apply_zero_eq_one hu)
    (CommuteHomComponent.inv_right hu hcomm) r (-r) p
  rw [add_neg_cancel, ← Units.val_mul, mul_inv_cancel, Units.val_one, newtonPowerSum_one] at key
  exact eq_neg_of_add_eq_zero_left ((add_comm _ _).trans key.symm)

/-- **Newton's recursion on an integral power with exponent `±1`** of a unit of shape
`1 + c_1 + c_2 + ⋯`, which is the shape of a factor `c(ℰ^n)^{(-1)^n}` of the total Chern class of
a complex: the recursion is scaled by the exponent, degree-zero term included. -/
theorem newtonPowerSum_zpow {u : (TotalChowClass C sY)ˣ}
    (hu : (u : TotalChowClass C sY) 0 = (1 : TotalChowClass C sY) 0)
    (hcomm : CommuteHomComponent (u : TotalChowClass C sY) (u : TotalChowClass C sY))
    (r : TotalChowClass C sY) (e : ℤˣ) (p : ℕ) :
    newtonPowerSum ((e : ℤ) • r) (fun i : ℕ+ ↦ homComponent (i : ℕ)
        ((u ^ (e : ℤ) : (TotalChowClass C sY)ˣ) : TotalChowClass C sY)) p =
      (e : ℤ) • newtonPowerSum r
        (fun i : ℕ+ ↦ homComponent (i : ℕ) (u : TotalChowClass C sY)) p := by
  rcases Int.units_eq_one_or e with he | he
  · rw [he, Units.val_one, one_smul, zpow_one, one_smul]
  · rw [he, show ((-1 : ℤˣ) : ℤ) = -1 from rfl, neg_smul, one_smul, neg_smul, one_smul,
      zpow_neg, zpow_one]
    exact newtonPowerSum_inv hu hcomm r p

/-- **Newton's recursion on an ordered product of units is the sum of the recursions on the
factors**, when every factor has degree-`0` component `1 ∈ A^0(Y)` and the components of any two
of them commute: this is the identity `P_p(a b) = P_p(a) + P_p(b)` of Stacks 0F9C iterated along
the list, the degree-zero terms adding with it. -/
theorem newtonPowerSum_listProd {ι : Type*} (f : ι → (TotalChowClass C sY)ˣ)
    (r : ι → TotalChowClass C sY) (p : ℕ) : ∀ l : List ι,
    (∀ n ∈ l, (f n : TotalChowClass C sY) 0 = (1 : TotalChowClass C sY) 0) →
    (∀ m ∈ l, ∀ n ∈ l, CommuteHomComponent (f m : TotalChowClass C sY)
      (f n : TotalChowClass C sY)) →
    newtonPowerSum ((l.map r).sum) (fun i : ℕ+ ↦ homComponent (i : ℕ)
        (((l.map f).prod : (TotalChowClass C sY)ˣ) : TotalChowClass C sY)) p =
      (l.map fun n ↦ newtonPowerSum (r n)
        (fun i : ℕ+ ↦ homComponent (i : ℕ) (f n : TotalChowClass C sY)) p).sum := by
  intro l
  induction l with
  | nil =>
    intro _ _
    simp only [List.map_nil, List.sum_nil, List.prod_nil, Units.val_one]
    exact newtonPowerSum_one p
  | cons v l ih =>
    intro hf hc
    have hfl : ∀ w ∈ l.map f, (w : TotalChowClass C sY) 0 = (1 : TotalChowClass C sY) 0 := by
      intro w hw
      obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hw
      exact hf n (List.mem_cons_of_mem v hn)
    rw [List.map_cons, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons,
      List.prod_cons, Units.val_mul,
      newtonPowerSum_mul_of_commute_homComponent (hf v List.mem_cons_self)
        (val_listProd_apply_zero _ hfl)
        (CommuteHomComponent.listProd_right _ fun w hw ↦ by
          obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hw
          exact hc v List.mem_cons_self n (List.mem_cons_of_mem v hn))
        (r v) ((l.map r).sum) p,
      ih (fun n hn ↦ hf n (List.mem_cons_of_mem v hn))
        fun m hm n hn ↦ hc m (List.mem_cons_of_mem v hm) n (List.mem_cons_of_mem v hn)]

end TotalChowClass

/-! ### Sums over the sorted members of a finite set of degrees -/

/-- The ordered sum over the members of a finite set of degrees in increasing order is the sum
over that set: the summands of a sum commute, so the order the product `c(ℰ^•)` is taken in is
immaterial to the alternating sum it produces. -/
theorem list_sum_map_sort {A : Type*} [AddCommMonoid A] (s : Finset ℤ) (g : ℤ → A) :
    ((s.sort (· ≤ ·)).map g).sum = ∑ n ∈ s, g n := by
  rw [((Finset.sort_perm_toList s (· ≤ ·)).map g).sum_eq, Finset.sum_map_toList]

/-! ### The power sum of a single module of constant rank -/

section Module

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

/-- **The power sum `P_p(ℰ) ∈ ∏_{q ≥ 0} A^q(Y)` of a finite locally free module of constant rank
`r`**, as a total class: Newton's recursion of Stacks 0F9B applied to the components of the total
Chern class `c(ℰ)`, with the rank `r` as its degree-zero term. This is the summand the source's
formula `P_p(ℰ^•) = ∑_n (-1)^n P_p(ℰ^n)` is built from. -/
def modulePowerSum (F : Y.Modules) (r : ℕ)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r) (p : ℕ) :
    TotalChowClass C sY :=
  letI := hF
  newtonPowerSum ((r : ℤ) • (1 : TotalChowClass C sY))
    (fun i : ℕ+ ↦ TotalChowClass.homComponent (i : ℕ) (totalChern C sY F r)) p

/-- **The degree-zero power sum is the rank**, the rank variable of Stacks 0F9B. -/
theorem modulePowerSum_zero (F : Y.Modules) (r : ℕ)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r) :
    modulePowerSum C sY F r hF 0 = (r : ℤ) • 1 :=
  newtonPowerSum_zero _ _

end Module

/-! ### The source's formula for a bounded complex of constant ranks -/

section Bounded

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (P : CochainComplex Y.Modules ℤ)

/-- The degree-`0` component of the unit `c(ℰ)` is the class `1 ∈ A^0(Y)`. -/
private theorem totalChernUnit_apply_zero (F : Y.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] :
    ((totalChernUnit C sY F r : (TotalChowClass C sY)ˣ) : TotalChowClass C sY) 0 =
      (1 : TotalChowClass C sY) 0 := by
  rw [val_totalChernUnit]
  exact totalChern_apply_zero C sY F r

/-- The components of the units `c(ℰ)` and `c(ℱ)` commute. -/
private theorem commute_homComponent_totalChernUnit (F F' : Y.Modules) (r r' : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F' r'] :
    CommuteHomComponent ((totalChernUnit C sY F r : (TotalChowClass C sY)ˣ) : TotalChowClass C sY)
      ((totalChernUnit C sY F' r' : (TotalChowClass C sY)ˣ) : TotalChowClass C sY) := by
  rw [val_totalChernUnit, val_totalChernUnit]
  exact commute_homComponent_totalChern C sY F F' r r'

/-- **Newton's recursion on a factor `c(ℰ^n)^{(-1)^n}`** of the total Chern class of a bounded
complex of constant ranks is `(-1)^n P_p(ℰ^n)`, the degree-zero term `(-1)^n rank(ℰ^n)` being
scaled with it. -/
theorem newtonPowerSum_complexChernFactor (ρ : ℤ →₀ ℕ)
    (hP : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n))
    (n : ℤ) (p : ℕ) :
    letI := hP n
    newtonPowerSum (((n.negOnePow : ℤ)) • ((ρ n : ℤ) • (1 : TotalChowClass C sY)))
        (fun i : ℕ+ ↦ TotalChowClass.homComponent (i : ℕ)
          ((complexChernFactor C sY P ρ hP n : (TotalChowClass C sY)ˣ) :
            TotalChowClass C sY)) p =
      ((n.negOnePow : ℤ)) • modulePowerSum C sY (P.X n) (ρ n) (hP n) p := by
  let := hP n
  rw [complexChernFactor, modulePowerSum]
  exact TotalChowClass.newtonPowerSum_zpow (totalChernUnit_apply_zero C sY _ _)
    (commute_homComponent_totalChernUnit C sY _ _ _ _) _ _ p

/-- **The source's formula `P_p(ℰ^•) = ∑_n (-1)^n P_p(ℰ^n)`.** For a complex `ℰ^•` of finite
locally free modules with `ℰ^n` of constant rank `ρ n`, `ρ` finitely supported, Newton's
recursion of Stacks 0F9B applied to the components of the total Chern class
`c(ℰ^•) = ∏_n c(ℰ^n)^{(-1)^n}` (`Stacks.Chow.complexChernBounded`), with the alternating rank
`∑_n (-1)^n rank(ℰ^n)` as its degree-zero term, is the alternating sum of the power sums of the
terms — the class the source displays. The sums run over the degrees of nonzero rank, outside
which both sides' summands are those of a rank-zero module. -/
theorem newtonPowerSum_complexChernBounded_eq_sum (ρ : ℤ →₀ ℕ)
    (hP : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n))
    (p : ℕ) (s : Finset ℤ) :
    newtonPowerSum
        (∑ n ∈ s, ((n.negOnePow : ℤ) * (ρ n : ℤ)) • (1 : TotalChowClass C sY))
        (fun i : ℕ+ ↦ TotalChowClass.homComponent (i : ℕ)
          ((complexChernProd C sY P ρ hP s : (TotalChowClass C sY)ˣ) :
            TotalChowClass C sY)) p =
      ∑ n ∈ s, ((n.negOnePow : ℤ)) • modulePowerSum C sY (P.X n) (ρ n) (hP n) p := by
  rw [← list_sum_map_sort s fun n ↦ ((n.negOnePow : ℤ) * (ρ n : ℤ)) • (1 : TotalChowClass C sY),
    ← list_sum_map_sort s fun n ↦ ((n.negOnePow : ℤ)) •
      modulePowerSum C sY (P.X n) (ρ n) (hP n) p]
  simp only [← smul_smul]
  have hcomm : ∀ m n : ℤ, CommuteHomComponent
      ((complexChernFactor C sY P ρ hP m : (TotalChowClass C sY)ˣ) : TotalChowClass C sY)
      ((complexChernFactor C sY P ρ hP n : (TotalChowClass C sY)ˣ) : TotalChowClass C sY) := by
    intro m n
    let := hP m
    let := hP n
    rw [complexChernFactor, complexChernFactor]
    exact (CommuteHomComponent.zpow_right (totalChernUnit_apply_zero C sY _ _)
      (CommuteHomComponent.zpow_right (totalChernUnit_apply_zero C sY _ _)
        (commute_homComponent_totalChernUnit C sY _ _ _ _).symm _).symm _).symm
  rw [complexChernProd,
    TotalChowClass.newtonPowerSum_listProd (complexChernFactor C sY P ρ hP)
      (fun n ↦ ((n.negOnePow : ℤ)) • ((ρ n : ℤ) • (1 : TotalChowClass C sY))) p _
      (fun n _ ↦ complexChernFactor_apply_zero C sY P ρ hP n) fun m _ n _ ↦ hcomm m n]
  refine congrArg List.sum (List.map_congr_left fun n _ ↦ ?_)
  exact newtonPowerSum_complexChernFactor C sY P ρ hP n p

end Bounded

/-! ### The formula on the rank loci of a locally bounded complex -/

section LocallyBounded

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  {P : CochainComplex Y.Modules ℤ} (hP : IsLocallyBoundedFiniteLocallyFree P)

/-- **The class `P_p(ℰ^•)` of Stacks 0ESZ is the source's alternating sum
`∑_n (-1)^n P_p(ℰ^n)`.** `Stacks.Chow.complexPowerSum` is Newton's recursion applied to
`c(ℰ^•)` and the alternating rank class; on each rank locus `Y_ρ` of the decomposition the class
is glued over, the complex is bounded with constant ranks `ρ` and the recursion is the
alternating sum of the power sums `Stacks.Chow.modulePowerSum` of its terms. Since the rank loci
are a clopen decomposition of `Y`, this identifies the class the library builds with the class
the source defines. -/
theorem res_complexPowerSum_complexRankLocus (ρ : ℤ →₀ ℕ) (p : ℕ) :
    TotalChowClass.res (complexRankLocus hP ρ).ι rfl (complexPowerSum C sY hP p) =
      ∑ n ∈ ρ.support, ((n.negOnePow : ℤ)) •
        modulePowerSum C ((complexRankLocus hP ρ).ι ≫ sY)
          ((pullbackComplex (complexRankLocus hP ρ).ι P).X n) (ρ n)
          (isFiniteLocallyFreeOfRank_complexRankLocus hP ρ n) p := by
  have hsupp : (Function.support fun n : ℤ ↦ (n.negOnePow : ℤ) * (ρ n : ℤ)) ⊆
      (ρ.support : Set ℤ) := by
    intro n hn
    by_contra hns
    have h0 : ρ n = 0 := Finsupp.notMem_support_iff.1 (by simpa using hns)
    exact hn (by simp [h0])
  rw [complexPowerSum, map_newtonPowerSum, res_complexRankClass_complexRankLocus,
    finsum_eq_finsetSum_of_support_subset _ hsupp, Finset.sum_smul,
    ← newtonPowerSum_complexChernBounded_eq_sum C ((complexRankLocus hP ρ).ι ≫ sY)
      (pullbackComplex (complexRankLocus hP ρ).ι P) ρ
      (isFiniteLocallyFreeOfRank_complexRankLocus hP ρ) p ρ.support]
  congr 1
  funext i
  rw [TotalChowClass.res_homComponent, res_complexChern_complexRankLocus]
  rfl

end LocallyBounded

end Stacks.Chow

end
