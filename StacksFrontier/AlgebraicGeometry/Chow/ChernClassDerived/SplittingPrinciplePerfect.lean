module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ConnectedComponents
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.DerivedChernClasses
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PerfectPowerSum
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TotalChernWhitney
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.ChernRootsTotal
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.FirstFourPowerSums
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.SplittingProjective
public import StacksCore.Tactic.StacksAttribute

/-!
# The splitting principle for the Chern classes of a perfect object

Let `(S, δ)`, `X` and `E` be as in Definition 0F9E, the Chern classes of `E` being defined.
Remark 0FAD describes how a relation between the classes `c_p(E)`, `P_p(E)` of
Definition 0F9E (2) is proved: choose an envelope `f : Y ⟶ X` and a locally bounded complex `ℰ^•`
of finite locally free `𝒪_Y`-modules representing `Lf^*E`; by the uniqueness in Stacks 0GUD it
suffices to prove the relation for the classes of `ℰ^•`; on a connected component of `Y` the
complex is bounded with terms of fixed ranks; and by the splitting principle (Stacks 02UL) each
term may be assumed filtered with invertible successive quotients `ℒ_{n,j}`. Then, with
`x_{n,j} = c_1(ℒ_{n,j})`,

  `c(E) = ∏_{n even} ∏_j (1 + x_{n,j}) ∏_{n odd} ∏_j (1 + x_{n,j})^{-1}`,

  `P_p(E) = ∑_{n even} ∑_j x_{n,j}^p - ∑_{n odd} ∑_j x_{n,j}^p`.

This file proves that reduction and these two formulas. A *split chart* at a point `y ∈ Y`
(`Stacks.Chow.SplitChart`) consists of the connected component `V` of `y`, on which `ℰ^•` has the
fixed ranks `rank_y ℰ^n`, and a splitting morphism `π : P ⟶ V` of Stacks 02UL with the
filtrations of the `π^*ℰ^n`. Split charts exist at every point
(`Stacks.Chow.nonempty_splitChart`), restriction to all of them is injective on `A^*(X)`
(`Stacks.Chow.eq_of_forall_splitChart_res_eq`), and on each of them the two formulas hold
(`Stacks.Chow.SplitChart.res_perfectChernClass`, `Stacks.Chow.SplitChart.res_perfectPowerSum`).
`Stacks.Chow.exists_splitCharts` packages the three as Remark 0FAD.

## Main definitions

* `Stacks.Chow.EnvelopePresentation.componentOpens` — the connected component of a point of the
  source of the envelope, an open subscheme.
* `Stacks.Chow.SplitChart` — a split chart.
* `Stacks.Chow.SplitChart.res`, `Stacks.Chow.SplitChart.root`, `Stacks.Chow.SplitChart.rootFactor`
  — restriction to a chart, the Chern roots `x_{n,j}`, and the units `1 + x_{n,j}`.

## Main results

* `Stacks.Chow.exists_splitCharts` — Stacks 0FAD, the splitting principle.
* `Stacks.Chow.nonempty_splitChart`, `Stacks.Chow.eq_of_forall_splitChart_res_eq`,
  `Stacks.Chow.SplitChart.res_perfectChernClass`, `Stacks.Chow.SplitChart.res_perfectPowerSum`.
* `Stacks.Chow.totalChern_eq_prod_of_hasQuotients` — Stacks 02UJ in the ring of total classes.

## Implementation notes

The ring `A^*(X)` of total Chow cohomology classes is not known to be commutative. The factors
`1 + x_{n,j}` commute, being total Chern classes of modules (Stacks 02UA), so the product formula
holds in any order; it is stated with the products over the degrees taken in increasing order.
The reduction to the split charts is a statement about integral classes: `c(E)` and `P_p(E)` are
integral, and `ch_p(E) = P_p(E)/p!`. For rational classes the first step, restriction along the
envelope, is still injective
(`Stacks.Chow.rationalChowCohomologyRestriction_injective_of_isEnvelope`), but restriction to the
connected components need not be after tensoring with `𝐐`: `A^p(Y) = ∏_V A^p(V)` over the
components, and `(∏_V M_V) ⊗ 𝐐 ⟶ ∏_V (M_V ⊗ 𝐐)` is not injective when the `M_V` have unbounded
torsion.

## References

* [Stacks Project, Tag 0FAD](https://stacks.math.columbia.edu/tag/0FAD)
* [Stacks Project, Tag 0GUD](https://stacks.math.columbia.edu/tag/0GUD)
* [Stacks Project, Tag 02UL](https://stacks.math.columbia.edu/tag/02UL)
* [Stacks Project, Tag 0F9E](https://stacks.math.columbia.edu/tag/0F9E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Finset

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

namespace TotalChowClass

variable {C : ChowSituation.{u}} {Y : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]

/-- The homogeneous components of a class homogeneous of degree `1`. -/
theorem homComponent_of_isHomogeneous_one {x : TotalChowClass C sY} (hx : x.IsHomogeneous 1)
    (i : ℕ) : homComponent i x = if i = 1 then x else 0 := by
  refine ext fun p ↦ ?_
  rw [homComponent_apply]
  by_cases hp : p = i
  · subst hp
    by_cases hi : p = 1
    · rw [ite_eq_left rfl, ite_eq_left hi]
    · rw [ite_eq_left rfl, ite_eq_right hi, hx p hi]; rfl
  · rw [ite_eq_right hp]
    by_cases hi : i = 1
    · subst hi; rw [ite_eq_left rfl, hx p hp]
    · rw [ite_eq_right hi]; rfl

/-- The homogeneous components of `1 + x` for `x` homogeneous of degree `1`. -/
theorem homComponent_one_add_of_isHomogeneous_one {x : TotalChowClass C sY}
    (hx : x.IsHomogeneous 1) (i : ℕ) :
    homComponent i (1 + x) = if i = 0 then 1 else if i = 1 then x else 0 := by
  rw [map_add, homComponent_one, homComponent_of_isHomogeneous_one hx]
  rcases i with _ | _ | i <;> simp

/-- The power sums of `1 + x` for `x` homogeneous of degree `1` are the powers of `x`:
`P_p(1 + x) = x^p` for `p ≥ 1`. -/
theorem newtonComponents_one_add_of_isHomogeneous_one {x : TotalChowClass C sY}
    (hx : x.IsHomogeneous 1) (p : ℕ) (hp : 0 < p) : newtonComponents (1 + x) p = x ^ p := by
  refine newtonPowerSum_eq_pow_of_rankOne _ x _ ?_ (fun i hi ↦ ?_) p hp
  · rw [homComponent_one_add_of_isHomogeneous_one hx, PNat.one_coe, ite_eq_right one_ne_zero,
      ite_eq_left rfl]
  · rw [homComponent_one_add_of_isHomogeneous_one hx, ite_eq_right (by omega),
      ite_eq_right (by omega)]

/-- Restriction along `h` is injective as soon as it is injective in every degree, whatever the
structure morphism the target is presented with. -/
theorem res_injective_of_forall_injective {Y' : Scheme.{u}} {sY' : Y' ⟶ C.S}
    [LocallyOfFiniteType sY'] (h : Y' ⟶ Y) [LocallyOfFiniteType h] (hs : h ≫ sY = sY')
    (hinj : ∀ p : ℕ, Function.Injective (chowCohomologyRestriction C (gysinSystemOfInvertible C)
      sY h (p : ℤ) (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C))) :
    Function.Injective (res (C := C) h hs) := by
  subst hs
  intro c d hcd
  funext p
  exact hinj p (by rw [← res_rfl_apply, ← res_rfl_apply, hcd])

/-- The component of degree `p` of a restriction depends only on the component of degree `p`. -/
theorem res_apply_congr {Y' : Scheme.{u}} {sY' : Y' ⟶ C.S} [LocallyOfFiniteType sY']
    (h : Y' ⟶ Y) [LocallyOfFiniteType h] (hs : h ≫ sY = sY') {c d : TotalChowClass C sY}
    {p : ℕ} (hcd : c p = d p) : res h hs c p = res h hs d p := by
  subst hs
  rw [res_rfl_apply, res_rfl_apply, hcd]

/-- Restriction commutes with Newton's power sums of the homogeneous components. -/
theorem res_newtonComponents {Y' : Scheme.{u}} {sY' : Y' ⟶ C.S} [LocallyOfFiniteType sY']
    (h : Y' ⟶ Y) [LocallyOfFiniteType h] (hs : h ≫ sY = sY') (c : TotalChowClass C sY) (p : ℕ) :
    res h hs (newtonComponents c p) = newtonComponents (res h hs c) p := by
  rw [newtonComponents, map_newtonPowerSum (res h hs), map_zero]
  simp only [res_homComponent]

/-- Each factor `c(P^n)^{(-1)^n}` of the total Chern class of a bounded complex is either `c(P^n)`
or an inverse of it. -/
theorem complexChernFactor_eq_totalChern_or (P : CochainComplex Y.Modules ℤ) (ρ : ℤ → ℕ)
    (hP : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n))
    (n : ℤ) :
    ((complexChernFactor C sY P ρ hP n : TotalChowClass C sY) =
        (letI := hP n; totalChern C sY (P.X n) (ρ n)) ∧ (n.negOnePow : ℤˣ) = 1) ∨
      ((letI := hP n; totalChern C sY (P.X n) (ρ n)) *
        (complexChernFactor C sY P ρ hP n : TotalChowClass C sY) = 1 ∧
        (n.negOnePow : ℤˣ) = -1) := by
  let := hP n
  rcases Int.units_eq_one_or (n.negOnePow) with h | h
  · left
    refine ⟨?_, h⟩
    simp only [complexChernFactor, h, Units.val_one, zpow_one, val_totalChernUnit]
  · right
    refine ⟨?_, h⟩
    simp only [complexChernFactor, h, Units.val_neg, Units.val_one, zpow_neg, zpow_one]
    rw [← val_totalChernUnit C sY (P.X n) (ρ n), ← Units.val_mul, mul_inv_cancel, Units.val_one]

/-- The factors of the total Chern class of a bounded complex have homogeneous component `1` in
degree `0`. -/
theorem homComponent_zero_complexChernFactor (P : CochainComplex Y.Modules ℤ) (ρ : ℤ → ℕ)
    (hP : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n))
    (n : ℤ) : homComponent 0 (complexChernFactor C sY P ρ hP n : TotalChowClass C sY) = 1 :=
  homComponent_zero_of_apply_zero (complexChernFactor_apply_zero C sY P ρ hP n)

/-- The homogeneous components of the factors of the total Chern class of a bounded complex
commute pairwise. -/
theorem commute_homComponent_complexChernFactor (P : CochainComplex Y.Modules ℤ) (ρ : ℤ → ℕ)
    (hP : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n))
    (m n : ℤ) (i j : ℕ) :
    Commute (homComponent i (complexChernFactor C sY P ρ hP m : TotalChowClass C sY))
      (homComponent j (complexChernFactor C sY P ρ hP n : TotalChowClass C sY)) := by
  let := hP m
  let := hP n
  have hc0 := homComponent_zero_totalChern C sY (P.X n) (ρ n)
  have hc0' := homComponent_zero_totalChern C sY (P.X m) (ρ m)
  have hcc : ∀ i j, Commute (homComponent i (totalChern C sY (P.X m) (ρ m)))
      (homComponent j (totalChern C sY (P.X n) (ρ n))) :=
    fun i j ↦ commute_homComponent_totalChern C sY _ _ _ _ i j
  have hfc : ∀ i j, Commute (homComponent i (totalChern C sY (P.X m) (ρ m)))
      (homComponent j (complexChernFactor C sY P ρ hP n : TotalChowClass C sY)) := by
    intro i j
    rcases complexChernFactor_eq_totalChern_or (C := C) (sY := sY) P ρ hP n with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]; exact hcc i j
    · exact (commute_homComponent_of_mul_eq_one hc0 h (fun k ↦ (hcc i k).symm) j).symm
  rcases complexChernFactor_eq_totalChern_or (C := C) (sY := sY) P ρ hP m with ⟨h, -⟩ | ⟨h, -⟩
  · rw [h]; exact hfc i j
  · exact commute_homComponent_of_mul_eq_one hc0' h (fun k ↦ hfc k j) i

/-- The power sums of the total Chern class of a bounded complex of fixed ranks are the alternating
sums of the power sums of its terms: `P_p(c(P)) = ∑_n (-1)^n P_p(c(P^n))` for `p ≥ 1`. -/
theorem newtonComponents_complexChernBounded_eq_sum (P : CochainComplex Y.Modules ℤ)
    (ρ : ℤ →₀ ℕ)
    (hP : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n))
    (p : ℕ) :
    newtonComponents (complexChernBounded C sY P ρ hP) p =
      ∑ n ∈ ρ.support, ((n.negOnePow : ℤˣ) : ℤ) •
        newtonComponents (letI := hP n; totalChern C sY (P.X n) (ρ n)) p := by
  set f : ℤ → TotalChowClass C sY := fun n ↦ (complexChernFactor C sY P ρ hP n : _) with hf
  have hprod : complexChernBounded C sY P ρ hP = ((ρ.support.sort (· ≤ ·)).map f).prod := by
    rw [complexChernBounded, complexChernProd, ← Units.coeHom_apply, map_list_prod, List.map_map]
    rfl
  have hfN : ∀ n, newtonComponents (f n) p =
      ((n.negOnePow : ℤˣ) : ℤ) • newtonComponents (let := hP n; totalChern C sY (P.X n) (ρ n))
        p := by
    intro n
    let := hP n
    rcases complexChernFactor_eq_totalChern_or (C := C) (sY := sY) P ρ hP n with ⟨h, hs⟩ | ⟨h, hs⟩
    · simp only [hf]
      rw [h, hs, Units.val_one, one_smul]
    · simp only [hf]
      rw [newtonComponents_of_mul_eq_one (homComponent_zero_totalChern C sY _ _) h
        (fun i j ↦ commute_homComponent_totalChern C sY _ _ _ _ i j), hs, Units.val_neg,
        Units.val_one, neg_one_zsmul]
  rw [hprod, newtonComponents_list_prod _
      (fun x hx ↦ by
        obtain ⟨n, -, rfl⟩ := List.mem_map.mp hx
        exact homComponent_zero_complexChernFactor P ρ hP n)
      (fun x hx z hz i j ↦ by
        obtain ⟨n, -, rfl⟩ := List.mem_map.mp hx
        obtain ⟨n', -, rfl⟩ := List.mem_map.mp hz
        exact commute_homComponent_complexChernFactor P ρ hP n n' i j), List.map_map,
    ← List.sum_toFinset _ (Finset.sort_nodup _ _), Finset.sort_toFinset]
  exact Finset.sum_congr rfl fun n _ ↦ hfN n

end TotalChowClass

/-! ### Chern roots -/

section Roots

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

/-- `c(ℒ) = 1 + c_1(ℒ)` for an invertible module `ℒ`, in the ring of total classes. -/
theorem totalChern_eq_one_add_firstChernTotal (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L] :
    letI := isFiniteLocallyFreeOfRank_one_of_isInvertible L
    totalChern C sY L 1 = 1 + TotalChowClass.firstChernTotal C sY L := by
  let := isFiniteLocallyFreeOfRank_one_of_isInvertible L
  refine TotalChowClass.ext fun p ↦ ?_
  rw [TotalChowClass.add_apply]
  rcases p with _ | _ | p
  · rw [totalChern_apply_zero, TotalChowClass.firstChernTotal_apply_of_ne C sY L (by omega),
      add_zero]
  · rw [TotalChowClass.one_apply_of_ne (by omega),
      TotalChowClass.firstChernTotal_eq_homComponent_totalChern, TotalChowClass.homComponent_apply,
      ite_eq_left rfl]
    exact (zero_add _).symm
  · rw [totalChern_apply_of_lt C sY L 1 (by omega), TotalChowClass.one_apply_of_ne (by omega),
      TotalChowClass.firstChernTotal_apply_of_ne C sY L (by omega), add_zero]

/-- The first Chern classes of two invertible modules commute. -/
theorem commute_firstChernTotal (L M : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M] :
    Commute (TotalChowClass.firstChernTotal C sY L) (TotalChowClass.firstChernTotal C sY M) := by
  let := isFiniteLocallyFreeOfRank_one_of_isInvertible L
  let := isFiniteLocallyFreeOfRank_one_of_isInvertible M
  rw [TotalChowClass.firstChernTotal_eq_homComponent_totalChern,
    TotalChowClass.firstChernTotal_eq_homComponent_totalChern]
  exact TotalChowClass.commute_homComponent_totalChern C sY _ _ _ _ 1 1

/-- If `ℰ` carries a filtration of length `r` whose successive quotients are the invertible modules
`ℒ_i`, then `c(ℰ) = ∏_i c(ℒ_i)`, the product taken in the given order, and `c(ℒ_i) = 1 + c_1(ℒ_i)`
(Stacks 02UJ in the ring of total classes). -/
theorem totalChern_eq_prod_of_hasQuotients :
    ∀ (r : ℕ) (E : Y.Modules)
      [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
      (L : Fin r → Y.Modules)
      [∀ i, AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property
        (L i)],
      HasQuotients Y r E L →
      totalChern C sY E r = (List.ofFn fun i ↦
        (letI := isFiniteLocallyFreeOfRank_one_of_isInvertible (L i);
          totalChern C sY (L i) 1)).prod := by
  intro r
  induction r with
  | zero =>
    intro E _ L _ _
    rw [totalChern_of_rank_zero]
    simp
  | succ r ih =>
    intro E _ L _ h
    obtain ⟨F, hF, f, g, w, hS, hrec⟩ := h
    have := hF
    let := isFiniteLocallyFreeOfRank_one_of_isInvertible (L 0)
    have hw : totalChern C sY E (r + 1) = totalChern C sY F r * totalChern C sY (L 0) 1 :=
      totalChern_shortExact C sY (ShortComplex.mk f g w) hS r 1
    rw [hw, (commute_totalChern C sY F (L 0) r 1).eq, ih F (fun i ↦ L i.succ) hrec,
      List.ofFn_succ, List.prod_cons]

/-- The power sums of an invertible module: `P_p(ℒ) = c_1(ℒ)^p` for `p ≥ 1`. -/
theorem newtonComponents_totalChern_of_isInvertible (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]
    (p : ℕ) (hp : 0 < p) :
    letI := isFiniteLocallyFreeOfRank_one_of_isInvertible L
    TotalChowClass.newtonComponents (totalChern C sY L 1) p =
      TotalChowClass.firstChernTotal C sY L ^ p := by
  rw [totalChern_eq_one_add_firstChernTotal]
  exact TotalChowClass.newtonComponents_one_add_of_isHomogeneous_one
    (TotalChowClass.isHomogeneous_firstChernTotal C sY L) p hp

/-- The power sums of a module filtered by invertible modules are the power sums of its Chern
roots: `P_p(∏_i c(ℒ_i)) = ∑_i c_1(ℒ_i)^p` for `p ≥ 1`. -/
theorem newtonComponents_list_prod_totalChern {r : ℕ} (L : Fin r → Y.Modules)
    [∀ i, AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property
      (L i)] (p : ℕ) (hp : 0 < p) :
    TotalChowClass.newtonComponents (List.ofFn fun i ↦
        (letI := isFiniteLocallyFreeOfRank_one_of_isInvertible (L i);
          totalChern C sY (L i) 1)).prod p =
      ∑ i, TotalChowClass.firstChernTotal C sY (L i) ^ p := by
  rw [TotalChowClass.newtonComponents_list_prod]
  · rw [List.map_ofFn, List.sum_ofFn]
    exact Finset.sum_congr rfl fun i _ ↦ newtonComponents_totalChern_of_isInvertible C sY (L i) p hp
  · intro c hc'
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc'
    let := isFiniteLocallyFreeOfRank_one_of_isInvertible (L i)
    exact TotalChowClass.homComponent_zero_totalChern C sY _ _
  · intro c hc' d hd k l
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc'
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hd
    let := isFiniteLocallyFreeOfRank_one_of_isInvertible (L i)
    let := isFiniteLocallyFreeOfRank_one_of_isInvertible (L j)
    exact TotalChowClass.commute_homComponent_totalChern C sY _ _ _ _ k l

end Roots

/-! ### Separating the even and the odd terms of an alternating product -/

/-- The sign `(-1)^n` of an even integer is `1`. -/
private theorem val_negOnePow_of_even {n : ℤ} (h : Even n) : ((n.negOnePow : ℤˣ) : ℤ) = 1 := by
  simp [Int.negOnePow_even n h]

/-- The sign `(-1)^n` of an integer that is not even is `-1`. -/
private theorem val_negOnePow_of_not_even {n : ℤ} (h : ¬ Even n) :
    ((n.negOnePow : ℤˣ) : ℤ) = -1 := by
  simp [Int.negOnePow_odd n (Int.not_even_iff_odd.mp h)]

/-- In a group, an ordered product `∏ u_n^{(-1)^n}` of pairwise commuting elements times the
product of the `u_n` with `n` odd is the product of the `u_n` with `n` even. -/
theorem list_prod_zpow_negOnePow_mul {G : Type*} [Group G] (v : ℤ → G)
    (hv : ∀ m n, Commute (v m) (v n)) (l : List ℤ) :
    (l.map fun n ↦ v n ^ ((n.negOnePow : ℤˣ) : ℤ)).prod *
        ((l.filter fun n ↦ ¬ Even n).map v).prod =
      ((l.filter fun n ↦ Even n).map v).prod := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have hcomm : Commute (t.map fun n ↦ v n ^ ((n.negOnePow : ℤˣ) : ℤ)).prod (v a) :=
      Commute.list_prod_left _ _ fun x hx ↦ by
        obtain ⟨n, -, rfl⟩ := List.mem_map.mp hx
        exact (hv n a).zpow_left _
    by_cases ha : Even a
    · rw [List.map_cons, List.prod_cons, List.filter_cons_of_neg (by simpa using ha),
        List.filter_cons_of_pos (by simpa using ha), List.map_cons, List.prod_cons,
        val_negOnePow_of_even ha, zpow_one, mul_assoc, ih]
    · rw [List.map_cons, List.prod_cons, List.filter_cons_of_pos (by simpa using ha),
        List.filter_cons_of_neg (by simpa using ha), List.map_cons, List.prod_cons,
        val_negOnePow_of_not_even ha, zpow_neg, zpow_one, ← ih, mul_assoc,
        ← mul_assoc _ (v a), hcomm.eq, mul_assoc, inv_mul_cancel_left]

/-- A module of rank `0` carries the empty filtration. -/
theorem exists_hasQuotients_of_rank_eq_zero {Y : Scheme.{u}} (M : Y.Modules) :
    ∀ (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r],
      r = 0 → ∃ L : Fin r → Y.Modules,
        (∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property
          (L j)) ∧ HasQuotients Y r M L := by
  intro r _ hr
  subst hr
  exact ⟨Fin.elim0, fun j ↦ j.elim0, isZero_of_isFiniteLocallyFreeOfRank_zero M⟩

/-! ### Split charts -/

section Component

variable {C : ChowSituation.{u}} {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  {E : DerivedCategory X.Modules}

include sX in
/-- The source of the envelope of a presentation is locally of finite type over the locally
Noetherian base, hence locally Noetherian. -/
theorem EnvelopePresentation.isLocallyNoetherian_Y (H : EnvelopePresentation E) :
    IsLocallyNoetherian H.Y :=
  LocallyOfFiniteType.isLocallyNoetherian (H.f ≫ sX)

include sX in
/-- The connected component of a point of the source of the envelope, as an open subscheme. -/
def EnvelopePresentation.componentOpens (H : EnvelopePresentation E) (y : H.Y) : H.Y.Opens :=
  ⟨connectedComponent y, by
    have := H.isLocallyNoetherian_Y sX
    exact isOpen_connectedComponent⟩

/-- The underlying set of `componentOpens` is the connected component of the point. -/
@[simp]
theorem EnvelopePresentation.coe_componentOpens (H : EnvelopePresentation E) (y : H.Y) :
    (H.componentOpens sX y : Set H.Y) = connectedComponent y :=
  rfl

/-- On a connected component of the source of the envelope the ranks of the terms of the
presenting complex are constant. -/
theorem EnvelopePresentation.complexRank_eq_of_mem_componentOpens (H : EnvelopePresentation E)
    {y z : H.Y} (hz : z ∈ H.componentOpens sX y) :
    complexRank H.locallyBounded z = complexRank H.locallyBounded y :=
  Finsupp.ext fun n ↦ by
    rw [complexRank_apply, complexRank_apply]
    exact (isLocallyConstant_fiberRank_X H.locallyBounded n).apply_eq_of_isPreconnected
      isPreconnected_connectedComponent hz mem_connectedComponent

/-- On a connected component of the source of the envelope, the presenting complex is a bounded
complex of finite locally free modules of fixed ranks: its `n`-th term has the rank of `ℰ^n` at any
point of the component. -/
theorem EnvelopePresentation.isFiniteLocallyFreeOfRank_componentOpens (H : EnvelopePresentation E)
    (y : H.Y) (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((pullbackComplex (H.componentOpens sX y).ι H.P).X n)
      (complexRank H.locallyBounded y n) := by
  let : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (H.P.X n) :=
    H.locallyBounded.1 n
  exact Scheme.Modules.isFiniteLocallyFreeOfRank_pullback_of_fiberRank_eq (H.P.X n) _ _
    fun z hz ↦ by rw [← complexRank_apply H.locallyBounded z n,
      H.complexRank_eq_of_mem_componentOpens sX hz]

end Component

section Chart

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  {E : DerivedCategory X.Modules}

/-- A split chart of an envelope presentation `(f : Y ⟶ X, ℰ^•)` of `E` at a point `y ∈ Y`:
on the connected component `V` of `y`, where `ℰ^•` is a bounded complex of finite locally free
modules of the fixed ranks `ρ = (rank_y ℰ^n)_n`, a splitting morphism `π : P ⟶ V` in the sense
of Stacks 02UL (flat, proper, of constant relative dimension, with injective flat pullback on
Chow groups) along which

* restriction of total Chow cohomology classes `A^*(V) ⟶ A^*(P)` is injective, and
* each `π^*ℰ^n` has a filtration of length `ρ n` whose successive quotients `ℒ_{n,j}` are
  invertible `𝒪_P`-modules. -/
structure SplitChart (H : EnvelopePresentation E) (y : H.Y) where
  /-- The relative dimension of the splitting morphism. -/
  d : ℕ
  /-- The splitting morphism `π : P ⟶ V` over the connected component `V` of `y`. -/
  T : SplittingMorphism C ((H.componentOpens sX y).ι ≫ H.f ≫ sX) d
  /-- The successive quotients `ℒ_{n,j}`, `j < rank_y ℰ^n`, of the filtration of `π^*ℰ^n`. -/
  L : ∀ n : ℤ, Fin (complexRank H.locallyBounded y n) → T.P.Modules
  /-- The successive quotients are invertible. -/
  isInvertible : ∀ n j, AlgebraicGeometry.SheafOfModules.IsInvertible T.P.sheaf.obj
    T.P.ringCatSheaf.property (L n j)
  /-- `π^*ℰ^n` has a filtration with the successive quotients `ℒ_{n,j}`. -/
  hasQuotients : ∀ n, HasQuotients T.P (complexRank H.locallyBounded y n)
    ((Scheme.Modules.pullback T.π).obj ((pullbackComplex (H.componentOpens sX y).ι H.P).X n))
    (L n)
  /-- Restriction of total Chow cohomology classes along `π` is injective. -/
  injective : Function.Injective (TotalChowClass.res (C := C) T.π T.hsP)

variable {C sX}

namespace SplitChart

variable {H : EnvelopePresentation E} {y : H.Y} (χ : SplitChart C sX H y)

/-- The morphism `P ⟶ V ⟶ Y ⟶ X` of a split chart. -/
def map : χ.T.P ⟶ X :=
  χ.T.π ≫ (H.componentOpens sX y).ι ≫ H.f

/-- The morphism of a split chart is locally of finite type. -/
instance : LocallyOfFiniteType χ.map := by
  unfold map
  infer_instance

/-- The morphism of a split chart followed by `sX` is the structure morphism of `P`. -/
theorem map_comp : χ.map ≫ sX = χ.T.sP := by
  rw [← χ.T.hsP, map]
  simp only [Category.assoc]

/-- Restriction to a split chart, `A^*(X) ⟶ A^*(P)`. -/
def res : TotalChowClass C sX →+* TotalChowClass C χ.T.sP :=
  TotalChowClass.res χ.map χ.map_comp

/-- Restriction to a split chart is restriction along the envelope, then to the connected
component, then along the splitting morphism. -/
theorem res_eq (c : TotalChowClass C sX) :
    χ.res c = TotalChowClass.res χ.T.π χ.T.hsP (TotalChowClass.res
      (H.componentOpens sX y).ι rfl (TotalChowClass.res H.f rfl c)) := by
  rw [TotalChowClass.res_res, TotalChowClass.res_res]
  rfl

/-- The Chern roots `x_{n,j} = c_1(ℒ_{n,j})` of a split chart. -/
def root (n : ℤ) (j : Fin (complexRank H.locallyBounded y n)) : TotalChowClass C χ.T.sP :=
  letI := χ.isInvertible n j
  TotalChowClass.firstChernTotal C χ.T.sP (χ.L n j)

/-- The factor `1 + x_{n,j}` of a split chart, the total Chern class of `ℒ_{n,j}`, as a unit of the
ring of total classes. -/
def rootFactor (n : ℤ) (j : Fin (complexRank H.locallyBounded y n)) :
    (TotalChowClass C χ.T.sP)ˣ :=
  letI := χ.isInvertible n j
  letI := isFiniteLocallyFreeOfRank_one_of_isInvertible (χ.L n j)
  totalChernUnit C χ.T.sP (χ.L n j) 1

/-- The underlying class of `rootFactor n j` is `1 + root n j`. -/
theorem val_rootFactor (n : ℤ) (j : Fin (complexRank H.locallyBounded y n)) :
    (χ.rootFactor n j : TotalChowClass C χ.T.sP) = 1 + χ.root n j := by
  let := χ.isInvertible n j
  rw [rootFactor, val_totalChernUnit]
  exact totalChern_eq_one_add_firstChernTotal C χ.T.sP (χ.L n j)

end SplitChart

/-- Split charts exist at every point of the source of the envelope of a presentation. -/
theorem nonempty_splitChart (H : EnvelopePresentation E) (y : H.Y) :
    Nonempty (SplitChart C sX H y) := by
  set V := H.componentOpens sX y
  set ρ := complexRank H.locallyBounded y
  have hρ := H.isFiniteLocallyFreeOfRank_componentOpens sX y
  obtain ⟨T, -, -, -, -, hfilt, hinj⟩ := exists_splittingMorphism_isProjective C
    (V.ι ≫ H.f ≫ sX) {n // n ∈ ρ.support} (fun n ↦ (pullbackComplex V.ι H.P).X n.1)
    (fun n ↦ ρ n.1) (fun n ↦ hρ n.1)
  have hM : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback T.π).obj ((pullbackComplex V.ι H.P).X n)) (ρ n) := fun n ↦
    let := hρ n
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback T.π _ (ρ n)
  have hq : ∀ n, ∃ L : Fin (ρ n) → T.P.Modules,
      (∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible T.P.sheaf.obj T.P.ringCatSheaf.property
        (L j)) ∧
      HasQuotients T.P (ρ n) ((Scheme.Modules.pullback T.π).obj ((pullbackComplex V.ι H.P).X n))
        L := by
    intro n
    by_cases hn : n ∈ ρ.support
    · exact exists_hasQuotients_of_hasInvertibleFiltration (hfilt ⟨n, hn⟩)
    · have := hM n
      exact exists_hasQuotients_of_rank_eq_zero _ (ρ n) (Finsupp.notMem_support_iff.mp hn)
  choose L hL hLq using hq
  refine ⟨⟨_, T, L, hL, hLq, TotalChowClass.res_injective_of_forall_injective T.π T.hsP
    fun p a b hab ↦ ?_⟩⟩
  have h := hinj (gysinSystemOfInvertible C) (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (a₁ := DirectSum.of _ (p : ℤ) a) (a₂ := DirectSum.of _ (p : ℤ) b)
  simp only [chowCohomologyTotalRestriction, DirectSum.map_of, hab] at h
  exact DirectSum.of_injective (p : ℤ) (h trivial)

/-- Let `(f : Y ⟶ X, ℰ^•)` be an envelope presentation of `E` and choose a split chart at every
point of `Y`. Two total Chow cohomology classes on `X` whose restrictions to all the charts agree
are equal. -/
theorem eq_of_forall_splitChart_res_eq (H : EnvelopePresentation E)
    (χ : ∀ y : H.Y, SplitChart C sX H y) {a b : TotalChowClass C sX}
    (h : ∀ y, (χ y).res a = (χ y).res b) : a = b := by
  have := H.isLocallyNoetherian_Y sX
  let rep : _root_.ConnectedComponents H.Y → H.Y :=
    Function.surjInv _root_.ConnectedComponents.surjective_coe
  have hrep : ∀ i, (rep i : _root_.ConnectedComponents H.Y) = i :=
    Function.surjInv_eq _root_.ConnectedComponents.surjective_coe
  have hU : IsClopenDecomposition fun i ↦ H.componentOpens sX (rep i) :=
    { disjoint := fun i j hij ↦ TopologicalSpace.Opens.coe_disjoint.mp
        (connectedComponent_disjoint fun he ↦ hij (by
          rw [← hrep i, ← hrep j]
          exact _root_.ConnectedComponents.coe_eq_coe.mpr he))
      iSup_eq_top := top_le_iff.mp fun z _ ↦ TopologicalSpace.Opens.mem_iSup.mpr
        ⟨(z : _root_.ConnectedComponents H.Y), by
          change z ∈ connectedComponent (rep z)
          rw [_root_.ConnectedComponents.coe_eq_coe.mp (hrep z)]
          exact mem_connectedComponent⟩ }
  refine TotalChowClass.res_injective_of_isEnvelope H.f H.envelope rfl ?_
  refine TotalChowClass.eq_of_res_eq hU fun i ↦ (χ (rep i)).injective ?_
  rw [← SplitChart.res_eq, ← SplitChart.res_eq, h]

namespace SplitChart

variable {H : EnvelopePresentation E} {y : H.Y} (χ : SplitChart C sX H y)

/-- The ranks of the terms of the presenting complex on a split chart. -/
theorem isFiniteLocallyFreeOfRank_pullback (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback χ.T.π).obj
        ((pullbackComplex (H.componentOpens sX y).ι H.P).X n))
      (complexRank H.locallyBounded y n) :=
  let := H.isFiniteLocallyFreeOfRank_componentOpens sX y n
  AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback χ.T.π _ _

/-- The restriction of `c(E)` to a split chart is the total Chern class of the pullback of the
presenting complex, a bounded complex of fixed ranks. -/
theorem res_perfectChernClass_eq_complexChernBounded (hE : HasDefinedChernClasses E) :
    χ.res (perfectChernClass C sX hE) = complexChernBounded C χ.T.sP
      (pullbackComplex χ.T.π (pullbackComplex (H.componentOpens sX y).ι H.P))
      (complexRank H.locallyBounded y)
      (isFiniteLocallyFreeOfRank_pullbackComplex_X _ χ.T.π _
        (H.isFiniteLocallyFreeOfRank_componentOpens sX y)) := by
  rw [χ.res_eq, Stacks.Chow.res_perfectChernClass C sX hE H,
    res_complexChern_eq_complexChernBounded C (H.f ≫ sX) H.locallyBounded
      (H.componentOpens sX y).ι rfl _ (H.isFiniteLocallyFreeOfRank_componentOpens sX y),
    TotalChowClass.res_complexChernBounded]

/-- `c(π^*ℰ^n) = ∏_j (1 + x_{n,j})` on a split chart. -/
theorem list_prod_rootFactor (n : ℤ) :
    (List.ofFn (χ.rootFactor n)).prod =
      (letI := χ.isFiniteLocallyFreeOfRank_pullback n;
        totalChernUnit C χ.T.sP ((Scheme.Modules.pullback χ.T.π).obj
          ((pullbackComplex (H.componentOpens sX y).ι H.P).X n))
          (complexRank H.locallyBounded y n)) := by
  let := χ.isFiniteLocallyFreeOfRank_pullback n
  let := χ.isInvertible n
  refine Units.ext ?_
  rw [val_totalChernUnit, totalChern_eq_prod_of_hasQuotients C χ.T.sP _ _ (χ.L n)
    (χ.hasQuotients n), ← Units.coeHom_apply, map_list_prod, List.map_ofFn]
  rfl

/-- The Chern roots of `c(E)` on a split chart, Remark 0FAD: with `x_{n,j} = c_1(ℒ_{n,j})`,

  `c(E)|_P = ∏_{n even} ∏_j (1 + x_{n,j}) · (∏_{n odd} ∏_j (1 + x_{n,j}))^{-1}`,

the products over the degrees taken in increasing order (all the factors commute). -/
theorem res_perfectChernClass (hE : HasDefinedChernClasses E) :
    χ.res (perfectChernClass C sX hE) =
      ↑(((((complexRank H.locallyBounded y).support.sort (· ≤ ·)).filter fun n ↦ Even n).map
          fun n ↦ (List.ofFn (χ.rootFactor n)).prod).prod *
        (((((complexRank H.locallyBounded y).support.sort (· ≤ ·)).filter fun n ↦ ¬ Even n).map
          fun n ↦ (List.ofFn (χ.rootFactor n)).prod).prod)⁻¹) := by
  rw [χ.res_perfectChernClass_eq_complexChernBounded, complexChernBounded, complexChernProd]
  congr 1
  refine eq_mul_inv_of_mul_eq ?_
  have hv : ∀ m n, Commute (List.ofFn (χ.rootFactor m)).prod (List.ofFn (χ.rootFactor n)).prod := by
    intro m n
    rw [χ.list_prod_rootFactor, χ.list_prod_rootFactor]
    let := χ.isFiniteLocallyFreeOfRank_pullback m
    let := χ.isFiniteLocallyFreeOfRank_pullback n
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, val_totalChernUnit, val_totalChernUnit]
    exact commute_totalChern C χ.T.sP _ _ _ _
  have hfac : complexChernFactor C χ.T.sP
      (pullbackComplex χ.T.π (pullbackComplex (H.componentOpens sX y).ι H.P))
      (complexRank H.locallyBounded y)
      (isFiniteLocallyFreeOfRank_pullbackComplex_X _ χ.T.π _
        (H.isFiniteLocallyFreeOfRank_componentOpens sX y)) =
      fun n ↦ (List.ofFn (χ.rootFactor n)).prod ^ ((n.negOnePow : ℤˣ) : ℤ) := by
    funext n
    rw [χ.list_prod_rootFactor]
    rfl
  rw [hfac]
  exact list_prod_zpow_negOnePow_mul _ hv _

/-- The power sums of `E` on a split chart, Remark 0FAD: with `x_{n,j} = c_1(ℒ_{n,j})`,
`P_p(E)|_P = ∑_n (-1)^n ∑_j x_{n,j}^p`, for every `p ≥ 0`. -/
theorem res_perfectPowerSum_eq_sum (hE : HasDefinedChernClasses E) (p : ℕ) :
    χ.res (perfectPowerSum C sX hE p) =
      ∑ n ∈ (complexRank H.locallyBounded y).support,
        ((n.negOnePow : ℤˣ) : ℤ) • ∑ j, χ.root n j ^ p := by
  rcases p with _ | p
  · rw [perfectPowerSum_zero, χ.res_eq, Stacks.Chow.res_perfectRankClass C sX hE H,
      TotalChowClass.res_res]
    rcases isEmpty_or_nonempty χ.T.P with hP | hP
    · have := TotalChowClass.subsingleton_of_isEmpty χ.T.sP
      exact Subsingleton.elim _ _
    have hσ : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((pullbackComplex (χ.T.π ≫ (H.componentOpens sX y).ι) H.P).X n)
        (complexRank H.locallyBounded y n) := fun n ↦
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
        ((Scheme.Modules.pullbackComp χ.T.π (H.componentOpens sX y).ι).app (H.P.X n))
        (χ.isFiniteLocallyFreeOfRank_pullback n)
    rw [res_complexRankClass_of_constant_rank C (H.f ≫ sX) H.locallyBounded _ _ _ hσ,
      finsum_eq_sum_of_support_subset (s := (complexRank H.locallyBounded y).support) _
        (fun n hn ↦ by
          rw [Function.mem_support] at hn
          rw [Finset.mem_coe, Finsupp.mem_support_iff]
          intro h0
          exact hn (by rw [h0]; simp)), Finset.sum_smul]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    simp only [pow_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_smul,
      natCast_zsmul]
  · rw [perfectPowerSum, AlgebraicGeometry.map_newtonPowerSum χ.res,
      AlgebraicGeometry.newtonPowerSum_eq_of_pos _ 0 _ (p + 1) (by omega)]
    have hc : (fun i : ℕ+ ↦ χ.res (TotalChowClass.homComponent (i : ℕ)
        (perfectChernClass C sX hE))) =
        fun i : ℕ+ ↦ TotalChowClass.homComponent (i : ℕ) (χ.res (perfectChernClass C sX hE)) :=
      funext fun i ↦ TotalChowClass.res_homComponent _ _ _ _
    rw [hc]
    change TotalChowClass.newtonComponents (χ.res (perfectChernClass C sX hE)) (p + 1) = _
    rw [χ.res_perfectChernClass_eq_complexChernBounded,
      TotalChowClass.newtonComponents_complexChernBounded_eq_sum]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    congr 1
    let := χ.isInvertible n
    let := χ.isFiniteLocallyFreeOfRank_pullback n
    change TotalChowClass.newtonComponents (totalChern C χ.T.sP ((Scheme.Modules.pullback χ.T.π).obj
      ((pullbackComplex (H.componentOpens sX y).ι H.P).X n)) (complexRank H.locallyBounded y n))
      (p + 1) = _
    rw [totalChern_eq_prod_of_hasQuotients C χ.T.sP _ _ (χ.L n) (χ.hasQuotients n)]
    exact newtonComponents_list_prod_totalChern C χ.T.sP (χ.L n) (p + 1) (by omega)

/-- The power sums of `E` on a split chart, Remark 0FAD in the form of the source: with
`x_{n,j} = c_1(ℒ_{n,j})`,

  `P_p(E)|_P = ∑_{n even} ∑_j x_{n,j}^p - ∑_{n odd} ∑_j x_{n,j}^p`,

for every `p ≥ 0` (for `p = 0` both sides are the rank `∑_n (-1)^n rank(ℰ^n)`). -/
theorem res_perfectPowerSum (hE : HasDefinedChernClasses E) (p : ℕ) :
    χ.res (perfectPowerSum C sX hE p) =
      (∑ n ∈ (complexRank H.locallyBounded y).support with Even n, ∑ j, χ.root n j ^ p) -
        ∑ n ∈ (complexRank H.locallyBounded y).support with ¬ Even n, ∑ j, χ.root n j ^ p := by
  rw [χ.res_perfectPowerSum_eq_sum hE p,
    ← Finset.sum_filter_add_sum_filter_not _ (fun n : ℤ ↦ Even n), sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  congr 1 <;> refine Finset.sum_congr rfl fun n hn ↦ ?_
  · rw [val_negOnePow_of_even (Finset.mem_filter.mp hn).2, one_smul]
  · rw [val_negOnePow_of_not_even (Finset.mem_filter.mp hn).2, neg_one_zsmul]

end SplitChart

/-! ### The splitting principle -/

/-- Let `(S, δ)`, `X` and `E` be as in Definition 0F9E, the Chern classes of `E` being defined,
and choose an envelope `f : Y ⟶ X` and a locally bounded complex `ℰ^•` of finite locally free
`𝒪_Y`-modules representing `Lf^*E`. Then there is a split chart `π_y : P_y ⟶ V_y` at every point
`y ∈ Y`: over the connected component `V_y` of `y`, where `ℰ^•` is a bounded complex of finite
locally free modules of fixed ranks, `π_y` is the splitting morphism of Stacks 02UL, along which
each `ℰ^n` acquires a filtration with invertible successive quotients `ℒ_{n,j}`. For such a
choice of charts:

1. a relation between total Chow cohomology classes on `X` — in particular between the classes
   `c_p(E)` and `P_p(E)` — may be checked after restriction to all the charts: restriction
   `A^*(X) ⟶ ∏_y A^*(P_y)` is injective;
2. with `x_{n,j} = c_1(ℒ_{n,j})`, on each chart
   `c(E) = ∏_{n even} ∏_j (1 + x_{n,j}) · (∏_{n odd} ∏_j (1 + x_{n,j}))^{-1}`, the factor
   `1 + x_{n,j} = c(ℒ_{n,j})` being a unit;
3. with `x_{n,j} = c_1(ℒ_{n,j})`, on each chart
   `P_p(E) = ∑_{n even} ∑_j x_{n,j}^p - ∑_{n odd} ∑_j x_{n,j}^p` for every `p ≥ 0`.

Here `c(E)` and `P_p(E)` are the classes of Definition 0F9E (2). -/
@[stacks 0FAD "the splitting principle: for every envelope f : Y -> X and complex E^bullet \
representing Lf^*E there are split charts (the connected component of each point of Y, where \
E^bullet is bounded of fixed ranks, followed by the splitting morphism of 02UL filtering each \
term by invertible modules L_{n,j}), restriction to all of them is injective on A^*(X), and on \
them c(E) = prod_{n even} (1 + x_{n,j}) prod_{n odd} (1 + x_{n,j})^{-1} and P_p(E) = \
sum_{n even} x_{n,j}^p - sum_{n odd} x_{n,j}^p with x_{n,j} = c_1(L_{n,j})"]
theorem exists_splitCharts (hE : HasDefinedChernClasses E) (H : EnvelopePresentation E) :
    ∃ χ : ∀ y : H.Y, SplitChart C sX H y,
      Function.Injective (fun (c : TotalChowClass C sX) (y : H.Y) ↦ (χ y).res c) ∧
      (∀ y n j, ((χ y).rootFactor n j : TotalChowClass C (χ y).T.sP) = 1 + (χ y).root n j) ∧
      (∀ y, (χ y).res (perfectChernClass C sX hE) =
        ↑(((((complexRank H.locallyBounded y).support.sort (· ≤ ·)).filter fun n ↦ Even n).map
            fun n ↦ (List.ofFn ((χ y).rootFactor n)).prod).prod *
          (((((complexRank H.locallyBounded y).support.sort (· ≤ ·)).filter
            fun n ↦ ¬ Even n).map fun n ↦ (List.ofFn ((χ y).rootFactor n)).prod).prod)⁻¹)) ∧
      ∀ y (p : ℕ), (χ y).res (perfectPowerSum C sX hE p) =
        (∑ n ∈ (complexRank H.locallyBounded y).support with Even n,
            ∑ j, (χ y).root n j ^ p) -
          ∑ n ∈ (complexRank H.locallyBounded y).support with ¬ Even n,
            ∑ j, (χ y).root n j ^ p := by
  let χ : ∀ y : H.Y, SplitChart C sX H y := fun y ↦ (nonempty_splitChart H y).some
  exact ⟨χ, fun a b hab ↦ eq_of_forall_splitChart_res_eq H χ fun y ↦ congrFun hab y,
    fun y ↦ (χ y).val_rootFactor, fun y ↦ (χ y).res_perfectChernClass hE,
    fun y p ↦ (χ y).res_perfectPowerSum hE p⟩

end Chart

end Stacks.Chow

end
