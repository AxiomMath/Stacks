module

public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.TensorChernRelations
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.ClosedCover
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelConstantRankGeneral

/-!
# Power sums of a tensor product of finite locally free modules

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let `ℰ`, `ℱ` be finite locally free `𝒪_X`-modules of ranks `r` and `s`.
The power sums `P_p` of Stacks 0F9B satisfy

  `P_p(ℰ ⊗ ℱ) = ∑_{p₁ + p₂ = p} C(p, p₁) · P_{p₁}(ℰ) · P_{p₂}(ℱ)`

in the ring `∏_q A^q(X)` of total Chow cohomology classes, for every `p ≥ 0`, the degree-zero
power sum being the rank. This is the identity of Stacks 0F9D, proved here with no hypothesis.

The proof is the splitting argument of the proof of Stacks 0FA6 in
`StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.TensorChernClasses`, organised as an
induction on the rank of the second factor, one invertible quotient at a time.

* If `ℱ` has rank `0` both sides vanish, and if `ℰ` and `ℱ` are both of rank one the identity is
  the binomial theorem for `c₁(ℰ ⊗ ℱ) = c₁(ℰ) + c₁(ℱ)` (Stacks 0FA6), the power sums of a module
  of rank one being the powers of its first Chern class.
* For `ℱ` of rank `m + 1`, a total class on `X` is determined by its restrictions along the
  projective bundles `π : 𝐏(g^*ℱ) ⟶ T` of the pullbacks of `ℱ` to the test schemes `g : T ⟶ X`
  (`Stacks.Chow.TotalChowClass.eq_of_res_eq_of_flat`): flat pullback along `π` is injective on
  Chow groups by the top half of Stacks 02TW, and a bivariant class commutes with it by
  Stacks 0B76. On `𝐏(g^*ℱ)` the tautological sequence `0 ⟶ 𝒦 ⟶ π^*ℱ ⟶ 𝒪(1) ⟶ 0` stays exact
  after tensoring with `π^*ℰ`, since `𝒪(1)` is flat, so the power sums being additive (Stacks
  0F9C) the identity for `(ℰ, ℱ)` follows from those for `(ℰ, 𝒦)` and `(ℰ, 𝒪(1))`.
* The identity for `(ℰ, 𝒪(1))` is the one for `(𝒪(1), ℰ)` read through the symmetry of the
  tensor product, and the latter is the case of a first factor of rank one, done first by the
  same induction.

## Main definitions

* `Stacks.Chow.PowerSumTensorFormula` — the identity of Stacks 0F9D for two modules of given
  ranks, as a proposition.

## Main results

* `Stacks.Chow.TotalChowClass.eq_of_res_eq_of_flat` — a total class is determined by its
  restrictions along flat morphisms with injective pullback over every test scheme.
* `Stacks.Chow.isNewtonPowerSums_powerSumTotal` — Newton's recursion for the power sums of a
  module.
* `Stacks.Chow.powerSumTotal_of_rank_one` — `P_p(ℒ) = c₁(ℒ)^p` for `ℒ` of rank one.
* `Stacks.Chow.powerSumTotal_sheafTensor` — the identity of Stacks 0F9D for total classes.

## References

* [Stacks Project, Tag 0F9D](https://stacks.math.columbia.edu/tag/0F9D)
* [Stacks Project, Tag 0F9C](https://stacks.math.columbia.edu/tag/0F9C)
* [Stacks Project, Tag 0FA6](https://stacks.math.columbia.edu/tag/0FA6)
* [Stacks Project, Tag 02TW](https://stacks.math.columbia.edu/tag/02TW)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Finset
open Stacks.SheafOfModules.Tensor (sheafTensor)

universe u

namespace Stacks.Chow

namespace TotalChowClass

variable {C : ChowSituation.{u}} {X : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]

/-- Two total classes with the same restriction along `h` have the same operation on `h`. -/
theorem op_eq_op_of_res_eq {Y : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
    (h : Y ⟶ X) [LocallyOfFiniteType h] (hs : h ≫ sX = sY) {c d : TotalChowClass C sX}
    (hcd : res h hs c = res h hs d) : c.op h = d.op h := by
  have h₁ := op_res h hs c (𝟙 Y)
  have h₂ := op_res h hs d (𝟙 Y)
  rw [hcd] at h₁
  have key : ∀ (m : Y ⟶ X) [LocallyOfFiniteType m], m = h → c.op m = d.op m →
      c.op h = d.op h := by
    rintro m _ rfl hm
    exact hm
  exact key (𝟙 Y ≫ h) (Category.id_comp h) (eq_of_heq (h₁.symm.trans h₂))

/-- **Descent of total classes along flat morphisms with injective pullback.** Two total classes
on `X` are equal if, over every test scheme `g : T ⟶ X`, there is a flat morphism `π : P ⟶ T`
along which flat pullback on Chow groups is injective and along whose composite with `g` the two
classes restrict to the same class. A bivariant class commutes with flat pullback (Stacks 0B76),
so the two operations on `g` agree after pullback along `π`, hence agree. -/
theorem eq_of_res_eq_of_flat {c d : TotalChowClass C sX}
    (h : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g], ∃ (P : Scheme.{u})
      (π : P ⟶ T) (_ : LocallyOfFiniteType π) (_ : Flat π) (r : ℕ)
      (hr : AlgebraicGeometry.RelativeDimension π r),
      (∀ k : ℤ, Function.Injective (flatPullbackChow C (π ≫ g ≫ sX) (g ≫ sX) π rfl r hr k
        (flatPullbackDescends C _ _ _ _ r hr k))) ∧
      res (π ≫ g) (Category.assoc π g sX) c = res (π ≫ g) (Category.assoc π g sX) d) :
    c = d := by
  refine ext_op fun {T} g _ ↦ ?_
  obtain ⟨P, π, _, _, r, hr, hinj, hres⟩ := h g
  have hop := op_eq_op_of_res_eq (π ≫ g) (Category.assoc π g sX) hres
  funext k i
  refine AddMonoidHom.ext fun x ↦ hinj (k - i) (eq_of_heq ?_)
  have hc := BivariantClass.idRule_flatPullbackChow C (gysinSystemOfInvertible C) sX (c i) g π
    r hr (π ≫ g) rfl k x
  have hd := BivariantClass.idRule_flatPullbackChow C (gysinSystemOfInvertible C) sX (d i) g π
    r hr (π ≫ g) rfl k x
  have hm : c.op (π ≫ g) (k + r) i _ = d.op (π ≫ g) (k + r) i _ :=
    congrArg (fun F ↦ F (k + r) i (flatPullbackChow C ((π ≫ g) ≫ sX) (g ≫ sX) π
      (Category.assoc π g sX).symm r hr k (flatPullbackDescends C _ _ _ _ r hr k) x)) hop
  -- flat pullback does not see how the structure morphism of its source is written
  have key : ∀ (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (e : (π ≫ g) ≫ sX = sP)
      (hb : π ≫ g ≫ sX = (π ≫ g) ≫ sX) (hb' : π ≫ g ≫ sX = sP) (n : ℤ) (hfac hfac')
      (y : chowGroup C (g ≫ sX) n),
      flatPullbackChow C ((π ≫ g) ≫ sX) (g ≫ sX) π hb r hr n hfac y ≍
        flatPullbackChow C sP (g ≫ sX) π hb' r hr n hfac' y := by
    intro sP _ e _ _ _ _ _ _
    subst e
    rfl
  exact (key _ (Category.assoc π g sX) _ rfl _ _ _ _).symm.trans
    ((hc.symm.trans ((heq_of_eq hm).trans hd)).trans (key _ (Category.assoc π g sX) _ rfl _ _ _ _))

end TotalChowClass

open TotalChowClass

/-! ### Power sums of a module -/

section PowerSum

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **Newton's recursion for the power sums of a module**: the power sums `P_p(ℰ)`, `p ≥ 1`, and
the total Chern class of `ℰ` satisfy `P_{p+1} = ∑_{j < p} (-1)^j c_{j+1} P_{p-j} +
(-1)^p (p + 1) c_{p+1}`. -/
theorem isNewtonPowerSums_powerSumTotal (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    IsNewtonPowerSums (totalChern C sX E r) (powerSumTotal C sX E r) :=
  isNewtonPowerSums_of_powerSumEval (chernSet_commute C sX) _
    (fun i ↦ Subring.subset_closure (homPart_totalChern_mem_chernSet C sX E r i)) _
    fun _ hp ↦ powerSumTotal_of_ne_zero C sX E r hp

/-- **The power sums of a module of rank one are the powers of its first Chern class**:
`P_p(ℒ) = c₁(ℒ)^p`, also for `p = 0`, where `P_0(ℒ) = 1` is the rank. -/
theorem powerSumTotal_of_rank_one (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1] (p : ℕ) :
    powerSumTotal C sX L 1 p = TotalChowClass.homComponent 1 (totalChern C sX L 1) ^ p := by
  induction p using Nat.strong_induction_on with
  | _ p ih =>
  rcases p with _ | p
  · rw [powerSumTotal_zero, Nat.cast_one, pow_zero]
  rw [isNewtonPowerSums_powerSumTotal C sX L 1 p]
  rcases p with _ | p
  · simp
  rw [homPart_totalChern_of_lt C sX L 1 (by omega : 1 < p + 1 + 1), smul_zero, add_zero,
    Finset.sum_eq_single 0]
  · rw [pow_zero, one_smul, zero_add, ih (p + 1 - 0) (by omega), Nat.sub_zero, ← pow_succ']
  · intro j _ hj
    rw [homPart_totalChern_of_lt C sX L 1 (by omega : 1 < j + 1), zero_mul, smul_zero]
  · intro h
    exact absurd (mem_range.mpr (Nat.succ_pos p)) h

/-- **Power sums of modules commute**: they lie in the commutative ring of Chern classes, or are
integers. -/
theorem commute_powerSumTotal (E F : X.Modules) (r s : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F s] (p q : ℕ) :
    Commute (powerSumTotal C sX E r p) (powerSumTotal C sX F s q) := by
  rcases eq_or_ne p 0 with rfl | hp
  · rw [powerSumTotal_zero]
    exact Nat.cast_commute _ _
  rcases eq_or_ne q 0 with rfl | hq
  · rw [powerSumTotal_zero]
    exact (Nat.cast_commute _ _).symm
  rw [powerSumTotal_of_ne_zero C sX E r hp, powerSumTotal_of_ne_zero C sX F s hq]
  unfold Commute SemiconjBy
  exact congrArg Subtype.val (mul_comm (AlgebraicGeometry.powerSumEval (chernSeq C sX E r) p)
    (AlgebraicGeometry.powerSumEval (chernSeq C sX F s) q))

end PowerSum

/-! ### The identity of Stacks 0F9D -/

section Formula

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **The identity of Stacks 0F9D** for modules `ℰ` and `ℱ` of ranks `r` and `s`:
`P_p(ℰ ⊗ ℱ) = ∑_{p₁ + p₂ = p} C(p, p₁) P_{p₁}(ℰ) P_{p₂}(ℱ)` for every `p`. -/
def PowerSumTensorFormula (E F : X.Modules) (r s : ℕ)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    [hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F s] : Prop :=
  letI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := X.ringCatSheaf) _ _ :=
      isFiniteLocallyFreeOfRank_tensor hE hF
  ∀ p : ℕ, powerSumTotal C sX (((sheafTensor X.sheaf).obj E).obj F) (r * s) p =
    ∑ q ∈ antidiagonal p,
      (p.choose q.1 : ℤ) • (powerSumTotal C sX E r q.1 * powerSumTotal C sX F s q.2)

variable {C sX} in
/-- The identity is invariant under isomorphisms of the two factors. -/
theorem PowerSumTensorFormula.of_iso {E E' F F' : X.Modules} {r s : ℕ}
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    [hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F s]
    [hE' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' r]
    [hF' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F' s]
    (e : E ≅ E') (f : F ≅ F') (h : PowerSumTensorFormula C sX E F r s) :
    PowerSumTensorFormula C sX E' F' r s := by
  let : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := X.ringCatSheaf) _ _ :=
      isFiniteLocallyFreeOfRank_tensor hE hF
  let : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := X.ringCatSheaf) _ _ :=
      isFiniteLocallyFreeOfRank_tensor hE' hF'
  intro p
  refine (powerSumTotal_congr C sX (sheafTensorMapIso e f) rfl p).symm.trans ((h p).trans ?_)
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [powerSumTotal_congr C sX e rfl q.1, powerSumTotal_congr C sX f rfl q.2]

/-- **The identity for a second factor of rank zero**: both sides vanish. -/
theorem powerSumTensorFormula_of_rank_zero (E F : X.Modules) (r : ℕ)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    [hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F 0] :
    PowerSumTensorFormula C sX E F r 0 := by
  let hT : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := X.ringCatSheaf) _ _ :=
      isFiniteLocallyFreeOfRank_tensor hE hF
  intro p
  have hT0 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := X.ringCatSheaf) (((sheafTensor X.sheaf).obj E).obj F) 0 :=
    GenuineChern.rank_of_iso (Iso.refl _) (Nat.mul_zero r) hT
  refine (powerSumTotal_congr_rank C sX _ hT hT0 p).trans
    ((powerSumTotal_of_rank_zero C sX (((sheafTensor X.sheaf).obj E).obj F) p).trans ?_)
  refine (Finset.sum_eq_zero fun q _ ↦ ?_).symm
  rw [powerSumTotal_of_rank_zero C sX F, mul_zero, smul_zero]

/-- **The identity for two factors of rank one**: by Stacks 0FA6 the first Chern class of
`ℰ ⊗ ℱ` is `c₁(ℰ) + c₁(ℱ)`, and the power sums of a module of rank one are the powers of its first
Chern class, so the identity is the binomial theorem. -/
theorem powerSumTensorFormula_one_one (E F : X.Modules)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 1]
    [hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F 1] :
    PowerSumTensorFormula C sX E F 1 1 := by
  let hT : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := X.ringCatSheaf) _ _ :=
      isFiniteLocallyFreeOfRank_tensor hE hF
  intro p
  have hT1 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := X.ringCatSheaf) (((sheafTensor X.sheaf).obj E).obj F) 1 :=
    GenuineChern.rank_of_iso (Iso.refl _) (Nat.mul_one 1) hT
  have h₁ := totalChern_sheafTensor_degree_one C sX E F 1 1
  simp only [Nat.cast_one, one_smul] at h₁
  have hc : Commute (TotalChowClass.homComponent 1 (totalChern C sX E 1))
      (TotalChowClass.homComponent 1 (totalChern C sX F 1)) :=
    chernSet_commute C sX _ (homPart_totalChern_mem_chernSet C sX E 1 1) _
      (homPart_totalChern_mem_chernSet C sX F 1 1)
  have hT' : totalChern C sX (((sheafTensor X.sheaf).obj E).obj F) 1 =
      totalChern C sX (((sheafTensor X.sheaf).obj E).obj F) (1 * 1) :=
    totalChern_congr C sX (Iso.refl _) (Nat.mul_one 1).symm
  refine (powerSumTotal_congr_rank C sX _ hT hT1 p).trans
    ((powerSumTotal_of_rank_one C sX (((sheafTensor X.sheaf).obj E).obj F) p).trans ?_)
  rw [hT', h₁, add_comm (TotalChowClass.homComponent 1 (totalChern C sX F 1)), hc.add_pow,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [powerSumTotal_of_rank_one C sX E, powerSumTotal_of_rank_one C sX F, zsmul_eq_mul,
    Int.cast_natCast, (Nat.cast_commute _ _).eq]

variable {C sX} in
/-- **The identity is symmetric in the two factors**: the tensor product is symmetric, the binomial
coefficients are symmetric and power sums of modules commute. -/
theorem PowerSumTensorFormula.symm {E F : X.Modules} {r s : ℕ}
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    [hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F s]
    (h : PowerSumTensorFormula C sX F E s r) : PowerSumTensorFormula C sX E F r s := by
  let : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := X.ringCatSheaf) _ _ :=
      isFiniteLocallyFreeOfRank_tensor hE hF
  let : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := X.ringCatSheaf) _ _ :=
      isFiniteLocallyFreeOfRank_tensor hF hE
  intro p
  have e : ((sheafTensor X.sheaf).obj E).obj F ≅ ((sheafTensor X.sheaf).obj F).obj E :=
    ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding X.sheaf).app E).app F
  refine (powerSumTotal_congr C sX e (Nat.mul_comm r s) p).trans ((h p).trans ?_)
  rw [← Finset.Nat.sum_antidiagonal_swap]
  refine Finset.sum_congr rfl fun q hq ↦ ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [(commute_powerSumTotal C sX F E s r _ _).eq,
    Nat.choose_symm_of_eq_add (hq.symm.trans (add_comm _ _))]

/-- **The identity along an extension by an invertible module.** Let `0 ⟶ 𝒦 ⟶ ℱ ⟶ ℒ ⟶ 0` be
exact with `𝒦` of rank `m` and `ℒ` invertible. The identities for `(ℰ, 𝒦)` and `(ℰ, ℒ)` give the
one for `(ℰ, ℱ)`: tensoring with `ℰ` keeps the sequence exact because `ℒ` is flat (Stacks 03EX),
and the power sums are additive (Stacks 0F9C). -/
theorem powerSumTensorFormula_of_shortExact (E : X.Modules) (r : ℕ)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (m : ℕ)
    [h₁ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ m]
    [h₂ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ (m + 1)]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property S.X₃]
    (hK : PowerSumTensorFormula C sX E S.X₁ r m)
    (hL : letI := isFiniteLocallyFreeOfRank_one_of_isInvertible S.X₃
      PowerSumTensorFormula C sX E S.X₃ r 1) :
    PowerSumTensorFormula C sX E S.X₂ r (m + 1) := by
  let h₃ := isFiniteLocallyFreeOfRank_one_of_isInvertible S.X₃
  obtain ⟨w, hT⟩ : ∃ w : ((sheafTensor X.sheaf).obj E).map S.f ≫
      ((sheafTensor X.sheaf).obj E).map S.g = 0,
      (ShortComplex.mk (((sheafTensor X.sheaf).obj E).map S.f)
        (((sheafTensor X.sheaf).obj E).map S.g) w).ShortExact :=
    ⟨_, Stacks.Sheaves.ChangeOfRings.shortExact_map_sheafTensorObj X.sheaf E S hS
      (isFlat_of_isInvertible S.X₃)⟩
  let hT₁ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := X.ringCatSheaf) _ _ :=
      isFiniteLocallyFreeOfRank_tensor hE h₁
  let hT₃ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := X.ringCatSheaf) _ _ :=
      isFiniteLocallyFreeOfRank_tensor hE h₃
  let hT₂ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := X.ringCatSheaf) _ _ :=
      isFiniteLocallyFreeOfRank_tensor hE h₂
  have hT₂' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := X.ringCatSheaf) (((sheafTensor X.sheaf).obj E).obj S.X₂) (r * m + r * 1) :=
    GenuineChern.rank_of_iso (Iso.refl _) (by ring) hT₂
  intro p
  have hadd : powerSumTotal C sX (((sheafTensor X.sheaf).obj E).obj S.X₂) (r * m + r * 1) p =
      powerSumTotal C sX (((sheafTensor X.sheaf).obj E).obj S.X₁) (r * m) p +
        powerSumTotal C sX (((sheafTensor X.sheaf).obj E).obj S.X₃) (r * 1) p :=
    powerSumTotal_eq_add_of_shortExact C sX _ hT (r * m) (r * 1) p
  refine (powerSumTotal_congr_rank C sX _ hT₂ hT₂' p).trans
    (hadd.trans ((congrArg₂ (· + ·) (hK p) (hL p)).trans ?_))
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [← smul_add, ← mul_add, powerSumTotal_eq_add_of_shortExact C sX S hS m 1 q.2]

end Formula

/-! ### The induction on the rank -/

section Induction

variable (C : ChowSituation.{u})

/-- **The inductive step, by descent along the projective bundle.** Granted the identity for all
modules of ranks `r` and `m` and of ranks `r` and `1`, it holds for modules `ℰ` of rank `r` and `ℱ`
of rank `m + 1`. Over a test scheme `g : T ⟶ X`, on the projective bundle `π : 𝐏(g^*ℱ) ⟶ T` the
tautological sequence `0 ⟶ 𝒦 ⟶ π^*g^*ℱ ⟶ 𝒪(1) ⟶ 0` has `𝒦` of rank `m`, so the identity holds
for the pullbacks of `ℰ` and `ℱ` (`Stacks.Chow.powerSumTensorFormula_of_shortExact`); it descends
along `π`, flat pullback along which is injective (the top half of Stacks 02TW). -/
theorem powerSumTensorFormula_succ (r m : ℕ)
    (ih : ∀ {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (E F : X.Modules)
      [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
      [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F m],
      PowerSumTensorFormula C sX E F r m)
    (h₁ : ∀ {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (E F : X.Modules)
      [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
      [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F 1],
      PowerSumTensorFormula C sX E F r 1)
    {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (E F : X.Modules)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    [hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F (m + 1)] :
    PowerSumTensorFormula C sX E F r (m + 1) := by
  let : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := X.ringCatSheaf) _ _ :=
      isFiniteLocallyFreeOfRank_tensor hE hF
  intro p
  refine TotalChowClass.eq_of_res_eq_of_flat fun {T} g _ ↦ ?_
  -- the projective bundle of the pullback of `ℱ` to `T`
  let hET := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank E r g
  let hFT := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F (m + 1) g
  set G := (Scheme.Modules.pullback g).obj F
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G :=
    GenuineChern.isFiniteLocallyFree_of_rank G (m + 1)
  have := GenuineChern.flat_bundleProj G m
  have := GenuineChern.locallyOfFiniteType_bundleProj G m
  have : G.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree G
  refine ⟨bundle G, bundleProj G, inferInstance, inferInstance, m + 1 - 1,
    GenuineChern.relativeDimension_bundleProj G m,
    fun k ↦ GenuineChern.pullback_injective (g ≫ sX) G (GenuineChern.topHalf C) m k, ?_⟩
  set π := bundleProj G
  set sP : bundle G ⟶ C.S := π ≫ g ≫ sX
  -- the tautological sequence `0 ⟶ 𝒦 ⟶ π^*G ⟶ 𝒪(1) ⟶ 0`
  let τ : (Scheme.Modules.pullback π).obj G ⟶ bundleTwist G :=
    Stacks.ProjectiveBundleSplitting.tautologicalMap G (bundlePieces G)
  have hτ : Epi τ := Stacks.ProjectiveBundleSplitting.epi_tautologicalMap G (bundlePieces G)
  have hE' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback π).obj ((Scheme.Modules.pullback g).obj E)) r :=
    GenuineChern.isFiniteLocallyFreeOfRank_pullback _ _ r
  have hF' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback π).obj G) (m + 1) :=
    GenuineChern.isFiniteLocallyFreeOfRank_pullback _ G (m + 1)
  have hL : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (bundleTwist G) 1 :=
    isFiniteLocallyFreeOfRank_one_of_isInvertible _
  have hK : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (kernel τ) m :=
    GenuineChern.rank_of_iso (Iso.refl _) (by omega)
      (Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi τ hτ (m + 1) 1
        hF' hL)
  let S : ShortComplex (bundle G).Modules := ShortComplex.mk (kernel.ι τ) τ (kernel.condition τ)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel τ }
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ m := hK
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ (m + 1) := hF'
  have : AlgebraicGeometry.SheafOfModules.IsInvertible (bundle G).sheaf.obj
      (bundle G).ringCatSheaf.property S.X₃ := isInvertible_bundleTwist G
  -- the identity on the bundle, for the pullbacks of `ℰ` and `ℱ`
  let hEP := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank E r (π ≫ g)
  let hFP := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F (m + 1) (π ≫ g)
  have hP : PowerSumTensorFormula C sP ((Scheme.Modules.pullback (π ≫ g)).obj E)
      ((Scheme.Modules.pullback (π ≫ g)).obj F) r (m + 1) :=
    PowerSumTensorFormula.of_iso
      (show (Scheme.Modules.pullback π).obj ((Scheme.Modules.pullback g).obj E) ≅ _ from
        (Scheme.Modules.pullbackComp π g).app E)
      (show (Scheme.Modules.pullback π).obj G ≅ _ from (Scheme.Modules.pullbackComp π g).app F)
      (powerSumTensorFormula_of_shortExact C sP _ r S hS m (ih _ _ _) (h₁ _ _ _))
  -- the two restrictions
  let := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank
    (((sheafTensor X.sheaf).obj E).obj F) (r * (m + 1)) (π ≫ g)
  let : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := (bundle G).ringCatSheaf) _ _ :=
      isFiniteLocallyFreeOfRank_tensor hEP hFP
  refine (res_powerSumTotal C sX (π ≫ g) (Category.assoc π g sX) _ (r * (m + 1)) p).trans
    (((powerSumTotal_congr C sP (sheafTensorPullbackIso (π ≫ g) E F) rfl p).trans
      (hP p)).trans ?_)
  rw [map_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [map_zsmul, map_mul, res_powerSumTotal, res_powerSumTotal]

/-- **The identity for a first factor of rank one**, by induction on the rank of the second. -/
theorem powerSumTensorFormula_one_left (s : ℕ) {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (E F : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 1]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F s] :
    PowerSumTensorFormula C sX E F 1 s := by
  induction s generalizing X with
  | zero => exact powerSumTensorFormula_of_rank_zero C sX E F 1
  | succ m ih =>
    exact powerSumTensorFormula_succ C 1 m (fun sX _ E F _ _ ↦ ih sX E F)
      (fun sX _ E F _ _ ↦ powerSumTensorFormula_one_one C sX E F) sX E F

/-- **The identity for a second factor of rank one**, by symmetry. -/
theorem powerSumTensorFormula_one_right (r : ℕ) {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (E F : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F 1] :
    PowerSumTensorFormula C sX E F r 1 :=
  (powerSumTensorFormula_one_left C r sX F E).symm

/-- **The identity of Stacks 0F9D for all ranks**, by induction on the rank of the second
factor. -/
theorem powerSumTensorFormula (r s : ℕ) {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (E F : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F s] :
    PowerSumTensorFormula C sX E F r s := by
  induction s generalizing X with
  | zero => exact powerSumTensorFormula_of_rank_zero C sX E F r
  | succ m ih =>
    exact powerSumTensorFormula_succ C r m (fun sX _ E F _ _ ↦ ih sX E F)
      (fun sX _ E F _ _ ↦ powerSumTensorFormula_one_right C r sX E F) sX E F

end Induction

/-! ### Stacks 0F9D -/

section Main

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (E F : X.Modules) (r s : ℕ)
  [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
  [hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F s]

/-- **The power sums of a tensor product of finite locally free modules**, Stacks 0F9D. For `ℰ`
and `ℱ` finite locally free of ranks `r` and `s` on `X` locally of finite type over `S`,

  `P_p(ℰ ⊗ ℱ) = ∑_{p₁ + p₂ = p} C(p, p₁) P_{p₁}(ℰ) P_{p₂}(ℱ)`

in the ring of total Chow cohomology classes of `X`, for every `p ≥ 0`, where `P_0` is the rank.
-/
theorem powerSumTotal_sheafTensor (p : ℕ) :
    letI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (R := X.ringCatSheaf) _ _ :=
        isFiniteLocallyFreeOfRank_tensor hE hF
    powerSumTotal C sX (((sheafTensor X.sheaf).obj E).obj F) (r * s) p =
      ∑ q ∈ antidiagonal p,
        (p.choose q.1 : ℤ) • (powerSumTotal C sX E r q.1 * powerSumTotal C sX F s q.2) :=
  powerSumTensorFormula C r s sX E F p

end Main

end Stacks.Chow

end
