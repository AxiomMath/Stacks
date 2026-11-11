module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChernClassBivariant
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChernCapFlatPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChernCapInvertibleSubmodule
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ProjectiveBundleSegreZero

/-!
# The Chern classes of Stacks 0ERY are those of the Segre recursion

In Situation 0EDT let `X/B` be good and let `ℰ` be a finite locally free `𝒪_X`-module of rank
`r`. Stacks 0ERY characterizes the maps `c_j(ℰ) ∩ - : CH_k(X') → CH_{k-j}(X')` on a good test
space `g : X' → X` by `c₀(ℰ) ∩ α = α` and the relation

`∑_{i=0}^{r} (-1)^i c₁(𝒪_{P'}(1))^i ∩ π'^*(c_{r-i}(ℰ) ∩ α) = 0`

on the base change `π' : P' = P ×_X X' → X'` of the projective bundle `π : P → X` of `ℰ`
(`AlgebraicGeometry.Space.chernCap`, from which the classes `c_j(ℰ) ∈ A^j(X)` of Stacks 0ERZ are
made, `AlgebraicGeometry.Space.chernClass`). The proof of Stacks 0ERY computes these maps:
capping the relation with `c₁(𝒪_{P'}(1))^m` and pushing forward to `X'`, with
`π'_*(c₁(𝒪_{P'}(1))^s ∩ π'^*β) = 0` for `s < r - 1` and `= β` for `s = r - 1` (Stacks 0ERU),
gives `c₀ = 1` and `c_n = ∑_{j<n} (-1)^{n-j+1} t_{n-j} c_j` for the Segre operations
`t_i ∩ β = π'_*(c₁(𝒪_{P'}(1))^{r-1+i} ∩ π'^*β)`. These are the operations
`AlgebraicGeometry.Space.PrivateChern.chernCap` of the module `g^*ℰ` on `CH_*(X')`, whose
projective bundle is `P'` (`AlgebraicGeometry.Space.projectiveBundlePullbackIso`). This file
proves that identification.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.eq_chernSeq_of_pushforward_relation`: the algebra of the
  proof of Stacks 0ERY, the relation pushed forward determines the classes recursively.
* `AlgebraicGeometry.Space.of_chowGroupCanonicalEquivChowGroup_chernCap`: the maps
  `AlgebraicGeometry.Space.chernCap` of Stacks 0ERY on a test space `g : X' → X` are the
  operations `AlgebraicGeometry.Space.PrivateChern.chernCap` of `g^*ℰ` on `CH_*(X')`, the Chow
  groups of Stacks 0EQ6 being identified with the summands of `CH_*(X')` by
  `AlgebraicGeometry.Space.chowGroupCanonicalEquivChowGroup`.

## References

* [Stacks Project, Tag 0ERY](https://stacks.math.columbia.edu/tag/0ERY)
* [Stacks Project, Tag 0ERZ](https://stacks.math.columbia.edu/tag/0ERZ)
* [Stacks Project, Tag 0ERU](https://stacks.math.columbia.edu/tag/0ERU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

namespace PrivateChern

/-! ### The algebra of the proof of Stacks 0ERY -/

section Algebra

variable {M : Type*} [AddCommGroup M]

/-- Powers of `-1` in `AddMonoid.End M` act as the integer powers of `-1`. -/
theorem neg_one_pow_end_apply (n : ℕ) (y : M) :
    ((-1 : AddMonoid.End M) ^ n) y = ((-1 : ℤ) ^ n) • y := by
  rw [show ((-1 : AddMonoid.End M) ^ n) = (((-1) ^ n : ℤ) : AddMonoid.End M) by push_cast; rfl,
    AddMonoid.End.intCast_apply]

/-- A finite sum of endomorphisms is evaluated pointwise. -/
theorem end_finsetSum_apply {ι : Type*} (s : Finset ι) (f : ι → AddMonoid.End M) (y : M) :
    (∑ j ∈ s, f j) y = ∑ j ∈ s, f j y :=
  AddMonoidHom.finsetSum_apply _ _ _

/-- **The relation of Stacks 0ERY, pushed forward, determines the classes.** Let
`S_e = π_*(c₁^e ∩ π^*-)` be operations on a group with `S_e = 0` for `e < d` and
`S_{d+i} = t_i`, `t₀ = 1`. If `γ₀, …, γ_{d+1}` satisfy, for every `s`,
`∑_{j=0}^{d+1} (-1)^{d+1-j} S_{d+1-j+s}(γ_j) = 0` (the relation
`∑_i (-1)^i c₁^i ∩ π^*γ_{r-i} = 0`, `r = d + 1`, capped with `c₁^s` and pushed forward), then
`γ_n = c_n(γ₀)` for the Chern sequence `c` of `t`, for every `n ≤ d + 1`. -/
theorem eq_chernSeq_of_pushforward_relation (S t : ℕ → AddMonoid.End M) (d : ℕ)
    (hlow : ∀ e < d, S e = 0) (hhigh : ∀ i, S (d + i) = t i) (ht0 : t 0 = 1) (γ : ℕ → M)
    (hrel : ∀ s : ℕ, ∑ j ∈ Finset.range (d + 2),
      ((-1 : ℤ) ^ (d + 1 - j)) • S (d + 1 - j + s) (γ j) = 0) :
    ∀ N ≤ d + 1, γ N = chernSeq t N (γ 0) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN
    cases N with
    | zero => rw [chernSeq_zero]; rfl
    | succ n =>
      have h := hrel n
      rw [← Finset.sum_subset (Finset.range_subset_range.2 (by omega : n + 2 ≤ d + 2))
        (fun j hj hj' => by
          rw [Finset.mem_range] at hj hj'
          rw [hlow _ (by omega), AddMonoid.End.zero_apply, smul_zero])] at h
      rw [Finset.sum_range_succ] at h
      have hlast : d + 1 - (n + 1) + n = d + 0 := by omega
      rw [hlast, hhigh, ht0, AddMonoid.End.one_apply] at h
      have hterm : ∀ j ∈ Finset.range (n + 1),
          ((-1 : ℤ) ^ (d + 1 - j)) • S (d + 1 - j + n) (γ j) =
            -(((-1 : ℤ) ^ (d - n)) • (((-1 : ℤ) ^ (n - j)) • t (n + 1 - j) (γ j))) := by
        intro j hj
        rw [Finset.mem_range] at hj
        rw [show d + 1 - j + n = d + (n + 1 - j) by omega, hhigh,
          show d + 1 - j = d - n + (n - j) + 1 by omega, pow_succ, pow_add, mul_neg_one,
          neg_smul, mul_smul]
      rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, ← Finset.smul_sum,
        show d + 1 - (n + 1) = d - n by omega, neg_add_eq_zero] at h
      have hc : chernSeq t (n + 1) (γ 0) =
          ∑ j ∈ Finset.range (n + 1), ((-1 : ℤ) ^ (n - j)) • t (n + 1 - j) (γ j) := by
        rw [chernSeq_succ, end_finsetSum_apply, ← Fin.sum_univ_eq_sum_range
          (fun j => ((-1 : ℤ) ^ (n - j)) • t (n + 1 - j) (γ j))]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [AddMonoid.End.coe_mul, Function.comp_apply, neg_one_pow_end_apply,
          AddMonoid.End.coe_mul, Function.comp_apply, ← ih j (by omega) (by omega)]
      rw [hc]
      have hinv : ∀ y : M, ((-1 : ℤ) ^ (d - n)) • ((-1 : ℤ) ^ (d - n)) • y = y := fun y => by
        rw [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]
      rw [← hinv (γ (n + 1)), ← h, hinv]

end Algebra

/-! ### The operations on Chow homology on classes of cycles -/

section Classes

variable (D : BaseSpaceDimensionSituation.{u})

/-- The cap product `c₁(ℒ) ∩ -` on `CH_*(X)`, as an element of the ring `AddMonoid.End CH_*(X)`,
in which its powers are taken. -/
abbrev firstChernCapChowEnd {X : D.Ambient} (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L) :
    AddMonoid.End (chowHomology.{u, u + 1} D sX hX) :=
  firstChernCapChow.{u, u + 1} D sX hX L hL

/-- **Powers of the cap product with `c₁(ℒ)` on the class of a cycle**:
`c₁(ℒ)^s ∩ [β] = [c₁(ℒ)^s ∩ β]` for `β ∈ Z_{m+s}(X)`, the cycle-level power being
`AlgebraicGeometry.Space.firstChernCapPowCycleMap`. -/
theorem firstChernCapChow_pow_of_chowClass_eq {X : D.Ambient} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L) :
    ∀ (s : ℕ) (m : ℤ) (b : CycleGroup D sX (m + s)),
      (firstChernCapChowEnd D sX hX L hL ^ s)
          (DirectSum.of _ (m + s) (chowClass.{u + 1} D sX hX (m + s) b)) =
        DirectSum.of (fun k => chowGroup.{u + 1} D sX hX k) m
          (chowClass.{u + 1} D sX hX m (firstChernCapPowCycleMap D sX hX L hL s m b))
  | 0, m, b => by
    rw [pow_zero, AddMonoid.End.one_apply]
    exact of_chowClass_congr D sX hX (by simp) _ _ rfl
  | s + 1, m, b => by
    have h : m + ((s + 1 : ℕ) : ℤ) = m + 1 + (s : ℤ) := by push_cast; ring
    have ih := firstChernCapChow_pow_of_chowClass_eq sX hX L hL s (m + 1) (cycleGroupCast D sX h b)
    rw [pow_succ', AddMonoid.End.coe_mul, Function.comp_apply,
      of_chowClass_congr D sX hX h b (cycleGroupCast D sX h b) rfl, ih]
    exact firstChernCapChow_of_chowClass D sX hX L hL m _

/-- **Proper pushforward on Chow homology on the class of a cycle**: `p_*[β] = [p_*β]`. -/
theorem properPushforwardChow_of_chowClass {X Y : D.Ambient} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) (p : X ⟶ Y) (hpB : p ≫ sY = sX)
    (hp : IsProper D.site D.base D.base_mem p) (k : ℤ) (b : CycleGroup D sX k) :
    properPushforwardChow.{u, u + 1} D sX hX sY hY p hpB hp
        (DirectSum.of _ k (chowClass.{u + 1} D sX hX k b)) =
      DirectSum.of (fun k => chowGroup.{u + 1} D sY hY k) k
        (chowClass.{u + 1} D sY hY k (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k b)) := by
  rw [properPushforwardChow_of, chowGroupProperPushforward_chowClass]

/-- **The vanishing half of Stacks 0ERU on Chow homology**, for every projective bundle datum of
fibre dimension `d`: `π_*(c₁(𝒪_P(1))^e ∩ π^*α) = 0` for `e < d`. -/
theorem ProjectiveBundleDatum.pushforwardChow_comp_twistCap_pow_comp_pullbackChow_eq_zero
    {X : D.Ambient} {sX : X ⟶ D.space} {hX : D.IsGood sX} {d : ℕ}
    (P : ProjectiveBundleDatum D sX hX d) (e : ℕ) (he : e < d) :
    P.pushforwardChow.comp ((P.twistCap.{u, u + 1} ^ e).comp P.pullbackChow) = 0 := by
  refine chowHomology_hom_ext D sX hX fun k b => ?_
  have hkm : k + (d : ℤ) = (k + d - e) + e := by ring
  change properPushforwardChow.{u, u + 1} D P.toBase P.isGood sX hX P.proj P.proj_comp P.isProper
      ((firstChernCapChowEnd D P.toBase P.isGood P.twist P.isInvertible_twist ^ e)
        (flatPullbackChow.{u, u + 1} D P.toBase P.isGood sX hX P.proj P.proj_comp d P.isFlat
          P.hasRelativeDimension (DirectSum.of _ k (chowClass.{u + 1} D sX hX k b)))) = 0
  rw [flatPullbackChow_of_chowClass_eq D P.toBase P.isGood sX hX P.proj P.proj_comp d P.isFlat
      P.hasRelativeDimension k _ hkm b,
    firstChernCapChow_pow_of_chowClass_eq D P.toBase P.isGood P.twist P.isInvertible_twist e,
    properPushforwardChow_of_chowClass,
    properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_eq_zero D sX hX P.toBase
      P.isGood P.proj P.proj_comp P.isProper.2.1.2 d P.isFlat P.hasRelativeDimension P.twist
      P.isInvertible_twist e he k _ hkm b, map_zero, map_zero]

end Classes

/-! ### The algebra with the classes indexed by `Fin (d + 2)` -/

section Datum

/-- **The relation of Stacks 0ERY, pushed forward, determines the classes**, with the classes
indexed by `Fin (d + 2)` and the relation written as in
`AlgebraicGeometry.Space.ProjectiveBundleRelation.relationSumAt`:
`∑_i (-1)^i S_{i+s}(γ_{r-i}) = 0` for every `s`, `r = d + 1`. -/
theorem eq_chernSeq_of_pushforward_relation_fin {M : Type*} [AddCommGroup M]
    (S t : ℕ → AddMonoid.End M) (d : ℕ) (hlow : ∀ e < d, S e = 0)
    (hhigh : ∀ i, S (d + i) = t i) (ht0 : t 0 = 1) (γ : Fin (d + 2) → M)
    (hrel : ∀ s : ℕ, ∑ i : Fin (d + 2), ((-1 : ℤ) ^ (i : ℕ)) • S (i + s) (γ (Fin.rev i)) = 0)
    (j : Fin (d + 2)) : γ j = chernSeq t j (γ 0) := by
  let γ' : ℕ → M := fun n => if h : n < d + 2 then γ ⟨n, h⟩ else 0
  have hγ' : ∀ i : Fin (d + 2), γ' i = γ i := fun i => by simp [γ', i.2]
  have h0 : γ' 0 = γ 0 := by simp [γ']
  have key := eq_chernSeq_of_pushforward_relation S t d hlow hhigh ht0 γ' (fun s => ?_) j
    (Nat.lt_succ_iff.mp j.2)
  · rw [hγ', h0] at key
    exact key
  · let F : Fin (d + 2) → M := fun j => ((-1 : ℤ) ^ (d + 1 - (j : ℕ))) •
      S (d + 1 - (j : ℕ) + s) (γ' j)
    calc ∑ j ∈ Finset.range (d + 2), ((-1 : ℤ) ^ (d + 1 - j)) • S (d + 1 - j + s) (γ' j)
        = ∑ j : Fin (d + 2), F j := (Fin.sum_univ_eq_sum_range
          (fun j => ((-1 : ℤ) ^ (d + 1 - j)) • S (d + 1 - j + s) (γ' j)) (d + 2)).symm
      _ = ∑ i : Fin (d + 2), F (Fin.revPerm i) := (Equiv.sum_comp Fin.revPerm F).symm
      _ = ∑ i : Fin (d + 2), ((-1 : ℤ) ^ (i : ℕ)) • S (i + s) (γ (Fin.rev i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have hi := i.2
        change ((-1 : ℤ) ^ (d + 1 - ((Fin.rev i : Fin (d + 2)) : ℕ))) •
            S (d + 1 - ((Fin.rev i : Fin (d + 2)) : ℕ) + s) (γ' (Fin.rev i)) = _
        rw [hγ', Fin.val_rev, show d + 1 - (d + 2 - ((i : ℕ) + 1)) = (i : ℕ) by omega]
      _ = 0 := hrel s

end Datum

end PrivateChern

open PrivateChern

/-! ### From the Chow groups of Stacks 0EQ6 to Chow homology -/

section Transport

variable (D : BaseSpaceDimensionSituation.{u})

/-- The inclusion of `CH_k(X)` (the Chow group of Stacks 0EQ6 at the canonical embeddings) as the
summand of degree `k` of the Chow homology `CH_*(X) = ⨁_k CH_k(X)`, through
`AlgebraicGeometry.Space.chowGroupCanonicalEquivChowGroup`. -/
def chowGroupCanonicalToChowHomology {X : D.Ambient} (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (k : ℤ) : chowGroupCanonical.{u + 1} D sX hX k →+ chowHomology.{u, u + 1} D sX hX :=
  (DirectSum.of (fun k => chowGroup.{u + 1} D sX hX k) k).comp
    (chowGroupCanonicalEquivChowGroup.{u + 1} D sX hX k).toAddMonoidHom

/-- On the class of a cycle, `chowGroupCanonicalToChowHomology` is the class in `CH_*(X)`. -/
theorem chowGroupCanonicalToChowHomology_chowClassCanonical {X : D.Ambient} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (k : ℤ) (b : CycleGroup D sX k) :
    chowGroupCanonicalToChowHomology D sX hX k (chowClassCanonical.{u + 1} D sX hX k b) =
      DirectSum.of (fun k => chowGroup.{u + 1} D sX hX k) k (chowClass.{u + 1} D sX hX k b) :=
  rfl

/-- `chowGroupCanonicalToChowHomology` does not see the transport along an equality of degrees. -/
theorem chowGroupCanonicalToChowHomology_degreeCast {X : D.Ambient} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) {a b : ℤ} (h : a = b) (x : chowGroupCanonical.{u + 1} D sX hX a) :
    chowGroupCanonicalToChowHomology D sX hX b
        (ProjectiveBundleRelation.degreeCast (fun m => chowGroupCanonical.{u + 1} D sX hX m) h x) =
      chowGroupCanonicalToChowHomology D sX hX a x := by
  subst h
  rfl

/-- `chowGroupCanonicalToChowHomology` does not see the transport
`AlgebraicGeometry.Space.chowGroupCanonicalCast`. -/
theorem chowGroupCanonicalToChowHomology_chowGroupCanonicalCast {X : D.Ambient}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) {a b : ℤ} (h : a = b)
    (x : chowGroupCanonical.{u + 1} D sX hX a) :
    chowGroupCanonicalToChowHomology D sX hX b (chowGroupCanonicalCast.{u + 1} D sX hX h x) =
      chowGroupCanonicalToChowHomology D sX hX a x := by
  obtain ⟨β, rfl⟩ : ∃ β, chowClassCanonical.{u + 1} D sX hX a β = x :=
    QuotientAddGroup.mk'_surjective _ x
  rw [chowGroupCanonicalCast_chowClassCanonical,
    chowGroupCanonicalToChowHomology_chowClassCanonical,
    chowGroupCanonicalToChowHomology_chowClassCanonical]
  exact (of_chowClass_congr D sX hX h _ _ rfl).symm

/-- **Flat pullback, read in Chow homology.** -/
theorem chowGroupCanonicalToChowHomology_flatPullbackChowMapCanonical {X Y : D.Ambient}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y)
    (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f) (m N : ℤ) (h : m + (r : ℤ) = N)
    (x : chowGroupCanonical.{u + 1} D sY hY m) :
    chowGroupCanonicalToChowHomology D sX hX N
        (flatPullbackChowMapCanonical.{u + 1} D sX hX sY hY f hbase r hflat hr m N h x) =
      flatPullbackChow.{u, u + 1} D sX hX sY hY f hbase r hflat hr
        (chowGroupCanonicalToChowHomology D sY hY m x) := by
  obtain ⟨β, rfl⟩ : ∃ β, chowClassCanonical.{u + 1} D sY hY m β = x :=
    QuotientAddGroup.mk'_surjective _ x
  rw [flatPullbackChowMapCanonical_chowClassCanonical,
    chowGroupCanonicalToChowHomology_chowClassCanonical,
    chowGroupCanonicalToChowHomology_chowClassCanonical,
    flatPullbackChow_of_chowClass_eq D sX hX sY hY f hbase r hflat hr m N h β]

/-- **The cap powers of `c₁(ℒ)`, read in Chow homology.** -/
theorem chowGroupCanonicalToChowHomology_bundleFormulaCap {X : D.Ambient} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L) (s : ℕ)
    (N m : ℤ) (h : N = m + s) (x : chowGroupCanonical.{u + 1} D sX hX N) :
    chowGroupCanonicalToChowHomology D sX hX m (bundleFormulaCap D sX hX L hL s N m h x) =
      (firstChernCapChowEnd D sX hX L hL ^ s)
        (chowGroupCanonicalToChowHomology D sX hX N x) := by
  obtain ⟨β, rfl⟩ : ∃ β, chowClassCanonical.{u + 1} D sX hX N β = x :=
    QuotientAddGroup.mk'_surjective _ x
  rw [bundleFormulaCap, AddMonoidHom.comp_apply, chowGroupCanonicalCast_chowClassCanonical,
    firstChernCapPowChowMap_chowClassCanonical,
    chowGroupCanonicalToChowHomology_chowClassCanonical,
    chowGroupCanonicalToChowHomology_chowClassCanonical,
    of_chowClass_congr D sX hX h β (cycleGroupCast D sX h β) rfl,
    firstChernCapChow_pow_of_chowClass_eq]

/-- **The relation of Stacks 0ERY, read in Chow homology**: the image in `CH_*(P)` of
`∑_{i=0}^{r} (-1)^i c₁(ℒ)^i ∩ π^*(b_{r-i})` is the same sum of the operations on Chow homology. -/
theorem chowGroupCanonicalToChowHomology_bundleRelationSumAt {Y P : D.Ambient}
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) (sP : P ⟶ D.space) (hP : D.IsGood sP) (π : P ⟶ Y)
    (hπB : π ≫ sY = sP) (n : ℕ) (hflat : IsFlat D.site D.base D.base_mem π)
    (hrel : HasRelativeDimension n D.site D.base D.base_mem π)
    (L : Modules.{u, u} D.site D.base D.base_mem P hP.1)
    (hL : IsInvertibleModule (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    (e : ℤ) (he : (n : ℤ) = e) (r : ℕ) (k : ℤ)
    (b : ∀ j : Fin (r + 1), chowGroupCanonical.{u + 1} D sY hY (k - ((j : ℕ) : ℤ))) :
    chowGroupCanonicalToChowHomology D sP hP (k - r + e)
        (bundleRelationSumAt D sY hY sP hP π hπB n hflat hrel L hL e he r k b) =
      ∑ i : Fin (r + 1), ((-1 : ℤ) ^ (i : ℕ)) •
        (firstChernCapChowEnd D sP hP L hL ^ (i : ℕ))
          (flatPullbackChow.{u, u + 1} D sP hP sY hY π hπB n hflat hrel
            (chowGroupCanonicalToChowHomology D sY hY _ (b (Fin.rev i)))) := by
  simp only [bundleRelationSumAt, ProjectiveBundleRelation.relationSumAt,
    ProjectiveBundleRelation.relationTerm, map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [chowGroupCanonicalToChowHomology_bundleFormulaCap, bundleRelationPull, bundleFormulaPull,
    chowGroupCanonicalToChowHomology_flatPullbackChowMapCanonical]

end Transport

/-! ### The maps of Stacks 0ERY are the Chern classes of the inverse image -/

section Bridge

attribute [local irreducible] AlgebraicGeometry.Space.projectiveBundle
  AlgebraicGeometry.Space.projectiveBundleProj
  AlgebraicGeometry.Space.modulePullback
  Stacks.RelativeProj.symmetricSituationOfQuasicoherent
  Stacks.RelativeProj.symmetricSituation
  Stacks.RelativeProj.Situation.relativeProj
  Stacks.RelativeProj.Data.relativeProj
  SheafOfModules.sheafifiedSymmetricAlgebra
  presheafToSheaf
  Stacks.RelativeProj.Situation.relativeProjToBase
  Stacks.RelativeProj.Data.toBase
  AlgebraicGeometry.Space.presentationOfIsAlgebraicSpace
  AlgebraicGeometry.Space.presentationOfAtlas
  AlgebraicGeometry.Space.QuasiCoherentDescent.pullbackComparison
  AlgebraicGeometry.Space.modulePullbackCompIso

variable (D : BaseSpaceDimensionSituation.{u}) {X : D.Ambient} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (E : Modules.{u, u} D.site D.base D.base_mem X hX.1)

/-- **The base change `P' = P ×_X X'` of the projective bundle of `ℰ` to a test space
`g : X' → X`**, with its projection `π' : P' → X'` and `𝒪_{P'}(1) = (g')^*𝒪_P(1)`, as a projective
bundle datum of fibre dimension `n` over `X'`, for `ℰ` of rank `n + 1`. -/
def chernTestDatum (n : ℕ) (hE : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) E (n + 1))
    {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) :
    ProjectiveBundleDatum D (g ≫ sX) hY n where
  space := pullback (chernProj D sX hX E (n + 1) hE) g
  toBase := pullback.snd (chernProj D sX hX E (n + 1) hE) g ≫ g ≫ sX
  isGood := isGood_chernTestBundle D sX hX E (n + 1) hE g hY
  proj := pullback.snd (chernProj D sX hX E (n + 1) hE) g
  proj_comp := rfl
  isProper := @isProper_projectiveBundleBaseChangeProj D X Y sX hX E
    (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank hX.1 hE) hE.isFiniteLocallyFreeOnSite g hY
  isFlat := @isFlat_projectiveBundleBaseChangeProj D X Y sX hX E
    (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank hX.1 hE) hE.isFiniteLocallyFreeOnSite g
    hY n hE
  hasRelativeDimension := @hasRelativeDimension_projectiveBundleBaseChangeProj D X Y sX hX E
    (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank hX.1 hE) hE.isFiniteLocallyFreeOnSite g
    hY n hE
  twist := chernTestTwist D sX hX E (n + 1) hE g hY
  isInvertible_twist := isInvertibleModule_chernTestTwist D sX hX E (n + 1) hE g hY

/-- **The Segre operations of `P' = P ×_X X'` are those of `g^*ℰ`**: `P'` is the projective bundle
of `g^*ℰ` (`AlgebraicGeometry.Space.projectiveBundlePullbackIso`), compatibly with the twists
(`AlgebraicGeometry.Space.projectiveBundleFiberProductTwistIso`). -/
theorem segreCap_chernTestDatum (n : ℕ) (hE : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) E (n + 1))
    {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX))
    (hrY : PrivateChern.IsFiniteLocallyFreeOfRank D (g ≫ sX) hY
      ((spaceModulePullback D hX.1 hY.1 g).obj E) (n + 1)) (i : ℕ) :
    (chernTestDatum D sX hX E n hE g hY).segreCap.{u, u + 1} i =
      (projectiveBundleDatum ((spaceModulePullback D hX.1 hY.1 g).obj E) n hrY).segreCap i := by
  have := isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank hX.1 hE
  let gs := goodSpaceHom D sX hX g hY
  let Θ := projectiveBundlePullbackIso gs E hE.isFiniteLocallyFreeOnSite
  have hiso : IsIso Θ.inv.hom :=
    ⟨⟨Θ.hom.hom, congrArg (fun f => f.hom) Θ.inv_hom_id,
      congrArg (fun f => f.hom) Θ.hom_inv_id⟩⟩
  have hφπ := projectiveBundlePullbackIso_inv_comp_proj D (X := ⟨X, hX.1⟩) E n hE gs
  let P := projectiveBundleDatum ((spaceModulePullback D hX.1 hY.1 g).obj E) n hrY
  let Q := chernTestDatum D sX hX E n hE g hY
  let f' : Q.space ⟶ P.space := Θ.inv.hom
  have hcomm : f' ≫ P.proj = Q.proj ≫ 𝟙 Y := by
    rw [Category.comp_id]
    exact hφπ
  have hiso' : IsIso f' := hiso
  have sq : IsPullback f' Q.proj P.proj (𝟙 Y) := IsPullback.of_horiz_isIso ⟨hcomm⟩
  have e : pullbackLine D Q.toBase Q.isGood P.toBase P.isGood f' P.twist ≅ Q.twist :=
    projectiveBundleFiberProductTwistIso D (X := ⟨X, hX.1⟩) E n hE gs
  exact ProjectiveBundleDatum.segreCap_eq_of_isPullback_id P Q sq e i

/-- **The maps `c_j(ℰ) ∩ -` of Stacks 0ERY on a test space are the Chern classes of the inverse
image.** For a good test space `g : X' → X` and `α ∈ CH_k(X')`, the class
`c_j(ℰ) ∩ α ∈ CH_{k-j}(X')` of Stacks 0ERY (`AlgebraicGeometry.Space.chernCap`, the cap operation
of `c_j(ℰ) ∈ A^j(X)` of Stacks 0ERZ on `X'`) is, in `CH_*(X') = ⨁_k CH_k(X')`, the operation
`AlgebraicGeometry.Space.PrivateChern.chernCap` of `g^*ℰ` applied to `α`: the proof of Stacks
0ERY, which pushes the defining relation forward after capping with powers of `c₁(𝒪_{P'}(1))`,
computes the classes recursively through the Segre operations of `P' = 𝐏(g^*ℰ)`. -/
theorem chowGroupCanonicalToChowHomology_chernCap (r : ℕ) (hE : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) E r)
    {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX))
    (hrY : PrivateChern.IsFiniteLocallyFreeOfRank D (g ≫ sX) hY
      ((spaceModulePullback D hX.1 hY.1 g).obj E) r)
    (j : Fin (r + 1)) (k : ℤ) (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY k) :
    chowGroupCanonicalToChowHomology D (g ≫ sX) hY (k - ((j : ℕ) : ℤ))
        (Space.chernCap D sX hX E r hE g hY j k α) =
      PrivateChern.chernCap.{u, u + 1} (hX := hY) ((spaceModulePullback D hX.1 hY.1 g).obj E) r
        hrY j (chowGroupCanonicalToChowHomology D (g ≫ sX) hY k α) := by
  cases r with
  | zero =>
    obtain rfl : j = 0 := Subsingleton.elim (α := Fin 1) _ _
    rw [Space.chernCap_zero, chowGroupCanonicalToChowHomology_degreeCast, Fin.val_zero,
      PrivateChern.chernCap_zero]
    rfl
  | succ n =>
    have := isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank hX.1 hE
    let Q := chernTestDatum D sX hX E n hE g hY
    let γ : Fin (n + 1 + 1) → chowHomology.{u, u + 1} D (g ≫ sX) hY := fun j =>
      chowGroupCanonicalToChowHomology D (g ≫ sX) hY _
        (Space.chernCap D sX hX E (n + 1) hE g hY j k α)
    have hT : ∑ i : Fin (n + 1 + 1), ((-1 : ℤ) ^ (i : ℕ)) • (Q.twistCap.{u, u + 1} ^ (i : ℕ))
        (Q.pullbackChow (γ (Fin.rev i))) = 0 :=
      (chowGroupCanonicalToChowHomology_bundleRelationSumAt D (g ≫ sX) hY _ Q.isGood Q.proj rfl n
        Q.isFlat Q.hasRelativeDimension Q.twist Q.isInvertible_twist _ (chernRank_sub_one n)
        (n + 1) k (fun j => Space.chernCap D sX hX E (n + 1) hE g hY j k α)).symm.trans
        ((congrArg (chowGroupCanonicalToChowHomology D Q.toBase Q.isGood _)
          (chernRelationSum_chernCap D sX hX E (n + 1) hE g hY k α)).trans (map_zero _))
    have hrel : ∀ s : ℕ, ∑ i : Fin (n + 1 + 1), ((-1 : ℤ) ^ (i : ℕ)) •
        (Q.pushforwardChow.comp ((Q.twistCap.{u, u + 1} ^ (i + s)).comp Q.pullbackChow))
          (γ (Fin.rev i)) = 0 := by
      intro s
      have h := congrArg (fun x => Q.pushforwardChow ((Q.twistCap.{u, u + 1} ^ s) x)) hT
      simp only [map_zero, map_sum, map_zsmul] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      change ((-1 : ℤ) ^ (i : ℕ)) • Q.pushforwardChow ((Q.twistCap.{u, u + 1} ^ ((i : ℕ) + s))
        (Q.pullbackChow (γ (Fin.rev i)))) = _
      rw [add_comm (i : ℕ) s, pow_add, AddMonoid.End.coe_mul, Function.comp_apply]
    have ht0 : Q.segreCap.{u, u + 1} 0 = 1 := by
      rw [segreCap_chernTestDatum D sX hX E n hE g hY hrY 0]
      exact segreCap_zero_projectiveBundleDatum _ n hrY
    have key := PrivateChern.eq_chernSeq_of_pushforward_relation_fin
      (fun e => Q.pushforwardChow.comp ((Q.twistCap.{u, u + 1} ^ e).comp Q.pullbackChow))
      Q.segreCap n
      (fun e he => ProjectiveBundleDatum.pushforwardChow_comp_twistCap_pow_comp_pullbackChow_eq_zero
        D Q e he)
      (fun i => rfl) ht0 γ hrel j
    have hQ : Q.segreCap.{u, u + 1} =
        (projectiveBundleDatum ((spaceModulePullback D hX.1 hY.1 g).obj E) n hrY).segreCap :=
      funext (segreCap_chernTestDatum D sX hX E n hE g hY hrY)
    have hγ0 : γ 0 = chowGroupCanonicalToChowHomology D (g ≫ sX) hY k α := by
      change chowGroupCanonicalToChowHomology D (g ≫ sX) hY _
        (Space.chernCap D sX hX E (n + 1) hE g hY 0 k α) = _
      rw [Space.chernCap_zero, chowGroupCanonicalToChowHomology_degreeCast]
    rw [hQ, hγ0] at key
    exact key

end Bridge

end AlgebraicGeometry.Space

end
