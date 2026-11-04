module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.TotalChernClass

/-!
# Chern classes of a twist by an invertible module

In the situation `Stacks.WeilCohomology.ChernSetup`, let `ℰ` be a finite locally free
`𝒪_X`-module of constant rank `r` and let `ℒ` be an invertible `𝒪_X`-module. Then
`c^A_i(ℰ ⊗ ℒ) = ∑_{j=0}^{i} binom(r - i + j, j) c^A_{i-j}(ℰ) ∪ c₁^A(ℒ)^j`.
The rank is written `r + 1` below, as in the construction of the Chern classes, which is stated
for a module of positive constant rank.

## Main results

* `Stacks.WeilCohomology.ChernSetup.chernClass_eq_of_bundleIso`: the binomial formula for a
  module `ℱ` of the same rank as `ℰ` whose projective bundle is identified with that of `ℰ` in
  such a way that the tautological class is shifted by `c₁^A(ℒ)`.
* `Stacks.WeilCohomology.ChernSetup.chernClass_tensorObj`: the same formula for `ℱ = ℰ ⊗ ℒ`.

## Implementation notes

The comparison of the two projective bundles is a hypothesis: an isomorphism
`𝐏(ℰ) ≅ 𝐏(ℰ ⊗ ℒ)` over `X` under which the first Chern class of the tautological module of
`𝐏(ℰ ⊗ ℒ)` pulls back to `c₁^A(𝒪_{𝐏(ℰ)}(1)) + p^*c₁^A(ℒ)`. The situation
`Stacks.WeilCohomology.ChernSetup` carries the projective bundle of a module as a field, with no
functoriality.

The rank of `ℰ` is constant, and that `ℰ ⊗ ℒ` again has rank `r` is a hypothesis.

The degree is restricted to `i ≤ r`. Both sides of the formula do vanish for `i > r` under the
convention that `binom(n, j)` is zero for `j > n ≥ 0`, but the upper index `r - i + j` is a
truncated natural subtraction, which realises a different convention there.

The binomial coefficient acts by `nsmul` and the sign by `zsmul`, as in
`Stacks.WeilCohomology.ChernSetup.sum_chernClass_eq_zero`, so that the scalars commute past the
classes in a ring that is not commutative.

## References

* [Stacks Project, Tag 0FI8](https://stacks.math.columbia.edu/tag/0FI8)
* [Stacks Project, Tag 0FI5](https://stacks.math.columbia.edu/tag/0FI5)
* [Stacks Project, Tag 0FI4](https://stacks.math.columbia.edu/tag/0FI4)
* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v v₁ w

namespace Stacks.WeilCohomology

/-! ### Binomial identities in a ring -/

/-- A power of a negated element, with the sign pulled out as an integer scalar. -/
private theorem neg_pow_eq_zsmul {A : Type*} [Ring A] (u : A) (n : ℕ) :
    (-u) ^ n = ((-1 : ℤ) ^ n) • u ^ n := by
  rw [neg_pow, zsmul_eq_mul]
  push_cast
  rfl

/-- **The binomial theorem for `x = (x + u) + (-u)`**, for `u` commuting with `x`: the
alternating binomial sum of the mixed powers `(x + u)^i u^{k-i}` collapses to `x^k`. -/
private theorem sum_alternating_choose_smul {A : Type*} [Ring A] {x u : A} (h : Commute x u)
    (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), ((-1 : ℤ) ^ i * (k.choose i : ℤ)) • ((x + u) ^ i * u ^ (k - i)) =
      ((-1 : ℤ) ^ k) • x ^ k := by
  have hc : Commute (x + u) (-u) := (h.add_left (Commute.refl u)).neg_right
  have hx : x + u + -u = x := by abel
  have key := hc.add_pow k
  rw [hx] at key
  rw [key, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hsign : (-1 : ℤ) ^ k * (-1 : ℤ) ^ (k - i) = (-1 : ℤ) ^ i := by
    rw [← pow_add, show k + (k - i) = i + 2 * (k - i) from by omega, pow_add, pow_mul]
    simp
  rw [neg_pow_eq_zsmul u (k - i), mul_smul_comm, smul_mul_assoc,
    (Nat.cast_commute (k.choose i) ((x + u) ^ i * u ^ (k - i))).symm.eq, ← nsmul_eq_mul,
    ← natCast_zsmul, smul_smul, smul_smul, hsign]

/-- **The substitution `x ↦ x + u` in an alternating sum of a twisted family.** Let `u` commute
with `x`, and let `a : ℕ → A` be arbitrary. Replacing `a_k` by the binomial twist
`∑_{j ≤ k} binom(R - k + j, j) u^j a_{k-j}` turns the alternating sum of the `(x + u)^i a_{R-i}`
into the alternating sum of the `x^i a_{R-i}`. No commutation of `u` with the `a_k` is assumed.
-/
private theorem sum_alternating_twist {A : Type*} [Ring A] {x u : A} (h : Commute x u)
    (a : ℕ → A) (R : ℕ) :
    ∑ i ∈ Finset.range (R + 1), ((-1 : ℤ) ^ i) • ((x + u) ^ i *
          ∑ j ∈ Finset.range (R - i + 1), (i + j).choose j • (u ^ j * a (R - i - j))) =
      ∑ k ∈ Finset.range (R + 1), ((-1 : ℤ) ^ k) • (x ^ k * a (R - k)) := by
  classical
  set F : ℕ → ℕ → A := fun i k =>
    ((-1 : ℤ) ^ i * (k.choose i : ℤ)) • ((x + u) ^ i * (u ^ (k - i) * a (R - k))) with hF
  have step1 : ∀ i ∈ Finset.range (R + 1),
      ((-1 : ℤ) ^ i) • ((x + u) ^ i *
          ∑ j ∈ Finset.range (R - i + 1), (i + j).choose j • (u ^ j * a (R - i - j)))
        = ∑ k ∈ Finset.Ico i (R + 1), F i k := by
    intro i hi
    have hiR : i ≤ R := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum, Finset.smul_sum,
      show R + 1 - i = R - i + 1 from by omega]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [hF]
    rw [show i + j - i = j from by omega, show R - (i + j) = R - i - j from by omega,
      Nat.choose_symm_add, mul_smul_comm, ← natCast_zsmul, smul_smul]
  have step3 : ∀ k ∈ Finset.range (R + 1),
      ∑ i ∈ Finset.range (k + 1), F i k = ((-1 : ℤ) ^ k) • (x ^ k * a (R - k)) := by
    intro k _
    have hterm : ∀ i, F i k
        = (((-1 : ℤ) ^ i * (k.choose i : ℤ)) • ((x + u) ^ i * u ^ (k - i))) * a (R - k) := by
      intro i
      simp only [hF]
      rw [← mul_assoc, smul_mul_assoc]
    rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.sum_mul,
      sum_alternating_choose_smul h k, smul_mul_assoc]
  rw [Finset.sum_congr rfl step1, Finset.range_eq_Ico,
    Finset.sum_Ico_Ico_comm 0 (R + 1) F, ← Finset.range_eq_Ico]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [← Finset.range_eq_Ico]
  exact step3 k hk

/-- **The binomial formula for a twisted family, from the two defining relations.** Let
`φ : A₁ ⟶ A₂` be a ring map, let `x ∈ A₂` commute with `φ t` for a central `t ∈ A₁`, and let
`cE, cF : ℕ → A₁` be families with `cE 0 = cF 0 = 1` satisfying
`∑_{k=0}^{R} (-1)^k x^k φ(cE_{R-k}) = 0` and `∑_{k=0}^{R} (-1)^k (x + φ t)^k φ(cF_{R-k}) = 0`.
If the map `(c_0, …, c_{R-1}) ↦ ∑_i (x + φ t)^i φ(c_i)` is injective, then
`cF_m = ∑_{j=0}^{m} binom(R - m + j, j) cE_{m-j} t^j` for every `m ≤ R`. -/
private theorem eq_of_alternating_relations {A₁ A₂ : Type*} [Ring A₁] [Ring A₂] (φ : A₁ →+* A₂)
    (x : A₂) (t : A₁) (ht : ∀ a : A₁, Commute t a) (hxu : Commute x (φ t))
    (cE cF : ℕ → A₁) (R : ℕ) (hcE : cE 0 = 1) (hcF : cF 0 = 1)
    (hrelE : ∑ k ∈ Finset.range (R + 1), ((-1 : ℤ) ^ k) • (x ^ k * φ (cE (R - k))) = 0)
    (hrelF : ∑ k ∈ Finset.range (R + 1),
      ((-1 : ℤ) ^ k) • ((x + φ t) ^ k * φ (cF (R - k))) = 0)
    (hinj : Function.Injective
      (fun c : Fin R → A₁ => ∑ i : Fin R, (x + φ t) ^ (i : ℕ) * φ (c i)))
    (m : ℕ) (hm : m ≤ R) :
    cF m = ∑ j ∈ Finset.range (m + 1), (R - m + j).choose j • (cE (m - j) * t ^ j) := by
  obtain ⟨B, hB⟩ : ∃ B : ℕ → A₁, ∀ n, B n =
      ∑ j ∈ Finset.range (n + 1), (R - n + j).choose j • (cE (n - j) * t ^ j) :=
    ⟨_, fun _ => rfl⟩
  rw [← hB m]
  have hd : cF 0 - B 0 = 0 := by rw [hB, hcF]; simp [hcE]
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · exact sub_eq_zero.mp hd
  have hBpull : ∀ i, i ≤ R → φ (B (R - i)) =
      ∑ j ∈ Finset.range (R - i + 1), (i + j).choose j • (φ t ^ j * φ (cE (R - i - j))) := by
    intro i hi
    rw [hB, map_sum, show R - (R - i) = i from by omega]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← ((ht (cE (R - i - j))).pow_left j).eq, map_nsmul, map_mul, map_pow]
  have hrelB : ∑ k ∈ Finset.range (R + 1),
      ((-1 : ℤ) ^ k) • ((x + φ t) ^ k * φ (B (R - k))) = 0 := by
    rwa [Finset.sum_congr rfl (fun k hk => by
      rw [hBpull k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]),
      sum_alternating_twist hxu (fun n => φ (cE n)) R]
  have hdiff : ∑ k ∈ Finset.range (R + 1),
      ((-1 : ℤ) ^ k) • ((x + φ t) ^ k * φ (cF (R - k) - B (R - k))) = 0 := by
    have hsplit : ∑ k ∈ Finset.range (R + 1),
          ((-1 : ℤ) ^ k) • ((x + φ t) ^ k * φ (cF (R - k) - B (R - k)))
        = (∑ k ∈ Finset.range (R + 1), ((-1 : ℤ) ^ k) • ((x + φ t) ^ k * φ (cF (R - k))))
          - ∑ k ∈ Finset.range (R + 1), ((-1 : ℤ) ^ k) • ((x + φ t) ^ k * φ (B (R - k))) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by rw [map_sub, mul_sub, smul_sub]
    rw [hsplit, hrelF, hrelB, sub_zero]
  have hdiff' : ∑ k ∈ Finset.range R,
      ((-1 : ℤ) ^ k) • ((x + φ t) ^ k * φ (cF (R - k) - B (R - k))) = 0 := by
    rwa [Finset.sum_range_succ, show R - R = 0 from by omega, hd, map_zero, mul_zero,
      smul_zero, add_zero] at hdiff
  have htup : (fun i : Fin R => ((-1 : ℤ) ^ (i : ℕ)) • (cF (R - (i : ℕ)) - B (R - (i : ℕ))))
      = 0 := by
    apply hinj
    simp only [Pi.zero_apply, map_zero, mul_zero, Finset.sum_const_zero]
    have hterm : ∀ i : Fin R,
        (x + φ t) ^ (i : ℕ) * φ (((-1 : ℤ) ^ (i : ℕ)) • (cF (R - (i : ℕ)) - B (R - (i : ℕ))))
          = ((-1 : ℤ) ^ (i : ℕ)) •
            ((x + φ t) ^ (i : ℕ) * φ (cF (R - (i : ℕ)) - B (R - (i : ℕ)))) :=
      fun i => by rw [map_zsmul, mul_smul_comm]
    rwa [Finset.sum_congr rfl (fun i _ => hterm i), Fin.sum_univ_eq_sum_range
      (fun k => ((-1 : ℤ) ^ k) • ((x + φ t) ^ k * φ (cF (R - k) - B (R - k)))) R]
  have hco := congrFun htup ⟨R - m, by omega⟩
  simp only [Pi.zero_apply] at hco
  rw [show R - (R - m) = m from by omega] at hco
  have hsq : ((-1 : ℤ) ^ (R - m)) * ((-1 : ℤ) ^ (R - m)) = 1 := by
    rw [← pow_add, show R - m + (R - m) = 2 * (R - m) from by omega, pow_mul]
    simp
  have hfin := congrArg (fun z : A₁ => ((-1 : ℤ) ^ (R - m)) • z) hco
  simp only [smul_zero, smul_smul, hsq, one_smul] at hfin
  exact sub_eq_zero.mp hfin

/-! ### The Chern classes of a twist -/

namespace ChernSetup

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}

/-- **The binomial formula for the Chern classes of a module whose projective bundle is that of
`ℰ` with the tautological class shifted by `c₁^A(ℒ)`.** Let `ℰ` and `ℱ` be finite locally free
`𝒪_X`-modules of the same constant rank `r + 1`, let `ℒ` be invertible, and suppose the
projective bundles `p : P ⟶ X` of `ℰ` and `p' : P' ⟶ X` of `ℱ` are isomorphic over `X` by
`g : P ≅ P'` with
`g^*c₁^A(𝒪_{P'}(1)) = c₁^A(𝒪_P(1)) + p^*c₁^A(ℒ)`. Then for `i ≤ r + 1`
`c^A_i(ℱ) = ∑_{j=0}^{i} binom(r + 1 - i + j, j) c^A_{i-j}(ℰ) ∪ c₁^A(ℒ)^j`. -/
theorem chernClass_eq_of_bundleIso (𝔄 : ChernSetup.{u, v, v₁, w} C S) (X : C)
    (E F L : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1))
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F (r + 1))
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 L)
    (g : (𝔄.bundleDatum X E r hE).bundle ≅ (𝔄.bundleDatum X F r hF).bundle)
    (hg : g.hom ≫ (𝔄.bundleDatum X F r hF).proj = (𝔄.bundleDatum X E r hE).proj)
    (htwist : 𝔄.pull g.hom
        (𝔄.c₁ (𝔄.bundleDatum X F r hF).bundle (𝔄.bundleDatum X F r hF).twistClass) =
      𝔄.c₁ (𝔄.bundleDatum X E r hE).bundle (𝔄.bundleDatum X E r hE).twistClass +
        𝔄.pull (𝔄.bundleDatum X E r hE).proj (𝔄.c₁ X (picardClassOf (S.obj X) L hL)))
    (i : ℕ) (hi : i ≤ r + 1) :
    𝔄.chernClass X F r hF i =
      ∑ j ∈ Finset.range (i + 1), (r + 1 - i + j).choose j •
        (𝔄.chernClass X E r hE (i - j) * 𝔄.c₁ X (picardClassOf (S.obj X) L hL) ^ j) := by
  have hpullcomp : ∀ c : 𝔄.A X,
      𝔄.pull g.hom (𝔄.pull (𝔄.bundleDatum X F r hF).proj c)
        = 𝔄.pull (𝔄.bundleDatum X E r hE).proj c := fun c => by
    rw [← RingHom.comp_apply, ← 𝔄.pull_comp g.hom (𝔄.bundleDatum X F r hF).proj, hg]
  have hginj : Function.Injective (𝔄.pull g.hom) := by
    intro α β hαβ
    have h1 := congrArg (𝔄.pull g.inv) hαβ
    rwa [← RingHom.comp_apply, ← RingHom.comp_apply, ← 𝔄.pull_comp g.inv g.hom, g.inv_hom_id,
      𝔄.pull_id, RingHom.id_apply, RingHom.id_apply] at h1
  have hrel : ∀ (M : (S.obj X).Modules)
      (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M (r + 1)),
      ∑ k ∈ Finset.range (r + 1 + 1), ((-1 : ℤ) ^ k) •
        (𝔄.c₁ (𝔄.bundleDatum X M r hM).bundle (𝔄.bundleDatum X M r hM).twistClass ^ k *
          𝔄.pull (𝔄.bundleDatum X M r hM).proj (𝔄.chernClass X M r hM (r + 1 - k))) = 0 :=
    fun M hM => (Fin.sum_univ_eq_sum_range _ _).symm.trans (𝔄.sum_chernClass_eq_zero X M r hM)
  have hmap : ∀ (k : ℕ) (c : 𝔄.A X),
      𝔄.pull g.hom (𝔄.c₁ (𝔄.bundleDatum X F r hF).bundle
          (𝔄.bundleDatum X F r hF).twistClass ^ k *
        𝔄.pull (𝔄.bundleDatum X F r hF).proj c) =
      (𝔄.c₁ (𝔄.bundleDatum X E r hE).bundle (𝔄.bundleDatum X E r hE).twistClass +
          𝔄.pull (𝔄.bundleDatum X E r hE).proj (𝔄.c₁ X (picardClassOf (S.obj X) L hL))) ^ k *
        𝔄.pull (𝔄.bundleDatum X E r hE).proj c := fun k c => by
    rw [map_mul, map_pow, htwist, hpullcomp]
  refine eq_of_alternating_relations (𝔄.pull (𝔄.bundleDatum X E r hE).proj)
    (𝔄.c₁ (𝔄.bundleDatum X E r hE).bundle (𝔄.bundleDatum X E r hE).twistClass)
    (𝔄.c₁ X (picardClassOf (S.obj X) L hL)) (fun a => 𝔄.c₁_central X _ a)
    (𝔄.c₁_central (𝔄.bundleDatum X E r hE).bundle _ _) (𝔄.chernClass X E r hE)
    (𝔄.chernClass X F r hF) (r + 1) (𝔄.chernClass_zero X E r hE)
    (𝔄.chernClass_zero X F r hF) (hrel E hE) ?_ ?_ i hi
  · have himg := congrArg (𝔄.pull g.hom) (hrel F hF)
    rw [map_sum, map_zero] at himg
    rw [← himg]
    exact Finset.sum_congr rfl fun k _ => by rw [map_zsmul, hmap]
  · intro c c' hcc
    refine (𝔄.bijective_bundleFormula X F r hF).injective (hginj ?_)
    simpa only [map_sum, hmap] using hcc

/-- Let `ℰ` be a finite locally free `𝒪_X`-module of constant rank `r + 1` and let `ℒ` be an
invertible `𝒪_X`-module, with `ℰ ⊗ ℒ` again of rank `r + 1`. Then for `i ≤ r + 1`
`c^A_i(ℰ ⊗ ℒ) = ∑_{j=0}^{i} binom(r + 1 - i + j, j) c^A_{i-j}(ℰ) ∪ c₁^A(ℒ)^j`,
given an isomorphism `g : 𝐏(ℰ) ≅ 𝐏(ℰ ⊗ ℒ)` over `X` under which `c₁^A(𝒪_{𝐏(ℰ ⊗ ℒ)}(1))` pulls
back to `c₁^A(𝒪_{𝐏(ℰ)}(1)) + p^*c₁^A(ℒ)`. -/
@[stacks 0FI8 "the comparison `𝐏(ℰ) ≅ 𝐏(ℰ ⊗ ℒ)` of projective bundles and its effect on the
tautological class are hypotheses, the situation carrying no functoriality of `𝐏`; the rank is
constant and that of `ℰ ⊗ ℒ` is assumed; see the module documentation"]
theorem chernClass_tensorObj (𝔄 : ChernSetup.{u, v, v₁, w} C S) (X : C)
    (E L : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1))
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 L)
    (hEL : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Modules.tensorObjRingedSpace (S.obj X) E L) (r + 1))
    (g : (𝔄.bundleDatum X E r hE).bundle ≅
      (𝔄.bundleDatum X (Scheme.Modules.tensorObjRingedSpace (S.obj X) E L) r hEL).bundle)
    (hg : g.hom ≫ (𝔄.bundleDatum X
        (Scheme.Modules.tensorObjRingedSpace (S.obj X) E L) r hEL).proj =
      (𝔄.bundleDatum X E r hE).proj)
    (htwist : 𝔄.pull g.hom
        (𝔄.c₁ (𝔄.bundleDatum X (Scheme.Modules.tensorObjRingedSpace (S.obj X) E L) r hEL).bundle
          (𝔄.bundleDatum X
            (Scheme.Modules.tensorObjRingedSpace (S.obj X) E L) r hEL).twistClass) =
      𝔄.c₁ (𝔄.bundleDatum X E r hE).bundle (𝔄.bundleDatum X E r hE).twistClass +
        𝔄.pull (𝔄.bundleDatum X E r hE).proj (𝔄.c₁ X (picardClassOf (S.obj X) L hL)))
    (i : ℕ) (hi : i ≤ r + 1) :
    𝔄.chernClass X (Scheme.Modules.tensorObjRingedSpace (S.obj X) E L) r hEL i =
      ∑ j ∈ Finset.range (i + 1), (r + 1 - i + j).choose j •
        (𝔄.chernClass X E r hE (i - j) * 𝔄.c₁ X (picardClassOf (S.obj X) L hL) ^ j) :=
  𝔄.chernClass_eq_of_bundleIso X E _ L r hE hEL hL g hg htwist i hi

end ChernSetup

end Stacks.WeilCohomology

end
