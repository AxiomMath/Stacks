module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.GysinAtInfinityRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.ModificationProduct
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.BabyCaseLemmas

/-!
# Newton's identities for the classes `P'_p(Q)` and `c'_p(Q)` of Stacks 0F9K

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `Z ⊆ X` be a closed subscheme, let `b : W ⟶ 𝐏¹_X` be proper and an
isomorphism over `𝐀¹_X`, let `Q ∈ D(𝒪_W)` have defined Chern classes and let `T ⊆ W_∞` be a
closed subscheme containing every point of `W_∞` lying over `X ∖ Z` such that `Q|_T` is zero.
Stacks 0FAX: in `A^*(Z ⟶ X)`, with the multiplication of Stacks 0FA0,

  `P'_1(Q) = c'_1(Q)`,
  `P'_2(Q) = c'_1(Q)² - 2c'_2(Q)`,
  `P'_3(Q) = c'_1(Q)³ - 3c'_1(Q)c'_2(Q) + 3c'_3(Q)`,
  `P'_4(Q) = c'_1(Q)⁴ - 4c'_1(Q)²c'_2(Q) + 4c'_1(Q)c'_3(Q) + 2c'_2(Q)² - 4c'_4(Q)`,

and so on. The classes `c'_p(Q)` are defined for every `p ≥ 1` because the zero module has rank
`< 1`.

## The proof

The source shows that the multiplication of Remark 0FA0 on the classes `a_p = c'_p(Q)` agrees
with the one on the classes `b_p = c'_p(Q|_E)` of Stacks 0F9H, pushed forward along `E ⟶ Z` after
composition with the class `C` of Stacks 0F9J, using Stacks 0FA1 and 0FAV. Here this is done for
every pair of classes `q₁, q₂ ∈ A^*(W)` vanishing over `T`
(`Stacks.Chow.IsLocalizedModificationClass.supportedMul`): `res(q₁') ∘ q₂' = (q₁ q₂)'`. By
Stacks 0FA1 the left side is `q₁' ∘ (Z ⟶ X)_* ∘ q₂' = q₁' ∘ i_0^* q₂`, and
`q₁' ∘ i_0^* q₂ = (E ⟶ Z)_* ∘ (q₁|_E)' ∘ C ∘ i_0^* q₂ = (E ⟶ Z)_* ∘ (q₁|_E)' ∘ q₂|_{W_∞} ∘ C`
by the general form of the second equality of Stacks 0FAV
(`Stacks.Chow.gysinAtInfinityClass_comp_modificationZeroRestriction_heq`). Newton's identities
for `P_p(Q)` and `c_p(Q)` on `W` (Stacks 0FAD, `Stacks.Chow.isNewtonPowerSums_perfectPowerSum`)
therefore pass to the localized classes.

## Main results

* `Stacks.Chow.commutesAtInfinity_gysinAtInfinityData` — the class of Stacks 0F9J commutes with
  every restriction to the section at zero, in the sense used by the products of localized
  classes.
* `Stacks.Chow.modificationPowerSum_succ` — **Stacks 0FAX**, Newton's recursion.
* `Stacks.Chow.modificationPowerSum_first_four` — **Stacks 0FAX**, the four displayed identities.

## Implementation notes

As for Stacks 0FAK (`Stacks.Chow.closedCoverPowerSum_succ`), the "and so on" of the source is
Newton's recursion `P'_{p+1} = ∑_{j<p} (-1)^j c'_{j+1} P'_{p-j} + (-1)^p (p+1) c'_{p+1}`, which
determines `P'_p` as the universal power-sum polynomial in the `c'_i`; the products are the third
multiplication `(c, c') ↦ res(c) ∘ c'` of Stacks 0FA0 (`Stacks.Chow.supportedMul`), bracketed to
the right and read in the degree of the left side.

## References

* [Stacks Project, Tag 0FAX](https://stacks.math.columbia.edu/tag/0FAX)
* [Stacks Project, Tag 0F9K](https://stacks.math.columbia.edu/tag/0F9K)
* [Stacks Project, Tag 0FA0](https://stacks.math.columbia.edu/tag/0FA0)
* [Stacks Project, Tag 0FA1](https://stacks.math.columbia.edu/tag/0FA1)
* [Stacks Project, Tag 0FAV](https://stacks.math.columbia.edu/tag/0FAV)
* [Stacks Project, Tag 0FAD](https://stacks.math.columbia.edu/tag/0FAD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

variable (C : ChowSituation.{u}) {X W Z T : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))

/-- The class at infinity of Stacks 0F9J commutes with the restriction of every class
`q ∈ A^r(W)` to the section at zero: `C ∘ i_0^* q = q|_{W_∞} ∘ C`. -/
theorem commutesAtInfinity_gysinAtInfinityData {r : ℤ}
    (q : chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f) r) :
    CommutesAtInfinity (gysinAtInfinityData C f b hA) q :=
  gysinAtInfinityClass_comp_modificationZeroRestriction_heq C f b hA q

variable (z : Z ⟶ X) [IsClosedImmersion z] (t : T ⟶ modificationFibreAtInfinity f b)
  [IsClosedImmersion t] {Q : DerivedCategory W.Modules} (hQ : HasDefinedChernClasses Q)
  (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
  (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
    (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q))

/-- The class `c'_p(Q)` of Stacks 0F9K for `p ≥ 1`, when `Q|_T` is zero: the zero module has rank
`< p`. -/
abbrev modificationChernClassOfIsZero (p : ℕ) (hp : 0 < p) :
    BivariantClass C (gysinSystemOfInvertible C) (z ≫ f) f z rfl p :=
  modificationChernClass C f b hA z t hQ p hT
    (exists_isFiniteLocallyFreeOfRankLT_of_isZero (t ≫ modificationInclusionAtInfinity f b) hzero
      hp)

/-- The Chern classes `c_i(Q)` of `Q` on `W` vanish over `T` for `i ≥ 1` when `Q|_T` is zero. -/
private theorem vanishesOver_perfectChernClass_of_isZero {Q : DerivedCategory W.Modules}
    (hQ : HasDefinedChernClasses Q)
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q)) {i : ℕ} (hi : 0 < i) :
    BivariantClass.VanishesOver (perfectChernClass C (modificationProjection f b ≫ f) hQ i)
      (t ≫ modificationInclusionAtInfinity f b) :=
  vanishesOver_perfectChernClass_of_rankLT C (modificationProjection f b ≫ f)
    (t ≫ modificationInclusionAtInfinity f b) hQ i
    (exists_isFiniteLocallyFreeOfRankLT_of_isZero _ hzero hi)

/-- In the situation of Stacks 0F9K, assume that `Q|_T` is zero, so that `c'_p(Q)` is defined
for every `p ≥ 1`. Then the classes `P'_p(Q) ∈ A^p(Z ⟶ X)` are Newton's
polynomials in the classes `c'_i(Q)`, with the multiplication of Stacks 0FA0
(`(c, c') ↦ res(c) ∘ c'`, `Stacks.Chow.supportedMul`):

  `P'_{p+1}(Q) = ∑_{j < p} (-1)^j c'_{j+1}(Q) P'_{p-j}(Q) + (-1)^p (p + 1) c'_{p+1}(Q)`

for every `p ≥ 0`. This is the recursion defining the universal power-sum polynomials, so
`P'_1 = c'_1`, `P'_2 = c'_1² - 2c'_2`, `P'_3 = c'_1³ - 3c'_1c'_2 + 3c'_3`, and so on. The summand
`c'_{j+1} P'_{p-j}` lies in `A^{(j+1)+(p-j)}(Z ⟶ X)`, read in degree `p + 1`. -/
@[stacks 0FAX "Newton's recursion P'_{p+1} = ∑_{j<p} (-1)^j c'_{j+1} P'_{p-j} + \
(-1)^p (p+1) c'_{p+1}, for every p ≥ 0, with the multiplication of 0FA0; it determines every \
displayed identity and the ones after it (and so on)"]
theorem modificationPowerSum_succ (q : ℕ) :
    modificationPowerSum C f b hA z t hQ (q + 1) hT hzero =
      ∑ j ∈ (Finset.range q).attach, ((-1 : ℤ) ^ (j : ℕ)) •
          bivariantClassDegreeCongr C _ (z ≫ f) f z rfl
            (newton_degree_eq (Finset.mem_range.mp j.2))
            (supportedMul C (z ≫ f) f z rfl
              (modificationChernClassOfIsZero C f b hA z t hQ hT hzero ((j : ℕ) + 1)
                (Nat.succ_pos _))
              (modificationPowerSum C f b hA z t hQ (q - j) hT hzero)) +
        ((-1 : ℤ) ^ q * ((q : ℤ) + 1)) •
          modificationChernClassOfIsZero C f b hA z t hQ hT hzero (q + 1) (Nat.succ_pos _) :=
  localizedModificationClass_isNewtonPowerSums (gysinAtInfinityData C f b hA) z t hT
    (isNewtonPowerSums_perfectPowerSum C (modificationProjection f b ≫ f) hQ)
    (fun _ hi => vanishesOver_perfectChernClass_of_isZero C f b t hQ hzero hi)
    (fun q _ => vanishesOver_perfectPowerSumClass_of_isZero C (modificationProjection f b ≫ f)
      (t ≫ modificationInclusionAtInfinity f b) hQ q hzero)
    (fun _q _ => commutesAtInfinity_gysinAtInfinityData C f b hA _) q

/-- In the situation of Stacks 0F9K, with `Q|_T` zero,

* `P'_1 = c'_1`,
* `P'_2 = c'_1² - 2c'_2`,
* `P'_3 = c'_1³ - 3c'_1c'_2 + 3c'_3`,
* `P'_4 = c'_1⁴ - 4c'_1²c'_2 + 4c'_1c'_3 + 2c'_2² - 4c'_4`

in `A^p(Z ⟶ X)`, with the multiplication `(c, c') ↦ res(c) ∘ c'` of Stacks 0FA0
(`Stacks.Chow.supportedMul`), products bracketed to the right and read in the degree of the
left-hand side. The general case ("and so on") is `Stacks.Chow.modificationPowerSum_succ`. -/
@[stacks 0FAX "the four displayed identities, with the multiplication of 0FA0"]
theorem modificationPowerSum_first_four :
    let c := fun i (hi : 0 < i) =>
      modificationChernClassOfIsZero C f b hA z t hQ hT hzero i hi
    let m := fun {a b : ℤ} (x : BivariantClass C (gysinSystemOfInvertible C) (z ≫ f) f z rfl a)
      (y : BivariantClass C (gysinSystemOfInvertible C) (z ≫ f) f z rfl b) =>
        supportedMul C (z ≫ f) f z rfl x y
    let P := fun q => modificationPowerSum C f b hA z t hQ q hT hzero
    let d := fun {a b : ℤ} (h : a = b) =>
      bivariantClassDegreeCongr C (gysinSystemOfInvertible C) (z ≫ f) f z rfl h
    P 1 = c 1 (by norm_num) ∧
    P 2 = d (by norm_num) (m (c 1 (by norm_num)) (c 1 (by norm_num))) -
      (2 : ℤ) • c 2 (by norm_num) ∧
    P 3 = d (by norm_num) (m (c 1 (by norm_num)) (d (by norm_num : (1 : ℤ) + 1 = 2)
        (m (c 1 (by norm_num)) (c 1 (by norm_num))))) -
      (3 : ℤ) • d (by norm_num) (m (c 1 (by norm_num)) (c 2 (by norm_num))) +
      (3 : ℤ) • c 3 (by norm_num) ∧
    P 4 = d (by norm_num) (m (c 1 (by norm_num)) (d (by norm_num : (1 : ℤ) + 2 = 3)
        (m (c 1 (by norm_num)) (d (by norm_num : (1 : ℤ) + 1 = 2)
          (m (c 1 (by norm_num)) (c 1 (by norm_num))))))) -
      (4 : ℤ) • d (by norm_num) (m (c 1 (by norm_num)) (d (by norm_num : (1 : ℤ) + 2 = 3)
        (m (c 1 (by norm_num)) (c 2 (by norm_num))))) +
      (4 : ℤ) • d (by norm_num) (m (c 1 (by norm_num)) (c 3 (by norm_num))) +
      (2 : ℤ) • d (by norm_num) (m (c 2 (by norm_num)) (c 2 (by norm_num))) -
      (4 : ℤ) • c 4 (by norm_num) := by
  intro c m P d
  set D := gysinAtInfinityData C f b hA
  set sW := modificationProjection f b ≫ f
  set cc := perfectChernClass C sW hQ with hcc
  have F := (isNewtonPowerSums_perfectPowerSum C sW hQ).first_four
    (commute_homPart_perfectChernClass C sW hQ)
  have hm' : ∀ {i j k : ℕ} (Q : TotalChowClass C sW) (h : i + j = k),
      (TotalChowClass.homComponent i cc * Q) k =
        bivariantClassDegreeCongr C _ sW sW (𝟙 W) (Category.id_comp _)
          (by rw [← h]; push_cast; rfl) ((cc i).mulId C sW (Q j)) :=
    fun Q h => TotalChowClass.homPart_mul_apply C sW cc Q h
  have hx : ∀ i, (TotalChowClass.homComponent i cc) i = cc i := fun i => by
    rw [TotalChowClass.homComponent_apply, ite_eq_left rfl]
  have hm : ∀ {i j k : ℕ} (h : i + j = k),
      (TotalChowClass.homComponent i cc * TotalChowClass.homComponent j cc) k =
        bivariantClassDegreeCongr C _ sW sW (𝟙 W) (Category.id_comp _)
          (by rw [← h]; push_cast; rfl) ((cc i).mulId C sW (cc j)) :=
    fun h => by rw [hm' _ h, hx]
  have hsm : ∀ (n : ℤ) (y : TotalChowClass C sW) (k : ℕ), (n • y) k = n • y k :=
    fun _ _ _ => rfl
  have e : ∀ i (hi : 0 < i), IsLocalizedModificationClass D z t hT (cc i) (c i hi) := fun i hi =>
    IsLocalizedModificationClass.of_vanishesOver
      (vanishesOver_perfectChernClass_of_isZero C f b t hQ hzero hi)
  have vP : ∀ q, BivariantClass.VanishesOver (perfectPowerSumComponent C sW hQ q)
      (t ≫ modificationInclusionAtInfinity f b) := fun q =>
    vanishesOver_perfectPowerSumClass_of_isZero C sW (t ≫ modificationInclusionAtInfinity f b) hQ
      q hzero
  have em : ∀ {p r k : ℤ}
      {q₁ : chowCohomologyComponent C (gysinSystemOfInvertible C) sW p}
      {q₂ : chowCohomologyComponent C (gysinSystemOfInvertible C) sW r}
      {c₁ : BivariantClass C (gysinSystemOfInvertible C) (z ≫ f) f z rfl p}
      {c₂ : BivariantClass C (gysinSystemOfInvertible C) (z ≫ f) f z rfl r}
      (h₁ : IsLocalizedModificationClass D z t hT q₁ c₁)
      (h₂ : IsLocalizedModificationClass D z t hT q₂ c₂) (hk : p + r = k),
      IsLocalizedModificationClass D z t hT
        (bivariantClassDegreeCongr C _ sW sW (𝟙 W) (Category.id_comp _) hk (q₁.mulId C sW q₂))
        (d hk (m c₁ c₂)) := fun h₁ h₂ hk =>
    (h₁.supportedMul h₂ (commutesAtInfinity_gysinAtInfinityData C f b hA _)
      ).bivariantClassDegreeCongr hk
  have eP : ∀ q, P q = localizedModificationClass D z t hT (vP q) := fun q => rfl
  have e1 := e 1 Nat.one_pos
  have e2 := e 2 (by norm_num)
  have e3 := e 3 (by norm_num)
  have e11 := em e1 e1 (by norm_num : (1 : ℤ) + 1 = 2)
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨hv, hH⟩ := e1
    rw [eP, hH]
    refine localizedModificationClass_congr D z t hT ?_ _ _
    rw [perfectPowerSumComponent, F.1, hx]
  · obtain ⟨hv, hH⟩ := e11.sub (e2.zsmul 2)
    rw [eP, hH]
    refine localizedModificationClass_congr D z t hT ?_ _ _
    rw [perfectPowerSumComponent, F.2.1, TotalChowClass.sub_apply, hsm, hm (by norm_num), hx]
  · rw [eP]
    obtain ⟨hv, hH⟩ := ((em e1 e11 (by norm_num : (1 : ℤ) + 2 = 3)).sub
      ((em e1 e2 (by norm_num : (1 : ℤ) + 2 = 3)).zsmul 3)).add
      (e3.zsmul 3)
    rw [hH]
    refine localizedModificationClass_congr D z t hT ?_ _ _
    rw [perfectPowerSumComponent, F.2.2.1, TotalChowClass.add_apply, TotalChowClass.sub_apply, hsm,
      hsm, hm' _ (by norm_num : 1 + 2 = 3), hm (by norm_num : 1 + 1 = 2),
      hm (by norm_num : 1 + 2 = 3), hx]
  · rw [eP]
    have e12 := em e1 e2 (by norm_num : (1 : ℤ) + 2 = 3)
    have e111 := em e1 e11 (by norm_num : (1 : ℤ) + 2 = 3)
    obtain ⟨hv, hH⟩ := ((((em e1 e111 (by norm_num : (1 : ℤ) + 3 = 4)).sub
      ((em e1 e12 (by norm_num : (1 : ℤ) + 3 = 4)).zsmul 4)).add
      ((em e1 e3 (by norm_num : (1 : ℤ) + 3 = 4)).zsmul 4)).add
      ((em e2 e2 (by norm_num : (2 : ℤ) + 2 = 4)).zsmul 2)).sub
      ((e 4 (by norm_num)).zsmul 4)
    rw [hH]
    refine localizedModificationClass_congr D z t hT ?_ _ _
    rw [perfectPowerSumComponent, F.2.2.2, TotalChowClass.sub_apply, TotalChowClass.add_apply,
      TotalChowClass.add_apply, TotalChowClass.sub_apply, hsm, hsm, hsm, hsm,
      hm' (TotalChowClass.homComponent 1 cc * (TotalChowClass.homComponent 1 cc *
        TotalChowClass.homComponent 1 cc)) (by norm_num : 1 + 3 = 4),
      hm' (TotalChowClass.homComponent 1 cc * TotalChowClass.homComponent 1 cc)
        (by norm_num : 1 + 2 = 3),
      hm (by norm_num : 1 + 1 = 2),
      hm' (TotalChowClass.homComponent 1 cc * TotalChowClass.homComponent 2 cc)
        (by norm_num : 1 + 3 = 4),
      hm (by norm_num : 1 + 2 = 3), hm (by norm_num : 1 + 3 = 4), hm (by norm_num : 2 + 2 = 4), hx]

end Stacks.Chow

end
