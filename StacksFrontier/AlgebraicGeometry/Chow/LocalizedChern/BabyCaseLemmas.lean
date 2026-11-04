module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.BabyCase
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.ClosedCoverProduct
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.RestrictHomology
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.DirectSum
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PerfectTwist
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreEulerCharacteristicSingle

/-!
# Properties of the classes `P'_p(E₂)` and `c'_p(E₂)`

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `i₁ : X₁ ⟶ X`, `i₂ : X₂ ⟶ X` be closed immersions with `X = X₁ ∪ X₂`
set-theoretically, and let `E₂ ∈ D(𝒪_{X₂})` have defined Chern classes. Stacks 0F9H constructs
the classes `P'_p(E₂)`, `c'_p(E₂) ∈ A^p(X₂ ⟶ X)` (`Stacks.Chow.closedCoverPowerSum`,
`Stacks.Chow.closedCoverChernClass`). This file proves the relations between them of Section 42.50
of the source.

## Main results

* `Stacks.Chow.isFiniteLocallyFreeOfRankLT_of_isZero` — the zero module has rank `< p` for every
  `p ≥ 1`; so if `E₂` restricts to zero on `X₁ ∩ X₂`, every `c'_p(E₂)` with `p ≥ 1` is defined.
* `Stacks.Chow.closedCoverPowerSum_succ`, `Stacks.Chow.closedCoverPowerSum_first_four` —
  **Stacks 0FAK**: Newton's recursion
  `P'_{p+1} = ∑_{j < p} (-1)^j c'_{j+1} P'_{p-j} + (-1)^p (p + 1) c'_{p+1}`, and the four
  displayed identities.
* `Stacks.Chow.closedCoverPowerSum_biprod` — **Stacks 0FAM**: `P'_p(E ⊕ F) = P'_p(E) + P'_p(F)`.
* `Stacks.Chow.closedCoverChernClass_derivedTwist` — the formula of Stacks 0FAN for `E₂`
  restricting to zero on `X₁ ∩ X₂`.

## References

* [Stacks Project, Tag 0FAK](https://stacks.math.columbia.edu/tag/0FAK)
* [Stacks Project, Tag 0FAM](https://stacks.math.columbia.edu/tag/0FAM)
* [Stacks Project, Tag 0FAN](https://stacks.math.columbia.edu/tag/0FAN)
* [Stacks Project, Tag 0F9H](https://stacks.math.columbia.edu/tag/0F9H)
* [Stacks Project, Tag 0FA0](https://stacks.math.columbia.edu/tag/0FA0)
* [Stacks Project, Tag 0FAD](https://stacks.math.columbia.edu/tag/0FAD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The zero module has small rank -/

section ZeroRank

/-- **The zero module has rank `< p` for every `p ≥ 1`.** -/
theorem isFiniteLocallyFreeOfRankLT_of_isZero {W : Scheme.{u}} {M : W.Modules} (hM : IsZero M)
    {p : ℕ} (hp : 0 < p) : IsFiniteLocallyFreeOfRankLT (X := W.toRingedSpace) M p := by
  refine ⟨@AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ _ _ _
    _ _ M 0 (isFiniteLocallyFreeOfRank_zero_of_isZero hM), fun x => ⟨⊤, trivial, 0, hp, ?_⟩⟩
  have hz : IsZero ((Scheme.Modules.restrictFunctor (⊤ : W.Opens).ι).obj M) :=
    Functor.map_isZero _ hM
  exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    ((Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict W ⊤).app M).symm
    (isFiniteLocallyFreeOfRank_zero_of_isZero hz)

/-- **An object restricting to zero restricts to a module of rank `< p`**, for every `p ≥ 1`: the
zero module placed in degree `0`. -/
theorem exists_isFiniteLocallyFreeOfRankLT_of_isZero {W Y : Scheme.{u}} (z : W ⟶ Y)
    {E : DerivedCategory Y.Modules}
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      z.toLRSHom.toShHom).obj E)) {p : ℕ} (hp : 0 < p) :
    ∃ M : W.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        z.toLRSHom.toShHom).obj E ≅ (DerivedCategory.singleFunctor _ 0).obj M) :=
  ⟨(0 : W.Modules), isFiniteLocallyFreeOfRankLT_of_isZero (isZero_zero _) hp,
    ⟨hzero.iso (Functor.map_isZero _ (isZero_zero _))⟩⟩

/-- `c_p(E)` vanishes over `z` for `p ≥ 1` when the derived pullback of `E` along `z` is zero. -/
private theorem vanishesOver_perfectChernClass_of_isZero_derivedPullback (C : ChowSituation.{u})
    {W Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (z : W ⟶ Y)
    [LocallyOfFiniteType z] {E : DerivedCategory Y.Modules} (hE : HasDefinedChernClasses E)
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      z.toLRSHom.toShHom).obj E)) (p : ℕ) (hp : 0 < p) :
    BivariantClass.VanishesOver (perfectChernClass C sY hE p) z :=
  vanishesOver_perfectChernClass_of_rankLT C sY z hE p
    (exists_isFiniteLocallyFreeOfRankLT_of_isZero z hzero hp)

end ZeroRank

/-! ### Stacks 0FAK -/

section Newton

variable (C : ChowSituation.{u}) {X X₁ X₂ : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (i₁ : X₁ ⟶ X) (i₂ : X₂ ⟶ X) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
  (sX₂ : X₂ ⟶ C.S) [LocallyOfFiniteType sX₂] (hi₂ : i₂ ≫ sX = sX₂)
  {E₂ : DerivedCategory X₂.Modules} (hE₂ : HasDefinedChernClasses E₂)
  (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
  (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
    (pullback.snd i₁ i₂).toLRSHom.toShHom).obj E₂))

/-- The class `c'_p(E₂)` of Stacks 0F9H for `p ≥ 1`, when `E₂` restricts to zero on `X₁ ∩ X₂`:
the zero module has rank `< p`. -/
abbrev closedCoverChernClassOfIsZero (p : ℕ) (hp : 0 < p) :
    BivariantClass C (gysinSystemOfInvertible C) sX₂ sX i₂ hi₂ p :=
  closedCoverChernClass C sX i₁ i₂ sX₂ hi₂ hE₂ p hcover
    (exists_isFiniteLocallyFreeOfRankLT_of_isZero (pullback.snd i₁ i₂) hzero hp)

/-- In the situation of Stacks 0F9H, assume that `E₂` restricts to zero on `X₁ ∩ X₂`, so that
`c'_p(E₂)` is defined for every `p ≥ 1`. Then the classes `P'_p(E₂) ∈ A^p(X₂ ⟶ X)` are Newton's
polynomials in the classes `c'_i(E₂)`, with the multiplication of Stacks 0FA0
(`(c, c') ↦ res(c) ∘ c'`, `Stacks.Chow.supportedMul`):

  `P'_{p+1}(E₂) = ∑_{j < p} (-1)^j c'_{j+1}(E₂) P'_{p-j}(E₂) + (-1)^p (p + 1) c'_{p+1}(E₂)`

for every `p ≥ 0`. This is the recursion defining the universal power-sum polynomials of Stacks
0F9B, so `P'_1 = c'_1`, `P'_2 = c'_1² - 2c'_2`, `P'_3 = c'_1³ - 3c'_1c'_2 + 3c'_3`, and so on.
The summand `c'_{j+1} P'_{p-j}` lies in `A^{(j+1)+(p-j)}(X₂ ⟶ X)`, read in degree `p + 1`. -/
@[stacks 0FAK "Newton's recursion P'_{p+1} = ∑_{j<p} (-1)^j c'_{j+1} P'_{p-j} + \
(-1)^p (p+1) c'_{p+1}, for every p ≥ 0, with the multiplication of 0FA0; it determines every \
displayed identity and the ones after it (and so on)"]
theorem closedCoverPowerSum_succ (q : ℕ) :
    closedCoverPowerSum C sX i₁ i₂ sX₂ hi₂ hE₂ (q + 1) hcover hzero =
      ∑ j ∈ (Finset.range q).attach, ((-1 : ℤ) ^ (j : ℕ)) •
          bivariantClassDegreeCongr C _ sX₂ sX i₂ hi₂ (newton_degree_eq (Finset.mem_range.mp j.2))
            (supportedMul C sX₂ sX i₂ hi₂
              (closedCoverChernClassOfIsZero C sX i₁ i₂ sX₂ hi₂ hE₂ hcover hzero ((j : ℕ) + 1)
                (Nat.succ_pos _))
              (closedCoverPowerSum C sX i₁ i₂ sX₂ hi₂ hE₂ (q - j) hcover hzero)) +
        ((-1 : ℤ) ^ q * ((q : ℤ) + 1)) •
          closedCoverChernClassOfIsZero C sX i₁ i₂ sX₂ hi₂ hE₂ hcover hzero (q + 1)
            (Nat.succ_pos _) := by
  subst hi₂
  exact closedCoverExtension_isNewtonPowerSums C sX i₁ i₂ hcover
    (isNewtonPowerSums_perfectPowerSum C (i₂ ≫ sX) hE₂)
    (vanishesOver_perfectChernClass_of_isZero_derivedPullback C (i₂ ≫ sX) (pullback.snd i₁ i₂)
      hE₂ hzero)
    (fun q => vanishesOver_perfectPowerSumClass_of_isZero C (i₂ ≫ sX) (pullback.snd i₁ i₂) hE₂ q
      hzero) q

include hzero in
/-- `c_i(E₂)` vanishes over `X₁ ∩ X₂` for `i ≥ 1` when `E₂` restricts to zero there. -/
theorem vanishesOver_perfectChernClass_of_isZero' (i : ℕ) (hi : 0 < i) :
    BivariantClass.VanishesOver (perfectChernClass C (i₂ ≫ sX) hE₂ i) (pullback.snd i₁ i₂) :=
  vanishesOver_perfectChernClass_of_isZero_derivedPullback C _ _ hE₂ hzero i hi

/-- `c'_i(E₂)` extends `c_i(E₂)`. -/
theorem isClosedCoverExtension_closedCoverChernClassOfIsZero (i : ℕ) (hi : 0 < i) :
    IsClosedCoverExtension C (gysinSystemOfInvertible C) sX i₁ i₂ (i₂ ≫ sX) rfl
      (perfectChernClass C (i₂ ≫ sX) hE₂ i)
      (closedCoverChernClassOfIsZero C sX i₁ i₂ (i₂ ≫ sX) rfl hE₂ hcover hzero i hi) :=
  isClosedCoverExtension_closedCoverChernClass C sX i₁ i₂ (i₂ ≫ sX) rfl hE₂ i hcover _

/-- In the situation of Stacks 0F9H, with `E₂` restricting to zero on `X₁ ∩ X₂`,

* `P'_1 = c'_1`,
* `P'_2 = c'_1² - 2c'_2`,
* `P'_3 = c'_1³ - 3c'_1c'_2 + 3c'_3`,
* `P'_4 = c'_1⁴ - 4c'_1²c'_2 + 4c'_1c'_3 + 2c'_2² - 4c'_4`

in `A^p(X₂ ⟶ X)`, with the multiplication `(c, c') ↦ res(c) ∘ c'` of Stacks 0FA0
(`Stacks.Chow.supportedMul`), products bracketed to the right and read in the degree of the
left-hand side. The general case ("and so on") is `Stacks.Chow.closedCoverPowerSum_succ`. -/
@[stacks 0FAK "the four displayed identities, with the multiplication of 0FA0"]
theorem closedCoverPowerSum_first_four :
    let c := fun i (hi : 0 < i) =>
      closedCoverChernClassOfIsZero C sX i₁ i₂ (i₂ ≫ sX) rfl hE₂ hcover hzero i hi
    let m := fun {a b : ℤ} (x : BivariantClass C (gysinSystemOfInvertible C) (i₂ ≫ sX) sX i₂ rfl a)
      (y : BivariantClass C (gysinSystemOfInvertible C) (i₂ ≫ sX) sX i₂ rfl b) =>
        supportedMul C (i₂ ≫ sX) sX i₂ rfl x y
    let P := fun q => closedCoverPowerSum C sX i₁ i₂ (i₂ ≫ sX) rfl hE₂ q hcover hzero
    let d := fun {a b : ℤ} (h : a = b) =>
      bivariantClassDegreeCongr C (gysinSystemOfInvertible C) (i₂ ≫ sX) sX i₂ rfl h
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
  set cc := perfectChernClass C (i₂ ≫ sX) hE₂ with hcc
  have F := (isNewtonPowerSums_perfectPowerSum C (i₂ ≫ sX) hE₂).first_four
    (commute_homPart_perfectChernClass C (i₂ ≫ sX) hE₂)
  -- components of products of homogeneous parts
  have hm : ∀ {i j k : ℕ} (h : i + j = k),
      (TotalChowClass.homComponent i cc * TotalChowClass.homComponent j cc) k =
        bivariantClassDegreeCongr C _ (i₂ ≫ sX) (i₂ ≫ sX) (𝟙 X₂) (Category.id_comp _)
          (by rw [← h]; push_cast; rfl) ((cc i).mulId C (i₂ ≫ sX) (cc j)) := by
    intro i j k h
    rw [TotalChowClass.homPart_mul_apply C (i₂ ≫ sX) cc _ h, TotalChowClass.homComponent_apply,
      ite_eq_left rfl]
  have hm' : ∀ {i j k : ℕ} (Q : TotalChowClass C (i₂ ≫ sX)) (h : i + j = k),
      (TotalChowClass.homComponent i cc * Q) k =
        bivariantClassDegreeCongr C _ (i₂ ≫ sX) (i₂ ≫ sX) (𝟙 X₂) (Category.id_comp _)
          (by rw [← h]; push_cast; rfl) ((cc i).mulId C (i₂ ≫ sX) (Q j)) :=
    fun Q h => TotalChowClass.homPart_mul_apply C (i₂ ≫ sX) cc Q h
  have hx : ∀ i, (TotalChowClass.homComponent i cc) i = cc i := fun i => by
    rw [TotalChowClass.homComponent_apply, ite_eq_left rfl]
  have hsm : ∀ (n : ℤ) (y : TotalChowClass C (i₂ ≫ sX)) (k : ℕ), (n • y) k = n • y k :=
    fun _ _ _ => rfl
  -- the characterizations
  have v : ∀ i (hi : 0 < i), BivariantClass.VanishesOver (cc i) (pullback.snd i₁ i₂) :=
    fun i hi => vanishesOver_perfectChernClass_of_isZero' C sX i₁ i₂ hE₂ hzero i hi
  have e : ∀ i (hi : 0 < i), IsClosedCoverExtension C (gysinSystemOfInvertible C) sX i₁ i₂
      (i₂ ≫ sX) rfl (cc i) (c i hi) := fun i hi =>
    isClosedCoverExtension_closedCoverChernClassOfIsZero C sX i₁ i₂ hE₂ hcover hzero i hi
  have vP : ∀ q, BivariantClass.VanishesOver (perfectPowerSumComponent C (i₂ ≫ sX) hE₂ q)
      (pullback.snd i₁ i₂) := fun q =>
    vanishesOver_perfectPowerSumClass_of_isZero C (i₂ ≫ sX) (pullback.snd i₁ i₂) hE₂ q hzero
  have vm : ∀ {i j : ℕ} {k : ℤ} (hj : 0 < j) (h : (i : ℤ) + j = k),
      BivariantClass.VanishesOver (bivariantClassDegreeCongr C _ (i₂ ≫ sX) (i₂ ≫ sX) (𝟙 X₂)
        (Category.id_comp _) h ((cc i).mulId C (i₂ ≫ sX) (cc j))) (pullback.snd i₁ i₂) :=
    fun hj h => BivariantClass.VanishesOver.bivariantClassDegreeCongr C h
      (BivariantClass.VanishesOver.mulId_left C (v _ hj) _)
  have v11 : BivariantClass.VanishesOver (bivariantClassDegreeCongr C _ (i₂ ≫ sX) (i₂ ≫ sX)
      (𝟙 X₂) (Category.id_comp _) (by norm_num : ((1 : ℕ) : ℤ) + ((1 : ℕ) : ℤ) = 2)
      ((cc 1).mulId C (i₂ ≫ sX) (cc 1))) (pullback.snd i₁ i₂) := vm Nat.one_pos _
  have e11 := ((e 1 Nat.one_pos).supportedMul C sX i₁ i₂ hcover (v 1 Nat.one_pos)
    (v 1 Nat.one_pos) (e 1 Nat.one_pos)).bivariantClassDegreeCongr C sX i₁ i₂
    (by norm_num : (1 : ℤ) + 1 = 2)
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (IsClosedCoverExtension.eq_closedCoverExtension hcover (vP 1) ?_).symm
    rw [perfectPowerSumComponent, F.1, hx]
    exact e 1 Nat.one_pos
  · refine (IsClosedCoverExtension.eq_closedCoverExtension hcover (vP 2) ?_).symm
    rw [perfectPowerSumComponent, F.2.1, TotalChowClass.sub_apply, hsm, hm (by norm_num), hx]
    exact e11.sub C sX i₁ i₂ ((e 2 (by norm_num)).zsmul C sX i₁ i₂ 2)
  · refine (IsClosedCoverExtension.eq_closedCoverExtension hcover (vP 3) ?_).symm
    rw [perfectPowerSumComponent, F.2.2.1, TotalChowClass.add_apply, TotalChowClass.sub_apply, hsm,
      hsm, hm' _ (by norm_num : 1 + 2 = 3), hm (by norm_num : 1 + 1 = 2),
      hm (by norm_num : 1 + 2 = 3), hx]
    refine ((IsClosedCoverExtension.sub C sX i₁ i₂ ?_ ?_).add ?_)
    · exact ((e 1 Nat.one_pos).supportedMul C sX i₁ i₂ hcover (v 1 Nat.one_pos) v11
        e11).bivariantClassDegreeCongr C sX i₁ i₂ _
    · exact (((e 1 Nat.one_pos).supportedMul C sX i₁ i₂ hcover (v 1 Nat.one_pos)
        (v 2 (by norm_num)) (e 2 (by norm_num))).bivariantClassDegreeCongr C sX i₁ i₂ _).zsmul
          C sX i₁ i₂ 3
    · exact (e 3 (by norm_num)).zsmul C sX i₁ i₂ 3
  · refine (IsClosedCoverExtension.eq_closedCoverExtension hcover (vP 4) ?_).symm
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
    have v12 : BivariantClass.VanishesOver (bivariantClassDegreeCongr C _ (i₂ ≫ sX) (i₂ ≫ sX)
        (𝟙 X₂) (Category.id_comp _) (by norm_num : ((1 : ℕ) : ℤ) + ((2 : ℕ) : ℤ) = 3)
        ((cc 1).mulId C (i₂ ≫ sX) (cc 2))) (pullback.snd i₁ i₂) := vm (by norm_num) _
    have e12 := ((e 1 Nat.one_pos).supportedMul C sX i₁ i₂ hcover (v 1 Nat.one_pos)
      (v 2 (by norm_num)) (e 2 (by norm_num))).bivariantClassDegreeCongr C sX i₁ i₂
      (by norm_num : ((1 : ℕ) : ℤ) + ((2 : ℕ) : ℤ) = 3)
    have v111 : BivariantClass.VanishesOver (bivariantClassDegreeCongr C _ (i₂ ≫ sX) (i₂ ≫ sX)
        (𝟙 X₂) (Category.id_comp _) (by norm_num : ((1 : ℕ) : ℤ) + 2 = 3)
        ((cc 1).mulId C (i₂ ≫ sX) (bivariantClassDegreeCongr C _ (i₂ ≫ sX) (i₂ ≫ sX)
          (𝟙 X₂) (Category.id_comp _) (by norm_num : ((1 : ℕ) : ℤ) + ((1 : ℕ) : ℤ) = 2)
          ((cc 1).mulId C (i₂ ≫ sX) (cc 1))))) (pullback.snd i₁ i₂) :=
      BivariantClass.VanishesOver.bivariantClassDegreeCongr C _
        (BivariantClass.VanishesOver.mulId_left C v11 _)
    have e111 := ((e 1 Nat.one_pos).supportedMul C sX i₁ i₂ hcover (v 1 Nat.one_pos) v11
      e11).bivariantClassDegreeCongr C sX i₁ i₂ (by norm_num : ((1 : ℕ) : ℤ) + 2 = 3)
    refine IsClosedCoverExtension.sub C sX i₁ i₂ (((IsClosedCoverExtension.sub C sX i₁ i₂ ?_ ?_).add
      ?_).add ?_) ?_
    · exact ((e 1 Nat.one_pos).supportedMul C sX i₁ i₂ hcover (v 1 Nat.one_pos) v111
        e111).bivariantClassDegreeCongr C sX i₁ i₂ _
    · exact (((e 1 Nat.one_pos).supportedMul C sX i₁ i₂ hcover (v 1 Nat.one_pos) v12
        e12).bivariantClassDegreeCongr C sX i₁ i₂ _).zsmul C sX i₁ i₂ 4
    · exact (((e 1 Nat.one_pos).supportedMul C sX i₁ i₂ hcover (v 1 Nat.one_pos)
        (v 3 (by norm_num)) (e 3 (by norm_num))).bivariantClassDegreeCongr C sX i₁ i₂ _).zsmul
          C sX i₁ i₂ 4
    · exact (((e 2 (by norm_num)).supportedMul C sX i₁ i₂ hcover (v 2 (by norm_num))
        (v 2 (by norm_num)) (e 2 (by norm_num))).bivariantClassDegreeCongr C sX i₁ i₂ _).zsmul
          C sX i₁ i₂ 2
    · exact (e 4 (by norm_num)).zsmul C sX i₁ i₂ 4

end Newton

/-! ### Stacks 0FAM -/

section DirectSum

variable (C : ChowSituation.{u}) {X X₁ X₂ : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (i₁ : X₁ ⟶ X) (i₂ : X₂ ⟶ X) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
  (sX₂ : X₂ ⟶ C.S) [LocallyOfFiniteType sX₂] (hi₂ : i₂ ≫ sX = sX₂)
  (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)

/-- The derived pullback of a direct sum of two objects restricting to zero restricts to zero. -/
theorem isZero_derivedPullback_biprod {W Y : Scheme.{u}} (z : W ⟶ Y)
    {E F : DerivedCategory Y.Modules}
    (hE : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      z.toLRSHom.toShHom).obj E))
    (hF : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      z.toLRSHom.toShHom).obj F)) :
    IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      z.toLRSHom.toShHom).obj (E ⊞ F : DerivedCategory Y.Modules)) := by
  refine IsZero.of_iso ?_ (derivedPullbackBiprodIso z E F)
  rw [IsZero.iff_id_eq_zero]
  exact biprod.hom_ext _ _ (hE.eq_of_tgt _ _) (hF.eq_of_tgt _ _)

/-- Let `i₁ : X₁ ⟶ X`, `i₂ : X₂ ⟶ X` be closed immersions with `X = X₁ ∪ X₂` set-theoretically, and
let `E, F ∈ D(𝒪_{X₂})` have defined Chern classes and restrict to zero on `X₁ ∩ X₂`. Then
`P'_p(E ⊕ F) = P'_p(E) + P'_p(F)` in `A^p(X₂ ⟶ X)` for every `p ≥ 0`, with `P'_p` the classes of
Stacks 0F9H. (The Chern classes of `E ⊕ F` are defined and it restricts to zero on `X₁ ∩ X₂`, so
`P'_p(E ⊕ F)` is defined; perfectness of `E`, `F` is not needed.) -/
@[stacks 0FAM]
theorem closedCoverPowerSum_biprod {E F : DerivedCategory X₂.Modules}
    (hE : HasDefinedChernClasses E) (hF : HasDefinedChernClasses F)
    (hzE : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.snd i₁ i₂).toLRSHom.toShHom).obj E))
    (hzF : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.snd i₁ i₂).toLRSHom.toShHom).obj F)) (p : ℕ) :
    closedCoverPowerSum C sX i₁ i₂ sX₂ hi₂ (hasDefinedChernClasses_biprod hE hF) p hcover
        (isZero_derivedPullback_biprod (pullback.snd i₁ i₂) hzE hzF) =
      closedCoverPowerSum C sX i₁ i₂ sX₂ hi₂ hE p hcover hzE +
        closedCoverPowerSum C sX i₁ i₂ sX₂ hi₂ hF p hcover hzF := by
  have hcls : perfectPowerSumComponent C sX₂ (hasDefinedChernClasses_biprod hE hF) p =
      perfectPowerSumComponent C sX₂ hE p + perfectPowerSumComponent C sX₂ hF p := by
    rw [perfectPowerSumComponent, perfectPowerSumComponent, perfectPowerSumComponent,
      perfectPowerSum_biprod C sX₂ hE hF (hasDefinedChernClasses_biprod hE hF)]
    rfl
  refine (IsClosedCoverExtension.eq_closedCoverExtension hcover
    (vanishesOver_perfectPowerSumClass_of_isZero C sX₂ (pullback.snd i₁ i₂)
      (hasDefinedChernClasses_biprod hE hF) p
      (isZero_derivedPullback_biprod (pullback.snd i₁ i₂) hzE hzF)) ?_).symm
  rw [hcls]
  exact (isClosedCoverExtension_closedCoverPowerSum C sX i₁ i₂ sX₂ hi₂ hE p hcover hzE).add
    (isClosedCoverExtension_closedCoverPowerSum C sX i₁ i₂ sX₂ hi₂ hF p hcover hzF)

end DirectSum

/-! ### Stacks 0FAN -/

section Twist

variable (C : ChowSituation.{u}) {X X₁ X₂ : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (i₁ : X₁ ⟶ X) (i₂ : X₂ ⟶ X) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
  (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ) (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- The twist of an object restricting to zero restricts to zero. -/
theorem isZero_derivedPullback_derivedTwist {W Y : Scheme.{u}} (z : W ⟶ Y)
    {E : DerivedCategory Y.Modules} (M : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      z.toLRSHom.toShHom).obj E)) :
    IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      z.toLRSHom.toShHom).obj (derivedTwist E M)) := by
  refine IsZero.of_iso ?_ (derivedPullbackDerivedTwistIso z E M)
  let F := (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor W.sheaf).flip.obj
    (DerivedCategory.Q.obj (singleZero ((Scheme.Modules.pullback z).obj M)))
  let := (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct W.sheaf).commShift_left
    (DerivedCategory.Q.obj (singleZero ((Scheme.Modules.pullback z).obj M)))
  have := (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct W.sheaf).exact_left
    (DerivedCategory.Q.obj (singleZero ((Scheme.Modules.pullback z).obj M)))
  exact F.map_isZero hzero

/-- The formula of Stacks 0FAN for an object `E₂` restricting to zero on `X₁ ∩ X₂`. -/
theorem closedCoverChernClass_derivedTwist_of_isZero {E₂ : DerivedCategory X₂.Modules}
    (perfect : RingedSpace.IsPerfect.{u, u + 1} E₂) (hE₂ : HasDefinedChernClasses E₂)
    (constantRank : ∀ x : X₂, DerivedFibreBetti.chiDerivedFibre X₂ E₂
      (DerivedFibreBetti.isPseudoCoherent_of_isPerfect E₂ perfect) x = 0)
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.snd i₁ i₂).toLRSHom.toShHom).obj E₂)) (i : ℕ) (hi : 0 < i) :
    haveI := isInvertible_pullback i₂ L
    closedCoverChernClassOfIsZero C sX i₁ i₂ (i₂ ≫ sX) rfl
        (hasDefinedChernClasses_derivedTwist hE₂ ((Scheme.Modules.pullback i₂).obj L)) hcover
        (isZero_derivedPullback_derivedTwist (pullback.snd i₁ i₂) _ hzero) i hi =
      ∑ j ∈ (Finset.range i).attach, Ring.choose (-(i : ℤ) + (j : ℕ)) (j : ℕ) •
        bivariantClassDegreeCongr C _ (i₂ ≫ sX) sX i₂ rfl
          (twist_degree_eq (Finset.mem_range.mp j.2))
          (supportedRightComp C (i₂ ≫ sX) sX i₂ rfl
            (closedCoverChernClassOfIsZero C sX i₁ i₂ (i₂ ≫ sX) rfl hE₂ hcover hzero (i - j)
              (by have := Finset.mem_range.mp j.2; omega))
            ((TotalChowClass.firstChernTotal C sX L ^ (j : ℕ)) (j : ℕ))) := by
  have := isInvertible_pullback i₂ L
  have hc := perfectChernClass_derivedTwist_apply C (i₂ ≫ sX) ((Scheme.Modules.pullback i₂).obj L)
    perfect hE₂ 0 constantRank i
  rw [← TotalChowClass.res_firstChernTotal C sX L i₂ rfl] at hc
  have h := closedCoverExtension_twist C sX i₁ i₂ hcover 0 i hc
    (by obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hi; simp [Ring.choose_zero_succ])
    (vanishesOver_perfectChernClass_of_isZero_derivedPullback C (i₂ ≫ sX) (pullback.snd i₁ i₂)
      hE₂ hzero)
    (vanishesOver_perfectChernClass_of_isZero_derivedPullback C (i₂ ≫ sX) (pullback.snd i₁ i₂) _
      (isZero_derivedPullback_derivedTwist (pullback.snd i₁ i₂) _ hzero) i hi)
  simp only [zero_sub] at h
  exact h

/-- In the situation of Stacks 0F9H — `E₂ ∈ D(𝒪_{X₂})` perfect with defined Chern classes,
restricting on `X₁ ∩ X₂` to a finite locally free module of rank `< p` placed in degree `0` —
assume that `E₂` has constant rank `0`, and let `ℒ` be an invertible `𝒪_X`-module. Then the
restriction of `E₂` to `X₁ ∩ X₂` is zero (`hzero` in the statement, by the assumption on the rank),
so `c'_i(E₂)` and `c'_i(E₂ ⊗ ℒ)` are defined for every `i ≥ 1`, and

  `c'_i(E₂ ⊗ ℒ) = ∑_{j=0}^{i-1} binom(-i + j, j) c'_{i-j}(E₂) c_1(ℒ)^j`

in `A^i(X₂ ⟶ X)`. Here `E₂ ⊗ ℒ` is the twist of `E₂` by `ℒ|_{X₂}` (Stacks 0FAF),
`c_1(ℒ)^j ∈ A^j(X)`, and the product `A^{i-j}(X₂ ⟶ X) × A^j(X) ⟶ A^i(X₂ ⟶ X)` is the first
multiplication of Stacks 0FA0 (`Stacks.Chow.supportedRightComp`), the summand being read in
degree `i`. -/
@[stacks 0FAN]
theorem closedCoverChernClass_derivedTwist {E₂ : DerivedCategory X₂.Modules}
    (perfect : RingedSpace.IsPerfect.{u, u + 1} E₂) (hE₂ : HasDefinedChernClasses E₂)
    (constantRank : ∀ x : X₂, DerivedFibreBetti.chiDerivedFibre X₂ E₂
      (DerivedFibreBetti.isPseudoCoherent_of_isPerfect E₂ perfect) x = 0) {p : ℕ}
    (hrank : ∃ M : (pullback i₁ i₂).Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (pullback.snd i₁ i₂).toLRSHom.toShHom).obj E₂ ≅
          (DerivedCategory.singleFunctor _ 0).obj M)) (i : ℕ) (hi : 0 < i) :
    haveI := isInvertible_pullback i₂ L
    let hzero := DerivedFibreBetti.isZero_derivedPullback_of_chiDerivedFibre_eq_zero
      (pullback.snd i₁ i₂) E₂ perfect constantRank hrank
    closedCoverChernClassOfIsZero C sX i₁ i₂ (i₂ ≫ sX) rfl
        (hasDefinedChernClasses_derivedTwist hE₂ ((Scheme.Modules.pullback i₂).obj L)) hcover
        (isZero_derivedPullback_derivedTwist (pullback.snd i₁ i₂) _ hzero) i hi =
      ∑ j ∈ (Finset.range i).attach, Ring.choose (-(i : ℤ) + (j : ℕ)) (j : ℕ) •
        bivariantClassDegreeCongr C _ (i₂ ≫ sX) sX i₂ rfl
          (twist_degree_eq (Finset.mem_range.mp j.2))
          (supportedRightComp C (i₂ ≫ sX) sX i₂ rfl
            (closedCoverChernClassOfIsZero C sX i₁ i₂ (i₂ ≫ sX) rfl hE₂ hcover hzero (i - j)
              (by have := Finset.mem_range.mp j.2; omega))
            ((TotalChowClass.firstChernTotal C sX L ^ (j : ℕ)) (j : ℕ))) :=
  closedCoverChernClass_derivedTwist_of_isZero C sX i₁ i₂ hcover L perfect hE₂ constantRank _ i hi

end Twist

end Stacks.Chow

end
