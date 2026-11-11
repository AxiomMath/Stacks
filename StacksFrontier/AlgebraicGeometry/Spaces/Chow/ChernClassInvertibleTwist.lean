module

public import Mathlib.RingTheory.Polynomial.Vieta
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChernClassDualTensorOfProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChernClassWhitney
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IteratedFirstChernCapCommutativity
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChernCapFlatPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChernCapPropertiesAssembly
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChernCapVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChowOperationsCompatibility
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.FilteredTotalChernClass
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.FirstChernClassOfRankOne

/-!
# Chern classes of a finite locally free module twisted by an invertible module

In Situation 0EDT let `X/B` be good, let `ℰ` be a finite locally free `𝒪_X`-module of rank `r`
and let `ℒ` be an invertible `𝒪_X`-module. Then (Stacks 0ES4)

  `c_i(ℰ ⊗ ℒ) = ∑_{j=0}^{i} C(r - i + j, j) c_{i-j}(ℰ) c₁(ℒ)^j`   in `A^*(X)`.

Along a splitting `π : P ⟶ X` (Stacks 0ESC) the module `π^*ℰ` acquires a filtration with
invertible successive quotients `ℒ_1, …, ℒ_r`, so that with `x_k = c₁(ℒ_k)` and `y = c₁(π^*ℒ)`
the Whitney formula and the additivity of `c₁` give

  `c(π^*ℰ) = ∏ (1 + x_k)`,   `c(π^*(ℰ ⊗ ℒ)) = ∏ (1 + x_k + y)`,

and expanding `∏_k ((1 + y) + x_k) = ∑_m e_m(x) (1 + y)^{r-m}` gives the formula on `P`, from
which it descends to `X` since `π^*` is injective on Chow homology and intertwines the Chern
classes. The properties of the Chern classes this uses,
`AlgebraicGeometry.Space.PrivateChern.ChernCapProperties`, are vanishing above the rank, the
Whitney formula (Stacks 0ES9), additivity of `c₁` (Stacks 0EQK), invariance under isomorphism,
and the commutativity of first Chern classes (Stacks 0EQZ).

## Main results

* `AlgebraicGeometry.Space.chernCap_tensorObj_of_isInvertibleModule`: the formula of Stacks 0ES4
  on `CH_*(X)` for `AlgebraicGeometry.Space.PrivateChern.chernCap`; Stacks 0ES4 for the classes of
  Definition 0ERZ is `AlgebraicGeometry.Space.chernCapGraded_tensorObj_of_isInvertibleModule`
  (`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChernClassTensorInvertible`).
* `AlgebraicGeometry.Space.PrivateChern.commute_firstChernCapChow`: the cap products with the
  first Chern classes of two invertible modules commute on `CH_*(X)`.
* `AlgebraicGeometry.Space.PrivateChern.chernCap_eq_of_iso`: isomorphic modules have the same
  Chern classes.
* `PowerSeries.coeff_list_prod_one_add_C_add_mul_X_of_commute`: the formal identity
  `[X^i] ∏_k (1 + (x_k + y) X) = ∑_j C(r - i + j, j) [X^{i-j}] ∏_k (1 + x_k X) · y^j`.

## References

* [Stacks Project, Tag 0ES4](https://stacks.math.columbia.edu/tag/0ES4)
* [Stacks Project, Tag 02UD](https://stacks.math.columbia.edu/tag/02UD)
* [Stacks Project, Tag 0ESC](https://stacks.math.columbia.edu/tag/0ESC)
* [Stacks Project, Tag 0EQZ](https://stacks.math.columbia.edu/tag/0EQZ)
-/

@[expose] public noncomputable section

/-! ### The formal identity -/

namespace PowerSeries

section Comm

variable {A : Type*} [CommRing A]

/-- The coefficients of `(1 + y X)^p` are `C(p, m) y^m`. -/
theorem coeff_one_add_C_mul_X_pow (y : A) : ∀ (p m : ℕ),
    coeff m ((1 + C y * X) ^ p) = (p.choose m : A) * y ^ m
  | 0, 0 => by simp
  | 0, m + 1 => by simp [coeff_one]
  | p + 1, 0 => by
    rw [coeff_zero_eq_constantCoeff_apply, map_pow]
    simp
  | p + 1, m + 1 => by
    rw [pow_succ', coeff_one_add_C_mul_X_mul, coeff_one_add_C_mul_X_pow y p,
      coeff_one_add_C_mul_X_pow y p, Nat.choose_succ_succ', Nat.cast_add]
    ring

/-- The elementary symmetric functions of the `a X` are `e_j(a) X^j`. -/
theorem esymm_map_C_mul_X (s : Multiset A) (j : ℕ) :
    (s.map fun a => C a * X).esymm j = C (s.esymm j) * X ^ j := by
  rw [Multiset.esymm, Multiset.esymm, Multiset.powersetCard_map, Multiset.map_map,
    map_multiset_sum, Multiset.map_map, ← Multiset.sum_map_mul_right]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun t ht => ?_)
  rw [Multiset.mem_powersetCard] at ht
  simp only [Function.comp_apply]
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, ht.2,
    map_multiset_prod]

/-- **The product of the `1 + (a + y) X`** is `∑_m e_m(a) X^m (1 + y X)^{r - m}`, for a multiset of
`r` elements `a`. -/
theorem prod_one_add_C_add_mul_X_eq_sum (s : Multiset A) (y : A) :
    (s.map fun a => 1 + C (a + y) * X).prod =
      ∑ m ∈ Finset.range (Multiset.card s + 1),
        C (s.esymm m) * X ^ m * (1 + C y * X) ^ (Multiset.card s - m) := by
  have h := congrArg (Polynomial.eval (1 + C y * X))
    (Multiset.prod_X_add_C_eq_sum_esymm (s.map fun a => C a * X))
  rw [Polynomial.eval_multiset_prod, Multiset.map_map, Polynomial.eval_finsetSum] at h
  simp only [Function.comp_def, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_pow, Multiset.card_map, esymm_map_C_mul_X] at h
  rw [← h, Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun a _ => ?_)
  simp only [Function.comp_apply]
  rw [map_add]
  ring

/-- The elementary symmetric functions of a multiset vanish above its cardinality. -/
theorem _root_.Multiset.esymm_eq_zero_of_card_lt {s : Multiset A} {m : ℕ}
    (h : Multiset.card s < m) : s.esymm m = 0 := by
  rw [Multiset.esymm, Multiset.powersetCard_eq_empty m h]
  simp

/-- **The coefficients of the product of the `1 + (a + y) X`**, for a multiset of `r` elements
`a`: `[X^i] ∏ (1 + (a + y) X) = ∑_{j ≤ i} C(r + j - i, j) e_{i-j}(a) y^j`. -/
theorem coeff_prod_one_add_C_add_mul_X (s : Multiset A) (y : A) (i : ℕ) :
    coeff i (s.map fun a => 1 + C (a + y) * X).prod =
      ∑ j ∈ Finset.range (i + 1),
        ((Multiset.card s + j - i).choose j : ℤ) • (s.esymm (i - j) * y ^ j) := by
  set n := Multiset.card s
  let g : ℕ → A := fun k => if k ≤ i then s.esymm k * ((n - k).choose (i - k) * y ^ (i - k))
    else 0
  have hL : coeff i (s.map fun a => 1 + C (a + y) * X).prod =
      ∑ k ∈ Finset.range (n + 1), g k := by
    rw [prod_one_add_C_add_mul_X_eq_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
    simp only [g]
    split_ifs
    · rw [coeff_one_add_C_mul_X_pow]
    · rw [mul_zero]
  have hR : ∑ j ∈ Finset.range (i + 1),
      ((n + j - i).choose j : ℤ) • (s.esymm (i - j) * y ^ j) =
      ∑ k ∈ Finset.range (i + 1), g k := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    simp only [g, ite_eq_left (by omega : k ≤ i)]
    rw [show i + 1 - 1 - k = i - k by omega, show i - (i - k) = k by omega,
      show n + (i - k) - i = n - k by omega, zsmul_eq_mul, Int.cast_natCast]
    ring
  have hz : ∀ k, n < k → g k = 0 := fun k hk => by
    simp only [g, Multiset.esymm_eq_zero_of_card_lt hk, zero_mul, ite_self]
  rw [hL, hR]
  rcases le_total n i with hni | hin
  · refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun k hk hk' => hz k ?_
    rw [Finset.mem_range] at hk hk'
    omega
  · refine (Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun k hk hk' => ?_).symm
    rw [Finset.mem_range] at hk hk'
    simp only [g, ite_eq_right (by omega : ¬k ≤ i)]

end Comm

section Noncomm

variable {R : Type*} [Ring R]

/-- **The coefficients of `∏_k (1 + (x_k + y) X)`** for pairwise commuting elements `y`, `x_1`, …,
`x_r` of a ring: with `c_m = [X^m] ∏_k (1 + x_k X)`,
`[X^i] ∏_k (1 + (x_k + y) X) = ∑_{j ≤ i} C(r + j - i, j) c_{i-j} y^j`. -/
theorem coeff_list_prod_one_add_C_add_mul_X_of_commute (xs : List R) (y : R)
    (hc : ∀ a ∈ y :: xs, ∀ b ∈ y :: xs, Commute a b) (i : ℕ) :
    coeff i ((xs.map fun x => 1 + C (x + y) * X).prod) =
      ∑ j ∈ Finset.range (i + 1), ((xs.length + j - i).choose j : ℤ) •
        (coeff (i - j) ((xs.map fun x => 1 + C x * X).prod) * y ^ j) := by
  obtain ⟨A, _, ι, zs, hzs⟩ := exists_commSubring_of_pairwise_commute (y :: xs) hc
  obtain ⟨y', xs', rfl, rfl⟩ : ∃ (y' : A) (xs' : List A), ι y' = y ∧ xs'.map ι = xs := by
    cases zs with
    | nil => exact absurd hzs (by simp)
    | cons a zs =>
      rw [List.map_cons, List.cons.injEq] at hzs
      exact ⟨a, zs, hzs.1, hzs.2⟩
  have h : ((xs'.map ι).map fun x => 1 + C (x + ι y') * X) =
      (xs'.map fun x => 1 + C (x + y') * X).map (PowerSeries.map ι) := by
    simp [List.map_map, Function.comp_def]
  rw [h, ← map_list_prod, coeff_map, ← Multiset.prod_coe, ← Multiset.map_coe,
    coeff_prod_one_add_C_add_mul_X, map_sum]
  simp only [List.length_map, Multiset.coe_card, map_zsmul, map_mul, map_pow]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hc' : (xs'.map ι).map (fun x => 1 + C x * X) =
      xs'.map (fun x => 1 + C (ι x) * X) := by
    simp [List.map_map, Function.comp_def]
  rw [hc', coeff_list_prod_one_add_C_mul_X]

end Noncomm

end PowerSeries

open CategoryTheory CategoryTheory.Limits MonoidalCategory ZeroObject

universe u

namespace AlgebraicGeometry.Space.PrivateChern

variable {D : BaseSpaceDimensionSituation.{u}}

/-- **The cap products with the first Chern classes of two invertible modules commute** on
`CH_*(X)` (Stacks 0EQZ): `c₁(ℒ) ∩ c₁(𝒩) ∩ α = c₁(𝒩) ∩ c₁(ℒ) ∩ α`. -/
theorem commute_firstChernCapChow {X : D.Ambient} {sX : X ⟶ D.space} (hX : D.IsGood sX)
    (L N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (goodSpace hX) L) (hN : IsInvertibleModule (goodSpace hX) N) :
    @Commute (AddMonoid.End (chowHomology.{u, u + 1} D sX hX)) _
      (firstChernCapChow.{u, u + 1} D sX hX L hL) (firstChernCapChow.{u, u + 1} D sX hX N hN) := by
  unfold Commute SemiconjBy
  refine chowHomology_hom_ext D sX hX fun k b => ?_
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 + 1 := ⟨k - 2, by omega⟩
  change firstChernCapChow.{u, u + 1} D sX hX L hL (firstChernCapChow.{u, u + 1} D sX hX N hN
      (DirectSum.of _ (j + 1 + 1) (chowClass.{u + 1} D sX hX (j + 1 + 1) b))) =
    firstChernCapChow.{u, u + 1} D sX hX N hN (firstChernCapChow.{u, u + 1} D sX hX L hL
      (DirectSum.of _ (j + 1 + 1) (chowClass.{u + 1} D sX hX (j + 1 + 1) b)))
  rw [firstChernCapChow_of_chowClass D sX hX N hN (j + 1) b,
    firstChernCapChow_of_chowClass D sX hX L hL j,
    firstChernCapChow_of_chowClass D sX hX L hL (j + 1) b,
    firstChernCapChow_of_chowClass D sX hX N hN j]
  exact congrArg _ (chowClass_eq_of_chowClassCanonical_eq D sX hX
    (chowClassCanonical_firstChernCapCycleMap_firstChernCapCycleMap_comm.{0, u} D sX hX L hL N hN j
      b))

/-- Stacks 0ES8 degree by degree on every good space, in the form taken by the Whitney formula. -/
theorem chernCap_succ_eq_of_shortComplex_all :
    ∀ {P : D.Ambient} {sP : P ⟶ D.space} (hP : D.IsGood sP) (r : ℕ)
      (T : ShortComplex (Modules.{u, u} D.site D.base D.base_mem P hP.1))
      (_ : T.ShortExact) (h₁ : IsInvertibleModule (goodSpace hP) T.X₁)
      (h₂ : IsFiniteLocallyFreeOfRank D sP hP T.X₂ (r + 1))
      (h₃ : IsFiniteLocallyFreeOfRank D sP hP T.X₃ r) (n : ℕ),
      chernCap.{u, u + 1} T.X₂ (r + 1) h₂ (n + 1) =
        chernCap.{u, u + 1} T.X₃ r h₃ (n + 1) +
          chernCap.{u, u + 1} T.X₁ 1
            (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hP) h₁) 1 *
            chernCap.{u, u + 1} T.X₃ r h₃ n :=
  chernCap_succ_eq_of_shortComplex

/-- **The splitting principle with an intertwining injection** (Stacks 0ESC with the compatibility
of the Chern classes with flat pullback), for the Chow groups whose rational equivalences are
indexed in the universe `u + 1`. -/
theorem hasIntertwiningSplittings : HasIntertwiningSplittings.{u, u + 1} D :=
  hasIntertwiningSplittings_of_flatPullbackChow chernCap_spaceModulePullback_flatPullbackChow

/-- **Isomorphic modules have the same Chern classes**: `c_n(ℰ) = c_n(ℰ')` for `ℰ ≅ ℰ'`. -/
theorem chernCap_eq_of_iso {X : D.Ambient} {sX : X ⟶ D.space} (hX : D.IsGood sX)
    {E E' : Modules.{u, u} D.site D.base D.base_mem X hX.1} (e : E ≅ E') (r : ℕ)
    (h : IsFiniteLocallyFreeOfRank D sX hX E r) (h' : IsFiniteLocallyFreeOfRank D sX hX E' r)
    (n : ℕ) : chernCap.{u, u + 1} E r h n = chernCap.{u, u + 1} E' r h' n := by
  let : Abelian (Modules.{u, u} D.site D.base D.base_mem X hX.1) := instAbelianModules hX.1
  let : HasZeroObject (Modules.{u, u} D.site D.base D.base_mem X hX.1) :=
    instHasZeroObjectModules hX.1
  let T : ShortComplex (Modules.{u, u} D.site D.base D.base_mem X hX.1) :=
    ShortComplex.mk e.hom (0 : E' ⟶ 0) comp_zero
  have hT : T.ShortExact :=
    { exact := (T.exact_iff_epi rfl).mpr (IsIso.epi_of_iso e.hom)
      mono_f := IsIso.mono_of_iso e.hom
      epi_g := (isZero_zero (Modules.{u, u} D.site D.base D.base_mem X hX.1)).epi T.g }
  have h₃ : IsFiniteLocallyFreeOfRank D sX hX T.X₃ 0 :=
    RingedSite.isFiniteLocallyFreeOfRank_zero_of_isZero _ (isZero_zero _)
  have hw := chernCap_shortExact_of_succ chernCap_succ_eq_of_shortComplex_all hX hT
    (r₁ := r) (r₂ := 0) h h' h₃ n
  refine (hw.trans ?_).symm
  rw [Finset.sum_eq_single (n, 0)]
  · change chernCap.{u, u + 1} E r h n * chernCap.{u, u + 1} T.X₃ 0 h₃ 0 = _
    rw [chernCap_zero, mul_one]
  · rintro ⟨p, q⟩ hpq hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hpq
    rcases q with _ | m
    · exact absurd (by simp only at hpq; rw [← hpq, add_zero]) hne
    · change chernCap.{u, u + 1} E r h p * chernCap.{u, u + 1} T.X₃ 0 h₃ (m + 1) = 0
      rw [chernCap_of_rank_zero, mul_zero]
  · exact fun hn => absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (add_zero n)) hn

attribute [local instance] modulesMonoidalCategory

/-- Finite sums of intertwined operations are intertwined. -/
theorem intertwines_finset_sum {M N : Type*} [AddCommGroup M] [AddCommGroup N] (g : M →+ N)
    {ι : Type*} (s : Finset ι) {φ : ι → AddMonoid.End M} {φ' : ι → AddMonoid.End N}
    (h : ∀ j, ∀ α, φ' j (g α) = g (φ j α)) (α : M) :
    (∑ j ∈ s, φ' j) (g α) = g ((∑ j ∈ s, φ j) α) := by
  rw [show (∑ j ∈ s, φ' j) (g α) = ∑ j ∈ s, φ' j (g α) from AddMonoidHom.finsetSum_apply _ _ _,
    show (∑ j ∈ s, φ j) α = ∑ j ∈ s, φ j α from AddMonoidHom.finsetSum_apply _ _ _, map_sum]
  exact Finset.sum_congr rfl fun j _ => h j α

/-- The Chern classes do not depend on how the rank is written. -/
theorem chernCap_rank_congr {X : D.Ambient} {sX : X ⟶ D.space} {hX : D.IsGood sX}
    (E : Modules.{u, u} D.site D.base D.base_mem X hX.1) {r r' : ℕ} (hrr' : r = r')
    (h : IsFiniteLocallyFreeOfRank D sX hX E r) (h' : IsFiniteLocallyFreeOfRank D sX hX E r')
    (n : ℕ) : chernCap.{u, u + 1} E r h n = chernCap.{u, u + 1} E r' h' n := by
  subst hrr'
  rfl

/-- **The twist of a module of rank `r` by an invertible module has rank `r`.** -/
theorem isFiniteLocallyFreeOfRank_tensorObj_of_isInvertibleModule {X : D.Ambient}
    {sX : X ⟶ D.space} {hX : D.IsGood sX} {E L : Modules.{u, u} D.site D.base D.base_mem X hX.1}
    {r : ℕ} (hE : IsFiniteLocallyFreeOfRank D sX hX E r)
    (hL : IsInvertibleModule (goodSpace hX) L) :
    IsFiniteLocallyFreeOfRank D sX hX (E ⊗ L) r :=
  Nat.mul_one r ▸ isFiniteLocallyFreeOfRank_tensorObj D.site D.base D.base_mem X hX.1 hE
    (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hX) hL)

end AlgebraicGeometry.Space.PrivateChern

namespace AlgebraicGeometry.Space

open PrivateChern

attribute [local instance] modulesMonoidalCategory

variable {D : BaseSpaceDimensionSituation.{u}}

/-- **The twist formula of Stacks 0ES4 for the Chern classes computed from the Segre
operations.** In Situation 0EDT let `X/B` be good, let `ℰ` be a finite locally free
`𝒪_X`-module of rank `r` and let `ℒ` be an invertible `𝒪_X`-module; `ℰ ⊗ ℒ` is finite locally
free of rank `r`. Then for every `i`

  `c_i(ℰ ⊗ ℒ) = ∑_{j=0}^{i} C(r + j - i, j) c_{i-j}(ℰ) c₁(ℒ)^j`

as operations on `CH_*(X) = ⨁_k CH_k(X)`, for the Chern classes
`AlgebraicGeometry.Space.PrivateChern.chernCap`, the coefficients of the inverse of the Segre
series of the projective bundle. For `i ≤ r` the binomial coefficient is the source's
`C(r - i + j, j)`; for `i > r` both sides vanish, which is the convention `c_i = 0` above the
rank, the left side by vanishing above the rank and the right side termwise
(`c_{i-j}(ℰ) = 0` for `i - j > r` and `C(r + j - i, j) = 0` otherwise).

Stacks 0ES4 itself, for the Chern classes `c_j(ℰ) ∈ A^j(X)` of Definition 0ERZ, is
`AlgebraicGeometry.Space.chernCapGraded_tensorObj_of_isInvertibleModule`, which applies this
theorem on every good test space `X' ⟶ X` to the pulled back modules, through the identification
of the two descriptions of the Chern classes
(`AlgebraicGeometry.Space.chowGroupCanonicalGradedToChowHomology_chernCapGraded`). -/
theorem chernCap_tensorObj_of_isInvertibleModule {X : D.Ambient} {sX : X ⟶ D.space}
    (hX : D.IsGood sX) {E L : Modules.{u, u} D.site D.base D.base_mem X hX.1} {r : ℕ}
    (hE : PrivateChern.IsFiniteLocallyFreeOfRank D sX hX E r)
    (hL : IsInvertibleModule (goodSpace hX) L) (i : ℕ) :
    chernCap.{u, u + 1} (E ⊗ L) r (isFiniteLocallyFreeOfRank_tensorObj_of_isInvertibleModule hE hL)
        i =
      ∑ j ∈ Finset.range (i + 1), ((r + j - i).choose j : ℤ) •
        (chernCap.{u, u + 1} E r hE (i - j) *
          chernCap.{u, u + 1} L 1
            (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hX) hL) 1 ^ j) := by
  have hC := chernCapProperties D
  have hL1 := isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hX) hL
  have hEL := isFiniteLocallyFreeOfRank_tensorObj_of_isInvertibleModule hE hL
  obtain ⟨P, sP, hP, π, g, hg, hfilE, hfilL, hnat⟩ :=
    PrivateChern.hasIntertwiningSplittings hX E L r 1 hE hL1
  obtain ⟨Ls, Ns, hLlen, hNlen, hcE, hcL, hcEL⟩ := exists_chernSeries_tensorObj_eq_prod
    (hC.chernCap_eq_zero_of_lt hP) (hC.chernCap_shortExact hP) (hC.chernCap_one_tensorObj hP)
    hfilE hfilL
  obtain ⟨N, rfl⟩ := List.length_eq_one_iff.1 hNlen
  let x : {M : Modules.{u, u} D.site D.base D.base_mem P hP.1 //
      IsInvertibleModule (goodSpace hP) M} → AddMonoid.End (chowHomology.{u, u + 1} D sP hP) :=
    fun M => chernCap.{u, u + 1} M.1 1
      (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hP) M.2) 1
  have hrP := isFiniteLocallyFreeOfRank_of_hasFiltrationOfLength hfilE
  have h1P := isFiniteLocallyFreeOfRank_of_hasFiltrationOfLength hfilL
  have hy : chernCap.{u, u + 1} ((spaceModulePullback D hX.1 hP.1 π).obj L) 1 h1P 1 = x N := by
    simpa [PowerSeries.coeff_mk, PowerSeries.coeff_one, x] using congrArg (PowerSeries.coeff 1) hcL
  have hcomm : ∀ a ∈ x N :: Ls.map x, ∀ b ∈ x N :: Ls.map x, Commute a b := by
    intro a ha b hb
    rw [← List.map_cons] at ha hb
    obtain ⟨M, -, rfl⟩ := List.mem_map.1 ha
    obtain ⟨M', -, rfl⟩ := List.mem_map.1 hb
    exact hC.chernCap_one_commute hP _ _ _ _
  have eE : PowerSeries.mk
      (chernCap.{u, u + 1} ((spaceModulePullback D hX.1 hP.1 π).obj E) r hrP) =
      ((Ls.map x).map fun a => 1 + PowerSeries.C a * PowerSeries.X).prod :=
    hcE.trans (by rw [List.map_map]; rfl)
  have hrsP := isFiniteLocallyFreeOfRank_tensorObj D.site D.base D.base_mem P hP.1 hrP h1P
  have eEL : PowerSeries.mk (chernCap.{u, u + 1} ((spaceModulePullback D hX.1 hP.1 π).obj E ⊗
      (spaceModulePullback D hX.1 hP.1 π).obj L) (r * 1) hrsP) =
      ((Ls.map x).map fun a => 1 + PowerSeries.C (a + x N) * PowerSeries.X).prod :=
    hcEL.trans (congrArg List.prod (by rw [List.map_map]; exact List.map_eq_flatMap.symm))
  have key := PowerSeries.coeff_list_prod_one_add_C_add_mul_X_of_commute (Ls.map x) (x N) hcomm i
  rw [← eE, ← eEL, List.length_map, hLlen] at key
  simp only [PowerSeries.coeff_mk] at key
  have hELP := isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem
    (ObjectProperty.homMk π : (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
      ⟨X, hX.1⟩) hEL
  have hiso : chernCap.{u, u + 1} ((spaceModulePullback D hX.1 hP.1 π).obj (E ⊗ L)) r hELP i =
      chernCap.{u, u + 1} ((spaceModulePullback D hX.1 hP.1 π).obj E ⊗
        (spaceModulePullback D hX.1 hP.1 π).obj L) (r * 1) hrsP i :=
    (chernCap_eq_of_iso hP (@Functor.Monoidal.μIso _ _ _ _ _ _ _ (modulePullbackMonoidal
      (ObjectProperty.homMk π : (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
        ⟨X, hX.1⟩)) E L).symm r hELP (Nat.mul_one r ▸ hrsP) i).trans
      (chernCap_rank_congr _ (Nat.mul_one r).symm _ _ i)
  exact eq_of_intertwines hg (fun α => hnat (E ⊗ L) r hEL hELP i α)
    (intertwines_finset_sum g _ fun j α => intertwines_zsmul g
      (intertwines_mul g (fun α => hnat E r hE hrP (i - j) α)
        (intertwines_pow g (fun α => hnat L 1 hL1 h1P 1 α) j)) _ α)
    (hiso.trans (key.trans (by rw [hy])))

end AlgebraicGeometry.Space

end
