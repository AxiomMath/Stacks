module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.RationalChowRing
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.BivariantPowerSumShortExact
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.KGroupChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCharacterKGroup
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PerfectTwist
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.WhitneyInvertible
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Rank
public import StacksCore.Tactic.StacksAttribute

/-!
# The Chern character as a ring map on `K_0(Vect(X))`

Let `(S, δ)` be as in Situation 02QL and let `X` be locally of finite type over `S`.
**Stacks 0FEM** records that the Chern character defines a canonical ring map

  `ch : K_0(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X) ⊗ 𝐐`

sending a generator `[ℰ]` to `ch(ℰ) = ∑_{p ≥ 0} ch_p(ℰ)`, `ch_p(ℰ) = P_p(ℰ)/p!`, and extended
additively; it is well defined by Stacks 0F9C and a ring map by Stacks 0F9D.

Here `∏_{i ≥ 0} A^i(X) ⊗ 𝐐` is `Stacks.Chow.fullRationalChowCohomology` at the Gysin system of the
first Chern class of an invertible module, with the ring structure
`Stacks.Chow.instRingFullRationalChowCohomology` (the Cauchy product of the products of
Stacks 0B75 with rational coefficients), and `ch(ℰ)` is `Stacks.Chow.moduleChernCharacter`, the
family `(ch_0(ℰ), ch_1(ℰ), …)` built from the power sums `P_p(ℰ)` of Stacks 0F9B evaluated at the
Chern classes of `ℰ`, for `ℰ` finite locally free of any rank.

## The two inputs, and what is proved here

* Additivity, Stacks 0F9C, is `Stacks.Chow.moduleChernCharacter_eq_add_of_shortExact`.
* Multiplicativity, Stacks 0F9D, is `Stacks.Chow.totalChernCharacterArbitraryRank_tensorObj`,
  stated for power series over `A^*(X) ⊗ 𝐐`. It is transported to `∏_{i ≥ 0} A^i(X) ⊗ 𝐐` along
  the injective ring map `Stacks.Chow.toRationalPowerSeriesRingHom`, which sends `ch(ℰ)` to that
  power series because `P_p(ℰ)` is homogeneous of degree `p`
  (`Stacks.Chow.isHomogeneous_modulePowerSumArbitraryRank`): `P_p` is weighted homogeneous of
  degree `p` in the Chern classes, the rank sitting in degree `0`.
* The value on the unit, `ch(𝒪_X) = 1`, is `Stacks.Chow.moduleChernCharacter_unitModule`: the rank
  of `𝒪_X` is `1` and its total Chern class is `1`, by Stacks 02SP.

## Main definitions

* `Stacks.Chow.moduleChernCharacterOrZero` — `ch(ℰ)`, and `0` off the finite locally free modules.
* `Stacks.Chow.chernCharacterRingHom` — **Stacks 0FEM**, the ring map.

## Main results

* `Stacks.Chow.moduleChernCharacter_tensorObj` — `ch(ℰ ⊗ ℱ) = ch(ℰ) ch(ℱ)` in
  `∏_{i ≥ 0} A^i(X) ⊗ 𝐐`.
* `Stacks.Chow.chernCharacterRingHom_spec` — **Stacks 0FEM**.

## References

* [Stacks Project, Tag 0FEM](https://stacks.math.columbia.edu/tag/0FEM)
* [Stacks Project, Tag 0F9C](https://stacks.math.columbia.edu/tag/0F9C)
* [Stacks Project, Tag 0F9D](https://stacks.math.columbia.edu/tag/0F9D)
* [Stacks Project, Tag 0ESX](https://stacks.math.columbia.edu/tag/0ESX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct

universe u

namespace Stacks.Chow

/-! ### Homogeneity of the power sums -/

namespace TotalChowClass

variable {C : ChowSituation.{u}} {Y : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]

/-- The zero class is homogeneous of every degree. -/
theorem isHomogeneous_zero (n : ℕ) : (0 : TotalChowClass C sY).IsHomogeneous n :=
  fun _ _ ↦ rfl

/-- A sum of classes homogeneous of degree `n` is homogeneous of degree `n`. -/
theorem IsHomogeneous.add {n : ℕ} {c d : TotalChowClass C sY} (hc : c.IsHomogeneous n)
    (hd : d.IsHomogeneous n) : (c + d).IsHomogeneous n := fun p hp ↦ by
  rw [add_apply, hc p hp, hd p hp, add_zero]

/-- The negative of a class homogeneous of degree `n` is homogeneous of degree `n`. -/
theorem IsHomogeneous.neg {n : ℕ} {c : TotalChowClass C sY} (hc : c.IsHomogeneous n) :
    (-c).IsHomogeneous n := fun p hp ↦ by
  rw [neg_apply, hc p hp, neg_zero]

/-- An integer multiple of a class homogeneous of degree `n` is homogeneous of degree `n`. -/
theorem IsHomogeneous.zsmul {n : ℕ} {c : TotalChowClass C sY} (hc : c.IsHomogeneous n) (k : ℤ) :
    (k • c).IsHomogeneous n := fun p hp ↦ by
  change k • c p = 0
  rw [hc p hp, smul_zero]

/-- A class homogeneous of degree `m` is homogeneous of degree `n` when `m = n`. -/
theorem IsHomogeneous.congr_degree {m n : ℕ} {c : TotalChowClass C sY} (hc : c.IsHomogeneous m)
    (h : m = n) : c.IsHomogeneous n :=
  h ▸ hc

/-- A finite sum of classes homogeneous of degree `n` is homogeneous of degree `n`. -/
theorem isHomogeneous_sum {ι : Type*} (s : Finset ι) {n : ℕ} (c : ι → TotalChowClass C sY)
    (h : ∀ i ∈ s, (c i).IsHomogeneous n) : (∑ i ∈ s, c i).IsHomogeneous n := fun p hp ↦ by
  rw [sum_apply]
  exact Finset.sum_eq_zero fun i hi ↦ h i hi p hp

/-- The image of a natural number is homogeneous of degree `0`. -/
theorem isHomogeneous_natCast (k : ℕ) : ((k : TotalChowClass C sY)).IsHomogeneous 0 := by
  induction k with
  | zero => rw [Nat.cast_zero]; exact isHomogeneous_zero 0
  | succ k ih => rw [Nat.cast_succ]; exact ih.add isHomogeneous_one

/-- Every power of `-1` is homogeneous of degree `0`. -/
theorem isHomogeneous_neg_one_pow (k : ℕ) : ((-1 : TotalChowClass C sY) ^ k).IsHomogeneous 0 := by
  induction k with
  | zero => rw [pow_zero]; exact isHomogeneous_one
  | succ k ih => rw [pow_succ]; exact ih.mul isHomogeneous_one.neg

/-- A class homogeneous of degree `p` is its own homogeneous component of degree `p`. -/
theorem IsHomogeneous.homComponent_eq {p : ℕ} {c : TotalChowClass C sY} (hc : c.IsHomogeneous p) :
    homComponent p c = c := by
  refine ext fun q ↦ ?_
  rw [homComponent_apply]
  split_ifs with h
  · rfl
  · exact (hc q h).symm

/-- **Newton's recursion is weighted homogeneous**: if the degree-zero term is homogeneous of
degree `0` and the `i`-th Chern class is homogeneous of degree `i`, the `p`-th power sum is
homogeneous of degree `p`. -/
theorem isHomogeneous_newtonPowerSum {r : TotalChowClass C sY} (hr : r.IsHomogeneous 0)
    {c : ℕ+ → TotalChowClass C sY} (hc : ∀ i : ℕ+, (c i).IsHomogeneous i) (p : ℕ) :
    (newtonPowerSum r c p).IsHomogeneous p := by
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    cases p with
    | zero => rw [newtonPowerSum_zero]; exact hr
    | succ p =>
      rw [newtonPowerSum_succ]
      refine IsHomogeneous.add (isHomogeneous_sum _ _ fun j hj ↦ ?_) ?_
      · have hjp := Finset.mem_range.mp hj
        refine (((isHomogeneous_neg_one_pow j).mul (hc _)).mul
          (ih (p - j) (by omega))).congr_degree ?_
        rw [Nat.succPNat_coe]
        omega
      · refine (((isHomogeneous_neg_one_pow p).mul
          ((isHomogeneous_natCast p).add isHomogeneous_one)).mul (hc _)).congr_degree ?_
        rw [Nat.succPNat_coe]
        omega

end TotalChowClass

section PowerSum

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **`P_p(ℰ)` is homogeneous of degree `p`**, for `ℰ` of constant rank. -/
theorem isHomogeneous_modulePowerSum (F : X.Modules) (r : ℕ)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r) (p : ℕ) :
    (modulePowerSum C sX F r hF p).IsHomogeneous p := by
  let := hF
  unfold modulePowerSum
  exact TotalChowClass.isHomogeneous_newtonPowerSum
    (TotalChowClass.isHomogeneous_one.zsmul _)
    (fun i ↦ TotalChowClass.isHomogeneous_homComponent _ _) p

variable (E : X.Modules) [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- **`P_p(ℰ)` is homogeneous of degree `p`**, for `ℰ` of any rank: it is so on every rank
locus. -/
theorem isHomogeneous_modulePowerSumArbitraryRank (p : ℕ) :
    (modulePowerSumArbitraryRank C sX E p).IsHomogeneous p := by
  have h : TotalChowClass.homComponent p (modulePowerSumArbitraryRank C sX E p) =
      modulePowerSumArbitraryRank C sX E p := by
    refine eq_modulePowerSumArbitraryRank_of_res_eq C sX E p fun r ↦ ?_
    rw [TotalChowClass.res_homComponent, res_modulePowerSumArbitraryRank_rankLocus]
    exact (isHomogeneous_modulePowerSum C _ _ r _ p).homComponent_eq
  rw [← h]
  exact TotalChowClass.isHomogeneous_homComponent p _

/-- The Chern character `(ch_p(ℰ))_p` of `∏_{i ≥ 0} A^i(X) ⊗ 𝐐` is sent to the power series over
`A^*(X) ⊗ 𝐐` whose coefficients are the `ch_p(ℰ) = P_p(ℰ)/p!`. -/
theorem toRationalPowerSeries_moduleChernCharacter :
    toRationalPowerSeries C sX (moduleChernCharacter C sX E) =
      totalChernCharacterArbitraryRank C sX E := by
  ext p
  rw [coeff_toRationalPowerSeries, coeff_totalChernCharacterArbitraryRank,
    moduleChernCharacter_apply, moduleChernCharacterComponent, rationalSingle_tmul,
    chernCharacterComponentArbitraryRank, modulePowerSumComponentArbitraryRank,
    (isHomogeneous_modulePowerSumArbitraryRank C sX E p).single_apply_eq]

end PowerSum

/-! ### Multiplicativity and the unit -/

section Ring

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **Stacks 0F9D in `∏_{i ≥ 0} A^i(X) ⊗ 𝐐`**: `ch(ℰ ⊗ ℱ) = ch(ℰ) ch(ℱ)`. -/
theorem moduleChernCharacter_tensorObj (E F : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F] :
    moduleChernCharacter C sX (Scheme.Modules.tensorObj E F) =
      moduleChernCharacter C sX E * moduleChernCharacter C sX F := by
  refine toRationalPowerSeries_injective ?_
  rw [toRationalPowerSeries_mul]
  simp only [toRationalPowerSeries_moduleChernCharacter,
    totalChernCharacterArbitraryRank_tensorObj]

/-- `𝒪_X` is finite locally free of rank `1`. -/
instance isFiniteLocallyFreeOfRank_unitModule :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (Scheme.unitModule X) 1 :=
  SheafOfModules.isFiniteLocallyFreeOfRank_unit X

/-- `𝒪_X` is finite locally free. -/
instance isFiniteLocallyFree_unitModule :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (Scheme.unitModule X) :=
  isFiniteLocallyFree_unit X

/-- The total Chern class of `𝒪_X` is `1`, by Stacks 02SP. -/
theorem totalChern_unitModule : totalChern C sX (Scheme.unitModule X) 1 = 1 := by
  refine TotalChowClass.ext_op fun g _ ↦ ?_
  let := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank (Scheme.unitModule X) 1 g
  refine (op_totalChern C sX _ 1 g).trans ?_
  rw [TotalChowClass.op_one]
  exact GenuineChern.chernFamily_eq_one_of_iso_unit C (g ≫ sX) _
    (Scheme.Modules.pullbackUnitIso g)

/-- The power sums of `𝒪_X`: `P_0(𝒪_X) = 1` and `P_p(𝒪_X) = 0` for `p > 0`. -/
theorem modulePowerSumArbitraryRank_unitModule (p : ℕ) :
    modulePowerSumArbitraryRank C sX (Scheme.unitModule X) p = if p = 0 then 1 else 0 := by
  rw [modulePowerSumArbitraryRank_eq_modulePowerSum C sX _ 1
    (isFiniteLocallyFreeOfRank_unitModule (X := X))]
  unfold modulePowerSum
  rw [totalChern_unitModule]
  split_ifs with hp
  · subst hp
    rw [newtonPowerSum_zero, Nat.cast_one, one_smul]
  · rw [newtonPowerSum_eq_of_pos _ 0 _ p (Nat.pos_of_ne_zero hp), TotalChowClass.newtonPowerSum_one]

/-- **`ch(𝒪_X) = 1`** in `∏_{i ≥ 0} A^i(X) ⊗ 𝐐`. -/
theorem moduleChernCharacter_unitModule :
    moduleChernCharacter C sX (Scheme.unitModule X) = 1 := by
  refine toRationalPowerSeries_injective ?_
  rw [toRationalPowerSeries_one]
  ext p
  rw [coeff_toRationalPowerSeries, moduleChernCharacter_apply, moduleChernCharacterComponent,
    modulePowerSumComponentArbitraryRank, modulePowerSumArbitraryRank_unitModule,
    PowerSeries.coeff_one]
  split_ifs with hp
  · subst hp
    rw [rationalSingle_tmul, TotalChowClass.isHomogeneous_one.single_apply_eq]
    simp [Algebra.TensorProduct.one_def]
  · rw [TotalChowClass.zero_apply, TensorProduct.tmul_zero, map_zero]

end Ring

/-! ### The ring map -/

section KGroup

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

open Classical in
/-- `ch(ℰ)` for a finite locally free module `ℰ`, and `0` for every other module: the assignment
on the generators of `K_0(Vect(X))` that the Chern character map extends. -/
def moduleChernCharacterOrZero (M : X.Modules) :
    fullRationalChowCohomology C (gysinSystemOfInvertible C) sX :=
  if _h : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M then
    moduleChernCharacter C sX M
  else 0

/-- For `ℰ` finite locally free, `moduleChernCharacterOrZero` at `ℰ` is `ch(ℰ)`. -/
theorem moduleChernCharacterOrZero_of_isFiniteLocallyFree (M : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M] :
    moduleChernCharacterOrZero C sX M = moduleChernCharacter C sX M := by
  rw [moduleChernCharacterOrZero, dite_eq_left
    ‹Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M›]

/-- For a module that is not finite locally free, `moduleChernCharacterOrZero` is `0`. -/
theorem moduleChernCharacterOrZero_of_not (M : X.Modules)
    (hM : ¬ Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M) :
    moduleChernCharacterOrZero C sX M = 0 := by
  rw [moduleChernCharacterOrZero, dite_eq_right hM]

/-- The Chern character map exists and is unique: the extension of `[ℰ] ↦ ch(ℰ)` to a ring map
on `K_0(Vect(X))`. -/
theorem existsUnique_chernCharacterRingHom :
    ∃! φ : VectorBundleKZero X →+* fullRationalChowCohomology C (gysinSystemOfInvertible C) sX,
      ∀ M : X.Modules, Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u}
        (R := X.ringCatSheaf) M → φ (VectorBundleKZero.classOf X M) =
          moduleChernCharacterOrZero C sX M := by
  refine VectorBundleKZero.existsUnique_ringHom_of_tensorMultiplicative X
    (moduleChernCharacterOrZero C sX) (moduleChernCharacterOrZero_of_not C sX) ?_ ?_ ?_
  · intro E F G f g w hE hF hG hf hg hex
    simp only [moduleChernCharacterOrZero_of_isFiniteLocallyFree]
    exact moduleChernCharacter_eq_add_of_shortExact C sX (ShortComplex.mk f g w)
      { exact := hex }
  · intro M N hM hN
    have := @AlgebraicGeometry.isFiniteLocallyFree_tensorObj X M N hM hN
    simp only [moduleChernCharacterOrZero_of_isFiniteLocallyFree]
    exact moduleChernCharacter_tensorObj C sX M N
  · exact (moduleChernCharacterOrZero_of_isFiniteLocallyFree C sX (Scheme.unitModule X)).trans
      (moduleChernCharacter_unitModule C sX)

/-- **Stacks 0FEM.** The Chern character map
`ch : K_0(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X) ⊗ 𝐐`, a ring homomorphism sending `[ℰ]` to `ch(ℰ)`. -/
def chernCharacterRingHom :
    VectorBundleKZero X →+* fullRationalChowCohomology C (gysinSystemOfInvertible C) sX :=
  (existsUnique_chernCharacterRingHom C sX).exists.choose

/-- **The value on a generator**: `ch([ℰ]) = ch(ℰ)`. -/
theorem chernCharacterRingHom_classOf (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    chernCharacterRingHom C sX (VectorBundleKZero.classOf X E) = moduleChernCharacter C sX E :=
  ((existsUnique_chernCharacterRingHom C sX).exists.choose_spec E inferInstance).trans
    (moduleChernCharacterOrZero_of_isFiniteLocallyFree C sX E)

/-- **The map is canonical**: a ring homomorphism sending every `[ℰ]` to `ch(ℰ)` is the Chern
character map. -/
theorem eq_chernCharacterRingHom
    (φ : VectorBundleKZero X →+* fullRationalChowCohomology C (gysinSystemOfInvertible C) sX)
    (hφ : ∀ (E : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E],
      φ (VectorBundleKZero.classOf X E) = moduleChernCharacter C sX E) :
    φ = chernCharacterRingHom C sX := by
  refine (existsUnique_chernCharacterRingHom C sX).unique (fun M hM ↦ ?_)
    ((existsUnique_chernCharacterRingHom C sX).exists.choose_spec)
  rw [hφ M, moduleChernCharacterOrZero_of_isFiniteLocallyFree]

/-- Let `X` be locally of finite type over the base of chapter 42. The Chern character defines a
canonical ring map

  `ch : K_0(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X) ⊗ 𝐐`

(`Stacks.Chow.chernCharacterRingHom`, a ring homomorphism into the ring
`Stacks.Chow.instRingFullRationalChowCohomology`) which

1. sends a generator `[ℰ]`, `ℰ` finite locally free of any rank, to `ch(ℰ)`, whose degree-`p`
   component is `ch_p(ℰ) = P_p(ℰ)/p!` (`Stacks.Chow.moduleChernCharacterComponent`);
2. is the only ring map with property 1 (it is obtained "by extending additively").

It is well defined by Stacks 0F9C (`Stacks.Chow.moduleChernCharacter_eq_add_of_shortExact`) and a
ring map by Stacks 0F9D (`Stacks.Chow.moduleChernCharacter_tensorObj`). -/
@[stacks 0FEM]
theorem chernCharacterRingHom_spec :
    (∀ (E : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E],
      chernCharacterRingHom C sX (VectorBundleKZero.classOf X E) = moduleChernCharacter C sX E ∧
        ∀ p : ℕ, chernCharacterRingHom C sX (VectorBundleKZero.classOf X E) p =
          ((Nat.factorial p : ℚ)⁻¹) ⊗ₜ[ℤ] modulePowerSumComponentArbitraryRank C sX E p) ∧
    (∀ φ : VectorBundleKZero X →+* fullRationalChowCohomology C (gysinSystemOfInvertible C) sX,
      (∀ (E : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E],
        φ (VectorBundleKZero.classOf X E) = moduleChernCharacter C sX E) →
      φ = chernCharacterRingHom C sX) :=
  ⟨fun E _ ↦ ⟨chernCharacterRingHom_classOf C sX E, fun p ↦ by
      rw [chernCharacterRingHom_classOf]; rfl⟩,
    eq_chernCharacterRingHom C sX⟩

end KGroup

end Stacks.Chow

end
