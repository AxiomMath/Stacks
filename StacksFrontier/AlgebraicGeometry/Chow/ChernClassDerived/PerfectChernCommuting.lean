module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TotalClassCommutingDescent
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PerfectPowerSum
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BivariantChernCap

/-!
# The Chern classes of a perfect object commute with bivariant classes

Let `(S, δ)` be as in Situation 02QL, let `g : X' ⟶ X` be locally of finite type, let
`c ∈ A^q(X' ⟶ X)`, let `h : Y ⟶ X` be locally of finite type and let `E ∈ D(𝒪_Y)` be an object
whose Chern classes are defined. Then

  `c ∩ (c_p(E) ∩ α) = c_p(E) ∩ (c ∩ α)`  and, for `E` perfect,
  `c ∩ (P_p(E) ∩ α) = P_p(E) ∩ (c ∩ α)`

for every test scheme `m : W ⟶ Y` and `α ∈ A_k(W)`, with `c` capping at `W ⟶ Y ⟶ X`. At `h` the
identity of `X` this is clause (2) of Stacks 0FAC; the form along `h` is the one used in the
proofs of Stacks 0FAJ and 0FAW.

## The argument

The proof is the source's, organized by `Stacks.Chow.TotalChowClass.CommutesWith`:

1. for a finite locally free module the identity is Stacks 02UA (2), on the test schemes
   (`Stacks.Chow.GenuineChern.chernCap_cap`);
2. the total Chern class of a bounded complex of finite locally free modules of constant ranks is
   a product of total Chern classes of modules and their inverses, and the total classes
   commuting with `c` form a subring closed under these inverses;
3. the total Chern class of a locally bounded complex is glued from those of its restrictions to
   the rank loci, a decomposition into open and closed subschemes;
4. the class of `E` restricts along the envelope of a presentation to that of the presenting
   complex, and commuting descends along envelopes (Stacks 02UC and 0GUF).

The classes `P_p(E)` are Newton's polynomials in the Chern classes for `p ≥ 1` and the rank,
glued from integers over the loci of constant Euler characteristic, for `p = 0`.

## Main results

* `Stacks.Chow.TotalChowClass.commutesWith_perfectChernClass` — `c(E)` commutes with `c`.
* `Stacks.Chow.TotalChowClass.commutesWith_perfectPowerSumTotal` — `(P_p(E))_p` commutes
  with `c`.

## References

* [Stacks Project, Tag 0FAC](https://stacks.math.columbia.edu/tag/0FAC)
* [Stacks Project, Tag 02UA](https://stacks.math.columbia.edu/tag/02UA)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 0GUF](https://stacks.math.columbia.edu/tag/0GUF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

namespace TotalChowClass

variable {C : ChowSituation.{u}} {X X' Y : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
  {g : X' ⟶ X} [LocallyOfFiniteType g] {q : ℤ}
  {c : BivariantClass C (gysinSystemOfInvertible C) (g ≫ sX) sX g rfl q}
  {h : Y ⟶ X} [LocallyOfFiniteType h] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
  {hY : h ≫ sX = sY}

/-- The Chern class cap products of Stacks 02U6 only depend on the structure morphism up to
equality. -/
theorem chernCap_heq_of_eq {T : Scheme.{u}} {q₁ q₂ : T ⟶ C.S} [LocallyOfFiniteType q₁]
    [LocallyOfFiniteType q₂] (hq : q₁ = q₂) (r : ℕ) (F : T.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] (k : ℤ) (j : Fin (r + 1))
    {α : chowGroup C q₁ k} {α' : chowGroup C q₂ k} (hα : α ≍ α') :
    GenuineChern.chernCap C r q₁ F k j α ≍ GenuineChern.chernCap C r q₂ F k j α' := by
  subst hq
  cases hα
  rfl

variable (C sX g c h sY hY) in
/-- **Stacks 02UA (2) on the test schemes**: the total Chern class of a finite locally free
module commutes with every bivariant class. -/
theorem commutesWith_totalChern (F : Y.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] :
    (totalChern C sY F r).CommutesWith C sX g c h sY hY := by
  intro W m _
  refine GradedCapFamily.Intertwines.iff_heq.2 fun k j α ↦ ?_
  by_cases hj : j ≤ r
  · let jj : Fin (r + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
    let := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r m
    let := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r
      (pullback.snd g (m ≫ h) ≫ m)
    let := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (pullback.snd g (m ≫ h))
      ((Scheme.Modules.pullback m).obj F) r
    have e₁ := op_totalChern_apply C sY F r m k jj α
    have e₂ := op_totalChern_apply C sY F r (pullback.snd g (m ≫ h) ≫ m) (k - q) jj
      (capAlong C sX g c h sY hY m k α)
    have hα' : chowGroupCongr C (comp_structure_eq C sX h sY hY m) k α ≍ α :=
      chowGroupCongr_heq C _ k α
    have key := GenuineChern.chernCap_cap (BivariantChowClass.equivBivariantClass.symm c)
      (m ≫ h) ((Scheme.Modules.pullback m).obj F) r
      ((Scheme.Modules.pullback (pullback.snd g (m ≫ h) ≫ m)).obj F)
      ((Scheme.Modules.pullbackComp (pullback.snd g (m ≫ h)) m).app F).symm k jj
      (chowGroupCongr C (comp_structure_eq C sX h sY hY m) k α)
    show capAlong C sX g c h sY hY m (k - jj) ((totalChern C sY F r).op m k jj α) ≍
      (totalChern C sY F r).op (pullback.snd g (m ≫ h) ≫ m) (k - q) jj
        (capAlong C sX g c h sY hY m k α)
    rw [e₁, e₂]
    refine (capAlong_heq C sX g c h sY hY m (k - jj) _ _
      (chernCap_heq_of_eq (comp_structure_eq C sX h sY hY m) r _ k jj hα'.symm)).trans ?_
    refine ((chowGroupCast_heq C _ _ _).symm.trans (heq_of_eq key.symm)).trans ?_
    exact chernCap_heq_of_eq (testStructure_eq C sX g h sY hY m) r _ (k - q) jj
      ((capAlong_heq C sX g c h sY hY m k α _ hα'.symm).symm)
  · have hj' : r < j := Nat.lt_of_not_le hj
    rw [op_totalChern_of_lt C sY F r m k hj', op_totalChern_of_lt C sY F r _ (k - q) hj',
      AddMonoidHom.zero_apply, AddMonoidHom.zero_apply, map_zero]
    exact (heq_of_eq (AddEquiv.map_zero (chowGroupDegreeEquiv C _
      (by ring : k - q - (j : ℤ) = k - (j : ℤ) - q))).symm).trans
      (chowGroupDegreeEquiv_heq C _ _ 0)

/-- Integer powers of a unit `1 + x_1 + x_2 + ⋯` commuting with `c` commute with `c`. -/
theorem CommutesWith.zpow (x : (TotalChowClass C sY)ˣ)
    (hx0 : (x : TotalChowClass C sY) 0 = (1 : TotalChowClass C sY) 0)
    (hx : (x : TotalChowClass C sY).CommutesWith C sX g c h sY hY) (z : ℤ) :
    (↑(x ^ z) : TotalChowClass C sY).CommutesWith C sX g c h sY hY := by
  cases z with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, zpow_natCast, Units.val_pow_eq_pow_val]
    exact CommutesWith.pow hx n
  | negSucc n =>
    rw [zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val]
    exact CommutesWith.pow (CommutesWith.inv x hx0 hx) (n + 1)

variable (C sX g c h sY hY) in
/-- The total Chern class `c(P) = ∏ c(P^n)^{(-1)^n}` of a bounded complex of finite locally free
modules of constant ranks commutes with every bivariant class. -/
theorem commutesWith_complexChernBounded (P : CochainComplex Y.Modules ℤ) (ρ : ℤ →₀ ℕ)
    (hP : ∀ n, SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n)) :
    (complexChernBounded C sY P ρ hP).CommutesWith C sX g c h sY hY := by
  rw [complexChernBounded, complexChernProd, ← Units.coeHom_apply, map_list_prod,
    List.map_map]
  refine CommutesWith.list_prod fun x hx ↦ ?_
  obtain ⟨n, -, rfl⟩ := List.mem_map.1 hx
  let := hP n
  refine CommutesWith.zpow _ ?_ ?_ _
  · rw [val_totalChernUnit]
    exact totalChern_apply_zero C sY (P.X n) (ρ n)
  · rw [val_totalChernUnit]
    exact commutesWith_totalChern C sX g c h sY hY (P.X n) (ρ n)

variable (C sX g c h sY hY) in
/-- The total Chern class of a locally bounded complex of finite locally free modules commutes
with every bivariant class: it is glued from the classes of its restrictions to the rank loci. -/
theorem commutesWith_complexChern {P : CochainComplex Y.Modules ℤ}
    (hP : IsLocallyBoundedFiniteLocallyFree P) :
    (complexChern C sY hP).CommutesWith C sX g c h sY hY := by
  refine CommutesWith.of_isClopenDecomposition (c := c) (hY := hY)
    (isClopenDecomposition_complexRankLoci hP) fun ρ ↦ ?_
  rw [res_complexChern_complexRankLocus]
  exact commutesWith_complexChernBounded C sX g c _ _ _ _ _
    (isFiniteLocallyFreeOfRank_complexRankLocus hP ρ.down)

variable (C sX g c h sY hY) in
/-- **The total Chern class of an object whose Chern classes are defined commutes with every
bivariant class**: `c ∩ (c_p(E) ∩ α) = c_p(E) ∩ (c ∩ α)`. It restricts along the envelope of a
presentation to the class of the presenting complex, and commuting descends along envelopes. -/
theorem commutesWith_perfectChernClass {E : DerivedCategory Y.Modules}
    (hE : HasDefinedChernClasses E) :
    (perfectChernClass C sY hE).CommutesWith C sX g c h sY hY := by
  set H := hE.some
  have : IsProper H.f := H.envelope.isProper
  refine CommutesWith.of_isEnvelope (c := c) (hY := hY) H.f H.envelope (H.f ≫ sY) rfl ?_
  rw [res_perfectChernClass C sY hE H]
  exact commutesWith_complexChern C sX g c _ _ _ H.locallyBounded

/-! ### The classes `P_p` -/

/-- Homogeneous components of a total class commuting with `c` commute with `c`. -/
theorem CommutesWith.homComponent {x : TotalChowClass C sY}
    (hx : x.CommutesWith C sX g c h sY hY) (i : ℕ) :
    (TotalChowClass.homComponent i x).CommutesWith C sX g c h sY hY := by
  intro W m _
  rw [op_homComponent, op_homComponent]
  exact (hx m).homComponent i

/-- Newton's power sums of the homogeneous components of a total class commuting with `c`
commute with `c`. -/
theorem CommutesWith.newtonComponents {x : TotalChowClass C sY}
    (hx : x.CommutesWith C sX g c h sY hY) (n : ℕ) :
    (TotalChowClass.newtonComponents x n).CommutesWith C sX g c h sY hY := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · rw [TotalChowClass.newtonComponents, newtonPowerSum_zero]
      exact CommutesWith.zero
    · rw [TotalChowClass.newtonComponents, newtonPowerSum_succ_zsmul]
      refine CommutesWith.add (CommutesWith.sum _ fun j hj ↦ ?_) ?_
      · exact CommutesWith.zsmul (CommutesWith.mul (CommutesWith.homComponent hx _)
          (ih (n - j) (by omega))) _
      · exact CommutesWith.zsmul (CommutesWith.homComponent hx _) _

variable (C sX g c h sY hY) in
/-- The rank `P_0(E) = r(E)` of a perfect object commutes with every bivariant class: on each
locus of constant Euler characteristic `n` it is `n` times the unit. -/
theorem commutesWith_perfectRankClass {E : DerivedCategory Y.Modules}
    (perfect : RingedSpace.IsPerfect.{u, u + 1} (X := Y.toRingedSpace) E)
    (hE : HasDefinedChernClasses E) :
    (perfectRankClass C sY hE).CommutesWith C sX g c h sY hY := by
  rw [perfectRankClass_eq_glue_eulerLoci perfect C sY hE]
  refine CommutesWith.of_isClopenDecomposition (c := c) (hY := hY)
    (isClopenDecomposition_eulerLoci perfect) fun n ↦ ?_
  rw [res_glue]
  exact CommutesWith.zsmul CommutesWith.one _

variable (C sX g c h sY hY) in
/-- **The classes `P_p(E)` of a perfect object commute with every bivariant class**:
`c ∩ (P_p(E) ∩ α) = P_p(E) ∩ (c ∩ α)`. -/
theorem commutesWith_perfectPowerSumTotal {E : DerivedCategory Y.Modules}
    (perfect : RingedSpace.IsPerfect.{u, u + 1} (X := Y.toRingedSpace) E)
    (hE : HasDefinedChernClasses E) :
    (perfectPowerSumTotal C sY hE).CommutesWith C sX g c h sY hY := by
  rw [commutesWith_iff]
  intro W m _ n k α
  rw [perfectPowerSumTotal_apply]
  rcases n with _ | n
  · rw [perfectPowerSumComponent_zero]
    exact (commutesWith_iff ..).1
      (commutesWith_perfectRankClass C sX g c h sY hY perfect hE) m 0 k α
  · rw [perfectPowerSumComponent_succ]
    exact (commutesWith_iff ..).1
      (CommutesWith.newtonComponents (commutesWith_perfectChernClass C sX g c h sY hY hE)
        (n + 1)) m (n + 1) k α

end TotalChowClass

end Stacks.Chow

end
