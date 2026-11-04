module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Tactic.LinearCombination
public import StacksFrontier.RingTheory.Cech.Substrate

/-!
# The extended alternating Čech complex is contractible when some `f i` is a unit

Let `R` be a commutative ring, `f : Fin r → R` and `M` an `R`-module. If some `f i` is a unit,
then the extended alternating Čech complex `Cech.cechComplex f M` of `M` is homotopy equivalent
to `0`: the identity chain map is chain homotopic to the zero chain map. The contracting homotopy
deletes the index `i` from a summand indexed by a set containing `i`, with the Čech sign, using
that inverting the unit `f i` does not change a localization.

## Main definitions

* `Stacks.CechContractible.cechιInvEquivOfIsUnit`: for `f i` a unit and `i ∈ S`, the linear
  equivalence `M_{∏S} ≃ₗ M_{∏(S \ {i})}` inverse to the canonical localization map.
* `Stacks.CechContractible.cechHomotopyHom`: the contracting homotopy of the extended alternating
  Čech complex, as a family of linear maps.
* `Stacks.CechContractible.contractingHomotopy`: that family packaged as a `Homotopy` between `𝟙`
and `0`.

## Main results

* `Stacks.CechContractible.cechHomotopyHom_comm`: the homotopy identity `dh + hd = 𝟙` in each
degree.
* `Stacks.CechContractible.cechComplex_nullHomotopic`: the extended alternating Čech complex is
  homotopy equivalent to `0` when some `f i` is a unit.

## References

* [Stacks: Tag 0G6J](https://stacks.math.columbia.edu/tag/0G6J)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Cech

namespace Stacks.CechContractible

noncomputable section

variable {R : Type*} [CommRing R] {r : ℕ} (f : Fin r → R)
  (M : Type*) [AddCommGroup M] [Module R M]

/-- The value of the differential `Cech.cechD` on a generator `lof T x`, as a finite sum over
`k ∉ T` of the localized images of `x` placed in the summands `insert k T`, with the guard
`k ∈ Tᶜ` carried by a `dite`. -/
theorem cechD_lof_sum_compl (p : ℕ)
    (T : {s : Finset (Fin r) // s.card = p}) (x : cechMod f M T.1) :
    cechD f M p (DirectSum.lof R {s : Finset (Fin r) // s.card = p}
        (fun s => cechMod f M s.1) T x)
      = ∑ k ∈ T.1ᶜ, if h : k ∈ T.1ᶜ then
          (cechSign (insert k T.1) k) • DirectSum.lof R {s : Finset (Fin r) // s.card = p+1}
            (fun s => cechMod f M s.1)
            ⟨insert k T.1, by
              rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp h), T.2]⟩
            (cechι f M (Finset.subset_insert k T.1) x)
        else 0 := by
  rw [cechD_lof, ← Finset.sum_attach T.1ᶜ (fun k => if h : k ∈ T.1ᶜ then
      (cechSign (insert k T.1) k) • DirectSum.lof R {s : Finset (Fin r) // s.card = p+1}
        (fun s => cechMod f M s.1)
        ⟨insert k T.1, by
          rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp h), T.2]⟩
        (cechι f M (Finset.subset_insert k T.1) x)
      else 0)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dite_eq_left i.2, cechSign_insert]

/-- Čech sign cancellation: for `k ≠ j` not in `T`, the products of the insertion signs along the
two orders of inserting `k` and `j` into `T` are opposite. -/
theorem cechSign_insert_mul_insert_eq_neg_swap (k j : Fin r) (hkj : k ≠ j) (T : Finset (Fin r))
    (hk : k ∉ T) (hj : j ∉ T) :
    cechSign (insert k T) k * cechSign (insert j (insert k T)) j
      = - (cechSign (insert j T) j * cechSign (insert k (insert j T)) k) := by
  simp only [cechSign_insert]
  exact cechSign_swap T hkj hk hj

/-- If `f i` is a unit, then `M_{∏(S \ {i})}` is a localization of `M` at the submonoid generated
by the elements `f j`, `j ∈ S`. -/
theorem isLocalizedModule_closure_erase_of_isUnit
    {i : Fin r} (hi : IsUnit (f i)) (S : Finset (Fin r)) :
    IsLocalizedModule (Submonoid.closure (f '' (S : Set (Fin r))))
      (LocalizedModule.mkLinearMap (cechSub f (S.erase i)) M) := by
  have hle : cechSub f (S.erase i) ≤ Submonoid.closure (f '' (S : Set (Fin r))) :=
    (cechSub_le_closure f (Finset.erase_subset i S))
  have hunit : ∀ x : Submonoid.closure (f '' (S : Set (Fin r))),
      IsUnit ((algebraMap R
        (Module.End R (cechMod f M (S.erase i)))) (x : R)) := by
    have hsub : Submonoid.closure (f '' (S : Set (Fin r))) ≤ Submonoid.comap
        (algebraMap R (Module.End R (cechMod f M (S.erase i))))
          (IsUnit.submonoid _) := by
      apply Submonoid.closure_le.mpr
      rintro _ ⟨j, hj, rfl⟩
      rw [SetLike.mem_coe, Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
      by_cases hji : j = i
      · subst hji; exact hi.map _
      · have hjE : j ∈ S.erase i := Finset.mem_erase.mpr ⟨hji, by exact_mod_cast hj⟩
        have hmem : f j ∈ Submonoid.closure
            (f '' ((S.erase i : Finset (Fin r)) : Set (Fin r))) := by
          apply Submonoid.subset_closure; exact ⟨j, by exact_mod_cast hjE, rfl⟩
        exact IsLocalizedModule.map_units
          (LocalizedModule.mkLinearMap (cechSub f (S.erase i)) M) ⟨f j, hmem⟩
    intro x
    have hx := hsub x.2
    rw [Submonoid.mem_comap, IsUnit.mem_submonoid_iff] at hx
    exact hx
  refine ⟨hunit, ?_, ?_⟩
  · intro y
    obtain ⟨⟨m, s⟩, hms⟩ := IsLocalizedModule.surj (cechSub f (S.erase i))
      (LocalizedModule.mkLinearMap (cechSub f (S.erase i)) M) y
    exact ⟨⟨m, ⟨s, hle s.2⟩⟩, hms⟩
  · intro x₁ x₂ hx
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := cechSub f (S.erase i))
      (f := LocalizedModule.mkLinearMap (cechSub f (S.erase i)) M) hx
    exact ⟨⟨c, hle c.2⟩, hc⟩

/-- The canonical map `M_{∏(S\{i})} → M_{∏S}` is bijective when `f i` is a unit. -/
theorem cechι_bijective_of_isUnit
    {i : Fin r} (hi : IsUnit (f i)) (S : Finset (Fin r)) :
    Function.Bijective (cechι f M (Finset.erase_subset i S)) := by
  have := isLocalizedModule_closure_erase_of_isUnit f M hi S
  have key : cechι f M (Finset.erase_subset i S)
      = (IsLocalizedModule.linearEquiv (Submonoid.closure (f '' (S : Set (Fin r))))
          (LocalizedModule.mkLinearMap (cechSub f (S.erase i)) M)
          (LocalizedModule.mkLinearMap (cechSub f S) M)).toLinearMap := by
    refine IsLocalizedModule.ext (Submonoid.closure (f '' (S : Set (Fin r))))
      (LocalizedModule.mkLinearMap (cechSub f (S.erase i)) M)
      (fun x => IsLocalizedModule.map_units
        (LocalizedModule.mkLinearMap (cechSub f S) M) x) ?_
    refine LinearMap.ext fun m => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, cechι_mk,
      IsLocalizedModule.linearEquiv_apply]
  rw [key]
  exact (IsLocalizedModule.linearEquiv _ _ _).bijective

/-- For `f i` a unit and `i ∈ S`, the linear equivalence `M_{∏S} ≃ₗ M_{∏(S \ {i})}` inverse to the
canonical localization map.

The hypothesis `_hiS` is not used in the construction; it records the regime in which this
equivalence is intended. -/
def cechιInvEquivOfIsUnit
    {i : Fin r} (hi : IsUnit (f i)) (S : Finset (Fin r)) (_hiS : i ∈ S) :
    cechMod f M S ≃ₗ[R] cechMod f M (S.erase i) :=
  (LinearEquiv.ofBijective (cechι f M (Finset.erase_subset i S))
    (cechι_bijective_of_isUnit f M hi S)).symm

/-- The contracting homotopy of the extended alternating Čech complex, as a family of `R`-linear
maps `C^a → C^b`. For `hi : IsUnit (f i)`, it sends the summand indexed by an `a`-element subset
`S` to the summand `S.erase i` via `cechSign S i • cechιInvEquivOfIsUnit … S` when `b + 1 = a` and
`i ∈ S`, and is `0` otherwise. -/
def cechHomotopyHom
    {i : Fin r} (hi : IsUnit (f i)) (a b : ℕ) :
    cechTerm f M a →ₗ[R] cechTerm f M b :=
  DirectSum.toModule R _ _ (fun S =>
    if hba : b + 1 = a then
      if hiS : i ∈ S.1 then
        (cechSign S.1 i) •
          (DirectSum.lof R {s : Finset (Fin r) // s.card = b}
              (fun s => cechMod f M s.1)
              ⟨S.1.erase i, by
                rw [Finset.card_erase_of_mem hiS, S.2]; omega⟩).comp
            (cechιInvEquivOfIsUnit f M hi S.1 hiS).toLinearMap
      else (0 : cechMod f M S.1 →ₗ[R]
              cechTerm f M b)
    else (0 : cechMod f M S.1 →ₗ[R]
            cechTerm f M b))

/-- The inverse of `cechιInvEquivOfIsUnit` is the canonical localization map `Cech.cechι` along
`S.erase i ⊆ S`. -/
@[simp]
theorem cechιInvEquivOfIsUnit_symm_eq_cechι
    {i : Fin r} (hiu : IsUnit (f i)) (S : Finset (Fin r)) (hiS : i ∈ S) :
    (cechιInvEquivOfIsUnit f M hiu S hiS).symm
      = cechι f M (Finset.erase_subset i S) := by
  rw [cechιInvEquivOfIsUnit, LinearEquiv.symm_symm]
  rfl

/-- `cechιInvEquivOfIsUnit` undoes the canonical localization map `Cech.cechι` along
`S.erase i ⊆ S`. -/
@[simp]
theorem cechιInvEquivOfIsUnit_cechι_apply
    {i : Fin r} (hiu : IsUnit (f i)) (S : Finset (Fin r)) (hiS : i ∈ S)
    (z : cechMod f M (S.erase i)) :
    (cechιInvEquivOfIsUnit f M hiu S hiS) (cechι f M (Finset.erase_subset i S) z) = z := by
  rw [← cechιInvEquivOfIsUnit_symm_eq_cechι f M hiu S hiS]
  exact (cechιInvEquivOfIsUnit f M hiu S hiS).apply_symm_apply z

/-- A generator `lof S x` evaluated at a component `U`, as a `dite` on `S = U`. -/
private theorem lof_apply_eq_dite {n : ℕ} (S U : {s : Finset (Fin r) // s.card = n})
    (x : cechMod f M S.1) :
    (DirectSum.lof R {s : Finset (Fin r) // s.card = n} (fun s => cechMod f M s.1) S x) U
      = if hU : S = U then hU ▸ x else 0 := by
  rw [DirectSum.apply_eq_component (R := R), DirectSum.component.of]

/-- An integer multiple of a generator `lof S x` evaluated at a component `U`. -/
private theorem zsmul_lof_apply_eq_dite {n : ℕ} (c : ℤ) (S U : {s : Finset (Fin r) // s.card = n})
    (x : cechMod f M S.1) :
    (c • DirectSum.lof R {s : Finset (Fin r) // s.card = n} (fun s => cechMod f M s.1) S x) U
      = if hU : S = U then c • (hU ▸ x) else 0 := by
  rw [show ∀ z : DirectSum _ fun s : {s : Finset (Fin r) // s.card = n} => cechMod f M s.1,
    (c • z) U = c • z U from fun _ => rfl, lof_apply_eq_dite]
  split_ifs
  exacts [rfl, zsmul_zero _]

/-- Localizing the deletion of the unit `i` recovers the element. -/
private theorem cechι_cechιInvEquivOfIsUnit_apply
    {i : Fin r} (hiu : IsUnit (f i)) (S : Finset (Fin r)) (hiS : i ∈ S) (y : cechMod f M S) :
    cechι f M (Finset.erase_subset i S) (cechιInvEquivOfIsUnit f M hiu S hiS y) = y := by
  rw [← cechιInvEquivOfIsUnit_symm_eq_cechι f M hiu S hiS]
  exact (cechιInvEquivOfIsUnit f M hiu S hiS).symm_apply_apply y

/-- The value of `cechHomotopyHom` on a generator `lof S y`. -/
theorem cechHomotopyHom_lof
    {i : Fin r} (hi : IsUnit (f i)) (a b : ℕ) (hba : b + 1 = a)
    (S : {s : Finset (Fin r) // s.card = a}) (y : cechMod f M S.1) :
    cechHomotopyHom f M hi a b (DirectSum.lof R {s : Finset (Fin r) // s.card = a}
        (fun s => cechMod f M s.1) S y)
      = if hiS : i ∈ S.1 then
          (cechSign S.1 i) • DirectSum.lof R {s : Finset (Fin r) // s.card = b}
            (fun s => cechMod f M s.1)
            ⟨S.1.erase i, by
              rw [Finset.card_erase_of_mem hiS, S.2]; omega⟩
            ((cechιInvEquivOfIsUnit f M hi S.1 hiS) y)
        else 0 := by
  rw [cechHomotopyHom, DirectSum.toModule_lof, dite_eq_left hba]
  by_cases hiS : i ∈ S.1
  · rw [dite_eq_left hiS, dite_eq_left hiS]
    simp only [LinearMap.smul_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearEquiv.coe_coe]
  · rw [dite_eq_right hiS, dite_eq_right hiS]; rfl

/-- The `U`-component of `cechHomotopyHom` applied to a generator `lof S y`. -/
theorem cechHomotopyHom_lof_apply
    {i : Fin r} (hi : IsUnit (f i)) (a b : ℕ) (hba : b + 1 = a)
    (V : {s : Finset (Fin r) // s.card = a}) (v : cechMod f M V.1)
    (U : {s : Finset (Fin r) // s.card = b}) :
    (cechHomotopyHom f M hi a b (DirectSum.lof R {s : Finset (Fin r) // s.card = a}
        (fun s => cechMod f M s.1) V v)) U
      = if hiV : i ∈ V.1 then
          (if hU : (⟨V.1.erase i, by
                rw [Finset.card_erase_of_mem hiV, V.2]; omega⟩ :
                {s : Finset (Fin r) // s.card = b}) = U then
            (cechSign V.1 i) •
              (hU ▸ (cechιInvEquivOfIsUnit f M hi V.1 hiV) v)
          else 0)
        else 0 := by
  rw [cechHomotopyHom_lof f M hi a b hba V v]
  by_cases hiV : i ∈ V.1
  · rw [dite_eq_left hiV, dite_eq_left hiV]
    exact zsmul_lof_apply_eq_dite f M _ _ _ _
  · rw [dite_eq_right hiV, dite_eq_right hiV]
    rfl

/-- The `U`-component of `Cech.cechD` applied to a generator `lof S y`, in any degree `p`. -/
theorem cechD_lof_apply (p : ℕ)
    (V : {s : Finset (Fin r) // s.card = p}) (z : cechMod f M V.1)
    (U : {s : Finset (Fin r) // s.card = p+1}) :
    (cechD f M p (DirectSum.lof R {s : Finset (Fin r) // s.card = p}
        (fun s => cechMod f M s.1) V z)) U
      = ∑ m ∈ V.1ᶜ, if h : m ∈ V.1ᶜ then
          (if hU : (⟨insert m V.1, by
                rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp h), V.2]⟩ :
                {s : Finset (Fin r) // s.card = p+1}) = U then
            (cechSign (insert m V.1) m) • (hU ▸ cechι f M (Finset.subset_insert m V.1) z)
          else 0)
        else 0 := by
  classical
  rw [cechD_lof_sum_compl, DFinsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro m hm
  rw [dite_eq_left hm, dite_eq_left hm]
  exact zsmul_lof_apply_eq_dite f M _ _ _ _

/-- `cechSign` squares to `1` (it is `±1`). -/
@[simp]
theorem cechSign_mul_self (k : Fin r) (S : Finset (Fin r)) : cechSign S k * cechSign S k = 1 := by
  unfold cechSign
  rw [← pow_add, ← two_mul, pow_mul]
  simp

/-- Transport an element of a localized module along a subtype equality (`▸`), reduced to `HEq`. -/
theorem cechMod_eqRec_eq_of_heq (n : ℕ)
    (V S : {s : Finset (Fin r) // s.card = n}) (hU : V = S)
    (e : cechMod f M V.1) (y : cechMod f M S.1)
    (hey : HEq e y) : (hU ▸ e) = y := by
  subst hU; simp only [eq_of_heq hey]

/-- `Cech.cechι` is `HEq`-congruent when the source sets are equal and the inputs are `HEq`. -/
theorem cechι_heq_of_source_eq
    {s₁ s₂ t : Finset (Fin r)} (h₁ : s₁ ⊆ t) (h₂ : s₂ ⊆ t) (hs : s₁ = s₂)
    (x₁ : cechMod f M s₁) (x₂ : cechMod f M s₂)
    (hx : HEq x₁ x₂) :
    HEq (cechι f M h₁ x₁) (cechι f M h₂ x₂) := by
  subst hs; rw [eq_of_heq hx]

/-- Expansion of the first homotopy term `h ∘ d` applied to `lof S y`, taken at component `U`,
in any degree `p`. -/
theorem cechHomotopyHom_cechD_lof_apply
    {i : Fin r} (hiu : IsUnit (f i)) (p : ℕ)
    (S : {s : Finset (Fin r) // s.card = p}) (y : cechMod f M S.1)
    (U : {s : Finset (Fin r) // s.card = p}) :
    ((cechHomotopyHom f M hiu (p + 1) p)
          ((cechD f M p)
            ((DirectSum.lof R { s : Finset (Fin r) // s.card = p }
              (fun s => cechMod f M s.1) S) y))) U
    = ∑ k ∈ S.1ᶜ, if hk : k ∈ S.1ᶜ then
        cechSign (insert k S.1) k •
          ((cechHomotopyHom f M hiu (p+1) p
            (DirectSum.lof R {s : Finset (Fin r) // s.card = p+1}
              (fun s => cechMod f M s.1)
              ⟨insert k S.1, by rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp hk), S.2]⟩
              (cechι f M (Finset.subset_insert k S.1) y))) U)
        else 0 := by
  classical
  rw [cechD_lof_sum_compl, map_sum, DFinsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rw [dite_eq_left hk, dite_eq_left hk, map_zsmul]
  rfl

/-- Deleting the unit `i` from `insert i S` after localizing into it recovers `y` (as `HEq`). -/
theorem cechιInvEquivOfIsUnit_cechι_insert_heq
    {i : Fin r} (hiu : IsUnit (f i)) (S : Finset (Fin r)) (y : cechMod f M S)
    (hiSset : i ∉ S) (hiIns : i ∈ insert i S) :
    HEq ((cechιInvEquivOfIsUnit f M hiu (insert i S) hiIns)
          ((cechι f M (Finset.subset_insert i S)) y)) y := by
  have heq : (insert i S).erase i = S := Finset.erase_insert hiSset
  set z : LocalizedModule (cechSub f ((insert i S).erase i)) M := cast (by rw [heq]) y with hz
  have hzy : HEq z y := by rw [hz]; exact cast_heq _ _
  have hround := cechιInvEquivOfIsUnit_cechι_apply f M hiu (insert i S) hiIns z
  have hlm : HEq ((cechι f M (Finset.erase_subset i (insert i S))) z)
      ((cechι f M (Finset.subset_insert i S)) y) :=
    cechι_heq_of_source_eq f M (Finset.erase_subset i (insert i S)) (Finset.subset_insert i S)
      heq z y hzy
  have hlm' : (cechι f M (Finset.erase_subset i (insert i S))) z
      = (cechι f M (Finset.subset_insert i S)) y := eq_of_heq hlm
  have hap := congrArg (cechιInvEquivOfIsUnit f M hiu (insert i S) hiIns) hlm'
  rw [hround] at hap
  rw [← hap]; exact hzy

/-- `Cech.cechι` is `HEq`-congruent under equality of the (common-source) target sets. -/
theorem cechι_heq_of_target_eq
    {s t₁ t₂ : Finset (Fin r)} (h₁ : s ⊆ t₁) (h₂ : s ⊆ t₂) (ht : t₁ = t₂)
    (x : cechMod f M s) :
    HEq (cechι f M h₁ x) (cechι f M h₂ x) := by
  subst ht; rfl

/-- Naturality of `cechιInvEquivOfIsUnit` under inserting an index: deleting the unit `i` after
inserting `k` agrees with localizing along `S.erase i ⊆ (insert k S).erase i` after deleting
`i`. -/
theorem cechιInvEquivOfIsUnit_naturality_insert
    {i : Fin r} (hiu : IsUnit (f i)) (S : Finset (Fin r)) (hiS : i ∈ S)
    (k : Fin r) (y : cechMod f M S)
    (hiIns : i ∈ insert k S)
    (hsub : S.erase i ⊆ (insert k S).erase i) :
    (cechιInvEquivOfIsUnit f M hiu (insert k S) hiIns) ((cechι f M (Finset.subset_insert k S)) y)
      = (cechι f M hsub) ((cechιInvEquivOfIsUnit f M hiu S hiS) y) := by
  set z := (cechιInvEquivOfIsUnit f M hiu S hiS) y with hz
  have hy : y = (cechι f M (Finset.erase_subset i S)) z :=
    (cechι_cechιInvEquivOfIsUnit_apply f M hiu S hiS y).symm
  have e1 : (cechι f M (Finset.subset_insert k S)) y
      = (cechι f M ((Finset.erase_subset i S).trans (Finset.subset_insert k S))) z := by
    rw [hy, ← cechι_comp f M (Finset.erase_subset i S) (Finset.subset_insert k S)]; rfl
  rw [e1]
  have hmid : (Finset.erase_subset i S).trans (Finset.subset_insert k S)
      = hsub.trans (Finset.erase_subset i (insert k S)) := rfl
  rw [hmid, ← cechι_comp f M hsub (Finset.erase_subset i (insert k S))]
  rw [LinearMap.comp_apply]
  rw [cechιInvEquivOfIsUnit_cechι_apply f M hiu (insert k S) hiIns]

/-- `cechιInvEquivOfIsUnit_naturality_insert` transported along `(insert k S).erase i = U`: the
value is the localization of `cechιInvEquivOfIsUnit … y` along `S.erase i ⊆ U`. -/
theorem cechιInvEquivOfIsUnit_naturality_insert_eqRec
    (q : ℕ) {i : Fin r} (hiu : IsUnit (f i)) (S : {s : Finset (Fin r) // s.card = q+1})
    (hiS : i ∈ S.1) (k : Fin r) (hkS : k ∉ S.1) (y : cechMod f M S.1)
    (hiIns : i ∈ insert k S.1) (U : {s : Finset (Fin r) // s.card = q+1})
    (hU : (⟨(insert k S.1).erase i, by
        rw [Finset.card_erase_of_mem hiIns, Finset.card_insert_of_notMem hkS, S.2]; omega⟩ :
        {s : Finset (Fin r) // s.card = q+1}) = U)
    (hsubU : S.1.erase i ⊆ U.1) :
    (hU ▸ (cechιInvEquivOfIsUnit f M hiu (insert k S.1) hiIns)
        ((cechι f M (Finset.subset_insert k S.1)) y))
      = (cechι f M hsubU) ((cechιInvEquivOfIsUnit f M hiu S.1 hiS) y) := by
  have hsub : S.1.erase i ⊆ (insert k S.1).erase i := by
    have hh : (insert k S.1).erase i = U.1 := congrArg Subtype.val hU
    rw [hh]; exact hsubU
  rw [cechιInvEquivOfIsUnit_naturality_insert f M hiu S.1 hiS k y hiIns hsub]
  apply cechMod_eqRec_eq_of_heq f M _ _ _ hU
  have heqset : (insert k S.1).erase i = U.1 := congrArg Subtype.val hU
  exact cechι_heq_of_target_eq f M hsub hsubU heqset _

/-- Combined sign identity for the `i ∈ S` regime: the coefficient sums of the two homotopy
terms add up to the diagonal indicator `[S = U]`. -/
theorem cechSign_sum_insert_add_sum_erase_eq_ite (i : Fin r) (S U : Finset (Fin r)) (hiS : i ∈ S) :
    (∑ k ∈ Sᶜ, (if insert k (S.erase i) = U then
        cechSign (insert k S) k * cechSign (insert k S) i else 0))
    + cechSign S i * (∑ m ∈ (S.erase i)ᶜ, (if insert m (S.erase i) = U then
        cechSign (insert m (S.erase i)) m else 0))
    = (if S = U then 1 else 0) := by
  classical
  have hcompl : (S.erase i)ᶜ = insert i Sᶜ := by
    ext x
    simp only [Finset.mem_compl, Finset.mem_erase, Finset.mem_insert, not_and]
    by_cases hx : x = i
    · subst hx
      simp [hiS]
    · simp [hx]
  rw [Finset.mul_sum, hcompl]
  have hiSc : i ∉ Sᶜ := by simp [hiS]
  rw [Finset.sum_insert hiSc]
  have hSe : insert i (S.erase i) = S := Finset.insert_erase hiS
  rw [hSe]
  have hiterm : cechSign S i * (if S = U then cechSign S i else 0)
      = (if S = U then (1:ℤ) else 0) := by
    by_cases h : S = U
    · rw [ite_eq_left h, ite_eq_left h, cechSign_mul_self]
    · rw [ite_eq_right h, ite_eq_right h, mul_zero]
  rw [show ∀ (a b c : ℤ), a + (b + c) = (a + c) + b from fun a b c => by ring]
  rw [hiterm]
  have hcancel : (∑ k ∈ Sᶜ, (if insert k (S.erase i) = U then
        cechSign (insert k S) k * cechSign (insert k S) i else 0))
      + (∑ k ∈ Sᶜ, cechSign S i * (if insert k (S.erase i) = U then
        cechSign (insert k (S.erase i)) k else 0)) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro k hk
    have hkS : k ∉ S := Finset.mem_compl.mp hk
    by_cases hU : insert k (S.erase i) = U
    · rw [ite_eq_left hU, ite_eq_left hU]
      have hmi : k ≠ i := fun e => hkS (e ▸ hiS)
      have hmE : k ∉ S.erase i := fun h => hkS (Finset.mem_of_mem_erase h)
      have hiE : i ∉ S.erase i := by simp
      have hc := cechSign_insert_mul_insert_eq_neg_swap k i hmi (S.erase i) hmE hiE
      rw [Finset.insert_erase hiS] at hc
      have h1 : insert i (insert k (S.erase i)) = insert k S := by
        rw [Finset.insert_comm, Finset.insert_erase hiS]
      rw [h1] at hc
      have hBB := cechSign_mul_self i (insert k S)
      have hCC := cechSign_mul_self i S
      have hD : cechSign (insert k (S.erase i)) k
          = -(cechSign S i * cechSign (insert k S) k) * cechSign (insert k S) i := by
        have := congrArg (· * cechSign (insert k S) i) hc
        rw [mul_assoc, hBB, mul_one] at this
        exact this
      rw [hD]
      linear_combination (-(cechSign (insert k S) k * cechSign (insert k S) i)) * hCC
    · rw [ite_eq_right hU, ite_eq_right hU, mul_zero, add_zero]
  rw [hcancel, zero_add]

/-- In the regime `i ∉ S`, the composite `h ∘ d` acts as the identity on a generator `lof S y`:
only the term inserting the unit index `i` survives, and it deletes `i` again. -/
theorem cechHomotopyHom_cechD_lof_apply_of_notMem
    {i : Fin r} (hiu : IsUnit (f i)) (p : ℕ)
    (S U : {s : Finset (Fin r) // s.card = p}) (y : cechMod f M S.1) (hiSset : i ∉ S.1) :
    (DirectSum.lof R {s : Finset (Fin r) // s.card = p} (fun s => cechMod f M s.1) S y) U
      = ((cechHomotopyHom f M hiu (p+1) p) ((cechD f M p)
          (DirectSum.lof R {s : Finset (Fin r) // s.card = p}
            (fun s => cechMod f M s.1) S y))) U := by
  classical
  rw [cechHomotopyHom_cechD_lof_apply f M hiu p S y U, Finset.sum_eq_single i]
  · have hiSc : i ∈ S.1ᶜ := Finset.mem_compl.mpr hiSset
    rw [dite_eq_left hiSc]
    have hiIns : i ∈ (⟨insert i S.1, by rw [Finset.card_insert_of_notMem hiSset, S.2]⟩ :
        {s : Finset (Fin r) // s.card = p+1}).1 := Finset.mem_insert_self i S.1
    rw [cechHomotopyHom_lof_apply f M hiu (p+1) p rfl
        ⟨insert i S.1, by rw [Finset.card_insert_of_notMem hiSset, S.2]⟩
        (cechι f M (Finset.subset_insert i S.1) y) U, dite_eq_left hiIns]
    have heq : (insert i S.1).erase i = S.1 := Finset.erase_insert hiSset
    by_cases hSU : S = U
    · subst hSU
      have hU : (⟨(insert i S.1).erase i, by
            rw [Finset.card_erase_of_mem hiIns]; simp [Finset.card_insert_of_notMem hiSset, S.2]⟩ :
            {s : Finset (Fin r) // s.card = p}) = S := Subtype.ext heq
      rw [dite_eq_left hU]
      rw [lof_apply_eq_dite, dite_eq_left rfl]
      rw [smul_smul, cechSign_mul_self, one_smul]
      exact (cechMod_eqRec_eq_of_heq f M _ _ _ hU _ y
        (cechιInvEquivOfIsUnit_cechι_insert_heq f M hiu S.1 y hiSset hiIns)).symm
    · have hne : ¬ (⟨(insert i S.1).erase i, by
            rw [Finset.card_erase_of_mem hiIns]; simp [Finset.card_insert_of_notMem hiSset, S.2]⟩ :
            {s : Finset (Fin r) // s.card = p}) = U :=
          fun hc => hSU (Subtype.ext (heq ▸ congrArg Subtype.val hc))
      rw [dite_eq_right hne]
      rw [lof_apply_eq_dite, dite_eq_right hSU]
      exact (zsmul_zero _).symm
  · intro k hk hki
    rw [dite_eq_left hk, cechHomotopyHom_lof_apply f M hiu (p+1) p rfl
        ⟨insert k S.1, by rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp hk), S.2]⟩
        (cechι f M (Finset.subset_insert k S.1) y) U]
    have hnotin : i ∉ insert k S.1 := by
      simp only [Finset.mem_insert, not_or]; exact ⟨fun h => hki h.symm, hiSset⟩
    rw [dite_eq_right hnotin]; exact zsmul_zero _
  · intro h; exact absurd (Finset.mem_compl.mpr hiSset) h

/-- The homotopy identity in degree `0`: `id = h¹ ∘ d⁰`. -/
theorem cechHomotopyHom_comm_zero
    {i : Fin r} (hiu : IsUnit (f i)) :
    LinearMap.id
      = (cechHomotopyHom f M hiu (0+1) 0).comp (cechD f M 0) := by
  refine DirectSum.linearMap_ext _ fun S => LinearMap.ext fun y => DFinsupp.ext fun U => ?_
  have hiSset : i ∉ S.1 := by rw [Finset.card_eq_zero.mp S.2]; simp
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  exact cechHomotopyHom_cechD_lof_apply_of_notMem f M hiu 0 S U y hiSset

/-- In the regime `i ∈ S`, the two homotopy terms `h ∘ d` and `d ∘ h` add up to the identity on
a generator `lof S y`: the coefficients of the surviving summands are collected by
`cechSign_sum_insert_add_sum_erase_eq_ite`. -/
theorem cechHomotopyHom_cechD_add_cechD_cechHomotopyHom_lof_apply_of_mem
    {i : Fin r} (hiu : IsUnit (f i)) (q : ℕ)
    (S U : {s : Finset (Fin r) // s.card = q+1}) (y : cechMod f M S.1) (hiSset : i ∈ S.1) :
    (DirectSum.lof R {s : Finset (Fin r) // s.card = q+1} (fun s => cechMod f M s.1) S y) U
      = ((cechHomotopyHom f M hiu (q+1+1) (q+1)) ((cechD f M (q+1))
          (DirectSum.lof R {s : Finset (Fin r) // s.card = q+1}
            (fun s => cechMod f M s.1) S y))) U
        + ((cechD f M q) ((cechHomotopyHom f M hiu (q+1) q)
            (DirectSum.lof R {s : Finset (Fin r) // s.card = q+1}
              (fun s => cechMod f M s.1) S y))) U := by
  classical
  set z := (cechιInvEquivOfIsUnit f M hiu S.1 hiSset) y with hz
  set Se : {s : Finset (Fin r) // s.card = q} :=
    ⟨S.1.erase i, by rw [Finset.card_erase_of_mem hiSset, S.2]; omega⟩
  have hT2 : ((cechD f M q) ((cechHomotopyHom f M hiu (q + 1) q)
        (DirectSum.lof R { s : Finset (Fin r) // s.card = q + 1 }
          (fun s => cechMod f M s.1) S y))) U
      = cechSign S.1 i • ((cechD f M q (DirectSum.lof R {s : Finset (Fin r) // s.card = q}
          (fun s => cechMod f M s.1) Se z)) U) := by
    rw [cechHomotopyHom_lof f M hiu (q+1) q rfl S y, dite_eq_left hiSset, map_zsmul]
    rfl
  rw [cechHomotopyHom_cechD_lof_apply f M hiu (q+1) S y U, hT2, cechD_lof_apply f M q Se z U]
  rw [lof_apply_eq_dite]
  set w : cechMod f M U.1 := if h : S.1.erase i ⊆ U.1 then cechι f M h z else 0 with hw
  have hsub : ∀ {k : Fin r}, insert k (S.1.erase i) = U.1 → S.1.erase i ⊆ U.1 :=
    fun h => h ▸ Finset.subset_insert _ _
  have hT1red : (∑ k ∈ S.1ᶜ, if hk : k ∈ S.1ᶜ then
        cechSign (insert k S.1) k • ((cechHomotopyHom f M hiu (q+1+1) (q+1)
          (DirectSum.lof R {s : Finset (Fin r) // s.card = q+1+1}
            (fun s => cechMod f M s.1)
            ⟨insert k S.1, by rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp hk), S.2]⟩
            (cechι f M (Finset.subset_insert k S.1) y))) U)
        else 0)
      = (∑ k ∈ S.1ᶜ, (if insert k (S.1.erase i) = U.1 then
          cechSign (insert k S.1) k * cechSign (insert k S.1) i else 0)) • w := by
    rw [Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro k hk
    have hkS : k ∉ S.1 := Finset.mem_compl.mp hk
    have hiIns : i ∈ insert k S.1 := Finset.mem_insert_of_mem hiSset
    have hki : k ≠ i := by rintro rfl; exact hkS hiSset
    have heqset : (insert k S.1).erase i = insert k (S.1.erase i) :=
      Finset.erase_insert_of_ne hki
    rw [dite_eq_left hk]
    rw [cechHomotopyHom_lof_apply f M hiu (q+1+1) (q+1) rfl
        ⟨insert k S.1, by rw [Finset.card_insert_of_notMem hkS, S.2]⟩
        (cechι f M (Finset.subset_insert k S.1) y) U, dite_eq_left hiIns]
    by_cases hU : (⟨(insert k S.1).erase i, by
          rw [Finset.card_erase_of_mem hiIns, Finset.card_insert_of_notMem hkS, S.2]; omega⟩ :
          {s : Finset (Fin r) // s.card = q+1}) = U
    · rw [dite_eq_left hU]
      have hind : insert k (S.1.erase i) = U.1 := by
        rw [← heqset]; exact congrArg Subtype.val hU
      rw [ite_eq_left hind, smul_smul]
      congr 1
      rw [hw, dite_eq_left (hsub hind)]
      exact cechιInvEquivOfIsUnit_naturality_insert_eqRec f M q hiu S hiSset k hkS y hiIns
        U hU (hsub hind)
    · rw [dite_eq_right hU]
      have hind : ¬ insert k (S.1.erase i) = U.1 := by
        intro hc; exact hU (Subtype.ext (heqset.trans hc))
      rw [ite_eq_right hind, zero_smul]
      exact zsmul_zero _
  have hT2red : (∑ m ∈ Se.1ᶜ, if h : m ∈ Se.1ᶜ then
        (if hU : (⟨insert m Se.1, by
              rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp h), Se.2]⟩ :
              {s : Finset (Fin r) // s.card = q+1}) = U then
          (cechSign (insert m Se.1) m) • (hU ▸ cechι f M (Finset.subset_insert m Se.1) z)
        else 0) else 0)
      = (∑ m ∈ (S.1.erase i)ᶜ, (if insert m (S.1.erase i) = U.1 then
          cechSign (insert m (S.1.erase i)) m else 0)) • w := by
    rw [Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro m hm
    rw [dite_eq_left hm]
    by_cases hU : (⟨insert m Se.1, by
          rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp hm), Se.2]⟩ :
          {s : Finset (Fin r) // s.card = q+1}) = U
    · rw [dite_eq_left hU]
      have hind : insert m (S.1.erase i) = U.1 := congrArg Subtype.val hU
      rw [ite_eq_left hind]
      congr 1
      rw [hw, dite_eq_left (hsub hind)]
      apply cechMod_eqRec_eq_of_heq f M _ _ _ hU
      exact cechι_heq_of_target_eq f M (Finset.subset_insert m Se.1) (hsub hind) hind z
    · rw [dite_eq_right hU]
      have hind : ¬ insert m (S.1.erase i) = U.1 := fun hc => hU (Subtype.ext hc)
      rw [ite_eq_right hind, zero_smul]
  rw [hT1red, hT2red, smul_smul, ← add_smul]
  rw [cechSign_sum_insert_add_sum_erase_eq_ite i S.1 U.1 hiSset]
  by_cases hSU : S = U
  · subst hSU
    rw [ite_eq_left (rfl : S.1 = S.1), one_smul, dite_eq_left rfl, hw,
      dite_eq_left (Finset.erase_subset i S.1)]
    exact (cechι_cechιInvEquivOfIsUnit_apply f M hiu S.1 hiSset y).symm
  · rw [dite_eq_right hSU, ite_eq_right fun hc => hSU (Subtype.ext hc), zero_smul]

/-- The homotopy identity in degree `q + 1`: `id = h^{q+2} ∘ d^{q+1} + d^q ∘ h^{q+1}`. -/
theorem cechHomotopyHom_comm_succ
    {i : Fin r} (hiu : IsUnit (f i)) (q : ℕ) :
    LinearMap.id
      = (cechHomotopyHom f M hiu (q+1+1) (q+1)).comp (cechD f M (q+1))
        + (cechD f M q).comp (cechHomotopyHom f M hiu (q+1) q) := by
  refine DirectSum.linearMap_ext _ fun S => LinearMap.ext fun y => DFinsupp.ext fun U => ?_
  simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.add_apply]
  rw [DFinsupp.add_apply]
  by_cases hiSset : i ∈ S.1
  · exact cechHomotopyHom_cechD_add_cechD_cechHomotopyHom_lof_apply_of_mem f M hiu q S U y hiSset
  · -- i ∉ S regime: the second term vanishes and the first reduces to the identity.
    have hT2 : ((cechD f M q) ((cechHomotopyHom f M hiu (q + 1) q)
          (DirectSum.lof R { s : Finset (Fin r) // s.card = q + 1 }
            (fun s => cechMod f M s.1) S y))) U = 0 := by
      rw [cechHomotopyHom_lof f M hiu (q+1) q rfl S y, dite_eq_right hiSset, map_zero]; rfl
    rw [hT2, add_zero]
    exact cechHomotopyHom_cechD_lof_apply_of_notMem f M hiu (q+1) S U y hiSset


/-- The homotopy identity `dh + hd = 𝟙` for the contracting homotopy `cechHomotopyHom` of
`Cech.cechComplex f M`, in the `dNext`/`prevD` form of `Homotopy`, in each degree `p`. -/
theorem cechHomotopyHom_comm
    {i : Fin r} (hiu : IsUnit (f i)) (p : ℕ) :
    HomologicalComplex.Hom.f (𝟙 (cechComplex f M)) p
      = (dNext p (fun a b => ModuleCat.ofHom (cechHomotopyHom f M hiu a b)))
        + (prevD p (fun a b => ModuleCat.ofHom (cechHomotopyHom f M hiu a b)))
        + HomologicalComplex.Hom.f (0 : cechComplex f M ⟶ cechComplex f M) p := by
  classical
  have hd : ∀ n, (cechComplex f M).d n (n+1) = ModuleCat.ofHom (cechD f M n) := fun n => by
    simp only [cechComplex, CochainComplex.of_d]
  rw [HomologicalComplex.zero_f, add_zero]
  rw [dNext_eq _ (show (ComplexShape.up ℕ).Rel p (p+1) from rfl), hd]
  cases p with
  | zero =>
    rw [prevD_eq_zero _ 0 (by intro h; exact Nat.succ_ne_zero _ h), add_zero,
      HomologicalComplex.id_f]
    apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_id]
    exact cechHomotopyHom_comm_zero f M hiu
  | succ q =>
    rw [prevD_eq _ (show (ComplexShape.up ℕ).Rel q (q+1) from rfl)]
    rw [hd, HomologicalComplex.id_f]
    apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_add, ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_id]
    exact cechHomotopyHom_comm_succ f M hiu q

/-- The contracting homotopy of `Cech.cechComplex f M` attached to a unit `f i`: it deletes the
index `i` from a summand indexed by a set containing `i`, with the Čech sign. -/
def contractingHomotopy {i : Fin r} (hiu : IsUnit (f i)) :
    Homotopy (𝟙 (cechComplex f M)) 0 where
  hom a b := ModuleCat.ofHom (cechHomotopyHom f M hiu a b)
  zero a b hab := by
    apply ModuleCat.hom_ext
    rw [ModuleCat.hom_ofHom, ModuleCat.hom_zero]
    refine DirectSum.linearMap_ext _ fun S => LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, cechHomotopyHom, DirectSum.toModule_lof,
      dite_eq_right (show ¬(b + 1 = a) from hab)]
    rfl
  comm := cechHomotopyHom_comm f M hiu

/-- **Stacks 0G6J**.
If some `f i` is a unit in `R`, then the extended alternating Čech complex of `M` is homotopy
equivalent to `0`: the identity chain map is chain homotopic to the zero chain map. -/
@[stacks 0G6J]
theorem cechComplex_nullHomotopic
    (hunit : ∃ i : Fin r, IsUnit (f i)) :
    Nonempty (Homotopy (𝟙 (cechComplex f M)) 0) :=
  hunit.elim fun _ hiu => ⟨contractingHomotopy f M hiu⟩

end

end Stacks.CechContractible
