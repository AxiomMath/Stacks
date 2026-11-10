module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import Mathlib.Order.SuccPred.Int
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksFrontier.RingTheory.Cech.Substrate
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The extended alternating Čech complex

Let `R` be a commutative ring, `M` an `R`-module and `f_1, …, f_r ∈ R`. For a finite subset
`S ⊆ {1, …, r}` write `f_S = ∏_{i ∈ S} f_i` and `M_{f_S}` for the localization of `M` at the
powers of `f_S`. The extended alternating Čech complex of `M` has `p`-th term
`C^p(M) = ⨁_{i_0 < ⋯ < i_{p-1}} M_{f_{i_0} ⋯ f_{i_{p-1}}}` for `0 ≤ p ≤ r` and `0` otherwise, and
differential `d^p : C^p(M) → C^{p+1}(M)` whose component at `T = {k_0 < ⋯ < k_p}` is
`∑_j (-1)^j ι(x_{T ∖ k_j})`, where `ι` denotes the localization maps `M_{f_S} → M_{f_T}` for
`S ⊆ T`. Each `d^p` is `R`-linear and `d^{p+1} ∘ d^p = 0`, so this is a complex of `R`-modules.

## Main definitions

* `ExtendedAlternatingCech.Idx`: the index type of `C^p(M)`, the `p`-element subsets of `Fin r`.
* `ExtendedAlternatingCech.cechTermPi`: the term `C^p(M)` for `0 ≤ p ≤ r`, as a product over the
  `p`-element subsets of `Fin r`.
* `ExtendedAlternatingCech.cechD`: the differential `d^p : C^p(M) →ₗ[R] C^{p+1}(M)`.
* `ExtendedAlternatingCech.cechZeroEquiv`: the identification `C^0(M) ≃ₗ[R] M`.
* `ExtendedAlternatingCech.cechX`: the integer-indexed term `C^p(M)` in `ModuleCat R`, which is
  zero outside `0 ≤ p ≤ r`.
* `ExtendedAlternatingCech.cechdSucc`: the integer-indexed differential `C^p(M) ⟶ C^{p+1}(M)`.
* `ExtendedAlternatingCech.cechd`: the integer-indexed differential `C^i(M) ⟶ C^j(M)`.
* `ExtendedAlternatingCech.cechXZeroIso`: the identification `cechX f M 0 ≅ ModuleCat.of R M`.
* `ExtendedAlternatingCech.cechRing`: the ring localization `R_{f_S}`.
* `ExtendedAlternatingCech.ιRing`: the ring localization map `R_{f_S} →ₐ[R] R_{f_T}` for `S ⊆ T`.
* `ExtendedAlternatingCech.mlocREquiv`: the identification of the module localization of `R`
  at `f_S` with `R_{f_S}`.
* `ExtendedAlternatingCech.locUnitEquiv`: localizing a module at a submonoid of units changes
  nothing.

## Main results

* `ExtendedAlternatingCech.cechD_apply`: the componentwise alternating-sum formula for `d^p`.
* `ExtendedAlternatingCech.cechD_comp_cechD`: `d^{p+1} ∘ d^p = 0`.
* `ExtendedAlternatingCech.cechd_succ`, `ExtendedAlternatingCech.cechd_eq_zero_of_ne`: the
  integer-indexed differential is `cechdSucc` in consecutive degrees and zero elsewhere.
* `ExtendedAlternatingCech.cechd_comp_cechd`: `d ∘ d = 0` in the integer grading.
* `ExtendedAlternatingCech.mlocREquiv_cechι`: the module localization maps for `M = R`
  agree with the ring localization maps.

## Implementation notes

The `p`-element subsets of `{1, …, r}` are indexed by the subtype
`Idx r p = {S : Finset (Fin r) // S.card = p}`.
Since this index is finite, `C^p(M)` is modelled as a product rather than a direct sum.

## References

* [Stacks Project, Section 15.30, Tag 0G6F](https://stacks.math.columbia.edu/tag/0G6F)
-/

@[expose] public section

-- Required: the `Idx`/`cechTermPi` `abbrev`s must unfold during unification, both for the
-- `Subsingleton (cechX f M p)` instances and for the index rewrites in the double-sum vanishing
-- lemma below.
set_option backward.isDefEq.respectTransparency false
open CategoryTheory

namespace ExtendedAlternatingCech

universe u
variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)

variable (M : Type u) [AddCommGroup M] [Module R M]

/-- The index type of the term `C^p(M)`: the `p`-element subsets of `{1,...,r}`. -/
abbrev Idx (r p : ℕ) := { S : Finset (Fin r) // S.card = p }

/-- The term `C^p(M)` of the complex: the product over `p`-element subsets `S ⊆ {1,...,r}` of
the localizations `M_{f_S}`. -/
abbrev cechTermPi (p : ℕ) :=
  (S : Idx r p) → Cech.cechMod f M S.1

/-- `T.erase k` viewed as an index of `cechTermPi p` (it has cardinality `p` when
`T.card = p + 1` and `k ∈ T`). -/
def Idx.erase {p : ℕ} (T : Idx r (p + 1)) (k : T.1) : Idx r p :=
  ⟨T.1.erase k, by
    have := T.2; rw [Finset.card_erase_of_mem k.2]; omega⟩

/-- The underlying finset of `T.erase k` is `T.1.erase k`. -/
@[simp]
theorem Idx.val_erase {p : ℕ} (T : Idx r (p + 1)) (k : T.1) : (T.erase k).1 = T.1.erase k :=
  rfl

/-- The differential `d^p : C^p(M) → C^{p+1}(M)`, whose component at a tuple
`T = {k_0 < ... < k_p}` is `∑_j (-1)^j ι(x_{T \ k_j})`. -/
noncomputable def cechD (p : ℕ) : cechTermPi f M p →ₗ[R] cechTermPi f M (p + 1) :=
  LinearMap.pi
    (fun T =>
      ∑ k ∈ T.1.attach,
        Cech.cechSign T.1 k •
          (Cech.cechι f M (Finset.erase_subset _ _)).comp
            (LinearMap.proj (T.erase k)))

/-- The component of `d^p x` at `T` is the alternating sum over `k ∈ T` of the images of the
components `x_{T \ k}` under the localization maps. -/
theorem cechD_apply {p : ℕ} (x : cechTermPi f M p) (T : Idx r (p + 1)) :
    cechD f M p x T =
      ∑ k ∈ T.1.attach,
        Cech.cechSign T.1 k •
          Cech.cechι f M (Finset.erase_subset _ _) (x (T.erase k)) := by
  rw [cechD, LinearMap.pi_apply, LinearMap.coe_sum, Finset.sum_apply]
  rfl

/-- The unique `0`-element subset of `{1,...,r}` is the empty set. -/
instance instUniqueIdxZero : Unique (Idx r 0) where
  default := ⟨∅, Finset.card_empty⟩
  uniq := fun ⟨_, hS⟩ => Subtype.ext (Finset.card_eq_zero.mp hS)

/-- Localizing a module `M` at a submonoid consisting of units gives back `M`. -/
noncomputable def locUnitEquiv {S : Submonoid R} (hS : S ≤ IsUnit.submonoid R) :
    LocalizedModule S M ≃ₗ[R] M :=
  haveI := IsLocalization.of_le_isUnit hS
  haveI := isLocalizedModule_id S M R
  IsLocalizedModule.linearEquiv S (LocalizedModule.mkLinearMap S M) (LinearMap.id : M →ₗ[R] M)

/-- `locUnitEquiv` sends `m / 1` to `m`. -/
@[simp]
theorem locUnitEquiv_mk_one {S : Submonoid R} (hS : S ≤ IsUnit.submonoid R) (m : M) :
    locUnitEquiv M hS (LocalizedModule.mk m 1) = m :=
  have := IsLocalization.of_le_isUnit hS
  have := isLocalizedModule_id S M R
  IsLocalizedModule.linearEquiv_apply S (LocalizedModule.mkLinearMap S M) LinearMap.id m

/-- The inverse of `locUnitEquiv` sends `m` to `m / 1`. -/
@[simp]
theorem locUnitEquiv_symm_apply {S : Submonoid R} (hS : S ≤ IsUnit.submonoid R) (m : M) :
    (locUnitEquiv M hS).symm m = LocalizedModule.mk m 1 :=
  ((locUnitEquiv M hS).symm_apply_eq).mpr (locUnitEquiv_mk_one M hS m).symm

/-- The canonical `R`-linear identification `C^0(M) ≃ M`, coming from `M_{f_∅} = M_1 = M`. -/
noncomputable def cechZeroEquiv : cechTermPi f M 0 ≃ₗ[R] M :=
  (LinearEquiv.piUnique (R := R) (fun (S : Idx r 0) => Cech.cechMod f M S.1)).trans
    (locUnitEquiv M (hS := by
      rw [show ((default : Idx r 0) : Finset (Fin r)) = ∅ from rfl]
      exact Submonoid.powers_le.mpr
        ((IsUnit.mem_submonoid_iff _).mpr (by rw [Finset.prod_empty]; exact isUnit_one))))

/-- `cechZeroEquiv` sends the constant tuple `m / 1` to `m`. -/
@[simp]
theorem cechZeroEquiv_mk_one (m : M) :
    cechZeroEquiv f M (fun _ => LocalizedModule.mk m 1) = m := by
  simp [cechZeroEquiv]

/-- The inverse of `cechZeroEquiv` sends `m` to the constant tuple `m / 1`. -/
@[simp]
theorem cechZeroEquiv_symm_apply (m : M) :
    (cechZeroEquiv f M).symm m = fun _ => LocalizedModule.mk m 1 :=
  (cechZeroEquiv f M).symm_apply_eq.mpr (cechZeroEquiv_mk_one f M m).symm

/-- The integer-indexed term `C^p(M)` as an object of `ModuleCat R`: it is `cechTermPi f M p` for
`0 ≤ p ≤ r`, and the zero module otherwise. -/
noncomputable def cechX (p : ℤ) : ModuleCat.{u} R :=
  if p ∈ Set.Icc (0 : ℤ) (r : ℤ) then ModuleCat.of R (cechTermPi f M p.toNat)
  else ModuleCat.of R PUnit

/-- In the range `0 ≤ p ≤ r`, the integer-indexed term is the product term `cechTermPi f M p`. -/
theorem cechX_eq_of_mem_Icc {p : ℤ} (hp : p ∈ Set.Icc (0 : ℤ) (r : ℤ)) :
    cechX f M p = ModuleCat.of R (cechTermPi f M p.toNat) := by
  rw [cechX, ite_eq_left hp]

/-- Outside the range `0 ≤ p ≤ r`, the integer-indexed term is the trivial module. -/
theorem cechX_eq_punit_of_notMem_Icc {p : ℤ} (hp : p ∉ Set.Icc (0 : ℤ) (r : ℤ)) :
    cechX f M p = ModuleCat.of R PUnit := by
  rw [cechX, ite_eq_right hp]

/-- Outside the range `0 ≤ p ≤ r`, the integer-indexed term is a subsingleton. -/
theorem subsingleton_cechX_of_notMem_Icc {p : ℤ} (hp : p ∉ Set.Icc (0 : ℤ) (r : ℤ)) :
    Subsingleton (cechX f M p) := by
  rw [cechX_eq_punit_of_notMem_Icc f M hp]
  infer_instance

/-- The integer-indexed term in degree `0` is the product term `cechTermPi f M 0`. -/
theorem cechX_zero_eq : cechX f M 0 = ModuleCat.of R (cechTermPi f M 0) := by
  rw [cechX_eq_of_mem_Icc f M (Set.mem_Icc.mpr ⟨le_refl 0, Int.natCast_nonneg r⟩)]
  rfl

/-- The differential `cechX p ⟶ cechX (p+1)`: it is `cechD` when both `p` and `p+1` lie in
`[0, r]`, and `0` otherwise. -/
noncomputable def cechdSucc (p : ℤ) : cechX f M p ⟶ cechX f M (p + 1) := by
  unfold cechX
  by_cases hp : p ∈ Set.Icc (0 : ℤ) (r : ℤ)
  · by_cases hp1 : p + 1 ∈ Set.Icc (0 : ℤ) (r : ℤ)
    · rw [ite_eq_left hp, ite_eq_left hp1]
      have hp' := Set.mem_Icc.mp hp
      have hcast : (p + 1).toNat = p.toNat + 1 := by omega
      refine ModuleCat.ofHom (?_ : cechTermPi f M p.toNat →ₗ[R] cechTermPi f M (p + 1).toNat)
      rw [hcast]; exact cechD f M p.toNat
    · rw [ite_eq_left hp, ite_eq_right hp1]; exact ModuleCat.ofHom 0
  · rw [ite_eq_right hp]; exact 0

/-- The full integer-indexed differential `d_{i,j} : C^i(M) ⟶ C^j(M)`, nonzero
only when `j = i + 1`. -/
noncomputable def cechd (i j : ℤ) : cechX f M i ⟶ cechX f M j :=
  if h : i + 1 = j then cechdSucc f M i ≫ eqToHom (by rw [h]) else 0

/-- Outside consecutive degrees the integer-indexed differential vanishes. -/
@[simp]
theorem cechd_eq_zero_of_ne {i j : ℤ} (h : i + 1 ≠ j) : cechd f M i j = 0 := by
  rw [cechd, dite_eq_right h]

/-- In consecutive degrees the integer-indexed differential is `cechdSucc`. -/
theorem cechd_succ (i : ℤ) : cechd f M i (i + 1) = cechdSucc f M i := by
  rw [cechd, dite_eq_left rfl]
  simp

/-- For distinct `l, k ∈ U`, removing `l` and then `k` gives the opposite sign to removing `k`
and then `l`: `cechSign U l * cechSign (U.erase l) k = -(cechSign U k * cechSign (U.erase k) l)`.
-/
theorem cechSign_mul_swap (U : Finset (Fin r)) (l k : Fin r) (hl : l ∈ U) (hk : k ∈ U)
    (hlk : l ≠ k) :
    Cech.cechSign U l * Cech.cechSign (U.erase l) k
      = -(Cech.cechSign U k * Cech.cechSign (U.erase k) l) := by
  have hkT : k ∉ (U.erase l).erase k := Finset.notMem_erase k _
  have hlT : l ∉ (U.erase l).erase k := fun h =>
    Finset.notMem_erase l U (Finset.mem_of_mem_erase h)
  have hUl : U.erase l = insert k ((U.erase l).erase k) :=
    (Finset.insert_erase (Finset.mem_erase.mpr ⟨Ne.symm hlk, hk⟩)).symm
  have hUk : U.erase k = insert l ((U.erase l).erase k) := by
    rw [Finset.erase_right_comm]
    exact (Finset.insert_erase (Finset.mem_erase.mpr ⟨hlk, hl⟩)).symm
  have e1 : Cech.cechSign U l = Cech.cechSign (insert k ((U.erase l).erase k)) l := by
    rw [← hUl]; exact (Cech.cechSign_erase U l).symm
  have e2 : Cech.cechSign (U.erase l) k = Cech.cechSign ((U.erase l).erase k) k :=
    (Cech.cechSign_erase (U.erase l) k).symm
  have e3 : Cech.cechSign U k = Cech.cechSign (insert l ((U.erase l).erase k)) k := by
    rw [← hUk]; exact (Cech.cechSign_erase U k).symm
  have e4 : Cech.cechSign (U.erase k) l = Cech.cechSign ((U.erase l).erase k) l := by
    rw [hUk, Cech.cechSign_insert]
  rw [e1, e2, e3, e4, mul_comm (Cech.cechSign (insert k ((U.erase l).erase k)) l),
    mul_comm (Cech.cechSign (insert l ((U.erase l).erase k)) k)]
  exact Cech.cechSign_swap ((U.erase l).erase k) (Ne.symm hlk) hkT hlT

/-- The element `Cech.cechι f M hsub (x V)` depends only on `V`: if `V = V'` then
`Cech.cechι f M hsub (x V) = Cech.cechι f M hsub' (x V')`. -/
theorem cechι_apply_congr {p : ℕ} {W : Finset (Fin r)} (x : cechTermPi f M p)
    {V V' : Idx r p} (hVV' : V = V') {hsub : V.1 ⊆ W} {hsub' : V'.1 ⊆ W} :
    Cech.cechι f M hsub (x V) = Cech.cechι f M hsub' (x V') := by
  subst hVV'; rfl

/-- The double alternating sum
`∑_{l ∈ U} ∑_{k ∈ U \ l} cechSign U l • cechSign (U \ l) k • ι(x_{(U \ l) \ k})` vanishes. -/
theorem sum_sum_cechSign_smul_cechι_eq_zero {p : ℕ} (U : Idx r (p + 1 + 1)) (x : cechTermPi f M p) :
    ∑ l ∈ U.1.attach,
        Cech.cechSign U.1 l.1 •
          ∑ k ∈ (U.1.erase l).attach,
            Cech.cechSign (U.1.erase l) k.1 •
              Cech.cechι f M ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))
                (x ((U.erase l).erase k)) =
      0 := by
  have hcomb :
    ∀ l ∈ U.1.attach,
      Cech.cechSign U.1 l.1 •
          ∑ k ∈ (U.1.erase l).attach,
            Cech.cechSign (U.1.erase l) k.1 •
              Cech.cechι f M ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))
                (x ((U.erase l).erase k)) =
        ∑ k ∈ (U.1.erase l).attach,
          (Cech.cechSign U.1 l.1 * Cech.cechSign (U.1.erase l) k.1) •
            Cech.cechι f M ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))
              (x ((U.erase l).erase k)) :=
    fun l _ =>
    (map_sum (zsmulAddGroupHom (Cech.cechSign U.1 l.1) :
          Cech.cechMod f M U.1 →+ Cech.cechMod f M U.1) _ _).trans
      (Finset.sum_congr rfl (fun k _ => (mul_smul _ _ _).symm))
  rw [Finset.sum_congr rfl hcomb]
  rw [Finset.sum_sigma' U.1.attach fun l => (U.1.erase l.1).attach]
  refine
    Finset.sum_involution (g := fun a _ =>
      (⟨⟨a.2.1, Finset.mem_of_mem_erase a.2.2⟩,
          ⟨a.1.1,
            Finset.mem_erase.mpr
              ⟨fun h => (Finset.ne_of_mem_erase a.2.2) (by simpa using h.symm), a.1.2⟩⟩⟩ :
        (l : U.1) × (U.1.erase l.1)))
      ?_ ?_ ?_ ?_
  · rintro ⟨l, k⟩ -
    have hkl : k.1 ≠ l.1 := Finset.ne_of_mem_erase k.2
    have hkU : k.1 ∈ U.1 := Finset.mem_of_mem_erase k.2
    have hlk : l.1 ∈ U.1.erase k.1 := Finset.mem_erase.mpr ⟨hkl.symm, l.2⟩
    have hidx :
      (U.erase l).erase k = (U.erase ⟨k.1, hkU⟩).erase ⟨l.1, hlk⟩ :=
      Subtype.ext Finset.erase_right_comm
    have hsign := cechSign_mul_swap U.1 l.1 k.1 l.2 hkU hkl.symm
    have hve :
      Cech.cechι f M ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))
          (x ((U.erase l).erase k)) =
        Cech.cechι f M ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))
          (x ((U.erase ⟨k.1, hkU⟩).erase ⟨l.1, hlk⟩)) :=
      cechι_apply_congr f M x hidx
    rw [hve, ← add_smul, hsign, neg_add_cancel, zero_smul]
  · rintro ⟨l, k⟩ - -
    intro hfix
    have hkl : k.1 ≠ l.1 := Finset.ne_of_mem_erase k.2
    simp only [Sigma.mk.injEq] at hfix
    exact hkl (by simpa using (Subtype.ext_iff.mp hfix.1))
  · rintro ⟨l, k⟩ -
    simp [Finset.mem_sigma]
  · rintro ⟨l, k⟩ -
    rfl

/-- The composition of two consecutive differentials `d^{p+1} ∘ d^p` of the extended alternating
Čech complex of `M` is zero. -/
theorem cechD_comp_cechD (p : ℕ) : (cechD f M (p + 1)).comp (cechD f M p) = 0 := by
  refine LinearMap.ext fun x => funext fun U => ?_
  rw [LinearMap.comp_apply, LinearMap.zero_apply, Pi.zero_apply, cechD_apply]
  have step1 :
    ∀ l ∈ U.1.attach,
      Cech.cechSign U.1 l.1 •
          (Cech.cechι f M (Finset.erase_subset _ _))
            ((cechD f M p) x (U.erase l)) =
        Cech.cechSign U.1 l.1 •
          ∑ k ∈ (U.1.erase l).attach,
            Cech.cechSign (U.1.erase l) k.1 •
              Cech.cechι f M ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))
                (x ((U.erase l).erase k)) := by
    intro l _
    rw [cechD_apply, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul]
    congr 1
    exact Cech.cechι_cechι f M _ _ _
  rw [Finset.sum_congr rfl step1]
  exact sum_sum_cechSign_smul_cechι_eq_zero f M U x

/-- When `p` and `p + 1` lie in `[0, r]`, the underlying linear map of `cechdSucc f M p` is
heterogeneously equal to `cechD f M p.toNat`. -/
theorem cechdSucc_hom_heq (p : ℤ) (hp : p ∈ Set.Icc (0 : ℤ) (r : ℤ))
    (hp1 : p + 1 ∈ Set.Icc (0 : ℤ) (r : ℤ)) :
    HEq (cechdSucc f M p).hom (cechD f M p.toNat) := by
  have hp' := Set.mem_Icc.mp hp
  have hcast : (p + 1).toNat = p.toNat + 1 := by omega
  unfold cechdSucc
  rw [dite_eq_left hp, dite_eq_left hp1]
  simp only [eq_mpr_eq_cast, id_eq, cast_cast]
  refine HEq.trans (b := ModuleCat.Hom.hom (ModuleCat.ofHom (cechD f M p.toNat))) ?_ ?_
  · congr 1
    · exact cechX_eq_of_mem_Icc f M hp
    · rw [cechX_eq_of_mem_Icc f M hp1, hcast]
    · refine (cast_heq _ _).trans ?_
      congr 1 <;>
        first
        | rw [hcast]
        | exact cast_heq _ _
  · rw [ModuleCat.hom_ofHom]

/-- If `p` does not lie in `[0, r]`, then `cechdSucc f M p = 0`. -/
theorem cechdSucc_eq_zero_of_notMem_Icc (p : ℤ) (hp : p ∉ Set.Icc (0 : ℤ) (r : ℤ)) :
    cechdSucc f M p = 0 := by
  unfold cechdSucc
  rw [dite_eq_right hp]
  simp only [eq_mpr_eq_cast, id_eq]
  apply eq_of_heq
  refine (cast_heq _ _).trans ?_
  rw [cechX_eq_punit_of_notMem_Icc f M hp]

/-- If `p + 1` does not lie in `[0, r]`, then `cechdSucc f M p = 0`. -/
theorem cechdSucc_eq_zero_of_succ_notMem_Icc (p : ℤ)
    (hp1 : p + 1 ∉ Set.Icc (0 : ℤ) (r : ℤ)) :
    cechdSucc f M p = 0 := by
  have : Subsingleton (cechX f M (p + 1)) := subsingleton_cechX_of_notMem_Icc f M hp1
  exact ModuleCat.hom_ext (LinearMap.ext fun _ => Subsingleton.elim _ _)

/-- Conjugating the underlying linear map of a morphism `g : A ⟶ B` by the
`eqToHom`s of object equalities `X = A`, `Y = B` does not change it (up to `HEq`). -/
theorem eqToHom_conj_hom_heq {X Y A B : ModuleCat.{u} R} (hX : X = A) (hY : Y = B) (g : A ⟶ B) :
    HEq (((eqToHom hY.symm).hom ∘ₗ g.hom) ∘ₗ (eqToHom hX).hom) g.hom := by
  subst hX; subst hY; simp

/-- When `p` and `p + 1` lie in `[0, r]` and `p.toNat = n`, `cechdSucc f M p` is `cechD f M n`
conjugated by `eqToHom`s. -/
private theorem cechdSucc_eq_eqToHom_comp (p : ℤ) (hp : p ∈ Set.Icc (0 : ℤ) (r : ℤ))
    (hp1 : p + 1 ∈ Set.Icc (0 : ℤ) (r : ℤ)) (n : ℕ) (hn : p.toNat = n)
    (hX0 : cechX f M p = ModuleCat.of R (cechTermPi f M n))
    (hX1 : cechX f M (p + 1) = ModuleCat.of R (cechTermPi f M (n + 1))) :
    cechdSucc f M p = eqToHom hX0 ≫ ModuleCat.ofHom (cechD f M n) ≫ eqToHom hX1.symm := by
  subst hn
  apply ModuleCat.hom_ext
  apply eq_of_heq
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom]
  exact (cechdSucc_hom_heq f M p hp hp1).trans
    (eqToHom_conj_hom_heq hX0 hX1 (ModuleCat.ofHom (cechD f M p.toNat))).symm

/-- **Stacks 0G6G**.
For consecutive integer degrees `i, j, k`, the composition `d_{j,k} ∘ d_{i,j}` of the
differentials of the extended alternating Čech complex vanishes. -/
@[stacks 0G6G]
theorem cechd_comp_cechd (i j k : ℤ) (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) :
    CategoryStruct.comp (cechd f M i j) (cechd f M j k) = 0 := by
  rw [ComplexShape.up_Rel] at hij hjk
  subst hij; subst hjk
  rw [cechd, dite_eq_left rfl, cechd, dite_eq_left rfl]
  by_cases hi : i ∈ Set.Icc (0 : ℤ) (r : ℤ)
  · by_cases hi1 : i + 1 ∈ Set.Icc (0 : ℤ) (r : ℤ)
    · by_cases hi2 : i + 1 + 1 ∈ Set.Icc (0 : ℤ) (r : ℤ)
      · have hi' := Set.mem_Icc.mp hi
        have hn1 : (i + 1).toNat = i.toNat + 1 := by omega
        have hcc := cechD_comp_cechD f M i.toNat
        have hX0 : cechX f M i = ModuleCat.of R (cechTermPi f M i.toNat) :=
          cechX_eq_of_mem_Icc f M hi
        have hX1 : cechX f M (i + 1) = ModuleCat.of R (cechTermPi f M (i.toNat + 1)) := by
          rw [cechX_eq_of_mem_Icc f M hi1, hn1]
        have hX2 : cechX f M (i + 1 + 1) = ModuleCat.of R (cechTermPi f M (i.toNat + 1 + 1)) := by
          rw [cechX_eq_of_mem_Icc f M hi2,
            show (i + 1 + 1).toNat = i.toNat + 1 + 1 from by omega]
        have c1 := cechdSucc_eq_eqToHom_comp f M i hi hi1 _ rfl hX0 hX1
        have c2 := cechdSucc_eq_eqToHom_comp f M (i + 1) hi1 hi2 _ hn1 hX1 hX2
        rw [c1, c2]
        simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
          Category.comp_id]
        rw [←
          Category.assoc (ModuleCat.ofHom (cechD f M i.toNat))
            (ModuleCat.ofHom (cechD f M (i.toNat + 1))),
          ← ModuleCat.ofHom_comp, hcc]
        apply ModuleCat.hom_ext
        simp
      · rw [cechdSucc_eq_zero_of_succ_notMem_Icc f M (i + 1) hi2]
        simp
    · rw [cechdSucc_eq_zero_of_succ_notMem_Icc f M i hi1]
      simp
  · rw [cechdSucc_eq_zero_of_notMem_Icc f M i hi]
    simp

/-- The identification of the integer-indexed term in degree `0` with `ModuleCat.of R M`. -/
noncomputable def cechXZeroIso : cechX f M 0 ≅ ModuleCat.of R M :=
  (eqToIso (cechX_zero_eq f M)).trans (LinearEquiv.toModuleIso (cechZeroEquiv f M))

/-- The ring localization `R_{f_S} = Localization.Away (f_S)`. -/
abbrev cechRing (S : Finset (Fin r)) :=
  Localization.Away (∏ i ∈ S, f i)

/-- For `S ⊆ T`, the element `f_S` is a unit in `R_{f_T}` (since `f_S | f_T`). -/
theorem isUnit_algebraMap_prod_of_subset (S T : Finset (Fin r)) (h : S ⊆ T) :
    IsUnit (algebraMap R (cechRing f T) (∏ i ∈ S, f i)) :=
  IsLocalization.Away.isUnit_of_dvd (∏ i ∈ T, f i) (Finset.prod_dvd_prod_of_subset _ _ _ h)

/-- The canonical ring-localization homomorphism `R_{f_S} → R_{f_T}` for `S ⊆ T`, as an
`R`-algebra homomorphism. -/
@[ega "0 1.4.1" "special case", ega "0 7.6.7" "ρ^{T, special case"]
noncomputable def ιRing (S T : Finset (Fin r)) (h : S ⊆ T) : cechRing f S →ₐ[R] cechRing f T :=
  { IsLocalization.Away.lift (S := cechRing f S) (∏ i ∈ S, f i)
      (g := algebraMap R (cechRing f T)) (isUnit_algebraMap_prod_of_subset f S T h) with
    commutes' := fun a => IsLocalization.lift_eq _ a }

/-- `ιRing` commutes with the structure maps from `R`. -/
@[simp]
theorem ιRing_algebraMap (S T : Finset (Fin r)) (h : S ⊆ T) (a : R) :
    ιRing f S T h (algebraMap R (cechRing f S) a) = algebraMap R (cechRing f T) a :=
  IsLocalization.lift_eq _ a

/-- The canonical `R`-linear identification of the localization of the `R`-module `R` at the
powers of `f_S` with the ring localization `R_{f_S}`. -/
noncomputable def mlocREquiv (S : Finset (Fin r)) : Cech.cechMod f R S ≃ₗ[R] cechRing f S :=
  IsLocalizedModule.linearEquiv (Submonoid.powers (∏ i ∈ S, f i))
    (LocalizedModule.mkLinearMap (Cech.cechSub f S) R)
    (Algebra.linearMap R (Localization.Away (∏ i ∈ S, f i)))

/-- `mlocREquiv` sends `a / 1` to the image of `a` under the structure map. -/
@[simp]
theorem mlocREquiv_mk_one (S : Finset (Fin r)) (a : R) :
    mlocREquiv f S (LocalizedModule.mk a 1) = algebraMap R (cechRing f S) a :=
  IsLocalizedModule.linearEquiv_apply (Submonoid.powers (∏ i ∈ S, f i))
    (LocalizedModule.mkLinearMap (Cech.cechSub f S) R)
    (Algebra.linearMap R (Localization.Away (∏ i ∈ S, f i))) a

/-- Under the identification `mlocREquiv`, the module-localization map `ι` for `M = R`
corresponds to the ring-localization homomorphism `ιRing`. -/
theorem mlocREquiv_cechι (S T : Finset (Fin r)) (h : S ⊆ T) (x : Cech.cechMod f R S) :
    mlocREquiv f T (Cech.cechι f R h x) = ιRing f S T h (mlocREquiv f S x) := by
  have hunits :
    ∀ y : Submonoid.powers (∏ i ∈ S, f i),
      IsUnit ((algebraMap R (Module.End R (cechRing f T))) (y : R)) := by
    intro y
    obtain ⟨n, hn⟩ := y.2
    obtain ⟨c, hc⟩ : (y : R) ∣ (∏ i ∈ T, f i) ^ n := by
      rw [← hn]
      exact pow_dvd_pow_of_dvd (Finset.prod_dvd_prod_of_subset _ _ _ h) n
    have hb : IsUnit (algebraMap R (Module.End R (cechRing f T)) ((∏ i ∈ T, f i) ^ n)) := by
      rw [map_pow]
      exact (IsLocalizedModule.map_units (Algebra.linearMap R (Localization.Away (∏ i ∈ T, f i)))
        ⟨∏ i ∈ T, f i, Submonoid.mem_powers _⟩).pow n
    rw [hc, map_mul] at hb
    exact (((Commute.all (y : R) c).map _).isUnit_mul_iff.mp hb).1
  have key :
    (mlocREquiv f T).toLinearMap.comp (Cech.cechι f R h)
      = (ιRing f S T h).toLinearMap.comp (mlocREquiv f S).toLinearMap := by
    refine
      IsLocalizedModule.ext (Submonoid.powers (∏ i ∈ S, f i))
        (LocalizedModule.mkLinearMap (Submonoid.powers (∏ i ∈ S, f i)) R) hunits ?_
    refine LinearMap.ext fun a => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LocalizedModule.mkLinearMap_apply]
    rw [show Cech.cechι f R h (LocalizedModule.mk a 1) = LocalizedModule.mk a 1 from
      Cech.cechι_mk f R h a]
    change mlocREquiv f T (LocalizedModule.mk a 1)
      = ιRing f S T h (mlocREquiv f S (LocalizedModule.mk a 1))
    simp only [mlocREquiv_mk_one, ιRing_algebraMap]
  exact LinearMap.congr_fun key x


@[deprecated (since := "2026-09-27")]
alias cechdInt := cechd

@[deprecated (since := "2026-09-27")]
alias cechdInt_eq_zero_of_ne := cechd_eq_zero_of_ne

@[deprecated (since := "2026-09-27")]
alias cechdInt_succ := cechd_succ

@[deprecated (since := "2026-09-27")]
alias cechdInt_comp_cechdInt := cechd_comp_cechd

end ExtendedAlternatingCech
