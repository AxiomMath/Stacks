module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.SectionDivision
public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.SectionRing
public import StacksFrontier.RingTheory.GradedAlgebra.GenusOneSectionRing
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic

/-!
# The section ring of a point divisor as an abstract genus-one section ring

Let `X` be an integral scheme over a field `k` with `Γ(X, 𝒪_X) = k`, `x` a point of `X` whose
local ring is a discrete valuation ring with residue field `k`, and `L` an invertible module with
a section `Z` of `L` that does not vanish off `x` and has order `d` at `x`. Given the
Riemann–Roch bounds on the dimensions of the graded pieces, this file packages the section ring
`Γ_*(X, L)`, graded by `k`-submodules, with the order at `x`, as the data
`Stacks.GenusOneSectionRing.Data` of the abstract theory.

## Main definitions

* `AlgebraicGeometry.GenusOne.ringOrd`: the order at `x` of an element of `Γ_*(X, L)`, the least
  order of its homogeneous components.
* `AlgebraicGeometry.GenusOne.sectionRingData`: the data.

## Main results

* `AlgebraicGeometry.GenusOne.ringOrd_of`: on a homogeneous element the order is that of
  `Stacks.StalkOrder.sectionOrd`.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open Stacks.GradedSections (powSections sectionRing mul mulMap)
open Stacks.SectionProduct (globalSection)
open Stacks.TensorPowers (natTensorPow)
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (baseRingHom)
open Stacks.StalkOrder

open scoped DirectSum

universe u

namespace AlgebraicGeometry.GenusOne

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

attribute [local instance] Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.sectionAlgebra

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
  (x : X) [IsDomain (X.presheaf.stalk x)] [IsDiscreteValuationRing (X.presheaf.stalk x)]

/-- **The order at `x` of an element of `Γ_*(X, L)`**: the least order at `x` of its homogeneous
components. -/
def ringOrd (a : sectionRing L) : ℕ∞ := ⨅ n : ℕ, sectionOrd x L (a n)

omit [IsDiscreteValuationRing (X.presheaf.stalk x)] in
/-- The order at `x` of the zero section of `L ^⊗ n` is `⊤`. -/
theorem sectionOrd_zero [IsDiscreteValuationRing (X.presheaf.stalk x)] (n : ℕ) :
    sectionOrd x L (0 : powSections L n) = ⊤ := by
  have := Stacks.SectionProduct.isInvertibleModule_natTensorPow (X := X) L n
  unfold sectionOrd sectionGerm
  rw [stalkOrd_eq_top_iff]
  have h : globalSection X (natTensorPow L n) 0 = 0 :=
    map_zero (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X (natTensorPow L n))
  rw [h, map_zero]

/-- **On a homogeneous element the order is that of its only component.** -/
theorem ringOrd_of {m : ℕ} (s : powSections L m) :
    ringOrd L x (DirectSum.of (powSections L) m s) = sectionOrd x L s := by
  classical
  refine le_antisymm (iInf_le_of_le m (by rw [DirectSum.of_eq_same])) (le_iInf fun n => ?_)
  by_cases h : n = m
  · subst h
    rw [DirectSum.of_eq_same]
  · rw [DirectSum.of_eq_of_ne m n s h, sectionOrd_zero]
    exact le_top

variable (k : Type u) [Field k] [X.Over (Spec (.of k))]

/-- An element of `Γ_*(X, L)` lies in the `m`-th graded piece if and only if it is the image of
a section of `L ^⊗ m`. -/
theorem mem_gradingK_iff_exists {m : ℕ} {a : sectionRing L} :
    a ∈ gradingK L k m ↔ ∃ s : powSections L m, DirectSum.of (powSections L) m s = a :=
  Iff.rfl

/-- **The order of a product of homogeneous elements is the sum of the orders.** -/
theorem ringOrd_mul {m n : ℕ} {a b : sectionRing L} (ha : a ∈ gradingK L k m)
    (hb : b ∈ gradingK L k n) : ringOrd L x (a * b) = ringOrd L x a + ringOrd L x b := by
  obtain ⟨s, rfl⟩ := ha
  obtain ⟨t, rfl⟩ := hb
  rw [Stacks.SectionProduct.of_mul_of, ringOrd_of, ringOrd_of, ringOrd_of, sectionOrd_mul]

/-- **The order of a sum of two homogeneous elements of one degree is at least the smaller
order.** -/
theorem min_le_ringOrd_add {m : ℕ} {a b : sectionRing L} (ha : a ∈ gradingK L k m)
    (hb : b ∈ gradingK L k m) :
    min (ringOrd L x a) (ringOrd L x b) ≤ ringOrd L x (a + b) := by
  obtain ⟨s, rfl⟩ := ha
  obtain ⟨t, rfl⟩ := hb
  rw [← map_add, ringOrd_of, ringOrd_of, ringOrd_of]
  exact min_le_sectionOrd_add L s t

omit [IsDomain (X.presheaf.stalk x)] [IsDiscreteValuationRing (X.presheaf.stalk x)] in
/-- The germ of the image of a scalar is a unit when the scalar is nonzero. -/
theorem isUnit_germ_baseRingHom {c : k} (hc : c ≠ 0) :
    IsUnit ((X.presheaf.Γgerm x).hom (baseRingHom k X c)) :=
  ((Units.mk0 c hc).isUnit.map (baseRingHom k X)).map (X.presheaf.Γgerm x).hom

/-- **Scaling by a nonzero scalar does not change the order.** -/
theorem ringOrd_smul {m : ℕ} {a : sectionRing L} (ha : a ∈ gradingK L k m) {c : k}
    (hc : c ≠ 0) : ringOrd L x (c • a) = ringOrd L x a := by
  obtain ⟨s, rfl⟩ := ha
  rw [smul_of, ringOrd_of, ringOrd_of, sectionOrd_unitScalarEquiv_symm_comp,
    IsDiscreteValuationRing.addVal_eq_zero_iff.mpr (isUnit_germ_baseRingHom x k hc), zero_add]

omit [IsDomain (X.presheaf.stalk x)] [IsDiscreteValuationRing (X.presheaf.stalk x)] in
/-- The global section of a difference of homogeneous elements, one of them scaled by a
function. -/
theorem sectionGerm_sub_comp {m : ℕ} (s t : powSections L m) (c : Γ(X, ⊤)) :
    sectionGerm (x := x) L (s - (Stacks.SectionRingGeometric.unitScalarEquiv X).symm c ≫ t) =
      sectionGerm (x := x) L s - (X.presheaf.Γgerm x).hom c • sectionGerm (x := x) L t := by
  unfold sectionGerm
  have h : globalSection X (natTensorPow L m)
      (s - (Stacks.SectionRingGeometric.unitScalarEquiv X).symm c ≫ t) =
      globalSection X (natTensorPow L m) s - globalSection X (natTensorPow L m)
        ((Stacks.SectionRingGeometric.unitScalarEquiv X).symm c ≫ t) :=
    map_sub (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X (natTensorPow L m)) _ _
  rw [h, map_sub]
  show _ - ((natTensorPow L m).presheaf.Γgerm x).hom
      (globalSection X _ ((Stacks.SectionRingGeometric.unitScalarEquiv X).symm c ≫ t)) = _
  rw [globalSection_unitScalarEquiv_symm_comp, Stacks.ModuleStalk.Γgerm_smul]

/-- **Two homogeneous elements of one degree and one finite order agree to first order up to a
scalar**, when the residue field at `x` is `k`. -/
theorem exists_lt_ringOrd_sub [IsIntegral X]
    (hres : ∀ v : X.presheaf.stalk x, ∃ c : k,
      v - (X.presheaf.Γgerm x).hom (baseRingHom k X c) ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    {m : ℕ} {a b : sectionRing L} (ha : a ∈ gradingK L k m) (hb : b ∈ gradingK L k m)
    (hb0 : b ≠ 0) (hab : ringOrd L x a = ringOrd L x b) :
    ∃ c : k, ringOrd L x a < ringOrd L x (a - c • b) := by
  obtain ⟨s, rfl⟩ := ha
  obtain ⟨t, rfl⟩ := hb
  have := Stacks.SectionProduct.isInvertibleModule_natTensorPow (X := X) L m
  rw [ringOrd_of, ringOrd_of] at hab
  have htop : sectionOrd x L t ≠ ⊤ := fun h =>
    hb0 (by rw [(sectionOrd_eq_top_iff L t).mp h, map_zero])
  obtain ⟨v, hv⟩ := exists_unit_smul_eq (M := natTensorPow L m) (x := x) hab
  obtain ⟨c, hc⟩ := hres v
  refine ⟨c, ?_⟩
  rw [smul_of, ← map_sub, ringOrd_of, ringOrd_of, hab]
  unfold sectionOrd
  rw [sectionGerm_sub_comp]
  show stalkOrd _ x (sectionGerm L t) < stalkOrd _ x (sectionGerm L s - _)
  rw [hv, ← sub_smul, stalkOrd_smul]
  have h1 : 1 ≤ IsDiscreteValuationRing.addVal (X.presheaf.stalk x)
      ((v : X.presheaf.stalk x) - (X.presheaf.Γgerm x).hom (baseRingHom k X c)) := by
    rw [Order.one_le_iff_pos, pos_iff_ne_zero]
    exact fun h0 =>
      (IsLocalRing.mem_maximalIdeal _).mp hc (IsDiscreteValuationRing.addVal_eq_zero_iff.mp h0)
  show sectionOrd x L t < _ + sectionOrd x L t
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  rw [← hn]
  calc (n : ℕ∞) < 1 + n := by
        exact_mod_cast Nat.lt_one_add_iff.mpr le_rfl
    _ ≤ _ := add_le_add_left h1 _

/-- **Division by powers of `Z`** in the section ring: a homogeneous element of degree `m + j`
whose order is at least `d j` is `Z ^ j` times a homogeneous element of degree `m`, when `Z` has
degree one, order `d`, and does not vanish off `x`. -/
theorem exists_eq_Z_pow_mul (Z : powSections L 1)
    (hZ : ∀ y : X, y ≠ x →
      y ∈ Stacks.NonvanishingOpen.nonvanishingOpen X (natTensorPow L 1) (globalSection X _ Z))
    {d : ℕ} (hZd : sectionOrd x L Z = d) :
    ∀ (j : ℕ) {m : ℕ} {a : sectionRing L}, a ∈ gradingK L k (m + j) →
      ((d * j : ℕ) : ℕ∞) ≤ ringOrd L x a →
        ∃ b ∈ gradingK L k m, a = DirectSum.of (powSections L) 1 Z ^ j * b
  | 0, m, a, ha, _ => ⟨a, ha, by rw [pow_zero, one_mul]⟩
  | j + 1, m, a, ha, hord => by
    have hdeg : m + (j + 1) = 1 + (m + j) := by omega
    rw [hdeg] at ha
    obtain ⟨t, rfl⟩ := ha
    rw [ringOrd_of] at hord
    have hle : sectionOrd x L Z ≤ sectionOrd x L t := by
      rw [hZd]
      refine le_trans ?_ hord
      exact_mod_cast Nat.le_mul_of_pos_right d (Nat.succ_pos j)
    obtain ⟨b', rfl⟩ := Stacks.StalkOrder.exists_mul_eq_of_sectionOrd_le L Z hZ t hle
    have hb'ord : ((d * j : ℕ) : ℕ∞) ≤ ringOrd L x (DirectSum.of (powSections L) (m + j) b') := by
      rw [ringOrd_of]
      rw [sectionOrd_mul, hZd, Nat.mul_succ, Nat.cast_add, add_comm (d : ℕ∞)] at hord
      exact (ENat.add_le_add_iff_right (ENat.natCast_ne_top d)).mp hord
    obtain ⟨b, hb, hbeq⟩ := exists_eq_Z_pow_mul Z hZ hZd j ⟨b', rfl⟩ hb'ord
    refine ⟨b, hb, ?_⟩
    rw [← Stacks.SectionProduct.of_mul_of, hbeq, pow_succ', mul_assoc]

/-- **Degree zero is the ground field**, when `k ⟶ Γ(X, 𝒪_X)` is surjective. -/
theorem exists_eq_algebraMap_of_mem_zero (hsurj : Function.Surjective (baseRingHom k X))
    {a : sectionRing L} (ha : a ∈ gradingK L k 0) :
    ∃ c : k, a = algebraMap k (sectionRing L) c := by
  obtain ⟨s, rfl⟩ := ha
  obtain ⟨c, hc⟩ := hsurj (Stacks.SectionRingGeometric.unitScalarEquiv X s)
  refine ⟨c, ?_⟩
  rw [Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.algebraMap_eq, hc,
    Equiv.symm_apply_apply]

/-- **The data of the abstract theory**, for the section ring of `L` with the order at `x`. -/
def sectionRingData [IsIntegral X]
    (hres : ∀ v : X.presheaf.stalk x, ∃ c : k,
      v - (X.presheaf.Γgerm x).hom (baseRingHom k X c) ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hsurj : Function.Surjective (baseRingHom k X)) (Z : powSections L 1)
    (hZ : ∀ y : X, y ≠ x →
      y ∈ Stacks.NonvanishingOpen.nonvanishingOpen X (natTensorPow L 1) (globalSection X _ Z))
    {d : ℕ} (hZd : sectionOrd x L Z = d) (hfin : ∀ m, FiniteDimensional k (gradingK L k m))
    (hle : ∀ m, 1 ≤ m → d * m ≤ Module.finrank k (gradingK L k m))
    (hev : ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → Module.finrank k (gradingK L k m) ≤ d * m) :
    Stacks.GenusOneSectionRing.Data (gradingK L k) d where
  ord := ringOrd L x
  ord_eq_top_iff {m a} ha := by
    obtain ⟨s, rfl⟩ := ha
    rw [ringOrd_of, sectionOrd_eq_top_iff]
    exact ⟨fun h => by rw [h, map_zero],
      fun h => DirectSum.of_injective (β := powSections L) m (h.trans (map_zero _).symm)⟩
  ord_mul ha hb := ringOrd_mul L x k ha hb
  min_le_ord_add ha hb := min_le_ringOrd_add L x k ha hb
  ord_smul ha _ hc := ringOrd_smul L x k ha hc
  exists_lt_ord_sub ha hb hb0 hab := exists_lt_ringOrd_sub L x k hres ha hb hb0 hab
  Z := DirectSum.of (powSections L) 1 Z
  Z_mem := ⟨Z, rfl⟩
  ord_Z := by rw [ringOrd_of, hZd]
  exists_eq_Z_pow_mul ha hj := exists_eq_Z_pow_mul L x k Z hZ hZd _ ha hj
  exists_eq_algebraMap ha := exists_eq_algebraMap_of_mem_zero L k hsurj ha
  finiteDimensional := hfin
  le_finrank hm := hle _ hm
  eventually_finrank_le := hev

attribute [local instance]
  Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule

/-- **The `m`-th graded piece is `Γ(X, L ^⊗ m)`**, `k`-linearly. -/
def gradingKEquivSections (m : ℕ) : gradingK L k m ≃ₗ[k] Γ(natTensorPow L m, ⊤) :=
  { toFun := fun a => globalSection X (natTensorPow L m)
      ((Stacks.ExternalGrading.summandEquiv (powSections L) m).symm ⟨a.1, a.2⟩)
    invFun := fun y => ⟨DirectSum.of (powSections L) m
      ((Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X (natTensorPow L m)).symm y),
        ⟨_, rfl⟩⟩
    left_inv := fun a => by
      obtain ⟨_, s, rfl⟩ := a
      apply Subtype.ext
      change DirectSum.of (powSections L) m
          ((Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X (natTensorPow L m)).symm
            (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X (natTensorPow L m)
              ((Stacks.ExternalGrading.summandEquiv (powSections L) m).symm
                (Stacks.ExternalGrading.summandEquiv (powSections L) m s)))) = _
      rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
    right_inv := fun y => by
      change Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X (natTensorPow L m)
          ((Stacks.ExternalGrading.summandEquiv (powSections L) m).symm
            (Stacks.ExternalGrading.summandEquiv (powSections L) m
              ((Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X
                (natTensorPow L m)).symm y))) = y
      rw [AddEquiv.symm_apply_apply, AddEquiv.apply_symm_apply]
    map_add' := fun a b => by
      change globalSection X _ ((Stacks.ExternalGrading.summandEquiv (powSections L) m).symm
        (⟨a.1, a.2⟩ + ⟨b.1, b.2⟩)) = _
      rw [map_add]
      exact map_add (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _) _ _
    map_smul' := fun c a => by
      obtain ⟨_, s, rfl⟩ := a
      have h : (⟨c • DirectSum.of (powSections L) m s, (gradingK L k m).smul_mem c ⟨s, rfl⟩⟩ :
          Stacks.AmpleFiniteAvoidance.grading L m) =
          Stacks.ExternalGrading.summandEquiv (powSections L) m
            ((Stacks.SectionRingGeometric.unitScalarEquiv X).symm (baseRingHom k X c) ≫ s) :=
        Subtype.ext (smul_of L k c s)
      change globalSection X _ ((Stacks.ExternalGrading.summandEquiv (powSections L) m).symm
        ⟨c • DirectSum.of (powSections L) m s, (gradingK L k m).smul_mem c ⟨s, rfl⟩⟩) =
          baseRingHom k X c • globalSection X _
            ((Stacks.ExternalGrading.summandEquiv (powSections L) m).symm
              (Stacks.ExternalGrading.summandEquiv (powSections L) m s))
      rw [h, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply,
        globalSection_unitScalarEquiv_symm_comp] }

/-- The `m`-th graded piece is `k`-linearly equivalent to `H⁰(X, L ^⊗ m)`. -/
private def gradingKEquivCohomology (m : ℕ) :
    gradingK L k m ≃ₗ[k] cohomologyOverField k (X ↘ Spec (.of k)) (natTensorPow L m) 0 :=
  (gradingKEquivSections L k m).trans
    (cohomologyOverFieldZeroIsoSections k (X ↘ Spec (.of k)) (natTensorPow L m)).toLinearEquiv.symm

/-- **The dimension of the `m`-th graded piece is `dim_k H⁰(X, L ^⊗ m)`.** -/
theorem finrank_gradingK (m : ℕ) :
    Module.finrank k (gradingK L k m) =
      Module.finrank k (cohomologyOverField k (X ↘ Spec (.of k)) (natTensorPow L m) 0) :=
  (gradingKEquivCohomology L k m).finrank_eq

/-- The graded pieces are finite dimensional when the cohomology is. -/
theorem finiteDimensional_gradingK (m : ℕ)
    [FiniteDimensional k (cohomologyOverField k (X ↘ Spec (.of k)) (natTensorPow L m) 0)] :
    FiniteDimensional k (gradingK L k m) :=
  LinearEquiv.finiteDimensional (gradingKEquivCohomology L k m).symm

end AlgebraicGeometry.GenusOne

end
