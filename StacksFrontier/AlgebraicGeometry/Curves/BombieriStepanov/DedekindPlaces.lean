module

public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.ValuationCenter
public import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# Maximal ideals of a Dedekind subring of the function field as places

Let `X` be an integral curve, universally closed over a field `F`, whose local rings at its places
are discrete valuation rings, and let `A` be a Dedekind domain with fraction field `R(X)`
containing `F`. For a nonzero maximal ideal `P` of `A` the localization `A_P` is a valuation
subring of `R(X)` containing `F` and different from `R(X)`, so it is the local ring `𝒪_{X,x}` of a
place `x = x_P` (`Stacks.BombieriStepanov.exists_curvePlace_mem_iff`). The inclusion
`A ⊆ A_P = 𝒪_{X,x}` followed by the residue map is a surjection `θ_P : A → κ(x_P)` with kernel
`P`. This is how the closed points of an affine Dedekind model are read on a proper model.

## Main results

* `Stacks.BombieriStepanov.exists_curvePlace_eq_localization`: the place `x_P`.
* `Stacks.BombieriStepanov.toStalk`: the inclusion `A → 𝒪_{X,x}` once `A ⊆ 𝒪_{X,x}`.
* `Stacks.BombieriStepanov.ker_residue_comp_toStalk`,
  `Stacks.BombieriStepanov.surjective_residue_comp_toStalk`: `θ_P` is onto with kernel `P`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order IsDedekindDomain

universe u

namespace Stacks.BombieriStepanov

variable {X : Scheme.{u}} [IsIntegral X] {A : Type u} [CommRing A] [Algebra A X.functionField]
  [IsFractionRing A X.functionField]

section ToStalk

variable (x : X) (hA : ∀ a : A, ∃ s : X.presheaf.stalk x,
  algebraMap (X.presheaf.stalk x) X.functionField s = algebraMap A X.functionField a)

/-- The inclusion `A → 𝒪_{X,x}`, when `A ⊆ 𝒪_{X,x}` inside `R(X)`. -/
def toStalk : A →+* X.presheaf.stalk x where
  toFun a := (hA a).choose
  map_one' := IsFractionRing.injective (X.presheaf.stalk x) X.functionField (by
    rw [(hA 1).choose_spec, map_one, map_one])
  map_mul' a b := IsFractionRing.injective (X.presheaf.stalk x) X.functionField (by
    rw [(hA _).choose_spec, map_mul, map_mul, (hA a).choose_spec, (hA b).choose_spec])
  map_zero' := IsFractionRing.injective (X.presheaf.stalk x) X.functionField (by
    rw [(hA 0).choose_spec, map_zero, map_zero])
  map_add' a b := IsFractionRing.injective (X.presheaf.stalk x) X.functionField (by
    rw [(hA _).choose_spec, map_add, map_add, (hA a).choose_spec, (hA b).choose_spec])

omit [IsFractionRing A X.functionField] in
/-- `toStalk` is compatible with the inclusions into the function field. -/
theorem algebraMap_toStalk (a : A) :
    algebraMap (X.presheaf.stalk x) X.functionField (toStalk x hA a) =
      algebraMap A X.functionField a :=
  (hA a).choose_spec

end ToStalk

/-- An element of `A` outside an ideal `P` has nonzero image in the fraction field. -/
private theorem algebraMap_ne_zero_of_notMem {P : Ideal A} {t : A} (ht : t ∉ P) :
    algebraMap A X.functionField t ≠ 0 := fun h =>
  ht ((map_eq_zero_iff _ (IsFractionRing.injective A _)).1 h ▸ P.zero_mem)

section Dedekind

variable [IsDedekindDomain A]

/-- Membership in the localization `A_P ⊆ R(X)`. -/
theorem mem_valuationSubringAtPrime_iff (v : HeightOneSpectrum A) (f : X.functionField) :
    f ∈ v.valuationSubringAtPrime X.functionField ↔
      ∃ a t : A, t ∉ v.asIdeal ∧ f = algebraMap A X.functionField a * (algebraMap A _ t)⁻¹ := by
  change (∃ (a s : A) (_ : s ∈ v.asIdeal.primeCompl), f = _) ↔ _
  simp [Ideal.primeCompl]

variable {F : Type u} [Field F] (p : X ⟶ Spec (.of F))

/-- **The place of a maximal ideal.** For a nonzero maximal ideal `P` of a Dedekind domain
`A ⊇ F` with fraction field `R(X)`, there is a place `x` of `X` whose local ring is `A_P`. -/
theorem exists_curvePlace_eq_localization [UniversallyClosed p] [IsCurve F p]
    (hdvr : ∀ x : X, coheight x = 1 → IsDiscreteValuationRing (X.presheaf.stalk x))
    (hF : ∀ c : F,
      ∃ a : A, algebraMap A X.functionField a = (fieldToStalk p (genericPoint X)).hom c)
    (P : Ideal A) [P.IsMaximal] (hP : P ≠ ⊥) :
    ∃ x : CurvePlace X, ∀ f : X.functionField,
      (∃ s : X.presheaf.stalk x.1, algebraMap _ X.functionField s = f) ↔
        ∃ a t : A, t ∉ P ∧ f = algebraMap A X.functionField a * (algebraMap A _ t)⁻¹ := by
  set v : HeightOneSpectrum A := ⟨P, inferInstance, hP⟩
  have hk : ∀ c : F, (fieldToStalk p (genericPoint X)).hom c ∈
      v.valuationSubringAtPrime X.functionField := by
    intro c
    obtain ⟨a, ha⟩ := hF c
    rw [mem_valuationSubringAtPrime_iff]
    exact ⟨a, 1, P.one_notMem, by simp [ha]⟩
  have hV : v.valuationSubringAtPrime X.functionField ≠ ⊤ := by
    obtain ⟨π, hπP, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
    intro htop
    have hmem : (algebraMap A X.functionField π)⁻¹ ∈
        v.valuationSubringAtPrime X.functionField := htop ▸ ValuationSubring.mem_top _
    rw [mem_valuationSubringAtPrime_iff] at hmem
    obtain ⟨a, t, ht, heq⟩ := hmem
    have hπ0' : algebraMap A X.functionField π ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective A _)).2 hπ0
    have ht0 := algebraMap_ne_zero_of_notMem (X := X) ht
    have h1 : algebraMap A X.functionField t = algebraMap A X.functionField (a * π) := by
      rw [map_mul]
      field_simp at heq
      linear_combination heq
    exact ht (IsFractionRing.injective A X.functionField h1 ▸ P.mul_mem_left a hπP)
  obtain ⟨x, hx⟩ := exists_curvePlace_mem_iff p hdvr _ hk hV
  exact ⟨x, fun f => (hx f).symm.trans (mem_valuationSubringAtPrime_iff v f)⟩

end Dedekind

section Residue

variable {P : Ideal A} [P.IsMaximal] {x : X}
  (hx : ∀ f : X.functionField,
    (∃ s : X.presheaf.stalk x, algebraMap _ X.functionField s = f) ↔
      ∃ a t : A, t ∉ P ∧ f = algebraMap A X.functionField a * (algebraMap A _ t)⁻¹)

omit [IsFractionRing A X.functionField] in
include hx in
/-- If `𝒪_{X,x} = A_P`, then `A ⊆ 𝒪_{X,x}` inside the function field. -/
theorem forall_exists_algebraMap_eq : ∀ a : A, ∃ s : X.presheaf.stalk x,
    algebraMap (X.presheaf.stalk x) X.functionField s = algebraMap A X.functionField a :=
  fun a => (hx _).2 ⟨a, 1, P.one_notMem, by simp⟩

omit [IsFractionRing A X.functionField] [P.IsMaximal] in
include hx in
/-- The inverse of an element of `A` outside `P` lies in `𝒪_{X,x}`. -/
theorem exists_algebraMap_eq_inv {t : A} (ht : t ∉ P) : ∃ s : X.presheaf.stalk x,
    algebraMap (X.presheaf.stalk x) X.functionField s = (algebraMap A X.functionField t)⁻¹ :=
  (hx _).2 ⟨1, t, ht, by simp⟩

include hx in
/-- `a ∈ A` maps into the maximal ideal of `𝒪_{X,x}` exactly when `a ∈ P`. -/
theorem toStalk_mem_maximalIdeal_iff (a : A) :
    toStalk x (forall_exists_algebraMap_eq hx) a ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) ↔ a ∈ P := by
  have hinj := IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  have hinjA := IsFractionRing.injective A X.functionField
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hnu
    by_contra haP
    obtain ⟨s, hs⟩ := exists_algebraMap_eq_inv hx haP
    have ha0 := algebraMap_ne_zero_of_notMem (X := X) haP
    refine hnu (IsUnit.of_mul_eq_one s (hinj ?_))
    rw [map_mul, algebraMap_toStalk, hs, map_one, mul_inv_cancel₀ ha0]
  · intro haP hu
    obtain ⟨w, hw⟩ := hu
    obtain ⟨b, t, ht, heq⟩ := (hx (algebraMap (X.presheaf.stalk x) X.functionField
      ((w⁻¹ : (X.presheaf.stalk x)ˣ) : X.presheaf.stalk x))).1 ⟨_, rfl⟩
    have h1 : algebraMap _ X.functionField ((w : X.presheaf.stalk x) *
        (w⁻¹ : (X.presheaf.stalk x)ˣ)) = 1 := by rw [Units.mul_inv, map_one]
    rw [map_mul, heq, hw, algebraMap_toStalk] at h1
    have ht0 := algebraMap_ne_zero_of_notMem (X := X) ht
    have h2 : algebraMap A X.functionField (a * b) = algebraMap A X.functionField t := by
      rw [map_mul]
      field_simp at h1
      exact h1
    exact ht (hinjA h2 ▸ P.mul_mem_right b haP)

include hx in
/-- The kernel of `θ_P : A → κ(x)` is `P`. -/
theorem ker_residue_comp_toStalk :
    RingHom.ker ((IsLocalRing.residue (X.presheaf.stalk x)).comp
      (toStalk x (forall_exists_algebraMap_eq hx))) = P := by
  ext a
  rw [RingHom.mem_ker, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff,
    toStalk_mem_maximalIdeal_iff hx]

include hx in
/-- `θ_P : A → κ(x)` is onto. -/
theorem surjective_residue_comp_toStalk :
    Function.Surjective ((IsLocalRing.residue (X.presheaf.stalk x)).comp
      (toStalk x (forall_exists_algebraMap_eq hx))) := by
  have hinj := IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  intro y
  obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨b, t, ht, heq⟩ := (hx (algebraMap _ X.functionField s)).1 ⟨s, rfl⟩
  obtain ⟨u, i, hi, hu⟩ := Ideal.IsMaximal.exists_inv (inferInstance : P.IsMaximal) ht
  obtain ⟨st, hst⟩ := exists_algebraMap_eq_inv hx ht
  refine ⟨b * u, ?_⟩
  rw [RingHom.comp_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  have hP : b * (t * u - 1) ∈ P := P.mul_mem_left b (by
    have h' : t * u - 1 = -i := by linear_combination hu
    rw [h']
    exact P.neg_mem hi)
  have hm := (toStalk_mem_maximalIdeal_iff hx _).2 hP
  have heq' : toStalk x (forall_exists_algebraMap_eq hx) (b * u) - s =
      toStalk x (forall_exists_algebraMap_eq hx) (b * (t * u - 1)) * st := by
    refine hinj ?_
    have ht0 := algebraMap_ne_zero_of_notMem (X := X) ht
    simp only [map_sub, map_mul, algebraMap_toStalk, hst, heq, map_one]
    field_simp
  rw [heq']
  exact Ideal.mul_mem_right _ _ hm

end Residue

end Stacks.BombieriStepanov

end
