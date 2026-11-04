module

public import StacksFrontier.AlgebraicGeometry.Chow.DvrTameSymbol.Invariance
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbolGeneral.Local

/-!
# At a discrete valuation ring the general tame symbol is the tame symbol of Section 42.5

Let `A` be a discrete valuation ring with fraction field `F`. Then `A` is its own normalization,
the family `Stacks.Chow.normalizationDvrFamily` has a single member, the local ring of `A` at its
maximal ideal, and the map from `A` to it is an isomorphism. So the tame symbol built by
normalization and norm (`Stacks.Normalization.SemilocalDvrFamily.tameSymbol`) is the tame symbol
`Stacks.Chow.dvrMilnorTameSymbol'` of `A`, provided the norm of a trivial extension is the
identity — which is the projection formula `N_{L/K}(ι z) = [L : K] z` at `[L : K] = 1`
(`Stacks.Chow.MilnorKNormFamily.ProjectionFormula`).

## Main results

* `Stacks.Normalization.SemilocalDvrFamily.tameShift_eq_of_bijective` — for a family each of
  whose members is isomorphic to `A`, and with a single member, the general symbol is `∂_A`.
* `Stacks.Chow.bijective_algebraMap_normalizationDvrFamily`,
  `Stacks.Chow.card_normalizationDvrFamily_index` — the normalization of a discrete valuation
  ring is such a family.
* `Stacks.Chow.tameSymbol_normalizationDvrFamily_eq_dvrMilnorTameSymbol'` — at a discrete
  valuation ring the general tame symbol is `Stacks.Chow.dvrMilnorTameSymbol'`.

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
-/

@[expose] public noncomputable section

open IsLocalRing IsDiscreteValuationRing

universe u

namespace Stacks.Chow

/-- **The projection formula for the norm maps, in the form `N_{L/K}(ι z) = [L : K] z`.** -/
def MilnorKNormFamily.ProjectionFormula (N : MilnorKNormFamily.{u}) : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (z : MilnorKRing K),
    N K L (milnorKRingMap (algebraMap K L) z) = (Module.finrank K L : ℤ) • z

/-- **The norm of a trivial extension is the identity on the image**: if `K → L` is bijective,
`N_{L/K}(ι z) = z`. -/
theorem MilnorKNormFamily.ProjectionFormula.apply_of_bijective {N : MilnorKNormFamily.{u}}
    (hN : N.ProjectionFormula) {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (h : Function.Bijective (algebraMap K L)) (z : MilnorKRing K) :
    N K L (milnorKRingMap (algebraMap K L) z) = z := by
  rw [hN, Module.finrank_of_bijective_algebraMap h, Nat.cast_one, one_smul]

end Stacks.Chow

namespace Stacks.Normalization.SemilocalDvrFamily

open Stacks.Chow

attribute [local instance] finite_index commRing isDomain isDiscreteValuationRing algebraBase
  isLocalHom algebraFractionField isScalarTower isFractionRing moduleFiniteResidueField

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {F : Type u}
  [Field F] [Algebra A F] [IsFractionRing A F] (𝓕 : SemilocalDvrFamily.{u, u, u} A F)
  {N : MilnorKNormFamily.{u}}

omit [IsFractionRing A F] in
/-- A bijective local homomorphism of local rings induces a bijection of residue fields. -/
theorem bijective_algebraMap_residueField_of_bijective (m : 𝓕.Index)
    (hbij : Function.Bijective (algebraMap A (𝓕.Dvr m))) :
    Function.Bijective (algebraMap (ResidueField A) (ResidueField (𝓕.Dvr m))) := by
  refine ⟨(algebraMap (ResidueField A) (ResidueField (𝓕.Dvr m))).injective, fun y ↦ ?_⟩
  obtain ⟨b, rfl⟩ := residue_surjective y
  obtain ⟨a, rfl⟩ := hbij.2 b
  exact ⟨residue A a, ResidueField.algebraMap_residue a⟩

/-- **A member isomorphic to `A` contributes `∂_A`.** -/
theorem tameShiftAt_eq_of_bijective (hN : N.ProjectionFormula) (m : 𝓕.Index)
    (hbij : Function.Bijective (algebraMap A (𝓕.Dvr m))) (x : MilnorKRing F) :
    𝓕.tameShiftAt N m x = MilnorKShift.shift
      (dvrMilnorShiftMap (A := A) (F := F) (exists_irreducible A).choose_spec x) := by
  have hunr : Irreducible (algebraMap A (𝓕.Dvr m) (exists_irreducible A).choose) :=
    (MulEquiv.irreducible_iff (RingEquiv.ofBijective _ hbij)).mpr
      (exists_irreducible A).choose_spec
  rw [tameShiftAt_apply, dvrMilnorShiftMap_shift_algebraMap (exists_irreducible A).choose_spec
      (exists_irreducible (𝓕.Dvr m)).choose_spec hunr,
    hN.apply_of_bijective (𝓕.bijective_algebraMap_residueField_of_bijective m hbij)]

/-- **A family with a single member, isomorphic to `A`, has the tame symbol `∂_A`.** -/
theorem tameShift_eq_of_bijective (hN : N.ProjectionFormula)
    (hbij : ∀ m, Function.Bijective (algebraMap A (𝓕.Dvr m))) (hcard : Nat.card 𝓕.Index = 1)
    (x : MilnorKRing F) :
    𝓕.tameShift N x = MilnorKShift.shift
      (dvrMilnorShiftMap (A := A) (F := F) (exists_irreducible A).choose_spec x) := by
  let := Fintype.ofFinite 𝓕.Index
  rw [tameShift_apply, Finset.sum_congr rfl fun m _ ↦ 𝓕.tameShiftAt_eq_of_bijective hN m (hbij m) x,
    Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hcard, one_smul]

end Stacks.Normalization.SemilocalDvrFamily

namespace Stacks.Chow

variable (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  (F : Type u) [Field F] [Algebra A F] [IsFractionRing A F]

/-- A discrete valuation ring has Krull dimension one. -/
theorem ringKrullDim_eq_one_of_isDiscreteValuationRing : ringKrullDim A = 1 :=
  IsDiscreteValuationRing.ringKrullDim_eq_one A

/-- **A discrete valuation ring is its own normalization**: the map from `A` to its integral
closure in `F` is bijective. -/
theorem bijective_algebraMap_integralClosure :
    Function.Bijective (algebraMap A ↥(integralClosure A F)) := by
  refine ⟨fun a b hab ↦ IsFractionRing.injective A F ?_, fun y ↦ ?_⟩
  · simpa using congrArg (fun z : ↥(integralClosure A F) ↦ (z : F)) hab
  · have hy : (y : F) ∈ (⊥ : Subalgebra A F) := by
      rw [← IsIntegrallyClosed.integralClosure_eq_bot A F]
      exact y.2
    obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hy
    exact ⟨a, Subtype.ext ha⟩

/-- A maximal ideal of the integral closure of a discrete valuation ring contracts to the maximal
ideal of the ring. -/
private theorem comap_eq_maximalIdeal_of_isMaximal {B : Type u} [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] (I : Ideal B) [I.IsMaximal] :
    I.comap (algebraMap A B) = IsLocalRing.maximalIdeal A :=
  eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) I)

/-- **The normalization of a discrete valuation ring has a single maximal ideal.** -/
theorem card_normalizationDvrFamily_index :
    Nat.card (normalizationDvrFamily A F
      (ringKrullDim_eq_one_of_isDiscreteValuationRing A)).Index = 1 := by
  show Nat.card (MaximalSpectrum ↥(integralClosure A F)) = 1
  have hbij := bijective_algebraMap_integralClosure A F
  have hsub : Subsingleton (MaximalSpectrum ↥(integralClosure A F)) := by
    refine ⟨fun v w ↦ MaximalSpectrum.ext (Ideal.comap_injective_of_surjective _ hbij.2 ?_)⟩
    rw [comap_eq_maximalIdeal_of_isMaximal A v.asIdeal,
      comap_eq_maximalIdeal_of_isMaximal A w.asIdeal]
  have hne : Nonempty (MaximalSpectrum ↥(integralClosure A F)) := by
    obtain ⟨m, hm⟩ := Ideal.exists_maximal ↥(integralClosure A F)
    exact ⟨⟨m, hm⟩⟩
  exact Nat.card_unique

/-- **The map from a discrete valuation ring to the members of its normalization family is
bijective**: the integral closure is `A`, and its localization at its maximal ideal inverts only
units. -/
theorem bijective_algebraMap_normalizationDvrFamily
    (m : (normalizationDvrFamily A F (ringKrullDim_eq_one_of_isDiscreteValuationRing A)).Index) :
    Function.Bijective (@algebraMap A
      ((normalizationDvrFamily A F (ringKrullDim_eq_one_of_isDiscreteValuationRing A)).Dvr m) _
      ((normalizationDvrFamily A F
        (ringKrullDim_eq_one_of_isDiscreteValuationRing A)).commRing m).toSemiring
      ((normalizationDvrFamily A F
        (ringKrullDim_eq_one_of_isDiscreteValuationRing A)).algebraBase m)) := by
  have : m.asIdeal.IsMaximal := m.isMaximal
  show Function.Bijective (algebraMap A (Localization.AtPrime m.asIdeal))
  have hbij := bijective_algebraMap_integralClosure A F
  have hunits : m.asIdeal.primeCompl ≤ IsUnit.submonoid ↥(integralClosure A F) := by
    intro s hs
    obtain ⟨a, rfl⟩ := hbij.2 s
    have ha : a ∉ IsLocalRing.maximalIdeal A := fun ha ↦ hs <|
      (comap_eq_maximalIdeal_of_isMaximal A m.asIdeal).ge ha
    exact (IsLocalRing.notMem_maximalIdeal.mp ha).map _
  have hloc : Function.Bijective (algebraMap ↥(integralClosure A F)
      (Localization.AtPrime m.asIdeal)) :=
    (IsLocalization.atUnits ↥(integralClosure A F) m.asIdeal.primeCompl
      (S := Localization.AtPrime m.asIdeal) hunits).bijective
  rw [IsScalarTower.algebraMap_eq A ↥(integralClosure A F) (Localization.AtPrime m.asIdeal),
    RingHom.coe_comp]
  exact hloc.comp hbij

variable {A F} in
/-- **At a discrete valuation ring the normalization-and-norm symbol is the tame symbol of
Section 42.5**, on the whole Milnor K-ring. -/
theorem tameShift_normalizationDvrFamily_eq {N : MilnorKNormFamily.{u}} (hN : N.ProjectionFormula)
    (hdim : ringKrullDim A = 1) (x : MilnorKRing F) :
    (normalizationDvrFamily A F hdim).tameShift N x = MilnorKShift.shift
      (dvrMilnorShiftMap (A := A) (F := F) (exists_irreducible A).choose_spec x) :=
  Stacks.Normalization.SemilocalDvrFamily.tameShift_eq_of_bijective _ hN
    (bijective_algebraMap_normalizationDvrFamily A F) (card_normalizationDvrFamily_index A F) x

variable {A F} in
/-- **At a discrete valuation ring the general tame symbol is the tame symbol
`Stacks.Chow.dvrMilnorTameSymbol'` of Section 42.5, in every degree.** -/
theorem tameSymbol_normalizationDvrFamily_eq_dvrMilnorTameSymbol' {N : MilnorKNormFamily.{u}}
    (hN : N.ProjectionFormula) (hgr : N.PreservesGrading) (hdim : ringKrullDim A = 1) (i : ℕ) :
    (normalizationDvrFamily A F hdim).tameSymbol hgr i = dvrMilnorTameSymbol' A F i :=
  AddMonoidHom.ext fun y ↦ Subtype.ext (by
    rw [Stacks.Normalization.SemilocalDvrFamily.coe_tameSymbol,
      tameShift_normalizationDvrFamily_eq hN hdim, dvrMilnorTameSymbol'_coe])

end Stacks.Chow

end
