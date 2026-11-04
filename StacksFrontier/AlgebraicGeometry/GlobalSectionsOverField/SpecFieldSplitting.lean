module

public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.GlobalSectionsOverField.SpecFieldFiniteSums
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.CohomologyGapSplitting
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.ExtVanishingRegular
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncationLevelHomology
public import StacksFrontier.CategoryTheory.Triangulated.OperationsOnFullSubcategories

/-!
# A bounded complex with coherent cohomology on the spectrum of a field splits

Let `k` be a field. An object `K` of `D(𝒪_{Spec k})` whose cohomology sheaves are coherent and
vanish outside `[a, b]` is a finite direct sum of the objects `𝒪_{Spec k}[-p]`, `p ∈ [a, b]`. In
the notation of [Stacks, Tag 0FX0]: `K ∈ smd(add(𝒪_{Spec k}[a, b]))`, with no extension needed.

`Spec k` is a regular Noetherian scheme of dimension `0`, so [Stacks, Tag 0FZ4] at the gap of
length `0` (with [Stacks, Tag 0FZ3] part (2)) splits `K ≅ τ_{≤ b-1}K ⊕ τ_{≥ b}K` in every degree
`b`; the top piece is concentrated in one degree with coherent cohomology, hence a finite sum of
copies of `𝒪_{Spec k}[-b]`
(`AlgebraicGeometry.exists_iso_biproduct_singleFunctor_unit_of_isGE_of_isLE`). This is the form in
which the cohomology `RΓ(X, 𝓕 ⊗ ℰ)` of [Stacks, Tag 0FZ6] and [Stacks, Section 0G07] enters the
bounds there.

## Main definitions

* `AlgebraicGeometry.specFieldSums`: the property `smd(add(𝒪_{Spec k}[a, b]))`.

## Main results

* `AlgebraicGeometry.specFieldSums_of_isGE_of_isLE`.

## References

* [Stacks Project, Tag 0FZ4](https://stacks.math.columbia.edu/tag/0FZ4)
* [Stacks Project, Tag 0FX0](https://stacks.math.columbia.edu/tag/0FX0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty ZeroObject

namespace AlgebraicGeometry

universe u

attribute [local instance 100000] HasDerivedCategory.standard

variable {k : Type u} [Field k]

/-- `smd(add(𝒪_{Spec k}[a, b]))`: direct summands of finite direct sums of the objects
`𝒪_{Spec k}[-p]`, `p ∈ [a, b]`, of `D(𝒪_{Spec k})`. -/
abbrev specFieldSums (k : Type u) [Field k] (a b : ℤ) :
    ObjectProperty (DerivedCategory (Spec (.of k)).Modules) :=
  (⨆ p ∈ Set.Icc a b, (ObjectProperty.singleton
    ((DerivedCategory.singleFunctor (Spec (.of k)).Modules 0).obj
      (SheafOfModules.unit (Spec (.of k)).ringCatSheaf))).isoClosure.shift p
    ).binaryProductsClosure.retractClosure

/-- `𝒪_{Spec k}[-p]` lies in `smd(add(𝒪_{Spec k}[a, b]))` for `p ∈ [a, b]`. -/
theorem specFieldSums_singleFunctor (a b p : ℤ) (hp : p ∈ Set.Icc a b) :
    specFieldSums k a b ((DerivedCategory.singleFunctor (Spec (.of k)).Modules p).obj
      (SheafOfModules.unit (Spec (.of k)).ringCatSheaf)) :=
  le_retractClosure _ _ (le_limitsClosure _ _ _ ((prop_iSup_iff _ _).2 ⟨p,
    (prop_iSup_iff _ _).2 ⟨hp, ⟨_, (ObjectProperty.singleton_iff _ _).2 rfl,
      ⟨((DerivedCategory.singleFunctors (Spec (.of k)).Modules).shiftIso p 0 p
        (by omega)).app _⟩⟩⟩⟩))

/-- `smd(add(𝒪_{Spec k}[a, b]))` is contained in `smd(add(𝒪_{Spec k}[a', b']))` when
`[a, b] ⊆ [a', b']`. -/
theorem specFieldSums_mono {a b a' b' : ℤ} (ha : a' ≤ a) (hb : b ≤ b') :
    specFieldSums k a b ≤ specFieldSums k a' b' :=
  monotone_retractClosure (limitsClosure_monotone _
    (iSup₂_le fun p hp => le_iSup₂_of_le p (Set.Icc_subset_Icc ha hb hp) le_rfl))

/-- `smd(add(𝒪_{Spec k}[a, b]))` is closed under finite direct sums, for `a ≤ b`. -/
theorem specFieldSums_isClosedUnderFiniteProducts {a b : ℤ} (hab : a ≤ b) :
    (specFieldSums k a b).IsClosedUnderFiniteProducts := by
  have := isClosedUnderBinaryProducts_retractClosure
    (⨆ p ∈ Set.Icc a b, (ObjectProperty.singleton
      ((DerivedCategory.singleFunctor (Spec (.of k)).Modules 0).obj
        (SheafOfModules.unit (Spec (.of k)).ringCatSheaf))).isoClosure.shift p
      ).binaryProductsClosure
  have : (specFieldSums k a b).ContainsZero := by
    obtain ⟨Y, hY, -⟩ := specFieldSums_singleFunctor (k := k) a b a ⟨le_rfl, hab⟩
    exact ⟨⟨0, isZero_zero _, Y, hY,
      ⟨{ i := 0, r := 0, retract := (isZero_zero _).eq_of_src _ _ }⟩⟩⟩
  exact IsClosedUnderFiniteProducts.mk'

/-- A coherent object concentrated in degree `d ∈ [a, b]` lies in `smd(add(𝒪_{Spec k}[a, b]))`. -/
private theorem specFieldSums_of_isGE_of_isLE_self (K : DerivedCategory (Spec (.of k)).Modules)
    {a b : ℤ} (d : ℤ) (hd : d ∈ Set.Icc a b) [K.IsGE d] [K.IsLE d]
    (hc : ((DerivedCategory.homologyFunctor (Spec (.of k)).Modules d).obj K).IsCoherent) :
    specFieldSums k a b K := by
  have hq := Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
    ((DerivedCategory.homologyFunctor (Spec (.of k)).Modules d).obj K)
  have := hq.1
  have := hq.2
  obtain ⟨m, ⟨e⟩⟩ := exists_iso_biproduct_singleFunctor_unit_of_isGE_of_isLE K d
  have := specFieldSums_isClosedUnderFiniteProducts (k := k) (a := a) (b := b) (hd.1.trans hd.2)
  exact (specFieldSums k a b).prop_of_iso e.symm
    (prop_of_isLimit_fan _ (biproduct.isLimit _) fun _ => specFieldSums_singleFunctor _ _ d hd)

/-- `Spec k` has dimension `0`. -/
theorem topologicalKrullDim_spec_field :
    topologicalKrullDim (Spec (.of k)) = ((0 : ℕ) : WithBot ℕ∞) := by
  rw [show topologicalKrullDim (Spec (.of k)) = topologicalKrullDim (PrimeSpectrum k) from rfl,
    PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_field]
  rfl

/-- **A bounded complex with coherent cohomology on `Spec k` is a finite sum of shifts of
`𝒪_{Spec k}`.** If the cohomology sheaves of `K ∈ D(𝒪_{Spec k})` are coherent and vanish outside
`[a, b]`, then `K ∈ smd(add(𝒪_{Spec k}[a, b]))`. -/
theorem specFieldSums_of_isGE_of_isLE (K : DerivedCategory (Spec (.of k)).Modules) (a b : ℤ)
    (hab : a ≤ b) [K.IsGE a] [K.IsLE b]
    (hcoh : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor (Spec (.of k)).Modules i).obj K).IsCoherent) :
    specFieldSums k a b K := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, b = a + n := ⟨(b - a).toNat, by omega⟩
  subst hn
  induction n generalizing K with
  | zero =>
    have : K.IsLE a := by simpa using ‹K.IsLE (a + ((0 : ℕ) : ℤ))›
    exact specFieldSums_of_isGE_of_isLE_self K a ⟨le_rfl, by omega⟩ (hcoh a)
  | succ n ih =>
    set b : ℤ := a + ((n + 1 : ℕ) : ℤ) with hb
    have : K.IsLE b := ‹_›
    have hreg : IsRegular (Spec (.of k)) := isRegular_of_smooth_over_field (𝟙 (Spec (.of k)))
    have hbdd : DerivedCategory.TStructure.t.bounded K := ⟨⟨a, ‹_›⟩, ⟨b, ‹_›⟩⟩
    obtain ⟨e⟩ : Nonempty (K ≅ (DerivedCategory.TStructure.t.truncLE (b - 1)).obj K ⊞
        (DerivedCategory.TStructure.t.truncGE b).obj K) := by
      have h := exists_iso_biprod_truncLE_truncGE (Spec (.of k)) hreg 0
        topologicalKrullDim_spec_field (forall_separatedCohomologyHomVanishing _ 0) K hbdd hcoh b
        (fun i h₁ h₂ => absurd h₂ (by omega))
      rw [show b + ((0 : ℕ) : ℤ) - 1 = b - 1 by omega, show b + ((0 : ℕ) : ℤ) = b by omega] at h
      exact h
    have := specFieldSums_isClosedUnderFiniteProducts (k := k) (a := a) (b := b) (by omega)
    have hbin : (specFieldSums k a b).IsClosedUnderBinaryProducts :=
      isClosedUnderBinaryProducts_retractClosure _
    refine (specFieldSums k a b).prop_of_iso e.symm
      ((specFieldSums k a b).prop_of_isLimit_binaryFan (BinaryBiproduct.isLimit _ _) ?_ ?_)
    · -- `τ_{≤ b-1}K` is in the window `[a, b - 1]`.
      have hle : ((DerivedCategory.TStructure.t.truncLE (b - 1)).obj K).IsLE
          (a + ((n : ℕ) : ℤ)) :=
        DerivedCategory.TStructure.t.isLE_of_le _ (b - 1) _ (by omega)
      refine specFieldSums_mono le_rfl (by omega) _ (ih _ ?_ (by omega))
      intro i
      by_cases hi : i ≤ b - 1
      · have := Stacks.TruncationLevel.isIso_homologyMap_truncLEι_app (b - 1) i hi K
        exact AlgebraicGeometry.isCoherent_of_moduleIso
          (asIso ((DerivedCategory.homologyFunctor _ i).map
            ((DerivedCategory.TStructure.t.truncLEι (b - 1)).app K))).symm (hcoh i)
      · have hz : IsZero ((DerivedCategory.homologyFunctor (Spec (.of k)).Modules i).obj
            ((DerivedCategory.TStructure.t.truncLE (b - 1)).obj K)) :=
          DerivedCategory.isZero_of_isLE _ (b - 1) i (by omega)
        exact ObjectProperty.prop_of_isZero
          (P := fun M : SheafOfModules (Spec (.of k)).ringCatSheaf => M.IsCoherent) hz
    · -- `τ_{≥ b}K` is concentrated in degree `b`.
      have hH : ∀ i, ((DerivedCategory.homologyFunctor (Spec (.of k)).Modules i).obj
          ((DerivedCategory.TStructure.t.truncGE b).obj K)).IsCoherent := by
        intro i
        by_cases hi : b ≤ i
        · have := DerivedCategory.isIso_homologyMap_truncGEπ_app b i hi K
          exact AlgebraicGeometry.isCoherent_of_moduleIso
            (asIso ((DerivedCategory.homologyFunctor _ i).map
              ((DerivedCategory.TStructure.t.truncGEπ b).app K))) (hcoh i)
        · have hz : IsZero ((DerivedCategory.homologyFunctor (Spec (.of k)).Modules i).obj
              ((DerivedCategory.TStructure.t.truncGE b).obj K)) :=
            DerivedCategory.isZero_of_isGE _ b i (by omega)
          exact ObjectProperty.prop_of_isZero
            (P := fun M : SheafOfModules (Spec (.of k)).ringCatSheaf => M.IsCoherent) hz
      have : ((DerivedCategory.TStructure.t.truncGE b).obj K).IsGE b :=
        DerivedCategory.TStructure.t.isGE_truncGE_obj K b b
      exact specFieldSums_of_isGE_of_isLE_self _ b ⟨by omega, le_rfl⟩ (hH b)

end AlgebraicGeometry

end
