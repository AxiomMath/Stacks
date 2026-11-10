module

public import StacksFrontier.AlgebraicGeometry.Perfect.AcyclicDirectImageBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatDegreeZeroDirectImage
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.DirectImage

/-!
# The direct image of `𝒬(m)` for a family in `Quot^P` commutes with base change

Let `n ≥ 0`, `r ≥ 1`, `P ∈ ℚ[t]`, `m = AlgebraicGeometry.ProjectiveQuot.regularityIndex n r P`,
and let `K ∈ Quot^P_{𝒪^{⊕ r}/ℙⁿ/ℤ}(T)` with quotient `𝒬` and `π : ℙⁿ_T ⟶ T`. Then

* `π_*(𝒬(m))` is finite locally free of rank `P(m)`;
* `𝒬(m)` has no cohomology in positive degrees over the inverse image of an affine open of `T`;
* for every cartesian square over a morphism `T' ⟶ T` the base-change morphism
  `h^* π_*(𝒬(m)) ⟶ π'_*(h'^* 𝒬(m))` is an isomorphism.

This is the cohomology and base change step in the proof of Stacks 0DPA: it makes `π_*(𝒬(m))`
a quotient of rank `P(m)` whose formation commutes with base change, the point of the
Grassmannian attached to `K`.

## Main results

* `AlgebraicGeometry.ProjectiveQuot.isFiniteLocallyFreeOfRank_pushforward_twist_quotient`.
* `AlgebraicGeometry.ProjectiveQuot.subsingleton_rightDerived_twist_quotient`.
* `AlgebraicGeometry.ProjectiveQuot.isIso_baseChangeNatTrans_twist_quotient`.

## References

* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
* [Stacks Project, Tag 0B9X](https://stacks.math.columbia.edu/tag/0B9X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProjectiveQuot

variable {n r : ℕ} {P : Polynomial ℚ}

/-- `𝒬(m)` is of finite presentation and quasi-coherent for `K ∈ Quot^P(T)`. -/
private theorem isFinitePresentation_and_isQuasicoherent_twist_quotient {T : Scheme.{u}}
    {K : Subobject (freeModule n r T)} (hK : K ∈ hilbertFamilies n r P T) :
    (twist (regularityIndex.{u} n r P : ℤ) (quotient K)).IsFinitePresentation ∧
      (twist (regularityIndex.{u} n r P : ℤ) (quotient K)).IsQuasicoherent :=
  have := isFinitePresentation_twist _ _ hK.1.1
  ⟨this, Stacks.Modules.isQuasicoherent_of_isFinitePresentation _⟩

/-- **`π_*(𝒬(m))` is finite locally free of rank `P(m)`** for `K ∈ Quot^P(T)`. -/
theorem isFiniteLocallyFreeOfRank_pushforward_twist_quotient {T : Scheme.{u}}
    {K : Subobject (freeModule n r T)} (hK : K ∈ hilbertFamilies n r P T) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pushforward (projectiveSpaceOver n T ↘ T)).obj
        (twist (regularityIndex.{u} n r P : ℤ) (quotient K)))
      ⌊P.eval ((regularityIndex.{u} n r P : ℕ) : ℚ)⌋₊ := by
  obtain ⟨M, hM, ⟨e⟩⟩ := hasDerivedPushforwardRank_twist_quotient hK (𝟙 T)
    (projectiveSpaceOver n T ↘ T) (𝟙 _) IsPullback.of_id_fst
  exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    (((Scheme.Modules.pushforward (projectiveSpaceOver n T ↘ T)).mapIso
      ((Scheme.Modules.pullbackId _).app _)).symm ≪≫
      ProperFlatFibreEulerCharacteristic.pushforwardIsoOfIsoSingle e).symm hM

/-- **`𝒬(m)` has no higher cohomology over the inverse image of an affine open of `T`.** -/
theorem subsingleton_rightDerived_twist_quotient {T : Scheme.{u}}
    {K : Subobject (freeModule n r T)} (hK : K ∈ hilbertFamilies n r P T) (V : T.Opens)
    (hV : IsAffineOpen V) (i : ℕ) (hi : 0 < i) :
    Subsingleton (((moduleGlobalSections ((projectiveSpaceOver n T ↘ T) ⁻¹ᵁ V)).rightDerived i).obj
      ((Scheme.Modules.pullback ((projectiveSpaceOver n T ↘ T) ⁻¹ᵁ V).ι).obj
        (twist (regularityIndex.{u} n r P : ℤ) (quotient K)))) := by
  have hpb : IsPullback ((projectiveSpaceOver n T ↘ T) ⁻¹ᵁ V).ι
      ((projectiveSpaceOver n T ↘ T) ∣_ V) (projectiveSpaceOver n T ↘ T) V.ι :=
    (isPullback_morphismRestrict _ V).flip
  obtain ⟨M, -, ⟨e⟩⟩ := hasDerivedPushforwardRank_twist_quotient hK V.ι _ _ hpb
  have : IsAffine V.toScheme := hV
  have := isProper_projectiveSpaceOver n T
  have : IsProper ((projectiveSpaceOver n T ↘ T) ∣_ V) :=
    MorphismProperty.of_isPullback hpb inferInstance
  obtain ⟨_, _⟩ := isFinitePresentation_and_isQuasicoherent_twist_quotient hK
  have := Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback
    ((projectiveSpaceOver n T ↘ T) ⁻¹ᵁ V).ι
    (twist (regularityIndex.{u} n r P : ℤ) (quotient K))
  exact ProperFlatFibreEulerCharacteristic.subsingleton_rightDerived_of_iso_single e i hi

/-- **Cohomology and base change for `Quot^P`.** For `K ∈ Quot^P(T)`,
`m = regularityIndex n r P` and a cartesian square over any `h : T' ⟶ T`, the base-change
morphism `h^* π_*(𝒬(m)) ⟶ π'_*(h'^* 𝒬(m))` is an isomorphism. -/
theorem isIso_baseChangeNatTrans_twist_quotient {T : Scheme.{u}}
    {K : Subobject (freeModule n r T)} (hK : K ∈ hilbertFamilies n r P T)
    {Y' T' : Scheme.{u}} (h : T' ⟶ T) (π' : Y' ⟶ T') (h' : Y' ⟶ projectiveSpaceOver n T)
    (hsq : IsPullback h' π' (projectiveSpaceOver n T ↘ T) h) :
    IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans hsq.w).app
      (twist (regularityIndex.{u} n r P : ℤ) (quotient K))) := by
  have := isProper_projectiveSpaceOver n T
  obtain ⟨_, _⟩ := isFinitePresentation_and_isQuasicoherent_twist_quotient hK
  exact Stacks.AlgebraicGeometry.AcyclicDirectImageBaseChange.isIso_baseChangeNatTrans_of_acyclic
    hsq _ (isFlatOver_twist _ _ _ hK.1.2)
    (fun V hV i hi => subsingleton_rightDerived_twist_quotient hK V hV i hi)

end AlgebraicGeometry.ProjectiveQuot

end
