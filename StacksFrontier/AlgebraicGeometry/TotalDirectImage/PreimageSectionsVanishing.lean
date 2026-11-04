module

public import StacksFrontier.AlgebraicGeometry.UniformVanishingDirectImage.Basic
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# A uniform degree bound for the sections functor on the preimages of a basis

Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes with `S` quasi-compact.
There is an integer `N`, depending only on `f`, and a basis `B` of the opens of `S`, such that the
higher right derived functors of `Γ(f⁻¹ V, -)` vanish from degree `N` onwards on every
quasi-coherent `𝒪_X`-module, for every `V ∈ B`.

## Main results

* `AlgebraicGeometry.exists_isBasis_isZero_rightDerivedPlus_sectionsOnPreimage`: the degree bound,
  with the `ℤ`-indexed `Functor.rightDerivedPlus`.

## References

* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 071L](https://stacks.math.columbia.edu/tag/071L)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

/-- For a quasi-compact and quasi-separated `f : X ⟶ S` with `S` quasi-compact there are an `N`
and a basis `B` of the opens of `S` such that `R ᵖ Γ(f⁻¹ V, -)` vanishes on every quasi-coherent
`𝒪_X`-module, for every `V ∈ B` and every `p ≥ N`. -/
theorem exists_isBasis_isZero_rightDerivedPlus_sectionsOnPreimage {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [CompactSpace S] :
    ∃ (N : ℕ) (B : Set S.Opens), Opens.IsBasis B ∧
      ∀ V ∈ B, ∀ M : X.Modules, M.IsQuasicoherent → ∀ p : ℤ, (N : ℤ) ≤ p →
        IsZero (((secF X.ringCatSheaf (f ⁻¹ᵁ V)).rightDerivedPlus p).obj M) := by
  obtain ⟨n, B, hB, hvan⟩ := exists_isBasis_isZero_cohomology_preimage f
  refine ⟨n, B, hB, fun V hV M hM p hp ↦ ?_⟩
  have : M.IsQuasicoherent := hM
  have : (secF X.ringCatSheaf (f ⁻¹ᵁ V)).Additive := secFAdditive X.ringCatSheaf (f ⁻¹ᵁ V)
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ p)
  exact (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff
    (secF X.ringCatSheaf (f ⁻¹ᵁ V)) hk M).2 (hvan V hV M k (by omega))

end AlgebraicGeometry

end
