module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalGysinRule
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.SectionGeneratesGlobalSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorGlobalSectionGermUnit

/-!
# A global section generates `ℒ_ξ` at every prime divisor outside its zero scheme

In Situation 0EDT let `X/B` be good and integral, let `ℒ` be an invertible `𝒪_X`-module and let
`σ ∈ Γ(X, ℒ)` be a global section, with zero scheme `Z(σ)` (Stacks 0845).  This file proves
that for a prime divisor `Z` not contained in `Z(σ)`, `σ` generates `ℒ_ξ` at the generic point `ξ`
of `Z`, that is `AlgebraicGeometry.Space.PrimeDivisor.SectionGenerates` holds for the meromorphic
section of `σ`; this is the condition behind Section 0EQU's choice "`s_i = s` whenever
`Z_i ⊄ Z(σ)`".

The hypothesis is stated in two equivalent forms: `|Z(σ)|` is closed and `|Z|` is the closure of
`ξ`, so `ξ` lies on `Z(σ)` exactly when `Z ⊆ Z(σ)`.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.ambientGenericPoint_toIntegralClosedSubspace`: the
  generic point of a prime divisor is the ambient generic point of the integral closed subspace
  it is.
* `PrimeDivisor.sectionGenerates_globalSectionMeromorphic_of_notMem_zeroScheme`: `σ` generates
  `ℒ_ξ` when `ξ ∉ |Z(σ)|`.
* `AlgebraicGeometry.Space.PrimeDivisor.sectionGenerates_globalSectionMeromorphic_of_not_le`:
  the same in the form `Z ⊄ Z(σ)` in which Section 0EQU phrases the choice.

## References

* [Stacks Project, Section 0EQU](https://stacks.math.columbia.edu/tag/0EQU)
* [Stacks Project, Tag 0845](https://stacks.math.columbia.edu/tag/0845)
* [Stacks Project, Tag 0ER9](https://stacks.math.columbia.edu/tag/0ER9)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (Z : PrimeDivisor D.site D.base D.base_mem X)
    (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (B := D.site) ⟨X, hX.1⟩ L)

include hX hint in
/-- The generic point of a prime divisor is the ambient generic point of the integral closed
subspace it is. -/
theorem PrimeDivisor.ambientGenericPoint_toIntegralClosedSubspace :
    (Z.toIntegralClosedSubspace D.site D.base D.base_mem).ambientGenericPoint
        D.site D.base D.base_mem =
      Z.genericPoint D.site D.base D.base_mem X := by
  have : T0Space (points D.site D.base D.base_mem X) :=
    t0Space_points_of_isDecentSpace D.site D.base D.base_mem hX.1 hint.2.1
  exact ((Z.toIntegralClosedSubspace D.site D.base D.base_mem).isGenericPoint_ambientGenericPoint
    D.site D.base D.base_mem hX.1).eq (Z.isGenericPoint_genericPoint D.site D.base D.base_mem X)

include hint in
/-- A global section generates `ℒ_ξ` at every prime divisor whose generic point `ξ` misses the
zero scheme. -/
theorem PrimeDivisor.sectionGenerates_globalSectionMeromorphic_of_notMem_zeroScheme
    (σ : L.sections)
    (h : Z.genericPoint D.site D.base D.base_mem X ∉
      subspacePointSet D.site D.base D.base_mem X
        (zeroScheme D.site D.base D.base_mem ⟨X, hX.1⟩ L σ).1) :
    Z.SectionGenerates D sX hX hint L hL
      (globalSectionMeromorphic D.site D.base D.base_mem hX.1 L σ) :=
  Z.sectionGenerates_globalSectionMeromorphic_of_isUnit D sX hX hint L hL σ
    (Z.isUnit_globalSectionGerm_of_notMem_zeroScheme D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX) L hL σ h)

include hint in
/-- For a prime divisor `Z` with generic point `ξ` and `Z ⊄ Z(σ)`, the global section `σ`
generates `ℒ_ξ`. -/
theorem PrimeDivisor.sectionGenerates_globalSectionMeromorphic_of_not_le (σ : L.sections)
    (h : ¬ Z.subspace ≤ (zeroScheme D.site D.base D.base_mem ⟨X, hX.1⟩ L σ).1) :
    Z.SectionGenerates D sX hX hint L hL
      (globalSectionMeromorphic D.site D.base D.base_mem hX.1 L σ) :=
  Z.sectionGenerates_globalSectionMeromorphic_of_notMem_zeroScheme D sX hX hint L hL σ
    (Z.ambientGenericPoint_toIntegralClosedSubspace D sX hX hint ▸
      notMem_subspacePointSet_ambientGenericPoint_of_not_le D hX.1
        (zeroScheme D.site D.base D.base_mem ⟨X, hX.1⟩ L σ).1
        (zeroScheme D.site D.base D.base_mem ⟨X, hX.1⟩ L σ).2
        (Z.toIntegralClosedSubspace D.site D.base D.base_mem) h)

end AlgebraicGeometry.Space

end
