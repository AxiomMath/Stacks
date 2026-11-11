module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureSheafCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesTensorQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjChartSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjClosedSubspaceIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants

/-!
# The graded ideal of a closed subspace of a relative Proj is quasi-coherent

Let `S` be a scheme, `X` an algebraic space over `S` and `𝒜` a quasi-coherent graded
`𝒪_X`-algebra, let `π : P ⟶ X` be the relative Proj of `𝒜` and let `i : Z ⟶ P` be a closed
subspace.  Stacks 085L forms the graded ideal `ℐ ⊆ 𝒜` as the kernel of the canonical map
`𝒜 ⟶ ⨁_{d ≥ 0} π_*((i_*𝒪_Z)(d))`, written degree by degree in
`StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjClosedSubspaceIdeal` as
`AlgebraicGeometry.Space.closedSubspaceGradedIdeal`, and the third step of its proof reads:
"as `π` is quasi-compact, `π_*` transforms quasi-coherent modules into quasi-coherent modules
(Stacks 03M9), hence `ℐ` is a quasi-coherent `𝒪_X`-module".

That file proves the quasi-coherence of `ℐ_d` at the twists of Stacks 084D on `Proj_X(𝒜)`.  This
file proves it for any datum of quasi-coherent twists on a morphism `π : P ⟶ X` presented on an
étale chart by the restriction of `𝒜`, for `π` quasi-compact and `i` a closed immersion.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_twistedStructureDirectImage`: for `π`
  quasi-compact, presented on an étale chart by the restriction of `𝒜`, and `i` a closed
  immersion, every direct image `π_*((i_*𝒪_Z)(d))` is quasi-coherent.  The steps are those of the
  source: `π` is separated (Stacks 084E), hence quasi-separated (Stacks 03KK); `i_*𝒪_Z` is
  quasi-coherent (the closed-immersion case of Stacks 03M9); the twist `(i_*𝒪_Z)(d)` is the
  tensor product with the quasi-coherent `𝒪_P(d)` (Stacks 03M1(5)); and `π_*` of a quasi-coherent
  module along a quasi-compact quasi-separated morphism is quasi-coherent (Stacks 03M9).
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_closedSubspaceGradedIdealObj_of_isQuasiCompact`:
  **`ℐ_d` is quasi-coherent**, with no input beyond the hypotheses above.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_closedSubspaceGradedIdeal`: the same for the
  submodule `ℐ_d ⊆ 𝒜_d` itself, whose sections are the sections of `𝒜_d` killed by the canonical
  map.
* `AlgebraicGeometry.Space.isQuasicoherent_restrictToChartScheme_closedSubspaceGradedIdeal`: the
  restriction of `ℐ_d` to the scheme of any étale chart of `X` is quasi-coherent.

## Implementation notes

The twists `𝒪_P(d)` and the homogeneous section maps are the datum
`AlgebraicGeometry.Space.ClosedSubspaceTwistSections` of the file defining `ℐ`; the results below
are statements about the ideal that datum defines, and they use of it only the quasi-coherence of
its twists, which is one of its fields.  No `stacks` attribute is attached here.

## References

* [Stacks Project, Tag 085L](https://stacks.math.columbia.edu/tag/085L)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 084E](https://stacks.math.columbia.edu/tag/084E)
* [Stacks Project, Tag 03KK](https://stacks.math.columbia.edu/tag/03KK)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

section Ideal

variable {s : RelativeProjSituation.{u, u}}
    {P : AlgebraicSpaces s.site s.base s.containsBase} {π : P ⟶ s.space}
    {Z : AlgebraicSpaces s.site s.base s.containsBase}

/-- **The direct images `π_*((i_*𝒪_Z)(d))` are quasi-coherent.**  Let `π : P ⟶ X` be
quasi-compact and presented on an étale chart by the restriction of `𝒜`, and let `i : Z ⟶ P` be a
closed immersion.  Then for every `d` the direct image along `π` of the twist `(i_*𝒪_Z)(d)` is a
quasi-coherent `𝒪_X`-module.

`π` is separated by Stacks 084E, `AlgebraicGeometry.Space.isSeparated_relativeProj_of_chart`,
hence quasi-separated; `i_*𝒪_Z` is quasi-coherent because `i` is a closed immersion; its tensor
product with the quasi-coherent twist `𝒪_P(d)` is quasi-coherent; and the direct image along the
quasi-compact quasi-separated `π` is quasi-coherent by Stacks 03M9,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_qcqs`. -/
theorem isQuasicoherentOnSite_twistedStructureDirectImage
    (c : RelativeProjSituationChart s π.hom)
    (hπ : IsQuasiCompact s.site s.base s.containsBase π.hom)
    (T : ClosedSubspaceTwistSections s P π) (i : Z ⟶ P)
    (hi : IsClosedImmersion s.site s.base s.containsBase i.hom) (d : ℕ) :
    (twistedStructureDirectImage T i d).IsQuasicoherentOnSite := by
  have : (closedSubspacePushforwardStructure i).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_structureSheafPushforward s.site s.base s.containsBase i hi
  exact isQuasicoherentOnSite_modulePushforward_of_qcqs s.site s.base s.containsBase π hπ
    (isQuasiSeparated_of_isSeparated s.site s.base s.containsBase
      (isSeparated_relativeProj_of_chart s P.2 π.hom c))
    _ (isQuasicoherentOnSite_tensorObj s.site s.base s.containsBase P.1 P.2 _ _)

/-- **Stacks 085L, the quasi-coherence of `ℐ`, on the source's hypotheses.**  For `π : P ⟶ X`
quasi-compact, presented on an étale chart by the restriction of `𝒜`, and `i : Z ⟶ P` a closed
immersion, the degree-`d` piece of the graded ideal cut out by `Z` is a quasi-coherent
`𝒪_X`-module.

The direct images are quasi-coherent by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_twistedStructureDirectImage`, and the kernel of a
map of quasi-coherent modules is quasi-coherent (Stacks 03M1(3),
`AlgebraicGeometry.Space.isClosedUnderKernels_quasicoherentSheaves_smallEtale`). -/
theorem isQuasicoherentOnSite_closedSubspaceGradedIdealObj_of_isQuasiCompact
    (c : RelativeProjSituationChart s π.hom)
    (hπ : IsQuasiCompact s.site s.base s.containsBase π.hom)
    (T : ClosedSubspaceTwistSections s P π) (i : Z ⟶ P)
    (hi : IsClosedImmersion s.site s.base s.containsBase i.hom) (d : ℕ) :
    (closedSubspaceGradedIdealObj T i d).IsQuasicoherentOnSite :=
  let : CategoryTheory.ObjectProperty.IsClosedUnderKernels
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (structureRingSheaf s.site s.base s.containsBase s.space)) :=
    AlgebraicGeometry.Space.isClosedUnderKernels_quasicoherentSheaves_smallEtale
      s.site s.base s.containsBase s.space.1 s.space.2
  CategoryTheory.ObjectProperty.prop_kernel _ (closedSubspaceSectionMap T i d)
    (s.isQuasicoherent (d : ℤ)) (isQuasicoherentOnSite_twistedStructureDirectImage c hπ T i hi d)

/-- **The submodule `ℐ_d ⊆ 𝒜_d` is quasi-coherent**, on the same hypotheses: the sectionwise
kernel of the canonical map is a kernel (`Stacks.SheafOfModules.isLimitKernelForkKerSubmodule`),
hence isomorphic to the categorical kernel, which is quasi-coherent by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_closedSubspaceGradedIdealObj_of_isQuasiCompact`. -/
theorem isQuasicoherentOnSite_closedSubspaceGradedIdeal
    (c : RelativeProjSituationChart s π.hom)
    (hπ : IsQuasiCompact s.site s.base s.containsBase π.hom)
    (T : ClosedSubspaceTwistSections s P π) (i : Z ⟶ P)
    (hi : IsClosedImmersion s.site s.base s.containsBase i.hom) (d : ℕ) :
    (closedSubspaceGradedIdeal T i d).toSheafOfModules.IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((Stacks.SheafOfModules.isLimitKernelForkKerSubmodule
        (closedSubspaceSectionMap T i d)).conePointUniqueUpToIso
      (kernelIsKernel (closedSubspaceSectionMap T i d))).symm
    (isQuasicoherentOnSite_closedSubspaceGradedIdealObj_of_isQuasiCompact c hπ T i hi d)

/-- **The chart restriction of `ℐ_d` is quasi-coherent.**  On the same hypotheses, the module
restriction of `ℐ_d` to the scheme of any étale chart `V` of `X` is a quasi-coherent module on
that scheme, by the étale-to-Zariski direction of Stacks 03DX,
`AlgebraicGeometry.Space.isQuasicoherent_restrictToChartScheme`. -/
theorem isQuasicoherent_restrictToChartScheme_closedSubspaceGradedIdeal
    (c : RelativeProjSituationChart s π.hom)
    (hπ : IsQuasiCompact s.site s.base s.containsBase π.hom)
    (T : ClosedSubspaceTwistSections s P π) (i : Z ⟶ P)
    (hi : IsClosedImmersion s.site s.base s.containsBase i.hom) (d : ℕ)
    (V : SmallEtale s.site s.base s.containsBase s.space.1) :
    (restrictToChartScheme s.site s.base s.containsBase s.space.1 s.space.2
      (closedSubspaceGradedIdeal T i d).toSheafOfModules V).IsQuasicoherent :=
  isQuasicoherent_restrictToChartScheme s.site s.base s.containsBase s.space _
    (isQuasicoherentOnSite_closedSubspaceGradedIdeal c hπ T i hi d) V

end Ideal

end AlgebraicGeometry.Space

end
