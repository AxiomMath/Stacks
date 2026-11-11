module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjClosedSubspaceIdealQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.ShrinkComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.Space
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PsiDescended

/-!
# The ideal `ℐ ⊆ 𝒜` cut out by a closed subspace of `Proj_X(𝒜)` (Stacks 085L)

In Situation 0849 let `π : P = Proj_X(𝒜) ⟶ X` be the relative Proj of Stacks 084C and
`X = U/R` a presentation of its base.  The twists `𝒪_P(d)` of Stacks 084D are the descended twists
`AlgebraicGeometry.Space.RelativeProjSituation.twistModule`, and the homogeneous-section maps
`𝒜_d ⟶ π_*𝒪_P(d)` are the adjoints of `ψ_d : π^*𝒜_d ⟶ 𝒪_P(d)`
(`AlgebraicGeometry.Space.RelativeProjSituation.psiTwistHom`).  For a closed subspace `i : Z ⟶ P`,
the graded ideal `ℐ ⊆ 𝒜` of Stacks 085L is, in degree `d`, the kernel of
`𝒜_d ⟶ π_*𝒪_P(d) ⟶ π_*((i_*𝒪_Z)(d))`
(`AlgebraicGeometry.Space.closedSubspaceGradedIdeal` at these twists); it is quasi-coherent when
`π` is quasi-compact.

## Main definitions

* `AlgebraicGeometry.Space.C1359Bridge.psiTwistSections`: the twists `𝒪_P(d)` and the
  homogeneous-section maps `𝒜_d ⟶ π_*𝒪_P(d)` adjoint to `ψ_d`.
* `AlgebraicGeometry.Space.C1359Bridge.psiClosedSubspaceIdeal`: the degree-`d` piece of `ℐ`.

## References

* [Stacks Project, Tag 085L](https://stacks.math.columbia.edu/tag/085L)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space.C1359Bridge

variable (s : RelativeProjSituation.{u, u})
  (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)

/-- **The homogeneous-section map `𝒜_d ⟶ π_*𝒪_P(d)` of Stacks 084D**: the identification of `𝒜_d`
with its re-presented copy followed by the adjoint, along `π^* ⊣ π_*`, of
`ψ_d : π^*𝒜_d ⟶ 𝒪_P(d)` (`AlgebraicGeometry.Space.RelativeProjSituation.psiTwistHom`). -/
def psiSectionMap (d : ℕ) :
    s.algebra.piece (d : ℤ) ⟶ (modulePushforward s.site s.base s.containsBase s.π).obj
      (s.twistModule Px (d : ℤ)).obj :=
  (s.smallAlgebraPieceIso (d : ℤ)).inv ≫
    ((modulePullbackAdjunction s.site s.base s.containsBase s.relativeProjSpaceHom).homEquiv _ _)
      (s.psiTwistHom Px d)

/-- **The twists `𝒪_P(d)` of Stacks 084D and their homogeneous-section maps**, as consumed by the
canonical map of Stacks 085L. -/
def psiTwistSections : ClosedSubspaceTwistSections s s.Proj s.π where
  twist d := (s.twistModule Px (d : ℤ)).obj
  isQuasicoherent d := s.isQuasicoherentOnSite_twistModule Px (d : ℤ)
  sectionMap d := psiSectionMap s Px d

variable {Z : AlgebraicSpaces s.site s.base s.containsBase} (i : Z ⟶ s.Proj)

/-- **The graded ideal `ℐ ⊆ 𝒜` of Stacks 085L cut out by a closed subspace `i : Z ⟶ Proj_X(𝒜)`**,
in degree `d`: the kernel of the canonical map `𝒜_d ⟶ π_*𝒪_P(d) ⟶ π_*((i_*𝒪_Z)(d))`. -/
abbrev psiClosedSubspaceIdeal (d : ℕ) : (s.algebra.piece (d : ℤ)).Submodule :=
  closedSubspaceGradedIdeal (psiTwistSections s Px) i d

/-- A local section of `𝒜_d` lies in `ℐ_d` exactly when the canonical map kills it. -/
theorem mem_psiClosedSubspaceIdeal (d : ℕ)
    (U : (SmallEtale s.site s.base s.containsBase s.space.1)ᵒᵖ)
    (x : (s.algebra.piece (d : ℤ)).val.obj U) :
    x ∈ (psiClosedSubspaceIdeal s Px i d).obj U ↔
      (closedSubspaceSectionMap (psiTwistSections s Px) i d).val.app U x = 0 :=
  mem_closedSubspaceGradedIdeal _ i d U x

/-- The direct images `π_*((i_*𝒪_Z)(d))` are quasi-coherent for `π` quasi-compact and `i` a
closed immersion: `π` is separated (Stacks 084E), `(i_*𝒪_Z)(d)` is quasi-coherent, and Stacks 03M9
applies to the quasi-compact quasi-separated `π`. -/
theorem isQuasicoherentOnSite_psiTwistedStructureDirectImage
    (hπ : IsQuasiCompact s.site s.base s.containsBase s.π.hom)
    (hi : IsClosedImmersion s.site s.base s.containsBase i.hom) (d : ℕ) :
    (twistedStructureDirectImage (psiTwistSections s Px) i d).IsQuasicoherentOnSite := by
  have : (closedSubspacePushforwardStructure i).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_structureSheafPushforward s.site s.base s.containsBase i hi
  exact isQuasicoherentOnSite_modulePushforward_of_qcqs s.site s.base s.containsBase s.π hπ
    (isQuasiSeparated_of_isSeparated s.site s.base s.containsBase s.isSeparated_relativeProjπ)
    _ (isQuasicoherentOnSite_tensorObj s.site s.base s.containsBase s.Proj.1 s.Proj.2 _ _)

/-- **`ℐ` is quasi-coherent** (Stacks 085L): for `π` quasi-compact and `i` a closed immersion,
every homogeneous piece `ℐ_d` is a quasi-coherent `𝒪_X`-module. -/
theorem isQuasicoherentOnSite_psiClosedSubspaceIdeal
    (hπ : IsQuasiCompact s.site s.base s.containsBase s.π.hom)
    (hi : IsClosedImmersion s.site s.base s.containsBase i.hom) (d : ℕ) :
    (psiClosedSubspaceIdeal s Px i d).toSheafOfModules.IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((Stacks.SheafOfModules.isLimitKernelForkKerSubmodule
        (closedSubspaceSectionMap (psiTwistSections s Px) i d)).conePointUniqueUpToIso
      (kernelIsKernel (closedSubspaceSectionMap (psiTwistSections s Px) i d))).symm
    (isQuasicoherentOnSite_closedSubspaceGradedIdealObj (psiTwistSections s Px) i hπ hi d)

end AlgebraicGeometry.Space.C1359Bridge

end
