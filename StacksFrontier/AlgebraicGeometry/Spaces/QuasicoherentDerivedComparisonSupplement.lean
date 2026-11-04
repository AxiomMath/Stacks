module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.CokernelAffineSurjectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedCategory
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentFiniteProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentGrothendieck
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentKernelsOnSite
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentKernelsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.ShortExactQuasicoherent
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
import StacksCore.Tactic.StacksAttribute
import all StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedComparison
public import StacksFrontier.AlgebraicGeometry.Size.CoveringsSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.Topology.Dimension.KrullSupplement

/-!
# The triangulated subcategory `D_QCoh(𝒪_F)` of an algebraic space

For an algebraic space `F`, the quasi-coherent `𝒪_F`-modules on its small étale site form a weak
Serre subcategory of all `𝒪_F`-modules, and the complexes with quasi-coherent cohomology form a
strictly full saturated triangulated subcategory `D_QCoh(𝒪_F)` of `D(𝒪_F)` (Stacks 06UQ).

## Main results

* `AlgebraicGeometry.Space.isWeakSerre_quasicoherentSheaves`: if quasi-coherent `𝒪_F`-modules
  are closed under kernels, cokernels and extensions, then in an exact sequence of five
  `𝒪_F`-modules whose four outer terms are quasi-coherent, the middle term is quasi-coherent.
* `AlgebraicGeometry.Space.isTriangulated_quasicoherentDerivedCategory_of_qcohKernels`: under the
  same hypotheses, `D_QCoh(𝒪_F)` is a triangulated subcategory of `D(𝒪_F)`.
* `AlgebraicGeometry.Space.isWeakSerreClass_quasicoherentSheaves_of_h03DW`: at the universe of
  the schemes, quasi-coherence is a weak Serre class given the uniform form of Stacks 03DW.
* `AlgebraicGeometry.Space.quasicoherentDerivedCategory_isTriangulated_saturated_of_h03DW`: at the
  universe of the schemes, `D_QCoh(𝒪_F)` is a strictly full saturated triangulated subcategory of
  `D(𝒪_F)` given the uniform form of Stacks 03DW.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u m

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    [HasSheafify (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{m}]
    [(smallEtaleRingedSite B S hS F hF).J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [(SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderKernels]
    [(SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderCokernels]

section WeakSerre

variable [(SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderExtensions]

/-- The five term formulation of `AlgebraicGeometry.Space.quasicoherentSheaves_isWeakSerreClass`:
in an exact sequence of five `𝒪_F`-modules whose four outer terms are quasi-coherent, the middle
term is quasi-coherent. -/
theorem isWeakSerre_quasicoherentSheaves :
    WeakSerre.IsWeakSerre
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))) := by
  refine ⟨inferInstance, ObjectProperty.exists_prop_of_isWeakSerreClass _,
    fun E h₀ h₁ h₃ h₄ => ?_⟩
  exact ObjectProperty.prop_mid_of_exact₄ (ObjectProperty.prop_obj₂_of_exact _)
    E.zero₀ E.zero₁ E.zero₂ E.exact₁ E.exact₂ E.exact₃ h₀ h₁ h₃ h₄

/-- **`D_QCoh(𝒪_F)` is a triangulated subcategory of `D(𝒪_F)`**, by Stacks 06UQ applied to the
weak Serre subcategory of quasi-coherent `𝒪_F`-modules. -/
instance isTriangulated_quasicoherentDerivedCategory_of_qcohKernels :
    (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O)))).IsTriangulated :=
  DerivedCategoryB.derivedCategoryB_isTriangulated _
    (isWeakSerre_quasicoherentSheaves B S hS F hF)

/-- `D_QCoh(𝒪_F)` is strictly full: the complexes with quasi-coherent cohomology are closed under
isomorphism in `D(𝒪_F)`. -/
instance isClosedUnderIsomorphisms_quasicoherentDerivedCategory :
    (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O)))).IsClosedUnderIsomorphisms :=
  DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms _
    (isWeakSerre_quasicoherentSheaves B S hS F hF)

/-- `D_QCoh(𝒪_F)` is saturated: a retract in `D(𝒪_F)` of a complex with quasi-coherent cohomology
again has quasi-coherent cohomology. -/
instance isStableUnderRetracts_quasicoherentDerivedCategory :
    (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O)))).IsStableUnderRetracts :=
  DerivedCategoryB.derivedCategoryB_isStableUnderRetracts _
    (isWeakSerre_quasicoherentSheaves B S hS F hF)

end WeakSerre

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

open Opposite

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **Stacks 03M1 as a weak Serre class at the universe of the schemes, on the uniform form of
Stacks 03DW alone.**  Quasi-coherence of `𝒪_F`-modules on the small étale site of an algebraic
space is a weak Serre class in the sense of Stacks 0754, with no hypothesis beyond `h03DW`. -/
theorem isWeakSerreClass_quasicoherentSheaves_of_h03DW
    (h03DW : ∀ {P Q : Modules.{u, u} B S hS F hF} (q : P ⟶ Q), Epi q →
      IsCartesianOnAffineCharts (kernel q) → ∀ W : SmallEtale B S hS F,
        IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
          Function.Surjective (q.val.app (op W))) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).IsWeakSerreClass :=
  let := isClosedUnderKernels_quasicoherentSheaves_schemeUniverse B S hS F hF
  let := isClosedUnderCokernels_quasicoherentSheaves B S hS F hF
  let := isClosedUnderExtensions_quasicoherentSheaves_of_h03DW B S hS F hF h03DW
  quasicoherentSheaves_isWeakSerreClass B S hS F hF

/-- **`D_QCoh(𝒪_F)` is a strictly full saturated triangulated subcategory of `D(𝒪_F)` at the
universe of the schemes, on the uniform form of Stacks 03DW alone.**  This is Stacks 06UQ applied
to `AlgebraicGeometry.Space.isWeakSerreClass_quasicoherentSheaves_of_h03DW`. -/
theorem quasicoherentDerivedCategory_isTriangulated_saturated_of_h03DW
    (h03DW : ∀ {P Q : Modules.{u, u} B S hS F hF} (q : P ⟶ Q), Epi q →
      IsCartesianOnAffineCharts (kernel q) → ∀ W : SmallEtale B S hS F,
        IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
          Function.Surjective (q.val.app (op W))) :
    (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS F hF).O)))).IsClosedUnderIsomorphisms ∧
      (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS F hF).O)))).IsTriangulated ∧
      (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS F hF).O)))).IsStableUnderRetracts :=
  let := isClosedUnderKernels_quasicoherentSheaves_schemeUniverse B S hS F hF
  let := isClosedUnderCokernels_quasicoherentSheaves B S hS F hF
  let := isClosedUnderExtensions_quasicoherentSheaves_of_h03DW B S hS F hF h03DW
  DerivedCategoryB.derivedCategoryB_isTriangulated_saturated _
    (isWeakSerre_quasicoherentSheaves B S hS F hF)

end AlgebraicGeometry.Space

end

