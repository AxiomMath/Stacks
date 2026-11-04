module

public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionRightAdjointSheafHomLocallySmall
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCompactGeneration
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModule

/-!
# The twisted inverse image of a closed immersion applied to the structure sheaf

For a pseudo-coherent closed immersion `i : Z ⟶ X` of schemes with `X` quasi-compact and
quasi-separated, the right adjoint `c` of `Ri_* : D_QCoh(𝒪_Z) ⥤ D_QCoh(𝒪_X)` satisfies
`c(𝒪_X) ≅ R𝓗om_{𝒪_X}(𝒪_Z, 𝒪_X)` in `D(𝒪_Z)` ([Stacks, Tag 0A9X] at the structure sheaf).
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Duality.KoszulRegular

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [CompactSpace X]
  [QuasiSeparatedSpace X]

/-- The canonical proof that `Ri_*` preserves quasi-coherent cohomology. -/
abbrev hpushClosedImmersion :=
  Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs i

/-- `Ri_*` restricted to `D_QCoh` has a right adjoint ([Stacks, Tag 0A9E]); the source is
quasi-compact and quasi-separated, being closed in `X`. -/
instance isLeftAdjoint_quasiCoherentDerivedPushforward_closedImmersion :
    (quasiCoherentDerivedPushforward i (hpushClosedImmersion i)).IsLeftAdjoint := by
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace i
  have : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated i
  infer_instance

/-- A module placed in degree zero is cohomologically bounded below. -/
theorem isBoundedBelow_singleFunctor_obj {Y : Scheme.{u}} (M : Y.Modules) :
    DerivedCategoryB.IsBoundedBelow ((DerivedCategory.singleFunctor Y.Modules 0).obj M) :=
  ⟨0, fun n hn => DerivedCategory.isZero_of_isGE (C := Y.Modules)
    ((DerivedCategory.singleFunctor Y.Modules 0).obj M) 0 n hn⟩

/-- `c(𝒪_X) ≅ R𝓗om_{𝒪_X}(𝒪_Z, 𝒪_X)` for a pseudo-coherent closed immersion. -/
def twistedInverseImageStructureSheafIso (hpc : PseudoCoherent i) :
    ((twistedInverseImage i (hpushClosedImmersion i)).obj
        (DerivedPushforward.derivedStructureSheaf X)).obj ≅
      (LocallySmall.derivedSheafHomExactSupport i).obj
        (DerivedPushforward.derivedStructureSheaf X).obj :=
  haveI := LocallySmall.isIso_rightAdjointToDerivedSheafHom_app i (hpushClosedImmersion i)
    (twistedInverseImage i (hpushClosedImmersion i))
    (twistedInverseImageAdjunction i (hpushClosedImmersion i)) hpc
    ⟨DerivedPushforward.derivedStructureSheaf X, isBoundedBelow_singleFunctor_obj _⟩
  asIso ((LocallySmall.rightAdjointToDerivedSheafHom i (hpushClosedImmersion i)
    (twistedInverseImage i (hpushClosedImmersion i))
    (twistedInverseImageAdjunction i (hpushClosedImmersion i))).app
      (DerivedPushforward.derivedStructureSheaf X))

end Stacks.Duality.KoszulRegular
