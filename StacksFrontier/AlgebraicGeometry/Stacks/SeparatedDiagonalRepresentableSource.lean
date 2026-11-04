module

public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationCancellation
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationFibreProductProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionGroupoidStabilizerDimension

/-!
# A separated diagonal passes to the source of a representable 1-morphism

Let `ι : 𝒳' ⟶ 𝒳` be a 1-morphism of algebraic stacks over `S` which is representable by algebraic
spaces. If the diagonal `Δ_{𝒳/S}` is separated (in the sense of Stacks 04XB), so is
`Δ_{𝒳'/S}`: the structure morphism of `𝒳'` is `ι` followed by that of `𝒳`, the relative diagonal
of a composite is `Δ_ι` followed by the comparison 1-morphism of Stacks 050H, `Δ_ι` is separated
by Stacks 04YQ part (4), the comparison is separated by Stacks 050H part (3), and separatedness
composes (Stacks 045B).

## Main results

* `isSeparated_relativeDiagonal_structureMorphism_of_isRepresentable`: if `Δ_{𝒳/S}` is
  separated and `ι : 𝒳' ⟶ 𝒳` is representable by algebraic spaces, then `Δ_{𝒳'/S}` is
  separated.
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A separated diagonal over `S` passes to the source of a 1-morphism representable by
algebraic spaces.** -/
theorem isSeparated_relativeDiagonal_structureMorphism_of_isRepresentable
    {𝒳' 𝒳 : AlgebraicStacks.{u, w} B S hS} (ι : 𝒳' ⟶ 𝒳)
    (hι : IsRepresentableByAlgebraicSpaces B S hS ι.hom.hom)
    (hΔ : Stack.IsSeparated.{u, u, u + 1} B S hS
      (_root_.AlgebraicGeometry.Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val
        (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
        (structureMorphism B S hS 𝒳).hom)) :
    Stack.IsSeparated.{u, u, u + 1} B S hS
      (_root_.AlgebraicGeometry.Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒳'.val
        (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
        (structureMorphism B S hS 𝒳').hom) := by
  have : (Space.separatedProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) :=
    (Space.separated_isLocalAtTarget_fpqc.{u, u + 1} B S hS).of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u + 1} B S hS)
  set σ := structureMorphism B S hS 𝒳 with hσdef
  have hσ : structureMorphism B S hS 𝒳' = ι ≫ σ := (comp_structureMorphism B S hS ι).symm
  have hfac : _root_.AlgebraicGeometry.Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒳'.val
        (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val (ι ≫ σ).hom =
      (relativeDiagonal B S hS ι).hom ≫ (mapBase B S hS ι ι σ).hom := by
    rw [← Bicategory.InducedBicategory.bicategory_comp_hom]
    exact congrArg (fun q => q.hom) (relativeDiagonal_comp B S hS ι σ)
  rw [hσ, hfac]
  obtain ⟨hrep₁, hsep₁⟩ :=
    Stack.isSeparated_relativeDiagonal_of_isRepresentableByAlgebraicSpaces B S hS ι hι
  exact hasRelativeProperty_comp.{u, u, u + 1, u + 1} B S hS (Space.separatedProperty B S hS)
    (relativeDiagonal B S hS ι).hom (mapBase B S hS ι ι σ).hom hrep₁
    (isRepresentableByAlgebraicSpaces_mapBase B S hS ι ι σ) hsep₁
    (isSeparated_mapBase B S hS ι ι σ hΔ)

end AlgebraicGeometry.Stack.AlgebraicStacks

end
