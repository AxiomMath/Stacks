module

public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedDiagonalTFAE
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRelocalize
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemePointBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreProductComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.CategoryTheory.FiberedCategory.SliceAsElements

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An algebraic space is separated over `S` when the relative diagonal of the structure
morphism of an algebraic stack it represents is universally closed.** Let `𝓝` be an algebraic
stack over `S` represented by an algebraic space `N` (Stacks 02ZV). If the relative diagonal of
the structure morphism `𝓝 ⟶ S` of Stacks 050D is universally closed (Stacks 0513), then `N` is
separated over `S` (Stacks 02X5).

The structure morphism is representable by algebraic spaces, so Stacks 0512 reads the
hypothesis in the sense of Stacks 04XB, and Stacks 04YS makes the structure morphism separated in
that sense. Its representing morphism of presheaves is a morphism `N ⟶ h_S` to a terminal
presheaf; each of its base changes along a scheme-valued point of `h_S` is identified with the
lower-shriek extension of a presheaf representing the corresponding base change of the
structure morphism, so it is separated, and separatedness is tested on these base changes
(Stacks 03KM). Separatedness of `N ⟶ h_S` is separatedness of `N` over `S` (Stacks 04ZI). -/
theorem isSeparatedOver_of_universallyClosed_relativeDiagonal_of_equivalenceOver
    {𝓝 : AlgebraicStacks.{u, w} B S hS}
    {N : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hN : IsAlgebraicSpace B S hS N)
    (eF : StacksRepresentableCFG.EquivalenceOver 𝓝.val.val.p
      (presheafOfCategories (N ⋙ typeToCat)).p)
    (h : AlgebraicStacks.UniversallyClosed B S hS (relativeDiagonalAlgebraicStacks B S hS
      (structureMorphism B S hS 𝓝))) :
    Space.IsSeparatedOver B S hS N := by
  let p := structureMorphism B S hS 𝓝
  let X : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))
  have hrep : IsRepresentableByAlgebraicSpaces B S hS p.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS
      (schemeStack.{u, w} B S hS X).property
      ⟨N, hN, ⟨eF⟩⟩ p.hom
  have h04XB : UniversallyClosed B S hS (relativeDiagonal.{u, u, u + 1} B S hS 𝓝.val
      (schemeStack.{u, w} B S hS X).val p.hom) :=
    (representable_universallyClosed_iff_closedMap_baseChange B S hS
      (relativeDiagonalAlgebraicStacks B S hS p)
      (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS p)).2
      (fun 𝒵 g => h 𝒵 g)
  have hsep : IsSeparated B S hS p.hom :=
    ((isSeparated_relativeDiagonal_tfae B S hS p hrep).out 4 1).1 h04XB
  let G := yoneda.obj X
  let eG : StacksRepresentableCFG.EquivalenceOver (schemeStack.{u, w} B S hS X).val.val.p
      (presheafOfCategories (G ⋙ typeToCat)).p :=
    PresheafOfCategories.sliceElementsEquivalenceOver X
  let r := representingMap B S hS 𝓝.val (schemeStack.{u, w} B S hS X).val N G eF eG p.hom
  have hloc : (Space.separatedProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  have hr : Space.IsSeparated B S hS r :=
    (hasRelativeProperty_iff_prop_representingMap B S hS (Space.separatedProperty B S hS) p.hom
      hrep N G hN (isAlgebraicSpace_yoneda B S hS X) eF eG).1 hsep
  exact (Space.isSeparatedOver_iff_isSeparated_of_isTerminal B S hS
    (IsTerminal.isTerminalObj yoneda X Over.mkIdTerminal) r).2 hr

/-- **An algebraic space is separated over `S` when the relative diagonal of the structure
morphism of its algebraic stack is universally closed**: the case of
`AlgebraicGeometry.Stack.isSeparatedOver_of_universallyClosed_relativeDiagonal_of_equivalenceOver`
for the algebraic stack the space defines. -/
theorem isSeparatedOver_of_universallyClosed_relativeDiagonal
    {N : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hN : IsAlgebraicSpace B S hS N)
    (h : AlgebraicStacks.UniversallyClosed B S hS (relativeDiagonalAlgebraicStacks B S hS
      (structureMorphism B S hS (algebraicSpaceStack.{u, w} B S hS N hN)))) :
    Space.IsSeparatedOver B S hS N :=
  isSeparatedOver_of_universallyClosed_relativeDiagonal_of_equivalenceOver.{u, w} B S hS hN
    (StacksRepresentableCFG.EquivalenceOver.refl _) h

end AlgebraicGeometry.Stack

end
