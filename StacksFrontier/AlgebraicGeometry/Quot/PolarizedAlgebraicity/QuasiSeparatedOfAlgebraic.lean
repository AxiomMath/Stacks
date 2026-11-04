module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesQuasiSeparatedFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedAlgebraicity.IsomSpaceAffine
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedLimitPreservingProof
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingFinitePresentationEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingOfFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStructureMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingTwoFibreProductObjects
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalIsomSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAxioms

/-!
# `𝒫olarized → Spec(ℤ)` is quasi-separated and locally of finite presentation, given algebraicity

Quasi-separatedness (Stacks 04YW) and local finite presentation (Stacks 06Q2) are properties of
1-morphisms of *algebraic* stacks, so they are stated here at
`AlgebraicGeometry.PolarizedAlgebraicity.polarizedAlgebraicStackOf B hS hT h`, the stack
`AlgebraicGeometry.polarizedStackUnconditional` of polarized proper schemes over a terminal base of
the site packaged as an algebraic stack from a proof `h` that it is one. The unconditional
statement, Stacks 0DPU, supplies `h` (Quot, Theorem 0D4X) and lives in
`StacksFrontier.AlgebraicGeometry.Quot.PolarizedQuasiSeparatedLocallyFinitePresentation`.

## Local finite presentation

The source's proof: by Stacks 0CMY it suffices that `𝒫olarized` is limit preserving, which is
Stacks 0D43, `AlgebraicGeometry.isLimitPreservingPolarizedUnconditional`. Limit preservation makes
the structure functor of `𝒫olarized` to the site limit preserving on objects, hence also the
structure morphism of Stacks 050D, whose target, the algebraic stack of the base itself, is limit
preserving by Stacks 0CMX. Stacks 0CMY (2) ⟹ (3) concludes.

## Quasi-separatedness

Quasi-separatedness asks that the diagonal `Δ` be quasi-compact and quasi-separated in the sense
of Properties of Stacks, Section 04XB. The source deduces this from Stacks 0DPT. Here both are read
off the isomorphism spaces: the base change of `Δ` along a scheme-valued point `(υ, χ, α)` over
`U` is `Isom_𝒫(υ, χ) ⟶ U`
(`AlgebraicGeometry.Stack.prop_algebraicSpaceMap_relativeDiagonal_iff_isomSpace`), which is
represented by a scheme affine over `U`
(`AlgebraicGeometry.PolarizedAlgebraicity.exists_iso_yoneda_isAffineHom_polarizedIsomSpace`), hence
is quasi-compact and separated, so quasi-separated.

## References

* [Stacks Project, Tag 0DPU](https://stacks.math.columbia.edu/tag/0DPU)
* [Stacks Project, Tag 0DPT](https://stacks.math.columbia.edu/tag/0DPT)
* [Stacks Project, Tag 0D43](https://stacks.math.columbia.edu/tag/0D43)
* [Stacks Project, Tag 0CMY](https://stacks.math.columbia.edu/tag/0CMY)
* [Stacks Project, Tag 0CMX](https://stacks.math.columbia.edu/tag/0CMX)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.PolarizedAlgebraicity

universe u w

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S) (hT : IsTerminal (B.obj hS))

/-- **`𝒫olarized` as an algebraic stack, from a proof that it is one.** The stack of polarized
proper schemes over a terminal base of the site, as an object of the 2-category of algebraic
stacks. -/
abbrev polarizedAlgebraicStackOf
    (h : Stack.IsAlgebraicStack.{u, w} B S hS (polarizedStackUnconditional B hS hT).val) :
    Stack.AlgebraicStacks.{u, w} B S hS :=
  ⟨polarizedStackUnconditional B hS hT, h⟩

/-- **Local finite presentation of `𝒫olarized → Spec(ℤ)`, given algebraicity.** By Stacks 0CMY
it suffices that `𝒫olarized` is limit preserving, which is Stacks 0D43. -/
theorem isLocallyOfFinitePresentation_structureMorphism_polarizedAlgebraicStackOf
    (h : Stack.IsAlgebraicStack.{u, w} B S hS (polarizedStackUnconditional B hS hT).val) :
    Stack.AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
      (Stack.structureMorphism B S hS (polarizedAlgebraicStackOf B hS hT h)) := by
  have hP := Stack.isLimitPreservingOnObjects_toTerminalCFG_of_isLimitPreserving B S hS
    (polarizedStackUnconditional B hS hT) (isLimitPreservingPolarizedUnconditional B hS hT)
  exact Stack.AlgebraicStacks.isLocallyOfFinitePresentation_of_isLimitPreservingOnObjects
    B S hS _
    (Stack.isLimitPreservingOnObjects_of_toTerminalCFG B S hS
      (polarizedStackUnconditional B hS hT) _
      (Stack.structureMorphism B S hS (polarizedAlgebraicStackOf B hS hT h)).hom hP
      (Stack.isLimitPreserving_schemeStack_id.{u, w} B S hS))

/-- **The diagonal of `𝒫olarized` is quasi-compact, given algebraicity.** Every base change of
`Δ` along a scheme-valued point over `U` is an isomorphism space `Isom_𝒫(υ, χ) ⟶ U`, which is
quasi-compact. -/
theorem isQuasiCompact_relativeDiagonal_polarizedAlgebraicStackOf
    (h : Stack.IsAlgebraicStack.{u, w} B S hS (polarizedStackUnconditional B hS hT).val) :
    Stack.IsQuasiCompact B S hS
      (Stack.relativeDiagonal.{u, u, u + 1} B S hS (polarizedAlgebraicStackOf B hS hT h).val
        (Stack.schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
        (Stack.structureMorphism B S hS (polarizedAlgebraicStackOf B hS hT h)).hom) := by
  intro U y hy F hF hE
  have : MorphismProperty.RespectsIso (@Space.IsQuasiCompact B S hS) :=
    MorphismProperty.RespectsIso.of_respects_arrow_iso _ (fun f g e hf =>
      Space.isQuasiCompact_of_arrowIso B S hS f.hom g.hom e.hom.left e.hom.right
        e.hom.w hf)
  exact (Stack.prop_algebraicSpaceMap_relativeDiagonal_iff_isomSpace B S hS
    (@Space.IsQuasiCompact B S hS)
    (Stack.structureMorphism B S hS (polarizedAlgebraicStackOf B hS hT h))
    (Stack.faithful_schemeStack_p.{u, w} B S hS) U y hy F hF hE).2
    (isQuasiCompact_relocalizeToYoneda_polarizedIsomSpace B hS hT _ _ _)

/-- **The diagonal of `𝒫olarized` is quasi-separated, given algebraicity.** Every base change of
`Δ` along a scheme-valued point over `U` is an isomorphism space `Isom_𝒫(υ, χ) ⟶ U`, which is
separated, hence quasi-separated. -/
theorem isQuasiSeparated_relativeDiagonal_polarizedAlgebraicStackOf
    (h : Stack.IsAlgebraicStack.{u, w} B S hS (polarizedStackUnconditional B hS hT).val) :
    Stack.IsQuasiSeparated B S hS
      (Stack.relativeDiagonal.{u, u, u + 1} B S hS (polarizedAlgebraicStackOf B hS hT h).val
        (Stack.schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
        (Stack.structureMorphism B S hS (polarizedAlgebraicStackOf B hS hT h)).hom) := by
  intro U y hy F hF hE
  have := Space.isSeparated_respectsIso B S hS
  exact Space.isQuasiSeparated_of_isSeparated B S hS
    ((Stack.prop_algebraicSpaceMap_relativeDiagonal_iff_isomSpace B S hS
      (@Space.IsSeparated B S hS)
      (Stack.structureMorphism B S hS (polarizedAlgebraicStackOf B hS hT h))
      (Stack.faithful_schemeStack_p.{u, w} B S hS) U y hy F hF hE).2
      (isSeparated_relocalizeToYoneda_polarizedIsomSpace B hS hT _ _ _))

/-- **`𝒫olarized → Spec(ℤ)` is quasi-separated and locally of finite presentation, given
algebraicity.** The statement of Stacks 0DPU at `polarizedAlgebraicStackOf B hS hT h`. -/
theorem isQuasiSeparated_and_isLocallyOfFinitePresentation_polarizedAlgebraicStackOf
    (h : Stack.IsAlgebraicStack.{u, w} B S hS (polarizedStackUnconditional B hS hT).val) :
    Stack.AlgebraicStacks.IsQuasiSeparated B S hS
        (Stack.structureMorphism B S hS (polarizedAlgebraicStackOf B hS hT h)) ∧
      Stack.AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
        (Stack.structureMorphism B S hS (polarizedAlgebraicStackOf B hS hT h)) :=
  ⟨⟨isQuasiCompact_relativeDiagonal_polarizedAlgebraicStackOf B hS hT h,
      isQuasiSeparated_relativeDiagonal_polarizedAlgebraicStackOf B hS hT h⟩,
    isLocallyOfFinitePresentation_structureMorphism_polarizedAlgebraicStackOf B hS hT h⟩

end AlgebraicGeometry.PolarizedAlgebraicity

end
