module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae

/-!
# Permanence of the separation axioms

The three separation axioms — separatedness, local separatedness and quasi-separatedness of a
morphism of algebraic spaces — are stable under composition, and each of them propagates
between a space and the morphisms out of it in both directions: from the target of a morphism
to its source, and between the absolute form of the axiom and its form relative to the base
scheme.

## Main results

* `AlgebraicGeometry.Space.isQuasiSeparated_comp`: a composite of quasi-separated morphisms is
  quasi-separated; the other two axioms are `AlgebraicGeometry.Space.isSeparated_comp` and
  `AlgebraicGeometry.Space.isLocallySeparated_comp`.
* `AlgebraicGeometry.Space.isAbsolutelySeparated_of_isSeparated`,
  `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated`,
  `AlgebraicGeometry.Space.isAbsolutelyLocallySeparated_of_isLocallySeparated`,
  `AlgebraicGeometry.Space.isSeparatedOver_of_isSeparated`,
  `AlgebraicGeometry.Space.isQuasiSeparatedOver_of_isQuasiSeparated` and
  `AlgebraicGeometry.Space.isLocallySeparatedOver_of_isLocallySeparated`: a separation axiom
  passes from the target of a morphism with that axiom to its source.
* `AlgebraicGeometry.Space.isSeparatedOver_of_isAbsolutelySeparated`,
  `AlgebraicGeometry.Space.isLocallySeparatedOver_of_isAbsolutelyLocallySeparated` and
  `AlgebraicGeometry.Space.isQuasiSeparatedOver_of_isAbsolutelyQuasiSeparated`: an algebraic
  space with an absolute separation axiom has it over the base scheme.
* `AlgebraicGeometry.Space.isQuasiSeparated_of_isQuasiSeparatedOver`,
  `AlgebraicGeometry.Space.isSeparated_of_isSeparatedOver` and
  `AlgebraicGeometry.Space.isLocallySeparated_of_isLocallySeparatedOver`: every morphism out of
  a space with a separation axiom over the base scheme has that axiom.

## Implementation notes

Quasi-separatedness of a morphism is quasi-compactness of its relative diagonal tested on
morphisms from quasi-compact algebraic spaces. The arguments for it run on the represented
reading `Stacks.SeparationLocal.DiagonalProp` and are transported back by
`AlgebraicGeometry.Space.isQuasiSeparated_iff_diagonalProp_quasiCompact`, which needs the
relative diagonal to be representable (`Stacks.SeparationLocal.relativelyRepresentable_diagonal`);
this is why the quasi-separated statements, and only they, carry algebraicity hypotheses.

An algebraic space has a separation axiom over `S` exactly when its morphism to a terminal
presheaf has it (`AlgebraicGeometry.Space.isSeparatedOver_iff_isSeparated_of_isTerminal` and its
companions). The absolute axioms are the axioms over the terminal scheme, formed through
`AlgebraicGeometry.Space.viewOverIntegers`, and are compared with the axioms over `S` by
relocalization along `S ⟶ Spec ℤ` (`AlgebraicGeometry.Space.isSeparated_relocalize` and its
companions).

Every statement which does not need algebraicity is given for an arbitrary morphism of
presheaves on the big fppf site of `S`.

## References

* [Stacks Project, Tag 03KQ](https://stacks.math.columbia.edu/tag/03KQ)
* [Stacks Project, Tag 04ZH](https://stacks.math.columbia.edu/tag/04ZH)
* [Stacks Project, Tag 04ZI](https://stacks.math.columbia.edu/tag/04ZI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.SeparationLocal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### Composition -/

/-- The relative diagonal of a morphism `f : F ⟶ G` of algebraic spaces over `S` which is
quasi-separated is quasi-compact after every represented base change. -/
private theorem diagonalProp_quasiCompact_of_isAlgebraicSpace_of_isQuasiSeparated
    (hF : IsAlgebraicSpace B S hS F) {f : F ⟶ G} (hf : IsQuasiSeparated B S hS f) :
    DiagonalProp B S hS (@AlgebraicGeometry.QuasiCompact.{u}) f :=
  diagonalProp_quasiCompact_of_isQuasiSeparated B S hS
    (relativelyRepresentable_diagonal B S hS hF f) hf

/-- The composite of two quasi-separated morphisms of algebraic spaces over `S` is
quasi-separated. -/
@[stacks 03KQ "quasi-separated"]
theorem isQuasiSeparated_comp (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (p : F ⟶ G) (q : G ⟶ H) (hp : IsQuasiSeparated B S hS p)
    (hq : IsQuasiSeparated B S hS q) : IsQuasiSeparated B S hS (p ≫ q) :=
  isQuasiSeparated_of_diagonalProp_quasiCompact B S hS
    (diagonalProp_quasiCompact_comp B S hS p q
      (diagonalProp_quasiCompact_of_isAlgebraicSpace_of_isQuasiSeparated B S hS hF hp)
      (diagonalProp_quasiCompact_of_isAlgebraicSpace_of_isQuasiSeparated B S hS hG hq))

/-- Quasi-separatedness, as a morphism property of algebraic spaces over `S`, is stable under
composition. -/
instance isQuasiSeparated_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition
      (fun ⦃F' G' : AlgebraicSpaces B S hS⦄ (f : F' ⟶ G') => IsQuasiSeparated B S hS f.hom) where
  comp_mem := fun {X' Y' _Z'} k l hk hl =>
    isQuasiSeparated_comp B S hS X'.property Y'.property k.hom l.hom hk hl

/-! ### The separation axioms of the source of a morphism -/

/-- If `G` is separated over `S` and `f : F ⟶ G` is separated,
then `F` is separated over `S`. -/
@[stacks 04ZH "part (4)"]
theorem isSeparatedOver_of_isSeparated {f : F ⟶ G} (hG : IsSeparatedOver B S hS G)
    (hf : IsSeparated B S hS f) : IsSeparatedOver B S hS F := by
  refine (isSeparatedOver_iff_isSeparated_of_isTerminal B S hS terminalIsTerminal
    (terminal.from F)).2 ?_
  rw [← terminal.comp_from f]
  exact isSeparated_comp B S hS f (terminal.from G) hf
    ((isSeparatedOver_iff_isSeparated_of_isTerminal B S hS terminalIsTerminal
      (terminal.from G)).1 hG)

/-- If `G` is locally separated over `S` and `f : F ⟶ G` is
locally separated, then `F` is locally separated over `S`. -/
@[stacks 04ZH "part (6)"]
theorem isLocallySeparatedOver_of_isLocallySeparated {f : F ⟶ G}
    (hG : IsLocallySeparatedOver B S hS G) (hf : IsLocallySeparated B S hS f) :
    IsLocallySeparatedOver B S hS F := by
  refine (isLocallySeparatedOver_iff_isLocallySeparated_of_isTerminal B S hS terminalIsTerminal
    (terminal.from F)).2 ?_
  rw [← terminal.comp_from f]
  exact isLocallySeparated_comp B S hS f (terminal.from G) hf
    ((isLocallySeparatedOver_iff_isLocallySeparated_of_isTerminal B S hS terminalIsTerminal
      (terminal.from G)).1 hG)

/-- If `G` is quasi-separated over `S` and the relative diagonal of `f : F ⟶ G` is
quasi-compact after every represented base change, then `F` is quasi-separated over `S`. -/
private theorem isQuasiSeparatedOver_of_diagonalProp_quasiCompact {f : F ⟶ G}
    (hG : IsQuasiSeparatedOver B S hS G)
    (hf : DiagonalProp B S hS (@AlgebraicGeometry.QuasiCompact.{u}) f) :
    IsQuasiSeparatedOver B S hS F := by
  refine (isQuasiSeparatedOver_iff_diagonalProp_quasiCompact_of_isTerminal B S hS
    terminalIsTerminal (terminal.from F)).2 ?_
  rw [← terminal.comp_from f]
  exact diagonalProp_quasiCompact_comp B S hS f (terminal.from G) hf
    ((isQuasiSeparatedOver_iff_diagonalProp_quasiCompact_of_isTerminal B S hS terminalIsTerminal
      (terminal.from G)).1 hG)

/-- If `G` is quasi-separated over `S` and `f : F ⟶ G` is quasi-separated, then `F` is
quasi-separated over `S`. -/
@[stacks 04ZH "part (5)"]
theorem isQuasiSeparatedOver_of_isQuasiSeparated (hF : IsAlgebraicSpace B S hS F) {f : F ⟶ G}
    (hG : IsQuasiSeparatedOver B S hS G) (hf : IsQuasiSeparated B S hS f) :
    IsQuasiSeparatedOver B S hS F :=
  isQuasiSeparatedOver_of_diagonalProp_quasiCompact B S hS hG
    (diagonalProp_quasiCompact_of_isAlgebraicSpace_of_isQuasiSeparated B S hS hF hf)

/-! ### Comparison of the absolute axioms with the axioms over the base -/

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- If `G` is separated and `f : F ⟶ G` is separated, then `F` is separated. -/
@[stacks 04ZH "part (1)"]
theorem isAbsolutelySeparated_of_isSeparated {f : F ⟶ G}
    (hG : IsAbsolutelySeparated B S hS hZ G) (hf : IsSeparated B S hS f) :
    IsAbsolutelySeparated B S hS hZ F :=
  isSeparatedOver_of_isSeparated B (⊤_ Scheme.{u}) hZ hG
    (isSeparated_relocalize B S hS hZ (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ) hf)

/-- If `G` is locally separated and `f : F ⟶ G` is locally
separated, then `F` is locally separated. -/
@[stacks 04ZH "part (3)"]
theorem isAbsolutelyLocallySeparated_of_isLocallySeparated {f : F ⟶ G}
    (hG : IsAbsolutelyLocallySeparated B S hS hZ G) (hf : IsLocallySeparated B S hS f) :
    IsAbsolutelyLocallySeparated B S hS hZ F :=
  isLocallySeparatedOver_of_isLocallySeparated B (⊤_ Scheme.{u}) hZ hG
    (isLocallySeparated_relocalize B S hS hZ (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ) hf)

/-- If `G` is quasi-separated and `f : F ⟶ G` is quasi-separated, then `F` is
quasi-separated. -/
@[stacks 04ZH "part (2)"]
theorem isAbsolutelyQuasiSeparated_of_isQuasiSeparated (hF : IsAlgebraicSpace B S hS F)
    {f : F ⟶ G} (hG : IsAbsolutelyQuasiSeparated B S hS hZ G)
    (hf : IsQuasiSeparated B S hS f) : IsAbsolutelyQuasiSeparated B S hS hZ F :=
  isQuasiSeparatedOver_of_diagonalProp_quasiCompact B (⊤_ Scheme.{u}) hZ hG
    (diagonalProp_quasiCompact_relocalize B S hS hZ
      (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ)
      (diagonalProp_quasiCompact_of_isAlgebraicSpace_of_isQuasiSeparated B S hS hF hf))

/-- A separated algebraic space over `S` is separated over `S`, that is, an algebraic space
which is separated over the terminal scheme is separated over its own base scheme. -/
@[stacks 04ZI "part (1)"]
theorem isSeparatedOver_of_isAbsolutelySeparated (hF : IsAlgebraicSpace B S hS F)
    (h : IsAbsolutelySeparated B S hS hZ F) : IsSeparatedOver B S hS F :=
  (isSeparatedOver_iff_isSeparated_of_isTerminal B S hS terminalIsTerminal
      (terminal.from F)).2 <|
    isSeparated_of_relocalize B S hS hZ (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ)
      (relativelyRepresentable_diagonal B S hS hF (terminal.from F))
      (isSeparated_of_isSeparatedOver B (⊤_ Scheme.{u}) hZ h _)

/-- A locally separated algebraic space is locally separated over
its base scheme. -/
@[stacks 04ZI "part (2)"]
theorem isLocallySeparatedOver_of_isAbsolutelyLocallySeparated (hF : IsAlgebraicSpace B S hS F)
    (h : IsAbsolutelyLocallySeparated B S hS hZ F) : IsLocallySeparatedOver B S hS F :=
  (isLocallySeparatedOver_iff_isLocallySeparated_of_isTerminal B S hS terminalIsTerminal
      (terminal.from F)).2 <|
    isLocallySeparated_of_relocalize B S hS hZ (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ)
      (relativelyRepresentable_diagonal B S hS hF (terminal.from F))
      (isLocallySeparated_of_isLocallySeparatedOver B (⊤_ Scheme.{u}) hZ h _)

/-- A quasi-separated algebraic space is quasi-separated over its
base scheme. -/
@[stacks 04ZI "part (3)"]
theorem isQuasiSeparatedOver_of_isAbsolutelyQuasiSeparated (hF : IsAlgebraicSpace B S hS F)
    (h : IsAbsolutelyQuasiSeparated B S hS hZ F) : IsQuasiSeparatedOver B S hS F :=
  (isQuasiSeparatedOver_iff_diagonalProp_quasiCompact_of_isTerminal B S hS terminalIsTerminal
      (terminal.from F)).2 <|
    diagonalProp_quasiCompact_of_relocalize B S hS hZ
      (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ)
      (relativelyRepresentable_diagonal B S hS hF (terminal.from F))
      (diagonalProp_quasiCompact_of_isQuasiSeparatedOver B (⊤_ Scheme.{u}) hZ h _)

/-- Every morphism out of an algebraic space which is quasi-separated over `S` is
quasi-separated. -/
@[stacks 04ZI "part (6)"]
theorem isQuasiSeparated_of_isQuasiSeparatedOver (hF : IsQuasiSeparatedOver B S hS F)
    (p : F ⟶ G) : IsQuasiSeparated B S hS p :=
  isQuasiSeparated_of_diagonalProp_quasiCompact B S hS
    (diagonalProp_quasiCompact_of_isQuasiSeparatedOver B S hS hF p)

end AlgebraicGeometry.Space

end
