module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentFinitePresentationColimitAffineOverNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectsColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitProjectionAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ClosedSubspaceApproximationFromSubmodules
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleOverIntegers

/-!
# Quasi-coherent modules on a qcqs algebraic space, from Noetherian approximation

This file carries out the source's proofs of Stacks 07V9 and of the colimit assertion of
Stacks 0829 over one input, absolute Noetherian approximation for algebraic spaces over `Spec ℤ`
(Stacks 07SU), which is not proved in this development.  That input is the hypothesis `h07SU`;
nothing here carries a `stacks` attribute.

* `AlgebraicGeometry.Space.exists_isColimit_isFinitePresentation_of_noetherianApproximation`:
  the source's proof of Stacks 07V9.  View `X` over `Spec ℤ`; by `h07SU` it is the limit of an
  inverse system of quasi-separated algebraic spaces of finite type over `Spec ℤ` with affine
  transition morphisms; a stage `X_i` is Noetherian, the projection `X ⟶ X_i` is affine (Stacks
  07SF, part (1), with no condition on the index), and Stacks 07UW applies to it.  The module
  categories of `X` over `S` and over `Spec ℤ` agree, quasi-coherence and finite presentation
  included.
* The theorem that `AlgebraicGeometry.Space.finiteTypeQuasicoherentSubobjectCocone` is a colimit
  cocone over a filtered category: the source's proof of Stacks 0829 from the above: the finite
  type quasi-coherent submodules of a quasi-coherent module form a directed system, and their
  colimit is the module.
* `AlgebraicGeometry.Space.hasClosedSubspaceApproximation_of_noetherianApproximation`: the
  source's proof of Stacks 0A0U from the above: a closed subspace of a quasi-compact and
  quasi-separated algebraic space is the directed limit of closed subspaces of finite
  presentation, cut out by the finite type quasi-coherent subideals of its ideal sheaf.

## The input `h07SU`

`h07SU` is the content of Stacks 07SU over the base `Spec ℤ` itself, i.e. at the base
`⊤_ Scheme` of the site: every quasi-compact and quasi-separated algebraic space `Z` over
`Spec ℤ` has a `AlgebraicGeometry.Space.NoetherianApproximation` — a directed set, an inverse
system of algebraic spaces over `Spec ℤ` with affine transition morphisms whose stages are
quasi-separated and of finite type over `Spec ℤ`, and `Z` as its limit.  No condition on the size
of the index set is asked; such a condition would make the hypothesis false (for `Z = Spec R`
with `R` a ring of cardinality at least the cofinality of the site's cutoff).  Nor is the
statement read over an arbitrary base `S`: over the spectrum of an uncountable field no
nonempty algebraic space has a system of stages of finite type over `Spec ℤ` lying over that
base.

## References

* [Stacks Project, Tag 07V9](https://stacks.math.columbia.edu/tag/07V9)
* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
* [Stacks Project, Tag 0A0U](https://stacks.math.columbia.edu/tag/0A0U)
* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 07UW](https://stacks.math.columbia.edu/tag/07UW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **The source's proof of Stacks 07V9, over absolute Noetherian approximation.**  Let `X` be a
quasi-compact and quasi-separated algebraic space over `S`.  Granted Stacks 07SU over `Spec ℤ`
(`h07SU`), every quasi-coherent `𝒪_X`-module is a filtered colimit, over a small filtered index
category, of `𝒪_X`-modules of finite presentation. -/
theorem exists_isColimit_isFinitePresentation_of_noetherianApproximation
    (h07SU : ∀ Z : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ Z → IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ Z →
        IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ Z →
          HasNoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ Z)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hqc : IsQuasiCompactSpace B S hS X) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (F : Modules.{u, u} B S hS X hX) (hF : F.IsQuasicoherentOnSite) :
    ∃ (K : Type u) (inst : SmallCategory K),
      let _ := inst
      ∃ (_ : IsFiltered K) (D : K ⥤ Modules.{u, u} B S hS X hX)
        (φ : D ⟶ (Functor.const K).obj F),
        (∀ k, (D.obj k).IsFinitePresentation) ∧ Nonempty (IsColimit (Cocone.mk F φ)) := by
  have hX' : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (viewOverIntegers B S hS hZ X) :=
    isAlgebraicSpace_viewOver B S (⊤_ Scheme.{u}) hS hZ (integersMap B S hS hZ) X hX
  have hqc' : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ (viewOverIntegers B S hS hZ X) :=
    isQuasiCompactSpace_relocalize B S hS hZ (integersMap B S hS hZ) hqc
  obtain ⟨A⟩ := h07SU _ hX' hqc' (isAbsolutelyQuasiSeparated_viewOverIntegers B S hS hZ X hqs)
  let := A.preorder
  obtain ⟨i⟩ : Nonempty A.I := A.nonempty
  let j : (A.I)ᵒᵖ := Opposite.op i
  have hπ : IsAffineHom B (⊤_ Scheme.{u}) hZ (A.π.app j) :=
    NoetherianApproximation.isAffineHom_π B (⊤_ Scheme.{u}) hZ A hX' j
  have hN : IsNoetherian B (⊤_ Scheme.{u}) hZ hZ (A.diagram.obj j) :=
    isNoetherian_of_isFiniteType_viewOverIntegers B (⊤_ Scheme.{u}) hZ hZ _
      (A.isAlgebraicSpace j) (A.isAbsolutelyQuasiSeparated j) (A.isFiniteTypeOverIntegers j)
  exact exists_isFilteredColimit_isFinitePresentation_of_viewOverIntegers B S hS hZ X hX
    (fun F' hF' => exists_isColimit_isFinitePresentation_of_isAffineHom B (⊤_ Scheme.{u}) hZ hZ
      (X := ⟨viewOverIntegers B S hS hZ X, hX'⟩) (Y := ⟨A.diagram.obj j, A.isAlgebraicSpace j⟩)
      (ObjectProperty.homMk (A.π.app j)) hπ hN F' hF') F hF

/-- **The source's proof of Stacks 0829, over absolute Noetherian approximation.**  Let `X` be a
quasi-compact and quasi-separated algebraic space over `S` and `G` a quasi-coherent
`𝒪_X`-module.  Granted Stacks 07SU over `Spec ℤ` (`h07SU`), `G` is the directed colimit of its
finite type quasi-coherent submodules: those submodules form a directed system, and the cocone
of their inclusions into `G` is a colimit cocone.

Directedness needs no hypothesis
(`AlgebraicGeometry.Space.isFiltered_finiteTypeQuasicoherentSubobject`); the colimit assertion
takes the images of a presentation of `G` by modules of finite presentation, which is the source's
proof of Stacks 07V9 above. -/
theorem isFiltered_and_nonempty_isColimit_finiteTypeQuasicoherentSubobjectCocone_of_approximation
    (h07SU : ∀ Z : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ Z → IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ Z →
        IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ Z →
          HasNoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ Z)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hqc : IsQuasiCompactSpace B S hS X) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (G : Modules.{u, u} B S hS X hX) [G.IsQuasicoherentOnSite] :
    IsFiltered (FiniteTypeQuasicoherentSubobject B S hS X hX G) ∧
      Nonempty (IsColimit (finiteTypeQuasicoherentSubobjectCocone B S hS X hX G)) := by
  refine ⟨isFiltered_finiteTypeQuasicoherentSubobject B S hS X hX G, ?_⟩
  obtain ⟨K, inst, -, D, φ, hfp, ⟨hcol⟩⟩ :=
    exists_isColimit_isFinitePresentation_of_noetherianApproximation B S hS hZ h07SU hX hqc hqs
      G ‹_›
  let _ := inst
  exact nonempty_isColimit_finiteTypeQuasicoherentSubobjectCocone_of_isFinitePresentation
    B S hS X hX G D φ hfp hcol

/-- **The source's proof of Stacks 0A0U, over absolute Noetherian approximation.**  Let `Y` be a
quasi-compact and quasi-separated algebraic space over `S` and `X ⊆ Y` a closed subspace.  Granted
Stacks 07SU over `Spec ℤ` (`h07SU`), `X` is the directed inverse limit of closed subspaces
`X_i ⊆ Y` of finite presentation over `Y`: the conclusion
`AlgebraicGeometry.Space.HasClosedSubspaceApproximation`, whose transition morphisms and
projections are closed immersions by
`AlgebraicGeometry.Space.isClosedImmersion_closedSubspaceDiagram_map` and
`AlgebraicGeometry.Space.isClosedImmersion_closedSubspaceCone_π`.

The ideal sheaf of `X` is the colimit of its finite type quasi-coherent submodules by Stacks 0829
(above), and
`hasClosedSubspaceApproximation_of_isColimit_finiteTypeQuasicoherentSubobjectCocone` is the rest
of the source's argument. -/
theorem hasClosedSubspaceApproximation_of_noetherianApproximation
    (h07SU : ∀ Z : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ Z → IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ Z →
        IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ Z →
          HasNoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ Z)
    (Y : AlgebraicSpaces B S hS) (hqc : IsQuasiCompactSpace B S hS Y.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1) (X : ClosedSubspaces B S hS Y.1) :
    HasClosedSubspaceApproximation B S hS Y X :=
  hasClosedSubspaceApproximation_of_isColimit_finiteTypeQuasicoherentSubobjectCocone B S hS Y
    (fun G _ =>
      (isFiltered_and_nonempty_isColimit_finiteTypeQuasicoherentSubobjectCocone_of_approximation
        B S hS hZ h07SU Y.2 hqc hqs G).2) X

end AlgebraicGeometry.Space

end
