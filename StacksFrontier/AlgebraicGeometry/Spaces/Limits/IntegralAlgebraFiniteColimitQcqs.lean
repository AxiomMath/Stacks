module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.Main
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectsQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.IntegralAlgebraFiniteColimit

/-!
# An integral quasi-coherent algebra on a qcqs algebraic space and its finite subalgebras

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S` and let `𝒜` be an
integral quasi-coherent `𝒪_X`-algebra.  Stacks 082C asserts that

1. `𝒜` is the directed colimit of its finite quasi-coherent `𝒪_X`-subalgebras, and
2. `𝒜` is a directed colimit of finite `𝒪_X`-algebras of finite presentation.

The source deduces both clauses from Stacks 07V9 (every quasi-coherent module on `X` is a
filtered colimit of modules of finite presentation) and the colimit assertion of Stacks 0829
(every quasi-coherent module on `X` is the union of its finite type quasi-coherent submodules),
by the argument of Stacks 082B and Stacks 086Z.  Both inputs are available here without
hypotheses beyond the source's: Stacks 07V9 as
`AlgebraicGeometry.Space.exists_isFilteredColimit_isFinitePresentation_essentiallySmall`
applied to `AlgebraicGeometry.Space.isLocallyFpGenerated_of_isQuasiCompactSpace`, and the colimit
assertion of Stacks 0829 as
`AlgebraicGeometry.Space.nonempty_isColimit_finiteTypeQuasicoherentSubobjectCocone_of_qcqs`.
This file feeds them to the deduction
`Space.isFiltered_isColimit_finiteSubalgebra_and_exists_directed_finite_of_presentation`.

## Main results

* `AlgebraicGeometry.Space.exists_small_isFilteredColimit_isFinitePresentation`: Stacks 07V9 with
  a small filtered index category and finite presentation in the sense of
  `SheafOfModules.IsFinitePresentation`.
* `AlgebraicGeometry.Space.isFiltered_isColimit_finiteSubalgebra_and_exists_directed_finite`:
  **both clauses of Stacks 082C.**

## Implementation notes

Clause (1) is rendered as: the category of finite quasi-coherent subalgebras of `𝒜` (a full
subcategory of the subobjects of `𝒜`, hence a preorder) is filtered, that is directed, and `𝒜`
is the colimit of the cocone of their inclusions.  Clause (2) is rendered as a colimit cocone
with vertex `𝒜` over a nonempty directed preorder, in the universe of the schemes, of
quasi-coherent algebras that are finite and of finite presentation.

## References

* [Stacks Project, Tag 082C](https://stacks.math.columbia.edu/tag/082C)
* [Stacks Project, Tag 07V9](https://stacks.math.columbia.edu/tag/07V9)
* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
* [Stacks Project, Tag 086Z](https://stacks.math.columbia.edu/tag/086Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 07V9 over a small index category.**  On a quasi-compact and quasi-separated
algebraic space `X` every quasi-coherent `𝒪_X`-module `F` is the colimit of a diagram, indexed
by a small filtered category, of `𝒪_X`-modules of finite presentation in the sense of
`SheafOfModules.IsFinitePresentation`.  The index category of
`AlgebraicGeometry.Space.exists_isFilteredColimit_isFinitePresentation_essentiallySmall` is
essentially small, and is replaced by its small model. -/
theorem exists_small_isFilteredColimit_isFinitePresentation
    (hZ : B.Contains (⊤_ Scheme.{u})) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hqc : IsQuasiCompactSpace B S hS X)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X) (F : Modules.{u, u} B S hS X hX)
    (hF : F.IsQuasicoherentOnSite) :
    ∃ (I : Type u) (inst : SmallCategory I),
      let _ := inst
      ∃ (_ : IsFiltered I) (D : I ⥤ Modules.{u, u} B S hS X hX)
        (φ : D ⟶ (Functor.const I).obj F),
        (∀ i, (D.obj i).IsFinitePresentation) ∧ Nonempty (IsColimit (Cocone.mk F φ)) := by
  obtain ⟨K, inst, hfil, hsmall, D, φ, hfp, ⟨hcol⟩⟩ :=
    exists_isFilteredColimit_isFinitePresentation_essentiallySmall B S hS hZ hX hqc hqs
      (fun K hK => isLocallyFpGenerated_of_isQuasiCompactSpace B S hS hZ hX hqc hqs K hK) F hF
  let _ := inst
  let e := equivSmallModel.{u} K
  have : IsFiltered (SmallModel.{u} K) := IsFiltered.of_equivalence e
  exact ⟨SmallModel.{u} K, inferInstance, this, e.inverse ⋙ D, Functor.whiskerLeft e.inverse φ,
    fun i => hfp (e.inverse.obj i), ⟨IsColimit.whiskerEquivalence hcol e.symm⟩⟩

/-- **Stacks 082C.**  Let `X` be a quasi-compact and quasi-separated algebraic space over a
scheme `S` and let `A` be an integral quasi-coherent `𝒪_X`-algebra.  Then

1. the finite quasi-coherent subalgebras of `A` form a directed (filtered) category and `A` is
   the colimit of the cocone of their inclusions, and
2. `A` is the colimit of a directed system, over a nonempty directed preorder, of
   quasi-coherent `𝒪_X`-algebras that are finite and of finite presentation.

The hypotheses are the source's. -/
@[stacks 082C]
theorem isFiltered_isColimit_finiteSubalgebra_and_exists_directed_finite
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (hqc : IsQuasiCompactSpace B S hS X)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X)
    (A : AlgebraSheaf.{u, u} B S hS X hX) (hA : A.IsQuasicoherent) (hint : A.IsIntegral) :
    (IsFiltered (FiniteSubalgebra B S hS X hX A) ∧
        Nonempty (IsColimit (finiteSubalgebraCocone B S hS X hX A))) ∧
      ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
        (D : I ⥤ AlgebraSheaf.{u, u} B S hS X hX) (t : D ⟶ (Functor.const I).obj A)
        (_ : IsColimit (Cocone.mk A t)),
        ∀ i, (D.obj i).IsQuasicoherent ∧ (D.obj i).IsFinite ∧ (D.obj i).IsFinitePresentation :=
  isFiltered_isColimit_finiteSubalgebra_and_exists_directed_finite_of_presentation B S hS
    ⟨X, hX⟩ hqc hqs
    (fun G hG => exists_small_isFilteredColimit_isFinitePresentation B S hS B.contains_terminal
      hX hqc hqs G hG)
    A hA hint

end AlgebraicGeometry.Space

end
