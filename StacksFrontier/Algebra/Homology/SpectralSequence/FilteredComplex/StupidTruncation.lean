module

public import StacksCore.CategoryTheory.Filtration.GradedPieces
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Defs
public import StacksFrontier.Algebra.Homology.StupidTruncation
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The brutal truncation filtration of a cochain complex

Every cochain complex `K^•` of an abelian category carries the decreasing filtration by its
brutal (or stupid) truncations, `F^pK^• = σ_{≥ p}K^•`. This file builds that filtered complex,
identifies its graded pieces, and records the resulting description in the derived category: the
`p`-th graded piece is the single complex on `K^p` placed in degree `p`, which represents
`K^p[-p]`.

The filtration is assembled from the comparisons `σ_{≥ p'}K^• ⟶ σ_{≥ p}K^•` for `p ≤ p'`, which
are monomorphisms because they are compatible with the inclusions into `K^•`. The graded piece
`gr^p` is the cokernel of `σ_{≥ p + 1}K^• ⟶ σ_{≥ p}K^•`, and the short exact sequence
`0 ⟶ σ_{≥ p + 1}K^• ⟶ σ_{≥ p}K^• ⟶ (single p)(K^p) ⟶ 0` identifies it with the single complex on
the bottom term.

## Main definitions

* `CochainComplex.stupidTruncationFiltration`: the filtered complex `F^pK^• = σ_{≥ p}K^•`.
* `CochainComplex.stupidGradedPieceIso`: the identification of `gr^pK^•` with the single complex
  on `K^p` in degree `p`.
* `CochainComplex.stupidGradedPieceDerivedIso`: the resulting identification
  `gr^pK^• ≅ K^p[-p]` in the derived category.

## Implementation notes

The filtration is indexed by `ℤᵒᵖ`, as every `CochainComplex.Filtered` is, and the index `p` is
the truncation degree itself, which is what makes the filtration decreasing — unlike the
canonical truncation filtration of
`StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.CanonicalTruncation`, where the
index has to be negated.

## References

* [Stacks Project, Tag 0118](https://stacks.math.columbia.edu/tag/0118)
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite ComplexShape
open HomologicalComplex StacksDraft.StupidTruncation

namespace CochainComplex

/-- A complex filtered by its brutal truncations, `F^pK^• = σ_{≥ p}K^•`. -/
@[ega "0 11.5.1", sga "4½ Fonctions_L 1.12"]
def stupidTruncationFiltration {C : Type*} [Category* C] [Abelian C]
    (K : CochainComplex C ℤ) : CochainComplex.Filtered C := by
  letI (p : ℤ) : Mono (ιStupidTrunc K (embeddingUpIntGE p)) := mono_ιStupidTrunc K _
  exact
    { X := K
      filtration.toMonoOver :=
        { obj := fun i ↦ MonoOver.mk (ιStupidTrunc K (embeddingUpIntGE i.unop))
          map := fun f ↦ MonoOver.homMk (stupidTruncGEMapLE K (leOfHom f.unop))
            (stupidTruncGEMapLE_ι K _) } }

/-- The `p`-th step of the brutal truncation filtration is the brutal truncation `σ_{≥ p}K^•`. -/
lemma stupidTruncationFiltration_filtration_obj {C : Type*} [Category* C] [Abelian C]
    (K : CochainComplex C ℤ) (p : ℤ) :
    (stupidTruncationFiltration K).filtration.obj (op p) =
      K.stupidTrunc (embeddingUpIntGE p) :=
  rfl

/-- The inclusion of the `p`-th step of the brutal truncation filtration into `K^•` is the
canonical inclusion of the brutal truncation. -/
lemma stupidTruncationFiltration_filtration_ι_app {C : Type*} [Category* C] [Abelian C]
    (K : CochainComplex C ℤ) (p : ℤ) :
    (stupidTruncationFiltration K).filtration.ι.app (op p) =
      ιStupidTrunc K (embeddingUpIntGE p) :=
  rfl

/-- The `p`-th graded piece of the brutal truncation filtration is the single complex on `K^p`
placed in degree `p`: the projection onto the bottom term of `σ_{≥ p}K^•` is a cokernel of the
inclusion of `σ_{≥ p + 1}K^•`. -/
@[ega "III 7.9.6" "partial", sga "4½ Fonctions_L 1.12" "partial"]
def stupidGradedPieceIso {C : Type*} [Category* C] [Abelian C]
    (K : CochainComplex C ℤ) (p : ℤ) :
    (FilteredObject.gr p).obj (stupidTruncationFiltration K) ≅
      (HomologicalComplex.single C (ComplexShape.up ℤ) p).obj (K.X p) :=
  ((stupidTruncGEShortComplex_shortExact K p).gIsCokernel.coconePointUniqueUpToIso
    (cokernelIsCokernel _)).symm

/-- The `p`-th graded piece of the brutal truncation filtration of `K^•` represents `K^p[-p]` in
the derived category. -/
@[sga "4½ Fonctions_L 1.12" "partial"]
def stupidGradedPieceDerivedIso {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (K : CochainComplex A ℤ) (p : ℤ) :
    DerivedCategory.Q.obj
        ((FilteredObject.gr (C := CochainComplex A ℤ) p).obj (stupidTruncationFiltration K)) ≅
      ((DerivedCategory.singleFunctor A 0).obj (K.X p))⟦-p⟧ := by
  let eQ : DerivedCategory.Q.obj
      ((FilteredObject.gr (C := CochainComplex A ℤ) p).obj (stupidTruncationFiltration K)) ≅
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor A p).obj (K.X p)) := by
    simpa only [CochainComplex.singleFunctor, CochainComplex.singleFunctors] using
      DerivedCategory.Q.mapIso (stupidGradedPieceIso K p)
  exact eQ ≪≫ ((DerivedCategory.singleFunctorIsoCompQ A p).app (K.X p)).symm ≪≫
    ((DerivedCategory.singleFunctors A).shiftIso (-p) p 0 (by omega)).symm.app (K.X p)

end CochainComplex

end
