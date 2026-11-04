module

public import StacksFrontier.AlgebraicGeometry.FinitePresentationResidue.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteAlgebraLimitPresentation.Basic
public import StacksFrontier.AlgebraicGeometry.IntegralApproximation.SmallIndex

/-!
# Finite finitely presented approximation of integral algebra sheaves from three hypotheses

An integral quasi-coherent sheaf `A` of commutative `𝒪_X`-algebras is a directed colimit, over a
preorder in `Type u`, of quasi-coherent algebra sheaves that are both finite and of finite
presentation, provided that the finite quasi-coherent subalgebras of `A` have `A` as colimit,
that every quasi-coherent finite algebra sheaf is a colimit of a `u`-small directed system of
finite finitely presented ones indexed in `Type (u + 1)`, and that every quasi-coherent finite
finitely presented algebra sheaf is a finitely presentable object.

## Main definitions

* `Tag086NForAlgebraSheavesLarge`: every quasi-coherent finite algebra sheaf is a colimit of
  quasi-coherent finite finitely presented ones over a `u`-small nonempty directed preorder in
  `Type (u + 1)`.

## Main results

* `tag086NForAlgebraSheaves_of_large`: `Tag086NForAlgebraSheavesLarge X` implies
  `Tag086NForAlgebraSheaves X`.
* `finiteApproximableByFinitePresentation_of_large`: `Tag086NForAlgebraSheavesLarge X` and
  `Tag01BSForAlgebraSheaves X` imply `FiniteApproximableByFinitePresentation X`.
* `exists_small_index_finite_finitePresentation_of_three_items`: an integral quasi-coherent
  algebra sheaf is a directed colimit of quasi-coherent finite finitely presented ones, under the
  three hypotheses above.

## References

* [Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
* [Stacks Project, Tag 086N](https://stacks.math.columbia.edu/tag/086N)
* [Stacks Project, Tag 09YY](https://stacks.math.columbia.edu/tag/09YY)
* [Stacks Project, Tag 01BS](https://stacks.math.columbia.edu/tag/01BS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.RelativeSpec Stacks.AlgebraicGeometry.FiniteSubalgebras
open Stacks.AlgebraicGeometry.Tag0817FinitePresentationResidue

universe u

namespace Stacks.AlgebraicGeometry.Tag0817PartTwoResidue

variable {X : Scheme.{u}}

/-- Every quasi-coherent finite sheaf of commutative `𝒪_X`-algebras is the colimit of a system
indexed by a `u`-small nonempty directed preorder in `Type (u + 1)`, all of whose objects are
quasi-coherent, finite and of finite presentation. -/
def Tag086NForAlgebraSheavesLarge (X : Scheme.{u}) : Prop :=
  ∀ B : AlgebraSheaf X, B.IsQuasicoherent → B.IsFinite →
    ∃ (J : Type (u + 1)) (_ : Preorder J) (_ : Nonempty J) (_ : IsDirected J (· ≤ ·))
      (_ : Small.{u} J) (G : J ⥤ AlgebraSheaf X) (t : G ⟶ (Functor.const J).obj B)
      (_ : IsColimit (Cocone.mk B t)),
      ∀ j, (G.obj j).IsQuasicoherent ∧ (G.obj j).IsFinite ∧ (G.obj j).IsFinitePresentation

/-- `Tag086NForAlgebraSheavesLarge X` implies `Tag086NForAlgebraSheaves X`: an approximating system
over a `u`-small index in `Type (u + 1)` can be reindexed over a preorder in `Type u`. -/
theorem tag086NForAlgebraSheaves_of_large (h : Tag086NForAlgebraSheavesLarge X) :
    Tag086NForAlgebraSheaves X := by
  intro B hBqc hBfin
  obtain ⟨J, _, _, _, _, G, t, ht, hG⟩ := h B hBqc hBfin
  obtain ⟨K, _, _, _, E, σ, hσ, hE⟩ :=
    SmallIndex.exists_small_index_finite_finitePresentation B t ht hG
  exact ⟨K, inferInstance, inferInstance, E, σ, hσ, hE⟩

/-- `Tag086NForAlgebraSheavesLarge X` and `Tag01BSForAlgebraSheaves X` together imply
`FiniteApproximableByFinitePresentation X`. -/
theorem finiteApproximableByFinitePresentation_of_large
    (h086N : Tag086NForAlgebraSheavesLarge X) (h01BS : Tag01BSForAlgebraSheaves X) :
    FiniteApproximableByFinitePresentation X :=
  finiteApproximableByFinitePresentation_of (tag086NForAlgebraSheaves_of_large h086N) h01BS

/-- Let `A` be an integral quasi-coherent sheaf of commutative `𝒪_X`-algebras. Suppose

1. the canonical cocone of the finite quasi-coherent subalgebras of `A` is colimiting;
2. every quasi-coherent finite algebra sheaf on `X` is a colimit of a `u`-small directed system
   of quasi-coherent finite finitely presented ones (`Tag086NForAlgebraSheavesLarge X`);
3. every quasi-coherent finite finitely presented algebra sheaf on `X` is a finitely presentable
   object of `Stacks.RelativeSpec.AlgebraSheaf X` (`Tag01BSForAlgebraSheaves X`).

Then `A` is a directed colimit, over a preorder in `Type u`, of quasi-coherent finite finitely
presented algebra sheaves. No hypothesis on `X` is used. -/
theorem exists_small_index_finite_finitePresentation_of_three_items (A : AlgebraSheaf X)
    (hAqc : A.IsQuasicoherent) (hAint : A.IsIntegral)
    (hcolim : Nonempty (IsColimit (finiteSubalgebraCocone A)))
    (h086N : Tag086NForAlgebraSheavesLarge X) (h01BS : Tag01BSForAlgebraSheaves X) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (F : I ⥤ AlgebraSheaf X) (s : F ⟶ (Functor.const I).obj A)
      (_ : IsColimit (Cocone.mk A s)),
      ∀ i, (F.obj i).IsQuasicoherent ∧ (F.obj i).IsFinite ∧
        (F.obj i).IsFinitePresentation :=
  exists_small_index_finite_finitePresentation_of_isColimit A hAqc hAint hcolim
    (finiteApproximableByFinitePresentation_of_large h086N h01BS)

/-- `exists_small_index_finite_finitePresentation_of_three_items` for a quasi-compact
quasi-separated scheme `X`. -/
example (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (A : AlgebraSheaf X) (hAqc : AlgebraSheaf.IsQuasicoherent A)
    (hAint : AlgebraSheaf.IsIntegral A)
    (hcolim : Nonempty (IsColimit (finiteSubalgebraCocone A)))
    (h086N : Tag086NForAlgebraSheavesLarge X) (h01BS : Tag01BSForAlgebraSheaves X) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (F : I ⥤ AlgebraSheaf X)
      (t : F ⟶ (Functor.const I).obj A) (_ : IsColimit (Cocone.mk A t)),
      ∀ i, AlgebraSheaf.IsQuasicoherent (F.obj i) ∧ AlgebraSheaf.IsFinite (F.obj i) ∧
        AlgebraSheaf.IsFinitePresentation (F.obj i) :=
  exists_small_index_finite_finitePresentation_of_three_items A hAqc hAint hcolim h086N h01BS

end Stacks.AlgebraicGeometry.Tag0817PartTwoResidue

end
