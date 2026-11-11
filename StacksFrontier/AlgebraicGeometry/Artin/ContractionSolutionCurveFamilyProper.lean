module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolution
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.LimitPreservingFunctorOfPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent

/-!
# Properness and finite presentation of the target of a contraction

Let `(f : X' ⟶ X, T, a)` be a solution of Artin's contraction problem (Stacks 0GH8,
`AlgebraicGeometry.Artin.ContractionSituation.Solution`) whose contraction `f` is surjective on
points. If `X'` is proper over `S`, then `X` is universally closed and quasi-compact over `S`
(Stacks 08AJ and 040W, applied to the surjection `f`). Together with separatedness of `X` and with
local finite presentation of `X` over `S`, which a limit preserving `X` has (Stacks 04AK), this
makes `X` proper and of finite presentation over `S`.

## Main results

* `AlgebraicGeometry.Space.isProper_terminal_from_yoneda`: a scheme of the site whose structure
  morphism is proper is proper over `S` as an algebraic space.
* `AlgebraicGeometry.Artin.ContractionSituation.Solution.isProper_terminal_from`: the target of
  a surjective contraction is proper over `S`.
* `AlgebraicGeometry.Artin.ContractionSituation.Solution.isFinitePresentation_terminal_from`: it
  is of finite presentation over `S`.

## References

* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 040W](https://stacks.math.columbia.edu/tag/040W)
* [Stacks Project, Tag 04AK](https://stacks.math.columbia.edu/tag/04AK)
* [Stacks Project, Tag 08AJ](https://stacks.math.columbia.edu/tag/08AJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A scheme proper over `S` is a proper algebraic space over `S`.** For an object `Z` of the big
fppf site of `S` whose structure morphism is proper, the structure morphism of its Yoneda presheaf
to the terminal presheaf is proper: it is the Yoneda image of the structure morphism, followed by
the identification of the Yoneda presheaf of the terminal object with the terminal presheaf. -/
theorem isProper_terminal_from_yoneda (Z : BigFppfOver B S hS)
    (hZ : _root_.AlgebraicGeometry.IsProper (B.inclusion.map Z.hom)) :
    IsProper B S hS (terminal.from (yoneda.obj Z)) := by
  rw [show terminal.from (yoneda.obj Z) =
      yoneda.map (Over.homMk Z.hom : Z ⟶ Over.mk (𝟙 (B.obj hS))) ≫
        (((Over.mkIdTerminal (X := B.obj hS)).isTerminalObj yoneda _).uniqueUpToIso
          terminalIsTerminal).hom from
      terminal.hom_ext _ _]
  exact (isProper_comp_isIso_iff B S hS _ _).2 (isProper_yoneda_map B S hS _ hZ)

end Space

namespace Artin.ContractionSituation.Solution

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {c : ContractionSituation B S hS} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (s : c.Solution X)

/-- The target of a solution whose contraction `f` is surjective on points is universally closed
over `S` as soon as `X'` is: Stacks 08AJ applied to `X' ⟶ X ⟶ S`. -/
theorem universallyClosed_terminal_from
    (hX' : Space.UniversallyClosed B S hS (terminal.from c.X'))
    (hsurj : Space.IsSurjective B S hS s.f) :
    Space.UniversallyClosed B S hS (terminal.from X) :=
  Space.universallyClosed_of_isSurjective_comp B S hS c.isAlgebraicSpace_X' s.isAlgebraicSpace_X
    (Space.isAlgebraicSpace_terminal B S hS) s.f (terminal.from X)
    (by rwa [show s.f ≫ terminal.from X = terminal.from c.X' from terminal.hom_ext _ _]) hsurj

/-- The target of a solution whose contraction `f` is surjective on points is quasi-compact over
`S` as soon as `X'` is: Stacks 040W applied to `X' ⟶ X ⟶ S`. -/
theorem isQuasiCompact_terminal_from
    (hX' : Space.IsQuasiCompact B S hS (terminal.from c.X'))
    (hsurj : Space.IsSurjective B S hS s.f) :
    Space.IsQuasiCompact B S hS (terminal.from X) :=
  Space.isQuasiCompact_of_comp_surjective B S hS c.isAlgebraicSpace_X' s.isAlgebraicSpace_X
    (Space.isAlgebraicSpace_terminal B S hS) s.f (terminal.from c.X') (terminal.from X)
    (terminal.hom_ext _ _) hsurj hX'

/-- **The target of a surjective contraction is proper.** Let `(f : X' ⟶ X, T, a)` be a solution
with `f` surjective on points, `X'` proper over `S`, `X` separated and locally of finite type over
`S`. Then `X` is proper over `S`. -/
theorem isProper_terminal_from (hX' : Space.IsProper B S hS (terminal.from c.X'))
    (hsurj : Space.IsSurjective B S hS s.f)
    (hsep : Space.IsSeparated B S hS (terminal.from X))
    (hft : Space.IsLocallyOfFiniteType B S hS (terminal.from X)) :
    Space.IsProper B S hS (terminal.from X) :=
  Space.IsProper.mk' B S hS hsep ⟨hft, s.isQuasiCompact_terminal_from hX'.2.1.2 hsurj⟩
    (s.universallyClosed_terminal_from hX'.2.2 hsurj)

include s in
/-- A limit preserving target of a solution is locally of finite type over `S` (Stacks 04AK). -/
theorem isLocallyOfFiniteType_terminal_from_of_limitPreserving
    (hl : LimitPreserving.{u, u, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) X) :
    Space.IsLocallyOfFiniteType B S hS (terminal.from X) :=
  Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
    (Space.isLocallyOfFinitePresentation_of_limitPreserving B S hS s.isAlgebraicSpace_X hl)

/-- **The target of a surjective contraction is of finite presentation.** Let
`(f : X' ⟶ X, T, a)` be a solution with `f` surjective on points, `X'` quasi-compact over `S`,
`X` separated over `S` and limit preserving. Then `X` is of finite presentation over `S`. -/
theorem isFinitePresentation_terminal_from
    (hX' : Space.IsQuasiCompact B S hS (terminal.from c.X'))
    (hsurj : Space.IsSurjective B S hS s.f)
    (hsep : Space.IsSeparated B S hS (terminal.from X))
    (hl : LimitPreserving.{u, u, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) X) :
    Space.IsFinitePresentation B S hS (terminal.from X) :=
  ⟨Space.isLocallyOfFinitePresentation_of_limitPreserving B S hS s.isAlgebraicSpace_X hl,
    s.isQuasiCompact_terminal_from hX' hsurj, Space.isQuasiSeparated_of_isSeparated B S hS hsep⟩

end Artin.ContractionSituation.Solution

end AlgebraicGeometry

end
