module

public import StacksFrontier.AlgebraicGeometry.FiniteAlgebraLimitPresentation.SmallIndex
public import StacksFrontier.AlgebraicGeometry.FiniteSubalgebra.Basic
public import StacksFrontier.AlgebraicGeometry.PartTwoResidue.Basic

/-!
# Part (2) of [Stacks, Tag 0817] from [Stacks, Tag 01BS] for algebra sheaves

Part (2) of [Stacks, Tag 0817] asks that an integral quasi-coherent algebra `A` on a
quasi-compact quasi-separated scheme be a directed colimit, over a preorder in `Type u`, of
quasi-coherent algebras that are **both finite and of finite presentation**.

`Stacks.AlgebraicGeometry.Tag0817PartTwoResidue`'s
`exists_small_index_finite_finitePresentation_of_three_items` reduces it to three hypotheses:

1. `hcolim`, part (1)'s colimit assertion;
2. `h086N : Tag086NForAlgebraSheavesLarge X`, [Stacks, Tag 086N] for algebra sheaves at an index
   in `Type (u + 1)` together with a `CategoryTheory.Small.{u}` instance on that index;
3. `h01BS : Tag01BSForAlgebraSheaves X`, the finite presentability *as objects of
   `Stacks.RelativeSpec.AlgebraSheaf X`* of the approximating algebras.

On a quasi-compact quasi-separated scheme the first two hold:

* `hcolim` is
  `Stacks.AlgebraicGeometry.FiniteSubalgebras.nonempty_isColimit_finiteSubalgebraCocone`, whose
  only hypotheses are `[CompactSpace X]`, `[QuasiSeparatedSpace X]`, quasi-coherence and
  integrality;
* [Stacks, Tag 086N] holds with the index already in `Type u`, by
  `Stacks.FiniteAlgebraLimitPresentation.exists_small_isColimit_finite_finitePresentation`, which
  is `Tag086NForAlgebraSheaves` outright.

So part (2) follows from `Tag01BSForAlgebraSheaves X` alone. Part (2) itself is proved, without
that hypothesis, as
`Stacks.AlgebraicGeometry.Tag0817PartTwo.exists_small_index_finite_finitePresentation`, through
[Stacks, Tag 01ZC] carried across the relative-spectrum anti-equivalence
(`Stacks.AlgebraicGeometry.Tag0817Presentable.presentableAlong_of_isFinitePresentation`); the
results below record that `Tag01BSForAlgebraSheaves X` is a sufficient condition.

## Main results

* `tag086NForAlgebraSheaves_of_qcqs`: [Stacks, Tag 086N] for algebra sheaves, with index in
  `Type u`, on a quasi-compact quasi-separated scheme.
* `finiteApproximableByFinitePresentation_of_tag01BS`: the fused residue of
  `Stacks.AlgebraicGeometry.Tag0817FinitePresentationResidue` from tag 01BS alone.
* `exists_small_index_finite_finitePresentation_of_tag01BS`: part (2) of [Stacks, Tag 0817] from
  the additional hypothesis `Tag01BSForAlgebraSheaves X`.

## Implementation notes

`Tag01BSForAlgebraSheaves X` is

  `∀ C : Stacks.RelativeSpec.AlgebraSheaf X, C.IsQuasicoherent → C.IsFinite →`
  `  C.IsFinitePresentation → CategoryTheory.IsFinitelyPresentable.{u} C`.

[Stacks, Tag 01BS] for sheaves of *modules* is
`Stacks.SheafOfModules.preservesColimitsOfShape_coyoneda_of_isFinitePresentation`; the statement
for sheaves of *algebras* asks for `IsFinitelyPresentable` in `CategoryTheory.Under X.sheaf`, where
filtered colimits are the sheafified ones.

## References

* [Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
* [Stacks Project, Tag 086N](https://stacks.math.columbia.edu/tag/086N)
* [Stacks Project, Tag 01BS](https://stacks.math.columbia.edu/tag/01BS)
* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.RelativeSpec Stacks.AlgebraicGeometry.FiniteSubalgebras
open Stacks.AlgebraicGeometry.Tag0817FinitePresentationResidue

universe u

namespace Stacks.AlgebraicGeometry.Tag0817PartTwoResidue

/-- **[Stacks, Tag 086N] for algebra sheaves, at the index universe of part (2) of
[Stacks, Tag 0817].**

Every quasi-coherent finite sheaf of commutative `𝒪_X`-algebras on a quasi-compact and
quasi-separated scheme is the colimit of a filtered system, indexed by a small category in
`Type u`, all of whose objects are quasi-coherent, finite and of finite presentation.

This is `Stacks.FiniteAlgebraLimitPresentation.exists_small_isColimit_finite_finitePresentation`
repackaged: a nonempty directed preorder in `Type u` is a filtered small category by instance
search. -/
theorem tag086NForAlgebraSheaves_of_qcqs (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] : Tag086NForAlgebraSheaves X := by
  intro B hBqc hBfin
  obtain ⟨I, _, _, _, F, t, ht, hF⟩ :=
    FiniteAlgebraLimitPresentation.exists_small_isColimit_finite_finitePresentation X B hBqc hBfin
  exact ⟨I, inferInstance, inferInstance, F, t, ht, hF⟩

/-- **The fused residue of `Stacks.AlgebraicGeometry.Tag0817FinitePresentationResidue` from
[Stacks, Tag 01BS] alone**, on a quasi-compact and quasi-separated scheme.

This is `tag086NForAlgebraSheaves_of_qcqs` fed to `finiteApproximableByFinitePresentation_of`. -/
theorem finiteApproximableByFinitePresentation_of_tag01BS (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (h01BS : Tag01BSForAlgebraSheaves X) :
    FiniteApproximableByFinitePresentation X :=
  finiteApproximableByFinitePresentation_of (tag086NForAlgebraSheaves_of_qcqs X) h01BS

/-- **Part (2) of [Stacks, Tag 0817] from [Stacks, Tag 01BS] for algebra sheaves.**

Let `X` be a quasi-compact and quasi-separated scheme and `A` an integral quasi-coherent sheaf of
commutative `𝒪_X`-algebras.  Suppose every quasi-coherent finite finitely presented algebra sheaf
on `X` is a finitely presentable object of `Stacks.RelativeSpec.AlgebraSheaf X` —
[Stacks, Tag 01BS] for algebra sheaves.  Then `A` is a directed colimit, over a preorder in
`Type u`, of quasi-coherent algebra sheaves that are finite and of finite presentation.

The other two hypotheses of `exists_small_index_finite_finitePresentation_of_three_items` are
supplied by `Stacks.AlgebraicGeometry.FiniteSubalgebras.nonempty_isColimit_finiteSubalgebraCocone`
and `tag086NForAlgebraSheaves_of_qcqs`. -/
theorem exists_small_index_finite_finitePresentation_of_tag01BS {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (A : AlgebraSheaf X) (hAqc : A.IsQuasicoherent)
    (hAint : A.IsIntegral) (h01BS : Tag01BSForAlgebraSheaves X) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (F : I ⥤ AlgebraSheaf X) (s : F ⟶ (Functor.const I).obj A)
      (_ : IsColimit (Cocone.mk A s)),
      ∀ i, (F.obj i).IsQuasicoherent ∧ (F.obj i).IsFinite ∧
        (F.obj i).IsFinitePresentation :=
  exists_small_index_finite_finitePresentation_of_isColimit A hAqc hAint
    (nonempty_isColimit_finiteSubalgebraCocone A hAqc hAint)
    (finiteApproximableByFinitePresentation_of_tag01BS X h01BS)

/-- `exists_small_index_finite_finitePresentation_of_tag01BS` with `X` explicit and the
predicates written in `AlgebraSheaf.IsQuasicoherent A` form. -/
example (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (A : AlgebraSheaf X) (hAqc : AlgebraSheaf.IsQuasicoherent A)
    (hAint : AlgebraSheaf.IsIntegral A) (h01BS : Tag01BSForAlgebraSheaves X) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (F : I ⥤ AlgebraSheaf X)
      (t : F ⟶ (Functor.const I).obj A) (_ : IsColimit (Cocone.mk A t)),
      ∀ i, AlgebraSheaf.IsQuasicoherent (F.obj i) ∧ AlgebraSheaf.IsFinite (F.obj i) ∧
        AlgebraSheaf.IsFinitePresentation (F.obj i) :=
  exists_small_index_finite_finitePresentation_of_tag01BS A hAqc hAint h01BS

end Stacks.AlgebraicGeometry.Tag0817PartTwoResidue

end
