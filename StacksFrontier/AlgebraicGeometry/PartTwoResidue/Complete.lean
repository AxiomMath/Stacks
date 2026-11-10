module

public import StacksFrontier.AlgebraicGeometry.FiniteSubalgebra.SmallSystem
public import StacksFrontier.AlgebraicGeometry.PartTwoResidue.Presentable

/-!
# Part (2) of [Stacks, Tag 0817]

Let `X` be a quasi-compact and quasi-separated scheme and let `A` be an integral quasi-coherent
sheaf of commutative `𝒪_X`-algebras.  Then `A` is a directed colimit, over a nonempty directed
preorder in the universe of the scheme, of quasi-coherent `𝒪_X`-algebras that are **both finite
and of finite presentation**.  That is part (2) of the tag, and it is proved here outright.

## Route

Three inputs, each proved, and no hypothesis beyond the tag's own:

* part (1) of the tag at a `u`-small index —
  `Stacks.AlgebraicGeometry.FiniteSubalgebras.exists_small_isColimit_finite`: `A` is the colimit
  of a directed system of **finite** quasi-coherent subalgebras;
* [Stacks, Tag 086N] at a `u`-small index —
  `Stacks.FiniteAlgebraLimitPresentation.exists_small_isColimit_finite_finitePresentation`: each of
  those is in turn the colimit of a directed system of quasi-coherent algebras that are finite and
  of finite presentation;
* the splice, `Stacks.FinitelyPresentableComposition.exists_directed_index_algebraSheaf`, whose one
  hypothesis is that the inner stages are finitely presentable **along those two cocones**.  All
  the stages and all the vertices involved are quasi-coherent, so that hypothesis is
  `Stacks.AlgebraicGeometry.Tag0817Presentable.presentableAlong_of_isFinitePresentation`, i.e.
  [Stacks, Tag 01ZC] carried across the relative-spectrum anti-equivalence of [Stacks, Tag 01SA].

## Main results

* `exists_small_index_finite_finitePresentation`: **part (2) of [Stacks, Tag 0817]**, with the
  tag's hypotheses and nothing else.
* `nonempty_integralLimitPresentation`: **[Stacks, Tag 09YZ]**, which part (2) was the last
  missing input of — an integral morphism over a quasi-compact and quasi-separated base is a
  directed inverse limit of schemes finite and of finite presentation over that base.

## The covering set of the tags

[Stacks, Tag 0817] has three assertions and therefore a covering set of three declarations:

* the directedness of part (1),
  `Stacks.AlgebraicGeometry.FiniteSubalgebras.isFiltered_finiteSubalgebra`;
* the colimit of part (1),
  `Stacks.AlgebraicGeometry.FiniteSubalgebras.nonempty_isColimit_finiteSubalgebraCocone`;
* part (2), `exists_small_index_finite_finitePresentation` below.

The attribute sits on all three.

[Stacks, Tag 09YZ] is a single assertion, so its covering set is the single declaration
`nonempty_integralLimitPresentation` below, which carries its attribute.  The affine-base case
`AlgebraicGeometry.nonempty_integralLimitPresentation_of_isAffine` is a strictly weaker statement
and so is *not* in that covering set and no longer carries the tag.

## What the earlier records say, and why it is now stale

`StacksFrontier/AlgebraicGeometry/FinitePresentationResidue/Basic.lean`,
`StacksFrontier/AlgebraicGeometry/PartTwoResidue/Basic.lean`,
`StacksFrontier/AlgebraicGeometry/FinitelyPresentableComposition/AlgebraSheaf.lean` and
`StacksFrontier/AlgebraicGeometry/Limits/IntegralLimitFromAlgebraColimit.lean` all record part (2)
as owed [Stacks, Tag 01BS] for algebra sheaves, namely
`CategoryTheory.IsFinitelyPresentable` of a finite finitely presented quasi-coherent algebra as an
object of `Stacks.RelativeSpec.AlgebraSheaf X`.  That statement is still absent and still looks
hard — it quantifies over filtered colimits of algebra sheaves that need not be quasi-coherent,
whose construction wants a sheafification of presheaves of commutative rings that does not
synthesize at this pin.  It is simply not what the composition needs: reading the uses of its
hypothesis shows every one of them is along the two cocones at hand, all of whose stages and
vertices are quasi-coherent, and there the relative spectrum is available and tag 01ZC answers.

The conditional statements in those files are left standing: they are true, their hypotheses are
weaker than tag 01BS, and `exists_small_index_finite_finitePresentation` does not go through them
(it calls the composition directly, with part (1)'s small-index form rather than the subobject
category).

## References

* [Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
* [Stacks Project, Tag 09YZ](https://stacks.math.columbia.edu/tag/09YZ)
* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
* [Stacks Project, Tag 086N](https://stacks.math.columbia.edu/tag/086N)
* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 01BS](https://stacks.math.columbia.edu/tag/01BS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.RelativeSpec

universe u

namespace Stacks.AlgebraicGeometry.Tag0817PartTwo

/-- **Stacks Project, Tag 0817, part (2).**  On a quasi-compact and quasi-separated scheme an
integral quasi-coherent sheaf of commutative `𝒪_X`-algebras is a directed colimit, over a nonempty
directed preorder in the universe of the scheme, of quasi-coherent `𝒪_X`-algebras that are both
finite and of finite presentation.

Part (1) of the tag writes `A` as the colimit of its finite quasi-coherent subalgebras,
[Stacks, Tag 086N] writes each of those as a colimit of finite finitely presented ones, and the
two colimits are spliced by
`Stacks.FinitelyPresentableComposition.exists_directed_index_algebraSheaf`; its presentability
hypothesis holds along these cocones by
`Stacks.AlgebraicGeometry.Tag0817Presentable.presentableAlong_of_isFinitePresentation`. -/
@[stacks 0817 "part (2): A is a directed colimit of finite and finitely presented quasi-coherent
algebras, for X quasi-compact and quasi-separated and A quasi-coherent and integral"]
theorem exists_small_index_finite_finitePresentation (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (A : AlgebraSheaf X) (hAqc : AlgebraSheaf.IsQuasicoherent A)
    (hAint : AlgebraSheaf.IsIntegral A) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (F : I ⥤ AlgebraSheaf X) (t : F ⟶ (Functor.const I).obj A)
      (_ : IsColimit (Cocone.mk A t)),
      ∀ i, AlgebraSheaf.IsQuasicoherent (F.obj i) ∧ AlgebraSheaf.IsFinite (F.obj i) ∧
        AlgebraSheaf.IsFinitePresentation (F.obj i) := by
  classical
  obtain ⟨I, _, _, _, D, t, ht, hD⟩ :=
    FiniteSubalgebras.exists_small_isColimit_finite A hAqc hAint
  choose K hKpre hKne hKdir E σ hσ hE using fun i : I =>
    Stacks.FiniteAlgebraLimitPresentation.exists_small_isColimit_finite_finitePresentation
      X (D.obj i) (hD i).1 (hD i).2
  let _ : ∀ i, Preorder (K i) := hKpre
  have : ∀ i, Nonempty (K i) := hKne
  have : ∀ i, IsDirected (K i) (· ≤ ·) := hKdir
  have : ∀ i, IsFiltered (K i) := fun i => inferInstance
  refine Stacks.FinitelyPresentableComposition.exists_directed_index_algebraSheaf
    (K := K) (E := E) t σ ht hσ (fun i k => ⟨?_, fun i' => ?_⟩)
    (fun B => B.IsQuasicoherent ∧ B.IsFinite ∧ B.IsFinitePresentation) (fun i k => hE i k)
  · exact Tag0817Presentable.presentableAlong_of_isFinitePresentation
      (fun j => (hD j).1) hAqc t ht (hE i k).1 (hE i k).2.2
  · exact Tag0817Presentable.presentableAlong_of_isFinitePresentation
      (fun k' => (hE i' k').1) (hD i').1 (σ i') (hσ i') (hE i k).1 (hE i k).2.2

/-- Part (2) of [Stacks, Tag 0817] in the packaged form
`Stacks.IntegralLimit.IntegralAlgebraHasFiniteFinitePresentationColimit`, which is the same
statement quantified over the scheme.  That proposition is the standing hypothesis of
`Stacks.IntegralLimit.nonempty_integralLimitPresentation_of_algebraColimit`, so it is discharged
here. -/
theorem integralAlgebraHasFiniteFinitePresentationColimit :
    Stacks.IntegralLimit.IntegralAlgebraHasFiniteFinitePresentationColimit.{u} :=
  fun S hc hqs A hAqc hAint =>
    @exists_small_index_finite_finitePresentation S hc hqs A hAqc hAint

/-- **Stacks Project, Tag 09YZ.**  An integral morphism to a quasi-compact and quasi-separated
scheme exhibits its source as the limit of a directed inverse system of schemes finite and of
finite presentation over that target.

This is the tag's own proof.  The quasi-coherent algebra `f_* 𝒪_X` ([Stacks, Tag 01LC], here
`Stacks.AffineAlgebraEquivalence.isQuasicoherent_pushforwardAlgebra`) is integral, part (2) of
[Stacks, Tag 0817] — `exists_small_index_finite_finitePresentation` above, packaged as
`integralAlgebraHasFiniteFinitePresentationColimit` — writes it as a filtered colimit of finite,
finitely presented quasi-coherent `𝒪_S`-algebras, and the relative spectrum turns that colimit
into the required limit of schemes, with the finiteness and the finite presentation of each stage
read off its algebra.  That last passage is
`Stacks.IntegralLimit.nonempty_integralLimitPresentation_of_algebraColimit`, whose only hypothesis
was part (2).

The base is quasi-compact and quasi-separated, as the tag asks; the affine-base case
`AlgebraicGeometry.nonempty_integralLimitPresentation_of_isAffine` is strictly weaker and is
subsumed by this. -/
@[stacks 09YZ "an integral morphism over a quasi-compact and quasi-separated base is the limit of
a directed inverse system of schemes finite and of finite presentation over that base"]
theorem nonempty_integralLimitPresentation {X S : Scheme.{u}} (f : X ⟶ S) [IsIntegralHom f]
    [CompactSpace S] [QuasiSeparatedSpace S] :
    Nonempty (_root_.AlgebraicGeometry.IntegralLimitPresentation f) :=
  Stacks.IntegralLimit.nonempty_integralLimitPresentation_of_algebraColimit
    integralAlgebraHasFiniteFinitePresentationColimit f

end Stacks.AlgebraicGeometry.Tag0817PartTwo

end
