module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.ConnectedOpenSpreadOut
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.SpreadOutImplications
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.RegularSliceThroughPoint

/-!
# The Stacks 057K chain with Tag 0570 discharged

The chain `055P`, `055R` → `057I` → `055W` → `057J` → `057K` is available in the library with
three statements carried as explicit hypotheses: Tags `0570`, `055P` and `055R`. Tag `0570` is
now proved, in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.RegularSliceThroughPoint`, so it
can be supplied rather than assumed. This module does that, and propagates the result up the
chain, so that each link carries only Tags `055P` and `055R`, or Tag `057I`, of which those two
are the only missing inputs.

## Main results

Everything here lives in the `AlgebraicGeometry` namespace.

* `Statement057K` writes down the statement of Tag `057K` as a `Prop`, in the same style as the
  statements of its inputs in
  `StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.ConditionalStatements`.
* `statement055W_of_statement057I` and
  `exists_elementaryEtaleNeighborhood_open_geometricallyConnected_of_statement057I`
  are Tag `055W` conditional on Tag `057I` alone.
* `statement055W_of_statement055P_statement055R` is Tag `055W` conditional on Tags `055P` and
  `055R` alone.
* `statement057J_of_statement055P_statement055R` and
  `statement057K_of_statement055P_statement055R` are Tags `057J` and `057K` conditional on
  Tags `055P` and `055R` alone.

## Implementation notes

Nothing here is tagged: every statement still carries a hypothesis that the corresponding Stacks
statement does not have. Tag `055R` is in turn available granted Tag `0559`, which is the single
remaining input of the whole chain; that reduction is in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.FromGenericFibreIrreducibility`.

## References

* [Stacks Project, Tag 057K](https://stacks.math.columbia.edu/tag/057K)
* [Stacks Project, Tag 057J](https://stacks.math.columbia.edu/tag/057J)
* [Stacks Project, Tag 055W](https://stacks.math.columbia.edu/tag/055W)
* [Stacks Project, Tag 057I](https://stacks.math.columbia.edu/tag/057I)
* [Stacks Project, Tag 0570](https://stacks.math.columbia.edu/tag/0570)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 057K.** A morphism locally of finite type is, in elementary étale
neighbourhoods of a point and of its image, finite over a smooth morphism of relative dimension
the dimension of the fibre at that point, with geometrically integral fibres and purely
transcendental residue field extension; and the finite morphism is of finite presentation as
soon as the original one is. -/
abbrev Statement057K : Prop :=
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X),
    ∃ (n : ℕ) (_ : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = n)
      (U : EtaleNeighborhood X x) (V : EtaleNeighborhood S (f x))
      (Y : Scheme.{u}) (h : Y ⟶ V.scheme) (π : U.scheme ⟶ Y),
      U.IsElementary ∧ V.IsElementary ∧ (U.toBase ≫ f = π ≫ h ≫ V.toBase) ∧
        SmoothOfRelativeDimension n h ∧
        (∀ s' : V.scheme, GeometricallyIntegral (h.fiberToSpecResidueField s')) ∧
        IsFinite π ∧ (∀ z : U.scheme, π z = π U.point ↔ z = U.point) ∧
        (∃ heq : h (π U.point) = V.point,
          letI : Algebra (V.scheme.residueField V.point) (Y.residueField (π U.point)) :=
            ((V.scheme.residueFieldCongr heq).inv ≫ h.residueFieldMap (π U.point)).hom.toAlgebra
          PurelyTranscendental (V.scheme.residueField V.point)
            (Y.residueField (π U.point))) ∧
        (LocallyOfFinitePresentation f → FinitePresentation π)

/-- **Stacks Project, Tag 057K** follows from Tag 055W. This is
`AlgebraicGeometry.exists_finite_over_smooth_geometricallyIntegral_of_statement055W` in the
shape `AlgebraicGeometry.Statement057K`. -/
theorem statement057K_of_statement055W (h055W : Statement055W.{u}) : Statement057K.{u} :=
  fun f _ x ↦ exists_finite_over_smooth_geometricallyIntegral_of_statement055W h055W f x

/-- **Stacks Project, Tag 055W**, conditional on Tag 057I alone: Tag 0570, the other input of
the proof of Tag 055W, is available. -/
theorem statement055W_of_statement057I (h057I : Statement057I.{u}) : Statement055W.{u} :=
  statement055W_of_statement0570_statement057I Stacks.AlgebraicGeometry.statement0570 h057I

/-- **Stacks Project, Tag 055W**, conditional on Tags 055P and 055R alone, which are the two
inputs of Tag 057I. -/
theorem statement055W_of_statement055P_statement055R
    (h055P : Statement055P.{u}) (h055R : Statement055R.{u}) : Statement055W.{u} :=
  statement055W_of_statement057I (ConnectedComponentSection.statement057I h055P h055R)

/-- **Stacks Project, Tag 055W**, conditional on Tag 057I alone, with the binders written out:
a geometrically connected open in a fibre of a flat, finitely presented morphism with
geometrically reduced fibres spreads, after an affine elementary étale base change, to a
quasi-compact open with geometrically connected fibres. -/
theorem exists_elementaryEtaleNeighborhood_open_geometricallyConnected_of_statement057I
    (h057I : Statement057I.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) (s : S) (T : (f.fiber s).Opens)
    (hfp : FinitePresentation f) [Flat f] [GeometricallyReduced f]
    [GeometricallyConnected (T.ι ≫ f.fiberToSpecResidueField s)] :
    ∃ (U : EtaleNeighborhood S s) (_ : U.IsElementary) (_ : IsAffine U.scheme)
      (V : (pullback f U.toBase).Opens),
      QuasiCompact V.ι ∧ GeometricallyConnected (V.ι ≫ pullback.snd f U.toBase) ∧
      ∀ x : (pullback.snd f U.toBase).fiber U.point,
        ((pullback.snd f U.toBase).fiberι U.point x ∈ V) ↔
          pullback.fst f U.toBase ((pullback.snd f U.toBase).fiberι U.point x) ∈
            f.fiberι s '' (T : Set (f.fiber s)) :=
  statement055W_of_statement057I h057I f s T hfp

/-- **Stacks Project, Tag 057J**, conditional on Tags 055P and 055R alone. -/
theorem statement057J_of_statement055P_statement055R
    (h055P : Statement055P.{u}) (h055R : Statement055R.{u}) : Statement057J.{u} :=
  statement057J_of_statement055W (statement055W_of_statement055P_statement055R h055P h055R)

/-- **Stacks Project, Tag 057K**, conditional on Tags 055P and 055R alone. -/
theorem statement057K_of_statement055P_statement055R
    (h055P : Statement055P.{u}) (h055R : Statement055R.{u}) : Statement057K.{u} :=
  statement057K_of_statement055W (statement055W_of_statement055P_statement055R h055P h055R)

end AlgebraicGeometry

end
