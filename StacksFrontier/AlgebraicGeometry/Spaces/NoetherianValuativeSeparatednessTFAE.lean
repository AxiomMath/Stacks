module

public import StacksFrontier.AlgebraicGeometry.Limits.NoetherianValuativeCriterion.GenericProperness
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianValuativeSeparatedness

/-!
# The Noetherian valuative criterion for separatedness of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is quasi-separated
and locally of finite type, with `Y` locally Noetherian. Then `f` is separated if and only if
every valuative diagram (Stacks 0H1V) has at most one dotted arrow, if and only if this holds
for the diagrams over discrete valuation rings, if and only if it holds for the diagrams over
discrete valuation rings whose generic arrow picks out a point of codimension zero of `X`.

## Main results

* `AlgebraicGeometry.Space.isSeparated_of_isLocallyOfFiniteType_of_codimensionZeroUniqueness`:
  condition (4) implies condition (1).
* `AlgebraicGeometry.Space.isSeparated_tfae_of_isLocallyOfFiniteType`: **Stacks 0H1W**, the
  equivalence of the four conditions.

## Implementation notes

The reduction of (4) implies (1) to a statement about schemes is
`AlgebraicGeometry.Space.isSeparated_of_codimensionZeroUniqueness`: an étale chart of the
relative diagonal is a quasi-compact monomorphism of schemes, locally of finite type over a
locally Noetherian scheme, satisfying condition (4) of Stacks 0208. The scheme-level step,
that such a morphism is proper, is the implication (4) implies (1) of Stacks 0208, which is
`AlgebraicGeometry.isProper_of_genericDiscreteValuativeCriterion`. The present module supplies
that step, so the statements here carry exactly the hypotheses of the source.

## References

* [Stacks Project, Tag 0H1W](https://stacks.math.columbia.edu/tag/0H1W)
* [Stacks Project, Tag 0208](https://stacks.math.columbia.edu/tag/0208)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 0H1W, (4) implies (1).** Let `f : X ⟶ Y` be a quasi-separated morphism of
algebraic spaces over `S`, locally of finite type, with `Y` locally Noetherian. If every
valuative diagram for `f` over a discrete valuation ring whose generic arrow picks out a point
of codimension zero of `X` has at most one dotted arrow, then `f` is separated. -/
theorem isSeparated_of_isLocallyOfFiniteType_of_codimensionZeroUniqueness
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hqs : IsQuasiSeparated B S hS f) (hlft : IsLocallyOfFiniteType B S hS f)
    (hnoeth : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (h : ValuativeCriterion.CodimensionZeroUniqueness f) :
    IsSeparated B S hS f :=
  isSeparated_of_codimensionZeroUniqueness
    (fun p hU hp hpqc _ hcrit => by
      have := hU
      have := hp
      have := hpqc
      exact AlgebraicGeometry.isProper_of_genericDiscreteValuativeCriterion p hcrit)
    hX hY f hqs hlft hnoeth h

/-- **Stacks 0H1W.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is
quasi-separated and locally of finite type, with `Y` locally Noetherian. The following are
equivalent:

1. `f` is separated;
2. every valuative diagram for `f` has at most one dotted arrow;
3. every valuative diagram for `f` whose valuation ring is a discrete valuation ring has at most
   one dotted arrow;
4. every valuative diagram for `f` whose valuation ring is a discrete valuation ring and whose
   generic arrow picks out a point of codimension zero of `X` has at most one dotted arrow. -/
@[stacks 0H1W]
theorem isSeparated_tfae_of_isLocallyOfFiniteType
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hqs : IsQuasiSeparated B S hS f) (hlft : IsLocallyOfFiniteType B S hS f)
    (hnoeth : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsLocallyNoetherian T)) :
    List.TFAE
      [ IsSeparated B S hS f,
        ValuativeCriterion.Uniqueness f,
        ValuativeCriterion.DiscreteUniqueness f,
        ValuativeCriterion.CodimensionZeroUniqueness f ] := by
  tfae_have 1 → 2 := valuativeCriterion_uniqueness_of_isSeparated f
  tfae_have 2 → 3 := discreteUniqueness_of_uniqueness
  tfae_have 3 → 4 := codimensionZeroUniqueness_of_discreteUniqueness
  tfae_have 4 → 1 :=
    isSeparated_of_isLocallyOfFiniteType_of_codimensionZeroUniqueness hX hY f hqs hlft hnoeth
  tfae_finish

end AlgebraicGeometry.Space

end
