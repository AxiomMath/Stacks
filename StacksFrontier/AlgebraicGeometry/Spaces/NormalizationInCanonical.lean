module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraIdentity
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralClosureQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInUniversalProperty

/-!
# The canonical normalization of an algebraic space in another

`AlgebraicGeometry.Space.isRelativeNormalization_toNormalizationIn` shows that the normalization
`ν : X' ⟶ X` of Stacks 0822 and its canonical factorization satisfy
`AlgebraicGeometry.Space.IsRelativeNormalization`, the characterization of Stacks 0823 which
every dependent tag of section 48 takes as a hypothesis.  It takes seven inputs.  Three of them
need not be taken: this file supplies them and restates the conclusion with only the other four.

## Main results

* `AlgebraicGeometry.Space.isRelativeNormalization_canonicalToNormalizationIn`: the
  normalization of `X` in `Y` and its canonical factorization are a relative normalization, for
  a morphism `f` whose direct image `f_* 𝒪_Y` is quasi-coherent.

## Implementation notes

The three inputs discharged, and what discharges each:

* `hqc'`, quasi-coherence of the integral closure of `𝒪_X` in `f_* 𝒪_Y`, is
  `AlgebraicGeometry.Space.AlgebraSheaf.isQuasicoherent_integralClosureSheaf` at `hqc` — the
  quasi-coherence assertion of Stacks 0820.
* `hloc`, `AlgebraicGeometry.Space.AlgebraSheaf.IsIntegralLocalOnAffineCharts` for `f_* 𝒪_Y`, is
  `AlgebraicGeometry.Space.AlgebraSheaf.isIntegralLocalOnAffineCharts_of_isQuasicoherent` at
  `hqc`.  The implementation notes of
  `StacksFrontier.AlgebraicGeometry.Spaces.IntegralClosureSheaf` call this predicate the input to
  Stacks 0820 that the library cannot supply; that is no longer so.
* `hid`, the identity clause of Stacks 03G8 on the direct-image algebra, is
  `AlgebraicGeometry.Space.pushforwardAlgebraUnitIso`.

`hid` is data rather than a proposition, so supplying it is not merely dropping a hypothesis: it
pins down *which* morphism `f' : Y ⟶ X'` the conclusion is about, namely the one built from the
canonical identification `(𝟙_Y)_* 𝒪_Y ≅ 𝒪_Y` rather than from an arbitrary one.  That is why the
statement below names a single factorization where
`AlgebraicGeometry.Space.isRelativeNormalization_toNormalizationIn` names a family of them.

**What is still taken, and why none of it is the content of Stacks 0822.**  Four inputs remain,
and each is a clause of a tag other than 0822: `E` and `C` are the two clauses of Stacks 081V,
`P` is the universal property of the relative spectrum and `D` the dictionary between
integrality of an algebra and integrality of its relative spectrum — both of them structures
that `StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInUniversalProperty` states and that
have no inhabitant — and `hqc` is Stacks 03M9 for the structure sheaf, which is what the
quasi-compactness and quasi-separatedness of the source's `f` are there to give.  No
`@[stacks]` attribute is placed here: 0822 is registered on the two declarations of
`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationIn` that construct `ν` and the
factorization, and 0823 on the three declarations of
`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInUniversalProperty`, including the one this
file restates.

## References

* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
* [Stacks Project, Tag 0823](https://stacks.math.columbia.edu/tag/0823)
* [Stacks Project, Tag 0820](https://stacks.math.columbia.edu/tag/0820)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The normalization of `X` in `Y` is a relative normalization**, in the sense of the
characterization of Stacks 0823, for a morphism `f : Y ⟶ X` of algebraic spaces whose direct
image `f_* 𝒪_Y` is quasi-coherent.

The normalization is the one Stacks 0822 constructs,
`AlgebraicGeometry.Space.normalizationIn`, and the factorization is
`AlgebraicGeometry.Space.toNormalizationIn` at the canonical identification
`(𝟙_Y)_* 𝒪_Y ≅ 𝒪_Y`.  This is
`AlgebraicGeometry.Space.isRelativeNormalization_toNormalizationIn` with the three inputs it
takes beyond `hqc` supplied; see the implementation notes. -/
theorem isRelativeNormalization_canonicalToNormalizationIn
    {E : AffineAlgebraAntiEquivalence B S hS} {C : BaseChangeCompatibility B S hS E}
    (P : RelativeSpecUniversalProperty B S hS E C) (D : IntegralAlgebraDictionary B S hS E)
    {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hqc : (pushforwardAlgebra B S hS (Over.mk f)).IsQuasicoherent) :
    IsRelativeNormalization B S hS f.hom
      (normalizationIn B S hS E f
        (AlgebraSheaf.isQuasicoherent_integralClosureSheaf
          (pushforwardAlgebra B S hS (Over.mk f)) hqc)).obj.hom.hom
      (toNormalizationIn B S hS E C f hqc
        (AlgebraSheaf.isQuasicoherent_integralClosureSheaf
          (pushforwardAlgebra B S hS (Over.mk f)) hqc)
        (pushforwardAlgebraUnitIso B S hS Y)).left.hom :=
  isRelativeNormalization_toNormalizationIn P D f hqc _ _
    (AlgebraSheaf.isIntegralLocalOnAffineCharts_of_isQuasicoherent
      (pushforwardAlgebra B S hS (Over.mk f)) hqc)

end AlgebraicGeometry.Space

end
