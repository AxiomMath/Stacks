module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctorIsomAffine
public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctorLocallyFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctorSeparatedIntegralFibres

/-!
# Properties of an algebraic space representing `Pic_{X/B}`

Let `f : X ⟶ B` be a flat, proper morphism of finite presentation of algebraic spaces with
`𝒪_T ≅ f_{T,*}𝒪_{X_T}` for every scheme `T` over `B` (the standing assumptions of Stacks
Section 0DMD), and let `p : H ⟶ B` be an algebraic space over `B` whose functor of points over
`B` is identified with the relative Picard functor `Pic_{X/B}`. Then `p` is quasi-separated and
locally of finite presentation (Stacks 0DNI), and if moreover the geometric fibres of `f` are
integral, `p` is separated (Stacks 0DNJ).

## Main results

* `PicardSituation.isQuasiSeparated_and_isLocallyOfFinitePresentation_of_represents_picardFunctor`:
  an algebraic space representing `Pic_{X/B}` is quasi-separated and locally of finite
  presentation over `B`.
* `PicardSituation.isSeparated_of_represents_picardFunctor_of_hasIntegralGeometricFibres`:
  if the geometric fibres of `f` are integral, an algebraic space representing `Pic_{X/B}` is
  separated over `B`.

## Implementation notes

The statements quantify over an algebraic space `H` with an identification of its points over
`B` with `Pic_{X/B}`, rather than taking `Pic_{X/B}` itself as the algebraic space (Stacks 0D2C).
Quasi-separatedness uses only that `f` is flat, proper and of finite presentation, and local
finite presentation only that `f` is of finite presentation; the hypothesis
`𝒪_T ≅ f_{T,*}𝒪_{X_T}` enters through Stacks 0D2C, which is replaced by the representing space,
and through Stacks 0DNJ.

## References

* [Stacks Project, Tag 0DNI](https://stacks.math.columbia.edu/tag/0DNI)
* [Stacks Project, Tag 0DNJ](https://stacks.math.columbia.edu/tag/0DNJ)
* [Stacks Project, Tag 0DMD](https://stacks.math.columbia.edu/tag/0DMD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.PicardSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {s : PicardSituation B S hS}
  {H : AlgebraicSpaces B S hS} {p : H ⟶ s.base}

/-- Let `f : X ⟶ B` be a flat, proper morphism of finite presentation of algebraic spaces, and
let `p : H ⟶ B` be an algebraic space over `B` whose functor of points over `B` is identified
(`c`) with the relative Picard functor `Pic_{X/B}`. Then `p` is quasi-separated and locally of
finite presentation. -/
@[stacks 0DNI "Stated for every algebraic space representing Pic_{X/B}, i.e. with an \
identification c of its points over B with Pic_{X/B}, since Section 0DMD presupposes that \
Pic_{X/B} is an algebraic space (Stacks 0D2C); with Pic_{X/B} itself as that space this is \
the lemma as printed. The cohomological-flatness condition O_T -> f_{T,*}O_{X_T} iso of the \
section is dropped: f flat, proper and of finite presentation suffices."]
theorem isQuasiSeparated_and_isLocallyOfFinitePresentation_of_represents_picardFunctor
    (c : spacePointsOver p ⋙ uliftFunctor.{u + 1, u} ≅ s.picardFunctor)
    (hflat : IsFlat B S hS s.f.hom) (hfp : IsFinitePresentation B S hS s.f.hom)
    (hproper : IsProper B S hS s.f.hom) :
    IsQuasiSeparated B S hS p.hom ∧ Space.IsLocallyOfFinitePresentation B S hS p.hom :=
  ⟨isQuasiSeparated_of_represents_picardFunctor c hflat hfp hproper,
    isLocallyOfFinitePresentation_of_represents_picardFunctor c hfp⟩

/-- Let `f : X ⟶ B` be a flat, proper morphism of finite presentation of algebraic spaces with
`𝒪_T ≅ f_{T,*}𝒪_{X_T}` for every scheme `T` over `B`, whose geometric fibres are integral, and
let `p : H ⟶ B` be an algebraic space over `B` whose functor of points over `B` is identified
(`c`) with the relative Picard functor `Pic_{X/B}`. Then `p` is separated. -/
@[stacks 0DNJ "Stated for every algebraic space representing Pic_{X/B}, i.e. with an \
identification c of its points over B with Pic_{X/B}, since Section 0DMD presupposes that \
Pic_{X/B} is an algebraic space (Stacks 0D2C); with Pic_{X/B} itself as that space this is \
the lemma as printed."]
theorem isSeparated_of_represents_picardFunctor_of_hasIntegralGeometricFibres
    (c : spacePointsOver p ⋙ uliftFunctor.{u + 1, u} ≅ s.picardFunctor)
    (hflat : IsFlat B S hS s.f.hom) (hfp : IsFinitePresentation B S hS s.f.hom)
    (hproper : IsProper B S hS s.f.hom) (hstein : s.StructureSheafMapIso)
    (hgeom : HasIntegralGeometricFibres B S hS s.f.hom) :
    IsSeparated B S hS p.hom :=
  isSeparated_of_isQuasiSeparated_of_hasIntegralGeometricFibres c hflat hfp hproper hstein hgeom
    (isQuasiSeparated_of_represents_picardFunctor c hflat hfp hproper)

end AlgebraicGeometry.Space.PicardSituation

end
