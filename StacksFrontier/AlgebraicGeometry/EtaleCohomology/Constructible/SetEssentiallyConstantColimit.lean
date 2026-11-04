module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ConstructibleQuasiCompact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.EssentiallyConstantColimit

/-!
# Filtered colimits of constructible sheaves of sets are essentially constant

Let `X` be a quasi-compact quasi-separated scheme of a big étale site and let
`F = colim_{i ∈ I} F_i` be a filtered colimit of sheaves of sets on `X_étale`. If `F` and all the
`F_i` are constructible, then the ind-object `F_i` is essentially constant with value `F`. This is
part (1) of Stacks 095P.

The proof applies `isEssentiallyConstantWith_of_isConstructibleSetSheaf_colimit`, which assumes
that every constructible sheaf of sets admits a finite coequalizer presentation by representable
sheaves of quasi-compact quasi-separated schemes, and discharges that hypothesis with
`isConstructibleSetSheaf_iff_hasFiniteQCSRepresentableCoequalizerPresentation_unconditional`
(Stacks 09Y9).

## Main results

* `AlgebraicGeometry.exists_isEssentiallyConstantWith_of_isConstructibleSetSheaf_colimit`: a
  filtered colimit of constructible sheaves of sets with constructible colimit is essentially
  constant with value the colimit.

## References

* [Stacks Project, Tag 095P](https://stacks.math.columbia.edu/tag/095P)
* [Stacks Project, Tag 09Y9](https://stacks.math.columbia.edu/tag/09Y9)
* [Stacks Project, Tag 09Z4](https://stacks.math.columbia.edu/tag/09Z4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v' v u

namespace AlgebraicGeometry

/-- Let `X` be a quasi-compact quasi-separated scheme and let `F = colim_{i ∈ I} F_i` be a
filtered colimit of sheaves of sets on `X_étale`. If `F` and all the `F_i` are constructible, then
the ind-object `F_i` is essentially constant with value `F`. -/
@[stacks 095P "part (1), sheaves of sets"]
public theorem exists_isEssentiallyConstantWith_of_isConstructibleSetSheaf_colimit
    (B : BigEtaleSite.{u}) (X : B.Scheme) [CompactSpace X.1] [QuasiSeparatedSpace X.1]
    {I : Type v} [Category.{v'} I] [IsFiltered I] [EssentiallySmall.{u + 1} I]
    (F : I ⥤ Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1)))
    (t : Cocone F) (ht : IsColimit t)
    (hF : ∀ i, IsConstructibleSetSheaf B X (F.obj i))
    (hcolim : IsConstructibleSetSheaf B X t.pt) :
    ∃ (i : I) (r : t.pt ⟶ F.obj i),
      EssentiallyConstantInd.IsEssentiallyConstantWith F t i r :=
  isEssentiallyConstantWith_of_isConstructibleSetSheaf_colimit B X
    (fun G =>
      (isConstructibleSetSheaf_iff_hasFiniteQCSRepresentableCoequalizerPresentation_unconditional
        B X G).1)
    F t ht hF hcolim

end AlgebraicGeometry

end
