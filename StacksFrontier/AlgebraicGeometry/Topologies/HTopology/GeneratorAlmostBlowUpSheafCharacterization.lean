module

public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpSubterminal

/-!
# The four-condition characterization of h sheaves

Stacks 0EVI: a presheaf of sets on the big h site `(Sch/S)_h` of Stacks 0EU1 is a sheaf if and
only if

1. it is a sheaf for the Zariski topology;
2. for every morphism `f : X ⟶ Y` of the site with `Y` affine and `f` surjective, flat, proper
   and of finite presentation, `F(Y)` is the equalizer of the two maps `F(X) ⟶ F(X ×_Y X)`;
3. it turns every almost blowup square of the site of the shape of Example 0EVG into a cartesian
   square of sets;
4. it turns every almost blowup square of the site of the shape of Example 0EVH into a cartesian
   square of sets.

## Main results

* `AlgebraicGeometry.BigHOver.isSheaf_iff_generatorAlmostBlowUpConditions`: **Stacks 0EVI**.

## Implementation notes

The necessity of the four conditions is
`AlgebraicGeometry.BigHOver.zariski_and_affineFlatProperFP_and_generatorSquares_of_isSheaf`, and
their sufficiency is `AlgebraicGeometry.BigHOver.isSheaf_of_generatorSquares`. Condition (2) in
the source's equalizer form is
`AlgebraicGeometry.BigHOver.IsAffineFlatProperFinitePresentationSheaf.bijective_mapToEqualizer`.

## References

* [Stacks Project, Tag 0EVI](https://stacks.math.columbia.edu/tag/0EVI)
-/

@[expose] public section

open CategoryTheory

universe v u

namespace AlgebraicGeometry.BigHOver

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (F : (BigHOver B S hS)ᵒᵖ ⥤ Type v)

/-- **Stacks 0EVI.** A presheaf of sets on the big h category over `S` is a sheaf for the h
topology if and only if it is a Zariski sheaf, satisfies the sheaf condition for every flat proper
surjection of finite presentation of the site onto an affine object, and sends the almost blowup
squares of the site of the shapes of Examples 0EVG and 0EVH to cartesian squares of sets. -/
@[stacks 0EVI]
public theorem isSheaf_iff_generatorAlmostBlowUpConditions :
    Presheaf.IsSheaf (BigHOver.topology B S hS) F ↔
      (IsZariskiSheaf B S hS F ∧ IsAffineFlatProperFinitePresentationSheaf B S hS F ∧
        IsOneGeneratorAlmostBlowUpSheaf B S hS F ∧ IsTwoGeneratorAlmostBlowUpSheaf B S hS F) :=
  ⟨zariski_and_affineFlatProperFP_and_generatorSquares_of_isSheaf B S hS F,
    fun ⟨hzar, haff, h1, h2⟩ ↦ isSheaf_of_generatorSquares B S hS F hzar haff h1 h2⟩

end AlgebraicGeometry.BigHOver

end
