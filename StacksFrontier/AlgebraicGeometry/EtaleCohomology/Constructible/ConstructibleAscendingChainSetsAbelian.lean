module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.AbelianEssentiallyConstantColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SerreSubcategory
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SetEssentiallyConstantColimit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Ascending chains of subsheaves of a constructible sheaf of sets or of abelian groups

Let `X` be a Noetherian scheme. Every ascending chain `F₁ ⊂ F₂ ⊂ F₃ ⊂ ⋯ ⊂ F` of subsheaves of a
constructible sheaf of sets, or of a constructible sheaf of abelian groups, on the small étale
site of `X` stabilizes: for some `n` one has `Fₙ = Fₙ₊₁ = Fₙ₊₂ = ⋯`. As in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ConstructibleAscendingChain`, this is
stated as `F` being a Noetherian object of the ambient sheaf category, which by
`CategoryTheory.isNoetherianObject_iff_monotone_chain_condition` is the ascending chain condition
on the subobjects of `F`.

## Main results

* `AlgebraicGeometry.isNoetherianObject_of_isConstructibleSetSheaf'` — sheaves of sets.
* `AlgebraicGeometry.isNoetherianObject_of_isConstructibleAbelianSheaf'` — sheaves of abelian
  groups.

The case of sheaves of modules over a Noetherian ring is
`AlgebraicGeometry.isNoetherianObject_of_isConstructibleModuleSheaf'`.

## Implementation notes

This is the source's proof. `AlgebraicGeometry.isNoetherianObject_of_isConstructibleSetSheaf` and
`AlgebraicGeometry.isNoetherianObject_of_isConstructibleAbelianSheaf` reduce the statement to two
inputs, and both are supplied here from their proofs in this library:

* Stacks 09BH, that a subsheaf of a constructible sheaf is constructible, is
  `AlgebraicGeometry.isConstructibleSetSheaf_of_mono` (part (1)) and
  `AlgebraicGeometry.isConstructibleAbelianSheaf_of_mono` (part (2)), with their inputs Stacks
  03S8, the surjection half of Stacks 09Y9 and Stacks 00YT given by
  `AlgebraicGeometry.representableIsConstructibleSetSheaf`,
  `AlgebraicGeometry.hasFiniteRepresentableCover` and
  `AlgebraicGeometry.smallEtaleUnderlyingSetCommutes`;
* Stacks 095P, that a filtered system of constructible sheaves with constructible colimit is
  essentially constant, is
  `AlgebraicGeometry.exists_isEssentiallyConstantWith_of_isConstructibleSetSheaf_colimit`
  (part (1)) and
  `AlgebraicGeometry.exists_isEssentiallyConstantWith_of_isConstructibleAbelianSheaf_colimit`
  (part (2)), read at the index category `ℕ`.

The quasi-compactness and quasi-separatedness that Stacks 095P asks of `X` follow from its being
Noetherian.

## References

* [Stacks Project, Tag 09YV](https://stacks.math.columbia.edu/tag/09YV)
* [Stacks Project, Tag 09BH](https://stacks.math.columbia.edu/tag/09BH)
* [Stacks Project, Tag 095P](https://stacks.math.columbia.edu/tag/095P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks 09YV for sheaves of sets.** On a Noetherian scheme every ascending chain of
subsheaves of a constructible sheaf of sets on the small étale site stabilizes: the sheaf is a
Noetherian object of the category of sheaves of sets.

Stacks 09BH (1) and Stacks 095P (1) are supplied to
`AlgebraicGeometry.isNoetherianObject_of_isConstructibleSetSheaf` by
`AlgebraicGeometry.isConstructibleSetSheaf_of_mono` and
`AlgebraicGeometry.exists_isEssentiallyConstantWith_of_isConstructibleSetSheaf_colimit`. -/
@[stacks 09YV "sheaves of sets: on a Noetherian scheme a constructible sheaf of sets on the \
small etale site is a Noetherian object, so every ascending chain of subsheaves stabilizes",
  sga "4 IX 2.9" "(ii)"]
public theorem isNoetherianObject_of_isConstructibleSetSheaf'
    (B : BigEtaleSite.{u}) (X : B.Scheme) [IsNoetherian X.obj]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)))
    (hF : IsConstructibleSetSheaf B X F) :
    IsNoetherianObject F := by
  refine isNoetherianObject_of_isConstructibleSetSheaf B X (fun {_ _} i hi hH => ?_)
    (fun M c hc hM hc' =>
      exists_isEssentiallyConstantWith_of_isConstructibleSetSheaf_colimit B X M c hc hM hc')
    F hF
  have := hi
  exact isConstructibleSetSheaf_of_mono B X (representableIsConstructibleSetSheaf B X)
    (hasFiniteRepresentableCover B X) i hH

/-- **Stacks 09YV for sheaves of abelian groups.** On a Noetherian scheme every ascending chain
of subsheaves of a constructible sheaf of abelian groups on the small étale site stabilizes: the
sheaf is a Noetherian object of the category of abelian sheaves.

Stacks 09BH (2) and Stacks 095P (2) are supplied to
`AlgebraicGeometry.isNoetherianObject_of_isConstructibleAbelianSheaf` by
`AlgebraicGeometry.isConstructibleAbelianSheaf_of_mono` and
`AlgebraicGeometry.exists_isEssentiallyConstantWith_of_isConstructibleAbelianSheaf_colimit`. -/
@[stacks 09YV "sheaves of abelian groups: on a Noetherian scheme a constructible abelian sheaf \
on the small etale site is a Noetherian object, so every ascending chain of subsheaves \
stabilizes", sga "4 IX 2.9" "(ii), special case"]
public theorem isNoetherianObject_of_isConstructibleAbelianSheaf'
    (B : BigEtaleSite.{u}) (X : B.Scheme) [IsNoetherian X.obj]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B X F) :
    IsNoetherianObject F := by
  refine isNoetherianObject_of_isConstructibleAbelianSheaf B X (fun {_ _} i hi hH => ?_)
    (fun M c hc hM hc' =>
      exists_isEssentiallyConstantWith_of_isConstructibleAbelianSheaf_colimit B X M c hc hM hc')
    F hF
  have := hi
  exact isConstructibleAbelianSheaf_of_mono B X (smallEtaleUnderlyingSetCommutes B X)
    (representableIsConstructibleSetSheaf B X) (hasFiniteRepresentableCover B X) i hH

end AlgebraicGeometry

end
