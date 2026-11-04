module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedChernSetup

/-!
# The data of a localized Chern class, and Situation 0GUJ over it

Conditions (1) and (2) of Situation 0GUJ of the Stacks Project, without its finiteness condition
(3): a scheme `X` locally of finite type over the base of chapter 42, a closed subscheme
`i : Z ⟶ X`, a degree `p`, and a perfect object `E` of the derived category of `X` which away
from `Z` is zero or a finite locally free module of rank `< p`. Remark 0GUK extends the localized
classes to such data whose Chern classes are defined.

Situation 0GUJ is then these data together with one of the four finiteness alternatives of its
condition (3), `Stacks.Chow.LocalizedSituation`, so that the classes of Remark 0GUK and those of
Situation 0GUJ are stated on the same data: a situation `S` has its data
`S.toLocalizedChernData`.

## Main definitions

* `Stacks.Chow.LocalizedChernData` — conditions (1) and (2) of Situation 0GUJ.
* `Stacks.Chow.LocalizedSituation` — Situation 0GUJ, as the data `Stacks.Chow.LocalizedChernData`
  with condition (3).

## Implementation notes

`Stacks.Chow.LocalizedChernSituation` states the same situation as one flat structure.
`Stacks.Chow.LocalizedSituation` extends the data instead, which is the form the localized classes
of Remark 0GUK need.

## References

* [Stacks Project, Tag 0GUJ](https://stacks.math.columbia.edu/tag/0GUJ)
* [Stacks Project, Tag 0GUK](https://stacks.math.columbia.edu/tag/0GUK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open AlgebraicGeometry.RingedSpace.PseudoCoherence

universe u

namespace Stacks.Chow

attribute [local instance] HasDerivedCategory.standard

/-- **The data of a localized Chern class**: a scheme locally of finite type over the base of
chapter 42, a closed subscheme, a degree, and a perfect object of the derived category of the
ambient scheme which away from the closed subscheme is zero or a finite locally free module of
rank below the degree. These are conditions (1) and (2) of Situation 0GUJ, without its finiteness
condition (3); Remark 0GUK extends the localized classes to such data whose Chern classes are
defined. -/
structure LocalizedChernData where
  /-- The base situation of chapter 42, with its dimension function. -/
  base : ChowSituation.{u}
  /-- The ambient scheme. -/
  X : Scheme.{u}
  /-- Its structure morphism over the base. -/
  a : X ⟶ base.S
  /-- The ambient scheme is locally of finite type over the base. -/
  [locallyOfFiniteType : LocallyOfFiniteType a]
  /-- The closed subscheme along which the classes are localized. -/
  Z : Scheme.{u}
  /-- Its inclusion into the ambient scheme. -/
  i : Z ⟶ X
  /-- The inclusion is a closed immersion. -/
  [isClosedImmersion : IsClosedImmersion i]
  /-- The object of the derived category the classes are attached to. -/
  E : DerivedCategory (OXMod.{u, u, u} X.toRingedSpace)
  /-- The degree of the Chern class. -/
  p : ℕ
  /-- `E` is a perfect object: Stacks 0GUJ (1). -/
  perfect : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E
  /-- On the complement of the closed subscheme `E` is zero, or else a finite locally free
  module of rank `< p` placed in cohomological degree `0`: Stacks 0GUJ (2). -/
  restriction :
    letI U : Opens X :=
      ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    letI F := Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (X.toRingedSpace.ofRestrict U.isOpenEmbedding)
    IsZero (F.obj E) ∨
      ∃ M : OXMod.{u, u, u} (X.toRingedSpace.restrict U.isOpenEmbedding),
        IsFiniteLocallyFreeOfRankLT M p ∧
          Nonempty (F.obj E ≅ (DerivedCategory.singleFunctor _ 0).obj M)

attribute [instance] LocalizedChernData.locallyOfFiniteType LocalizedChernData.isClosedImmersion

/-- The standing situation for the localized Chern classes and localized Chern character components
of chapter 42 of the Stacks Project: a scheme locally of finite type over the base, a closed
subscheme, a perfect object of the derived category of the ambient scheme which away from the
closed subscheme is zero or a finite locally free module of rank below the chosen degree (the data
`Stacks.Chow.LocalizedChernData`), and one of the four finiteness alternatives of the source. -/
@[stacks 0GUJ]
structure LocalizedSituation extends LocalizedChernData.{u} where
  /-- One of the four finiteness alternatives of Stacks 0GUJ (3): the ambient scheme is
  quasi-compact, or its irreducible components are, or `E` is represented by a locally bounded
  complex of finite locally free modules, or `E` is the pullback of a perfect object on a scheme
  over the base with quasi-compact irreducible components. -/
  finiteness :
    CompactSpace X ∨
      (∀ C ∈ irreducibleComponents X, IsCompact C) ∨
      (∃ P : CochainComplex (OXMod.{u, u, u} X.toRingedSpace) ℤ,
        IsLocallyBoundedFiniteLocallyFree P ∧ Nonempty (DerivedCategory.Q.obj P ≅ E)) ∨
      (∃ (X' : Scheme.{u}) (a' : X' ⟶ base.S) (f : X ⟶ X')
          (E' : DerivedCategory (OXMod.{u, u, u} X'.toRingedSpace)),
        LocallyOfFiniteType a' ∧ f ≫ a' = a ∧
          Cohomology.PerfectComplexes.IsPerfect (X := X'.toRingedSpace) E' ∧
          Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            f.toLRSHom.toShHom).obj E' ≅ E) ∧
          ∀ C ∈ irreducibleComponents X', IsCompact C)

end Stacks.Chow

end
