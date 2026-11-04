module

public import StacksFrontier.Homology.DerivedIndexing.Composite
public import
  StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.SingleRightDerivedUnitFunctorNaturality

/-!
# The canonical map `(Pℱ)[0] ⟶ RP(ℱ[0])` is functorial in `P`

For an additive functor `P : 𝒜 ⥤ ℬ` with `𝒜` having enough injectives,
`Stacks.DerivedIndexing.rightDerivedPlusUnitSingle P` is the canonical map
`(Pℱ)[0] ⟶ RP(ℱ[0])` in `D⁺(ℬ)` out of which the degreewise comparison
`Stacks.DerivedIndexing.rightDerivedPlusEdge` of a composite of right derived functors is built.
This file records its two functorialities in `P`: naturality against a transformation of the
functor being derived, and compatibility with composition.

Neither is new mathematics in this development. `Stacks.Cohomology.singleRightDerivedUnit` is the
*same transformation* — the two definitions agree symbol for symbol, which is
`rightDerivedPlusUnitSingle_eq_singleRightDerivedUnit` below — and both functorialities were
proved for that spelling, as `Stacks.Cohomology.singleRightDerivedUnit_fac_app` and
`Stacks.Cohomology.singleRightDerivedUnit_comp_app`. What this file adds is the two statements in
the spelling the `ℤ`-indexing uses: against
`Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans` rather than an arbitrary transformation
of right derived functors satisfying the characterising factorization, and against
`Stacks.DerivedIndexing.rightDerivedPlusCompTrans` rather than
`CategoryTheory.Functor.rightDerivedFunctorPlusComp`.

## Main results

* `Stacks.DerivedIndexing.rightDerivedPlusUnitSingle_eq_singleRightDerivedUnit`: **the two
  spellings of the canonical map are one transformation.**
* `Stacks.DerivedIndexing.rightDerivedPlusUnitSingle_natTrans_app`: **the canonical map is
  natural in the functor being derived**, against
  `Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans`.
* `Stacks.DerivedIndexing.rightDerivedPlusUnitSingle_comp_app`: **the canonical map of a
  composite is the two canonical maps**, read through the comparison
  `Stacks.DerivedIndexing.rightDerivedPlusCompTrans` of [Stacks, Tag 05T2].

## Implementation notes

The second statement is `Stacks.Cohomology.singleRightDerivedUnit_comp_app` with no proof step at
all: `Stacks.DerivedIndexing.rightDerivedPlusCompTrans` and
`CategoryTheory.Functor.rightDerivedFunctorPlusComp` are the same descent along the same unit, as
`CategoryTheory.Functor.rightDerivedPlusCompTrans_eq` records, so the two statements are the same
proposition up to unfolding two definitions. It is restated because `rw` does not cross that
boundary and the consumers of the degreewise comparison are written with the first spelling.

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2)
* [Stacks Project, Tag 01F8](https://stacks.math.columbia.edu/tag/01F8)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w w' w'' v v' v'' u u' u''

namespace Stacks.DerivedIndexing

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section Functoriality

variable {C : Type u} {D : Type u'} {E : Type u''}
  [Category.{v} C] [Category.{v'} D] [Category.{v''} E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D] [HasDerivedCategory.{w''} E]
  [EnoughInjectives C]

/-- **The two spellings of the canonical map `(Pℱ)[0] ⟶ RP(ℱ[0])` are one transformation.**
`Stacks.DerivedIndexing.rightDerivedPlusUnitSingle` and
`Stacks.Cohomology.singleRightDerivedUnit` are both the unit of `RP` on the complexes
concentrated in degree zero, read through the identification of `P(ℱ[0])` with `(Pℱ)[0]` and the
identification of `ℱ[0]` with its image from `K⁺(𝒜)`; they are assembled out of the same three
factors in the same order. -/
theorem rightDerivedPlusUnitSingle_eq_singleRightDerivedUnit (P : C ⥤ D) [P.Additive] :
    rightDerivedPlusUnitSingle P = Stacks.Cohomology.singleRightDerivedUnit P :=
  rfl

/-- **The canonical map `(Pℱ)[0] ⟶ RP(ℱ[0])` is natural in the functor being derived.** For a
transformation `τ : F ⟶ G` of additive functors, `τ` placed in degree zero followed by the
canonical map of `G` is the canonical map of `F` followed by the induced map
`Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans τ` of right derived functors.

This is `Stacks.Cohomology.singleRightDerivedUnit_fac_app` at
`ρ = rightDerivedFunctorPlusNatTrans τ`, whose characterising factorization is
`Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans_app`. -/
theorem rightDerivedPlusUnitSingle_natTrans_app {F G : C ⥤ D} [F.Additive] [G.Additive]
    (τ : F ⟶ G) (X : C) :
    (DerivedCategory.Plus.singleFunctor D 0).map (τ.app X) ≫
        (rightDerivedPlusUnitSingle G).app X =
      (rightDerivedPlusUnitSingle F).app X ≫
        (rightDerivedFunctorPlusNatTrans τ).app
          ((DerivedCategory.Plus.singleFunctor C 0).obj X) :=
  Stacks.Cohomology.singleRightDerivedUnit_fac_app F G τ
    (Functor.mapHomotopyCategoryPlusNatTrans τ) (rightDerivedFunctorPlusNatTrans τ) rfl
    (rightDerivedFunctorPlusNatTrans_app τ) X

/-- **The canonical map `(Pℱ)[0] ⟶ RP(ℱ[0])` of a composite is the two canonical maps.** For
additive `P : 𝒜 ⥤ ℬ` and `Q : ℬ ⥤ 𝒞`, the canonical map of `Q ∘ P` at `ℱ`, followed by the
comparison `R(Q ∘ P) ⟶ RP ⋙ RQ` of [Stacks, Tag 05T2], is the canonical map of `Q` at `Pℱ`
followed by `RQ` of the canonical map of `P` at `ℱ`.

Nothing is assumed beyond additivity and enough injectives; in particular the comparison need
not be invertible. -/
theorem rightDerivedPlusUnitSingle_comp_app (P : C ⥤ D) (Q : D ⥤ E) [P.Additive] [Q.Additive]
    [EnoughInjectives D] (X : C) :
    (rightDerivedPlusUnitSingle (P ⋙ Q)).app X ≫
        (rightDerivedPlusCompTrans P Q).app ((DerivedCategory.Plus.singleFunctor C 0).obj X) =
      (rightDerivedPlusUnitSingle Q).app (P.obj X) ≫
        Q.rightDerivedFunctorPlus.map ((rightDerivedPlusUnitSingle P).app X) :=
  Stacks.Cohomology.singleRightDerivedUnit_comp_app P Q X

end Functoriality

end Stacks.DerivedIndexing

end
