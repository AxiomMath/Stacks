module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineFlatChartDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleAtlasCriterion

/-!
# The étale atlas criterion, unconditionally

A sheaf on the big fppf site over a scheme `S` is an algebraic space over `S` as soon as it
admits a representable, surjective, étale morphism from an object of the site, and likewise as
soon as it admits one from an algebraic space over `S`. In particular the condition on the
diagonal in the definition of an algebraic space need not be checked.

`StacksFrontier.AlgebraicGeometry.Spaces.EtaleAtlasCriterion` proves both criteria conditional on

```
AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve B S hS
  (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType)
```

and on nothing else. That proposition is a theorem,
`AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft`, so
substituting it discharges both tags.

## Main results

* `AlgebraicGeometry.isAlgebraicSpace_of_surjective_etale_atlas`: a sheaf with a representable,
  surjective, étale atlas by an object of the site is an algebraic space over `S`.
* `AlgebraicGeometry.isAlgebraicSpace_of_relativelyRepresentable_surjective_etale`: a sheaf with
  a representable, surjective, étale cover by an algebraic space over `S` is an algebraic space
  over `S`.

## Implementation notes

Nothing is reproved here. The two statements below are the two theorems of
`StacksFrontier.AlgebraicGeometry.Spaces.EtaleAtlasCriterion` with their descent hypothesis
supplied, and the mathematics lives there and in the quotient theorem Stacks 02WW which that
file consumes.

The covering-sieve form of effective descent is the one to substitute, not the single-morphism
form `AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale`: the proof of Stacks 0BGQ
in `EtaleAtlasCriterion` passes through the diagonal of a quotient sheaf, which consumes the
covering-sieve form because an unbounded coproduct of objects of the site need not lie in the
site. The two propositions mention their property in both hypothesis and conclusion and so are
monotone in neither direction; they are independent statements, and it is the covering-sieve one
that is a theorem at the monomorphisms locally of finite type.

Representability of the cover in the second criterion is not a separate hypothesis: it is the
first component of `CategoryTheory.MorphismProperty.presheaf`, so each of the surjectivity and
étaleness hypotheses already carries it.

The hypothesis `HasSheafify (BigFppfOver.topology B S hS) (Type u)` of the conditional forms is
discharged by the instance `AlgebraicGeometry.hasSheafifyBigFppfOver`, so it is absent below; it
is a choice of universe for the quotient presheaf rather than an open assumption.

## References

* [Stacks Project, Tag 0BGQ](https://stacks.math.columbia.edu/tag/0BGQ)
* [Stacks Project, Tag 0BGR](https://stacks.math.columbia.edu/tag/0BGR)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 0BGQ.** A sheaf `F` on the big fppf site over `S` admitting a representable,
surjective, étale morphism `f : h_U ⟶ F` from an object `U` of the site is an algebraic space
over `S`.

The kernel pair `R = U ×_F U` of `f` is an object of the site with étale projections forming an
étale equivalence relation, so the quotient sheaf `U/R` is an algebraic space by Stacks 02WW;
both `F` and `U/R` are the coequalizer of the two projections in fppf sheaves of sets, hence
isomorphic. -/
@[stacks 0BGQ]
theorem isAlgebraicSpace_of_surjective_etale_atlas
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ F)
    (hsurj : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) f)
    (hetale : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) f) :
    IsAlgebraicSpace B S hS F :=
  isAlgebraicSpace_of_surjective_etale_atlas_of_descent B S hS hF U f hsurj hetale
    (Space.isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft B S hS)

/-- **Stacks 0BGR.** A sheaf `F` on the big fppf site over `S` admitting a representable,
surjective, étale morphism `a : G ⟶ F` from an algebraic space `G` over `S` is an algebraic space
over `S`.

A surjective étale atlas `h_U ⟶ G` of `G` by an object of the site is representable because `G`
has representable diagonal, and composing it with `a` gives an atlas of the same kind for `F`. -/
@[stacks 0BGR]
theorem isAlgebraicSpace_of_relativelyRepresentable_surjective_etale
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hG : IsAlgebraicSpace B S hS G)
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) (a : G ⟶ F)
    (hs : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) a)
    (he : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) a) :
    IsAlgebraicSpace B S hS F :=
  isAlgebraicSpace_of_relativelyRepresentable_surjective_etale_of_descent B S hS hG hF a hs he
    (Space.isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft B S hS)

end AlgebraicGeometry

end
