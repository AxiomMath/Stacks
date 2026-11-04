module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineBaseCoveringSieveDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafAlgebraicGlueing

/-!
# The quotient of an étale equivalence relation, from descent over the affine base objects

`AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_relation_of_diagDescent` — the quotient
sheaf of an étale equivalence relation on an *arbitrary* object of the big fppf site of `S` is an
algebraic space — carries one hypothesis, effective descent along the covering sieves of the site
at the monomorphisms locally of finite type. This file weakens that hypothesis to a statement about
affine base objects and chosen fppf covering families.

Two reductions do it, neither costing a hypothesis. The base object becomes affine by
`AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_of_affineBase_of_le_monomorphisms`,
whose size hypothesis is free below the monomorphisms; this is the reduction already applied to
the *affine* case of Stacks 0265 in
`StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafChartFromDiagonal`. The covering sieve then
becomes a chosen covering family by
`AlgebraicGeometry.BigFppfOver.exists_isCovering_of_mem_topology`, which is step 1 of Stacks
02W8 in the shape of
`AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_of_isCovering`.

## Main definitions

* `AlgebraicGeometry.Space.IsEffectiveDescentOnAffineBase`: effective descent for morphisms
  with a given property over the *affine* objects of the big fppf site of `S`, along the chosen
  fppf covering families of such an object.

## Main results

* `AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_of_isEffectiveDescentOnAffineBase`:
  for a property below the monomorphisms, descent over the affine base objects implies descent
  along every covering sieve over every base object.
* `AlgebraicGeometry.Space.isAlgebraicSpace_quotient_of_affineBaseDescent`: the quotient sheaf
  of an étale equivalence relation on an arbitrary object of the site is an algebraic space,
  conditional on descent over the affine base objects alone.
* `AlgebraicGeometry.Space.isAlgebraicSpace_actionQuotient_of_affineBaseDescent`: the same for
  the quotient by a group action.

## Implementation notes

The hypothesis is taken at the monomorphisms locally of finite type rather than at the property
of Stacks 02W8, because that is the only instance the two theorems weakened here consume: their
chart is obtained from their diagonal, by
`AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_of_diagDescent`. Being below the
monomorphisms is also exactly what makes the affine-base reduction unconditional, through
`AlgebraicGeometry.Scheme.size_le_of_mono`; the property of Stacks 02W8 is not below the
monomorphisms, and its own affine-base reduction needs a regular cutoff or a size bound
instead.

Replacing the covering sieve by a family is free in this direction and is worth doing because a
family carries geometry: joint surjectivity and the flatness and local finite presentation of
its members, by
`AlgebraicGeometry.BigFppfSite.jointlySurjective_flat_locallyOfFinitePresentation_of_isCovering`.
A saturated covering sieve carries none of that. Together with affineness — hence
quasi-compactness — of the base, this is the shape in which the remaining steps of Stacks 02W8
are to be proved.

## References

* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 0265](https://stacks.math.columbia.edu/tag/0265)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 02Z2](https://stacks.math.columbia.edu/tag/02Z2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Morphisms with property `P` **descend effectively over the affine base objects** of the big
fppf site of `S` when the following holds. Let `f : X ⟶ Y` be a morphism of presheaves with `X`
and `Y` sheaves, let `h : yoneda.obj a ⟶ Y` be a morphism from a representable presheaf whose
object `a` is affine, and let `E` be a chosen fppf covering family of `a`. If the base change of
`f` along `yoneda.map (E.f i) ≫ h` is representable with `P` for every member of the family, then
so is the base change of `f` along `h`.

Compared with `AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve` two quantifiers are
restricted and nothing else changes: the base object is affine, and the covering is a chosen
family rather than a saturated covering sieve. For a property below the monomorphisms the two
predicates are in fact equivalent, by
`AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_of_isEffectiveDescentOnAffineBase`
in one direction and by restriction in the other. -/
def IsEffectiveDescentOnAffineBase (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u}) : Prop :=
  ∀ ⦃X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (f : X ⟶ Y),
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) X →
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y →
    ∀ ⦃a : BigFppfOver B S hS⦄ (h : yoneda.obj a ⟶ Y) (E : PreZeroHypercover.{u + 1} a),
      IsAffine ((BigFppfOver.toScheme B S hS).obj a) →
      BigFppfOver.IsCovering B S hS ⟨a, E⟩ →
      (∀ i, (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
        (pullback.snd f (yoneda.map (E.f i) ≫ h))) →
      (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f h)

/-- **Effective descent over the affine base objects implies effective descent along every
covering sieve**, for a property below the monomorphisms which is Zariski local on the target and
satisfies fppf descent.

The base object becomes affine by
`AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_of_affineBase_of_le_monomorphisms`,
whose size hypothesis is free below the monomorphisms. The covering sieve of the affine base then
contains a chosen covering family, by
`AlgebraicGeometry.BigFppfOver.exists_isCovering_of_mem_topology`, and the hypothesis of the
descent problem restricts to it for free, being a condition on the arrows of the sieve. -/
theorem isEffectiveDescentAlongCoveringSieve_of_isEffectiveDescentOnAffineBase
    {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtTarget P]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    (hPmono : P ≤ MorphismProperty.monomorphisms Scheme.{u})
    (H : IsEffectiveDescentOnAffineBase B S hS P) :
    IsEffectiveDescentAlongCoveringSieve B S hS P := by
  refine isEffectiveDescentAlongCoveringSieve_of_affineBase_of_le_monomorphisms hPmono ?_
  intro X Y f hX hY a h T haff hTmem hall
  obtain ⟨E, hE, hET⟩ := BigFppfOver.exists_isCovering_of_mem_topology B S hS hTmem
  exact H f hX hY h E haff hE fun i ↦ hall (E.f i) (hET i)

/-- **Effective descent at the monomorphisms locally of finite type, from its restriction to the
affine base objects.** This is the hypothesis of
`AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_relation_of_diagDescent`, and the
property is below the monomorphisms, so the reduction asks nothing of the site's cutoff. -/
theorem IsEffectiveDescentOnAffineBase.monomorphisms_inf_locallyOfFiniteType
    (H : IsEffectiveDescentOnAffineBase B S hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType)) :
    IsEffectiveDescentAlongCoveringSieve B S hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType) :=
  have _h1 := monomorphisms_inf_locallyOfFiniteType_isZariskiLocalAtTarget.{u}
  have _h2 := monomorphisms_inf_locallyOfFiniteType_descendsAlong_fppf.{u}
  isEffectiveDescentAlongCoveringSieve_of_isEffectiveDescentOnAffineBase
    (fun _ _ _ hg ↦ hg.1) H

/-- **Stacks 02WW, the algebraic-space property, from descent over the affine base objects.**
The quotient sheaf of an étale equivalence relation on an object `U` of the big fppf site of `S`
is an algebraic space over `S`, with no affineness assumed of `U`, conditional on effective
descent at the monomorphisms locally of finite type over the *affine* objects of the site and on
nothing else. No cardinal hypothesis and no hypothesis on the site's cutoff is used.

This is `AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_relation_of_diagDescent` with
its hypothesis weakened; it is to the arbitrary-object case what
`AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_of_affineBase` is to the affine case.
The hypothesis is undischarged, so no attribute is placed. -/
theorem isAlgebraicSpace_quotient_of_affineBaseDescent (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {R U : BigFppfOver B S hS} (s t : R ⟶ U)
    [Stacks.Groupoids.IsEtaleEquivalenceRelation (relation B S hS s t)]
    (H : IsEffectiveDescentOnAffineBase B S hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType)) :
    IsAlgebraicSpace B S hS
      (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) (relation B S hS s t)).obj :=
  isAlgebraicSpace_quotientSheaf_relation_of_diagDescent B S hS s t
    H.monomorphisms_inf_locallyOfFiniteType

/-- **Stacks 02Z2, the algebraic-space property, from descent over the affine base objects.** The
quotient of an object `V` of the big fppf site of `S` by the action of a group whose stabilizers
act faithfully on fixed residue fields is an algebraic space over `S`, conditional on effective
descent at the monomorphisms locally of finite type over the *affine* objects of the site and on
nothing else.

This is `AlgebraicGeometry.Space.isAlgebraicSpace_actionQuotient` with its hypothesis weakened in
the same way. The hypothesis is undischarged, so no attribute is placed. -/
theorem isAlgebraicSpace_actionQuotient_of_affineBaseDescent {S : Scheme.{u}} (G : Type v)
    [Group G] [Small.{u} G] (B : BigFppfSite.{u}) (hS : B.Contains S) (V : BigFppfOver B S hS)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (a : G →* Aut (underlyingOver B hS V))
    (ha : ActsNontriviallyOnFixedResidueFields (underlyingOver B hS V) G a)
    (H : IsEffectiveDescentOnAffineBase B S hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType)) :
    IsAlgebraicSpace B S hS (actionQuotient G B hS V a) :=
  isAlgebraicSpace_actionQuotient G B hS V a ha H.monomorphisms_inf_locallyOfFiniteType

end AlgebraicGeometry.Space

end
