module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardEtaleBaseChange

/-!
# The transported structure sheaf of an étale restriction is the structure sheaf

Let `h : U ⟶ V` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  Restriction of sheaves of sets along small étale postcomposition with `h`,
`AlgebraicGeometry.Space.smallEtaleSetRestriction`, preserves finite products, so a sheaf of
rings on the small étale site of `V` can be carried along it by
`Stacks.Sheaves.ToposPullback.pullbackRingSheaf`: the underlying sheaf of sets is restricted and
the ring operations are transported through the chosen finite products of the category of
sheaves of sets.  For the structure sheaf `𝒪_V` the result has the *same* underlying sheaf of
sets as `𝒪_U`, on the nose, because postcomposition leaves the underlying scheme of a chart
unchanged, and the two ring structures also agree: the identity on sections is an isomorphism of
sheaves of rings

`pullbackRingSheaf (smallEtaleSetRestriction h) 𝒪_V ≅ 𝒪_U`.

That comparison is the piece the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleInverseImageStructureSheaf.lean` record as still owed
by Stacks' Equation 03LW, the abuse of notation `G|_{U_étale} = h^*G = h_{small}^{-1}G`: the
module-level clause of Stacks 03LV needs the ring sheaf over which
`Stacks.Sheaves.ToposPullback.pullbackModuleFunctor` is indexed to be identified with `𝒪_U`.

**This file is a named specialisation, not a construction.**  The general comparison is proved,
for an arbitrary continuous functor of sites and an arbitrary sheaf of rings, as
`Stacks.Sheaves.ToposPullback.restrictionRingIso`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ToposRingImageAdjunction.lean`).  Everything
below is that isomorphism instantiated at small étale postcomposition and the structure sheaf,
plus the two `rfl` facts that make the instantiation land on `𝒪_U` rather than on a restriction
of `𝒪_V` spelt differently.

## Main definitions

* `AlgebraicGeometry.Space.etaleRestrictionRingSheafIso` is the isomorphism of sheaves of rings.
* `AlgebraicGeometry.Space.etaleRestrictionRingSheafHom` is its forward map, the identity on
  sections.

## Main results

* `AlgebraicGeometry.Space.smallEtaleSetRestriction_comp_sectionsFunctor`: restriction followed
  by sections over a chart `W` of `U` is sections over the composite chart of `V`, on the nose.
* `AlgebraicGeometry.Space.ringSheaf_pullbackRingSheaf_smallEtaleSetRestriction`: the underlying
  sheaf of sets of the transported ring sheaf is the underlying sheaf of sets of `𝒪_U`, by `rfl`.
* `AlgebraicGeometry.Space.forgetRing_etaleRestrictionRingSheafHom` and
  `AlgebraicGeometry.Space.forgetRing_etaleRestrictionRingSheafIso_inv`: both the forward map and
  the inverse are the identity on underlying sheaves of sets.  The second is the one the
  module-level step needs, since it restricts scalars along the inverse.
* `AlgebraicGeometry.Space.etaleRestrictionRingSheafIso_hom`: the forward map of the isomorphism
  is that comparison, so no choice is made.

## Implementation notes

The ring structure that `Stacks.Sheaves.ToposPullback.pullbackRingSheaf` puts on sections is
`CategoryTheory.Sheaf.ringObjRing`, whose operations are the internal ring operations of `𝒪_V`
read through the finite-product-preserving functor
`smallEtaleSetRestriction h hh ⋙ CategoryTheory.Sheaf.sectionsFunctor _ W`.  `rfl`
does *not* identify the two sheaves of rings as written — the elaborator reports that it will
not unfold `CategoryTheory.Limits.getLimitCone`, which is an exposure fact about `rfl` at its
transparency setting under the module system and not a proof that the two are not definitionally
equal.  Either way a comparison morphism is needed, which is what the general
`Stacks.Sheaves.ToposPullback.restrictionRingIso` supplies.

What makes that general isomorphism apply here with no work is that the transporting functor is
definitionally a sections functor: restriction followed by sections over `W` is sections over
`(smallEtalePostcomp h hh).obj W`, because restriction of a sheaf is reindexing of its sections.
So the transported operations are literally the operations of `𝒪_V` read at the composite chart,
and the four computation rules `CategoryTheory.Sheaf.sectionsFunctor_map_ringAddHom`,
`..._ringMulHom`, `..._ringZeroHom` and `..._ringOneHom` identify them with the direct ones;
those four are exactly the four field proofs of
`Stacks.Sheaves.ToposPullback.restrictionRingHom`.  Naturality is not one of its fields; it
lives in the natural transformation underlying
`Stacks.Sheaves.ToposPullback.restrictionRingIso`, where it is proved by `rfl`.

The sibling rule `CategoryTheory.Sheaf.sectionsFunctor_map_ringNegHom` is not needed by
either file: a `RingHom` derives negation from addition.

`AlgebraicGeometry.Space.smallEtaleSetRestriction` is a reducible `abbrev` for
`(smallEtalePostcomp h hh).sheafPushforwardContinuous (Type u) _ _`, which is the shape the
general isomorphism is stated at, so the instantiation needs no transport.

**Relation to `h⁻¹𝒪_V ≅ 𝒪_U`.**
`AlgebraicGeometry.Space.isIso_fSharpInverseImage_of_isEtale` and
`AlgebraicGeometry.Space.etaleInverseImageStructureSheafIso` are Stacks 03LV's first clause:
the inverse image of `𝒪_V` along the *morphism of small étale topoi* is `𝒪_U`.  That is a
different object and a different map from the one here — the inverse image of the topos morphism
is only isomorphic to restriction, by
`AlgebraicGeometry.Space.smallToposMorphismTypeU_inverseImageIso`, and on the structure sheaf
that isomorphism is the structure map of `h`, not the identity on sections.  The module-level
step of Equation 03LW needs both: the topos-morphism form to rewrite
`AlgebraicGeometry.Space.modulePullback`, and the identity-on-sections form below to land the
result on `AlgebraicGeometry.Space.etaleModulePullback`, whose sections are the restricted ones
on the nose.

**What is still owed for Equation 03LW.**  The remaining step is the module analogue: that the
transported addition and scalar action on the sections of
`Stacks.Sheaves.ToposPullback.pullbackModuleObj` are the direct ones, so that
`pullbackModuleFunctor (smallEtaleSetRestriction h hh) 𝒪_V` followed by restriction of scalars
along `(etaleRestrictionRingSheafIso h hh).inv` is
`AlgebraicGeometry.Space.etaleModulePullback h hh`.  The computation rules for that step exist in
the same place and in the same shape — `CategoryTheory.Sheaf.sectionsFunctor_map_moduleAddHom`
and `CategoryTheory.Sheaf.sectionsFunctor_map_moduleSMulHom` — so the pattern is the one
`restrictionRingHom` uses; it is not supplied in this file.  After it,
`AlgebraicGeometry.Space.modulePullback` is identified with `etaleModulePullback` (the transported
extension of scalars being along an isomorphism, by
`AlgebraicGeometry.Space.isIso_fSharpInverseImage_of_isEtale`), the adjunction
`AlgebraicGeometry.Space.modulePullbackAdjPushforward` becomes an adjunction for the étale
restriction, and its unit is the first arrow of the exact sequence of Stacks 03M8.

**No new global instance.**  `AlgebraicGeometry.Space.isIso_etaleRestrictionRingSheafHom` is a
`theorem`, by convention; it is one projection off the isomorphism, so a
consumer that needs it in instance position supplies it with `have` at no cost.  The
precedent is the pair of theorems at
`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentGrothendieck.lean:232,239`.

**No attribute.**  Neither Stacks 03LV nor Equation 03LW asserts this: it is an artefact of the
way inverse images of sheaves of modules are constructed in this development, where the ring
structure on the inverse image of a sheaf of rings is transported through chosen products rather
than restricted.  The source draws no such distinction.  Equation 03LW and Stacks 03LQ are both
`kind: equation` in the audit, which is the genre this development does not tag; and Stacks 03LV
is a lemma whose first clause already carries two part-stringed sites at
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleInverseImageStructureSheaf.lean:144,187`, while this
file states a step *toward* its second clause and not that clause, so no part string is earned.

**Universes.**  Everything is at the universe `u` of the structure rings, which is where
`AlgebraicGeometry.Space.modulePullback` and `AlgebraicGeometry.Space.modulePushforward` live.
`Stacks.Sheaves.ToposPullback.pullbackRingSheaf` is given all six of its universes explicitly in
the type ascriptions below; without them they default to `0` and every argument mismatches.
Pinning them is one of the two reasons this named specialisation exists, the other being that
the module-level step of Equation 03LW will look for the comparison in this namespace.
No `set_option` appears in this file.

## References

* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
-/

@[expose] public section

open CategoryTheory
open Stacks.Sheaves.ToposPullback CategoryTheory.Sheaf

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : AlgebraicSpaces B S hS}

/-- Restriction of sheaves of sets along small étale postcomposition with `h : U ⟶ V`, followed
by sections over a chart `W` of `U`, is sections over the composite chart
`(smallEtalePostcomp h hh).obj W` of `V`.

Restriction of a sheaf along a functor of sites is reindexing of its sections, so this holds on
the nose.  It is why the transported ring operations are literally the ring operations of the
structure sheaf of `V`, and hence why
`Stacks.Sheaves.ToposPullback.restrictionRingIso` applies here. -/
theorem smallEtaleSetRestriction_comp_sectionsFunctor (h : U ⟶ V) (hh : IsEtale B S hS h.hom)
    (W : (SmallEtale B S hS U.1)ᵒᵖ) :
    smallEtaleSetRestriction B S hS h hh ⋙
        sectionsFunctor (SmallEtale.topology B S hS U.1) W =
      sectionsFunctor (SmallEtale.topology B S hS V.1)
        (Opposite.op ((smallEtalePostcomp B S hS h hh).obj W.unop)) :=
  rfl

/-- The underlying sheaf of sets of the transport of the structure sheaf of `V` along small
étale restriction is the underlying sheaf of sets of the structure sheaf of `U`.

Both are the restriction along small étale postcomposition of the sheaf of regular functions of
`V`, and postcomposition leaves the underlying scheme of a chart unchanged, so this holds by
`rfl`.  It is what makes the isomorphism below land on `𝒪_U`. -/
theorem ringSheaf_pullbackRingSheaf_smallEtaleSetRestriction (h : U ⟶ V)
    (hh : IsEtale B S hS h.hom) :
    ringSheaf (pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS U.1)
        (smallEtaleSetRestriction B S hS h hh) (structureRingSheaf B S hS V)) =
      structureSetSheaf B S hS U :=
  rfl

/-- **The transported structure sheaf of an étale restriction is the structure sheaf.**  For an
étale morphism `h : U ⟶ V` of algebraic spaces, the transport of `𝒪_V` along restriction of
sheaves of sets to the small étale site of `U` is `𝒪_U`, as sheaves of rings, by the identity on
sections.

This is `Stacks.Sheaves.ToposPullback.restrictionRingIso` — the same statement for an arbitrary
continuous functor of sites and an arbitrary sheaf of rings — instantiated at small étale
postcomposition with `h` and at the structure sheaf of `V`.  Nothing is constructed here; what
the named form adds is the six explicit universes of
`Stacks.Sheaves.ToposPullback.pullbackRingSheaf` and the identification of the target with
`AlgebraicGeometry.Space.structureRingSheaf`, which holds because restricting the sheaf of
regular functions along postcomposition leaves it unchanged. -/
noncomputable def etaleRestrictionRingSheafIso (h : U ⟶ V) (hh : IsEtale B S hS h.hom) :
    pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS U.1)
        (smallEtaleSetRestriction B S hS h hh) (structureRingSheaf B S hS V) ≅
      structureRingSheaf B S hS U :=
  restrictionRingIso (SmallEtale.topology B S hS U.1) (SmallEtale.topology B S hS V.1)
    (smallEtalePostcomp B S hS h hh) (structureRingSheaf B S hS V)

/-- The forward map of `AlgebraicGeometry.Space.etaleRestrictionRingSheafIso`: the identity on
sections, read as a morphism of sheaves of rings. -/
noncomputable def etaleRestrictionRingSheafHom (h : U ⟶ V) (hh : IsEtale B S hS h.hom) :
    pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS U.1)
        (smallEtaleSetRestriction B S hS h hh) (structureRingSheaf B S hS V) ⟶
      structureRingSheaf B S hS U :=
  (etaleRestrictionRingSheafIso B S hS h hh).hom

/-- The forward map of `AlgebraicGeometry.Space.etaleRestrictionRingSheafIso` is
`AlgebraicGeometry.Space.etaleRestrictionRingSheafHom`.

This holds by `Eq.refl`, the forward map being that morphism by definition, so the lemma
records the API shape rather than establishing anything: canonicity of the isomorphism comes
from its definition as `Stacks.Sheaves.ToposPullback.restrictionRingIso`, not from here. -/
theorem etaleRestrictionRingSheafIso_hom (h : U ⟶ V) (hh : IsEtale B S hS h.hom) :
    (etaleRestrictionRingSheafIso B S hS h hh).hom =
      etaleRestrictionRingSheafHom B S hS h hh :=
  rfl

/-- The comparison `AlgebraicGeometry.Space.etaleRestrictionRingSheafHom` is the *identity* on
underlying sheaves of sets, not merely an isomorphism.

This is `Stacks.Sheaves.ToposPullback.restrictionRingIso_hom_ringSheafMap`. -/
theorem forgetRing_etaleRestrictionRingSheafHom (h : U ⟶ V) (hh : IsEtale B S hS h.hom) :
    (sheafCompose (SmallEtale.topology B S hS U.1) (forget RingCat.{u})).map
        (etaleRestrictionRingSheafHom B S hS h hh) = 𝟙 (structureSetSheaf B S hS U) :=
  restrictionRingIso_hom_ringSheafMap (SmallEtale.topology B S hS U.1)
    (SmallEtale.topology B S hS V.1) (smallEtalePostcomp B S hS h hh)
    (structureRingSheaf B S hS V)

/-- The *inverse* of `AlgebraicGeometry.Space.etaleRestrictionRingSheafIso` is also the identity
on underlying sheaves of sets.

This is `Stacks.Sheaves.ToposPullback.restrictionRingIso_inv_ringSheafMap`.  It is the direction
the module-level step of Equation 03LW consumes, since that step restricts scalars along the
inverse; an isomorphism produced from a reflection-of-isomorphisms argument instead would have an
inverse that nothing describes. -/
theorem forgetRing_etaleRestrictionRingSheafIso_inv (h : U ⟶ V) (hh : IsEtale B S hS h.hom) :
    (sheafCompose (SmallEtale.topology B S hS U.1) (forget RingCat.{u})).map
        (etaleRestrictionRingSheafIso B S hS h hh).inv = 𝟙 (structureSetSheaf B S hS U) :=
  restrictionRingIso_inv_ringSheafMap (SmallEtale.topology B S hS U.1)
    (SmallEtale.topology B S hS V.1) (smallEtalePostcomp B S hS h hh)
    (structureRingSheaf B S hS V)

/-- The comparison `AlgebraicGeometry.Space.etaleRestrictionRingSheafHom` is an isomorphism, it
being the forward map of one.

This is a `theorem` and not an `instance`: a consumer that needs it in instance position
supplies it with `have`.  See the implementation notes. -/
theorem isIso_etaleRestrictionRingSheafHom (h : U ⟶ V) (hh : IsEtale B S hS h.hom) :
    IsIso (etaleRestrictionRingSheafHom B S hS h hh) :=
  (etaleRestrictionRingSheafIso B S hS h hh).isIso_hom

end AlgebraicGeometry.Space

end
