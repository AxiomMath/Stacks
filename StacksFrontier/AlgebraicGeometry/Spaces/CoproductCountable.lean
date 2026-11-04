module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.Coproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductAlgebraic
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Sheafification

/-!
# Countable coproducts of algebraic spaces

A big fppf site contains the coproduct of a countable family of its schemes, so the site, the
slice of it over a base scheme `S`, the category of algebraic spaces over `S` and every slice
of that category all have countable coproducts. In the first two cases the coproduct is
computed on underlying schemes; in the last two it is the coproduct of the underlying sheaves
of sets, which is an algebraic space by Stacks 02WQ.

Countability is exactly the hypothesis the size bound needs: the cutoff of a big fppf site is
a strong prelimit of uncountable cofinality, so it is closed under countable coproducts of
schemes but not under arbitrary ones.

## Main definitions

* `AlgebraicGeometry.Space.algebraicSpacesToSheaf` is the inclusion of the algebraic spaces
  over `S` into the sheaves of sets on the big fppf site over `S`; it is fully faithful and
  preserves fibre products.

## Main results

* `AlgebraicGeometry.BigFppfSite.hasColimitsOfShape_discrete` and
  `AlgebraicGeometry.BigFppfOver.hasColimitsOfShape_discrete`: countable coproducts in a big
  fppf site and in its slice over `S`.
* `AlgebraicGeometry.Space.createsColimitsOfShape_discrete_algebraicSpacesToSheaf`: the
  inclusion of the algebraic spaces into the sheaves creates countable coproducts. This is the
  statement that a countable coproduct of algebraic spaces is an algebraic space, in the form
  that also yields the universal property and the preservation statement.
* `AlgebraicGeometry.Space.hasColimitsOfShape_discrete_algebraicSpaces` and
  `AlgebraicGeometry.Space.hasColimitsOfShape_discrete_over`: countable coproducts of
  algebraic spaces over `S`, and of algebraic spaces over a fixed algebraic space.

## Implementation notes

The three existence statements are each an application of a creation result, so none of them
repeats the construction of the previous one. Closure of the site's cutoff under countable
coproducts of schemes
(`AlgebraicGeometry.schemeSizeBelow_isClosedUnderColimitsOfShape_discrete`) makes the
inclusion of the cutoff category into schemes create them; the projection of a slice creates
all colimits; and the inclusion of the algebraic spaces into the sheaves creates countable
coproducts because the coproduct sheaf is an algebraic space.

That last step is Stacks 02WQ (`AlgebraicGeometry.isAlgebraicSpace_coproduct`), whose
hypothesis that the chosen atlases of the members have a coproduct *inside* the site is met by
the countable coproducts of the site established here.

Coproducts of sheaves of sets on the big fppf site over `S` are recorded as an instance of
their own rather than left to the generic one for a site with sheafification: resolving that
one has to rediscover sheafification of `Type u`-valued presheaves on this site, which is the
expensive step of every search in this file.

The index type may live in any universe, provided it is `u`-small: a coproduct of `u`-schemes
indexed outside `Type u` need not exist, and `u`-smallness is what a family indexed by `Fin 3`
or by `ℕ` has. Only the closure statement for the site's cutoff is proved in `Type u` itself;
it is transported to a `u`-small index type along `CategoryTheory.Discrete.equivalence`, and
everything downstream is stated for the `u`-small index type directly.

## References

* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry

/-- A big fppf site has countable coproducts: its cutoff is closed under countable coproducts
of schemes, so the inclusion into schemes creates them. -/
noncomputable instance BigFppfSite.hasColimitsOfShape_discrete (B : BigFppfSite.{u})
    {I : Type v} [Small.{u} I] [Countable I] :
    HasColimitsOfShape (Discrete I) B.Schemes := by
  have : Countable (Shrink.{u} I) := Countable.of_equiv I (equivShrink.{u} I)
  have : (schemeSizeBelow B.cutoff).IsClosedUnderColimitsOfShape
      (Discrete (Shrink.{u} I)) :=
    schemeSizeBelow_isClosedUnderColimitsOfShape_discrete B.aleph0_lt_cutoff
      B.aleph0_lt_cutoff_cof Cardinal.mk_le_aleph0
  have : (schemeSizeBelow B.cutoff).IsClosedUnderColimitsOfShape (Discrete I) :=
    ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence
      (Discrete.equivalence (equivShrink.{u} I).symm)
  exact hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape B.inclusion

/-- The big fppf site over `S` has countable coproducts, computed on underlying schemes: the
projection of a slice creates colimits. -/
noncomputable instance BigFppfOver.hasColimitsOfShape_discrete (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {I : Type v} [Small.{u} I] [Countable I] :
    HasColimitsOfShape (Discrete I) (BigFppfOver B S hS) :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (Over.forget (B.obj hS))

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Sheaves of sets on the big fppf site over `S` have coproducts of every shape, as the
sheafification of the coproduct of presheaves. This is the generic instance for a site with
sheafification, recorded here so that searches in this file do not have to rediscover
sheafification of `Type u`-valued presheaves on this site. -/
noncomputable instance hasColimitsOfShape_discrete_sheaf {I : Type v} [Small.{u} I] :
    HasColimitsOfShape (Discrete I)
      (Sheaf (BigFppfOver.topology B S hS) (Type u)) :=
  ⟨fun _ => HasColimit.mk ⟨Sheaf.sheafifyCocone (colimit.cocone _),
    Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩⟩

/-- An algebraic space over `S`, regarded as a sheaf of sets on the big fppf site over `S`. -/
def algebraicSpacesToSheaf :
    AlgebraicSpaces B S hS ⥤ Sheaf (BigFppfOver.topology B S hS) (Type u) where
  obj X := ⟨X.obj, X.property.isSheaf⟩
  map f := ObjectProperty.homMk f.hom

/-- The inclusion of the algebraic spaces over `S` into the sheaves of sets is fully faithful:
both categories are full subcategories of the presheaves. -/
def algebraicSpacesToSheafFullyFaithful :
    (algebraicSpacesToSheaf B S hS).FullyFaithful where
  preimage f := ObjectProperty.homMk f.hom

instance : (algebraicSpacesToSheaf B S hS).Full :=
  (algebraicSpacesToSheafFullyFaithful B S hS).full

instance : (algebraicSpacesToSheaf B S hS).Faithful :=
  (algebraicSpacesToSheafFullyFaithful B S hS).faithful

/-- The inclusion of the algebraic spaces over `S` into the sheaves of sets preserves fibre
products: the fibre product of algebraic spaces is the fibre product of presheaves, and so is
the fibre product of sheaves. -/
noncomputable instance preservesLimitsOfShape_walkingCospan_algebraicSpacesToSheaf :
    PreservesLimitsOfShape WalkingCospan (algebraicSpacesToSheaf B S hS) := by
  refine preservesLimitsOfShape_walkingCospan_of_forall_isPullback fun X Y Z f g _ => ?_
  refine ⟨_, _, _, AlgebraicSpaces.isPullback_fiberProduct B S hS f g, ?_⟩
  exact IsPullback.of_map_of_faithful (sheafToPresheaf _ (Type u))
    (IsPullback.of_hasPullback f.hom g.hom)

/-- **A countable coproduct of algebraic spaces is an algebraic space**, in the form that also
records its universal property: the inclusion of the algebraic spaces over `S` into the
sheaves of sets on the big fppf site over `S` creates countable coproducts.

The coproduct sheaf is an algebraic space by Stacks 02WQ, whose hypothesis that the chosen
atlases of the members have a coproduct in the site is met by the countable coproducts of the
site. -/
noncomputable instance createsColimitsOfShape_discrete_algebraicSpacesToSheaf
    {I : Type v} [Small.{u} I] [Countable I] :
    CreatesColimitsOfShape (Discrete I) (algebraicSpacesToSheaf B S hS) := by
  classical
  refine ⟨fun {K} => ?_⟩
  let A := algebraicSpacesToSheaf B S hS
  let l := colimit.cocone (K ⋙ A)
  have hl : IsColimit l := colimit.isColimit (K ⋙ A)
  have hfan : IsColimit (Cofan.mk l.pt (fun i => l.ι.app ⟨i⟩) :
      Cofan (fun i => A.obj (K.obj ⟨i⟩))) := by
    refine IsColimit.ofIsoColimit ((IsColimit.precomposeHomEquiv
      (Discrete.natIsoFunctor (F := K ⋙ A)).symm l).symm hl) (Cocone.ext (Iso.refl _) ?_)
    rintro ⟨i⟩
    simp
  choose U a hsurj hetale using fun i : I => (K.obj ⟨i⟩).property.exists_atlas
  have halg : IsAlgebraicSpace B S hS l.pt.obj :=
    isAlgebraicSpace_coproduct B S hS (fun i => (K.obj ⟨i⟩).obj)
      (fun i => (K.obj ⟨i⟩).property) l.pt (fun i => l.ι.app ⟨i⟩) hfan
      U a hsurj hetale (∐ U) (Sigma.ι U) (coproductIsCoproduct U)
  exact createsColimitOfFullyFaithfulOfIso' hl ⟨l.pt.obj, halg⟩ (Iso.refl _)

/-- The algebraic spaces over `S` have countable coproducts. -/
noncomputable instance hasColimitsOfShape_discrete_algebraicSpaces
    {I : Type v} [Small.{u} I] [Countable I] :
    HasColimitsOfShape (Discrete I) (AlgebraicSpaces B S hS) :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape
    (algebraicSpacesToSheaf B S hS)

/-- The algebraic spaces over `S` with a morphism to a fixed algebraic space `Z` have countable
coproducts, computed as coproducts of algebraic spaces over `S`. The index type may live in
any universe, provided it is `u`-small. -/
noncomputable instance hasColimitsOfShape_discrete_over {I : Type v} [Small.{u} I] [Countable I]
    (Z : AlgebraicSpaces B S hS) : HasColimitsOfShape (Discrete I) (Over Z) :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (Over.forget Z)

end Space

end AlgebraicGeometry

end
