module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSections

/-!
# Morphisms of sets out of the sheafification of a presheaf of abelian groups

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let `A` be
a presheaf of abelian groups on its small étale site, at the universe of the objects of that
site — the universe in which the site admits sheafification of presheaves of modules, by
`AlgebraicGeometry.Space.moduleHasWeakSheafify`.  Then a morphism of presheaves of *sets* from
`A` into a sheaf of sets extends uniquely over the sheafification of `A`:

`Hom(A^# , T) ≃ Hom(A, T)` for every sheaf of sets `T`.

The reason is that the sheafification map of `A` is locally bijective, hence so is the morphism
of presheaves of sets underlying it — local injectivity and local surjectivity are both defined
through underlying sets — and a locally bijective morphism of presheaves of sets is one of
`CategoryTheory.GrothendieckTopology.W`, which *is* the class of morphisms along which morphisms
into a sheaf extend uniquely (`CategoryTheory.ObjectProperty.isLocal`).

## Main results

* `AlgebraicGeometry.Space.w_whiskerRight_toSheafify_forget`: the morphism of presheaves of sets
  underlying the sheafification map of a presheaf of abelian groups becomes an isomorphism after
  sheafification of presheaves of sets.
* `AlgebraicGeometry.Space.sheafifyForgetHomEquiv`: the resulting bijection on morphisms into a
  sheaf of sets, whose forward direction is restriction along the sheafification map.

## Implementation notes

No compatibility of the forgetful functor with sheafification is needed, and in particular no
`CategoryTheory.GrothendieckTopology.PreservesSheafification` instance for
`CategoryTheory.forget AddCommGrpCat` on this site: `CategoryTheory.GrothendieckTopology.W` is by
definition the class of morphisms `f` such that precomposition with `f` is bijective on
morphisms into every sheaf, so the extension property is immediate from local bijectivity and
does not pass through a sheafification of presheaves of sets at all.

The coefficient universe is the universe `u + 1` of the objects of the small étale site.  That is
the universe `AlgebraicGeometry.Space.meromorphicSectionPresheaf` lifts its extension of scalars
to before sheafifying, and the universe at which the local equivalences of presheaves of abelian
groups on this site are known to be the locally bijective morphisms
(`AlgebraicGeometry.Space.moduleWEqualsLocallyBijective`).

## References

* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- Sheafification of presheaves of abelian groups on the small étale site of `F`, at the
universe `u + 1` of the objects of the site.

The content is `AlgebraicGeometry.Space.moduleHasWeakSheafify`; that instance is stated at the
coefficient universe `max (u + 1) z`, and instance search cannot solve the universe constraint
`u + 1 =?= max (u + 1) ?z`, so the specialization has to be registered.  Being a `Prop`, it
agrees with the general instance wherever both are available. -/
noncomputable instance objUniverseHasWeakSheafify :
    HasWeakSheafify (SmallEtale.topology B S hS F) AddCommGrpCat.{u + 1} :=
  moduleHasWeakSheafify.{u, u + 1} B S hS F

/-- The local equivalences of presheaves of abelian groups on the small étale site of `F`, at the
universe `u + 1` of the objects of the site, are exactly the locally bijective morphisms.

As for `AlgebraicGeometry.Space.objUniverseHasWeakSheafify`, the content is
`AlgebraicGeometry.Space.moduleWEqualsLocallyBijective` and only the universe specialization is
new. -/
instance objUniverseWEqualsLocallyBijective :
    (SmallEtale.topology B S hS F).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  moduleWEqualsLocallyBijective.{u, u + 1} B S hS F

/-- **The sheafification map of a presheaf of abelian groups is locally bijective on underlying
sets.**  For a presheaf of abelian groups on the small étale site of `F` at the universe of the
objects of the site, the morphism of presheaves of sets underlying its sheafification map becomes
an isomorphism after sheafification of presheaves of sets.

Local injectivity and local surjectivity are defined through underlying sets, so both transfer
from the sheafification map to the morphism of presheaves of sets underlying it; and for
presheaves of sets the two together are exactly membership in
`CategoryTheory.GrothendieckTopology.W`. -/
theorem w_whiskerRight_toSheafify_forget
    (A : (SmallEtale B S hS F)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (SmallEtale.topology B S hS F).W
      (Functor.whiskerRight (toSheafify (SmallEtale.topology B S hS F) A)
        (CategoryTheory.forget AddCommGrpCat.{u + 1})) := by
  have hsurj : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS F)
      (Functor.whiskerRight (toSheafify (SmallEtale.topology B S hS F) A)
        (CategoryTheory.forget AddCommGrpCat.{u + 1})) :=
    (Presheaf.isLocallySurjective_iff_whisker_forget (SmallEtale.topology B S hS F)
      (toSheafify (SmallEtale.topology B S hS F) A)).1 inferInstance
  have hinj : Presheaf.IsLocallyInjective (SmallEtale.topology B S hS F)
      (Functor.whiskerRight (toSheafify (SmallEtale.topology B S hS F) A)
        (CategoryTheory.forget AddCommGrpCat.{u + 1})) :=
    Presheaf.isLocallyInjective_forget (SmallEtale.topology B S hS F)
      (toSheafify (SmallEtale.topology B S hS F) A)
  exact GrothendieckTopology.W_of_isLocallyBijective (SmallEtale.topology B S hS F) _

/-- **A morphism of presheaves of sets into a sheaf extends uniquely over the sheafification of a
presheaf of abelian groups.**  For a presheaf of abelian groups `A` on the small étale site of
`F` at the universe of the objects of the site and a sheaf of sets `T` on that site,
restriction along the sheafification map of `A` is a bijection from the morphisms of presheaves
of sets out of the sheafification of `A` onto the morphisms of presheaves of sets out of `A`.

This is `AlgebraicGeometry.Space.w_whiskerRight_toSheafify_forget` read through the definition of
`CategoryTheory.GrothendieckTopology.W` as `CategoryTheory.ObjectProperty.isLocal` of the sheaf
condition. -/
noncomputable def sheafifyForgetHomEquiv
    (A : (SmallEtale B S hS F)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (T : Sheaf (SmallEtale.topology B S hS F) (Type (u + 1))) :
    (sheafify (SmallEtale.topology B S hS F) A ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1} ⟶ T.obj) ≃
      (A ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1} ⟶ T.obj) :=
  ObjectProperty.isLocal.homEquiv (w_whiskerRight_toSheafify_forget B S hS F A) T.obj T.property

/-- The extension of a morphism of presheaves of sets into a sheaf over the sheafification of a
presheaf of abelian groups restricts to the morphism it extends. -/
theorem sheafifyForgetHomEquiv_symm_comp
    (A : (SmallEtale B S hS F)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (T : Sheaf (SmallEtale.topology B S hS F) (Type (u + 1)))
    (ψ : A ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1} ⟶ T.obj) :
    Functor.whiskerRight (toSheafify (SmallEtale.topology B S hS F) A)
          (CategoryTheory.forget AddCommGrpCat.{u + 1}) ≫
        (sheafifyForgetHomEquiv B S hS F A T).symm ψ = ψ :=
  (sheafifyForgetHomEquiv B S hS F A T).apply_symm_apply ψ

end AlgebraicGeometry.Space

end
