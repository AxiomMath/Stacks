module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.CompositionOfDirectImages
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.CompositionGeneral
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposSiteHomOfRingedSiteGeneral

/-!
# The pullback of modules along a composite of morphisms of ringed sites

For two morphisms of ringed sites `f : X ⟶ Y` and `g : Y ⟶ Z` at independent object and
morphism universes, the pullback of sheaves of modules along the composite is the composite of
the two pullbacks,

`(g ∘ f)^* ≅ g^* ⋙ f^*`.

Both sides are left adjoint to one and the same functor.  The pushforward along the composite is
the composite of the pushforwards — `AlgebraicGeometry.RingedToposSiteHom.pushforwardToposCompIso`,
which is the identity on sections — and adjunctions compose, so this is uniqueness of left
adjoints.

## Main definitions

* `AlgebraicGeometry.RingedSite.HomGeneral.pullbackModulesGeneralCompIso`: the comparison
  `(g ∘ f)^* ≅ g^* ⋙ f^*`.

## Main results

* `AlgebraicGeometry.RingedSite.HomGeneral.toRingedToposSiteHom_comp`: the passage from a
  morphism of ringed sites at independent universes to a site-presented morphism of ringed topoi
  carries composition to composition.

## Implementation notes

No `stacks` attribute is attached.  The statement is the pseudo-functoriality half of
Stacks 03D8, and that clause is registered on
`AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RingedToposPullbackModulesComp.lean`), for the
four-field presentation of a morphism of ringed topoi; what is new here is only that the
site-presented form at independent universes is available, which is the form every site of
schemes in this development is stated at.  The proof is the same two lines.

## References

* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uX vX uY vY uZ vZ w

namespace AlgebraicGeometry.RingedSite

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}} {Z : RingedSite.{uZ, vZ, w}}

/-- **Stacks 03AD part (3) is carried to Stacks 01D3 part (3).**  The site-presented morphism of
ringed topoi attached to a composite of morphisms of ringed sites at independent universes is the
composite of the attached morphisms of ringed topoi.  Both are assembled from the same two data
in the same way — the underlying functors compose and the structure maps are the same three-fold
composite — so the two sides are equal. -/
public theorem HomGeneral.toRingedToposSiteHom_comp (f : HomGeneral X Y) (g : HomGeneral Y Z) :
    (f.comp g).toRingedToposSiteHom =
      AlgebraicGeometry.RingedToposSiteHom.comp g.toRingedToposSiteHom
        f.toRingedToposSiteHom :=
  rfl

variable [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [EssentiallySmall.{w} Y.C] [EssentiallySmall.{w} Z.C]
  [LocallySmall.{w} X.C] [LocallySmall.{w} Y.C]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The pullback of sheaves of modules along a composite of morphisms of ringed sites is the
composite of the pullbacks**, `(g ∘ f)^* ≅ g^* ⋙ f^*`, at independent object and morphism
universes.

The left-hand side is the pullback along the *single* morphism of ringed sites `f.comp g`, that
is `SheafOfModules.pullback` of its own structure map, and is in general not the composite of the
two factors on the nose.  Both sides are left adjoint to `f_* ⋙ g_*`: the left-hand side by
`AlgebraicGeometry.RingedToposSiteHom.pushforwardToposCompIso` transported across its adjunction
`AlgebraicGeometry.RingedSite.HomGeneral.pullbackAdjPushforwardModulesGeneral`, the right-hand
side because adjunctions compose.  So they agree by uniqueness of left adjoints.

This is the step by which a statement about the pullback along a composite of morphisms of ringed
sites is reduced to the two factors; see the implementation notes for where the tag sits. -/
public def HomGeneral.pullbackModulesGeneralCompIso (f : HomGeneral X Y) (g : HomGeneral Y Z) :
    (f.comp g).pullbackModulesGeneral ≅
      g.pullbackModulesGeneral ⋙ f.pullbackModulesGeneral :=
  ((f.comp g).pullbackAdjPushforwardModulesGeneral.ofNatIsoRight
      (AlgebraicGeometry.RingedToposSiteHom.pushforwardToposCompIso
        f.toRingedToposSiteHom g.toRingedToposSiteHom)).leftAdjointUniq
    (g.pullbackAdjPushforwardModulesGeneral.comp f.pullbackAdjPushforwardModulesGeneral)

end AlgebraicGeometry.RingedSite

end
