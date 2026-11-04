module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSmallModel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteFlat

/-!
# Sheaves of modules on the model and on the small étale site

The comparison of the small étale site of `S` with its `Type u` small model exhibits the model,
with the transported topology, as a **dense subsite** of the small étale site: the comparison is
an equivalence of categories, hence cover dense, and the transported topology is by construction
the induced one, for which `CategoryTheory.Functor.IsDenseSubsite` then holds.  That is the
hypothesis under which the Comparison Lemma for sheaves of modules
(`Stacks.DenseSubsiteModules.moduleRestrictionEquivalence`) and the invariance of flatness under
change of presenting site (`Stacks.DenseSubsiteModules.isFlat_moduleRestriction_iff`) are
proved, and both are stated with the four site universes free.  This file reads them off for the
model.

The content is the two transport statements, and the observation that the transport functor is
one already named: restriction of sheaves of modules to the model *is* the pushforward of
sheaves of modules along `AlgebraicGeometry.SmallEtale.fromEtaleHom`, by `rfl`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.smallModelModuleRestriction`: restriction of sheaves of modules
  from the small étale site to the model.
* `AlgebraicGeometry.SmallEtale.smallModelModulesEquiv`: **the Comparison Lemma for sheaves of
  modules**, as an equivalence `Mod(𝒪) ≌ Mod(𝒪_model)`.

## Main results

* `AlgebraicGeometry.SmallEtale.smallModelModuleRestriction_eq_pushforward`: the restriction is
  the pushforward of sheaves of modules along
  `AlgebraicGeometry.SmallEtale.fromEtaleHom`, on the nose.
* `AlgebraicGeometry.SmallEtale.isFlat_iff_smallModelModuleRestriction`: **flatness transports
  between the small étale site and the model**, in both directions.  This is the statement that
  Stacks 05VD for `ε` was missing: `Stacks.Sheaves.RingedToposModules.isFlat_pullbackModules`
  pins the source ringed topos to have its section universe equal to its object universe, which
  the small étale presentation does not, but it does apply to the model, and this `iff` carries
  the conclusion back.

## Implementation notes

**Why the statements avoid the structure projections of the two ringed topoi.**  Everything here
is phrased with `AlgebraicGeometry.SmallEtale.topology`,
`AlgebraicGeometry.SmallEtale.commRingStructureSheaf`,
`AlgebraicGeometry.SmallEtale.structureSheaf`,
`AlgebraicGeometry.SmallEtale.smallModelTopology` and
`AlgebraicGeometry.SmallEtale.smallModelStructureSheaf` rather than with
`(ringedTopos B S hS).J`, `(ringedTopos B S hS).O` and their counterparts on the model.  The
projections of a `def`-produced structure do not unfold at instance transparency, so a statement
phrased with them demands each of `HasWeakSheafify`, `GrothendieckTopology.WEqualsLocallyBijective`
and `GrothendieckTopology.HasSheafCompose` to be restated at the projected spelling, as
`AlgebraicGeometry.SmallEtale.hasWeakSheafify_ringedTopos_J` and
`AlgebraicGeometry.SmallEtale.wEqualsLocallyBijective_ringedTopos_J` had to be.  At the spellings
used here every instance is found as it stands.

**No instance is declared.**  The Comparison Lemma for sheaves of abelian groups along the
comparison — `(smallModelEquiv.inverse.sheafPushforwardContinuous AddCommGrpCat.{u} _ _)` is an
equivalence — is what both transport statements assume, and Mathlib derives it from the
existence of the limits indexing the right Kan extension along the comparison.  Those limits
exist because the indexing comma categories are essentially small at `u`, the model being small
and the small étale site locally small; that is
`AlgebraicGeometry.RingedTopos.hasLimitsOfShape_structuredArrow_equivSmallModel_inverse_op`,
stated there for an arbitrary site essentially small at the universe of the sections and an
arbitrary complete category whose morphisms lie in that universe, so that the same instance
serves for sheaves of abelian groups and of rings.

**`Stacks.commRingSheafToRingSheaf` needs its site argument named.**  Its topology is an implicit
argument and the universes of a `SheafOfModules.{u}` over it are not solved for from the
surrounding expected type, so the applications below pass `(J := ...)` explicitly; without it the
elaborator defaults the site universes to `0`.

## References

* [Stacks Project, Tag 00XU](https://stacks.math.columbia.edu/tag/00XU), the Comparison Lemma
* [Stacks Project, Tag 03DG](https://stacks.math.columbia.edu/tag/03DG), method (2)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER), part (3)
* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.DenseSubsiteModules

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The comma categories indexing the right Kan extension along the comparison of the small
étale site of `S` with its small model have all limits of a complete category in the universe
shape of `AddCommGrpCat.{u}` and `CommRingCat.{u}`: they are essentially small at `u`, the model
being small and the small étale site locally small.

This is what makes restriction of sheaves along the comparison an equivalence, and so is the
hypothesis under which the Comparison Lemma for sheaves of modules and the invariance of
flatness below hold. -/
public instance hasLimitsOfShape_structuredArrow_smallModelEquiv_inverse_op
    (W : (SmallEtale B S hS)ᵒᵖ) (A : Type (u + 1)) [Category.{u} A] [HasLimits A] :
    HasLimitsOfShape (StructuredArrow W (smallModelEquiv B S hS).inverse.op) A :=
  inferInstance

/-- **Restriction of sheaves of modules from the small étale site of `S` to the model.**  A
sheaf of `𝒪`-modules is sent to its sections over the objects of the model, as a sheaf of modules
over the restricted structure sheaf. -/
public noncomputable abbrev smallModelModuleRestriction :
    _root_.SheafOfModules.{u} (structureSheaf B S hS) ⥤
      _root_.SheafOfModules.{u}
        (Stacks.commRingSheafToRingSheaf (J := smallModelTopology B S hS)
          (smallModelStructureSheaf B S hS)) :=
  moduleRestriction.{u} (smallModelTopology B S hS) (topology B S hS)
    (smallModelEquiv B S hS).inverse (structureSheaf B S hS)

/-- **Restriction of sheaves of modules to the model is the pushforward of sheaves of modules
along `AlgebraicGeometry.SmallEtale.fromEtaleHom`, on the nose.**

Both are restriction of sections along the comparison followed by restriction of scalars, and
the structure map of `fromEtaleHom` is the identity, so no comparison isomorphism intervenes. -/
public theorem smallModelModuleRestriction_eq_pushforward :
    smallModelModuleRestriction B S hS = (fromEtaleHom B S hS).pushforwardTopos := rfl

/-- **The Comparison Lemma for sheaves of modules, for the model.**  Restriction of sheaves of
modules from the small étale site of `S` to the model is an equivalence of categories.

So `Mod(𝒪)` on the small étale site and `Mod(𝒪_model)` on the model are the same abelian
category, and in particular restriction preserves and reflects every finite limit and colimit.
That is what makes the transport of flatness below possible, and it is also what will carry the
derived category of one to the derived category of the other. -/
public noncomputable def smallModelModulesEquiv :
    _root_.SheafOfModules.{u} (structureSheaf B S hS) ≌
      _root_.SheafOfModules.{u}
        (Stacks.commRingSheafToRingSheaf (J := smallModelTopology B S hS)
          (smallModelStructureSheaf B S hS)) :=
  moduleRestrictionEquivalence.{u} (smallModelTopology B S hS) (topology B S hS)
    (smallModelEquiv B S hS).inverse (structureSheaf B S hS)

/-- **Flatness transports between the small étale site of `S` and the model, in both
directions.**  A sheaf of `𝒪`-modules on the small étale site is flat if and only if its
restriction to the model is flat over the restricted structure sheaf.

This is `Stacks.DenseSubsiteModules.isFlat_moduleRestriction_iff`, Stacks 03DG method (2) for
flatness, which has all four site universes free.  It is the missing link between Stacks 05VD on
the model and Stacks 05VD on the small étale site: the library's Stacks 05VD
(`Stacks.Sheaves.RingedToposModules.isFlat_pullbackModules`) pins the source ringed topos to
`RingedTopos.{v, max u v, max u v}`, which `AlgebraicGeometry.SmallEtale.ringedTopos` — a
`RingedTopos.{u, u + 1, u}` — is not, while the model is a `RingedTopos.{u, u, u}` and so is. -/
public theorem isFlat_iff_smallModelModuleRestriction
    (N : _root_.SheafOfModules.{u} (structureSheaf B S hS)) :
    Stacks.SheafOfModules.IsFlat (O := commRingStructureSheaf B S hS) N ↔
      Stacks.SheafOfModules.IsFlat (O := smallModelStructureSheaf B S hS)
        ((smallModelModuleRestriction B S hS).obj N) :=
  isFlat_moduleRestriction_iff.{u} (smallModelTopology B S hS) (topology B S hS)
    (smallModelEquiv B S hS).inverse (commRingStructureSheaf B S hS) N

end AlgebraicGeometry.SmallEtale

end
