module

public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.SheafifyCommRing.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# The small étale site ringed by a constant coefficient ring

The small étale site of a scheme `X`, ringed by the constant sheaf of rings with value a
coefficient ring `Λ`, as an `AlgebraicGeometry.RingedSite`.

## Main definitions

* `Stacks.EtaleCohomology.etaleConstantCommRingSheaf`: the constant sheaf of rings `Λ̲`.
* `Stacks.EtaleCohomology.etaleConstantRingedSite`: the small étale site ringed by it.

## Main results

* `Stacks.EtaleCohomology.hasSheafify_addCommGrpCat_smallEtale_coefficients` and
  `wEqualsLocallyBijective_addCommGrpCat_smallEtale_coefficients`: sheafification of abelian
  presheaves at the coefficient universe, and its weak equivalences, the site being essentially
  small.

## Universes

For `X : Scheme.{u}` the site `X.Etale` is a `Type (u + 1)` with `Category.{u}`, so its object
universe is `u + 1` and its morphism universe is `u`; and the coefficients of
`Stacks.EtaleCohomology.EtaleModules.{u, r}` sit in `max (u + 1) r` for a ring universe `r`,
because the site's objects must fit in the coefficient category and the site must be
essentially small in it.  So the ringed site here is an
`AlgebraicGeometry.RingedSite.{u + 1, u, max (u + 1) r}`, whose three universes are pairwise
distinct in general.

That is not the shape of `AlgebraicGeometry.smallEtaleRingedSite`, which is a
`RingedSite.{u + 1, u, u}` — the small étale site ringed by its own *structure* sheaf, where
the module universe is the morphism universe.

## Implementation notes

`CommRingCat`-valued sheafification at the coefficient universe is
`Stacks.SheafifyCommRing.hasSheafifyCommRingCat`, which is general — `HasSheafify J
CommRingCat.{max u v w}` with the site's two universes and the sections universe independent —
but is applied here with its universes written out.  Instance search will not find it against a
goal in `CommRingCat.{max (u + 1) r}`, because solving `max (u + 1) u ?w = max (u + 1) r` for
`?w` is a universe unification Lean does not perform; `?w := r` is the solution and is supplied.
That is the same reason
`Stacks.EtaleCohomology.hasSheafifyCommRingCat_smallEtale` exists as a specialisation at
`CommRingCat.{u + 1}`, and this file adds no second instance: it names the application rather
than registering one, so nothing is shadowed.

The value of the constant sheaf is `ULift.{max (u + 1) r} Λ` rather than `Λ`, the coefficient
category being `CommRingCat.{max (u + 1) r}` while `Λ : Type r`.  `ULift` is correct here and
`Shrink` is not needed: `ULift.{max (u + 1) r} Λ` lands in `Type (max (u + 1) r)` on the nose,
since that universe already contains `r`.  (`Shrink` is the right tool in the opposite
situation, where a ring must be moved *down* into `Type (u + 1)` — see
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Constructible/ShrinkCoefficients.lean`.)

**What this is for, and what it is not.**  Stacks 0GL5 is the projection formula for `Rf_!`
against the derived tensor product `- ⊗^L_Λ -` of sheaves of `Λ̲`-modules, and the second
diagram of Stacks 0GL6 follows from it at `K` the constant sheaf `Λ₂`.  Neither is proved here,
and neither is that derived tensor product: the existence theorem of Stacks 06YU,
`Stacks.SheafOfModules.exists_derivedTensorProduct`
(`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/Existence.lean`), is stated for an
`AlgebraicGeometry.RingedSite.{c, u, u}`, whose morphism universe and module universe are one
and the same; the ringed site built here keeps them apart, so that theorem does not apply to it
at any instantiation of `c` and `u`.  Nor is the sheaf of modules over `Λ̲` identified with
`Stacks.EtaleCohomology.EtaleModules`, which is
`Sheaf X.smallEtaleTopology (ModuleCat Λ)`.  So nothing here carries the 0GL6 tag.

*That identification exists, but not at this file's spelling.*  The equivalence
`SheafOfModules Λ̲ ≌ Sheaf J (ModuleCat Λ)` is in the library:
`Stacks.SheafOfModules.ConstantRing.sheafifiedConstRingModulesEquivalence` proves
`Sheaf J (ModuleCat.{t} Λ) ≌ SheafOfModules.{t} (sheafifiedConstRing J Λ)`, with the ring
universe and the module universe independent.  What separates it from `etaleConstantRingedSite`
is a spelling of the ring sheaf rather than a missing theorem: that equivalence puts the
constant ring sheaf at the *ring's own* universe and in `RingCat`, while the ringed site here
needs it in `CommRingCat` at the *module* universe `max (u + 1) r` and with value `ULift Λ`
rather than `Λ`, for the reason given just above.  So crossing the two costs a `ULift` ring
transport and the `CommRingCat`-to-`RingCat` step, and nothing deeper.

## References

* [Stacks Project, Tag 03TR](https://stacks.math.columbia.edu/tag/03TR)
* [Stacks Project, Remark 0GL6](https://stacks.math.columbia.edu/tag/0GL6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [CommRing Λ] (X : Scheme.{u})

/-- Presheaves of commutative rings on the small étale site of a scheme can be sheafified at
the coefficient universe of `Stacks.EtaleCohomology.EtaleModules`.  This is
`Stacks.SheafifyCommRing.hasSheafifyCommRingCat` with its universes written out; see the
implementation notes for why they have to be. -/
theorem hasSheafify_commRingCat_smallEtale_coefficients :
    HasSheafify X.smallEtaleTopology CommRingCat.{max (u + 1) r} :=
  Stacks.SheafifyCommRing.hasSheafifyCommRingCat.{r, u, u + 1} X.smallEtaleTopology

/-- Presheaves of abelian groups on the small étale site of a scheme can be sheafified at the
coefficient universe, the site being essentially small.  This is the `AddCommGrpCat` analogue of
`Stacks.EtaleCohomology.etaleModules_hasSheafify` and, like it, has to be named: instance search
cannot solve the universe constraint on its own. -/
theorem hasSheafify_addCommGrpCat_smallEtale_coefficients :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r} :=
  hasSheafifyEssentiallySmallSite.{_, _, _, _, max (u + 1) r} _ _

/-- Weak equivalences of presheaves of abelian groups on the small étale site are the locally
bijective maps, at the coefficient universe. -/
theorem wEqualsLocallyBijective_addCommGrpCat_smallEtale_coefficients :
    X.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{max (u + 1) r} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

attribute [local instance] hasSheafify_commRingCat_smallEtale_coefficients
  hasSheafify_addCommGrpCat_smallEtale_coefficients
  wEqualsLocallyBijective_addCommGrpCat_smallEtale_coefficients

/-- **The constant sheaf of rings `Λ̲` with value `Λ` on the small étale site of `X`.**  Its
value is `ULift Λ`, the coefficient category sitting in `max (u + 1) r` while `Λ` sits in
`r`. -/
abbrev etaleConstantCommRingSheaf : Sheaf X.smallEtaleTopology CommRingCat.{max (u + 1) r} :=
  (constantSheaf X.smallEtaleTopology CommRingCat.{max (u + 1) r}).obj
    (CommRingCat.of (ULift.{max (u + 1) r} Λ))

/-- **The small étale site of `X` ringed by the constant coefficient ring `Λ`.**  Object
universe `u + 1`, morphism universe `u`, module universe `max (u + 1) r`: three independent
universes, which is what distinguishes this from
`AlgebraicGeometry.smallEtaleRingedSite`, ringed by its own structure sheaf at module universe
equal to the morphism universe. -/
abbrev etaleConstantRingedSite : AlgebraicGeometry.RingedSite.{u + 1, u, max (u + 1) r} where
  C := X.Etale
  J := X.smallEtaleTopology
  O := etaleConstantCommRingSheaf.{u, r} Λ X

end Stacks.EtaleCohomology

end
