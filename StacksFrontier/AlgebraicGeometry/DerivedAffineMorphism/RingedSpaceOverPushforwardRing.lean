module

public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.DerivedPushforwardOverPushforwardRing
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.PullbackPushforwardAdjunction
public import StacksFrontier.Topology.Sheaves.Cohomology.SheafedSpaceLimits.ConeLiftAndBasePushforward

/-!
# The morphism of ringed spaces `(X, 𝒪_X) ⟶ (S, f_* 𝒪_X)`, and `Φ` as its derived pushforward

Let `f : X ⟶ S` be a morphism of schemes.  The space `S` carrying the sheaf of rings `f_* 𝒪_X`
is a ringed space, and `f` itself is a morphism of ringed spaces
`g : (X, 𝒪_X) ⟶ (S, f_* 𝒪_X)`: the continuous map is `f.base`, and the structure map
`f_* 𝒪_X ⟶ g_* 𝒪_X` is the identity, there being nothing to say, since `g_* 𝒪_X` *is*
`f_* 𝒪_X`.

This file builds `g` and identifies
`Stacks.AlgebraicGeometry.DerivedAffinePushforward.derivedPushforwardOverRing`, the functor `Φ`
of [Stacks, Tag 0AVW], with the derived pushforward `Rg_*` of
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/PullbackPushforwardAdjunction.lean`.

## Main definitions

* `Stacks.AlgebraicGeometry.DerivedAffinePushforward.pushforwardStructureSpace` — the ringed
  space `(S, f_* 𝒪_X)`.
* `Stacks.AlgebraicGeometry.DerivedAffinePushforward.toPushforwardStructureSpace` — the
  morphism of ringed spaces `g : (X, 𝒪_X) ⟶ (S, f_* 𝒪_X)`.

## Main results

* `ringSheaf_pushforwardStructureSpace` and `structureSheafHom_toPushforwardStructureSpace`:
  the sheaf of rings of `(S, f_* 𝒪_X)` is `f_* 𝒪_X`, and the structure map of `g` is its
  identity.
* `modulePushforward_toPushforwardStructureSpace`: direct image of sheaves of modules along `g`
  **is** direct image over `f_* 𝒪_X`, the functor of which `Φ` is the derived functor.
* `derivedPushforwardOverRing_eq_derivedPushforward` and
  `derivedPushforwardOverRingIsoDerivedPushforward` — **`Φ = Rg_*`**, as an equality of functors
  and as the resulting isomorphism, with
  `derivedPushforwardUnit_toPushforwardStructureSpace` for their comparison maps.

## Implementation notes

*Everything here is `rfl`, and that is the result.*  What this file removes is the belief that
`Φ`, built in
`StacksFrontier/AlgebraicGeometry/DerivedAffineMorphism/DerivedPushforwardOverPushforwardRing.lean`
as a total right derived functor in its own right, is only *isomorphic* to a derived pushforward
along a morphism of ringed spaces, so that the derived machinery available for the latter would
have to be transported across an isomorphism.  It is not: with `g` taken to be
`Stacks.Cohomology.SpectralLimit.SheafedSpaceLimit.pushMor`, the identity-structure-map morphism
from a sheafed space into the pushforward of its own sheaf, the two degreewise direct images are
the *same functor*, hence so are the two total right derived functors and their comparison maps.
The isomorphism recorded below is `Iso.refl`, and it exists only because that is the shape a
consumer of a natural isomorphism asks for.

What this buys is that the derived pullback and the derived adjunction
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackPushforwardAdjunction` apply
to `Φ` with no transport: an adjunction `Lg^* ⊣ Rg_*` *is* an adjunction `Lg^* ⊣ Φ`.  It does
not by itself settle the first clause of [Stacks, Tag 0AVW], that `Φ` is an equivalence onto
`D_QCoh(f_* 𝒪_X)`.  Two things once named here as unavailable for that clause now hold:
`g` is flat, hence `g^*` is exact and no resolving datum for `Lg^*` is asked for
(`Stacks.AlgebraicGeometry.DerivedAffinePushforward.isFlat_toPushforwardStructureSpace`), and
[Stacks, Tag 01BG] for `g^*` is
`Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_pullbackModules`.  Both are
assembled in
`StacksFrontier/AlgebraicGeometry/DerivedAffineMorphism/FlatOverPushforwardRing.lean`.

*The two derived-category models have to be carried across a spelling seam.*  `Rg_*` takes its
models at `structureSheafRing` of the two ringed spaces, whereas `Φ` takes them at
`AlgebraicGeometry.Scheme.ringCatSheaf` and at
`Stacks.AlgebraicGeometry.AffineQcohPushforward.pushforwardRing`.  The spellings are equal by
`rfl`, but their discrimination keys differ — `ringCatSheaf` is an `abbrev` and unfolds, while
`structureSheafRing` is semireducible and stays folded — so instance search crosses neither way on
its own.  Worse than failing, it succeeds wrongly: `SheafOfModules.hasDerivedCategory` of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` is a *global* `HasDerivedCategory.{u}`
instance that does match the `structureSheafRing` spelling, so a bare `Rg_*` written beside `Φ`
silently acquires the locally small model and then fails to meet `Φ` with a universe mismatch
rather than with a missing instance.  Two devices handle this.
`derivedPushforwardStructureSpaceHom` is `Rg_*` with `Φ`'s own two instances passed by hand, and it
is what the statements below use, so they cannot be quietly specialized to one model.  The two
`scoped instance`s `hasDerivedCategory_ringSheaf_toRingedSpace` and
`hasDerivedCategory_ringSheaf_pushforwardStructureSpace` close the seam for a consumer, who may
then write `derivedPullback (toPushforwardStructureSpace f)` and
`derivedPullbackPushforwardAdjunction (toPushforwardStructureSpace f) _ _ _` against `Φ`'s models
with no plumbing; `derivedPushforward_eq_derivedPushforwardStructureSpaceHom` is the check that the
two devices agree, and is what would break were the bridges to stop firing.

## References

* [Stacks Project, Tag 0AVW](https://stacks.math.columbia.edu/tag/0AVW)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.AffineQcohPushforward
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward derivedPushforwardUnit)
open Stacks.Cohomology.SpectralLimit.SheafedSpaceLimit (pushSpace pushMor)

universe u w

namespace Stacks.AlgebraicGeometry.DerivedAffinePushforward

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-! ### The ringed space `(S, f_* 𝒪_X)` and the morphism `g` -/

/-- **The ringed space `(S, f_* 𝒪_X)`**: the space underlying the target of `f`, carrying the
direct image of the structure sheaf of the source. -/
abbrev pushforwardStructureSpace : RingedSpace.{u, u} :=
  pushSpace X.toRingedSpace f.base

/-- **The morphism of ringed spaces `g : (X, 𝒪_X) ⟶ (S, f_* 𝒪_X)`** underlying a morphism of
schemes `f : X ⟶ S`: the continuous map is `f.base`, and the structure map
`f_* 𝒪_X ⟶ g_* 𝒪_X` is the identity, the target being the source. -/
abbrev toPushforwardStructureSpace : X.toRingedSpace ⟶ pushforwardStructureSpace f :=
  pushMor X.toRingedSpace f.base

/-- The continuous map underlying `g` is the one underlying `f`. -/
theorem base_toPushforwardStructureSpace :
    (toPushforwardStructureSpace f).hom.base = f.base :=
  rfl

/-- The structure map of `g` is the identity of `f_* 𝒪_X`. -/
theorem c_toPushforwardStructureSpace :
    (toPushforwardStructureSpace f).hom.c = 𝟙 (f.base _* X.presheaf) :=
  rfl

/-- The sheaf of rings of `(S, f_* 𝒪_X)` is the pushed-forward sheaf of rings `f_* 𝒪_X` of
`Stacks.AlgebraicGeometry.AffineQcohPushforward.pushforwardRing`. -/
theorem ringSheaf_pushforwardStructureSpace :
    structureSheafRing (pushforwardStructureSpace f) = pushforwardRing f.base X.ringCatSheaf :=
  rfl

/-- The structure map of `g`, read as the morphism of `RingCat`-valued sheaves of rings that
`CategoryTheory.SheafOfModules.pushforward` consumes, is the identity of `f_* 𝒪_X`.  This is
what makes `g_*` the direct image *over `f_* 𝒪_X`* rather than over `𝒪_S`. -/
theorem structureSheafHom_toPushforwardStructureSpace :
    structureSheafHom (toPushforwardStructureSpace f) =
      𝟙 (pushforwardRing f.base X.ringCatSheaf) :=
  rfl

/-- **Direct image of sheaves of modules along `g` is direct image over `f_* 𝒪_X`.**  The two
functors `Mod(𝒪_X) ⥤ Mod(f_* 𝒪_X)` are equal, not merely isomorphic: both are
`CategoryTheory.SheafOfModules.pushforward` of the identity of `f_* 𝒪_X`. -/
theorem modulePushforward_toPushforwardStructureSpace :
    modulePushforward (toPushforwardStructureSpace f) =
      pushforwardModules.{u} f.base X.ringCatSheaf :=
  rfl

/-! ### The derived categories across the two spellings of the sheaves of rings -/

/-- A chosen derived category of `𝒪_X`-modules, read at the `structureSheafRing` spelling of the
sheaf of rings that the ringed-space API uses; it is the same category. -/
scoped instance hasDerivedCategory_ringSheaf_toRingedSpace (Z : Scheme.{u})
    [h : HasDerivedCategory.{w} (SheafOfModules.{u} Z.ringCatSheaf)] :
    HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) :=
  h

/-- A chosen derived category of `f_* 𝒪_X`-modules, read at the `structureSheafRing` spelling of
the sheaf of rings of `(S, f_* 𝒪_X)`. -/
scoped instance hasDerivedCategory_ringSheaf_pushforwardStructureSpace
    [h : HasDerivedCategory.{w} (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf))] :
    HasDerivedCategory.{w}
      (SheafOfModules.{u} (structureSheafRing (pushforwardStructureSpace f))) :=
  h

/-! ### `Φ` is the derived pushforward along `g` -/

section Derived

variable [h₁ : HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]
  [h₂ : HasDerivedCategory.{w} (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf))]

/-- **`Rg_*`**, the derived pushforward along `g`, at the two derived categories `Φ` is stated
at, which are passed by hand so that no statement about it can be quietly specialized to another
model. -/
abbrev derivedPushforwardStructureSpaceHom :=
  @derivedPushforward X.toRingedSpace (pushforwardStructureSpace f)
    (toPushforwardStructureSpace f) h₁ h₂

/-- The canonical comparison from degreewise direct image to `Rg_*`, at the same two models. -/
abbrev derivedPushforwardUnitStructureSpaceHom :=
  @derivedPushforwardUnit X.toRingedSpace (pushforwardStructureSpace f)
    (toPushforwardStructureSpace f) h₁ h₂

/-- **`Φ = Rg_*`.**  The functor `Φ : D(𝒪_X) ⥤ D(f_* 𝒪_X)` of [Stacks, Tag 0AVW] is the derived
pushforward along the morphism of ringed spaces `g : (X, 𝒪_X) ⟶ (S, f_* 𝒪_X)`: both are the
total right derived functor of one and the same degreewise direct image, by
`modulePushforward_toPushforwardStructureSpace`, at one and the same pair of derived
categories. -/
theorem derivedPushforwardOverRing_eq_derivedPushforward :
    derivedPushforwardOverRing.{w} f = derivedPushforwardStructureSpaceHom f :=
  rfl

/-- **`Φ ≅ Rg_*`**, the identification of `derivedPushforwardOverRing_eq_derivedPushforward` in
the shape a consumer of a natural isomorphism asks for.  It is the identity. -/
def derivedPushforwardOverRingIsoDerivedPushforward :
    derivedPushforwardOverRing.{w} f ≅ derivedPushforwardStructureSpaceHom f :=
  Iso.refl _

/-- The comparison maps of `Φ` and of `Rg_*` agree, so that
`derivedPushforwardOverRing_eq_derivedPushforward` is an identification of right derived
functors and not merely of functors. -/
theorem derivedPushforwardUnit_toPushforwardStructureSpace :
    derivedPushforwardUnitStructureSpaceHom f = derivedPushforwardOverRingUnit.{w} f :=
  rfl

/-- `Rg_*` written with its models left to instance search, under the two `scoped instance`s
above, is `Rg_*` at `Φ`'s models.  This is the check that those bridges fire: were they to stop,
the two sides would have different models and this would fail to typecheck. -/
theorem derivedPushforward_eq_derivedPushforwardStructureSpaceHom :
    derivedPushforward (toPushforwardStructureSpace f) =
      derivedPushforwardStructureSpaceHom f :=
  rfl

end Derived

end Stacks.AlgebraicGeometry.DerivedAffinePushforward

end
