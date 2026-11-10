module

public import StacksFrontier.AlgebraicGeometry.Crystalline.FCrystal

/-!
# `X^{(1)}` and the relative Frobenius in the proof of [Stacks, Tag 07N5]

The proof of [Stacks, Tag 07N5] opens by setting

`X^{(1)} = X ×_{S₀, F_{S₀}} S₀`

and writing `F_{X/S₀} : X ⟶ X^{(1)}` for the relative Frobenius morphism, and then makes two
assertions about this factorization before any cohomology appears:

1. *the composition of `F_{X/S₀} : X ⟶ X^{(1)}` with the projection `X^{(1)} ⟶ X` is the absolute
   Frobenius morphism `F_X`*; and
2. *hence `F_{X/S₀}^* E^{(1)} = (F_X)^*_cris E`*, where `E^{(1)}` is the base change of `E` by
   `Spec(σ)`, that is the pullback of `E` to `Cris(X^{(1)}/S)` along the morphism of crystalline
   topoi attached to the square with `X^{(1)} ⟶ X` on top and `Spec(σ) : S ⟶ S` on the bottom.

Both are proved here, in the Frobenius crystal situation [Stacks, Tag 07N2] itself.  They are the
two steps of the source's argument that are purely about the sites and the coefficients: neither
needs [Stacks, Tag 07MU], [Stacks, Tag 07MY] or any of the three arrows the proof then compares,
and neither uses the Noetherian, `p`-adic completeness, properness or smoothness hypotheses of the
tag.

## `X^{(1)}` as a crystalline situation

`X^{(1)}` is the Frobenius twist `AlgebraicGeometry.frobeniusTwist` of `X` over the closed fibre
`S₀`, which is already in the library, and `F_{X/S₀}` is `AlgebraicGeometry.relativeFrobenius`.
What is new is that `X^{(1)}` is made into a global crystalline situation
[Stacks, Tag 07MF] over the *same* divided power base `(S, I, γ)`, which is what lets
`Cris(X^{(1)}/S)` and its sheaves of modules be spoken of: `frobeniusTwistSituation`.  The only
field needing an argument is the local nilpotence of `p`, and it transports along the projection
`X^{(1)} ⟶ X` exactly as it does along any morphism to `X`.

## The two change-of-base functors

With `X^{(1)}/S` available, the two morphisms of the source's diagram become two instances of
change of divided power base `Crystalline.GlobalCrystallineSituation.changeBase`:

* `twistChangeBase : CRIS(X/S) ⥤ CRIS(X^{(1)}/S)`, along `𝟙 : S ⟶ S` and `F_{X/S₀}`.  Its
  commuting square is the second projection identity `relativeFrobenius_snd`.
* `sigmaChangeBase : CRIS(X^{(1)}/S) ⥤ CRIS(X/S)`, along `Spec(σ) : S ⟶ S` and the projection
  `X^{(1)} ⟶ X`.  Its commuting square is the defining square of the fibre product `X^{(1)}`,
  together with `Crystalline.FCrystalSituation.closedFiberMap_specSigma`, that `Spec(σ)` induces
  the absolute Frobenius on `S₀`.

The pullbacks of sheaves of modules along these are `twistModulePullback`, which is
`F_{X/S₀}^*`, and `sigmaModulePullback`, which is `E ↦ E^{(1)}`.

The source's second assertion is then the statement that their composite is the Frobenius pullback
`Crystalline.FCrystalSituation.frobeniusModulePullback`.  It is proved by composing the two
change-of-base functors, which is again change of base along the composite of the two squares, and
the composite of the squares is the Frobenius square precisely by the source's first assertion.

## Why the big crystalline site

Everything here is on the **big** crystalline site, and not by preference.  The small-site change
of divided power base `Crystalline.GlobalCrystallineSituation.smallChangeBase` carries
`[IsOpenImmersion g]` on the morphism of the schemes over the closed fibres, because an object
`(U, T, δ)` of `Cris(X/S)` has `U ⟶ X` an open immersion and composing it with `g` destroys that.
None of the three morphisms this file changes base along is an open immersion under the
hypotheses of [Stacks, Tag 07N5].  The absolute Frobenius `F_X` and the projection
`X^{(1)} ⟶ X` — the latter being the base change of the absolute Frobenius of `S₀` — are
universal homeomorphisms which are isomorphisms only over a perfect base, and the relative
Frobenius `F_{X/S₀}` is an isomorphism when `X ⟶ S₀` is étale
(`AlgebraicGeometry.isIso_relativeFrobenius_of_etale`) and not for the proper smooth `X ⟶ S₀` of
positive relative dimension that the tag allows, where it is an iterated `α_p`-cover of degree
`p ^ d` (`AlgebraicGeometry.isIteratedAlphaPCover_relativeFrobenius`).  So the small-site functor
does not exist for them, and with it neither does the
construction of the base change map (07MT) in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/BaseChangeMapConstruction.lean`, which is
built from `smallChangeBase` and carries the same hypothesis.  The big-site
`Crystalline.GlobalCrystallineSituation.changeBase` carries no hypothesis on `g` at all, which is
why the two assertions above are reachable.

## What actually blocks the first arrow, which is not that hypothesis

The section above does not show that the first arrow of the source's proof is out of reach
*because* the small-site change of base wants an open immersion; the obstruction lies elsewhere.

Functoriality of the small crystalline topos for a general `g` is proved, by the source's own
detour `f_cris = π_Y ∘ f_CRIS ∘ i_X`: `Crystalline.GlobalCrystallineSituation.crisMorphism`
(`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/ToposFunctoriality.lean`) carries no
hypothesis on `g`, because the one step [Stacks, Tag 07IJ] omits in general — that the objects of
`Cris(X/S)` cover the final sheaf of `(X/S)_CRIS` — is proved in general, as
`Crystalline.GlobalCrystallineSituation.CrystallineThickening.coversTop_ι`.  With it come the
module-valued `f_{cris, *}` (`...SmallSite.crisModuleDirectImage`) and the pullback
`...SmallSite.crisModuleInverseImage`, both for every `g`, and the comparisons of global sections
`...SmallSite.smallRestrictionGlobalSectionsIso` and `...SmallSite.crisGlobalSectionsIso`, the
latter proved unconditionally for every morphism of global crystalline situations.

What is missing is a single statement, and it is about *coefficients* rather than about `g`:
**exactness of the module-level `i_!`**, clause (6) of [Stacks, Tag 07IJ] at module coefficients.
It is unproved; see the corresponding section of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/LowerShriekModules.lean`, where the abelian
`...CrystallineThickening.preservesFiniteLimits_lowerShriekAb` is proved but does not transfer,
the comparison [Stacks, Tag 0798] of the two lower shrieks being non-invertible in general
(`Stacks.SheafOfModules.lowerShriekForget_not_isomorphic`).  Where that bites is exactness of
`crisModuleInverseImage`, which is literally `i_{X', !}` followed by a restriction and is what
computes `RP(M[0])` as `P(M)[0]` in the assembly of the derived base change map.

The module-level `i_!` is not needed a second time, to upgrade the underived
`smallRestrictionGlobalSectionsIso` to its derived form
`RΓ(CRIS(X/S), N) ≅ RΓ(Cris(X/S), i_X^{-1}N)`: the upgrade does not ask for preservation of
injectives by `i_X^{-1}`, which would be equivalent to exactness of `i_!`.  The derived form is
proved as
`Crystalline.GlobalCrystallineSituation.SmallSite.derivedRestrictModuleGlobalSectionsObjIso` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/ModuleRestrictionAcyclicity.lean`: what the
upgrade asks for is `Γ(Cris(X/S), -)`-acyclicity of `i_X^{-1}I` for `I` injective, which is
strictly weaker than preservation of injectives, and is obtained by crossing to abelian
coefficients with [Stacks, Tag 03FD] on each of the two sites and running Leray for the
retraction there, where clause (6) of [Stacks, Tag 07IJ] is proved.

## Main definitions

Everything lives in the namespace `Crystalline.FCrystalSituation`.

* `frobeniusTwistOver` — `X^{(1)} = X ×_{S₀, F_{S₀}} S₀` as a scheme over `S₀`.
* `twistProjection` — the projection `X^{(1)} ⟶ X`.
* `frobeniusTwistSituation` — **`X^{(1)}/S` as a global crystalline situation** over the same
  divided power base.
* `relativeFrobeniusToTwist` — **the relative Frobenius `F_{X/S₀} : X ⟶ X^{(1)}`** of the proof
  of [Stacks, Tag 07N5].
* `twistChangeBase`, `sigmaChangeBase` — the two change-of-base functors on the big crystalline
  categories.
* `twistModulePullback`, `sigmaModulePullback` — `F_{X/S₀}^*` and `E ↦ E^{(1)}` on sheaves of
  modules.

The two squares over the closed fibre that the changes of base are taken along are
`toClosedFiber_comp_closedFiberMap_id` and `twistToClosedFiber_comp_closedFiberMap_specSigma`, and
each change-of-base functor's continuity for the big crystalline Zariski topologies is recorded as
an instance so that the pullbacks of modules and their composite are available.

## Main results

* `relativeFrobeniusToTwist_comp_twistProjection` — **`F_{X/S₀}` followed by the projection
  `X^{(1)} ⟶ X` is the absolute Frobenius `F_X`**, the first assertion above.
* `twistChangeBaseCompIso` — the composite of the two change-of-base functors is the Frobenius
  endofunctor of `CRIS(X/S)`.
* `frobeniusModulePullbackIso` — **`F_{X/S₀}^* E^{(1)} = (F_X)^*_cris E`**, the second assertion
  above, as an isomorphism of functors on sheaves of `𝒪_{X/S}`-modules.

## What is and is not proved

[Stacks, Tag 07N5] is **not** proved here: it is
`Crystalline.GlobalCrystallineSituation.SmallSite.statement07N5` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/Frobenius07N5Theorem.lean`, which carries
the tag.  Its conclusion is that the canonical map `F_E ∘ (F_X)^*_cris` becomes an isomorphism
after inverting `p`, and nothing in this file speaks about cohomology at all.  What is proved here
is the opening geometry of the source's proof: the factorization `F_X = F_{X/S₀} ≫ (X^{(1)} ⟶ X)`
and the resulting identification of the two pullbacks of coefficients, both in the situation of
the tag and under no hypothesis beyond it.

In particular nothing here supplies the canonical map of the tag, the base change map (07QC) of
the source's first arrow or the relative Frobenius pullback (07N6) of its second, and nothing here
is a step towards [Stacks, Tag 07MU] or [Stacks, Tag 07MY].

**No `@[stacks 07N5]` attribute is placed in this file.**  Two that earlier sat on
`relativeFrobeniusToTwist_comp_twistProjection` and on `frobeniusModulePullbackIso` were
withdrawn: a tag may be registered only on a declaration that states the *whole* tag, and each of
those two states one step of the source's proof — the factorization of the absolute Frobenius
through `X^{(1)}`, and the resulting identification of two pullbacks of coefficients — whereas
[Stacks, Tag 07N5] asserts that a map of derived categories becomes an isomorphism after inverting
`p`, which neither of them mentions.

The tag's own assertion is `Crystalline.GlobalCrystallineSituation.SmallSite.Statement07N5`, and
`...SmallSite.statement07N5` establishes it at the canonical map, over the two change-of-base
squares this module sets up, from the source's own three arrows
(`...SmallSite.frobeniusMap07N5Canonical_eq_comp`): the first is an isomorphism,
`...SmallSite.isIso_baseChangeArrow07QC`, from [Stacks, Tag 07MU] and [Stacks, Tag 07MY]; the
second is an isogeny, `...SmallSite.becomesIsoAfterInvertingPrime_relativeFrobeniusArrow07N6`,
from the bound of [Stacks, Tag 07QB] for `X ⟶ S₀` smooth of locally bounded relative dimension
(`...SmallSite.exists_bound_crisModuleCohomologyMap_relativeFrobeniusToTwist_of_smooth`, resting
on the argument of [Stacks, Tag 07Q9] in the form
`...SmallSite.annihilation07Q9_of_isIteratedAlphaPCover_localDegree`); and the third is an isogeny
by nondegeneracy, `...SmallSite.becomesIsoAfterInvertingPrime_frobeniusCohomologyMap`.

## References

* [Stacks Project, Tag 07N5](https://stacks.math.columbia.edu/tag/07N5)
* [Stacks Project, Tag 07N2](https://stacks.math.columbia.edu/tag/07N2)
* [Stacks Project, Tag 0CC9](https://stacks.math.columbia.edu/tag/0CC9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Frobenius

universe u

noncomputable section

namespace Crystalline.FCrystalSituation

open GlobalCrystallineSituation

variable (T : FCrystalSituation.{u})

/-! ### `X^{(1)}` and the relative Frobenius -/

/-- `X`, regarded as an object of `Over S₀` for the closed fibre `S₀ = V(I)`.  This is the input
of the Frobenius twist and of the relative Frobenius. -/
abbrev overClosedFiber : Over (DividedPowerScheme.closedFiber T.global.S) :=
  Over.mk T.global.toClosedFiber

/-- **`X^{(1)} = X ×_{S₀, F_{S₀}} S₀`**, the scheme over `S₀` with which the proof of
[Stacks, Tag 07N5] opens: the Frobenius twist of `X` over the closed fibre. -/
abbrev frobeniusTwistOver : Over (DividedPowerScheme.closedFiber T.global.S) :=
  (frobeniusTwist (DividedPowerScheme.closedFiber T.global.S) T.global.p
    T.isInCharacteristic_closedFiber).obj T.overClosedFiber

/-- **The projection `X^{(1)} ⟶ X`**, the first projection of the fibre product defining the
Frobenius twist. -/
def twistProjection : T.frobeniusTwistOver.left ⟶ T.global.X :=
  pullback.fst T.global.toClosedFiber
    (absoluteFrobenius (DividedPowerScheme.closedFiber T.global.S) T.global.p
      T.isInCharacteristic_closedFiber)

/-- The structure morphism of `X^{(1)}` is the second projection of the fibre product. -/
theorem frobeniusTwistOver_hom :
    T.frobeniusTwistOver.hom =
      pullback.snd T.global.toClosedFiber
        (absoluteFrobenius (DividedPowerScheme.closedFiber T.global.S) T.global.p
          T.isInCharacteristic_closedFiber) := rfl

/-- The defining square of `X^{(1)}`: the projection to `X` followed by `X ⟶ S₀` is the structure
morphism of `X^{(1)}` followed by the absolute Frobenius of `S₀`. -/
theorem twistProjection_comp_toClosedFiber :
    T.twistProjection ≫ T.global.toClosedFiber =
      T.frobeniusTwistOver.hom ≫
        absoluteFrobenius (DividedPowerScheme.closedFiber T.global.S) T.global.p
          T.isInCharacteristic_closedFiber :=
  pullback.condition

/-- **`X^{(1)}/S` as a global crystalline situation [Stacks, Tag 07MF]**, over the same divided
power base `(S, I, γ)` as `X/S`: the scheme is `X^{(1)}` and the structure morphism to the closed
fibre is the second projection.  The prime is locally nilpotent on `X^{(1)}` because it is on `X`
and the projection `X^{(1)} ⟶ X` induces maps of local rings. -/
def frobeniusTwistSituation : GlobalCrystallineSituation.{u} where
  p := T.global.p
  S := T.global.S
  X := T.frobeniusTwistOver.left
  toClosedFiber := T.frobeniusTwistOver.hom
  prime_locallyNilpotent x := by
    simpa using (T.global.prime_locallyNilpotent (T.twistProjection.base x)).map
      (T.twistProjection.stalkMap x).hom

/-- The divided power base of `X^{(1)}/S` is that of `X/S`. -/
@[simp]
theorem frobeniusTwistSituation_S : (T.frobeniusTwistSituation).S = T.global.S := rfl

/-- The scheme of the situation `X^{(1)}/S` is `X^{(1)}`. -/
@[simp]
theorem frobeniusTwistSituation_X :
    (T.frobeniusTwistSituation).X = T.frobeniusTwistOver.left := rfl

/-- The morphism of `X^{(1)}` to the closed fibre `S₀` is the structure morphism of `X^{(1)}`. -/
@[simp]
theorem frobeniusTwistSituation_toClosedFiber :
    (T.frobeniusTwistSituation).toClosedFiber = T.frobeniusTwistOver.hom := rfl

/-- **The relative Frobenius `F_{X/S₀} : X ⟶ X^{(1)}`** of the proof of [Stacks, Tag 07N5]. -/
def relativeFrobeniusToTwist : T.global.X ⟶ T.frobeniusTwistOver.left :=
  (relativeFrobenius (DividedPowerScheme.closedFiber T.global.S) T.global.p
    T.isInCharacteristic_closedFiber T.overClosedFiber).left

/-- **The first assertion of the proof of [Stacks, Tag 07N5]**: the composition of the relative
Frobenius `F_{X/S₀} : X ⟶ X^{(1)}` with the projection `X^{(1)} ⟶ X` is the absolute Frobenius
`F_X`.

It is the characterising property of the relative Frobenius
`AlgebraicGeometry.relativeFrobenius_fst`, read in the Frobenius crystal situation.

This is a *step* of that proof and not the theorem, so it carries no `@[stacks 07N5]` attribute:
the tag asserts that the canonical map `F_E ∘ (F_X)^*_cris` becomes an isomorphism after
inverting `p`, and this statement does not mention cohomology.  See the "What is and is not
proved" section of the module docstring. -/
theorem relativeFrobeniusToTwist_comp_twistProjection :
    T.relativeFrobeniusToTwist ≫ T.twistProjection = T.frobenius :=
  relativeFrobenius_fst (DividedPowerScheme.closedFiber T.global.S) T.global.p
    T.isInCharacteristic_closedFiber T.overClosedFiber

/-- The relative Frobenius is a morphism over `S₀`: followed by the structure morphism of
`X^{(1)}` it is the structure morphism of `X`. -/
theorem relativeFrobeniusToTwist_comp_toClosedFiber :
    T.relativeFrobeniusToTwist ≫ T.frobeniusTwistOver.hom = T.global.toClosedFiber :=
  relativeFrobenius_snd (DividedPowerScheme.closedFiber T.global.S) T.global.p
    T.isInCharacteristic_closedFiber T.overClosedFiber

/-! ### The two change-of-base functors -/

/-- The square over the closed fibre that `F_{X/S₀} : X ⟶ X^{(1)}` and the identity of `S` make
commute: the relative Frobenius is a morphism over `S₀`. -/
theorem toClosedFiber_comp_closedFiberMap_id :
    T.global.toClosedFiber ≫ DividedPowerScheme.closedFiberMap (𝟙 T.global.S) =
      T.relativeFrobeniusToTwist ≫ (T.frobeniusTwistSituation).toClosedFiber := by
  change _ = T.relativeFrobeniusToTwist ≫ T.frobeniusTwistOver.hom
  rw [DividedPowerScheme.closedFiberMap_id, Category.comp_id,
    T.relativeFrobeniusToTwist_comp_toClosedFiber]

/-- The square over the closed fibre that the projection `X^{(1)} ⟶ X` and `Spec(σ) : S ⟶ S` make
commute: `Spec(σ)` induces the absolute Frobenius of `S₀`, and the resulting square is the
defining square of the fibre product `X^{(1)}`. -/
theorem twistToClosedFiber_comp_closedFiberMap_specSigma :
    (T.frobeniusTwistSituation).toClosedFiber ≫ DividedPowerScheme.closedFiberMap T.specSigma =
      T.twistProjection ≫ T.global.toClosedFiber := by
  change T.frobeniusTwistOver.hom ≫ DividedPowerScheme.closedFiberMap T.specSigma = _
  rw [T.closedFiberMap_specSigma]
  exact T.twistProjection_comp_toClosedFiber.symm

/-- **Change of divided power base along `F_{X/S₀}`**, the functor
`CRIS(X/S) ⥤ CRIS(X^{(1)}/S)` of [Stacks, Tag 07IC] attached to the identity of `S` and to the
relative Frobenius `X ⟶ X^{(1)}`. -/
abbrev twistChangeBase :
    GlobalCrystallineSituation.Thickening T.global ⥤
      GlobalCrystallineSituation.Thickening T.frobeniusTwistSituation :=
  GlobalCrystallineSituation.changeBase T.global T.frobeniusTwistSituation (𝟙 T.global.S)
    T.relativeFrobeniusToTwist T.toClosedFiber_comp_closedFiberMap_id

/-- Change of base along `F_{X/S₀}` is continuous for the big crystalline Zariski topologies,
by `Crystalline.GlobalCrystallineSituation.changeBase_isContinuous`. -/
instance twistChangeBase_isContinuous :
    T.twistChangeBase.IsContinuous (GlobalCrystallineSituation.topology T.global)
      (GlobalCrystallineSituation.topology T.frobeniusTwistSituation) :=
  GlobalCrystallineSituation.changeBase_isContinuous

/-- Change of base along `F_{X/S₀}` leaves the divided power thickening unchanged. -/
@[simp]
theorem twistChangeBase_obj_thickening (A : GlobalCrystallineSituation.Thickening T.global) :
    (T.twistChangeBase.obj A).thickening = A.thickening := rfl

/-- Change of base along `F_{X/S₀}` composes the map to `X` with `F_{X/S₀}`. -/
@[simp]
theorem twistChangeBase_obj_toX (A : GlobalCrystallineSituation.Thickening T.global) :
    (T.twistChangeBase.obj A).toX = A.toX ≫ T.relativeFrobeniusToTwist := rfl

/-- Change of base along `F_{X/S₀}` leaves the map to `S` unchanged. -/
@[simp]
theorem twistChangeBase_obj_toBase (A : GlobalCrystallineSituation.Thickening T.global) :
    (T.twistChangeBase.obj A).toBase = A.toBase :=
  Category.comp_id _

/-- Change of base along `F_{X/S₀}` leaves the source component of a morphism unchanged. -/
@[simp]
theorem twistChangeBase_map_sourceHom {A B : GlobalCrystallineSituation.Thickening T.global}
    (k : A ⟶ B) : (T.twistChangeBase.map k).sourceHom = k.sourceHom := rfl

/-- Change of base along `F_{X/S₀}` leaves the target component of a morphism unchanged. -/
@[simp]
theorem twistChangeBase_map_targetHom {A B : GlobalCrystallineSituation.Thickening T.global}
    (k : A ⟶ B) : (T.twistChangeBase.map k).targetHom = k.targetHom := rfl

/-- **Change of divided power base along `Spec(σ)` and the projection `X^{(1)} ⟶ X`**, the functor
`CRIS(X^{(1)}/S) ⥤ CRIS(X/S)` of [Stacks, Tag 07IC] whose pullback of modules is the base change
`E ↦ E^{(1)}` of the proof of [Stacks, Tag 07N5]. -/
abbrev sigmaChangeBase :
    GlobalCrystallineSituation.Thickening T.frobeniusTwistSituation ⥤
      GlobalCrystallineSituation.Thickening T.global :=
  GlobalCrystallineSituation.changeBase T.frobeniusTwistSituation T.global T.specSigma
    T.twistProjection T.twistToClosedFiber_comp_closedFiberMap_specSigma

/-- Change of base along `Spec(σ)` and the projection `X^{(1)} ⟶ X` is continuous for the big
crystalline Zariski topologies, by
`Crystalline.GlobalCrystallineSituation.changeBase_isContinuous`. -/
instance sigmaChangeBase_isContinuous :
    T.sigmaChangeBase.IsContinuous
      (GlobalCrystallineSituation.topology T.frobeniusTwistSituation)
      (GlobalCrystallineSituation.topology T.global) :=
  GlobalCrystallineSituation.changeBase_isContinuous

/-- Change of base along `Spec(σ)` and `X^{(1)} ⟶ X` leaves the divided power thickening
unchanged. -/
@[simp]
theorem sigmaChangeBase_obj_thickening
    (A : GlobalCrystallineSituation.Thickening T.frobeniusTwistSituation) :
    (T.sigmaChangeBase.obj A).thickening = A.thickening := rfl

/-- Change of base along `Spec(σ)` and `X^{(1)} ⟶ X` composes the map to `S` with `Spec(σ)`. -/
@[simp]
theorem sigmaChangeBase_obj_toBase
    (A : GlobalCrystallineSituation.Thickening T.frobeniusTwistSituation) :
    (T.sigmaChangeBase.obj A).toBase = A.toBase ≫ T.specSigma := rfl

/-- Change of base along `Spec(σ)` and `X^{(1)} ⟶ X` composes the map to `X^{(1)}` with the
projection `X^{(1)} ⟶ X`. -/
@[simp]
theorem sigmaChangeBase_obj_toX
    (A : GlobalCrystallineSituation.Thickening T.frobeniusTwistSituation) :
    (T.sigmaChangeBase.obj A).toX = A.toX ≫ T.twistProjection := rfl

/-- Change of base along `Spec(σ)` and `X^{(1)} ⟶ X` leaves the source component of a
morphism unchanged. -/
@[simp]
theorem sigmaChangeBase_map_sourceHom
    {A B : GlobalCrystallineSituation.Thickening T.frobeniusTwistSituation} (k : A ⟶ B) :
    (T.sigmaChangeBase.map k).sourceHom = k.sourceHom := rfl

/-- Change of base along `Spec(σ)` and `X^{(1)} ⟶ X` leaves the target component of a
morphism unchanged. -/
@[simp]
theorem sigmaChangeBase_map_targetHom
    {A B : GlobalCrystallineSituation.Thickening T.frobeniusTwistSituation} (k : A ⟶ B) :
    (T.sigmaChangeBase.map k).targetHom = k.targetHom := rfl

/-- The Frobenius endofunctor of `CRIS(X/S)` leaves the divided power thickening unchanged. -/
@[simp]
theorem frobeniusChangeBase_obj_thickening
    (A : GlobalCrystallineSituation.Thickening T.global) :
    (T.frobeniusChangeBase.obj A).thickening = A.thickening := rfl

/-- The Frobenius endofunctor of `CRIS(X/S)` composes the map to `S` with `Spec(σ)`. -/
@[simp]
theorem frobeniusChangeBase_obj_toBase (A : GlobalCrystallineSituation.Thickening T.global) :
    (T.frobeniusChangeBase.obj A).toBase = A.toBase ≫ T.specSigma := rfl

/-- The Frobenius endofunctor of `CRIS(X/S)` composes the map to `X` with `F_X`. -/
@[simp]
theorem frobeniusChangeBase_obj_toX (A : GlobalCrystallineSituation.Thickening T.global) :
    (T.frobeniusChangeBase.obj A).toX = A.toX ≫ T.frobenius := rfl

/-- The Frobenius endofunctor of `CRIS(X/S)` leaves the source component of a morphism
unchanged. -/
@[simp]
theorem frobeniusChangeBase_map_sourceHom {A B : GlobalCrystallineSituation.Thickening T.global}
    (k : A ⟶ B) : (T.frobeniusChangeBase.map k).sourceHom = k.sourceHom := rfl

/-- The Frobenius endofunctor of `CRIS(X/S)` leaves the target component of a morphism
unchanged. -/
@[simp]
theorem frobeniusChangeBase_map_targetHom {A B : GlobalCrystallineSituation.Thickening T.global}
    (k : A ⟶ B) : (T.frobeniusChangeBase.map k).targetHom = k.targetHom := rfl

/-- **The two change-of-base functors compose to the Frobenius endofunctor of `CRIS(X/S)`.**

Change of base leaves the underlying divided power thickening of an object untouched and composes
its structure maps with the given pair of morphisms, so the composite of the two functors composes
them with `𝟙 ≫ Spec(σ)` and with `F_{X/S₀} ≫ (X^{(1)} ⟶ X)`.  The first is `Spec(σ)` and the
second is the absolute Frobenius `F_X`, by
`Crystalline.FCrystalSituation.relativeFrobeniusToTwist_comp_twistProjection`; so the composite is
change of base along `Spec(σ)` and `F_X`, which is
`Crystalline.FCrystalSituation.frobeniusChangeBase`.  Every component of the isomorphism is the
identity on the underlying thickening. -/
def twistChangeBaseCompIso :
    T.twistChangeBase ⋙ T.sigmaChangeBase ≅ T.frobeniusChangeBase :=
  NatIso.ofComponents
    (fun A =>
      { hom :=
          { sourceHom := 𝟙 _
            targetHom := 𝟙 _
            immersion_naturality := by simp
            base_naturality := by simp
            toX_naturality := by
              simp only [Functor.comp_obj, sigmaChangeBase_obj_thickening,
                twistChangeBase_obj_thickening, frobeniusChangeBase_obj_thickening,
                frobeniusTwistSituation_X, frobeniusChangeBase_obj_toX, sigmaChangeBase_obj_toX,
                twistChangeBase_obj_toX, Category.id_comp, Category.assoc,
                T.relativeFrobeniusToTwist_comp_twistProjection] }
        inv :=
          { sourceHom := 𝟙 _
            targetHom := 𝟙 _
            immersion_naturality := by simp
            base_naturality := by simp
            toX_naturality := by
              simp only [Functor.comp_obj, sigmaChangeBase_obj_thickening,
                twistChangeBase_obj_thickening, frobeniusChangeBase_obj_thickening,
                frobeniusTwistSituation_X, frobeniusChangeBase_obj_toX, sigmaChangeBase_obj_toX,
                twistChangeBase_obj_toX, Category.id_comp, Category.assoc,
                T.relativeFrobeniusToTwist_comp_twistProjection] }
        hom_inv_id := GlobalCrystallineSituation.Thickening.Hom.ext (by simp) (by simp)
        inv_hom_id := GlobalCrystallineSituation.Thickening.Hom.ext (by simp) (by simp) })
    fun k => GlobalCrystallineSituation.Thickening.Hom.ext (by simp) (by simp)

/-- The composite of the two changes of base is continuous, being a composite of continuous
functors. -/
instance twistChangeBase_comp_sigmaChangeBase_isContinuous :
    (T.twistChangeBase ⋙ T.sigmaChangeBase).IsContinuous
      (GlobalCrystallineSituation.topology T.global)
      (GlobalCrystallineSituation.topology T.global) :=
  Functor.isContinuous_comp _ _ _
    (GlobalCrystallineSituation.topology T.frobeniusTwistSituation) _

/-! ### `F_{X/S₀}^* E^{(1)} = (F_X)^*_cris E` -/

/-- **The pullback `F_{X/S₀}^*` of sheaves of modules**, from sheaves of
`𝒪_{X^{(1)}/S}`-modules to sheaves of `𝒪_{X/S}`-modules. -/
abbrev twistModulePullback :
    SheafOfModules.{u}
        (GlobalCrystallineSituation.crystallineStructureSheaf T.frobeniusTwistSituation) ⥤
      SheafOfModules.{u} (GlobalCrystallineSituation.crystallineStructureSheaf T.global) :=
  GlobalCrystallineSituation.changeBaseModulePullback T.global T.frobeniusTwistSituation
    (𝟙 T.global.S) T.relativeFrobeniusToTwist T.toClosedFiber_comp_closedFiberMap_id

/-- **The base change `E ↦ E^{(1)}` by `Spec(σ)`**, the pullback of a sheaf of
`𝒪_{X/S}`-modules to `CRIS(X^{(1)}/S)` along the square with `X^{(1)} ⟶ X` on top and
`Spec(σ) : S ⟶ S` on the bottom. -/
abbrev sigmaModulePullback :
    SheafOfModules.{u} (GlobalCrystallineSituation.crystallineStructureSheaf T.global) ⥤
      SheafOfModules.{u}
        (GlobalCrystallineSituation.crystallineStructureSheaf T.frobeniusTwistSituation) :=
  GlobalCrystallineSituation.changeBaseModulePullback T.frobeniusTwistSituation T.global
    T.specSigma T.twistProjection T.twistToClosedFiber_comp_closedFiberMap_specSigma

/-- **The second assertion of the proof of [Stacks, Tag 07N5]**:
`F_{X/S₀}^* E^{(1)} = (F_X)^*_cris E`, that is, the base change of a sheaf of
`𝒪_{X/S}`-modules by `Spec(σ)`, pulled back along the relative Frobenius
`F_{X/S₀} : X ⟶ X^{(1)}`, is its Frobenius pullback.

It is deduced here the way the source deduces it: both pullbacks are restriction along a change
of divided power base, the composite of two such restrictions is the restriction along the
composite change of base (`SheafOfModules.pushforwardComp`), and the composite change of base is
change of base along `(𝟙 ≫ Spec(σ), F_{X/S₀} ≫ (X^{(1)} ⟶ X)) = (Spec(σ), F_X)`, which is
`Crystalline.FCrystalSituation.twistChangeBaseCompIso`.  No tensor product is needed anywhere
because the comparison map of structure sheaves for a change of divided power base is the
identity.

This is a *step* of that proof and not the theorem, so it carries no `@[stacks 07N5]` attribute:
it identifies two pullbacks of coefficients and says nothing about the cohomology of either, let
alone about a map becoming invertible after `p` is inverted.  See the "What is and is not proved"
section of the module docstring. -/
def frobeniusModulePullbackIso :
    T.sigmaModulePullback ⋙ T.twistModulePullback ≅ T.frobeniusModulePullback :=
  SheafOfModules.pushforwardComp (F := T.twistChangeBase) (G := T.sigmaChangeBase)
      (GlobalCrystallineSituation.changeBaseStructureHom T.global T.frobeniusTwistSituation
        (𝟙 T.global.S) T.relativeFrobeniusToTwist T.toClosedFiber_comp_closedFiberMap_id)
      (GlobalCrystallineSituation.changeBaseStructureHom T.frobeniusTwistSituation T.global
        T.specSigma T.twistProjection T.twistToClosedFiber_comp_closedFiberMap_specSigma) ≪≫
    SheafOfModules.pushforwardCongr₂ (e := T.twistChangeBaseCompIso.symm)
      (ψ := GlobalCrystallineSituation.changeBaseStructureHom T.global T.global T.specSigma
        T.frobenius T.toClosedFiber_comp_closedFiberMap_specSigma) (he := by ext; rfl)

end Crystalline.FCrystalSituation

end

end
