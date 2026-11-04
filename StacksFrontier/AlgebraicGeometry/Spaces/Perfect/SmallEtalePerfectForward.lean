module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtalePseudoCoherentForward
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectnessAlongAnExactFunctor

/-!
# Stacks 08HG, the direction `E` perfect ⟹ `ε^*E` perfect

Let `S` be a scheme and `E` an object of `D(𝒪_S)`.  Stacks 08HG says that `E` is a perfect object
of `D(𝒪_S)` if and only if `ε^*E` is a perfect object of `D(𝒪_étale)`, where `ε` is the morphism
of ringed sites of Stacks 08H7.  This module proves the forward implication.

## What `ε^*` is here

`ε` is flat — the exactness assertion of Stacks 08H8,
`AlgebraicGeometry.SmallEtale.preservesFiniteLimits_associatedModuleOfSheaf` — so its pullback on
complexes of modules is the termwise associated-module functor and `ε^*` on the derived category is
`CategoryTheory.Functor.mapDerivedCategory` of that functor.  No K-flat resolution and no derived
pullback of Stacks 06YY enter.  This is the same reading of `ε^*` as in clause (1) ⇒ (2) of
Stacks 08HE, `AlgebraicGeometry.SmallEtale.pseudoCoherentToAssociatedModule_of_slice_exact`, and
the two statements are about the same functor.

## Why Stacks 08H6 is not the engine

The source proves this direction by Cohomology on Sites, Lemma 08H6, "perfectness is preserved by
derived pullback".  That result is proved, as
`AlgebraicGeometry.RingedSite.Hom.isPerfect_derivedPullback`, but it cannot be read at `ε`, and
not for want of a transport:

* it is stated for an `AlgebraicGeometry.RingedSite.Hom`, whose two ringed sites must have their
  objects and their morphisms in **one** universe, whereas the small étale ringed site of a scheme
  over `Scheme.{u}` is a `RingedSite.{u + 1, u, u}` — so no `RingedSite.Hom` can hold `ε` at all,
  which is why `ε` is packaged as a `RingedSite.HomGeneral` and as a
  `AlgebraicGeometry.RingedToposSiteHom`; and
* it fixes all three universes of both ringed sites to `0`, which a scheme reaches only at
  `u = 0`.

So the proof below runs the argument again in the universe shape `ε` lives in, through the engine
`AlgebraicGeometry.RingedSite.isPerfect_mapDerivedCategory_of_hypotheses`, which is the
perfectness counterpart of the engine clause (1) ⇒ (2) of Stacks 08HE uses.  That engine is a
transfer of perfectness along an additive exact functor equipped with exact slice factors, a unit
comparison and a localization square, over a family of objects covering the final object; it
mentions no morphism of ringed topoi.

## The one hypothesis carried

Of the engine's ten inputs, nine are available at `ε`:

* the functor is `AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf`, additive and right exact
  as a left adjoint and left exact by the exactness assertion of Stacks 08H8;
* the slice factors are `SheafOfModules.pullback` of the localized comparison
  `AlgebraicGeometry.SmallEtale.sliceStructureMap`, additive and right exact for the same reason;
* the unit comparison is `SheafOfModules.pullbackObjUnitToUnit` of that localized comparison, an
  isomorphism;
* the localization square is `AlgebraicGeometry.SmallEtale.associatedModuleOverIso`, the step
  Stacks 03DV leaves implicit, `(𝓕|_V)^a ≅ (𝓕^a)|_{ε(V)}`;
* the covering is `AlgebraicGeometry.SmallEtale.coversTop_obj_opensToSmallEtale`, the images under
  `ε` of *all* the opens of `S`.

The tenth is left exactness of the associated-module functor of the small étale site *of the
slice over an open*.  It is supplied by
`AlgebraicGeometry.SmallEtale.preservesFiniteLimits_pullback_sliceStructureMap`, which localizes
the whole-site Stacks 08H8 along the open immersion; the same lemma discharges clause (1) ⇒ (2) of
Stacks 08HE.  The implementation notes of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtalePseudoCoherentForward.lean`
record what closing it takes, namely the slice-level flatness
`AlgebraicGeometry.SheafOfModules.IsFlatMapULift` of the slice structure map together with an
instance of the transport
`AlgebraicGeometry.RingedSite.HomGeneral.pullbackModulesToposIsoGeneral` for the slice.  It is
strictly weaker than the conclusion — a statement about one functor on sheaves of modules, with no
mention of perfectness, of a complex or of a derived category — and it is not the content of this
module: deleting it leaves the whole transfer, the square, the covering and the unit comparison,
which is what makes the conclusion perfectness of `ε^*E` rather than a restatement of an
assumption.

## What is not proved

The converse, `ε^*E` perfect ⟹ `E` perfect, is **not** proved.  The source obtains it from the
criterion of Stacks 08G8 together with the converse halves of Stacks 08HE and Stacks 08HF.  The
converse of Stacks 08HF is available —
`AlgebraicGeometry.SmallEtale.hasTorAmplitude_derivedPullback_of_hasTorAmplitude` is the `iff`,
read on the `Type u`-presented model of the small étale ringed topos — but the converse of
Stacks 08HE is not: clause (2) ⇒ (1) of Stacks 08HE is the unproved
`AlgebraicGeometry.SmallEtale.AssociatedModuleToPseudoCoherent`.  Stacks 08G8 is moreover itself
pinned to `RingedSite.{0, 0, 0}`.

## Main results

* `AlgebraicGeometry.SmallEtale.perfectToAssociatedModule_of_slice_exact`: **the direction `E`
  perfect ⟹ `ε^*E` perfect of Stacks 08HG**, with no assumed inputs.

## References

* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 08G8](https://stacks.math.columbia.edu/tag/08G8)
* [Stacks Project, Tag 08H6](https://stacks.math.columbia.edu/tag/08H6)
* [Stacks Project, Tag 08H7](https://stacks.math.columbia.edu/tag/08H7)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
* [Stacks Project, Tag 08HG](https://stacks.math.columbia.edu/tag/08HG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u d d'

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  [HasDerivedCategory.{d}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))]
  [HasDerivedCategory.{d'} (SheafOfModules.{u} (structureSheaf B S hS))]

/-- **Clause (1) of Stacks 08HG**: the object `E` of `D(𝒪_S)` is perfect, in the sense of
Stacks 08G5 on the small Zariski ringed site of `S`. -/
public abbrev IsPerfectZariski
    (E : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))) :
    Prop :=
  S.zariskiRingedSite.IsPerfect E

/-- **Clause (2) of Stacks 08HG**: the pullback `ε^*E` of `E` along the morphism of ringed sites
`ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` of Stacks 08H7 is perfect on the small étale site of `S`.

The derived functor is `CategoryTheory.Functor.mapDerivedCategory` of the associated-module functor
of Stacks 03DU (4), which exists because that functor is additive, right exact and — by the
exactness assertion of Stacks 08H8 — left exact.  This is the sense in which `ε` "is flat hence
defines a pullback on complexes of modules", and it is the reading of `ε^*` that clause (2) of
Stacks 08HE also takes. -/
public abbrev IsPerfectSmallEtale
    (E : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))) :
    Prop :=
  let associated :
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O) ⥤
        SheafOfModules.{u} (structureSheaf B S hS) := associatedModuleOfSheaf B S hS
  letI : associated.Additive := additive_associatedModuleOfSheaf B S hS
  letI : PreservesFiniteLimits associated := preservesFiniteLimits_associatedModuleOfSheaf B S hS
  letI : PreservesFiniteColimits associated :=
    preservesFiniteColimits_associatedModuleOfSheaf B S hS
  (smallEtaleRingedSite B S hS).IsPerfect (associated.mapDerivedCategory.obj E)

/-- **Stacks 08HG, the direction `E` perfect ⟹ `ε^*E` perfect.**

If `E` is a perfect object of `D(𝒪_S)` then `ε^*E` is a perfect object of `D(𝒪_étale)`, `ε` being
the morphism of ringed sites of Stacks 08H7 and `ε^*` the termwise associated-module functor on the
derived category, which is what `ε` being flat means.

Left exactness of the associated-module functor on a slice over an open of `S` is the exactness
assertion of Stacks 08H8 localized at that open, proved by
`AlgebraicGeometry.SmallEtale.preservesFiniteLimits_pullback_sliceStructureMap`.  Everything else
is available: the transfer engine
`AlgebraicGeometry.RingedSite.isPerfect_mapDerivedCategory_of_hypotheses`, the localization square
of Stacks 03DV (`associatedModuleOverIso`), the unit comparison, and the covering
(`coversTop_obj_opensToSmallEtale`). -/
@[stacks 08HG "the direction `E` perfect ⟹ `ε^*E` perfect ONLY. Left exactness of
  `SheafOfModules.pullback (SmallEtale.sliceStructureMap B S hS V)` -- the exactness assertion of
  Stacks 08H8 localized at an open `V` of `S` -- is supplied by
  `AlgebraicGeometry.SmallEtale.preservesFiniteLimits_pullback_sliceStructureMap`, which localizes
  the whole-site 08H8 (`preservesFiniteLimits_associatedModule`) along the open immersion. The
  converse
  direction `ε^*E` perfect ⟹ `E` perfect is NOT proved: the source derives it from Stacks 08G8
  together with the converses of Stacks 08HE and Stacks 08HF, and of those the converse of
  Stacks 08HE does not exist in this tree."]
public theorem perfectToAssociatedModule_of_slice_exact
    (E : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O)))
    (hE : IsPerfectZariski S E) :
    IsPerfectSmallEtale B S hS E := by
  let G : ∀ V : S.Opens, _ := fun V => SheafOfModules.pullback.{u} (sliceStructureMap B S hS V)
  have hη : ∀ V : S.Opens, _ :=
    fun V => asIso (SheafOfModules.pullbackObjUnitToUnit.{u} (sliceStructureMap B S hS V))
  exact RingedSite.isPerfect_mapDerivedCategory_of_hypotheses
    (X := smallEtaleRingedSite B S hS)
    (Y := S.zariskiRingedSite)
    (opensToSmallEtale B S hS) (associatedModuleOfSheaf B S hS)
    G
    (additive_associatedModuleOfSheaf B S hS)
    (preservesFiniteLimits_associatedModuleOfSheaf B S hS)
    (preservesFiniteColimits_associatedModuleOfSheaf B S hS)
    (fun V => SheafOfModules.pullback_additive (sliceStructureMap B S hS V))
    (preservesFiniteLimits_pullback_sliceStructureMap B S hS)
    (fun V => PreservesColimitsOfSize.preservesFiniteColimits.{0, 0}
      (F := SheafOfModules.pullback.{u} (sliceStructureMap B S hS V)))
    inferInstance
    (coversTop_obj_opensToSmallEtale B S hS)
    hη
    (associatedModuleOverIso B S hS) E hE

end AlgebraicGeometry.SmallEtale

end
