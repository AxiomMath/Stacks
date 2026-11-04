module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalizationOfDirectImages
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTraceDualizingModule
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Étale localization of the trace of a finite morphism of algebraic spaces

Let `π : Z ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B` and let `f : X ⟶ Y` be étale.  The relative dualizing module of `π`, pushed forward,
is the dual `𝓗om_{𝒪_Y}(π_*𝒪_Z, 𝒪_Y)` (`AlgebraicGeometry.Space.dualizingPushforward`), and the
trace `Tr_π : π_*ω_{Z/Y} ⟶ 𝒪_Y` of [Stacks, Tag 0GUZ] is evaluation at the global section `1`
of `π_*𝒪_Z` (`AlgebraicGeometry.Space.dualizingTrace`).

This file proves that **the trace commutes with étale restriction on the base**: the restriction
to `X` of `Tr_π` is the trace of the restricted dual, read through the isomorphism

`𝓗om_{𝒪_Y}(ℳ, 𝒩)|_X ≅ 𝓗om_{𝒪_X}(ℳ|_X, 𝒩|_X)`

of `AlgebraicGeometry.Space.etaleModulePullbackInternalHomSmallIso`.

## Main definitions

* `AlgebraicGeometry.Space.dualEvalAtSectionInternalHom` — evaluation of the dual at a global
  section of its argument, on the model `AlgebraicGeometry.Space.smallEtaleInternalHom` of the
  internal Hom whose sections live in `u + 1`.
* `AlgebraicGeometry.Space.dualEvalAtSectionLift` and
  `AlgebraicGeometry.Space.dualEvalAtSection` — the same map on the module-universe-`u` model
  `AlgebraicGeometry.Space.smallEtaleInternalHomSmall`, at the raised universe and brought back
  down.  `AlgebraicGeometry.Space.dualizingTrace` is the value of the latter at the structure
  map `𝒪_Y ⟶ π_*𝒪_Z`, by `rfl`.
* `AlgebraicGeometry.Space.etaleModulePullbackSectionHom` — a global section of an
  `𝒪_Y`-module, read as a global section of its étale restriction.
* `AlgebraicGeometry.Space.etaleSliceDualIso` — the transport of
  `AlgebraicGeometry.Space.smallEtaleInternalHom` along étale restriction, at the raised module
  universe.

## Main results

* `AlgebraicGeometry.Space.traceLift_map_etaleModulePullback_map`: **raising the module
  universe commutes with étale restriction**, on morphisms (on objects it is `rfl`).
* `AlgebraicGeometry.Space.etaleModulePullback_map_dualEvalAtSectionInternalHom`: evaluation of
  the dual at a global section commutes with étale restriction, at the raised module universe.
* `AlgebraicGeometry.Space.etaleModulePullback_map_dualEvalAtSection`: the same at the module
  universe of the schemes — **the universe lift is pushed through the slice equivalence.**
* `AlgebraicGeometry.Space.etaleModulePullback_map_dualizingTrace`: **the trace of
  [Stacks, Tag 0GUZ] commutes with étale restriction on the base.**

## Implementation notes

### Why the universe lift is the whole difficulty

`AlgebraicGeometry.Space.dualizingTrace` is not built where it lives.  Its two ingredients —
functoriality of the internal Hom in its first variable
(`AlgebraicGeometry.Space.smallEtaleInternalHomMapLeft`) and the identification
`𝓗om_{𝒪_Y}(𝒪_Y, 𝒩) ≅ 𝒩` (`AlgebraicGeometry.RingedSite.internalHomSheafULiftUnitIso`) — exist
only at module universe `u + 1`, because a section of an internal Hom over an étale chart is a
morphism of modules on the slice of the small étale site at that chart and the objects of that
slice lie in `Type (u + 1)`.  So the trace is assembled at `u + 1` as
`AlgebraicGeometry.Space.dualizingTraceLift` and descended along the fully faithful universe
lift `Stacks.SheafOfModules.moduleULift`.

Étale restriction, on the other hand, is supplied at module universe `u` by
`AlgebraicGeometry.Space.etaleModulePullbackInternalHomSmallIso`.  Comparing the two therefore
means carrying the slice equivalence of [Stacks, Tag 04M0] through the universe lift.  Three
facts make that possible, and each of them holds on the nose:

* `AlgebraicGeometry.Space.etaleModulePullback` leaves the module universe free, and raising the
  module universe commutes with it **by `rfl` on objects**; on morphisms the two spellings agree
  chartwise, which is
  `AlgebraicGeometry.Space.traceLift_map_etaleModulePullback_map`.  So the comparison
  `Stacks.SheafOfModules.InternalHom.pushforwardModuleULiftIso` that
  `Stacks.SheafOfModules.InternalHom.sliceEquivInternalHomSmallIso` is built with is the
  identity here, and does not appear below.
* `Stacks.SheafOfModules.InternalHom.sliceEquivInternalHomSmallIso` is the preimage, along the
  universe lift, of a composite whose middle factor is
  `Stacks.SheafOfModules.InternalHom.sliceEquivInternalHomIso` at free universes.  That makes
  `AlgebraicGeometry.Space.traceLift_map_etaleModulePullbackInternalHomSmallIso_hom` a chartwise
  identity: the universe lift of the restriction isomorphism at module universe `u` **is** the
  restriction isomorphism at module universe `u + 1`, conjugated by
  `AlgebraicGeometry.Space.smallEtaleInternalHomSmallIso`.
* At module universe `u + 1` the three remaining factors of the trace commute with restriction
  chartwise: restriction along `AlgebraicGeometry.Space.smallEtalePostcomp` reindexes a local
  morphism along the slice functor `X_{ét}/W ⥤ Y_{ét}/f(W)`
  (`Stacks.SheafOfModules.InternalHom.sliceEquivInternalHomIso_hom_app`), the two universe
  comparisons of
  `StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/FinitePresentationKernel.lean` are
  `ULift.up` and `ULift.down` on sections, precomposition is precomposition, and the slice
  functor carries the identity of `W` to the identity of `f(W)` — so
  `AlgebraicGeometry.Space.etaleModulePullback_map_dualEvalAtSectionInternalHom` is again a
  chartwise identity.

The universe-`u` statement then follows by faithfulness of the universe lift, the two
occurrences of `AlgebraicGeometry.Space.smallEtaleInternalHomSmallIso` cancelling.

The whole proof is therefore three chartwise identities and one cancellation.  Every argument of
`Stacks.SheafOfModules.InternalHom.sliceEquivInternalHomIso` is supplied explicitly, as in
`AlgebraicGeometry.Space.etaleModulePullbackInternalHomSmallIso`: left to unification the
instantiation does not elaborate within the heartbeat budget, and the second argument of the
internal Hom must be written out rather than left to be inferred, since solving
`(-)|_X ∘ ?N = 𝒪_X` for `?N` unfolds both the unit module and the restriction functor and does
not terminate.

### What is not proved

**No part of [Stacks, Tag 0GUZ] is claimed, and nothing here carries `@[stacks 0GUZ]`.**

`AlgebraicGeometry.Space.etaleModulePullback_map_dualizingTrace` reads the restricted trace on
`𝓗om_{𝒪_X}((π_*𝒪_Z)|_X, 𝒪_X)`.  The source reads it instead on `𝓗om_{𝒪_X}(p_*𝒪_W, 𝒪_X)` for
the base change `p : W ⟶ X` of `π` along `f`, that is as
`AlgebraicGeometry.Space.dualizingTrace` of `p`, through
`AlgebraicGeometry.Space.etaleModulePullbackDualizingPushforwardIso`, whose second factor moves
the first argument of the internal Hom along Stacks 03LX at the structure sheaf
(`AlgebraicGeometry.Space.pushforwardStructureModuleEtaleBaseChangeIso`, written `ρ` here).
Passing from the statement proved here to that one needs two further inputs, neither of which is
in the development:

* that `ρ` **matches the global sections `1`**: that
  `(-)|_X` applied to `AlgebraicGeometry.Space.pushforwardStructureUnit` of `π`, followed by
  `ρ`, is `AlgebraicGeometry.Space.pushforwardStructureUnit` of `p`.  This is a statement about
  Stacks 03LX at the unit module.  It is true because the isomorphism of Stacks 03LX is induced
  by the morphism of sheaves of *rings*
  `AlgebraicGeometry.Space.baseChangeRingMap`, and a morphism of sheaves of rings carries `1`
  to `1`; but `AlgebraicGeometry.Space.modulePushforwardEtaleBaseChangeIso` is assembled from
  six transports of sheaves of modules and no result reads it on sections, so the reduction to
  that ring map is not available.
* a description of `AlgebraicGeometry.Space.smallEtaleInternalHomSmallCongrLeft` — the second
  factor of `AlgebraicGeometry.Space.etaleModulePullbackDualizingPushforwardIso` — as the
  descent of `AlgebraicGeometry.Space.smallEtaleInternalHomMapLeft`.  That transport is defined
  through `CategoryTheory.MonoidalClosed.internalHom` of
  `AlgebraicGeometry.Space.modulesMonoidalClosed`, hence through
  `CategoryTheory.MonoidalClosed.pre` and the adjunction
  `AlgebraicGeometry.RingedSite.sheafTensorRightInternalHomSmallAdjunction` of Stacks 03EO, and
  is not computed on sections anywhere.

The other step of [Stacks, Tag 0GUZ] that remains is the one that produces the sections; see the
implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalizationOfDirectImages`, which also record that
it needs Stacks 04HL for algebraic spaces.

## References

* [Stacks Project, Tag 0GUZ](https://stacks.math.columbia.edu/tag/0GUZ)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### Evaluation of the dual at a global section -/

/-- **Evaluation of the dual `𝓗om_{𝒪_Y}(A, 𝒪_Y)` at a global section `b : 𝒪_Y ⟶ A`**, on the
model `AlgebraicGeometry.Space.smallEtaleInternalHom` of the internal Hom whose sections live in
`u + 1`.

It is precomposition with `b` followed by the identification `𝓗om_{𝒪_Y}(𝒪_Y, 𝒩) ≅ 𝒩`; the
universe comparison `AlgebraicGeometry.RingedSite.internalHomSheafULiftIso` is what lets the
`u`-module `A` be replaced by its universe lift, which is where
`AlgebraicGeometry.Space.smallEtaleInternalHomMapLeft` and
`AlgebraicGeometry.RingedSite.internalHomSheafULiftUnitIso` live.  This is the composite of the
last three factors of `AlgebraicGeometry.Space.dualizingTraceLift`. -/
def dualEvalAtSectionInternalHom (A : Modules.{u, u} B S hS Y.1 Y.2)
    (b : SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Y.1 Y.2).O) ⟶ A) :
    smallEtaleInternalHom B S hS Y.1 Y.2 A
        (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Y.1 Y.2).O)) ⟶
      (traceLift B S hS (X := Y)).obj
        (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Y.1 Y.2).O)) :=
  (RingedSite.internalHomSheafULiftIso (smallEtaleRingedSite B S hS Y.1 Y.2) A _).inv ≫
    smallEtaleInternalHomMapLeft B S hS Y.1 Y.2 ((traceLift B S hS (X := Y)).map b) _ ≫
    (RingedSite.internalHomSheafULiftUnitIso (smallEtaleRingedSite B S hS Y.1 Y.2) _).hom

/-- **Evaluation of the dual at a global section, at the raised module universe.**  This is
`AlgebraicGeometry.Space.dualizingTraceLift` with the structure map `𝒪_Y ⟶ π_*𝒪_Z` replaced by
an arbitrary global section of an arbitrary `𝒪_Y`-module. -/
def dualEvalAtSectionLift (A : Modules.{u, u} B S hS Y.1 Y.2)
    (b : SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Y.1 Y.2).O) ⟶ A) :
    (traceLift B S hS (X := Y)).obj
        (smallEtaleInternalHomSmall B S hS Y.1 Y.2 A
          (SheafOfModules.unit
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS Y.1 Y.2).O))) ⟶
      (traceLift B S hS (X := Y)).obj
        (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Y.1 Y.2).O)) :=
  (smallEtaleInternalHomSmallIso B S hS Y.1 Y.2 A
      (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Y.1 Y.2).O))).hom ≫
    dualEvalAtSectionInternalHom B S hS A b

/-- **Evaluation of the dual `𝓗om_{𝒪_Y}(A, 𝒪_Y)` at a global section `b : 𝒪_Y ⟶ A`**, at the
module universe of the schemes.

It is `AlgebraicGeometry.Space.dualEvalAtSectionLift` brought down along the fully faithful
universe lift of the sections, exactly as `AlgebraicGeometry.Space.dualizingTrace` is brought
down from `AlgebraicGeometry.Space.dualizingTraceLift`; at the structure map
`𝒪_Y ⟶ π_*𝒪_Z` of [Stacks, Tag 03G8] it **is** that trace, by `rfl`
(`AlgebraicGeometry.Space.dualEvalAtSection_pushforwardStructureUnit`). -/
def dualEvalAtSection (A : Modules.{u, u} B S hS Y.1 Y.2)
    (b : SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Y.1 Y.2).O) ⟶ A) :
    smallEtaleInternalHomSmall B S hS Y.1 Y.2 A
        (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Y.1 Y.2).O)) ⟶
      SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Y.1 Y.2).O) :=
  (Stacks.SheafOfModules.moduleULiftFullyFaithful.{u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS Y.1 Y.2).O)).preimage (dualEvalAtSectionLift B S hS A b)

/-- The universe lift of `AlgebraicGeometry.Space.dualEvalAtSection` is the composite it was
descended from, the lift being fully faithful. -/
theorem traceLift_map_dualEvalAtSection (A : Modules.{u, u} B S hS Y.1 Y.2)
    (b : SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Y.1 Y.2).O) ⟶ A) :
    (traceLift B S hS (X := Y)).map (dualEvalAtSection B S hS A b) =
      dualEvalAtSectionLift B S hS A b :=
  (Stacks.SheafOfModules.moduleULiftFullyFaithful.{u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS Y.1 Y.2).O)).map_preimage _

/-- **The trace `Tr_π` of [Stacks, Tag 0GUZ] is evaluation of the dual at the global section
`1`**: it is `AlgebraicGeometry.Space.dualEvalAtSection` at the structure map
`π^♯ : 𝒪_Y ⟶ π_*𝒪_Z` of [Stacks, Tag 03G8], read as a morphism of `𝒪_Y`-modules. -/
theorem dualEvalAtSection_pushforwardStructureUnit {Z : AlgebraicSpaces B S hS} (π : Z ⟶ Y) :
    dualEvalAtSection B S hS (pushforwardStructureModule B S hS π)
        (pushforwardStructureUnit B S hS π) = dualizingTrace B S hS π :=
  rfl

/-! ### The universe lift under étale restriction -/

/-- **Raising the module universe of the sections commutes with étale restriction**, on
morphisms.  On objects it is `rfl`: étale restriction only reindexes sections along small étale
postcomposition, and the universe lift only applies `ULift` to each module of sections, so the
two commute chartwise. -/
theorem traceLift_map_etaleModulePullback_map (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    {M N : Modules.{u, u} B S hS Y.1 Y.2} (θ : M ⟶ N) :
    (traceLift B S hS (X := X)).map ((etaleModulePullback B S hS f hf).map θ) =
      (etaleModulePullback.{u, u + 1} B S hS f hf).map
        ((traceLift B S hS (X := Y)).map θ) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  rfl

/-- **The internal Hom commutes with étale restriction, at the raised module universe.**  This
is `Stacks.SheafOfModules.InternalHom.sliceEquivInternalHomIso` — the transport of the internal
Hom of Stacks 03EM along a functor of sites which is continuous, cocontinuous (Stacks 03LP) and
an equivalence on every slice (Stacks 04M0) — read at small étale postcomposition along an
étale morphism of algebraic spaces, with the module sections in `u` and the internal Hom's own
sections in `u + 1`.

It is the universe-`u + 1` companion of
`AlgebraicGeometry.Space.etaleModulePullbackInternalHomSmallIso`, which is the preimage of a
composite whose middle factor is exactly this isomorphism.

Its second argument is the structure sheaf, and the restriction of the structure sheaf, read as
the unit module, is the structure sheaf (`AlgebraicGeometry.Space.etaleModulePullback_obj_unit`);
the target is spelled with the unit module of `X` so that the isomorphism composes with
`AlgebraicGeometry.Space.dualEvalAtSectionInternalHom` on `X` without an intervening
definitional unfolding. -/
@[sga "4 IV 12.3" "b), case N = A"]
def etaleSliceDualIso (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (A : Modules.{u, u} B S hS Y.1 Y.2) :
    (etaleModulePullback.{u, u + 1} B S hS f hf).obj
        (smallEtaleInternalHom B S hS Y.1 Y.2 A
          (SheafOfModules.unit
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS Y.1 Y.2).O))) ≅
      smallEtaleInternalHom B S hS X.1 X.2
        ((etaleModulePullback B S hS f hf).obj A)
        (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O)) :=
  @Stacks.SheafOfModules.InternalHom.sliceEquivInternalHomIso.{u + 1, u, u, u}
    (smallEtaleRingedSite B S hS Y.1 Y.2) (smallEtaleRingedSite B S hS X.1 X.2)
    (smallEtalePostcomp B S hS f hf)
    (smallEtaleRingedSite_isContinuous_smallEtalePostcomp B S hS f hf)
    (smallEtalePostcomp_isCocontinuous B S hS f hf)
    (fun W => SmallEtale.isEquivalence_overPostcomp B S hS f hf W)
    (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)))
    (IsIso.id _) A
    (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))

/-- **A global section of an `𝒪_Y`-module, read as a global section of its étale
restriction.**  The restriction of the unit module is the unit module
(`AlgebraicGeometry.Space.etaleModulePullback_obj_unit`), so `b|_X` is a morphism out of the
unit module of `X`; that is what is recorded here, so that the identification is performed once
and the statements below are type-correct without it. -/
def etaleModulePullbackSectionHom (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    {A : Modules.{u, u} B S hS Y.1 Y.2}
    (b : SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Y.1 Y.2).O) ⟶ A) :
    SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O) ⟶
      (etaleModulePullback B S hS f hf).obj A :=
  (etaleModulePullback B S hS f hf).map b

/-- **The universe lift of `AlgebraicGeometry.Space.etaleModulePullbackInternalHomSmallIso` is
`AlgebraicGeometry.Space.etaleSliceDualIso`**, conjugated by the comparison
`AlgebraicGeometry.Space.smallEtaleInternalHomSmallIso` of the two models of the internal Hom.

The isomorphism at module universe `u` is by construction the preimage, along the universe lift,
of a composite of exactly these three factors preceded by
`Stacks.SheafOfModules.InternalHom.pushforwardModuleULiftIso`; that first factor is the identity
here, because raising the module universe commutes with étale restriction chartwise
(`AlgebraicGeometry.Space.traceLift_map_etaleModulePullback_map`).  So the statement holds
chartwise. -/
theorem traceLift_map_etaleModulePullbackInternalHomSmallIso_hom (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) (A : Modules.{u, u} B S hS Y.1 Y.2) :
    (traceLift B S hS (X := X)).map
        (etaleModulePullbackInternalHomSmallIso B S hS f hf A
          (SheafOfModules.unit
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS Y.1 Y.2).O))).hom =
      (etaleModulePullback.{u, u + 1} B S hS f hf).map
          (smallEtaleInternalHomSmallIso B S hS Y.1 Y.2 A
            (SheafOfModules.unit
              (Stacks.SheafOfModules.Tensor.ringSheaf
                (smallEtaleRingedSite B S hS Y.1 Y.2).O))).hom ≫
        (etaleSliceDualIso B S hS f hf A).hom ≫
        (smallEtaleInternalHomSmallIso B S hS X.1 X.2
          ((etaleModulePullback B S hS f hf).obj A)
          (SheafOfModules.unit
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS X.1 X.2).O))).inv := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  rfl

/-! ### The trace under étale restriction -/

/-- **Evaluation of the dual at a global section commutes with étale restriction**, at the
raised module universe.

Over a chart `W` of `X` both sides restrict a local morphism along the slice functor
`X_{ét}/W ⥤ Y_{ét}/f(W)` and then evaluate it at the global section `1` over the identity;
they agree because that slice functor is small étale postcomposition on the nose, which carries
the identity of `W` to the identity of `f(W)`, and because the two universe comparisons of
`AlgebraicGeometry.RingedSite.internalHomSheafULiftIso` and
`AlgebraicGeometry.RingedSite.internalHomSheafULiftUnitIso` are `ULift.up` and `ULift.down` on
sections. -/
theorem etaleModulePullback_map_dualEvalAtSectionInternalHom (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) (A : Modules.{u, u} B S hS Y.1 Y.2)
    (b : SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Y.1 Y.2).O) ⟶ A) :
    (etaleModulePullback.{u, u + 1} B S hS f hf).map
        (dualEvalAtSectionInternalHom B S hS A b) =
      (etaleSliceDualIso B S hS f hf A).hom ≫
        dualEvalAtSectionInternalHom B S hS ((etaleModulePullback B S hS f hf).obj A)
          (etaleModulePullbackSectionHom B S hS f hf b) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro α
  rfl

/-- **Evaluation of the dual at a global section commutes with étale restriction**, at the
module universe of the schemes: for an étale `f : X ⟶ Y` of algebraic spaces, an `𝒪_Y`-module
`A` and a global section `b : 𝒪_Y ⟶ A`,

`(ev_b)|_X = ev_{b|_X}`

under `AlgebraicGeometry.Space.etaleModulePullbackInternalHomSmallIso`.

This is the statement at the universe the trace is *stated* at; it is proved at the universe the
trace is *built* at and descended, the universe lift being faithful.  The two occurrences of
`AlgebraicGeometry.Space.smallEtaleInternalHomSmallIso` introduced by
`AlgebraicGeometry.Space.traceLift_map_etaleModulePullbackInternalHomSmallIso_hom` and by
`AlgebraicGeometry.Space.dualEvalAtSectionLift` cancel. -/
theorem etaleModulePullback_map_dualEvalAtSection (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (A : Modules.{u, u} B S hS Y.1 Y.2)
    (b : SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Y.1 Y.2).O) ⟶ A) :
    (etaleModulePullback B S hS f hf).map (dualEvalAtSection B S hS A b) =
      (etaleModulePullbackInternalHomSmallIso B S hS f hf A
          (SheafOfModules.unit
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS Y.1 Y.2).O))).hom ≫
        dualEvalAtSection B S hS ((etaleModulePullback B S hS f hf).obj A)
          (etaleModulePullbackSectionHom B S hS f hf b) := by
  refine (Stacks.SheafOfModules.moduleULiftFullyFaithful.{u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O)).map_injective ?_
  have h₁ : (traceLift B S hS (X := X)).map
        ((etaleModulePullback B S hS f hf).map (dualEvalAtSection B S hS A b)) =
      (etaleModulePullback.{u, u + 1} B S hS f hf).map
        (dualEvalAtSectionLift B S hS A b) := by
    rw [traceLift_map_etaleModulePullback_map B S hS f hf (dualEvalAtSection B S hS A b),
      traceLift_map_dualEvalAtSection B S hS A b]
  have h₂ : (traceLift B S hS (X := X)).map
        ((etaleModulePullbackInternalHomSmallIso B S hS f hf A
            (SheafOfModules.unit
              (Stacks.SheafOfModules.Tensor.ringSheaf
                (smallEtaleRingedSite B S hS Y.1 Y.2).O))).hom ≫
          dualEvalAtSection B S hS ((etaleModulePullback B S hS f hf).obj A)
            (etaleModulePullbackSectionHom B S hS f hf b)) =
      (traceLift B S hS (X := X)).map
          (etaleModulePullbackInternalHomSmallIso B S hS f hf A
            (SheafOfModules.unit
              (Stacks.SheafOfModules.Tensor.ringSheaf
                (smallEtaleRingedSite B S hS Y.1 Y.2).O))).hom ≫
        ((smallEtaleInternalHomSmallIso B S hS X.1 X.2
              ((etaleModulePullback B S hS f hf).obj A)
              (SheafOfModules.unit
                (Stacks.SheafOfModules.Tensor.ringSheaf
                  (smallEtaleRingedSite B S hS X.1 X.2).O))).hom ≫
          dualEvalAtSectionInternalHom B S hS ((etaleModulePullback B S hS f hf).obj A)
            (etaleModulePullbackSectionHom B S hS f hf b)) := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    rfl
  have h₃ : (etaleModulePullback.{u, u + 1} B S hS f hf).map
        (dualEvalAtSectionLift B S hS A b) =
      (etaleModulePullback.{u, u + 1} B S hS f hf).map
          (smallEtaleInternalHomSmallIso B S hS Y.1 Y.2 A
            (SheafOfModules.unit
              (Stacks.SheafOfModules.Tensor.ringSheaf
                (smallEtaleRingedSite B S hS Y.1 Y.2).O))).hom ≫
        (etaleSliceDualIso B S hS f hf A).hom ≫
          dualEvalAtSectionInternalHom B S hS ((etaleModulePullback B S hS f hf).obj A)
            (etaleModulePullbackSectionHom B S hS f hf b) := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    rfl
  have hcancel : ∀ {W₁ W₂ W₃ W₄ W₅ : Modules.{u, u + 1} B S hS X.1 X.2}
      (p : W₁ ⟶ W₂) (q : W₂ ⟶ W₃) (ι : W₄ ≅ W₃) (r : W₃ ⟶ W₅),
      p ≫ q ≫ r = (p ≫ q ≫ ι.inv) ≫ ι.hom ≫ r := by
    intro W₁ W₂ W₃ W₄ W₅ p q ι r
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]
  refine Eq.trans h₁ (Eq.trans ?_ (Eq.symm h₂))
  rw [h₃, traceLift_map_etaleModulePullbackInternalHomSmallIso_hom B S hS f hf A]
  exact hcancel _ _ _ _

/-- **The trace of [Stacks, Tag 0GUZ] commutes with étale localization on the base.**  Let
`π : Z ⟶ Y` be a morphism of algebraic spaces over `S` and let `f : X ⟶ Y` be étale.  Then the
restriction to `X` of the trace

`Tr_π : π_*ω_{Z/Y} = 𝓗om_{𝒪_Y}(π_*𝒪_Z, 𝒪_Y) ⟶ 𝒪_Y`

is the evaluation of `𝓗om_{𝒪_X}((π_*𝒪_Z)|_X, 𝒪_X)` at the restricted global section `1`, under
the isomorphism `AlgebraicGeometry.Space.etaleModulePullbackInternalHomSmallIso` which commutes
the internal Hom past étale restriction.

No hypothesis on `π` is needed, as none is needed for the trace itself.  See the implementation
notes for what separates this from the form the source uses, which reads the right-hand side on
`𝓗om_{𝒪_X}(p_*𝒪_W, 𝒪_X)` for the base change `p` of `π` along `f`. -/
theorem etaleModulePullback_map_dualizingTrace {Z : AlgebraicSpaces B S hS} (π : Z ⟶ Y)
    (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    (etaleModulePullback B S hS f hf).map (dualizingTrace B S hS π) =
      (etaleModulePullbackInternalHomSmallIso B S hS f hf
          (pushforwardStructureModule B S hS π)
          (SheafOfModules.unit
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS Y.1 Y.2).O))).hom ≫
        dualEvalAtSection B S hS
          ((etaleModulePullback B S hS f hf).obj (pushforwardStructureModule B S hS π))
          (etaleModulePullbackSectionHom B S hS f hf (pushforwardStructureUnit B S hS π)) :=
  etaleModulePullback_map_dualEvalAtSection B S hS f hf (pushforwardStructureModule B S hS π)
    (pushforwardStructureUnit B S hS π)

end AlgebraicGeometry.Space

end
