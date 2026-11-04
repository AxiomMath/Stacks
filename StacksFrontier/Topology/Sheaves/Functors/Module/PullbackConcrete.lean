module

public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.Topology.Sheaves.Sheafify.ModuleStalkSheafification

/-!
# A concrete description of the module pullback along a morphism of ringed spaces

`RingedSpaceModuleAdjunction.modulePullback f` is defined abstractly, as *the* left adjoint of
`modulePullback f`'s partner `modulePushforward f` (Stacks 0096).  Mathlib's
`CategoryTheory.SheafOfModules.pullbackIso` descends that abstract left adjoint to an explicit
composite: forget a sheaf of `𝒪_Y`-modules to a presheaf of modules, pull the presheaf back,
and sheafify the result.  This file records that composite for `modulePullback`.

## Main results

* `RingedSpaceModuleAdjunction.modulePullbackConcrete` identifies `modulePullback f` with
  `forget ⋙ PresheafOfModules.pullback (structureSheafHom f).hom ⋙ sheafification (𝟙 _)`.
* `RingedSpaceModuleAdjunction.modulePullbackStalkIso` reads off the consequence for stalks:
  the stalk of `f^* G` at `x` is the stalk at `x` of the presheaf-level pullback.

## Implementation notes

The two `IsRightAdjoint` hypotheses that `SheafOfModules.pullbackIso` needs — one at the level
of presheaves of modules, one at the level of sheaves — are both available: the presheaf-level
one is Mathlib's `PresheafOfModules.instIsRightAdjointPushforward` for the two small sites
`Opens Y` and `Opens X`, and the sheaf-level one is
`RingedSpaceModuleAdjunction.modulePushforward_isRightAdjoint`.  Since
`CategoryTheory.Functor.IsRightAdjoint` is a `Prop`, the instance `pullbackIso` picks up (which
Mathlib builds from the presheaf-level one through `PullbackConstruction.adjunction`) is equal
by proof irrelevance to the one `modulePullback` is defined with, so no transport is needed and
`pullbackIso` applies to `modulePullback` on the nose.

This is only a change of description: the right-hand side is still built from the abstract left
adjoint `PresheafOfModules.pullback`, for which Mathlib gives no sectionwise formula.  What it
buys is that the sheafification has been separated out, so that any invariant insensitive to
sheafification — a stalk, for instance — may be computed on the presheaf-level pullback.

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Functor

namespace RingedSpaceModuleAdjunction

universe u

/-- The pushforward of *presheaves* of modules along `f^♯` admits a left adjoint.  This is
Mathlib's `PresheafOfModules.instIsRightAdjointPushforward` for the two small sites `Opens Y`
and `Opens X`; it is recorded here because instance search does not find it through the
`sheafCompose` that `structureSheafRing` is built from. -/
instance presheafPushforward_isRightAdjoint {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) :
    (PresheafOfModules.pushforward.{u} (structureSheafHom f).hom).IsRightAdjoint :=
  PresheafOfModules.instIsRightAdjointPushforward _

/-- **The concrete description of the abstract left adjoint `modulePullback`.**

For a morphism of ringed spaces `f : X ⟶ Y`, the pullback functor on sheaves of modules
`f^* : Mod(𝒪_Y) ⥤ Mod(𝒪_X)` — defined as the left adjoint of `f_*` — is isomorphic to the
composite that forgets a sheaf of `𝒪_Y`-modules to a presheaf of modules, applies the
pullback of presheaves of modules along `f^♯`, and sheafifies. -/
noncomputable def modulePullbackConcrete {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) :
    modulePullback f ≅
      SheafOfModules.forget (structureSheafRing Y) ⋙
        PresheafOfModules.pullback.{u} (structureSheafHom f).hom ⋙
          PresheafOfModules.sheafification (R₀ := (structureSheafRing X).obj)
            (𝟙 (structureSheafRing X).obj) :=
  SheafOfModules.pullbackIso (structureSheafHom f)

/-- The canonical `𝒪_{X,x}`-module structure on the stalk at `x` of a presheaf of modules over
the sheaf of rings `structureSheafRing X` of a ringed space.  It is
`Stacks.Sheafify.moduleStalkOfRingSheaf` at `X.sheaf`, recorded again here because
`structureSheafRing X` is a `def` and instance search will not unfold it to
recognise it as `Stacks.Sheafify.ModuleStalkTensor.ringSheaf X.sheaf`. -/
noncomputable instance (priority := 100) moduleStalkOfRingedSpace {X : RingedSpace.{u, u}}
    (P : PresheafOfModules.{u} (structureSheafRing X).obj) (x : X.carrier) :
    Module (X.presheaf.stalk x)
      (ToType (TopCat.Presheaf.stalk (C := Ab.{u}) P.presheaf x)) :=
  Stacks.Sheafify.moduleStalkOfRingSheaf X.sheaf P x

/-- The presheaf-level pullback of a sheaf of `𝒪_Y`-modules: the middle factor of
`modulePullbackConcrete`, before sheafification. -/
noncomputable abbrev modulePullbackPresheaf {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : SheafOfModules.{u} (structureSheafRing Y)) :
    PresheafOfModules.{u} (structureSheafRing X).obj :=
  (PresheafOfModules.pullback.{u} (structureSheafHom f).hom).obj G.val

/-- **The stalks of `f^* G` are the stalks of the presheaf-level pullback.**

For a morphism of ringed spaces `f : X ⟶ Y`, a sheaf of `𝒪_Y`-modules `G` and a point `x : X`,
the stalk at `x` of the pullback `f^* G` is `𝒪_{X,x}`-linearly isomorphic to the stalk at `x` of
the presheaf-level pullback of `G.val`.

This is what `modulePullbackConcrete` buys: `f^* G` is the sheafification of the presheaf-level
pullback, and sheafification does not change stalks. -/
noncomputable def modulePullbackStalkIso {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : SheafOfModules.{u} (structureSheafRing Y)) (x : X.carrier) :
    (TopCat.Presheaf.stalk (C := Ab.{u}) (modulePullbackPresheaf f G).presheaf x)
      ≃ₗ[X.presheaf.stalk x]
        (TopCat.Presheaf.stalk (C := Ab.{u}) ((modulePullback f).obj G).val.presheaf x) :=
  Stacks.Sheafify.stalkIsoOfSheafifyIso X.sheaf (modulePullbackPresheaf f G) x
    ((modulePullbackConcrete f).app G).symm

end RingedSpaceModuleAdjunction

end
