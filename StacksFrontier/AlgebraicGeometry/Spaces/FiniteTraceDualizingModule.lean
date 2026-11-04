module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentInternalHom
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentSheavesProperties

/-!
# The dualizing module of a finite morphism of algebraic spaces and its trace

Let `π : Y ⟶ X` be a finite morphism of algebraic spaces and let `𝒜 = π_*𝒪_Y`, a
quasi-coherent sheaf of `𝒪_X`-algebras.  The relative dualizing module `ω_{Y/X}` of `π` is
characterised by an isomorphism

`π_*ω_{Y/X} ≅ 𝓗om_{𝒪_X}(π_*𝒪_Y, 𝒪_X)`

of `π_*𝒪_Y`-modules, and the structure map `𝒪_X ⟶ π_*𝒪_Y` then produces the *trace*

`Tr_π : π_*ω_{Y/X} ⟶ 𝒪_X`.

This file constructs the right-hand side of that characterisation together with the trace.
`AlgebraicGeometry.Space.dualizingPushforward` is the `𝒪_X`-module
`𝓗om_{𝒪_X}(π_*𝒪_Y, 𝒪_X)`, which for an affine — in particular a finite — `π` *is* `π_*ω_{Y/X}`:
the characterising isomorphism is an isomorphism of `π_*𝒪_Y`-modules, so the underlying
`𝒪_X`-module of `π_*ω_{Y/X}` is this internal Hom on the nose.
`AlgebraicGeometry.Space.dualizingTrace` is `Tr_π` on it.  Neither construction needs a
hypothesis on `π`, so none is imposed; finiteness of `π` enters only where the quasi-coherence
and coherence of `π_*𝒪_Y` are used, and those are hypotheses of the results below.

## Main definitions

* `AlgebraicGeometry.Space.pushforwardStructureSection` — the global section `1` of
  `π_*𝒪_Y`.
* `AlgebraicGeometry.Space.pushforwardStructureUnit` — the structure map
  `𝒪_X ⟶ π_*𝒪_Y` of `𝒪_X`-modules, the morphism of modules underlying `π♯`.
* `AlgebraicGeometry.Space.dualizingPushforward` — `π_*ω_{Y/X} = 𝓗om_{𝒪_X}(π_*𝒪_Y, 𝒪_X)`.
* `AlgebraicGeometry.Space.dualizingTrace` — the trace `Tr_π : π_*ω_{Y/X} ⟶ 𝒪_X`,
  "evaluation at `1 ∈ π_*𝒪_Y`".

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_dualizingPushforward` — `π_*ω_{Y/X}` is
  quasi-coherent when `π_*𝒪_Y` is of finite presentation, by Stacks 03M1(6).
* `AlgebraicGeometry.Space.isCoherent_dualizingPushforward` — and coherent when `π_*𝒪_Y` is,
  by Stacks 07UE.
* `AlgebraicGeometry.Space.moduleULift_map_dualizingTrace` — the universe lift of the trace is
  the composite of evaluation at `1` with the universe comparisons it was descended from.

## Implementation notes

The internal Hom used is `AlgebraicGeometry.Space.smallEtaleInternalHomSmall`, the module
universe `u` model of the internal Hom of Stacks 03EM on the small étale ringed site.  Working
at universe `u` is what makes the output comparable with `π_*𝒪_Y` itself, and it is the universe
in which Stacks 03M1(6)
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_internalHomSheafSmall`) is available.

The price is that the two pieces the trace is built from — functoriality of the internal Hom in
its first variable, and the identification `𝓗om_{𝒪_X}(𝒪_X, N) ≅ N` — are available only after
raising the module universe to `u + 1`, because a section of `𝓗om(M, N)` over an étale chart is
a morphism of modules on the slice of the small étale site at that chart, whose objects lie in
`Type (u + 1)`.  The trace is therefore assembled at universe `u + 1`, where
`AlgebraicGeometry.Space.smallEtaleInternalHomMapLeft` and
`AlgebraicGeometry.RingedSite.internalHomSheafULiftUnitIso` live, and brought back down by full
faithfulness of the universe lift
(`Stacks.SheafOfModules.moduleULiftFullyFaithful`).  The universe lift of
`AlgebraicGeometry.Space.dualizingTrace` is pinned to that composite by
`AlgebraicGeometry.Space.moduleULift_map_dualizingTrace`, so the descent is not an
unconstrained choice.

What is *not* here is `ω_{Y/X}` itself, as a module on `Y`.  Producing it from
`dualizingPushforward` is an application of the affine direct image equivalence of Stacks 08AI,
whose target is the category of quasi-coherent `π_*𝒪_Y`-modules; that needs the
`π_*𝒪_Y`-module structure on `𝓗om_{𝒪_X}(π_*𝒪_Y, 𝒪_X)` given by `(a · φ)(b) = φ(a b)`, which
this library does not have for any sheaf of algebras.  See the module documentation of
`StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafUnderlyingModule` for the restriction of
scalars layer such a structure would have to be built against.

## References

* [Stacks Project, Tag 0GUZ](https://stacks.math.columbia.edu/tag/0GUZ), whose proof
  constructs `ω_{Y/X}` and `Tr_π` inline.
* [Stacks Project, Tag 08AI](https://stacks.math.columbia.edu/tag/08AI)
* [Stacks Project, Tag 060Z](https://stacks.math.columbia.edu/tag/060Z)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y X : AlgebraicSpaces B S hS}

/-! ### The structure map `𝒪_X ⟶ π_*𝒪_Y` as a map of modules -/

/-- The global section `1` of `π_*𝒪_Y`.  The sections of `π_*𝒪_Y` over an étale chart of `X`
are the sections of `𝒪_Y` over the base change of that chart, and `π_*𝒪_Y` is the free module
of rank one over the sheaf of rings `π_*𝒪_Y` with its scalars restricted along `π♯`, so its
global sections are those of that free module and `1` is the one its identity morphism names. -/
def pushforwardStructureSection (π : Y ⟶ X) :
    (pushforwardStructureModule B S hS π).sections :=
  (SheafOfModules.unit (structureRingSheafDirectImage B S hS π)).unitHomEquiv
    (𝟙 (SheafOfModules.unit (structureRingSheafDirectImage B S hS π)))

/-- **The structure map `π♯ : 𝒪_X ⟶ π_*𝒪_Y` of Stacks 03G8, as a morphism of
`𝒪_X`-modules.**  It is the morphism out of the free module of rank one corresponding to the
global section `1` of `π_*𝒪_Y`, so a section `r` of `𝒪_X` is sent to `r · 1`, the image of `r`
under the structure map of the algebra `π_*𝒪_Y`. -/
def pushforwardStructureUnit (π : Y ⟶ X) :
    SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) ⟶
      pushforwardStructureModule B S hS π :=
  (pushforwardStructureModule B S hS π).unitHomEquiv.symm
    (pushforwardStructureSection B S hS π)

/-- The global section of `π_*𝒪_Y` corresponding to `pushforwardStructureUnit` is
`pushforwardStructureSection`. -/
@[simp]
theorem unitHomEquiv_pushforwardStructureUnit (π : Y ⟶ X) :
    (pushforwardStructureModule B S hS π).unitHomEquiv
        (pushforwardStructureUnit B S hS π) =
      pushforwardStructureSection B S hS π :=
  Equiv.apply_symm_apply _ _

/-! ### The dualizing module of a finite morphism, pushed forward -/

/-- **The relative dualizing module of a finite morphism of algebraic spaces, pushed forward to
the base**: the internal Hom `𝓗om_{𝒪_X}(π_*𝒪_Y, 𝒪_X)`.

The relative dualizing module `ω_{Y/X}` of [Stacks, Tag 0GUZ] is characterised by an isomorphism
`π_*ω_{Y/X} ≅ 𝓗om_{𝒪_X}(π_*𝒪_Y, 𝒪_X)` of `π_*𝒪_Y`-modules, so for an affine — in particular a
finite — morphism `π` this is `π_*ω_{Y/X}` as an `𝒪_X`-module.  The construction itself needs no
hypothesis on `π`; it is the identification with a pushforward from `Y` that does, through
[Stacks, Tag 08AI]. -/
def dualizingPushforward (π : Y ⟶ X) : Modules.{u, u} B S hS X.1 X.2 :=
  smallEtaleInternalHomSmall B S hS X.1 X.2 (pushforwardStructureModule B S hS π)
    (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))

/-- **Stacks 03M1(6) for `π_*ω_{Y/X}`.**  The pushed-forward relative dualizing module of a
finite morphism is quasi-coherent as soon as `π_*𝒪_Y` is of finite presentation — which it is
whenever `X` is Noetherian, `π_*𝒪_Y` being of finite type by [Stacks, Tag 060Z]. -/
theorem isQuasicoherentOnSite_dualizingPushforward (π : Y ⟶ X)
    (hqc : (pushforwardStructureModule B S hS π).IsQuasicoherentOnSite)
    (hfp : (pushforwardStructureModule B S hS π).IsFinitePresentationOnSite) :
    (dualizingPushforward B S hS π).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_internalHomSheafSmall B S hS X.1 X.2 _ _ hqc
    (SheafOfModules.isQuasicoherentOnSite_unit _) hfp

/-- **Stacks 07UE for `π_*ω_{Y/X}`.**  The pushed-forward relative dualizing module of a finite
morphism is coherent as soon as `π_*𝒪_Y` is. -/
theorem isCoherent_dualizingPushforward (π : Y ⟶ X)
    [IsCoherent B S hS X.1 X.2 (pushforwardStructureModule B S hS π)]
    [IsCoherent B S hS X.1 X.2
      (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))] :
    IsCoherent B S hS X.1 X.2 (dualizingPushforward B S hS π) :=
  isCoherent_smallEtaleInternalHomSmall B S hS X.1 X.2 _ _

/-! ### The trace map -/

section Trace

variable (π : Y ⟶ X)

/-- Raising the module universe of `𝒪_X`-modules from `u` to `u + 1`.  A section of an internal
Hom over an étale chart is a morphism of modules on the slice of the small étale site at that
chart, so the internal Hom of two modules at universe `u` has its sections at `u + 1`; this is
the lift along which the universe-`u` model of the internal Hom is compared with it. -/
abbrev traceLift :=
  Stacks.SheafOfModules.moduleULift.{u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)

/-- The trace at the raised module universe: evaluation at `1 ∈ π_*𝒪_Y`, read through the
identification of the universe lift of the internal Hom with the internal Hom of the universe
lifts. -/
def dualizingTraceLift :
    (traceLift B S hS (X := X)).obj (dualizingPushforward B S hS π) ⟶
      (traceLift B S hS (X := X)).obj
        (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O)) :=
  (smallEtaleInternalHomSmallIso B S hS X.1 X.2 _ _).hom ≫
    (RingedSite.internalHomSheafULiftIso (smallEtaleRingedSite B S hS X.1 X.2)
      (pushforwardStructureModule B S hS π) _).inv ≫
    smallEtaleInternalHomMapLeft B S hS X.1 X.2
      ((traceLift B S hS (X := X)).map (pushforwardStructureUnit B S hS π)) _ ≫
    (RingedSite.internalHomSheafULiftUnitIso (smallEtaleRingedSite B S hS X.1 X.2) _).hom

/-- **The trace `Tr_π : π_*ω_{Y/X} ⟶ 𝒪_X` of a finite morphism of algebraic spaces.**

On an étale chart of `X` it is evaluation at `1 ∈ π_*𝒪_Y`: the structure map
`𝒪_X ⟶ π_*𝒪_Y` of [Stacks, Tag 03G8] is the morphism of modules carrying `1` to `1`, and
`Tr_π` is precomposition with it followed by the identification
`𝓗om_{𝒪_X}(𝒪_X, 𝒪_X) ≅ 𝒪_X`.  This is the map [Stacks, Tag 0GUZ] writes `Tr_π`, and it is the
only global map `π_*𝒪_Y ⟶ 𝒪_X` there is. -/
def dualizingTrace :
    dualizingPushforward B S hS π ⟶
      SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) :=
  (Stacks.SheafOfModules.moduleULiftFullyFaithful.{u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O)).preimage
    (dualizingTraceLift B S hS π)

/-- The universe lift of the trace is the composite it was descended from.  This pins
`AlgebraicGeometry.Space.dualizingTrace` down: the descent along the universe lift is unique
because the lift is fully faithful. -/
theorem moduleULift_map_dualizingTrace :
    (traceLift B S hS (X := X)).map (dualizingTrace B S hS π) =
      dualizingTraceLift B S hS π :=
  (Stacks.SheafOfModules.moduleULiftFullyFaithful.{u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O)).map_preimage _

end Trace

end AlgebraicGeometry.Space

end
