module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackFlatReflect
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteUpSheafificationPullback
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAssociatedModuleMonoidal
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedConservativity
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFlatRingedToposHom
import StacksCore.Tactic.StacksAttribute

/-! # Descent, Lemma 05VG for flatness on the small étale site

Let `S` be a scheme of a big étale site `B`.  **Descent, Lemma 05VG** for Modules on Sites,
Definition 03ER (3) at the small site for `τ = étale` says that a sheaf of `𝒪_S`-modules `𝓕` is
flat if and only if its associated module `𝓕ᵃ` on `S_étale` is flat.  This file proves it, as
`AlgebraicGeometry.SmallEtale.isFlat_associatedModule_iff`.

## The two halves

The `only if` half is **Stacks 05VD** at `ε`, `ε^*` being the pullback of sheaves of modules
along the morphism of ringed topoi attached to `ε = id_{small, étale, Zar} : S_étale → S_Zar`.

The `if` half is **étale descent of flatness**, and it is the converse of 05VD at `ε`.  It is not
available from `Stacks.Sheaves.LocalTypeComparison.isFlat_iff`, whose reverse half applies 05VD
to the inverse morphism and therefore needs the pushforward of `ε` to be an equivalence of
topoi — false here, the small étale topos of `S` not being its Zariski topos.  What replaces that
hypothesis is `Stacks.Sheaves.RingedToposModules.isFlat_of_isFlat_pullbackModules`: a pullback of
sheaves of modules which **preserves and reflects monomorphisms** reflects flatness, because
Stacks 03EL carries the tensor endofunctor across it and flatness is the preservation of
monomorphisms by that endofunctor.  Both hypotheses hold at `ε`, and both are assertions of
Stacks 08H8 already proved for an arbitrary `𝒪_S`-module:

* `ε^*` is left exact — `AlgebraicGeometry.SmallEtale.preservesFiniteLimits_associatedModule`,
  the exactness assertion of 08H8 — hence preserves monomorphisms;
* `ε^*` detects the zero object —
  `AlgebraicGeometry.SmallEtale.isZero_of_isZero_associatedModule_general`, the zero-detection
  assertion of 08H8 — and a left exact functor which does so reflects monomorphisms, which is
  `AlgebraicGeometry.SmallEtale.reflectsMonomorphisms_associatedModule`.

So the geometric input to the descent is zero-detection by `ε^*`, and nothing about coverings of
the small étale site has to be handled here.

## No quasi-coherence

`𝓕` is an arbitrary sheaf of `𝒪_S`-modules.  The source's clause carries quasi-coherence, so
this is the clause over a hypothesis weaker than the source's, exactly as at `τ = Zariski`
(`AlgebraicGeometry.SmallZariski.isFlat_iff_associatedModule`).  The reason is different in the
two cases: at `τ = Zariski` the comparison is an equivalence of the whole module categories,
while here it is only exact and zero-detecting, and that is already enough.

## Main results

* `AlgebraicGeometry.SmallEtale.isFlat_associatedModule_iff`: **Descent, Lemma 05VG for
  Modules on Sites, Definition 03ER (3), at the small site for `τ = étale`.**

## Implementation notes

The comparison is taken at `AlgebraicGeometry.SmallEtale.toZariskiRingedToposModulesHom`, the
packaging of `ε` as a `Stacks.Sheaves.RingedToposModules.RingedToposHom` that the pullback of
Stacks 03D6 and the comparison of Stacks 03EL consume, and
`AlgebraicGeometry.SmallEtale.pullbackModulesToZariskiIso` identifies its pullback with the
associated-module functor of Stacks 03DU (4).  The two hypotheses are therefore recorded as
instances at the pullback spelling, transported along that isomorphism; flatness itself is
carried across it by `Stacks.ModuleUp.isFlat_of_iso_anySite`.

The source ringed topos is `RingedTopos.{u, u + 1, u}`, its objects a universe above its
sections, and the target is `RingedTopos.{u, u, u}`; the engine lemma binds the two at six
independent universes, so nothing is narrowed.

## References

* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The two hypotheses of the reflection lemma, at `ε` -/

/-- **`ε^*` is left exact**, read at the pullback-of-modules spelling.

This is `AlgebraicGeometry.SmallEtale.exactFunctor_pullbackModules_toZariskiRingedSiteHom`
applied to the flatness of the structure map of `ε`, which is the input
`AlgebraicGeometry.SmallEtale.preservesFiniteLimits_associatedModule` uses as well. -/
public instance preservesFiniteLimits_pullbackModulesToZariskiToposModules :
    PreservesFiniteLimits
      (pullbackModules.{u, u, u, u + 1, u, u} (toZariskiRingedToposModulesHom B S hS)) :=
  exactFunctor_pullbackModules_toZariskiRingedSiteHom B S hS
    (isFlatMapULift_fSharpInverseImage_toZariskiRingedSiteHom B S hS)

/-- **`ε^*` preserves monomorphisms**, being left exact. -/
public instance preservesMonomorphisms_pullbackModulesToZariskiToposModules :
    (pullbackModules.{u, u, u, u + 1, u, u}
      (toZariskiRingedToposModulesHom B S hS)).PreservesMonomorphisms :=
  CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _

/-- **`ε^*` reflects monomorphisms**, read at the pullback-of-modules spelling.

This is `AlgebraicGeometry.SmallEtale.reflectsMonomorphisms_associatedModule` — left
exactness plus the zero-detection assertion of Stacks 08H8 for an arbitrary `𝒪_S`-module —
transported along `AlgebraicGeometry.SmallEtale.pullbackModulesToZariskiIso`. -/
public instance reflectsMonomorphisms_pullbackModulesToZariskiToposModules :
    (pullbackModules.{u, u, u, u + 1, u, u}
      (toZariskiRingedToposModulesHom B S hS)).ReflectsMonomorphisms :=
  (Functor.ReflectsMonomorphisms.iso_iff (pullbackModulesToZariskiIso B S hS)).mpr
    (reflectsMonomorphisms_associatedModule B S hS)

/-! ### The clause -/

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03ER (3), on the small étale site.**
A sheaf of `𝒪_S`-modules is flat if and only if `𝓕ᵃ` is flat as an `𝒪`-module on `S_étale`.

The `only if` half is Stacks 05VD at `ε`; the `if` half is étale descent of flatness, in the form
`Stacks.Sheaves.RingedToposModules.isFlat_of_isFlat_pullbackModules` — a pullback of sheaves of
modules which preserves and reflects monomorphisms reflects flatness.  Both hypotheses hold at
`ε` by the exactness and zero-detection assertions of Stacks 08H8, recorded above as instances.

`𝓕` is arbitrary: no quasi-coherence is needed, so this is the source's clause over a weaker
hypothesis.  The small Zariski counterpart is
`AlgebraicGeometry.SmallZariski.isFlat_iff_associatedModule`. -/
@[stacks 05VG "flat (03ER (3)), small site at τ = étale, at the comparison functor of 03DX \
itself"]
public theorem isFlat_associatedModule_iff (𝓕 : S.Modules) :
    Stacks.SheafOfModules.IsFlat (O := S.zariskiRingedSite.O) 𝓕 ↔
      Stacks.SheafOfModules.IsFlat (O := (smallEtaleRingedSite B S hS).O)
        ((associatedModule B S hS).obj 𝓕) := by
  rw [Stacks.Sheaves.RingedToposModules.isFlat_iff_pullbackModules_of_reflectsMonomorphisms
    (toZariskiRingedToposModulesHom B S hS) 𝓕]
  have e := (pullbackModulesToZariskiIso B S hS).app 𝓕
  exact ⟨Stacks.ModuleUp.isFlat_of_iso_anySite (O := (smallEtaleRingedSite B S hS).O) e,
    Stacks.ModuleUp.isFlat_of_iso_anySite (O := (smallEtaleRingedSite B S hS).O) e.symm⟩

end AlgebraicGeometry.SmallEtale

end
