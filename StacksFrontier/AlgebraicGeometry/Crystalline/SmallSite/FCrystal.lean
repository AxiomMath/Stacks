module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.FCrystal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LowerShriekCounitPullback
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LowerShriekModules
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleRestrictionCohomologyULift
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleUniverseComparison

/-!
# F-crystals on the small crystalline site

In Situation [Stacks, Tag 07N2], [Stacks, Tag 07N3] defines an *F-crystal on `X/S` relative to
`σ`* as a crystal `E` in finite locally free `𝒪_{X/S}`-modules together with a map
`F_E : (F_X)_cris^* E ⟶ E`.  Both halves are read on the **small** crystalline site `Cris(X/S)`:
the crystals of [Stacks, Tag 07IU] are sheaves of `𝒪_{X/S}`-modules on `Cris(X/S)`, and
`(F_X)_cris` is the endomorphism of the small crystalline topos `(X/S)_cris` that the absolute
Frobenius `F_X` and `Spec(σ)` induce by [Stacks, Tag 07IK], namely
`(F_X)_cris = π_X ∘ (F_X)_CRIS ∘ i_X`.

This file states that definition.

* The module is a `Crystalline.GlobalCrystallineSituation.SmallSite.ModuleSheaf`, a sheaf of
  `𝒪_{X/S}`-modules on `Cris(X/S)`.  Its sections are taken in `Type (u + 1)`, the module
  universe at which the inverse image of [Stacks, Tag 07IK] on modules is built, the module-level
  `i_!` of [Stacks, Tag 07IJ] needing a sheafification there.
* The crystal condition is
  `...SmallSite.ModuleSheaf.IsFiniteLocallyFreeQuasicoherentCrystal`,
  the condition of [Stacks, Tag 07IU] on `Cris(X/S)`: quasi-coherence, condition (1) of
  [Stacks, Tag 07IT], together with finite local freeness.  It is the transcription to the raised
  module universe of
  `Crystalline.GlobalCrystallineSituation.SmallSite.IsFiniteLocallyFreeQuasicoherentCrystal`, and
  `...SmallSite.isFiniteLocallyFreeQuasicoherentCrystal_moduleULift`
  carries the latter to the former.
* `(F_X)_cris^*` is `Crystalline.FCrystalSituation.smallFrobeniusModulePullback`, the module
  inverse image `Crystalline.GlobalCrystallineSituation.SmallSite.crisModuleInverseImage` along
  `Spec(σ)` and `F_X`.  That functor is `i_{X, !}` followed by restriction along
  `Cris(X/S) ⥤ CRIS(X/S) ⥤ CRIS(X/S)`, the decomposition of [Stacks, Tag 07IK], and it is the
  pullback of modules along the morphism of ringed topoi `(F_X)_cris`, by
  `Crystalline.GlobalCrystallineSituation.SmallSite.crisModuleInverseImageIsoPullbackModules`.
  No hypothesis on `F_X` is needed: it is not an open immersion, and the construction does not
  ask it to be.

## The big-site notion

`Crystalline.FCrystal` of `StacksFrontier.AlgebraicGeometry.Crystalline.FCrystal` is the analogue on
the big crystalline site `CRIS(X/S)`, with `(F_X)_CRIS^*` in place of `(F_X)_cris^*`.  Every one of
its Frobenius structures gives a Frobenius structure on its restriction to `Cris(X/S)`:
`Crystalline.FCrystal.smallFrobenius` below is that map, the restriction of `F_E` composed with the
comparison `(F_X)_cris^*(i_X^{-1} E) ⟶ i_X^{-1}(F_X)_CRIS^* E` given by the counit of
`i_! ⊣ i^{-1}`, `Crystalline.GlobalCrystallineSituation.SmallSite.lowerShriekCounitPullback`.

## Main definitions

* `Crystalline.FCrystalSituation.smallFrobeniusModulePullback` — `(F_X)_cris^*` on sheaves of
  `𝒪_{X/S}`-modules on the small crystalline site.
* `Crystalline.SmallFCrystal` — an F-crystal on `X/S` relative to `σ`, [Stacks, Tag 07N3].
* `Crystalline.SmallFCrystal.Nondegenerate` — nondegeneracy of an F-crystal,
  [Stacks, Tag 07N3].
* `Crystalline.FCrystal.smallFrobenius` — the Frobenius structure on `Cris(X/S)` that an
  F-crystal on the big crystalline site restricts to.

## Implementation notes

Nondegeneracy quantifies over `i : ℕ`, which carries the source's `i ≥ 0`, and the scalar `p ^ i`
acts on the endomorphism group of `(F_X)_cris^* E` through the `ℕ`-action of the additive group of
morphisms in the abelian category of sheaves of modules.  The source's `V ∘ F_E` is the
diagrammatic composite `F_E ≫ V`, an endomorphism of `(F_X)_cris^* E`.

## References

* [Stacks Project, Tag 07N3](https://stacks.math.columbia.edu/tag/07N3)
* [Stacks Project, Tag 07N2](https://stacks.math.columbia.edu/tag/07N2)
* [Stacks Project, Tag 07IK](https://stacks.math.columbia.edu/tag/07IK)
* [Stacks Project, Tag 07IJ](https://stacks.math.columbia.edu/tag/07IJ)
* [Stacks Project, Tag 07IU](https://stacks.math.columbia.edu/tag/07IU)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Crystalline.FCrystalSituation

open GlobalCrystallineSituation GlobalCrystallineSituation.SmallSite

variable (T : FCrystalSituation.{u})

/-- **The Frobenius pullback `(F_X)_cris^*` of sheaves of `𝒪_{X/S}`-modules on the small
crystalline site `Cris(X/S)`.**  It is the module inverse image along the morphism of crystalline
topoi that `Spec(σ)` and the absolute Frobenius `F_X` induce, [Stacks, Tag 07IK]: the module-level
`i_{X, !}` of [Stacks, Tag 07IJ] followed by restriction along
`Cris(X/S) ⥤ CRIS(X/S) ⥤ CRIS(X/S)`, the second functor being change of divided power base along
`Spec(σ)` and `F_X`. -/
def smallFrobeniusModulePullback : ModuleSheaf T.global ⥤ ModuleSheaf T.global :=
  crisModuleInverseImage T.specSigma T.frobenius T.toClosedFiber_comp_closedFiberMap_specSigma

end Crystalline.FCrystalSituation

namespace Crystalline

open GlobalCrystallineSituation GlobalCrystallineSituation.SmallSite

/-- **Stacks Project, Tag 07N3.**  An *F-crystal on `X/S` relative to `σ`*: a crystal `E` in
finite locally free `𝒪_{X/S}`-modules on the small crystalline site `Cris(X/S)` together with a map
`F_E : (F_X)_cris^* E ⟶ E`.

The crystal in finite locally free modules is the notion of [Stacks, Tag 07IU] on `Cris(X/S)`,
`...SmallSite.ModuleSheaf.IsFiniteLocallyFreeQuasicoherentCrystal`:
quasi-coherence, condition (1) of [Stacks, Tag 07IT], together with finite local freeness.  The
pullback `(F_X)_cris^*` is `Crystalline.FCrystalSituation.smallFrobeniusModulePullback`, the
pullback of modules along `(F_X)_cris = π_X ∘ (F_X)_CRIS ∘ i_X` of [Stacks, Tag 07IK]. -/
@[stacks 07N3 "F-crystal"]
structure SmallFCrystal (T : FCrystalSituation.{u}) where
  /-- The underlying sheaf of `𝒪_{X/S}`-modules `E` on `Cris(X/S)`. -/
  crystal : ModuleSheaf T.global
  /-- It is a crystal in finite locally free modules, [Stacks, Tag 07IU]. -/
  isFiniteLocallyFreeQuasicoherentCrystal :
    ModuleSheaf.IsFiniteLocallyFreeQuasicoherentCrystal crystal
  /-- The Frobenius structure `F_E : (F_X)_cris^* E ⟶ E`. -/
  frobenius : T.smallFrobeniusModulePullback.obj crystal ⟶ crystal

/-- **Stacks Project, Tag 07N3.**  An F-crystal is *nondegenerate* when there are an integer
`i ≥ 0` and a map `V : E ⟶ (F_X)_cris^* E` with `V ∘ F_E = p ^ i`, the composite being taken
diagrammatically as `F_E ≫ V`, an endomorphism of `(F_X)_cris^* E`, and the scalar `p ^ i` acting
through the `ℕ`-action on morphisms. -/
@[stacks 07N3 "nondegenerate"]
def SmallFCrystal.Nondegenerate {T : FCrystalSituation.{u}} (E : SmallFCrystal T) : Prop :=
  ∃ (i : ℕ) (V : E.crystal ⟶ T.smallFrobeniusModulePullback.obj E.crystal),
    E.frobenius ≫ V = (T.global.p ^ i) • 𝟙 (T.smallFrobeniusModulePullback.obj E.crystal)

/-- **The Frobenius structure on `Cris(X/S)` of an F-crystal on the big crystalline site.**  For
`E` a sheaf of `𝒪_{X/S}`-modules on `CRIS(X/S)` with `F_E : (F_X)_CRIS^* E ⟶ E`, the restriction
`i_X^{-1} E` to `Cris(X/S)`, with its sections raised to the module universe of
`Crystalline.SmallFCrystal`, carries the map

`(F_X)_cris^*(i_X^{-1} E) ⟶ i_X^{-1}(F_X)_CRIS^* E ⟶ i_X^{-1} E`,

the first arrow being the restriction of the counit `i_{X, !} i_X^{-1} E ⟶ E`,
`Crystalline.GlobalCrystallineSituation.SmallSite.lowerShriekCounitPullback`, and the second the
restriction of `F_E`. -/
def FCrystal.smallFrobenius {T : FCrystalSituation.{u}} (E : FCrystal T) :
    T.smallFrobeniusModulePullback.obj
        ((moduleULift T.global).obj (restrictSheafOfModules E.crystal)) ⟶
      (moduleULift T.global).obj (restrictSheafOfModules E.crystal) :=
  lowerShriekCounitPullback T.specSigma T.frobenius T.toClosedFiber_comp_closedFiberMap_specSigma
      ((bigModuleULift T.global).obj E.crystal) ≫
    (moduleRestrictι T.global).map ((bigModuleULift T.global).map E.frobenius)

end Crystalline

end
