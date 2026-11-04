module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.ClosedQuotient
public import StacksFrontier.AlgebraicGeometry.Bridge.EssentialImage
import StacksCore.Tactic.StacksAttribute

/-!
# Tag 08KS for a closed quotient morphism, and for a closed immersion of schemes

`Stacks.Tag08KS.modulePushforward_fullyFaithful` and
`Stacks.Tag08KS.modulePushforward_essImage_iff_kernelIdeal_annihilates` are stated for a bare
morphism of ringed spaces carrying the two hypotheses of Stacks Situation 17.6.1. This file
instantiates them twice: at
`RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces`, which bundles exactly those
two hypotheses, and at a closed immersion of schemes, which is where the consumers live.

## Main results

* `Stacks.Tag08KS.ClosedQuotient.modulePushforward_full`,
  `Stacks.Tag08KS.ClosedQuotient.modulePushforward_faithful`,
  `Stacks.Tag08KS.ClosedQuotient.modulePushforward_essImage_iff`: the three statements for a
  bundled closed quotient morphism of ringed spaces.
* `Stacks.Tag08KS.full_pushforward_of_isClosedImmersion` and
  `Stacks.Tag08KS.faithful_pushforward_of_isClosedImmersion`: for a closed immersion of
  schemes, `i_* : Mod(𝒪_Z) ⥤ Mod(𝒪_X)` is full and faithful, as instances.
* `Stacks.Tag08KS.essImage_pushforward_iff_of_isClosedImmersion`: for a closed immersion of
  schemes, a module is a pushforward exactly when the kernel ideal of `i^♯` annihilates it.
* `Stacks.Tag08KS.isIso_unit_app_iff_of_isClosedImmersion`: the same as a criterion for the
  unit of `i^* ⊣ i_*` to be an isomorphism, which is the form Stacks Tag 0C6K's sequences
  consume.

## Implementation notes

**The level change is definitional.** The two ingredients
are `Stacks.SchemeCohomology.modulePushforward_hom`, which says
`RingedSpaceModuleAdjunction.modulePushforward (f.toLRSHom.toShHom) = Scheme.Modules.pushforward f`
by `rfl`, and `Stacks.SchemeCohomology.ringSheaf_ringedSpace`, likewise `rfl`. So no comparison
isomorphism and no transport is needed: the scheme-level statements below are the ringed-space
ones read at a different spelling. In particular there is no need for the route through the
*topos*-level Tag 08M3 (`AlgebraicGeometry.ClosedRingedImmersion`); identifying
`AlgebraicGeometry.RingedToposHom.pushforwardModules` with `Scheme.Modules.pushforward` is not
required, because 08KS's own ringed-space statement is proved directly.

Everything is *also* stated over `SheafOfModules.pushforward i.toRingCatSheafHom`, which is
what `Scheme.Modules.pushforward i` is defined to be. `Scheme.Modules` is a `def`, so an
instance about the wrapper is invisible to search through it, and the consumers state their
arrows over the unwrapped category for that reason — see the implementation notes of
`Stacks.RegularSectionSequence`. Supplying both spellings costs two lines and spares callers
the mismatch.

The two hypotheses are discharged by
`Stacks.AlgebraicGeometry.ClosedImmersion.isClosedEmbedding_base_toShHom` and
`Stacks.AlgebraicGeometry.ClosedImmersion.isLocallySurjective_c_toShHom`.

## References

* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Tag08KS

/-! ### A bundled closed quotient morphism of ringed spaces -/

namespace ClosedQuotient

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})

/-- The kernel ideal of a bundled closed quotient morphism is the kernel ideal of its
underlying morphism: the two spellings are the same ideal, by definition. -/
theorem kernelIdeal_eq (U : Opens S.X) : kernelIdeal S.i U = S.kernelIdeal U := rfl

/-- **Stacks Project, Tag 08KS.** Pushforward of modules along a closed quotient morphism of
ringed spaces is fully faithful. -/
theorem modulePushforward_fullyFaithful :
    Nonempty (modulePushforward S.i).FullyFaithful :=
  Stacks.Tag08KS.modulePushforward_fullyFaithful S.i S.isClosedEmbedding S.isLocallySurjective

/-- Pushforward of modules along a closed quotient morphism of ringed spaces is full. -/
instance modulePushforward_full : (modulePushforward S.i).Full :=
  Stacks.Tag08KS.modulePushforward_full S.i S.isClosedEmbedding S.isLocallySurjective

/-- Pushforward of modules along a closed quotient morphism of ringed spaces is faithful. -/
instance modulePushforward_faithful : (modulePushforward S.i).Faithful :=
  Stacks.Tag08KS.modulePushforward_faithful S.i S.isClosedEmbedding S.isLocallySurjective

/-- **Stacks Project, Tag 08KS.** For a closed quotient morphism of ringed spaces, the essential
image of pushforward of modules is the modules annihilated by the kernel ideal. -/
theorem modulePushforward_essImage_iff (G : SheafOfModules.{u} (structureSheafRing S.X)) :
    (modulePushforward S.i).essImage G ↔
      ∀ (U : Opens S.X) (a : (structureSheafRing S.X).obj.obj (op U)),
        a ∈ S.kernelIdeal U → ∀ m : G.val.obj (op U), a • m = 0 :=
  Stacks.Tag08KS.modulePushforward_essImage_iff_kernelIdeal_annihilates S.i
    S.isClosedEmbedding S.isLocallySurjective G

end ClosedQuotient

/-! ### A closed immersion of schemes -/

section Scheme

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i]

/-- **Stacks Project, Tag 08KS.** Pushforward of modules along a closed immersion of schemes is
full. -/
instance full_pushforward_of_isClosedImmersion :
    (SheafOfModules.pushforward.{u} i.toRingCatSheafHom).Full :=
  modulePushforward_full i.toLRSHom.toShHom
    (Stacks.ClosedImmersion.isClosedEmbedding_base_toShHom i)
    (Stacks.ClosedImmersion.isLocallySurjective_c_toShHom i)

/-- **Stacks Project, Tag 08KS.** Pushforward of modules along a closed immersion of schemes is
faithful. -/
instance faithful_pushforward_of_isClosedImmersion :
    (SheafOfModules.pushforward.{u} i.toRingCatSheafHom).Faithful :=
  modulePushforward_faithful i.toLRSHom.toShHom
    (Stacks.ClosedImmersion.isClosedEmbedding_base_toShHom i)
    (Stacks.ClosedImmersion.isLocallySurjective_c_toShHom i)

/-- Pushforward of modules along a closed immersion of schemes is full, in the
`AlgebraicGeometry.Scheme.Modules` spelling. -/
instance full_schemeModulesPushforward_of_isClosedImmersion :
    (Scheme.Modules.pushforward i).Full :=
  inferInstanceAs (SheafOfModules.pushforward.{u} i.toRingCatSheafHom).Full

/-- Pushforward of modules along a closed immersion of schemes is faithful, in the
`AlgebraicGeometry.Scheme.Modules` spelling. -/
instance faithful_schemeModulesPushforward_of_isClosedImmersion :
    (Scheme.Modules.pushforward i).Faithful :=
  inferInstanceAs (SheafOfModules.pushforward.{u} i.toRingCatSheafHom).Faithful

/-- **Stacks Project, Tag 08KS.** For a closed immersion of schemes `i : Z ⟶ X`, an
`𝒪_X`-module is a pushforward from `Z` exactly when the kernel ideal of `i^♯` annihilates it. -/
theorem essImage_pushforward_iff_of_isClosedImmersion
    (G : SheafOfModules.{u} X.ringCatSheaf) :
    (SheafOfModules.pushforward.{u} i.toRingCatSheafHom).essImage G ↔
      ∀ (U : Opens X) (a : X.ringCatSheaf.obj.obj (op U)),
        a ∈ RingHom.ker (i.toLRSHom.c.app (op U)).hom →
          ∀ m : G.val.obj (op U), a • m = 0 :=
  modulePushforward_essImage_iff_kernelIdeal_annihilates i.toLRSHom.toShHom
    (Stacks.ClosedImmersion.isClosedEmbedding_base_toShHom i)
    (Stacks.ClosedImmersion.isLocallySurjective_c_toShHom i) G

/-- **Stacks Project, Tag 08KS, in the form a cokernel argument consumes.** For a closed
immersion of schemes, the unit of `i^* ⊣ i_*` is an isomorphism at `G` exactly when the kernel
ideal of `i^♯` annihilates `G`.

This is the hypothesis that Stacks Tag 0C6K's sequence lemmas have to assume: see
`Stacks.RegularSectionSequence.exists_cokernelIso_restrictionUnit`, whose `hiso` is this
left-hand side, and `Stacks.Tag0C6KIdealSequence`. Those files spell the adjunction
`SheafOfModules.pullbackPushforwardAdjunction i.toRingCatSheafHom`; that is what
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction` is *defined* to be, and the
`CategoryTheory.Functor.IsRightAdjoint` argument the two spellings carry is a `Prop`, so the
two adjunctions are the same term and this applies to either. -/
theorem isIso_unit_app_iff_of_isClosedImmersion (G : SheafOfModules.{u} X.ringCatSheaf) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app G) ↔
      ∀ (U : Opens X) (a : X.ringCatSheaf.obj.obj (op U)),
        a ∈ RingHom.ker (i.toLRSHom.c.app (op U)).hom →
          ∀ m : G.val.obj (op U), a • m = 0 :=
  (Scheme.Modules.pullbackPushforwardAdjunction
      i).isIso_unit_app_iff_mem_essImage.trans
    (essImage_pushforward_iff_of_isClosedImmersion i G)

end Scheme

end Stacks.Tag08KS
