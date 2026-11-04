module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AlphaPCoverFrobeniusTwistSituation
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.QuasicoherentOfCrystal
public import StacksFrontier.AlgebraicGeometry.Crystalline.FCrystal
public import StacksFrontier.AlgebraicGeometry.Crystalline.FrobeniusRelativeTwist
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.OpenSectionsMoore07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.QuasicoherentCrystal

/-!
# Change of divided power base preserves crystals in quasi-coherent modules

Let `S = (p, (S, I, γ), X)` and `S' = (p, (S', I', γ'), X')` be global crystalline situations
[Stacks, Tag 07MF] and let `(f, g)` be a morphism from the first to the second: a morphism of
divided power schemes `f : S ⟶ S'` and a morphism `g : X ⟶ X'` compatible with the maps to the
closed fibres.  Change of divided power base `changeBase S S' f g h : CRIS(X/S) ⥤ CRIS(X'/S')`
[Stacks, Tag 07IC] leaves the divided power thickening of an object alone and only composes its
structure morphisms with `f` and `g`, and the pullback of sheaves of modules along it,
`changeBaseModulePullback`, is restriction along it.

This file proves that this pullback preserves quasi-coherence, and that followed by the
restriction to the small site `Cris(X/S)` it carries a quasi-coherent sheaf of
`𝒪_{X'/S'}`-modules on `CRIS(X'/S')` to a crystal in quasi-coherent `𝒪_{X/S}`-modules on
`Cris(X/S)`.  The specialisation is the input of [Stacks, Tag 07QB] in the proof of
[Stacks, Tag 07N5]: the base change `E^{(1)}` of an `F`-crystal `E` by `Spec(σ)`, read on the
small site of `X^{(1)}/S`, is a crystal in quasi-coherent modules.

## The proof

Quasi-coherence on either site is [Stacks, Tag 07IT]: local quasi-coherence together with the
crystal condition on the comparison maps of sheaves of modules.  Both pass along change of base
because the restriction `F_T` of the pullback to the ambient scheme of an object `(U, T, δ)` is
the restriction of the given module to the ambient scheme of the image of that object, and the
comparison map of a morphism `k` is the comparison map of the image of `k`.  Both pass along the
restriction from `CRIS(X/S)` to `Cris(X/S)` for the same reason.

## Main results

* `Crystalline.GlobalCrystallineSituation.isQuasicoherentOnSite_changeBaseModulePullback` — the
  pullback along a change of divided power base of a quasi-coherent sheaf of modules on the big
  crystalline site is quasi-coherent.
* `Crystalline.GlobalCrystallineSituation.SmallSite.isQuasiCoherentCrystal_restrictSheafOfModules`
  — the restriction to `Cris(X/S)` of a quasi-coherent sheaf of modules on `CRIS(X/S)` is a
  crystal in quasi-coherent modules.
* `...SmallSite.isQuasiCoherentCrystal_restrictSheafOfModules_changeBaseModulePullback` — the two
  together.
* `Crystalline.FCrystal.isQuasiCoherentCrystal_restrictSheafOfModules_sigmaModulePullback` — the
  base change `E^{(1)}` of an `F`-crystal, restricted to the small site of `X^{(1)}/S`, is a
  crystal in quasi-coherent modules.

## Implementation notes

The comparison maps of the pullback and of the given module live over different global
crystalline situations, and their definitional equality is too expensive to check directly.  As
for `Crystalline.GlobalCrystallineSituation.SmallSite.isSheafCrystal_smallExtendSheafRestriction`,
the identity is consumed through the generic
`Crystalline.GlobalCrystallineSituation.SmallSite.isIso_sheafComparisonOfNatTrans07Q9_pushforward₀`
at the two cheap identifications `restrictOpenFunctor_comp_changeBase` and
`heq_whiskerRight_restrictOpenFunctorMap_changeBase`.  It is applied to
`changeBaseModuleRestriction`, the restriction along change of base with no restriction of
scalars, which is the pullback up to the identity isomorphism `changeBaseModulePullbackIso`.

## References

* [Stacks Project, Tag 07IC](https://stacks.math.columbia.edu/tag/07IC)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 07N5](https://stacks.math.columbia.edu/tag/07N5)
* [Stacks Project, Tag 07QB](https://stacks.math.columbia.edu/tag/07QB)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

variable {S S' : GlobalCrystallineSituation.{u}} (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
  (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)

/-! ### Change of base and the restrictions to the opens of an ambient scheme -/

/-- **Restricting an object of `CRIS(X/S)` to the opens of its ambient scheme commutes with
change of divided power base**, on the nose: change of base leaves the divided power thickening
alone, so the image of the restriction of `A` to an open is the restriction of the image of `A`
to that same open. -/
theorem restrictOpenFunctor_comp_changeBase (A : Thickening S) :
    A.restrictOpenFunctor ⋙ changeBase S S' f g h =
      ((changeBase S S' f g h).obj A).restrictOpenFunctor :=
  rfl

/-- **Restricting a morphism of `CRIS(X/S)` over the opens of the ambient scheme of its target
commutes with change of divided power base**, on the nose: change of base leaves both components
of a morphism alone.  The two natural transformations have equal, but not identical, types,
whence the `HEq`. -/
theorem heq_whiskerRight_restrictOpenFunctorMap_changeBase {A B : Thickening S} (k : A ⟶ B) :
    HEq (Functor.whiskerRight (Thickening.restrictOpenFunctorMap k) (changeBase S S' f g h))
      (Thickening.restrictOpenFunctorMap ((changeBase S S' f g h).map k)) :=
  HEq.rfl

/-! ### The restriction along change of base -/

/-- **The restriction of a sheaf of `𝒪_{X'/S'}`-modules along change of divided power base**:
precomposition with `changeBase`, a sheaf of modules over `𝒪_{X/S}` because change of base
preserves the structure presheaf on the nose (`changeBase_op_comp_crisRing`) and is continuous.
It is the pullback `changeBaseModulePullback` without its restriction of scalars along the
identity, `changeBaseModulePullbackIso`. -/
def changeBaseModuleRestriction (N : SheafOfModules.{u} (crystallineStructureSheaf S')) :
    SheafOfModules.{u} (crystallineStructureSheaf S) where
  val := (PresheafOfModules.pushforward₀ (changeBase S S' f g h) (crisRing S')).obj N.val
  isSheaf := (changeBase S S' f g h).op_comp_isSheaf_of_isSheaf _ _ _ N.isSheaf

/-- **The pullback along change of divided power base is the restriction along it**: the
restriction of scalars along the identity of `𝒪_{X/S}` changes nothing, so the identity is an
isomorphism. -/
def changeBaseModulePullbackIso (N : SheafOfModules.{u} (crystallineStructureSheaf S')) :
    (changeBaseModulePullback S S' f g h).obj N ≅ changeBaseModuleRestriction f g h N :=
  Iso.refl _

/-- **The restriction along change of base of a locally quasi-coherent sheaf of modules is
locally quasi-coherent**, [Stacks, Tag 07IS]: its restriction to the ambient scheme of an object
is the restriction of the given module to the ambient scheme of the image of that object. -/
theorem isLocallyQuasiCoherent_changeBaseModuleRestriction
    (N : SheafOfModules.{u} (crystallineStructureSheaf S')) (hN : IsLocallyQuasiCoherent N) :
    IsLocallyQuasiCoherent (changeBaseModuleRestriction f g h N) :=
  fun A ↦ hN ((changeBase S S' f g h).obj A)

/-- **The restriction along change of base of a crystal in `𝒪_{X'/S'}`-modules is a crystal in
`𝒪_{X/S}`-modules**, [Stacks, Tag 07IS]: the comparison map of a morphism `k` of `CRIS(X/S)` is
the comparison map of `(changeBase S S' f g h).map k`. -/
theorem isSheafCrystal_changeBaseModuleRestriction
    (N : SheafOfModules.{u} (crystallineStructureSheaf S')) (hN : IsSheafCrystal N) :
    IsSheafCrystal (changeBaseModuleRestriction f g h N) := by
  intro A B k
  exact SmallSite.isIso_sheafComparisonOfNatTrans07Q9_pushforward₀ _ _
    (Thickening.restrictOpenFunctorMap k) (changeBase S S' f g h) (crisRing S') N.val
    (LA' := ((changeBase S S' f g h).obj A).restrictOpenFunctor)
    (LB' := ((changeBase S S' f g h).obj B).restrictOpenFunctor)
    (η' := Thickening.restrictOpenFunctorMap ((changeBase S S' f g h).map k))
    (restrictOpenFunctor_comp_changeBase f g h A)
    (restrictOpenFunctor_comp_changeBase f g h B)
    (heq_whiskerRight_restrictOpenFunctorMap_changeBase f g h k) _ _ _ _ _ _ _ _
    (hN _ _ ((changeBase S S' f g h).map k))

/-! ### The pullback along change of base -/

/-- **The pullback along change of divided power base of a locally quasi-coherent sheaf of
modules is locally quasi-coherent**, [Stacks, Tag 07IS]. -/
theorem isLocallyQuasiCoherent_changeBaseModulePullback
    (N : SheafOfModules.{u} (crystallineStructureSheaf S')) (hN : IsLocallyQuasiCoherent N) :
    IsLocallyQuasiCoherent ((changeBaseModulePullback S S' f g h).obj N) :=
  isLocallyQuasiCoherent_changeBaseModuleRestriction f g h N hN

/-- **The pullback along change of divided power base of a crystal in `𝒪_{X'/S'}`-modules is a
crystal in `𝒪_{X/S}`-modules**, [Stacks, Tag 07IS]. -/
theorem isSheafCrystal_changeBaseModulePullback
    (N : SheafOfModules.{u} (crystallineStructureSheaf S')) (hN : IsSheafCrystal N) :
    IsSheafCrystal ((changeBaseModulePullback S S' f g h).obj N) :=
  isSheafCrystal_changeBaseModuleRestriction f g h N hN

/-- **The pullback along change of divided power base of a quasi-coherent sheaf of
`𝒪_{X'/S'}`-modules on `CRIS(X'/S')` is a quasi-coherent sheaf of `𝒪_{X/S}`-modules on
`CRIS(X/S)`.**  By [Stacks, Tag 07IT] on both big sites, quasi-coherence is local
quasi-coherence together with the crystal condition, and both are preserved. -/
theorem isQuasicoherentOnSite_changeBaseModulePullback
    (N : SheafOfModules.{u} (crystallineStructureSheaf S')) (hN : N.IsQuasicoherentOnSite) :
    ((changeBaseModulePullback S S' f g h).obj N).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isLocallyQuasiCoherent
    (isLocallyQuasiCoherent_changeBaseModulePullback f g h N
      (isLocallyQuasiCoherent_of_isQuasicoherentOnSite N hN))
    (isSheafCrystal_changeBaseModulePullback f g h N
      (isSheafCrystal_of_isQuasicoherentOnSite N hN))

namespace SmallSite

/-! ### Restriction to the small site -/

/-- **The restriction to `Cris(X/S)` of a locally quasi-coherent sheaf of `𝒪_{X/S}`-modules on
`CRIS(X/S)` is locally quasi-coherent**, [Stacks, Tag 07IS]: its restriction to the ambient
scheme of an object of the small site is the big-site restriction to the ambient scheme of the
underlying object. -/
theorem isLocallyQuasiCoherent_restrictSheafOfModules
    {N : SheafOfModules.{u} (crystallineStructureSheaf S)}
    (hN : GlobalCrystallineSituation.IsLocallyQuasiCoherent N) :
    IsLocallyQuasiCoherent (restrictSheafOfModules N) :=
  fun A ↦ hN A.obj

/-- **The restriction to `Cris(X/S)` of a quasi-coherent sheaf of `𝒪_{X/S}`-modules on
`CRIS(X/S)` is a crystal in quasi-coherent modules.**  By [Stacks, Tag 07IT] on the big site the
given module is locally quasi-coherent and a crystal; both conditions pass to the restriction,
and by [Stacks, Tag 07IT] on the small site together they are quasi-coherence there. -/
theorem isQuasiCoherentCrystal_restrictSheafOfModules
    {N : SheafOfModules.{u} (crystallineStructureSheaf S)} (hN : N.IsQuasicoherentOnSite) :
    IsQuasiCoherentCrystal S (restrictSheafOfModules N) :=
  have hcrys : IsSheafCrystal (restrictSheafOfModules N) :=
    isSheafCrystal_restrictSheafOfModules
      (GlobalCrystallineSituation.isSheafCrystal_of_isQuasicoherentOnSite N hN)
  ⟨isQuasicoherentOnSite_of_isLocallyQuasiCoherent
    (isLocallyQuasiCoherent_restrictSheafOfModules
      (GlobalCrystallineSituation.isLocallyQuasiCoherent_of_isQuasicoherentOnSite N hN)) hcrys,
    hcrys⟩

/-- **Pulling a quasi-coherent sheaf of modules back along a change of divided power base and
restricting to the small site gives a crystal in quasi-coherent modules.**  For a morphism
`(f, g)` of global crystalline situations from `(S, X)` to `(S', X')` and a quasi-coherent sheaf
`N` of `𝒪_{X'/S'}`-modules on `CRIS(X'/S')`, the restriction to `Cris(X/S)` of its pullback along
`changeBase S S' f g h` is quasi-coherent and a crystal in `𝒪_{X/S}`-modules. -/
theorem isQuasiCoherentCrystal_restrictSheafOfModules_changeBaseModulePullback
    (N : SheafOfModules.{u} (crystallineStructureSheaf S')) (hN : N.IsQuasicoherentOnSite) :
    IsQuasiCoherentCrystal S
      (restrictSheafOfModules ((changeBaseModulePullback S S' f g h).obj N)) :=
  isQuasiCoherentCrystal_restrictSheafOfModules
    (isQuasicoherentOnSite_changeBaseModulePullback f g h N hN)

end SmallSite

end Crystalline.GlobalCrystallineSituation

namespace Crystalline.FCrystal

open GlobalCrystallineSituation GlobalCrystallineSituation.SmallSite

variable {T : FCrystalSituation.{u}} (E : FCrystal T)

/-- **The base change `E^{(1)}` of an `F`-crystal by `Spec(σ)`, restricted to the small site
`Cris(X^{(1)}/S)`, is a crystal in quasi-coherent modules**, the situation `X^{(1)}/S` being
spelled as in [Stacks, Tag 07QB], from `p ∈ I` alone.  An `F`-crystal is quasi-coherent on
`CRIS(X/S)` [Stacks, Tag 07IU], and `E ↦ E^{(1)}` is the pullback along a change of divided power
base. -/
theorem isQuasiCoherentCrystal_restrictSheafOfModules_sigmaModulePullback :
    IsQuasiCoherentCrystal (T.global.frobeniusTwistSituation T.prime_mem)
      (restrictSheafOfModules (T.sigmaModulePullback.obj E.crystal)) :=
  isQuasiCoherentCrystal_restrictSheafOfModules_changeBaseModulePullback _ _ _ E.crystal
    E.isFiniteLocallyFreeQuasicoherentCrystal.isQuasicoherentOnSite

/-- **The base change `E^{(1)}` of an `F`-crystal by `Spec(σ)`, restricted to the small site
`Cris(X^{(1)}/S)`, is a crystal in quasi-coherent modules**, with the situation `X^{(1)}/S`
spelled as `Crystalline.FCrystalSituation.frobeniusTwistSituation`; the two spellings agree by
`Crystalline.FCrystalSituation.frobeniusTwistSituation_eq`. -/
theorem isQuasiCoherentCrystal_restrictSheafOfModules_sigmaModulePullback' :
    IsQuasiCoherentCrystal T.frobeniusTwistSituation
      (restrictSheafOfModules (T.sigmaModulePullback.obj E.crystal)) :=
  isQuasiCoherentCrystal_restrictSheafOfModules_changeBaseModulePullback _ _ _ E.crystal
    E.isFiniteLocallyFreeQuasicoherentCrystal.isQuasicoherentOnSite

end Crystalline.FCrystal
