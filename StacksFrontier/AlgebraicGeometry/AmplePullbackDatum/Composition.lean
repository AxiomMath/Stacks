module

public import StacksFrontier.AlgebraicGeometry.AmpleBridge.BaseChange
public import StacksFrontier.AlgebraicGeometry.AmplePullbackDatum.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.CompositionThreshold

/-!
# Stacks Tag 0C4K over a quasi-compact base, unconditionally

[Stacks, Tag 0C4K]: for `f : X ⟶ Y` and `g : Y ⟶ S` with `S` quasi-compact, `L` ample relative to
`f` and `M` ample relative to `g`, the module `L ⊗ f^* M ^⊗ a` is ample relative to `g ∘ f` for
every `a` beyond a single threshold.

`StacksFrontier/AlgebraicGeometry/RelativeAmple/CompositionThreshold.lean` proves this on the single
premise `Stacks.RelativeAmpleCompositionThreshold.RelativeEventualAffineDatum`, which asks for
`Stacks.AmplePullbackPart1.EventualAffineDatum` for the data restricted over each affine open of
`S`. `Stacks.AmplePullbackDatum.eventualAffineDatum` proves the datum from relative ampleness on
the source and absolute ampleness on the base, so all that is left is to check that the restricted
data satisfy those two hypotheses: ampleness of `M|_{g⁻¹U}` is the defining clause of relative
ampleness of `M` at the affine open `U`, and relative ampleness of `L` restricted to `g⁻¹U` is
[Stacks, Tag 0893], base change of relative ampleness, at the cartesian square of
`AlgebraicGeometry.isPullback_morphismRestrict`.

## Main results

* `Stacks.AmplePullbackDatum.isRelativelyAmple_morphismRestrict`: **relative ampleness restricts to
  an open of the base**, `Stacks.RelativeAmple.IsRelativelyAmple (f ∣_ V) (L|_{f⁻¹V})`.
  `StacksFrontier/AlgebraicGeometry/RelativeAmple/Basic.lean` records that "the stability of relative
  ampleness under restriction of the base to an open is also not stated"; it is a special case of
  the base change already proved.
* `Stacks.AmplePullbackDatum.relativeEventualAffineDatum`:
  `Stacks.RelativeAmpleCompositionThreshold.RelativeEventualAffineDatum`, with no premise.
* `Stacks.AmplePullbackDatum.exists_threshold_isRelativelyAmple_comp`: **[Stacks, Tag 0C4K]**, with
  no premise beyond the source's own hypotheses.

## Implementation notes

`AlgebraicGeometry.isPullback_morphismRestrict f V` presents `f ∣_ V` as the base change of `f`
along `V.ι`, in the orientation `IsPullback (f ∣_ V) (f ⁻¹ᵁ V).ι V.ι f`; the base-change statement
`AlgebraicGeometry.Scheme.Modules.RelativelyAmpleBaseChange` wants the transposed square, so
`CategoryTheory.IsPullback.flip` is applied. That statement is phrased over
`Stacks.RelativeAmple.IsRelativelyAmple`, the spelling of [Stacks, Tag 01VH] that
`AlgebraicGeometry.IsQuasiProjective` uses, and the bridge
`Stacks.AmpleBridge.isRelativelyAmple_iff_isRelativelyAmple` moves between it and
`Stacks.RelativeAmple.IsRelativelyAmple`, over which the rest of this cluster is written. Its
invertibility binder is indexed by `Scheme.ringCatSheaf` rather than by
`Stacks.SheafInternalHom.isSheaf_structureRingPresheaf`, and instance search does not pass between
the two spellings, so the pulled-back module's invertibility is reinstated by hand.

## References

* [Stacks Project, Tag 0C4K](https://stacks.math.columbia.edu/tag/0C4K)
* [Stacks Project, Tag 0893](https://stacks.math.columbia.edu/tag/0893)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
* [EGA II, Proposition 4.6.13 (i)]
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Ample
open Stacks.AmpleLocallyClosed (pullbackModule)
open Stacks.AmplePullbackPart1 (tensorPullbackPowModule)

universe u

namespace Stacks.AmplePullbackDatum

/-! ### Relative ampleness restricted to an open of the base -/

/-- **Relative ampleness restricts to an open of the base.** If `L` is ample relative to
`f : X ⟶ Y` and `V ⊆ Y` is open, then the restriction of `L` to `f⁻¹V` is ample relative to
`f ∣_ V : f⁻¹V ⟶ V`.

`StacksFrontier/AlgebraicGeometry/RelativeAmple/Basic.lean` and
`StacksFrontier/AlgebraicGeometry/RelativeAmpleComposition/Basic.lean` both record this as not stated.
It needs nothing new: `AlgebraicGeometry.isPullback_morphismRestrict` says that `f ∣_ V` is the
base change of `f` along `V.ι`, and base change of relative ampleness is [Stacks, Tag 0893],
`Stacks.AmpleBridge.relativelyAmpleBaseChange`. -/
theorem isRelativelyAmple_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (L : X.Modules)
    [IsInvertibleModule X L] (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) (V : Y.Opens) :
    Stacks.RelativeAmple.IsRelativelyAmple (f ∣_ V) (pullbackModule (f ⁻¹ᵁ V).ι L) := by
  have hinv : IsInvertibleModule (f ⁻¹ᵁ V).toScheme (pullbackModule (f ⁻¹ᵁ V).ι L) :=
    inferInstance
  have : AlgebraicGeometry.SheafOfModules.IsInvertible (f ⁻¹ᵁ V).toScheme.presheaf
      (f ⁻¹ᵁ V).toScheme.ringCatSheaf.2 ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj L) := hinv
  exact (Stacks.AmpleBridge.isRelativelyAmple_iff_isRelativelyAmple _ _).mpr
    (Stacks.AmpleBridge.relativelyAmpleBaseChange (isPullback_morphismRestrict f V).flip L
      ((Stacks.AmpleBridge.isRelativelyAmple_iff_isRelativelyAmple f L).mp hL))

/-! ### The datum over each affine open of the base -/

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (L : X.Modules) (M : Y.Modules)
  [IsInvertibleModule X L] [IsInvertibleModule Y M]

/-- **`Stacks.RelativeAmpleCompositionThreshold.RelativeEventualAffineDatum`, with no premise.**

Over an affine open `U ⊆ S` the restricted data are `f ∣_ (g⁻¹U)`, `L|_{(g ∘ f)⁻¹U}` and
`M|_{g⁻¹U}`. `Stacks.AmplePullbackDatum.eventualAffineDatum` applies to them because the restricted
`L` is ample relative to the restricted `f`
(`Stacks.AmplePullbackDatum.isRelativelyAmple_morphismRestrict`) and the restricted `M` is
*absolutely* ample on `g⁻¹U`, which for `U` affine is the defining clause of relative ampleness of
`M`. -/
theorem relativeEventualAffineDatum (hL : Stacks.RelativeAmple.IsRelativelyAmple f L)
    (hM : Stacks.RelativeAmple.IsRelativelyAmple g M) :
    Stacks.RelativeAmpleCompositionThreshold.RelativeEventualAffineDatum f g L M := fun U hU =>
  eventualAffineDatum (f ∣_ (g ⁻¹ᵁ U)) (pullbackModule (f ⁻¹ᵁ (g ⁻¹ᵁ U)).ι L)
    (pullbackModule (g ⁻¹ᵁ U).ι M) (isRelativelyAmple_morphismRestrict f L hL (g ⁻¹ᵁ U))
    (hM.2 U hU)

/-! ### Stacks Tag 0C4K -/

/-- **[Stacks, Tag 0C4K].** Let `f : X ⟶ Y` and `g : Y ⟶ S` be morphisms of schemes, `L` an
invertible `𝒪_X`-module and `M` an invertible `𝒪_Y`-module. If `S` is quasi-compact, `L` is ample
relative to `f` and `M` is ample relative to `g`, then there is a threshold `n` beyond which
`L ⊗ f^* M ^⊗ a` is ample relative to `g ∘ f`.

`Stacks.RelativeAmpleCompositionThreshold.exists_threshold_isRelativelyAmple_comp` carries the
datum of [Stacks, Tag 01PW] over each affine open of the base as an explicit premise;
`Stacks.AmplePullbackDatum.relativeEventualAffineDatum` discharges it, so nothing is assumed here
beyond the three hypotheses of the source. -/
@[stacks 0C4K]
theorem exists_threshold_isRelativelyAmple_comp [CompactSpace S]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L)
    (hM : Stacks.RelativeAmple.IsRelativelyAmple g M) :
    ∃ n : ℕ, ∀ a : ℕ, n ≤ a → Stacks.RelativeAmple.IsRelativelyAmple (f ≫ g)
      (tensorPullbackPowModule f L M a) :=
  Stacks.RelativeAmpleCompositionThreshold.exists_threshold_isRelativelyAmple_comp f g L M
    (relativeEventualAffineDatum f g L M hL hM) hL hM

end Stacks.AmplePullbackDatum

end
