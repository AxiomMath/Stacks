module

public import StacksFrontier.AlgebraicGeometry.Blowup.StructureSheafPushforward
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.HigherDirectImage

/-!
# `b_*(b^*L) = L` for a blowup in a closed point of a regular surface

Let `W` be an integral regular Noetherian scheme of dimension two, let `w ∈ W` be a closed point
and let `b : W' ⟶ W` be the blowing up of `W` in the reduced point `{w}`. For an **invertible**
`𝒪_W`-module `L`,

`b_*(b^*L) ≅ L`.

This is the degree-zero half of the untwisted branch of the dichotomy of [Stacks, Tag 0B3T], in
the form the induction of [Stacks, Tag 0B4T] consumes it: there `L = (Ω^r_{W/S₀})^{**}`, which is
invertible by [Stacks, Tag 0B3T] itself.

## The route

Three isomorphisms compose, none of them conditional beyond the invertibility of `L`.

1. The left unitor of [Stacks, Tag 01CA] presents `b^*L` as `𝒪_{W'} ⊗ b^*L`.
2. The projection formula for an invertible module in degree zero
   (`Stacks.ProjectionFormula.pushforwardTensorRightNatIso`, the `q = 0` clause of
   [Stacks, Tag 0FZE]) turns `b_*(𝒪_{W'} ⊗ b^*L)` into `(b_*𝒪_{W'}) ⊗ L`.
3. `b_*𝒪_{W'} ≅ 𝒪_W` ([Stacks, Tag 0AY8], the blowing up of a closed point of an integral
   regular Noetherian surface being a modification of a normal integral scheme —
   `AlgebraicGeometry.isIso_unitToPushforwardObjUnit_blowUpToBase_vanishingIdeal_singleton`), and
   the left unitor again.

In particular the computation is **global**: it is available at an arbitrary closed point of an
integral regular Noetherian surface, and not only over the spectrum of a local ring, because its
one geometric input is.

## Main results

The elided prefix is `Stacks.BlowupTwistUnit`.

* `pushforwardUnitIsoUnit`: `b_*𝒪_{W'} ≅ 𝒪_W`, as an isomorphism rather than as the
  invertibility of a map.
* `pushforwardPullbackIso`: **`b_*(b^*L) ≅ L`** for `L` invertible.

## Implementation notes

The tensor products are written through `Stacks.ProjectionFormula.tensorRightInvertible`, the
endofunctor `(-) ⊗_{𝒪} L`, rather than through the bifunctor applied to a pair; that is the
spelling `Stacks.ProjectionFormula.pushforwardTensorRightNatIso` is stated in, and it avoids
writing out the ringed-space structure sheaf as an anonymous constructor.

No derived category occurs, at either model: everything here is the ordinary direct image.

**No `@[stacks]` attribute is placed.** The projection formula is [Stacks, Tag 0FZE] and
`b_*𝒪_{W'} = 𝒪_W` is [Stacks, Tag 0AY8], each registered where it is proved; the composite is
not a statement of the source, but an input of the induction of [Stacks, Tag 0B4T].

## References

* [Stacks Project, Tag 0B4T](https://stacks.math.columbia.edu/tag/0B4T)
* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 0AY8](https://stacks.math.columbia.edu/tag/0AY8)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.BlowupTwistUnit

variable {W : Scheme.{u}} [AlgebraicGeometry.IsIntegral W] [IsNoetherian W]

/-- **`b_*𝒪_{W'} ≅ 𝒪_W`** for the blowing up `b : W' ⟶ W` of an integral regular Noetherian
surface at a closed point, this being
`AlgebraicGeometry.isIso_unitToPushforwardObjUnit_blowUpToBase_vanishingIdeal_singleton`
read as an isomorphism. -/
def pushforwardUnitIsoUnit (hreg : IsRegular W) (hdim : topologicalKrullDim W = 2) (w : W)
    (hw : IsClosed ({w} : Set W)) :
    (Scheme.Modules.pushforward (AlgebraicGeometry.blowUpToBase
        (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))).obj
      (SheafOfModules.unit (AlgebraicGeometry.blowUp
        (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))).ringCatSheaf) ≅
      SheafOfModules.unit W.ringCatSheaf :=
  haveI := AlgebraicGeometry.isIso_unitToPushforwardObjUnit_blowUpToBase_vanishingIdeal_singleton
    hreg hdim w hw
  (asIso (C := W.Modules) (_root_.SheafOfModules.unitToPushforwardObjUnit
    (AlgebraicGeometry.blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
      (⟨{w}, hw⟩ : Closeds W))).toRingCatSheafHom)).symm

/-- **`b_*(b^*L) ≅ L`** for the blowing up `b : W' ⟶ W` of an integral regular Noetherian surface
at a closed point and `L` an invertible `𝒪_W`-module.

The left unitor presents `b^*L` as `𝒪_{W'} ⊗ b^*L`, the projection formula of [Stacks, Tag 0FZE]
in degree zero turns its direct image into `(b_*𝒪_{W'}) ⊗ L`, and
`Stacks.BlowupTwistUnit.pushforwardUnitIsoUnit` followed by the left unitor again gives `L`. -/
def pushforwardPullbackIso (hreg : IsRegular W) (hdim : topologicalKrullDim W = 2) (w : W)
    (hw : IsClosed ({w} : Set W)) (L : W.Modules)
    [Stacks.SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L] :
    (Scheme.Modules.pushforward (AlgebraicGeometry.blowUpToBase
          (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))).obj
        ((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase
          (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))).obj L) ≅ L :=
  (Scheme.Modules.pushforward (AlgebraicGeometry.blowUpToBase
        (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))).mapIso
      (Stacks.RingedSpace.tensorSheafUnitLeftIso
        (AlgebraicGeometry.blowUp (Scheme.IdealSheafData.vanishingIdeal
          (⟨{w}, hw⟩ : Closeds W))).toRingedSpace
        ((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase
          (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))).obj L)).symm ≪≫
    (Stacks.ProjectionFormula.pushforwardTensorRightNatIso
        (AlgebraicGeometry.blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
          (⟨{w}, hw⟩ : Closeds W))) L).app
      (SheafOfModules.unit (AlgebraicGeometry.blowUp
        (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))).ringCatSheaf) ≪≫
    (Stacks.ProjectionFormula.tensorRightInvertible W L).mapIso
      (pushforwardUnitIsoUnit hreg hdim w hw) ≪≫
    Stacks.RingedSpace.tensorSheafUnitLeftIso W.toRingedSpace L

end Stacks.BlowupTwistUnit

end
