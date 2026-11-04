module

public import StacksFrontier.AlgebraicGeometry.Blowup.Proper
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.CoherentDirectImage
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Triangle
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupChain

/-!
# `Ω_{W'/S₀}` is coherent after a blowup in a closed point

Let `q : W ⟶ S₀` be any morphism of schemes with `W` locally Noetherian and `Ω_{W/S₀}` coherent,
and let `b : W' ⟶ W` be the blowing up of `W` in a closed point. This file proves that
`Ω_{W'/S₀}` and `b^*Ω_{W/S₀}` are coherent.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isCoherent_relativeDifferentials_comp`: for `f : Y ⟶ X` and
  `q : X ⟶ S` with `Y` locally Noetherian, if `f^*Ω_{X/S}` and `Ω_{Y/X}` are coherent then so is
  `Ω_{Y/S}`.
* `AlgebraicGeometry.Scheme.Hom.isCoherent_relativeDifferentials_comp_of_locallyOfFiniteType`:
  the same for a morphism `f` locally of finite type, with `X` locally Noetherian and `Ω_{X/S}`
  coherent.
* `Stacks.BlowupTwistUnit.isCoherent_relativeDifferentials_blowUpToBase_comp` and
  `Stacks.BlowupTwistUnit.isCoherent_pullback_relativeDifferentials_blowUpToBase`: `Ω_{W'/S₀}`
  and `b^*Ω_{W/S₀}` are coherent at the blowup in a closed point.

## References

* [Stacks Project, Tag 01UX](https://stacks.math.columbia.edu/tag/01UX)
* [Stacks Project, Tag 0EBF](https://stacks.math.columbia.edu/tag/0EBF)
* [Stacks Project, Tag 0B4T](https://stacks.math.columbia.edu/tag/0B4T)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {S X Y : Scheme.{u}}

/-- **`Ω_{Y/S}` is coherent as soon as the two outer terms of the fundamental exact sequence
`f^*Ω_{X/S} ⟶ Ω_{Y/S} ⟶ Ω_{Y/X} ⟶ 0` are.** For `f : Y ⟶ X` and `q : X ⟶ S` with `Y` locally
Noetherian, if `f^*Ω_{X/S}` and `Ω_{Y/X}` are coherent then so is `Ω_{Y/S}`. -/
theorem isCoherent_relativeDifferentials_comp (q : X ⟶ S) (f : Y ⟶ X) [IsLocallyNoetherian Y]
    [((Scheme.Modules.pullback f).obj (relativeDifferentials q)).IsCoherent]
    [(relativeDifferentials f).IsCoherent] :
    (relativeDifferentials (f ≫ q)).IsCoherent := by
  have hepi : Epi (f.toRelativeDifferentials q) := toRelativeDifferentials_epi f q
  obtain ⟨hzero, hexact⟩ := toRelativeDifferentials_exact f q
  have : Epi ((ShortComplex.mk _ _ hzero).toCycles ≫
      (ShortComplex.mk _ _ hzero).cyclesIsoKernel.hom) :=
    have : Epi (ShortComplex.mk _ _ hzero).toCycles :=
      (ShortComplex.exact_iff_epi_toCycles _).mp hexact
    epi_comp _ _
  have : (kernel (f.toRelativeDifferentials q)).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_epi
      ((ShortComplex.mk _ _ hzero).toCycles ≫ (ShortComplex.mk _ _ hzero).cyclesIsoKernel.hom)
  exact CoherentAbelian.isCoherent_X₂_of_shortExact
    (ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel (f.toRelativeDifferentials q))
      (show Mono (kernel.ι (f.toRelativeDifferentials q)) from inferInstance) hepi)
    ‹_› ‹_›

/-- **`Ω_{Y/S}` is coherent when `Ω_{X/S}` is and `f : Y ⟶ X` is locally of finite type**, with
`X` locally Noetherian and nothing assumed about `q : X ⟶ S`. -/
theorem isCoherent_relativeDifferentials_comp_of_locallyOfFiniteType (q : X ⟶ S) (f : Y ⟶ X)
    [IsLocallyNoetherian X] [LocallyOfFiniteType f] [(relativeDifferentials q).IsCoherent] :
    (relativeDifferentials (f ≫ q)).IsCoherent :=
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  have := isCoherent_pullback f (relativeDifferentials q)
  have := isCoherent_relativeDifferentials f
  isCoherent_relativeDifferentials_comp q f

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.BlowupTwistUnit

/-- **`Ω_{W'/S₀}` is coherent after the blowup in a closed point.** For `b : W' ⟶ W` the blowing
up of a locally Noetherian `W` in a closed point `w`, and any factorization `W ⟶ S ⟶ S₀` whose
differentials `Ω_{W/S₀}` are coherent, the differentials `Ω_{W'/S₀}` of the composite are
coherent. -/
theorem isCoherent_relativeDifferentials_blowUpToBase_comp {S₀ S W : Scheme.{u}}
    [IsLocallyNoetherian W] (p : S ⟶ S₀) (h : W ⟶ S) (w : W) (hw : IsClosed ({w} : Set W))
    [(Scheme.Hom.relativeDifferentials (h ≫ p)).IsCoherent] :
    (Scheme.Hom.relativeDifferentials
      (AlgebraicGeometry.blowUpToBase
        (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) ≫ (h ≫ p))).IsCoherent :=
  Scheme.Hom.isCoherent_relativeDifferentials_comp_of_locallyOfFiniteType _ _

/-- **`b^*Ω_{W/S₀}` is coherent after the blowup in a closed point.** For `b : W' ⟶ W` the
blowing up of a locally Noetherian `W` in a closed point `w`, and any factorization
`W ⟶ S ⟶ S₀` whose differentials `Ω_{W/S₀}` are coherent, the pullback `b^*Ω_{W/S₀}` is
coherent. -/
theorem isCoherent_pullback_relativeDifferentials_blowUpToBase {S₀ S W : Scheme.{u}}
    [IsLocallyNoetherian W] (p : S ⟶ S₀) (h : W ⟶ S) (w : W) (hw : IsClosed ({w} : Set W))
    [(Scheme.Hom.relativeDifferentials (h ≫ p)).IsCoherent] :
    ((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase
        (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩))).obj
      (Scheme.Hom.relativeDifferentials (h ≫ p))).IsCoherent :=
  have : IsLocallyNoetherian (AlgebraicGeometry.blowUp
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : TopologicalSpace.Closeds W))) :=
    LocallyOfFiniteType.isLocallyNoetherian (AlgebraicGeometry.blowUpToBase
      (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩))
  isCoherent_pullback _ _

end Stacks.BlowupTwistUnit

end
