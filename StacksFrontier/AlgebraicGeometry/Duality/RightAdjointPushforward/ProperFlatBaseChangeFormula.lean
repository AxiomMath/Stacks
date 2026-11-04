module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonFlat
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.AffineBaseChangeLocal

/-!
# The twisted inverse image of a base change of a proper flat morphism

Let `S` be a quasi-compact and quasi-separated scheme, let `g : Y ⟶ S` be proper, flat and of
finite presentation, and let `f : X ⟶ S` be a morphism from a quasi-compact quasi-separated
scheme. Write `p : X ×_S Y ⟶ X` and `q : X ×_S Y ⟶ Y` for the two projections and
`ω_{Y/S} = a_g(𝒪_S)` for the relative dualizing complex of [Stacks, Tag 0B6S]. Then the right
adjoint `a_p` of `Rp_* : D_QCoh(𝒪_{X ×_S Y}) ⥤ D_QCoh(𝒪_X)` is

`a_p(M) ≅ Lp^*M ⊗ᴸ Lq^*ω_{Y/S}`,

naturally in `M`. This is the content of [Stacks, Tag 0B6S] used by [Stacks, Tag 0FYX]: the
projection `p` is again proper, flat and of finite presentation, so `a_p(M) ≅ Lp^*M ⊗ a_p(𝒪_X)`
by [Stacks, Tag 0E4K], and `a_p(𝒪_X) ≅ Lq^*a_g(𝒪_S)` by [Stacks, Tag 0AAB] applied to `𝒪_S`,
since `Lf^*𝒪_S = 𝒪_X`.

## Main definitions

* `Stacks.Duality.twistedInverseImageUnitBaseChangeIso` — `Lq^*ω_{Y/S} ≅ a_p(𝒪_X)`.
* `Stacks.Duality.twistedInverseImageFstIso` — `a_p ≅ Lp^*(-) ⊗ᴸ Lq^*ω_{Y/S}`.

## Implementation notes

Everything is at the locally small model, in the monoidal category `D_QCoh` of
`Stacks.Duality.monoidalCategory_quasiCoherentDerivedCategory`. The instance binders on
`X ×_S Y` are consequences of the others; they are binders because the right adjoint `a_p` is
found by instance search from them.

## References

* [Stacks Project, Tag 0B6S](https://stacks.math.columbia.edu/tag/0B6S)
* [Stacks Project, Tag 0E4K](https://stacks.math.columbia.edu/tag/0E4K)
* [Stacks Project, Tag 0AAB](https://stacks.math.columbia.edu/tag/0AAB)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.Duality.DerivedPushforward

universe u

namespace Stacks.Duality

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
  [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace (pullback f g : Scheme.{u})] [QuasiSeparatedSpace (pullback f g : Scheme.{u})]
  [IsProper g] [Flat g] [LocallyOfFinitePresentation g]

/-- **The base change of the relative dualizing complex.** For `g : Y ⟶ S` proper, flat and of
finite presentation, `Lq^*a_g(𝒪_S) ≅ a_p(𝒪_X)` on `X ×_S Y`: the base change map of
[Stacks, Tag 0AA6] at `𝒪_S`, which is invertible by [Stacks, Tag 0AAB], followed by `a_p` of
`Lf^*𝒪_S ≅ 𝒪_X`. -/
def twistedInverseImageUnitBaseChangeIso :
    (quasiCoherentDerivedPullback' (pullback.snd f g)).obj
        ((twistedInverseImage g (isQuasicoherent_homology_derivedPushforward_of_qcqs g)).obj
          (𝟙_ _)) ≅
      (twistedInverseImage (pullback.fst f g)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj (𝟙_ _) := by
  have sq : IsPullback (pullback.snd f g) (pullback.fst f g) g f :=
    (IsPullback.of_hasPullback f g).flip
  haveI := isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent sq
    (torIndependent_of_flat_left g f)
  have hbc := isIso_twistedInverseImageBaseChangeMap_app_of_isProper_of_flat sq
    (derivedStructureSheaf S)
  exact (quasiCoherentDerivedPullback' (pullback.snd f g)).mapIso
      ((twistedInverseImage g _).mapIso (eqToIso (tensorUnit_quasiCoherentDerivedCategory S))) ≪≫
    @asIso _ _ _ _ ((twistedInverseImageBaseChangeMap (pullback.snd f g) (pullback.fst f g) g f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs g)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f) sq).app (derivedStructureSheaf S))
      hbc ≪≫
    (twistedInverseImage (pullback.fst f g) _).mapIso
      ((quasiCoherentDerivedPullback' f).mapIso
          (eqToIso (tensorUnit_quasiCoherentDerivedCategory S).symm) ≪≫
        (Functor.Monoidal.εIso (quasiCoherentDerivedPullback' f)).symm)

/-- **`a_p(M) ≅ Lp^*M ⊗ᴸ Lq^*ω_{Y/S}`, naturally in `M`.** The comparison map
`Lp^*M ⊗ a_p(𝒪_X) ⟶ a_p(M ⊗ 𝒪_X)` of [Stacks, Tag 0A9S] is invertible because `p`, a base change
of `g`, is proper, flat and of finite presentation ([Stacks, Tag 0E4K]); the right unitor, and
`a_p(𝒪_X) ≅ Lq^*ω_{Y/S}` (`Stacks.Duality.twistedInverseImageUnitBaseChangeIso`), finish. -/
def twistedInverseImageFstIso :
    twistedInverseImage (pullback.fst f g)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _) ≅
      quasiCoherentDerivedPullback' (pullback.fst f g) ⋙
        MonoidalCategory.tensorRight ((quasiCoherentDerivedPullback' (pullback.snd f g)).obj
          ((twistedInverseImage g (isQuasicoherent_homology_derivedPushforward_of_qcqs g)).obj
            (𝟙_ _))) := by
  let p := pullback.fst f g
  let hp := isQuasicoherent_homology_derivedPushforward_of_qcqs p
  let adj := quasiCoherentDerivedAdjunction p (isQuasicoherent_homology_derivedPullback' p) hp
  let adj₂ := twistedInverseImageAdjunction p hp
  haveI : ∀ K : quasiCoherentDerivedCategory X,
      IsIso ((adj.comparisonNatTrans adj₂ (𝟙_ _)).app K) := fun K =>
    isIso_comparisonMap_of_flat p K (𝟙_ _)
  haveI : IsIso (adj.comparisonNatTrans adj₂ (𝟙_ _)) := NatIso.isIso_of_isIso_app _
  exact (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight (rightUnitorNatIso _).symm _ ≪≫
    (asIso (adj.comparisonNatTrans adj₂ (𝟙_ _))).symm ≪≫
    Functor.isoWhiskerLeft _ (NatIso.ofComponents
      (fun M => whiskerLeftIso M (twistedInverseImageUnitBaseChangeIso f g).symm)
      (fun _ => (whisker_exchange _ _).symm))

end Stacks.Duality

end
