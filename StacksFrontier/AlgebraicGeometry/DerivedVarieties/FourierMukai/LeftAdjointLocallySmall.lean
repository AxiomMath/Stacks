module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullbackBraided
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentPerfectDual
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.ProperFlatBaseChangeFormula
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleTransport
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.Composition
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.Composition

/-!
# The left adjoint of a Fourier-Mukai transform at the locally small model

Let `S` be a quasi-compact quasi-separated scheme, `g : Y ⟶ S` proper, flat and of finite
presentation with invertible relative dualizing complex `ω = a_g(𝒪_S)`, and `f : X ⟶ S` a
morphism from a quasi-compact quasi-separated scheme. Write `p, q` for the two projections of
`P = X ×_S Y` and let `K` be a perfect object of `D_QCoh(𝒪_P)` with dual `K^∨`. This file proves,
at the locally small model of the derived categories and on `D_QCoh`, that

`N ↦ Rp_*(Lq^*N ⊗ᴸ (K^∨ ⊗ᴸ Lq^*ω))`  is left adjoint to  `M ↦ Rq_*(Lp^*M ⊗ᴸ K)`.

This is the core of [Stacks, Tag 0FYX]. The proof composes four adjunctions,
`Lq^* ⊣ Rq_*`, `- ⊗ K^∨ ⊣ - ⊗ K` (the duality of a perfect object), `- ⊗ W ⊣ - ⊗ W⁻¹` for the
invertible `W = Lq^*ω`, and `Rp_* ⊣ a_p`, and identifies `a_p ⋙ (- ⊗ W⁻¹)` with `Lp^*` through
`a_p(M) ≅ Lp^*M ⊗ W` (`Stacks.Duality.twistedInverseImageFstIso`, i.e. [Stacks, Tag 0E4K] and
[Stacks, Tag 0AAB]).

## Main definitions

* `CategoryTheory.MonoidalCategory.twistedDualAdjunction` — the abstract composite adjunction.
* `Stacks.Duality.fourierMukaiLeftAdjunctionLocallySmall` — the adjunction on `D_QCoh`.

## References

* [Stacks Project, Tag 0FYX](https://stacks.math.columbia.edu/tag/0FYX)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.Duality.DerivedPushforward

universe u

namespace CategoryTheory.MonoidalCategory

variable {C D E : Type*} [Category C] [Category D] [Category E] [MonoidalCategory D]
  [BraidedCategory D]
  {F : C ⥤ D} {G : D ⥤ C} (adjFG : F ⊣ G) {L : E ⥤ D} {R : D ⥤ E} {a : E ⥤ D}
  (adjRa : R ⊣ a) {W : D} (hW : HasInverse W) (e : a ≅ L ⋙ tensorRight W)
  (K Kd : D) [ExactPairing K Kd]

/-- **The left adjoint of `L ⋙ (- ⊗ K) ⋙ G`, twisted by an invertible object.** Given
adjunctions `F ⊣ G` and `R ⊣ a`, an invertible `W` with `a ≅ L ⋙ (- ⊗ W)`, and a dual pair
`(K, Kd)` in a braided monoidal category, the functor `F ⋙ (- ⊗ (Kd ⊗ W)) ⋙ R` is left adjoint to
`L ⋙ (- ⊗ K) ⋙ G`. -/
def twistedDualAdjunction :
    F ⋙ tensorRight (Kd ⊗ W) ⋙ R ⊣ L ⋙ tensorRight K ⋙ G :=
  letI : ExactPairing Kd K := BraidedCategory.exactPairing_swap K Kd
  (((adjFG.comp (tensorRightAdjunction Kd K)).comp
      hW.tensorRightEquivalence.toAdjunction).comp adjRa).ofNatIsoLeft
      (Functor.associator _ _ _ ≪≫ Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft F
          ((Functor.associator _ _ _).symm ≪≫
            Functor.isoWhiskerRight (tensorRightTensor Kd W).symm R)) |>.ofNatIsoRight
    (Functor.isoWhiskerRight e _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft L ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight hW.tensorRightEquivalence.unitIso.symm _ ≪≫
        Functor.leftUnitor _))

end CategoryTheory.MonoidalCategory

namespace Stacks.Duality

section FourierMukai

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- The Fourier-Mukai transform `M ↦ Rq_*(Lp^*M ⊗ᴸ K)` on `D_QCoh` at the locally small model,
`p` and `q` being the two projections of `X ×_S Y`. -/
abbrev fourierMukaiLocallySmall [QuasiCompact f] [QuasiSeparated f] [CompactSpace Y]
    (K : quasiCoherentDerivedCategory (pullback f g)) :
    quasiCoherentDerivedCategory X ⥤ quasiCoherentDerivedCategory Y :=
  quasiCoherentDerivedPullback' (pullback.fst f g) ⋙ MonoidalCategory.tensorRight K ⋙
    quasiCoherentDerivedPushforward (pullback.snd f g)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)

/-- The transform `N ↦ Rp_*(Lq^*N ⊗ᴸ K')` on `D_QCoh` at the locally small model, computed on
`X ×_S Y`. -/
abbrev fourierMukaiDualLocallySmall [QuasiCompact g] [QuasiSeparated g] [CompactSpace X]
    (K' : quasiCoherentDerivedCategory (pullback f g)) :
    quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X :=
  quasiCoherentDerivedPullback' (pullback.snd f g) ⋙ MonoidalCategory.tensorRight K' ⋙
    quasiCoherentDerivedPushforward (pullback.fst f g)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)

end FourierMukai

section Core

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
  [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace (pullback f g : Scheme.{u})] [QuasiSeparatedSpace (pullback f g : Scheme.{u})]
  [IsProper g] [Flat g] [LocallyOfFinitePresentation g] [QuasiCompact f] [QuasiSeparated f]

/-- The relative dualizing complex `ω_{Y/S} = a_g(𝒪_S)` of [Stacks, Tag 0B6S], pulled back to
`X ×_S Y` along the second projection. -/
abbrev pulledBackDualizingComplex : quasiCoherentDerivedCategory (pullback f g) :=
  (quasiCoherentDerivedPullback' (pullback.snd f g)).obj
    ((twistedInverseImage g (isQuasicoherent_homology_derivedPushforward_of_qcqs g)).obj (𝟙_ _))

/-- **The core of [Stacks, Tag 0FYX] at the locally small model.** If `ω_{Y/S} = a_g(𝒪_S)` is
invertible and `K` is perfect, then `N ↦ Rp_*(Lq^*N ⊗ᴸ (K^∨ ⊗ᴸ Lq^*ω))` is left adjoint to the
Fourier-Mukai transform `M ↦ Rq_*(Lp^*M ⊗ᴸ K)` on `D_QCoh`. -/
def fourierMukaiLeftAdjunctionLocallySmall
    (hω : IsInvertible
      ((twistedInverseImage g (isQuasicoherent_homology_derivedPushforward_of_qcqs g)).obj (𝟙_ _)))
    (K : quasiCoherentDerivedCategory (pullback f g))
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (pullback f g).toRingedSpace) K.obj) :
    fourierMukaiDualLocallySmall f g (perfectDual K hK ⊗ pulledBackDualizingComplex f g) ⊣
      fourierMukaiLocallySmall f g K :=
  letI := exactPairingPerfectDual K hK
  twistedDualAdjunction
    (quasiCoherentDerivedAdjunction (pullback.snd f g)
      (isQuasicoherent_homology_derivedPullback' _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (twistedInverseImageAdjunction (pullback.fst f g)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (hasInverse_of_tensorComparison (quasiCoherentDerivedPullback' (pullback.snd f g))
      (fun A B => (Functor.Monoidal.μIso _ A B).symm)
      (Functor.Monoidal.εIso _).symm hω.some)
    (twistedInverseImageFstIso f g) K (perfectDual K hK)

end Core

section Symmetry

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
  [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
  [CompactSpace X] [CompactSpace Y]

/-- **A Fourier-Mukai transform for the swapped product.** For a complex `A` on `X ×_S Y`, the
Fourier-Mukai transform `D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)` with kernel `σ^*A` on `Y ×_S X`, where
`σ : Y ×_S X ≅ X ×_S Y` exchanges the factors, is `N ↦ Rp_*(Lq^*N ⊗ᴸ A)` computed on
`X ×_S Y`. -/
def fourierMukaiLocallySmallSymmetryIso (A : quasiCoherentDerivedCategory (pullback f g)) :
    fourierMukaiLocallySmall g f
        ((quasiCoherentDerivedPullback' (pullbackSymmetry g f).hom).obj A) ≅
      fourierMukaiDualLocallySmall f g A := by
  let σ := (pullbackSymmetry g f).hom
  let L := quasiCoherentDerivedPullback' σ
  have hq : σ ≫ pullback.snd f g = pullback.fst g f := pullbackSymmetry_hom_comp_snd g f
  have hp : σ ≫ pullback.fst f g = pullback.snd g f := pullbackSymmetry_hom_comp_fst g f
  -- `Lσ^*` is an equivalence, so the unit of `Lσ^* ⊣ Rσ_*` is invertible
  have hσ : ∀ (K : quasiCoherentDerivedCategory (pullback g f)) (i : ℤ),
      ((DerivedCategory.homologyFunctor (pullback f g).Modules i).obj
        ((derivedPushforward σ).obj K.obj)).IsQuasicoherent :=
    isQuasicoherent_homology_derivedPushforward_of_qcqs σ
  let adj := quasiCoherentDerivedAdjunction σ (isQuasicoherent_homology_derivedPullback' σ) hσ
  haveI : (quasiCoherentDerivedPushforward σ hσ).IsEquivalence :=
    (quasiCoherentDerivedPushforwardEquivalenceOfIsIso σ hσ
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).isEquivalence_functor
  haveI : L.IsEquivalence := adj.isEquivalence_left_of_isEquivalence_right
  -- `Lσ^*` is monoidal
  let μ : L ⋙ MonoidalCategory.tensorRight (L.obj A) ≅ MonoidalCategory.tensorRight A ⋙ L :=
    NatIso.ofComponents (fun B => Functor.Monoidal.μIso L B A)
      (fun _ => Functor.LaxMonoidal.μ_natural_left _ _ _)
  exact Functor.isoWhiskerRight
      ((quasiCoherentDerivedPullbackCongr hq).symm ≪≫
        (quasiCoherentDerivedPullbackCompIso σ (pullback.snd f g)).symm) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight μ _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
          (quasiCoherentDerivedPushforwardCongr hp.symm
              (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
              (isQuasicoherent_homology_derivedPushforward_of_qcqs (σ ≫ pullback.fst f g)) ≪≫
            (quasiCoherentDerivedPushforwardCompIso σ (pullback.fst f g) hσ
              (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
              (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).symm) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (asIso adj.unit).symm _ ≪≫ Functor.leftUnitor _))

end Symmetry

end Stacks.Duality

end
