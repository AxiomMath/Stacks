module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonFlat
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.AffineBaseChangeLocal
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.Composition
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.Basic

/-!
# Rigidity of the relative dualizing complex

Let `Y` be a quasi-compact and quasi-separated scheme and `f : X ⟶ Y` proper, flat and of finite
presentation, with relative dualizing complex `ω = a(𝒪_Y)` ([Stacks, Tag 0B6S]), `a` the right
adjoint of `Rf_*` on `D_QCoh`. Let `pr₁, pr₂ : X ×_Y X ⟶ X` be the projections and `c` the right
adjoint of `RΔ_*` for the diagonal `Δ : X ⟶ X ×_Y X` ([Stacks, Tag 0A9E]). Then
([Stacks, Tag 0E2P])
`𝒪_X ≅ c(L pr₁^* ω) ≅ c(L pr₂^* ω)` (Equation 0E2Q) and
`ω ≅ c(L pr₁^* ω ⊗ᴸ L pr₂^* ω)` (Equation 0E2R).

The proof is the source's. With `b` the right adjoint for `pr₁`, `pr₁ ∘ Δ = id` gives `c ∘ b ≅ id`,
[Stacks, Tag 0E4K] for `pr₁` gives `b(ω) ≅ L pr₁^*ω ⊗ᴸ b(𝒪_X)`, and flat base change
([Stacks, Tag 0AAB]) together with `Lf^*𝒪_Y = 𝒪_X` gives `b(𝒪_X) ≅ L pr₂^* a(𝒪_Y)`.

As [Stacks, Tag 0BRU] remarks, the second isomorphism says that `ω` is *rigid*: the right-hand
side is quadratic in `ω`, the left-hand side linear.

## Main definitions

* `Stacks.Duality.quasiCoherentDerivedPullbackStructureSheafIso` — `Lf^*𝒪_Y ≅ 𝒪_X` in `D_QCoh`.
* `Stacks.Duality.structureSheafIsoDiagonalTwistedInverseImagePullbackFst`,
  `Stacks.Duality.structureSheafIsoDiagonalTwistedInverseImagePullbackSnd` — Equation 0E2Q.
* `Stacks.Duality.relativeDualizingComplexRigidityIso` — Equation 0E2R, the isomorphism which
  makes `ω` rigid ([Stacks, Tag 0BRU]).

## References

* [Stacks Project, Tag 0E2P](https://stacks.math.columbia.edu/tag/0E2P)
* [Stacks Project, Tag 0BRU](https://stacks.math.columbia.edu/tag/0BRU)
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

section StructureSheaf

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **`Lf^*𝒪_Y ≅ 𝒪_X` in `D_QCoh`**: the unit constraint of the monoidal functor `Lf^*`, the
monoidal units of `D_QCoh(𝒪_Y)` and `D_QCoh(𝒪_X)` being the structure sheaves in degree zero. -/
def quasiCoherentDerivedPullbackStructureSheafIso :
    (quasiCoherentDerivedPullback' f).obj (derivedStructureSheaf Y) ≅ derivedStructureSheaf X :=
  eqToIso (congrArg (quasiCoherentDerivedPullback' f).obj
      (tensorUnit_quasiCoherentDerivedCategory Y).symm) ≪≫
    (Functor.Monoidal.εIso (quasiCoherentDerivedPullback' f)).symm ≪≫
    eqToIso (tensorUnit_quasiCoherentDerivedCategory X)

end StructureSheaf

section General

/-- **[Stacks, Tag 0E4K] as an isomorphism**: for `f : X ⟶ Y` proper, flat and of finite
presentation over a quasi-compact quasi-separated base, `Lf^*K ⊗ᴸ a(𝒪_Y) ≅ a(K)` through the map
of Equation 48.8.0.1. -/
def twistedInverseImageTensorIsoOfFlat {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace Y]
    [QuasiSeparatedSpace Y] [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (K : quasiCoherentDerivedCategory Y) :
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    ((quasiCoherentDerivedTensor X).obj ((quasiCoherentDerivedPullback' f).obj K)).obj
        ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
          (derivedStructureSheaf Y)) ≅
      (twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj K :=
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  haveI := isIso_twistedInverseImageCompareWithPullback_of_flat f K
  asIso (twistedInverseImageCompareWithPullback f
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    (quasiCoherentDerivedPullbackTensorIso f).hom (quasiCoherentDerivedTensorRightUnitor Y) K)

/-- **Flat base change of the relative dualizing complex** ([Stacks, Tag 0AAB] at `𝒪_Y`): for a
cartesian square of quasi-compact quasi-separated schemes with `f` proper, flat and of finite
presentation, `a'(𝒪_{X'}) ≅ L(g')^* a(𝒪_Y)`, through the base change map of [Stacks, Tag 0AA6]
and `Lg^*𝒪_Y ≅ 𝒪_{Y'}`. -/
def twistedInverseImageStructureSheafBaseChangeIso {X' X Y' Y : Scheme.{u}}
    [CompactSpace Y'] [QuasiSeparatedSpace Y'] [CompactSpace Y] [QuasiSeparatedSpace Y]
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f] :
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    haveI : QuasiCompact f' := MorphismProperty.of_isPullback sq inferInstance
    haveI : QuasiSeparated f' := MorphismProperty.of_isPullback sq inferInstance
    haveI : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace f'
    haveI : QuasiSeparatedSpace X' := quasiSeparatedSpace_of_quasiSeparated f'
    (twistedInverseImage f' (isQuasicoherent_homology_derivedPushforward_of_qcqs f')).obj
        (derivedStructureSheaf Y') ≅
      (quasiCoherentDerivedPullback' g').obj
        ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
          (derivedStructureSheaf Y)) :=
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  haveI : QuasiCompact f' := MorphismProperty.of_isPullback sq inferInstance
  haveI : QuasiSeparated f' := MorphismProperty.of_isPullback sq inferInstance
  haveI : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace f'
  haveI : QuasiSeparatedSpace X' := quasiSeparatedSpace_of_quasiSeparated f'
  haveI := isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent sq
    (torIndependent_of_flat_left f g)
  haveI := isIso_twistedInverseImageBaseChangeMap_app_of_isProper_of_flat sq
    (derivedStructureSheaf Y)
  (twistedInverseImage f' (isQuasicoherent_homology_derivedPushforward_of_qcqs f')).mapIso
      (quasiCoherentDerivedPullbackStructureSheafIso g).symm ≪≫
    (asIso ((twistedInverseImageBaseChangeMap g' f' f g
      (isQuasicoherent_homology_derivedPushforward_of_qcqs g')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs g)
      sq).app (derivedStructureSheaf Y))).symm

end General

section Rigidity

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace Y] [QuasiSeparatedSpace Y] [IsProper f]
  [Flat f] [LocallyOfFinitePresentation f]

/-- **The composite `c ∘ b` of the twisted inverse images of the first projection and of the
diagonal is the identity**: `pr₁ ∘ Δ = id_X`, and the twisted inverse image is compatible with
composition. -/
def twistedInverseImagePullbackFstCompDiagonalIso :
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    haveI : CompactSpace (pullback f f : Scheme.{u}) :=
      QuasiCompact.compactSpace_of_compactSpace (pullback.fst f f)
    haveI : QuasiSeparatedSpace (pullback f f : Scheme.{u}) := quasiSeparatedSpace_of_quasiSeparated
      (pullback.fst f f)
    twistedInverseImage (pullback.fst f f)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (pullback.fst f f)) ⋙
      twistedInverseImage (pullback.diagonal f)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (pullback.diagonal f)) ≅
      𝟭 (quasiCoherentDerivedCategory X) :=
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  haveI : CompactSpace (pullback f f : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst f f)
  haveI : QuasiSeparatedSpace (pullback f f : Scheme.{u}) := quasiSeparatedSpace_of_quasiSeparated
    (pullback.fst f f)
  (twistedInverseImageCompIso (pullback.diagonal f) (pullback.fst f f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).symm ≪≫
    twistedInverseImageCongr (pullback.diagonal_fst f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _) ≪≫
    twistedInverseImageIdIso X (isQuasicoherent_homology_derivedPushforward_of_qcqs _)

/-- **The composite `c ∘ b'` of the twisted inverse images of the second projection and of the
diagonal is the identity**: `pr₂ ∘ Δ = id_X`. -/
def twistedInverseImagePullbackSndCompDiagonalIso :
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    haveI : CompactSpace (pullback f f : Scheme.{u}) :=
      QuasiCompact.compactSpace_of_compactSpace (pullback.fst f f)
    haveI : QuasiSeparatedSpace (pullback f f : Scheme.{u}) := quasiSeparatedSpace_of_quasiSeparated
      (pullback.fst f f)
    twistedInverseImage (pullback.snd f f)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (pullback.snd f f)) ⋙
      twistedInverseImage (pullback.diagonal f)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (pullback.diagonal f)) ≅
      𝟭 (quasiCoherentDerivedCategory X) :=
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  haveI : CompactSpace (pullback f f : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst f f)
  haveI : QuasiSeparatedSpace (pullback f f : Scheme.{u}) := quasiSeparatedSpace_of_quasiSeparated
    (pullback.fst f f)
  (twistedInverseImageCompIso (pullback.diagonal f) (pullback.snd f f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).symm ≪≫
    twistedInverseImageCongr (pullback.diagonal_snd f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _) ≪≫
    twistedInverseImageIdIso X (isQuasicoherent_homology_derivedPushforward_of_qcqs _)

/-- **[Stacks, Tag 0E2Q], first projection**: `𝒪_X ≅ c(L pr₁^* ω_{X/Y}^•)`; this is the first
isomorphism of [Stacks, Tag 0E2P], where
`ω_{X/Y}^• = a(𝒪_Y)` is the relative dualizing complex and `c` the twisted inverse image of the
diagonal `Δ : X ⟶ X ×_Y X`. With `b'` the twisted inverse image of `pr₂`, `𝒪_X = c(b'(𝒪_X))` as
`pr₂ ∘ Δ = id`, and `b'(𝒪_X) = L pr₁^* a(𝒪_Y)` by flat base change. -/
@[stacks 0E2Q "first projection: 𝒪_X ≅ c(L pr₁^* ω_{X/Y}^•)"]
def structureSheafIsoDiagonalTwistedInverseImagePullbackFst :
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    haveI : CompactSpace (pullback f f : Scheme.{u}) :=
      QuasiCompact.compactSpace_of_compactSpace (pullback.fst f f)
    haveI : QuasiSeparatedSpace (pullback f f : Scheme.{u}) := quasiSeparatedSpace_of_quasiSeparated
      (pullback.fst f f)
    derivedStructureSheaf X ≅
      (twistedInverseImage (pullback.diagonal f)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (pullback.diagonal f))).obj
        ((quasiCoherentDerivedPullback' (pullback.fst f f)).obj
          ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
            (derivedStructureSheaf Y))) :=
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  haveI : CompactSpace (pullback f f : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst f f)
  haveI : QuasiSeparatedSpace (pullback f f : Scheme.{u}) := quasiSeparatedSpace_of_quasiSeparated
    (pullback.fst f f)
  ((twistedInverseImagePullbackSndCompDiagonalIso f).app (derivedStructureSheaf X)).symm ≪≫
    (twistedInverseImage (pullback.diagonal f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (pullback.diagonal f))).mapIso
      (twistedInverseImageStructureSheafBaseChangeIso (IsPullback.of_hasPullback f f))

/-- **[Stacks, Tag 0E2Q], second projection**: `𝒪_X ≅ c(L pr₂^* ω_{X/Y}^•)`; this is the second
isomorphism of [Stacks, Tag 0E2P]. With `b` the twisted
inverse image of `pr₁`, `𝒪_X = c(b(𝒪_X))` as `pr₁ ∘ Δ = id`, and `b(𝒪_X) = L pr₂^* a(𝒪_Y)` by
flat base change. -/
@[stacks 0E2Q "second projection: 𝒪_X ≅ c(L pr₂^* ω_{X/Y}^•)"]
def structureSheafIsoDiagonalTwistedInverseImagePullbackSnd :
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    haveI : CompactSpace (pullback f f : Scheme.{u}) :=
      QuasiCompact.compactSpace_of_compactSpace (pullback.fst f f)
    haveI : QuasiSeparatedSpace (pullback f f : Scheme.{u}) := quasiSeparatedSpace_of_quasiSeparated
      (pullback.fst f f)
    derivedStructureSheaf X ≅
      (twistedInverseImage (pullback.diagonal f)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (pullback.diagonal f))).obj
        ((quasiCoherentDerivedPullback' (pullback.snd f f)).obj
          ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
            (derivedStructureSheaf Y))) :=
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  haveI : CompactSpace (pullback f f : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst f f)
  haveI : QuasiSeparatedSpace (pullback f f : Scheme.{u}) := quasiSeparatedSpace_of_quasiSeparated
    (pullback.fst f f)
  ((twistedInverseImagePullbackFstCompDiagonalIso f).app (derivedStructureSheaf X)).symm ≪≫
    (twistedInverseImage (pullback.diagonal f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (pullback.diagonal f))).mapIso
      (twistedInverseImageStructureSheafBaseChangeIso (IsPullback.of_hasPullback f f).flip)

/-- **[Stacks, Tag 0E2R], the rigidity isomorphism**; this is the isomorphism of
[Stacks, Tag 0E2P] in Equation 0E2R:
`ω_{X/Y}^• ≅ c(L pr₁^* ω_{X/Y}^• ⊗ᴸ_{𝒪_{X ×_Y X}} L pr₂^* ω_{X/Y}^•)`, where
`ω_{X/Y}^• = a(𝒪_Y)` is the relative dualizing complex of [Stacks, Tag 0B6S] and `c` the twisted
inverse image of the diagonal `Δ : X ⟶ X ×_Y X`. With `b` the twisted inverse image of `pr₁`:
`ω = c(b(ω))` as `pr₁ ∘ Δ = id`, `b(ω) = L pr₁^*ω ⊗ᴸ b(𝒪_X)` by [Stacks, Tag 0E4K], and
`b(𝒪_X) = L pr₂^* a(𝒪_Y)` by [Stacks, Tag 0AAB]. -/
@[stacks 0E2R]
def relativeDualizingComplexRigidityIso :
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    haveI : CompactSpace (pullback f f : Scheme.{u}) :=
      QuasiCompact.compactSpace_of_compactSpace (pullback.fst f f)
    haveI : QuasiSeparatedSpace (pullback f f : Scheme.{u}) := quasiSeparatedSpace_of_quasiSeparated
      (pullback.fst f f)
    (twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
        (derivedStructureSheaf Y) ≅
      (twistedInverseImage (pullback.diagonal f)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (pullback.diagonal f))).obj
        (((quasiCoherentDerivedTensor (pullback f f : Scheme.{u})).obj
          ((quasiCoherentDerivedPullback' (pullback.fst f f)).obj
            ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
              (derivedStructureSheaf Y)))).obj
          ((quasiCoherentDerivedPullback' (pullback.snd f f)).obj
            ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
              (derivedStructureSheaf Y)))) :=
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  haveI : CompactSpace (pullback f f : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst f f)
  haveI : QuasiSeparatedSpace (pullback f f : Scheme.{u}) := quasiSeparatedSpace_of_quasiSeparated
    (pullback.fst f f)
  haveI : IsProper (pullback.fst f f) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback f f).flip inferInstance
  haveI : Flat (pullback.fst f f) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback f f).flip inferInstance
  haveI : LocallyOfFinitePresentation (pullback.fst f f) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback f f).flip inferInstance
  ((twistedInverseImagePullbackFstCompDiagonalIso f).app
      ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
        (derivedStructureSheaf Y))).symm ≪≫
    (twistedInverseImage (pullback.diagonal f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (pullback.diagonal f))).mapIso
      ((twistedInverseImageTensorIsoOfFlat (pullback.fst f f) _).symm ≪≫
        ((quasiCoherentDerivedTensor (pullback f f : Scheme.{u})).obj
          ((quasiCoherentDerivedPullback' (pullback.fst f f)).obj
            ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
              (derivedStructureSheaf Y)))).mapIso
          (twistedInverseImageStructureSheafBaseChangeIso (IsPullback.of_hasPullback f f).flip))

end Rigidity

/-! ### Registrations

[Stacks, Tag 0E2P] consists of the two canonical isomorphisms of Equation 0E2Q and the canonical
isomorphism of Equation 0E2R; that tag is not registered in this module. [Stacks, Tag 0BRU]
remarks that the isomorphism of Equation 0E2R makes the relative dualizing complex rigid, in the
sense of van den Bergh: `ω_{X/Y}^•` is identified with `c` of the quadratic expression
`L pr₁^*ω_{X/Y}^• ⊗ᴸ L pr₂^*ω_{X/Y}^•`. -/

add_to_stacks 0BRU "the rigidity isomorphism ω_{X/Y}^• ≅ c(L pr₁^* ω_{X/Y}^• ⊗ᴸ L pr₂^* ω_{X/Y}^•) \
  of Equation 0E2R"
  Stacks.Duality.relativeDualizingComplexRigidityIso

end Stacks.Duality
