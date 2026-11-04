module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.AffineBaseChangeLocal
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.Composition

/-!
# Rigidity of the relative dualizing complex

Let `Y` be a quasi-compact and quasi-separated scheme and `f : X ⟶ Y` proper, flat and of finite
presentation, with relative dualizing complex `ω = a(𝒪_Y)` and `c` the right adjoint of `RΔ_*`
for the diagonal `Δ : X ⟶ X ×_Y X`. Then `c(Lpr₁^*ω) ≅ 𝒪_X ≅ c(Lpr₂^*ω)` and
`ω ≅ c(Lpr₁^*ω ⊗ᴸ Lpr₂^*ω)`: [Stacks, Tag 0E2P].
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

/-- **The twisted inverse image of a section is a left inverse**: for `s ≫ g = 𝟙`, the composite
`a_s ∘ a_g` of twisted inverse images is the identity, as `a_{s ≫ g} ≅ a_s ∘ a_g`. -/
def twistedInverseImageCompIsoOfCompEqId {X P : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] [CompactSpace P] [QuasiSeparatedSpace P] (s : X ⟶ P) (g : P ⟶ X)
    (h : s ≫ g = 𝟙 X) :
    twistedInverseImage g (isQuasicoherent_homology_derivedPushforward_of_qcqs g) ⋙
        twistedInverseImage s (isQuasicoherent_homology_derivedPushforward_of_qcqs s) ≅
      𝟭 (quasiCoherentDerivedCategory X) :=
  (twistedInverseImageCompIso s g _ _
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (s ≫ g))).symm ≪≫
    twistedInverseImageCongr h _ (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 X)) ≪≫
      twistedInverseImageIdIso X _

section Rigidity

variable {X' X Y' Y : Scheme.{u}} [CompactSpace X'] [QuasiSeparatedSpace X'] [CompactSpace X]
  [QuasiSeparatedSpace X] [CompactSpace Y'] [QuasiSeparatedSpace Y'] [CompactSpace Y]
  [QuasiSeparatedSpace Y]

/-- The isomorphism `L(g')^* a(K) ≅ a'(Lg^*K)` of [Stacks, Tag 0AAB], for `f` proper, flat and of
finite presentation. -/
def pullbackTwistedInverseImageIsoOfFlat {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g) [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (K : quasiCoherentDerivedCategory Y) :
    (quasiCoherentDerivedPullback' g').obj
        ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj K) ≅
      (twistedInverseImage f' (isQuasicoherent_homology_derivedPushforward_of_qcqs f')).obj
        ((quasiCoherentDerivedPullback' g).obj K) :=
  haveI := isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent sq
    (torIndependent_of_flat_left f g)
  haveI := isIso_twistedInverseImageBaseChangeMap_app_of_isProper_of_flat sq K
  asIso ((twistedInverseImageBaseChangeMap g' f' f g
    (isQuasicoherent_homology_derivedPushforward_of_qcqs g')
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
    (isQuasicoherent_homology_derivedPushforward_of_qcqs g)
    sq).app K)

/-- **`L(g')^*ω ≅ a'(𝒪_X)`** in a cartesian square over `f : X ⟶ Y` proper, flat and of finite
presentation, `ω = a(𝒪_Y)`: [Stacks, Tag 0AAB] and `Lf^*𝒪_Y ≅ 𝒪_X`. -/
def pullbackRelativeDualizingComplexIso {g' : X' ⟶ X} {f' : X' ⟶ X} {f : X ⟶ Y}
    (sq : IsPullback g' f' f f) [IsProper f] [Flat f] [LocallyOfFinitePresentation f] :
    (quasiCoherentDerivedPullback' g').obj
        ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
          (DerivedPushforward.derivedStructureSheaf Y)) ≅
      (twistedInverseImage f' (isQuasicoherent_homology_derivedPushforward_of_qcqs f')).obj
        (DerivedPushforward.derivedStructureSheaf X) :=
  pullbackTwistedInverseImageIsoOfFlat sq (DerivedPushforward.derivedStructureSheaf Y) ≪≫
    (twistedInverseImage f' _).mapIso
      (ObjectProperty.isoMk _ (derivedPullbackStructureSheafIso f) :
        (quasiCoherentDerivedPullback' f).obj (DerivedPushforward.derivedStructureSheaf Y) ≅
          DerivedPushforward.derivedStructureSheaf X)

/-- **`c(L(g')^*ω) ≅ 𝒪_X` for a section `s` of `f'`** in a cartesian square over `f : X ⟶ Y`
proper, flat and of finite presentation, `ω = a(𝒪_Y)` and `c` the twisted inverse image of `s`:
`L(g')^*ω ≅ a'(𝒪_X)` and `c ∘ a' = id`. -/
def twistedInverseImageSectionPullbackRelativeDualizingIso {g' : X' ⟶ X} {f' : X' ⟶ X}
    {f : X ⟶ Y} (sq : IsPullback g' f' f f) [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] (s : X ⟶ X') (hs : s ≫ f' = 𝟙 X) :
    (twistedInverseImage s (isQuasicoherent_homology_derivedPushforward_of_qcqs s)).obj
        ((quasiCoherentDerivedPullback' g').obj
          ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
            (DerivedPushforward.derivedStructureSheaf Y))) ≅
      DerivedPushforward.derivedStructureSheaf X :=
  (twistedInverseImage s _).mapIso (pullbackRelativeDualizingComplexIso sq) ≪≫
    (twistedInverseImageCompIsoOfCompEqId s f' hs).app _

/-- **`ω ≅ c(L(g')^*ω ⊗ᴸ L(f')^*ω)` for a common section `s` of `f'` and `g'`** in a cartesian
square over `f : X ⟶ Y` proper, flat and of finite presentation: `ω ≅ c(a_{g'}(ω))` as
`c ∘ a_{g'} = id`, `a_{g'}(ω) ≅ L(g')^*ω ⊗ᴸ a_{g'}(𝒪_X)` by [Stacks, Tag 0E4K] and
`a_{g'}(𝒪_X) ≅ L(f')^*ω` by [Stacks, Tag 0AAB]. -/
def twistedInverseImageSectionTensorRelativeDualizingIso {g' : X' ⟶ X} {f' : X' ⟶ X}
    {f : X ⟶ Y} (sq : IsPullback g' f' f f) [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] (s : X ⟶ X') (hs : s ≫ g' = 𝟙 X) :
    (twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
        (DerivedPushforward.derivedStructureSheaf Y) ≅
      (twistedInverseImage s (isQuasicoherent_homology_derivedPushforward_of_qcqs s)).obj
        (((quasiCoherentDerivedTensor X').obj ((quasiCoherentDerivedPullback' g').obj
          ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
            (DerivedPushforward.derivedStructureSheaf Y)))).obj
          ((quasiCoherentDerivedPullback' f').obj
            ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
              (DerivedPushforward.derivedStructureSheaf Y)))) :=
  haveI : IsProper g' := MorphismProperty.of_isPullback sq.flip inferInstance
  haveI : Flat g' := MorphismProperty.of_isPullback sq.flip inferInstance
  haveI : LocallyOfFinitePresentation g' := MorphismProperty.of_isPullback sq.flip inferInstance
  let ω := (twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
    (DerivedPushforward.derivedStructureSheaf Y)
  haveI := isIso_twistedInverseImageCompareWithPullback_of_flat g' ω
  ((twistedInverseImageCompIsoOfCompEqId s g' hs).app ω).symm ≪≫
    (twistedInverseImage s _).mapIso
      ((asIso (twistedInverseImageCompareWithPullback g'
        (isQuasicoherent_homology_derivedPushforward_of_qcqs g')
        (quasiCoherentDerivedPullbackTensorIso g').hom (quasiCoherentDerivedTensorRightUnitor X)
          ω)).symm ≪≫
        ((quasiCoherentDerivedTensor X').obj _).mapIso
          (pullbackRelativeDualizingComplexIso sq.flip).symm)

end Rigidity

/-- **Rigidity, [Stacks, Tag 0E2P].** Let `Y` be a quasi-compact and quasi-separated scheme and
`f : X ⟶ Y` proper, flat and of finite presentation, with relative dualizing complex
`ω = a(𝒪_Y)` ([Stacks, Tag 0B6S]), and let `c` be the right adjoint of `RΔ_*` on `D_QCoh` for the
diagonal `Δ : X ⟶ X ×_Y X` ([Stacks, Tag 0A9E]). There are canonical isomorphisms
`𝒪_X ≅ c(Lpr₁^*ω)`, `𝒪_X ≅ c(Lpr₂^*ω)` (Equation 0E2Q) and `ω ≅ c(Lpr₁^*ω ⊗ᴸ Lpr₂^*ω)`
(Equation 0E2R). -/
@[stacks 0E2P]
def relativeDualizingComplexRigidity {X Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsProper f] [Flat f] [LocallyOfFinitePresentation f] :
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    haveI : CompactSpace (pullback f f : Scheme.{u}) :=
      QuasiCompact.compactSpace_of_compactSpace (pullback.snd f f)
    haveI : QuasiSeparatedSpace (pullback f f : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.snd f f)
    ((DerivedPushforward.derivedStructureSheaf X ≅
        (twistedInverseImage (pullback.diagonal f)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (pullback.diagonal f))).obj
          ((quasiCoherentDerivedPullback' (pullback.fst f f)).obj
            ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
            (DerivedPushforward.derivedStructureSheaf Y)))) ×
      (DerivedPushforward.derivedStructureSheaf X ≅
        (twistedInverseImage (pullback.diagonal f)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (pullback.diagonal f))).obj
          ((quasiCoherentDerivedPullback' (pullback.snd f f)).obj
            ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
            (DerivedPushforward.derivedStructureSheaf Y))))) ×
      (((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
          (DerivedPushforward.derivedStructureSheaf Y)) ≅
        (twistedInverseImage (pullback.diagonal f)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (pullback.diagonal f))).obj
          (((quasiCoherentDerivedTensor (pullback f f)).obj
            ((quasiCoherentDerivedPullback' (pullback.fst f f)).obj
              ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
              (DerivedPushforward.derivedStructureSheaf Y)))).obj
            ((quasiCoherentDerivedPullback' (pullback.snd f f)).obj
              ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
              (DerivedPushforward.derivedStructureSheaf Y))))) :=
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  haveI : CompactSpace (pullback f f : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f f)
  haveI : QuasiSeparatedSpace (pullback f f : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd f f)
  let sq := IsPullback.of_hasPullback f f
  (((twistedInverseImageSectionPullbackRelativeDualizingIso sq (pullback.diagonal f)
      (pullback.diagonal_snd f)).symm,
    (twistedInverseImageSectionPullbackRelativeDualizingIso sq.flip (pullback.diagonal f)
      (pullback.diagonal_fst f)).symm),
    twistedInverseImageSectionTensorRelativeDualizingIso sq (pullback.diagonal f)
      (pullback.diagonal_fst f))


end Stacks.Duality
