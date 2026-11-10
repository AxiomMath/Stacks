module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackObstructionVanishingInputs
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeDimensionOneTorAmplitude
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleGlobalSectionsCohomologyBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.TorAmplitudeOneCohomologyVanishing

/-!
# The Picard stack is smooth in relative dimension one, given that it is algebraic (Stacks 0DPJ)

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S` which is flat, proper and of
finite presentation (the standing assumptions of Section 0DM9), and of relative dimension `≤ 1`.
Stacks 0DPJ says that the structure morphism `Picardstack_{X/B} ⟶ B` is smooth. The statement
presupposes Stacks 0D04, that `Picardstack_{X/B}` is an algebraic stack, which is the only input
of `AlgebraicGeometry.Space.isSmooth_picardStructureMorphism_of_isAlgebraicStack` below.

The source's proof is carried out in full:

* `Picardstack_{X/B} ⟶ B` is locally of finite presentation (Stacks 0DMB):
  `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_picardStructureMorphism`;
* it is formally smooth, by Stacks 09ZX and 0DNM, as soon as `H²(X_{T'}, 𝓘) = 0` for the ideal
  `𝓘` of `X_T ⊂ X_{T'}`, for every first-order thickening `T ⊂ T'` of affine test schemes
  (`AlgebraicGeometry.Space.isSmooth_picardStructureMorphism_of_preimageH2Vanishes`);
* the vanishing: `𝓘` is the pullback `q^*𝒞` of the conormal module of `T ⊂ T'` along the
  projection `q : X_T ⟶ T` (flatness, Stacks 06BH) and its cohomology is computed on `X_T`
  (Stacks 05ZM); `q` is proper, flat, of finite presentation and of relative dimension `≤ 1`, so
  `Rq_*𝒪` has Tor amplitude in `[0, 1]` (Stacks 0CTM, 068V, and the vanishing of the cohomology
  of curves over a field, which is where Stacks 0A4T enters the source), and then
  `H²(X_T, q^*𝒞) = 0` by the projection formula (Stacks 08IN) and the Leray spectral sequence
  over the affine `T` (Stacks 08EX); finally Stacks 03FD passes from the module-valued
  cohomology to the cohomology of the underlying abelian sheaf.

## Main results

* `AlgebraicGeometry.Space.picardPreimageH2Vanishes_of_hasRelativeDimensionLE_one`: the
  vanishing of the obstruction groups.
* `AlgebraicGeometry.Space.isSmooth_picardStructureMorphism_of_isAlgebraicStack`: **Stacks 0DPJ**
  with the algebraicity of the Picard stack (Stacks 0D04) as its only input.

## Implementation notes

**No declaration here carries a tag.** The registration waits on Stacks 0D04 (Stacks 09DS),
not yet proved here. Once `AlgebraicGeometry.Space.isAlgebraicStack_picardCFG D hflat hproper`
is proved, the registered statement is
`isSmooth_picardStructureMorphism_of_isAlgebraicStack D hflat hproper hd
(isAlgebraicStack_picardCFG D hflat hproper)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

namespace AlgebraicGeometry.Space

attribute [local instance] enoughInjectives_sheaf_smallEtale hasExt_sheaf_smallEtale

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The obstruction groups of the Picard stack vanish in relative dimension `≤ 1`.** Let
`f : X ⟶ B` be flat, proper, of finite presentation and of relative dimension `≤ 1`. For every
first-order thickening `T ⊂ T'` of affine test schemes over `B`, the ideal of the inverse image of
`T` in `X_{T'}` has vanishing second cohomology on the small étale site of `X_{T'}`. -/
theorem picardPreimageH2Vanishes_of_hasRelativeDimensionLE_one (D : CoherentSituation B S hS)
    (hflat : IsFlat B S hS D.f.hom) (hproper : IsProper B S hS D.f.hom)
    (hd : HasRelativeDimensionLE 1 B S hS D.f.hom) :
    PicardPreimageH2Vanishes D.toPicardSituation := by
  intro T T' g hT hT' hg
  let q := baseChangeInclusion D.f T'
  have hqfl : IsFlat B S hS q.hom := isFlat_projection D hflat T'
  have hqpr : IsProper B S hS q.hom := isProper_projection D hproper T'
  have hqfp : IsFinitePresentation B S hS q.hom := D.isFinitePresentation_projection T'
  have hqd : HasRelativeDimensionLE 1 B S hS q.hom := D.hasRelativeDimensionLE_projection hd T'
  let p := squareZeroPreimageProjection B S hS g.left hg q
  have hpfl : IsFlat B S hS p.hom := isFlat_squareZeroPreimageProjection B S hS g.left hg hqfl
  have hppr : IsProper B S hS p.hom := isProper_squareZeroPreimageProjection B S hS g.left hg hqpr
  have hpfp : IsFinitePresentation B S hS p.hom :=
    isFinitePresentation_squareZeroPreimageProjection B S hS g.left hg hqfp
  have hpd : HasRelativeDimensionLE 1 B S hS p.hom :=
    hasRelativeDimensionLE_squareZeroPreimageProjection B S hS g.left hg
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hqfp.1) hqd
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T.left) := hT
  let K := squareZeroConormalModule g.left hg
  have hvan := isZero_rightDerived_globalSections_modulePullback_of_torAmplitude B S hS T.left hT
    p hppr.2.1.2 (isQuasiSeparated_of_isSeparated B S hS hppr.1) hpfl
    (fun K _ i hi =>
      isZero_homology_derivedTensor_pushforward_structureModule_of_hasRelativeDimensionLE_one
        T.left p hppr hpfl hpfp hpd K i hi)
    K (isQuasicoherentOnSite_squareZeroConormalModule g.left hg) 2 le_rfl
  let Z := squareZeroPreimageSpace B S hS g.left hg q
  let G := (modulePullback B S hS (preimageProjection B S hS q
    (squareZeroSubspace B S hS g.left hg))).obj (conormalModule B S hS
      ((schemeSpaceFunctor B S hS).obj T'.left) (squareZeroSubspace B S hS g.left hg))
  have : HasInjectiveResolutions (SheafOfModules.{u} (structureRingSheaf B S hS Z)) :=
    hasInjectiveResolutions_modules B S hS Z.1 Z.2
  have hvanG : IsZero (((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
      (structureRingSheaf B S hS Z)).rightDerived 2).obj G) :=
    IsZero.of_iso hvan (((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
      (structureRingSheaf B S hS Z)).rightDerived 2).mapIso
        (modulePullbackConormalIsoSquareZeroPreimageProjection g.left hg q).symm)
  have h2 := subsingleton_sheafH_of_isZero_rightDerived_globalSections Z G 1 hvanG
  exact (Equiv.subsingleton_congr
    (squareZeroPreimageIdealCohomologyAddEquiv B S hS g.left hg q hqfl 2).toEquiv).mpr h2

/-- **Stacks 0DPJ, with Stacks 0D04 as its only input.** Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` which is flat, proper, of finite presentation (the field of the
standing datum `D`) and of relative dimension `≤ 1`, and suppose that the Picard stack
`Picardstack_{X/Y}` is an algebraic stack (Stacks 0D04). Then the structure morphism
`Picardstack_{X/Y} ⟶ Y` is smooth, as a 1-morphism of algebraic stacks. -/
theorem isSmooth_picardStructureMorphism_of_isAlgebraicStack (D : CoherentSituation B S hS)
    (hflat : IsFlat B S hS D.f.hom) (hproper : IsProper B S hS D.f.hom)
    (hd : HasRelativeDimensionLE 1 B S hS D.f.hom)
    (h0D04 : Stack.IsAlgebraicStack.{u, w} B S hS
      (picardCFG (modulePushforwardCoherence B S hS) D.toPicardSituation).val) :
    Stack.AlgebraicStacks.IsSmooth B S hS (picardStructureMorphism D h0D04) :=
  isSmooth_picardStructureMorphism_of_preimageH2Vanishes D hflat hproper h0D04
    (picardPreimageH2Vanishes_of_hasRelativeDimensionLE_one D hflat hproper hd)

end AlgebraicGeometry.Space

end
