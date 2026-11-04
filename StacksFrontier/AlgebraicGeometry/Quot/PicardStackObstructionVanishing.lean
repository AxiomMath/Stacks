module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackSmoothOfAlgebraic
public import StacksFrontier.AlgebraicGeometry.Quot.SpacesDefoThickeningIdealCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.PicardLiftingModules

/-!
# Lifting invertible modules along `X_T ⊂ X_{T'}` through the preimage of `T ⊂ T'`

Let `f : X ⟶ B` be a morphism of algebraic spaces and `T ⊂ T'` a first-order thickening of test
schemes over `B`. The proof of Stacks 0DPJ lifts an invertible module on `X_T` to `X_{T'}` by
Stacks 0DNM, once `H²(X_{T'}, 𝓘) = 0` for the ideal `𝓘` of `X_T` in `X_{T'}`. This file reads
`X_T` as the inverse image `q⁻¹(T)` of `T` under the projection `q : X_{T'} ⟶ T'` — the two are
fibre products of the same cospan — so that the ideal is the one of the inverse image, whose
cohomology `AlgebraicGeometry.Space.squareZeroPreimageIdealCohomologyAddEquiv` computes.

## Main results

* `AlgebraicGeometry.Space.exists_lift_invertibleModule_of_subsingleton_preimage`: the lift.
* `AlgebraicGeometry.Space.hasThickeningLifts_picardToBase_of_preimageH2Vanishes`: the lifts of
  `Picardstack_{X/B} ⟶ 𝒮_B` along first-order thickenings, from the vanishing of the obstruction
  groups.

No declaration here carries a tag; these are steps of the proof of Stacks 0DPJ.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Space

attribute [local instance] enoughInjectives_sheaf_smallEtale hasExt_sheaf_smallEtale

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **`X_T` is the inverse image of `T` under the projection `X_{T'} ⟶ T'`**: both are fibre
products of `X_{T'} ⟶ T' ⟵ T`. -/
def baseChangeSpaceIsoSquareZeroPreimageSpace {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {T T' : SchemesOver Y} (g : T ⟶ T') (hg : IsSquareZeroClosedImmersion B S hS g.left) :
    baseChangeSpace f T ≅ squareZeroPreimageSpace B S hS g.left hg (baseChangeInclusion f T') :=
  (isPullback_baseChangeMap f g).isoIsPullback _ _
    (isPullback_squareZeroPreimageProjection B S hS g.left hg (baseChangeInclusion f T'))

/-- The identification of `X_T` with `q⁻¹(T)` is compatible with the two maps into `X_{T'}`. -/
theorem baseChangeSpaceIsoSquareZeroPreimageSpace_hom_comp {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) {T T' : SchemesOver Y} (g : T ⟶ T')
    (hg : IsSquareZeroClosedImmersion B S hS g.left) :
    (baseChangeSpaceIsoSquareZeroPreimageSpace f g hg).hom ≫
        subspaceInclusion B S hS (baseChangeSpace f T')
          (preimageSubspace B S hS (baseChangeInclusion f T')
            (squareZeroSubspace B S hS g.left hg)) =
      baseChangeMap f g :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- **Lifting an invertible module along `X_T ⊂ X_{T'}` (Stacks 0DNM)**, once the ideal of the
inverse image `q⁻¹(T) ⊂ X_{T'}` has vanishing second cohomology. -/
theorem exists_lift_invertibleModule_of_subsingleton_preimage {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) {T T' : SchemesOver Y} (g : T ⟶ T')
    (hg : IsSquareZeroClosedImmersion B S hS g.left)
    (h2 : Subsingleton (Sheaf.H.{u + 1} (thickeningUnitsShortComplex B S hS
      (isFirstOrderThickening_preimage_squareZeroSubspace B S hS g.left hg
        (baseChangeInclusion f T'))).X₁ 2))
    (L : Modules.{u, u} B S hS (baseChangeSpace f T).1 (baseChangeSpace f T).2)
    (hL : IsInvertibleModule (baseChangeSpace f T) L) :
    ∃ (L' : Modules.{u, u} B S hS (baseChangeSpace f T').1 (baseChangeSpace f T').2)
      (_ : IsInvertibleModule (baseChangeSpace f T') L'),
      Nonempty ((modulePullback B S hS (baseChangeMap f g)).obj L' ≅ L) := by
  let e := baseChangeSpaceIsoSquareZeroPreimageSpace f g hg
  let hZ := isFirstOrderThickening_preimage_squareZeroSubspace B S hS g.left hg
    (baseChangeInclusion f T')
  obtain ⟨L', hL', ⟨φ⟩⟩ := exists_isInvertibleModule_modulePullback_iso_of_subsingleton B S hS
    hZ h2 ((modulePullback B S hS e.inv).obj L) (modulePullbackInvertible e.inv L hL)
  refine ⟨L', hL', ⟨?_⟩⟩
  exact eqToIso (congrArg (fun k => (modulePullback B S hS k).obj L')
      (baseChangeSpaceIsoSquareZeroPreimageSpace_hom_comp f g hg).symm) ≪≫
    ((modulePullbackCompIso B S hS e.hom _).app L').symm ≪≫
    (modulePullback B S hS e.hom).mapIso φ ≪≫
    (modulePullbackCompIso B S hS e.hom e.inv).app L ≪≫
    eqToIso (congrArg (fun k => (modulePullback B S hS k).obj L) e.hom_inv_id) ≪≫
    ((modulePushforwardCoherence B S hS).modulePullbackIdIso _).app L

/-- **The vanishing of the obstruction groups, on the inverse images.** For every first-order
thickening `T ⊂ T'` of affine test schemes over the base, the ideal of the inverse image of `T`
under `X_{T'} ⟶ T'` has vanishing second cohomology on the small étale site of `X_{T'}`. -/
def PicardPreimageH2Vanishes (s : PicardSituation B S hS) : Prop :=
  ∀ ⦃T T' : s.SchemesOver⦄ (g : T ⟶ T'),
    IsAffine ((BigFppfOver.toScheme B S hS).obj T.left) →
    IsAffine ((BigFppfOver.toScheme B S hS).obj T'.left) →
    ∀ hg : IsSquareZeroClosedImmersion B S hS g.left,
      Subsingleton (Sheaf.H.{u + 1} (thickeningUnitsShortComplex B S hS
        (isFirstOrderThickening_preimage_squareZeroSubspace B S hS g.left hg
          (baseChangeInclusion s.f T'))).X₁ 2)

/-- **Lifts of `Picardstack_{X/B} ⟶ 𝒮_B` from the vanishing of the obstruction groups**, read on
the inverse images (Stacks 0DNM). -/
theorem hasThickeningLifts_picardToBase_of_preimageH2Vanishes (s : PicardSituation B S hS)
    (h : PicardPreimageH2Vanishes s) :
    Stack.HasThickeningLifts (picardToBase (modulePushforwardCoherence B S hS) s) :=
  hasThickeningLifts_picardToBase_of_exists_lift s fun _ _ g hT hT' hg L hL =>
    exists_lift_invertibleModule_of_subsingleton_preimage s.f g hg (h g hT hT' hg) L hL

/-- **The structure morphism `Picardstack_{X/Y} ⟶ Y` is smooth** (the proof of Stacks 0DPJ),
given Stacks 0D04 and the vanishing of the obstruction groups on the inverse images. -/
theorem isSmooth_picardStructureMorphism_of_preimageH2Vanishes (D : CoherentSituation B S hS)
    (hflat : IsFlat B S hS D.f.hom) (hproper : IsProper B S hS D.f.hom)
    (h0D04 : Stack.IsAlgebraicStack.{u, w} B S hS
      (picardCFG (modulePushforwardCoherence B S hS) D.toPicardSituation).val)
    (h : PicardPreimageH2Vanishes D.toPicardSituation) :
    Stack.AlgebraicStacks.IsSmooth B S hS (picardStructureMorphism D h0D04) := by
  have := Stack.faithful_fibredCategory_projection (C := B) (S := S) (hS := hS) D.Y.1
  exact
    (Stack.AlgebraicStacks.isSmooth_iff_isLocallyOfFinitePresentation_and_isFormallySmoothOnObjects
      B S hS _).2
    ⟨isLocallyOfFinitePresentation_picardStructureMorphism D hflat hproper h0D04,
      Stack.isFormallySmoothOnObjects_of_faithful_of_exists_lift
        ((shrinkHomsComparison _ h0D04).hasThickeningLifts_conj _ _
          (hasThickeningLifts_picardToBase_of_preimageH2Vanishes _ h))⟩

end AlgebraicGeometry.Space

end
