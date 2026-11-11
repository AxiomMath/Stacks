module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedAffinePullbackGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPushforwardCoherentProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.DerivedProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.CoherentCohomologyConverse
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.CoherentCohomologyEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.DerivedPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedModulePushforwardLeftTExact
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.QcqsOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyBaseChangeMap
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.TriangulatedSubcategory

/-!
# Direct images of supported perfect objects along a base change of a Noetherian model

Let `f₀ : X₀ ⟶ Y₀` be a flat morphism of finite presentation of algebraic spaces with `Y₀` affine
and Noetherian, let `T₀ ⊆ |X₀|` be a closed subset proper over `Y₀`, and let
`f₁ : X₁ ⟶ Y₁` be the base change of `f₀` along a morphism `y : Y₁ ⟶ Y₀` from an affine `Y₁`,
with projection `a : X₁ ⟶ X₀`. Then for every perfect object `P` of `D(𝒪_{X₁})` supported on
`a⁻¹T₀` the derived direct image `Rf₁_*P` is pseudo-coherent.

This is the Noetherian case of "the derived direct image of a perfect object with support proper
over the base is pseudo-coherent", carried along a base change.

* Pseudo-coherence of `Rf₁_*(-)` is a thick condition, so by the generation statement
  `AlgebraicGeometry.Space.prop_of_isPerfect_of_cohomologySupportedOn_preimage` (Stacks 0AEC and
  0GFD) it suffices to treat `La^*G₀` for a perfect `G₀ ∈ D(𝒪_{X₀})` supported on `T₀`.
* Since `f₀` is flat, `Rf₁_*La^*G₀ ≅ Ly^*Rf₀_*G₀` (Stacks 08IR), and `Ly^*` preserves
  pseudo-coherence (Stacks 08H4).
* On the Noetherian space `X₀` the perfect object `G₀` lies in `D^b_{Coh}` (Stacks 08IK) with
  cohomology supported on `T₀`, so `Rf₀_*G₀ ∈ D^b_{Coh}(𝒪_{Y₀})` by Stacks 08GK, which is
  pseudo-coherent on the Noetherian `Y₀` (Stacks 08IK).

## Main results

* `AlgebraicGeometry.Space.isPseudoCoherent_derivedModulePushforward_of_noetherianModel`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The derived direct image of a perfect object with support proper over a Noetherian model.**
Let `f₀ : X₀ ⟶ Y₀` be flat and of finite presentation with `Y₀` affine and Noetherian, `T₀ ⊆ |X₀|`
closed and proper over `Y₀`, and `X₁ = X₀ ×_{Y₀} Y₁` for an affine `Y₁`, with projections
`a : X₁ ⟶ X₀` and `f₁ : X₁ ⟶ Y₁`. Then `Rf₁_*P` is pseudo-coherent for every perfect
`P ∈ D(𝒪_{X₁})` supported on `a⁻¹T₀`. -/
theorem isPseudoCoherent_derivedModulePushforward_of_noetherianModel
    {X₀ X₁ Y₀ Y₁ : AlgebraicSpaces B S hS}
    (hY₀ : IsNoetherian B S hS B.contains_terminal Y₀.1) (hY₀a : IsAffineSpace B S hS Y₀.1)
    (hY₁ : IsAffineSpace B S hS Y₁.1) (f₀ : X₀ ⟶ Y₀) (hf₀ : IsFinitePresentation B S hS f₀.hom)
    (hfl₀ : IsFlat B S hS f₀.hom) (T₀ : Set (points B S hS X₀.1)) (hT₀ : IsClosed T₀)
    (hT₀p : IsProperOver B S hS X₀.2 Y₀.2 f₀.hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf₀.1) T₀ hT₀)
    (y : Y₁ ⟶ Y₀) (f₁ : X₁ ⟶ Y₁) (a : X₁ ⟶ X₀) (sq : IsPullback a f₁ f₀ y)
    (P : DerivedCategory (Modules.{u, u} B S hS X₁.1 X₁.2))
    (hP : (smallEtaleRingedSite B S hS X₁.1 X₁.2).IsPerfect P)
    (hPs : CohomologySupportedOn B S hS X₁.1 X₁.2 (pointsMap B S hS X₁.1 a.hom ⁻¹' T₀) P) :
    (smallEtaleRingedSite B S hS Y₁.1 Y₁.2).IsPseudoCoherent
      ((derivedModulePushforward B S hS f₁).obj P) := by
  have hft₀ := isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf₀.1
  have hf₁ : IsFinitePresentation B S hS f₁.hom :=
    (isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback sq hf₀
  have hX₀qc := isQuasiCompactSpace_of_isQuasiCompact_hom_of_isAffineSpace B S hS f₀ hf₀.2.1 hY₀a
  have hX₀qs := isAbsolutelyQuasiSeparated_of_isQuasiSeparated_hom_of_isAffineSpace B S hS
    B.contains_terminal f₀ hf₀.2.2 hY₀a
  have hX₁qc := isQuasiCompactSpace_of_isQuasiCompact_hom_of_isAffineSpace B S hS f₁ hf₁.2.1 hY₁
  have hX₁qs := isAbsolutelyQuasiSeparated_of_isQuasiSeparated_hom_of_isAffineSpace B S hS
    B.contains_terminal f₁ hf₁.2.2 hY₁
  have ha : IsAffineHom B S hS a.hom :=
    IsAffineHom.of_isPullback (AlgebraicSpaces.isPullback_hom _ _ _ sq.flip)
      (isAffineHom_of_isAffineSpace B S hS y.hom hY₁ hY₀a)
  have hX₀N := hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType B S hS
    X₀.2 Y₀.2 f₀.hom hft₀ hY₀.2.2
  have hX₀ : IsNoetherian B S hS B.contains_terminal X₀.1 := ⟨hX₀qc, hX₀qs, hX₀N⟩
  have hT₀c : IsCompact T₀ᶜ := by
    have := noetherianSpace_of_isQuasiCompact_of_isLocallyNoetherian B S hS X₀.1 X₀.2 hX₀qc hX₀N
    exact NoetherianSpace.isCompact _
  let R₁ := derivedModulePushforward B S hS f₁
  let : R₁.CommShift ℤ := derivedModulePushforward_commShift B S hS f₁
  let : R₁.IsTriangulated := derivedModulePushforward_isTriangulated B S hS f₁
  let Φ := (smallEtaleRingedSite B S hS Y₁.1 Y₁.2).isPseudoCoherentObject.inverseImage R₁
  have : Φ.IsClosedUnderIsomorphisms :=
    ⟨fun e h => (smallEtaleRingedSite B S hS Y₁.1 Y₁.2).isPseudoCoherentObject.prop_of_iso
      (R₁.mapIso e) h⟩
  have : Φ.IsStableUnderRetracts :=
    ⟨fun r h => (smallEtaleRingedSite B S hS Y₁.1 Y₁.2).isPseudoCoherentObject.prop_of_retract
      (r.map R₁) h⟩
  refine prop_of_isPerfect_of_cohomologySupportedOn_preimage a ha hX₁qc hX₁qs hX₀qc hX₀qs T₀ hT₀
    hT₀c Φ (fun G₀ hG₀ hG₀q hG₀s => ?_) P hP hPs
  -- the base change of `Rf₀_*G₀` along `y`
  have hiso := isIso_smallEtaleDerivedBaseChangeMap_of_isFlat sq hf₀.2.1 hf₀.2.2 hfl₀ G₀ hG₀q
  refine (smallEtaleRingedSite B S hS Y₁.1 Y₁.2).isPseudoCoherentObject.prop_of_iso
    (@asIso _ _ _ _ _ hiso)
    (isPseudoCoherent_smallEtaleDerivedModulePullback y _ ?_)
  -- `Rf₀_*G₀ ∈ D^b_{Coh}(𝒪_{Y₀})`
  have hG₀pc := RingedSite.isPseudoCoherent_of_isPerfect_general
    (X := smallEtaleRingedSite B S hS X₀.1 X₀.2) (E := G₀) hG₀
  obtain ⟨-, hcoh⟩ := (isPseudoCoherent_iff_of_isNoetherian B S hS X₀.1 X₀.2 B.contains_terminal
    hX₀ G₀ hG₀q).1 hG₀pc
  have hcoh' : ∀ i : ℤ, IsCoherent B S hS X₀.1 X₀.2
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X₀.1 X₀.2) i).obj G₀) := fun i =>
    (isCoherent_iff_isCoherentOnSite B S hS X₀.1 X₀.2 _).2 (hcoh i)
  obtain ⟨lo, hi, hlohi⟩ := exists_isZero_homology_of_isPerfect B S hS X₀ hX₀qc G₀ hG₀
  have hbd : DerivedCategoryB.derivedCategoryBBounded (isCoherent.{u, u} B S hS X₀.1 X₀.2) G₀ :=
    ⟨⟨⟨lo, fun n hn => hlohi n (Or.inl hn)⟩, ⟨hi, fun n hn => hlohi n (Or.inr hn)⟩⟩, hcoh'⟩
  have hRf := derivedCategoryBBounded_derivedModulePushforward_of_hasProperSupport B S hS
    B.contains_terminal f₀ hft₀ hY₀ G₀ hbd
    (hasProperSupport_homology_of_cohomologySupportedOn_of_isCoherent B S hS X₀.2 Y₀.2 f₀.hom
      hft₀ hT₀ hT₀p G₀ hG₀s hcoh')
  let eR := (derivedModulePushforwardIsoTotalRightDerived B S hS f₀).app G₀
  obtain ⟨d, hd⟩ := hRf.1.2
  exact isPseudoCoherent_of_isCoherent_homology_of_isNoetherian B S hS Y₀ B.contains_terminal hY₀
    _ (fun i => isCoherent_of_iso B S hS Y₀.2 ((DerivedCategory.homologyFunctor _ i).mapIso eR.symm)
      (hRf.2 i))
    ⟨d, fun i hi' => (hd i hi').of_iso ((DerivedCategory.homologyFunctor _ i).mapIso eR)⟩

end AlgebraicGeometry.Space

end
