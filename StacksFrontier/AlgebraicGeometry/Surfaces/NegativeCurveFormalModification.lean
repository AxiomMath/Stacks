module

public import StacksFrontier.AlgebraicGeometry.Surfaces.NegativeCurveFormalModificationTower
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFormalModification
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleAdicMonomorphism
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SmallerBaseFormalSpaces
public import StacksFrontier.AlgebraicGeometry.Morphisms.ProperModificationOffClosedPointSpace
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionEqualizerSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.RingTheory.Support.Finite

/-!
# The formal modification contracting a curve with negative normal bundle

Let `D` be an ideal sheaf on a locally Noetherian scheme `X` over `S`, with subscheme `C` and
local Noetherian ring of formal functions `A = lim Γ(Cₙ, 𝒪)` with maximal ideal `𝔪 ⊆ F₁`, and let
`kₙ : Xₙ ⟶ Y` algebraize the `𝔪`-adic tower `Xₙ = C_{M n} ×_{Spec A} Spec (A ⧸ 𝔪ⁿ⁺¹)` over a
proper `fY : Y ⟶ Spec A` (Stacks 089A,
`AlgebraicGeometry.Scheme.IdealSheafData.IsPositiveConormal.exists_isProper_algebraization`).
This file builds the morphism of formal algebraic spaces
`g : X_{/|C|} ≅ Y_{/f⁻¹(𝔪)} ⟶ (Spec A)_{/\{𝔪\}}`
of the construction of Stacks 0D5E, and shows that it is a formal modification (Stacks 0GDK) as
soon as `Y` is irreducible of dimension at most two with `Γ(Y, 𝒪_Y) = A` and `dim A ≥ 2`: then
`Y ⟶ Spec A` is an isomorphism off the closed point
(`AlgebraicGeometry.Space.isIso_pullback_snd_yoneda_map_openSubspaceOfPoints_compl_closedPoint`),
so its completion is a formal modification by Stacks 0GDM, and precomposing with the isomorphism
of completions keeps it one.

The target of `g` is the completion `W = (Spec A)_{/\{𝔪\}}` of Situation 0GH8 for Stacks 0GIB,
in the spelling of `AlgebraicGeometry.FormalSpace.completionAtClosedPoint` (to which it is
definitionally equal), and the source is the completion of `X` along `|C|` in the spelling of
`AlgebraicGeometry.Artin.ContractionSituation.ofScheme`.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.completionSheafIsoAlgebraizationClosedFibre`:
  `X_{/|C|} ≅ Y_{/f⁻¹(𝔪)}`, with the target in the form of the source of `f_{/\{𝔪\}}`.
* `AlgebraicGeometry.Scheme.IdealSheafData.algebraizationCompletionMap`: `g`.

## Main results

* `AlgebraicGeometry.FormalSpace.IsFormalModification.iso_hom_comp`: formal modifications are
  stable under precomposition with an isomorphism.
* `AlgebraicGeometry.Scheme.IdealSheafData.isFormalModification_algebraizationCompletionMap`:
  `g` is a formal modification.

## References

* [Stacks Project, Tag 0GDK](https://stacks.math.columbia.edu/tag/0GDK)
* [Stacks Project, Tag 0GDM](https://stacks.math.columbia.edu/tag/0GDM)
* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A formal modification precomposed with an isomorphism is a formal modification.** The
source stays locally Noetherian, and properness, rig-étaleness, rig-surjectivity and
rig-surjectivity of the diagonal are unchanged by an isomorphism of the source. -/
theorem IsFormalModification.iso_hom_comp {X X' Y : FppfSheaf B S hS} (e : X ≅ X')
    {h : X' ⟶ Y} (hh : IsFormalModification B S hS h) :
    IsFormalModification B S hS (e.hom ≫ h) :=
  isFormalModification_isIso_comp e.hom h
    (isLocallyNoetherian_of_iso B S hS e.symm hh.isLocallyNoetherian_source)
    hh.isLocallyNoetherian_target hh.isProper (isRigEtale_iso_hom_comp B S hS e h hh.isRigEtale)
    hh.isRigSurjective hh.isRigSurjective_diagonal

end FormalSpace

namespace Scheme.IdealSheafData

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : Scheme.{u}} (D : X.IdealSheafData) {M : ℕ → ℕ} (hX : B.Contains X) (πX : X ⟶ S)
  (hM : Monotone M)
  [IsNoetherianRing (formalNeighborhoodRing D)] [IsLocalRing (formalNeighborhoodRing D)]
  (hA : B.Contains (Spec (.of (formalNeighborhoodRing D))))
  (σ : Spec (.of (formalNeighborhoodRing D)) ⟶ S)
  (hσ : ∀ n, thickeningToSpec D n ≫ σ = (D ^ (n + 1)).subschemeι ≫ πX)
  {Y : Scheme.{u}} (fY : Y ⟶ Spec (.of (formalNeighborhoodRing D))) [IsProper fY]
  {k : ∀ n, adicTower D (IsLocalRing.maximalIdeal _) M n ⟶ Y}
  (hpb : ∀ n, IsPullback (k n) (adicTowerToThickening D (IsLocalRing.maximalIdeal _) M n) fY
    (adicThickeningι (formalNeighborhoodRing D) (IsLocalRing.maximalIdeal _) n))

omit [IsNoetherianRing (formalNeighborhoodRing D)] in
/-- The points of `Y` over the closed point of `Spec A`, read through `h_Y ⟶ h_{Spec A}`: the
inverse image of `V(𝔪)` is the inverse image of the closed point under the map of point
spaces. -/
theorem preimage_zeroLocus_maximalIdeal_eq :
    Space.pointsToScheme B S hS (algebraizationObject D hA σ fY) ⁻¹'
        (fY ⁻¹' PrimeSpectrum.zeroLocus
          (IsLocalRing.maximalIdeal (formalNeighborhoodRing D) : Set (formalNeighborhoodRing D))) =
      Space.pointsMap B S hS _ (yoneda.map (algebraizationObjectHom D hA σ fY)) ⁻¹'
        (Space.pointsToScheme B S hS (siteObject B S hS hA σ) ⁻¹'
          {IsLocalRing.closedPoint (formalNeighborhoodRing D)}) := by
  ext x
  simp only [Set.mem_preimage, Space.pointsToScheme_pointsMap_yoneda, zeroLocus_maximalIdeal,
    toScheme_map_algebraizationObjectHom]
  exact Iff.rfl

/-- **The completion of `X` along `|C|` is the completion of the algebraization along its
closed fibre** `X_{/|C|} ≅ Y_{/f⁻¹(𝔪)}`, the target written as the source of the completion
`f_{/\{𝔪\}}` of `f : h_Y ⟶ h_{Spec A}`. -/
def completionSheafIsoAlgebraizationClosedFibre [IsLocallyNoetherian X]
    (hI : IsLocalRing.maximalIdeal (formalNeighborhoodRing D) ≤ formalNeighborhoodFiltration D 1)
    (hMle : ∀ n, n ≤ M n)
    (hk : ∀ n, adicTowerSucc D (IsLocalRing.maximalIdeal _) hM n ≫ k (n + 1) = k n) :
    Space.completionSheaf B S hS (yoneda.obj (siteObject B S hS hX πX))
        (Space.pointsToScheme B S hS _ ⁻¹' (D.support : Set X)) ≅
      Space.completionSheaf B S hS (yoneda.obj (algebraizationObject D hA σ fY))
        (Space.pointsMap B S hS _ (yoneda.map (algebraizationObjectHom D hA σ fY)) ⁻¹'
          (Space.pointsToScheme B S hS (siteObject B S hS hA σ) ⁻¹'
            {IsLocalRing.closedPoint (formalNeighborhoodRing D)})) :=
  completionSheafIsoAlgebraization D _ M hX πX hM hA σ hσ fY hpb hI hMle hk ≪≫
    eqToIso (congrArg (Space.completionSheaf B S hS (yoneda.obj (algebraizationObject D hA σ fY)))
      (preimage_zeroLocus_maximalIdeal_eq D hA σ fY))

/-- **The formal contraction of `C`**: the morphism
`g : X_{/|C|} ≅ Y_{/f⁻¹(𝔪)} ⟶ (Spec A)_{/\{𝔪\}}`, the completion of the algebraization
`fY : Y ⟶ Spec A` along the closed point preceded by the comparison of completions. -/
def algebraizationCompletionMap [IsLocallyNoetherian X]
    (hI : IsLocalRing.maximalIdeal (formalNeighborhoodRing D) ≤ formalNeighborhoodFiltration D 1)
    (hMle : ∀ n, n ≤ M n)
    (hk : ∀ n, adicTowerSucc D (IsLocalRing.maximalIdeal _) hM n ≫ k (n + 1) = k n) :
    Space.completionSheaf B S hS (yoneda.obj (siteObject B S hS hX πX))
        (Space.pointsToScheme B S hS _ ⁻¹' (D.support : Set X)) ⟶
      Space.completionSheaf B S hS (yoneda.obj (siteObject B S hS hA σ))
        (Space.pointsToScheme B S hS _ ⁻¹' {IsLocalRing.closedPoint (formalNeighborhoodRing D)}) :=
  (completionSheafIsoAlgebraizationClosedFibre D hX πX hM hA σ hσ fY hpb hI hMle hk).hom ≫
    Space.completionSheafMap B S hS (yoneda.map (algebraizationObjectHom D hA σ fY)) _

/-- **The formal contraction of `C` is a formal modification** (Stacks 0GDK). Let `Y` be
irreducible of dimension at most two with `A ≅ Γ(Y, 𝒪_Y)` through `fY`, and `dim A ≥ 2`. Then
`fY` is proper and an isomorphism off the closed point of `Spec A`, so its completion along the
closed point is a formal modification (Stacks 0GDM), and so is its composite with the
isomorphism `X_{/|C|} ≅ Y_{/f⁻¹(𝔪)}`. -/
theorem isFormalModification_algebraizationCompletionMap [IsLocallyNoetherian X]
    (hI : IsLocalRing.maximalIdeal (formalNeighborhoodRing D) ≤ formalNeighborhoodFiltration D 1)
    (hMle : ∀ n, n ≤ M n)
    (hk : ∀ n, adicTowerSucc D (IsLocalRing.maximalIdeal _) hM n ≫ k (n + 1) = k n)
    (hdimA : 2 ≤ ringKrullDim (formalNeighborhoodRing D)) [IrreducibleSpace Y]
    [IsIso fY.appTop] (hdimY : topologicalKrullDim Y ≤ 2) :
    FormalSpace.IsFormalModification B S hS
      (algebraizationCompletionMap D hX πX hM hA σ hσ fY hpb hI hMle hk) := by
  refine FormalSpace.IsFormalModification.iso_hom_comp _ ?_
  have : IrreducibleSpace ((BigFppfOver.toScheme B S hS).obj (algebraizationObject D hA σ fY)) :=
    ‹IrreducibleSpace Y›
  have : AlgebraicGeometry.IsProper
      ((BigFppfOver.toScheme B S hS).map (algebraizationObjectHom D hA σ fY)) := ‹IsProper fY›
  have : IsIso ((BigFppfOver.toScheme B S hS).map (algebraizationObjectHom D hA σ fY)).appTop :=
    ‹IsIso fY.appTop›
  exact FormalSpace.isFormalModification_completionSheafMap (isAlgebraicSpace_yoneda B S hS _)
    (isAlgebraicSpace_yoneda B S hS _)
    (Space.isLocallyNoetherian_yoneda B S hS _
      (inferInstanceAs (IsLocallyNoetherian (Spec (.of (formalNeighborhoodRing D))))))
    _ _ (Space.isClosed_preimage_pointsToScheme
      (IsLocalRing.isClosed_singleton_closedPoint (formalNeighborhoodRing D)))
    (Space.isProper_yoneda_map B S hS _ ‹_›)
    (Space.isIso_pullback_snd_yoneda_map_openSubspaceOfPoints_compl_closedPoint hdimA hA σ
      (algebraizationObjectHom D hA σ fY) hdimY)

end Scheme.IdealSheafData

end AlgebraicGeometry

end
