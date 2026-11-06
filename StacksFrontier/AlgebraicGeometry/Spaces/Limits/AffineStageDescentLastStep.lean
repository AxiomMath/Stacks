module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOverAffineFpqcDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.IsomorphismOfChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineStageDescentSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismsSupplement
public import
  StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescentSituationGlobalFunctionsDescentSupplement

/-!
# Affineness of a later stage from the Cartesian square of Stacks 084U

Let `D` be a descent situation over a terminal base scheme whose limit is affine. Let `A` be a
ring with a morphism from the stage `X₀ = D.system.obj (op D.base)` to `Spec A`, let
`C = A[x₁, …, xₙ] ⧸ (g₁, …, gₙ)` be a standard-étale presentation over `A`, and let `f₀` be a
morphism over `X₀` from an affine étale chart `U₀ ⟶ X₀` to `X₀ ×_{Spec A} Spec C` whose second
component is given by functions on `U₀` killing the `g_λ`, as in the square of Stacks 084U. If the
base change of `f₀` to the limit is an isomorphism, `Spec A` and `Spec C` lie in the site and
`Spec C ⟶ Spec A` is affine, flat and surjective, then some later stage of `D` is an affine
algebraic space.

## Main results

* `DescentSituation.exists_isAffineSpace_system_obj_of_presentation_of_chartsBounded` (in the
  namespace `AlgebraicGeometry.Space`): some stage `k ≥ D.base` is an affine algebraic space.

## References

* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 084R](https://stacks.math.columbia.edu/tag/084R)
* [Stacks Project, Tag 084S](https://stacks.math.columbia.edu/tag/084S)
* [Stacks Project, Tag 084U](https://stacks.math.columbia.edu/tag/084U)
* [Stacks Project, Tag 041Z](https://stacks.math.columbia.edu/tag/041Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

/-- Pullbacks of presheaves on the big fppf site over `S`, supplied directly: instance search
for them now times out. -/
local instance (priority := high) hasLimit_cospan_presheaf_AffineStageDescentLastStep
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Z₁ Z₂ Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Z₁ ⟶ Z) (f : Z₂ ⟶ Z) :
    HasLimit (cospan g f) :=
  @HasLimitsOfShape.has_limit _ _ _ _ functorCategoryHasLimitsOfShape _

namespace DescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)

/-- In a descent situation `D` over a terminal base scheme with affine limit, let `f₀` be a
morphism over the stage `D.base` from an affine étale chart `U` to the fibre product of that stage
with `Spec C` over `Spec A`, where `C` is the standard-étale presentation algebra of `gi` over `A`
and the second component of `f₀` is given by the functions `hi` on `U`. Suppose the restriction of
`U` to the limit is the affine étale chart `W` and the coordinate map of the base-changed
presentation on `W` is bijective (`hbij`). If `Spec A` and `Spec C` lie in the site and
`Spec C ⟶ Spec A` is affine, flat and surjective, then some stage `k ≥ D.base` is an affine
algebraic space. -/
theorem exists_isAffineSpace_system_obj_of_presentation_of_chartsBounded (hterminal : IsTerminal S)
    (hI : ChartsBounded B S hS D.system)
    {Ai : Type u} [CommRing Ai] {n : ℕ} (gi : Fin n → MvPolynomial (Fin n) Ai)
    {p : D.system.obj (op D.base) ⟶ schemePoints B S hS (Spec (CommRingCat.of Ai))}
    {U : BigFppfOver B S hS}
    (hUaff : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    {a : yoneda.obj U ⟶ D.system.obj (op D.base)} (ha : IsEtale B S hS a)
    (f₀ : Over.mk a ⟶ Over.mk (pullback.fst p (schemePointsMap B S hS
      (Spec.map (CommRingCat.ofHom (presentationStructureHom gi))))))
    {ψi : Ai →+* Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)}
    {hi : Fin n → Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)}
    {hreli : ∀ l, MvPolynomial.eval₂ ψi hi (gi l) = 0}
    (hf₀snd : f₀.left ≫ pullback.snd p (schemePointsMap B S hS
          (Spec.map (CommRingCat.ofHom (presentationStructureHom gi))))
        = yonedaEquiv.symm (specMapOfGlobalHom (presentationAlgebra gi)
            (coordinateHom gi ψi hi hreli)))
    {W : BigFppfOver B S hS} (hWaff : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
    {c : yoneda.obj W ⟶ limit D.system} {b : W ⟶ U}
    (hstage : IsPullback c (yoneda.map b) (limit.π D.system (op D.base)) a)
    (hcchart : IsEtaleChart B S hS (limit D.system) (CostructuredArrow.mk c))
    (hcsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c)
    {T : BigFppfOver B S hS} (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (eT : limit D.system ≅ yoneda.obj T)
    (mp : Ai →+* Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
    {ψlim : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) →+*
      Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)}
    (hψlim : ψlim = (globalFunctionsChartRestriction B S hS D.limitObjSpace
          ⟨CostructuredArrow.mk c, hcchart⟩).comp
        (globalFunctionsAffineEquiv B S hS D.limitObjSpace T eT).symm.toRingHom)
    {hlim : Fin n → Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)}
    (hhlim : ∀ k, hlim k = ((BigFppfOver.toScheme B S hS).map b).appTop.hom (hi k))
    (hmp : ψlim.comp mp = (((BigFppfOver.toScheme B S hS).map b).appTop.hom).comp ψi)
    {hrellim : ∀ l, MvPolynomial.eval₂ ψlim hlim (MvPolynomial.map mp (gi l)) = 0}
    (hbij : Function.Bijective
      (coordinateHom (fun k => MvPolynomial.map mp (gi k)) ψlim hlim hrellim))
    (hcA : B.Contains (Spec (CommRingCat.of Ai)))
    (hcB : B.Contains (Spec (CommRingCat.of (presentationAlgebra gi))))
    (hqcg : AlgebraicGeometry.IsAffineHom
      (Spec.map (CommRingCat.ofHom (presentationStructureHom gi))))
    (hflatg : AlgebraicGeometry.Flat
      (Spec.map (CommRingCat.ofHom (presentationStructureHom gi))))
    (hsurjg : AlgebraicGeometry.Surjective
      (Spec.map (CommRingCat.ofHom (presentationStructureHom gi)))) :
    ∃ k, D.base ≤ k ∧ IsAffineSpace B S hS (D.system.obj (op k)) := by
  have hUqc : CompactSpace ((BigFppfOver.toScheme B S hS).obj U) := inferInstance
  have hUqs : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj U) := inferInstance
  let M := D.morphismDescentSystemOfPresentationOfChartsBounded hI gi p hUqc hUqs ha f₀
  let g := Spec.map (CommRingCat.ofHom (presentationStructureHom gi))
  obtain ⟨k, hk, hisok⟩ := MorphismDescentSystemOfChartsBounded.exists_isIso_mapAt M
    (D.isIso_mapLimit_morphismDescentSystemOfPresentation hterminal hI gi hUqc hUqs
      ha f₀ hf₀snd hWaff hstage hcchart hcsurj hT eT mp hψlim hhlim hmp hbij)
    (isLocallyOfFinitePresentation_left_of_presentationBaseChange B S hS
      (D.algebraicSpace D.base) gi p ha f₀)
  refine ⟨k, hk, ?_⟩
  have hTgtaff : IsAffineSpace B S hS (M.targetAt k hk) :=
    (MorphismDescentSystemOfChartsBounded.isAffineSpace_sourceAt _
      (isAffineSpace_yoneda B S hS U hUaff) k hk).of_iso (asIso (M.mapAt k hk))
  have hpaste : IsPullback
      (pullback.fst (M.baseAtToInitial k hk) (pullback.fst p (schemePointsMap B S hS g)))
      (pullback.snd (M.baseAtToInitial k hk) (pullback.fst p (schemePointsMap B S hS g)) ≫
        pullback.snd p (schemePointsMap B S hS g))
      (M.baseAtToInitial k hk ≫ p) (schemePointsMap B S hS g) :=
    (M.targetAt_isPullback k hk).paste_vert (IsPullback.of_hasPullback _ _)
  have haff : ∀ {Z : Scheme.{u}} [IsAffine Z] (hc : B.Contains Z),
      IsAffine ((BigFppfOver.toScheme B S hS).obj (terminalSiteObject B S hS hterminal hc)) :=
    fun hc => by rw [toScheme_terminalSiteObject]; infer_instance
  have hpb' : IsPullback
      (pullback.fst (M.baseAtToInitial k hk) (pullback.fst p (schemePointsMap B S hS g)))
      ((pullback.snd (M.baseAtToInitial k hk) (pullback.fst p (schemePointsMap B S hS g)) ≫
        pullback.snd p (schemePointsMap B S hS g)) ≫
        (schemePointsIso B S hS hterminal hcB).symm.hom)
      ((M.baseAtToInitial k hk ≫ p) ≫ (schemePointsIso B S hS hterminal hcA).symm.hom)
      (yoneda.map (siteHomOfTerminal B S hS hterminal hcB hcA g)) :=
    hpaste.of_iso' (Iso.refl _) (Iso.refl _) (schemePointsIso B S hS hterminal hcB)
      (schemePointsIso B S hS hterminal hcA) (by simp) (by simp) (by simp)
      (schemePointsUnit_comp_schemePointsMap_siteHom B S hS hterminal hcB hcA _)
  refine isAffineSpace_of_isAffineSpace_pullback_of_fpqcSingleton B S hS hZ
    (D.algebraicSpace k)
    (WA := ⟨terminalSiteObject B S hS hterminal hcA, haff hcA⟩)
    (WB := ⟨terminalSiteObject B S hS hterminal hcB, haff hcB⟩)
    ((M.baseAtToInitial k hk ≫ p) ≫ (schemePointsIso B S hS hterminal hcA).symm.hom)
    (siteHomOfTerminal B S hS hterminal hcB hcA g)
    ?_ ?_ ?_ hpb' hTgtaff
  all_goals rwa [toScheme_map_siteHomOfTerminal]

end DescentSituation

end AlgebraicGeometry.Space

end
