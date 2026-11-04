module

public import StacksFrontier.AlgebraicGeometry.Quot.DegreeZeroSectionsChartModel
public import StacksFrontier.AlgebraicGeometry.Quot.AffineLocalRepresentability
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineMemberThroughPoint
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.SheafConditionAffine

/-!
# Local representability of the degree-zero sections functor

Let `K` be a pseudo-coherent object of `D(𝒪_X)` on an algebraic space `X` such that
`H⁻¹(Lg^*K) = 0` for every scheme `g : T → X`, and let `P₀` be a K-flat complex with flat terms
representing `K`.  Then every scheme over `X` is covered, in the fppf topology, by schemes over
which the degree-zero sections functor of `P₀` is represented by a scheme affine and of finite
presentation: this is the representability half of the proof of Stacks 08JX, part (1).

The covering is built from an étale atlas `U₀ ⟶ X` and the strictly perfect approximations of
`P₀` on a covering of `U₀` that pseudo-coherence provides (Stacks 08FT and 08FU): for a point `z`
of a scheme `Z` over `X`, a point of `Z ×_X U₀` over `z` maps to a point of `U₀`, which lies in
the image of a chart `V ⟶ U₀` carrying an approximation; the fibre product
`(Z ×_X U₀) ×_{U₀} V` is étale over `Z` and maps to `V`, and the local model of
`AlgebraicGeometry.Space.exists_open_restriction_matKerIso` on it gives an open neighbourhood of a
point over `z` on which the functor is the kernel functor of a matrix.

## Main results

* `AlgebraicGeometry.Space.exists_etale_neighbourhood_representedOverLift`: the local model at a
  point of a scheme over `X`.
* `AlgebraicGeometry.Space.exists_covering_representedOverLift`: the covering of a scheme over
  `X` by schemes over which the functor is represented.

## References

* [Stacks Project, Tag 08JX](https://stacks.math.columbia.edu/tag/08JX)
* [Stacks Project, Tag 08FU](https://stacks.math.columbia.edu/tag/08FU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (IsKFlat)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] etaleModulePullback_additive

-- The inverse images are never unfolded here: two inverse images along equal morphisms are
-- compared, and unfolding them makes the unifier time out.
attribute [local irreducible] modulePullback

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable {X : AlgebraicSpaces B S hS} (P₀ : CochainComplex (toposModules B S hS X) ℤ)
  (hP₀ : IsKFlat (Y := smallEtaleRingedTopos B S hS X)
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P₀))
  {K : derivedModules B S hS X} (hK : IsPseudoCoherentObject K)
  (hL : BottomRankStratum.HasDerivedModulePullbacks B S hS)
  (hvan : HasVanishingDegreeNegOneDerivedPullback hL K) (e : DerivedCategory.Q.obj P₀ ≅ K)

include hK e in
/-- **A K-flat representative of a pseudo-coherent object is a `(-2)`-pseudo-coherent complex**
(Stacks 08FU, part (2)). -/
theorem isPseudoCoherentComplexFrom_representative :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentComplexFrom P₀ (-2) := by
  obtain ⟨K', hK', ⟨e'⟩⟩ := hK
  exact RingedSite.isPseudoCoherentComplexFrom_of_iso_general _ K (-2) ⟨K', hK' (-2), ⟨e'⟩⟩ P₀ e


include hK e in
/-- **The chart data at a point of a scheme over `X`.**  Every point `z` of a scheme `Z` over `X`
lies in the image of an étale morphism `p : c ⟶ Z` whose composite to `X` factors through an
étale chart `V` of `X` carrying a strictly perfect approximation above degree `-2` of the
pullback of `P₀`. -/
theorem exists_etale_chart_data (Z : SchemesOver X)
    (z : (BigFppfOver.toScheme B S hS).obj Z.left) :
    ∃ (c : BigFppfOver B S hS) (p : c ⟶ Z.left) (V : SmallEtale B S hS X.1) (a : c ⟶ V.1.left)
      (P : CochainComplex (toposModules B S hS ((schemeSpaceFunctor B S hS).obj V.1.left)) ℤ)
      (_ : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS ((schemeSpaceFunctor B S hS).obj V.1.left).1
          ((schemeSpaceFunctor B S hS).obj V.1.left).2).O) P)
      (γ : P ⟶ (((toposModulePullbackData B S hS).pull (chartMorphism V)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P₀),
      (∀ j : ℤ, -2 < j → IsIso (HomologicalComplex.homologyMap γ j)) ∧
        Epi (HomologicalComplex.homologyMap γ (-2)) ∧
        Etale ((BigFppfOver.toScheme B S hS).map p) ∧
        z ∈ Set.range ((BigFppfOver.toScheme B S hS).map p).base ∧
        (schemeSpaceFunctor B S hS).map p ≫ Z.hom =
          (schemeSpaceFunctor B S hS).map a ≫ chartMorphism V := by
  have : HasPullbacks (BigFppfOver B S hS) := by
    let := B.hasPullbacks_schemes
    infer_instance
  let T := BigFppfOver.toScheme B S hS
  obtain ⟨U₀, f₀, hsurj, het⟩ := X.2.exists_atlas
  let V₀ : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk f₀, het⟩
  obtain ⟨Sv, hSv, hdata⟩ := isPseudoCoherentComplexFrom_representative P₀ hK e V₀
  let g : yoneda.obj Z.left ⟶ X.1 := Z.hom.hom
  let sndW := het.rep.snd g
  let fstW := het.rep.fst' g
  have sqW : IsPullback (yoneda.map fstW) (yoneda.map sndW) f₀ g := het.rep.isPullback' g
  have hsW : Surjective (T.map sndW) := hsurj.property g _ _ sqW
  have heW : Etale (T.map sndW) := het.property g _ _ sqW
  obtain ⟨w, hw⟩ := hsW.surj z
  obtain ⟨Q, φ, hφ, -, hu⟩ := SmallEtale.exists_affine_mem_range_of_mem_topology B S hS X.1
    (T := Sieve.generate Sv) hSv ((T.map fstW).base w)
  obtain ⟨V, h, s, hs, hhs⟩ := hφ
  obtain ⟨P, hP, α, hiso, hepi⟩ := hdata s hs
  obtain ⟨P', hP', γ, hγ, hγ'⟩ := exists_chartApproximation P₀ (-2) V P hP α hiso hepi
  let P'' : CochainComplex (toposModules B S hS ((schemeSpaceFunctor B S hS).obj V.1.left)) ℤ := P'
  have hP'' : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS ((schemeSpaceFunctor B S hS).obj V.1.left).1
        ((schemeSpaceFunctor B S hS).obj V.1.left).2).O) P'' := hP'
  have : (modulePullback B S hS (chartToSpace B S hS X V)).Additive :=
    toposModulePullbackData_additive (chartToSpace B S hS X V)
  let c := (NatIso.mapHomologicalComplex (modulePullbackIsoEtaleModulePullback B S hS
    (chartToSpace B S hS X V) (isEtale_chartToSpace B S hS X V)).symm (ComplexShape.up ℤ)).app P₀
  let γ'' : P'' ⟶ (((toposModulePullbackData B S hS).pull (chartMorphism V)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P₀ := γ ≫ c.hom
  have hγ₁ : ∀ j : ℤ, -2 < j → IsIso (HomologicalComplex.homologyMap γ'' j) :=
    fun j hj => RingedSite.isIso_homologyMap_comp_iso _ c j (hγ j hj)
  have hγ₂ : Epi (HomologicalComplex.homologyMap γ'' (-2)) :=
    RingedSite.epi_homologyMap_comp_iso _ c (-2) hγ'
  clear_value P'' γ''
  let sV : V.1.left ⟶ U₀ := (SmallEtale.toOver B S hS X.1).map s
  have hsV : Etale (T.map sV) := etale_of_etale_charts B S hS V.1.hom f₀ V.2 het sV
    (CostructuredArrow.w s.hom)
  let pr1 := pullback.fst fstW sV
  let pr2 := pullback.snd fstW sV
  have hsq : IsPullback (T.map pr1) (T.map pr2) (T.map fstW) (T.map sV) :=
    (IsPullback.of_hasPullback fstW sV).map T
  have hpr1 : Etale (T.map pr1) :=
    AlgebraicGeometry.Etale.etale_isStableUnderBaseChange.of_isPullback hsq.flip hsV
  -- a point of the fibre product over `z`
  obtain ⟨y, hy⟩ := hu
  have hyu : (T.map sV).base ((T.map ((SmallEtale.toOver B S hS X.1).map h)).base y) =
      (T.map fstW).base w := by
    rw [← hy, ← hhs, Functor.map_comp, Functor.map_comp, Scheme.Hom.comp_base, TopCat.comp_app]
  obtain ⟨x, hx1, hx2⟩ := Scheme.Pullback.exists_preimage_pullback w
    ((T.map ((SmallEtale.toOver B S hS X.1).map h)).base y) hyu.symm
  let x' := (PreservesPullback.iso T fstW sV).inv.base x
  have hx' : (T.map pr1).base x' = w := by
    show (T.map pr1).base ((PreservesPullback.iso T fstW sV).inv.base x) = w
    rw [← Scheme.Hom.comp_apply, PreservesPullback.iso_inv_fst, hx1]
  -- the local model on the fibre product
  have hcomm : (schemeSpaceFunctor B S hS).map (pr1 ≫ sndW) ≫ Z.hom =
      (schemeSpaceFunctor B S hS).map pr2 ≫ chartMorphism V := by
    refine ObjectProperty.hom_ext _ ?_
    show yoneda.map (pr1 ≫ sndW) ≫ g = yoneda.map pr2 ≫ V.1.hom
    calc yoneda.map (pr1 ≫ sndW) ≫ g = yoneda.map pr1 ≫ yoneda.map fstW ≫ f₀ := by
          rw [sqW.w, Functor.map_comp, Category.assoc]
      _ = yoneda.map (pr2 ≫ sV) ≫ f₀ := by
          rw [← pullback.condition, Functor.map_comp, Category.assoc]
      _ = yoneda.map pr2 ≫ V.1.hom := by
          rw [Functor.map_comp, Category.assoc]
          exact congrArg (fun k => yoneda.map pr2 ≫ k) (CostructuredArrow.w s.hom)
  refine ⟨_, pr1 ≫ sndW, V, pr2, P'', hP'', γ'', hγ₁, hγ₂, ?_, ⟨x', ?_⟩, hcomm⟩
  · rw [Functor.map_comp]
    infer_instance
  · rw [Functor.map_comp, Scheme.Hom.comp_base, TopCat.comp_app, hx', hw]

include hP₀ hK hvan e in
/-- **Stacks 08JX, the local model at a point of a scheme over `X`.**  Every point of a scheme `Z`
over `X` lies in the image of an étale morphism `d ⟶ Z` over which the degree-zero sections
functor of `P₀` is represented by a scheme affine and of finite presentation over `d`. -/
theorem exists_etale_neighbourhood_representedOverLift (Z : SchemesOver X)
    (z : (BigFppfOver.toScheme B S hS).obj Z.left) :
    ∃ (d : BigFppfOver B S hS) (q : d ⟶ Z.left),
      Etale ((BigFppfOver.toScheme B S hS).map q) ∧
        z ∈ Set.range ((BigFppfOver.toScheme B S hS).map q).base ∧
        IsAffineFinitePresentationRepresentedOverLift
          (degreeZeroSectionsFunctor (schemesOverCone X) P₀) (precompTest Z q) := by
  obtain ⟨c, p, V, a, P, hP, γ, hγ₁, hγ₂, hpe, ⟨x, hx⟩, hcomm⟩ :=
    exists_etale_chart_data P₀ hK e Z z
  obtain ⟨d, t, hoi, ⟨y', hy'⟩, r, m, N, ⟨eN⟩⟩ := exists_open_restriction_matKerIso P₀ hP₀
    (chartMorphism V) P hP γ hγ₁ hγ₂ hL hvan e a x
  obtain ⟨W', w', haff, hlfp, ⟨eW⟩⟩ := exists_matKerFunctor_iso d N
  have hk : (precompTest Z (t ≫ p)).hom =
      (schemeSpaceFunctor B S hS).map (t ≫ a) ≫ chartMorphism V := by
    show (schemeSpaceFunctor B S hS).map (t ≫ p) ≫ Z.hom = _
    rw [Functor.map_comp, Category.assoc, hcomm, ← Category.assoc, ← Functor.map_comp]
  refine ⟨d, t ≫ p, ?_, ⟨y', ?_⟩, W', w', haff, hlfp, ⟨eW ≪≫ eN.symm ≪≫
    eqToIso (congrArg (fun k => (CostructuredArrow.map k).op ⋙
      degreeZeroSectionsFunctor (schemesOverCone X) P₀) hk.symm)⟩⟩
  · rw [Functor.map_comp]
    infer_instance
  · rw [Functor.map_comp, Scheme.Hom.comp_base, TopCat.comp_app, hy', hx]

include hP₀ hK hvan e in
/-- **The degree-zero sections functor is represented locally on every scheme over `X`**: every
scheme `Z` over `X` carries a family of étale morphisms generating a covering sieve, over each
member of which the functor is represented by a scheme affine and of finite presentation. -/
theorem exists_covering_representedOverLift (Z : SchemesOver X) :
    ∃ T : Presieve Z.left, Sieve.generate T ∈ BigFppfOver.topology B S hS Z.left ∧
      ∀ ⦃c : BigFppfOver B S hS⦄ (q : c ⟶ Z.left), T q →
        IsAffineFinitePresentationRepresentedOverLift
          (degreeZeroSectionsFunctor (schemesOverCone X) P₀) (precompTest Z q) := by
  choose d q hq hz hrep using fun z =>
    exists_etale_neighbourhood_representedOverLift P₀ hP₀ hK hL hvan e Z z
  refine ⟨Presieve.ofArrows d q, BigFppfOver.sieve_generate_ofArrows_mem_topology d q ?_, ?_⟩
  · rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨fun y => ⟨y, hz y⟩, fun y => ?_⟩
    have := hq y
    exact ⟨inferInstance, inferInstance⟩
  · rintro c q' ⟨z⟩
    exact hrep z

end AlgebraicGeometry.Space

end
