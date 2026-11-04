module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartPrimeAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDerivedSectionsHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentAffineChartOverLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedCoherator.Bound
public import StacksFrontier.Homology.Perfect.RelativeBaseChangeVanishingAbove

/-!
# The local step of [Stacks, Tag 0CX9]: a chart on which `K` is a finitely presented module

Let `X` be an algebraic space over an affine `T`, locally of finite type, and `K ∈ D_QCoh(𝒪_X)`
pseudo-coherent relative to `T`, with no cohomology sheaves in negative degrees. Let
`p₀ : T₀ ⟶ T` have surjective ring map, and assume that on every affine chart `U` the derived
base change `RΓ(U, K) ⊗^𝐋_{Γ(T)} Γ(T₀)` has no cohomology in positive degrees. Then every point
`x` of `X` lying over `T₀` lies on an affine chart `c` with

1. `Γ(T', Hⁱ(K)) = 0` for `i ≠ 0` and every chart `T' ⟶ c`,
2. `Γ(T', H⁰(K))` finitely presented over `Γ(T')` for every affine chart `T' ⟶ c`,
3. `Hⁱ(RΓ(c, K)) = 0` for `i > 0`.

This is the first half of the proof of [Stacks, Tag 0CX9], with `T₀ = Spec(A₁)`: choose an
affine chart `U` at `x` and the prime `𝔭` of `x` on it
(`AlgebraicGeometry.Space.exists_isAffineChart_prime_of_pointsMap_mem_range`), spread the
vanishing out to `g ∉ 𝔭`
(`StacksDraft.Perfect.exists_forall_pow_smul_eq_zero_of_isRelativelyPseudoCoherent`,
in place of the source's shortening of a finite free complex), and take `c = D(g)`: the sections
of the quasi-coherent `Hⁱ(K)` over `D(g)` are the localization of those over `U`
(`AlgebraicGeometry.Space.isLocalizedModule_chartRestrictLinear_openChart_basicOpen`), read through
`Hⁱ(RΓ(U, K)) = Γ(U, Hⁱ(K))` (`AlgebraicGeometry.Space.chartDerivedSectionsHomologyIso`).

## Main results

* `AlgebraicGeometry.Space.exists_affineChart_vanishing_of_isRelativelyPseudoCoherent`.

## References

* [Stacks Project, Tag 0CX9](https://stacks.math.columbia.edu/tag/0CX9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] hasRightDerivedFunctor_chartSections

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A module over the sections of an affine chart, all of whose elements are killed by powers of
`g`, has no sections over the basic open `D(g)` when it is the module of sections of a
quasi-coherent module. -/
theorem subsingleton_val_obj_openChart_basicOpen (X : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite)
    (U : SmallEtale B S hS X.1) (hU : IsAffine (chartScheme U)) (g : chartRing B S hS X.1 X.2 U)
    (hg : ∀ y : M.val.obj (op U), ∃ k : ℕ, g ^ k • y = 0) :
    Subsingleton (M.val.obj (op (openChart B S hS X.1 U ((chartScheme U).basicOpen g)))) := by
  let := chartSectionsModule M (openChartInclusion B S hS X.1 U ((chartScheme U).basicOpen g))
  have hl := isLocalizedModule_chartRestrictLinear_openChart_basicOpen B S hS X.2 M
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 M hM) U hU g
  have : Subsingleton (LocalizedModule (Submonoid.powers g) (M.val.obj (op U))) :=
    LocalizedModule.subsingleton_iff.2 fun m => by
      obtain ⟨k, hk⟩ := hg m
      exact ⟨g ^ k, ⟨k, rfl⟩, hk⟩
  exact (IsLocalizedModule.iso (Submonoid.powers g)
    (chartRestrictLinear M (openChartInclusion B S hS X.1 U
      ((chartScheme U).basicOpen g)))).symm.injective.subsingleton

/-- **The local step of [Stacks, Tag 0CX9].** -/
theorem exists_affineChart_vanishing_of_isRelativelyPseudoCoherent (X : AlgebraicSpaces B S hS)
    {T T₀ : BigFppfOver B S hS} [hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (hX : X.1 ⟶ yoneda.obj T) (hf : IsLocallyOfFiniteType B S hS hX) (p₀ : T₀ ⟶ T)
    (hp₀ : Function.Surjective (representedAffineCommRingCatHom B S hS p₀).hom)
    (K : spaceDerivedCategory B S hS X) (hK : spaceQuasicoherentProp B S hS X K)
    (hKb : SpaceCohomologyVanishesBelow X 0 K)
    (hrel : IsRelativelyPseudoCoherent B S hS X.1 X.2 hX hf ⟨K, hK⟩)
    (ha : ∀ U : SmallEtale B S hS X.1, IsAffineChart B S hS X.1 U → ∀ i : ℤ, 0 < i →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (representedAffineCommRingCatHom B S hS p₀).hom).functor.obj
          ((ModuleCat.restrictScalars (representedAffineCommRingCatHom B S hS
            (yoneda.preimage (U.1.hom ≫ hX))).hom).mapDerivedCategory.obj
            ((Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections
              (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
                U).obj K)))))
    (x : points B S hS X.1)
    (hx : pointsMap B S hS X.1 hX x ∈
      Set.range (pointsMap B S hS (yoneda.obj T₀) (yoneda.map p₀))) :
    ∃ c : SmallEtale B S hS X.1, IsAffineChart B S hS X.1 c ∧ x ∈ chartPointsRange (X := X) c ∧
      (∀ i : ℤ, i ≠ 0 → ∀ T' : SmallEtale B S hS X.1, (T' ⟶ c) →
        IsZero (((spaceDerivedHomology B S hS X i).obj K).val.obj (op T'))) ∧
      (∀ T' : SmallEtale B S hS X.1,
        IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj T') →
        (T' ⟶ c) → Module.FinitePresentation (chartRing B S hS X.1 X.2 T')
          (((spaceDerivedHomology B S hS X 0).obj K).val.obj (op T'))) ∧
      (∀ i : ℤ, 0 < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
            c).obj K))) := by
  obtain ⟨U, hU, P, hP, hker, hpts⟩ :=
    exists_isAffineChart_prime_of_pointsMap_mem_range B S hS X hX p₀ x hx
  let V := selfChart B S hS T
  have hV : IsAffine (chartScheme V) := hT
  -- the two consequences of relative pseudo-coherence at an affine chart `W`
  have key : ∀ (W : SmallEtale B S hS X.1) (hW : IsAffine (chartScheme W)),
      have : IsAffine ((BigFppfOver.toScheme B S hS).obj W.obj.left) := hW
      have : IsAffine ((BigFppfOver.toScheme B S hS).obj V.obj.left) := hV
      let : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map
          (yoneda.preimage (W.1.hom ≫ hX))) :=
        hf _ _ W.obj.hom V.obj.hom _ W.property V.property
          ((Category.comp_id _).trans (yoneda.map_preimage _))
      let : Algebra ((structurePresheaf B S hS (yoneda.obj T)).obj (op V))
          ((structurePresheaf B S hS X.1).obj (op W)) :=
        (((BigFppfOver.toScheme B S hS).map (yoneda.preimage (W.1.hom ≫ hX))).appTop.hom).toAlgebra
      let : Algebra.FiniteType ((structurePresheaf B S hS (yoneda.obj T)).obj (op V))
          ((structurePresheaf B S hS X.1).obj (op W)) :=
        HasRingHomProperty.appTop (@LocallyOfFiniteType)
          ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (W.1.hom ≫ hX))) inferInstance
      (∀ (P : Ideal ((structurePresheaf B S hS X.1).obj (op W))) [P.IsPrime],
        RingHom.ker (representedAffineCommRingCatHom B S hS p₀).hom ≤
          P.comap (algebraMap ((structurePresheaf B S hS (yoneda.obj T)).obj (op V))
            ((structurePresheaf B S hS X.1).obj (op W))) →
        ∃ g : chartRing B S hS X.1 X.2 W, g ∉ P ∧ ∀ i : ℤ, 0 < i →
          ∀ y : (DerivedCategory.homologyFunctor (ModuleCat (chartRing B S hS X.1 X.2 W)) i).obj
            (chartDerivedSections B S hS X.1 X.2 W ⟨K, hK⟩), ∃ k : ℕ, g ^ k • y = 0) ∧
      ((∀ i : ℤ, 0 < i → IsZero
          ((DerivedCategory.homologyFunctor (ModuleCat (chartRing B S hS X.1 X.2 W)) i).obj
            (chartDerivedSections B S hS X.1 X.2 W ⟨K, hK⟩))) →
        Module.FinitePresentation (chartRing B S hS X.1 X.2 W)
          ((DerivedCategory.homologyFunctor (ModuleCat (chartRing B S hS X.1 X.2 W)) 0).obj
            (chartDerivedSections B S hS X.1 X.2 W ⟨K, hK⟩))) := by
    intro W hW _ _ _ _ _
    have h : ∀ m : ℤ, _root_.PseudoCoherence.IsRelativelyPseudoCoherentFrom
        (R := (structurePresheaf B S hS (yoneda.obj T)).obj (op V))
        (chartDerivedSections B S hS X.1 X.2 W ⟨K, hK⟩) m := fun m =>
      hrel m W V (yoneda.preimage (W.1.hom ≫ hX))
        ((Category.comp_id _).trans (yoneda.map_preimage _)) hW hV
    exact ⟨fun P _ hker =>
      StacksDraft.Perfect.exists_forall_pow_smul_eq_zero_of_isRelativelyPseudoCoherent
        (chartDerivedSections B S hS X.1 X.2 W ⟨K, hK⟩) h
        (representedAffineCommRingCatHom B S hS p₀).hom hp₀ 0 (ha W hW) P hker,
      StacksDraft.Perfect.finitePresentation_homology_zero_of_isRelativelyPseudoCoherent
        (chartDerivedSections B S hS X.1 X.2 W ⟨K, hK⟩) (h _)⟩
  -- spreading out the vanishing at `U`
  have hU' : IsAffine (chartScheme U) := hU
  obtain ⟨g, hgP, hg⟩ := @(key U hU').1 P hP hker
  let g' : chartRing B S hS X.1 X.2 U := g
  let c := openChart B S hS X.1 U ((chartScheme U).basicOpen g')
  have hc' : IsAffine (chartScheme c) :=
    isAffine_chartScheme_openChart_basicOpen B S hS X.1 U hU' g'
  have hc : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj c) := hc'
  -- the sections of `Hⁱ(K)`, `i > 0`, over `U` are killed by powers of `g`
  have hgU : ∀ i : ℤ, 0 < i → ∀ y : ((spaceDerivedHomology B S hS X i).obj K).val.obj (op U),
      ∃ k : ℕ, g' ^ k • y = 0 := by
    intro i hi y
    let e := (chartDerivedSectionsHomologyIso B S hS X K hK U hU i).toLinearEquiv
    obtain ⟨k, hk⟩ := hg i hi (e y)
    refine ⟨k, e.injective ?_⟩
    rwa [map_smul, map_zero]
  have hsub : ∀ i : ℤ, 0 < i →
      Subsingleton (((spaceDerivedHomology B S hS X i).obj K).val.obj (op c)) := fun i hi =>
    subsingleton_val_obj_openChart_basicOpen B S hS X _ (hK i) U hU' g' (hgU i hi)
  have hle : ∀ i : ℤ, 0 < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
          c).obj K)) := fun i hi =>
    have := hsub i hi
    (ModuleCat.isZero_of_subsingleton _).of_iso
      (chartDerivedSectionsHomologyIso B S hS X K hK c hc i).symm
  refine ⟨c, hc, hpts g' hgP, fun i hi T' f => ?_, fun T' hT' f => ?_, hle⟩
  · rcases lt_or_gt_of_ne hi with hneg | hpos
    · exact Functor.map_isZero (SheafOfModules.evaluation _ (op T')) (hKb i hneg)
    · have := subsingleton_val_obj_of_subsingleton_affineChart (hK i) hc (hsub i hpos) T' f
      exact ModuleCat.isZero_of_subsingleton _
  · have := (key c hc').2 hle
    exact finitePresentation_val_obj_of_finitePresentation_affineChart (hK 0) hc hT' f
      (Module.FinitePresentation.of_equiv
        (chartDerivedSectionsHomologyIso B S hS X K hK c hc 0).symm.toLinearEquiv)

end AlgebraicGeometry.Space

end
