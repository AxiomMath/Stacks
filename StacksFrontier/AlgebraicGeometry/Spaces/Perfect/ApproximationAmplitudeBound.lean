module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationAffineMember
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationInductionStep
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.Noetherian.BoundedAbove
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SurjectivePoints

/-!
# The amplitude of a pseudo-coherent object over a quasi-compact étale space

Let `g : Y ⟶ X` be an étale morphism of algebraic spaces over a scheme `S` with `Y`
quasi-compact, and let `E` be an object of `D_QCoh(𝒪_X)` which is `m`-pseudo-coherent.  Then
there is an integer `t` with `Hⁱ(E)|_Y = 0` for all `i > t`: the cohomology sheaves of `E` are
supported off the image of `|Y|` in all large degrees.

In the proof of Stacks 08HN this is the existence of "the largest integer `t` such that
`Hᵗ(E)|_U` is nonzero", which the source justifies by "`U` is quasi-compact and `E|_U` is
`(m - r)`-pseudo-coherent".  A quasi-compact `Y` has a surjective étale chart `h_{U₀} ⟶ Y` with
`U₀` quasi-compact (Stacks 03E3); the restriction of `E` to `h_{U₀}` is `ε^*E₀` for an
`m`-pseudo-coherent `E₀` on the scheme `U₀` (Stacks 071Q and 08HE), whose cohomology vanishes in
large degrees because `U₀` is quasi-compact.

## Main results

* `AlgebraicGeometry.Space.exists_cohomologySupportedOnFrom_compl_range`

## References

* [Stacks Project, Tag 08HN](https://stacks.math.columbia.edu/tag/08HN)
* [Stacks Project, Tag 03E3](https://stacks.math.columbia.edu/tag/03E3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 10000] HasDerivedCategory.standard smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective smallEtaleRingedSite_hasSheafify_over
  smallEtaleRingedSite_wEqualsLocallyBijective_over

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

/-- **The cohomology of a pseudo-coherent object is supported off a quasi-compact étale space
in large degrees.** -/
theorem exists_cohomologySupportedOnFrom_compl_range {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X)
    (hg : IsEtale B S hS g.hom) (hYqc : IsQuasiCompactSpace B S hS Y.1)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) (m : ℤ)
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom E.obj m) :
    ∃ t : ℤ, CohomologySupportedOnFrom B S hS X.1 X.2
      (Set.range (pointsMap B S hS Y.1 g.hom))ᶜ (t + 1) E.obj := by
  obtain ⟨U₀, a, hcpt, hsurj, ha⟩ := hYqc
  have := hcpt
  let A : (⟨yoneda.obj U₀, isAlgebraicSpace_yoneda B S hS U₀⟩ : AlgebraicSpaces B S hS) ⟶ Y :=
    ObjectProperty.homMk a
  let c := A ≫ g
  have hc : IsEtale B S hS c.hom := isEtale_comp B S hS ha hg
  have := etaleModulePullback_additive.{u, u} B S hS c hc
  have := preservesFiniteLimits_etaleModulePullback B S hS c hc
  have := preservesFiniteColimits_etaleModulePullback B S hS c hc
  let E' := (etaleModulePullback.{u, u} B S hS c hc).mapDerivedCategory.obj E.obj
  have hE'q := derivedQuasicoherent_etaleModulePullback B S hS c hc E.obj E.property
  have hE'pc := isPseudoCoherentFrom_etaleModulePullback B S hS c hc E.obj m hE
  obtain ⟨E₀, hqc₀, ⟨eE⟩⟩ := exists_representedDerivedAssociatedModule_iso B S hS U₀ E' hE'q
  obtain ⟨K, hK, ⟨f⟩⟩ := hE'pc
  have hE₀ := isPseudoCoherentFrom_of_representedDerivedAssociatedModule B S hS U₀ E₀ m
    ⟨K, hK, ⟨f ≪≫ eE.symm⟩⟩
  obtain ⟨b, hb⟩ := isBoundedAbove_of_isPseudoCoherentFrom _ E₀ m hE₀
  refine ⟨b, ?_⟩
  have hzero : ∀ i : ℤ, b + 1 ≤ i → IsZero ((etaleModulePullback.{u, u} B S hS c hc).obj
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj E.obj)) := by
    intro i hi
    have h₀ : IsZero ((DerivedCategory.homologyFunctor _ i).obj E₀) := hb i (by omega)
    have h₁ : IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((representedDerivedAssociatedModule B S hS U₀).obj E₀)) :=
      ((representedAssociatedModule B S hS U₀ (isAlgebraicSpace_yoneda B S hS U₀)).map_isZero
        h₀).of_iso (((representedAssociatedModule B S hS U₀
          (isAlgebraicSpace_yoneda B S hS U₀)).mapDerivedCategoryHomologyIso i).app E₀)
    exact (h₁.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso eE).symm).of_iso
      (((etaleModulePullback.{u, u} B S hS c hc).mapDerivedCategoryHomologyIso i).app E.obj).symm
  have hsupp := cohomologySupportedOnFrom_compl_range_of_isZero B S hS c hc (b + 1) E.obj hzero
  have hrange : Set.range (pointsMap B S hS _ c.hom) = Set.range (pointsMap B S hS Y.1 g.hom) := by
    change Set.range (pointsMap B S hS _ (a ≫ g.hom)) = _
    rw [pointsMap_comp, Set.range_comp,
      (surjective_pointsMap_of_presheaf_surjective B S hS a hsurj).range_eq, Set.image_univ]
  rwa [hrange] at hsupp

end AlgebraicGeometry.Space
