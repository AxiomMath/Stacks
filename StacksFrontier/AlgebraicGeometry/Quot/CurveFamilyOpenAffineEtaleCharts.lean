module

public import StacksFrontier.AlgebraicGeometry.Quot.StableFamilyDualizingAmpleOverOpen
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableLocusOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange

/-!
# Affine étale scheme charts of a prestable family over an open of the base

Let `f : X → S` be a prestable family of curves, `U ⊆ S` an open and `X₁ = f⁻¹(U)`, presented
by a cartesian square over `U ⊆ S`. The restricted family `X₁ → U`
(`AlgebraicGeometry.CurveFamily.ofIsPullback`) is prestable, and Stacks 0E6F gives it étale
local scheme charts. Restricting the charts to affine opens, `X₁` is covered, for the étale
topology, by schemes `Zᵢ` with cartesian squares

    Zᵢ ⟶ X₁
    ↓     ↓
    Tᵢ ⟶ U

where `Tᵢ` is affine, `Tᵢ ⟶ U` is étale and `Zᵢ ⟶ Tᵢ` is a proper, flat, finitely presented,
at-worst-nodal morphism of schemes of relative dimension one.

## Main results

* `AlgebraicGeometry.CurveFamily.isPrestableCurveFamily_ofIsPullback`: the restricted family is
  prestable.
* `AlgebraicGeometry.CurveFamily.exists_affine_etale_charts_of_isPullback`: the charts.

## References

* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **A base change of a prestable family is prestable**, in the form of a cartesian square
presenting the base change (`AlgebraicGeometry.CurveFamily.ofIsPullback`). -/
theorem isPrestableCurveFamily_ofIsPullback {X : CurveFamily B hZ}
    (hX : IsPrestableCurveFamily B hZ X) {V : BigFppfOver B integerBase hZ} (t : V ⟶ X.base)
    {X₁ : AlgebraicSpaces B integerBase hZ} {p₁ : X₁ ⟶ X.total} {f₁ : X₁ ⟶ schemeSpace V}
    (h : IsPullback p₁ f₁ X.toBase (schemeSpaceMap t)) :
    IsPrestableCurveFamily B hZ (X.ofIsPullback B hZ t p₁ f₁ h) :=
  isPrestableCurveFamily_of_hom (X.homOfIsPullback B hZ t p₁ f₁ h) hX

/-- **Affine étale scheme charts of a base change of a prestable family.** Let `X` be a
prestable family of curves and `X₁ → V` its base change along `t : V ⟶ S`. There is a family of
cartesian squares `Zᵢ ⟶ X₁` over `φᵢ : Tᵢ ⟶ V`, with `Zᵢ, Tᵢ` schemes of the site, `Tᵢ` affine,
`φᵢ` étale and `Zᵢ ⟶ Tᵢ` at-worst-nodal of relative dimension one, whose members `Zᵢ ⟶ X₁`
form an étale covering of `X₁`. -/
theorem exists_affine_etale_charts_of_isPullback {X : CurveFamily B hZ}
    (hX : IsPrestableCurveFamily B hZ X) {V : BigFppfOver B integerBase hZ} (t : V ⟶ X.base)
    {X₁ : AlgebraicSpaces B integerBase hZ} {p₁ : X₁ ⟶ X.total} {f₁ : X₁ ⟶ schemeSpace V}
    (h : IsPullback p₁ f₁ X.toBase (schemeSpaceMap t)) :
    ∃ (I : Type u) (T Z : I → BigFppfOver B integerBase hZ) (φ : ∀ i, T i ⟶ V)
      (q : ∀ i, Z i ⟶ T i) (p : ∀ i, schemeSpace (Z i) ⟶ X₁),
      (∀ i, IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj (T i))) ∧
      (∀ i, Etale ((BigFppfOver.toScheme B integerBase hZ).map (φ i))) ∧
      (∀ i, IsPullback (p i) (schemeSpaceMap (q i)) f₁ (schemeSpaceMap (φ i))) ∧
      (∀ i, IsAtWorstNodalOfRelativeDimensionOne
        ((BigFppfOver.toScheme B integerBase hZ).map (q i))) ∧
      Space.IsEtaleCovering B integerBase hZ (fun i ↦ yoneda.obj (Z i)) (fun i ↦ (p i).hom) := by
  let 𝒯 := BigFppfOver.toScheme B integerBase hZ
  let G := X.ofIsPullback B hZ t p₁ f₁ h
  have hG : IsPrestableCurveFamily B hZ G := isPrestableCurveFamily_ofIsPullback hX t h
  choose T₀ Z₀ φ₀ q₀ p₀ hφ₀ hmem hsq₀ using C1590Private.hasEtaleLocalSchemeCharts B hZ G
  choose t₀ ht₀ using hmem
  choose A hA htA _ using fun u : 𝒯.obj V =>
    exists_isAffineOpen_mem_and_subset (X := 𝒯.obj (T₀ u)) (x := t₀ u) (U := ⊤) trivial
  have hAc : ∀ u, B.Contains (A u).toScheme := fun u => B.contains_of_mono (A u).ι (T₀ u).left.2
  let T : 𝒯.obj V → BigFppfOver B integerBase hZ := fun u =>
    BigFppfOver.siteObjectOver B integerBase hZ (T₀ u) (hAc u) (A u).ι
  let ι : ∀ u, T u ⟶ T₀ u := fun u =>
    BigFppfOver.siteMapOver B integerBase hZ (T₀ u) (hAc u) (A u).ι
  have hsq : ∀ u, IsPullback (schemeSpaceMap (pullback.fst (q₀ u) (ι u)) ≫ p₀ u)
      (schemeSpaceMap (pullback.snd (q₀ u) (ι u))) f₁ (schemeSpaceMap (ι u ≫ φ₀ u)) := by
    intro u
    have := (C1590Private.isPullback_schemeSpaceMap
      (IsPullback.of_hasPullback (q₀ u) (ι u))).paste_horiz (hsq₀ u)
    exact (congrArg (IsPullback (schemeSpaceMap (pullback.fst (q₀ u) (ι u)) ≫ p₀ u)
      (schemeSpaceMap (pullback.snd (q₀ u) (ι u))) f₁) (schemeSpaceMap_comp (ι u) (φ₀ u))).mpr this
  have hφ : ∀ u, Etale (𝒯.map (ι u ≫ φ₀ u)) := by
    intro u
    have : Etale (𝒯.map (φ₀ u)) := hφ₀ u
    rw [Functor.map_comp]
    show Etale ((A u).ι ≫ 𝒯.map (φ₀ u))
    infer_instance
  refine ⟨𝒯.obj V, T, fun u => pullback (q₀ u) (ι u), fun u => ι u ≫ φ₀ u,
    fun u => pullback.snd (q₀ u) (ι u), fun u => schemeSpaceMap (pullback.fst (q₀ u) (ι u)) ≫ p₀ u,
    fun u => (hA u : IsAffine (A u).toScheme), hφ, hsq, fun u => ?_, ?_⟩
  · exact (Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
      isAtWorstNodalOfRelativeDimensionOne_isEtaleLocalOnSourceAndTarget _).1
      ((Space.isAtWorstNodalOfRelativeDimensionOne_isStableUnderBaseChange B integerBase
        hZ).of_isPullback (hsq u) hG.1)
  · refine ⟨X₁.property, fun u => isAlgebraicSpace_yoneda B integerBase hZ _,
      fun u => Space.isEtale_of_isPullback B integerBase hZ _ _ _ _ (hsq u).flip
        (C1590Private.isEtale_schemeSpaceMap_of_etale _ (hφ u)), ?_⟩
    refine Set.eq_univ_of_forall fun x => ?_
    let b := Space.pointsMap B integerBase hZ X₁.obj f₁.hom x
    let u := Space.pointsToScheme B integerBase hZ V b
    let a := (Space.pointsEquivScheme B integerBase hZ (T u)).symm ⟨t₀ u, htA u⟩
    have ha : Space.pointsToScheme B integerBase hZ (T u) a = ⟨t₀ u, htA u⟩ :=
      (Space.pointsEquivScheme B integerBase hZ (T u)).apply_symm_apply _
    have hab : Space.pointsMap B integerBase hZ X₁.obj f₁.hom x =
        Space.pointsMap B integerBase hZ _ (schemeSpaceMap (ι u ≫ φ₀ u)).hom a := by
      apply (Space.pointsEquivScheme B integerBase hZ V).injective
      show u = Space.pointsToScheme B integerBase hZ V
        (Space.pointsMap B integerBase hZ _ (yoneda.map (ι u ≫ φ₀ u)) a)
      rw [Space.pointsToScheme_pointsMap_yoneda, ha]
      show u = 𝒯.map (φ₀ u) ((A u).ι ⟨t₀ u, htA u⟩)
      rw [Scheme.Opens.ι_apply]
      exact (ht₀ u).symm
    obtain ⟨w, hw, -⟩ := Space.exists_points_of_isPullback B integerBase hZ
      (AlgebraicSpaces.isPullback_hom B integerBase hZ (hsq u)) x a hab
    exact Set.mem_iUnion.mpr ⟨u, w, hw⟩

end CurveFamily

end AlgebraicGeometry

end
