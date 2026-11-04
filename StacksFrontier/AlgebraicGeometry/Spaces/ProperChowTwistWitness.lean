module

public import StacksFrontier.AlgebraicGeometry.QuasiProjectiveCompactification.Projective
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.AffineSiteObjectBase
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveSpaceImmersionTwistSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveSpaceImmersionTwistVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.TotallyAcyclicPushforwardAcyclicity

/-!
# The Chow twist of a closed subspace of a space proper over a Noetherian affine scheme

Let `T` be a Noetherian affine scheme of the big fppf site of `S`, `f' : X' ⟶ h_T` a proper
morphism of algebraic spaces and `Z ⊆ X'` a closed subspace. There are a scheme `Z'` of the site
with a proper surjection `p : h_{Z'} ⟶ Z` and a coherent invertible module `𝓜` on `Z'` with
`R^j q_* 𝓜^a = 0` for `j > 0`, where `q : h_{Z'} ⟶ Z ⟶ X'`, such that `𝒢 = q_* 𝓜^a` is coherent,
has coherent higher direct images along `f'`, and has support containing the image of `q`.

## Main results

* `AlgebraicGeometry.Space.exists_chowTwist_hasCoherentHigherDirectImages`: the existence of
  `Z'`, `p` and `𝓜`.

## References

* [Stacks Project, Tag 08AR](https://stacks.math.columbia.edu/tag/08AR)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
* [Stacks Project, Tag 08AQ](https://stacks.math.columbia.edu/tag/08AQ)
* [Stacks Project, Tag 02O4](https://stacks.math.columbia.edu/tag/02O4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Ample

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Let `T` be a Noetherian affine scheme of the site, `f' : X' ⟶ h_T` proper and `Z ⊆ X'` a
closed subspace. There are an object `Z'` of the site, a
proper surjection `p : h_{Z'} ⟶ Z`, a coherent invertible module `𝓜` on the scheme underlying
`Z'` with `R^j q_* 𝓜^a = 0` for `j > 0`, where `q = p ≫ (Z ⟶ X')`, such that `𝒢 = q_* 𝓜^a` is
coherent, has coherent higher direct images along `f'`, and has support containing the image
of `q`. -/
theorem exists_chowTwist_hasCoherentHigherDirectImages (T : BigFppfOver B S hS)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hTN : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T))
    (X' : AlgebraicSpaces B S hS)
    (f' : X' ⟶ ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩) (hf' : IsProper B S hS f'.hom)
    {Z : Subfunctor X'.1} (hZ : IsClosedSubspace B S hS Z) :
    ∃ (Z' : BigFppfOver B S hS) (p : yoneda.obj Z' ⟶ (closedSubfunctorSpace B S hS hZ).1)
      (M : ((BigFppfOver.toScheme B S hS).obj Z').Modules),
      IsProper B S hS p ∧ IsSurjective B S hS p ∧ M.IsCoherent ∧
      Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj Z') M ∧
      (have := hasInjectiveResolutions_modules B S hS (yoneda.obj Z')
          (isAlgebraicSpace_yoneda B S hS Z')
        have := modulePushforward_additive B S hS
          (ObjectProperty.homMk p ≫ closedSubfunctorι B S hS hZ :
            (⟨yoneda.obj Z', isAlgebraicSpace_yoneda B S hS Z'⟩ : AlgebraicSpaces B S hS) ⟶ X')
        ∀ j, 0 < j → IsZero (((modulePushforward B S hS
          (ObjectProperty.homMk p ≫ closedSubfunctorι B S hS hZ :
            (⟨yoneda.obj Z', isAlgebraicSpace_yoneda B S hS Z'⟩ : AlgebraicSpaces B S hS) ⟶
              X')).rightDerived j).obj
          ((representedAssociatedModule B S hS Z' (isAlgebraicSpace_yoneda B S hS Z')).obj M))) ∧
      IsCoherent B S hS X'.1 X'.2 ((modulePushforward B S hS
          (ObjectProperty.homMk p ≫ closedSubfunctorι B S hS hZ :
            (⟨yoneda.obj Z', isAlgebraicSpace_yoneda B S hS Z'⟩ : AlgebraicSpaces B S hS) ⟶ X')).obj
          ((representedAssociatedModule B S hS Z' (isAlgebraicSpace_yoneda B S hS Z')).obj M)) ∧
      HasCoherentHigherDirectImages B S hS f' ((modulePushforward B S hS
          (ObjectProperty.homMk p ≫ closedSubfunctorι B S hS hZ :
            (⟨yoneda.obj Z', isAlgebraicSpace_yoneda B S hS Z'⟩ : AlgebraicSpaces B S hS) ⟶ X')).obj
          ((representedAssociatedModule B S hS Z' (isAlgebraicSpace_yoneda B S hS Z')).obj M)) ∧
      Set.range (pointsMap B S hS (yoneda.obj Z')
          (ObjectProperty.homMk p ≫ closedSubfunctorι B S hS hZ :
            (⟨yoneda.obj Z', isAlgebraicSpace_yoneda B S hS Z'⟩ : AlgebraicSpaces B S hS) ⟶
              X').hom) ⊆
        supportOfSheaf B S hS X'.1 ((SheafOfModules.toSheaf _).obj ((modulePushforward B S hS
          (ObjectProperty.homMk p ≫ closedSubfunctorι B S hS hZ :
            (⟨yoneda.obj Z', isAlgebraicSpace_yoneda B S hS Z'⟩ : AlgebraicSpaces B S hS) ⟶
              X')).obj
          ((representedAssociatedModule B S hS Z' (isAlgebraicSpace_yoneda B S hS Z')).obj
            M))) := by
  let TS := BigFppfOver.toScheme B S hS
  have := hT
  have := hTN
  let Zs := closedSubfunctorSpace B S hS hZ
  let ι := closedSubfunctorι B S hS hZ
  have hι : IsProper B S hS ι.hom :=
    isProper_of_isClosedImmersion B S hS Zs.2 X'.2 _ hZ.2
  have hg : IsProper B S hS (ι.hom ≫ f'.hom) :=
    isProper_comp' B S hS ι.hom f'.hom X'.2 (isAlgebraicSpace_yoneda B S hS T) hι hf'
  obtain ⟨Z', ψ, p, hp, hps, hw, hψ, hHproj⟩ :=
    exists_chowSchemeCover_of_isProper_over_affine B S hS T hT Zs.2 (ι.hom ≫ f'.hom) hg
  let q : (⟨yoneda.obj Z', isAlgebraicSpace_yoneda B S hS Z'⟩ : AlgebraicSpaces B S hS) ⟶ X' :=
    ObjectProperty.homMk p ≫ ι
  have hq : q.hom ≫ f'.hom = yoneda.map ψ := by
    rw [← hw]; rfl
  have hqp : IsProper B S hS q.hom :=
    isProper_comp' B S hS p ι.hom Zs.2 X'.2 hp hι
  obtain ⟨m, i, hi, hiψ⟩ := hHproj
  obtain ⟨D, k, hD, hk, -⟩ := exists_projectiveSpaceImmersion_of_isClosedImmersion B S hS T f'
    hf'.1 ψ q hq m i hi hiψ
  have : IsLocallyNoetherian (TS.obj Z') := LocallyOfFiniteType.isLocallyNoetherian (TS.map ψ)
  have hZt := BigFppfSite.contains_terminal B
  have hTY : HasEtaleLocalProperty B S hS (yoneda.obj T)
      (fun V : Scheme.{u} ↦ IsLocallyNoetherian V) :=
    hasEtaleLocalProperty_of_representable B S hS _ _ T (Iso.refl _) hTN
  have hTnoeth : IsNoetherian B S hS hZt (yoneda.obj T) :=
    ⟨IsAffineSpace.isQuasiCompactSpace ⟨T, hT, ⟨Iso.refl _⟩⟩,
      isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS _ hZt
        ⟨T, inferInstance, ⟨Functor.representableByEquiv.symm (Iso.refl _)⟩⟩, hTY⟩
  have hX'noeth : IsNoetherian B S hS hZt X'.1 :=
    isNoetherian_of_isFinitePresentation B S hS hZt f'.hom X'.2 (isAlgebraicSpace_yoneda B S hS T)
      (isFinitePresentation_of_isFiniteType B S hS X'.2 (isAlgebraicSpace_yoneda B S hS T) f'.hom
        hTY hf'.2.1 (isQuasiSeparated_of_isSeparated B S hS hf'.1)) hTnoeth
  have hXqc : IsQuasiCompactSpace B S hS X'.1 := hX'noeth.1
  have hXN : HasEtaleLocalProperty B S hS X'.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V) :=
    hX'noeth.2.2
  have hD' : D.hom = ObjectProperty.homMk p ≫ closedSubfunctorι B S hS hZ := hD
  obtain ⟨d₀', hd₀⟩ := ProjectiveSpaceImmersion.exists_isZero_rightDerived_twistPow D k hk hXqc hXN
  obtain ⟨d₁, hd₁⟩ :=
    ProjectiveSpaceImmersion.exists_range_subset_supportOfSheaf_twistPow D k hk hXqc
  let d₀ := max d₀' d₁
  have hDqc : IsQuasiCompact B S hS D.hom.hom := hD ▸ hqp.2.1.2
  have hDqs : IsQuasiSeparated B S hS D.hom.hom :=
    hD ▸ isQuasiSeparated_of_isSeparated B S hS hqp.1
  have hcoh :=
    ProjectiveSpaceImmersion.isCoherent_modulePushforward_twistPow D k hk hXN hDqc hDqs d₀
  let M := ProjectiveSpaceImmersion.twistPow k d₀
  have hpowZ : AlgebraicGeometry.SheafOfModules.IsInvertible (TS.obj Z').presheaf
      (TS.obj Z').ringCatSheaf.2
      (Stacks.Ample.tensorPowModule (TS.obj Z') (ProjectiveSpaceImmersion.schemeTwist k)
        (d₀ : ℤ)) :=
    Stacks.Ample.isInvertibleModule_tensorPowModule (TS.obj Z')
      (ProjectiveSpaceImmersion.schemeTwist k) (d₀ : ℤ)
  have hMcoh : M.IsCoherent :=
    AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible (TS.obj Z')
      (unitModule (TS.obj Z'))
      (Stacks.Ample.tensorPowModule (TS.obj Z') (ProjectiveSpaceImmersion.schemeTwist k) (d₀ : ℤ))
  have hMinv : Stacks.Ample.IsInvertibleModule (TS.obj Z') M :=
    Stacks.AmplePullbackPart1.isInvertibleModule_tensorModules (TS.obj Z') (unitModule (TS.obj Z'))
      (Stacks.Ample.tensorPowModule (TS.obj Z') (ProjectiveSpaceImmersion.schemeTwist k) (d₀ : ℤ))
  refine ⟨Z', p, M, hp, hps, hMcoh, hMinv, ?_, ?_, ?_, ?_⟩ <;> rw [← hD']
  · exact hd₀ d₀ (le_max_left _ _)
  · exact hcoh
  · have hc := hasCoherentHigherDirectImages_representedSpaceMap B S hS ψ
      (⟨m, i, hi, hiψ⟩ : IsProjectiveMorphism (TS.map ψ)) M hMcoh
    have heq : D.hom ≫ f' = representedSpaceMap B S hS ψ :=
      ObjectProperty.hom_ext _ (by rw [hD]; exact hq)
    rw [← heq] at hc
    intro n
    have :=
      hasInjectiveResolutions_modules B S hS (yoneda.obj Z') (isAlgebraicSpace_yoneda B S hS Z')
    exact isCoherent_of_iso B S hS _ (rightDerivedModulePushforwardCompIsoOfAcyclic B S hS D.hom f'
      ((representedAssociatedModule B S hS Z' (isAlgebraicSpace_yoneda B S hS Z')).obj M)
      (hd₀ d₀ (le_max_left _ _)) n) (hc n)
  · exact hd₁ d₀ (le_max_right _ _)

end AlgebraicGeometry.Space

end
