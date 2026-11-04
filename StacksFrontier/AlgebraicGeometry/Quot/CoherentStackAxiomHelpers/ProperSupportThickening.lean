module

public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ModuleSupportProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupportEquality
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportClosedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic

/-!
# Proper support descends along a thickening of the base

Let `h : T' ⟶ T` be a morphism of the big fppf site whose underlying morphism of schemes is a
thickening, let `f : X ⟶ T` be a morphism of algebraic spaces locally of finite type, and let
`X' = X ×_T T'`.  A quasi-coherent `𝒪_X`-module `F` of finite type whose inverse image to `X'`
has support proper over `T'` has itself support proper over `T`.

The support of the inverse image is the inverse image of the support (Stacks 07TZ), and the base
change `X' ⟶ X` of the thickening is a closed immersion which is surjective on points.  So the
reduced induced closed subspace of `X'` on the support of the inverse image, followed by
`X' ⟶ X`, is a closed subspace of `X` with the support of `F` as its set of points; it is proper
over `T` because it is proper over `T'` and `T' ⟶ T` is a closed immersion.  Stacks 0CZC then
says that the support of `F` is proper over `T`.

## Main results

* `AlgebraicGeometry.Space.hasProperSupport_of_isPullback_of_isThickening`.

## References

* [Stacks Project, Tag 0CZC](https://stacks.math.columbia.edu/tag/0CZC)
* [Stacks Project, Tag 0CZD](https://stacks.math.columbia.edu/tag/0CZD)
* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Proper support descends along a thickening of the base.**  In a cartesian square of
algebraic spaces `X' ⟶ X` over the morphism `T' ⟶ T` represented by a thickening of schemes,
with `X ⟶ T` locally of finite type, a quasi-coherent module of finite type on `X` whose inverse
image to `X'` has support proper over `T'` has support proper over `T`. -/
theorem hasProperSupport_of_isPullback_of_isThickening
    {X' X : AlgebraicSpaces B S hS} {T' T : BigFppfOver B S hS}
    {g' : X' ⟶ X} {f' : X' ⟶ (schemeSpaceFunctor B S hS).obj T'}
    {f : X ⟶ (schemeSpaceFunctor B S hS).obj T} {h : T' ⟶ T}
    (sq : IsPullback g' f' f ((schemeSpaceFunctor B S hS).map h))
    (hh : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map h))
    (hf : IsLocallyOfFiniteType B S hS f.hom) (hf' : IsLocallyOfFiniteType B S hS f'.hom)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (hqc : F.IsQuasicoherentOnSite) (hft : SheafOfModules.IsFiniteTypeOnSite F)
    (hF' : HasProperSupport B S hS X'.2 ((schemeSpaceFunctor B S hS).obj T').2 f'.hom hf'
      ((SheafOfModules.toSheaf _).obj ((modulePullback B S hS g').obj F))) :
    HasProperSupport B S hS X.2 ((schemeSpaceFunctor B S hS).obj T).2 f.hom hf
      ((SheafOfModules.toSheaf _).obj F) := by
  classical
  obtain ⟨hcl', hproper'⟩ := hF'
  have hcl : IsClosed (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F)) :=
    let := hft; isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS X.1 X.2 F
  refine ⟨hcl, ?_⟩
  set T₀ := supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) with hT₀
  set T₁ := supportOfSheaf B S hS X'.1
    ((SheafOfModules.toSheaf _).obj ((modulePullback B S hS g').obj F)) with hT₁
  have hT₁eq : T₁ = pointsMap B S hS X'.1 g'.hom ⁻¹' T₀ :=
    supportOfSheaf_modulePullback_eq B S hS g' F hqc hft
  -- the base change of the thickening
  have sqp : IsPullback g'.hom f'.hom f.hom ((schemeSpaceFunctor B S hS).map h).hom :=
    AlgebraicSpaces.isPullback_hom B S hS sq
  have hci_h : IsClosedImmersion B S hS ((schemeSpaceFunctor B S hS).map h).hom :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@AlgebraicGeometry.IsClosedImmersion.{u}) h).2 hh.1
  have hsurj_h : IsSurjective B S hS ((schemeSpaceFunctor B S hS).map h).hom :=
    isSurjective_of_presheafSurjective B S hS _
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
        (@AlgebraicGeometry.Surjective.{u}) h).2 ⟨hh.2⟩)
  have hci_g' : IsClosedImmersion B S hS g'.hom :=
    (isClosedImmersion_isStableUnderBaseChange B S hS).of_isPullback sqp.flip hci_h
  have hsurj_g' : IsSurjective B S hS g'.hom :=
    isSurjective_of_isPullback B S hS sq.flip hsurj_h
  -- the reduced induced subspace on the support of the inverse image, pushed into `X`
  set R' := reducedClosedSubspace B S hS X'.1 X'.2 T₁ hcl' with hR'
  have hR'cl : IsClosedSubspace B S hS R' :=
    isClosedSubspace_reducedClosedSubspace_of_closedImmersionDescent B S hS X'.1 X'.2 T₁ hcl'
      (isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion B S hS)
  let j : R'.toFunctor ⟶ X.1 := R'.ι ≫ g'.hom
  have hcij : IsClosedImmersion B S hS j := isClosedImmersion_comp B S hS _ _ hR'cl.2 hci_g'
  have hPmono : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) ≤
      MorphismProperty.monomorphisms (BigFppfOver B S hS) := by
    intro A A' k hk
    have : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map k) := hk
    refine ⟨fun {W} k₁ k₂ hkk => ?_⟩
    refine Functor.map_injective (BigFppfOver.toScheme B S hS) ?_
    refine (cancel_mono ((BigFppfOver.toScheme B S hS).map k)).1 ?_
    simpa only [Functor.map_comp] using congrArg (fun q => (BigFppfOver.toScheme B S hS).map q) hkk
  have : Mono j :=
    MorphismProperty.presheaf_monomorphisms_le_monomorphisms _
      (MorphismProperty.relative_monotone hPmono _ hcij)
  let e : R'.toFunctor ≅ (Subfunctor.range j).toFunctor := asIso (Subfunctor.toRange j)
  have he : e.inv ≫ j = (Subfunctor.range j).ι := by
    calc e.inv ≫ j = e.inv ≫ (Subfunctor.toRange j ≫ (Subfunctor.range j).ι) :=
          congrArg (fun k => e.inv ≫ k) (Subfunctor.toRange_ι j).symm
      _ = _ := by simp [e]
  have hR'alg : IsAlgebraicSpace B S hS R'.toFunctor :=
    isAlgebraicSpace_reducedClosedSubspace B S hS X'.1 X'.2 T₁ hcl'
  have hZalg : IsAlgebraicSpace B S hS (Subfunctor.range j).toFunctor :=
    isAlgebraicSpace_of_iso B S hS e hR'alg
  have hZ : IsClosedSubspace B S hS (Subfunctor.range j) := by
    refine ⟨hZalg, ?_⟩
    have h := MorphismProperty.RespectsIso.precomp
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) e.inv j hcij
    exact he ▸ h
  have hR'T : Set.range (pointsMap B S hS R'.toFunctor R'.ι) = T₁ :=
    range_pointsMap_ι_reducedClosedSubspace B S hS X'.1 X'.2 T₁ hcl'
  have hZT : Set.range (pointsMap B S hS (Subfunctor.range j).toFunctor
      (Subfunctor.range j).ι) = T₀ := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      rw [← he, pointsMap_comp_apply, pointsMap_comp_apply]
      have hmem : pointsMap B S hS R'.toFunctor R'.ι
          (pointsMap B S hS (Subfunctor.range j).toFunctor e.inv z) ∈ T₁ := hR'T.le ⟨_, rfl⟩
      rwa [hT₁eq] at hmem
    · intro hx
      obtain ⟨y, rfl⟩ := hsurj_g' x
      obtain ⟨r, rfl⟩ := hR'T.ge (by rwa [hT₁eq])
      refine ⟨pointsMap B S hS R'.toFunctor e.hom r, ?_⟩
      rw [← he, pointsMap_comp_apply, pointsMap_comp_apply, ← pointsMap_comp_apply
        B S hS e.hom e.inv, e.hom_inv_id, pointsMap_id]
      rfl
  have hproperZ : IsProper B S hS ((Subfunctor.range j).ι ≫ f.hom) := by
    have hcomm : j ≫ f.hom = (R'.ι ≫ f'.hom) ≫ ((schemeSpaceFunctor B S hS).map h).hom := by
      show (R'.ι ≫ g'.hom) ≫ f.hom = _
      rw [Category.assoc, sqp.w, Category.assoc]
    have hjf : IsProper B S hS (j ≫ f.hom) := by
      rw [hcomm]
      exact isProper_comp B S hS hR'alg ((schemeSpaceFunctor B S hS).obj T').2
        ((schemeSpaceFunctor B S hS).obj T).2 _ _ hproper'
        (isProper_of_isClosedImmersion B S hS ((schemeSpaceFunctor B S hS).obj T').2
          ((schemeSpaceFunctor B S hS).obj T).2 _ hci_h)
    rw [← he, Category.assoc]
    exact isProper_comp B S hS hZalg hR'alg ((schemeSpaceFunctor B S hS).obj T).2 _ _
      (isProper_of_isIso B S hS e.inv) hjf
  exact (isProper_reducedClosedSubspace_iff_exists B S hS X.2
    ((schemeSpaceFunctor B S hS).obj T).2 f.hom hf T₀ hcl).2
    ⟨Subfunctor.range j, hZ, hZT, hproperZ⟩

end AlgebraicGeometry.Space
