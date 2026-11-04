module

public import StacksFrontier.AlgebraicGeometry.Spaces.SiteChangeThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeModulesFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeModulesCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackIsoProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleCompFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FlatImageSystem
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesPlusStrictlyFull
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorPresheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.StalkBaseChangeNormalCompletion

/-!
# Properties carried across the change of site of Stacks 04SG

Let `h : Spec R ⟶ S` be a morphism of a big fppf site, `X` an algebraic space over `S` with a
morphism `π : X ⟶ Spec R`, `X'` the algebraic space over `Spec R` it is
(`AlgebraicGeometry.Space.siteChangeSpace`), `f' : X' ⟶ Spec R` its structure morphism and
`Ψ : Mod(𝒪_X) ⥤ Mod(𝒪_{X'})` the equivalence of `AlgebraicGeometry.Space.siteChangeModules`.
This file proves that the properties of morphisms and modules entering Stacks 08B9, 08BE and
08VP are the same on both sides:

* `f'` is locally of finite type, of finite type, separated, exactly when (respectively, as soon
  as) `π` is (`AlgebraicGeometry.Space.isLocallyOfFiniteType_siteChangeStructure_iff`,
  `AlgebraicGeometry.Space.isFiniteType_siteChangeStructure_iff`,
  `AlgebraicGeometry.Space.isSeparated_siteChangeStructure`);
* `X'` is locally Noetherian when `X` is (`AlgebraicGeometry.Space.fact_siteChangeSpace`);
* `Ψ M` is coherent exactly when `M` is
  (`AlgebraicGeometry.Space.isCoherent_siteChangeModules_iff`);
* `Ψ M` has support proper over `Spec R` exactly when `M` does
  (`AlgebraicGeometry.Space.hasProperSupport_siteChangeModules_iff`), Stacks 0CZD;
* `M` is flat over `Spec R` as soon as `Ψ M` is
  (`AlgebraicGeometry.Space.isFlatOver_of_isFlatOver_siteChangeModules`), Stacks 05VV.

## References

* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 0CZD](https://stacks.math.columbia.edu/tag/0CZD)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [-instance] CategoryTheory.catToReflQuiver

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {R : Type u} [CommRing R]
  {hR : B.Contains (Spec (.of R))} {h : B.obj hR ⟶ B.obj hS}
  (X : AlgebraicSpaces B S hS) (π : X ⟶ schemeSpace (Over.mk h))

/-! ### The structure morphism -/

/-- The structure morphism `Λ_h (Spec R) ⟶ Spec R` of the lower-shriek extension of the terminal
space over `Spec R`, an isomorphism. -/
abbrev siteChangeTargetIso :
    (OverShriek.relocalizePresheafFunctor h).obj (schemeSpace (baseObject R B hR)).1 ⟶
      (schemeSpace (Over.mk h)).1 :=
  OverShriek.relocalizeToYoneda h (schemeSpace (baseObject R B hR)).1

instance isIso_siteChangeTargetIso : IsIso (siteChangeTargetIso (R := R) (hR := hR) (h := h)) :=
  isIso_relocalizeToYoneda_yonedaId B (Spec (.of R)) S hR hS h

/-- **The structure morphism of `X'`, extended back to `S`, is `π` read through `Λ_h X' ≅ X`.** -/
theorem relocalize_siteChangeStructure_comp :
    (OverShriek.relocalizePresheafFunctor h).map (siteChangeStructure X π).hom ≫
        siteChangeTargetIso =
      ((siteChangeIso B X π).hom ≫ π).hom := by
  rw [siteChangeIso_hom_comp]
  exact relocalizeToYoneda_naturality B (Spec (.of R)) S hR hS h _

/-- **`f'` is locally of finite type exactly when `π` is.** -/
theorem isLocallyOfFiniteType_siteChangeStructure_iff :
    IsLocallyOfFiniteType B (Spec (.of R)) hR (siteChangeStructure X π).hom ↔
      IsLocallyOfFiniteType B S hS π.hom := by
  have := isLocallyOfFiniteType_respectsIso B S hS
  rw [← isLocallyOfFiniteType_relocalize_iff B (Spec (.of R)) hR S hS h,
    ← MorphismProperty.cancel_right_of_respectsIso
      (fun ⦃F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (f : F ⟶ G) => IsLocallyOfFiniteType B S hS f)
      _ siteChangeTargetIso, relocalize_siteChangeStructure_comp]
  exact MorphismProperty.cancel_left_of_respectsIso
    (fun ⦃F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (f : F ⟶ G) => IsLocallyOfFiniteType B S hS f)
    (siteChangeIso B X π).hom.hom π.hom

/-- **`f'` is of finite type exactly when `π` is.** -/
theorem isFiniteType_siteChangeStructure_iff :
    IsFiniteType B (Spec (.of R)) hR (siteChangeStructure X π).hom ↔
      IsFiniteType B S hS π.hom := by
  rw [← isFiniteType_relocalize_iff B (Spec (.of R)) hR S hS h,
    ← isFiniteType_comp_isIso_iff B S hS _ siteChangeTargetIso, relocalize_siteChangeStructure_comp]
  exact isFiniteType_isIso_comp_iff B S hS (siteChangeIso B X π).hom.hom π.hom

/-- **`f'` is separated as soon as `π` is.** -/
theorem isSeparated_siteChangeStructure (hπ : IsSeparated B S hS π.hom) :
    IsSeparated B (Spec (.of R)) hR (siteChangeStructure X π).hom := by
  refine isSeparated_of_relocalizeMap B (Spec (.of R)) S hR hS h _ ?_
  rw [← isSeparated_comp_isIso_iff B S hS _ siteChangeTargetIso,
    relocalize_siteChangeStructure_comp]
  exact (isSeparated_isIso_comp_iff B S hS (siteChangeIso B X π).hom.hom π.hom).2 hπ

/-- `Λ_h X'` is locally Noetherian when `X` is, since `Λ_h X' ≅ X`. -/
private theorem hasEtaleLocalProperty_relocalizeSpace_siteChangeSpace
    (hX : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V)) :
    HasEtaleLocalProperty B S hS (relocalizeSpace B hR hS h (siteChangeSpace B X π)).1
      (fun V : Scheme.{u} => IsLocallyNoetherian V) :=
  hasEtaleLocalProperty_of_iso B S hS _ ((ObjectProperty.ι _).mapIso (siteChangeIso B X π).symm) hX

/-- **`X'` is locally Noetherian when `X` is.** -/
theorem fact_siteChangeSpace
    [hX : Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))] :
    Fact (HasEtaleLocalProperty B (Spec (.of R)) hR (siteChangeSpace B X π).1
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
  ⟨hasEtaleLocalProperty_of_relocalize B (Spec (.of R)) S hR hS h _ (siteChangeSpace B X π).2
    (hasEtaleLocalProperty_relocalizeSpace_siteChangeSpace X π hX.out)⟩

/-- **`Λ_h X'` is locally Noetherian when `X` is.** -/
theorem fact_relocalizeSpace_siteChangeSpace
    [hX : Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))] :
    Fact (HasEtaleLocalProperty B S hS (relocalizeSpace B hR hS h
      (siteChangeSpace B X π)).1 (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
  ⟨hasEtaleLocalProperty_relocalizeSpace_siteChangeSpace X π hX.out⟩

/-! ### Modules -/

/-- `Ψ` is the inverse image along `Λ_h X' ≅ X` followed by restriction to `X'`. -/
def siteChangeModulesIso :
    siteChangeModules B X π ≅ modulePullback B S hS (siteChangeIso B X π).hom ⋙
      (relocalizeModulesEquivalence B hR hS h (siteChangeSpace B X π).1
        (siteChangeSpace B X π).2).inverse :=
  Functor.isoWhiskerRight (modulePushforwardInvIsoModulePullback B S hS (siteChangeIso B X π)) _

/-- **`Ψ M` is coherent exactly when `M` is.** -/
theorem isCoherent_siteChangeModules_iff
    [hX : Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (M : Modules.{u, u} B S hS X.1 X.2) :
    IsCoherent B (Spec (.of R)) hR (siteChangeSpace B X π).1 (siteChangeSpace B X π).2
        ((siteChangeModules B X π).obj M) ↔ IsCoherent B S hS X.1 X.2 M := by
  have := fact_relocalizeSpace_siteChangeSpace X π
  rw [← isCoherent_modulePullback_iso_iff (siteChangeIso B X π) M,
    ← isCoherent_relocalizeModulesEquivalence_inverse_iff B hR hS h _
      (siteChangeSpace B X π).2]
  exact ⟨isCoherent_of_iso B (Spec (.of R)) hR (siteChangeSpace B X π).2
      ((siteChangeModulesIso X π).app M),
    isCoherent_of_iso B (Spec (.of R)) hR (siteChangeSpace B X π).2
      ((siteChangeModulesIso X π).app M).symm⟩

/-- **`Ψ M` has support proper over `Spec R` exactly when `M` has support proper over `Spec R`
along `π`** (Stacks 0CZD). -/
theorem hasProperSupport_siteChangeModules_iff (hπ : IsLocallyOfFiniteType B S hS π.hom)
    (M : Modules.{u, u} B S hS X.1 X.2) (hqc : M.IsQuasicoherentOnSite)
    (hft : SheafOfModules.IsFiniteTypeOnSite M) :
    HasProperSupport B (Spec (.of R)) hR (siteChangeSpace B X π).2
        (schemeSpace (baseObject R B hR)).2 (siteChangeStructure X π).hom
        ((isLocallyOfFiniteType_siteChangeStructure_iff X π).2 hπ)
        ((SheafOfModules.toSheaf _).obj ((siteChangeModules B X π).obj M)) ↔
      HasProperSupport B S hS X.2 (schemeSpace (Over.mk h)).2 π.hom hπ
        ((SheafOfModules.toSheaf _).obj M) := by
  let e := siteChangeIso B X π
  let hf' := (isLocallyOfFiniteType_siteChangeStructure_iff X π).2 hπ
  have hΛ := (isLocallyOfFiniteType_relocalize_iff B (Spec (.of R)) hR S hS h
    (siteChangeStructure X π).hom).2 hf'
  have hg₁ : IsLocallyOfFiniteType B S hS (e.hom ≫ π).hom := by
    rw [← relocalize_siteChangeStructure_comp]
    exact isLocallyOfFiniteType_comp' B S hS _ _ (relocalizeSpace B hR hS h
      (schemeSpace (baseObject R B hR))).2 (schemeSpace (Over.mk h)).2 hΛ
      (isLocallyOfFiniteType_of_isClosedImmersion B S hS _
        (isClosedImmersion_of_isIso B S hS siteChangeTargetIso))
  have h1 : HasProperSupport B (Spec (.of R)) hR (siteChangeSpace B X π).2
        (schemeSpace (baseObject R B hR)).2 (siteChangeStructure X π).hom hf'
        ((SheafOfModules.toSheaf _).obj ((siteChangeModules B X π).obj M)) ↔
      HasProperSupport B (Spec (.of R)) hR (siteChangeSpace B X π).2
        (schemeSpace (baseObject R B hR)).2 (siteChangeStructure X π).hom hf'
        ((SheafOfModules.toSheaf _).obj ((relocalizeModulesEquivalence B hR hS h
          (siteChangeSpace B X π).1 (siteChangeSpace B X π).2).inverse.obj
            ((modulePullback B S hS e.hom).obj M))) :=
    ⟨hasProperSupport_of_iso _ _ hf' ((siteChangeModulesIso X π).app M),
      hasProperSupport_of_iso _ _ hf' ((siteChangeModulesIso X π).app M).symm⟩
  rw [h1, hasProperSupport_relocalizeModulesEquivalence_inverse_iff B hR hS h
    (siteChangeSpace B X π).2 (schemeSpace (baseObject R B hR)).2 (siteChangeStructure X π).hom
    hf',
    ← hasProperSupport_comp_isIso_iff B S hS _ _ (schemeSpace (Over.mk h)).2 _
      siteChangeTargetIso _ (by rw [relocalize_siteChangeStructure_comp]; exact hg₁),
    hasProperSupport_congr_hom B S hS _ _ (relocalize_siteChangeStructure_comp X π) _ hg₁]
  exact hasProperSupport_modulePullback_iso_iff e π hπ hg₁ M hqc hft

/-- **`M` is flat over `Spec R` along `π` as soon as `Ψ M` is flat over `Spec R`** (Stacks
05VV). -/
theorem isFlatOver_of_isFlatOver_siteChangeModules (M : Modules.{u, u} B S hS X.1 X.2)
    (hqc : M.IsQuasicoherentOnSite)
    (hM : IsFlatOver B (Spec (.of R)) hR (siteChangeSpace B X π).2 (siteChangeStructure X π).hom
      ((siteChangeModules B X π).obj M)) :
    IsFlatOver B S hS X.2 π.hom M := by
  let e := siteChangeIso B X π
  let N := (modulePullback B S hS e.hom).obj M
  have hNq : N.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS e.hom M hqc
  have : ((modulePullback B S hS e.inv).obj N).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS e.inv N hNq
  have := hqc
  have h1 := IsFlatOver.of_iso B (Spec (.of R)) hR (siteChangeSpace B X π).2
    ((siteChangeModulesIso X π).app M) hM
  have h2 := (isFlatOver_relocalizeModulesEquivalence_inverse_iff B hR hS h
    (siteChangeSpace B X π).2 (schemeSpace (baseObject R B hR)).2
    (siteChangeStructure X π).hom N).1 h1
  let fΛ : relocalizeSpace B hR hS h (siteChangeSpace B X π) ⟶
      relocalizeSpace B hR hS h (schemeSpace (baseObject R B hR)) :=
    ObjectProperty.homMk
      ((OverShriek.relocalizePresheafFunctor h).map (siteChangeStructure X π).hom)
  let gΛ : relocalizeSpace B hR hS h (schemeSpace (baseObject R B hR)) ⟶
      schemeSpace (Over.mk h) := ObjectProperty.homMk siteChangeTargetIso
  have h3 := isFlatOver_comp_of_isFlat B S hS fΛ gΛ N h2 (isFlat_of_isIso siteChangeTargetIso
    (schemeSpace (Over.mk h)).2)
  have hfg : fΛ ≫ gΛ = e.hom ≫ π :=
    ObjectProperty.hom_ext _ (relocalize_siteChangeStructure_comp X π)
  rw [hfg] at h3
  have hpb : IsPullback e.inv π (e.hom ≫ π) (𝟙 _) := IsPullback.of_horiz_isIso ⟨by simp⟩
  have h4 := isFlatOver_modulePullback B S hS hpb N h3
  exact IsFlatOver.of_iso B S hS X.2
    (((modulePushforwardCoherence B S hS).modulePullbackEquivalence e).unitIso.app M).symm h4

end AlgebraicGeometry.Space

end
