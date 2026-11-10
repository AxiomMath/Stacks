module

public import StacksFrontier.AlgebraicGeometry.Quot.EtaleLocallyProjectiveCurvesAmpleFibre
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilySmoothLocallyPolarizedOf

/-!
# Families of curves are étale locally H-projective schemes (Stacks 0E6F)

Let `X ⟶ S` be a family of curves. Then there is an étale covering `{S_i ⟶ S}` such that each
`X_i = X ×_S S_i` is a scheme, and even H-projective over `S_i`.

## Main results

* `AlgebraicGeometry.CurveFamily.exists_isRelativelyAmple_chart_of_isAmple_fibre_of_isAffine`: an
  étale chart through `s` carrying a relatively ample invertible module on the base change, from a
  module on an étale base change which is ample on a fibre.
* `AlgebraicGeometry.CurveFamily.isSmoothLocallyPolarized_of_curveFamily`: every family of curves
  is smooth locally polarized.
* `AlgebraicGeometry.CurveFamily.exists_etale_isPullback_isProjectiveMorphism`: Stacks 0E6F
  pointwise, for finitely many families over one base, with one étale neighbourhood for all.
* `AlgebraicGeometry.CurveFamily.exists_etaleCovering_isPullback_isProjectiveMorphism`:
  **Stacks 0E6F**.

## Implementation notes

"`X ×_S S_i` is a scheme" is a cartesian square of algebraic spaces whose corner is the algebraic
space `schemeSpace Z` of a scheme `Z` of the site, with `Z ⟶ S_i` a morphism of the site, as in
`StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesEtaleLocallyProjective`. H-projectivity is
`AlgebraicGeometry.IsProjectiveMorphism` of Stacks 01W8. The étale covering is a family of étale
morphisms of the site whose images cover the base.

## References

* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
* [Stacks Project, Tag 0DQ0](https://stacks.math.columbia.edu/tag/0DQ0)
* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
* [Stacks Project, Tag 0B5Y](https://stacks.math.columbia.edu/tag/0B5Y)
* [Stacks Project, Tag 083B](https://stacks.math.columbia.edu/tag/083B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- The base change of an algebraic space `X` over a scheme `S` of the site along `T ⟶ S` exists,
as a cartesian square of algebraic spaces. -/
private theorem exists_isPullback_schemeSpaceMap {X : AlgebraicSpaces B integerBase hZ}
    {S T : BigFppfOver B integerBase hZ} (f : X ⟶ schemeSpace S) (g : T ⟶ S) :
    ∃ (X' : AlgebraicSpaces B integerBase hZ) (p : X' ⟶ X) (q : X' ⟶ schemeSpace T),
      IsPullback p q f (schemeSpaceMap g) := by
  let X' : AlgebraicSpaces B integerBase hZ :=
    ⟨pullback f.hom (yoneda.map g), isAlgebraicSpace_pullback B integerBase hZ _ _ X.2
      (isAlgebraicSpace_yoneda _ _ _ _) (isAlgebraicSpace_yoneda _ _ _ _)⟩
  exact ⟨X', ObjectProperty.homMk (pullback.fst _ _), ObjectProperty.homMk (pullback.snd _ _),
    Space.isPullback_homMk B integerBase hZ X.2 (isAlgebraicSpace_yoneda _ _ _ _)
      (isAlgebraicSpace_yoneda _ _ _ _) X'.2 (IsPullback.of_hasPullback _ _)⟩

/-- **A relatively ample chart from a module ample on a fibre after an étale base change.** Let
`X ⟶ S` be a family of curves, `φ : U ⟶ S` an étale morphism of the site, `X_U` a base change of
`X` along `φ`, `L` an invertible module on `X_U`, and `u ∈ U`. Suppose that the reading of `L` on
a scheme presentation `V` of the base change of `X_U` along a morphism `r : F ⟶ U` from a
nonempty affine scheme all of whose points map to `u` is ample. Then there are a smooth (indeed
étale) `π : T' ⟶ S` of the site through the image of `u`, a base change `X_{T'}` of `X` along
`π`, and an invertible module on `X_{T'}` ample relative to `X_{T'} ⟶ T'` (Stacks 0D31). -/
theorem exists_isRelativelyAmple_chart_of_isAmple_fibre_of_isAffine (X : CurveFamily B hZ)
    {U V F : BigFppfOver B integerBase hZ}
    (φ : U ⟶ X.base) (hφ : Etale ((𝒯).map φ)) (u : (𝒯).obj U)
    {XU : AlgebraicSpaces B integerBase hZ} (qU : XU ⟶ X.total) (fU : XU ⟶ schemeSpace U)
    (sqU : IsPullback qU fU X.toBase (schemeSpaceMap φ))
    (L : Space.Modules.{u, u} B integerBase hZ XU.1 XU.2)
    (hL : Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase hZ XU.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase hZ XU.1 XU.2).O)).property L)
    (j : yoneda.obj V ⟶ XU.1)
    (v : V ⟶ F) (r : F ⟶ U) [IsAffine ((𝒯).obj F)] (y₀ : (𝒯).obj F)
    (hr : ∀ y, (𝒯).map r y = u) (hsq : IsPullback j (yoneda.map v) fU.hom (yoneda.map r))
    (hamp : ∃ hL : Stacks.Ample.IsInvertibleModule ((𝒯).obj V)
        (Space.baseChangeModule B integerBase hZ L V j),
      @Stacks.Ample.IsAmple _ _ hL) :
    ∃ (T' : BigFppfOver B integerBase hZ) (π : T' ⟶ X.base),
      Smooth ((𝒯).map π) ∧ (𝒯).map φ u ∈ Set.range ((𝒯).map π) ∧
      ∃ (Xs : AlgebraicSpaces B integerBase hZ) (p : Xs ⟶ X.total) (q : Xs ⟶ schemeSpace T'),
        IsPullback p q X.toBase (schemeSpaceMap π) ∧
        ∃ L' : Space.Modules.{u, u} B integerBase hZ Xs.1 Xs.2,
          Space.IsRelativelyAmple B integerBase hZ q L' := by
  have sqU' := AlgebraicSpaces.isPullback_hom B integerBase hZ sqU
  have hfU : Space.IsProper B integerBase hZ fU.hom :=
    Space.isProper_of_isPullback_presheaf B integerBase hZ XU.2 X.total.2
      (isAlgebraicSpace_yoneda _ _ _ U)
      (isAlgebraicSpace_yoneda _ _ _ X.base) sqU' X.proper
  obtain ⟨O, huO, hrel⟩ :=
    Space.exists_mem_isRelativelyAmple_openSub_of_isAmple_fibre_of_isAffine (f := fU) hfU L hL u j
      v r y₀ hr hsq hamp
  obtain ⟨X₁, p₁, f₁, sq₁⟩ := exists_isPullback_schemeSpaceMap fU (Space.openSubHom U O)
  refine ⟨Space.openSub U O, Space.openSubHom U O ≫ φ, ?_, ⟨⟨u, huO⟩, ?_⟩, X₁, p₁ ≫ qU, f₁, ?_,
    _, hrel p₁ f₁ sq₁⟩
  · have het : Etale ((𝒯).map (Space.openSubHom U O ≫ φ)) := by
      rw [Functor.map_comp]
      exact MorphismProperty.comp_mem @Etale _ _
        (Space.etale_toScheme_map_openSubHom B integerBase hZ U O) hφ
    have := (Etale.iff_smoothOfRelativeDimension_zero _).1 het
    exact SmoothOfRelativeDimension.smooth 0 _
  · rw [Functor.map_comp, Space.toScheme_map_openSubHom]; rfl
  · rw [schemeSpaceMap_comp]
    exact sq₁.paste_horiz sqU

open Stacks.AlgebraicGeometry.ComponentDegrees in
/-- **Every family of curves is smooth locally polarized.** Through every point `s` of the base of
a family of curves `X ⟶ S` there is an étale (in particular smooth) morphism `π : T' ⟶ S` of the
site whose image contains `s`, along which the base change of `X` is a scheme carrying an
invertible module ample relative to the base change of `X ⟶ S`. -/
theorem isSmoothLocallyPolarized_of_curveFamily (G : CurveFamily B hZ) :
    G.IsSmoothLocallyPolarized := by
  refine isSmoothLocallyPolarized_of G fun s => ?_
  classical
  obtain ⟨V, v, j, hsq, hdim⟩ := exists_isPullback_residueField G s
  let F₁ := integerSiteObject B hZ (B.residueField_spec_contains G.base.left.property s)
  let r := residueFieldIntegerMap G s
  let fX : G.total.obj ⟶ yoneda.obj G.base := G.toBase.hom
  have hsq' : IsPullback j (yoneda.map v) fX (yoneda.map r) := hsq
  have hVp : IsProper ((𝒯).map v) :=
    Space.isProper_toScheme_map_of_isProper_yoneda_map B integerBase hZ v
      (Space.isProper_of_isPullback B integerBase hZ (isAlgebraicSpace_yoneda B integerBase hZ V)
        G.total.property (isAlgebraicSpace_yoneda B integerBase hZ _)
        (schemeSpace G.base).property hsq G.proper)
  let fV : (𝒯).obj V ⟶ Spec (.of (((𝒯).obj G.base).residueField s)) := (𝒯).map v
  have : IsProper fV := hVp
  have : IsLocallyNoetherian ((𝒯).obj V) := LocallyOfFiniteType.isLocallyNoetherian fV
  have : JacobsonSpace ((𝒯).obj V) := LocallyOfFiniteType.jacobsonSpace fV
  have : IsNoetherian ((𝒯).obj V) :=
    isNoetherian_of_isProper_over_field (((𝒯).obj G.base).residueField s) fV
  have : Subsingleton ((𝒯).obj F₁) := inferInstanceAs (Subsingleton (Spec (.of _)))
  have : Nonempty ((𝒯).obj F₁) := inferInstanceAs (Nonempty (Spec (.of _)))
  have hjmono : Mono j := by
    have : Mono ((𝒯).map r) := (inferInstance :
      Mono (((𝒯).obj G.base).fromSpecResidueField s))
    have : Mono r := (𝒯).mono_of_mono_map this
    have : Mono (yoneda.map r) := Functor.map_mono yoneda r
    exact hsq'.mono_fst_of_mono
  let ι := ↥(genericPointsOne ((𝒯).obj V))
  have : Finite ι := (finite_genericPointsOne ((𝒯).obj V)).to_subtype
  have : Fintype ι := Fintype.ofFinite ι
  have key : ∀ ζ : ι, ∃ (U : BigFppfOver B integerBase hZ) (φ : U ⟶ G.base) (u : (𝒯).obj U)
      (W : BigFppfOver B integerBase hZ) (e : yoneda.obj W ⟶ G.total.obj) (w : W.left.1)
      (hw : B.Contains (Spec (.of (W.left.1.residueField w)))) (x : (𝒯).obj V),
      x ∈ closure {ζ.1} ∧
      Space.pointsMap B integerBase hZ _ e (Space.presheafPoint B integerBase hZ W w hw) =
        Space.pointsMap B integerBase hZ _ j (Space.presheafPoint B integerBase hZ V x
          (B.residueField_spec_contains V.left.property x)) ∧
      Etale ((𝒯).map φ) ∧ (𝒯).map φ u = s ∧ IsIso (((𝒯).map φ).residueFieldMap u) ∧
      ∀ (T : BigFppfOver B integerBase hZ) (ψ : T ⟶ U), Etale ((𝒯).map ψ) →
      ∀ (XU : AlgebraicSpaces B integerBase hZ) (qU : XU.1 ⟶ G.total.obj)
        (fU : XU.1 ⟶ yoneda.obj T),
        IsPullback qU fU fX (yoneda.map (ψ ≫ φ)) →
        ∃ (P : BigFppfOver B integerBase hZ) (π : yoneda.obj P ⟶ XU.1) (p : P ⟶ T) (rr : P ⟶ W)
          (hπ : Space.IsClosedImmersion B integerBase hZ π),
          π ≫ fU = yoneda.map p ∧ π ≫ qU = yoneda.map rr ≫ e ∧
          _root_.AlgebraicGeometry.IsFinite ((𝒯).map p) ∧
          (∀ t, (𝒯).map ψ t = u → ∃ v', (𝒯).map p v' = t ∧ (𝒯).map rr v' = w) ∧
          Space.IsEffectiveCartierDivisor B integerBase hZ XU
            ⟨Subfunctor.range π, Space.isClosedSubspace_range_of_isClosedImmersion B integerBase hZ
              π (isAlgebraicSpace_yoneda B integerBase hZ P) hπ⟩ := by
    intro ζ
    obtain ⟨A, hA, f, x, hxA, hxζ, hf, hx, O, hxO, hiso⟩ :=
      exists_isRegular_isolated_of_mem_genericPointsOne hdim ζ.2
    obtain ⟨W, e, w, hw, gW, he, hmono, hgW, hWaff, hpt⟩ :=
      exists_elementaryEtaleChart_of_mem_fibre G s v j hsq x
    have : Flat ((𝒯).map gW) :=
      Space.prop_toScheme_map_of_holdsOnEveryEtaleChart B integerBase hZ G.flat e he hgW.symm
    have : LocallyOfFinitePresentation ((𝒯).map gW) :=
      Space.prop_toScheme_map_of_holdsOnEveryEtaleChart B integerBase hZ G.finitePresentation.1 e
        he hgW.symm
    have hws := toScheme_map_apply_eq_of_pointsMap_eq G s v j hsq x e w hw gW hgW hpt
    obtain ⟨Z, hwZ, hprin, hfib, z, hz, hqf⟩ :=
      exists_chartDivisor_of_fibre_equation G s v j hsq hA f hf hxA hx O hxO hiso e w hw gW he hgW
        hpt
    obtain ⟨U, φ, u, hφ, -, hu, hres, hpiece⟩ :=
      Space.exists_etale_isEffectiveCartierDivisor_range_of_chart fX G.proper.1 e he w hw hmono gW
        hgW Z hwZ hprin hfib z hz hqf
    refine ⟨U, φ, u, W, e, w, hw, x, hxζ, hpt, hφ, hu.trans hws, hres, ?_⟩
    intro T ψ hψ XU qU fU sqU
    obtain ⟨P, π, p, rr, hπ, h1, h2, h3, -, -, h6, h7⟩ := hpiece T ψ hψ XU qU fU sqU
    exact ⟨P, π, p, rr, hπ, h1, h2, h3, h6, h7⟩
  choose U φ u W e w hw x hxζ hpt hφ hu hres hpiece using key
  let ε : F₁ ⟶ Space.residueFieldObject B integerBase hZ G.base s
      (B.residueField_spec_contains G.base.left.property s) :=
    Over.homMk (𝟙 _) (by
      apply ObjectProperty.hom_ext
      exact specULiftZIsTerminal.hom_ext _ _)
  have hε : ε ≫ Space.residueFieldMap B integerBase hZ G.base s
      (B.residueField_spec_contains G.base.left.property s) = r := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact Category.id_comp _
  have hlift : ∀ ζ : ι, ∃ σ' : F₁ ⟶ U ζ, σ' ≫ φ ζ = r ∧ ∀ y, (𝒯).map σ' y = u ζ := by
    intro ζ
    obtain ⟨σ, hσ, hσu⟩ :=
      Space.exists_lift_residueFieldMap_of_isIso_residueFieldMap (φ ζ) (u ζ) s (hu ζ) (hres ζ)
    refine ⟨ε ≫ σ, by rw [Category.assoc, hσ, hε], fun y => ?_⟩
    rw [Functor.map_comp, Scheme.Hom.comp_apply, hσu]
  choose σ' hσ' hσu using hlift
  obtain ⟨T, φT, σT, hφT, hσT, hψ⟩ := Space.exists_etale_common_lift r U φ hφ σ' hσ' Finset.univ
  have hψ' : ∀ ζ : ι, ∃ ψ : T ⟶ U ζ, Etale ((𝒯).map ψ) ∧ ψ ≫ φ ζ = φT ∧ σT ≫ ψ = σ' ζ :=
    fun ζ => hψ ζ (Finset.mem_univ ζ)
  choose ψ hψet hψφ hψσ using hψ'
  obtain ⟨XT, qT', fT', sqU⟩ := exists_isPullback_schemeSpaceMap G.toBase φT
  let qT : XT.1 ⟶ G.total.obj := qT'.hom
  let fT : XT.1 ⟶ yoneda.obj T := fT'.hom
  have sqT : IsPullback qT fT fX (yoneda.map φT) := AlgebraicSpaces.isPullback_hom B _ _ sqU
  have hP : ∀ ζ : ι, _ := fun ζ => hpiece ζ T (ψ ζ) (hψet ζ) XT qT fT
    (by rw [hψφ ζ]; exact sqT)
  choose P π p rr hπ hπfT hπqT hfin hpts hcart using hP
  let Dζ : ι → Space.ClosedSubspaces B integerBase hZ XT.1 := fun ζ =>
    ⟨Subfunctor.range (π ζ), Space.isClosedSubspace_range_of_isClosedImmersion B integerBase hZ
      (π ζ) (isAlgebraicSpace_yoneda B integerBase hZ (P ζ)) (hπ ζ)⟩
  let l := (Finset.univ : Finset ι).toList
  let D := Space.sumClosedSubspacesList XT Dζ (Space.emptyClosedSubspace XT) l
  have hD : Space.IsEffectiveCartierDivisor B integerBase hZ XT D :=
    Space.isEffectiveCartierDivisor_sumClosedSubspacesList XT Dζ _
      (Space.isEffectiveCartierDivisor_emptyClosedSubspace XT) l fun ζ _ => hcart ζ
  let L := Space.associatedInvertibleSheaf B integerBase hZ XT D hD
  have hLinv : Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase hZ XT.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase hZ XT.1 XT.2).O)).property L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
      (Space.associatedInvertibleSheaf_isInvertible B integerBase hZ XT D hD)
  let σs := Space.canonicalSection B integerBase hZ XT D hD
  let jT : yoneda.obj V ⟶ XT.1 := sqT.lift j (yoneda.map (v ≫ σT)) (by
    rw [hsq'.w, ← hσT]
    simp only [Functor.map_comp, Category.assoc])
  have hjT : jT ≫ qT = j := sqT.lift_fst _ _ _
  have hjT' : jT ≫ fT = yoneda.map (v ≫ σT) := sqT.lift_snd _ _ _
  have hsqT : IsPullback jT (yoneda.map v) fT (yoneda.map σT) := by
    refine IsPullback.of_right ?_ (by rw [hjT', Functor.map_comp]) sqT
    rw [hjT, ← Functor.map_comp, hσT]
    exact hsq'
  obtain ⟨y₀⟩ : Nonempty ((𝒯).obj F₁) := inferInstance
  let t := (𝒯).map σT y₀
  have hr : ∀ y, (𝒯).map σT y = t := fun y => by rw [Subsingleton.elim y y₀]
  have ht : (𝒯).map φT t = s := by
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hσT]
    exact Scheme.fromSpecResidueField_apply _ _
  let k : Space.representedAlgebraicSpace B integerBase hZ V ⟶ XT := ObjectProperty.homMk jT
  let M := Space.pointModule B integerBase hZ L V k
  let τ := Space.pointGlobalSection B integerBase hZ L V k σs
  have hMinv : Stacks.Ample.IsInvertibleModule ((𝒯).obj V) M :=
    Space.isInvertibleModule_pointModule B integerBase hZ L hLinv V k
  have hMinv' : SheafOfModules.IsInvertible ((𝒯).obj V).toRingedSpace.presheaf
      (structureSheafRing ((𝒯).obj V).toRingedSpace).property M :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).1 hMinv
  have hzeroD : ∀ y : (𝒯).obj V, y ∉ Stacks.Ample.nonvanishingLocus M τ ↔
      ∃ ζ ∈ l, Space.pointsMap B integerBase hZ _ jT (Space.presheafPoint B integerBase hZ V y
        (B.residueField_spec_contains V.left.property y)) ∈
          Set.range (Space.pointsMap B integerBase hZ _ (π ζ)) := by
    intro y
    rw [Space.notMem_nonvanishingLocus_pointGlobalSection_iff_mem_subspacePointSet B integerBase hZ
      L hLinv σs V k y, Space.zeroScheme_canonicalSection_eq,
      Space.mem_subspacePointSet_sumClosedSubspacesList_iff]
    refine exists_congr fun ζ => and_congr_right fun _ => ?_
    have : Mono (π ζ) := Space.mono_of_isClosedImmersion B integerBase hZ (π ζ) (hπ ζ)
    change _ ∈ Set.range (Space.pointsMap B integerBase hZ (Subfunctor.range (π ζ)).toFunctor
      (Subfunctor.range (π ζ)).ι) ↔ _
    rw [Space.range_pointsMap_ι_range_of_mono B integerBase hZ (π ζ)]
    rfl
  have hampM : Scheme.Modules.IsAmple ((𝒯).obj V) M := by
    refine isAmple_of_mem_nonvanishingLocus_genericPointsOne (((𝒯).obj G.base).residueField s)
      fV hdim M τ ?_ ?_
    · intro ζ hζ
      by_contra hnv
      obtain ⟨η, -, hη⟩ := (hzeroD ζ).1 hnv
      refine notMem_range_pointsMap_of_isFinite fT σT jT v hsqT (π η) (hπ η) (p η) (hπfT η) ζ
        ?_ hη
      intro hcl
      have h0 := (mem_genericPointsOne_iff.1 hζ).2
      rw [hcl.closure_eq] at h0
      have : topologicalKrullDim ({ζ} : Set ((𝒯).obj V)) = 0 :=
        topologicalKrullDim_eq_zero_of_discreteTopology_nonempty
      rw [this] at h0
      exact zero_ne_one h0
    · intro ζ hζ
      refine ⟨x ⟨ζ, hζ⟩, hxζ ⟨ζ, hζ⟩, (hzeroD _).2 ⟨⟨ζ, hζ⟩, Finset.mem_toList.2
        (Finset.mem_univ _), ?_⟩⟩
      set η : ι := ⟨ζ, hζ⟩
      have htu : (𝒯).map (ψ η) t = u η := by
        rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hψσ η, hσu]
      obtain ⟨v', hv't, hv'w⟩ := hpts η t htu
      refine ⟨Space.presheafPoint B integerBase hZ (P η) v'
        (B.residueField_spec_contains (P η).left.property v'), ?_⟩
      refine eq_pointsMap_of_isPullback_of_mono fT σT jT v hsqT qT j hjT _ _ ?_ ?_
      · rw [← Function.comp_apply (f := Space.pointsMap B integerBase hZ _ qT),
          ← Space.pointsMap_comp, hπqT, Space.pointsMap_comp, Function.comp_apply,
          Space.pointsMap_presheafPoint B integerBase hZ (P η) (W η) (rr η) v' _
            (B.residueField_spec_contains (W η).left.property _)]
        have hv'w' : (rr η).left.hom v' = w η := hv'w
        simp only [hv'w']
        exact hpt η
      · rw [← Function.comp_apply (f := Space.pointsMap B integerBase hZ _ fT),
          ← Space.pointsMap_comp, hπfT, Space.pointsMap_presheafPoint B integerBase hZ (P η) T
            (p η) v' _ (B.residueField_spec_contains T.left.property _)]
        refine ⟨Space.presheafPoint B integerBase hZ F₁ y₀
          (B.residueField_spec_contains F₁.left.property y₀), ?_⟩
        rw [Space.pointsMap_presheafPoint B integerBase hZ F₁ T σT y₀ _
          (B.residueField_spec_contains T.left.property _)]
        have hv't' : (p η).left.hom v' = (σT).left.hom y₀ := hv't
        simp only [hv't']
  let E : M ≅ Space.baseChangeModule B integerBase hZ L V jT :=
    (Space.restrictToChartSchemeIsoChartRestrictionSheaf B integerBase hZ
      (Space.representedAlgebraicSpace B integerBase hZ V)
      ((Space.modulePullback B integerBase hZ k).obj L)
      (Space.idEtaleChart B integerBase hZ V)).symm
  have hBinv : Stacks.Ample.IsInvertibleModule ((𝒯).obj V)
      (Space.baseChangeModule B integerBase hZ L V jT) :=
    Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ E
  have hamp : ∃ hL : Stacks.Ample.IsInvertibleModule ((𝒯).obj V)
      (Space.baseChangeModule B integerBase hZ L V jT), @Stacks.Ample.IsAmple _ _ hL :=
    ⟨hBinv, (Stacks.RelativeVeryAmple.isAmple_congr M _ E).1
      ((Stacks.AmpleBridge.isAmple_iff_isAmple _ M).2 hampM)⟩
  have hchart := exists_isRelativelyAmple_chart_of_isAmple_fibre_of_isAffine G φT hφT t _ _ sqU L
    hLinv jT v σT y₀ hr hsqT hamp
  rwa [ht] at hchart

/-- **Stacks 0E6F pointwise, for finitely many families over one base.** Let `X i`, for `i` in a
finite type, be families of curves over a common base `S`, and `s ∈ S`. There is an étale
morphism `φ : U ⟶ S` of the site with a point `u` over `s`, along which every `X i` becomes a
scheme `Z`, H-projective over `U`. -/
theorem exists_etale_isPullback_isProjectiveMorphism {ι : Type*} [Finite ι]
    {S : BigFppfOver B integerBase hZ} (X : ι → CurveFamily B hZ) (hX : ∀ i, (X i).base = S)
    (s : (𝒯).obj S) :
    ∃ (U : BigFppfOver B integerBase hZ) (φ : U ⟶ S) (u : (𝒯).obj U),
      Etale ((𝒯).map φ) ∧ (𝒯).map φ u = s ∧
      ∀ i, ∃ (Z : BigFppfOver B integerBase hZ) (p : schemeSpace Z ⟶ (X i).total) (q : Z ⟶ U),
        IsPullback p (schemeSpaceMap q) (X i).toBase
          (schemeSpaceMap (φ ≫ eqToHom (hX i).symm)) ∧
        IsProjectiveMorphism ((𝒯).map q) :=
  exists_etale_isPullback_isProjectiveMorphism_of_isSmoothLocallyPolarized X hX
    (fun i => isSmoothLocallyPolarized_of_curveFamily (X i)) s

/-- **Families of curves are étale locally H-projective schemes.** Let `X ⟶ S` be a family of
curves. Then there is an étale covering `{S_j ⟶ S}` (a family of étale morphisms of the site whose
images cover `S`) such that each `X_j = X ×_S S_j` is a scheme `Z` — a cartesian square of
algebraic spaces with `schemeSpace Z` at its corner — and `Z ⟶ S_j` is H-projective. -/
@[stacks 0E6F]
theorem exists_etaleCovering_isPullback_isProjectiveMorphism (X : CurveFamily B hZ) :
    ∃ (J : Type u) (U : J → BigFppfOver B integerBase hZ) (φ : ∀ j, U j ⟶ X.base),
      (∀ j, Etale ((𝒯).map (φ j))) ∧
      (∀ s : (𝒯).obj X.base, ∃ j, s ∈ Set.range ((𝒯).map (φ j))) ∧
      ∀ j, ∃ (Z : BigFppfOver B integerBase hZ) (p : schemeSpace Z ⟶ X.total) (q : Z ⟶ U j),
        IsPullback p (schemeSpaceMap q) X.toBase (schemeSpaceMap (φ j)) ∧
        IsProjectiveMorphism ((𝒯).map q) :=
  exists_etaleCovering_isPullback_isProjectiveMorphism_of_isSmoothLocallyPolarized_one X
    (isSmoothLocallyPolarized_of_curveFamily X)

end AlgebraicGeometry.CurveFamily

end
