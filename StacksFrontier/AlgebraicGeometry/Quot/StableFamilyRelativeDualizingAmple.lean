module

public import StacksFrontier.AlgebraicGeometry.Quot.StableFamilyDualizingAmpleOverOpen
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOpenAffineEtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineRelativeDualizingBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackTopDegree
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackEtale
public import StacksFrontier.AlgebraicGeometry.Duality.C1590Private.RelativeDualizingSheafNodal
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartwiseInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineRelativeDualizingComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedIsLEEtaleFamily
public import StacksCore.Tactic.StacksAttribute

/-!
# Stable fibres and ampleness of the relative dualizing sheaf

Let `f : X → S` be a prestable family of curves of genus `g ≥ 2` and `s ∈ S`. The fibre `X_s` has
no rational tail and no rational bridge if and only if the relative dualizing sheaf `ω_{X/S}` is
ample on `f⁻¹(U)` for some open neighbourhood `U` of `s`.

The relative dualizing sheaf is read over affine opens `U` of the base: the relative dualizing
complex of `f⁻¹(U) → U` is `a_U(𝒪_U)` (the third remark after Stacks 0E5X,
`AlgebraicGeometry.Space.affineRelativeDualizingComplex`), and `ω_{f⁻¹(U)/U}` is its cohomology
sheaf in degree `-1` (Stacks 0E6Q).

## Main results

* `CurveFamily.hasNoRationalTailNoRationalBridge_iff_exists_isAffineOpen_isRelativelyAmple`: for a
  prestable family of curves of genus `g ≥ 2`, the fibre over `s` has no rational tail and no
  rational bridge if and only if `ω_{f⁻¹(U)/U}` is ample on `f⁻¹(U)` relative to `U` for some
  affine open `U ∋ s`.
* `AlgebraicGeometry.CurveFamily.nonempty_relativeDualizingSheafOver_iso_modulePullback`: for
  affine opens `V ⊆ U`, `ω_{f⁻¹(V)/V}` is the restriction of `ω_{f⁻¹(U)/U}` (Stacks 0E6C at an
  open immersion).
* `AlgebraicGeometry.CurveFamily.isLE_relativeDualizingComplexOver`: `a_U(𝒪_U)` has no cohomology
  above degree `-1` (Stacks 0E6P).
* `AlgebraicGeometry.CurveFamily.isInvertible_relativeDualizingSheafOver`: `ω_{f⁻¹(U)/U}` is
  invertible (Stacks 0E6R).
* `AlgebraicGeometry.CurveFamily.nonempty_baseChangeModule_relativeDualizingSheafOver_iso`: on a
  fibre `X_s`, `s ∈ U`, `ω_{f⁻¹(U)/U}` restricts to the dualizing sheaf of the fibre (Stacks 0E6R
  with the identification over a field of Section 0E6N).

## References

* [Stacks Project, Tag 0E74](https://stacks.math.columbia.edu/tag/0E74)
* [Stacks Project, Tag 0E5X](https://stacks.math.columbia.edu/tag/0E5X)
* [Stacks Project, Tag 0E5I](https://stacks.math.columbia.edu/tag/0E5I)
* [Stacks Project, Tag 0E6Q](https://stacks.math.columbia.edu/tag/0E6Q)
* [Stacks Project, Tag 0E6R](https://stacks.math.columbia.edu/tag/0E6R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace CurveFamily

/-- The open subscheme of the base of a family of curves on an affine open is an affine algebraic
space. -/
theorem isAffineSpace_openSub (X : CurveFamily B hZ)
    {U : ((BigFppfOver.toScheme B integerBase hZ).obj X.base).Opens} (hU : IsAffineOpen U) :
    Space.IsAffineSpace B integerBase hZ (schemeSpace (Space.openSub X.base U)).1 :=
  Space.isAffineSpace_yoneda B integerBase hZ _ hU

/-- The base change of a family of curves along the inclusion of an open of the base is of
finite presentation. -/
theorem isFinitePresentation_of_isPullback_openSub (X : CurveFamily B hZ)
    {U : ((BigFppfOver.toScheme B integerBase hZ).obj X.base).Opens}
    {X₁ : AlgebraicSpaces B integerBase hZ} {p₁ : X₁ ⟶ X.total}
    {f₁ : X₁ ⟶ schemeSpace (Space.openSub X.base U)}
    (h : IsPullback p₁ f₁ X.toBase (schemeSpaceMap (Space.openSubHom X.base U))) :
    Space.IsFinitePresentation B integerBase hZ f₁.hom :=
  Space.IsFinitePresentation.of_isPullback B integerBase hZ X₁.2 X.total.2
    (schemeSpace (Space.openSub X.base U)).2 (schemeSpace X.base).2
    (AlgebraicSpaces.isPullback_hom B integerBase hZ h) X.finitePresentation

/-- The relative dualizing sheaf `ω_{f⁻¹(U)/U}` of the family over an affine open `U` of the
base, for a presentation `X₁ = f⁻¹(U)` of the restricted family. -/
abbrev relativeDualizingSheafOver (X : CurveFamily B hZ)
    {U : ((BigFppfOver.toScheme B integerBase hZ).obj X.base).Opens} (hU : IsAffineOpen U)
    {X₁ : AlgebraicSpaces B integerBase hZ} {p₁ : X₁ ⟶ X.total}
    {f₁ : X₁ ⟶ schemeSpace (Space.openSub X.base U)}
    (h : IsPullback p₁ f₁ X.toBase (schemeSpaceMap (Space.openSubHom X.base U))) :
    Space.Modules.{u, u} B integerBase hZ X₁.1 X₁.2 :=
  Space.affineRelativeDualizingSheaf B.contains_terminal f₁
    (isFinitePresentation_of_isPullback_openSub X h) (isAffineSpace_openSub X hU)

/-- The base change of a family of curves along the inclusion of an open of the base is proper. -/
theorem isProper_of_isPullback_openSub (X : CurveFamily B hZ)
    {U : ((BigFppfOver.toScheme B integerBase hZ).obj X.base).Opens}
    {X₁ : AlgebraicSpaces B integerBase hZ} {p₁ : X₁ ⟶ X.total}
    {f₁ : X₁ ⟶ schemeSpace (Space.openSub X.base U)}
    (h : IsPullback p₁ f₁ X.toBase (schemeSpaceMap (Space.openSubHom X.base U))) :
    Space.IsProper B integerBase hZ f₁.hom :=
  (Space.isProper_isStableUnderBaseChange B integerBase hZ).of_isPullback h X.proper

/-- The base change of a family of curves along the inclusion of an open of the base is flat. -/
theorem isFlat_of_isPullback_openSub (X : CurveFamily B hZ)
    {U : ((BigFppfOver.toScheme B integerBase hZ).obj X.base).Opens}
    {X₁ : AlgebraicSpaces B integerBase hZ} {p₁ : X₁ ⟶ X.total}
    {f₁ : X₁ ⟶ schemeSpace (Space.openSub X.base U)}
    (h : IsPullback p₁ f₁ X.toBase (schemeSpaceMap (Space.openSubHom X.base U))) :
    Space.IsFlat B integerBase hZ f₁.hom :=
  (Space.isFlat_isStableUnderBaseChange B integerBase hZ).of_isPullback h X.flat

/-- A base change of the family over an open of the base to a scheme of the site is of finite
presentation. -/
theorem isFinitePresentation_schemeSpaceMap_of_isPullback (X : CurveFamily B hZ)
    {U : ((BigFppfOver.toScheme B integerBase hZ).obj X.base).Opens}
    {X₁ : AlgebraicSpaces B integerBase hZ} {p₁ : X₁ ⟶ X.total}
    {f₁ : X₁ ⟶ schemeSpace (Space.openSub X.base U)}
    (h : IsPullback p₁ f₁ X.toBase (schemeSpaceMap (Space.openSubHom X.base U)))
    {T Z : BigFppfOver B integerBase hZ} {φ : T ⟶ Space.openSub X.base U} {q : Z ⟶ T}
    {p : schemeSpace Z ⟶ X₁} (hsq : IsPullback p (schemeSpaceMap q) f₁ (schemeSpaceMap φ)) :
    Space.IsFinitePresentation B integerBase hZ (schemeSpaceMap q).hom :=
  Space.IsFinitePresentation.of_isPullback B integerBase hZ (schemeSpace Z).2 X₁.2
    (schemeSpace T).2 (schemeSpace (Space.openSub X.base U)).2
    (AlgebraicSpaces.isPullback_hom B integerBase hZ hsq)
    (isFinitePresentation_of_isPullback_openSub X h)

/-- For a cartesian square `Z ⟶ f⁻¹(U)` over `T ⟶ U` with `T` an affine scheme of the
site, the derived pullback of `ω^•_{f⁻¹(U)/U} = a_U(𝒪_U)` to `Z` is `a_T(𝒪_T)` (Stacks 0E5I(1)
at `𝒪`). -/
theorem nonempty_quasicoherentDerivedModulePullback_relativeDualizingComplexOver_iso
    (X : CurveFamily B hZ)
    {U : ((BigFppfOver.toScheme B integerBase hZ).obj X.base).Opens} (hU : IsAffineOpen U)
    {X₁ : AlgebraicSpaces B integerBase hZ} {p₁ : X₁ ⟶ X.total}
    {f₁ : X₁ ⟶ schemeSpace (Space.openSub X.base U)}
    (h : IsPullback p₁ f₁ X.toBase (schemeSpaceMap (Space.openSubHom X.base U)))
    {T Z : BigFppfOver B integerBase hZ} (φ : T ⟶ Space.openSub X.base U) (q : Z ⟶ T)
    (p : schemeSpace Z ⟶ X₁) [IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj T)]
    (hsq : IsPullback p (schemeSpaceMap q) f₁ (schemeSpaceMap φ)) :
    Nonempty ((Space.quasicoherentDerivedModulePullback p).obj
        (Space.affineRelativeDualizingComplex B.contains_terminal f₁
          (isFinitePresentation_of_isPullback_openSub X h) (isAffineSpace_openSub X hU)) ≅
      Space.affineRelativeDualizingComplex B.contains_terminal (schemeSpaceMap q)
        (isFinitePresentation_schemeSpaceMap_of_isPullback X h hsq)
        (Space.isAffineSpace_yoneda B integerBase hZ T inferInstance)) :=
  Space.nonempty_quasicoherentDerivedModulePullback_affineRelativeDualizingComplex_iso
    B.contains_terminal hsq (isAffineSpace_openSub X hU)
    (Space.isAffineSpace_yoneda B integerBase hZ T inferInstance)
    (isProper_of_isPullback_openSub X h) (isFlat_of_isPullback_openSub X h)
    (isFinitePresentation_of_isPullback_openSub X h)
    (isFinitePresentation_schemeSpaceMap_of_isPullback X h hsq)

/-- The base change of the family to a chart `Z ⟶ T` of an étale chart of the base is flat,
locally of finite presentation and proper. -/
private theorem flat_lfp_isProper_toScheme_map_of_isPullback (X : CurveFamily B hZ)
    {U : ((BigFppfOver.toScheme B integerBase hZ).obj X.base).Opens}
    {X₁ : AlgebraicSpaces B integerBase hZ} {p₁ : X₁ ⟶ X.total}
    {f₁ : X₁ ⟶ schemeSpace (Space.openSub X.base U)}
    (h : IsPullback p₁ f₁ X.toBase (schemeSpaceMap (Space.openSubHom X.base U)))
    {T Z : BigFppfOver B integerBase hZ} {φ : T ⟶ Space.openSub X.base U} {q : Z ⟶ T}
    {p : schemeSpace Z ⟶ X₁} (hsq : IsPullback p (schemeSpaceMap q) f₁ (schemeSpaceMap φ)) :
    Flat ((BigFppfOver.toScheme B integerBase hZ).map q) ∧
      LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map q) ∧
      IsProper ((BigFppfOver.toScheme B integerBase hZ).map q) :=
  let G := X.ofIsPullback B hZ (Space.openSubHom X.base U) p₁ f₁ h
  ⟨G.flat_toScheme_map_of_isPullback hsq,
    G.locallyOfFinitePresentation_toScheme_map_of_isPullback hsq,
    G.isProper_toScheme_map_of_isPullback_schemeSpaceMap hsq⟩

/-- For a prestable family and an affine open `U` of the base, the relative dualizing complex
`a_U(𝒪_U)` of `f⁻¹(U) → U` has no cohomology above degree `-1` (Stacks 0E6P). -/
theorem isLE_relativeDualizingComplexOver (X : CurveFamily B hZ)
    (hX : IsPrestableCurveFamily B hZ X)
    {U : ((BigFppfOver.toScheme B integerBase hZ).obj X.base).Opens} (hU : IsAffineOpen U)
    {X₁ : AlgebraicSpaces B integerBase hZ} {p₁ : X₁ ⟶ X.total}
    {f₁ : X₁ ⟶ schemeSpace (Space.openSub X.base U)}
    (h : IsPullback p₁ f₁ X.toBase (schemeSpaceMap (Space.openSubHom X.base U))) :
    letI := HasDerivedCategory.standard (Space.Modules.{u, u} B integerBase hZ X₁.1 X₁.2)
    (Space.affineRelativeDualizingComplex B.contains_terminal f₁
      (isFinitePresentation_of_isPullback_openSub X h) (isAffineSpace_openSub X hU)).obj.IsLE
        (-1) := by
  let := HasDerivedCategory.standard (Space.Modules.{u, u} B integerBase hZ X₁.1 X₁.2)
  obtain ⟨I, T, Z, φ, q, p, haff, -, hsq, hnod, hcov⟩ :=
    exists_affine_etale_charts_of_isPullback hX (Space.openSubHom X.base U) h
  rw [DerivedCategory.isLE_iff]
  intro n hn
  refine Space.isZero_of_isZero_modulePullback_of_isEtale (Z := fun i => schemeSpace (Z i)) p
    hcov.etale (fun x => Set.mem_iUnion.mp (Set.eq_univ_iff_forall.mp hcov.jointly_surjective x))
    _ fun i => ?_
  have := haff i
  obtain ⟨_, _, _⟩ := flat_lfp_isProper_toScheme_map_of_isPullback X h (hsq i)
  obtain ⟨e⟩ := nonempty_quasicoherentDerivedModulePullback_relativeDualizingComplexOver_iso
    X hU h (φ i) (q i) (p i) (hsq i)
  let := HasDerivedCategory.standard
    (Space.Modules.{u, u} B integerBase hZ (schemeSpace (Z i)).1 (schemeSpace (Z i)).2)
  have hB := Space.isLE_affineRelativeDualizingComplex_of_isLE B.contains_terminal (q i)
    (isFinitePresentation_schemeSpaceMap_of_isPullback X h (hsq i)) (-1)
    (C1590Private.isLE_relativeDualizingComplex _
      (C1590Private.hasGorensteinCurveFibres_of_isAtWorstNodal (hnod i)))
  exact (((DerivedCategory.isLE_iff _ (-1)).1 hB n hn).of_iso
    ((DerivedCategory.homologyFunctor _ n).mapIso ((ObjectProperty.ι _).mapIso e))).of_iso
    (Space.smallEtaleDerivedModulePullbackHomologyIsoOfIsEtale (p i) (hcov.etale i) _ n).symm

/-- A point of the open subscheme `U` of the base maps into `U`. -/
private theorem toScheme_map_openSubHom_mem (X : CurveFamily B hZ)
    (W : ((BigFppfOver.toScheme B integerBase hZ).obj X.base).Opens)
    (y : (BigFppfOver.toScheme B integerBase hZ).obj (Space.openSub X.base W)) :
    (BigFppfOver.toScheme B integerBase hZ).map (Space.openSubHom X.base W) y ∈ W := by
  rw [Space.toScheme_map_openSubHom]
  exact (Scheme.Opens.range_ι W).subset (Set.mem_range_self y)

/-- The inclusion of an open of the base is a monomorphism of algebraic spaces. -/
private theorem mono_schemeSpaceMap_openSubHom (X : CurveFamily B hZ)
    (U : ((BigFppfOver.toScheme B integerBase hZ).obj X.base).Opens) :
    Mono (schemeSpaceMap (Space.openSubHom X.base U)) :=
  (ObjectProperty.ι _).mono_of_mono_map (show Mono (yoneda.map (Space.openSubHom X.base U)) from
    have := Space.mono_openSubHom_of_opens X.base U
    inferInstance)

/-- For opens `V ≤ U` of the base, the inclusion of `V` factors through that of `U`, also as
morphisms of algebraic spaces. -/
private theorem exists_openSubHom_factor (X : CurveFamily B hZ)
    {U V : ((BigFppfOver.toScheme B integerBase hZ).obj X.base).Opens} (hVU : V ≤ U) :
    ∃ t : Space.openSub X.base V ⟶ Space.openSub X.base U,
      t ≫ Space.openSubHom X.base U = Space.openSubHom X.base V ∧
      schemeSpaceMap t ≫ schemeSpaceMap (Space.openSubHom X.base U) =
        schemeSpaceMap (Space.openSubHom X.base V) := by
  have ht := Space.openSubLift_comp_openSubHom X.base U (Space.openSubHom X.base V)
    (fun y => hVU (toScheme_map_openSubHom_mem X V y))
  exact ⟨_, ht, by rw [← schemeSpaceMap_comp, ht]⟩

/-- For affine opens `V ⊆ U` of the base, `ω_{f⁻¹(V)/V}` is the
restriction of `ω_{f⁻¹(U)/U}` to `f⁻¹(V)`. -/
theorem nonempty_relativeDualizingSheafOver_iso_modulePullback (X : CurveFamily B hZ)
    {U V : ((BigFppfOver.toScheme B integerBase hZ).obj X.base).Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (hVU : V ≤ U)
    {X₁ : AlgebraicSpaces B integerBase hZ} {p₁ : X₁ ⟶ X.total}
    {f₁ : X₁ ⟶ schemeSpace (Space.openSub X.base U)}
    (h₁ : IsPullback p₁ f₁ X.toBase (schemeSpaceMap (Space.openSubHom X.base U)))
    {X₂ : AlgebraicSpaces B integerBase hZ} {p₂ : X₂ ⟶ X.total}
    {f₂ : X₂ ⟶ schemeSpace (Space.openSub X.base V)}
    (h₂ : IsPullback p₂ f₂ X.toBase (schemeSpaceMap (Space.openSubHom X.base V)))
    (q : X₂ ⟶ X₁) (hq : q ≫ p₁ = p₂) :
    Nonempty (X.relativeDualizingSheafOver hV h₂ ≅
      (Space.modulePullback B integerBase hZ q).obj (X.relativeDualizingSheafOver hU h₁)) := by
  let := HasDerivedCategory.standard (Space.Modules.{u, u} B integerBase hZ X₂.1 X₂.2)
  obtain ⟨t, ht, hst⟩ := exists_openSubHom_factor X hVU
  have := mono_schemeSpaceMap_openSubHom X U
  have hw : q ≫ f₁ = f₂ ≫ schemeSpaceMap t := by
    rw [← cancel_mono (schemeSpaceMap (Space.openSubHom X.base U))]
    simp only [Category.assoc]
    rw [← h₁.w, reassoc_of% hq, h₂.w, hst]
  have hsq : IsPullback q f₂ f₁ (schemeSpaceMap t) :=
    IsPullback.of_right (by rw [hq, hst]; exact h₂) hw h₁
  have hett : Space.IsEtale B integerBase hZ (schemeSpaceMap t).hom := by
    refine C1590Private.isEtale_schemeSpaceMap_of_etale t ?_
    have : IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map
        (Space.openSubHom X.base U)) := by
      rw [Space.toScheme_map_openSubHom]
      exact (inferInstance : IsOpenImmersion U.ι)
    have : IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map t ≫
        (BigFppfOver.toScheme B integerBase hZ).map (Space.openSubHom X.base U)) := by
      rw [← Functor.map_comp, ht, Space.toScheme_map_openSubHom]
      exact (inferInstance : IsOpenImmersion V.ι)
    have := IsOpenImmersion.of_comp ((BigFppfOver.toScheme B integerBase hZ).map t)
      ((BigFppfOver.toScheme B integerBase hZ).map (Space.openSubHom X.base U))
    infer_instance
  have hetq : Space.IsEtale B integerBase hZ q.hom :=
    Space.isEtale_of_isPullback B integerBase hZ _ _ _ _ hsq.flip hett
  obtain ⟨e⟩ := Space.nonempty_quasicoherentDerivedModulePullback_affineRelativeDualizingComplex_iso
    B.contains_terminal hsq (isAffineSpace_openSub X hU) (isAffineSpace_openSub X hV)
    (isProper_of_isPullback_openSub X h₁) (isFlat_of_isPullback_openSub X h₁)
    (isFinitePresentation_of_isPullback_openSub X h₁)
    (isFinitePresentation_of_isPullback_openSub X h₂)
  exact ⟨(DerivedCategory.homologyFunctor _ (-1)).mapIso ((ObjectProperty.ι _).mapIso e.symm) ≪≫
    Space.smallEtaleDerivedModulePullbackHomologyIsoOfIsEtale q hetq _ (-1)⟩

/-- For a prestable family and an affine open `U` of the base, `ω_{f⁻¹(U)/U}` is an invertible
module on `f⁻¹(U)` (Stacks 0E6R, part (1)). -/
theorem isInvertible_relativeDualizingSheafOver (X : CurveFamily B hZ)
    (hX : IsPrestableCurveFamily B hZ X)
    {U : ((BigFppfOver.toScheme B integerBase hZ).obj X.base).Opens} (hU : IsAffineOpen U)
    {X₁ : AlgebraicSpaces B integerBase hZ} {p₁ : X₁ ⟶ X.total}
    {f₁ : X₁ ⟶ schemeSpace (Space.openSub X.base U)}
    (h : IsPullback p₁ f₁ X.toBase (schemeSpaceMap (Space.openSubHom X.base U))) :
    Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase hZ X₁.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase hZ X₁.1 X₁.2).O)).property
      (X.relativeDualizingSheafOver hU h) := by
  obtain ⟨I, T, Z, φ, q, p, haff, -, hsq, hnod, hcov⟩ :=
    exists_affine_etale_charts_of_isPullback hX (Space.openSubHom X.base U) h
  refine Space.isInvertible_of_isEtaleCovering_baseChangeModule B integerBase hZ X₁ _
    (Space.isQuasicoherentOnSite_affineRelativeDualizingSheaf _ _ _ _) Z (fun i => (p i).hom)
    hcov fun i => ?_
  have := haff i
  obtain ⟨_, _, _⟩ := flat_lfp_isProper_toScheme_map_of_isPullback X h (hsq i)
  obtain ⟨e⟩ := nonempty_quasicoherentDerivedModulePullback_relativeDualizingComplexOver_iso
    X hU h (φ i) (q i) (p i) (hsq i)
  let := HasDerivedCategory.standard (Space.Modules.{u, u} B integerBase hZ X₁.1 X₁.2)
  let := HasDerivedCategory.standard
    (Space.Modules.{u, u} B integerBase hZ (schemeSpace (Z i)).1 (schemeSpace (Z i)).2)
  let := HasDerivedCategory.standard (Space.Modules.{u, u} B integerBase hZ (yoneda.obj (Z i))
    (isAlgebraicSpace_yoneda B integerBase hZ (Z i)))
  let E : Space.baseChangeModule B integerBase hZ (X.relativeDualizingSheafOver hU h) (Z i)
      (p i).hom ≅
      C1590Private.relativeDualizingSheaf ((BigFppfOver.toScheme B integerBase hZ).map (q i)) :=
    Space.restrictToChartSchemeMapIso B integerBase hZ
        (isAlgebraicSpace_yoneda B integerBase hZ (Z i))
        ((Space.smallEtaleDerivedModulePullbackHomologyIsoOfIsEtale (p i) (hcov.etale i) _
          (-1)).symm ≪≫
          (DerivedCategory.homologyFunctor (Space.Modules.{u, u} B integerBase hZ (yoneda.obj (Z i))
            (isAlgebraicSpace_yoneda B integerBase hZ (Z i))) (-1)).mapIso
            ((ObjectProperty.ι _).mapIso e))
        (Space.idEtaleChart B integerBase hZ (Z i)) ≪≫
      Space.restrictToChartSchemeAffineRelativeDualizingSheafIso B.contains_terminal (q i)
        (isFinitePresentation_schemeSpaceMap_of_isPullback X h (hsq i))
  have : Stacks.Ample.IsInvertibleModule _
      (C1590Private.relativeDualizingSheaf ((BigFppfOver.toScheme B integerBase hZ).map (q i))) :=
    C1590Private.isInvertible_relativeDualizingSheaf _
      (C1590Private.hasGorensteinCurveFibres_of_isAtWorstNodal (hnod i))
  exact Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ E.symm

/-- For a prestable family, an affine open `U` of the base and `s ∈ U`, the
restriction of `ω_{f⁻¹(U)/U}` to a presentation `V` of the fibre `X_s` is the dualizing sheaf
`ω_V` of the proper `κ(s)`-scheme `V` (Stacks 0BS2, 0E6R). -/
theorem nonempty_baseChangeModule_relativeDualizingSheafOver_iso (X : CurveFamily B hZ)
    (hX : IsPrestableCurveFamily B hZ X)
    {U : ((BigFppfOver.toScheme B integerBase hZ).obj X.base).Opens} (hU : IsAffineOpen U)
    {X₁ : AlgebraicSpaces B integerBase hZ} {p₁ : X₁ ⟶ X.total}
    {f₁ : X₁ ⟶ schemeSpace (Space.openSub X.base U)}
    (h : IsPullback p₁ f₁ X.toBase (schemeSpaceMap (Space.openSubHom X.base U)))
    {s : (BigFppfOver.toScheme B integerBase hZ).obj X.base} (hs : s ∈ U)
    {V : BigFppfOver B integerBase hZ} {v : V ⟶ X.residuePoint B hZ s}
    {q : yoneda.obj V ⟶ X.total.obj} (hq : X.IsFibrePresentation B hZ s v q)
    (q₁ : yoneda.obj V ⟶ X₁.obj) (hq₁ : q₁ ≫ p₁.hom = q) :
    haveI := hq.isProper
    Nonempty (Space.baseChangeModule B integerBase hZ (X.relativeDualizingSheafOver hU h) V q₁ ≅
      Stacks.Duality.dualizingSheafOverField (X.fibreMap B hZ s v)) := by
  have := hq.isProper
  have : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj (X.residuePoint B hZ s)) :=
    inferInstanceAs (IsAffine (Spec _))
  have hr : ∀ y, ((BigFppfOver.toScheme B integerBase hZ).map (X.residuePointMap B hZ s)) y = s :=
    fun _ => Scheme.fromSpecResidueField_apply _ _
  let rU := Space.openSubLift X.base U (X.residuePointMap B hZ s) (fun y => (hr y).symm ▸ hs)
  have hrU : rU ≫ Space.openSubHom X.base U = X.residuePointMap B hZ s :=
    Space.openSubLift_comp_openSubHom _ _ _ _
  have hy : yoneda.map rU ≫ yoneda.map (Space.openSubHom X.base U) =
      yoneda.map (X.residuePointMap B hZ s) :=
    (yoneda.map_comp _ _).symm.trans (congrArg yoneda.map hrU)
  have hpb := AlgebraicSpaces.isPullback_hom B integerBase hZ h
  have := mono_schemeSpaceMap_openSubHom X U
  have : Mono (schemeSpaceMap (Space.openSubHom X.base U)).hom :=
    inferInstanceAs (Mono ((ObjectProperty.ι _).map (schemeSpaceMap (Space.openSubHom X.base U))))
  have hq₁' : q₁ ≫ f₁.hom = yoneda.map v ≫ yoneda.map rU := by
    refine (cancel_mono (schemeSpaceMap (Space.openSubHom X.base U)).hom).1 ?_
    refine (Category.assoc _ _ _).trans ?_
    refine ((congrArg (q₁ ≫ ·) hpb.w).symm.trans ?_)
    refine (Category.assoc _ _ _).symm.trans ?_
    rw [hq₁, hq.w]
    exact (congrArg (yoneda.map v ≫ ·) hy).symm.trans (Category.assoc _ _ _).symm
  have hV₁ : IsPullback q₁ (yoneda.map v) f₁.hom (yoneda.map rU) := by
    refine IsPullback.of_right ?_ hq₁' hpb
    rw [hq₁]
    exact (congrArg (IsPullback q (yoneda.map v) X.toBase.hom) hy).mpr hq
  have hsq : IsPullback (ObjectProperty.homMk q₁ : schemeSpace V ⟶ X₁) (schemeSpaceMap v) f₁
      (schemeSpaceMap rU) :=
    Space.isPullback_homMk B integerBase hZ X₁.property
      (isAlgebraicSpace_yoneda B integerBase hZ _) (isAlgebraicSpace_yoneda B integerBase hZ _)
      (isAlgebraicSpace_yoneda B integerBase hZ _) hV₁
  obtain ⟨e⟩ := nonempty_quasicoherentDerivedModulePullback_relativeDualizingComplexOver_iso
    X hU h rU v _ hsq
  let := HasDerivedCategory.standard (Space.Modules.{u, u} B integerBase hZ X₁.1 X₁.2)
  let := HasDerivedCategory.standard
    (Space.Modules.{u, u} B integerBase hZ (schemeSpace V).1 (schemeSpace V).2)
  let := HasDerivedCategory.standard (Space.Modules.{u, u} B integerBase hZ (yoneda.obj V)
    (isAlgebraicSpace_yoneda B integerBase hZ V))
  have : IsProper ((BigFppfOver.toScheme B integerBase hZ).map v) := hq.isProper
  obtain ⟨top⟩ := Space.nonempty_homology_smallEtaleDerivedModulePullback_iso_of_isLE
    (ObjectProperty.homMk q₁ : schemeSpace V ⟶ X₁) _ (-1)
    (isLE_relativeDualizingComplexOver X hX hU h)
  exact ⟨Space.restrictToChartSchemeMapIso B integerBase hZ
        (isAlgebraicSpace_yoneda B integerBase hZ V)
        (top.symm ≪≫
          (DerivedCategory.homologyFunctor (Space.Modules.{u, u} B integerBase hZ (yoneda.obj V)
            (isAlgebraicSpace_yoneda B integerBase hZ V)) (-1)).mapIso
            ((ObjectProperty.ι _).mapIso e))
        (Space.idEtaleChart B integerBase hZ V) ≪≫
      Space.restrictToChartSchemeAffineRelativeDualizingSheafIso B.contains_terminal v
        (isFinitePresentation_schemeSpaceMap_of_isPullback X h hsq)⟩

/-- Let `f : X → S` be a prestable family of curves of genus `g ≥ 2` (genus `g` read as in
Stacks 0E6V: `R¹f_*𝒪_X` finite locally free of rank `g`) and let `s ∈ S`. The following are
equivalent:

1. the fibre `X_s` has no rational tail and no rational bridge (Stacks 0E3H, 0E3M); the fibre is
   presented by a scheme `V` of the site with a cartesian square over `Spec κ(s) → S`, as in
   Stacks 0E75;
2. for some affine open `U ∋ s`, the relative dualizing sheaf `ω_{f⁻¹(U)/U}`
   (`AlgebraicGeometry.CurveFamily.relativeDualizingSheafOver`) is ample on `f⁻¹(U)` relative to
   `U`, for every presentation `X₁ = f⁻¹(U)` of the restricted family by a cartesian square. -/
@[stacks 0E74]
theorem hasNoRationalTailNoRationalBridge_iff_exists_isAffineOpen_isRelativelyAmple
    (X : CurveFamily B hZ) (hX : IsPrestableCurveFamily B hZ X) (g : ℕ)
    (hgen : CurveFamily.HasGenus B hZ X g) (hg : 2 ≤ g)
    (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base) :
    (∃ (V : BigFppfOver B integerBase hZ) (v : V ⟶ X.residuePoint B hZ s)
        (q : yoneda.obj V ⟶ X.total.obj),
        X.IsFibrePresentation B hZ s v q ∧
          HasNoRationalTailNoRationalBridge
            (((BigFppfOver.toScheme B integerBase hZ).obj X.base).residueField s)
            (X.fibreMap B hZ s v)) ↔
      ∃ U : ((BigFppfOver.toScheme B integerBase hZ).obj X.base).Opens,
        ∃ hU : IsAffineOpen U, s ∈ U ∧
        ∀ ⦃X₁ : AlgebraicSpaces B integerBase hZ⦄ (p₁ : X₁ ⟶ X.total)
          (f₁ : X₁ ⟶ schemeSpace (Space.openSub X.base U))
          (h : IsPullback p₁ f₁ X.toBase (schemeSpaceMap (Space.openSubHom X.base U))),
            Space.IsRelativelyAmple B integerBase hZ f₁ (X.relativeDualizingSheafOver hU h) := by
  have hbasis : ∀ {W : ((BigFppfOver.toScheme B integerBase hZ).obj X.base).Opens} {x}, x ∈ W →
      ∃ W' ∈ ((BigFppfOver.toScheme B integerBase hZ).obj X.base).affineOpens, x ∈ W' ∧ W' ≤ W :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens _)
  constructor
  · rintro ⟨V, v, q, h, hno⟩
    obtain ⟨U₀, hU₀, hsU₀, -⟩ := hbasis (W := ⊤) (Set.mem_univ s)
    have sq₀ := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ X.toBase
      (schemeSpaceMap (Space.openSubHom X.base U₀))
    obtain ⟨U', hU'U₀, hamp, hfib⟩ := exists_opens_isRelativelyAmple_iff_of_isPullback_openSub X hX
      g (hasFibreGenus_of_hasGenus hX hgen) hg U₀ sq₀ (X.relativeDualizingSheafOver hU₀ sq₀)
      (isInvertible_relativeDualizingSheafOver X hX hU₀ sq₀)
      (fun _ hs _ _ _ h q₁ hq₁ =>
        nonempty_baseChangeModule_relativeDualizingSheafOver_iso X hX hU₀ sq₀ hs h q₁ hq₁)
    have hsU' : s ∈ U' := (hfib s hsU₀).1 ⟨V, v, q, h, hno⟩
    obtain ⟨U'', hU'', hsU'', hU''U'⟩ := hbasis hsU'
    refine ⟨U'', hU'', hsU'', fun X₂ p₂ f₂ h₂ => ?_⟩
    obtain ⟨t, ht, hst⟩ := exists_openSubHom_factor X (hU''U'.trans hU'U₀)
    let qq := sq₀.lift p₂ (f₂ ≫ schemeSpaceMap t) (by rw [Category.assoc, hst]; exact h₂.w)
    have hqq₁ : qq ≫ _ = p₂ := sq₀.lift_fst _ _ _
    have hqq₂ : qq ≫ _ = f₂ ≫ schemeSpaceMap t := sq₀.lift_snd _ _ _
    have hsq := IsPullback.of_right (by rw [hqq₁, hst]; exact h₂) hqq₂ sq₀
    have hA := (hamp t qq f₂ hsq).1 (fun y => by
      rw [ht]
      exact hU''U' (toScheme_map_openSubHom_mem X U'' y))
    obtain ⟨e⟩ := nonempty_relativeDualizingSheafOver_iso_modulePullback X hU₀ hU''
      (hU''U'.trans hU'U₀) sq₀ h₂ qq hqq₁
    exact (Space.isRelativelyAmple_congr f₂ e).mpr hA
  · rintro ⟨U, hU, hsU, hamp⟩
    have sq₀ := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ X.toBase
      (schemeSpaceMap (Space.openSubHom X.base U))
    obtain ⟨U', -, hampiff, hfib⟩ := exists_opens_isRelativelyAmple_iff_of_isPullback_openSub X hX
      g (hasFibreGenus_of_hasGenus hX hgen) hg U sq₀ (X.relativeDualizingSheafOver hU sq₀)
      (isInvertible_relativeDualizingSheafOver X hX hU sq₀)
      (fun _ hs _ _ _ h q₁ hq₁ =>
        nonempty_baseChangeModule_relativeDualizingSheafOver_iso X hX hU sq₀ hs h q₁ hq₁)
    refine (hfib s hsU).2 ?_
    have hid : ∀ {X₁ : AlgebraicSpaces B integerBase hZ}
        (k : X₁ ⟶ schemeSpace (Space.openSub X.base U)),
        IsPullback (𝟙 X₁) k k (schemeSpaceMap (𝟙 (Space.openSub X.base U))) := by
      intro X₁ k
      have : schemeSpaceMap (𝟙 (Space.openSub X.base U)) = 𝟙 _ :=
        ObjectProperty.hom_ext _ (yoneda.map_id _)
      rw [this]
      exact IsPullback.id_horiz k
    have hall := (hampiff (𝟙 _) (𝟙 _) _ (hid _)).2
      ((Space.isRelativelyAmple_congr _
        ((Space.modulePullbackIdIso B integerBase hZ _).app _).symm).mp (hamp _ _ sq₀))
    have hy := hall ⟨s, hsU⟩
    rwa [Category.id_comp, Space.toScheme_map_openSubHom] at hy

end CurveFamily

end AlgebraicGeometry

end
