module

public import StacksFrontier.AlgebraicGeometry.Quot.StableFamilyDualizingAmple
public import StacksFrontier.AlgebraicGeometry.Quot.UniversalStructureContractionOpenOfCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ProperLimitOfFinitePresentationEmbedding

/-!
# An étale scheme chart from an invertible module ample on a fibre

Let `f : X ⟶ U` be a proper morphism from an algebraic space to a scheme of the site, `L` an
invertible `𝒪_X`-module and `u ∈ U` a point whose fibre `X_u` is a scheme (a cartesian square over
`Spec κ(u) ⟶ U`) on which `L` is ample. By Stacks 0D3D there is an open subspace of `U` through
which a base change of `f` factors exactly when the pullback of `L` is ample on it (Stacks 0D31);
the fibre over `u` is such a base change (Stacks 0D32 and 01VK), so `u` lies in the corresponding
open `O ⊆ U`, and over `O` the pullback of `L` is relatively ample, which makes `f⁻¹(O)` a scheme
(Stacks 0D32).

For a family of curves `X ⟶ S` (towards Stacks 0E6F): if after an étale base change `U ⟶ S`
through `s` there is an invertible module on `X_U` ample on the fibre over a point `u` over `s`,
then the family has an étale scheme chart at `s`
(`AlgebraicGeometry.CurveFamily.HasEtaleSchemeChartAt`).

## Main results

* `AlgebraicGeometry.Space.isRelativelyAmple_residueField_of_isAmple_baseChangeModule`: ampleness
  on a scheme fibre, read through Stacks 0D31 on the fibre square.
* `AlgebraicGeometry.Space.exists_mem_isRelativelyAmple_openSub_of_isAmple_fibre`: Stacks 0D3A
  without the Noetherian hypothesis, from Stacks 0D3D.
* `AlgebraicGeometry.Space.exists_mem_isPullback_yoneda_of_isAmple_fibre`: over an open
  neighbourhood of `u` the base change of `f` is a scheme.
* `AlgebraicGeometry.CurveFamily.hasEtaleSchemeChartAt_of_isAmple_fibre`: an étale scheme chart
  of a family of curves at `s` from such a module after an étale base change.

Each of the four is also stated, with the suffix `_of_isAffine`, for the base change along any
morphism `r : F ⟶ U` from a nonempty affine scheme of the site all of whose points map to `u` (for
instance a field-valued point through `u` other than `Spec κ(u)`).

## References

* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
* [Stacks Project, Tag 0D32](https://stacks.math.columbia.edu/tag/0D32)
* [Stacks Project, Tag 0D3A](https://stacks.math.columbia.edu/tag/0D3A)
* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "𝒯" => BigFppfOver.toScheme B S hS

/-- **Ampleness over an affine base, read through Stacks 0D31.** Let `X` be an algebraic space,
`L` an invertible `𝒪_X`-module, `j : V ⟶ X` a morphism from a scheme of the site and `v : V ⟶ F`
a morphism to an affine scheme of the site. If the reading of `L` on `V` is ample, then the
pullback of `L` to `V` is ample relative to `V ⟶ F` in the sense of algebraic spaces
(Stacks 0D32, 01VK). -/
theorem isRelativelyAmple_of_isAmple_baseChangeModule_of_isAffine {V F : BigFppfOver B S hS}
    {X : AlgebraicSpaces B S hS} (L : Modules.{u, u} B S hS X.1 X.2)
    (hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property
        L)
    (j : yoneda.obj V ⟶ X.1) (v : V ⟶ F) [IsAffine ((𝒯).obj F)]
    (hamp : ∃ hL : Stacks.Ample.IsInvertibleModule ((𝒯).obj V) (baseChangeModule B S hS L V j),
      @Stacks.Ample.IsAmple _ _ hL) :
    IsRelativelyAmple B S hS (schemeSpaceMap v)
      ((modulePullback B S hS (ObjectProperty.homMk j : schemeSpace V ⟶ X)).obj L) := by
  obtain ⟨hLV, hampV⟩ := hamp
  let L' := (modulePullback B S hS (ObjectProperty.homMk j : schemeSpace V ⟶ X)).obj L
  let E : baseChangeModule B S hS L' V (𝟙 _) ≅ baseChangeModule B S hS L V j :=
    (baseChangeModuleCompIso B S hS (ObjectProperty.homMk j : schemeSpace V ⟶ X) L V (𝟙 _)).symm ≪≫
      eqToIso (congrArg (baseChangeModule B S hS L V) (Category.id_comp j))
  have hL'inv : Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B S hS (schemeSpace V).1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (schemeSpace V).1 (schemeSpace V).2).O)).property L' :=
    Stacks.SheafOfModules.isInvertible_pullbackModules_obj
      (f := smallEtaleRingedToposModulesHom B S hS
        (ObjectProperty.homMk j : schemeSpace V ⟶ X)) (L := L) (hL := hL)
  have := hLV
  refine isRelativelyAmple_of_exists_scheme _ L' hL'inv _ (Iso.refl _)
    ⟨V, Iso.refl _, Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ E.symm, ?_⟩
  have h1 := (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple ((𝒯).map v) _).mpr
    hampV
  have : Stacks.Ample.IsInvertibleModule _ (baseChangeModule B S hS L' V (𝟙 _)) :=
    Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ E.symm
  have h2 := (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ E).mpr h1
  convert h2 using 2 <;> first
    | rfl
    | (apply yoneda.map_injective
       simp only [Functor.map_preimage, Iso.refl_hom, schemeSpaceMap_hom]
       exact (Category.id_comp _).trans (Category.comp_id _))

/-- **Ampleness on a scheme fibre, read through Stacks 0D31.** Let `f : X ⟶ U` be a morphism
from an algebraic space to a scheme of the site, `L` an invertible `𝒪_X`-module and `u ∈ U` a
point whose fibre is the scheme `V`, through the cartesian square `hsq` over
`Spec κ(u) ⟶ U`. If the reading of `L` on `V` is ample, then the pullback of `L` to `V` is ample
relative to `V ⟶ Spec κ(u)` in the sense of algebraic spaces (Stacks 0D32, 01VK). -/
theorem isRelativelyAmple_residueField_of_isAmple_baseChangeModule {U V : BigFppfOver B S hS}
    {X : AlgebraicSpaces B S hS} (L : Modules.{u, u} B S hS X.1 X.2)
    (hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property
        L)
    (u : (𝒯).obj U) (j : yoneda.obj V ⟶ X.1)
    (v : V ⟶ residueFieldObject B S hS U u (B.residueField_spec_contains U.left.property u))
    (hamp : ∃ hL : Stacks.Ample.IsInvertibleModule ((𝒯).obj V) (baseChangeModule B S hS L V j),
      @Stacks.Ample.IsAmple _ _ hL) :
    IsRelativelyAmple B S hS (schemeSpaceMap v)
      ((modulePullback B S hS (ObjectProperty.homMk j : schemeSpace V ⟶ X)).obj L) := by
  have : IsAffine ((𝒯).obj
      (residueFieldObject B S hS U u (B.residueField_spec_contains U.left.property u))) :=
    inferInstanceAs (IsAffine (Spec _))
  exact isRelativelyAmple_of_isAmple_baseChangeModule_of_isAffine L hL j v hamp

/-- **Stacks 0D3A without the Noetherian hypothesis, from Stacks 0D3D, at an affine point.** Let
`f : X ⟶ U` be a proper morphism from an algebraic space to a scheme of the site, `L` an
invertible `𝒪_X`-module, `r : F ⟶ U` a morphism from a nonempty affine scheme of the site all of
whose points map to `u ∈ U` (for instance a field-valued point through `u`), and `V` a scheme
presenting the base change of `f` along `r` (the cartesian square `hsq`) on which the reading of
`L` is ample. Then there is an open neighbourhood `O` of `u` such that the pullback of `L` is
ample on every base change of `f` along `O ⟶ U`. -/
theorem exists_mem_isRelativelyAmple_openSub_of_isAmple_fibre_of_isAffine
    {U V F : BigFppfOver B S hS}
    {X : AlgebraicSpaces B S hS} (f : X ⟶ representedAlgebraicSpace B S hS U)
    (hf : IsProper B S hS f.hom) (L : Modules.{u, u} B S hS X.1 X.2)
    (hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property
        L)
    (u : (𝒯).obj U) (j : yoneda.obj V ⟶ X.1) (v : V ⟶ F) (r : F ⟶ U) [IsAffine ((𝒯).obj F)]
    (y₀ : (𝒯).obj F) (hr : ∀ y, (𝒯).map r y = u)
    (hsq : IsPullback j (yoneda.map v) f.hom (yoneda.map r))
    (hamp : ∃ hL : Stacks.Ample.IsInvertibleModule ((𝒯).obj V) (baseChangeModule B S hS L V j),
      @Stacks.Ample.IsAmple _ _ hL) :
    ∃ O : ((𝒯).obj U).Opens, u ∈ O ∧
      ∀ ⦃X₁ : AlgebraicSpaces B S hS⦄ (p₁ : X₁ ⟶ X)
        (f₁ : X₁ ⟶ schemeSpace (openSub U O)),
        IsPullback p₁ f₁ f (schemeSpaceMap (openSubHom U O)) →
        IsRelativelyAmple B S hS f₁ ((modulePullback B S hS p₁).obj L) := by
  obtain ⟨W, hW, hiff⟩ :=
    exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_isProper B S hS hf hL
  have hsq' : IsPullback (ObjectProperty.homMk j : schemeSpace V ⟶ X) (schemeSpaceMap v) f
      (schemeSpaceMap r) :=
    isPullback_homMk B S hS X.property (isAlgebraicSpace_yoneda B S hS _)
      (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _) hsq
  have hrW := (hiff (schemeSpaceMap r) _ _ hsq').2
    (isRelativelyAmple_of_isAmple_baseChangeModule_of_isAffine L hL j v hamp)
  have hmem : ∀ {T : BigFppfOver B S hS} (x : T ⟶ U),
      (∃ l : (schemeSpace T).1 ⟶ W.toFunctor, l ≫ W.ι = (schemeSpaceMap x).hom) ↔
        ∀ y, ((𝒯).map x) y ∈ opensOfOpenSubspace B S hS U W hW := by
    intro T x
    refine (FinitePartUniversalOpen.exists_lift_iff_mem (X := yoneda.obj U) W T
      (yoneda.map x)).trans ?_
    rw [yonedaEquiv_yoneda_map]
    exact mem_iff_of_isOpenSubspace B S hS U W hW x
  have hι : ∀ (O : ((𝒯).obj U).Opens) y, ((𝒯).map (openSubHom U O)) y ∈ O := by
    intro O y
    rw [toScheme_map_openSubHom]
    have hy := Set.mem_range_self (f := O.ι) y
    rwa [Scheme.Opens.range_ι] at hy
  have hu := (hmem r).1 hrW y₀
  rw [hr] at hu
  exact ⟨opensOfOpenSubspace B S hS U W hW, hu, fun X₁ p₁ f₁ hsq₁ =>
    (hiff _ p₁ f₁ hsq₁).1 ((hmem (openSubHom U _)).2 (hι _))⟩

/-- **Stacks 0D3A without the Noetherian hypothesis, from Stacks 0D3D.** Let `f : X ⟶ U` be a
proper morphism from an algebraic space to a scheme of the site, `L` an invertible `𝒪_X`-module
and `u ∈ U` a point whose fibre is a scheme `V` (the cartesian square `hsq` over
`Spec κ(u) ⟶ U`) on which the reading of `L` is ample. Then there is an open neighbourhood `O` of
`u` such that the pullback of `L` is ample on every base change of `f` along `O ⟶ U`. -/
theorem exists_mem_isRelativelyAmple_openSub_of_isAmple_fibre {U V : BigFppfOver B S hS}
    {X : AlgebraicSpaces B S hS} (f : X ⟶ representedAlgebraicSpace B S hS U)
    (hf : IsProper B S hS f.hom) (L : Modules.{u, u} B S hS X.1 X.2)
    (hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property
        L)
    (u : (𝒯).obj U) (j : yoneda.obj V ⟶ X.1)
    (v : V ⟶ residueFieldObject B S hS U u (B.residueField_spec_contains U.left.property u))
    (hsq : IsPullback j (yoneda.map v) f.hom
      (yoneda.map (residueFieldMap B S hS U u (B.residueField_spec_contains U.left.property u))))
    (hamp : ∃ hL : Stacks.Ample.IsInvertibleModule ((𝒯).obj V) (baseChangeModule B S hS L V j),
      @Stacks.Ample.IsAmple _ _ hL) :
    ∃ O : ((𝒯).obj U).Opens, u ∈ O ∧
      ∀ ⦃X₁ : AlgebraicSpaces B S hS⦄ (p₁ : X₁ ⟶ X)
        (f₁ : X₁ ⟶ schemeSpace (openSub U O)),
        IsPullback p₁ f₁ f (schemeSpaceMap (openSubHom U O)) →
        IsRelativelyAmple B S hS f₁ ((modulePullback B S hS p₁).obj L) := by
  have : IsAffine ((𝒯).obj
      (residueFieldObject B S hS U u (B.residueField_spec_contains U.left.property u))) :=
    inferInstanceAs (IsAffine (Spec _))
  obtain ⟨y₀⟩ : Nonempty ((𝒯).obj
      (residueFieldObject B S hS U u (B.residueField_spec_contains U.left.property u))) :=
    inferInstanceAs (Nonempty (Spec _))
  exact exists_mem_isRelativelyAmple_openSub_of_isAmple_fibre_of_isAffine f hf L hL u j v
    (residueFieldMap B S hS U u (B.residueField_spec_contains U.left.property u)) y₀
    (fun y => Scheme.fromSpecResidueField_apply _ _) hsq hamp

/-- **Near a fibre on which an invertible module is ample, a proper algebraic space over a scheme
is a scheme.** In the situation of
`AlgebraicGeometry.Space.exists_mem_isRelativelyAmple_openSub_of_isAmple_fibre_of_isAffine`, there
are an open neighbourhood `O` of `u` and a scheme `Z` of the site with a cartesian square
exhibiting `yoneda Z` as the base change of `f` along `O ⟶ U` (Stacks 0D32). -/
theorem exists_mem_isPullback_yoneda_of_isAmple_fibre_of_isAffine
    {U V F : BigFppfOver B S hS}
    {X : AlgebraicSpaces B S hS} (f : X ⟶ representedAlgebraicSpace B S hS U)
    (hf : IsProper B S hS f.hom) (L : Modules.{u, u} B S hS X.1 X.2)
    (hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property
        L)
    (u : (𝒯).obj U) (j : yoneda.obj V ⟶ X.1) (v : V ⟶ F) (r : F ⟶ U) [IsAffine ((𝒯).obj F)]
    (y₀ : (𝒯).obj F) (hr : ∀ y, (𝒯).map r y = u)
    (hsq : IsPullback j (yoneda.map v) f.hom (yoneda.map r))
    (hamp : ∃ hL : Stacks.Ample.IsInvertibleModule ((𝒯).obj V) (baseChangeModule B S hS L V j),
      @Stacks.Ample.IsAmple _ _ hL) :
    ∃ O : ((𝒯).obj U).Opens, u ∈ O ∧
      ∃ (Z : BigFppfOver B S hS) (p : yoneda.obj Z ⟶ X.1) (q : Z ⟶ openSub U O),
        IsPullback p (yoneda.map q) f.hom (yoneda.map (openSubHom U O)) := by
  obtain ⟨O, huO, hO⟩ :=
    exists_mem_isRelativelyAmple_openSub_of_isAmple_fibre_of_isAffine f hf L hL u j v r y₀ hr hsq
      hamp
  have sq₁ := AlgebraicSpaces.isPullback_fiberProduct B S hS f (schemeSpaceMap (openSubHom U O))
  obtain ⟨Z, eX, -, -⟩ := (hO _ _ sq₁).exists_scheme (openSub U O) (Iso.refl _)
  let F := AlgebraicSpaces.fiberProduct B S hS f (schemeSpaceMap (openSubHom U O))
  let fst : F ⟶ X := ObjectProperty.homMk (pullback.fst f.hom (schemeSpaceMap (openSubHom U O)).hom)
  let snd : F ⟶ schemeSpace (openSub U O) :=
    ObjectProperty.homMk (pullback.snd f.hom (schemeSpaceMap (openSubHom U O)).hom)
  let q : Z ⟶ openSub U O := yoneda.preimage (eX.hom ≫ snd.hom)
  have hq : yoneda.map q = eX.hom ≫ snd.hom := yoneda.map_preimage _
  refine ⟨O, huO, Z, eX.hom ≫ fst.hom, q, ?_⟩
  refine (AlgebraicSpaces.isPullback_hom B S hS sq₁).of_iso eX.symm (Iso.refl _) (Iso.refl _)
    (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [fst]
  · simp only [Iso.symm_hom, hq]
    exact (Category.comp_id _).trans (Iso.inv_hom_id_assoc eX _).symm
  · simp
  · exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- **Near a fibre on which an invertible module is ample, a proper algebraic space over a scheme
is a scheme.** In the situation of
`AlgebraicGeometry.Space.exists_mem_isRelativelyAmple_openSub_of_isAmple_fibre`, there are an
open neighbourhood `O` of `u` and a scheme `Z` of the site with a cartesian square exhibiting
`yoneda Z` as the base change of `f` along `O ⟶ U` (Stacks 0D32). -/
theorem exists_mem_isPullback_yoneda_of_isAmple_fibre {U V : BigFppfOver B S hS}
    {X : AlgebraicSpaces B S hS} (f : X ⟶ representedAlgebraicSpace B S hS U)
    (hf : IsProper B S hS f.hom) (L : Modules.{u, u} B S hS X.1 X.2)
    (hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property
        L)
    (u : (𝒯).obj U) (j : yoneda.obj V ⟶ X.1)
    (v : V ⟶ residueFieldObject B S hS U u (B.residueField_spec_contains U.left.property u))
    (hsq : IsPullback j (yoneda.map v) f.hom
      (yoneda.map (residueFieldMap B S hS U u (B.residueField_spec_contains U.left.property u))))
    (hamp : ∃ hL : Stacks.Ample.IsInvertibleModule ((𝒯).obj V) (baseChangeModule B S hS L V j),
      @Stacks.Ample.IsAmple _ _ hL) :
    ∃ O : ((𝒯).obj U).Opens, u ∈ O ∧
      ∃ (Z : BigFppfOver B S hS) (p : yoneda.obj Z ⟶ X.1) (q : Z ⟶ openSub U O),
        IsPullback p (yoneda.map q) f.hom (yoneda.map (openSubHom U O)) := by
  have : IsAffine ((𝒯).obj
      (residueFieldObject B S hS U u (B.residueField_spec_contains U.left.property u))) :=
    inferInstanceAs (IsAffine (Spec _))
  obtain ⟨y₀⟩ : Nonempty ((𝒯).obj
      (residueFieldObject B S hS U u (B.residueField_spec_contains U.left.property u))) :=
    inferInstanceAs (Nonempty (Spec _))
  exact exists_mem_isPullback_yoneda_of_isAmple_fibre_of_isAffine f hf L hL u j v
    (residueFieldMap B S hS U u (B.residueField_spec_contains U.left.property u)) y₀
    (fun y => Scheme.fromSpecResidueField_apply _ _) hsq hamp

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- **An étale scheme chart from a module ample on a fibre after an étale base change.** Let
`X ⟶ S` be a family of curves, `φ : U ⟶ S` an étale morphism of the site and `u ∈ U` a point over
`s ∈ S`, `X_U` a base change of `X` along `φ`, and `L` an invertible module on `X_U` whose reading
on a scheme `V` presenting the base change of `X_U` along `r : F ⟶ U` is ample, where `F` is a
nonempty affine scheme of the site all of whose points map to `u` (for instance a field-valued
point through `u`). Then the family has an étale scheme chart at `s` (the pointwise conclusion of
Stacks 0E6F). -/
theorem hasEtaleSchemeChartAt_of_isAmple_fibre_of_isAffine (X : CurveFamily B hZ)
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
    X.HasEtaleSchemeChartAt ((𝒯).map φ u) := by
  have sqU' := AlgebraicSpaces.isPullback_hom B integerBase hZ sqU
  have hfU : Space.IsProper B integerBase hZ fU.hom :=
    Space.isProper_of_isPullback_presheaf B integerBase hZ XU.2 X.total.2
      (isAlgebraicSpace_yoneda _ _ _ U)
      (isAlgebraicSpace_yoneda _ _ _ X.base) sqU' X.proper
  obtain ⟨O, huO, Z, p, q, sq⟩ :=
    Space.exists_mem_isPullback_yoneda_of_isAmple_fibre_of_isAffine (f := fU) hfU L hL u j v r y₀
      hr hsq hamp
  refine ⟨Space.openSub U O, Space.openSubHom U O ≫ φ, ⟨u, huO⟩, ?_, ?_, Z,
    ObjectProperty.homMk (p ≫ qU.hom), q, ?_⟩
  · rw [Functor.map_comp, Space.toScheme_map_openSubHom]
    exact MorphismProperty.comp_mem @Etale _ _ (inferInstance : Etale O.ι) hφ
  · rw [Functor.map_comp, Space.toScheme_map_openSubHom]; rfl
  · refine Space.isPullback_homMk B integerBase hZ X.total.property
      (isAlgebraicSpace_yoneda _ _ _ _) (isAlgebraicSpace_yoneda _ _ _ _)
      (isAlgebraicSpace_yoneda _ _ _ _) ?_
    rw [Functor.map_comp]
    exact sq.paste_horiz sqU'

/-- **An étale scheme chart from a module ample on a fibre after an étale base change.** Let
`X ⟶ S` be a family of curves, `φ : U ⟶ S` an étale morphism of the site and `u ∈ U` a point over
`s ∈ S`, `X_U` a base change of `X` along `φ`, and `L` an invertible module on `X_U` whose reading
on a scheme presentation `V` of the fibre of `X_U` over `u` is ample. Then the family has an étale
scheme chart at `s` (the pointwise conclusion of Stacks 0E6F). -/
theorem hasEtaleSchemeChartAt_of_isAmple_fibre (X : CurveFamily B hZ)
    {U V : BigFppfOver B integerBase hZ}
    (φ : U ⟶ X.base) (hφ : Etale ((𝒯).map φ)) (u : (𝒯).obj U)
    {XU : AlgebraicSpaces B integerBase hZ} (qU : XU ⟶ X.total) (fU : XU ⟶ schemeSpace U)
    (sqU : IsPullback qU fU X.toBase (schemeSpaceMap φ))
    (L : Space.Modules.{u, u} B integerBase hZ XU.1 XU.2)
    (hL : Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase hZ XU.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase hZ XU.1 XU.2).O)).property L)
    (j : yoneda.obj V ⟶ XU.1)
    (v : V ⟶ Space.residueFieldObject B integerBase hZ U u
      (B.residueField_spec_contains U.left.property u))
    (hsq : IsPullback j (yoneda.map v) fU.hom
      (yoneda.map (Space.residueFieldMap B integerBase hZ U u
        (B.residueField_spec_contains U.left.property u))))
    (hamp : ∃ hL : Stacks.Ample.IsInvertibleModule ((𝒯).obj V)
        (Space.baseChangeModule B integerBase hZ L V j),
      @Stacks.Ample.IsAmple _ _ hL) :
    X.HasEtaleSchemeChartAt ((𝒯).map φ u) := by
  have : IsAffine ((𝒯).obj (Space.residueFieldObject B integerBase hZ U u
      (B.residueField_spec_contains U.left.property u))) :=
    inferInstanceAs (IsAffine (Spec _))
  obtain ⟨y₀⟩ : Nonempty ((𝒯).obj (Space.residueFieldObject B integerBase hZ U u
      (B.residueField_spec_contains U.left.property u))) :=
    inferInstanceAs (Nonempty (Spec _))
  exact hasEtaleSchemeChartAt_of_isAmple_fibre_of_isAffine X φ hφ u qU fU sqU L hL j v
    (Space.residueFieldMap B integerBase hZ U u (B.residueField_spec_contains U.left.property u))
    y₀ (fun y => Scheme.fromSpecResidueField_apply _ _) hsq hamp

end AlgebraicGeometry.CurveFamily

end
