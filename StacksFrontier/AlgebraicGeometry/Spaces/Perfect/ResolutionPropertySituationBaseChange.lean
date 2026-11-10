module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescentLocus.CokernelSupportImage
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleAffineBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleAffinePushforwardExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafPullbackComparisonUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyIdealDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PullbackIdealImage
public import StacksFrontier.AlgebraicGeometry.Spaces.PullbackIdealImageZeroLocus
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPullbackStability
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedFiniteTypeOnCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Base change of the situation of Stacks 0GUY along an affine morphism

Let `X` be a quasi-compact and quasi-separated algebraic space over `S` with the choices of the
situation of Stacks 0GUY: an affine scheme `V` with a surjective étale `φ : V ⟶ X`, factored as
an open immersion `j : V ⟶ Y` followed by a finite `π : Y ⟶ X`, and a finite type
quasi-coherent sheaf of ideals `ℐ ⊆ 𝒪_Y` with `|V(ℐ)| = |Y| ∖ |j(V)|`.  For an affine morphism
`q : X' ⟶ X` from a quasi-compact and quasi-separated algebraic space, the base change of these
choices along `q` is again such a situation on `X'`: `V' = V ×_X X'` is affine because `q` is,
`Y' = Y ×_X X'` with the base changes of `j` and `π`, and the inverse-image ideal `q'⁻¹ℐ · 𝒪_{Y'}`.

## Main results

* `AlgebraicGeometry.Space.ResolutionPropertyDescentSituation.exists_baseChange`: the base
  change of the situation along an affine morphism, together with the cartesian square of `π`
  and the description of the new ideal as the inverse-image ideal.

## References

* [Stacks Project, Tag 0GUY](https://stacks.math.columbia.edu/tag/0GUY)
* [Stacks Project, Tag 0GV2](https://stacks.math.columbia.edu/tag/0GV2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_ResolutionPropertySituationBaseChange
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **The points of one leg of a cartesian square of algebraic spaces are the preimage of the
points of the opposite leg.** -/
theorem preimage_range_pointsMap_of_isPullback' {P X Y Z : AlgebraicSpaces B S hS}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (sq : IsPullback a b f g) :
    pointsMap B S hS Y.1 g.hom ⁻¹' Set.range (pointsMap B S hS X.1 f.hom) =
      Set.range (pointsMap B S hS P.1 b.hom) := by
  ext y
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨w, -, hw⟩ := exists_point_of_isPullback B S hS sq x y hx
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    refine ⟨pointsMap B S hS P.1 a.hom w, ?_⟩
    change (pointsMap B S hS X.1 f.hom ∘ pointsMap B S hS P.1 a.hom) w =
      (pointsMap B S hS Y.1 g.hom ∘ pointsMap B S hS P.1 b.hom) w
    rw [← pointsMap_comp, ← pointsMap_comp, ← ObjectProperty.FullSubcategory.comp_hom,
      ← ObjectProperty.FullSubcategory.comp_hom, sq.w]

namespace ResolutionPropertyDescentSituation

variable (hZ : B.Contains (⊤_ Scheme.{u}))

attribute [local instance] pointTopology

/-- **The base change of the situation of Stacks 0GUY along an affine morphism.**  Let
`q : X' ⟶ X` be an affine morphism of quasi-compact and quasi-separated algebraic spaces and
let `sit` be the situation of Stacks 0GUY on `X`.  Then there are a situation `sit'` on `X'` and
a morphism `q' : Y' ⟶ Y` making the square of `π' : Y' ⟶ X'` and `π : Y ⟶ X` cartesian, whose
ideal is the inverse-image ideal `q'⁻¹ℐ · 𝒪_{Y'}`.

The hypotheses `hI` and `hzero` say that, along every morphism into `Y`, the inverse-image ideal
of `ℐ` is quasi-coherent of finite type and its zero locus is the preimage of that of `ℐ`. -/
theorem exists_baseChange {X X' : AlgebraicSpaces B S hS}
    {hqc : IsQuasiCompactSpace B S hS X.1} {hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1}
    (sit : ResolutionPropertyDescentSituation B S hS hZ X hqc hqs)
    (q : X' ⟶ X) (hq : IsAffineHom B S hS q.hom)
    (hqc' : IsQuasiCompactSpace B S hS X'.1) (hqs' : IsAbsolutelyQuasiSeparated B S hS hZ X'.1)
    (hI : ∀ {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ sit.Y),
      IsFiniteTypeQuasicoherentIdeal B S hS Y' (pullbackIdealImage B S hS g sit.I))
    (hzero : ∀ {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ sit.Y),
      idealZeroLocus B S hS Y' (pullbackIdealImage B S hS g sit.I) =
        pointsMap B S hS Y'.1 g.hom ⁻¹' idealZeroLocus B S hS sit.Y sit.I) :
    ∃ (sit' : ResolutionPropertyDescentSituation B S hS hZ X' hqc' hqs') (q' : sit'.Y ⟶ sit.Y),
      IsPullback q' (πHom B S hS hZ sit') (πHom B S hS hZ sit) q ∧
        sit'.I = pullbackIdealImage B S hS q' sit.I := by
  obtain ⟨W, p, r, sqV⟩ := hq ⟨sit.V, sit.isAffine_V⟩ sit.φ
  let Y' : AlgebraicSpaces B S hS := AlgebraicSpaces.fiberProduct B S hS q (πHom B S hS hZ sit)
  have sqY := AlgebraicSpaces.isPullback_fiberProduct B S hS q (πHom B S hS hZ sit)
  let π' : Y' ⟶ X' := ObjectProperty.homMk (pullback.fst q.hom sit.π)
  let q' : Y' ⟶ sit.Y := ObjectProperty.homMk (pullback.snd q.hom sit.π)
  have sqYh : IsPullback π'.hom q'.hom q.hom sit.π := AlgebraicSpaces.isPullback_hom B S hS sqY
  let j' : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W) ⟶ Y'.1 :=
    pullback.lift p (yoneda.map r ≫ sit.j) (by
      rw [sqV.w, Category.assoc]
      exact congrArg (yoneda.map r ≫ ·) sit.comp_eq.symm)
  have hj'π : j' ≫ π'.hom = p := pullback.lift_fst _ _ _
  have hj'q : j' ≫ q'.hom = yoneda.map r ≫ sit.j := pullback.lift_snd _ _ _
  have sqJ : IsPullback (yoneda.map r) j' sit.j q'.hom := by
    refine IsPullback.of_bot ?_ hj'q.symm sqYh.flip
    have h2 : sit.j ≫ sit.π = sit.φ := sit.comp_eq
    rw [hj'π]
    change IsPullback (yoneda.map r) p (sit.j ≫ sit.π) q.hom
    rw [h2]
    exact sqV.flip
  let I' := pullbackIdealImage B S hS q' sit.I
  have hφ' : IsSurjective B S hS p := by
    have sqA : IsPullback (schemeSpaceMap r) (ObjectProperty.homMk p :
        schemeSpace ((BigAffineFppf.inclusion B S hS).obj W) ⟶ X')
        (ObjectProperty.homMk sit.φ : schemeSpace sit.V ⟶ X) q :=
      IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ sqV.w.symm) sqV.flip
    exact isSurjective_of_isPullback B S hS sqA sit.isSurjective_φ
  refine ⟨{
      V := (BigAffineFppf.inclusion B S hS).obj W
      isAffine_V := W.property
      φ := p
      isSurjective_φ := hφ'
      isEtale_φ := isEtale_of_isPullback_yoneda B S hS sqV.flip sit.isEtale_φ
      Y := Y'
      j := j'
      π := π'.hom
      isOpenImmersion_j := (MorphismProperty.relative_isStableUnderBaseChange
        (MorphismProperty.inverseImage
          (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))).of_isPullback sqJ sit.isOpenImmersion_j
      isFinite_π := isFinite_of_isPullback B S hS sqYh.flip sit.isFinite_π
      comp_eq := hj'π
      I := I'
      isFiniteTypeQuasicoherent_I := hI q'
      idealZeroLocus_I := ?_ }, q', sqY.flip, rfl⟩
  rw [hzero q', sit.idealZeroLocus_I, Set.preimage_compl]
  congr 1
  have sqJA : IsPullback (schemeSpaceMap r) (ObjectProperty.homMk j' :
      schemeSpace ((BigAffineFppf.inclusion B S hS).obj W) ⟶ Y')
      (ObjectProperty.homMk sit.j : schemeSpace sit.V ⟶ sit.Y) q' :=
    IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ sqJ.w) sqJ
  exact preimage_range_pointsMap_of_isPullback' sqJA

/-! ### The direct image of `𝒪_Y ⟶ 𝒪_Y/ℐ` -/

section DirectImage

variable {X : AlgebraicSpaces B S hS}
    {hqc : IsQuasiCompactSpace B S hS X.1} {hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1}
    (sit : ResolutionPropertyDescentSituation B S hS hZ X hqc hqs)

/-- The abelian structure on modules, pinned at the universes in use. -/
noncomputable local instance (priority := high) abelianModules_situationBaseChange
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    Abelian (Modules.{u, u} B S hS F hF) :=
  SheafOfModules.instAbelian.{u} _

/-- Zero morphisms of modules, from the pinned abelian structure. -/
noncomputable local instance (priority := high) hasZeroMorphismsModules_situationBaseChange
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    HasZeroMorphisms (Modules.{u, u} B S hS F hF) :=
  letI := abelianModules_situationBaseChange F hF
  inferInstance

/-- Kernels of modules, from the pinned abelian structure. -/
noncomputable local instance (priority := high) hasKernelsModules_situationBaseChange
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    HasKernels (Modules.{u, u} B S hS F hF) :=
  letI := abelianModules_situationBaseChange F hF
  inferInstance

/-- Cokernels of modules, from the pinned abelian structure. -/
noncomputable local instance (priority := high) hasCokernelsModules_situationBaseChange
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    HasCokernels (Modules.{u, u} B S hS F hF) :=
  letI := abelianModules_situationBaseChange F hF
  inferInstance

/-- The abelian structure on modules over the structure sheaf of an algebraic space, pinned at
the universe in use. -/
noncomputable local instance (priority := high) abelianStructureModules_situationBaseChange
    (Y : AlgebraicSpaces B S hS) :
    Abelian (SheafOfModules.{u} (structureRingSheaf B S hS Y)) :=
  SheafOfModules.instAbelian.{u} _

/-- The ideal `ℐ` of the situation, as an `𝒪_Y`-module. -/
noncomputable abbrev idealModule : Modules.{u, u} B S hS sit.Y.1 sit.Y.2 :=
  sit.I.toSheafOfModules

/-- The structure sheaf `𝒪_Y`, as an `𝒪_Y`-module. -/
noncomputable abbrev unitModule : Modules.{u, u} B S hS sit.Y.1 sit.Y.2 :=
  SheafOfModules.unit _

/-- The inclusion `ℐ ⟶ 𝒪_Y` of the ideal of the situation, as a morphism of `𝒪_Y`-modules. -/
noncomputable abbrev idealIncl : idealModule hZ sit ⟶ unitModule hZ sit :=
  sit.I.ι

/-- **The direct image `π_*𝒪_Y ⟶ π_*(𝒪_Y/ℐ)`** of the quotient map of the situation. -/
noncomputable abbrev quotientDirectImageMap :
    (modulePushforward B S hS (πHom B S hS hZ sit)).obj (unitModule hZ sit) ⟶
      (modulePushforward B S hS (πHom B S hS hZ sit)).obj (cokernel (idealIncl hZ sit)) :=
  (modulePushforward B S hS (πHom B S hS hZ sit)).map (cokernel.π (idealIncl hZ sit))

/-- **`π_*ℐ` is the kernel of `π_*𝒪_Y ⟶ π_*(𝒪_Y/ℐ)`.** -/
noncomputable def isLimitKernelForkQuotientDirectImageMap :
    IsLimit (KernelFork.ofι ((modulePushforward B S hS (πHom B S hS hZ sit)).map
        (idealIncl hZ sit))
      (((modulePushforward B S hS (πHom B S hS hZ sit)).map_comp _ _).symm.trans
        ((congrArg (modulePushforward B S hS (πHom B S hS hZ sit)).map
          (cokernel.condition (idealIncl hZ sit))).trans (Functor.map_zero _ _ _))) :
        KernelFork (quotientDirectImageMap hZ sit)) := by
  have hm0 : Mono sit.I.ι := inferInstance
  have hm : Mono (idealIncl hZ sit) := hm0
  have hk := Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel (idealIncl hZ sit))
  haveI : PreservesLimitsOfSize.{0, 0} (modulePushforward B S hS (πHom B S hS hZ sit)) :=
    (modulePullbackAdjunction B S hS (πHom B S hS hZ sit)).rightAdjoint_preservesLimits
  haveI := (modulePullbackAdjunction B S hS (πHom B S hS hZ sit)).isRightAdjoint
  exact KernelFork.mapIsLimit _ hk (modulePushforward B S hS (πHom B S hS hZ sit))

/-- `𝒪_Y` is quasi-coherent. -/
theorem isQuasicoherentOnSite_unitModule : (unitModule hZ sit).IsQuasicoherentOnSite :=
  SheafOfModules.isQuasicoherentOnSite_unit _

/-- `𝒪_Y/ℐ` is quasi-coherent. -/
theorem isQuasicoherentOnSite_cokernel_idealIncl :
    (cokernel (idealIncl hZ sit)).IsQuasicoherentOnSite := by
  have : (idealModule hZ sit).IsQuasicoherentOnSite := sit.isFiniteTypeQuasicoherent_I.1
  have := isQuasicoherentOnSite_unitModule hZ sit
  exact isQuasicoherentOnSite_cokernel_unconditional B S hS _ _ (idealIncl hZ sit)

/-- **`π_*𝒪_Y ⟶ π_*(𝒪_Y/ℐ)` is an epimorphism.** -/
theorem epi_quotientDirectImageMap : Epi (quotientDirectImageMap hZ sit) := by
  have := isQuasicoherentOnSite_unitModule hZ sit
  exact epi_modulePushforward_map_of_isAffineHom (πHom B S hS hZ sit) sit.isFinite_π.isAffineHom
    (isQuasicoherentOnSite_unitModule hZ sit) (isQuasicoherentOnSite_cokernel_idealIncl hZ sit) _

/-- **`π_*𝒪_Y ⟶ π_*(𝒪_Y/ℐ)` is a cokernel of `π_*ℐ ⟶ π_*𝒪_Y`.** -/
noncomputable def isColimitCokernelCoforkQuotientDirectImageMap :
    IsColimit (CokernelCofork.ofπ (quotientDirectImageMap hZ sit)
      (KernelFork.condition (KernelFork.ofι ((modulePushforward B S hS (πHom B S hS hZ sit)).map
        (idealIncl hZ sit))
      (((modulePushforward B S hS (πHom B S hS hZ sit)).map_comp _ _).symm.trans
        ((congrArg (modulePushforward B S hS (πHom B S hS hZ sit)).map
          (cokernel.condition (idealIncl hZ sit))).trans (Functor.map_zero _ _ _))) :
        KernelFork (quotientDirectImageMap hZ sit)))) := by
  haveI := epi_quotientDirectImageMap hZ sit
  exact Abelian.epiIsCokernelOfKernel _ (isLimitKernelForkQuotientDirectImageMap hZ sit)

/-- `π_*ℐ ⟶ π_*𝒪_Y`, the direct image of the inclusion of the ideal. -/
noncomputable abbrev idealDirectImageMap :
    (modulePushforward B S hS (πHom B S hS hZ sit)).obj (idealModule hZ sit) ⟶
      (modulePushforward B S hS (πHom B S hS hZ sit)).obj (unitModule hZ sit) :=
  (modulePushforward B S hS (πHom B S hS hZ sit)).map (idealIncl hZ sit)

/-- `idealDirectImage`, the module of Stacks 0GV1, is the direct image of `ℐ` along `π`. -/
noncomputable def idealDirectImageIso :
    idealDirectImage B S hS hZ sit ≅
      (modulePushforward B S hS (πHom B S hS hZ sit)).obj (idealModule hZ sit) :=
  ((modulePushforwardChartIso B S hS (πHom B S hS hZ sit)
    (relativelyRepresentable_hom_of_isFinite B S hS (πHom B S hS hZ sit)
      sit.isFinite_π)).app (idealModule hZ sit)).symm

/-- Exactness of `g, c₀` is transported along an isomorphism of arrows `c₀ ≅ c`. -/
private theorem exact_mk_iff_of_arrowIso {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
    {A N A' N' E : C} {c₀ : A ⟶ N} {c : A' ⟶ N'} (α : Arrow.mk c₀ ≅ Arrow.mk c) {g : E ⟶ A}
    {g' : E ⟶ A'} (hg' : g ≫ α.hom.left = g') {w : g ≫ c₀ = 0} {w' : g' ≫ c = 0} :
    (ShortComplex.mk g c₀ w).Exact ↔ (ShortComplex.mk g' c w').Exact := by
  subst hg'
  refine ShortComplex.exact_iff_of_iso (ShortComplex.isoMk (Iso.refl _)
    (Arrow.leftFunc.mapIso α) (Arrow.rightFunc.mapIso α) ?_ (Arrow.w α.hom))
  exact (Category.id_comp _).trans rfl

/-- **From a map onto `π_*ℐ` to an exact sequence `ℰ ⟶ 𝒜 ⟶ 𝒩`.**  Let `α` identify an arrow
`c₀ : 𝒜 ⟶ 𝒩` with `π_*𝒪_Y ⟶ π_*(𝒪_Y/ℐ)`.  An epimorphism `ℰ ⟶ π_*ℐ` gives a map `ℰ ⟶ 𝒜` with
which `c₀` is exact. -/
theorem exists_exact_of_epi_idealDirectImage {A N : Modules.{u, u} B S hS X.1 X.2}
    (c₀ : A ⟶ N) (α : Arrow.mk c₀ ≅ Arrow.mk (quotientDirectImageMap hZ sit))
    {E : Modules.{u, u} B S hS X.1 X.2} (e : E ⟶ idealDirectImage B S hS hZ sit) [Epi e] :
    ∃ (g : E ⟶ A) (w : g ≫ c₀ = 0), (ShortComplex.mk g c₀ w).Exact := by
  let m := idealDirectImageMap hZ sit
  let e' : E ⟶ (modulePushforward B S hS (πHom B S hS hZ sit)).obj (idealModule hZ sit) :=
    e ≫ (idealDirectImageIso hZ sit).hom
  have : Epi e' := epi_comp' ‹Epi e› (IsIso.epi_of_iso _)
  have hm : m ≫ quotientDirectImageMap hZ sit = 0 :=
    ((modulePushforward B S hS (πHom B S hS hZ sit)).map_comp _ _).symm.trans
      ((congrArg (modulePushforward B S hS (πHom B S hS hZ sit)).map
        (cokernel.condition (idealIncl hZ sit))).trans (Functor.map_zero _ _ _))
  have hc := isCokernelEpiComp (isColimitCokernelCoforkQuotientDirectImageMap hZ sit) e' rfl
  let S₂ := ShortComplex.mk (e' ≫ m) (quotientDirectImageMap hZ sit)
    (by rw [Category.assoc, hm, comp_zero])
  have hS₂ : S₂.Exact := ShortComplex.exact_of_g_is_cokernel S₂ hc
  have hw : (e' ≫ m ≫ α.inv.left) ≫ c₀ = 0 := by
    have h := Arrow.w α.inv
    simp only [Arrow.mk_hom] at h
    simp only [Category.assoc, h, reassoc_of% hm, zero_comp, comp_zero]
  refine ⟨e' ≫ m ≫ α.inv.left, hw, (exact_mk_iff_of_arrowIso α ?_).2 hS₂⟩
  simp only [Category.assoc, ← Arrow.comp_left, α.inv_hom_id, Arrow.id_left]
  exact congrArg (e' ≫ ·) (Category.comp_id m)

/-- **From an exact sequence `ℰ ⟶ 𝒜 ⟶ 𝒩` to an epimorphism onto `π_*ℐ`.**  Let `α` identify an
arrow `c₀ : 𝒜 ⟶ 𝒩` with `π_*𝒪_Y ⟶ π_*(𝒪_Y/ℐ)`.  A map `ℰ ⟶ 𝒜` with which `c₀` is exact gives an
epimorphism `ℰ ⟶ π_*ℐ`. -/
theorem exists_epi_idealDirectImage_of_exact {A N : Modules.{u, u} B S hS X.1 X.2}
    (c₀ : A ⟶ N) (α : Arrow.mk c₀ ≅ Arrow.mk (quotientDirectImageMap hZ sit))
    {E : Modules.{u, u} B S hS X.1 X.2} (g : E ⟶ A) (w : g ≫ c₀ = 0)
    (hg : (ShortComplex.mk g c₀ w).Exact) :
    ∃ e : E ⟶ idealDirectImage B S hS hZ sit, Epi e := by
  let g' := g ≫ α.hom.left
  have hw' : g' ≫ quotientDirectImageMap hZ sit = 0 := by
    have h := Arrow.w α.hom
    simp only [Arrow.mk_hom] at h
    rw [Category.assoc, h, ← Category.assoc, w, zero_comp]
  let S₂ := ShortComplex.mk g' (quotientDirectImageMap hZ sit) hw'
  have hS₂ : S₂.Exact := (exact_mk_iff_of_arrowIso α rfl).1 hg
  have hk := isLimitKernelForkQuotientDirectImageMap hZ sit
  let ℓ := hk.lift (KernelFork.ofι g' hw')
  have hℓ : ℓ ≫ idealDirectImageMap hZ sit = g' := hk.fac _ WalkingParallelPair.zero
  have hepi : Epi ℓ := by
    rw [ShortComplex.exact_iff_epi_kernel_lift] at hS₂
    let hiso := hk.conePointUniqueUpToIso (kernelIsKernel (quotientDirectImageMap hZ sit))
    have h2 : hiso.inv ≫ idealDirectImageMap hZ sit =
        kernel.ι (quotientDirectImageMap hZ sit) := by
      simpa using hk.conePointUniqueUpToIso_inv_comp
        (kernelIsKernel (quotientDirectImageMap hZ sit)) WalkingParallelPair.zero
    have : ℓ = kernel.lift _ g' hw' ≫ hiso.inv := by
      refine Fork.IsLimit.hom_ext hk ?_
      simp only [KernelFork.ι_ofι, Category.assoc]
      rw [hℓ, h2, kernel.lift_ι]
    rw [this]
    exact epi_comp' hS₂ (IsIso.epi_of_iso _)
  exact ⟨ℓ ≫ (idealDirectImageIso hZ sit).inv, epi_comp' hepi (IsIso.epi_of_iso _)⟩

/-- **`π_*(𝒪_Y/ℐ)` is of finite presentation when `π_*𝒪_Y` is.** -/
theorem isFinitePresentationOnSite_quotientDirectImage
    (hfp : (pushforwardStructureModule B S hS (πHom B S hS hZ sit)).IsFinitePresentationOnSite) :
    ((modulePushforward B S hS (πHom B S hS hZ sit)).obj
      (cokernel (idealIncl hZ sit))).IsFinitePresentationOnSite := by
  have hft : SheafOfModules.IsFiniteTypeOnSite
      ((modulePushforward B S hS (πHom B S hS hZ sit)).obj (idealModule hZ sit)) :=
    Stacks.SheafOfModules.FiniteTypeTransport.isFiniteTypeOnSite_of_iso (idealDirectImageIso hZ sit)
      (isFiniteTypeOnSite_idealDirectImage B S hS hZ sit)
  exact SheafOfModules.IsFinitePresentationOnSite.of_iso
    ((isColimitCokernelCoforkQuotientDirectImageMap hZ sit).coconePointUniqueUpToIso
      (cokernelIsCokernel (idealDirectImageMap hZ sit))).symm
    (isFinitePresentationOnSite_cokernel (idealDirectImageMap hZ sit) hft hfp)

/-- **The base change of `π_*𝒪_Y ⟶ π_*(𝒪_Y/ℐ)`.**  For a cartesian square of `π' : Y' ⟶ X'` and
`π : Y ⟶ X` along `q : X' ⟶ X` and `q' : Y' ⟶ Y`, and an identification `β` of `q'^*` of
`𝒪_Y ⟶ 𝒪_Y/ℐ` with `𝒪_{Y'} ⟶ 𝒪_{Y'}/ℐ'`, the inverse image along `q` of `π_*𝒪_Y ⟶ π_*(𝒪_Y/ℐ)`
is identified with `π'_*𝒪_{Y'} ⟶ π'_*(𝒪_{Y'}/ℐ')`. -/
theorem nonempty_arrowIso_quotientDirectImageMap_baseChange {X' : AlgebraicSpaces B S hS}
    {hqc' : IsQuasiCompactSpace B S hS X'.1} {hqs' : IsAbsolutelyQuasiSeparated B S hS hZ X'.1}
    (sit' : ResolutionPropertyDescentSituation B S hS hZ X' hqc' hqs') (q : X' ⟶ X)
    (q' : sit'.Y ⟶ sit.Y) (sq : IsPullback q' (πHom B S hS hZ sit') (πHom B S hS hZ sit) q)
    (β : Arrow.mk ((modulePullback B S hS q').map (cokernel.π (idealIncl hZ sit))) ≅
      Arrow.mk (cokernel.π (idealIncl hZ sit'))) :
    Nonempty (Arrow.mk ((modulePullback B S hS q).map (quotientDirectImageMap hZ sit)) ≅
      Arrow.mk (quotientDirectImageMap hZ sit')) := by
  obtain ⟨γ⟩ := nonempty_arrowIso_modulePullback_map_modulePushforward_map sq
    sit.isFinite_π.isAffineHom (cokernel.π (idealIncl hZ sit))
    (isQuasicoherentOnSite_unitModule hZ sit) (isQuasicoherentOnSite_cokernel_idealIncl hZ sit)
  let P := modulePushforward B S hS (πHom B S hS hZ sit')
  let δ : Arrow.mk (P.map ((modulePullback B S hS q').map (cokernel.π (idealIncl hZ sit)))) ≅
      Arrow.mk (quotientDirectImageMap hZ sit') :=
    Arrow.isoMk (P.mapIso (Arrow.leftFunc.mapIso β)) (P.mapIso (Arrow.rightFunc.mapIso β)) (by
      have h := Arrow.w β.hom
      simp only [Arrow.mk_hom] at h
      change P.map β.hom.left ≫ P.map (cokernel.π (idealIncl hZ sit')) =
        P.map ((modulePullback B S hS q').map (cokernel.π (idealIncl hZ sit))) ≫ P.map β.hom.right
      rw [← P.map_comp, ← P.map_comp, h])
  exact ⟨γ ≪≫ δ⟩

end DirectImage

/-! ### The base change, with its comparison of `π_*𝒪_Y ⟶ π_*(𝒪_Y/ℐ)` -/

section BaseChangeIso

variable {X : AlgebraicSpaces B S hS}
    {hqc : IsQuasiCompactSpace B S hS X.1} {hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1}
    (sit : ResolutionPropertyDescentSituation B S hS hZ X hqc hqs)

/-- **The base change of the situation, with the comparison of `π_*𝒪_Y ⟶ π_*(𝒪_Y/ℐ)`.**  Along
an affine morphism `q : X' ⟶ X` of quasi-compact and quasi-separated algebraic spaces the
situation of Stacks 0GUY base changes to a situation on `X'` (with the inverse-image ideal),
and the inverse image along `q` of `π_*𝒪_Y ⟶ π_*(𝒪_Y/ℐ)` is identified with
`π'_*𝒪_{Y'} ⟶ π'_*(𝒪_{Y'}/ℐ')`.  If `π_*𝒪_Y` is of finite presentation, so is `π'_*𝒪_{Y'}`. -/
theorem exists_baseChange_arrowIso {X' : AlgebraicSpaces B S hS} (q : X' ⟶ X)
    (hq : IsAffineHom B S hS q.hom)
    (hqc' : IsQuasiCompactSpace B S hS X'.1) (hqs' : IsAbsolutelyQuasiSeparated B S hS hZ X'.1)
    (hfp : (pushforwardStructureModule B S hS (πHom B S hS hZ sit)).IsFinitePresentationOnSite) :
    ∃ sit' : ResolutionPropertyDescentSituation B S hS hZ X' hqc' hqs',
      (pushforwardStructureModule B S hS (πHom B S hS hZ sit')).IsFinitePresentationOnSite ∧
      Nonempty (Arrow.mk ((modulePullback B S hS q).map (quotientDirectImageMap hZ sit)) ≅
        Arrow.mk (quotientDirectImageMap hZ sit')) := by
  obtain ⟨sit', q', sq, hI'⟩ := exists_baseChange hZ sit q hq hqc' hqs'
    (fun g => isFiniteTypeQuasicoherentIdeal_pullbackIdealImage B S hS g sit.I
      sit.isFiniteTypeQuasicoherent_I)
    (fun g => idealZeroLocus_pullbackIdealImage B S hS g sit.I sit.isFiniteTypeQuasicoherent_I.1)
  have hA : Arrow.mk (cokernel.π (pullbackIdealImage B S hS q' sit.I).ι :
        (unitModule hZ sit' ⟶ _)) = Arrow.mk (cokernel.π (idealIncl hZ sit')) := by
    unfold idealIncl idealModule
    rw [hI']
    rfl
  let β₀ : Arrow.mk ((modulePullback B S hS q').map (cokernel.π (idealIncl hZ sit))) ≅
      Arrow.mk (cokernel.π (pullbackIdealImage B S hS q' sit.I).ι :
        (unitModule hZ sit' ⟶ _)) :=
    Arrow.isoMk (modulePullbackUnitIso B S hS q')
      (cokernelPullbackIdealImageIso B S hS q' sit.I).symm (by
        have h := cokernel_π_cokernelPullbackIdealImageIso_hom B S hS q' sit.I
        change (modulePullbackUnitIso B S hS q').hom ≫
            cokernel.π (pullbackIdealImage B S hS q' sit.I).ι =
          (modulePullback B S hS q').map (cokernel.π (idealIncl hZ sit)) ≫
            (cokernelPullbackIdealImageIso B S hS q' sit.I).inv
        have h' : (modulePullbackUnitIso B S hS q').hom ≫
            cokernel.π (pullbackIdealImage B S hS q' sit.I).ι ≫
              (cokernelPullbackIdealImageIso B S hS q' sit.I).hom =
            (modulePullback B S hS q').map (cokernel.π (idealIncl hZ sit)) := by
          rw [h, Iso.hom_inv_id_assoc]
          rfl
        rw [← h']
        exact ((Category.assoc _ _ _).trans (congrArg ((modulePullbackUnitIso B S hS q').hom ≫ ·)
          ((Category.assoc _ _ _).trans ((congrArg
            (cokernel.π (pullbackIdealImage B S hS q' sit.I).ι ≫ ·)
            (cokernelPullbackIdealImageIso B S hS q' sit.I).hom_inv_id).trans
              (Category.comp_id _))))).symm)
  let β := β₀ ≪≫ eqToIso hA
  obtain ⟨α⟩ := nonempty_arrowIso_quotientDirectImageMap_baseChange hZ sit sit' q q' sq β
  exact ⟨sit', SheafOfModules.IsFinitePresentationOnSite.of_iso (Arrow.leftFunc.mapIso α)
    (isFinitePresentationOnSite_modulePullback B S hS q _ hfp), ⟨α⟩⟩

end BaseChangeIso

end ResolutionPropertyDescentSituation

end AlgebraicGeometry.Space

end
