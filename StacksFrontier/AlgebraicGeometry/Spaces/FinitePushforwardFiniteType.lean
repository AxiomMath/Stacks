module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteFiniteTypeBridge
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Descent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePushforwardChartRing
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFinitenessDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeRestriction
public import StacksFrontier.CategoryTheory.Sites.CoversTopRefinement
public import StacksFrontier.RingTheory.ModuleBaseChangePushout

/-!
# Finite type of a module and of its direct image along a finite morphism

Let `f : X ⟶ Y` be a finite — hence representable and affine — morphism of algebraic spaces over
a scheme `S` contained in a big fppf site `B`, and let `M` be an `𝒪_X`-module on the small étale
site of `X`.  If the base change comparison of the sections of `M` over morphisms of affine
étale charts is bijective, then so is that of the direct image `f_*M`; and when `M` is
quasi-coherent, `M` is of finite type if and only if `f_*M` is.

## Main results

* `AlgebraicGeometry.Space.algebra_isPushout_chartRing_smallBaseChange`: the base-change square
  of rings of a morphism of affine étale charts of `Y` is a pushout, in the
  `AlgebraicGeometry.Space.chartRing` spelling of the sections of the structure sheaf.
* `AlgebraicGeometry.Space.bijective_sectionsBaseChange_smallBaseChangeModulePushforward` and
  `AlgebraicGeometry.Space.isCartesianOnAffineCharts_smallBaseChangeModulePushforward`: the
  base change comparison of the sections of `f_*M` over a morphism of affine étale charts of `Y`
  is bijective when the comparison for `M` is.
* `AlgebraicGeometry.Space.coversTop_smallBaseChange_affineCharts`: the base changes of the
  affine étale charts of `Y` cover `X`.
* `AlgebraicGeometry.Space.isFiniteType_iff_smallBaseChangePushforward_of_isQuasicoherentOnSite`:
  a quasi-coherent module on the source of a finite morphism of algebraic spaces is of finite
  type if and only if its direct image is.

## References

* [Stacks Project, Tag 060Z](https://stacks.math.columbia.edu/tag/060Z)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

section Pushforward

variable (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)

/-- The direct image of `AlgebraicGeometry.Space.smallBaseChangeModulePushforward`, read as an
`𝒪_Y`-module on the small étale *ringed site* of `Y`. -/
noncomputable abbrev smallBaseChangePushforwardModules (M : Modules.{u, u} B S hS X.1 X.2) :
    Modules.{u, u} B S hS Y.1 Y.2 :=
  (smallBaseChangeModulePushforward B S hS f hf).obj M

/-! ### The base-change square of rings at the `chartRing` spelling -/

/-- The square of rings of a base-changed chart, read pointwise. -/
theorem appTop_smallBaseChange_square_apply {A Z : SmallEtale B S hS Y.1} (k : Z ⟶ A)
    (r : chartRing B S hS Y.1 Y.2 A) :
    (chartRestrict (hF := X.2) ((smallBaseChange B S hS f hf).map k))
        ((((BigFppfOver.toScheme B S hS).map (hf.snd A.1.hom)).appTop).hom r) =
      (((BigFppfOver.toScheme B S hS).map (hf.snd Z.1.hom)).appTop).hom
        (chartRestrict (hF := Y.2) k r) :=
  congrArg
    (fun φ : chartRing B S hS Y.1 Y.2 A →+*
        chartRing B S hS X.1 X.2 ((smallBaseChange B S hS f hf).obj Z) => φ r)
    (appTop_smallBaseChange_square B S hS f hf k)

/-- The algebra structure on the regular functions of the base change of the smaller chart over
the regular functions of the larger chart: pull back to the base change of the larger chart and
restrict. -/
@[instance_reducible]
noncomputable def baseChangeChartAlgebraComp {A Z : SmallEtale B S hS Y.1} (k : Z ⟶ A) :
    Algebra (chartRing B S hS Y.1 Y.2 A)
      (chartRing B S hS X.1 X.2 ((smallBaseChange B S hS f hf).obj Z)) :=
  ((chartRestrict (hF := X.2) ((smallBaseChange B S hS f hf).map k)).comp
    (((BigFppfOver.toScheme B S hS).map (hf.snd A.1.hom)).appTop).hom).toAlgebra

/-- The composite algebra structure factors through the base change of the larger chart. -/
theorem isScalarTower_baseChangeChartAlgebraComp_top {A Z : SmallEtale B S hS Y.1}
    (k : Z ⟶ A) :
    letI := baseChangeChartAlgebra B S hS f hf A
    letI := chartAlgebra (hF := X.2) ((smallBaseChange B S hS f hf).map k)
    letI := baseChangeChartAlgebraComp B S hS f hf k
    IsScalarTower (chartRing B S hS Y.1 Y.2 A)
      (chartRing B S hS X.1 X.2 ((smallBaseChange B S hS f hf).obj A))
      (chartRing B S hS X.1 X.2 ((smallBaseChange B S hS f hf).obj Z)) := by
  let := baseChangeChartAlgebra B S hS f hf A
  let := chartAlgebra (hF := X.2) ((smallBaseChange B S hS f hf).map k)
  let := baseChangeChartAlgebraComp B S hS f hf k
  exact IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The composite algebra structure factors through the smaller chart. -/
theorem isScalarTower_baseChangeChartAlgebraComp_left {A Z : SmallEtale B S hS Y.1}
    (k : Z ⟶ A) :
    letI := chartAlgebra (hF := Y.2) k
    letI := baseChangeChartAlgebra B S hS f hf Z
    letI := baseChangeChartAlgebraComp B S hS f hf k
    IsScalarTower (chartRing B S hS Y.1 Y.2 A) (chartRing B S hS Y.1 Y.2 Z)
      (chartRing B S hS X.1 X.2 ((smallBaseChange B S hS f hf).obj Z)) := by
  let := chartAlgebra (hF := Y.2) k
  let := baseChangeChartAlgebra B S hS f hf Z
  let := baseChangeChartAlgebraComp B S hS f hf k
  exact IsScalarTower.of_algebraMap_eq (appTop_smallBaseChange_square_apply B S hS f hf k)

/-- **The four rings of the base-change square of a morphism of affine charts form a pushout**,
in the `AlgebraicGeometry.Space.chartRing` spelling of the sections of the structure sheaf. -/
theorem algebra_isPushout_chartRing_smallBaseChange (haff : IsAffineHom B S hS f.hom)
    {A Z : SmallEtale B S hS Y.1}
    (hA : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj A))
    (hZ : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj Z))
    (k : Z ⟶ A) :
    letI := baseChangeChartAlgebra B S hS f hf A
    letI := chartAlgebra (hF := Y.2) k
    letI := chartAlgebra (hF := X.2) ((smallBaseChange B S hS f hf).map k)
    letI := baseChangeChartAlgebra B S hS f hf Z
    letI := baseChangeChartAlgebraComp B S hS f hf k
    haveI := isScalarTower_baseChangeChartAlgebraComp_top B S hS f hf k
    haveI := isScalarTower_baseChangeChartAlgebraComp_left B S hS f hf k
    Algebra.IsPushout (chartRing B S hS Y.1 Y.2 A)
      (chartRing B S hS X.1 X.2 ((smallBaseChange B S hS f hf).obj A))
      (chartRing B S hS Y.1 Y.2 Z)
      (chartRing B S hS X.1 X.2 ((smallBaseChange B S hS f hf).obj Z)) :=
  @algebra_isPushout_appTop_smallBaseChange B S hS X Y f hf haff A Z k hA hZ
    (baseChangeChartAlgebra B S hS f hf A) (chartAlgebra (hF := Y.2) k)
    (chartAlgebra (hF := X.2) ((smallBaseChange B S hS f hf).map k))
    (baseChangeChartAlgebra B S hS f hf Z) (baseChangeChartAlgebraComp B S hS f hf k)
    (isScalarTower_baseChangeChartAlgebraComp_top B S hS f hf k)
    (isScalarTower_baseChangeChartAlgebraComp_left B S hS f hf k) rfl rfl rfl rfl

/-! ### The direct image is cartesian on affine charts -/

variable (M : Modules.{u, u} B S hS X.1 X.2)

/-- The `𝒪_Y(A)`-module structure on the sections of `M` over the base change of the chart `A`,
coming from the direct image of `M`. -/
private noncomputable abbrev pushforwardSectionsModule (A : SmallEtale B S hS Y.1) :
    Module (chartRing B S hS Y.1 Y.2 A)
      (M.val.obj (op ((smallBaseChange B S hS f hf).obj A)) : Type u) :=
  ((smallBaseChangePushforwardModules B S hS f hf M).val.obj (op A)).isModule

/-- The sections of `M` over a base-changed chart form a tower over the regular functions on the
chart below and on its base change. -/
private theorem isScalarTower_pushforwardSectionsModule (A : SmallEtale B S hS Y.1) :
    letI := baseChangeChartAlgebra B S hS f hf A
    letI := pushforwardSectionsModule B S hS f hf M A
    IsScalarTower (chartRing B S hS Y.1 Y.2 A)
      (chartRing B S hS X.1 X.2 ((smallBaseChange B S hS f hf).obj A))
      (M.val.obj (op ((smallBaseChange B S hS f hf).obj A)) : Type u) := by
  let := baseChangeChartAlgebra B S hS f hf A
  let := pushforwardSectionsModule B S hS f hf M A
  exact IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- For an affine morphism `f` and a module `M` cartesian on affine charts, the base change
comparison of the sections of the direct image of `M` over a morphism `k : Z ⟶ A` of affine
étale charts of `Y` is bijective. -/
theorem bijective_sectionsBaseChange_smallBaseChangeModulePushforward
    (haff : IsAffineHom B S hS f.hom) (hM : IsCartesianOnAffineCharts M)
    {A Z : SmallEtale B S hS Y.1}
    (hA : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj A))
    (hZ : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj Z))
    (k : Z ⟶ A) :
    letI := chartAlgebra (hF := Y.2) k
    Function.Bijective
      (sectionsBaseChange (smallBaseChangePushforwardModules B S hS f hf M) k) := by
  let algRR' := chartAlgebra (hF := Y.2) k
  let algSS' := chartAlgebra (hF := X.2) ((smallBaseChange B S hS f hf).map k)
  let algRS := baseChangeChartAlgebra B S hS f hf A
  let algR'S' := baseChangeChartAlgebra B S hS f hf Z
  let algRS' := baseChangeChartAlgebraComp B S hS f hf k
  have towRSS' := isScalarTower_baseChangeChartAlgebraComp_top B S hS f hf k
  have towRR'S' := isScalarTower_baseChangeChartAlgebraComp_left B S hS f hf k
  have hpush := algebra_isPushout_chartRing_smallBaseChange B S hS f hf haff hA hZ k
  let modRMo := pushforwardSectionsModule B S hS f hf M A
  let modR'No := pushforwardSectionsModule B S hS f hf M Z
  let modRNo : Module (chartRing B S hS Y.1 Y.2 A)
      (M.val.obj (op ((smallBaseChange B S hS f hf).obj Z)) : Type u) :=
    Module.compHom (M.val.obj (op ((smallBaseChange B S hS f hf).obj Z)) : Type u)
      (chartRestrict (hF := Y.2) k)
  let modSNo := chartSectionsModule M ((smallBaseChange B S hS f hf).map k)
  have towRSMo := isScalarTower_pushforwardSectionsModule B S hS f hf M A
  have towR'S'No := isScalarTower_pushforwardSectionsModule B S hS f hf M Z
  have towRR'No : IsScalarTower (chartRing B S hS Y.1 Y.2 A)
      (chartRing B S hS Y.1 Y.2 Z)
      (M.val.obj (op ((smallBaseChange B S hS f hf).obj Z)) : Type u) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have towSS'No := chartSections_isScalarTower M ((smallBaseChange B S hS f hf).map k)
  have towRSNo : IsScalarTower (chartRing B S hS Y.1 Y.2 A)
      (chartRing B S hS X.1 X.2 ((smallBaseChange B S hS f hf).obj A))
      (M.val.obj (op ((smallBaseChange B S hS f hf).obj Z)) : Type u) :=
    IsScalarTower.of_algebraMap_smul fun r x =>
      congrArg
        (fun s : chartRing B S hS X.1 X.2 ((smallBaseChange B S hS f hf).obj Z) => s • x)
        (appTop_smallBaseChange_square_apply B S hS f hf k r)
  have hbij : Function.Bijective
      (sectionsBaseChange M ((smallBaseChange B S hS f hf).map k)) :=
    hM ((smallBaseChange B S hS f hf).obj A) ((smallBaseChange B S hS f hf).obj Z)
      (isAffine_smallBaseChange_obj B S hS f hf haff A hA)
      (isAffine_smallBaseChange_obj B S hS f hf haff Z hZ)
      ((smallBaseChange B S hS f hf).map k)
  have hbc : IsBaseChange (chartRing B S hS X.1 X.2 ((smallBaseChange B S hS f hf).obj Z))
      (chartRestrictLinear M ((smallBaseChange B S hS f hf).map k)) :=
    Stacks.FlatSectionsDescent.isBaseChange_of_bijective_liftBaseChange
      (chartRestrictLinear M ((smallBaseChange B S hS f hf).map k)) hbij
  let gR : (M.val.obj (op ((smallBaseChange B S hS f hf).obj A)) : Type u) →ₗ[
      chartRing B S hS Y.1 Y.2 A]
      (M.val.obj (op ((smallBaseChange B S hS f hf).obj Z)) : Type u) :=
    chartRestrictLinear (smallBaseChangePushforwardModules B S hS f hf M) k
  have key : Function.Bijective
      (LinearMap.liftBaseChange (chartRing B S hS Y.1 Y.2 Z) gR) :=
    Algebra.IsPushout.bijective_liftBaseChange_of_eq gR
      (chartRestrictLinear M ((smallBaseChange B S hS f hf).map k)) (fun _ => rfl) hbc
  exact key

/-- The direct image of a module cartesian on affine charts is cartesian on affine charts. -/
theorem isCartesianOnAffineCharts_smallBaseChangeModulePushforward
    (haff : IsAffineHom B S hS f.hom) (hM : IsCartesianOnAffineCharts M) :
    IsCartesianOnAffineCharts (smallBaseChangePushforwardModules B S hS f hf M) :=
  fun _ _ hA hZ k =>
    bijective_sectionsBaseChange_smallBaseChangeModulePushforward B S hS f hf M haff hM
      hA hZ k

/-! ### The base-changed affine charts cover the source -/

/-- The base changes of the étale charts of `Y` cover `X`. -/
theorem coversTop_smallBaseChange_obj :
    (smallEtaleRingedSite B S hS X.1 X.2).J.CoversTop
      (fun A : SmallEtale B S hS Y.1 => (smallBaseChange B S hS f hf).obj A) := by
  obtain ⟨V, hV⟩ := exists_isSurjective_chart B S hS Y
  exact (SmallEtale.coversTop_of_isSurjective B S hS X.1 X.2
    ((smallBaseChange B S hS f hf).obj V)
    (isSurjective_smallBaseChange_obj_hom B S hS f hf V hV)).of_exists_hom
    fun _ => ⟨V, ⟨𝟙 _⟩⟩

/-- The base changes of the affine étale charts of `Y` cover `X`. -/
theorem coversTop_smallBaseChange_affineCharts :
    (smallEtaleRingedSite B S hS X.1 X.2).J.CoversTop
      (fun A : {A : SmallEtale B S hS Y.1 // IsAffine (chartScheme A)} =>
        (smallBaseChange B S hS f hf).obj A.1) :=
  GrothendieckTopology.coversTop_obj_subtype (smallBaseChange B S hS f hf)
    (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)
    (coversTop_smallBaseChange_obj B S hS f hf) (fun A => IsAffine (chartScheme A)) fun U => by
      obtain ⟨I, V, ι, hVaff, hcov, -⟩ := SmallEtale.exists_affine_etale_ofArrows B S hS Y.1 U
      refine ⟨Presieve.ofArrows V ι, hcov, ?_⟩
      rintro W g ⟨j⟩
      exact hVaff j

/-! ### Finiteness of the sections over an affine chart and over its base change -/

/-- **The sections of the direct image along a finite morphism over an affine chart of `Y` form
a finite module** when the sections of the module over the base-changed chart do. -/
theorem moduleFinite_sections_smallBaseChangeModulePushforward (hfin : IsFinite B S hS f.hom)
    (A : SmallEtale B S hS Y.1) (hA : IsAffine (chartScheme A))
    (hMA : Module.Finite (chartRing B S hS X.1 X.2 ((smallBaseChange B S hS f hf).obj A))
      (M.val.obj (op ((smallBaseChange B S hS f hf).obj A)))) :
    Module.Finite (chartRing B S hS Y.1 Y.2 A)
      ((smallBaseChangePushforwardModules B S hS f hf M).val.obj (op A)) := by
  let algRS := baseChangeChartAlgebra B S hS f hf A
  have := moduleFinite_chartRing_smallBaseChange B S hS f hf hfin A hA
  let modRMo := pushforwardSectionsModule B S hS f hf M A
  have towRSMo := isScalarTower_pushforwardSectionsModule B S hS f hf M A
  exact Module.Finite.trans
    (chartRing B S hS X.1 X.2 ((smallBaseChange B S hS f hf).obj A))
    (M.val.obj (op ((smallBaseChange B S hS f hf).obj A)) : Type u)

/-- **The sections of a module over a base-changed chart form a finite module over the regular
functions on that chart** as soon as they form a finite module over the regular functions on
the chart below. -/
theorem moduleFinite_sections_baseChangeChart (A : SmallEtale B S hS Y.1)
    (hNA : Module.Finite (chartRing B S hS Y.1 Y.2 A)
      ((smallBaseChangePushforwardModules B S hS f hf M).val.obj (op A))) :
    Module.Finite (chartRing B S hS X.1 X.2 ((smallBaseChange B S hS f hf).obj A))
      (M.val.obj (op ((smallBaseChange B S hS f hf).obj A))) := by
  let algRS := baseChangeChartAlgebra B S hS f hf A
  let modRMo := pushforwardSectionsModule B S hS f hf M A
  have towRSMo := isScalarTower_pushforwardSectionsModule B S hS f hf M A
  have : Module.Finite (chartRing B S hS Y.1 Y.2 A)
      (M.val.obj (op ((smallBaseChange B S hS f hf).obj A)) : Type u) := hNA
  exact Module.Finite.of_restrictScalars_finite (chartRing B S hS Y.1 Y.2 A)
    (chartRing B S hS X.1 X.2 ((smallBaseChange B S hS f hf).obj A))
    (M.val.obj (op ((smallBaseChange B S hS f hf).obj A)) : Type u)

end Pushforward

/-! ### Finite type of the direct image along a finite morphism -/

/-- For a finite morphism `f : X ⟶ Y` of algebraic spaces a quasi-coherent `𝒪_X`-module `F` is
of finite type if and only if its direct image `f_*F` is. -/
@[stacks 060Z]
theorem isFiniteType_iff_smallBaseChangePushforward_of_isQuasicoherentOnSite
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsFinite B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hqc : F.IsQuasicoherentOnSite) :
    F.IsFiniteType ↔
      ((smallBaseChangeModulePushforward B S hS f
        (relativelyRepresentable_hom_of_isFinite B S hS f hf)).obj F).IsFiniteType := by
  have hrep := relativelyRepresentable_hom_of_isFinite B S hS f hf
  have hFcart : IsCartesianOnAffineCharts F :=
    isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 F hqc
  have hNcart :
      IsCartesianOnAffineCharts (smallBaseChangePushforwardModules B S hS f hrep F) :=
    isCartesianOnAffineCharts_smallBaseChangeModulePushforward B S hS f hrep F
      hf.isAffineHom hFcart
  constructor
  · intro h
    refine SheafOfModules.isFiniteType_of_presheaf_isFiniteType
      (smallBaseChangePushforwardModules B S hS f hrep F)
      (isFiniteType_of_forall_affine_moduleFinite B S hS Y.1 Y.2 _ hNcart fun A hA => ?_)
    exact moduleFinite_sections_smallBaseChangeModulePushforward B S hS f hrep F hf A hA
      (moduleFinite_sections_of_isFiniteType B S hS X.1 X.2 hFcart
        (Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteType F h)
        (isAffine_smallBaseChange_obj B S hS f hrep hf.isAffineHom A hA))
  · intro h
    refine SheafOfModules.isFiniteType_of_presheaf_isFiniteType F
      (isFiniteType_of_coversTop_affine_moduleFinite B S hS X.1 X.2 F hFcart
        (fun A : {A : SmallEtale B S hS Y.1 // IsAffine (chartScheme A)} =>
          (smallBaseChange B S hS f hrep).obj A.1)
        (fun A => isAffine_smallBaseChange_obj B S hS f hrep hf.isAffineHom A.1 A.2)
        (coversTop_smallBaseChange_affineCharts B S hS f hrep) fun A => ?_)
    exact moduleFinite_sections_baseChangeChart B S hS f hrep F A.1
      (moduleFinite_sections_of_isFiniteType B S hS Y.1 Y.2 hNcart
        (Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteType
          (smallBaseChangePushforwardModules B S hS f hrep F) h) A.2)

end AlgebraicGeometry.Space

end
