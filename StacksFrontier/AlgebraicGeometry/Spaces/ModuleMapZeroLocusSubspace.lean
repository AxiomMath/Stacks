module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityFlatInjectionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.RelativelyPureModules
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModule
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapLociFlatPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapTargetBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactAffineMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationCancellation
import all StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapLociFlatPullback

/-!
# The vanishing locus of a map of quasi-coherent modules as a subspace of the base

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and let `u : ℱ ⟶ 𝒢` be a
map of quasi-coherent `𝒪_X`-modules, as in Stacks 083F. The variant `F_zero` of Stacks 083F is
`AlgebraicGeometry.Space.ModuleMapSituation.zeroFunctor`, a subterminal presheaf on the test
schemes over `Y`. This file reads it as the subfunctor
`AlgebraicGeometry.Space.ModuleMapSituation.zeroSubfunctor` of `Y`, whose sections over an object
`U` of the site are the sections of `Y` over `U` at which the base change of `u` vanishes, and
proves that the two readings agree. It also proves that the vanishing subfunctor is unchanged by
passing to a suitable flat chart `g : X' ⟶ X`, and defines the predicates in terms of which the
conclusions of Stacks 0CWC are assembled.

## Main definitions

* `AlgebraicGeometry.Space.ModuleMapSituation.zeroTest`: a section of `Y` over an object of the
  site, read as a test scheme of the situation.
* `AlgebraicGeometry.Space.ModuleMapSituation.zeroSubfunctor`: `F_zero` as a subfunctor of `Y`.
* `AlgebraicGeometry.Space.ModuleMapSituation.targetPrePureSituation`: the situation of
  Stacks 0CV6 formed by `f` and the target module `𝒢`.
* `AlgebraicGeometry.Space.ModuleMapSituation.HasFlatChartWithClosedZeroLocus`: there is a flat
  chart whose image contains the support of `𝒢` and whose vanishing locus is represented by a
  closed subspace of `Y`.
* `AlgebraicGeometry.Space.ModuleMapSituation.ChartSectionsProjective`: the sections of `𝒢`
  along an affine chart are projective over the functions on an affine base.
* `AlgebraicGeometry.Space.ModuleMapSituation.HasAffineFlatChartEtaleLocallyOnBase`: étale
  locally on an affine base, a flat chart with affine source whose image contains the relative
  weak assassin and along which the sections of `𝒢` are projective.
* `AlgebraicGeometry.Space.ModuleMapSituation.DevissageInput`: every situation satisfying the
  hypotheses of Stacks 0CWC has such charts.
* `AlgebraicGeometry.Space.ModuleMapSituation.AffineChartZeroLocusClosed`: over an affine base,
  along a flat chart with affine source and projective sections, the vanishing locus is a closed
  subspace.
* `AlgebraicGeometry.Space.ModuleMapSituation.ZeroLocusClosedEtaleLocalOnBase`: closedness of
  the vanishing locus étale locally on the base implies closedness.

## Main results

* `AlgebraicGeometry.Space.exists_factor_iff_mem`: a section of a presheaf lies in a subfunctor
  exactly when the morphism it names factors through that subfunctor.
* `AlgebraicGeometry.Space.isQuasiCompact_of_comp_eq_schemeSpaceMap` and
  `AlgebraicGeometry.Space.isQuasiSeparated_of_comp_eq_schemeSpaceMap`: a chart with affine
  source over an affine base is quasi-compact (for a quasi-separated structure morphism) and
  quasi-separated.
* `AlgebraicGeometry.Space.ModuleMapSituation.isZeroAt_iff_exists_factor_zeroSubfunctor`: the
  two readings of `F_zero` agree.
* `AlgebraicGeometry.Space.ModuleMapSituation.zeroSubfunctor_eq_of_forall_isZeroAt_iff`: a
  subfunctor of `Y` that represents `F_zero` is `zeroSubfunctor`.
* `AlgebraicGeometry.Space.ModuleMapSituation.zeroSubfunctor_pullbackSituation_eq`: along a flat
  `g : X' ⟶ X` whose image contains the support of `𝒢`, the vanishing locus of `g^*u` is that
  of `u`.
* `AlgebraicGeometry.Space.ModuleMapSituation.zeroSubfunctor_pullbackSituation_eq_of_mono_unit`:
  the same, as soon as `𝒢 ⟶ g_*g^*𝒢` stays a monomorphism after every base change.
* `zeroSubfunctor_pullbackSituation_eq_of_relativeWeaklyAssociatedPoints_subset_range_of_qcqs`:
  the same for a quasi-compact and quasi-separated flat chart whose image contains the relative
  weak assassin `Ass_{X/Y}(𝒢)`.
* `AlgebraicGeometry.Space.ModuleMapSituation.hasFlatChartWithClosedZeroLocus_iff`:
  `HasFlatChartWithClosedZeroLocus` holds exactly when a flat chart whose image contains the
  support of `𝒢` exists and `zeroSubfunctor` is a closed subspace.

## References

* [Stacks Project, Tag 0CWC](https://stacks.math.columbia.edu/tag/0CWC)
* [Stacks Project, Tag 083F](https://stacks.math.columbia.edu/tag/083F)
* [Stacks Project, Tag 083I](https://stacks.math.columbia.edu/tag/083I)
* [Stacks Project, Tag 083J](https://stacks.math.columbia.edu/tag/083J)
* [Stacks Project, Tag 083L](https://stacks.math.columbia.edu/tag/083L)
* [Stacks Project, Tag 0CW5](https://stacks.math.columbia.edu/tag/0CW5)
* [Stacks Project, Tag 0CW6](https://stacks.math.columbia.edu/tag/0CW6)
* [Stacks Project, Tag 0CW2](https://stacks.math.columbia.edu/tag/0CW2)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 05LW](https://stacks.math.columbia.edu/tag/05LW)
* [Stacks Project, Tag 0CVZ](https://stacks.math.columbia.edu/tag/0CVZ)
* [Stacks Project, Tag 0CVV](https://stacks.math.columbia.edu/tag/0CVV)
* [Stacks Project, Tag 0CW3](https://stacks.math.columbia.edu/tag/0CW3)
* [Stacks Project, Tag 02WY](https://stacks.math.columbia.edu/tag/02WY)
* [Stacks Project, Tag 04AK](https://stacks.math.columbia.edu/tag/04AK)
* [Stacks Project, Tag 09TP](https://stacks.math.columbia.edu/tag/09TP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Factoring through a subfunctor -/

/-- **A section of a presheaf lies in a subfunctor exactly when the morphism it names factors
through that subfunctor.**  The morphism a section `x` of `F` over `A` names is
`yonedaEquiv.symm x : yoneda.obj A ⟶ F`. -/
theorem exists_factor_iff_mem {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (Z : Subfunctor F)
    {A : BigFppfOver B S hS} (x : F.obj (Opposite.op A)) :
    (∃ k : yoneda.obj A ⟶ Z.toFunctor, k ≫ Z.ι = yonedaEquiv.symm x) ↔
      x ∈ Z.obj (Opposite.op A) := by
  have hrange : Subfunctor.range (yonedaEquiv.symm x) ≤ Z ↔ x ∈ Z.obj (Opposite.op A) := by
    constructor
    · intro h
      have h1 := h (Opposite.op A) ⟨𝟙 A, rfl⟩
      rwa [show (yonedaEquiv.symm x).app (Opposite.op A) (𝟙 A) = x from by
        rw [← yonedaEquiv_apply, Equiv.apply_symm_apply]] at h1
    · intro hx V y hy
      obtain ⟨g, rfl⟩ := hy
      have hnat : (yonedaEquiv.symm x).app V g = F.map g.op x := by
        simp
      rw [hnat]
      exact Z.map g.op hx
  rw [← hrange]
  exact ⟨fun ⟨k, hk⟩ V y hy => by
      obtain ⟨z, rfl⟩ := hy
      exact hk ▸ (k.app V z).property,
    fun h => ⟨Subfunctor.lift _ h, Subfunctor.lift_ι _ h⟩⟩

/-! ### A chart with affine source over an affine base is quasi-compact and quasi-separated -/

/-- **The composite of a chart with affine source and a structure morphism to an affine base is
the Yoneda image of a morphism of the site**, read on underlying transformations. -/
theorem hom_comp_eq_yoneda_map_of_comp_eq_schemeSpaceMap {X : AlgebraicSpaces B S hS}
    {V W : BigFppfOver B S hS} (g : schemeSpace W ⟶ X) (f : X ⟶ schemeSpace V) (α : W ⟶ V)
    (htri : g ≫ f = schemeSpaceMap α) : g.hom ≫ f.hom = yoneda.map α := by
  rw [← schemeSpaceMap_hom α, ← htri]
  rfl

/-- **A chart with affine source over a quasi-separated structure morphism to an affine base is
quasi-compact.** -/
theorem isQuasiCompact_of_comp_eq_schemeSpaceMap {X : AlgebraicSpaces B S hS}
    {V W : BigFppfOver B S hS} (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W)) (g : schemeSpace W ⟶ X)
    (f : X ⟶ schemeSpace V) (hfqs : IsQuasiSeparated B S hS f.hom) (α : W ⟶ V)
    (htri : g ≫ f = schemeSpaceMap α) : IsQuasiCompact B S hS g.hom := by
  have _ := hV
  have _ := hW
  refine isQuasiCompact_of_comp_of_isQuasiSeparated B S hS g.hom f.hom
    (schemeSpace W).property (schemeSpace V).property ?_ hfqs
  rw [hom_comp_eq_yoneda_map_of_comp_eq_schemeSpaceMap B S hS g f α htri]
  exact isQuasiCompact_yoneda_map_of_isAffineHom B S hS α inferInstance

/-- **A chart with affine source over an affine base is quasi-separated.** -/
theorem isQuasiSeparated_of_comp_eq_schemeSpaceMap {X : AlgebraicSpaces B S hS}
    {V W : BigFppfOver B S hS} (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W)) (g : schemeSpace W ⟶ X)
    (f : X ⟶ schemeSpace V) (α : W ⟶ V) (htri : g ≫ f = schemeSpaceMap α) :
    IsQuasiSeparated B S hS g.hom := by
  have _ := hV
  have _ := hW
  refine isQuasiSeparated_of_comp B S hS g.hom f.hom ?_
  rw [hom_comp_eq_yoneda_map_of_comp_eq_schemeSpaceMap B S hS g f α htri]
  exact (isQuasiSeparated_yoneda_map_iff B S hS α).2 inferInstance

namespace ModuleMapSituation

variable {B S hS}

/-! ### `F_zero` as a subfunctor of the base -/

/-- A section of `Y` over an object `U` of the big fppf category over `S`, read as a test scheme
of the situation: the costructured arrow out of `U` that the section names by Yoneda. -/
def zeroTest (D : ModuleMapSituation.{u, u} B S hS) (U : BigFppfOver B S hS)
    (x : D.Y.1.obj (Opposite.op U)) : D.SchemesOver :=
  CostructuredArrow.mk (ObjectProperty.homMk (yonedaEquiv.symm x))

@[simp]
theorem zeroTest_left (D : ModuleMapSituation.{u, u} B S hS) (U : BigFppfOver B S hS)
    (x : D.Y.1.obj (Opposite.op U)) : (D.zeroTest U x).left = U :=
  rfl

@[simp]
theorem zeroTest_hom_hom (D : ModuleMapSituation.{u, u} B S hS) (U : BigFppfOver B S hS)
    (x : D.Y.1.obj (Opposite.op U)) : (D.zeroTest U x).hom.hom = yonedaEquiv.symm x :=
  rfl

/-- **`F_zero` as a subfunctor of the base.**  Its sections over an object `U` of the big fppf
category over `S` are the sections `x` of `Y` over `U` such that the base change of `u` along
`X ×_Y U ⟶ X`, the base change at the test scheme `x` names, is zero. -/
@[stacks 083F "the variant F_zero, read as a subfunctor of the base"]
def zeroSubfunctor (D : ModuleMapSituation.{u, u} B S hS) : Subfunctor D.Y.1 where
  obj U := {x | D.IsZeroAt (modulePullbackSystem B S hS) (D.zeroTest U.unop x)}
  map := by
    intro U V i x hx
    refine D.isZeroAt_of_hom (modulePullbackSystem B S hS)
      (show D.zeroTest V.unop (D.Y.1.map i x) ⟶ D.zeroTest U.unop x from
        CostructuredArrow.homMk i.unop ?_) hx
    apply ObjectProperty.hom_ext
    change yoneda.map i.unop ≫ yonedaEquiv.symm x = yonedaEquiv.symm (D.Y.1.map i x)
    apply yonedaEquiv.injective
    simpa using (yonedaEquiv_naturality (yonedaEquiv.symm x) i.unop).symm

theorem mem_zeroSubfunctor_iff (D : ModuleMapSituation.{u, u} B S hS)
    (U : BigFppfOver B S hS) (x : D.Y.1.obj (Opposite.op U)) :
    x ∈ D.zeroSubfunctor.obj (Opposite.op U) ↔
      D.IsZeroAt (modulePullbackSystem B S hS) (D.zeroTest U x) :=
  Iff.rfl

/-- **The two readings of `F_zero` agree.**  The base change of `u` at a test scheme `T` over
`Y` vanishes exactly when the structure morphism of `T` factors through the subfunctor
`AlgebraicGeometry.Space.ModuleMapSituation.zeroSubfunctor` of `Y`. -/
theorem isZeroAt_iff_exists_factor_zeroSubfunctor (D : ModuleMapSituation.{u, u} B S hS)
    (T : D.SchemesOver) :
    D.IsZeroAt (modulePullbackSystem B S hS) T ↔
      ∃ k : yoneda.obj T.left ⟶ D.zeroSubfunctor.toFunctor,
        k ≫ D.zeroSubfunctor.ι = T.hom.hom := by
  have h : yonedaEquiv.symm (yonedaEquiv T.hom.hom) = T.hom.hom := Equiv.symm_apply_apply _ _
  have hT : D.zeroTest T.left (yonedaEquiv T.hom.hom) = T := by
    simp only [zeroTest]
    rw [h]
    exact (CostructuredArrow.eq_mk T).symm
  have hmem : yonedaEquiv T.hom.hom ∈ D.zeroSubfunctor.obj (Opposite.op T.left) ↔
      D.IsZeroAt (modulePullbackSystem B S hS) T := by
    rw [mem_zeroSubfunctor_iff, hT]
  rw [← hmem, ← exists_factor_iff_mem B S hS D.zeroSubfunctor (yonedaEquiv T.hom.hom), h]

/-- **A subfunctor of `Y` that represents `F_zero` is the vanishing subfunctor.** -/
theorem zeroSubfunctor_eq_of_forall_isZeroAt_iff (D : ModuleMapSituation.{u, u} B S hS)
    (Z : Subfunctor D.Y.1)
    (h : ∀ T : D.SchemesOver, D.IsZeroAt (modulePullbackSystem B S hS) T ↔
      ∃ k : yoneda.obj T.left ⟶ Z.toFunctor, k ≫ Z.ι = T.hom.hom) :
    D.zeroSubfunctor = Z := by
  ext U x
  exact (h (D.zeroTest U.unop x)).trans (exists_factor_iff_mem B S hS Z (A := U.unop) x)

/-! ### The chart step -/

section Chart

variable (D : ModuleMapSituation.{u, u} B S hS) {X' : AlgebraicSpaces B S hS} (g : X' ⟶ D.X)
    (hF : ((modulePullback B S hS g).obj D.F).IsQuasicoherentOnSite)
    (hG : ((modulePullback B S hS g).obj D.G).IsQuasicoherentOnSite)

/-- **The chart step of Stacks 0CWC at the support.**  Let `g : X' ⟶ X` be a flat morphism of
algebraic spaces over `S` whose image contains the support of `𝒢`.  Then the vanishing locus of
`g^*u` over the base is the vanishing locus of `u`. -/
theorem zeroSubfunctor_pullbackSituation_eq (hgflat : IsFlat B S hS g.hom)
    (hGft : SheafOfModules.IsFiniteTypeOnSite D.G)
    (hGsupp : supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj D.G) ⊆
      Set.range (pointsMap B S hS X'.1 g.hom)) :
    D.zeroSubfunctor = (D.pullbackSituation g hF hG).zeroSubfunctor := by
  ext U x
  exact D.isZeroAt_pullbackSituation_iff_of_target g hF hG hgflat hGft hGsupp
    (D.zeroTest U.unop x)

/-! ### The chart step at the relative assassin -/

/-- **At a test scheme the base change of `u` vanishes exactly when the base change of `u'`
does, as soon as the canonical map `𝒢 ⟶ g_*g^*𝒢` stays a monomorphism after base change.** -/
theorem isZeroAt_pullbackSituation_iff_of_mono_unit
    (hmono : ∀ T : D.SchemesOver,
      Mono ((modulePullbackAdjunction B S hS (D.pullbackBaseChangeMap g hF hG T)).unit.app
        ((modulePullback B S hS (D.baseChangeProjection T)).obj D.G)))
    (T : D.SchemesOver) :
    D.IsZeroAt (modulePullbackSystem B S hS) T ↔
      (D.pullbackSituation g hF hG).IsZeroAt (modulePullbackSystem B S hS) T :=
  Iff.trans
    (modulePullback_map_eq_zero_iff_of_mono_unit B S hS (D.pullbackBaseChangeMap g hF hG T)
      (hmono T) (D.baseChangeHom (modulePullbackSystem B S hS) T)).symm
    (D.pullbackBaseChangeMap_map_eq_zero_iff g hF hG (modulePullbackSystem B S hS) T)

/-- **The vanishing locus is unchanged by passing to `X'`, as soon as the canonical map
`𝒢 ⟶ g_*g^*𝒢` stays a monomorphism after base change.** -/
theorem zeroSubfunctor_pullbackSituation_eq_of_mono_unit
    (hmono : ∀ T : D.SchemesOver,
      Mono ((modulePullbackAdjunction B S hS (D.pullbackBaseChangeMap g hF hG T)).unit.app
        ((modulePullback B S hS (D.baseChangeProjection T)).obj D.G))) :
    D.zeroSubfunctor = (D.pullbackSituation g hF hG).zeroSubfunctor := by
  ext U x
  exact D.isZeroAt_pullbackSituation_iff_of_mono_unit g hF hG hmono (D.zeroTest U.unop x)

/-- **The chart step of Stacks 0CWC at the relative assassin.**  In the situation of Stacks
083F, with `f : X ⟶ Y` locally of finite type and `𝒢` of finite type and flat over `Y`, let
`g : X' ⟶ X` be flat with

`Ass_{X/Y}(𝒢) ⊆ g(|X'|)`.

Then, under the hypotheses `h03M1`, `h0CU0` and `h0CVL`, the vanishing locus of `u` and that of
`u' = g^*u` agree as subfunctors of `Y`.  The hypothesis `h03M1`,
`AlgebraicGeometry.Space.UnitKernelQuasicoherentInput`, is false. -/
theorem zeroSubfunctor_pullbackSituation_eq_of_relativeWeaklyAssociatedPoints_subset_range
    (h03M1 : UnitKernelQuasicoherentInput B S hS)
    (h0CU0 : WeaklyAssociatedVanishingInput B S hS)
    (h0CVL : WeaklyAssociatedSubsetRelativeInput B S hS)
    (hgflat : IsFlat B S hS g.hom) (hf : IsLocallyOfFiniteType B S hS D.f.hom)
    (hGft : SheafOfModules.IsFiniteTypeOnSite D.G)
    (hGflat : IsFlatOver B S hS D.X.2 D.f.hom D.G)
    (hGass : relativeWeaklyAssociatedPoints B S hS D.f D.G ⊆
      Set.range (pointsMap B S hS X'.1 g.hom)) :
    D.zeroSubfunctor = (D.pullbackSituation g hF hG).zeroSubfunctor := by
  have := D.quasicoherent_G
  have : SheafOfModules.IsFiniteType D.G :=
    Stacks.SheafOfModules.isFiniteType_of_isFiniteTypeOnSite _ hGft
  refine D.zeroSubfunctor_pullbackSituation_eq_of_mono_unit g hF hG fun T => ?_
  exact mono_unit_baseChange_of_relativeWeaklyAssociatedPoints_subset_range' B S hS h03M1 h0CU0
    h0CVL (D.isPullback_baseChangeSpace T)
    (D.isPullback_pullbackBaseChangeMap g hF hG T).flip hf hgflat D.G hGflat hGass

/-- **For a quasi-compact and quasi-separated flat chart whose image contains `Ass_{X/Y}(𝒢)`,
the canonical map `𝒢 ⟶ g_*g^*𝒢` stays a monomorphism after every base change.** -/
theorem mono_unit_pullbackBaseChangeMap_of_qcqs
    (h0CVL : WeaklyAssociatedSubsetRelativeInput B S hS)
    (hgflat : IsFlat B S hS g.hom) (hgqc : IsQuasiCompact B S hS g.hom)
    (hgqs : IsQuasiSeparated B S hS g.hom) (hf : IsLocallyOfFiniteType B S hS D.f.hom)
    (hGft : SheafOfModules.IsFiniteTypeOnSite D.G)
    (hGflat : IsFlatOver B S hS D.X.2 D.f.hom D.G)
    (hGass : relativeWeaklyAssociatedPoints B S hS D.f D.G ⊆
      Set.range (pointsMap B S hS X'.1 g.hom)) :
    ∀ T : D.SchemesOver,
      Mono ((modulePullbackAdjunction B S hS (D.pullbackBaseChangeMap g hF hG T)).unit.app
        ((modulePullback B S hS (D.baseChangeProjection T)).obj D.G)) := by
  have := D.quasicoherent_G
  have : SheafOfModules.IsFiniteType D.G :=
    Stacks.SheafOfModules.isFiniteType_of_isFiniteTypeOnSite _ hGft
  intro T
  exact mono_unit_baseChange_of_relativeWeaklyAssociatedPoints_subset_range_of_qcqs B S hS
    h0CVL (D.isPullback_baseChangeSpace T)
    (D.isPullback_pullbackBaseChangeMap g hF hG T).flip hf hgflat hgqc hgqs D.G hGflat hGass

/-- **The chart step of Stacks 0CWC at the relative assassin, for a quasi-compact and
quasi-separated chart.**  In the situation of Stacks 083F, with `f : X ⟶ Y` locally of finite
type and `𝒢` of finite type and flat over `Y`, let `g : X' ⟶ X` be flat, quasi-compact and
quasi-separated with `Ass_{X/Y}(𝒢) ⊆ g(|X'|)`.  Then the vanishing locus of `u` and that of
`u' = g^*u` agree as subfunctors of `Y`. -/
theorem zeroSubfunctor_pullbackSituation_eq_of_relativeWeaklyAssociatedPoints_subset_range_of_qcqs
    (h0CVL : WeaklyAssociatedSubsetRelativeInput B S hS)
    (hgflat : IsFlat B S hS g.hom) (hgqc : IsQuasiCompact B S hS g.hom)
    (hgqs : IsQuasiSeparated B S hS g.hom) (hf : IsLocallyOfFiniteType B S hS D.f.hom)
    (hGft : SheafOfModules.IsFiniteTypeOnSite D.G)
    (hGflat : IsFlatOver B S hS D.X.2 D.f.hom D.G)
    (hGass : relativeWeaklyAssociatedPoints B S hS D.f D.G ⊆
      Set.range (pointsMap B S hS X'.1 g.hom)) :
    D.zeroSubfunctor = (D.pullbackSituation g hF hG).zeroSubfunctor :=
  D.zeroSubfunctor_pullbackSituation_eq_of_mono_unit g hF hG
    (D.mono_unit_pullbackBaseChangeMap_of_qcqs g hF hG h0CVL hgflat hgqc hgqs hf hGft hGflat
      hGass)

end Chart

/-! ### The hypotheses of Stacks 0CWC -/

/-- The situation of Stacks 0CV6 formed by the morphism `f` of Stacks 083F and the **target**
module `𝒢` of the map, at a point `y` of the base.  Purity of `𝒢` relative to `Y`, hypothesis
(2) of Stacks 0CWC, is `AlgebraicGeometry.Space.IsPureRelative` of this situation. -/
def targetPrePureSituation (D : ModuleMapSituation.{u, u} B S hS)
    (hft : IsFiniteType B S hS D.f.hom) (hdec : IsDecent B S hS D.f.hom)
    (hGft : SheafOfModules.IsFiniteTypeOnSite D.G) (y : points B S hS D.Y.1) :
    PrePureSituation.{u, u} B S hS where
  X := D.X.1
  Y := D.Y.1
  hX := D.X.2
  hY := D.Y.2
  f := D.f.hom
  finiteType := hft
  decent := hdec
  F := D.G
  moduleFiniteType := hGft
  moduleQuasicoherent := D.quasicoherent_G
  y := y

/-- There are a flat chart `g : X' ⟶ X` whose image contains the support of `𝒢` and a closed
subspace `Z` of the base through which a test scheme factors exactly when `g^*u` base changes
to zero at it. -/
def HasFlatChartWithClosedZeroLocus (D : ModuleMapSituation.{u, u} B S hS) : Prop :=
  ∃ (X' : AlgebraicSpaces B S hS) (g : X' ⟶ D.X)
    (hF : ((modulePullback B S hS g).obj D.F).IsQuasicoherentOnSite)
    (hG : ((modulePullback B S hS g).obj D.G).IsQuasicoherentOnSite)
    (Z : Subfunctor D.Y.1),
    IsFlat B S hS g.hom ∧
      supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj D.G) ⊆
        Set.range (pointsMap B S hS X'.1 g.hom) ∧
      IsClosedSubspace B S hS Z ∧
      ∀ T : D.SchemesOver,
        (D.pullbackSituation g hF hG).IsZeroAt (modulePullbackSystem B S hS) T ↔
          ∃ k : yoneda.obj T.left ⟶ Z.toFunctor, k ≫ Z.ι = T.hom.hom

/-! ### `HasFlatChartWithClosedZeroLocus` -/

/-- **Closedness of a chart's vanishing locus is closedness of the situation's.**  For a flat
chart whose image contains the support of `𝒢`, the vanishing subfunctor of the chart situation
is a closed subspace exactly when that of the original situation is. -/
theorem isClosedSubspace_pullbackSituation_zeroSubfunctor_iff
    (D : ModuleMapSituation.{u, u} B S hS) {X' : AlgebraicSpaces B S hS} (g : X' ⟶ D.X)
    (hF : ((modulePullback B S hS g).obj D.F).IsQuasicoherentOnSite)
    (hG : ((modulePullback B S hS g).obj D.G).IsQuasicoherentOnSite)
    (hgflat : IsFlat B S hS g.hom) (hGft : SheafOfModules.IsFiniteTypeOnSite D.G)
    (hGsupp : supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj D.G) ⊆
      Set.range (pointsMap B S hS X'.1 g.hom)) :
    IsClosedSubspace B S hS (D.pullbackSituation g hF hG).zeroSubfunctor ↔
      IsClosedSubspace B S hS D.zeroSubfunctor := by
  rw [D.zeroSubfunctor_pullbackSituation_eq g hF hG hgflat hGft hGsupp]

/-- `AlgebraicGeometry.Space.ModuleMapSituation.HasFlatChartWithClosedZeroLocus` holds exactly
when some flat chart whose image contains the support of `𝒢` exists and the vanishing
subfunctor of the base is a closed subspace. -/
theorem hasFlatChartWithClosedZeroLocus_iff (D : ModuleMapSituation.{u, u} B S hS)
    (hGft : SheafOfModules.IsFiniteTypeOnSite D.G) :
    D.HasFlatChartWithClosedZeroLocus ↔
      (∃ (X' : AlgebraicSpaces B S hS) (g : X' ⟶ D.X),
        ((modulePullback B S hS g).obj D.F).IsQuasicoherentOnSite ∧
        ((modulePullback B S hS g).obj D.G).IsQuasicoherentOnSite ∧
        IsFlat B S hS g.hom ∧
        supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj D.G) ⊆
          Set.range (pointsMap B S hS X'.1 g.hom)) ∧
      IsClosedSubspace B S hS D.zeroSubfunctor := by
  constructor
  · rintro ⟨X', g, hF, hG, Z, hgflat, hGsupp, hclosed, hrep⟩
    refine ⟨⟨X', g, hF, hG, hgflat, hGsupp⟩, ?_⟩
    rw [← D.isClosedSubspace_pullbackSituation_zeroSubfunctor_iff g hF hG hgflat hGft hGsupp,
      (D.pullbackSituation g hF hG).zeroSubfunctor_eq_of_forall_isZeroAt_iff Z hrep]
    exact hclosed
  · rintro ⟨⟨X', g, hF, hG, hgflat, hGsupp⟩, hclosed⟩
    exact ⟨X', g, hF, hG, (D.pullbackSituation g hF hG).zeroSubfunctor, hgflat, hGsupp,
      (D.isClosedSubspace_pullbackSituation_zeroSubfunctor_iff g hF hG hgflat hGft
        hGsupp).mpr hclosed,
      (D.pullbackSituation g hF hG).isZeroAt_iff_exists_factor_zeroSubfunctor⟩

/-! ### The inputs of Stacks 0CWC -/

/-- **The sections of `𝒢` along an affine chart are projective over the functions on the
affine base.**  For a chart `g : W ⟶ X` out of a scheme `W` of the site and a morphism
`α : W ⟶ V` of the site under it, the sections `Γ(W, g^*𝒢)`, the Zariski module
`AlgebraicGeometry.Space.baseChangeModule` read on `W`, form a projective module over
`Γ(V, 𝒪_V)`, the scalars acting through `α`. -/
def ChartSectionsProjective (D : ModuleMapSituation.{u, u} B S hS)
    (V W : BigFppfOver B S hS) (g : schemeSpace W ⟶ D.X) (α : W ⟶ V) : Prop :=
  let M := baseChangeModule B S hS D.G W g.hom
  let : Module Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) (Γ(M, ⊤) : Type u) :=
    Module.compHom _ ((BigFppfOver.toScheme B S hS).map α).appTop.hom
  Module.Projective Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) (Γ(M, ⊤) : Type u)

/-- **Affine flat charts étale locally on the base.**  For every point `y` of `Y` there is an
affine étale neighbourhood `V ⟶ Y` of `y` and, over the base change to `V`, a flat chart
`g : W ⟶ X_V` with affine source and a morphism `α : W ⟶ V` of the site under it, whose image
on points contains the relative weak assassin `Ass_{X_V/V}(𝒢_V)` and along which the sections
of `g^*𝒢_V` are projective over the functions on `V`. -/
def HasAffineFlatChartEtaleLocallyOnBase (D : ModuleMapSituation.{u, u} B S hS) : Prop :=
  ∀ y : points B S hS D.Y.1,
    ∃ (V : BigFppfOver B S hS) (b : schemeSpace V ⟶ D.Y),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
      IsEtale B S hS b.hom ∧
      y ∈ Set.range (pointsMap B S hS (schemeSpace V).1 b.hom) ∧
      ∃ (W : BigFppfOver B S hS) (g : schemeSpace W ⟶ (D.baseChangeTarget b).X)
        (_ : ((modulePullback B S hS g).obj (D.baseChangeTarget b).F).IsQuasicoherentOnSite)
        (_ : ((modulePullback B S hS g).obj (D.baseChangeTarget b).G).IsQuasicoherentOnSite)
        (α : W ⟶ V),
        IsAffine ((BigFppfOver.toScheme B S hS).obj W) ∧
          IsFlat B S hS g.hom ∧
          g ≫ (D.baseChangeTarget b).f = schemeSpaceMap α ∧
          relativeWeaklyAssociatedPoints B S hS (D.baseChangeTarget b).f
              (D.baseChangeTarget b).G ⊆
            Set.range (pointsMap B S hS (schemeSpace W).1 g.hom) ∧
          (D.baseChangeTarget b).ChartSectionsProjective V W g α

/-- **The dévissage of Stacks 0CWC.**  Every situation of Stacks 083F satisfying the hypotheses
of Stacks 0CWC, namely `f` of finite presentation and `𝒢` of finite presentation, flat over the
base and pure relative to it, has, étale locally on its base and over an affine, a flat chart
with affine source whose image carries `Ass_{X/Y}(𝒢)` and along which the sections of `g^*𝒢`
are projective over the functions on the base. -/
def DevissageInput (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) : Prop :=
  ∀ (D : ModuleMapSituation.{u, u} B S hS),
    IsFinitePresentation B S hS D.f.hom →
    SheafOfModules.IsFinitePresentationOnSite D.G →
    _root_.AlgebraicGeometry.Space.IsFlatOver B S hS D.X.2 D.f.hom D.G →
    ∀ (hft : IsFiniteType B S hS D.f.hom) (hdec : IsDecent B S hS D.f.hom)
      (hGft : SheafOfModules.IsFiniteTypeOnSite D.G),
      (∀ y : points B S hS D.Y.1,
        IsPureRelative (D.targetPrePureSituation hft hdec hGft y)) →
      D.HasAffineFlatChartEtaleLocallyOnBase

/-- **The affine endgame of Stacks 0CWC**, after Stacks 083L.  For `𝒢` of finite type and flat
over an affine base, and along a flat chart with affine source along which the sections of
`g^*𝒢` are projective over the functions on the base, the vanishing locus of the chart's map is
a closed subspace of the base. -/
def AffineChartZeroLocusClosed (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    Prop :=
  ∀ (D : ModuleMapSituation.{u, u} B S hS) (V W : BigFppfOver B S hS),
    IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
    IsAffine ((BigFppfOver.toScheme B S hS).obj W) →
    ∀ (hDY : D.Y = schemeSpace V) (g : schemeSpace W ⟶ D.X)
      (hF : ((modulePullback B S hS g).obj D.F).IsQuasicoherentOnSite)
      (hG : ((modulePullback B S hS g).obj D.G).IsQuasicoherentOnSite)
      (α : W ⟶ V),
      IsFlat B S hS g.hom →
      SheafOfModules.IsFiniteTypeOnSite D.G →
      _root_.AlgebraicGeometry.Space.IsFlatOver B S hS D.X.2 D.f.hom D.G →
      g ≫ D.f ≫ eqToHom hDY = schemeSpaceMap α →
      D.ChartSectionsProjective V W g α →
      IsClosedSubspace B S hS (D.pullbackSituation g hF hG).zeroSubfunctor

/-- **The descent step of the proof of Stacks 0CWC**: closedness of the vanishing subfunctor is
étale local on the base.  If every point of `Y` lies in the image of an étale `b : Y' ⟶ Y` over
which the vanishing subfunctor of the base change is a closed subspace, then the vanishing
subfunctor of `Y` is a closed subspace. -/
def ZeroLocusClosedEtaleLocalOnBase (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : Prop :=
  ∀ (D : ModuleMapSituation.{u, u} B S hS),
    (∀ y : points B S hS D.Y.1,
      ∃ (Y' : AlgebraicSpaces B S hS) (b : Y' ⟶ D.Y),
        IsEtale B S hS b.hom ∧
        y ∈ Set.range (pointsMap B S hS Y'.1 b.hom) ∧
        IsClosedSubspace B S hS (D.baseChangeTarget b).zeroSubfunctor) →
    IsClosedSubspace B S hS D.zeroSubfunctor

end ModuleMapSituation

end AlgebraicGeometry.Space

end
