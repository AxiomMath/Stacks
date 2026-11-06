module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyProjective
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.CategoryTheory.Sites.Modules.Flat
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRetract
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleTypesUnderEquivalence
import StacksFrontier.AlgebraicGeometry.Descent.ModuleFiniteness.FiniteType
import StacksFrontier.AlgebraicGeometry.Descent.ModuleFiniteness.Flat
import StacksFrontier.AlgebraicGeometry.Descent.Modules.FpqcLocallyProjective
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
import StacksFrontier.AlgebraicGeometry.Spaces.FpqcCoveringBaseChange
import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FpqcCoverings

/-!
# Descent of finiteness properties of modules along an fpqc covering of algebraic spaces

Let `X` be an algebraic space over a scheme `S` and let `𝓕` be a quasi-coherent `𝒪_X`-module.
Stacks 060U, 060W and 060Y assert that if `{f_i : X_i → X}` is an fpqc covering of algebraic
spaces for which every `f_i^*𝓕` is of finite type, flat, or locally projective, then `𝓕` has
that property.  The source deduces each from the corresponding statement for schemes — Stacks
05AZ, 05B1 and 05JZ — by étale localization.  This file carries out that localization: an fpqc
covering of `X` pulled back along an étale scheme chart `U → X` and refined by scheme atlases
is an fpqc covering of the scheme `U` whose members are étale charts of the `X_i`, so each of
the three scheme-level statements applies to the restriction `𝓕|_U`.

Each of the three properties is read on the restrictions `𝓕|_U` to the étale scheme charts, as
`AlgebraicGeometry.Space.IsLocallyProjective` of Stacks 060R and
`AlgebraicGeometry.Space.IsFlatOver` of Stacks 05VV read local projectivity and relative
flatness.

## Main definitions

* `AlgebraicGeometry.Space.ChartRestrictionBaseChange`: the base-change comparison for the
  restriction of a quasi-coherent module to an étale scheme chart, as a proposition.

## Main results

* `AlgebraicGeometry.Space.exists_chart_fpqc_refinement`: an fpqc covering of an algebraic
  space, pulled back along an étale scheme chart and refined by scheme atlases, is an fpqc
  covering of the chart's scheme whose members are étale charts of the members of the original
  covering.
* `AlgebraicGeometry.Space.schemeCover_of_fpqcYoneda`: an fpqc covering of algebraic spaces
  whose members and whose target are schemes of the site is an fpqc covering of schemes, and
  `AlgebraicGeometry.Space.fpqc_of_yoneda_refinements` is the criterion it rests on.
* `AlgebraicGeometry.Space.chartRestrictionBaseChange`: that comparison, **proved**.
* `AlgebraicGeometry.Space.isFiniteType_of_pullback_fpqc`: **Stacks 060U**,
  `AlgebraicGeometry.Space.isFlat_of_pullback_fpqc`: **Stacks 060W**, and
  `AlgebraicGeometry.Space.isLocallyProjective_of_pullback_fpqc`: **Stacks 060Y**.

## Implementation notes

The base-change comparison `AlgebraicGeometry.Space.ChartRestrictionBaseChange` — the
identification of the inverse image of `𝓕|_V` along a morphism of chart schemes with the
restriction `(a^*𝓕)|_W` of the inverse image, which is the compatibility of the chart
restriction of Stacks 03M0 with the pullback of Stacks 03LW — used to be a hypothesis of all
three statements.  It is now proved, in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionBaseChange.lean`, and
`AlgebraicGeometry.Space.chartRestrictionBaseChange` records it in the shape the proposition
asks for; the three statements consume it rather than assume it.  The proposition itself is
kept, since it names the comparison for the files which still refer to it.

Quasi-coherence of the restrictions `𝓕|_U` is a second hypothesis of each statement, as it is of
the results of `StacksFrontier/AlgebraicGeometry/Spaces/FlatFiniteTypeModuleLocus.lean`.  It is
`AlgebraicGeometry.Space.IsQuasicoherentOnCharts`, and it is no longer an assumption one has to
make: `AlgebraicGeometry.Space.isQuasicoherent_restrictToChart`
(`StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionCoherent.lean`) deduces it from
quasi-coherence of `𝓕` on the small étale site, by identifying the chart restriction with
`AlgebraicGeometry.Space.chartSchemeModule`.  The statements below are left carrying it so that
they apply to a module quasi-coherent on the charts without being quasi-coherent on the site.

The module universe is the universe `u` of the structure rings.  That is forced: the chart
restriction raises an arbitrary module universe `m` to `max u m`, and at `m > u` it no longer
lands in `AlgebraicGeometry.Scheme.Modules` of the chart, which is what
`AlgebraicGeometry.Scheme.Modules.pullback` and the three scheme-level statements consume.

`AlgebraicGeometry.Space.fpqc_of_yoneda_refinements` is stated for a family of morphisms of the
big fppf site rather than for an fpqc covering, because the quasi-compactness half of the
scheme-level fpqc condition is checked on the affine opens of the target, which are objects of
the site rather than members of the covering.

## References

* [Stacks Project, Tag 060U](https://stacks.math.columbia.edu/tag/060U)
* [Stacks Project, Tag 060W](https://stacks.math.columbia.edu/tag/060W)
* [Stacks Project, Tag 060Y](https://stacks.math.columbia.edu/tag/060Y)
* [Stacks Project, Tag 05AZ](https://stacks.math.columbia.edu/tag/05AZ)
* [Stacks Project, Tag 05B1](https://stacks.math.columbia.edu/tag/05B1)
* [Stacks Project, Tag 05JZ](https://stacks.math.columbia.edu/tag/05JZ)
* [Stacks Project, Tag 0419](https://stacks.math.columbia.edu/tag/0419)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace.Opens Opposite

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
private instance (priority := high) hasPullback_presheaf
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### From fpqc coverings of representable presheaves to fpqc coverings of schemes -/

/-- The morphisms of the big fppf site of `S` whose underlying morphism of schemes is étale
contain the identities and are closed under composition. -/
private theorem inverseImage_etale_isMultiplicative :
    MorphismProperty.IsMultiplicative
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) where
  id_mem X := by
    show Etale ((BigFppfOver.toScheme B S hS).map (𝟙 X))
    rw [(BigFppfOver.toScheme B S hS).map_id]
    infer_instance
  comp_mem f g hf hg := by
    change Etale ((BigFppfOver.toScheme B S hS).map f) at hf
    change Etale ((BigFppfOver.toScheme B S hS).map g) at hg
    show Etale ((BigFppfOver.toScheme B S hS).map (f ≫ g))
    rw [Functor.map_comp]
    exact Etale.etale_comp _ _

/-- Flatness of a morphism of schemes of the site, read off from flatness of the induced
morphism of representable presheaves. -/
theorem flat_of_isFlat_yoneda (U V : BigFppfOver B S hS) (g : U ⟶ V)
    (hg : IsFlat B S hS (yoneda.map g)) :
    Flat ((BigFppfOver.toScheme B S hS).map g) := by
  let E : MorphismProperty (BigFppfOver B S hS) :=
    MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)
  let : MorphismProperty.IsMultiplicative E := inverseImage_etale_isMultiplicative B S hS
  let : MorphismProperty.RespectsIso E :=
    MorphismProperty.RespectsIso.inverseImage (@Etale.{u}) (BigFppfOver.toScheme B S hS)
  let : MorphismProperty.IsMultiplicative E.presheaf :=
    MorphismProperty.relative_isMultiplicative E
  have hid (W : BigFppfOver B S hS) : E.presheaf (yoneda.map (𝟙 W)) := by
    simpa using (show E.presheaf (𝟙 (yoneda.obj W)) from MorphismProperty.id_mem _ _)
  exact hg U V (yoneda.map (𝟙 U)) (yoneda.map (𝟙 V)) g (hid U) (hid V) (by simp)

/-- A family of morphisms of schemes of the site whose members are flat and which, over every
affine scheme-valued point of the target, is refined by a finite fpqc covering by affines, is
an fpqc covering of schemes. -/
theorem fpqc_of_yoneda_refinements {V : BigFppfOver B S hS} (W : PreZeroHypercover.{v} V)
    (hflat : ∀ i, Flat ((BigFppfOver.toScheme B S hS).map (W.f i)))
    (hrefine : ∀ (T : BigAffineFppf B S hS) (h : (BigAffineFppf.inclusion B S hS).obj T ⟶ V),
      ∃ R : PreZeroHypercover.{u + 1} T, Finite R.I₀ ∧
        Presieve.map (BigAffineFppf.toScheme B S hS) R.presieve₀ ∈
          Scheme.fpqcPrecoverage ((BigAffineFppf.toScheme B S hS).obj T) ∧
        ∀ j, ∃ i, ∃ a : (BigAffineFppf.inclusion B S hS).obj (R.X j) ⟶ W.X i,
          a ≫ W.f i = (BigAffineFppf.inclusion B S hS).map (R.f j) ≫ h) :
    (W.map (BigFppfOver.toScheme B S hS)).presieve₀ ∈
      Scheme.fpqcPrecoverage ((BigFppfOver.toScheme B S hS).obj V) := by
  classical
  let F := BigFppfOver.toScheme B S hS
  let A := BigAffineFppf.inclusion B S hS
  have hqc : QuasiCompactCover (W.map F) := by
    constructor
    intro O hO
    have hm : B.Contains O.toScheme :=
      (Scheme.size_coe_opens_le (F.obj V) O).trans_lt V.left.2
    let m : B.obj hm ⟶ V.left := B.inclusion.preimage O.ι
    let T : BigAffineFppf B S hS := ⟨Over.mk (m ≫ V.hom), hO⟩
    let t : A.obj T ⟶ V := Over.homMk m rfl
    have ht : F.map t = O.ι := B.inclusion.map_preimage (X := B.obj hm) (Y := V.left) O.ι
    obtain ⟨R, hfin, hcov, hfac⟩ := hrefine T t
    let R' := R.map (BigAffineFppf.toScheme B S hS)
    have hcov' : R'.presieve₀ ∈ Scheme.fpqcPrecoverage O.toScheme := by
      show (R.map (BigAffineFppf.toScheme B S hS)).presieve₀ ∈
        Scheme.fpqcPrecoverage ((BigAffineFppf.toScheme B S hS).obj T)
      rw [PreZeroHypercover.presieve₀_map]
      exact hcov
    have hsurj := (Scheme.presieve₀_mem_precoverage_iff R').mp hcov'.2 |>.1
    choose i a ha using hfac
    have : Finite R.I₀ := hfin
    have (j : R.I₀) : IsAffine (R'.X j) := (R.X j).property
    let k : (j : R.I₀) → R'.X j → F.obj V := fun j => R'.f j ≫ O.ι
    have hc : IsCompactOpenCovered k (O : Set (F.obj V)) := by
      refine .of_finite (fun j : R.I₀ => j) (fun _ => ⊤) (fun _ => isCompact_univ) ?_
      ext x
      simp only [Set.mem_iUnion, Set.mem_image, TopologicalSpace.Opens.coe_top,
        Set.mem_univ, true_and]
      constructor
      · rintro ⟨j, y, rfl⟩
        exact (R'.f j y).2
      · intro hx
        obtain ⟨j, y, hy⟩ := hsurj ⟨x, hx⟩
        exact ⟨j, y, congrArg Subtype.val hy⟩
    apply IsCompactOpenCovered.of_comp (a := i) k
      (fun j => F.map (a j)) (fun _ => Scheme.Hom.continuous _) ?_
      (fun _ => Scheme.Hom.continuous _) O.isOpen hc
    intro j
    have he := congrArg F.map (ha j)
    rw [Functor.map_comp, Functor.map_comp, ht] at he
    funext x
    exact congrArg (fun k : R'.X j ⟶ F.obj V => k x) he.symm
  exact ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.mpr hqc,
    (Scheme.presieve₀_mem_precoverage_iff (W.map F)).mpr
      ⟨fun x => by
        obtain ⟨O, hO, hx, -⟩ :=
          TopologicalSpace.Opens.isBasis_iff_nbhd.mp
            (F.obj V).isBasis_affineOpens (mem_top x)
        obtain ⟨s, hs, V', hc, he⟩ := hqc.isCompactOpenCovered_of_isAffineOpen hO
        change x ∈ (O : Set (F.obj _)) at hx
        rw [← he] at hx
        simp only [Set.mem_iUnion, Set.mem_image] at hx
        obtain ⟨i, -, y, -, hxy⟩ := hx
        exact ⟨i, y, hxy⟩, hflat⟩⟩

/-- An fpqc covering of algebraic spaces all of whose members and whose target are schemes of
the site is an fpqc covering of schemes. -/
theorem schemeCover_of_fpqcYoneda {I : Type v} (V : BigFppfOver B S hS)
    (T : I → BigFppfOver B S hS) (g : ∀ i, T i ⟶ V)
    (hg : IsFpqcCovering B S hS fun i ↦ yoneda.map (g i)) :
    ((⟨I, T, g⟩ : PreZeroHypercover V).map (BigFppfOver.toScheme B S hS)).presieve₀ ∈
      Scheme.fpqcPrecoverage ((BigFppfOver.toScheme B S hS).obj V) := by
  apply fpqc_of_yoneda_refinements B S hS (⟨I, T, g⟩ : PreZeroHypercover V)
  · exact fun i ↦ flat_of_isFlat_yoneda B S hS (T i) V (g i) (hg.1 i)
  · intro A k
    obtain ⟨R, hfinite, hcover, hfactor⟩ := hg.2 A (yoneda.map k)
    refine ⟨R, hfinite, hcover, fun j ↦ ?_⟩
    obtain ⟨i, a, ha⟩ := hfactor j
    refine ⟨i, Yoneda.fullyFaithful.preimage a, ?_⟩
    apply Yoneda.fullyFaithful.map_injective
    simpa only [Functor.map_comp, Yoneda.fullyFaithful.map_preimage] using ha

/-! ### Étale localization of an fpqc covering -/

/-- Pulling an fpqc covering of an algebraic space back along an étale scheme chart and
refining it by scheme atlases gives an fpqc covering of the chart's scheme whose members are
étale charts of the members of the original covering. -/
theorem exists_chart_fpqc_refinement {I : Type v} {X : AlgebraicSpaces B S hS}
    (Xᵢ : I → AlgebraicSpaces B S hS) (f : ∀ i, Xᵢ i ⟶ X)
    (hf : IsFpqcCovering B S hS fun i ↦ (f i).hom) (V : SmallEtale B S hS X.obj) :
    ∃ (T : I → BigFppfOver B S hS) (c : ∀ i, yoneda.obj (T i) ⟶ (Xᵢ i).obj)
      (g : ∀ i, T i ⟶ V.obj.left),
      (∀ i, IsEtaleChart B S hS (Xᵢ i).obj (CostructuredArrow.mk (c i))) ∧
      Presieve.ofArrows (fun i ↦ (BigFppfOver.toScheme B S hS).obj (T i))
          (fun i ↦ (BigFppfOver.toScheme B S hS).map (g i)) ∈
        Scheme.fpqcPrecoverage (etaleChartScheme B S hS V) ∧
      ∀ i, yoneda.map (g i) ≫ V.obj.hom = c i ≫ (f i).hom := by
  classical
  let Vs : AlgebraicSpaces B S hS :=
    ⟨yoneda.obj V.obj.left, isAlgebraicSpace_yoneda B S hS V.obj.left⟩
  let v : Vs ⟶ X := ObjectProperty.homMk V.obj.hom
  have hv : IsEtale B S hS v.hom :=
    (isEtale_iff_presheaf_of_yoneda B S hS V.obj.hom).2 V.property
  let Y : I → AlgebraicSpaces B S hS := fun i ↦ AlgebraicSpaces.fiberProduct B S hS (f i) v
  let p : ∀ i, Y i ⟶ Xᵢ i := fun i ↦ ObjectProperty.homMk (pullback.fst (f i).hom v.hom)
  let q : ∀ i, Y i ⟶ Vs := fun i ↦ ObjectProperty.homMk (pullback.snd (f i).hom v.hom)
  have hpetale : ∀ i, IsEtale B S hS (p i).hom := fun i ↦
    isEtale_of_isPullback B S hS (q i) (p i) v (f i)
      (AlgebraicSpaces.isPullback_fiberProduct B S hS (f i) v).flip hv
  choose T e hsurj hetale using fun i ↦ (Y i).property.exists_atlas
  have hee (i : I) : IsEtale B S hS (e i) :=
    (isEtale_iff_presheaf_of_yoneda B S hS (e i)).2 (hetale i)
  have hEtaleCovering (i : I) :
      IsEtaleCovering B S hS (fun _ : Unit ↦ yoneda.obj (T i)) (fun _ ↦ e i) := by
    refine ⟨(Y i).property, fun _ ↦ isAlgebraicSpace_yoneda B S hS (T i),
      fun _ ↦ hee i, ?_⟩
    rw [Set.iUnion_const, Set.range_eq_univ]
    exact (surjective_iff_surjective_pointsMap B S hS (Y i).obj (Y i).property
      (T i) (e i)).1 (hsurj i)
  have hcomp : IsFpqcCovering B S hS fun i ↦ e i ≫ (q i).hom :=
    isFpqcCovering_reindex B S hS
      (isFpqcCovering_comp B S hS (X := Vs.obj) (Xi := fun i ↦ (Y i).obj)
        (Xij := fun ij : Σ _ : I, Unit ↦ yoneda.obj (T ij.1)) Vs.property
        (fun i ↦ (Y i).property) (fun i _ ↦ isAlgebraicSpace_yoneda B S hS (T i))
        (fun i ↦ (q i).hom) (fun i _ ↦ e i) (isFpqcCovering_pullback B S hS f v hf)
        (fun i ↦ isFpqcCovering_of_isEtaleCovering B S hS
          (fun _ : Unit ↦ yoneda.obj (T i)) (fun _ ↦ e i) (hEtaleCovering i)))
      (σ := fun i : I ↦ (⟨i, ()⟩ : Σ _ : I, Unit)) (fun r ↦ ⟨r.1, by cases r.2; rfl⟩)
  let g : ∀ i, T i ⟶ V.obj.left := fun i ↦ Yoneda.fullyFaithful.preimage (e i ≫ (q i).hom)
  have hg : ∀ i, yoneda.map (g i) = e i ≫ (q i).hom := fun i ↦
    Yoneda.fullyFaithful.map_preimage _
  refine ⟨T, fun i ↦ e i ≫ (p i).hom, g, fun i ↦ ?_, ?_, fun i ↦ ?_⟩
  · exact (isEtale_iff_presheaf_of_yoneda B S hS (e i ≫ (p i).hom)).1
      (isEtale_comp B S hS (hee i) (hpetale i))
  · exact schemeCover_of_fpqcYoneda B S hS V.obj.left T g (by simpa only [hg] using hcomp)
  · rw [hg i, Category.assoc, Category.assoc]
    exact e i ≫= (pullback.condition (f := (f i).hom) (g := v.hom)).symm

/-! ### Descent of the three properties -/

/-- The base-change comparison for the restriction of a quasi-coherent module to an étale
scheme chart: for a morphism `a : X ⟶ Z` of algebraic spaces, a quasi-coherent `𝒪_Z`-module
`G`, an étale chart `W` of `X` and an étale chart `V` of `Z` joined by a morphism `g` of the
underlying schemes of the site over `a`, the inverse image of `G|_V` along `g` is the
restriction `(a^*G)|_W` of the inverse image. -/
abbrev ChartRestrictionBaseChange :=
  ∀ {X Z : AlgebraicSpaces B S hS} (a : X ⟶ Z)
    (G : Modules.{u, u} B S hS Z.obj Z.property), G.IsQuasicoherentOnSite →
    ∀ (V : SmallEtale B S hS Z.obj) (W : SmallEtale B S hS X.obj)
      (g : W.obj.left ⟶ V.obj.left),
      yoneda.map g ≫ V.obj.hom = W.obj.hom ≫ a.hom →
      ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).obj
          (restrictToChart B S hS Z.property G V) ≅
        restrictToChart B S hS X.property ((modulePullback B S hS a).obj G) W)

/-- **The base-change comparison for the restriction of a quasi-coherent module to an étale
scheme chart**, in the shape `AlgebraicGeometry.Space.ChartRestrictionBaseChange` asks for.

This is `AlgebraicGeometry.Space.restrictToChartBaseChangeIso`, the compatibility of Stacks 03M0
with Stacks 03LW. -/
noncomputable def chartRestrictionBaseChange : ChartRestrictionBaseChange B S hS :=
  fun a G hG V W g hg ↦ restrictToChartBaseChangeIso B S hS a G hG V W g hg

/-- Local projectivity of a module on a scheme transports along an isomorphism. -/
private theorem isLocallyProjective_of_iso {Y : Scheme.{u}} {M N : Y.Modules} (e : M ≅ N)
    (h : Scheme.Modules.IsLocallyProjective M) : Scheme.Modules.IsLocallyProjective N := by
  intro O hO
  let iM : Module Γ(Y, O) (M.val.obj (op O)) := (M.val.obj (op O)).isModule
  let iN : Module Γ(Y, O) (N.val.obj (op O)) := (N.val.obj (op O)).isModule
  let eO : M.val.obj (op O) ≅ N.val.obj (op O) :=
    (PresheafOfModules.evaluation _ (op O)).mapIso ((SheafOfModules.forget _).mapIso e)
  have : Module.Projective Γ(Y, O) (M.val.obj (op O)) := h O hO
  show Module.Projective Γ(Y, O) (N.val.obj (op O))
  exact Module.Projective.of_equiv (σ := RingHom.id Γ(Y, O)) (σ' := RingHom.id Γ(Y, O))
    eO.toLinearEquiv

/-- **Stacks 060U.** A quasi-coherent module on an algebraic space whose inverse image along
every member of an fpqc covering is of finite type is itself of finite type, finite type being
read on the restriction to every étale scheme chart. -/
@[stacks 060U "finite type read on the restriction to every etale scheme chart; at the module \
universe of the structure rings"]
theorem isFiniteType_of_pullback_fpqc
    {I : Type v} {X : AlgebraicSpaces B S hS} (Xᵢ : I → AlgebraicSpaces B S hS)
    (f : ∀ i, Xᵢ i ⟶ X) (F : Modules.{u, u} B S hS X.obj X.property)
    (hF : F.IsQuasicoherentOnSite)
    (hf : IsFpqcCovering B S hS fun i ↦ (f i).hom)
    (hft : ∀ (i : I) (W : SmallEtale B S hS (Xᵢ i).obj),
      (restrictToChart B S hS (Xᵢ i).property
        ((modulePullback B S hS (f i)).obj F) W).IsFiniteType) :
    ∀ V : SmallEtale B S hS X.obj,
      (restrictToChart B S hS X.property F V).IsFiniteType := by
  intro V
  obtain ⟨T, c, g, hc, hcov, hsq⟩ := exists_chart_fpqc_refinement B S hS Xᵢ f hf V
  refine _root_.AlgebraicGeometry.isFiniteType_of_pullback_fpqc
    (restrictToChart B S hS X.property F V)
    (isQuasicoherent_restrictToChart B S hS X F hF V)
    (fun i ↦ (BigFppfOver.toScheme B S hS).obj (T i))
    (fun i ↦ (BigFppfOver.toScheme B S hS).map (g i)) hcov fun i ↦ ?_
  exact Stacks.SheafOfModules.Intrinsic.isFiniteType_of_iso
    (chartRestrictionBaseChange B S hS (f i) F hF V
      ⟨CostructuredArrow.mk (c i), hc i⟩ (g i) (hsq i)).symm
    (hft i ⟨CostructuredArrow.mk (c i), hc i⟩)

/-- **Stacks 060W.** A quasi-coherent module on an algebraic space whose inverse image along
every member of an fpqc covering is flat is itself flat, flatness being read on the restriction
to every étale scheme chart. -/
@[stacks 060W "flatness read on the restriction to every etale scheme chart; at the module \
universe of the structure rings"]
theorem isFlat_of_pullback_fpqc
    {I : Type v} {X : AlgebraicSpaces B S hS} (Xᵢ : I → AlgebraicSpaces B S hS)
    (f : ∀ i, Xᵢ i ⟶ X) (F : Modules.{u, u} B S hS X.obj X.property)
    (hF : F.IsQuasicoherentOnSite)
    (hf : IsFpqcCovering B S hS fun i ↦ (f i).hom)
    (hflat : ∀ (i : I) (W : SmallEtale B S hS (Xᵢ i).obj),
      SheafOfModules.IsFlat.{u, u, u, u} (O := (etaleChartScheme B S hS W).toRingedSpace.sheaf)
        (restrictToChart B S hS (Xᵢ i).property
          ((modulePullback B S hS (f i)).obj F) W)) :
    ∀ V : SmallEtale B S hS X.obj,
      SheafOfModules.IsFlat.{u, u, u, u} (O := (etaleChartScheme B S hS V).toRingedSpace.sheaf)
        (restrictToChart B S hS X.property F V) := by
  intro V
  obtain ⟨T, c, g, hc, hcov, hsq⟩ := exists_chart_fpqc_refinement B S hS Xᵢ f hf V
  refine @_root_.AlgebraicGeometry.isFlat_of_pullback_fpqc _ _ _
    (fun i ↦ (BigFppfOver.toScheme B S hS).map (g i)) hcov
    (restrictToChart B S hS X.property F V)
    (isQuasicoherent_restrictToChart B S hS X F hF V) fun i ↦ ?_
  exact Stacks.SheafOfModules.FlatRetract.isFlat_of_iso _
    (chartRestrictionBaseChange B S hS (f i) F hF V
      ⟨CostructuredArrow.mk (c i), hc i⟩ (g i) (hsq i)).symm
    (hflat i ⟨CostructuredArrow.mk (c i), hc i⟩)

/-- **Stacks 060Y.** A quasi-coherent module on an algebraic space whose inverse image along
every member of an fpqc covering is locally projective is itself locally projective, in the
chartwise sense of Stacks 060R. -/
@[stacks 060Y "local projectivity in the chartwise sense of Tag 060R; at the module universe \
of the structure rings"]
theorem isLocallyProjective_of_pullback_fpqc
    {I : Type v} {X : AlgebraicSpaces B S hS} (Xᵢ : I → AlgebraicSpaces B S hS)
    (f : ∀ i, Xᵢ i ⟶ X) (F : QuasicoherentSheaves.{u, u} B S hS X.obj X.property)
    (hf : IsFpqcCovering B S hS fun i ↦ (f i).hom)
    (hproj : ∀ i, IsLocallyProjective B S hS (Xᵢ i).property
      ⟨(modulePullback B S hS (f i)).obj F.obj,
        isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (f i)
          F.obj F.property⟩) :
    IsLocallyProjective B S hS X.property F := by
  intro V
  obtain ⟨T, c, g, hc, hcov, hsq⟩ := exists_chart_fpqc_refinement B S hS Xᵢ f hf V
  refine _root_.AlgebraicGeometry.isLocallyProjective_of_pullback_fpqc
    (restrictToChart B S hS X.property F.obj V)
    (isQuasicoherent_restrictToChart B S hS X F.obj F.property V)
    (fun i ↦ (BigFppfOver.toScheme B S hS).obj (T i))
    (fun i ↦ (BigFppfOver.toScheme B S hS).map (g i)) hcov fun i ↦ ?_
  exact isLocallyProjective_of_iso
    (chartRestrictionBaseChange B S hS (f i) F.obj F.property V
      ⟨CostructuredArrow.mk (c i), hc i⟩ (g i) (hsq i)).symm
    (hproj i ⟨CostructuredArrow.mk (c i), hc i⟩)

end AlgebraicGeometry.Space

end
