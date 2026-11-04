module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRelocalize
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctionsIntegral
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperReducedGlobalFunctionsFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.GeometricallyReduced
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeFibre

/-!
# The cohomological inputs of Stacks 0E6I

`AlgebraicGeometry.curvesH01_isOpenSubstack_and_factors_iff_and_over_field_iff_of` proves Stacks
0E6I from two inputs in curve-family form. This file proves the bridges from those inputs to the
shapes in which Stacks 0E6B, part (a), and Stacks 0E0R are stated for algebraic spaces, and states
Stacks 0E6I with those two statements as its only hypotheses.

## Main definitions

* `AlgebraicGeometry.Space.h0Fibre`, `AlgebraicGeometry.Space.h0FibreAlgebraMap` and
  `AlgebraicGeometry.Space.h0FibreRank`: for `f : X ⟶ U` and a field-valued point `Spec k ⟶ U`,
  the fibre `X_k = X ×_U Spec k`, the ring map `k ⟶ H⁰(X_k, 𝒪)` and `dim_k H⁰(X_k, 𝒪) ∈ ℕ∞`.
* `AlgebraicGeometry.CurveFamily.HasH0RankLeOneOnFieldFibres`: `dim_k H⁰(X_k, 𝒪) ≤ 1` on every
  fibre over a field.

## Main results

* `AlgebraicGeometry.Space.bijective_globalFunctionsMap_of_isIso_structureSharp`: over a scheme,
  an isomorphism `𝒪_T ≅ f_*𝒪_Z` makes pullback of global functions along `f` bijective.
* `AlgebraicGeometry.Space.bijective_globalFunctionsMap_of_forall_schemeSpace`: pullback of global
  functions along `π : Z ⟶ Y` is bijective as soon as it is so along every base change of `π`
  to a scheme.
* `AlgebraicGeometry.CurveFamily.hasUniversallyBijectiveGlobalFunctions_of_isIso_structureSharp`:
  `f_*𝒪_X = 𝒪_S` universally, in the form `HasUniversallyBijectiveGlobalFunctions`, from the
  invertibility of the structure maps of all base changes (the conclusion of Stacks 0E6B (a)).
* `AlgebraicGeometry.Space.bijective_algebraMap_fibreOverFieldValuedPoint_iff`: the fibre over a
  field-valued point formed over the field (the form of the hypothesis of Stacks 0E6B (a)) has
  `k = H⁰` exactly when pullback of global functions along `X ×_Y Spec k ⟶ Spec k` is bijective.
* `AlgebraicGeometry.CurveFamily.isOpenCurvesLocus_hasH0RankLeOneOnFieldFibres`: condition (o) of
  Stacks 0E0E for `dim H⁰ ≤ 1`, from the statement of Stacks 0E0R at `i = 0`.
* `AlgebraicGeometry.CurveFamily.isH01CurveFamily_iff_of`: given Stacks 0E6B (a), condition
  (1)(b) of Stacks 0E6I is `dim H⁰ ≤ 1` together with fibres of dimension `1`.
* `AlgebraicGeometry.curvesH01_isOpenSubstack_and_factors_iff_and_over_field_iff_of_statements`:
  Stacks 0E6I, parts (1) and (2), from the statements of Stacks 0E0R (`i = 0`) and 0E6B (a).

## Implementation notes

The hypothesis `hstruct` is the statement of Stacks 0E6B, part (a), for algebraic spaces over
`Spec(ℤ)` verbatim: its hypothesis reads `k = H⁰(X_k, 𝒪)` on the fibre
`AlgebraicGeometry.Space.fibreOverFieldValuedPoint` formed over `Spec k`, and its conclusion is
the invertibility of `𝒪_Y ⟶ f_*𝒪_X` after every base change. The hypothesis `hbetti` is Stacks
0E0R, parts (1) and (2), for `i = 0` and `𝓕 = 𝒪_X`, with `H⁰(X_k, 𝒪)` read as the global
functions of the fibre product: `dim_k H⁰(X_k, 𝒪)` at every field-valued point `Spec k ⟶ U` is
the value at its image point of one upper semicontinuous function on `U`. Neither carries a
`stacks` attribute here; no declaration of this file is registered.

The comparison of the fibre formed over `Spec k` with the fibre product is through
`AlgebraicGeometry.OverShriek.fibreOfSection`: it is the fibre product of the restrictions to the
site of `Spec k` (`AlgebraicGeometry.Space.isPullback_fibreOfSection`), its relocalization to the
site of the base is `X ×_Y Spec k`
(`AlgebraicGeometry.OverShriek.isPullback_relocalizeFibreOfSectionMap`), and relocalizing does
not change global functions (`AlgebraicGeometry.Space.globalFunctionsRelocalizeEquiv`).

`dim H⁰` is the `ℕ∞`-valued `Cardinal.toENat` of the rank, so no finiteness of `H⁰` is needed to
pass from `dim H⁰ ≤ 1` and a nonempty fibre to `k = H⁰`.

## References

* [Stacks Project, Tag 0E6I](https://stacks.math.columbia.edu/tag/0E6I)
* [Stacks Project, Tag 0E6B](https://stacks.math.columbia.edu/tag/0E6B)
* [Stacks Project, Tag 0E0R](https://stacks.math.columbia.edu/tag/0E0R)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Global functions across an invertible structure map -/

/-- Over the algebraic space of a scheme `U₀`, pullback of global functions along `f` is the
comparison `AlgebraicGeometry.Space.terminalChartPullback` at the identity chart of `U₀`, read
through `Γ(U₀, 𝒪) = H⁰(U₀, 𝒪)`. -/
theorem globalFunctionsMap_eq_terminalChartPullback {Z : AlgebraicSpaces B S hS}
    (U₀ : BigFppfOver B S hS) (f : Z ⟶ (schemeSpaceFunctor B S hS).obj U₀)
    (hV : IsIso ((comparisonFunctor B S hS ((schemeSpaceFunctor B S hS).obj U₀)).obj
      (idEtaleChart B S hS U₀)).1.hom)
    (s : globalFunctions' B S hS (yoneda.obj U₀)) :
    globalFunctionsMap B S hS f s =
      terminalChartPullback B S hS f (idEtaleChart B S hS U₀) hV
        (globalFunctionsYonedaRingEquiv B S hS U₀ s) := by
  refine Subtype.ext (funext fun U => ?_)
  let j := terminalChartIndex B S hS f (idEtaleChart B S hS U₀) hV U.unop
  have hψ : yoneda.map (chartBaseChangeMap B S hS f (idEtaleChart B S hS U₀) j) ≫
      ((SmallEtale.inclusion B S hS (yoneda.obj U₀)).obj (idEtaleChart B S hS U₀)).hom =
        ((SmallEtale.inclusion B S hS Z.obj).obj U.unop).hom ≫ f.hom := by
    refine (congrArg (· ≫ ((SmallEtale.inclusion B S hS (yoneda.obj U₀)).obj
      (idEtaleChart B S hS U₀)).hom) (yoneda_map_chartBaseChangeMap B S hS f _ j)).trans ?_
    let cV := (comparisonFunctor B S hS ((schemeSpaceFunctor B S hS).obj U₀)).obj
      (idEtaleChart B S hS U₀)
    show ((j.hom.unop.hom.left ≫ (spacesBaseChange B S hS f).projection.app cV) ≫
      cV.1.hom).hom = _
    rw [Category.assoc, ((spacesBaseChange B S hS f).isPullback cV).w, ← Category.assoc,
      Over.w j.hom.unop.hom]
    rfl
  exact globalFunctionsMap_val_chart B S hS f (idEtaleChart B S hS U₀) U.unop _ hψ s

/-- **Over a scheme, an invertible structure map makes pullback of global functions bijective.**
If `f : Z ⟶ U₀` is a morphism to the algebraic space of a scheme with `𝒪_{U₀} ≅ f_*𝒪_Z`, then
`Γ(U₀, 𝒪) ⟶ Γ(Z, 𝒪)` is bijective. -/
theorem bijective_globalFunctionsMap_of_isIso_structureSharp {Z : AlgebraicSpaces B S hS}
    (U₀ : BigFppfOver B S hS) (f : Z ⟶ (schemeSpaceFunctor B S hS).obj U₀)
    (hf : IsIso (structureSharp B S hS f)) :
    Function.Bijective (globalFunctionsMap B S hS f) := by
  have hV : IsIso ((comparisonFunctor B S hS ((schemeSpaceFunctor B S hS).obj U₀)).obj
      (idEtaleChart B S hS U₀)).1.hom := by
    show IsIso (𝟙 ((schemeSpaceFunctor B S hS).obj U₀))
    infer_instance
  have heq : ⇑(globalFunctionsMap B S hS f) =
      ⇑(terminalChartPullback B S hS f (idEtaleChart B S hS U₀) hV) ∘
        ⇑(globalFunctionsYonedaRingEquiv B S hS U₀) :=
    funext (globalFunctionsMap_eq_terminalChartPullback B S hS U₀ f hV)
  rw [heq]
  exact (bijective_terminalChartPullback B S hS f _ hV hf).comp
    (globalFunctionsYonedaRingEquiv B S hS U₀).bijective

/-! ### Global functions along base changes to schemes -/

section Gluing

variable {B S hS}

/-- **Gluing global functions along all scheme charts.** If, for every morphism `t` from a
representable presheaf to `Y`, precomposition of compatible functions on all scheme charts along
the base change `Z ×_Y T ⟶ T` of `π : Z ⟶ Y` is bijective, then so is precomposition along `π`:
a family on the charts of `Z` descends chart by chart, each chart `t` of `Y` giving the unique
function on `T` whose pullback to `Z ×_Y T` is the restriction of the family. -/
theorem bijective_chartFunctionsMap_of_forall {Z Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (π : Z ⟶ Y)
    (h : ∀ (T : BigFppfOver B S hS) (t : yoneda.obj T ⟶ Y),
      Function.Bijective (chartFunctionsMap B S hS (pullback.snd π t))) :
    Function.Bijective (chartFunctionsMap B S hS π) := by
  have key (T : BigFppfOver B S hS) (t : yoneda.obj T ⟶ Y) (s : chartFunctions B S hS Y) :
      chartFunctionsMap B S hS (pullback.snd π t) (chartFunctionsMap B S hS t s) =
        chartFunctionsMap B S hS (pullback.fst π t) (chartFunctionsMap B S hS π s) :=
    (congrArg (fun m => chartFunctionsMap B S hS m s) (pullback.condition (f := π) (g := t))).symm
  refine ⟨fun s₁ s₂ he => Subtype.ext (funext fun j => ?_), fun σ => ?_⟩
  · have ht : chartFunctionsMap B S hS j.unop.hom s₁ = chartFunctionsMap B S hS j.unop.hom s₂ :=
      (h j.unop.left j.unop.hom).1 (by rw [key, key, he])
    exact congrArg (fun r : chartFunctions B S hS (yoneda.obj j.unop.left) =>
      r.val (op (CostructuredArrow.mk (𝟙 (yoneda.obj j.unop.left))))) ht
  · let e (T : BigFppfOver B S hS) (t : yoneda.obj T ⟶ Y) := Equiv.ofBijective _ (h T t)
    let r (T : BigFppfOver B S hS) (t : yoneda.obj T ⟶ Y) : chartFunctions B S hS (yoneda.obj T) :=
      (e T t).symm (chartFunctionsMap B S hS (pullback.fst π t) σ)
    have hr (T : BigFppfOver B S hS) (t : yoneda.obj T ⟶ Y) :
        chartFunctionsMap B S hS (pullback.snd π t) (r T t) =
          chartFunctionsMap B S hS (pullback.fst π t) σ :=
      (e T t).apply_symm_apply _
    -- restriction of `r T t` along a morphism of charts is `r T' t'`
    have hres {T T' : BigFppfOver B S hS} (t : yoneda.obj T ⟶ Y) (ml : T' ⟶ T) :
        chartFunctionsMap B S hS (yoneda.map ml) (r T t) = r T' (yoneda.map ml ≫ t) := by
      apply (h T' (yoneda.map ml ≫ t)).1
      let k : pullback π (yoneda.map ml ≫ t) ⟶ pullback π t :=
        pullback.lift (pullback.fst π _) (pullback.snd π _ ≫ yoneda.map ml)
          (by rw [pullback.condition, Category.assoc])
      have hks : pullback.snd π (yoneda.map ml ≫ t) ≫ yoneda.map ml = k ≫ pullback.snd π t :=
        (pullback.lift_snd _ _ _).symm
      have hkf : k ≫ pullback.fst π t = pullback.fst π (yoneda.map ml ≫ t) :=
        pullback.lift_fst _ _ _
      rw [hr]
      show chartFunctionsMap B S hS (pullback.snd π (yoneda.map ml ≫ t) ≫ yoneda.map ml)
        (r T t) = _
      rw [hks]
      show chartFunctionsMap B S hS k (chartFunctionsMap B S hS (pullback.snd π t) (r T t)) = _
      rw [hr]
      show chartFunctionsMap B S hS (k ≫ pullback.fst π t) σ = _
      rw [hkf]
    let s : chartFunctions B S hS Y := ⟨fun j =>
      (r j.unop.left j.unop.hom).val (op (CostructuredArrow.mk (𝟙 (yoneda.obj j.unop.left)))),
      fun {j j'} m => by
        have hw : yoneda.map m.unop.left ≫ j.unop.hom = j'.unop.hom := CostructuredArrow.w m.unop
        have h1 := congrArg (fun x : chartFunctions B S hS (yoneda.obj j'.unop.left) =>
          x.val (op (CostructuredArrow.mk (𝟙 (yoneda.obj j'.unop.left)))))
          (hres j.unop.hom m.unop.left)
        have h2 := (r j.unop.left j.unop.hom).property
          (CostructuredArrow.homMk m.unop.left (by simp) :
            CostructuredArrow.mk (yoneda.map m.unop.left) ⟶
              CostructuredArrow.mk (𝟙 (yoneda.obj j.unop.left))).op
        refine h2.trans (h1.trans ?_)
        rw [hw]⟩
    refine ⟨s, Subtype.ext (funext fun c => ?_)⟩
    let W := c.unop.left
    let w := c.unop.hom
    let σw : yoneda.obj W ⟶ pullback π (w ≫ π) := pullback.lift w (𝟙 _) (by simp)
    have h1 : chartFunctionsMap B S hS σw
        (chartFunctionsMap B S hS (pullback.snd π (w ≫ π)) (r W (w ≫ π))) = r W (w ≫ π) := by
      show chartFunctionsMap B S hS (σw ≫ pullback.snd π (w ≫ π)) (r W (w ≫ π)) = _
      rw [pullback.lift_snd]
      rfl
    rw [hr] at h1
    change chartFunctionsMap B S hS (σw ≫ pullback.fst π (w ≫ π)) σ = _ at h1
    rw [pullback.lift_fst] at h1
    exact (congrArg (fun x : chartFunctions B S hS (yoneda.obj W) =>
      x.val (op (CostructuredArrow.mk (𝟙 (yoneda.obj W))))) h1).symm

/-- Pullback of global functions is bijective exactly when precomposition of compatible functions
on all scheme charts is. -/
theorem bijective_globalFunctionsMap_iff {U V : AlgebraicSpaces B S hS} (f : V ⟶ U) :
    Function.Bijective (globalFunctionsMap B S hS f) ↔
      Function.Bijective (chartFunctionsMap B S hS f.hom) := by
  have h : ⇑(globalFunctionsMap B S hS f) = ⇑(globalFunctionsChartEquiv B S hS V).val.symm ∘
      ⇑(chartFunctionsMap B S hS f.hom) ∘ ⇑(globalFunctionsChartEquiv B S hS U).val := rfl
  rw [h, Function.Bijective.of_comp_iff' (globalFunctionsChartEquiv B S hS V).val.symm.bijective,
    Function.Bijective.of_comp_iff _ (globalFunctionsChartEquiv B S hS U).val.bijective]

/-- **Pullback of global functions along `π : Z ⟶ Y` is bijective as soon as it is so along every
base change `Z ×_Y T ⟶ T` of `π` to a scheme `T`.** -/
theorem bijective_globalFunctionsMap_of_forall_schemeSpace {Z Y : AlgebraicSpaces B S hS}
    (π : Z ⟶ Y)
    (h : ∀ (T : BigFppfOver B S hS) (t : schemeSpace T ⟶ Y),
      Function.Bijective (globalFunctionsMap B S hS
        (ObjectProperty.homMk (pullback.snd π.hom t.hom) :
          AlgebraicSpaces.fiberProduct B S hS π t ⟶ schemeSpace T))) :
    Function.Bijective (globalFunctionsMap B S hS π) := by
  rw [bijective_globalFunctionsMap_iff]
  exact bijective_chartFunctionsMap_of_forall π.hom fun T t =>
    (bijective_globalFunctionsMap_iff _).1 (h T (ObjectProperty.homMk t))

end Gluing

end Space

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The fibre over a field-valued point, formed over the field -/

/-- Identifying the field `k` of a field-valued point with the global functions of `Spec k` in the
site of the base is a bijective ring map. -/
private theorem bijective_yonedaRingEquiv_symm_comp_ΓSpecIso_inv
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : FieldValuedPoint B S hS Y) :
    Function.Bijective
      ((globalFunctionsYonedaRingEquiv B S hS (p.siteObject B S hS Y)).symm.toRingHom.comp
        (Scheme.ΓSpecIso (.of p.carrier)).inv.hom) :=
  (globalFunctionsYonedaRingEquiv B S hS _).symm.bijective.comp
    ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance)

section FieldFibre

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y)

/-- The morphism `Spec k ⟶ S` of the site underlying a field-valued point. -/
abbrev FieldValuedPoint.baseSiteHom : B.obj p.contained ⟶ B.obj hS := (p.siteObject B S hS Y).hom

/-- The unique morphism from the fibre of `f` over the section of a field-valued point to the
terminal presheaf over the field. -/
def fibreOfSectionToTerminal :
    OverShriek.fibreOfSection (p.baseSiteHom B S hS) f (yonedaEquiv.symm p.value) ⟶
      yoneda.obj (Over.mk (𝟙 (B.obj p.contained))) where
  app W := ↾fun _ => Over.homMk W.unop.hom (Category.comp_id _)
  naturality _ _ _ := by
    ext _
    exact Over.OverMorphism.ext (Over.w _).symm

/-- The fibre of `f` over the section of a field-valued point, as a subpresheaf, is the fibre
product defining `AlgebraicGeometry.Space.restrictedFibre`. -/
theorem isPullback_fibreOfSection :
    IsPullback (OverShriek.fibreOfSectionι (p.baseSiteHom B S hS) f (yonedaEquiv.symm p.value))
      (fibreOfSectionToTerminal B S hS f p)
      ((OverShriek.relocalizeRestrict (p.baseSiteHom B S hS)).map f)
      (restrictedSection B S hS Y p.contained (p.baseSiteHom B S hS) p.value) := by
  apply IsPullback.of_forall_isPullback_app
  intro W
  rw [Limits.Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext x
    exact x.2.trans rfl
  · rintro x x' ⟨h1, -⟩
    exact Subtype.ext h1
  · intro x t hxt
    obtain rfl : t = Over.homMk (unop W).hom (Category.comp_id _) :=
      Over.OverMorphism.ext ((Category.comp_id _).symm.trans (Over.w t))
    exact ⟨⟨x, hxt.trans rfl⟩, rfl, rfl⟩

variable (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)

include hX hY in
/-- **The global functions of the fibre over a field-valued point, formed over the field, are the
global functions of the fibre product.** For `f : X ⟶ Y` and a field-valued point `p` of `Y`
with field `k`, the base ring map `k ⟶ H⁰(X_k, 𝒪)` of the fibre of `f` over `p` formed over
`Spec k` is bijective exactly when pullback of global functions along `X ×_Y Spec k ⟶ Spec k`
is. The fibre is the subpresheaf `AlgebraicGeometry.OverShriek.fibreOfSection`, whose
relocalization to the site of the base is `X ×_Y Spec k`, and relocalizing does not change global
functions (`AlgebraicGeometry.Space.globalFunctionsRelocalizeEquiv`). -/
theorem bijective_algebraMap_fibreOverFieldValuedPoint_iff :
    Function.Bijective (algebraMap p.carrier (globalFunctions B (Spec (.of p.carrier))
      p.contained (fibreOverFieldValuedPoint B S hS f p))) ↔
    Function.Bijective (globalFunctionsMap B S hS
      (ObjectProperty.homMk (pullback.snd f (yonedaEquiv.symm p.value)) :
        (⟨pullback f (yonedaEquiv.symm p.value), isAlgebraicSpace_pullback B S hS f _ hX
          (isAlgebraicSpace_yoneda B S hS _) hY⟩ : AlgebraicSpaces B S hS) ⟶
          schemeSpace (p.siteObject B S hS Y))) := by
  set a := p.baseSiteHom B S hS
  set β : yoneda.obj (Over.mk a) ⟶ Y := yonedaEquiv.symm p.value
  let fib := OverShriek.fibreOfSection a f β
  let e1 : fib ≅ fibreOverFieldValuedPoint B S hS f p :=
    (isPullback_fibreOfSection B S hS f p).isoPullback
  have hrf := isAlgebraicSpace_fibreOverFieldValuedPoint B S hS f hX hY p
  have hfib : IsAlgebraicSpace B (Spec (.of p.carrier)) p.contained fib :=
    isAlgebraicSpace_of_iso B _ p.contained e1.symm hrf
  have hpbP := OverShriek.isPullback_relocalizeFibreOfSectionMap a f β
  have hP : IsAlgebraicSpace B S hS (pullback f β) :=
    isAlgebraicSpace_pullback B S hS f β hX (isAlgebraicSpace_yoneda B S hS _) hY
  have hΛ : IsAlgebraicSpace B S hS ((OverShriek.relocalizePresheafFunctor a).obj fib) :=
    isAlgebraicSpace_of_iso B S hS hpbP.isoPullback.symm hP
  let P' : AlgebraicSpaces B S hS := ⟨pullback f β, hP⟩
  let Λ' : AlgebraicSpaces B S hS := ⟨_, hΛ⟩
  let I3 : Λ' ≅ P' := (ObjectProperty.fullyFaithfulι _).preimageIso hpbP.isoPullback
  let RF : AlgebraicSpaces B (Spec (.of p.carrier)) p.contained := ⟨_, hrf⟩
  let FB : AlgebraicSpaces B (Spec (.of p.carrier)) p.contained := ⟨fib, hfib⟩
  let I1 : RF ≅ FB := (ObjectProperty.fullyFaithfulι _).preimageIso e1.symm
  let rTY : Λ' ⟶ schemeSpace (p.siteObject B S hS Y) :=
    ObjectProperty.homMk (OverShriek.relocalizeToYoneda a fib)
  let snd : P' ⟶ schemeSpace (p.siteObject B S hS Y) := ObjectProperty.homMk (pullback.snd f β)
  let ι : p.carrier → globalFunctions' B S hS (yoneda.obj (p.siteObject B S hS Y)) := fun c =>
    (globalFunctionsYonedaRingEquiv B S hS (p.siteObject B S hS Y)).symm
      ((Scheme.ΓSpecIso (.of p.carrier)).inv c)
  have hι : Function.Bijective ι := bijective_yonedaRingEquiv_symm_comp_ΓSpecIso_inv B S hS p
  have hsnd : I3.hom ≫ snd = rTY :=
    ObjectProperty.hom_ext _ hpbP.isoPullback_hom_snd
  have key (c : p.carrier) :
      globalFunctionsRelocalizeEquiv B (Spec (.of p.carrier)) S p.contained hS a fib
          (globalFunctionsMap B S hS rTY (ι c)) =
        algebraMap p.carrier (globalFunctions B (Spec (.of p.carrier)) p.contained fib) c := by
    refine Subtype.ext (funext fun V => ?_)
    rw [globalFunctionsRelocalizeEquiv_apply]
    let ψ := relocalizeOverHom B (Spec (.of p.carrier)) S p.contained hS a
      ((SmallEtale.toOver B (Spec (.of p.carrier)) p.contained fib).obj V.unop)
    have hψ : yoneda.map ψ ≫ ((SmallEtale.inclusion B S hS (yoneda.obj (p.siteObject B S hS Y))).obj
        (idEtaleChart B S hS (p.siteObject B S hS Y))).hom =
        ((SmallEtale.inclusion B S hS Λ'.obj).obj
          ((SmallEtale.relocalizeEquivalence B (Spec (.of p.carrier)) S p.contained hS a
            fib).functor.obj V.unop)).hom ≫ rTY.hom := by
      ext W x
      exact Over.OverMorphism.ext rfl
    refine (globalFunctionsMap_val_chart B S hS rTY (idEtaleChart B S hS _)
      ((SmallEtale.relocalizeEquivalence B (Spec (.of p.carrier)) S p.contained hS a
        fib).functor.obj V.unop) ψ hψ (ι c)).trans ?_
    have hc : (ι c).val (op (idEtaleChart B S hS (p.siteObject B S hS Y))) =
        (Scheme.ΓSpecIso (.of p.carrier)).inv c :=
      (globalFunctionsYonedaRingEquiv_apply B S hS _ (ι c)).symm.trans
        ((globalFunctionsYonedaRingEquiv B S hS _).apply_symm_apply _)
    exact (congrArg (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map ψ).op).hom hc).trans rfl
  have hcomp : ⇑(algebraMap p.carrier (globalFunctions B (Spec (.of p.carrier)) p.contained
      (fibreOverFieldValuedPoint B S hS f p))) =
      ⇑(globalFunctionsMapEquiv B _ p.contained I1) ∘
        ⇑(globalFunctionsRelocalizeEquiv B (Spec (.of p.carrier)) S p.contained hS a fib) ∘
          ⇑(globalFunctionsMapEquiv B S hS I3) ∘ ⇑(globalFunctionsMap B S hS snd) ∘ ι := by
    funext c
    show _ = globalFunctionsMap B _ p.contained I1.hom
      (globalFunctionsRelocalizeEquiv B (Spec (.of p.carrier)) S p.contained hS a fib
        (globalFunctionsMap B S hS I3.hom (globalFunctionsMap B S hS snd (ι c))))
    have h3 : globalFunctionsMap B S hS I3.hom (globalFunctionsMap B S hS snd (ι c)) =
        globalFunctionsMap B S hS rTY (ι c) := by
      rw [← hsnd, globalFunctionsMap_comp]
      rfl
    rw [h3, key, globalFunctionsMap_algebraMap]
  rw [hcomp, Function.Bijective.of_comp_iff' (globalFunctionsMapEquiv B _ p.contained I1).bijective,
    Function.Bijective.of_comp_iff'
      (globalFunctionsRelocalizeEquiv B _ S p.contained hS a fib).bijective,
    Function.Bijective.of_comp_iff' (globalFunctionsMapEquiv B S hS I3).bijective]
  exact Function.Bijective.of_comp_iff (globalFunctionsMap B S hS snd) hι

include hX hY in
/-- One direction of `AlgebraicGeometry.Space.bijective_algebraMap_fibreOverFieldValuedPoint_iff`:
bijectivity of pullback of global functions along `X ×_Y Spec k ⟶ Spec k` gives
`k = H⁰(X_k, 𝒪)` for the fibre formed over `Spec k`. -/
theorem bijective_algebraMap_fibreOverFieldValuedPoint_of_bijective
    (h : Function.Bijective (globalFunctionsMap B S hS
      (ObjectProperty.homMk (pullback.snd f (yonedaEquiv.symm p.value)) :
        (⟨pullback f (yonedaEquiv.symm p.value), isAlgebraicSpace_pullback B S hS f _ hX
          (isAlgebraicSpace_yoneda B S hS _) hY⟩ : AlgebraicSpaces B S hS) ⟶
          schemeSpace (p.siteObject B S hS Y)))) :
    Function.Bijective (algebraMap p.carrier (globalFunctions B (Spec (.of p.carrier))
      p.contained (fibreOverFieldValuedPoint B S hS f p))) :=
  (bijective_algebraMap_fibreOverFieldValuedPoint_iff B S hS f p hX hY).2 h

end FieldFibre

/-! ### The dimension of `H⁰` of the fibres over fields -/

section FibreRank

/-- A bijective ring map out of a field makes the target a one-dimensional vector space. -/
theorem toENat_rank_eq_one_of_bijective {k A : Type*} [Field k] [CommRing A] (φ : k →+* A)
    (h : Function.Bijective φ) :
    letI := φ.toAlgebra
    Cardinal.toENat (Module.rank k A) = 1 := by
  let := φ.toAlgebra
  have : Nontrivial A := h.1.nontrivial
  have hf : Module.finrank k A = 1 := Algebra.finrank_eq_one_iff_bijective_algebraMap.2 h
  have : Module.Finite k A := Module.finite_of_finrank_eq_succ hf
  rw [← Module.finrank_eq_rank, hf]
  simp

/-- A ring map out of a field whose target is a nonzero vector space of dimension at most one is
bijective. -/
theorem bijective_of_toENat_rank_le_one {k A : Type*} [Field k] [CommRing A] [Nontrivial A]
    (φ : k →+* A)
    (h : letI := φ.toAlgebra
      Cardinal.toENat (Module.rank k A) ≤ 1) :
    Function.Bijective φ := by
  let := φ.toAlgebra
  have h0 : Cardinal.toENat (Module.rank k A) ≠ 0 := fun h0 =>
    (rank_pos (R := k) (M := A)).ne' (Cardinal.toENat_eq_zero.1 h0)
  have h1 : Cardinal.toENat (Module.rank k A) = 1 :=
    le_antisymm h (ENat.one_le_iff_ne_zero.2 h0)
  have hr : Module.rank k A = 1 := by
    simpa using Cardinal.toENat_eq_natCast.1 (h1.trans (Nat.cast_one (R := ℕ∞)).symm)
  have hf : Module.finrank k A = 1 := Module.finrank_eq_of_rank_eq (by simpa using hr)
  exact Algebra.finrank_eq_one_iff_bijective_algebraMap.1 hf

/-- The dimension of a ring over a field along `φ` is unchanged by composing `φ` with a ring
isomorphism. -/
theorem toENat_rank_comp_ringEquiv {k : Type*} {A A' : Type*} [Field k] [CommRing A] [CommRing A']
    (φ : k →+* A) (σ : A ≃+* A') :
    (letI := (σ.toRingHom.comp φ).toAlgebra; Cardinal.toENat (Module.rank k A')) =
      (letI := φ.toAlgebra; Cardinal.toENat (Module.rank k A)) := by
  let i1 : Algebra k A := φ.toAlgebra
  let i2 : Algebra k A' := (σ.toRingHom.comp φ).toAlgebra
  let L : A ≃ₗ[k] A' :=
    { σ.toAddEquiv with
      map_smul' := fun c x => by
        show σ (φ c * x) = σ (φ c) * σ x
        exact map_mul σ _ _ }
  have h := congrArg Cardinal.toENat L.lift_rank_eq
  rw [Cardinal.toENat_lift, Cardinal.toENat_lift] at h
  exact h.symm

variable {U : BigFppfOver B S hS} {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace U)
  (p : FieldValuedPoint B S hS (yoneda.obj U))

/-- The fibre `X ×_U Spec k` of `f : X ⟶ U` over a field-valued point `Spec k ⟶ U`. -/
abbrev h0Fibre : AlgebraicSpaces B S hS :=
  AlgebraicSpaces.fiberProduct B S hS f (schemeSpaceMap p.value)

/-- The projection `X ×_U Spec k ⟶ Spec k`. -/
abbrev h0FibreProj : h0Fibre B S hS f p ⟶ schemeSpace (p.siteObject B S hS _) :=
  ObjectProperty.homMk (pullback.snd f.hom (schemeSpaceMap p.value).hom)

/-- The ring map `k ⟶ H⁰(X_k, 𝒪)` of the fibre over a field-valued point. -/
noncomputable def h0FibreAlgebraMap :
    p.carrier →+* globalFunctions' B S hS (h0Fibre B S hS f p).obj :=
  (globalFunctionsMap B S hS (h0FibreProj B S hS f p)).comp
    ((globalFunctionsYonedaRingEquiv B S hS (p.siteObject B S hS _)).symm.toRingHom.comp
      (Scheme.ΓSpecIso (.of p.carrier)).inv.hom)

/-- **`dim_k H⁰(X_k, 𝒪_{X_k})`** for the fibre of `f` over a field-valued point `Spec k ⟶ U`,
as an element of `ℕ∞` (infinite dimension giving `⊤`). -/
noncomputable def h0FibreRank : ℕ∞ :=
  letI := (h0FibreAlgebraMap B S hS f p).toAlgebra
  Cardinal.toENat (Module.rank p.carrier (globalFunctions' B S hS (h0Fibre B S hS f p).obj))

/-- `k ⟶ H⁰(X_k, 𝒪)` is bijective exactly when pullback of global functions along the
projection `X_k ⟶ Spec k` is. -/
theorem bijective_h0FibreAlgebraMap_iff :
    Function.Bijective (h0FibreAlgebraMap B S hS f p) ↔
      Function.Bijective (globalFunctionsMap B S hS (h0FibreProj B S hS f p)) := by
  exact Function.Bijective.of_comp_iff (globalFunctionsMap B S hS (h0FibreProj B S hS f p))
    (bijective_yonedaRingEquiv_symm_comp_ΓSpecIso_inv B S hS p)

/-- If some point of `X` lies over the point of `U` of a field-valued point, the global functions
of the fibre over it form a nonzero ring. -/
theorem nontrivial_globalFunctions_h0Fibre
    (hx : ∃ x : points B S hS X.obj,
      pointsMap B S hS X.obj f.hom x = p.class B S hS (yoneda.obj U)) :
    Nontrivial (globalFunctions' B S hS (h0Fibre B S hS f p).obj) := by
  obtain ⟨x, hx⟩ := hx
  let y : FieldValuedPoint B S hS (yoneda.obj (p.siteObject B S hS _)) :=
    { carrier := p.carrier
      contained := p.contained
      toBase := p.toBase
      value := 𝟙 _ }
  obtain ⟨w, -, -⟩ := exists_point_of_isPullback_presheaf B S hS
    (IsPullback.of_hasPullback f.hom (schemeSpaceMap p.value).hom).flip
    (y.class B S hS _) x hx.symm
  obtain ⟨q, -⟩ := Quot.exists_rep w
  let φ := (globalFunctionsYonedaRingEquiv B S hS (q.siteObject B S hS _)).toRingHom.comp
    (globalFunctionsMap B S hS
      (ObjectProperty.homMk (yonedaEquiv.symm q.value) :
        schemeSpace (q.siteObject B S hS _) ⟶ h0Fibre B S hS f p))
  have : Nontrivial Γ((BigFppfOver.toScheme B S hS).obj (q.siteObject B S hS _), ⊤) :=
    inferInstanceAs (Nontrivial Γ(Spec (.of q.carrier), ⊤))
  exact φ.domain_nontrivial

end FibreRank

end Space

/-! ### `f_*𝒪_X = 𝒪_S` universally from invertible structure maps -/

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **`f_*𝒪_X = 𝒪_S` universally, from the structure maps of the base changes.** If for every
algebraic space `Y'` over the base `S` of a family of curves `f : X → S` the structure map
`𝒪_{Y'} ⟶ (f_{Y'})_*𝒪_{X_{Y'}}` of the base change is an isomorphism, then pullback of global
functions along every base change `X ×_S Y' ⟶ Y'` is bijective. -/
theorem hasUniversallyBijectiveGlobalFunctions_of_isIso_structureSharp {X : CurveFamily B hZ}
    (h : ∀ (Y' : AlgebraicSpaces B integerBase hZ) (g : Y' ⟶ schemeSpace X.base),
      IsIso (Space.structureSharp B integerBase hZ (pullback.snd X.toBase g))) :
    HasUniversallyBijectiveGlobalFunctions B hZ X := by
  intro Y' g
  refine Space.bijective_globalFunctionsMap_of_forall_schemeSpace _ fun T t => ?_
  have hb := Space.bijective_globalFunctionsMap_of_isIso_structureSharp B integerBase hZ T
    (pullback.snd X.toBase (t ≫ g)) (h _ (t ≫ g))
  have sq := (AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ
    (ObjectProperty.homMk (pullback.snd X.toBase.hom g.hom) :
      AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase g ⟶ Y') t).paste_horiz
    (AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ X.toBase g)
  have he := IsPullback.isoIsPullback_hom_snd _ _ sq (IsPullback.of_hasPullback X.toBase (t ≫ g))
  rw [← he, Space.globalFunctionsMap_comp, RingHom.coe_comp]
  exact (Space.globalFunctionsMapEquiv B integerBase hZ _).bijective.comp hb

/-- **`f_*𝒪_X = 𝒪_S` universally from `k = H⁰(X_k, 𝒪)` on the fibres over fields, given Stacks
0E6B (a).** The hypothesis `hstruct` is the statement of Stacks 0E6B, part (a), for algebraic
spaces over `Spec(ℤ)`: for `f : X ⟶ Y` proper, flat and of finite presentation with
`k = H⁰(X_k, 𝒪_{X_k})` at every field-valued point of `Y` (the fibre formed over `Spec k`), the
structure map `𝒪_Y ⟶ f_*𝒪_X` is an isomorphism, and so is that of every base change. -/
theorem hasUniversallyBijectiveGlobalFunctions_of_hasBijectiveGlobalFunctionsOnFieldFibres
    (hstruct : ∀ {X Y : AlgebraicSpaces B integerBase hZ} (f : X ⟶ Y),
      Space.IsProper B integerBase hZ f.hom → Space.IsFlat B integerBase hZ f.hom →
      Space.IsFinitePresentation B integerBase hZ f.hom →
      (∀ p : Space.FieldValuedPoint B integerBase hZ Y.1, Function.Bijective
        (algebraMap p.carrier (Space.globalFunctions B (Spec (.of p.carrier)) p.contained
          (Space.fibreOverFieldValuedPoint B integerBase hZ f.hom p)))) →
      IsIso (Space.structureSharp B integerBase hZ f) ∧
        ∀ (Y' : AlgebraicSpaces B integerBase hZ) (g : Y' ⟶ Y),
          IsIso (Space.structureSharp B integerBase hZ (pullback.snd f g)))
    {X : CurveFamily B hZ} (hX : HasBijectiveGlobalFunctionsOnFieldFibres B hZ X) :
    HasUniversallyBijectiveGlobalFunctions B hZ X :=
  hasUniversallyBijectiveGlobalFunctions_of_isIso_structureSharp fun Y' g =>
    (hstruct X.toBase X.proper X.flat X.finitePresentation fun p =>
      Space.bijective_algebraMap_fibreOverFieldValuedPoint_of_bijective B integerBase hZ
        X.toBase.hom p X.total.2 (schemeSpace X.base).2 (hX p)).2 Y' g

end CurveFamily

/-! ### The open locus of `dim H⁰ ≤ 1` -/

namespace CurveFamily

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- The fibre of a family of curves over a field-valued point of its base, and that of a family
it maps to over the image point, have the same `dim H⁰`: the first fibre is a base change of the
second, compatibly with the projections to the field. -/
theorem h0FibreRank_toBase_of_hom {F G : CurveFamily B hZ} (a : F ⟶ G)
    (p : Space.FieldValuedPoint B integerBase hZ (yoneda.obj F.base)) :
    Space.h0FibreRank B integerBase hZ F.toBase p =
      Space.h0FibreRank B integerBase hZ G.toBase
        (p.map B integerBase hZ _ (yoneda.map a.baseMap)) := by
  let p' := p.map B integerBase hZ _ (yoneda.map a.baseMap)
  have sqG := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ G.toBase
    (schemeSpaceMap p'.value)
  have hv : schemeSpaceMap p'.value = schemeSpaceMap p.value ≫ schemeSpaceMap a.baseMap :=
    schemeSpaceMap_comp p.value a.baseMap
  rw [hv] at sqG
  have sq := (AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ F.toBase
    (schemeSpaceMap p.value)).paste_horiz a.cartesian
  let e := sq.isoIsPullback _ _ sqG
  have he : e.hom ≫ Space.h0FibreProj B integerBase hZ G.toBase p' =
      Space.h0FibreProj B integerBase hZ F.toBase p :=
    IsPullback.isoIsPullback_hom_snd _ _ sq sqG
  have hmap : Space.h0FibreAlgebraMap B integerBase hZ F.toBase p =
      (Space.globalFunctionsMapEquiv B integerBase hZ e).toRingHom.comp
        (Space.h0FibreAlgebraMap B integerBase hZ G.toBase p') := by
    refine RingHom.ext fun c => ?_
    show Space.globalFunctionsMap B integerBase hZ (Space.h0FibreProj B integerBase hZ F.toBase p)
      _ = Space.globalFunctionsMap B integerBase hZ e.hom
        (Space.globalFunctionsMap B integerBase hZ
          (Space.h0FibreProj B integerBase hZ G.toBase p') _)
    rw [← he]
    exact (RingHom.congr_fun (Space.globalFunctionsMap_comp B integerBase hZ e.hom _) _).trans rfl
  unfold Space.h0FibreRank
  rw [hmap]
  exact Space.toENat_rank_comp_ringEquiv _ _

/-- At most one-dimensional `H⁰` on every fibre over a field: for every morphism `Spec k ⟶ S`
of the site, `dim_k H⁰(X_k, 𝒪_{X_k}) ≤ 1`. -/
def HasH0RankLeOneOnFieldFibres (X : CurveFamily B hZ) : Prop :=
  ∀ p : Space.FieldValuedPoint B integerBase hZ (yoneda.obj X.base),
    Space.h0FibreRank B integerBase hZ X.toBase p ≤ 1

/-- **Condition (o) of Stacks 0E0E for `dim H⁰ ≤ 1` on the fibres, given Stacks 0E0R at `i = 0`.**
The hypothesis `hbetti` is Stacks 0E0R, parts (1) and (2), for `i = 0` and `𝓕 = 𝒪_X`, read with
`H⁰ = Γ`: for `f : X ⟶ U` proper, flat and of finite presentation, `dim_k H⁰(X_k, 𝒪)` is, at every
field-valued point `Spec k ⟶ U`, the value at its image point of one upper semicontinuous
function on `U`. -/
theorem isOpenCurvesLocus_hasH0RankLeOneOnFieldFibres
    (hbetti : ∀ {U : BigFppfOver B integerBase hZ} {X : AlgebraicSpaces B integerBase hZ}
      (f : X ⟶ schemeSpace U), Space.IsProper B integerBase hZ f.hom →
      Space.IsFlat B integerBase hZ f.hom → Space.IsFinitePresentation B integerBase hZ f.hom →
      ∃ b : (BigFppfOver.toScheme B integerBase hZ).obj U → ℕ∞, UpperSemicontinuous b ∧
        ∀ p : Space.FieldValuedPoint B integerBase hZ (yoneda.obj U),
          Space.h0FibreRank B integerBase hZ f p = b (Space.schemePoint B integerBase hZ U p)) :
    IsOpenCurvesLocus B hZ (HasH0RankLeOneOnFieldFibres (B := B) (hZ := hZ)) := by
  refine IsOpenCurvesLocus.of_points fun G => ?_
  obtain ⟨b, hb, hbp⟩ := hbetti G.toBase G.proper G.flat G.finitePresentation
  have hIic : b ⁻¹' Set.Iic 1 = b ⁻¹' Set.Iio 2 := by
    ext y
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_Iio]
    rw [show (2 : ℕ∞) = 1 + 1 by norm_num]
    exact (ENat.lt_add_one_iff (by simp)).symm
  refine ⟨Space.pointsToScheme B integerBase hZ G.base ⁻¹' (b ⁻¹' Set.Iic 1), ?_,
    fun F a => ?_⟩
  · rw [hIic]
    exact (hb.isOpen_preimage 2).preimage
      (Space.schemePointsHomeomorph B integerBase hZ G.base).continuous
  · rw [Set.range_subset_iff]
    refine ⟨fun hR s => ?_, fun hΩ q => ?_⟩
    · obtain ⟨q, rfl⟩ := Quot.exists_rep s
      show b (Space.schemePoint B integerBase hZ G.base
        (q.map B integerBase hZ _ (yoneda.map a.baseMap))) ≤ 1
      rw [← hbp, ← h0FibreRank_toBase_of_hom a q]
      exact hR q
    · rw [h0FibreRank_toBase_of_hom a q, hbp]
      exact hΩ (q.class B integerBase hZ _)

/-- **The condition (1)(b) of Stacks 0E6I, given Stacks 0E6B (a).** A family of curves has
`f_*𝒪_X = 𝒪_S` universally with fibres of dimension `1` exactly when its fibres over fields have
`dim_k H⁰ ≤ 1` and have dimension `1`: a fibre of dimension `1` is nonempty, so its `H⁰` is a
nonzero `k`-vector space, and `dim_k H⁰ = 1` is `k = H⁰`. -/
theorem isH01CurveFamily_iff_of
    (hstruct : ∀ {X Y : AlgebraicSpaces B integerBase hZ} (f : X ⟶ Y),
      Space.IsProper B integerBase hZ f.hom → Space.IsFlat B integerBase hZ f.hom →
      Space.IsFinitePresentation B integerBase hZ f.hom →
      (∀ p : Space.FieldValuedPoint B integerBase hZ Y.1, Function.Bijective
        (algebraMap p.carrier (Space.globalFunctions B (Spec (.of p.carrier)) p.contained
          (Space.fibreOverFieldValuedPoint B integerBase hZ f.hom p)))) →
      IsIso (Space.structureSharp B integerBase hZ f) ∧
        ∀ (Y' : AlgebraicSpaces B integerBase hZ) (g : Y' ⟶ Y),
          IsIso (Space.structureSharp B integerBase hZ (pullback.snd f g)))
    (X : CurveFamily B hZ) :
    IsH01CurveFamily B hZ X ↔
      HasH0RankLeOneOnFieldFibres X ∧ HasFibresOfDimensionOne B hZ X := by
  refine and_congr_left fun hD => ⟨fun hU p => ?_, fun hR => ?_⟩
  · exact (Space.toENat_rank_eq_one_of_bijective _
      ((Space.bijective_h0FibreAlgebraMap_iff B integerBase hZ X.toBase p).2
        (hasBijectiveGlobalFunctionsOnFieldFibres_of_hasUniversallyBijectiveGlobalFunctions
          hU p))).le
  · refine hasUniversallyBijectiveGlobalFunctions_of_hasBijectiveGlobalFunctionsOnFieldFibres
      hstruct fun p => ?_
    have hx : ∃ x : Space.points B integerBase hZ X.total.obj,
        Space.pointsMap B integerBase hZ X.total.obj X.toBase.hom x =
          p.class B integerBase hZ (yoneda.obj X.base) := by
      have h := Space.fiberDimension_eq_bot_iff B integerBase hZ X.toBase.hom
        (p.class B integerBase hZ (yoneda.obj X.base))
      have h1 : Space.fiberDimension B integerBase hZ X.toBase.hom
          (p.class B integerBase hZ (yoneda.obj X.base)) = ((1 : ℕ) : WithBot ℕ∞) := hD _
      rw [h1] at h
      by_contra hne
      exact absurd (h.2 fun ⟨x, hx⟩ => hne ⟨x, hx⟩) (by simp)
    have := Space.nontrivial_globalFunctions_h0Fibre B integerBase hZ X.toBase p hx
    exact (Space.bijective_h0FibreAlgebraMap_iff B integerBase hZ X.toBase p).1
      (Space.bijective_of_toENat_rank_le_one _ (hR p))

/-- **Condition (o) of Stacks 0E0E for `Curves^{h0,1}`, from the statements of Stacks 0E0R
(at `i = 0`) and Stacks 0E6B (a).** -/
theorem isOpenCurvesLocus_isH01CurveFamily_of_h0FibreRank
    (hbetti : ∀ {U : BigFppfOver B integerBase hZ} {X : AlgebraicSpaces B integerBase hZ}
      (f : X ⟶ schemeSpace U), Space.IsProper B integerBase hZ f.hom →
      Space.IsFlat B integerBase hZ f.hom → Space.IsFinitePresentation B integerBase hZ f.hom →
      ∃ b : (BigFppfOver.toScheme B integerBase hZ).obj U → ℕ∞, UpperSemicontinuous b ∧
        ∀ p : Space.FieldValuedPoint B integerBase hZ (yoneda.obj U),
          Space.h0FibreRank B integerBase hZ f p = b (Space.schemePoint B integerBase hZ U p))
    (hstruct : ∀ {X Y : AlgebraicSpaces B integerBase hZ} (f : X ⟶ Y),
      Space.IsProper B integerBase hZ f.hom → Space.IsFlat B integerBase hZ f.hom →
      Space.IsFinitePresentation B integerBase hZ f.hom →
      (∀ p : Space.FieldValuedPoint B integerBase hZ Y.1, Function.Bijective
        (algebraMap p.carrier (Space.globalFunctions B (Spec (.of p.carrier)) p.contained
          (Space.fibreOverFieldValuedPoint B integerBase hZ f.hom p)))) →
      IsIso (Space.structureSharp B integerBase hZ f) ∧
        ∀ (Y' : AlgebraicSpaces B integerBase hZ) (g : Y' ⟶ Y),
          IsIso (Space.structureSharp B integerBase hZ (pullback.snd f g))) :
    IsOpenCurvesLocus B hZ (IsH01CurveFamily B hZ) := by
  intro G
  obtain ⟨W, hW, hchar⟩ := ((isOpenCurvesLocus_hasH0RankLeOneOnFieldFibres hbetti).and
    isOpenCurvesLocus_hasFibresOfDimensionOne) G
  exact ⟨W, hW, fun F a => (isH01CurveFamily_iff_of hstruct F).trans (hchar F a)⟩

end CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **Stacks 0E6I, parts (1) and (2), from the statements of Stacks 0E0R (at `i = 0`) and of
Stacks 0E6B (a).** The hypothesis `hbetti` is parts (1) and (2) of Stacks 0E0R for `i = 0` and
`𝓕 = 𝒪_X`, with `H⁰` read as global functions; `hstruct` is part (a) of Stacks 0E6B. Then
`Curves^{h0,1} ⊂ Curves` is an open substack such that
1. the classifying morphism of a family of curves `f : X → S` factors through it exactly when
   `f_*𝒪_X = 𝒪_S`, universally, and the fibres of `f` have dimension `1`;
2. for a proper scheme `X = T` of dimension at most one over a field `k = W`, the classifying
   morphism `Spec k → Curves` of `X` factors through it exactly when `H⁰(X, 𝒪_X) = k` and
   `dim(X) = 1`. -/
theorem curvesH01_isOpenSubstack_and_factors_iff_and_over_field_iff_of_statements
    (hbetti : ∀ {U : BigFppfOver B integerBase hZ} {X : AlgebraicSpaces B integerBase hZ}
      (f : X ⟶ schemeSpace U), Space.IsProper B integerBase hZ f.hom →
      Space.IsFlat B integerBase hZ f.hom → Space.IsFinitePresentation B integerBase hZ f.hom →
      ∃ b : (BigFppfOver.toScheme B integerBase hZ).obj U → ℕ∞, UpperSemicontinuous b ∧
        ∀ p : Space.FieldValuedPoint B integerBase hZ (yoneda.obj U),
          Space.h0FibreRank B integerBase hZ f p = b (Space.schemePoint B integerBase hZ U p))
    (hstruct : ∀ {X Y : AlgebraicSpaces B integerBase hZ} (f : X ⟶ Y),
      Space.IsProper B integerBase hZ f.hom → Space.IsFlat B integerBase hZ f.hom →
      Space.IsFinitePresentation B integerBase hZ f.hom →
      (∀ p : Space.FieldValuedPoint B integerBase hZ Y.1, Function.Bijective
        (algebraMap p.carrier (Space.globalFunctions B (Spec (.of p.carrier)) p.contained
          (Space.fibreOverFieldValuedPoint B integerBase hZ f.hom p)))) →
      IsIso (Space.structureSharp B integerBase hZ f) ∧
        ∀ (Y' : AlgebraicSpaces B integerBase hZ) (g : Y' ⟶ Y),
          IsIso (Space.structureSharp B integerBase hZ (pullback.snd f g))) :
    (ObjectProperty.IsClosedUnderIsomorphisms (IsH01CurveFamily B hZ) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ (IsH01CurveFamily B hZ)
          (CurveFamily.isOpenCurvesLocus_isH01CurveFamily_of_h0FibreRank hbetti
            hstruct).prop_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ (IsH01CurveFamily B hZ)
          (CurveFamily.isOpenCurvesLocus_isH01CurveFamily_of_h0FibreRank hbetti
            hstruct).prop_of_hom)) ∧
    (∀ (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsH01CurveFamily B hZ),
          z ⋙ ObjectProperty.ι (IsH01CurveFamily B hZ) = y) ↔
        IsH01CurveFamily B hZ (y.obj (Over.mk (𝟙 U.left))))) ∧
    (∀ {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W) (k : Type u) [Field k]
      (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
      (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
      (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
      (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
      (hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap g).hom)
      (hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap g).hom)
      (hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap g).hom)
      (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
      (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      (y.obj (Over.mk (𝟙 U.left)) ≅
        curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim) →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsH01CurveFamily B hZ),
          z ⋙ ObjectProperty.ι (IsH01CurveFamily B hZ) = y) ↔
        Function.Bijective ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW).appTop ∧
          topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1)) :=
  have hP := CurveFamily.isOpenCurvesLocus_isH01CurveFamily_of_h0FibreRank hbetti hstruct
  have hpush : ∀ X : CurveFamily B hZ, CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ X →
      HasUniversallyBijectiveGlobalFunctions B hZ X := fun _ hX =>
    CurveFamily.hasUniversallyBijectiveGlobalFunctions_of_hasBijectiveGlobalFunctionsOnFieldFibres
      hstruct hX
  ⟨isOpenImmersion_curvesSubstackInclusion hP,
    fun U y hy => factors_curvesSubstack_iff hP U y hy,
    fun g k _ hW hflat hproper hlfp hqc hsep hqsep hdim U y hy e =>
      (factors_curvesSubstack_iff_of_iso hP U y hy _ e).trans
        (CurveFamily.isH01CurveFamily_curveFamilyOfSchemeMorphism_iff_of hpush g k hW hflat
          hproper hlfp hqc hsep hqsep hdim)⟩

end AlgebraicGeometry

end
