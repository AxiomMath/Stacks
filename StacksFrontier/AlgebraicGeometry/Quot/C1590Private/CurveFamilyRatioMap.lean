module

public import Mathlib.AlgebraicGeometry.Limits
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilies
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDiagramBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdeals
public import StacksFrontier.AlgebraicGeometry.Spaces.ComplementChartDiagramCofinal
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModuleFMapCompDischarge
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFiniteReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismToAffineScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteObjectOfFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroSchemeOfCanonicalSection

/-!
# The ratio map of the complement of an effective Cartier divisor

Let `Y` be an algebraic space and `D ⊆ Y` an effective Cartier divisor, with invertible sheaf
`𝒪_Y(D)` and canonical section `1_D`. On every étale chart of the open complement `Y ∖ D` the
canonical section is a basis of `𝒪_Y(D)` (the unit function lies in the defining ideal of `D`
there), so every global section `t` of `𝒪_Y(D)` has a ratio `t / 1_D`, a global regular function
on `Y ∖ D`. Over an affine object `Sb` of the site, finitely many such functions define a morphism
`Y ∖ D ⟶ 𝔸ⁿ_{Sb}` (Stacks 05Z1).

## Main definitions

* `AlgebraicGeometry.C1590Private.ratio`: the ratio `t / 1_D` as a global function on `Y ∖ D`.
* `AlgebraicGeometry.C1590Private.affineSpaceOver`: `𝔸ⁿ` over an affine object of the site.
* `AlgebraicGeometry.C1590Private.ratioMap`: the morphism to `𝔸ⁿ_{Sb}` of `n` global functions.

## Main results

* `AlgebraicGeometry.C1590Private.bijective_smul_canonicalSection_complementChart`: `1_D` is a
  basis of `𝒪_Y(D)` on the charts of `Y ∖ D`.
* `AlgebraicGeometry.C1590Private.ratioMap_comp_proj`: the ratio map lies over `Sb`.
* `AlgebraicGeometry.C1590Private.smul_modulePullbackChartSection_injective`: a basis pulls back
  to a cancellable section over an affine chart diagram.

## References

* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
* [Stacks Project, Tag 05Z1](https://stacks.math.columbia.edu/tag/05Z1)
* [Stacks Project, Tag 0841](https://stacks.math.columbia.edu/tag/0841)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.C1590Private

universe u

open Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An étale chart of the open complement `Y ∖ Z` of a closed subspace, read as a chart of `Y`,
misses `Z`: the unit function lies in the defining ideal of `Z` there. The base change of
`Z ⟶ Y` to the chart factors through `Z` and through the open complement, so it is empty. -/
theorem one_mem_definingIdealAt_complementChart (Y : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS Y.1)
    (U : Space.SmallEtale B S hS (openComplementSpace B S hS Y Z).1) :
    (1 : ToType ((structureRingSheaf B S hS Y).obj.obj (op ((complementChart B S hS Y Z).obj U))))
      ∈ definingIdealAt B S hS Y Z (op ((complementChart B S hS Y Z).obj U)) := by
  set Ū := (complementChart B S hS Y Z).obj U
  have hsq := Z.2.2.rep.isPullback Ū.1.hom
  set P := Z.2.2.rep.pullback Ū.1.hom
  have : IsEmpty ((BigFppfOver.toScheme B S hS).obj P) := by
    have hmem := (U.1.hom.app (op P) (Z.2.2.rep.snd Ū.1.hom)).2
    refine hmem (op P) (𝟙 _) ?_
    have h := congrFun (congrArg (fun φ => φ.app (op P)) hsq.w) (𝟙 P)
    simp only [NatTrans.comp_app_apply] at h
    have h4 : ((U.1.hom.app (op P)) (Z.2.2.rep.snd Ū.1.hom)).1 =
        ((Z.2.2.rep.fst Ū.1.hom).app (op P) (𝟙 P)).1 := by
      refine Eq.trans ?_ h.symm
      rfl
    rw [Functor.map_id_apply, h4]
    exact ((Z.2.2.rep.fst Ū.1.hom).app (op P) (𝟙 P)).2
  have hsub : Subsingleton Γ((BigFppfOver.toScheme B S hS).obj P, ⊤) := inferInstance
  rw [definingIdealAt_eq_ker]
  exact (RingHom.mem_ker).2 (@Subsingleton.elim _ hsub _ _)



open Stacks.PresheafOfModules.TensorInternalHom Stacks.SheafOfModules.Invertible

variable (X : AlgebraicSpaces B S hS)
    (D : ClosedSubspaces B S hS X.1) (hD : IsEffectiveCartierDivisor B S hS X D)

omit hD in
private theorem restrictₛₗ_id_associatedInvertibleSheaf' (hD : IsEffectiveCartierDivisor B S hS X D)
    (V : Space.SmallEtale B S hS X.1)
    (σ : (modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D hD)).obj (op V)) :
    (modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D hD)).restrictₛₗ (𝟙 V).op σ =
      σ :=
  restrictₛₗ_id_apply B S hS X (associatedInvertibleSheaf B S hS X D hD) V σ

/-- The sheaf-hom attached to a section `σ` of `𝒪_X(D)` over `V` takes a multiple of the
restriction of a section `t` of `𝓘_D` over `V` to that multiple of the restricted contraction of
`σ` with `t`. This is `AlgebraicGeometry.Space.homSectionCoeff_smul_unitIsoGenerator` for an
arbitrary section `t` in place of the generator of a trivialization. -/
theorem homSectionCoeff_smul_restrict (V : Space.SmallEtale B S hS X.1)
    (t : (modulePresheaf B S hS X (idealSheafOfModules B S hS X D)).obj (op V))
    (W : Space.SmallEtale B S hS X.1) (f : W ⟶ V)
    (r : ToType ((structureRingSheaf B S hS X).obj.obj (op W)))
    (σ : (modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D hD)).obj (op V)) :
    homSectionCoeff (structureCommRings B S hS X)
        (modulePresheaf B S hS X (idealSheafOfModules B S hS X D))
        (modulePresheaf B S hS X (SheafOfModules.unit (structureRingSheaf B S hS X))) V
        (associatedInvertibleSheafHomEquiv B S hS X D hD V σ) (op W) f
        (r • (idealSheafOfModules B S hS X D).val.restrictₛₗ f.op t) =
      r * ((structureRingSheaf B S hS X).obj.map f.op).hom
        (canonicalSectionDual B S hS X D hD (op V) t σ) := by
  have hmap := map_smul (homSectionCoeff (structureCommRings B S hS X)
      (modulePresheaf B S hS X (idealSheafOfModules B S hS X D))
      (modulePresheaf B S hS X (SheafOfModules.unit (structureRingSheaf B S hS X))) V
      (associatedInvertibleSheafHomEquiv B S hS X D hD V σ) (op W) f)
    (show ToType ((structureCommRings B S hS X).obj (op W)) from r)
    (show (modulePresheaf B S hS X (idealSheafOfModules B S hS X D)).obj (op W) from
      (idealSheafOfModules B S hS X D).val.restrictₛₗ f.op t)
  refine hmap.trans (congrArg (fun z => r * z) ?_)
  have hr := homSectionCoeff_restrict (structureCommRings B S hS X)
    (modulePresheaf B S hS X (idealSheafOfModules B S hS X D))
    (modulePresheaf B S hS X (SheafOfModules.unit (structureRingSheaf B S hS X))) V
    (associatedInvertibleSheafHomEquiv B S hS X D hD V σ) f.op (𝟙 V) t
  rw [Category.comp_id] at hr
  refine hr.trans (congrArg _ ?_)
  have hh := associatedInvertibleSheafHomEquiv_apply B S hS X D hD V σ (op V) (𝟙 V) t
  rw [restrictₛₗ_id_associatedInvertibleSheaf' B S hS X D hD V σ] at hh
  exact hh

/-- The inclusion `𝓘_D ⟶ 𝒪_X` on the sections over an étale chart. -/
abbrev idealIncl (W : Space.SmallEtale B S hS X.1)
    (x : (modulePresheaf B S hS X (idealSheafOfModules B S hS X D)).obj (op W)) :
    ToType ((structureRingSheaf B S hS X).obj.obj (op W)) :=
  ((valPresheafMap (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
    (definingIdealSheaf B S hS X D).ι).app (op W)).hom x

/-- Below a chart on which a section `t₁` of `𝓘_D` is the unit function, every section of `𝓘_D`
is its value in `𝒪_X` times the restriction of `t₁`. -/
theorem eq_smul_restrict_of_idealIncl_eq_one (V : Space.SmallEtale B S hS X.1)
    (t₁ : (modulePresheaf B S hS X (idealSheafOfModules B S hS X D)).obj (op V))
    (ht : idealIncl B S hS X D V t₁ = 1) (W : Space.SmallEtale B S hS X.1) (f : W ⟶ V)
    (x : (modulePresheaf B S hS X (idealSheafOfModules B S hS X D)).obj (op W)) :
    x = idealIncl B S hS X D W x • (idealSheafOfModules B S hS X D).val.restrictₛₗ f.op t₁ := by
  apply Subtype.ext
  calc _ = idealIncl B S hS X D W x * 1 := (mul_one _).symm
    _ = idealIncl B S hS X D W x * ((structureRingSheaf B S hS X).obj.map f.op).hom
          (idealIncl B S hS X D V t₁) := by rw [ht, map_one]
    _ = _ := rfl

/-- **Contraction with a section of `𝓘_D` which is the unit function is injective** on the
sections of `𝒪_X(D)` over the chart: a sheaf-hom out of `𝓘_D` is determined by its value on that
section, every section of `𝓘_D` below the chart being a multiple of its restriction. -/
theorem canonicalSectionDual_injective_of_idealIncl_eq_one (V : Space.SmallEtale B S hS X.1)
    (t₁ : (modulePresheaf B S hS X (idealSheafOfModules B S hS X D)).obj (op V))
    (ht : idealIncl B S hS X D V t₁ = 1) :
    Function.Injective (canonicalSectionDual B S hS X D hD (op V) t₁) := by
  intro σ σ' hσ
  refine (associatedInvertibleSheafHomEquiv B S hS X D hD V).injective ?_
  refine homSection_ext (structureCommRings B S hS X)
    (modulePresheaf B S hS X (idealSheafOfModules B S hS X D))
    (modulePresheaf B S hS X (SheafOfModules.unit (structureRingSheaf B S hS X))) V _ _
    fun W f t => ?_
  rw [eq_smul_restrict_of_idealIncl_eq_one B S hS X D V t₁ ht W.unop f t,
    homSectionCoeff_smul_restrict B S hS X D hD V t₁ W.unop f _ σ,
    homSectionCoeff_smul_restrict B S hS X D hD V t₁ W.unop f _ σ', hσ]

/-- The canonical section `1_D` over an étale chart, as a section of the module presheaf of
`𝒪_X(D)`. -/
abbrev canonicalSectionAt (V : Space.SmallEtale B S hS X.1) :
    (modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D hD)).obj (op V) :=
  (canonicalSection B S hS X D hD).eval (op V)

/-- **The canonical section is a basis of `𝒪_X(D)` on a chart where some section of `𝓘_D` is
the unit function**: multiplication of the regular functions on the chart against `1_D` is
bijective onto the sections of `𝒪_X(D)` there. -/
theorem bijective_smul_canonicalSection_of_idealIncl_eq_one (V : Space.SmallEtale B S hS X.1)
    (t₁ : (modulePresheaf B S hS X (idealSheafOfModules B S hS X D)).obj (op V))
    (ht : idealIncl B S hS X D V t₁ = 1) :
    Function.Bijective (fun r : ToType ((structureCommRings B S hS X).obj (op V)) =>
      r • canonicalSectionAt B S hS X D hD V) := by
  have hone : canonicalSectionDual B S hS X D hD (op V) t₁
      (canonicalSectionAt B S hS X D hD V) = 1 :=
    (canonicalSectionDual_canonicalSection B S hS X D hD (op V) t₁).trans ht
  have hl : ∀ r, canonicalSectionDual B S hS X D hD (op V) t₁
      (r • canonicalSectionAt B S hS X D hD V) = r := fun r => by
    rw [map_smul, hone, smul_eq_mul, mul_one]
  refine ⟨fun r r' h => (hl r).symm.trans ((congrArg _ h).trans (hl r')), fun σ => ?_⟩
  refine ⟨canonicalSectionDual B S hS X D hD (op V) t₁ σ,
    canonicalSectionDual_injective_of_idealIncl_eq_one B S hS X D hD V t₁ ht ?_⟩
  exact hl _

/-- The unit function, as a section of `𝓘_D` over a chart of the open complement `X ∖ D`. -/
abbrev unitIdealSection (U : Space.SmallEtale B S hS (openComplementSpace B S hS X D).1) :
    (modulePresheaf B S hS X (idealSheafOfModules B S hS X D)).obj
      (op ((complementChart B S hS X D).obj U)) :=
  ⟨(1 : ToType ((structureRingSheaf B S hS X).obj.obj (op ((complementChart B S hS X D).obj U)))),
    one_mem_definingIdealAt_complementChart B S hS X D U⟩

/-- On a chart of the open complement `X ∖ D`, the canonical section is a basis of `𝒪_X(D)`. -/
theorem bijective_smul_canonicalSection_complementChart
    (U : Space.SmallEtale B S hS (openComplementSpace B S hS X D).1) :
    Function.Bijective (fun r : ToType ((structureCommRings B S hS X).obj
        (op ((complementChart B S hS X D).obj U))) =>
      r • canonicalSectionAt B S hS X D hD ((complementChart B S hS X D).obj U)) :=
  bijective_smul_canonicalSection_of_idealIncl_eq_one B S hS X D hD _
    (unitIdealSection B S hS X D U) rfl

/-- The ratio `t / 1_D` of a section `t` of `𝒪_X(D)` by the canonical section, on a chart of the
open complement `X ∖ D`. -/
def ratioAt (t : (associatedInvertibleSheaf B S hS X D hD).val.sections)
    (U : Space.SmallEtale B S hS (openComplementSpace B S hS X D).1) :
    ToType ((structureCommRings B S hS X).obj (op ((complementChart B S hS X D).obj U))) :=
  (Equiv.ofBijective _ (bijective_smul_canonicalSection_complementChart B S hS X D hD U)).symm
    (t.eval (op ((complementChart B S hS X D).obj U)))

/-- The ratio `t / 1_D` times the canonical section `1_D` is `t`, on a chart of `X ∖ D`. -/
theorem ratioAt_smul (t : (associatedInvertibleSheaf B S hS X D hD).val.sections)
    (U : Space.SmallEtale B S hS (openComplementSpace B S hS X D).1) :
    ratioAt B S hS X D hD t U •
        canonicalSectionAt B S hS X D hD ((complementChart B S hS X D).obj U) =
      t.eval (op ((complementChart B S hS X D).obj U)) :=
  (Equiv.ofBijective _
    (bijective_smul_canonicalSection_complementChart B S hS X D hD U)).apply_symm_apply _

/-- **The ratio `t / 1_D` on the open complement `X ∖ D`**, as a global regular function there:
the ratios on the charts of `X ∖ D` are compatible. -/
def ratio (t : (associatedInvertibleSheaf B S hS X D hD).val.sections) :
    globalFunctions B S hS (openComplementSpace B S hS X D).1 :=
  ⟨fun U => ratioAt B S hS X D hD t U.unop, fun {U U'} g => by
    apply (bijective_smul_canonicalSection_complementChart B S hS X D hD U'.unop).1
    have h1 := restrictₛₗ_smul (structureCommRings B S hS X)
      (modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D hD))
      ((complementChart B S hS X D).map g.unop).op (ratioAt B S hS X D hD t U.unop)
      (canonicalSectionAt B S hS X D hD ((complementChart B S hS X D).obj U.unop))
    rw [ratioAt_smul] at h1
    have h2 : (modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D hD)).restrictₛₗ
        ((complementChart B S hS X D).map g.unop).op
        (t.eval (op ((complementChart B S hS X D).obj U.unop))) =
        t.eval (op ((complementChart B S hS X D).obj U'.unop)) := t.2 _
    have h3 : (modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D hD)).restrictₛₗ
        ((complementChart B S hS X D).map g.unop).op
        (canonicalSectionAt B S hS X D hD ((complementChart B S hS X D).obj U.unop)) =
        canonicalSectionAt B S hS X D hD ((complementChart B S hS X D).obj U'.unop) :=
      (canonicalSection B S hS X D hD).2 _
    rw [h2, h3] at h1
    exact h1.symm.trans (ratioAt_smul B S hS X D hD t U'.unop).symm⟩

/-- Pullback of global functions along a morphism to an object of the site is functorial in the
target. -/
theorem pullbackToGlobalFunctions_comp_schemeSpaceMap (Y : AlgebraicSpaces B S hS)
    {T T' : BigFppfOver B S hS} (f : Y ⟶ schemeSpace T) (h : T ⟶ T') :
    pullbackToGlobalFunctions B S hS Y T' (f ≫ schemeSpaceMap h) =
      (pullbackToGlobalFunctions B S hS Y T f).comp
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map h).op).hom := by
  ext s U
  have key : yoneda.preimage (U.unop.1.hom ≫ f.hom ≫ yoneda.map h) =
      yoneda.preimage (U.unop.1.hom ≫ f.hom) ≫ h := yoneda.map_injective <| by
    rw [Functor.map_preimage, Functor.map_comp, Functor.map_preimage]
    exact (Category.assoc _ _ _).symm
  have e := congrArg (fun k => (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map k).op).hom s) key
  simp only [Functor.map_comp, op_comp, CommRingCat.hom_comp] at e
  exact e

/-- On an affine scheme `Z`, the composite `Spec Γ(Z)[x] ⟶ Spec Γ(Z) ≅ Z` pulls a global function
back to the constant polynomial. -/
theorem ΓSpecIso_hom_appTop_spec_comp_isoSpec_inv (Z : Scheme.{u}) [IsAffine Z] (n : ℕ)
    (s : Γ(Z, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Γ(Z, ⊤)))).hom.hom
      ((Scheme.Γ.map (Spec.map (CommRingCat.ofHom (algebraMap Γ(Z, ⊤)
        (MvPolynomial (Fin n) Γ(Z, ⊤)))) ≫ Z.isoSpec.inv).op).hom s) = MvPolynomial.C s := by
  have hinv : Z.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso Γ(Z, ⊤)).hom = 𝟙 _ := by
    rw [← Scheme.toSpecΓ_appTop, ← Scheme.Hom.comp_appTop, Scheme.toSpecΓ_isoSpec_inv,
      Scheme.Hom.id_appTop]
  have key : (Spec.map (CommRingCat.ofHom (algebraMap Γ(Z, ⊤)
        (MvPolynomial (Fin n) Γ(Z, ⊤)))) ≫ Z.isoSpec.inv).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Γ(Z, ⊤)))).hom =
      CommRingCat.ofHom (algebraMap Γ(Z, ⊤) (MvPolynomial (Fin n) Γ(Z, ⊤))) := by
    rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc]
    exact (congrArg (· ≫ CommRingCat.ofHom (algebraMap Γ(Z, ⊤) (MvPolynomial (Fin n) Γ(Z, ⊤))))
      hinv).trans (Category.id_comp _)
  exact congrArg (fun φ => φ.hom s) key

/-- **A basis pulls back to a cancellable section.** Over an affine chart diagram for `f`, if `b`
is a basis of the sections of a quasi-coherent module `M` over the target chart, then
multiplication against the chart pullback of `b` is injective on the regular functions of the
source chart: the base-change comparison is bijective and the base change of a free module of
rank one is free of rank one. -/
theorem smul_modulePullbackChartSection_injective {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (M : Space.Modules.{u, u} B S hS Y.1 Y.2) (hM : M.IsQuasicoherentOnSite)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (haU : IsAffine ((Space.SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (haV : IsAffine ((Space.SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V))
    (b : M.val.obj (op d.V))
    (hb : Function.Bijective fun r : chartRing B S hS Y.1 Y.2 d.V => r • b) :
    Function.Injective fun a : chartRing B S hS X.1 X.2 d.U =>
      a • modulePullbackChartSection B S hS f M d b := by
  let := chartDiagramAlgebra B S hS f d
  intro a a' h
  have h1 : TensorProduct.tmul (chartRing B S hS Y.1 Y.2 d.V) a b =
      TensorProduct.tmul (chartRing B S hS Y.1 Y.2 d.V) a' b :=
    (bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS f M hM d haU haV).1 h
  let e : chartRing B S hS Y.1 Y.2 d.V ≃ₗ[chartRing B S hS Y.1 Y.2 d.V] M.val.obj (op d.V) :=
    LinearEquiv.ofBijective (LinearMap.toSpanSingleton _ _ b) hb
  have h2 := congrArg (TensorProduct.rid (chartRing B S hS Y.1 Y.2 d.V)
    (chartRing B S hS X.1 X.2 d.U) ∘ (LinearMap.lTensor (chartRing B S hS X.1 X.2 d.U)
      e.symm.toLinearMap)) h1
  have he : e.symm b = 1 := e.injective <| (e.apply_symm_apply b).trans (one_smul _ _).symm
  have hr : ∀ c : chartRing B S hS X.1 X.2 d.U, (TensorProduct.rid (chartRing B S hS Y.1 Y.2 d.V)
      (chartRing B S hS X.1 X.2 d.U)) (LinearMap.lTensor (chartRing B S hS X.1 X.2 d.U)
        e.symm.toLinearMap (TensorProduct.tmul (chartRing B S hS Y.1 Y.2 d.V) c b)) = c := by
    intro c
    rw [LinearMap.lTensor_tmul, LinearEquiv.coe_coe, he, TensorProduct.rid_tmul, one_smul]
  exact (hr a).symm.trans (h2.trans (hr a'))

section AffineSpace

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- The morphism `Spec A[x₁, …, xₙ] ⟶ Spec A` is locally of finite type. -/
instance locallyOfFiniteType_spec_algebraMap_mvPolynomial (A : CommRingCat.{u}) (n : ℕ) :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin n) A)))) :=
  HasRingHomProperty.Spec_iff.2 (RingHom.finiteType_algebraMap.2 inferInstance)

/-- The affine space `𝔸ⁿ` over an affine object `Sb` of the site, as an object of the site: the
spectrum of the polynomial ring in `n` variables over `Γ(Sb, 𝒪)`, contained in the site because it
is of finite type over `Sb`. -/
noncomputable def affineSpaceOver (Sb : BigFppfOver B integerBase hZ)
    [IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj Sb)] (n : ℕ) :
    BigFppfOver B integerBase hZ :=
  BigFppfOver.siteObjectOver B integerBase hZ Sb
    (Space.contains_of_locallyOfFiniteType_of_quasiCompact B integerBase hZ (Y₀ := Sb)
      (Spec.map (CommRingCat.ofHom (algebraMap Γ((BigFppfOver.toScheme B integerBase hZ).obj Sb, ⊤)
        (MvPolynomial (Fin n) Γ((BigFppfOver.toScheme B integerBase hZ).obj Sb, ⊤)))) ≫
        ((BigFppfOver.toScheme B integerBase hZ).obj Sb).isoSpec.inv))
    (Spec.map (CommRingCat.ofHom (algebraMap Γ((BigFppfOver.toScheme B integerBase hZ).obj Sb, ⊤)
        (MvPolynomial (Fin n) Γ((BigFppfOver.toScheme B integerBase hZ).obj Sb, ⊤)))) ≫
        ((BigFppfOver.toScheme B integerBase hZ).obj Sb).isoSpec.inv)

/-- The affine space `𝔸ⁿ_{Sb}` over an affine object `Sb` of the site is affine. -/
instance (Sb : BigFppfOver B integerBase hZ)
    [IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj Sb)] (n : ℕ) :
    IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj (affineSpaceOver Sb n)) :=
  inferInstanceAs (IsAffine (Spec _))

/-- The structure morphism `𝔸ⁿ_{Sb} ⟶ Sb`. -/
noncomputable def affineSpaceOverProj (Sb : BigFppfOver B integerBase hZ)
    [IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj Sb)] (n : ℕ) :
    affineSpaceOver Sb n ⟶ Sb :=
  BigFppfOver.siteMapOver B integerBase hZ Sb _ _

/-- The ring homomorphism `Γ(𝔸ⁿ_{Sb}, 𝒪) ⟶ Γ(Y, 𝒪)` of a morphism `p : Y ⟶ Sb` and `n` global
functions `r` on `Y`: the coordinates go to the `r j` and the scalars are pulled back along
`p`. -/
noncomputable def ratioRingHom (Sb : BigFppfOver B integerBase hZ)
    [IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj Sb)] {n : ℕ}
    (Y : AlgebraicSpaces B integerBase hZ) (p : Y ⟶ schemeSpace Sb)
    (r : Fin n → globalFunctions B integerBase hZ Y.1) :
    Γ((BigFppfOver.toScheme B integerBase hZ).obj (affineSpaceOver Sb n), ⊤) →+*
      globalFunctions B integerBase hZ Y.1 :=
  (MvPolynomial.eval₂Hom (pullbackToGlobalFunctions B integerBase hZ Y Sb p) r).comp
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n)
      Γ((BigFppfOver.toScheme B integerBase hZ).obj Sb, ⊤)))).hom.hom

/-- **The morphism `Y ⟶ 𝔸ⁿ_{Sb}` of `n` global functions** over a morphism `p : Y ⟶ Sb` to an
affine object of the site (Stacks 05Z1). -/
noncomputable def ratioMap (Sb : BigFppfOver B integerBase hZ)
    [IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj Sb)] {n : ℕ}
    (Y : AlgebraicSpaces B integerBase hZ) (p : Y ⟶ schemeSpace Sb)
    (r : Fin n → globalFunctions B integerBase hZ Y.1) :
    Y ⟶ schemeSpace (affineSpaceOver Sb n) :=
  (morphismToAffineEquiv B integerBase hZ Y (affineSpaceOver Sb n) specULiftZIsTerminal).1.symm
    (ratioRingHom Sb Y p r)

/-- The equivalence between morphisms `Y ⟶ T` to an affine object and ring homomorphisms
`Γ(T, 𝒪) ⟶ Γ(Y, 𝒪)` sends a morphism to its pullback on global functions. -/
theorem morphismToAffineEquiv_apply (Y : AlgebraicSpaces B integerBase hZ)
    (T : BigFppfOver B integerBase hZ) [IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj T)]
    (f : Y ⟶ schemeSpace T) :
    (morphismToAffineEquiv B integerBase hZ Y T specULiftZIsTerminal).1 f =
      pullbackToGlobalFunctions B integerBase hZ Y T f := rfl

/-- The pullback of global functions along `ratioMap Sb Y p r` is `ratioRingHom Sb Y p r`. -/
theorem pullbackToGlobalFunctions_ratioMap (Sb : BigFppfOver B integerBase hZ)
    [IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj Sb)] {n : ℕ}
    (Y : AlgebraicSpaces B integerBase hZ) (p : Y ⟶ schemeSpace Sb)
    (r : Fin n → globalFunctions B integerBase hZ Y.1) :
    pullbackToGlobalFunctions B integerBase hZ Y (affineSpaceOver Sb n) (ratioMap Sb Y p r) =
      ratioRingHom Sb Y p r :=
  (morphismToAffineEquiv B integerBase hZ Y (affineSpaceOver Sb n)
    specULiftZIsTerminal).1.apply_symm_apply _

/-- The structure morphism `𝔸ⁿ_{Sb} ⟶ Sb` pulls a global function `s` on `Sb` back to the
constant polynomial `C s`. -/
theorem ΓSpecIso_hom_Γ_map_affineSpaceOverProj (Sb : BigFppfOver B integerBase hZ)
    [IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj Sb)] (n : ℕ)
    (s : Γ((BigFppfOver.toScheme B integerBase hZ).obj Sb, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n)
      Γ((BigFppfOver.toScheme B integerBase hZ).obj Sb, ⊤)))).hom.hom
      ((Scheme.Γ.map ((BigFppfOver.toScheme B integerBase hZ).map
        (affineSpaceOverProj Sb n)).op).hom s) = MvPolynomial.C s :=
  ΓSpecIso_hom_appTop_spec_comp_isoSpec_inv _ n s

/-- The morphism of global functions lies over `Sb`. -/
theorem ratioMap_comp_proj (Sb : BigFppfOver B integerBase hZ)
    [IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj Sb)] {n : ℕ}
    (Y : AlgebraicSpaces B integerBase hZ) (p : Y ⟶ schemeSpace Sb)
    (r : Fin n → globalFunctions B integerBase hZ Y.1) :
    ratioMap Sb Y p r ≫ schemeSpaceMap (affineSpaceOverProj Sb n) = p := by
  apply (morphismToAffineEquiv B integerBase hZ Y Sb specULiftZIsTerminal).1.injective
  rw [morphismToAffineEquiv_apply, morphismToAffineEquiv_apply,
    pullbackToGlobalFunctions_comp_schemeSpaceMap, pullbackToGlobalFunctions_ratioMap]
  ext s : 1
  exact (congrArg (MvPolynomial.eval₂Hom (pullbackToGlobalFunctions B integerBase hZ Y Sb p) r)
    (ΓSpecIso_hom_Γ_map_affineSpaceOverProj Sb n s)).trans (MvPolynomial.eval₂Hom_C _ _ _)

/-- The underlying morphism of `ratioMap Sb Y p r` composed with the projection is `p.hom`. -/
private theorem ratioMap_comp_proj_hom (Sb : BigFppfOver B integerBase hZ)
    [IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj Sb)] {n : ℕ}
    (Y : AlgebraicSpaces B integerBase hZ) (p : Y ⟶ schemeSpace Sb)
    (r : Fin n → globalFunctions B integerBase hZ Y.1) :
    (ratioMap Sb Y p r).hom ≫ (schemeSpaceMap (affineSpaceOverProj Sb n)).hom = p.hom :=
  congrArg (·.hom) (ratioMap_comp_proj Sb Y p r)

/-- If `p : Y ⟶ Sb` is locally of finite type, then so is `ratioMap Sb Y p r`. -/
theorem isLocallyOfFiniteType_ratioMap (Sb : BigFppfOver B integerBase hZ)
    [IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj Sb)] {n : ℕ}
    (Y : AlgebraicSpaces B integerBase hZ) (p : Y ⟶ schemeSpace Sb)
    (r : Fin n → globalFunctions B integerBase hZ Y.1)
    (hp : IsLocallyOfFiniteType B integerBase hZ p.hom) :
    IsLocallyOfFiniteType B integerBase hZ (ratioMap Sb Y p r).hom := by
  exact isLocallyOfFiniteType_of_comp B integerBase hZ Y.2 (isAlgebraicSpace_yoneda _ _ _ _)
    (isAlgebraicSpace_yoneda _ _ _ _) _ _ (ratioMap_comp_proj_hom Sb Y p r ▸ hp)

/-- If `p : Y ⟶ Sb` is separated, then so is `ratioMap Sb Y p r`. -/
theorem isSeparated_ratioMap (Sb : BigFppfOver B integerBase hZ)
    [IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj Sb)] {n : ℕ}
    (Y : AlgebraicSpaces B integerBase hZ) (p : Y ⟶ schemeSpace Sb)
    (r : Fin n → globalFunctions B integerBase hZ Y.1)
    (hp : Space.IsSeparated B integerBase hZ p.hom) :
    Space.IsSeparated B integerBase hZ (ratioMap Sb Y p r).hom := by
  exact isSeparated_of_comp B integerBase hZ _ _ (ratioMap_comp_proj_hom Sb Y p r ▸ hp)

end AffineSpace

end AlgebraicGeometry.C1590Private

end
