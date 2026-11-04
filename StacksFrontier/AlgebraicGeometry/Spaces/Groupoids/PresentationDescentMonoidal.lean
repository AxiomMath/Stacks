module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PresentationSchemeDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SpaceBaseDescentTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesTensorQuasicoherent

/-!
# Descent along a presentation is monoidal

Let `X = U/R` be a presentation of an algebraic space, and let `(M, τ)`, `(N, σ)`, `(K, κ)` be
quasi-coherent modules on the presenting scheme `U` with scheme transitions satisfying the cocycle
and unit conditions, so that they descend to quasi-coherent `𝒪_X`-modules `D(M)`, `D(N)`, `D(K)`
(`AlgebraicGeometry.Space.presentationDescendedModule`, Stacks 03M3).  This file descends a
multiplication: a morphism `μ : M^a ⊗ N^a ⟶ K^a` of the attached modules on the atlas which carries
the tensor product of the transitions `τ^a ⊗ σ^a` to `κ^a` (a hypothesis on the space `R`, read
through Stacks 03EL along the target and the source) descends to a unique morphism
`D(M) ⊗ D(N) ⟶ D(K)` whose inverse image along the atlas is `μ`, through Stacks 03EL and the chart
identifications.  This is the step of Stacks 084D that descends the multiplication of the twists.

## Main definitions

* `AlgebraicGeometry.Space.presentationDescendedTensorObj`: `D(M) ⊗ D(N)` as a quasi-coherent
  `𝒪_X`-module.
* `AlgebraicGeometry.Space.presentationDescendedTensorChartHom`: the morphism on the atlas to be
  descended.
* `AlgebraicGeometry.Space.presentationDescendedTensorHom`: **the descended multiplication**.

## Main results

* `AlgebraicGeometry.Space.presentationQuasicoherentEquivalence_compatible_iff`: a morphism between
  inverse images along the atlas is a morphism of groupoid modules exactly when it carries one
  canonical transition morphism to the other.
* `AlgebraicGeometry.Space.presentationDescendedTensorChartHom_compatible`: the chart morphism is
  a morphism of groupoid modules; the input is that the canonical transition morphism is monoidal,
  `AlgebraicGeometry.Space.spaceBaseDescent_tensor`.
* `AlgebraicGeometry.Space.existsUnique_presentationDescendedTensorHom`, with
  `AlgebraicGeometry.Space.presentationDescendedTensorHom_spec` and
  `AlgebraicGeometry.Space.presentationDescendedTensorHom_unique`: **descent along a presentation
  is monoidal**.

## Implementation notes

The compatibility is computed in an abstract lemma at variables and instantiated once with every
argument explicit.  The statement crossing the spelling `(e.functor.obj Y).F.obj` of the groupoid
module of `Y` and the spelling `φ^*Y` is isolated in
`AlgebraicGeometry.Space.presentationQuasicoherentEquivalence_compatible_iff` and
`AlgebraicGeometry.Space.presentationQuasicoherentEquivalence_functor_map_hom`, each stated at
variables, so that no larger statement asks the kernel to unfold the equivalence of Stacks 03M3.

## References

* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

/-- The abstract shape of the compatibility in
`AlgebraicGeometry.Space.existsUnique_presentationDescendedTensorHom`, at variables. -/
private theorem descend_tensor_compatible_of_readings {CU CV : Type*} [Category CU]
    [MonoidalCategory CU] [Category CV] [MonoidalCategory CV] (Pt Ps : CU ⥤ CV)
    {Y₁₂ Y₁ Y₂ YK A₁ A₂ AK : CU} (pA : Y₁₂ ⟶ Y₁ ⊗ Y₂) (cM : Y₁ ≅ A₁) (cN : Y₂ ≅ A₂)
    (cK : YK ≅ AK) (μ : A₁ ⊗ A₂ ⟶ AK)
    (δ₁₂ : Pt.obj Y₁₂ ⟶ Ps.obj Y₁₂) (δ₁ : Pt.obj Y₁ ⟶ Ps.obj Y₁) (δ₂ : Pt.obj Y₂ ⟶ Ps.obj Y₂)
    (δK : Pt.obj YK ⟶ Ps.obj YK)
    (αM : Pt.obj A₁ ⟶ Ps.obj A₁) (αN : Pt.obj A₂ ⟶ Ps.obj A₂) (αK : Pt.obj AK ⟶ Ps.obj AK)
    (tY : Pt.obj (Y₁ ⊗ Y₂) ≅ Pt.obj Y₁ ⊗ Pt.obj Y₂) (sY : Ps.obj (Y₁ ⊗ Y₂) ≅ Ps.obj Y₁ ⊗ Ps.obj Y₂)
    (tA : Pt.obj (A₁ ⊗ A₂) ≅ Pt.obj A₁ ⊗ Pt.obj A₂) (sA : Ps.obj (A₁ ⊗ A₂) ≅ Ps.obj A₁ ⊗ Ps.obj A₂)
    (hL : Pt.map pA ≫ tY.hom ≫ (δ₁ ⊗ₘ δ₂) = δ₁₂ ≫ Ps.map pA ≫ sY.hom)
    (hsY : Ps.map (cM.hom ⊗ₘ cN.hom) ≫ sA.hom = sY.hom ≫ (Ps.map cM.hom ⊗ₘ Ps.map cN.hom))
    (htY : Pt.map (cM.hom ⊗ₘ cN.hom) ≫ tA.hom = tY.hom ≫ (Pt.map cM.hom ⊗ₘ Pt.map cN.hom))
    (hM : δ₁ ≫ Ps.map cM.hom = Pt.map cM.hom ≫ αM)
    (hN : δ₂ ≫ Ps.map cN.hom = Pt.map cN.hom ≫ αN)
    (hK : δK ≫ Ps.map cK.hom = Pt.map cK.hom ≫ αK)
    (hμ : (tA.hom ≫ (αM ⊗ₘ αN) ≫ sA.inv) ≫ Ps.map μ = Pt.map μ ≫ αK) :
    δ₁₂ ≫ Ps.map (pA ≫ (cM.hom ⊗ₘ cN.hom) ≫ μ ≫ cK.inv) =
      Pt.map (pA ≫ (cM.hom ⊗ₘ cN.hom) ≫ μ ≫ cK.inv) ≫ δK := by
  have hK' : αK ≫ Ps.map cK.inv = Pt.map cK.inv ≫ δK := by
    rw [← cancel_epi (Pt.map cK.hom), ← reassoc_of% hK, ← Pt.map_comp_assoc, Iso.hom_inv_id,
      Pt.map_id, Category.id_comp, ← Ps.map_comp, Iso.hom_inv_id, Ps.map_id, Category.comp_id]
  have hsY' : sY.inv ≫ Ps.map (cM.hom ⊗ₘ cN.hom) =
      (Ps.map cM.hom ⊗ₘ Ps.map cN.hom) ≫ sA.inv := by
    rw [Iso.inv_comp_eq, ← reassoc_of% hsY, Iso.hom_inv_id, Category.comp_id]
  have hδ : (δ₁ ⊗ₘ δ₂) ≫ (Ps.map cM.hom ⊗ₘ Ps.map cN.hom) =
      (Pt.map cM.hom ⊗ₘ Pt.map cN.hom) ≫ (αM ⊗ₘ αN) := by
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, hM, hN]
  have hL' : δ₁₂ ≫ Ps.map pA = Pt.map pA ≫ tY.hom ≫ (δ₁ ⊗ₘ δ₂) ≫ sY.inv := by
    rw [reassoc_of% hL, Iso.hom_inv_id, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hL', reassoc_of% hsY', reassoc_of% hδ, ← reassoc_of% htY]
  simp only [Category.assoc] at hμ
  rw [reassoc_of% hμ, hK']

/-- A morphism equal to `f ≫ g ≫ μ ≫ i⁻¹` followed by `i` is `f ≫ g ≫ μ`, and conversely. -/
private theorem comp_hom_eq_iff_eq_comp_inv {𝒞 : Type*} [Category 𝒞] {a b b' c d : 𝒞}
    (x : a ⟶ c) (f : a ⟶ b) (g : b ⟶ b') (μ : b' ⟶ d) (i : c ≅ d) :
    x ≫ i.hom = f ≫ g ≫ μ ↔ x = f ≫ g ≫ μ ≫ i.inv := by
  constructor
  · intro h
    rw [← reassoc_of% h, Iso.hom_inv_id, Category.comp_id]
  · intro h
    rw [h]
    simp

section Descent

attribute [local irreducible] CategoryTheory.yoneda

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (P : Presentation B S hS X.obj X.property)
  {M N K : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj P.U).ringCatSheaf).FullSubcategory}
  (τ : quasicoherentPullbackObj B S hS P.target M ⟶ quasicoherentPullbackObj B S hS P.source M)
  (hc : PresentationSchemeCocycle P M τ) (hu : PresentationSchemeUnit P M τ)
  (σ : quasicoherentPullbackObj B S hS P.target N ⟶ quasicoherentPullbackObj B S hS P.source N)
  (hc' : PresentationSchemeCocycle P N σ) (hu' : PresentationSchemeUnit P N σ)
  (κ : quasicoherentPullbackObj B S hS P.target K ⟶ quasicoherentPullbackObj B S hS P.source K)
  (hc'' : PresentationSchemeCocycle P K κ) (hu'' : PresentationSchemeUnit P K κ)

omit hc hu in
/-- A morphism between the inverse images along the atlas of two quasi-coherent `𝒪_X`-modules is
a morphism of their quasi-coherent modules on the groupoid of the presentation exactly when it
carries one canonical transition morphism to the other. -/
theorem presentationQuasicoherentEquivalence_compatible_iff
    {Y Z : QuasicoherentSheaves.{u, u} B S hS X.obj X.property}
    (h : (modulePullback B S hS (presentationAtlas P)).obj Y.obj ⟶
      (modulePullback B S hS (presentationAtlas P)).obj Z.obj) :
    QuasicoherentModule.Compatible (M := (presentationQuasicoherentEquivalence P).functor.obj Y)
        (N := (presentationQuasicoherentEquivalence P).functor.obj Z) h ↔
      TransitionCommutes B S hS (U := (presentationGroupoid P).objects)
        (V := (presentationGroupoid P).arrows) (a := (presentationGroupoid P).target)
        (b := (presentationGroupoid P).source)
        (spaceBaseDescent B S hS (presentationGroupoid P) (presentationAtlas P)
          (presentationAtlas_comm P) Y.obj)
        (spaceBaseDescent B S hS (presentationGroupoid P) (presentationAtlas P)
          (presentationAtlas_comm P) Z.obj) h := by
  unfold QuasicoherentModule.Compatible TransitionCommutes
  rw [presentationQuasicoherentEquivalence_functor_obj_alpha,
    presentationQuasicoherentEquivalence_functor_obj_alpha]
  exact Iff.rfl

/-- `AlgebraicGeometry.Space.presentationDescendedModuleChartIso_comm` with the canonical
transition morphism written as `AlgebraicGeometry.Space.spaceBaseDescent`. -/
theorem presentationDescendedModuleChartIso_comm_spaceBaseDescent :
    TransitionCommutes B S hS (U := (presentationGroupoid P).objects)
      (V := (presentationGroupoid P).arrows) (a := (presentationGroupoid P).target)
      (b := (presentationGroupoid P).source)
      (spaceBaseDescent B S hS (presentationGroupoid P) (presentationAtlas P)
        (presentationAtlas_comm P) (presentationDescendedModule P M τ hc hu).obj)
      (presentationSchemeTransition P M τ)
      (presentationDescendedModuleChartIso P M τ hc hu).hom := by
  have h := presentationDescendedModuleChartIso_comm P M τ hc hu
  rwa [presentationQuasicoherentEquivalence_functor_obj_alpha] at h

omit hc hu in
/-- The underlying morphism of the image of a morphism under the equivalence of Stacks 03M3 is
its inverse image along the atlas. -/
theorem presentationQuasicoherentEquivalence_functor_map_hom
    {Y Z : QuasicoherentSheaves.{u, u} B S hS X.obj X.property} (f : Y ⟶ Z) :
    ((presentationQuasicoherentEquivalence P).functor.map f).hom =
      (modulePullback B S hS (presentationAtlas P)).map f.hom :=
  rfl

/-- The tensor product of two descended modules, as a quasi-coherent `𝒪_X`-module. -/
abbrev presentationDescendedTensorObj : QuasicoherentSheaves.{u, u} B S hS X.obj X.property :=
  ⟨(presentationDescendedModule P M τ hc hu).obj ⊗ (presentationDescendedModule P N σ hc' hu').obj,
    haveI := isQuasicoherentOnSite_presentationDescendedModule P M τ hc hu
    haveI := isQuasicoherentOnSite_presentationDescendedModule P N σ hc' hu'
    isQuasicoherentOnSite_tensorObj B S hS X.1 X.2 _ _⟩

variable (μ : MonoidalCategoryStruct.tensorObj
      (C := Modules.{u, u} B S hS (presentationGroupoid P).objects.1
        (presentationGroupoid P).objects.2)
      ((representedQuasicoherentSchemeEquivalence B S hS P.U).functor.obj M).obj
      ((representedQuasicoherentSchemeEquivalence B S hS P.U).functor.obj N).obj ⟶
      ((representedQuasicoherentSchemeEquivalence B S hS P.U).functor.obj K).obj)
  (hμ : TransitionCommutes B S hS (U := (presentationGroupoid P).objects)
    (V := (presentationGroupoid P).arrows) (a := (presentationGroupoid P).target)
    (b := (presentationGroupoid P).source)
    ((modulePullbackTensorIso B S hS (presentationGroupoid P).target
        ((representedQuasicoherentSchemeEquivalence B S hS P.U).functor.obj M).obj
        ((representedQuasicoherentSchemeEquivalence B S hS P.U).functor.obj N).obj).hom ≫
      (presentationSchemeTransition P M τ ⊗ₘ presentationSchemeTransition P N σ) ≫
      (modulePullbackTensorIso B S hS (presentationGroupoid P).source
        ((representedQuasicoherentSchemeEquivalence B S hS P.U).functor.obj M).obj
        ((representedQuasicoherentSchemeEquivalence B S hS P.U).functor.obj N).obj).inv)
    (presentationSchemeTransition P K κ) μ)

/-- The morphism on the atlas of the descended tensor product to be descended: the inverse image
of `D(M) ⊗ D(N)` along the atlas is `M^a ⊗ N^a` through Stacks 03EL and the chart
identifications, followed by `μ` and the chart identification of `D(K)`. -/
def presentationDescendedTensorChartHom :
    (modulePullback B S hS (presentationAtlas P)).obj
        (presentationDescendedTensorObj P τ hc hu σ hc' hu').obj ⟶
      (modulePullback B S hS (presentationAtlas P)).obj
        (presentationDescendedModule P K κ hc'' hu'').obj :=
  (modulePullbackTensorIso B S hS (presentationAtlas P) _ _).hom ≫
    ((presentationDescendedModuleChartIso P M τ hc hu).hom ⊗ₘ
      (presentationDescendedModuleChartIso P N σ hc' hu').hom) ≫ μ ≫
    (presentationDescendedModuleChartIso P K κ hc'' hu'').inv

include hμ in
/-- The chart morphism carries the canonical transition morphism of the inverse image of
`D(M) ⊗ D(N)` to that of the inverse image of `D(K)`. -/
theorem presentationDescendedTensorChartHom_transitionCommutes :
    TransitionCommutes B S hS (U := (presentationGroupoid P).objects)
      (V := (presentationGroupoid P).arrows) (a := (presentationGroupoid P).target)
      (b := (presentationGroupoid P).source)
      (spaceBaseDescent B S hS (presentationGroupoid P) (presentationAtlas P)
        (presentationAtlas_comm P)
        ((presentationDescendedModule P M τ hc hu).obj ⊗
          (presentationDescendedModule P N σ hc' hu').obj))
      (spaceBaseDescent B S hS (presentationGroupoid P) (presentationAtlas P)
        (presentationAtlas_comm P) (presentationDescendedModule P K κ hc'' hu'').obj)
      (presentationDescendedTensorChartHom P τ hc hu σ hc' hu' κ hc'' hu'' μ) := by
  have hh := descend_tensor_compatible_of_readings
    (modulePullback B S hS (presentationGroupoid P).target)
    (modulePullback B S hS (presentationGroupoid P).source)
    (modulePullbackTensorIso B S hS (presentationAtlas P)
      (presentationDescendedModule P M τ hc hu).obj
      (presentationDescendedModule P N σ hc' hu').obj).hom
    (presentationDescendedModuleChartIso P M τ hc hu)
    (presentationDescendedModuleChartIso P N σ hc' hu')
    (presentationDescendedModuleChartIso P K κ hc'' hu'') μ
    (spaceBaseDescent B S hS (presentationGroupoid P) (presentationAtlas P)
      (presentationAtlas_comm P)
      ((presentationDescendedModule P M τ hc hu).obj ⊗
        (presentationDescendedModule P N σ hc' hu').obj))
    (spaceBaseDescent B S hS (presentationGroupoid P) (presentationAtlas P)
      (presentationAtlas_comm P) (presentationDescendedModule P M τ hc hu).obj)
    (spaceBaseDescent B S hS (presentationGroupoid P) (presentationAtlas P)
      (presentationAtlas_comm P) (presentationDescendedModule P N σ hc' hu').obj)
    (spaceBaseDescent B S hS (presentationGroupoid P) (presentationAtlas P)
      (presentationAtlas_comm P) (presentationDescendedModule P K κ hc'' hu'').obj)
    (presentationSchemeTransition P M τ) (presentationSchemeTransition P N σ)
    (presentationSchemeTransition P K κ)
    (modulePullbackTensorIso B S hS (presentationGroupoid P).target
      ((modulePullback B S hS (presentationAtlas P)).obj
        (presentationDescendedModule P M τ hc hu).obj)
      ((modulePullback B S hS (presentationAtlas P)).obj
        (presentationDescendedModule P N σ hc' hu').obj))
    (modulePullbackTensorIso B S hS (presentationGroupoid P).source
      ((modulePullback B S hS (presentationAtlas P)).obj
        (presentationDescendedModule P M τ hc hu).obj)
      ((modulePullback B S hS (presentationAtlas P)).obj
        (presentationDescendedModule P N σ hc' hu').obj))
    (modulePullbackTensorIso B S hS (presentationGroupoid P).target
      ((representedQuasicoherentSchemeEquivalence B S hS P.U).functor.obj M).obj
      ((representedQuasicoherentSchemeEquivalence B S hS P.U).functor.obj N).obj)
    (modulePullbackTensorIso B S hS (presentationGroupoid P).source
      ((representedQuasicoherentSchemeEquivalence B S hS P.U).functor.obj M).obj
      ((representedQuasicoherentSchemeEquivalence B S hS P.U).functor.obj N).obj)
    (spaceBaseDescent_tensor B S hS (presentationGroupoid P) (presentationAtlas P)
      (presentationAtlas_comm P) (presentationDescendedModule P M τ hc hu).obj
      (presentationDescendedModule P N σ hc' hu').obj)
    (modulePullbackTensorIso_hom_naturality B S hS (presentationGroupoid P).source
      (presentationDescendedModuleChartIso P M τ hc hu).hom
      (presentationDescendedModuleChartIso P N σ hc' hu').hom)
    (modulePullbackTensorIso_hom_naturality B S hS (presentationGroupoid P).target
      (presentationDescendedModuleChartIso P M τ hc hu).hom
      (presentationDescendedModuleChartIso P N σ hc' hu').hom)
    (presentationDescendedModuleChartIso_comm_spaceBaseDescent P τ hc hu)
    (presentationDescendedModuleChartIso_comm_spaceBaseDescent P σ hc' hu')
    (presentationDescendedModuleChartIso_comm_spaceBaseDescent P κ hc'' hu'') hμ
  have hh' : spaceBaseDescent B S hS (presentationGroupoid P) (presentationAtlas P)
        (presentationAtlas_comm P)
        ((presentationDescendedModule P M τ hc hu).obj ⊗
          (presentationDescendedModule P N σ hc' hu').obj) ≫
      (modulePullback B S hS (presentationGroupoid P).source).map
        ((modulePullbackTensorIso B S hS (presentationAtlas P)
            (presentationDescendedModule P M τ hc hu).obj
            (presentationDescendedModule P N σ hc' hu').obj).hom ≫
          ((presentationDescendedModuleChartIso P M τ hc hu).hom ⊗ₘ
            (presentationDescendedModuleChartIso P N σ hc' hu').hom) ≫
          μ ≫ (presentationDescendedModuleChartIso P K κ hc'' hu'').inv) =
      (modulePullback B S hS (presentationGroupoid P).target).map
        ((modulePullbackTensorIso B S hS (presentationAtlas P)
            (presentationDescendedModule P M τ hc hu).obj
            (presentationDescendedModule P N σ hc' hu').obj).hom ≫
          ((presentationDescendedModuleChartIso P M τ hc hu).hom ⊗ₘ
            (presentationDescendedModuleChartIso P N σ hc' hu').hom) ≫
          μ ≫ (presentationDescendedModuleChartIso P K κ hc'' hu'').inv) ≫
        spaceBaseDescent B S hS (presentationGroupoid P) (presentationAtlas P)
          (presentationAtlas_comm P) (presentationDescendedModule P K κ hc'' hu'').obj := hh
  have hu : presentationDescendedTensorChartHom P τ hc hu σ hc' hu' κ hc'' hu'' μ =
      ((modulePullbackTensorIso B S hS (presentationAtlas P)
          (presentationDescendedModule P M τ hc hu).obj
          (presentationDescendedModule P N σ hc' hu').obj).hom ≫
        ((presentationDescendedModuleChartIso P M τ hc hu).hom ⊗ₘ
          (presentationDescendedModuleChartIso P N σ hc' hu').hom) ≫
        μ ≫ (presentationDescendedModuleChartIso P K κ hc'' hu'').inv) := rfl
  unfold TransitionCommutes
  rw [hu]
  exact hh'

include hμ in
/-- The chart morphism is compatible with the canonical transition morphisms of the two inverse
images: it is a morphism of quasi-coherent modules on the groupoid of the presentation. -/
theorem presentationDescendedTensorChartHom_compatible :
    QuasicoherentModule.Compatible
      (M := (presentationQuasicoherentEquivalence P).functor.obj
        (presentationDescendedTensorObj P τ hc hu σ hc' hu'))
      (N := (presentationQuasicoherentEquivalence P).functor.obj
        (presentationDescendedModule P K κ hc'' hu''))
      (presentationDescendedTensorChartHom P τ hc hu σ hc' hu' κ hc'' hu'' μ) :=
  (presentationQuasicoherentEquivalence_compatible_iff P _).2
    (presentationDescendedTensorChartHom_transitionCommutes P τ hc hu σ hc' hu' κ hc'' hu'' μ hμ)

omit hμ in
/-- The chart morphism, written out. -/
theorem presentationDescendedTensorChartHom_eq :
    presentationDescendedTensorChartHom P τ hc hu σ hc' hu' κ hc'' hu'' μ =
      (modulePullbackTensorIso B S hS (presentationAtlas P)
          (presentationDescendedModule P M τ hc hu).obj
          (presentationDescendedModule P N σ hc' hu').obj).hom ≫
        ((presentationDescendedModuleChartIso P M τ hc hu).hom ⊗ₘ
          (presentationDescendedModuleChartIso P N σ hc' hu').hom) ≫ μ ≫
        (presentationDescendedModuleChartIso P K κ hc'' hu'').inv :=
  rfl

/-- The groupoid morphism of the chart morphism. -/
def presentationDescendedTensorGroupoidHom :
    (presentationQuasicoherentEquivalence P).functor.obj
        (presentationDescendedTensorObj P τ hc hu σ hc' hu') ⟶
      (presentationQuasicoherentEquivalence P).functor.obj
        (presentationDescendedModule P K κ hc'' hu'') :=
  QuasicoherentModule.homMk (presentationDescendedTensorChartHom P τ hc hu σ hc' hu' κ hc'' hu'' μ)
    (presentationDescendedTensorChartHom_compatible P τ hc hu σ hc' hu' κ hc'' hu'' μ hμ)

/-- The morphism of quasi-coherent `𝒪_X`-modules `D(M) ⊗ D(N) ⟶ D(K)` corresponding to the
groupoid morphism of the chart morphism under the equivalence of Stacks 03M3. -/
def presentationDescendedTensorQuasicoherentHom :
    presentationDescendedTensorObj P τ hc hu σ hc' hu' ⟶
      presentationDescendedModule P K κ hc'' hu'' :=
  (presentationQuasicoherentEquivalence P).functor.preimage
    (presentationDescendedTensorGroupoidHom P τ hc hu σ hc' hu' κ hc'' hu'' μ hμ)

/-- The image of the descended morphism under the equivalence of Stacks 03M3 is the groupoid
morphism of the chart morphism. -/
theorem functor_map_presentationDescendedTensorQuasicoherentHom :
    (presentationQuasicoherentEquivalence P).functor.map
        (presentationDescendedTensorQuasicoherentHom P τ hc hu σ hc' hu' κ hc'' hu'' μ hμ) =
      (presentationDescendedTensorGroupoidHom P τ hc hu σ hc' hu' κ hc'' hu'' μ hμ) :=
  (presentationQuasicoherentEquivalence P).functor.map_preimage
      (presentationDescendedTensorGroupoidHom P τ hc hu σ hc' hu' κ hc'' hu'' μ hμ)

/-- **The descent of a multiplication**: the morphism `D(M) ⊗ D(N) ⟶ D(K)` of descended
`𝒪_X`-modules corresponding, under the equivalence of Stacks 03M3, to the morphism `μ` read on the
atlas through Stacks 03EL and the chart identifications. -/
def presentationDescendedTensorHom :
    (presentationDescendedModule P M τ hc hu).obj ⊗
        (presentationDescendedModule P N σ hc' hu').obj ⟶
      (presentationDescendedModule P K κ hc'' hu'').obj :=
  (presentationDescendedTensorQuasicoherentHom P τ hc hu σ hc' hu' κ hc'' hu'' μ hμ).hom

/-- The inverse image along the atlas of the descended multiplication is the chart morphism. -/
theorem modulePullback_map_presentationDescendedTensorHom :
    (modulePullback B S hS (presentationAtlas P)).map
        (presentationDescendedTensorHom P τ hc hu σ hc' hu' κ hc'' hu'' μ hμ) =
      presentationDescendedTensorChartHom P τ hc hu σ hc' hu' κ hc'' hu'' μ :=
  (presentationQuasicoherentEquivalence_functor_map_hom P _).symm.trans
    (congrArg QuasicoherentModule.Hom.hom
      (functor_map_presentationDescendedTensorQuasicoherentHom P τ hc hu σ hc' hu' κ hc'' hu''
        μ hμ))

/-- **The inverse image along the atlas of the descended multiplication is `μ`**, through
Stacks 03EL and the chart identifications. -/
theorem presentationDescendedTensorHom_spec :
    (modulePullback B S hS (presentationAtlas P)).map
        (presentationDescendedTensorHom P τ hc hu σ hc' hu' κ hc'' hu'' μ hμ) ≫
        (presentationDescendedModuleChartIso P K κ hc'' hu'').hom =
      (modulePullbackTensorIso B S hS (presentationAtlas P)
          (presentationDescendedModule P M τ hc hu).obj
          (presentationDescendedModule P N σ hc' hu').obj).hom ≫
        ((presentationDescendedModuleChartIso P M τ hc hu).hom ⊗ₘ
          (presentationDescendedModuleChartIso P N σ hc' hu').hom) ≫ μ :=
  (comp_hom_eq_iff_eq_comp_inv _ _ _ _ _).2
    ((modulePullback_map_presentationDescendedTensorHom P τ hc hu σ hc' hu' κ hc'' hu'' μ hμ).trans
      (presentationDescendedTensorChartHom_eq P τ hc hu σ hc' hu' κ hc'' hu'' μ))

/-- **The descended multiplication is unique**: a morphism `D(M) ⊗ D(N) ⟶ D(K)` whose inverse image
along the atlas is `μ`, through Stacks 03EL and the chart identifications, is the descended
multiplication. -/
theorem presentationDescendedTensorHom_unique
    (ψ : (presentationDescendedModule P M τ hc hu).obj ⊗
        (presentationDescendedModule P N σ hc' hu').obj ⟶
      (presentationDescendedModule P K κ hc'' hu'').obj)
    (hψ : (modulePullback B S hS (presentationAtlas P)).map ψ ≫
        (presentationDescendedModuleChartIso P K κ hc'' hu'').hom =
      (modulePullbackTensorIso B S hS (presentationAtlas P)
          (presentationDescendedModule P M τ hc hu).obj
          (presentationDescendedModule P N σ hc' hu').obj).hom ≫
        ((presentationDescendedModuleChartIso P M τ hc hu).hom ⊗ₘ
          (presentationDescendedModuleChartIso P N σ hc' hu').hom) ≫ μ) :
    ψ = presentationDescendedTensorHom P τ hc hu σ hc' hu' κ hc'' hu'' μ hμ := by
  have h1 : (modulePullback B S hS (presentationAtlas P)).map ψ =
      presentationDescendedTensorChartHom P τ hc hu σ hc' hu' κ hc'' hu'' μ :=
    ((comp_hom_eq_iff_eq_comp_inv _ _ _ _ _).1 hψ).trans
      (presentationDescendedTensorChartHom_eq P τ hc hu σ hc' hu' κ hc'' hu'' μ).symm
  have h2 : (presentationQuasicoherentEquivalence P).functor.map
      (ObjectProperty.homMk ψ : presentationDescendedTensorObj P τ hc hu σ hc' hu' ⟶
        presentationDescendedModule P K κ hc'' hu'') =
      (presentationQuasicoherentEquivalence P).functor.map
        (presentationDescendedTensorQuasicoherentHom P τ hc hu σ hc' hu' κ hc'' hu'' μ hμ) := by
    refine QuasicoherentModule.Hom.ext ?_
    refine (presentationQuasicoherentEquivalence_functor_map_hom P _).trans ?_
    refine Eq.trans ?_ (presentationQuasicoherentEquivalence_functor_map_hom P _).symm
    exact h1.trans
      (modulePullback_map_presentationDescendedTensorHom P τ hc hu σ hc' hu' κ hc'' hu'' μ hμ).symm
  exact congrArg (fun k => k.hom)
    ((presentationQuasicoherentEquivalence P).functor.map_injective h2)

include hμ in
/-- **Descent along a presentation is monoidal.**  Let `X = U/R` be a presentation of an algebraic
space and `(M, τ)`, `(N, σ)`, `(K, κ)` quasi-coherent modules on the presenting scheme with scheme
transitions satisfying the cocycle and unit conditions.  A morphism
`μ : M^a ⊗ N^a ⟶ K^a` on the atlas which carries the tensor product of the transitions
`τ^a ⊗ σ^a` (read through Stacks 03EL along the target and the source) to `κ^a` descends to a
unique morphism `D(M) ⊗ D(N) ⟶ D(K)` of the descended `𝒪_X`-modules whose inverse image along the
atlas is `μ`, through Stacks 03EL and the chart identifications. -/
theorem existsUnique_presentationDescendedTensorHom :
    ∃! ψ : (presentationDescendedModule P M τ hc hu).obj ⊗
        (presentationDescendedModule P N σ hc' hu').obj ⟶
        (presentationDescendedModule P K κ hc'' hu'').obj,
      (modulePullback B S hS (presentationAtlas P)).map ψ ≫
          (presentationDescendedModuleChartIso P K κ hc'' hu'').hom =
        (modulePullbackTensorIso B S hS (presentationAtlas P)
            (presentationDescendedModule P M τ hc hu).obj
            (presentationDescendedModule P N σ hc' hu').obj).hom ≫
          ((presentationDescendedModuleChartIso P M τ hc hu).hom ⊗ₘ
            (presentationDescendedModuleChartIso P N σ hc' hu').hom) ≫ μ :=
  ⟨presentationDescendedTensorHom P τ hc hu σ hc' hu' κ hc'' hu'' μ hμ,
    presentationDescendedTensorHom_spec P τ hc hu σ hc' hu' κ hc'' hu'' μ hμ,
    fun ψ hψ => presentationDescendedTensorHom_unique P τ hc hu σ hc' hu' κ hc'' hu'' μ hμ ψ hψ⟩

end Descent

end AlgebraicGeometry.Space

end
