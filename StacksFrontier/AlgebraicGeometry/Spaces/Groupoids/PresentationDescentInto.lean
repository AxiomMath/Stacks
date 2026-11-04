module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PresentationDescentMonoidal

/-!
# Descent along a presentation of a morphism into a descended module

Let `X = U/R` be a presentation of an algebraic space, and let `(M, τ)` be a quasi-coherent module
on the presenting scheme `U` with a scheme transition satisfying the cocycle and unit conditions,
so that it descends to a quasi-coherent `𝒪_X`-module `D(M)`
(`AlgebraicGeometry.Space.presentationDescendedModule`, Stacks 03M3).  This file descends a
morphism *into* `D(M)` from an arbitrary quasi-coherent `𝒪_X`-module `Y`, which need not itself be
given by descent data on `U`: a morphism `χ : φ^*Y ⟶ M^a` on the atlas `φ : U ⟶ X` which carries
the canonical transition morphism of `φ^*Y` to the transition `τ^a` descends to a unique morphism
`Y ⟶ D(M)` whose inverse image along the atlas is `χ`, through the chart identification of
`D(M)`.  This is the general form of
`AlgebraicGeometry.Space.existsUnique_presentationDescendedHom` (where `Y = D(N)`) and of
`AlgebraicGeometry.Space.existsUnique_presentationDescendedUnitHom` (where `Y = 𝒪_X`); it is the
form in which the homomorphism `ψ : π^*𝒜 ⟶ ⨁ 𝒪_P(n)` of Stacks 084D is descended, its source
`π^*𝒜` being an inverse image rather than a descended module.

## Main definitions

* `AlgebraicGeometry.Space.presentationDescendedIntoChartHom`: the morphism on the atlas to be
  descended.
* `AlgebraicGeometry.Space.presentationDescendedIntoHom`: **the descended morphism**.

## Main results

* `AlgebraicGeometry.Space.existsUnique_presentationDescendedIntoHom`, with
  `AlgebraicGeometry.Space.presentationDescendedIntoHom_spec` and
  `AlgebraicGeometry.Space.presentationDescendedIntoHom_unique`: **descent of a morphism into a
  descended module along a presentation**.

## References

* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- The abstract shape of the compatibility in
`AlgebraicGeometry.Space.existsUnique_presentationDescendedIntoHom`, at variables. -/
private theorem descend_into_compatible_of_readings {CU CV : Type*} [Category CU] [Category CV]
    (Pt Ps : CU ⥤ CV) {Y A YK : CU} (χ : Y ⟶ A) (cK : YK ≅ A)
    (δY : Pt.obj Y ⟶ Ps.obj Y) (δK : Pt.obj YK ⟶ Ps.obj YK) (αK : Pt.obj A ⟶ Ps.obj A)
    (hK : δK ≫ Ps.map cK.hom = Pt.map cK.hom ≫ αK)
    (hχ : δY ≫ Ps.map χ = Pt.map χ ≫ αK) :
    δY ≫ Ps.map (χ ≫ cK.inv) = Pt.map (χ ≫ cK.inv) ≫ δK := by
  have hK' : αK ≫ Ps.map cK.inv = Pt.map cK.inv ≫ δK := by
    rw [← cancel_epi (Pt.map cK.hom), ← reassoc_of% hK, ← Pt.map_comp_assoc, Iso.hom_inv_id,
      Pt.map_id, Category.id_comp, ← Ps.map_comp, Iso.hom_inv_id, Ps.map_id, Category.comp_id]
  rw [Ps.map_comp, Pt.map_comp, reassoc_of% hχ, hK', Category.assoc]

section Descent

attribute [local irreducible] CategoryTheory.yoneda

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (P : Presentation B S hS X.obj X.property)
  {M : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj P.U).ringCatSheaf).FullSubcategory}
  (τ : quasicoherentPullbackObj B S hS P.target M ⟶ quasicoherentPullbackObj B S hS P.source M)
  (hc : PresentationSchemeCocycle P M τ) (hu : PresentationSchemeUnit P M τ)
  (Y : QuasicoherentSheaves.{u, u} B S hS X.obj X.property)
  (χ : (modulePullback B S hS (presentationAtlas P)).obj Y.obj ⟶
    ((representedQuasicoherentSchemeEquivalence B S hS P.U).functor.obj M).obj)
  (hχ : TransitionCommutes B S hS (U := (presentationGroupoid P).objects)
    (V := (presentationGroupoid P).arrows) (a := (presentationGroupoid P).target)
    (b := (presentationGroupoid P).source)
    (spaceBaseDescent B S hS (presentationGroupoid P) (presentationAtlas P)
      (presentationAtlas_comm P) Y.obj)
    (presentationSchemeTransition P M τ) χ)

/-- The morphism on the atlas to be descended: `χ` followed by the chart identification of
`D(M)`. -/
def presentationDescendedIntoChartHom :
    (modulePullback B S hS (presentationAtlas P)).obj Y.obj ⟶
      (modulePullback B S hS (presentationAtlas P)).obj
        (presentationDescendedModule P M τ hc hu).obj :=
  χ ≫ (presentationDescendedModuleChartIso P M τ hc hu).inv

/-- The chart morphism, written out. -/
theorem presentationDescendedIntoChartHom_eq :
    presentationDescendedIntoChartHom P τ hc hu Y χ =
      χ ≫ (presentationDescendedModuleChartIso P M τ hc hu).inv :=
  rfl

/-- A morphism into `D(M)` has inverse image `χ` through the chart identification iff its inverse
image along the atlas is the chart morphism. -/
private theorem modulePullback_map_comp_chartIso_hom_eq_iff
    (ψ : Y.obj ⟶ (presentationDescendedModule P M τ hc hu).obj) :
    (modulePullback B S hS (presentationAtlas P)).map ψ ≫
        (presentationDescendedModuleChartIso P M τ hc hu).hom = χ ↔
      (modulePullback B S hS (presentationAtlas P)).map ψ =
        presentationDescendedIntoChartHom P τ hc hu Y χ :=
  (Iso.eq_comp_inv _).symm

include hχ in
/-- The chart morphism carries the canonical transition morphism of the inverse image of `Y` to
that of the inverse image of `D(M)`. -/
theorem presentationDescendedIntoChartHom_transitionCommutes :
    TransitionCommutes B S hS (U := (presentationGroupoid P).objects)
      (V := (presentationGroupoid P).arrows) (a := (presentationGroupoid P).target)
      (b := (presentationGroupoid P).source)
      (spaceBaseDescent B S hS (presentationGroupoid P) (presentationAtlas P)
        (presentationAtlas_comm P) Y.obj)
      (spaceBaseDescent B S hS (presentationGroupoid P) (presentationAtlas P)
        (presentationAtlas_comm P) (presentationDescendedModule P M τ hc hu).obj)
      (presentationDescendedIntoChartHom P τ hc hu Y χ) :=
  descend_into_compatible_of_readings (modulePullback B S hS (presentationGroupoid P).target)
    (modulePullback B S hS (presentationGroupoid P).source) χ
    (presentationDescendedModuleChartIso P M τ hc hu) _ _ (presentationSchemeTransition P M τ)
    (presentationDescendedModuleChartIso_comm_spaceBaseDescent P τ hc hu) hχ

include hχ in
/-- The chart morphism is a morphism of quasi-coherent modules on the groupoid of the
presentation. -/
theorem presentationDescendedIntoChartHom_compatible :
    QuasicoherentModule.Compatible
      (M := (presentationQuasicoherentEquivalence P).functor.obj Y)
      (N := (presentationQuasicoherentEquivalence P).functor.obj
        (presentationDescendedModule P M τ hc hu))
      (presentationDescendedIntoChartHom P τ hc hu Y χ) :=
  (presentationQuasicoherentEquivalence_compatible_iff P _).2
    (presentationDescendedIntoChartHom_transitionCommutes P τ hc hu Y χ hχ)

/-- The groupoid morphism of the chart morphism. -/
def presentationDescendedIntoGroupoidHom :
    (presentationQuasicoherentEquivalence P).functor.obj Y ⟶
      (presentationQuasicoherentEquivalence P).functor.obj
        (presentationDescendedModule P M τ hc hu) :=
  QuasicoherentModule.homMk (presentationDescendedIntoChartHom P τ hc hu Y χ)
    (presentationDescendedIntoChartHom_compatible P τ hc hu Y χ hχ)

/-- The morphism of quasi-coherent `𝒪_X`-modules `Y ⟶ D(M)` corresponding to the groupoid
morphism of the chart morphism under the equivalence of Stacks 03M3. -/
def presentationDescendedIntoQuasicoherentHom : Y ⟶ presentationDescendedModule P M τ hc hu :=
  (presentationQuasicoherentEquivalence P).functor.preimage
    (presentationDescendedIntoGroupoidHom P τ hc hu Y χ hχ)

/-- The image of the descended morphism under the equivalence of Stacks 03M3 is the groupoid
morphism of the chart morphism. -/
theorem functor_map_presentationDescendedIntoQuasicoherentHom :
    (presentationQuasicoherentEquivalence P).functor.map
        (presentationDescendedIntoQuasicoherentHom P τ hc hu Y χ hχ) =
      presentationDescendedIntoGroupoidHom P τ hc hu Y χ hχ :=
  (presentationQuasicoherentEquivalence P).functor.map_preimage
    (presentationDescendedIntoGroupoidHom P τ hc hu Y χ hχ)

/-- **The descent of a morphism into a descended module**: the morphism `Y ⟶ D(M)` corresponding,
under the equivalence of Stacks 03M3, to the morphism `χ` read through the chart identification
of `D(M)`. -/
def presentationDescendedIntoHom : Y.obj ⟶ (presentationDescendedModule P M τ hc hu).obj :=
  (presentationDescendedIntoQuasicoherentHom P τ hc hu Y χ hχ).hom

/-- The inverse image along the atlas of the descended morphism is the chart morphism. -/
theorem modulePullback_map_presentationDescendedIntoHom :
    (modulePullback B S hS (presentationAtlas P)).map
        (presentationDescendedIntoHom P τ hc hu Y χ hχ) =
      presentationDescendedIntoChartHom P τ hc hu Y χ :=
  (presentationQuasicoherentEquivalence_functor_map_hom P _).symm.trans
    (congrArg QuasicoherentModule.Hom.hom
      (functor_map_presentationDescendedIntoQuasicoherentHom P τ hc hu Y χ hχ))

/-- **The inverse image along the atlas of the descended morphism is `χ`**, through the chart
identification. -/
theorem presentationDescendedIntoHom_spec :
    (modulePullback B S hS (presentationAtlas P)).map
        (presentationDescendedIntoHom P τ hc hu Y χ hχ) ≫
        (presentationDescendedModuleChartIso P M τ hc hu).hom = χ :=
  (modulePullback_map_comp_chartIso_hom_eq_iff P τ hc hu Y χ _).2
    (modulePullback_map_presentationDescendedIntoHom P τ hc hu Y χ hχ)

/-- **The descended morphism is unique**: a morphism `Y ⟶ D(M)` whose inverse image along the atlas
is `χ`, through the chart identification, is the descended morphism. -/
theorem presentationDescendedIntoHom_unique
    (ψ : Y.obj ⟶ (presentationDescendedModule P M τ hc hu).obj)
    (hψ : (modulePullback B S hS (presentationAtlas P)).map ψ ≫
        (presentationDescendedModuleChartIso P M τ hc hu).hom = χ) :
    ψ = presentationDescendedIntoHom P τ hc hu Y χ hχ := by
  have h1 : (modulePullback B S hS (presentationAtlas P)).map ψ =
      presentationDescendedIntoChartHom P τ hc hu Y χ :=
    (modulePullback_map_comp_chartIso_hom_eq_iff P τ hc hu Y χ ψ).1 hψ
  have h2 : (presentationQuasicoherentEquivalence P).functor.map
      (ObjectProperty.homMk ψ : Y ⟶ presentationDescendedModule P M τ hc hu) =
      (presentationQuasicoherentEquivalence P).functor.map
        (presentationDescendedIntoQuasicoherentHom P τ hc hu Y χ hχ) := by
    refine QuasicoherentModule.Hom.ext ?_
    refine (presentationQuasicoherentEquivalence_functor_map_hom P _).trans ?_
    refine Eq.trans ?_ (presentationQuasicoherentEquivalence_functor_map_hom P _).symm
    exact h1.trans (modulePullback_map_presentationDescendedIntoHom P τ hc hu Y χ hχ).symm
  exact congrArg (fun k => k.hom)
    ((presentationQuasicoherentEquivalence P).functor.map_injective h2)

include hχ in
/-- **Descent of a morphism into a descended module along a presentation.**  Let `X = U/R` be a
presentation of an algebraic space with atlas `φ : U ⟶ X`, `(M, τ)` a quasi-coherent module on the
presenting scheme with a scheme transition satisfying the cocycle and unit conditions, and `Y` a
quasi-coherent `𝒪_X`-module.  A morphism `χ : φ^*Y ⟶ M^a` which carries the canonical transition
morphism of `φ^*Y` to the transition `τ^a` descends to a unique morphism `Y ⟶ D(M)` of
`𝒪_X`-modules whose inverse image along the atlas is `χ`, through the chart identification. -/
theorem existsUnique_presentationDescendedIntoHom :
    ∃! ψ : Y.obj ⟶ (presentationDescendedModule P M τ hc hu).obj,
      (modulePullback B S hS (presentationAtlas P)).map ψ ≫
          (presentationDescendedModuleChartIso P M τ hc hu).hom = χ :=
  ⟨presentationDescendedIntoHom P τ hc hu Y χ hχ,
    presentationDescendedIntoHom_spec P τ hc hu Y χ hχ,
    fun ψ hψ => presentationDescendedIntoHom_unique P τ hc hu Y χ hχ ψ hψ⟩

end Descent

end AlgebraicGeometry.Space

end
