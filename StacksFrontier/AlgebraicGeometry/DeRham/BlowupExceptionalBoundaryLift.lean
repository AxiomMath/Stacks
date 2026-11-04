module

public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleDominating
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalProjectiveBundle
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupDeRhamSplittingReduction
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.BoundaryCanonicalLift
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.SmoothDivisor
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniGenericMember

/-!
# The blowup half of the proof of [Stacks, Tag 0FUW]

Fix a scheme `S`, a smooth morphism `f : X ⟶ S` and a closed immersion `i : Z ⟶ X` with `Z`
smooth over `S`. Let `b : X' ⟶ X` be the blowing up of `X` along `Z` and `j : E ⟶ X'` its
exceptional divisor, read over `S` through the centre. Let `θ : Ω^•_{E/S}[-2] ⟶ Ω^•_{E/S}` be the
untwisted map of [Stacks, Tag 0FU7] for `c₁^{dR}(𝒪_{X'}(-E)|_E)`.

The proof of [Stacks, Tag 0FUW] uses the boundary map of [Stacks, Tag 0FUQ] for `E ⊂ X'` as a lift
`δ : Rj_*(Ω^•_{E/S}[-2]) ⟶ Ω^•_{X'/S}` of `Rj_*θ` through the canonical map
`Ω^•_{X'/S} ⟶ Rj_*Ω^•_{E/S}`. This file produces it, in the form
`Stacks.DeRham.BlowupTriangle.exists_retraction_toBlowUp_of_section` consumes.

## Main definitions

* `Stacks.DeRham.BlowupTriangle.untwistedChern`: the untwisted map of Tag 0FU7 for the first
  Chern class of the invertible module of a line-bundle situation.
* `Stacks.DeRham.BlowupTriangle.exceptionalSituation`: `𝒪_{X'}(-E)|_E` on `E`, over `S` through
  the centre.

## Main results

* `Stacks.DeRham.BlowupTriangle.exists_comp_inclusionUnit_eq_map_untwistedChern`: the lift.

## Implementation notes

The exceptional divisor is a divisor of `X'` over `S` through `b`, which is how
[Stacks, Tag 0FUQ] sees it, and is read over `S` through the centre in the triangle of
[Stacks, Tag 0FUV]; the two structure morphisms are equal, and the lift is transported along that
equality. The derived categories are the standard models, which is where the maps of Tag 0FU7 live.

## References

* [Stacks Project, Tag 0FUW](https://stacks.math.columbia.edu/tag/0FUW)
* [Stacks Project, Tag 0FUQ](https://stacks.math.columbia.edu/tag/0FUQ)
* [Stacks Project, Tag 0FU7](https://stacks.math.columbia.edu/tag/0FU7)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.DeRhamDirectImage
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)
open scoped Stacks.StandardDerivedModel

universe u

attribute [-instance] CategoryTheory.catToReflQuiver

-- The statements mix the `Modules` and `ModuleSheaves` spellings of the categories of modules,
-- which agree only at default transparency; these make them agree for unification.
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose SheafedSpace.sheaf
  AlgebraicGeometry.RingedSpace.inverseImage

namespace Stacks.DeRham.BlowupTriangle

/-- **The untwisted map of [Stacks, Tag 0FU7] for a first Chern class**: for a line-bundle
situation `(f : X ⟶ S, ℒ)`, the map `θ = ξ'[-2] : Ω^•_{X/S}[-2] ⟶ Ω^•_{X/S}`, where
`ξ' : Ω^•_{X/S} ⟶ Ω^•_{X/S}[2]` is the morphism of Tag 0FU7 attached to `c₁^{dR}(ℒ)`. -/
abbrev untwistedChern (D : Stacks.LineBundle.Situation.{u}) :
    (DerivedCategory.Q.obj (deRhamCochainComplex D.f))⟦(-2 : ℤ)⟧ ⟶
      DerivedCategory.Q.obj (deRhamCochainComplex D.f) :=
  (AlgebraicGeometry.SheafOfModules.deRhamClassMorphism (Scheme.Hom.deRhamAlgebras D.f)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f)) 2
      (AlgebraicGeometry.SheafOfModules.deRhamCohomologyFirstChernClass (X := D.X.toRingedSpace)
        (Scheme.Hom.deRhamAlgebras D.f)
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f)) D.L
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ D.L D.invertible)))⟦(-2 : ℤ)⟧' ≫
    (shiftFunctorCompIsoId _ (2 : ℤ) (-2) (by norm_num)).hom.app _

/-- A lift through the canonical map along `g` is a lift through the canonical map along any
morphism `g'` equal to `g`, composed with the identification of the two direct images. -/
theorem exists_lift_of_eq_of_heq {A B : RingedSpace.{u, u}}
    [HasDerivedCategory (RingedSpaceModuleAdjunction.ModuleSheaves A)]
    [HasDerivedCategory (RingedSpaceModuleAdjunction.ModuleSheaves B)] {g' g : A ⟶ B}
    (hg : g' = g) (K : CochainComplex (RingedSpaceModuleAdjunction.ModuleSheaves A) ℤ)
    {L : CochainComplex (RingedSpaceModuleAdjunction.ModuleSheaves B) ℤ}
    (κ : L ⟶ ((RingedSpaceModuleAdjunction.modulePushforward g).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K)
    (e : ((RingedSpaceModuleAdjunction.modulePushforward g).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K ⟶
      ((RingedSpaceModuleAdjunction.modulePushforward g').mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K)
    (he : HEq e (𝟙 (((RingedSpaceModuleAdjunction.modulePushforward g).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K)))
    {W : DerivedCategory (RingedSpaceModuleAdjunction.ModuleSheaves A)}
    (θ : W ⟶ DerivedCategory.Q.obj K)
    (H : ∃ δ : (derivedPushforward g).obj W ⟶ DerivedCategory.Q.obj L,
      δ ≫ DerivedCategory.Q.map κ ≫ unit g K = (derivedPushforward g).map θ) :
    ∃ δ : (derivedPushforward g').obj W ⟶ DerivedCategory.Q.obj L,
      δ ≫ DerivedCategory.Q.map (κ ≫ e) ≫ unit g' K = (derivedPushforward g').map θ := by
  subst hg
  obtain rfl := eq_of_heq he
  simpa using H

/-- **Transport of the lift along an equality of structure morphisms.** A lift for a divisor
`j : E ⟶ X'` read over `S` through `j ≫ f'` gives one for `E` read over `S` through any equal
morphism `e`. -/
theorem exists_lift_of_eq {E X' S : Scheme.{u}} (j : E ⟶ X') (f' : X' ⟶ S) (L : E.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible E.sheaf.obj E.ringCatSheaf.property L]
    {e : E ⟶ S} (h : j ≫ f' = e)
    (H : ∃ δ₁ : (derivedPushforward (Stacks.DeRhamSmooth.relativeBase j f')).obj
        ((DerivedCategory.Q.obj (deRhamCochainComplex (j ≫ f')))⟦(-2 : ℤ)⟧) ⟶
        DerivedCategory.Q.obj (deRhamCochainComplex f'),
      δ₁ ≫ DerivedCategory.Q.map (chain j f') ≫
          unit (Stacks.DeRhamSmooth.relativeBase j f') (deRhamCochainComplex (j ≫ f')) =
        (derivedPushforward (Stacks.DeRhamSmooth.relativeBase j f')).map
          (untwistedChern { X := E, S := S, f := j ≫ f', L := L })) :
    ∃ δ : (derivedPushforward (eqToHom (congrArg inverseImageBase h.symm) ≫
        Stacks.DeRhamSmooth.relativeBase j f')).obj
        ((DerivedCategory.Q.obj (deRhamCochainComplex e))⟦(-2 : ℤ)⟧) ⟶
        DerivedCategory.Q.obj (deRhamCochainComplex f'),
      δ ≫ DerivedCategory.Q.map (chain j f' ≫ (pushforwardTransportIso h _).inv) ≫
          unit (eqToHom (congrArg inverseImageBase h.symm) ≫
            Stacks.DeRhamSmooth.relativeBase j f') (deRhamCochainComplex e) =
        (derivedPushforward (eqToHom (congrArg inverseImageBase h.symm) ≫
          Stacks.DeRhamSmooth.relativeBase j f')).map
          (untwistedChern { X := E, S := S, f := e, L := L }) := by
  subst h
  exact exists_lift_of_eq_of_heq (by simp only [eqToHom_refl, Category.id_comp])
    (deRhamCochainComplex (j ≫ f')) (chain j f') (pushforwardTransportIso rfl _).inv
    (by simp only [pushforwardTransportIso, eqToIso.inv]; exact eqToHom_heq_id_dom _ _ _)
    (untwistedChern { X := E, S := S, f := j ≫ f', L := L }) H

attribute [local instance] Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal_reesData

variable {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i]

/-- **`𝒪_{X'}(-E)|_E` on the exceptional divisor**, as a line-bundle situation over `S` through
the centre. -/
abbrev exceptionalSituation : Stacks.LineBundle.Situation.{u} where
  X := Stacks.Blowup.exceptionalDivisor i.ker
  S := S
  f := exceptionalStructure f i
  L := (Stacks.LineBundle.divisorSituation (blowupMap i ≫ f)
    (Stacks.Blowup.exceptionalIdeal i.ker)).L
  invertible := (Stacks.LineBundle.divisorSituation (blowupMap i ≫ f)
    (Stacks.Blowup.exceptionalIdeal i.ker)).invertible

/-- **The blowup and its exceptional divisor are smooth over `S`** ([Stacks, Tag 0FUT]), for the
presentation `Stacks.Blowup.blowUp` of the blowup, read off the one for
`AlgebraicGeometry.blowUp` along the comparison `Stacks.Blowup.blowUpIso`. -/
theorem smooth_blowupMap_comp_and_exceptional [Smooth f] [Smooth (i ≫ f)] :
    Smooth (blowupMap i ≫ f) ∧ Smooth (exceptionalInclusion i ≫ blowupMap i ≫ f) := by
  obtain ⟨h₁, h₂, -⟩ :=
    AlgebraicGeometry.smooth_exceptionalDivisor_isoProjectiveBundle_twistOne_of_isClosedImmersion
      f i
  have hb : blowupMap i = (Stacks.Blowup.blowUpIso i.ker).hom ≫
      AlgebraicGeometry.blowUpToBase i.ker := (Stacks.Blowup.blowUpIso_hom_comp i.ker).symm
  have key : ∀ K : (Stacks.Blowup.blowUp i.ker).IdealSheafData,
      K = (AlgebraicGeometry.exceptionalIdeal i.ker).comap (Stacks.Blowup.blowUpIso i.ker).hom →
      Smooth (K.subschemeι ≫ (Stacks.Blowup.blowUpIso i.ker).hom ≫
        AlgebraicGeometry.blowUpToBase i.ker ≫ f) := by
    rintro K rfl
    have hp := Stacks.Bertini.isPullback_subschemeι_comap
      (AlgebraicGeometry.exceptionalIdeal i.ker) (Stacks.Blowup.blowUpIso i.ker).hom
    have := hp.isIso_snd_of_isIso
    rw [← Category.assoc, hp.w, Category.assoc]
    infer_instance
  have hK : Stacks.Blowup.exceptionalIdeal i.ker =
      (AlgebraicGeometry.exceptionalIdeal i.ker).comap (Stacks.Blowup.blowUpIso i.ker).hom := by
    show i.ker.comap (blowupMap i) = _
    rw [hb, Scheme.IdealSheafData.comap_comp]
  refine ⟨?_, ?_⟩
  · rw [hb, Category.assoc]
    infer_instance
  · have := key _ hK
    rwa [← Category.assoc ((Stacks.Blowup.blowUpIso i.ker).hom), ← hb] at this

/-- The de Rham complex of log poles is defined for the exceptional divisor of the blowup of a
scheme smooth over `S` along a closed subscheme smooth over `S`. -/
theorem hasLogPolesDeRhamComplex_exceptional [Smooth f] [Smooth (i ≫ f)] :
    (blowupMap i ≫ f).HasLogPolesDeRhamComplex (Stacks.Blowup.exceptionalIdeal i.ker) := by
  obtain ⟨h₁, h₂⟩ := smooth_blowupMap_comp_and_exceptional f i
  have := @Scheme.Hom.hasLogPolesDeRhamComplex_of_smooth _ _ _ (blowupMap i ≫ f) (𝟙 S)
    (Stacks.Blowup.exceptionalIdeal i.ker) inferInstance h₁ h₂
  simpa using this

/-- **The lift of `Rj_*θ` through the canonical map `Ω^•_{X'/S} ⟶ Rj_*Ω^•_{E/S}`.** For `f`
smooth and `Z` smooth over `S`, there is `δ : Rj_*(Ω^•_{E/S}[-2]) ⟶ Ω^•_{X'/S}` whose composite
with the canonical map is `Rj_*θ`, for `θ` the untwisted map of [Stacks, Tag 0FU7] for
`c₁^{dR}(𝒪_{X'}(-E)|_E)`: the boundary map of [Stacks, Tag 0FUQ]. -/
theorem exists_comp_inclusionUnit_eq_map_untwistedChern [Smooth f] [Smooth (i ≫ f)] :
    ∃ δ : (derivedPushforward (coefficientInclusion f i)).obj
        ((deRham (exceptionalStructure f i))⟦(-2 : ℤ)⟧) ⟶ deRham (blowupMap i ≫ f),
      δ ≫ inclusionUnit f i =
        (derivedPushforward (coefficientInclusion f i)).map
          (untwistedChern (exceptionalSituation f i)) :=
  exists_lift_of_eq (exceptionalInclusion i) (blowupMap i ≫ f) _
    (hL := (Stacks.LineBundle.divisorSituation (blowupMap i ≫ f)
      (Stacks.Blowup.exceptionalIdeal i.ker)).invertible) (exceptionalInclusion_comp f i)
    (Stacks.LineBundle.exists_comp_chain_unit_eq_map_divisorChernUntwisted (blowupMap i ≫ f)
      (Stacks.Blowup.exceptionalIdeal i.ker) (hasLogPolesDeRhamComplex_exceptional f i))

/-- **[Stacks, Tag 0FUW] from its centre half.** For `f` smooth and `Z` smooth over `S`: if the map
`c ⊕ Rp_*θ : Ω^•_{Z/S} ⊕ Rp_*(Ω^•_{E/S}[-2]) ⟶ Rp_*Ω^•_{E/S}` has a section restricting to the
inclusion of `Ω^•_{Z/S}` along the canonical map `c`, for `θ` the untwisted map of
[Stacks, Tag 0FU7] for `c₁^{dR}(𝒪_{X'}(-E)|_E)` (in the source, the decomposition of Remark 0FUN),
then the canonical map `Ω^•_{X/S} ⟶ Rb_*Ω^•_{X'/S}` has a retraction. -/
theorem exists_retraction_toBlowUp_of_centre [Smooth f] [Smooth (i ≫ f)]
    (hZ : ∃ (τ : (derivedPushforward (coefficientProjection f i)).obj
        (deRham (exceptionalStructure f i)) ⟶ deRham (i ≫ f))
      (ν : (derivedPushforward (coefficientProjection f i)).obj
        (deRham (exceptionalStructure f i)) ⟶
        (derivedPushforward (coefficientProjection f i)).obj
          ((deRham (exceptionalStructure f i))⟦(-2 : ℤ)⟧)),
      centreUnit f i ≫ τ = 𝟙 _ ∧ centreUnit f i ≫ ν = 0 ∧
        τ ≫ centreUnit f i + ν ≫ (derivedPushforward (coefficientProjection f i)).map
          (untwistedChern (exceptionalSituation f i)) = 𝟙 _) :
    ∃ r : blowUpDeRham f i ⟶ deRham f, toBlowUp f i ≫ r = 𝟙 _ := by
  obtain ⟨τ, ν, h₁, h₂, h₃⟩ := hZ
  obtain ⟨δ, hδ⟩ := exists_comp_inclusionUnit_eq_map_untwistedChern f i
  exact exists_retraction_toBlowUp_of_section f i _ τ ν h₁ h₂ h₃ δ hδ

end Stacks.DeRham.BlowupTriangle

end
