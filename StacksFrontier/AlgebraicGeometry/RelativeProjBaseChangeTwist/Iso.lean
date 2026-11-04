module

public import StacksFrontier.AlgebraicGeometry.RelativeProjBaseChangeTwist.Presentation
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjModuleBaseChangeIso

/-!
# The base change of a relative homogeneous spectrum, on the `SheafGradedAlgebra` substrate

Let `S` be a scheme, `A` a quasi-coherent graded `𝒪_S`-algebra (Situation 01NN, in the form
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`) and `g : S' ⟶ S` a morphism of
schemes. This file constructs the base-change morphism
`Proj_{S'}(g^*A) ⟶ Proj_S(A)` of the relative homogeneous spectra of
`Stacks.AlgebraicGeometry.RelativeProj.relativeProj`, proves that it exhibits `Proj_{S'}(g^*A)` as
`S' ×_S Proj_S(A)`, and computes it on the charts.

The square is the cartesian square
`Stacks.RelativeProj.Situation.isPullback_relativeProjBaseChange` of the
`Stacks.RelativeProj.Situation` substrate, transported along the two comparison isomorphisms
`Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.presentationIso` of the two glueings; the
situation of `g^*A` is the pullback situation on the nose
(`Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.situation_pullback`).

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom`: the base-change morphism.
* `Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeIso`: **the canonical
  isomorphism `r : Proj_{S'}(g^*A) ≅ S' ×_S Proj_S(A)`.**
* `Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.sectionBaseChange`: the graded ring map
  `Γ(U, A) ⟶ Γ(U', g^*A)` for affine opens `U' ⊆ g⁻¹U`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.isPullback_baseChangeHom`: the square is
  cartesian.
* `Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.chart_baseChangeHom`: on the chart over
  `U'` the base-change morphism is `Proj.map` of `Γ(U, A) ⟶ Γ(U', g^*A)` followed by the chart
  over `U`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.ProjPresentation

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist

variable {S S' : Scheme.{u}} (A : SheafGradedAlgebra S) (g : S' ⟶ S)

/-- The identification of the graded algebra of the situation of `g^*A` with the pullback of the
graded algebra of the situation of `A`: the identity. -/
def pullbackHom :
    SheafOfModules.GradedAlgebra.UnitalHom
      (Stacks.Conormal.gradedPullback g (situation A).algebra) (situation (A.pullback g)).algebra :=
  SheafOfModules.GradedAlgebra.UnitalHom.id _

/-- Each graded component of `pullbackHom A g` is an isomorphism. -/
theorem isIso_pullbackHom_app (m : ℕ) : IsIso ((pullbackHom A g).app (m : ℤ)) :=
  inferInstanceAs (IsIso (𝟙 _))

/-- The base-change morphism of the `Situation` substrate. -/
abbrev situationBaseChange :
    Stacks.RelativeProj.Situation.relativeProj (situation (A.pullback g)) ⟶
      Stacks.RelativeProj.Situation.relativeProj (situation A) :=
  Stacks.RelativeProj.Situation.relativeProjBaseChange g (pullbackHom A g)
    (isIso_pullbackHom_app A g)

/-- **The base-change morphism `Proj_{S'}(g^*A) ⟶ Proj_S(A)`.** -/
def baseChangeHom :
    (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (A.pullback g)).scheme ⟶
      (Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).scheme :=
  (presentationIso (A.pullback g)).hom ≫ situationBaseChange A g ≫ (presentationIso A).inv

/-- **The base-change square is cartesian**: `Proj_{S'}(g^*A)` is `S' ×_S Proj_S(A)`. -/
theorem isPullback_baseChangeHom :
    IsPullback (baseChangeHom A g)
      (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (A.pullback g)).toBase
      (Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).toBase g := by
  refine (Stacks.RelativeProj.Situation.isPullback_relativeProjBaseChange g (pullbackHom A g)
      (isIso_pullbackHom_app A g)).of_iso
    (presentationIso (A.pullback g)).symm (presentationIso A).symm (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simp only [Iso.symm_hom, baseChangeHom, Iso.inv_hom_id_assoc]
  · exact (Category.comp_id _).trans
      ((Iso.eq_inv_comp _).2 (presentationIso_hom_toBase (A.pullback g)))
  · exact (Category.comp_id _).trans ((Iso.eq_inv_comp _).2 (presentationIso_hom_toBase A))
  · exact (Category.comp_id g).trans (Category.id_comp g).symm

/-- **The canonical isomorphism `r : Proj_{S'}(g^*A) ≅ S' ×_S Proj_S(A)`.** -/
def baseChangeIso :
    (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (A.pullback g)).scheme ≅
      pullback g (Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).toBase :=
  (isPullback_baseChangeHom A g).flip.isoPullback

/-- The isomorphism `baseChangeIso A g` followed by the first projection to `S'` is the structure
morphism of `Proj_{S'}(g^*A)`. -/
@[reassoc (attr := simp)]
theorem baseChangeIso_hom_fst :
    (baseChangeIso A g).hom ≫
        pullback.fst g (Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).toBase =
      (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (A.pullback g)).toBase :=
  (isPullback_baseChangeHom A g).flip.isoPullback_hom_fst

/-- The isomorphism `baseChangeIso A g` followed by the second projection to `Proj_S(A)` is the
base-change morphism `baseChangeHom A g`. -/
@[reassoc (attr := simp)]
theorem baseChangeIso_hom_snd :
    (baseChangeIso A g).hom ≫
        pullback.snd g (Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).toBase =
      baseChangeHom A g :=
  (isPullback_baseChangeHom A g).flip.isoPullback_hom_snd

/-! ### The base-change morphism on the charts -/

/-- The graded ring map of sections `Γ(U, A) ⟶ Γ(U', g^*A)`, as the composite of the comparison
with the `Situation` substrate, the base change of section rings there, and the comparison back.
See `sectionBaseChange` for the same map with the canonical gradings. -/
def sectionBaseChangeComp (U : S.AffineZariskiSite) (U' : S'.AffineZariskiSite)
    (h : U'.toOpens ≤ g ⁻¹ᵁ U.toOpens) :
    (A.toGradedAlgebra).grading U →+*ᵍ ((A.pullback g).toGradedAlgebra).grading U' :=
  (chartInv (A.pullback g) U').comp
    ((Stacks.RelativeProj.Situation.gradedBaseChange (s := situation A)
        (s' := situation (A.pullback g)) g (pullbackHom A g)
        U.toOpens U'.toOpens h).comp (chartHom A U))

/-- **The graded ring map of sections `Γ(U, A) ⟶ Γ(U', g^*A)`** for affine opens `U` of `S` and
`U'` of `S'` with `U' ⊆ g⁻¹U`: a homogeneous section is sent to the restriction to `U'` of its
pullback. It is `sectionBaseChangeComp`, declared with the canonical gradings
`A.grading U.toOpens` and `(A.pullback g).grading U'.toOpens`, so that constructions on graded
rings elaborate against the canonical graded-ring instances. -/
def sectionBaseChange (U : S.AffineZariskiSite) (U' : S'.AffineZariskiSite)
    (h : U'.toOpens ≤ g ⁻¹ᵁ U.toOpens) :
    A.grading U.toOpens →+*ᵍ (A.pullback g).grading U'.toOpens :=
  sectionBaseChangeComp A g U U' h

/-- The comparison of irrelevant ideals for the graded ring map of sections. -/
theorem irrelevant_le_map_sectionBaseChange (U : S.AffineZariskiSite)
    (U' : S'.AffineZariskiSite) (h : U'.toOpens ≤ g ⁻¹ᵁ U.toOpens) :
    HomogeneousIdeal.irrelevant (((A.pullback g).toGradedAlgebra).grading U') ≤
      (HomogeneousIdeal.irrelevant ((A.toGradedAlgebra).grading U)).map
        (sectionBaseChange A g U U' h) :=
  HomogeneousIdeal.irrelevant_le_map_comp
    (HomogeneousIdeal.irrelevant_le_map_comp (irrelevant_le_map_chartHom A U)
      (Stacks.RelativeProj.Situation.irrelevant_le_gradedBaseChange (s := situation A)
        (s' := situation (A.pullback g)) g (pullbackHom A g)
        (siteAffineOpen U) (siteAffineOpen U') h (isIso_pullbackHom_app A g)))
    (irrelevant_le_map_chartInv (A.pullback g) U')

/-- `Proj.map` of `sectionBaseChange A g U U' h` is the composite of `Proj.map` of the three
graded ring maps of which it is composed: `chartInv`, `gradedBaseChange` and `chartHom`. -/
theorem proj_map_sectionBaseChange (U : S.AffineZariskiSite) (U' : S'.AffineZariskiSite)
    (h : U'.toOpens ≤ g ⁻¹ᵁ U.toOpens) :
    AlgebraicGeometry.Proj.map (sectionBaseChange A g U U' h)
        (irrelevant_le_map_sectionBaseChange A g U U' h) =
      AlgebraicGeometry.Proj.map (chartInv (A.pullback g) U')
          (irrelevant_le_map_chartInv (A.pullback g) U') ≫
        AlgebraicGeometry.Proj.map (Stacks.RelativeProj.Situation.gradedBaseChange
          (s := situation A) (s' := situation (A.pullback g)) g (pullbackHom A g)
          U.toOpens U'.toOpens h)
          (Stacks.RelativeProj.Situation.irrelevant_le_gradedBaseChange (s := situation A)
            (s' := situation (A.pullback g)) g (pullbackHom A g)
            (siteAffineOpen U) (siteAffineOpen U') h (isIso_pullbackHom_app A g)) ≫
        AlgebraicGeometry.Proj.map (chartHom A U) (irrelevant_le_map_chartHom A U) := by
  exact (Proj.map_comp _ _ _ _).trans (congrArg _ (Proj.map_comp _ _ _ _))

/-- For affine opens `U' ⊆ g⁻¹U`, the chart of `Proj_{S'}(g^*A)` over `U'` followed by the
base-change morphism is the composite of `Proj.map` of `chartInv`, `gradedBaseChange` and
`chartHom`, followed by the chart of `Proj_S(A)` over `U`. -/
theorem chart_baseChangeHom_aux (U : S.AffineZariskiSite) (U' : S'.AffineZariskiSite)
    (h : U'.toOpens ≤ g ⁻¹ᵁ U.toOpens) :
    (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (A.pullback g)).chart U'.toOpens
        (isAffineOpen_toOpens U') ≫ baseChangeHom A g =
      AlgebraicGeometry.Proj.map (chartInv (A.pullback g) U')
          (irrelevant_le_map_chartInv (A.pullback g) U') ≫
        AlgebraicGeometry.Proj.map (Stacks.RelativeProj.Situation.gradedBaseChange
          (s := situation A) (s' := situation (A.pullback g)) g (pullbackHom A g)
          U.toOpens U'.toOpens h)
          (Stacks.RelativeProj.Situation.irrelevant_le_gradedBaseChange (s := situation A)
            (s' := situation (A.pullback g)) g (pullbackHom A g)
            (siteAffineOpen U) (siteAffineOpen U') h (isIso_pullbackHom_app A g)) ≫
        AlgebraicGeometry.Proj.map (chartHom A U) (irrelevant_le_map_chartHom A U) ≫
        (Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).chart U.toOpens
          (isAffineOpen_toOpens U) := by
  have h2 := Stacks.RelativeProj.Situation.relativeProjChart_comp_relativeProjBaseChange_eq
    (s := situation A) (s' := situation (A.pullback g)) g (pullbackHom A g)
    (isIso_pullbackHom_app A g)
    (⟨(siteAffineOpen U', siteAffineOpen U), h⟩ :
      Stacks.RelativeProj.Situation.BaseChangeIndex (s := situation A)
        (s' := situation (A.pullback g)) g)
  rw [baseChangeHom, ← Category.assoc, chart_presentationIso_hom]
  refine (Category.assoc _ _ _).trans (congrArg _ ?_)
  rw [reassoc_of% h2, relativeProjChart_presentationIso_inv]

/-- **The base-change morphism on the charts.** For affine opens `U' ⊆ g⁻¹U`, the chart of
`Proj_{S'}(g^*A)` over `U'` followed by the base-change morphism is `Proj.map` of the graded ring
map of sections `Γ(U, A) ⟶ Γ(U', g^*A)` followed by the chart of `Proj_S(A)` over `U`. -/
theorem chart_baseChangeHom (U : S.AffineZariskiSite) (U' : S'.AffineZariskiSite)
    (h : U'.toOpens ≤ g ⁻¹ᵁ U.toOpens) :
    (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (A.pullback g)).chart U'.toOpens
        (isAffineOpen_toOpens U') ≫ baseChangeHom A g =
      AlgebraicGeometry.Proj.map (sectionBaseChange A g U U' h)
          (irrelevant_le_map_sectionBaseChange A g U U' h) ≫
        (Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).chart U.toOpens
          (isAffineOpen_toOpens U) := by
  rw [chart_baseChangeHom_aux A g U U' h, proj_map_sectionBaseChange A g U U' h]
  exact ((Category.assoc _ _ _).trans
    (congrArg (fun z => AlgebraicGeometry.Proj.map (chartInv (A.pullback g) U')
      (irrelevant_le_map_chartInv (A.pullback g) U') ≫ z) (Category.assoc _ _ _))).symm

end Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist

end
