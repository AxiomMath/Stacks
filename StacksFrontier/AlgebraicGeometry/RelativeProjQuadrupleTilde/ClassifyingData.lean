module

public import StacksFrontier.AlgebraicGeometry.ProjPresentationCompare.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Charts.Descent
public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.SituationComparison
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartDegreeOpenEquiv
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.SituationRestrict
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The relative homogeneous spectrum of a situation as a `RelativeProjData`

The relative homogeneous spectrum `Proj_S(𝒜)` of Situation 01NN exists twice in this repository:
as `Stacks.RelativeProj.Situation.relativeProj s`, glued from the projective spectra of the
graded rings of sections of a `Stacks.RelativeProj.Situation`, which is where the sheaf `ℳ̃` of a
quasi-coherent graded module lives; and as the datum
`Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData` over the sheaf-level graded algebra
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`, which is where the functor of
quadruples is shown to be represented. This file puts the first into the shape of the second:
**the scheme `relativeProj s`, with its structure morphism and its own charts read through the
identification of the two graded rings of sections, is a `RelativeProjData`.**

Through it every quadruple `(f : T → S, d, L, ψ)` of positive degree classifies a morphism
`h : T ⟶ relativeProj s`, the morphism representing its class in `F_d(T)`, and the morphisms of
pulled-back quadruples are the composites.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.sheafGradedAlgebra`: the graded algebra
  of a situation, as a `SheafGradedAlgebra`.
* `Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.relativeProjData`: `relativeProj s` as a
  `RelativeProjData` of it.
* `Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.classifyingHom`: the morphism
  `T ⟶ relativeProj s` a quadruple of positive degree classifies.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.relativeProjData_chart`: the chart of the
  datum is the situation's chart, precomposed with the identification of the two projective
  spectra.
* `Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.classifyingHom_comp_toBase`: the
  classifying morphism lies over the quadruple's morphism to the base.
* `Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.classifyingHom_pullback`: the morphism the
  pullback of a quadruple along `g : T' ⟶ T` classifies is `g ≫ h`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProj Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.SheafSymmetricAlgebra Stacks.AlgebraicGeometry.ProjPresentation
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde

variable (s : Stacks.RelativeProj.Situation.{u})

/-- The graded algebra of a situation vanishes on sections in negative degrees. -/
theorem vanishesInNegativeDegrees : VanishesInNegativeDegrees s.algebra :=
  fun n hn U x => section_eq_zero_of_isZero (s.negative_isZero n hn) U.unop x

/-- **The graded algebra of a situation, as sheaf-level graded algebra data.** -/
abbrev sheafGradedAlgebra : SheafGradedAlgebra s.base :=
  toSheafGradedAlgebra s.algebra s.mul_comm (vanishesInNegativeDegrees s) s.isQuasicoherent

/-- The identification of the graded rings of sections of the two substrates over an affine
open, from the `SheafGradedAlgebra` side to the situation side. -/
abbrev sectionGradedHom (U : s.base.AffineZariskiSite) :
    (sheafGradedAlgebra s).toGradedAlgebra.grading U →+*ᵍ
      s.sectionRingGrading (siteAffineOpen U).1 :=
  situationSectionGradedHom s.algebra s.mul_comm (vanishesInNegativeDegrees s)
    s.isQuasicoherent U.toOpens

/-- The identification of the graded rings of sections, from the situation side. -/
abbrev sectionGradedInv (U : s.base.AffineZariskiSite) :
    s.sectionRingGrading (siteAffineOpen U).1 →+*ᵍ
      (sheafGradedAlgebra s).toGradedAlgebra.grading U :=
  situationSectionGradedInv s.algebra s.mul_comm (vanishesInNegativeDegrees s)
    s.isQuasicoherent U.toOpens

/-- `sectionGradedInv` is a left inverse of `sectionGradedHom` over each affine open. -/
theorem sectionGradedInv_comp_hom (U : s.base.AffineZariskiSite) :
    (sectionGradedInv s U).comp (sectionGradedHom s U) =
      GradedRingHom.id ((sheafGradedAlgebra s).toGradedAlgebra.grading U) :=
  situationSectionGradedInv_comp_hom s.algebra s.mul_comm (vanishesInNegativeDegrees s)
    s.isQuasicoherent U.toOpens

/-- `sectionGradedInv` is a right inverse of `sectionGradedHom` over each affine open. -/
theorem sectionGradedHom_comp_inv (U : s.base.AffineZariskiSite) :
    (sectionGradedHom s U).comp (sectionGradedInv s U) =
      GradedRingHom.id (s.sectionRingGrading (siteAffineOpen U).1) :=
  situationSectionGradedHom_comp_inv s.algebra s.mul_comm (vanishesInNegativeDegrees s)
    s.isQuasicoherent U.toOpens

/-- The identification commutes with restriction of homogeneous sections. -/
theorem sectionGradedHom_res (U V : s.base.AffineZariskiSite) (h : U.toOpens ≤ V.toOpens) :
    (sectionGradedHom s U).comp ((sheafGradedAlgebra s).toGradedAlgebra.res h) =
      ((Stacks.RelativeProj.Situation.chartData s).restrict (siteAffineOpen_le h)).comp
        (sectionGradedHom s V) :=
  GradedRingHom.ext fun x =>
    situationSectionRingEquiv_resRingHom s.algebra s.mul_comm (vanishesInNegativeDegrees s)
      s.isQuasicoherent h x

/-- The identification commutes with the degree-zero identifications. -/
theorem sectionGradedHom_base (U : s.base.AffineZariskiSite) :
    (sheafGradedAlgebra s).toGradedAlgebra.strZero U ≫
        CommRingCat.ofHom (sectionGradedHom s U).gradedZeroRingHom =
      (Stacks.RelativeProj.Situation.chartData s).base (siteAffineOpen U) := by
  refine CommRingCat.hom_ext (RingHom.ext fun r => Subtype.ext ?_)
  exact (congrArg (situationSectionRingEquiv s.algebra s.mul_comm (vanishesInNegativeDegrees s)
      s.isQuasicoherent U.toOpens)
      (((sheafGradedAlgebra s).toGradedAlgebra).coe_strZero_apply U r)).trans
    ((situationSectionRingEquiv_strHom s.algebra s.mul_comm (vanishesInNegativeDegrees s)
      s.isQuasicoherent U.toOpens r).trans
      (Stacks.AlgebraicGeometry.RelativeProj.projZeroRingHom'_coe_of_mem _
        (Stacks.RelativeProj.Situation.sectionRingBaseMap_mem_zero s U.toOpens r)).symm)

/-- The induced isomorphism between the chart of the `SheafGradedAlgebra` over an affine open and
the chart of the situation over it. -/
abbrev situationChartIso (U : s.base.AffineZariskiSite) :
    (sheafGradedAlgebra s).toGradedAlgebra.projOver U ≅
      AlgebraicGeometry.Proj (s.sectionRingGrading (siteAffineOpen U).1) :=
  projIso (ℬ := fun W : s.base.affineOpens => s.sectionRingGrading W.1)
    (sheafGradedAlgebra s).toGradedAlgebra (sectionGradedHom s) (sectionGradedInv s)
    (sectionGradedInv_comp_hom s) (sectionGradedHom_comp_inv s) U

/-- The charts of the situation, read through the identification of the projective spectra, are
compatible with the transition morphisms of the `SheafGradedAlgebra` along an arbitrary inclusion
of affine opens. -/
theorem chart_transition_aux (U V : s.base.AffineZariskiSite) (h : U.toOpens ≤ V.toOpens) :
    projInclusionMap (sheafGradedAlgebra s) U.toOpens V.toOpens h (isAffineOpen_toOpens U)
        (isAffineOpen_toOpens V) ≫ (situationChartIso s V).hom ≫
          Stacks.RelativeProj.Situation.relativeProjChart s (siteAffineOpen V) =
      (situationChartIso s U).hom ≫
        Stacks.RelativeProj.Situation.relativeProjChart s (siteAffineOpen U) := by
  have hi := RelativeProjGeneral.irrelevant_le_map_res_of_le_opens
    (sheafGradedAlgebra s).toGradedAlgebra (U := U) (V := V) h
  have hw := Stacks.RelativeProj.Situation.relativeProjChart_transition s
    (W := siteAffineOpen U) (W' := siteAffineOpen V) h
  have ht := transition_projIso_hom (Stacks.RelativeProj.Situation.chartData s)
    (sheafGradedAlgebra s).toGradedAlgebra (sectionGradedHom s) (sectionGradedInv s)
    (sectionGradedInv_comp_hom s) (sectionGradedHom_comp_inv s) (sectionGradedHom_res s) U V h hi
  have he := GradedAlgebra.transition_eq_map (sheafGradedAlgebra s).toGradedAlgebra (U := U)
    (V := V) h (projInclusionDomain_eq_top (sheafGradedAlgebra s) U.toOpens V.toOpens h
      (isAffineOpen_toOpens U) (isAffineOpen_toOpens V)) hi
  refine (congrArg (· ≫ (situationChartIso s V).hom ≫
    Stacks.RelativeProj.Situation.relativeProjChart s (siteAffineOpen V)) he).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ Stacks.RelativeProj.Situation.relativeProjChart s (siteAffineOpen V))
    ht).trans ?_
  exact (Category.assoc _ _ _).trans
    (congrArg ((situationChartIso s U).hom ≫ ·) hw)

/-- **The relative homogeneous spectrum of a situation, as a `RelativeProjData`** of its graded
algebra read as sheaf-level data: the scheme `relativeProj s` with its structure morphism, the
chart over an affine open `U` being the situation's chart over `U` precomposed with the
isomorphism of projective spectra induced by the identification of the two graded rings of
sections over `U`. -/
@[ega "II 3.1.3", ega "II 8.3.1"]
def relativeProjData : RelativeProjData (sheafGradedAlgebra s) where
  scheme := Stacks.RelativeProj.Situation.relativeProj s
  toBase := Stacks.RelativeProj.Situation.relativeProjToBase s
  chart U hU := (situationChartIso s ⟨U, hU⟩).hom ≫
    Stacks.RelativeProj.Situation.relativeProjChart s ⟨U, hU⟩
  chart_isPullback U hU :=
    ((chartFamily (Stacks.RelativeProj.Situation.chartData s)
      (sheafGradedAlgebra s).toGradedAlgebra (sectionGradedHom s) (sectionGradedInv s)
      (sectionGradedInv_comp_hom s) (sectionGradedHom_comp_inv s) (sectionGradedHom_res s)
      (sectionGradedHom_base s)).isPullback ⟨U, hU⟩).flip
  chart_transition U V h hU hV := chart_transition_aux s ⟨U, hU⟩ ⟨V, hV⟩ h

/-- The scheme of the datum is the situation's relative homogeneous spectrum. -/
theorem relativeProjData_scheme :
    (relativeProjData s).scheme = Stacks.RelativeProj.Situation.relativeProj s := rfl

/-- The structure morphism of the datum is the situation's. -/
theorem relativeProjData_toBase :
    (relativeProjData s).toBase = Stacks.RelativeProj.Situation.relativeProjToBase s := rfl

/-- **The chart of the datum is the situation's chart**, precomposed with the identification of
the two projective spectra. -/
theorem relativeProjData_chart (U : s.base.Opens) (hU : IsAffineOpen U) :
    (relativeProjData s).chart U hU =
      (situationChartIso s ⟨U, hU⟩).hom ≫
        Stacks.RelativeProj.Situation.relativeProjChart s ⟨U, hU⟩ :=
  rfl

/-! ### The morphism a quadruple classifies -/

variable {T : Scheme.{u}} {f : T ⟶ s.base} {d : ℤ}

/-- **The morphism `h : T ⟶ Proj_S(𝒜)` a quadruple `(f : T → S, d, L, ψ)` of positive degree
classifies**: the morphism into the relative degree-`d` open `U_d` representing the class of the
quadruple in `F_d(T)`, followed by the inclusion of `U_d`. -/
def classifyingHom (hd : 0 < d) (P : Quadruple f s.algebra d) :
    T ⟶ Stacks.RelativeProj.Situation.relativeProj s :=
  Fd.degreeOpenEquiv' (sheafGradedAlgebra s) (relativeProjData s) hd T (Fd.mk f P) ≫
    ((relativeProjData s).degreeOpen d.toNat).ι

/-- **The classifying morphism lies over the quadruple's morphism to the base.** -/
theorem classifyingHom_comp_toBase (hd : 0 < d) (P : Quadruple f s.algebra d) :
    classifyingHom s hd P ≫ Stacks.RelativeProj.Situation.relativeProjToBase s = f := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hd.le
  exact Category.assoc _ _ _ |>.trans
    (Fd.homDegreeOpen_comp_toBase (sheafGradedAlgebra s) (relativeProjData s)
      (by exact_mod_cast hd) (Fd.mk f P))

/-- **The morphism the pullback of a quadruple classifies is the composite.** For `g : T' ⟶ T`
the pullback quadruple `(f ∘ g, d, g^*L, g^*ψ)` classifies `h ∘ g`. -/
theorem classifyingHom_pullback (hd : 0 < d) (P : Quadruple f s.algebra d) {T' : Scheme.{u}}
    (g : T' ⟶ T) :
    classifyingHom s hd (P.pullback g) = g ≫ classifyingHom s hd P :=
  (congrArg (· ≫ ((relativeProjData s).degreeOpen d.toNat).ι)
    (Fd.degreeOpenEquiv'_pullback (sheafGradedAlgebra s) (relativeProjData s) hd g
      (Fd.mk f P))).trans (Category.assoc _ _ _)

end Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde

end
