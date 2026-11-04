module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveCompletionChern.ChartRing
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.ChartTautological
public import StacksFrontier.AlgebraicGeometry.RelativeProjDegreeOne.Chart
public import StacksFrontier.AlgebraicGeometry.TwistPullbackRatio.Basic
public import StacksFrontier.AlgebraicGeometry.ProjChartKernel.Basic
public import StacksFrontier.AlgebraicGeometry.ProjDegreeOneTriv.Basic

/-!
# The tautological surjection on the open `T ≠ 0` of a chart

Let `E = Proj_X(Sym^*(𝒞)[T])` and `V` an affine open of `X`. On the open `W = D₊(T)` of the chart
of `E` over `V`, the twist `𝒪_E(1)` is free on `T`, and the tautological surjection sends the
pullback of a section `m` of `𝒞` to `y_m · T`, where `y_m = m / T` is the function on `W`
corresponding to the generator `m` of `Sym_R(M) = Γ(W, 𝒪_E)`.

## Main definitions

* `Stacks.Chow.ProjectiveCompletion.openW`: the open `W = D₊(T)` of the chart over `V`.
* `Stacks.Chow.ProjectiveCompletion.coordY`: the function `y_m = m / T` on `W`.

## Main results

* `Stacks.Chow.ProjectiveCompletion.psi_restrict_openW`: on `W`, `ψ₁(m) = y_m · ψ₁(T)`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SymGraded Stacks.AlgebraicGeometry.RelativeProj HomogeneousLocalization
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

namespace Stacks.Chow.ProjectiveCompletion

variable {X : Scheme.{u}} (𝒞 : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞] {V : X.Opens}
  (hV : IsAffineOpen V)

/-- The twist datum of the projective bundle of `𝒞 ⊕ 𝒪_X`. -/
abbrev twistData := projectiveBundleTwistData (module 𝒞) (bundlePieces (module 𝒞))

/-- The standard open `D₊(T)` of the chart over `V`. -/
abbrev chartD : (AlgebraicGeometry.Proj ((symAlg 𝒞).grading V)).Opens :=
  AlgebraicGeometry.Proj.basicOpen ((symAlg 𝒞).grading V)
    ((chartT 𝒞 V : (symAlg 𝒞).grading V 1) : (symAlg 𝒞).sectionRing V)

/-- **The open `W = D₊(T)` of the chart over `V`**, as an open of `E`. -/
def openW : (space 𝒞).Opens := chart 𝒞 V hV ''ᵁ chartD 𝒞 (V := V)

/-- The open `W` lies in the image of the whole chart over `V`. -/
theorem openW_le_chart_image : openW 𝒞 hV ≤ chart 𝒞 V hV ''ᵁ ⊤ :=
  Scheme.Hom.image_mono _ le_top

/-- The image of the chart over `V` is the preimage of `V` in `E`. -/
theorem chart_image_top_eq : chart 𝒞 V hV ''ᵁ ⊤ = proj 𝒞 ⁻¹ᵁ V :=
  Stacks.AlgebraicGeometry.RelativeProjTwistGlue.chart_image_top _ V hV

/-- The open `W` lies in the preimage of `V` in `E`. -/
theorem openW_le : openW 𝒞 hV ≤ proj 𝒞 ⁻¹ᵁ V :=
  (openW_le_chart_image 𝒞 hV).trans (chart_image_top_eq 𝒞 hV).le

/-- The open `W` lies in the preimage of `V` under the structure morphism of the relative `Proj`.
-/
theorem openW_le' : openW 𝒞 hV ≤ (relativeProj (symAlg 𝒞)).toBase ⁻¹ᵁ V :=
  openW_le 𝒞 hV

/-- The element `m / T` of `Γ(D₊(T), 𝒪)`, for a section `m` of `𝒞` over `V`. -/
def chartY (m : Γ(𝒞, V)) :
    Γ(AlgebraicGeometry.Proj ((symAlg 𝒞).grading V), chartD 𝒞 (V := V)) :=
  (AlgebraicGeometry.Proj.awayToSection ((symAlg 𝒞).grading V) _).hom
    (HomogeneousLocalization.Away.mk ((symAlg 𝒞).grading V) (chartT 𝒞 V).2 1
      ((chartE 𝒞 m : (symAlg 𝒞).grading V 1) : (symAlg 𝒞).sectionRing V)
      (by simp))

/-- **The function `y_m = m / T` on `W`.** -/
def coordY (m : Γ(𝒞, V)) : Γ(space 𝒞, openW 𝒞 hV) :=
  ((chart 𝒞 V hV).appIso (chartD 𝒞 (V := V))).inv (chartY 𝒞 m)

/-- The chart comparison on a standard open `D₊(q)`, at a degree-one homogeneous section. -/
private theorem mapSection_basicOpen_degreeSection_of_le (q : (symAlg 𝒞).grading V 1)
    (a : (symAlg 𝒞).sectionPieces V 1)
    (h : chart 𝒞 V hV ''ᵁ AlgebraicGeometry.Proj.basicOpen ((symAlg 𝒞).grading V)
      (q : (symAlg 𝒞).sectionRing V) ≤ (relativeProj (symAlg 𝒞)).toBase ⁻¹ᵁ V) :
    letI := (twistData 𝒞).chartData.chart_isOpenImmersion V hV
    (twistData 𝒞).chartData.mapSection V hV ((1 : ℕ) : ℤ)
        (AlgebraicGeometry.Proj.basicOpen ((symAlg 𝒞).grading V) (q : (symAlg 𝒞).sectionRing V))
        ((twistingSheaf ((symAlg 𝒞).grading V) ((1 : ℕ) : ℤ)).val.map
          (homOfLE (le_top : AlgebraicGeometry.Proj.basicOpen ((symAlg 𝒞).grading V)
            (q : (symAlg 𝒞).sectionRing V) ≤ ⊤)).op
          (degreeSection ((symAlg 𝒞).grading V) 1
            ⟨DirectSum.of ((symAlg 𝒞).sectionPieces V) 1 a, (symAlg 𝒞).of_mem_grading V a⟩)) =
      ((twistData 𝒞).algebra.piece ((1 : ℕ) : ℤ)).val.map (homOfLE h).op
        (((twistData 𝒞).ψ 1).val.app (op V) a) := by
  let := (twistData 𝒞).chartData.chart_isOpenImmersion V hV
  have hres := Stacks.AlgebraicGeometry.RelativeProjDegreeOne.mapSection_res
    (twistData 𝒞).chartData V hV ((1 : ℕ) : ℤ)
    (le_top : AlgebraicGeometry.Proj.basicOpen ((symAlg 𝒞).grading V)
      (q : (symAlg 𝒞).sectionRing V) ≤ ⊤)
    (degreeSection ((symAlg 𝒞).grading V) 1
      ⟨DirectSum.of ((symAlg 𝒞).sectionPieces V) 1 a, (symAlg 𝒞).of_mem_grading V a⟩)
  refine hres.symm.trans ?_
  rw [(twistData 𝒞).ψ_chart V hV 1 a]
  exact Stacks.AlgebraicGeometry.RelativeProjDegreeOne.map_eqRec
    (M := (twistData 𝒞).algebra.piece ((1 : ℕ) : ℤ))
    ((twistData 𝒞).chartData.chart_range V hV) _ _ _

/-- On a standard open `D₊(b)`, the degree-one section of `a` is `a / b` times that of `b`. -/
private theorem psi_eq_smul_away (a b : (symAlg 𝒞).sectionPieces V 1)
    (h : chart 𝒞 V hV ''ᵁ AlgebraicGeometry.Proj.basicOpen ((symAlg 𝒞).grading V)
      (DirectSum.of ((symAlg 𝒞).sectionPieces V) 1 b) ≤
        (relativeProj (symAlg 𝒞)).toBase ⁻¹ᵁ V) :
    ((twistData 𝒞).algebra.piece ((1 : ℕ) : ℤ)).val.map (homOfLE h).op
        (((twistData 𝒞).ψ 1).val.app (op V) a) =
      ((show (relativeProj (symAlg 𝒞)).scheme.Modules from
          (twistData 𝒞).algebra.piece ((1 : ℕ) : ℤ)).smul
          (((chart 𝒞 V hV).appIso _).inv
            ((AlgebraicGeometry.Proj.awayToSection ((symAlg 𝒞).grading V) _).hom
              (HomogeneousLocalization.Away.mk ((symAlg 𝒞).grading V)
                ((symAlg 𝒞).of_mem_grading V b) 1 (DirectSum.of ((symAlg 𝒞).sectionPieces V) 1 a)
                (by simp))))).hom
        (((twistData 𝒞).algebra.piece ((1 : ℕ) : ℤ)).val.map (homOfLE h).op
          (((twistData 𝒞).ψ 1).val.app (op V) b)) := by
  let := (twistData 𝒞).chartData.chart_isOpenImmersion V hV
  have h1 := mapSection_basicOpen_degreeSection_of_le 𝒞 hV ⟨_, (symAlg 𝒞).of_mem_grading V b⟩ a h
  have h2 := mapSection_basicOpen_degreeSection_of_le 𝒞 hV ⟨_, (symAlg 𝒞).of_mem_grading V b⟩ b h
  have hratio := Stacks.TwistPullbackRatio.degreeSection_res_eq ((symAlg 𝒞).grading V)
    ((symAlg 𝒞).of_mem_grading V a) ((symAlg 𝒞).of_mem_grading V b)
  have hsmul := Stacks.AlgebraicGeometry.RelativeProjDegreeOne.mapSection_smul
    (twistData 𝒞).chartData V hV ((1 : ℕ) : ℤ)
    (AlgebraicGeometry.Proj.basicOpen ((symAlg 𝒞).grading V)
      (DirectSum.of ((symAlg 𝒞).sectionPieces V) 1 b))
    ((AlgebraicGeometry.Proj.awayToSection ((symAlg 𝒞).grading V) _).hom
      (HomogeneousLocalization.Away.mk ((symAlg 𝒞).grading V) ((symAlg 𝒞).of_mem_grading V b) 1
        (DirectSum.of ((symAlg 𝒞).sectionPieces V) 1 a)
        (by simp)))
    ((twistingSheaf ((symAlg 𝒞).grading V) ((1 : ℕ) : ℤ)).val.map
      (homOfLE (le_top : AlgebraicGeometry.Proj.basicOpen ((symAlg 𝒞).grading V)
        (DirectSum.of ((symAlg 𝒞).sectionPieces V) 1 b) ≤ ⊤)).op
      (degreeSection ((symAlg 𝒞).grading V) 1 ⟨_, (symAlg 𝒞).of_mem_grading V b⟩))
  refine h1.symm.trans (Eq.trans ?_ (hsmul.trans (congrArg _ h2)))
  exact congrArg _ hratio

/-- **The chart comparison on `D₊(T)`, at a degree-one homogeneous section.** -/
theorem mapSection_chartD_degreeSection (a : (symAlg 𝒞).sectionPieces V 1) :
    letI := (twistData 𝒞).chartData.chart_isOpenImmersion V hV
    (twistData 𝒞).chartData.mapSection V hV ((1 : ℕ) : ℤ) (chartD 𝒞 (V := V))
        ((twistingSheaf ((symAlg 𝒞).grading V) ((1 : ℕ) : ℤ)).val.map
          (homOfLE (le_top : chartD 𝒞 (V := V) ≤ ⊤)).op
          (degreeSection ((symAlg 𝒞).grading V) 1
            ⟨DirectSum.of ((symAlg 𝒞).sectionPieces V) 1 a, (symAlg 𝒞).of_mem_grading V a⟩)) =
      ((twistData 𝒞).algebra.piece ((1 : ℕ) : ℤ)).val.map (homOfLE (openW_le' 𝒞 hV)).op
        (((twistData 𝒞).ψ 1).val.app (op V) a) :=
  mapSection_basicOpen_degreeSection_of_le 𝒞 hV (chartT 𝒞 V) a _

/-- **On `W`, the degree-one homogeneous section of `m` is `y_m` times that of `T`.** -/
theorem psi_restrict_openW (m : Γ(𝒞, V)) :
    ((twistData 𝒞).algebra.piece ((1 : ℕ) : ℤ)).val.map (homOfLE (openW_le' 𝒞 hV)).op
        (((twistData 𝒞).ψ 1).val.app (op V)
          ((Scheme.Modules.symmetricAlgebraGen X (module 𝒞)).val.app (op V)
            (Scheme.Modules.Hom.app (inl 𝒞) V m))) =
      ((show (relativeProj (symAlg 𝒞)).scheme.Modules from
          (twistData 𝒞).algebra.piece ((1 : ℕ) : ℤ)).smul (coordY 𝒞 hV m)).hom
        (((twistData 𝒞).algebra.piece ((1 : ℕ) : ℤ)).val.map (homOfLE (openW_le' 𝒞 hV)).op
          (((twistData 𝒞).ψ 1).val.app (op V)
            ((Scheme.Modules.symmetricAlgebraGen X (module 𝒞)).val.app (op V)
              ((module 𝒞).presheaf.map (homOfLE le_top).op (sectionT 𝒞))))) :=
  psi_eq_smul_away 𝒞 hV _ (_ : (symAlg 𝒞).sectionPieces V 1) _

/-! ### The ratio of two degree-one sections on a standard open of a chart -/

/-- The image in `E` of the standard open `D₊(q)` of the chart over `V`. -/
def chartOpen (q : (symAlg 𝒞).grading V 1) : (space 𝒞).Opens :=
  chart 𝒞 V hV ''ᵁ AlgebraicGeometry.Proj.basicOpen ((symAlg 𝒞).grading V)
    (q : (symAlg 𝒞).sectionRing V)

/-- The image of `D₊(q)` in `E` lies in the preimage of `V` under the structure morphism of the
relative `Proj`. -/
theorem chartOpen_le (q : (symAlg 𝒞).grading V 1) :
    chartOpen 𝒞 hV q ≤ (relativeProj (symAlg 𝒞)).toBase ⁻¹ᵁ V :=
  (Scheme.Hom.image_mono _ le_top).trans (chart_image_top_eq 𝒞 hV).le

/-- The ratio `p / q` as a function on the image of `D₊(q)` in `E`. -/
def chartRatio (p q : (symAlg 𝒞).grading V 1) : Γ(space 𝒞, chartOpen 𝒞 hV q) :=
  ((chart 𝒞 V hV).appIso _).inv
    ((AlgebraicGeometry.Proj.awayToSection ((symAlg 𝒞).grading V) _).hom
      (HomogeneousLocalization.Away.mk ((symAlg 𝒞).grading V) q.2 1
        (p : (symAlg 𝒞).sectionRing V) (by simp)))

/-- The chart comparison on `D₊(q)`, at a degree-one homogeneous section. -/
theorem mapSection_basicOpen_degreeSection (q : (symAlg 𝒞).grading V 1)
    (a : (symAlg 𝒞).sectionPieces V 1) :
    letI := (twistData 𝒞).chartData.chart_isOpenImmersion V hV
    (twistData 𝒞).chartData.mapSection V hV ((1 : ℕ) : ℤ)
        (AlgebraicGeometry.Proj.basicOpen ((symAlg 𝒞).grading V) (q : (symAlg 𝒞).sectionRing V))
        ((twistingSheaf ((symAlg 𝒞).grading V) ((1 : ℕ) : ℤ)).val.map
          (homOfLE (le_top : AlgebraicGeometry.Proj.basicOpen ((symAlg 𝒞).grading V)
            (q : (symAlg 𝒞).sectionRing V) ≤ ⊤)).op
          (degreeSection ((symAlg 𝒞).grading V) 1
            ⟨DirectSum.of ((symAlg 𝒞).sectionPieces V) 1 a, (symAlg 𝒞).of_mem_grading V a⟩)) =
      ((twistData 𝒞).algebra.piece ((1 : ℕ) : ℤ)).val.map (homOfLE (chartOpen_le 𝒞 hV q)).op
        (((twistData 𝒞).ψ 1).val.app (op V) a) :=
  mapSection_basicOpen_degreeSection_of_le 𝒞 hV q a _

/-- **On the image of `D₊(q)`, the degree-one homogeneous section of `p` is `p / q` times that of
`q`**, for degree-one elements `p`, `q` attached to sections of `𝒞 ⊕ 𝒪_X` over `V`. -/
theorem psi_ratio (a b : (symAlg 𝒞).sectionPieces V 1) :
    ((twistData 𝒞).algebra.piece ((1 : ℕ) : ℤ)).val.map
        (homOfLE (chartOpen_le 𝒞 hV ⟨_, (symAlg 𝒞).of_mem_grading V b⟩)).op
        (((twistData 𝒞).ψ 1).val.app (op V) a) =
      ((show (relativeProj (symAlg 𝒞)).scheme.Modules from
          (twistData 𝒞).algebra.piece ((1 : ℕ) : ℤ)).smul
          (chartRatio 𝒞 hV ⟨_, (symAlg 𝒞).of_mem_grading V a⟩
            ⟨_, (symAlg 𝒞).of_mem_grading V b⟩)).hom
        (((twistData 𝒞).algebra.piece ((1 : ℕ) : ℤ)).val.map
          (homOfLE (chartOpen_le 𝒞 hV ⟨_, (symAlg 𝒞).of_mem_grading V b⟩)).op
          (((twistData 𝒞).ψ 1).val.app (op V) b)) :=
  psi_eq_smul_away 𝒞 hV a b _

end Stacks.Chow.ProjectiveCompletion
