module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineBaseHom
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartConverse

/-!
# The chart-wise morphism lies over the base

Let `S` be a scheme, `𝒜` a quasi-coherent graded `𝒪_S`-algebra (Situation 01NN), `U` an affine
open of `S`, `d ≥ 1` and `X` a relative homogeneous spectrum of `𝒜` ([Stacks, Tag 01NQ]).
This file proves the equation

`Fd.chartBaseHom A U hU hk ≫ U.ι = (Proj.degreeOpen (𝒜(U)) k).ι ≫ P.chart U hU ≫ P.toBase`

from which `...RelativeProjQcohSheaf.Fd.chartHom_comp_toBase_of_chartBaseHom` derives that every
chart-wise morphism lies over its class's recorded morphism to the base.

## Implementation notes

The two sides are `AlgebraicGeometry.Proj.toSpecZero` for the graded ring of global sections of
`𝒜|_U` and for `𝒜(U)`, and the proof transports `Proj.toSpecZero` along
`...RelativeProjQcohSheaf.restrict_ι_proj`.  The transport lemma
`AlgebraicGeometry.Proj.toSpecZero_comp_specMap_congr` takes every datum of the two sides as a
separate argument, identifies the two `GradedRing` instances by
`AlgebraicGeometry.Proj.gradedRing_eq`, and compares the two degree-zero ring maps through their
values, where no `GradedRing` instance occurs.

## Main results

* `AlgebraicGeometry.Proj.toSpecZero_comp_specMap_congr`: the structure morphism to the
  spectrum of the degree-zero part, transported along an identification of the graded ring.
* `...RelativeProjQcohSheaf.Fd.chartEquiv_comp_projInclusionToOpen`: the chart-wise morphism
  lies over the class's own morphism to `U`.
* `...RelativeProjQcohSheaf.Fd.chartBaseHom_comp_ι`: the equation above.
* `...RelativeProjQcohSheaf.Fd.chartHom_comp_toBase`: every chart-wise morphism lies over its
  class's recorded morphism to the base.
* `...RelativeProjQcohSheaf.Fd.chartClassInv_eq_of_chartHom_eq_of_eq`: two chart-wise classes on
  one test scheme whose morphisms into a relative homogeneous spectrum agree have the same image
  under `...Fd.chartClassInv`.

## References

* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Proj (degreeOpen)
open Stacks.AlgebraicGeometry.MorphismsIntoProj (toProj)
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u v

namespace AlgebraicGeometry.Proj

/-- The structure morphism `Proj A ⟶ Spec A_0`, followed by the spectrum of a ring map out of a
fixed ring, transported along an identification of the graded ring; the two degree-zero ring
maps `p`, `q` are compared through their values. -/
theorem toSpecZero_comp_specMap_congr {σ₁ σ₂ : Type v} {R₁ R₂ : Type u}
    [cr₁ : CommRing R₁] [cr₂ : CommRing R₂] [sl₁ : SetLike σ₁ R₁] [sl₂ : SetLike σ₂ R₂]
    [AddSubgroupClass σ₁ R₁] [AddSubgroupClass σ₂ R₂]
    (𝒜 : ℕ → σ₁) (ℬ : ℕ → σ₂) [i : GradedRing 𝒜] [j : GradedRing ℬ]
    (hR : R₁ = R₂) (hσ : σ₁ = σ₂) (hcr : HEq cr₁ cr₂) (hsl : HEq sl₁ sl₂) (h𝒜 : HEq 𝒜 ℬ)
    (hProj : AlgebraicGeometry.Proj 𝒜 = AlgebraicGeometry.Proj ℬ)
    {W : CommRingCat.{u}} (p : W ⟶ CommRingCat.of (𝒜 0)) (q : W ⟶ CommRingCat.of (ℬ 0))
    (hpq : ∀ w : W, HEq ((p.hom w : 𝒜 0) : R₁) ((q.hom w : ℬ 0) : R₂))
    {Y : Scheme.{u}} (e : Spec W ⟶ Y) :
    eqToHom hProj ≫ AlgebraicGeometry.Proj.toSpecZero ℬ ≫ Spec.map q ≫ e
      = AlgebraicGeometry.Proj.toSpecZero 𝒜 ≫ Spec.map p ≫ e := by
  subst hR
  subst hσ
  obtain rfl := eq_of_heq hcr
  obtain rfl := eq_of_heq hsl
  obtain rfl := eq_of_heq h𝒜
  obtain rfl := AlgebraicGeometry.Proj.gradedRing_eq i j
  obtain rfl : p = q :=
    CommRingCat.hom_ext (RingHom.ext fun w => Subtype.ext (eq_of_heq (hpq w)))
  simp

end AlgebraicGeometry.Proj

namespace Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (U : S.Opens)

/-- The structure map of the graded ring of global sections of `𝒜|_U` is the structure map of
`𝒜` at the image open. -/
theorem restrict_ι_strHom_top (r : Γ(U.toScheme, (⊤ : U.toScheme.Opens))) :
    (A.restrict U.ι).strHom (⊤ : U.toScheme.Opens) r
      = A.strHom (U.ι ''ᵁ (⊤ : U.toScheme.Opens)) r := by
  have key : (A.restrict U.ι).strHom (⊤ : U.toScheme.Opens) r
      = A.strHom (U.ι ''ᵁ (⊤ : U.toScheme.Opens))
        ((U.ι.appIso (⊤ : U.toScheme.Opens)).inv r) := rfl
  rw [key, AlgebraicGeometry.Scheme.Opens.ι_appIso]
  rfl

/-- The structure map of the graded ring of global sections of `𝒜|_U` is the structure map of
`𝒜` over `U`, as a heterogeneous equality, the sources being compared by
`AlgebraicGeometry.Scheme.Opens.topIso`. -/
theorem heq_restrict_ι_strHom_top (r : Γ(U.toScheme, (⊤ : U.toScheme.Opens))) :
    HEq ((A.restrict U.ι).strHom (⊤ : U.toScheme.Opens) r) (A.strHom U (U.topIso.hom r)) := by
  rw [A.restrict_ι_strHom_top U r]
  have key : ∀ (W : S.Opens) (hW : W = U) (r' : Γ(S, W)),
      HEq (A.strHom W r') (A.strHom U (S.presheaf.map (eqToHom hW.symm).op r')) := by
    rintro W rfl r'
    simp
  exact key (U.ι ''ᵁ (⊤ : U.toScheme.Opens)) U.ι_image_top r

end Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (U : S.Opens)

/-! ### The degree-zero structure map of the chart -/

/-- The degree-zero structure map of the chart of an affine open `U`, read on the global sections
of `U` as a scheme: `...SheafGradedAlgebra.gradeZeroHom` at `U` precomposed with the
identification `Γ(U, ⊤) ≅ Γ(S, U)`. -/
def chartZeroHom {k : ℕ} :
    Γ(U.toScheme, (⊤ : U.toScheme.Opens)) ⟶ CommRingCat.of (A.grading U 0) :=
  letI : ℕ := k
  U.topIso.hom ≫ CommRingCat.ofHom (A.gradeZeroHom U)

/-- The structure morphism `...RelativeProj.projInclusionToOpen` of the chart of `U` to `U`,
factored through `Spec Γ(U, ⊤)`. -/
theorem projInclusionToOpen_eq (hU : IsAffineOpen U) :
    haveI : IsAffine U.toScheme := hU
    projInclusionToOpen A U hU
      = AlgebraicGeometry.Proj.toSpecZero (A.grading U)
        ≫ Spec.map (U.topIso.hom ≫ CommRingCat.ofHom (A.gradeZeroHom U))
        ≫ U.toScheme.isoSpec.inv := by
  have : IsAffine U.toScheme := hU
  have hz : A.toGradedAlgebra.strZero ⟨U, hU⟩ = CommRingCat.ofHom (A.gradeZeroHom U) :=
    CommRingCat.hom_ext (RingHom.ext fun r => Subtype.ext
      ((A.toGradedAlgebra.coe_strZero_apply ⟨U, hU⟩ r).trans (A.coe_gradeZeroHom U r).symm))
  have hiso : hU.isoSpec.inv = Spec.map U.topIso.hom ≫ U.toScheme.isoSpec.inv := by
    rw [AlgebraicGeometry.IsAffineOpen.isoSpec]
    simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, Scheme.Spec_map]
    rfl
  change AlgebraicGeometry.Proj.toSpecZero (A.grading U)
      ≫ Spec.map (A.toGradedAlgebra.strZero ⟨U, hU⟩) ≫ hU.isoSpec.inv = _
  rw [hz, hiso, Spec.map_comp]
  exact congrArg (fun z => AlgebraicGeometry.Proj.toSpecZero (A.grading U) ≫ z)
    (Category.assoc _ _ _).symm

/-! ### The transport of the chart's structure morphism -/

/-- Along the identification `...RelativeProjQcohSheaf.restrict_ι_proj`, the structure morphism
`...RelativeProj.projInclusionToOpen` of the chart of `U` is `AlgebraicGeometry.Proj.toSpecZero`
of the graded ring of global sections of `𝒜|_U`, followed by its degree-zero structure map and
the identification of `U` with the spectrum of its global sections. -/
theorem eqToHom_restrict_ι_proj_comp_projInclusionToOpen (hU : IsAffineOpen U) :
    haveI : IsAffine U.toScheme := hU
    eqToHom (restrict_ι_proj A U) ≫ projInclusionToOpen A U hU
      = AlgebraicGeometry.Proj.toSpecZero
            ((A.restrict U.ι).grading (⊤ : U.toScheme.Opens))
          ≫ Spec.map (AffineTripleSections.structureRingHom (A.restrict U.ι))
          ≫ U.toScheme.isoSpec.inv := by
  have : IsAffine U.toScheme := hU
  rw [projInclusionToOpen_eq A U hU]
  exact AlgebraicGeometry.Proj.toSpecZero_comp_specMap_congr
    ((A.restrict U.ι).grading (⊤ : U.toScheme.Opens)) (A.grading U)
    (SheafGradedAlgebra.restrict_ι_sectionRing_top A U)
    (restrict_ι_addSubgroup_eq_top A U) (restrict_ι_commRing_heq_top A U)
    (restrict_ι_setLike_heq_top A U) (SheafGradedAlgebra.restrict_ι_grading_top A U)
    (restrict_ι_proj A U) (AffineTripleSections.structureRingHom (A.restrict U.ι))
    (U.topIso.hom ≫ CommRingCat.ofHom (A.gradeZeroHom U))
    (fun r => A.heq_restrict_ι_strHom_top U r) _

/-! ### The chart-wise morphism lies over the class's own morphism to `U` -/

/-- The chart-wise morphism of a class of `F_d(T)` for `𝒜|_U`, read into `Proj 𝒜(U)` and
followed by the chart's structure morphism to `U`, is the class's own morphism to `U`. -/
theorem Fd.chartEquiv_comp_projInclusionToOpen (hU : IsAffineOpen U) {k : ℕ} (hk : 0 < k)
    (T : Scheme.{u}) (ξ : Fd (situationAlgebra (A.restrict U.ι)) (k : ℤ) T) :
    Fd.chartEquiv A U hU hk T ξ
        ≫ (degreeOpen (A.grading U) k).ι ≫ projInclusionToOpen A U hU
      = ξ.1 := by
  have : IsAffine U.toScheme := hU
  have hqc : ∀ n : ℤ, ((situationAlgebra (A.restrict U.ι)).piece n).IsQuasicoherent :=
    fun n => (A.restrict U.ι).isQuasicoherent n
  -- the chart-wise morphism read into `Proj 𝒜(U)` is the absolute classifying morphism of the
  -- graded ring of global sections of `𝒜|_U`, carried along `restrict_ι_proj`
  have hbridge : toProj (A.grading U) (Fd.chartEquiv A U hU hk T ξ)
      = toProj ((A.restrict U.ι).grading (⊤ : U.toScheme.Opens))
          (Quadruple.classifyingHomOfClass hk hqc ξ.2)
        ≫ eqToHom (restrict_ι_proj A U) := by
    change (Quadruple.classifyingHomOfClass hk hqc ξ.2
        ≫ eqToHom (SheafGradedAlgebra.restrict_ι_degreeOpen_toScheme A U k))
        ≫ (degreeOpen (A.grading U) k).ι = _
    rw [Category.assoc, eqToHom_comp_ι (restrict_ι_proj A U)
      (restrict_ι_degreeOpen_heq A U k)
      (SheafGradedAlgebra.restrict_ι_degreeOpen_toScheme A U k)]
    exact (Category.assoc _ _ _).symm
  have hgoal : Fd.chartEquiv A U hU hk T ξ
        ≫ (degreeOpen (A.grading U) k).ι ≫ projInclusionToOpen A U hU
      = toProj (A.grading U) (Fd.chartEquiv A U hU hk T ξ) ≫ projInclusionToOpen A U hU :=
    (Category.assoc _ _ _).symm
  rw [hgoal, hbridge, Category.assoc,
    eqToHom_restrict_ι_proj_comp_projInclusionToOpen A U hU]
  exact Quadruple.toProj_classifyingHomOfClass_comp_toSpecZero hk hqc ξ

/-! ### The equation the base clause was reduced to -/

/-- The morphism `...Fd.chartBaseHom` from the degree-`d` open of `Proj 𝒜(U)` down to `U`,
followed by the inclusion of `U`, is the chart's own structure morphism into a relative
homogeneous spectrum `X` of `𝒜` followed by `f : X ⟶ S`. -/
theorem Fd.chartBaseHom_comp_ι (P : RelativeProjData A) (hU : IsAffineOpen U) {k : ℕ}
    (hk : 0 < k) :
    Fd.chartBaseHom A U hU hk ≫ U.ι
      = (degreeOpen (A.grading U) k).ι ≫ P.chart U hU ≫ P.toBase := by
  have key : (degreeOpen (A.grading U) k).ι ≫ projInclusionToOpen A U hU
      = Fd.chartBaseHom A U hU hk := by
    have h := Fd.chartEquiv_comp_projInclusionToOpen A U hU hk
      (degreeOpen (A.grading U) k).toScheme
      ((Fd.chartEquiv A U hU hk (degreeOpen (A.grading U) k).toScheme).symm (𝟙 _))
    rw [Equiv.apply_symm_apply, Category.id_comp] at h
    exact h
  rw [(P.chart_isPullback U hU).w]
  exact (congrArg (fun z => z ≫ U.ι) key.symm).trans (Category.assoc _ _ _)

/-- For an affine open `U` of `S` and a class of `F_d(T)` for `𝒜|_U`, the morphism
`...Fd.chartHom` into a relative homogeneous spectrum `X` of `𝒜`, followed by `f : X ⟶ S`, is the
class's own morphism to `U` followed by the inclusion of `U`. -/
theorem Fd.chartHom_comp_toBase (P : RelativeProjData A) (hU : IsAffineOpen U) {k : ℕ}
    (hk : 0 < k) (T : Scheme.{u}) (ξ : Fd (situationAlgebra (A.restrict U.ι)) (k : ℤ) T) :
    Fd.chartHom A U P hU hk T ξ ≫ P.toBase = ξ.1 ≫ U.ι :=
  Fd.chartHom_comp_toBase_of_chartBaseHom A U P hU hk
    (Fd.chartBaseHom_comp_ι A U P hU hk) T ξ

/-! ### The converse of the chart agreement, with no base clause -/

/-- Let `U`, `V` be affine opens of `S`, `T` a test scheme, and let `η_U ∈ F_d(T)` for `𝒜|_U`
and `η_V ∈ F_d(T)` for `𝒜|_V` define the same morphism into a relative homogeneous spectrum of
`𝒜`. Then they are the chart-wise classes of one point of `F_d(T)` for `𝒜`. -/
theorem Fd.chartClassInv_eq_of_chartHom_eq_of_eq (V : S.Opens) (P : RelativeProjData A)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) {k : ℕ} (hk : 0 < k) {T : Scheme.{u}}
    (ηU : Fd (situationAlgebra (A.restrict U.ι)) (k : ℤ) T)
    (ηV : Fd (situationAlgebra (A.restrict V.ι)) (k : ℤ) T)
    (h : Fd.chartHom A U P hU hk T ηU = Fd.chartHom A V P hV hk T ηV) :
    Fd.chartClassInv A U ηU = Fd.chartClassInv A V ηV :=
  Fd.chartClassInv_eq_of_chartHom_eq A U V P hU hV hk ηU ηV
    (((Fd.chartHom_comp_toBase A U P hU hk T ηU).symm.trans
      (congrArg (fun z => z ≫ P.toBase) h)).trans
      (Fd.chartHom_comp_toBase A V P hV hk T ηV)) h

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
