module

public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.ConormalAlgebraSheafSections
public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.Basic
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Bridge
public import StacksFrontier.RingTheory.Filtration.AssociatedGradedGenerators
public import StacksFrontier.RingTheory.Filtration.AssociatedGradedGrading

/-!
# The graded ring of sections of the conormal algebra over an affine chart

Let `i : Z ⟶ X` be an immersion with conormal algebra `𝒞_{Z/X,*}` ([Stacks, Tag 0630]). This
file records `𝒞_{Z/X,*}` as sheaf-level graded algebra data in the sense of Situation 01NN
(`Stacks.Conormal.conormalSheafGradedAlgebra`), whose graded ring of sections over an open `W` is
`⨁_{n ≥ 0} 𝒞_{Z/X,n}(W)`, and identifies that graded ring over the preimage `i⁻¹U` of an affine
open `U = Spec R` of `X` over which `i` is a closed immersion, with `I = ker(R ⟶ Γ(Z, i⁻¹U))`:

  `Gr_I(R) = ⨁_{n ≥ 0} Iⁿ/Iⁿ⁺¹ ≅ ⨁_{n ≥ 0} 𝒞_{Z/X,n}(i⁻¹U)`

as graded rings (Stacks 0633 in each degree, `AlgebraicGeometry.affineSectionsEquiv`), compatibly
with the structure maps and with restriction to a smaller chart.

## Main definitions

* `Stacks.Conormal.conormalSheafGradedAlgebra`: `𝒞_{Z/X,*}` as sheaf-level graded algebra data.
* `Stacks.Conormal.gradedSectionRingHom` and `Stacks.Conormal.gradedSectionRingEquiv`: the ring
  isomorphism `Gr_I(R) ≅ ⨁ₙ 𝒞_{Z/X,n}(i⁻¹U)`.
* `Stacks.Conormal.gradedSectionRingGradedHom`: the same as a homomorphism of graded rings.

## Main results

* `Stacks.Conormal.gradedSectionRingHom_classOfPow`: the class of `a ∈ Iⁿ` goes to the
  homogeneous section of degree `n` it names.
* `Stacks.Conormal.gradedSectionRingHom_gradeZero`: on degree-zero classes it is the structure
  map.
* `Stacks.Conormal.gradedSectionRingHom_restrict`: it commutes with restriction.

## References

* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
* [Stacks Project, Tag 0633](https://stacks.math.columbia.edu/tag/0633)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite DirectSum
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace Stacks.Conormal

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/-- **The conormal algebra as sheaf-level graded algebra data** (Situation 01NN): it is
commutative, concentrated in nonnegative degrees, and has quasi-coherent pieces. -/
def conormalSheafGradedAlgebra : SheafGradedAlgebra Z :=
  Stacks.AlgebraicGeometry.SheafSymmetricAlgebra.toSheafGradedAlgebra (conormalAlgebra i).algebra
    (fun m n W a b => (conormalAlgebra i).mul_comm_int m n W a b)
    (fun n hn W x => (conormalAlgebra i).eq_zero_of_neg n hn W x)
    (conormalAlgebra i).isQuasicoherent

/-- **The conormal algebra as a quasi-coherent graded `𝒪_Z`-algebra in the affine-open form**
of Situation 01NN: its ring of sections over an affine open `W` of `Z` is
`⨁_{n ≥ 0} 𝒞_{Z/X,n}(W)`. This is `SheafGradedAlgebra.toGradedAlgebra` of
`Stacks.Conormal.conormalSheafGradedAlgebra`, written out field by field as an `abbrev` so that its
rings of sections are visibly the section rings. -/
abbrev conormalSiteAlgebra : Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra Z where
  ring W := CommRingCat.of ((conormalSheafGradedAlgebra i).sectionRing W.toOpens)
  grading W := (conormalSheafGradedAlgebra i).grading W.toOpens
  gradedRing W := (conormalSheafGradedAlgebra i).instGradedRing W.toOpens
  str W := CommRingCat.ofHom ((conormalSheafGradedAlgebra i).strHom W.toOpens)
  str_mem W r := (conormalSheafGradedAlgebra i).strHom_mem W.toOpens r
  res h := (conormalSheafGradedAlgebra i).res h
  res_id W := (conormalSheafGradedAlgebra i).toGradedAlgebra.res_id W
  res_comp hUV hVW := (conormalSheafGradedAlgebra i).toGradedAlgebra.res_comp hUV hVW
  res_str h r := (conormalSheafGradedAlgebra i).toGradedAlgebra.res_str h r
  isLocalization W f := (conormalSheafGradedAlgebra i).toGradedAlgebra.isLocalization W f

variable (U : X.affineOpens) (hU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl))

/-- **The ring homomorphism `Gr_I(R) ⟶ ⨁ₙ 𝒞_{Z/X,n}(i⁻¹U)`**, the degreewise identification of
Stacks 0633 on each summand. -/
def gradedSectionRingHom :
    AssociatedGraded.gradedRing (chartIdeal i U) →+*
      (conormalSheafGradedAlgebra i).sectionRing (i ⁻¹ᵁ U.1) :=
  DirectSum.toSemiring
    (fun n => (DirectSum.of ((conormalSheafGradedAlgebra i).sectionPieces (i ⁻¹ᵁ U.1)) n).comp
      ((affineSectionsEquiv i U hU).equiv n).toAddMonoidHom)
    ((congrArg (DirectSum.of ((conormalSheafGradedAlgebra i).sectionPieces (i ⁻¹ᵁ U.1)) 0)
      (affineSectionsEquiv i U hU).map_one).trans (DirectSum.one_def _).symm)
    (fun {n m} a b =>
      (congrArg (DirectSum.of ((conormalSheafGradedAlgebra i).sectionPieces (i ⁻¹ᵁ U.1)) (n + m))
        ((affineSectionsEquiv i U hU).map_mul n m a b)).trans (DirectSum.of_mul_of _ _).symm)

/-- On the degree-`n` summand, `gradedSectionRingHom` is the degree-`n` identification. -/
theorem gradedSectionRingHom_of (n : ℕ)
    (x : AssociatedGraded.piece (M := Γ(X, U)) (chartIdeal i U) n) :
    gradedSectionRingHom i U hU
        (DirectSum.of (fun k => AssociatedGraded.piece (M := Γ(X, U)) (chartIdeal i U) k) n x) =
      DirectSum.of ((conormalSheafGradedAlgebra i).sectionPieces (i ⁻¹ᵁ U.1)) n
        ((affineSectionsEquiv i U hU).equiv n x) :=
  DirectSum.toSemiring_of _ _ _ n x

/-- The class of `a ∈ Iⁿ` goes to the homogeneous section of degree `n` that it names. -/
theorem gradedSectionRingHom_classOfPow (n : ℕ) (a : ↥(chartIdeal i U ^ n)) :
    gradedSectionRingHom i U hU (AssociatedGraded.classOfPow (chartIdeal i U) n a) =
      DirectSum.of ((conormalSheafGradedAlgebra i).sectionPieces (i ⁻¹ᵁ U.1)) n
        ((conormalAlgebra i).localMap U hU n a) :=
  (gradedSectionRingHom_of i U hU n _).trans
    (congrArg _ ((affineSectionsEquiv i U hU).map_mk n _))

/-- `gradedSectionRingHom` is the degreewise identification, summand by summand. -/
theorem gradedSectionRingHom_apply_eq (z : AssociatedGraded.gradedRing (chartIdeal i U)) :
    gradedSectionRingHom i U hU z =
      DFinsupp.mapRange.addEquiv (fun n => (affineSectionsEquiv i U hU).equiv n) z := by
  induction z using DirectSum.induction_on with
  | zero => exact (map_zero (gradedSectionRingHom i U hU)).trans (map_zero _).symm
  | of n x =>
      rw [gradedSectionRingHom_of]
      exact (DFinsupp.mapRange_single
        (hf := fun k => ((affineSectionsEquiv i U hU).equiv k).map_zero)).symm
  | add z z' hz hz' =>
      exact (map_add (gradedSectionRingHom i U hU) z z').trans
        ((congrArg₂ (· + ·) hz hz').trans (map_add _ _ _).symm)

/-- `gradedSectionRingHom` is bijective. -/
theorem bijective_gradedSectionRingHom : Function.Bijective (gradedSectionRingHom i U hU) := by
  have h : ⇑(gradedSectionRingHom i U hU) =
      ⇑(DFinsupp.mapRange.addEquiv (fun n => (affineSectionsEquiv i U hU).equiv n)) :=
    funext (gradedSectionRingHom_apply_eq i U hU)
  rw [h]
  exact (DFinsupp.mapRange.addEquiv _).bijective

/-- **`Gr_I(R) ≅ ⨁ₙ 𝒞_{Z/X,n}(i⁻¹U)` as rings.** -/
def gradedSectionRingEquiv :
    AssociatedGraded.gradedRing (chartIdeal i U) ≃+*
      (conormalSheafGradedAlgebra i).sectionRing (i ⁻¹ᵁ U.1) :=
  RingEquiv.ofBijective _ (bijective_gradedSectionRingHom i U hU)

theorem gradedSectionRingEquiv_apply (z : AssociatedGraded.gradedRing (chartIdeal i U)) :
    gradedSectionRingEquiv i U hU z = gradedSectionRingHom i U hU z := rfl

/-- **`Gr_I(R) ≅ ⨁ₙ 𝒞_{Z/X,n}(i⁻¹U)` is graded.** -/
def gradedSectionRingGradedHom :
    AssociatedGraded.grading (chartIdeal i U) →+*ᵍ
      (conormalSheafGradedAlgebra i).grading (i ⁻¹ᵁ U.1) where
  toRingHom := gradedSectionRingHom i U hU
  map_mem {n x} hx := by
    obtain ⟨y, rfl⟩ := hx
    exact ⟨_, (gradedSectionRingHom_of i U hU n y).symm⟩

theorem gradedSectionRingGradedHom_apply (z : AssociatedGraded.gradedRing (chartIdeal i U)) :
    gradedSectionRingGradedHom i U hU z = gradedSectionRingHom i U hU z := rfl

/-- **On degree-zero classes the identification is the structure map**: the class of
`r ∈ Γ(X, U)` in degree zero goes to the image of `r` under `Γ(X, U) ⟶ Γ(Z, i⁻¹U)` followed by
the structure map of the conormal algebra. -/
theorem gradedSectionRingHom_gradeZero (r : Γ(X, U)) :
    gradedSectionRingHom i U hU
        (DirectSum.of (fun k => AssociatedGraded.piece (M := Γ(X, U)) (chartIdeal i U) k) 0
          (AssociatedGraded.gradeZeroMk (chartIdeal i U) r)) =
      (conormalSheafGradedAlgebra i).strHom (i ⁻¹ᵁ U.1) ((i.app U).hom r) := by
  rw [gradedSectionRingHom_of, SheafGradedAlgebra.strHom_apply]
  congr 1
  have hmk : AssociatedGraded.gradeZeroMk (chartIdeal i U) r =
      r • (GradedMonoid.GOne.one :
        AssociatedGraded.piece (M := Γ(X, U)) (chartIdeal i U) 0) :=
    congrArg (AssociatedGraded.mk (chartIdeal i U) 0) (Subtype.ext (mul_one r).symm)
  rw [hmk, (affineSectionsEquiv i U hU).map_smul]
  exact congrArg (fun y => (show Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ U.1)) from
    (i.app U).hom r) • y) (affineSectionsEquiv i U hU).map_one

/-- **The identification commutes with restriction to a smaller chart**, on classes. -/
theorem gradedSectionRingHom_restrict_classOfPow (V : X.affineOpens)
    (hV : IsClosedImmersion (i.resLE V.1 (i ⁻¹ᵁ V.1) le_rfl)) (hVU : V.1 ≤ U.1) (n : ℕ)
    (a : ↥(chartIdeal i U ^ n)) :
    (conormalSheafGradedAlgebra i).resRingHom (i.preimage_mono hVU)
        (gradedSectionRingHom i U hU (AssociatedGraded.classOfPow (chartIdeal i U) n a)) =
      gradedSectionRingHom i V hV (AssociatedGraded.classOfPow (chartIdeal i V) n
        ⟨X.presheaf.map (homOfLE hVU).op (a : Γ(X, U)),
          map_mem_chartIdeal_pow i hVU n a.2⟩) := by
  rw [gradedSectionRingHom_classOfPow, gradedSectionRingHom_classOfPow]
  exact ((conormalSheafGradedAlgebra i).resRingHom_of _ _).trans (congrArg _
    ((conormalAlgebra i).localMap_naturality U V hVU (i.preimage_mono hVU) hU hV n a _ rfl))

/-- **The identification commutes with restriction to a smaller chart.** -/
theorem gradedSectionRingHom_restrict (V : X.affineOpens)
    (hV : IsClosedImmersion (i.resLE V.1 (i ⁻¹ᵁ V.1) le_rfl)) (hVU : V.1 ≤ U.1)
    (z : AssociatedGraded.gradedRing (chartIdeal i U)) :
    (conormalSheafGradedAlgebra i).resRingHom (i.preimage_mono hVU)
        (gradedSectionRingHom i U hU z) =
      gradedSectionRingHom i V hV
        (AssociatedGraded.gradedRingMapOfRingHom (X.presheaf.map (homOfLE hVU).op).hom
          (map_chartIdeal_le i hVU) z) := by
  induction z using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | of n x =>
      induction x using Submodule.Quotient.induction_on with
      | _ a =>
        have ha : (a : Γ(X, U)) ∈ chartIdeal i U ^ n := by simpa using a.2
        exact (gradedSectionRingHom_restrict_classOfPow i U hU V hV hVU n ⟨a, ha⟩).trans
          (congrArg _ (AssociatedGraded.gradedRingMapOfRingHom_of
            (X.presheaf.map (homOfLE hVU).op).hom
            (map_chartIdeal_le i hVU) n (Submodule.Quotient.mk a)).symm)

end Stacks.Conormal

end
