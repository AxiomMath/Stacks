module

public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.PartialDerivative
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Comparison

/-!
# The coordinate derivatives annihilate the functions pulled back from the base

Let `R` be a commutative ring, grade `S = R[T₀, …, Tₙ]` by total degree and write `X = Proj S`
for projective `n`-space over `R`, with structure morphism `f : X ⟶ Spec R`. A section of
`𝒪_{Spec R}` pulls back along `f` to a section of `𝒪_X` which is locally a fraction of two
*constant* polynomials, so every coordinate derivative `∂/∂Tⱼ` kills it. This file proves that and
packages `∂/∂Tⱼ` as a derivation of `𝒪_X` relative to `f⁻¹ 𝒪_{Spec R}`, which is the form the
Euler sequence needs.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjEulerSequence.pderivSheafDerivation`: the `j`-th coordinate
  derivative as a derivation of `𝒪_X` with values in `𝒪_X(-1)`, relative to the structural map
  `f⁻¹ 𝒪_{Spec R} ⟶ 𝒪_X`.

## Main results

* `Stacks.AlgebraicGeometry.ProjEulerSequence.toSpecZero_appTop_val`: the global sections of the
  structure morphism `Proj 𝒜 ⟶ Spec 𝒜₀` of an arbitrary graded ring. A degree-zero element `z`
  pulls back to the section whose value at every point is `z / 1`.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.projToSpecCoeff_appTop_val`: the same for
  `Proj R[T] ⟶ Spec R`; a coefficient `r` pulls back to the section with value `C r / 1`
  everywhere.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.pderivApp_app_eq_zero`: `∂ⱼ` annihilates the
  pullback of every local section of `𝒪_{Spec R}`.

## Implementation notes

The description of the global sections of `AlgebraicGeometry.Proj.toSpecZero` is not in Mathlib,
so it is proved here, for an arbitrary graded ring rather than only for a polynomial ring. The
structure morphism is built from `AlgebraicGeometry.Proj.basicOpenToSpec` at the element `1`,
whose standard open is everything, pre-composed with two isomorphisms that undo the passage to
an open subscheme. Composing on the left with the inclusion of that standard open cancels both
isomorphisms, which turns Mathlib's `AlgebraicGeometry.Proj.basicOpenToSpec_app_top` into a
statement about `AlgebraicGeometry.Proj.toSpecZero` up to restriction maps — and restriction of
a section of the structure sheaf of `Proj` is literal restriction of a function, so the
restriction maps disappear as soon as the identity is evaluated at a point.

Vanishing of `∂ⱼ` on a pulled-back section is a pointwise statement, so it is enough to produce,
at each point `x` of `X`, a localization `A` of `R` and a ring homomorphism `A → S_{(x)}`
carrying constants to constants whose image contains the value of the section: this is
`Stacks.AlgebraicGeometry.ProjEulerSequence.pderivFiber_val_eq_zero_of_isLocalization`. Shrinking
the open set of `Spec R` to a standard open `D(t)` containing the image of `x` makes
`A = Γ(Spec R, D(t))`, which is the localization of `R` at the powers of `t`, and the
homomorphism is `f^♯` followed by evaluation at `x`. No stalk is needed.

## References

* [Stacks Project, Tag 0FMH](https://stacks.math.columbia.edu/tag/0FMH)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry HomogeneousLocalization
open AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace Stacks.AlgebraicGeometry.ProjEulerSequence

universe u

section GradedRing

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

attribute [local instance] ProjectiveSpectrum.isPrime

/-- The homogeneous ideal of a point of `Proj 𝒜` is a prime ideal. Mathlib's
`AlgebraicGeometry.ProjectiveSpectrum.isPrime` is not an instance at this spelling, so instance
search needs this one. -/
instance isPrime_toIdeal_of_point (x : ProjectiveSpectrum.top 𝒜) :
    x.asHomogeneousIdeal.toIdeal.IsPrime :=
  x.isPrime

/-- **The structure morphism of `Proj 𝒜` read on the standard open of `1`.** That standard open
is all of `Proj 𝒜`, and there the structure morphism `Proj 𝒜 ⟶ Spec 𝒜₀` is `Spec` of the
inclusion of the degree-zero part into the degree-zero localization at the powers of `1`. -/
theorem ι_basicOpen_one_comp_toSpecZero :
    (Proj.basicOpen 𝒜 1).ι ≫ Proj.toSpecZero 𝒜 =
      Proj.basicOpenToSpec 𝒜 1 ≫
        Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers (1 : A)))) := by
  have key : (Proj.basicOpen 𝒜 1).ι ≫
      (AlgebraicGeometry.Proj 𝒜).topIso.inv ≫
        ((AlgebraicGeometry.Proj 𝒜).isoOfEq (Proj.basicOpen_one 𝒜)).inv = 𝟙 _ := by
    rw [← Scheme.isoOfEq_hom_ι (AlgebraicGeometry.Proj 𝒜) (Proj.basicOpen_one 𝒜), Category.assoc,
      Scheme.ι_toIso_inv_assoc, Iso.hom_inv_id]
  have hsplit : (Proj.basicOpen 𝒜 1).ι ≫ Proj.toSpecZero 𝒜 =
      ((Proj.basicOpen 𝒜 1).ι ≫ (AlgebraicGeometry.Proj 𝒜).topIso.inv ≫
          ((AlgebraicGeometry.Proj 𝒜).isoOfEq (Proj.basicOpen_one 𝒜)).inv) ≫
        (Proj.basicOpenToSpec 𝒜 1 ≫
          Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers (1 : A))))) := by
    rw [Proj.toSpecZero]
    simp only [Category.assoc]
  rw [hsplit, key, Category.id_comp]

/-- **The global sections of the structure morphism `Proj 𝒜 ⟶ Spec 𝒜₀`.** A degree-zero element
`z` of `𝒜` pulls back to the global section of `𝒪_{Proj 𝒜}` whose value at every homogeneous
prime is the fraction `z / 1`. -/
theorem toSpecZero_appTop_val (z : 𝒜 0) (x : ProjectiveSpectrum.top 𝒜) :
    HomogeneousLocalization.val
        (((Proj.toSpecZero 𝒜).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv z)).1 ⟨x, trivial⟩) =
      algebraMap A (Localization x.asHomogeneousIdeal.toIdeal.primeCompl) (z : A) := by
  have h := Scheme.Hom.congr_app (ι_basicOpen_one_comp_toSpecZero 𝒜) ⊤
  simp only [Scheme.Hom.comp_app, Scheme.Hom.preimage_top, Proj.basicOpenToSpec_app_top,
    Scheme.Opens.ι_appTop] at h
  have h' := congrArg (fun φ => (Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv ≫ φ) h
  simp only [Category.assoc, Scheme.ΓSpecIso_naturality_assoc, Iso.inv_hom_id_assoc] at h'
  have h2 := DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp h') z
  have hx : x ∈ (Proj.basicOpen 𝒜 1).ι ''ᵁ ⊤ := by
    rw [Scheme.Opens.ι_image_top, Proj.basicOpen_one]; trivial
  refine (congrArg HomogeneousLocalization.val
    (congrFun (congrArg Subtype.val h2) ⟨x, hx⟩)).trans ?_
  have hx' : x ∈ ProjectiveSpectrum.basicOpen 𝒜 (1 : A) := by
    rw [ProjectiveSpectrum.basicOpen_one]; trivial
  refine Eq.trans (ProjectiveSpectrum.Proj.awayToSection_apply 𝒜 1
      (fromZeroRingHom 𝒜 (Submonoid.powers (1 : A)) z) ⟨x, hx'⟩) ?_
  rw [show ((fromZeroRingHom 𝒜 (Submonoid.powers (1 : A))) z).val =
      algebraMap A (Localization (Submonoid.powers (1 : A))) (z : A) from by
    rw [← Localization.mk_one_eq_algebraMap]; rfl]
  exact IsLocalization.map_eq _ _

end GradedRing

section Polynomial

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The homogeneous ideal of a point of `Proj R[T]`, viewed as an ideal, is prime. -/
local instance (x : ProjectiveSpectrum.top (ProjPolyChart.polyGrading R n)) :
    x.asHomogeneousIdeal.toIdeal.IsPrime :=
  x.isPrime

/-- The identification of `R` with the degree-zero part of the total-degree grading, as it is
spelled in the structure morphism of projective space, sends `r` to the constant `C r`. -/
theorem coe_projZeroRingHom'_algebraMap (r : R) :
    (((GradedRing.projZeroRingHom' (ProjPolyChart.polyGrading R n)).comp
          (algebraMap R (MvPolynomial (Fin (n + 1)) R)) r :
        ProjPolyChart.polyGrading R n 0) : MvPolynomial (Fin (n + 1)) R) =
      MvPolynomial.C r := by
  rw [RingHom.comp_apply,
    show (algebraMap R (MvPolynomial (Fin (n + 1)) R)) r =
      ((algebraMap R (ProjPolyChart.polyGrading R n 0) r :
        ProjPolyChart.polyGrading R n 0) : MvPolynomial (Fin (n + 1)) R) from by
      rw [SetLike.GradeZero.coe_algebraMap],
    GradedRing.projZeroRingHom'_apply_coe, SetLike.GradeZero.coe_algebraMap]
  simp [MvPolynomial.algebraMap_eq]

/-- **The structure morphism of projective space on global sections.** Composed with the
identification of `R` with the global sections of `Spec R`, it is the identification of `R` with
the degree-zero part of the grading followed by the structure morphism of `Proj`. -/
theorem ΓSpecIso_inv_comp_projToSpecCoeff_appTop :
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (ProjPolyChart.projToSpecCoeff R n).appTop =
      CommRingCat.ofHom ((GradedRing.projZeroRingHom' (ProjPolyChart.polyGrading R n)).comp
          (algebraMap R (MvPolynomial (Fin (n + 1)) R))) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (ProjPolyChart.polyGrading R n 0))).inv ≫
          (Proj.toSpecZero (ProjPolyChart.polyGrading R n)).appTop := by
  rw [Scheme.ΓSpecIso_inv_naturality_assoc, ProjPolyChart.projToSpecCoeff]
  simp only [Scheme.Hom.appTop, Scheme.Hom.comp_app, Scheme.Hom.preimage_top]

/-- **The global sections of the structure morphism of projective space.** A coefficient `r : R`
pulls back along `Proj R[T] ⟶ Spec R` to the global section of `𝒪_X` whose value at every point
is the fraction `C r / 1`. -/
theorem projToSpecCoeff_appTop_val (r : R)
    (x : ProjectiveSpectrum.top (ProjPolyChart.polyGrading R n)) :
    HomogeneousLocalization.val
        (((ProjPolyChart.projToSpecCoeff R n).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)).1 ⟨x, trivial⟩) =
      algebraMap (MvPolynomial (Fin (n + 1)) R)
        (Localization x.asHomogeneousIdeal.toIdeal.primeCompl) (MvPolynomial.C r) := by
  have h := DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp
    (ΓSpecIso_inv_comp_projToSpecCoeff_appTop R n)) r
  rw [← coe_projZeroRingHom'_algebraMap R n r]
  refine Eq.trans (congrArg
    (fun s : Γ(AlgebraicGeometry.Proj (ProjPolyChart.polyGrading R n), ⊤) =>
      HomogeneousLocalization.val (s.1 ⟨x, trivial⟩)) h) ?_
  exact toSpecZero_appTop_val (ProjPolyChart.polyGrading R n) _ x

section Assembly

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-- Evaluating a section of the structure sheaf of `Proj R[T]` at a point of its domain is a ring
homomorphism to the degree-zero homogeneous localization there: the sections form a subring of
the product of the fibres. -/
def sectionEval (U : Opens (ProjectiveSpectrum.top (ProjPolyChart.polyGrading R n)))
    (x : ProjectiveSpectrum.top (ProjPolyChart.polyGrading R n)) (hx : x ∈ U) :
    (ProjectiveSpectrum.Proj.structureSheaf
        (ProjPolyChart.polyGrading R n)).obj.obj (op U) →+*
      HomogeneousLocalization.AtPrime (ProjPolyChart.polyGrading R n)
        x.asHomogeneousIdeal.toIdeal where
  toFun a := a.1 ⟨x, hx⟩
  map_one' := Proj.one_apply _ ⟨x, hx⟩
  map_mul' a b := Proj.mul_apply _ a b ⟨x, hx⟩
  map_zero' := Proj.zero_apply _ ⟨x, hx⟩
  map_add' a b := Proj.add_apply _ a b ⟨x, hx⟩

/-- **The pullback of a constant has value `C r / 1` at every point.** Over any open set of
`Spec R` the image under `f^♯` of the constant function `r` is the constant fraction `C r / 1`,
because that constant is the restriction of a global constant. -/
theorem projToSpecCoeff_app_algebraMap_val (V : (Spec (CommRingCat.of R)).Opens) (r : R)
    (x : ProjectiveSpectrum.top (ProjPolyChart.polyGrading R n))
    (hx : x ∈ ProjPolyChart.projToSpecCoeff R n ⁻¹ᵁ V) :
    HomogeneousLocalization.val
        ((((ProjPolyChart.projToSpecCoeff R n).app V).hom
          (algebraMap R ((Spec.structureSheaf R).presheaf.obj (op V)) r)).1 ⟨x, hx⟩) =
      algebraMap (MvPolynomial (Fin (n + 1)) R)
        (Localization x.asHomogeneousIdeal.toIdeal.primeCompl) (MvPolynomial.C r) := by
  have hconst : (algebraMap R ((Spec.structureSheaf R).presheaf.obj (op V)) r) =
      ((Spec (CommRingCat.of R)).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) :=
    DFunLike.congr_fun
      (CommRingCat.hom_ext_iff.mp (Scheme.toOpen_eq (CommRingCat.of R) V)) r
  rw [hconst, NatTrans.naturality_apply (ProjPolyChart.projToSpecCoeff R n).c
    (homOfLE (le_top : V ≤ ⊤)).op ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)]
  exact projToSpecCoeff_appTop_val R n r x

/-- **`∂ⱼ` annihilates every section pulled back from the base.** A section of `𝒪_{Spec R}` over
an open `W` is, on the standard open `D(t)` around the image of a given point, an element of the
localization of `R` at the powers of `t`; its pullback therefore lies in the image of a ring
homomorphism from that localization carrying constants to constants, which `∂ⱼ` kills. -/
theorem pderivApp_app_eq_zero (j : Fin (n + 1)) (W : (Spec (CommRingCat.of R)).Opens)
    (b : Γ(Spec (CommRingCat.of R), W)) :
    pderivApp R n j (ProjPolyChart.projToSpecCoeff R n ⁻¹ᵁ W)
      (((ProjPolyChart.projToSpecCoeff R n).app W).hom b) = 0 := by
  refine (pderivApp_eq_zero_iff R n j _ _).mpr fun x => ?_
  obtain ⟨V, ⟨t, rfl⟩, hpV, hVW⟩ :=
    Opens.isBasis_iff_nbhd.mp PrimeSpectrum.isBasis_basic_opens x.2
  have hxV : x.1 ∈ ProjPolyChart.projToSpecCoeff R n ⁻¹ᵁ PrimeSpectrum.basicOpen t := hpV
  have hval : (((ProjPolyChart.projToSpecCoeff R n).app W).hom b).1 x =
      (((ProjPolyChart.projToSpecCoeff R n).app (PrimeSpectrum.basicOpen t)).hom
        (((Spec (CommRingCat.of R)).presheaf.map (homOfLE hVW).op).hom b)).1 ⟨x.1, hxV⟩ :=
    (congrFun (congrArg Subtype.val (NatTrans.naturality_apply
      (ProjPolyChart.projToSpecCoeff R n).c (homOfLE hVW).op b)) ⟨x.1, hxV⟩).symm
  rw [hval]
  exact pderivFiber_val_eq_zero_of_isLocalization R n j x.1
    (A := ((Spec.structureSheaf R).presheaf.obj (op (PrimeSpectrum.basicOpen t))))
    (Submonoid.powers t)
    ((sectionEval R n _ x.1 hxV).comp
      ((ProjPolyChart.projToSpecCoeff R n).app (PrimeSpectrum.basicOpen t)).hom)
    (fun r => projToSpecCoeff_app_algebraMap_val R n (PrimeSpectrum.basicOpen t) r x.1 hxV)
    (((Spec (CommRingCat.of R)).presheaf.map (homOfLE hVW).op).hom b)

/-- **`∂/∂Tⱼ` as a derivation of `𝒪_X` relative to the inverse image of `𝒪_{Spec R}`.** The
coordinate derivative kills everything pulled back along the structure morphism of projective
`n`-space, so the derivation `Stacks.AlgebraicGeometry.ProjEulerSequence.pderivDerivation`,
which is relative only to the constants `ℤ`, is in fact relative to `f⁻¹ 𝒪_{Spec R}`. -/
def pderivSheafDerivation (j : Fin (n + 1)) :
    AlgebraicGeometry.SheafOfModules.SheafDerivation
      (AlgebraicGeometry.inverseImageStructureMap (ProjPolyChart.projToSpecCoeff R n))
      (twistMinusOne R n) :=
  AlgebraicGeometry.SheafOfModules.ofComorphism (ProjPolyChart.projToSpecCoeff R n)
    (pderivDerivation R n j) (fun W b => pderivApp_app_eq_zero R n j W b)

end Assembly

end Polynomial

end Stacks.AlgebraicGeometry.ProjEulerSequence

end
