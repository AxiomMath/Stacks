module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassFamily
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuliEllipticCurvesBaseChange
public import StacksFrontier.AlgebraicGeometry.Blowup.ProjBaseChangeGlobal
public import StacksFrontier.AlgebraicGeometry.Blowup.RelativeProj
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceSections.GradedNaturality
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceSections.UnitRescale
public import StacksFrontier.AlgebraicGeometry.ProjGlobalSectionsAppTop.Consumers
public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.BaseChange
public import StacksFrontier.AlgebraicGeometry.HomogeneousQuotient.Defs
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Isomorphisms of Weierstrass plane cubics: coordinate changes and base change

For a Weierstrass equation `C` over a ring `R`, let `E_C ⊂ P²_R` be its plane cubic with the
projection `f : E_C → Spec R` and the section `(0 : 1 : 0)`, the pointed family
`AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.familyOf C`. This file constructs the two
isomorphisms of such families that the moduli stack of elliptic curves is built from: the one
induced by a coordinate change `γ = (u, r, s, t)`, and the identification of the base change of
`E_C` along `Spec S → Spec R` with the plane cubic of the base-changed equation. It also proves
that the first is compatible with the second.

## Main definitions

* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.changeIso`: the isomorphism of pointed
  families `E_{γ • C} ≅ E_C` over `Spec R` induced by the coordinate change `γ`, the projective
  substitution `x ↦ u²x + rz`, `y ↦ u³y + u²sx + tz`, `z ↦ z`.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.familyOfMapIso`: for `φ : R →+* S`, the
  isomorphism of pointed families over `Spec S` from the pullback of `E_C` along
  `Spec S → Spec R` to `E_{C.map φ}`.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.changeMap` and
  `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.mapMap`: the underlying morphisms of total
  spaces `E_{γ • C} ⟶ E_C` and `E_{C.map φ} ⟶ E_C`.

## Main results

* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.substOf_cubicOf`: the substitution of `γ`
  carries the cubic of `C` to `u⁶` times the cubic of `γ • C`.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.isPullback_mapMap`: the square formed by
  `E_{C.map φ} ⟶ E_C`, the two projections and `Spec S ⟶ Spec R` is cartesian.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.mapMap_changeMap` and
  `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.familyOfMapIso_changeIso`: the coordinate
  change commutes with base change along `ψ : R →+* S`.

## Implementation notes

Both isomorphisms are `AlgebraicGeometry.Proj.map` of graded ring homomorphisms between
homogeneous coordinate rings `R[x, y, z]/(F)`, built by `coordHom` from a graded homomorphism of
polynomial rings that carries one cubic into the ideal of the other. For a coordinate change the
inverse is induced by `γ⁻¹`, so `Proj.map` is an isomorphism by functoriality. That it fixes
`(0 : 1 : 0)` is naturality of `AlgebraicGeometry.Proj.fromOfGlobalSections` together with its
invariance under rescaling a ring map degreewise by a unit: the substitution sends `(0 : 1 : 0)`
to `(0 : u³ : 0)`.

Base change goes through `Stacks.ProjBaseChange.isPullback_map_of_baseChange`, which asks for a
grading by `R`-submodules; the grading `gradingOf C` of `WeierstrassFamily.lean` is by additive
subgroups, so the comparison passes through `moduleGradingOf C`, the same pieces as submodules,
and `moduleGradingIso C` identifies the two `Proj`s. The graded isomorphism
`S ⊗[R] R[x, y, z]/(F_C) ≅ S[x, y, z]/(F_{C.map φ})` is `baseChangeEquiv`.

The two Weierstrass equations `(γ • C).map ψ` and `γ.map ψ • C.map ψ` are equal
(`WeierstrassCurve.map_variableChange`) but not definitionally, so the naturality statements
compose with `eqToHom` of that equality transported to the plane cubics. The naturality is stated
on total spaces: in `familyOfMapIso_changeIso`, the base change of `changeIso γ C` read through
`familyOfMapIso` on both sides is `changeIso (γ.map ψ) (C.map ψ)` preceded by that `eqToHom`.

## References

* [Stacks Project, Tag 072S](https://stacks.math.columbia.edu/tag/072S)
* [Stacks Project, Tag 072T](https://stacks.math.columbia.edu/tag/072T)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
-/

@[expose] public noncomputable section

open CategoryTheory MvPolynomial TensorProduct

universe u

namespace AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R]

/-! ### The substitution of a coordinate change -/

/-- The `R`-algebra endomorphism of `R[x, y, z]` given by the coordinate change `γ = (u, r, s, t)`:
`x ↦ u²x + rz`, `y ↦ u³y + u²sx + tz`, `z ↦ z`. -/
def substOf (γ : WeierstrassCurve.VariableChange R) :
    MvPolynomial (Fin 3) R →ₐ[R] MvPolynomial (Fin 3) R :=
  aeval ![MvPolynomial.C ((γ.u : R) ^ 2) * X 0 + MvPolynomial.C γ.r * X 2,
    MvPolynomial.C ((γ.u : R) ^ 3) * X 1 + MvPolynomial.C ((γ.u : R) ^ 2 * γ.s) * X 0 +
      MvPolynomial.C γ.t * X 2, X 2]

/-- The coordinate change `γ` carries the Weierstrass cubic of `C` to `u⁶` times the Weierstrass
cubic of `γ • C`. -/
theorem substOf_cubicOf (γ : WeierstrassCurve.VariableChange R) (C : WeierstrassCurve R) :
    substOf γ (cubicOf C) = MvPolynomial.C ((γ.u : R) ^ 6) * cubicOf (γ • C) := by
  have hu : (γ.u : R) * (γ.u⁻¹ : Rˣ) = 1 := γ.u.mul_inv
  have h1 : C.a₁ = γ.u * (γ • C).a₁ - 2 * γ.s := by
    rw [WeierstrassCurve.variableChange_a₁]
    linear_combination -(C.a₁ + 2 * γ.s) * hu
  have h2 : C.a₂ = γ.u ^ 2 * (γ • C).a₂ + γ.s * C.a₁ - 3 * γ.r + γ.s ^ 2 := by
    rw [WeierstrassCurve.variableChange_a₂]
    linear_combination -(C.a₂ - γ.s * C.a₁ + 3 * γ.r - γ.s ^ 2) * pow_mul_pow_eq_one 2 hu
  have h3 : C.a₃ = γ.u ^ 3 * (γ • C).a₃ - γ.r * C.a₁ - 2 * γ.t := by
    rw [WeierstrassCurve.variableChange_a₃]
    linear_combination -(C.a₃ + γ.r * C.a₁ + 2 * γ.t) * pow_mul_pow_eq_one 3 hu
  have h4 : C.a₄ = γ.u ^ 4 * (γ • C).a₄ + γ.s * C.a₃ - 2 * γ.r * C.a₂ +
      (γ.t + γ.r * γ.s) * C.a₁ - 3 * γ.r ^ 2 + 2 * γ.s * γ.t := by
    rw [WeierstrassCurve.variableChange_a₄]
    linear_combination -(C.a₄ - γ.s * C.a₃ + 2 * γ.r * C.a₂ - (γ.t + γ.r * γ.s) * C.a₁ +
      3 * γ.r ^ 2 - 2 * γ.s * γ.t) * pow_mul_pow_eq_one 4 hu
  have h6 : C.a₆ = γ.u ^ 6 * (γ • C).a₆ - γ.r * C.a₄ - γ.r ^ 2 * C.a₂ - γ.r ^ 3 +
      γ.t * C.a₃ + γ.t ^ 2 + γ.r * γ.t * C.a₁ := by
    rw [WeierstrassCurve.variableChange_a₆]
    linear_combination -(C.a₆ + γ.r * C.a₄ + γ.r ^ 2 * C.a₂ + γ.r ^ 3 - γ.t * C.a₃ - γ.t ^ 2 -
      γ.r * γ.t * C.a₁) * pow_mul_pow_eq_one 6 hu
  simp only [cubicOf, WeierstrassCurve.Projective.polynomial, substOf, map_add, map_sub, map_mul,
    map_pow, aeval_X, aeval_C]
  simp only [WeierstrassCurve.toProjective]
  rw [h6, h4, h3, h2, h1]
  simp only [Matrix.cons_val, map_add, map_sub, map_mul, map_pow, map_ofNat, algebraMap_eq]
  ring

/-- The coordinate change preserves homogeneity and degree: it sends each variable to a linear
form. -/
theorem isHomogeneous_substOf (γ : WeierstrassCurve.VariableChange R) {n : ℕ}
    {p : MvPolynomial (Fin 3) R} (hp : p.IsHomogeneous n) : (substOf γ p).IsHomogeneous n := by
  have h := hp.aeval (n := 1) (τ := Fin 3)
    (![MvPolynomial.C ((γ.u : R) ^ 2) * X 0 + MvPolynomial.C γ.r * X 2,
      MvPolynomial.C ((γ.u : R) ^ 3) * X 1 + MvPolynomial.C ((γ.u : R) ^ 2 * γ.s) * X 0 +
        MvPolynomial.C γ.t * X 2, X 2]) fun i => by
    fin_cases i
    · exact (isHomogeneous_C_mul_X _ _).add (isHomogeneous_C_mul_X _ _)
    · exact ((isHomogeneous_C_mul_X _ _).add (isHomogeneous_C_mul_X _ _)).add
        (isHomogeneous_C_mul_X _ _)
    · exact isHomogeneous_X _ _
  rw [one_mul] at h
  exact h

/-- The substitution of `γ⁻¹` undoes the substitution of `γ`. -/
theorem substOf_inv_comp (γ : WeierstrassCurve.VariableChange R) :
    (substOf γ⁻¹).comp (substOf γ) = AlgHom.id R (MvPolynomial (Fin 3) R) := by
  have hU : MvPolynomial.C (γ.u : R) * MvPolynomial.C ((γ.u⁻¹ : Rˣ) : R) =
      (1 : MvPolynomial (Fin 3) R) := by
    rw [← map_mul, γ.u.mul_inv, map_one]
  refine MvPolynomial.algHom_ext fun i => ?_
  fin_cases i <;>
    simp [substOf, WeierstrassCurve.VariableChange.inv_def]
  · linear_combination (X 0 - MvPolynomial.C γ.r * X 2) * pow_mul_pow_eq_one 2 hU
  · linear_combination (X 1 + (MvPolynomial.C γ.r * MvPolynomial.C γ.s - MvPolynomial.C γ.t) *
      X 2) * pow_mul_pow_eq_one 3 hU - MvPolynomial.C γ.s * X 0 *
      (pow_mul_pow_eq_one 3 hU - pow_mul_pow_eq_one 2 hU) -
      MvPolynomial.C γ.r * MvPolynomial.C γ.s * X 2 * pow_mul_pow_eq_one 2 hU

/-- The substitution of `γ` undoes the substitution of `γ⁻¹`. -/
theorem substOf_comp_inv (γ : WeierstrassCurve.VariableChange R) :
    (substOf γ).comp (substOf γ⁻¹) = AlgHom.id R (MvPolynomial (Fin 3) R) := by
  simpa only [inv_inv] using substOf_inv_comp γ⁻¹

/-- The substitution `substOf γ` as a graded ring endomorphism of `R[x, y, z]` with its grading by
total degree. -/
def substGradedHom (γ : WeierstrassCurve.VariableChange R) :
    homogeneousSubmodule (Fin 3) R →+*ᵍ homogeneousSubmodule (Fin 3) R where
  __ := (substOf γ).toRingHom
  map_mem {_ _} hx := isHomogeneous_substOf γ hx

/-! ### Homomorphisms of homogeneous coordinate rings -/

/-- A graded ring homomorphism with a right inverse satisfies the hypothesis of
`AlgebraicGeometry.Proj.map`. -/
private theorem irrelevant_le_map_of_comp_eq_id {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜)
    (hfg : f.comp g = GradedRingHom.id ℬ) :
    HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f :=
  Proj.irrelevant_le_map_of_surjective f fun x => ⟨g x, GradedRingHom.congr_fun hfg x⟩

section CoordHom

variable {S : Type u} [CommRing S] {C : WeierstrassCurve R} {C' : WeierstrassCurve S}

/-- The graded ring homomorphism `R[x, y, z]/(F_C) → S[x, y, z]/(F_{C'})` induced by a graded ring
homomorphism `σ : R[x, y, z] → S[x, y, z]` that sends the cubic of `C` into the ideal of the cubic
of `C'`. -/
def coordHom (σ : homogeneousSubmodule (Fin 3) R →+*ᵍ homogeneousSubmodule (Fin 3) S)
    (hσ : σ (cubicOf C) ∈ (cubicIdealOf C').toIdeal) : gradingOf C →+*ᵍ gradingOf C' where
  __ := Ideal.quotientMap (cubicIdealOf C').toIdeal σ.toRingHom <| by
    change Ideal.span {cubicOf C} ≤ _
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hσ
  map_mem {_ x} hx := by
    obtain ⟨a, ha, rfl⟩ := (Stacks.HomogeneousIdeal.mem_quotientGrading_iff _ x).mp hx
    exact Stacks.HomogeneousIdeal.mk_mem_quotientGrading _ (σ.map_mem ha)

/-- `coordHom σ hσ` sends the class of `p` to the class of `σ p`. -/
theorem coordHom_mk (σ : homogeneousSubmodule (Fin 3) R →+*ᵍ homogeneousSubmodule (Fin 3) S)
    (hσ : σ (cubicOf C) ∈ (cubicIdealOf C').toIdeal) (p : MvPolynomial (Fin 3) R) :
    coordHom σ hσ (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (σ p) := rfl

/-- If `σ` sends each constant `a` to the constant `φ a`, then in degree zero `coordHom σ hσ` is
`φ`, read through the identifications of the degree-zero parts with `R` and `S`. -/
theorem gradedZeroRingHom_coordHom_comp
    (σ : homogeneousSubmodule (Fin 3) R →+*ᵍ homogeneousSubmodule (Fin 3) S)
    (hσ : σ (cubicOf C) ∈ (cubicIdealOf C').toIdeal) (φ : R →+* S)
    (hφ : ∀ a, σ (MvPolynomial.C a) = MvPolynomial.C (φ a)) :
    (coordHom σ hσ).gradedZeroRingHom.comp (toGradingZeroOf C) =
      (toGradingZeroOf C').comp φ :=
  RingHom.ext fun a => Subtype.ext <| by
    show Ideal.Quotient.mk _ (σ (MvPolynomial.C a)) = Ideal.Quotient.mk _ (MvPolynomial.C (φ a))
    rw [hφ]

end CoordHom

/-! ### The coordinate-change isomorphism -/

/-- The substitution of `γ` sends the cubic of `C` into the ideal of the cubic of `γ • C`. -/
theorem substOf_cubicOf_mem (γ : WeierstrassCurve.VariableChange R) (C : WeierstrassCurve R) :
    substGradedHom γ (cubicOf C) ∈ (cubicIdealOf (γ • C)).toIdeal := by
  show substOf γ (cubicOf C) ∈ Ideal.span {cubicOf (γ • C)}
  rw [substOf_cubicOf]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)

/-- The substitution of `γ⁻¹` sends the cubic of `γ • C` into the ideal of the cubic of `C`. -/
theorem substOf_inv_cubicOf_mem (γ : WeierstrassCurve.VariableChange R) (C : WeierstrassCurve R) :
    substGradedHom γ⁻¹ (cubicOf (γ • C)) ∈ (cubicIdealOf C).toIdeal := by
  have h := substOf_cubicOf_mem γ⁻¹ (γ • C)
  rwa [inv_smul_smul] at h

/-- The coordinate change `γ` on homogeneous coordinate rings,
`R[x, y, z]/(F_C) → R[x, y, z]/(F_{γ • C})`, as a graded ring homomorphism. -/
def changeHom (γ : WeierstrassCurve.VariableChange R) (C : WeierstrassCurve R) :
    gradingOf C →+*ᵍ gradingOf (γ • C) :=
  coordHom (substGradedHom γ) (substOf_cubicOf_mem γ C)

/-- The inverse coordinate change `γ⁻¹` on homogeneous coordinate rings,
`R[x, y, z]/(F_{γ • C}) → R[x, y, z]/(F_C)`, as a graded ring homomorphism. -/
def changeInvHom (γ : WeierstrassCurve.VariableChange R) (C : WeierstrassCurve R) :
    gradingOf (γ • C) →+*ᵍ gradingOf C :=
  coordHom (substGradedHom γ⁻¹) (substOf_inv_cubicOf_mem γ C)

/-- `changeInvHom γ C` is a left inverse of `changeHom γ C`. -/
theorem changeInvHom_comp_changeHom (γ : WeierstrassCurve.VariableChange R)
    (C : WeierstrassCurve R) :
    (changeInvHom γ C).comp (changeHom γ C) = GradedRingHom.id (gradingOf C) :=
  GradedRingHom.ext fun x => by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    show Ideal.Quotient.mk _ (substOf γ⁻¹ (substOf γ p)) = Ideal.Quotient.mk _ p
    rw [← AlgHom.comp_apply, substOf_inv_comp, AlgHom.id_apply]

/-- `changeInvHom γ C` is a right inverse of `changeHom γ C`. -/
theorem changeHom_comp_changeInvHom (γ : WeierstrassCurve.VariableChange R)
    (C : WeierstrassCurve R) :
    (changeHom γ C).comp (changeInvHom γ C) = GradedRingHom.id (gradingOf (γ • C)) :=
  GradedRingHom.ext fun x => by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    show Ideal.Quotient.mk _ (substOf γ (substOf γ⁻¹ p)) = Ideal.Quotient.mk _ p
    rw [← AlgHom.comp_apply, substOf_comp_inv, AlgHom.id_apply]

/-- The irrelevant ideal of the target of `changeHom γ C` lies in the image of the irrelevant ideal
of its source, the hypothesis of `AlgebraicGeometry.Proj.map`. -/
theorem irrelevant_le_map_changeHom (γ : WeierstrassCurve.VariableChange R)
    (C : WeierstrassCurve R) :
    HomogeneousIdeal.irrelevant (gradingOf (γ • C)) ≤
      (HomogeneousIdeal.irrelevant (gradingOf C)).map (changeHom γ C) :=
  irrelevant_le_map_of_comp_eq_id _ _ (changeHom_comp_changeInvHom γ C)

/-- The irrelevant ideal of the target of `changeInvHom γ C` lies in the image of the irrelevant
ideal of its source, the hypothesis of `AlgebraicGeometry.Proj.map`. -/
theorem irrelevant_le_map_changeInvHom (γ : WeierstrassCurve.VariableChange R)
    (C : WeierstrassCurve R) :
    HomogeneousIdeal.irrelevant (gradingOf C) ≤
      (HomogeneousIdeal.irrelevant (gradingOf (γ • C))).map (changeInvHom γ C) :=
  irrelevant_le_map_of_comp_eq_id _ _ (changeInvHom_comp_changeHom γ C)

/-- The morphism `E_{γ • C} ⟶ E_C` of plane cubics induced by the coordinate change `γ`. -/
def changeMap (γ : WeierstrassCurve.VariableChange R) (C : WeierstrassCurve R) :
    projOf (γ • C) ⟶ projOf C :=
  Proj.map (changeHom γ C) (irrelevant_le_map_changeHom γ C)

/-- The morphism of plane cubics induced by a coordinate change is an isomorphism, with inverse
induced by `changeInvHom γ C`. -/
instance isIso_changeMap (γ : WeierstrassCurve.VariableChange R) (C : WeierstrassCurve R) :
    IsIso (changeMap γ C) :=
  Proj.isIso_map _ (irrelevant_le_map_changeInvHom γ C) (changeInvHom_comp_changeHom γ C)
    (changeHom_comp_changeInvHom γ C)

/-- The morphism of plane cubics induced by a coordinate change lies over `Spec R`. -/
theorem changeMap_projectionOf (γ : WeierstrassCurve.VariableChange R) (C : WeierstrassCurve R) :
    changeMap γ C ≫ projectionOf C = projectionOf (γ • C) := by
  show Proj.map (changeHom γ C) (irrelevant_le_map_changeHom γ C) ≫
      Proj.toSpecZero (gradingOf C) ≫ Spec.map (CommRingCat.ofHom (toGradingZeroOf C)) =
    Proj.toSpecZero (gradingOf (γ • C)) ≫ Spec.map (CommRingCat.ofHom (toGradingZeroOf (γ • C)))
  rw [Proj.map_toSpecZero_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, changeHom,
    gradedZeroRingHom_coordHom_comp _ _ (RingHom.id R) (fun a => (substOf γ).commutes a),
    RingHom.comp_id]

/-- Evaluating the substitution of `γ` at `(0 : 1 : 0)` is evaluating at `(0 : u³ : 0)`. -/
theorem aeval_substOf (γ : WeierstrassCurve.VariableChange R) (p : MvPolynomial (Fin 3) R) :
    aeval ![0, 1, 0] (substOf γ p) = aeval ![0, (γ.u : R) ^ 3, 0] p := by
  rw [← AlgHom.comp_apply]
  congr 1
  refine MvPolynomial.algHom_ext fun i => ?_
  fin_cases i <;> simp [substOf]

/-- On the class of a homogeneous polynomial `p` of degree `d`, evaluation at `(0 : 1 : 0)` after
`changeHom γ C` is `(u³)ᵈ` times evaluation at `(0 : 1 : 0)`. -/
theorem evalZeroOf_changeHom (γ : WeierstrassCurve.VariableChange R) (C : WeierstrassCurve R)
    {d : ℕ} {p : MvPolynomial (Fin 3) R} (hp : p.IsHomogeneous d) :
    evalZeroOf (γ • C) (changeHom γ C (Ideal.Quotient.mk _ p)) =
      ((γ.u : R) ^ 3) ^ d * evalZeroOf C (Ideal.Quotient.mk _ p) := by
  show aeval ![0, 1, 0] (substOf γ p) = ((γ.u : R) ^ 3) ^ d * aeval ![0, 1, 0] p
  have h : (![0, (γ.u : R) ^ 3, 0] : Fin 3 → R) = fun i => (γ.u : R) ^ 3 * ![0, 1, 0] i := by
    funext i
    fin_cases i <;> simp
  rw [aeval_substOf, h, aeval_def, aeval_def]
  exact Stacks.ProjGlobalSectionsAppTop.eval₂_of_isHomogeneous _ _ _ hp

/-- The morphism of plane cubics induced by a coordinate change carries the section `(0 : 1 : 0)`
of `E_{γ • C}` to the section `(0 : 1 : 0)` of `E_C`. -/
theorem zeroOf_changeMap (γ : WeierstrassCurve.VariableChange R) (C : WeierstrassCurve R) :
    zeroOf (γ • C) ≫ changeMap γ C = zeroOf C := by
  have hfφ : (HomogeneousIdeal.irrelevant (gradingOf C)).toIdeal.map
      ((evalZeroGlobalOf (γ • C)).comp (changeHom γ C).toRingHom) = ⊤ := by
    rw [← Ideal.map_map]
    refine top_unique ((map_irrelevant_eq_top_of (γ • C)).symm.le.trans (Ideal.map_mono ?_))
    exact irrelevant_le_map_changeHom γ C
  show Proj.fromOfGlobalSections (gradingOf (γ • C)) (evalZeroGlobalOf (γ • C))
      (map_irrelevant_eq_top_of (γ • C)) ≫
      Proj.map (changeHom γ C) (irrelevant_le_map_changeHom γ C) =
    Proj.fromOfGlobalSections (gradingOf C) (evalZeroGlobalOf C) (map_irrelevant_eq_top_of C)
  rw [Proj.fromOfGlobalSections_comp_map _ _ _ _ hfφ]
  refine (Proj.fromOfGlobalSections_congr_unit _ _ _
    (Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom (γ.u ^ 3)) ?_ _ _).symm
  intro d a ha
  obtain ⟨p, hp, rfl⟩ := (Stacks.HomogeneousIdeal.mem_quotientGrading_iff _ a).mp ha
  show (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      (evalZeroOf (γ • C) (changeHom γ C (Ideal.Quotient.mk _ p))) = _
  rw [evalZeroOf_changeHom γ C hp]
  simp [evalZeroGlobalOf]

/-- **The coordinate-change isomorphism of plane cubics.** A coordinate change `γ = (u, r, s, t)`
induces an isomorphism from the pointed family `(E_{γ • C}, f, (0 : 1 : 0))` over `Spec R` to the
pointed family `(E_C, f, (0 : 1 : 0))`; its morphism of total spaces is `changeMap γ C`. -/
def changeIso (γ : WeierstrassCurve.VariableChange R) (C : WeierstrassCurve R) :
    FamilyIso (familyOf (γ • C)) (familyOf C) where
  iso := @asIso _ _ _ _ (changeMap γ C) (isIso_changeMap γ C)
  iso_map := changeMap_projectionOf γ C
  zero_iso := zeroOf_changeMap γ C

/-! ### Change of coefficients -/

section Map

variable {S : Type u} [CommRing S]

/-- The Weierstrass cubic of `C.map φ` is the image of the Weierstrass cubic of `C` under
`MvPolynomial.map φ`. -/
theorem cubicOf_map (C : WeierstrassCurve R) (φ : R →+* S) :
    cubicOf (C.map φ) = MvPolynomial.map φ (cubicOf C) :=
  WeierstrassCurve.Projective.map_polynomial (W' := C.toProjective) φ

/-- `MvPolynomial.map φ` sends the cubic of `C` into the ideal of the cubic of `C.map φ`. -/
theorem map_cubicOf_mem (C : WeierstrassCurve R) (φ : R →+* S) :
    Stacks.ProjectiveCohomology.polyGradedMap (Fin 3) φ (cubicOf C) ∈
      (cubicIdealOf (C.map φ)).toIdeal := by
  show MvPolynomial.map φ (cubicOf C) ∈ Ideal.span {cubicOf (C.map φ)}
  rw [cubicOf_map]
  exact Ideal.subset_span rfl

/-- The change of coefficients `R[x, y, z]/(F_C) → S[x, y, z]/(F_{C.map φ})` along `φ : R →+* S`,
as a graded ring homomorphism. -/
def mapHom (C : WeierstrassCurve R) (φ : R →+* S) : gradingOf C →+*ᵍ gradingOf (C.map φ) :=
  coordHom (Stacks.ProjectiveCohomology.polyGradedMap (Fin 3) φ) (map_cubicOf_mem C φ)

/-- The irrelevant ideal of `S[x, y, z]/(F_{C.map φ})` lies in the ideal generated by the image of
the irrelevant ideal of `R[x, y, z]/(F_C)` under `mapHom C φ`. -/
theorem irrelevant_le_map_mapHom (C : WeierstrassCurve R) (φ : R →+* S) :
    HomogeneousIdeal.irrelevant (gradingOf (C.map φ)) ≤
      (HomogeneousIdeal.irrelevant (gradingOf C)).map (mapHom C φ) := by
  refine (HomogeneousIdeal.irrelevant_le _).2 fun i hi x hx => ?_
  obtain ⟨q, hq, rfl⟩ := (Stacks.HomogeneousIdeal.mem_quotientGrading_iff _ x).mp hx
  have hq' : q.IsHomogeneous i := (mem_homogeneousSubmodule i q).1 hq
  rw [← q.support_sum_monomial_coeff, map_sum]
  refine Ideal.sum_mem _ fun d hd => ?_
  have hdeg : (monomial d (1 : R)).IsHomogeneous i := by
    refine isHomogeneous_monomial 1 ?_
    by_contra hne
    exact (MvPolynomial.mem_support_iff.mp hd) (hq'.coeff_eq_zero hne)
  have hmem : Ideal.Quotient.mk (cubicIdealOf C).toIdeal (monomial d 1) ∈
      (HomogeneousIdeal.irrelevant (gradingOf C)).toIdeal :=
    HomogeneousIdeal.mem_irrelevant_of_mem _ hi
      (Stacks.HomogeneousIdeal.mk_mem_quotientGrading _ ((mem_homogeneousSubmodule i _).2 hdeg))
  have h : Ideal.Quotient.mk (cubicIdealOf (C.map φ)).toIdeal (monomial d (coeff d q)) =
      Ideal.Quotient.mk _ (MvPolynomial.C (coeff d q)) *
        mapHom C φ (Ideal.Quotient.mk (cubicIdealOf C).toIdeal (monomial d 1)) := by
    show _ = _ * Ideal.Quotient.mk _ (MvPolynomial.map φ (monomial d 1))
    rw [← map_mul, MvPolynomial.map_monomial, map_one, C_mul_monomial, mul_one]
  rw [h]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hmem)

/-- The morphism `E_{C.map φ} ⟶ E_C` of plane cubics induced by the change of coefficients along
`φ : R →+* S`. -/
def mapMap (C : WeierstrassCurve R) (φ : R →+* S) : projOf (C.map φ) ⟶ projOf C :=
  Proj.map (mapHom C φ) (irrelevant_le_map_mapHom C φ)

/-- `mapMap C φ` lies over `Spec S ⟶ Spec R`. -/
theorem mapMap_projectionOf (C : WeierstrassCurve R) (φ : R →+* S) :
    mapMap C φ ≫ projectionOf C =
      projectionOf (C.map φ) ≫ Spec.map (CommRingCat.ofHom φ) := by
  show Proj.map (mapHom C φ) (irrelevant_le_map_mapHom C φ) ≫
      Proj.toSpecZero (gradingOf C) ≫ Spec.map (CommRingCat.ofHom (toGradingZeroOf C)) =
    (Proj.toSpecZero (gradingOf (C.map φ)) ≫
      Spec.map (CommRingCat.ofHom (toGradingZeroOf (C.map φ)))) ≫ Spec.map (CommRingCat.ofHom φ)
  rw [Proj.map_toSpecZero_assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, mapHom,
    gradedZeroRingHom_coordHom_comp _ _ φ (fun a => MvPolynomial.map_C φ a)]

/-- `mapMap C φ` carries the section `(0 : 1 : 0)` of `E_{C.map φ}` to the section `(0 : 1 : 0)` of
`E_C` pulled back along `Spec S ⟶ Spec R`. -/
theorem zeroOf_mapMap (C : WeierstrassCurve R) (φ : R →+* S) :
    zeroOf (C.map φ) ≫ mapMap C φ = Spec.map (CommRingCat.ofHom φ) ≫ zeroOf C := by
  have hring : (evalZeroGlobalOf (C.map φ)).comp (mapHom C φ).toRingHom =
      (Spec.map (CommRingCat.ofHom φ)).appTop.hom.comp (evalZeroGlobalOf C) := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun p => ?_)
    have h := congrArg (fun g => g.hom (evalZeroOf C (Ideal.Quotient.mk _ p)))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
    simp only [RingHom.comp_apply, evalZeroGlobalOf, ← h]
    congr 1
    show eval ![0, 1, 0] (MvPolynomial.map φ p) = φ (eval ![0, 1, 0] p)
    have hpt : (φ ∘ ![0, 1, 0] : Fin 3 → S) = ![0, 1, 0] := by
      funext i
      fin_cases i <;> simp
    rw [eval_map, eval, coe_eval₂Hom, eval₂_comp_left, hpt]
    rfl
  have hfφ : (HomogeneousIdeal.irrelevant (gradingOf C)).toIdeal.map
      ((evalZeroGlobalOf (C.map φ)).comp (mapHom C φ).toRingHom) = ⊤ := by
    rw [hring]
    exact Proj.map_irrelevant_comp_appTop_eq_top (gradingOf C) _ _ (map_irrelevant_eq_top_of C)
  show Proj.fromOfGlobalSections (gradingOf (C.map φ)) (evalZeroGlobalOf (C.map φ))
      (map_irrelevant_eq_top_of (C.map φ)) ≫
      Proj.map (mapHom C φ) (irrelevant_le_map_mapHom C φ) =
    Spec.map (CommRingCat.ofHom φ) ≫
      Proj.fromOfGlobalSections (gradingOf C) (evalZeroGlobalOf C) (map_irrelevant_eq_top_of C)
  rw [Proj.fromOfGlobalSections_comp_map _ _ _ _ hfφ,
    Proj.comp_fromOfGlobalSections (gradingOf C) _ _ _ (hring ▸ hfφ)]
  exact Proj.fromOfGlobalSections_congr hring _ _

/-- Each graded piece of the homogeneous coordinate ring of the plane cubic of `C'` is stable
under multiplication by scalars of `S`. -/
theorem smul_mem_gradingOf (C' : WeierstrassCurve S) (c : S) {i : ℕ} {x : coordRingOf C'}
    (hx : x ∈ gradingOf C' i) : c • x ∈ gradingOf C' i := by
  obtain ⟨q, hq, rfl⟩ := (Stacks.HomogeneousIdeal.mem_quotientGrading_iff _ x).mp hx
  rw [← Ideal.Quotient.mkₐ_eq_mk S, ← map_smul]
  exact Stacks.HomogeneousIdeal.mk_mem_quotientGrading _ (Submodule.smul_mem _ c hq)

end Map

/-! ### The grading by submodules -/

section ModuleGrading

variable (C : WeierstrassCurve R)

/-- The grading by total degree of the homogeneous coordinate ring, by `R`-submodules. -/
abbrev moduleGradingOf : ℕ → Submodule R (coordRingOf C) :=
  Stacks.RingTheory.HomogeneousQuotient.quotientGrading (homogeneousSubmodule (Fin 3) R)
    (cubicIdealOf C)

/-- The graded pieces of `moduleGradingOf C` and of `gradingOf C` have the same elements. -/
theorem mem_moduleGradingOf_iff {i : ℕ} (x : coordRingOf C) :
    x ∈ moduleGradingOf C i ↔ x ∈ gradingOf C i :=
  (Stacks.RingTheory.HomogeneousQuotient.mem_quotientGrading_iff _ _).trans
    (Stacks.HomogeneousIdeal.mem_quotientGrading_iff _ x).symm

/-- The identity, from the grading by additive subgroups to the grading by submodules. -/
def toModuleGrading : gradingOf C →+*ᵍ moduleGradingOf C where
  __ := RingHom.id (coordRingOf C)
  map_mem {_ x} hx := (mem_moduleGradingOf_iff C x).2 hx

/-- The identity, from the grading by submodules to the grading by additive subgroups. -/
def fromModuleGrading : moduleGradingOf C →+*ᵍ gradingOf C where
  __ := RingHom.id (coordRingOf C)
  map_mem {_ x} hx := (mem_moduleGradingOf_iff C x).1 hx

/-- The hypothesis of `AlgebraicGeometry.Proj.map` for `toModuleGrading C`. -/
theorem irrelevant_le_map_toModuleGrading :
    HomogeneousIdeal.irrelevant (moduleGradingOf C) ≤
      (HomogeneousIdeal.irrelevant (gradingOf C)).map (toModuleGrading C) :=
  Proj.irrelevant_le_map_of_surjective _ fun x => ⟨x, rfl⟩

/-- The hypothesis of `AlgebraicGeometry.Proj.map` for `fromModuleGrading C`. -/
theorem irrelevant_le_map_fromModuleGrading :
    HomogeneousIdeal.irrelevant (gradingOf C) ≤
      (HomogeneousIdeal.irrelevant (moduleGradingOf C)).map (fromModuleGrading C) :=
  Proj.irrelevant_le_map_of_surjective _ fun x => ⟨x, rfl⟩

/-- `toModuleGrading C` is a left inverse of `fromModuleGrading C`. -/
theorem toModuleGrading_comp_fromModuleGrading :
    (toModuleGrading C).comp (fromModuleGrading C) = GradedRingHom.id (moduleGradingOf C) :=
  GradedRingHom.ext fun _ => rfl

/-- `fromModuleGrading C` is a left inverse of `toModuleGrading C`. -/
theorem fromModuleGrading_comp_toModuleGrading :
    (fromModuleGrading C).comp (toModuleGrading C) = GradedRingHom.id (gradingOf C) :=
  GradedRingHom.ext fun _ => rfl

/-- `Proj` of the two gradings of the homogeneous coordinate ring are the same scheme. -/
def moduleGradingIso : Proj (moduleGradingOf C) ≅ projOf C where
  hom := Proj.map (toModuleGrading C) (irrelevant_le_map_toModuleGrading C)
  inv := Proj.map (fromModuleGrading C) (irrelevant_le_map_fromModuleGrading C)
  hom_inv_id :=
    (Proj.map_comp (fromModuleGrading C) (toModuleGrading C) _ _).symm.trans
      ((Proj.map_congr (toModuleGrading_comp_fromModuleGrading C) _ (by simp)).trans Proj.map_id)
  inv_hom_id :=
    (Proj.map_comp (toModuleGrading C) (fromModuleGrading C) _ _).symm.trans
      ((Proj.map_congr (fromModuleGrading_comp_toModuleGrading C) _ (by simp)).trans Proj.map_id)

/-- Under `moduleGradingIso C`, the projection of the plane cubic to `Spec R` is the structure
morphism of `Proj (moduleGradingOf C)` over `Spec R` through its degree-zero part. -/
theorem moduleGradingIso_hom_projectionOf :
    (moduleGradingIso C).hom ≫ projectionOf C =
      Proj.toSpecZero (moduleGradingOf C) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R ↥(moduleGradingOf C 0))) := by
  show Proj.map (toModuleGrading C) (irrelevant_le_map_toModuleGrading C) ≫
      Proj.toSpecZero (gradingOf C) ≫ Spec.map (CommRingCat.ofHom (toGradingZeroOf C)) = _
  rw [Proj.map_toSpecZero_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

end ModuleGrading

/-! ### Base change of the homogeneous coordinate ring -/

section BaseChange

variable (C : WeierstrassCurve R) (S : Type u) [CommRing S] [Algebra R S]

/-- The ideal of the cubic of `C.map (algebraMap R S)` is the extension of the ideal of the cubic
of `C` along `R[x, y, z] → S ⊗[R] R[x, y, z] ≅ S[x, y, z]`. -/
theorem cubicIdealOf_map_eq :
    (cubicIdealOf (C.map (algebraMap R S))).toIdeal =
      Ideal.map (MvPolynomial.algebraTensorAlgEquiv R S)
        (Ideal.map (Algebra.TensorProduct.includeRight :
            MvPolynomial (Fin 3) R →ₐ[R] S ⊗[R] MvPolynomial (Fin 3) R)
          (cubicIdealOf C).toIdeal) := by
  show Ideal.span {cubicOf (C.map (algebraMap R S))} =
    Ideal.map _ (Ideal.map _ (Ideal.span {cubicOf C}))
  rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, cubicOf_map]
  congr 2
  show _ = MvPolynomial.algebraTensorAlgEquiv R S (1 ⊗ₜ[R] cubicOf C)
  rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]

/-- The base change of the homogeneous coordinate ring of the plane cubic is the homogeneous
coordinate ring of the plane cubic over the extended base. -/
def baseChangeEquiv :
    S ⊗[R] coordRingOf C ≃ₐ[S] coordRingOf (C.map (algebraMap R S)) :=
  (Algebra.TensorProduct.tensorQuotientEquiv S _ S (cubicIdealOf C).toIdeal).trans
    (Ideal.quotientEquivAlg _ _ (MvPolynomial.algebraTensorAlgEquiv R S)
      (cubicIdealOf_map_eq C S))

/-- `baseChangeEquiv C S` sends `s ⊗ [p]` to the class of `s · p`, with `p` read over `S`. -/
@[simp]
theorem baseChangeEquiv_tmul (s : S) (p : MvPolynomial (Fin 3) R) :
    baseChangeEquiv C S (s ⊗ₜ[R] Ideal.Quotient.mk (cubicIdealOf C).toIdeal p) =
      Ideal.Quotient.mk _ (MvPolynomial.C s * MvPolynomial.map (algebraMap R S) p) := by
  show Ideal.quotientEquivAlg _ _ (MvPolynomial.algebraTensorAlgEquiv R S)
      (cubicIdealOf_map_eq C S)
      (Algebra.TensorProduct.tensorQuotientEquiv S (MvPolynomial (Fin 3) R) S
        (cubicIdealOf C).toIdeal (s ⊗ₜ[R] Ideal.Quotient.mk (cubicIdealOf C).toIdeal p)) = _
  rw [Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul]
  show Ideal.Quotient.mk _ (MvPolynomial.algebraTensorAlgEquiv R S (s ⊗ₜ[R] p)) = _
  rw [MvPolynomial.algebraTensorAlgEquiv_tmul, smul_eq_C_mul]

/-- The comparison of the base-changed homogeneous coordinate ring with the homogeneous coordinate
ring over the extended base, as a homomorphism of graded rings. -/
def baseChangeGradedHom :
    Stacks.ProjBaseChange.grading (moduleGradingOf C) S →+*ᵍ
      gradingOf (C.map (algebraMap R S)) where
  __ := (baseChangeEquiv C S).toRingEquiv.toRingHom
  map_mem := by
    intro i x hx
    have hx' : x ∈ Submodule.span S
        ((moduleGradingOf C i).map ((TensorProduct.mk R S _) 1)) := by
      rw [← Submodule.baseChange_eq_span]; exact hx
    refine Submodule.span_induction (p := fun x _ => baseChangeEquiv C S x ∈
      gradingOf (C.map (algebraMap R S)) i) ?_ ?_ ?_ ?_ hx'
    · rintro _ ⟨b, hb, rfl⟩
      obtain ⟨p, hp, rfl⟩ :=
        (Stacks.RingTheory.HomogeneousQuotient.mem_quotientGrading_iff _ _).1 hb
      have h : baseChangeEquiv C S ((TensorProduct.mk R S _) 1
          (Ideal.Quotient.mk (cubicIdealOf C).toIdeal p)) =
          Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap R S) p) := by
        change baseChangeEquiv C S (1 ⊗ₜ[R] Ideal.Quotient.mk (cubicIdealOf C).toIdeal p) = _
        rw [baseChangeEquiv_tmul, map_one, one_mul]
      rw [h]
      exact Stacks.HomogeneousIdeal.mk_mem_quotientGrading _
        ((mem_homogeneousSubmodule i _).2 (((mem_homogeneousSubmodule i p).1 hp).map _))
    · simp
    · intro x y _ _ hx hy
      rw [map_add]
      exact AddSubgroup.add_mem _ hx hy
    · intro c x _ hx
      rw [map_smul]
      exact smul_mem_gradingOf _ c hx

/-- The inverse comparison, as a homomorphism of graded rings. -/
def baseChangeGradedInv :
    gradingOf (C.map (algebraMap R S)) →+*ᵍ
      Stacks.ProjBaseChange.grading (moduleGradingOf C) S where
  __ := (baseChangeEquiv C S).symm.toRingEquiv.toRingHom
  map_mem := by
    classical
    intro i x hx
    obtain ⟨q, hq, rfl⟩ := (Stacks.HomogeneousIdeal.mem_quotientGrading_iff _ x).mp hx
    have hq' : q.IsHomogeneous i := (mem_homogeneousSubmodule i q).1 hq
    set z : S ⊗[R] coordRingOf C :=
      ∑ d ∈ q.support, coeff d q ⊗ₜ[R] Ideal.Quotient.mk (cubicIdealOf C).toIdeal (monomial d 1)
      with hzdef
    have hz : baseChangeEquiv C S z = Ideal.Quotient.mk _ q := by
      rw [hzdef, map_sum]
      simp only [baseChangeEquiv_tmul, MvPolynomial.map_monomial, map_one, C_mul_monomial,
        mul_one]
      rw [← map_sum, q.support_sum_monomial_coeff]
    have hmem : z ∈ Stacks.ProjBaseChange.grading (moduleGradingOf C) S i := by
      refine Submodule.sum_mem _ fun d hd => Submodule.tmul_mem_baseChange_of_mem _
        (Stacks.RingTheory.HomogeneousQuotient.quotientGrading_mk_mem _ _
          ((mem_homogeneousSubmodule i _).2 (isHomogeneous_monomial 1 ?_)))
      by_contra hne
      exact (MvPolynomial.mem_support_iff.mp hd) (hq'.coeff_eq_zero hne)
    change (baseChangeEquiv C S).symm (Ideal.Quotient.mk _ q) ∈ _
    rw [← hz, AlgEquiv.symm_apply_apply]
    exact hmem

/-- `baseChangeGradedInv C S` is a left inverse of `baseChangeGradedHom C S`. -/
theorem baseChangeGradedInv_comp_hom :
    (baseChangeGradedInv C S).comp (baseChangeGradedHom C S) = GradedRingHom.id _ :=
  GradedRingHom.ext fun x => (baseChangeEquiv C S).symm_apply_apply x

/-- `baseChangeGradedInv C S` is a right inverse of `baseChangeGradedHom C S`. -/
theorem baseChangeGradedHom_comp_inv :
    (baseChangeGradedHom C S).comp (baseChangeGradedInv C S) = GradedRingHom.id _ :=
  GradedRingHom.ext fun x => (baseChangeEquiv C S).apply_symm_apply x

/-- The change of coefficients along `algebraMap R S` factors as the inclusion `a ↦ 1 ⊗ a` into the
base change followed by `baseChangeGradedHom C S`. -/
theorem mapHom_comp_fromModuleGrading_eq :
    (mapHom C (algebraMap R S)).comp (fromModuleGrading C) =
      (baseChangeGradedHom C S).comp
        (Stacks.ProjBaseChange.includeRight (moduleGradingOf C) S) :=
  GradedRingHom.ext fun x => by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    show Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap R S) p) =
      baseChangeEquiv C S (1 ⊗ₜ[R] Ideal.Quotient.mk (cubicIdealOf C).toIdeal p)
    rw [baseChangeEquiv_tmul, map_one, one_mul]

/-- The hypothesis of `AlgebraicGeometry.Proj.map` for `baseChangeGradedHom C S`. -/
theorem irrelevant_le_map_baseChangeGradedHom :
    HomogeneousIdeal.irrelevant (gradingOf (C.map (algebraMap R S))) ≤
      (HomogeneousIdeal.irrelevant (Stacks.ProjBaseChange.grading (moduleGradingOf C) S)).map
        (baseChangeGradedHom C S) :=
  irrelevant_le_map_of_comp_eq_id _ _ (baseChangeGradedHom_comp_inv C S)

/-- The hypothesis of `AlgebraicGeometry.Proj.map` for `baseChangeGradedInv C S`. -/
theorem irrelevant_le_map_baseChangeGradedInv :
    HomogeneousIdeal.irrelevant (Stacks.ProjBaseChange.grading (moduleGradingOf C) S) ≤
      (HomogeneousIdeal.irrelevant (gradingOf (C.map (algebraMap R S)))).map
        (baseChangeGradedInv C S) :=
  irrelevant_le_map_of_comp_eq_id _ _ (baseChangeGradedInv_comp_hom C S)

/-- `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.isPullback_mapMap` for the structure map
of an `R`-algebra `S`. -/
theorem isPullback_mapMap_algebraMap :
    IsPullback (mapMap C (algebraMap R S)) (projectionOf (C.map (algebraMap R S)))
      (projectionOf C) (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  have he := irrelevant_le_map_baseChangeGradedHom C S
  have he' := irrelevant_le_map_baseChangeGradedInv C S
  have hf := HomogeneousIdeal.irrelevant_le_map_comp (irrelevant_le_map_fromModuleGrading C)
    (irrelevant_le_map_mapHom C (algebraMap R S))
  have H := Stacks.ProjBaseChange.isPullback_map_of_baseChange (moduleGradingOf C) S hf he he'
    (baseChangeGradedInv_comp_hom C S) (baseChangeGradedHom_comp_inv C S)
    (mapHom_comp_fromModuleGrading_eq C S)
  refine H.of_iso (Iso.refl _) (moduleGradingIso C) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [Proj.map_comp (fromModuleGrading C) (mapHom C (algebraMap R S))
      (irrelevant_le_map_fromModuleGrading C) (irrelevant_le_map_mapHom C (algebraMap R S)),
      Category.assoc]
    show mapMap C (algebraMap R S) ≫ (moduleGradingIso C).inv ≫ (moduleGradingIso C).hom = _
    rw [Iso.inv_hom_id, Category.comp_id]
    exact (Category.id_comp _).symm
  · rw [Iso.refl_hom, Category.comp_id]
    refine Eq.trans ?_ (Category.id_comp (projectionOf (C.map (algebraMap R S)))).symm
    show _ = Proj.toSpecZero (gradingOf (C.map (algebraMap R S))) ≫
      Spec.map (CommRingCat.ofHom (toGradingZeroOf (C.map (algebraMap R S))))
    have hring : (baseChangeGradedHom C S).gradedZeroRingHom.comp
        (algebraMap S ↥(Stacks.ProjBaseChange.grading (moduleGradingOf C) S 0)) =
        toGradingZeroOf (C.map (algebraMap R S)) := by
      refine RingHom.ext fun s => Subtype.ext ?_
      have h := baseChangeEquiv_tmul C S s 1
      rw [map_one, map_one, mul_one] at h
      exact h
    rw [Proj.map_toSpecZero_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hring]
  · rw [Iso.refl_hom, Category.comp_id, moduleGradingIso_hom_projectionOf]
  · simp

end BaseChange

/-! ### The plane cubic of a base-changed equation -/

section FamilyMap

variable {S : Type u} [CommRing S]

/-- **The plane cubic commutes with base change.** For a ring map `φ : R →+* S`, the square
formed by `mapMap C φ : E_{C.map φ} ⟶ E_C`, the two projections and
`Spec S ⟶ Spec R` is cartesian. -/
theorem isPullback_mapMap (C : WeierstrassCurve R) (φ : R →+* S) :
    IsPullback (mapMap C φ) (projectionOf (C.map φ)) (projectionOf C)
      (Spec.map (CommRingCat.ofHom φ)) := by
  let _ := φ.toAlgebra
  exact isPullback_mapMap_algebraMap C S

/-- **The base change of the plane cubic of `C` along `Spec S ⟶ Spec R` is the plane cubic of
`C.map φ`**, as pointed families over `Spec S`. -/
def familyOfMapIso (C : WeierstrassCurve R) (φ : R →+* S) :
    FamilyIso ((familyOf C).pullback (Spec.map (CommRingCat.ofHom φ))) (familyOf (C.map φ)) where
  iso := (isPullback_mapMap C φ).isoPullback.symm
  iso_map := (isPullback_mapMap C φ).isoPullback_inv_snd
  zero_iso := by
    refine (isPullback_mapMap C φ).hom_ext ?_ ?_
    · change Limits.pullback.lift _ _ _ ≫ (isPullback_mapMap C φ).isoPullback.inv ≫
          mapMap C φ = zeroOf (C.map φ) ≫ mapMap C φ
      rw [IsPullback.isoPullback_inv_fst]
      exact (Limits.pullback.lift_fst _ _ _).trans (zeroOf_mapMap C φ).symm
    · change Limits.pullback.lift _ _ _ ≫ (isPullback_mapMap C φ).isoPullback.inv ≫
          projectionOf (C.map φ) = zeroOf (C.map φ) ≫ projectionOf (C.map φ)
      rw [IsPullback.isoPullback_inv_snd]
      exact (Limits.pullback.lift_snd _ _ _).trans (zeroOf_projectionOf (C.map φ)).symm

/-- `familyOfMapIso C φ` followed by `mapMap C φ` is the first projection of the pullback. -/
@[reassoc]
theorem familyOfMapIso_hom_mapMap (C : WeierstrassCurve R) (φ : R →+* S) :
    (familyOfMapIso C φ).iso.hom ≫ mapMap C φ =
      Limits.pullback.fst (familyOf C).map (Spec.map (CommRingCat.ofHom φ)) :=
  (isPullback_mapMap C φ).isoPullback_inv_fst

/-- `familyOfMapIso C φ` followed by the projection of `E_{C.map φ}` is the second projection of
the pullback. -/
@[reassoc]
theorem familyOfMapIso_hom_projectionOf (C : WeierstrassCurve R) (φ : R →+* S) :
    (familyOfMapIso C φ).iso.hom ≫ projectionOf (C.map φ) =
      Limits.pullback.snd (familyOf C).map (Spec.map (CommRingCat.ofHom φ)) :=
  (familyOfMapIso C φ).iso_map

/-- The inverse of `familyOfMapIso C φ` followed by the first projection of the pullback is
`mapMap C φ`. -/
@[reassoc]
theorem familyOfMapIso_inv_fst (C : WeierstrassCurve R) (φ : R →+* S) :
    (familyOfMapIso C φ).iso.inv ≫
      Limits.pullback.fst (familyOf C).map (Spec.map (CommRingCat.ofHom φ)) = mapMap C φ :=
  (isPullback_mapMap C φ).isoPullback_hom_fst

/-- The inverse of `familyOfMapIso C φ` followed by the second projection of the pullback is the
projection of `E_{C.map φ}`. -/
@[reassoc]
theorem familyOfMapIso_inv_snd (C : WeierstrassCurve R) (φ : R →+* S) :
    (familyOfMapIso C φ).iso.inv ≫
      Limits.pullback.snd (familyOf C).map (Spec.map (CommRingCat.ofHom φ)) =
        projectionOf (C.map φ) :=
  (isPullback_mapMap C φ).isoPullback_hom_snd

end FamilyMap

/-! ### Naturality of the coordinate change in the base ring -/

section Naturality

variable {S : Type u} [CommRing S]

/-- Changing coefficients along `ψ` after the substitution of `γ` is the substitution of `γ.map ψ`
after changing coefficients along `ψ`. -/
theorem map_comp_substOf (γ : WeierstrassCurve.VariableChange R) (ψ : R →+* S) :
    (MvPolynomial.map ψ).comp (substOf γ).toRingHom =
      (substOf (γ.map ψ)).toRingHom.comp (MvPolynomial.map ψ) := by
  refine MvPolynomial.ringHom_ext (fun a => ?_) fun i => ?_
  · simp
  · fin_cases i <;> simp [substOf]

/-- The substitution of `γ` followed by `MvPolynomial.map ψ` sends the cubic of `C` into the ideal
of the cubic of `(γ • C).map ψ`. -/
theorem map_substOf_cubicOf_mem (γ : WeierstrassCurve.VariableChange R) (C : WeierstrassCurve R)
    (ψ : R →+* S) :
    ((Stacks.ProjectiveCohomology.polyGradedMap (Fin 3) ψ).comp (substGradedHom γ)) (cubicOf C) ∈
      (cubicIdealOf ((γ • C).map ψ)).toIdeal := by
  show MvPolynomial.map ψ (substOf γ (cubicOf C)) ∈ Ideal.span {cubicOf ((γ • C).map ψ)}
  rw [substOf_cubicOf, map_mul, MvPolynomial.map_C, cubicOf_map]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)

/-- The substitution of `γ` followed by `MvPolynomial.map ψ` sends the cubic of `C` into the ideal
of the cubic of `γ.map ψ • C.map ψ`. -/
theorem map_substOf_cubicOf_mem_map_smul (γ : WeierstrassCurve.VariableChange R)
    (C : WeierstrassCurve R) (ψ : R →+* S) :
    ((Stacks.ProjectiveCohomology.polyGradedMap (Fin 3) ψ).comp (substGradedHom γ)) (cubicOf C) ∈
      (cubicIdealOf ((γ.map ψ) • (C.map ψ))).toIdeal := by
  rw [WeierstrassCurve.map_variableChange]
  exact map_substOf_cubicOf_mem γ C ψ

/-- `changeHom γ C` followed by `mapHom (γ • C) ψ` is induced by the substitution of `γ` followed
by `MvPolynomial.map ψ`. -/
theorem mapHom_comp_changeHom (γ : WeierstrassCurve.VariableChange R) (C : WeierstrassCurve R)
    (ψ : R →+* S) :
    (mapHom (γ • C) ψ).comp (changeHom γ C) =
      coordHom ((Stacks.ProjectiveCohomology.polyGradedMap (Fin 3) ψ).comp (substGradedHom γ))
        (map_substOf_cubicOf_mem γ C ψ) :=
  GradedRingHom.ext fun x => by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [GradedRingHom.comp_apply, mapHom, changeHom, coordHom_mk, coordHom_mk, coordHom_mk,
      GradedRingHom.comp_apply]

/-- `mapHom C ψ` followed by `changeHom (γ.map ψ) (C.map ψ)` is induced by the substitution of `γ`
followed by `MvPolynomial.map ψ`. -/
theorem changeHom_comp_mapHom (γ : WeierstrassCurve.VariableChange R) (C : WeierstrassCurve R)
    (ψ : R →+* S) :
    (changeHom (γ.map ψ) (C.map ψ)).comp (mapHom C ψ) =
      coordHom ((Stacks.ProjectiveCohomology.polyGradedMap (Fin 3) ψ).comp (substGradedHom γ))
        (map_substOf_cubicOf_mem_map_smul γ C ψ) :=
  GradedRingHom.ext fun x => by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [GradedRingHom.comp_apply, mapHom, changeHom, coordHom_mk, coordHom_mk, coordHom_mk,
      GradedRingHom.comp_apply]
    exact congrArg (Ideal.Quotient.mk _) (RingHom.congr_fun (map_comp_substOf γ ψ) p).symm

/-- Transporting the projection of a plane cubic along an equality of Weierstrass equations. -/
theorem eqToHom_comp_projectionOf {D D' : WeierstrassCurve S} (h : D' = D) :
    eqToHom (congrArg projOf h.symm) ≫ projectionOf D' = projectionOf D := by
  subst h
  exact Category.id_comp _

/-- Two graded ring homomorphisms into the coordinate rings of equal Weierstrass equations
`D' = D`, both induced by the same `σ`, induce the same morphism of plane cubics up to the
identification `E_D = E_{D'}`. -/
theorem map_eq_eqToHom_comp_map {C : WeierstrassCurve R} {D D' : WeierstrassCurve S}
    (h : D' = D) (σ : homogeneousSubmodule (Fin 3) R →+*ᵍ homogeneousSubmodule (Fin 3) S)
    (h₁ : σ (cubicOf C) ∈ (cubicIdealOf D).toIdeal) (h₂ : σ (cubicOf C) ∈ (cubicIdealOf D').toIdeal)
    (f : gradingOf C →+*ᵍ gradingOf D) (f' : gradingOf C →+*ᵍ gradingOf D')
    (hf : f = coordHom σ h₁) (hf' : f' = coordHom σ h₂)
    (k : HomogeneousIdeal.irrelevant (gradingOf D) ≤
      (HomogeneousIdeal.irrelevant (gradingOf C)).map f)
    (k' : HomogeneousIdeal.irrelevant (gradingOf D') ≤
      (HomogeneousIdeal.irrelevant (gradingOf C)).map f') :
    (Proj.map f k : projOf D ⟶ projOf C) =
      eqToHom (congrArg projOf h.symm) ≫ (Proj.map f' k' : projOf D' ⟶ projOf C) := by
  subst h hf hf'
  exact (Category.id_comp _).symm

/-- **Naturality of the coordinate change in the base ring.** For `ψ : R →+* S`, changing
coordinates by `γ` and then changing coefficients along `ψ` is changing coefficients along `ψ`
and then changing coordinates by `γ.map ψ`, once the plane cubics of `(γ • C).map ψ` and of
`γ.map ψ • C.map ψ` are identified along `WeierstrassCurve.map_variableChange`. -/
theorem mapMap_changeMap (γ : WeierstrassCurve.VariableChange R) (C : WeierstrassCurve R)
    (ψ : R →+* S) :
    mapMap (γ • C) ψ ≫ changeMap γ C =
      eqToHom (congrArg projOf (WeierstrassCurve.map_variableChange C γ ψ).symm) ≫
        changeMap (γ.map ψ) (C.map ψ) ≫ mapMap C ψ := by
  have e₁ : mapMap (γ • C) ψ ≫ changeMap γ C =
      Proj.map ((mapHom (γ • C) ψ).comp (changeHom γ C))
        (HomogeneousIdeal.irrelevant_le_map_comp (irrelevant_le_map_changeHom γ C)
          (irrelevant_le_map_mapHom (γ • C) ψ)) :=
    (Proj.map_comp _ _ _ _).symm
  have e₂ : changeMap (γ.map ψ) (C.map ψ) ≫ mapMap C ψ =
      Proj.map ((changeHom (γ.map ψ) (C.map ψ)).comp (mapHom C ψ))
        (HomogeneousIdeal.irrelevant_le_map_comp (irrelevant_le_map_mapHom C ψ)
          (irrelevant_le_map_changeHom (γ.map ψ) (C.map ψ))) :=
    (Proj.map_comp _ _ _ _).symm
  rw [e₁, e₂]
  exact map_eq_eqToHom_comp_map (WeierstrassCurve.map_variableChange C γ ψ) _
    (map_substOf_cubicOf_mem γ C ψ) (map_substOf_cubicOf_mem_map_smul γ C ψ) _ _
    (mapHom_comp_changeHom γ C ψ) (changeHom_comp_mapHom γ C ψ) _ _

/-- **Naturality of the coordinate-change isomorphism in the base ring**, on total spaces: the
base change of `changeIso γ C` along `Spec S ⟶ Spec R`, read through `familyOfMapIso` on both
sides, is `changeIso (γ.map ψ) (C.map ψ)` preceded by the identification of the plane cubics of
`(γ • C).map ψ` and `γ.map ψ • C.map ψ`. -/
theorem familyOfMapIso_changeIso (γ : WeierstrassCurve.VariableChange R)
    (C : WeierstrassCurve R) (ψ : R →+* S) :
    (familyOfMapIso (γ • C) ψ).iso.inv ≫
        ((changeIso γ C).pullback (Spec.map (CommRingCat.ofHom ψ))).iso.hom ≫
          (familyOfMapIso C ψ).iso.hom =
      eqToHom (congrArg projOf (WeierstrassCurve.map_variableChange C γ ψ).symm) ≫
        (changeIso (γ.map ψ) (C.map ψ)).iso.hom := by
  dsimp only [familyOfMapIso, changeIso, FamilyIso.pullback, familyOf, Iso.symm_hom,
    Iso.symm_inv, asIso_hom]
  refine (isPullback_mapMap C ψ).hom_ext ?_ ?_
  · simp only [Category.assoc, IsPullback.isoPullback_inv_fst]
    refine (congrArg (_ ≫ ·) (Limits.pullback.lift_fst _ _ _)).trans ?_
    refine (IsPullback.isoPullback_hom_fst_assoc _ _).trans ?_
    exact mapMap_changeMap γ C ψ
  · simp only [Category.assoc, IsPullback.isoPullback_inv_snd]
    refine (congrArg (_ ≫ ·) (Limits.pullback.lift_snd _ _ _)).trans ?_
    refine (IsPullback.isoPullback_hom_snd _).trans ?_
    refine Eq.trans ?_ (congrArg (_ ≫ ·) (changeMap_projectionOf (γ.map ψ) (C.map ψ))).symm
    exact (eqToHom_comp_projectionOf (WeierstrassCurve.map_variableChange C γ ψ)).symm

end Naturality

end AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

end
