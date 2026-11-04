module

public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Examples.CoefficientProjFibreModels
public import StacksFrontier.AlgebraicGeometry.Examples.CoefficientProjNotFinitePresentation
public import StacksFrontier.Examples.Flatness.FiniteFlatNonprojectiveQuotient

/-!
# Proper flat families of projective curves and surfaces not of finite presentation

Let `R` be a ring with an ideal `I` for which `R ⧸ I` is finite and flat but not projective, so
that `I` is not finitely generated. Two proper flat families over `Spec R` which are not of
finite presentation are built from `I` by homogenizing the two affine examples of the same tag:

* `R[X₀, X₁, X₂] ⧸ (X₁X₂, a X₂ : a ∈ I)`, whose fibre at a prime `𝔭` is the vanishing locus of
  `X₁X₂` in `ℙ²` when `I ⊆ 𝔭` and is `ℙ¹` otherwise;
* `R[X₀, X₁, X₂] ⧸ (a X₂ : a ∈ I)` — the symmetric algebra of `R ⊕ R ⊕ R ⧸ I` — whose fibre is
  `ℙ²` when `I ⊆ 𝔭` and `ℙ¹` otherwise.

Both are coefficientwise ideals of the polynomial ring in three variables, so properness,
flatness and the failure of finite presentation are the general statements about such a family,
and the fibres are read off from the extension of the coefficient ideals to the residue field:
`I` extends to the zero ideal exactly when `I ⊆ 𝔭`, and to the unit ideal otherwise, which
collapses the family to one of the three recognizable shapes.

## Main results

* `Stacks.Examples.exists_proper_flat_not_finitePresentation_with_nodal_or_line_fibers`: a proper
  flat morphism, not locally of finite presentation, each of whose fibres is a projective line or
  the vanishing locus of `X₁X₂` in the projective plane.
* `Stacks.Examples.exists_proper_flat_not_finitePresentation_with_projectiveSpace_fibers`: a
  proper flat morphism, not locally of finite presentation, each of whose fibres is a projective
  line or a projective plane.

## Implementation notes

"Isomorphic to the fibre, over the residue field" is spelled as a cartesian square: a morphism
from the model scheme to the family whose square with the model's structure morphism over
`Spec κ(𝔭) ⟶ Spec R` is a pullback. The vanishing locus of `X₁X₂` in `ℙ²` is
`Stacks.CoefficientProj.monomialPairLocus`, whose closed immersion into `ℙ²` over the base is
`Stacks.CoefficientProj.monomialPairLocusToProjectiveSpace_comp`.

## References

* [Stacks Project, Tag 05LC](https://stacks.math.columbia.edu/tag/05LC)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial Stacks.CoefficientProj

namespace Stacks.Examples

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ProjFamily

/-! ### Extending an ideal to a residue field -/

variable {R : Type u} [CommRing R]

/-- An ideal contained in a prime extends to the zero ideal of the residue field there. -/
theorem map_algebraMap_residueField_eq_bot {I p : Ideal R} [p.IsPrime] (h : I ≤ p) :
    I.map (algebraMap R p.ResidueField) = ⊥ := by
  rw [Ideal.map, Ideal.span_eq_bot]
  rintro x ⟨a, ha, rfl⟩
  exact Ideal.algebraMap_residueField_eq_zero.mpr (h ha)

/-- An ideal not contained in a prime extends to the unit ideal of the residue field there. -/
theorem map_algebraMap_residueField_eq_top {I p : Ideal R} [p.IsPrime] (h : ¬ I ≤ p) :
    I.map (algebraMap R p.ResidueField) = ⊤ := by
  obtain ⟨a, haI, hap⟩ := SetLike.not_le_iff_exists.mp h
  refine Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ haI) (isUnit_iff_ne_zero.mpr ?_)
  exact fun hh => hap (Ideal.algebraMap_residueField_eq_zero.mp hh)

/-! ### The two coefficientwise families in three variables -/

section Families

variable (R) (I : Ideal R)

/-- The monomial `X₂`, the last of the three homogeneous coordinates. -/
abbrev twoDeg : Fin 3 →₀ ℕ := Finsupp.single (Fin.last 2) 1

/-- The monomial `X₁X₂`. -/
abbrev oneTwoDeg : Fin 3 →₀ ℕ := Finsupp.single (1 : Fin 3) 1 + Finsupp.single (Fin.last 2) 1

open scoped Classical in
/-- The coefficientwise family of `R[X₀, X₁, X₂] ⧸ (a X₂ : a ∈ I)`: the ideal `I` on the
monomials divisible by `X₂`, the zero ideal elsewhere. -/
def planeFamily : (Fin 3 →₀ ℕ) → Ideal R :=
  fun d => if twoDeg ≤ d then I else ⊥

open scoped Classical in
/-- The coefficientwise family of `R[X₀, X₁, X₂] ⧸ (X₁X₂, a X₂ : a ∈ I)`: the unit ideal on the
monomials divisible by `X₁X₂`, the ideal `I` on the remaining monomials divisible by `X₂`, and
the zero ideal elsewhere. -/
def nodeFamily : (Fin 3 →₀ ℕ) → Ideal R :=
  fun d => if oneTwoDeg ≤ d then ⊤ else if twoDeg ≤ d then I else ⊥

/-- On a monomial divisible by `X₂`, the plane family is `I`. -/
theorem planeFamily_of_le {d : Fin 3 →₀ ℕ} (h : twoDeg ≤ d) : planeFamily R I d = I := by
  classical
  rw [planeFamily, if_pos h]

/-- On a monomial not divisible by `X₂`, the plane family is the zero ideal. -/
theorem planeFamily_of_not_le {d : Fin 3 →₀ ℕ} (h : ¬ twoDeg ≤ d) : planeFamily R I d = ⊥ := by
  classical
  rw [planeFamily, if_neg h]

/-- On a monomial divisible by `X₁X₂`, the node family is the unit ideal. -/
theorem nodeFamily_of_le {d : Fin 3 →₀ ℕ} (h : oneTwoDeg ≤ d) : nodeFamily R I d = ⊤ := by
  classical
  rw [nodeFamily, if_pos h]

/-- On a monomial divisible by `X₂` but not by `X₁X₂`, the node family is `I`. -/
theorem nodeFamily_of_le_two {d : Fin 3 →₀ ℕ} (h₁ : ¬ oneTwoDeg ≤ d) (h₂ : twoDeg ≤ d) :
    nodeFamily R I d = I := by
  classical
  rw [nodeFamily, if_neg h₁, if_pos h₂]

/-- On a monomial not divisible by `X₂`, the node family is the zero ideal. -/
theorem nodeFamily_of_not_le {d : Fin 3 →₀ ℕ} (h : ¬ twoDeg ≤ d) : nodeFamily R I d = ⊥ := by
  classical
  have h₁ : ¬ oneTwoDeg ≤ d := fun hh => h (le_trans (le_add_self) hh)
  rw [nodeFamily, if_neg h₁, if_neg h]

/-- `X₂` does not divide the constant monomial. -/
theorem not_twoDeg_le_zero : ¬ twoDeg ≤ (0 : Fin 3 →₀ ℕ) := by
  intro h
  simpa using Finsupp.single_le_iff.mp h

/-- `X₂` divides a power of `X₂` exactly when the exponent is positive. -/
theorem twoDeg_le_single_iff (k : ℕ) :
    twoDeg ≤ Finsupp.single (Fin.last 2) k ↔ 1 ≤ k := by
  rw [Finsupp.single_le_iff, Finsupp.single_eq_same]

/-- `X₁X₂` never divides a power of `X₂`. -/
theorem not_oneTwoDeg_le_single (k : ℕ) :
    ¬ oneTwoDeg ≤ Finsupp.single (Fin.last 2) k := by
  intro h
  have h1 := h (1 : Fin 3)
  rw [Finsupp.single_apply, if_neg (by decide : ¬ (Fin.last 2 : Fin 3) = 1)] at h1
  simp at h1

/-- The plane family is monotone in the monomial. -/
theorem monotone_planeFamily : Monotone (planeFamily R I) := by
  intro d e hde
  by_cases h : twoDeg ≤ d
  · rw [planeFamily_of_le R I h, planeFamily_of_le R I (h.trans hde)]
  · rw [planeFamily_of_not_le R I h]
    exact bot_le

/-- The node family is monotone in the monomial. -/
theorem monotone_nodeFamily : Monotone (nodeFamily R I) := by
  intro d e hde
  by_cases h₁ : oneTwoDeg ≤ d
  · rw [nodeFamily_of_le R I h₁, nodeFamily_of_le R I (h₁.trans hde)]
  · by_cases h₂ : twoDeg ≤ d
    · rw [nodeFamily_of_le_two R I h₁ h₂]
      by_cases h₃ : oneTwoDeg ≤ e
      · rw [nodeFamily_of_le R I h₃]
        exact le_top
      · rw [nodeFamily_of_le_two R I h₃ (h₂.trans hde)]
    · rw [nodeFamily_of_not_le R I h₂]
      exact bot_le

/-- The plane family vanishes on the constant monomial. -/
theorem planeFamily_zero : planeFamily R I 0 = ⊥ :=
  planeFamily_of_not_le R I not_twoDeg_le_zero

/-- The node family vanishes on the constant monomial. -/
theorem nodeFamily_zero : nodeFamily R I 0 = ⊥ :=
  nodeFamily_of_not_le R I not_twoDeg_le_zero

/-- On every power of `X₂`, the plane family is contained in `I`. -/
theorem planeFamily_single_le (hk : ℕ) : planeFamily R I (Finsupp.single (Fin.last 2) hk) ≤ I := by
  by_cases h : twoDeg ≤ Finsupp.single (Fin.last 2) hk
  · rw [planeFamily_of_le R I h]
  · rw [planeFamily_of_not_le R I h]
    exact bot_le

/-- On every power of `X₂`, the node family is contained in `I`. -/
theorem nodeFamily_single_le (hk : ℕ) : nodeFamily R I (Finsupp.single (Fin.last 2) hk) ≤ I := by
  by_cases h : twoDeg ≤ Finsupp.single (Fin.last 2) hk
  · rw [nodeFamily_of_le_two R I (not_oneTwoDeg_le_single hk) h]
  · rw [nodeFamily_of_not_le R I h]
    exact bot_le

/-- On `X₂`, the plane family contains `I`. -/
theorem le_planeFamily_single : I ≤ planeFamily R I (Finsupp.single (Fin.last 2) 1) := by
  rw [planeFamily_of_le R I ((twoDeg_le_single_iff 1).mpr le_rfl)]

/-- On `X₂`, the node family contains `I`. -/
theorem le_nodeFamily_single : I ≤ nodeFamily R I (Finsupp.single (Fin.last 2) 1) := by
  rw [nodeFamily_of_le_two R I (not_oneTwoDeg_le_single 1) ((twoDeg_le_single_iff 1).mpr le_rfl)]

/-- Every quotient appearing in either family is flat as soon as `R ⧸ I` is. -/
theorem flat_quotient_planeFamily [Module.Flat R (R ⧸ I)] (d : Fin 3 →₀ ℕ) :
    Module.Flat R (R ⧸ planeFamily R I d) := by
  by_cases h : twoDeg ≤ d
  · rw [planeFamily_of_le R I h]
    infer_instance
  · rw [planeFamily_of_not_le R I h]
    exact Module.Flat.of_linearEquiv (Submodule.quotEquivOfEqBot _ rfl)

/-- Every quotient by a member of the node family is flat as soon as `R ⧸ I` is. -/
theorem flat_quotient_nodeFamily [Module.Flat R (R ⧸ I)] (d : Fin 3 →₀ ℕ) :
    Module.Flat R (R ⧸ nodeFamily R I d) := by
  by_cases h₁ : oneTwoDeg ≤ d
  · rw [nodeFamily_of_le R I h₁]
    infer_instance
  · by_cases h₂ : twoDeg ≤ d
    · rw [nodeFamily_of_le_two R I h₁ h₂]
      infer_instance
    · rw [nodeFamily_of_not_le R I h₂]
      exact Module.Flat.of_linearEquiv (Submodule.quotEquivOfEqBot _ rfl)

end Families

/-! ### The extended families -/

section BaseChange

variable (R) (I : Ideal R) (S : Type u) [CommRing S] [Algebra R S]

/-- If `I` extends to the zero ideal of `S`, so does every member of the plane family. -/
theorem baseChange_planeFamily_of_bot (h : I.map (algebraMap R S) = ⊥) :
    baseChange (planeFamily R I) S = fun _ => (⊥ : Ideal S) := by
  funext d
  show (planeFamily R I d).map (algebraMap R S) = ⊥
  by_cases hd : twoDeg ≤ d
  · rw [planeFamily_of_le R I hd, h]
  · rw [planeFamily_of_not_le R I hd, Ideal.map_bot]

/-- If `I` extends to the unit ideal of `S`, the extended plane family is the coefficientwise
family of the ideal generated by `X₂`. -/
theorem baseChange_planeFamily_of_top (h : I.map (algebraMap R S) = ⊤) :
    baseChange (planeFamily R I) S = monomialFamily S twoDeg := by
  funext d
  show (planeFamily R I d).map (algebraMap R S) = _
  by_cases hd : twoDeg ≤ d
  · rw [planeFamily_of_le R I hd, h, monomialFamily_of_le hd]
  · rw [planeFamily_of_not_le R I hd, Ideal.map_bot, monomialFamily_of_not_le hd]

/-- If `I` extends to the zero ideal of `S`, the extended node family is the coefficientwise
family of the ideal generated by `X₁X₂`. -/
theorem baseChange_nodeFamily_of_bot (h : I.map (algebraMap R S) = ⊥) :
    baseChange (nodeFamily R I) S = monomialFamily S oneTwoDeg := by
  funext d
  show (nodeFamily R I d).map (algebraMap R S) = _
  by_cases h₁ : oneTwoDeg ≤ d
  · rw [nodeFamily_of_le R I h₁, Ideal.map_top, monomialFamily_of_le h₁]
  · rw [monomialFamily_of_not_le h₁]
    by_cases h₂ : twoDeg ≤ d
    · rw [nodeFamily_of_le_two R I h₁ h₂, h]
    · rw [nodeFamily_of_not_le R I h₂, Ideal.map_bot]

/-- If `I` extends to the unit ideal of `S`, the extended node family is the coefficientwise
family of the ideal generated by `X₂`. -/
theorem baseChange_nodeFamily_of_top (h : I.map (algebraMap R S) = ⊤) :
    baseChange (nodeFamily R I) S = monomialFamily S twoDeg := by
  funext d
  show (nodeFamily R I d).map (algebraMap R S) = _
  by_cases h₁ : oneTwoDeg ≤ d
  · rw [nodeFamily_of_le R I h₁, Ideal.map_top,
      monomialFamily_of_le (le_trans (le_add_self) h₁)]
  · by_cases h₂ : twoDeg ≤ d
    · rw [nodeFamily_of_le_two R I h₁ h₂, h, monomialFamily_of_le h₂]
    · rw [nodeFamily_of_not_le R I h₂, Ideal.map_bot, monomialFamily_of_not_le h₂]

/-! ### The extended coefficient ideals -/

/-- `X₂` as a monomial. -/
theorem monomial_twoDeg_eq :
    monomial twoDeg (1 : S) = X (Fin.last 2) := rfl

/-- `X₁X₂` as a monomial. -/
theorem monomial_oneTwoDeg_eq :
    monomial oneTwoDeg (1 : S) = X (1 : Fin 3) * X (Fin.last 2) := by
  rw [MvPolynomial.X, MvPolynomial.X, monomial_mul_monomial, mul_one]

/-- If `I` extends to the zero ideal of `S`, the coefficient ideal of the extended plane family
is zero. -/
theorem coefficientIdeal_baseChange_planeFamily_of_bot (h : I.map (algebraMap R S) = ⊥) :
    coefficientIdeal (baseChange (planeFamily R I) S) = ⊥ := by
  rw [baseChange_planeFamily_of_bot R I S h, coefficientIdeal_const_bot]

/-- If `I` extends to the unit ideal of `S`, the coefficient ideal of the extended plane family
is generated by `X₂`. -/
theorem coefficientIdeal_baseChange_planeFamily_of_top (h : I.map (algebraMap R S) = ⊤) :
    coefficientIdeal (baseChange (planeFamily R I) S) = Ideal.span {X (Fin.last 2)} := by
  rw [baseChange_planeFamily_of_top R I S h, coefficientIdeal_monomialFamily,
    monomial_twoDeg_eq]

/-- If `I` extends to the zero ideal of `S`, the coefficient ideal of the extended node family
is generated by `X₁X₂`. -/
theorem coefficientIdeal_baseChange_nodeFamily_of_bot (h : I.map (algebraMap R S) = ⊥) :
    coefficientIdeal (baseChange (nodeFamily R I) S) =
      Ideal.span {X (1 : Fin 3) * X (Fin.last 2)} := by
  rw [baseChange_nodeFamily_of_bot R I S h, coefficientIdeal_monomialFamily,
    monomial_oneTwoDeg_eq]

/-- If `I` extends to the unit ideal of `S`, the coefficient ideal of the extended node family
is generated by `X₂`. -/
theorem coefficientIdeal_baseChange_nodeFamily_of_top (h : I.map (algebraMap R S) = ⊤) :
    coefficientIdeal (baseChange (nodeFamily R I) S) = Ideal.span {X (Fin.last 2)} := by
  rw [baseChange_nodeFamily_of_top R I S h, coefficientIdeal_monomialFamily,
    monomial_twoDeg_eq]

end BaseChange

end ProjFamily

open ProjFamily

/-- A monotone family of ideals, flat quotients, with `I` squeezed between its values on `X₂` and
the powers of `X₂`, gives a proper flat `Proj` over `Spec R` that is not of finite presentation
when `I` is not finitely generated. -/
private theorem proper_flat_not_finitePresentation_toSpecBase {R : Type u} [CommRing R]
    {I : Ideal R} (K : (Fin 3 →₀ ℕ) → Ideal R) (hK : Monotone K) (hK0 : K 0 = ⊥)
    (hflat : ∀ d, Module.Flat R (R ⧸ K d)) (hKj : ∀ k, K (Finsupp.single (Fin.last 2) k) ≤ I)
    (hIK : I ≤ K (Finsupp.single (Fin.last 2) 1)) (hI : ¬ I.FG) :
    IsProper (toSpecBase K) ∧ AlgebraicGeometry.Flat (toSpecBase K) ∧
      ¬ LocallyOfFinitePresentation (toSpecBase K) :=
  ⟨isProper_toSpecBase K hK hK0, flat_toSpecBase K hK hK0 hflat,
    not_locallyOfFinitePresentation K (Fin.last 2) I hKj hIK hI⟩

/-! ### The two examples -/

/-- There is a proper flat morphism of schemes, not locally of finite presentation, each of whose
fibres is either a projective line or the vanishing locus of `X₁X₂` in the projective plane over
the residue field of its point. -/
@[stacks 05LC "(3)"]
theorem exists_proper_flat_not_finitePresentation_with_nodal_or_line_fibers :
    ∃ (R : Type u) (_ : CommRing R) (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)),
      IsProper f ∧ AlgebraicGeometry.Flat f ∧ ¬ LocallyOfFinitePresentation f ∧
        ∀ (p : Ideal R) [p.IsPrime],
          (∃ g : projectiveSpaceOverRing 1 (CommRingCat.of p.ResidueField) ⟶ X,
            IsPullback g
              (projectiveSpaceOverRing 1 (CommRingCat.of p.ResidueField) ↘
                Spec (CommRingCat.of p.ResidueField))
              f (Spec.map (CommRingCat.ofHom (algebraMap R p.ResidueField)))) ∨
          (∃ g : monomialPairLocus p.ResidueField 2 1 (Fin.last 2) ⟶ X,
            IsPullback g (monomialPairLocusToSpec p.ResidueField 2 1 (Fin.last 2)) f
              (Spec.map (CommRingCat.ofHom (algebraMap R p.ResidueField)))) := by
  classical
  obtain ⟨D⟩ := nonempty_finiteFlatNonprojectiveQuotient.{u}
  have := D.flat
  obtain ⟨h₁, h₂, h₃⟩ := proper_flat_not_finitePresentation_toSpecBase (nodeFamily D.R D.I)
    (monotone_nodeFamily D.R D.I) (nodeFamily_zero D.R D.I) (flat_quotient_nodeFamily D.R D.I)
    (nodeFamily_single_le D.R D.I) (le_nodeFamily_single D.R D.I) D.not_fg
  refine ⟨D.R, inferInstance, AlgebraicGeometry.Proj (projGrading (nodeFamily D.R D.I)),
    toSpecBase (nodeFamily D.R D.I), h₁, h₂, h₃, fun p hp => ?_⟩
  by_cases hIp : D.I ≤ p
  · exact Or.inr (exists_isPullback_monomialPairLocus (nodeFamily D.R D.I) p.ResidueField 1
      (Fin.last 2) (coefficientIdeal_baseChange_nodeFamily_of_bot D.R D.I p.ResidueField
        (map_algebraMap_residueField_eq_bot hIp)))
  · exact Or.inl (exists_isPullback_projectiveSpace_of_span_X_last (S := p.ResidueField)
      (n := 1) (nodeFamily D.R D.I)
      (coefficientIdeal_baseChange_nodeFamily_of_top D.R D.I p.ResidueField
        (map_algebraMap_residueField_eq_top hIp)))

/-- There is a proper flat morphism of schemes, not locally of finite presentation, each of whose
fibres is either a projective line or a projective plane over the residue field of its point. -/
@[stacks 05LC "(4)"]
theorem exists_proper_flat_not_finitePresentation_with_projectiveSpace_fibers :
    ∃ (R : Type u) (_ : CommRing R) (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)),
      IsProper f ∧ AlgebraicGeometry.Flat f ∧ ¬ LocallyOfFinitePresentation f ∧
        ∀ (p : Ideal R) [p.IsPrime],
          (∃ g : projectiveSpaceOverRing 1 (CommRingCat.of p.ResidueField) ⟶ X,
            IsPullback g
              (projectiveSpaceOverRing 1 (CommRingCat.of p.ResidueField) ↘
                Spec (CommRingCat.of p.ResidueField))
              f (Spec.map (CommRingCat.ofHom (algebraMap R p.ResidueField)))) ∨
          (∃ g : projectiveSpaceOverRing 2 (CommRingCat.of p.ResidueField) ⟶ X,
            IsPullback g
              (projectiveSpaceOverRing 2 (CommRingCat.of p.ResidueField) ↘
                Spec (CommRingCat.of p.ResidueField))
              f (Spec.map (CommRingCat.ofHom (algebraMap R p.ResidueField)))) := by
  classical
  obtain ⟨D⟩ := nonempty_finiteFlatNonprojectiveQuotient.{u}
  have := D.flat
  obtain ⟨h₁, h₂, h₃⟩ := proper_flat_not_finitePresentation_toSpecBase (planeFamily D.R D.I)
    (monotone_planeFamily D.R D.I) (planeFamily_zero D.R D.I) (flat_quotient_planeFamily D.R D.I)
    (planeFamily_single_le D.R D.I) (le_planeFamily_single D.R D.I) D.not_fg
  refine ⟨D.R, inferInstance, AlgebraicGeometry.Proj (projGrading (planeFamily D.R D.I)),
    toSpecBase (planeFamily D.R D.I), h₁, h₂, h₃, fun p hp => ?_⟩
  by_cases hIp : D.I ≤ p
  · exact Or.inr (exists_isPullback_projectiveSpace (planeFamily D.R D.I) p.ResidueField
      (coefficientIdeal_baseChange_planeFamily_of_bot D.R D.I p.ResidueField
        (map_algebraMap_residueField_eq_bot hIp)))
  · exact Or.inl (exists_isPullback_projectiveSpace_of_span_X_last (S := p.ResidueField)
      (n := 1) (planeFamily D.R D.I)
      (coefficientIdeal_baseChange_planeFamily_of_top D.R D.I p.ResidueField
        (map_algebraMap_residueField_eq_top hIp)))

end Stacks.Examples

end
