module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Existence
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.GradedBasis
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.TateColimitDifferential

/-! # Tate's resolution of a prescribed polynomial presentation

`StacksFrontier/RingTheory/DividedPowers/TateResolution/TateTower.lean` builds Tate's dependent
`ω`-tower over a degree-zero base with a prescribed ideal, and
`StacksFrontier/RingTheory/DividedPowers/TateResolution/TateColimitDifferential.lean` assembles the
differential on its colimit and proves that colimit acyclic in positive degrees and exact at the
base. This file takes the base to be the polynomial ring of a prescribed surjection
`φ : R[xᵢ] → S` with the kernel of `φ` as the ideal to be killed, and assembles the result into a
`DividedPowers.TateResolution.Resolution`, which is the existence half of Tag 09PN.

Two further ingredients are needed.

*The augmentation, and that it kills boundaries.* The augmentation is the morphism out of the
colimit sending every variable to zero and restricting to `φ` on the coefficients, which the
colimit's mapping property provides; that it kills the positive-degree part is then immediate,
since the target is concentrated in degree zero. That it kills **every** boundary is not: a
boundary coming from degree one is a degree-zero element, where the augmentation is `φ` and is
far from zero. The content is that the boundary of a degree-one element lies in the kernel of
`φ`, which is what makes the degree-zero homology of the resolution `S` rather than a proper
quotient of it. It is proved here by the subring trick: the elements all of whose homogeneous
components have their boundary killed by the augmentation form a **subring** — closure under
multiplication is the Leibniz rule, with the sign harmless because an element of positive degree
is killed by the augmentation outright — and that subring contains the coefficients, the
variables and all their divided powers, hence contains every finite variable stage and so the
whole colimit. On a variable the check is degree-counting except in degree one, where the
boundary of the variable is by construction the element of `ker φ` indexing it.

*The polynomial presentation.* The presentation theorem
`DividedPowers.TateResolution.gradedDividedPowerPolynomialOfMappingProperty`
turns the mapping property of the colimit into a
`DividedPowers.TateResolution.GradedDividedPowerPolynomial` structure on it, from which freeness
of every homogeneous piece follows by
`DividedPowers.TateResolution.GradedDividedPowerPolynomial.free_grade`.

## Main definitions

* `DividedPowers.TateResolution.resolutionBase` — the base of the tower resolving `φ`: the
  polynomial ring graded in degree zero, with `ker φ` as the family of cycles to be killed.
* `DividedPowers.TateResolution.resolutionAlgebra`,
  `DividedPowers.TateResolution.resolutionDifferential`,
  `DividedPowers.TateResolution.resolutionCoefficient`,
  `DividedPowers.TateResolution.resolutionVariable` and
  `DividedPowers.TateResolution.resolutionAugmentation` — the carrier of the resolution with its
  differential, its degree-zero polynomial algebra, its variables and its augmentation.
* `DividedPowers.TateResolution.resolutionPolynomial` — the resolution as a graded divided power
  polynomial algebra over `R[xᵢ]`.
* `DividedPowers.TateResolution.tateResolution` — the resolution itself.

## Main results

* `DividedPowers.TateResolution.resolutionAugmentation_differential` — the augmentation kills
  every boundary.
* `DividedPowers.TateResolution.mem_resolutionAlgebra_grade_zero_iff` — the degree-zero part of
  the resolution is exactly the prescribed polynomial algebra.
* `DividedPowers.TateResolution.tateResolution` — every surjection from a polynomial ring extends
  to a Tate resolution, free over `R` in every degree.

## Implementation notes

The polynomial ring has to be moved into the universe in which the tower is built. Every stage of
the tower lies in a single universe, because the variables adjoined at a step are indexed by a
subtype of the previous stage's carrier, and the carrier of a
`DividedPowers.TateResolution.Resolution` must lie in the join of the universes of `R`, of `S` and
of the variables. `DividedPowers.TateResolution.resolutionCoefficientRing` is that copy and
`DividedPowers.TateResolution.resolutionCoefficientEquiv` identifies it with `R[xᵢ]`; the only
place this is visible afterwards is that the coefficient morphism of the resolution is the
inclusion of the base composed with that identification.

The construction gives the existence half of Tag 09PN. The finiteness half — a degreewise
finite resolution of a finite-type algebra over a Noetherian ring — needs the variables adjoined
at a step to be a finite generating family of the cycles rather than all of them, which is a
different tower; finiteness of the homogeneous pieces of a graded divided power polynomial algebra
with finitely many variables in each degree is
`DividedPowers.TateResolution.GradedDividedPowerPolynomial.finite_grade`.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
* [Stacks Project, Tag 09PM](https://stacks.math.columbia.edu/tag/09PM)
* [Stacks Project, Tag 0F4I](https://stacks.math.columbia.edu/tag/0F4I)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w

attribute [local instance] GradedDPAlgebra.ring GradedDPAlgebra.algebra
  GradedDPAlgebra.graded GradedDPAlgebra.strict

attribute [local instance] gradedLimitGradedAlgebra gradedLimitStrictlyGradedComm

/-- The polynomial ring `R[xᵢ]`, moved into the universe in which the resolution is built.

The type argument `_S` is not used. It is there to fix that universe, which must contain the
universe of the algebra being resolved as well as those of `R` and of the variables: every stage
of Tate's tower lies in one universe, and the carrier of a
`DividedPowers.TateResolution.Resolution` lies in the join of all three. -/
public abbrev resolutionCoefficientRing (R : Type u) (_S : Type v) (σ : Type w) [CommRing R] :
    Type (max u v w) := ULift.{max v w} (MvPolynomial σ R)

/-- The copy of `R[xᵢ]` in the universe of the resolution is `R[xᵢ]`. -/
public noncomputable def resolutionCoefficientEquiv (R : Type u) (S : Type v) (σ : Type w)
    [CommRing R] : resolutionCoefficientRing R S σ ≃ₐ[R] MvPolynomial σ R :=
  ULift.algEquiv

section Resolution

variable {R : Type u} {S : Type v} {σ : Type w} [CommRing R] [CommRing S] [Algebra R S]
  (φ : MvPolynomial σ R →ₐ[R] S)

/-- The prescribed presentation, read on the copy of `R[xᵢ]` that lives in the universe in which
the resolution is built. -/
public noncomputable def resolutionPresentation : resolutionCoefficientRing R S σ →ₐ[R] S :=
  φ.comp (resolutionCoefficientEquiv R S σ).toAlgHom

/-- **The base of Tate's tower resolving `φ`**: the polynomial ring `R[xᵢ]` graded in degree zero
and carrying the zero differential, with the kernel of `φ` as the family of degree-zero cycles to
be killed by the variables of degree one. -/
public noncomputable abbrev resolutionBase : TateStageData.{u, max v w} R 0 :=
  tateBase (R := R) (resolutionCoefficientRing R S σ)
    (RingHom.ker (resolutionPresentation φ))

/-- **The carrier of Tate's resolution of `φ`**: the colimit of the tower over the base. -/
public noncomputable abbrev resolutionAlgebra : GradedDPAlgebra.{u, max u v w} R :=
  tateColimit (resolutionBase φ)

/-- The differential of Tate's resolution of `φ`. -/
public noncomputable abbrev resolutionDifferential :
    (resolutionAlgebra φ).carrier →ₗ[R] (resolutionAlgebra φ).carrier :=
  tateColimitDifferential (resolutionBase φ)

/-- The degree-zero polynomial algebra of Tate's resolution of `φ`: the inclusion of the base of
the tower, read through the identification of that base with `R[xᵢ]`. -/
public noncomputable def resolutionCoefficient :
    MvPolynomial σ R →ₐ[R] (resolutionAlgebra φ).carrier :=
  (tateCoefficient (resolutionBase φ)).hom.comp
    (resolutionCoefficientEquiv R S σ).symm.toAlgHom

/-- The variables of Tate's resolution of `φ`, indexed together with their degrees. -/
public noncomputable def resolutionVariable
    (j : Σ n : ℕ, tateIndex (resolutionBase φ) n) : (resolutionAlgebra φ).carrier :=
  tateVariable (resolutionBase φ) j.1 j.2

/-- Each variable of the resolution is homogeneous of its prescribed degree. -/
public theorem resolutionVariable_mem (j : Σ n : ℕ, tateIndex (resolutionBase φ) n) :
    resolutionVariable φ j ∈ (resolutionAlgebra φ).grade (j.1 + 1) :=
  tateVariable_mem (resolutionBase φ) j.1 j.2

/-- The degree-zero polynomial algebra of the resolution lands in degree zero. -/
public theorem resolutionCoefficient_mem_grade_zero (p : MvPolynomial σ R) :
    resolutionCoefficient φ p ∈ (resolutionAlgebra φ).grade 0 :=
  (tateCoefficient (resolutionBase φ)).map_grade 0 _
    (mem_degreeZeroGrade_zero R (resolutionCoefficientRing R S σ) _)

/-- The degree-zero polynomial algebra of the resolution is a subalgebra: the inclusion of the
base of the tower is injective, and so is the identification of that base with `R[xᵢ]`. -/
public theorem resolutionCoefficient_injective :
    Function.Injective (resolutionCoefficient φ) :=
  (tateInclusion_injective (resolutionBase φ) 0).comp
    (resolutionCoefficientEquiv R S σ).symm.injective

/-- The degree-zero polynomial algebra, evaluated on the identification of the base. -/
private theorem resolutionCoefficient_equiv (b : resolutionCoefficientRing R S σ) :
    resolutionCoefficient φ (resolutionCoefficientEquiv R S σ b) =
      (tateCoefficient (resolutionBase φ)).hom b :=
  congrArg (tateCoefficient (resolutionBase φ)).hom
    ((resolutionCoefficientEquiv R S σ).symm_apply_apply b)

/-- The image of the degree-zero polynomial algebra is the image of the base of the tower: the
two differ by an isomorphism of the base. -/
public theorem range_resolutionCoefficient :
    Set.range (resolutionCoefficient φ) =
      Set.range (tateCoefficient (resolutionBase φ)).hom := by
  ext y
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · obtain ⟨p, rfl⟩ := hy
    exact ⟨(resolutionCoefficientEquiv R S σ).symm p, rfl⟩
  · obtain ⟨b, rfl⟩ := hy
    exact ⟨_, resolutionCoefficient_equiv φ b⟩

/-- The differential of the resolution vanishes in degree zero. -/
public theorem resolutionDifferential_grade_zero {x : (resolutionAlgebra φ).carrier}
    (hx : x ∈ (resolutionAlgebra φ).grade 0) : resolutionDifferential φ x = 0 :=
  IsDifferentialGradedAlgebra.d_grade_zero (𝒜 := (resolutionAlgebra φ).grade)
    (d := resolutionDifferential φ) (self := tateColimitDga (resolutionBase φ)) hx

/-- The differential of the resolution satisfies the signed Leibniz rule. -/
public theorem resolutionDifferential_leibniz {i k : ℕ} {x y : (resolutionAlgebra φ).carrier}
    (hx : x ∈ (resolutionAlgebra φ).grade i) (hy : y ∈ (resolutionAlgebra φ).grade k) :
    resolutionDifferential φ (x * y) =
      resolutionDifferential φ x * y + (-1 : R) ^ i • (x * resolutionDifferential φ y) :=
  IsDifferentialGradedAlgebra.leibniz (𝒜 := (resolutionAlgebra φ).grade)
    (d := resolutionDifferential φ) (self := tateColimitDga (resolutionBase φ)) hx hy

/-- **The degree-zero part of the resolution is the prescribed polynomial algebra.** No step of
the tower adds anything in degree zero, and the base has nothing in positive degree. -/
public theorem mem_resolutionAlgebra_grade_zero_iff (a : (resolutionAlgebra φ).carrier) :
    a ∈ (resolutionAlgebra φ).grade 0 ↔ ∃ p : MvPolynomial σ R, resolutionCoefficient φ p = a := by
  refine (mem_tateColimit_grade_zero_iff (R := R) (resolutionCoefficientRing R S σ)
    (RingHom.ker (resolutionPresentation φ)) a).trans ⟨fun hy => ?_, fun hy => ?_⟩
  · obtain ⟨q, hq⟩ := hy
    exact ⟨_, (resolutionCoefficient_equiv φ q).trans hq⟩
  · obtain ⟨p, hp⟩ := hy
    exact ⟨(resolutionCoefficientEquiv R S σ).symm p, hp⟩

/-- The finite variable stages of the resolution's variables cover the resolution. -/
public theorem resolutionAlgebra_finite_support (x : (resolutionAlgebra φ).carrier) :
    ∃ T : Finset (Σ n : ℕ, tateIndex (resolutionBase φ) n),
      x ∈ finiteVariableStage (resolutionAlgebra φ).gamma (resolutionCoefficient φ)
        (resolutionVariable φ) T := by
  obtain ⟨T, hT⟩ := chainColimit_finite_support (tateAlgebra (resolutionBase φ))
    (tateStep (resolutionBase φ)) (tateIndex (resolutionBase φ))
    (tateGenerator (resolutionBase φ)) (fun n => n + 1) (fun n => n.succ_pos)
    (tateStage_isSetVariableExtension (resolutionBase φ)) (resolutionVariable φ)
    (fun n j => ⟨⟨n, j⟩, rfl⟩) x
  refine ⟨T, ?_⟩
  rwa [finiteVariableStage_congr_coefficient (resolutionAlgebra φ).gamma
    (tateCoefficient (resolutionBase φ)).hom (resolutionVariable φ) (resolutionCoefficient φ)
    (range_resolutionCoefficient φ) T]

/-- **The resolution is free on its coefficients and its variables.** This is the mapping
property of the colimit of Tate's tower, with the coefficient morphism read through the
identification of the base with `R[xᵢ]`. -/
public theorem resolutionAlgebra_hasVariableMappingProperty :
    HasVariableMappingProperty (resolutionAlgebra φ).gamma (resolutionCoefficient φ)
      (resolutionVariable φ) := by
  intro E f hf t ht
  obtain ⟨F, hF1, hF2⟩ := tateColimit_exists_gradedDPHom (resolutionBase φ) E
    (degreeZeroDPHom R (resolutionCoefficientRing R S σ) E
      (f.comp (resolutionCoefficientEquiv R S σ).toAlgHom) (fun p => hf _))
    (fun n j => t ⟨n, j⟩) (fun n j => ht ⟨n, j⟩)
  refine ⟨F.hom.toRingHom, fun p => ?_, fun j => hF2 j.1 j.2, F.map_grade, F.map_dpow⟩
  refine (hF1 ((resolutionCoefficientEquiv R S σ).symm p)).trans ?_
  change f (resolutionCoefficientEquiv R S σ ((resolutionCoefficientEquiv R S σ).symm p)) = f p
  rw [AlgEquiv.apply_symm_apply]

/-- The resolution has degree-zero coefficients and homogeneous variables. -/
public instance resolutionIsHomogeneousVariableFamily :
    IsHomogeneousVariableFamily (resolutionAlgebra φ).grade (resolutionCoefficient φ)
      (resolutionVariable φ) where
  coefficient_mem := resolutionCoefficient_mem_grade_zero φ
  variable_homogeneous j := ⟨j.1 + 1, resolutionVariable_mem φ j⟩

/-- **The resolution is a graded divided power polynomial algebra over `R[xᵢ]`**, on the variables
adjoined by the tower. This is condition (4) of Tag 09PN, and what freeness of the homogeneous
pieces is read off. -/
public noncomputable def resolutionPolynomial :
    GradedDividedPowerPolynomial (resolutionAlgebra φ).grade (resolutionAlgebra φ).gamma
      (resolutionCoefficient φ) :=
  gradedDividedPowerPolynomialOfMappingProperty (resolutionAlgebra φ).gamma
    (resolutionCoefficient φ) (resolutionVariable φ) (resolutionVariable_mem φ)
    (resolutionCoefficient_injective φ) (resolutionAlgebra_finite_support φ)
    (resolutionAlgebra_hasVariableMappingProperty φ)

end Resolution

section Augmentation

variable {R : Type u} {S : Type v} {σ : Type w} [CommRing R] [CommRing S] [Algebra R S]
  (φ : MvPolynomial σ R →ₐ[R] S)

/-- **The augmentation of Tate's resolution exists**: the morphism of graded divided power
algebras out of the colimit which restricts to the prescribed presentation on the coefficients
and kills every variable, the target being `S` concentrated in degree zero. -/
public theorem exists_resolutionAugmentation :
    ∃ F : GradedDPHom (resolutionAlgebra φ) (degreeZeroDPAlgebra R S),
      (∀ p : resolutionCoefficientRing R S σ,
          F.hom ((tateCoefficient (resolutionBase φ)).hom p) = resolutionPresentation φ p) ∧
        (∀ (n : ℕ) (j : tateIndex (resolutionBase φ) n),
          F.hom (tateVariable (resolutionBase φ) n j) = 0) :=
  tateColimit_exists_gradedDPHom (resolutionBase φ) (degreeZeroDPAlgebra R S)
    (degreeZeroDPHom R (resolutionCoefficientRing R S σ) (degreeZeroDPAlgebra R S)
      (show resolutionCoefficientRing R S σ →ₐ[R] S from resolutionPresentation φ)
      (fun _ => mem_degreeZeroGrade_zero R S _))
    (fun _ _ => 0) (fun _ _ => Submodule.zero_mem _)

/-- **The augmentation of Tate's resolution of `φ`**: the morphism to `S` restricting to `φ` on
the degree-zero polynomial algebra and killing every variable. -/
public noncomputable def resolutionAugmentation :
    GradedDPHom (resolutionAlgebra φ) (degreeZeroDPAlgebra R S) :=
  (exists_resolutionAugmentation φ).choose

/-- The augmentation restricts to the prescribed presentation on the base of the tower. -/
public theorem resolutionAugmentation_base (p : resolutionCoefficientRing R S σ) :
    (resolutionAugmentation φ).hom ((tateCoefficient (resolutionBase φ)).hom p) =
      resolutionPresentation φ p :=
  (exists_resolutionAugmentation φ).choose_spec.1 p

/-- The augmentation kills every variable of the resolution. -/
public theorem resolutionAugmentation_variable
    (j : Σ n : ℕ, tateIndex (resolutionBase φ) n) :
    (resolutionAugmentation φ).hom (resolutionVariable φ j) = 0 :=
  (exists_resolutionAugmentation φ).choose_spec.2 j.1 j.2

/-- **The augmentation kills the positive-degree part**: its target is concentrated in degree
zero. -/
public theorem resolutionAugmentation_positive {n : ℕ} (hn : n ≠ 0)
    {a : (resolutionAlgebra φ).carrier} (ha : a ∈ (resolutionAlgebra φ).grade n) :
    (resolutionAugmentation φ).hom a = 0 :=
  eq_zero_of_mem_degreeZeroDPAlgebra_grade R S hn
    ((resolutionAugmentation φ).map_grade n a ha)

/-- The augmentation extends the prescribed presentation. -/
public theorem resolutionAugmentation_coefficient (p : MvPolynomial σ R) :
    (resolutionAugmentation φ).hom (resolutionCoefficient φ p) = φ p := by
  refine (resolutionAugmentation_base φ ((resolutionCoefficientEquiv R S σ).symm p)).trans ?_
  change φ (resolutionCoefficientEquiv R S σ ((resolutionCoefficientEquiv R S σ).symm p)) = φ p
  rw [AlgEquiv.apply_symm_apply]

/-- **The augmentation kills the boundary of every variable.** For a variable of degree one the
boundary is, by construction, the element of `ker φ` indexing the variable; for a variable of
higher degree it is homogeneous of positive degree, where the augmentation vanishes. -/
public theorem resolutionAugmentation_differential_variable
    (j : Σ n : ℕ, tateIndex (resolutionBase φ) n) :
    (resolutionAugmentation φ).hom
      (resolutionDifferential φ (resolutionVariable φ j)) = 0 := by
  obtain ⟨n, j⟩ := j
  have hD : resolutionDifferential φ (resolutionVariable φ ⟨n, j⟩) =
      (tateInclusion (resolutionBase φ) n).hom (tateCycle (resolutionBase φ) n j) :=
    tateColimitDifferential_variable (resolutionBase φ) n j
  rw [hD]
  match n with
  | 0 =>
      have hker : resolutionPresentation φ (tateCycle (resolutionBase φ) 0 j) = 0 :=
        RingHom.mem_ker.1 j.2
      exact (resolutionAugmentation_base φ (tateCycle (resolutionBase φ) 0 j)).trans hker
  | m + 1 =>
      refine resolutionAugmentation_positive φ (Nat.succ_ne_zero m) ?_
      exact (tateInclusion (resolutionBase φ) (m + 1)).map_grade (m + 1) _
        (tateCycle_mem (resolutionBase φ) (m + 1) j)

/-- Only one homogeneous component of a homogeneous element is nonzero, so the augmentation kills
the boundary of each component of a homogeneous element as soon as it kills the boundary of the
element itself. -/
public theorem resolutionAugmentation_differential_gradedPart_of_mem_grade {k : ℕ}
    {x : (resolutionAlgebra φ).carrier} (hx : x ∈ (resolutionAlgebra φ).grade k)
    (h : (resolutionAugmentation φ).hom (resolutionDifferential φ x) = 0) (m : ℕ) :
    (resolutionAugmentation φ).hom (resolutionDifferential φ
      (gradedPart (resolutionAlgebra φ).grade x m)) = 0 := by
  by_cases hm : k = m
  · subst hm
    rw [gradedPart_of_mem_same _ hx]
    exact h
  · rw [gradedPart_of_mem_ne _ hx hm, map_zero, map_zero]

/-- **The elements all of whose homogeneous components have their boundary killed by the
augmentation form a subring.** Closure under multiplication is the Leibniz rule: the boundary of
a product of two homogeneous elements is the sum of two terms, each of which has a factor that
the augmentation kills by hypothesis. The sign of the second term is harmless, the augmentation
being an `R`-algebra morphism.

The condition is imposed on every homogeneous component rather than on the element itself,
because the Leibniz rule relates homogeneous elements only, and a graded derivation of a product
of two inhomogeneous elements mixes the components. -/
public noncomputable def resolutionBoundaryKernel : Subring (resolutionAlgebra φ).carrier where
  carrier := {x | ∀ m : ℕ, (resolutionAugmentation φ).hom (resolutionDifferential φ
    (gradedPart (resolutionAlgebra φ).grade x m)) = 0}
  zero_mem' := by
    intro m
    rw [gradedPart_zero, map_zero, map_zero]
  one_mem' := by
    refine resolutionAugmentation_differential_gradedPart_of_mem_grade φ
      (SetLike.one_mem_graded (resolutionAlgebra φ).grade) ?_
    rw [resolutionDifferential_grade_zero φ
      (SetLike.one_mem_graded (resolutionAlgebra φ).grade), map_zero]
  add_mem' := by
    intro x y hx hy m
    rw [gradedPart_add, map_add, map_add, hx m, hy m, add_zero]
  neg_mem' := by
    intro x hx m
    rw [gradedPart_neg, map_neg, map_neg, hx m, neg_zero]
  mul_mem' := by
    intro x y hx hy m
    obtain ⟨s, hs⟩ := exists_gradedPart_decomposition (resolutionAlgebra φ).grade x
    obtain ⟨t, ht⟩ := exists_gradedPart_decomposition (resolutionAlgebra φ).grade y
    have hxy : gradedPart (resolutionAlgebra φ).grade (x * y) m =
        ∑ i ∈ s, ∑ k ∈ t, gradedPart (resolutionAlgebra φ).grade
          (gradedPart (resolutionAlgebra φ).grade x i *
            gradedPart (resolutionAlgebra φ).grade y k) m := by
      conv_lhs => rw [hs, ht]
      exact gradedPart_mul_sum (resolutionAlgebra φ).grade _ _ m
    rw [hxy, map_sum, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_sum, map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hik : i + k = m
    · rw [gradedPart_mul_homogeneous _ (gradedPart_mem _ x i) (gradedPart_mem _ y k) hik,
        resolutionDifferential_leibniz φ (gradedPart_mem _ x i) (gradedPart_mem _ y k),
        map_add, map_mul, hx i, zero_mul, zero_add, map_smul, map_mul, hy k, mul_zero,
        smul_zero]
    · rw [gradedPart_mul_homogeneous_of_ne _ (gradedPart_mem _ x i) (gradedPart_mem _ y k) hik,
        map_zero, map_zero]

/-- A homogeneous element whose boundary the augmentation kills lies in the subring. -/
public theorem mem_resolutionBoundaryKernel_of_mem_grade {k : ℕ}
    {x : (resolutionAlgebra φ).carrier} (hx : x ∈ (resolutionAlgebra φ).grade k)
    (h : (resolutionAugmentation φ).hom (resolutionDifferential φ x) = 0) :
    x ∈ resolutionBoundaryKernel φ :=
  resolutionAugmentation_differential_gradedPart_of_mem_grade φ hx h

/-- The degree-zero polynomial algebra lies in the subring: its elements have degree zero, where
the differential vanishes. -/
public theorem resolutionCoefficient_mem_resolutionBoundaryKernel (p : MvPolynomial σ R) :
    resolutionCoefficient φ p ∈ resolutionBoundaryKernel φ := by
  refine mem_resolutionBoundaryKernel_of_mem_grade φ
    (resolutionCoefficient_mem_grade_zero φ p) ?_
  rw [resolutionDifferential_grade_zero φ (resolutionCoefficient_mem_grade_zero φ p), map_zero]

/-- Every variable lies in the subring. -/
public theorem resolutionVariable_mem_resolutionBoundaryKernel
    (j : Σ n : ℕ, tateIndex (resolutionBase φ) n) :
    resolutionVariable φ j ∈ resolutionBoundaryKernel φ :=
  mem_resolutionBoundaryKernel_of_mem_grade φ (resolutionVariable_mem φ j)
    (resolutionAugmentation_differential_variable φ j)

/-- **Every divided power of a variable lies in the subring.** A divided power of a variable is
homogeneous, and by compatibility of the divided powers with the differential its boundary has
the boundary of the variable as a factor. -/
public theorem dpow_resolutionVariable_mem_resolutionBoundaryKernel
    (j : Σ n : ℕ, tateIndex (resolutionBase φ) n) (n : ℕ) :
    (resolutionAlgebra φ).gamma.dpow n (resolutionVariable φ j) ∈
      resolutionBoundaryKernel φ := by
  by_cases hpos : resolutionVariable φ j ∈ positiveEvenPart (resolutionAlgebra φ).grade
  · match n with
    | 0 =>
        rw [(resolutionAlgebra φ).gamma.dpow_zero hpos]
        exact one_mem _
    | n + 1 =>
        have htail : (resolutionAugmentation φ).hom (resolutionDifferential φ
            ((resolutionAlgebra φ).gamma.dpow (n + 1) (resolutionVariable φ j))) = 0 := by
          rw [(tateColimitCompatible (resolutionBase φ)).d_dpow (Nat.succ_ne_zero n) hpos,
            map_mul, resolutionAugmentation_differential_variable φ j, zero_mul]
        rcases positiveEven_homogeneous_eq_zero_or_grade (resolutionAlgebra φ).grade
          (resolutionVariable_mem φ j) hpos with hzero | ⟨d, hd⟩
      -- The variable is zero, so its divided powers are homogeneous of degree zero.
        · refine mem_resolutionBoundaryKernel_of_mem_grade φ (k := 0) ?_ htail
          have hmem := (resolutionAlgebra φ).gamma.dpow_mem_grade (d := 0)
            (Nat.succ_ne_zero n) hpos (by rw [hzero]; exact Submodule.zero_mem _)
          simpa using hmem
        · refine mem_resolutionBoundaryKernel_of_mem_grade φ
            (k := 2 * (n + 1) * (d + 1)) ?_ htail
          exact (resolutionAlgebra φ).gamma.dpow_mem_grade (Nat.succ_ne_zero n) hpos
            (hd ▸ resolutionVariable_mem φ j)
  · rw [(resolutionAlgebra φ).gamma.dpow_null hpos]
    exact zero_mem _

/-- **The augmentation kills every boundary.** The elements whose homogeneous components have
their boundaries killed form a subring containing the coefficients, the variables and all their
divided powers, hence containing every finite variable stage; the finite variable stages cover the
resolution, so the condition holds for every element, and summing it over the homogeneous
components of an element gives the statement for that element.

This is the one clause of Tag 09PN that is not degree bookkeeping: a boundary coming from degree
one is a degree-zero element, where the augmentation is `φ` itself. What makes it vanish is that
the boundary of a variable of degree one is the element of `ker φ` indexing that variable. -/
public theorem resolutionAugmentation_differential (x : (resolutionAlgebra φ).carrier) :
    (resolutionAugmentation φ).hom (resolutionDifferential φ x) = 0 := by
  obtain ⟨T, hT⟩ := resolutionAlgebra_finite_support φ x
  have hx : x ∈ resolutionBoundaryKernel φ :=
    finiteVariableStage_map_mem_subring (resolutionAlgebra φ).gamma (resolutionCoefficient φ)
      (resolutionVariable φ) T (AlgHom.id R (resolutionAlgebra φ).carrier)
      (resolutionBoundaryKernel φ)
      (fun p => resolutionCoefficient_mem_resolutionBoundaryKernel φ p)
      (fun j _ => resolutionVariable_mem_resolutionBoundaryKernel φ j)
      (fun j _ n => dpow_resolutionVariable_mem_resolutionBoundaryKernel φ j n) hT
  obtain ⟨s, hs⟩ := exists_gradedPart_decomposition (resolutionAlgebra φ).grade x
  conv_lhs => rw [hs]
  rw [map_sum, map_sum]
  exact Finset.sum_eq_zero fun m _ => hx m

end Augmentation

section Existence

variable {R : Type u} {S : Type v} {σ : Type w} [CommRing R] [CommRing S] [Algebra R S]

/-- **Tate's resolution of a prescribed polynomial presentation.** Every surjection
`φ : R[xᵢ] → S` from a polynomial ring extends to a divided power differential graded algebra
over `R`, free over `R` in every degree, whose degree-zero algebra is `R[xᵢ]` along `φ`, which is
a graded divided power polynomial algebra over `R[xᵢ]`, and whose augmentation to `S` is a
quasi-isomorphism: it kills the positive-degree part and every boundary, it is surjective, its
degree-zero kernel is exactly the boundaries from degree one, and the complex is exact in every
positive degree.

The algebra is the colimit of Tate's tower over `R[xᵢ]` with `ker φ` as the ideal to be killed in
degree one. Acyclicity is not a homology computation: the variables adjoined in degree `n + 1`
are indexed by **all** cycles of degree `n`, with the boundary of a variable being the cycle
indexing it, so a cycle of degree `n` is the boundary of its own variable by construction. -/
@[stacks 09PN "resolution of any polynomial presentation"]
public noncomputable def tateResolution (φ : MvPolynomial σ R →ₐ[R] S)
    (hφ : Function.Surjective φ) : Resolution R S σ φ where
  A := (resolutionAlgebra φ).carrier
  ring := (resolutionAlgebra φ).ring
  algebra := (resolutionAlgebra φ).algebra
  grade := (resolutionAlgebra φ).grade
  graded := (resolutionAlgebra φ).graded
  free := fun n => (resolutionPolynomial φ).free_grade n
  strict := (resolutionAlgebra φ).strict
  gamma := (resolutionAlgebra φ).gamma
  differential := resolutionDifferential φ
  dga := tateColimitDga (resolutionBase φ)
  compatible := tateColimitCompatible (resolutionBase φ)
  coefficient := resolutionCoefficient φ
  augmentation := (resolutionAugmentation φ).hom
  polynomial := resolutionPolynomial φ
  augmentation_surjective := by
    intro s
    obtain ⟨p, hp⟩ := hφ s
    exact ⟨resolutionCoefficient φ p, (resolutionAugmentation_coefficient φ p).trans hp⟩
  degree_zero := mem_resolutionAlgebra_grade_zero_iff φ
  augmentation_coefficient := AlgHom.ext (resolutionAugmentation_coefficient φ)
  augmentation_positive := fun n a hn ha =>
    resolutionAugmentation_positive φ (Nat.pos_iff_ne_zero.1 hn) ha
  augmentation_differential := resolutionAugmentation_differential φ
  exact_zero := by
    intro a ha haug
    obtain ⟨p, hp⟩ := (mem_resolutionAlgebra_grade_zero_iff φ a).1 ha
    have hker : resolutionPresentation φ ((resolutionCoefficientEquiv R S σ).symm p) = 0 := by
      refine (resolutionAugmentation_base φ _).symm.trans ?_
      rw [← hp] at haug
      exact haug
    obtain ⟨j, hj⟩ := exists_tateBase_cycle_eq.{u, max v w} (R := R)
      (resolutionCoefficientRing R S σ) (RingHom.ker (resolutionPresentation φ))
      (RingHom.mem_ker.2 hker)
    obtain ⟨b, hb, hdb⟩ :=
      exists_tateColimitDifferential_boundary_of_base (resolutionBase φ) j
    refine ⟨b, hb, ?_⟩
    rw [hdb, hj, ← hp]
    rfl
  exact_positive := by
    intro n a hn ha hda
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.1 hn)
    exact exists_tateColimitDifferential_boundary_of_cycle (resolutionBase φ) m ha hda

end Existence

end DividedPowers.TateResolution

end
