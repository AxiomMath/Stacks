module

public import StacksFrontier.AlgebraicGeometry.Blowup.ProjectiveSpaceEmbedding
public import StacksFrontier.AlgebraicGeometry.TwoGeneratorSquare

/-!
# The blowup in a two-generated centre sits inside the two-generator modification

Let `f₁, f₂` be elements of a commutative ring `A` and let `I = (f₁,f₂)`. Placing the two
generators in degree one presents the Rees algebra `⨁ₙ Iⁿ` as a graded quotient of `A[T₀,T₁]`
(`Stacks.Blowup.reesPresentation`), and that presentation kills `f₂T₀-f₁T₁`, because `f₂·f₁` and
`f₁·f₂` are the same element of `I`. So it factors through the modification ring
`A[T₀,T₁]/(f₂T₀-f₁T₁)` of the two-generator square of
`StacksFrontier/AlgebraicGeometry/TwoGeneratorSquare.lean`, and the factorisation is still
surjective. Taking `Proj` therefore exhibits the blowup of `Spec A` in `I` as a closed subscheme
of the modification `X' = Proj (A[T₀,T₁]/(f₂T₀-f₁T₁))`, over `Spec A`.

## Main definitions

* `Stacks.AlmostBlowUp.centerGens` is the pair `(f₁,f₂)` as a family indexed by `Fin 2`.
* `Stacks.AlmostBlowUp.reesQuotRingHom` is the ring map `A[T₀,T₁]/(f₂T₀-f₁T₁) ⟶ ⨁ₙ Iⁿ`.
* `Stacks.AlmostBlowUp.reesQuotPresentation` is that map as a homomorphism of graded rings.
* `Stacks.AlmostBlowUp.blowUpSpecToModification` is the induced morphism from the blowup of
  `Spec A` in `I` to the modification.

## Main results

* `Stacks.AlmostBlowUp.surjective_reesQuotPresentation`: the presentation of the Rees algebra by
  the modification ring is surjective.
* `Stacks.AlmostBlowUp.isClosedImmersion_blowUpSpecToModification`: the blowup of `Spec A` in
  `(f₁,f₂)` is a closed subscheme of the modification.
* `Stacks.AlmostBlowUp.blowUpSpecToModification_comp_modificationToBase`: it is a closed
  subscheme **over `Spec A`**.

## Implementation notes

Everything is deduced from `Stacks.Blowup.reesPresentation` and the lemmas around it; the only
new input is that the relation of the square dies, which is checked inside `A[X]` through
`Stacks.Blowup.coe_reesPresentation_apply`: a homogeneous polynomial of degree `n` goes to `Xⁿ`
times its value at `(f₁,f₂)`, and the value of `f₂T₀-f₁T₁` there is zero.

The degree-zero comparison is the same computation as
`Stacks.Blowup.gradedZeroRingHom_reesPresentation_comp_gradeZeroEquiv`, with
`Stacks.AlmostBlowUp.baseRingHom` in place of
`AlgebraicGeometry.ProjectiveSpace.gradeZeroEquiv`: both degree-zero identifications send `a` to
the constant `a`, and the presentation sends a constant polynomial to the corresponding element
of the Rees algebra.

This is one half of condition (4) in the definition of an almost blowup square (Tag 0EV6) for the
two-generator square of Tag 0EVH. The other half — that this closed subscheme is cut out by the
ideal of sections of `𝒪_{X'}` supported on the exceptional subscheme — is
`Stacks.AlmostBlowUp.supportedSectionsIdeal_eq_ker_blowUpSpecToModification` in
`StacksFrontier/AlgebraicGeometry/Blowup/TwoGeneratorSupportedSections.lean`, which turns the
inclusion proved here into the equality condition (4) asks for, and from which that file deduces
`Stacks.AlmostBlowUp.isAlmostBlowUpSquare_modificationToBase`. No `@[stacks 0EVH]` attribute is
attached here, because an inclusion of the blowup into the modification is on its own strictly
weaker than condition (4).

## References

* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
* [Stacks Project, Tag 0EV6](https://stacks.math.columbia.edu/tag/0EV6)
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Stacks.Blowup

universe u

namespace Stacks.AlmostBlowUp

attribute [local instance] MvPolynomial.gradedAlgebra

variable (A : Type u) [CommRing A] (f₁ f₂ : A)

/-! ### The two generators of the centre -/

/-- The pair `(f₁, f₂)` of generators of the centre, as a family indexed by `Fin 2`. -/
def centerGens : Fin 2 → A := ![f₁, f₂]

omit [CommRing A] in
/-- The first generator of the centre is `f₁`. -/
@[simp] theorem centerGens_zero : centerGens A f₁ f₂ 0 = f₁ := rfl

omit [CommRing A] in
/-- The second generator of the centre is `f₂`. -/
@[simp] theorem centerGens_one : centerGens A f₁ f₂ 1 = f₂ := rfl

/-- Each generator `centerGens A f₁ f₂ i` lies in the ideal `(f₁,f₂)`. -/
theorem centerGens_mem (i : Fin 2) : centerGens A f₁ f₂ i ∈ centerIdeal A f₁ f₂ :=
  Ideal.subset_span (by fin_cases i <;> simp)

/-- The ideal `(f₁,f₂)` is spanned by the range of `centerGens A f₁ f₂`. -/
theorem centerIdeal_eq_span_range :
    centerIdeal A f₁ f₂ = Ideal.span (Set.range (centerGens A f₁ f₂)) := by
  have h : Set.range (centerGens A f₁ f₂) = ({f₁, f₂} : Set A) := by
    ext x
    refine ⟨?_, ?_⟩
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hx
      rcases hx with rfl | hx
      · exact ⟨0, rfl⟩
      · rw [Set.mem_singleton_iff] at hx
        exact ⟨1, hx.symm⟩
  rw [h]

/-- The polynomial presentation of the Rees algebra of `(f₁,f₂)` attached to the two
generators. -/
abbrev centerReesPresentation :
    MvPolynomial.homogeneousSubmodule (Fin 2) A →+*ᵍ reesGrading (centerIdeal A f₁ f₂) :=
  reesPresentation (centerIdeal A f₁ f₂) (centerGens A f₁ f₂) (centerGens_mem A f₁ f₂)

/-! ### The relation of the square dies in the Rees algebra -/

/-- **The relation of the two-generator square dies in the Rees algebra.** Both `f₂T₀` and
`f₁T₁` go to the degree-one element `f₁f₂` of `⨁ₙ (f₁,f₂)ⁿ`. -/
theorem centerReesPresentation_relation_eq_zero :
    (centerReesPresentation A f₁ f₂).toRingHom
        (MvPolynomial.C f₂ * MvPolynomial.X (0 : Fin 2) -
          MvPolynomial.C f₁ * MvPolynomial.X (1 : Fin 2)) = 0 := by
  have hp : (MvPolynomial.C f₂ * MvPolynomial.X (0 : Fin 2) -
      MvPolynomial.C f₁ * MvPolynomial.X (1 : Fin 2)).IsHomogeneous 1 :=
    (MvPolynomial.mem_homogeneousSubmodule 1 _).mp (relation_mem_homogeneousSubmodule A f₁ f₂)
  refine Subtype.ext ?_
  rw [show ((centerReesPresentation A f₁ f₂).toRingHom
      (MvPolynomial.C f₂ * MvPolynomial.X (0 : Fin 2) -
        MvPolynomial.C f₁ * MvPolynomial.X (1 : Fin 2)) :
        reesAlgebra (centerIdeal A f₁ f₂)) =
      centerReesPresentation A f₁ f₂ (MvPolynomial.C f₂ * MvPolynomial.X (0 : Fin 2) -
        MvPolynomial.C f₁ * MvPolynomial.X (1 : Fin 2)) from rfl,
    coe_reesPresentation_apply (centerIdeal A f₁ f₂) (centerGens A f₁ f₂)
      (centerGens_mem A f₁ f₂) hp]
  simp [mul_comm]

/-- The ideal `(f₂T₀-f₁T₁)` lies in the kernel of the polynomial presentation of the Rees algebra
of `(f₁,f₂)`. -/
theorem relationIdeal_le_ker_centerReesPresentation :
    relationIdeal A f₁ f₂ ≤ RingHom.ker (centerReesPresentation A f₁ f₂).toRingHom := by
  rw [relationIdeal, Ideal.span_le]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  exact hx ▸ RingHom.mem_ker.mpr (centerReesPresentation_relation_eq_zero A f₁ f₂)

/-! ### The presentation of the Rees algebra by the modification ring -/

/-- **The Rees algebra of `(f₁,f₂)` is a quotient of the modification ring.** The polynomial
presentation kills the relation `f₂T₀-f₁T₁`, so it descends to `A[T₀,T₁]/(f₂T₀-f₁T₁)`. -/
def reesQuotRingHom :
    modificationRing A f₁ f₂ →+* reesAlgebra (centerIdeal A f₁ f₂) :=
  Ideal.Quotient.lift (relationIdeal A f₁ f₂) (centerReesPresentation A f₁ f₂).toRingHom
    fun _ hp => RingHom.mem_ker.mp (relationIdeal_le_ker_centerReesPresentation A f₁ f₂ hp)

/-- `reesQuotRingHom A f₁ f₂` sends the class of a polynomial `p` to the image of `p` under the
polynomial presentation of the Rees algebra. -/
@[simp]
theorem reesQuotRingHom_mk (p : MvPolynomial (Fin 2) A) :
    reesQuotRingHom A f₁ f₂ (Ideal.Quotient.mk (relationIdeal A f₁ f₂) p) =
      (centerReesPresentation A f₁ f₂).toRingHom p := rfl

/-- **The presentation of the Rees algebra by the modification ring, as a graded map.** The
degree-`d` part of the modification grading is the image of the homogeneous polynomials of
degree `d`, each of which the polynomial presentation sends into the degree-`d` part of the Rees
algebra. -/
def reesQuotPresentation :
    modificationGrading A f₁ f₂ →+*ᵍ reesGrading (centerIdeal A f₁ f₂) where
  __ := reesQuotRingHom A f₁ f₂
  map_mem := by
    intro d x hx
    obtain ⟨p, hp, rfl⟩ := AddSubgroup.mem_map.mp hx
    exact GradedRingHom.map_mem (centerReesPresentation A f₁ f₂)
      (Iff.mp (Submodule.mem_toAddSubgroup _) hp)

/-- `reesQuotPresentation A f₁ f₂` sends the class of a polynomial `p` to the image of `p` under
the polynomial presentation of the Rees algebra. -/
@[simp]
theorem reesQuotPresentation_mk (p : MvPolynomial (Fin 2) A) :
    reesQuotPresentation A f₁ f₂ (Ideal.Quotient.mk (relationIdeal A f₁ f₂) p) =
      (centerReesPresentation A f₁ f₂).toRingHom p := rfl

/-- **The presentation of the Rees algebra by the modification ring is surjective.** The
polynomial presentation already is, and the modification ring is a quotient of the polynomial
ring. -/
theorem surjective_reesQuotPresentation :
    Function.Surjective (reesQuotPresentation A f₁ f₂) := by
  intro y
  obtain ⟨p, hp⟩ := surjective_reesPresentation (centerIdeal A f₁ f₂) (centerGens A f₁ f₂)
    (centerGens_mem A f₁ f₂) (centerIdeal_eq_span_range A f₁ f₂) y
  exact ⟨Ideal.Quotient.mk (relationIdeal A f₁ f₂) p, hp⟩

/-! ### The blowup as a closed subscheme of the modification -/

/-- **The blowup of `Spec A` in `(f₁,f₂)` maps to the two-generator modification.** -/
def blowUpSpecToModification :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    blowUpSpec (centerIdeal A f₁ f₂) ⟶
      AlgebraicGeometry.Proj (modificationGrading A f₁ f₂) :=
  letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
  Proj.map (reesQuotPresentation A f₁ f₂)
    (Proj.irrelevant_le_map_of_surjective _ (surjective_reesQuotPresentation A f₁ f₂))

/-- **The blowup of `Spec A` in `(f₁,f₂)` is a closed subscheme of the two-generator
modification.** -/
instance isClosedImmersion_blowUpSpecToModification :
    IsClosedImmersion (blowUpSpecToModification A f₁ f₂) :=
  letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
  Proj.isClosedImmersion_map_of_surjective _ (surjective_reesQuotPresentation A f₁ f₂)

/-- The presentation of the Rees algebra by the modification ring is the identity on the
coefficient ring: the degree-zero part of the modification grading is a copy of `A` through the
constants, that of the Rees algebra through `algebraMap`, and a constant polynomial goes to the
corresponding element of the Rees algebra. -/
theorem gradedZeroRingHom_reesQuotPresentation_comp_baseRingHom :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    (reesQuotPresentation A f₁ f₂).gradedZeroRingHom.comp (baseRingHom A f₁ f₂) =
      (reesGradingZeroEquiv (centerIdeal A f₁ f₂)).toRingHom := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  refine RingHom.ext fun r ↦ Subtype.ext ?_
  have htgt : (((reesGradingZeroEquiv (centerIdeal A f₁ f₂)).toRingHom r :
        reesGrading (centerIdeal A f₁ f₂) 0) : reesAlgebra (centerIdeal A f₁ f₂)) =
      algebraMap A (reesAlgebra (centerIdeal A f₁ f₂)) r :=
    SetLike.GradeZero.coe_algebraMap (reesGrading (centerIdeal A f₁ f₂)) r
  exact (reesQuotPresentation_mk A f₁ f₂ (MvPolynomial.C r)).trans
    ((MvPolynomial.eval₂Hom_C _ _ r).trans htgt.symm)

/-- **The blowup of `Spec A` in `(f₁,f₂)` is a closed subscheme of the two-generator modification
over `Spec A`.** The composite of `blowUpSpecToModification A f₁ f₂` with the structure morphism
of the modification is the structure morphism of the blowup. -/
theorem blowUpSpecToModification_comp_modificationToBase :
    blowUpSpecToModification A f₁ f₂ ≫ modificationToBase A f₁ f₂ =
      Stacks.Blowup.toSpec (centerIdeal A f₁ f₂) := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  have key : Proj.map (reesQuotPresentation A f₁ f₂)
        (Proj.irrelevant_le_map_of_surjective _ (surjective_reesQuotPresentation A f₁ f₂)) ≫
        (Proj.toSpecZero (modificationGrading A f₁ f₂) ≫
          Spec.map (CommRingCat.ofHom (baseRingHom A f₁ f₂))) =
      Proj.toSpecZero (reesGrading (centerIdeal A f₁ f₂)) ≫
        Spec.map (CommRingCat.ofHom
          (reesGradingZeroEquiv (centerIdeal A f₁ f₂)).toRingHom) := by
    rw [Proj.map_toSpecZero_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      gradedZeroRingHom_reesQuotPresentation_comp_baseRingHom A f₁ f₂]
  exact key

end Stacks.AlmostBlowUp

end
