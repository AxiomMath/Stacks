module

public import StacksFrontier.RingTheory.Rig.FiniteTypeCompletions
public import StacksFrontier.RingTheory.Rig.RigEtaleAdicCompletionAscent
public import StacksFrontier.RingTheory.Rig.RigSmoothTower

/-!
# Rig-smoothness ascends to the completion of the base

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `Â` the `I`-adic completion of `A`. For a ring
map `φ : Â → R`, rig-smoothness of `R` over `(A, I)`, through `A → Â → R`, implies
rig-smoothness of `R` over `(Â, IÂ)`.

It is the step "`A^∧ → (A')^∧` is rig-smooth" in the source's proof of **Stacks 0GDH**: part (1)
of Stacks 0GAK makes `(A')^∧` rig-smooth over `(A, I)`, which is a statement over the
non-complete base `A`, while the arrow of `WAdm^{Noeth}` presenting the chart square is
`A^∧ → (A')^∧`. This is the rig-smooth counterpart of
`Rig.isRigEtaleOver_adicCompletion_of_isRigEtaleOver`.

## Main results

* `Rig.IsRigSmoothOver`: rig-smoothness of the algebra defined by a ring map over an ideal.
* `Rig.isRigSmoothOver_adicCompletion_of_isRigSmoothOver`: the statement above.

## Implementation notes

`Â` is itself an object of the category of Stacks 0AL4 over `(A, I)`, namely the completion of
the étale (identity) `A`-algebra `A`, so it has a completed polynomial presentation whose completed
naive cotangent complex has bijective differential (`Rig.exists_presentation_bijective_of_etale`,
from Stacks 0GAF). The transitivity sequence of Stacks 0ALM for `A → Â → R` then moves the
annihilation of `Ext¹` from `NL^∧_{R/A}` to `NL^∧_{R/Â}`
(`Rig.isRigSmooth_of_isRigSmooth_of_bijective`).

## References

* [Stacks Project, Tag 0GAF](https://stacks.math.columbia.edu/tag/0GAF)
* [Stacks Project, Tag 0GAK](https://stacks.math.columbia.edu/tag/0GAK)
* [Stacks Project, Tag 0ALM](https://stacks.math.columbia.edu/tag/0ALM)
* [Stacks Project, Tag 0GDH](https://stacks.math.columbia.edu/tag/0GDH)
-/

@[expose] public noncomputable section

universe u v

namespace Rig

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}

/-- The `I`-adic completion of a Noetherian ring is complete for the extension of `I`. -/
theorem isAdicComplete_map_adicCompletion :
    IsAdicComplete (I.map (algebraMap A (AdicCompletion I A))) (AdicCompletion I A) := by
  have h := adicCompletion_isAdicallyComplete A I A
  generalize hJ : I.map (algebraMap A A) = J at h
  rw [Algebra.algebraMap_self, Ideal.map_id] at hJ
  subst hJ
  exact h

/-- The reduction `Â / IÂ` of the `I`-adic completion is of finite type over `A / I`: the map
`A / I → Â / IÂ` is onto. -/
theorem finiteType_quotient_map_adicCompletion :
    Algebra.FiniteType (A ⧸ I)
      (AdicCompletion I A ⧸ I.map (algebraMap A (AdicCompletion I A))) := by
  refine RingHom.finiteType_algebraMap.mp (RingHom.FiniteType.of_surjective _ fun y ↦ ?_)
  obtain ⟨a, rfl⟩ := surjective_quotientMk_comp_algebraMap_adicCompletion I y
  exact ⟨Ideal.Quotient.mk I a, rfl⟩

/-- The `I`-adic completion `Â` of a Noetherian ring, as an object of the category of Stacks 0AL4
over `(A, I)`. -/
abbrev adicCompletionBaseObj : AdicFiniteTypeAlgebra.{u, u} A I :=
  ⟨CommAlgCat.of A (AdicCompletion I A), isAdicComplete_map_adicCompletion,
    finiteType_quotient_map_adicCompletion⟩

/-- `Â` has, over `(A, I)`, a completed polynomial presentation whose completed naive cotangent
complex has bijective differential: it is the completion of the étale `A`-algebra `A`. -/
theorem exists_presentation_bijective_adicCompletionBaseObj :
    ∃ Q : CompletedPolynomialPresentation I (adicCompletionBaseObj (I := I)),
      Function.Bijective (completedNaiveCotangentComplex _ Q).differential := by
  have hid : (RingHom.id A).Etale := by
    rw [RingHom.Etale, show (RingHom.id A).toAlgebra = Algebra.id A from Algebra.algebra_ext _ _
      fun _ ↦ rfl]
    infer_instance
  have he : ∀ J : Ideal A, J = I → ∃ e : AdicCompletion J A ≃+* AdicCompletion I A,
      ∀ s, e (algebraMap A (AdicCompletion J A) s) = algebraMap A (AdicCompletion I A) s := by
    rintro _ rfl
    exact ⟨RingEquiv.refl _, fun _ ↦ rfl⟩
  obtain ⟨e, he⟩ := he (I.map (RingHom.id A)) (Ideal.map_id I)
  exact exists_presentation_bijective_of_etale I (RingHom.id A) hid _ e he

/-- Rig-smoothness of the algebra defined by a ring homomorphism over a specified ideal, with
the completeness and finite-type data required for the algebra object: the rig-smooth
counterpart of `Rig.IsRigEtaleOver`. -/
abbrev IsRigSmoothOver {A : Type u} {B : Type v} [CommRing A] [IsNoetherianRing A] [CommRing B]
    (φ : A →+* B) (I : Ideal A) : Prop :=
  letI : Algebra A B := φ.toAlgebra
  ∃ hc : IsAdicComplete (I.map (algebraMap A B)) B,
    ∃ hf : Algebra.FiniteType (A ⧸ I) (B ⧸ I.map (algebraMap A B)),
      letI : Algebra.FiniteType (A ⧸ I) (B ⧸ I.map (algebraMap A B)) := hf
      IsRigSmooth (AdicFiniteTypeAlgebra.of (I := I) B hc)

/-- **Rig-smoothness over the base ascends to the completion of the base.** Let `A` be a
Noetherian ring, `I ⊆ A` an ideal, `Â` the `I`-adic completion of `A` and `φ : Â → R` a ring map.
If `R`, regarded as an `A`-algebra through `A → Â → R`, is rig-smooth over `(A, I)`, then `R` is
rig-smooth over `(Â, IÂ)`, with the same completeness and finite type data. -/
theorem isRigSmoothOver_adicCompletion_of_isRigSmoothOver {R : Type u} [CommRing R]
    (φ : AdicCompletion I A →+* R)
    (h : IsRigSmoothOver (φ.comp (algebraMap A (AdicCompletion I A))) I) :
    IsRigSmoothOver φ (I.map (algebraMap A (AdicCompletion I A))) := by
  obtain ⟨hc, hf, hrig⟩ := h
  let : Algebra (AdicCompletion I A) R := φ.toAlgebra
  let : Algebra A R := (φ.comp (algebraMap A (AdicCompletion I A))).toAlgebra
  let := hf
  obtain ⟨hc', hf'⟩ := adicFiniteType_adicCompletion_of_adicFiniteType φ hc hf
  refine ⟨hc', hf', ?_⟩
  let := hf'
  let base : AdicFiniteTypeAlgebra.{u, u} A I := adicCompletionBaseObj
  let total : AdicFiniteTypeAlgebra.{u, u} A I := AdicFiniteTypeAlgebra.of (I := I) R hc
  let : Algebra base.carrier total.carrier := φ.toAlgebra
  have : IsScalarTower A base.carrier total.carrier := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsNoetherianRing base.carrier :=
    inferInstanceAs (IsNoetherianRing (AdicCompletion I A))
  let : Algebra.FiniteType (base.carrier ⧸ base.adicIdeal)
      (total.carrier ⧸ base.adicIdeal.map (algebraMap base.carrier total.carrier)) := hf'
  obtain ⟨Q, hQ⟩ := exists_presentation_bijective_adicCompletionBaseObj (I := I)
  exact isRigSmooth_of_isRigSmooth_of_bijective (base := base) (total := total) hc' Q hQ hrig

end Rig

end
