module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.IteratedMvPolynomial
public import StacksFrontier.RingTheory.Rig.Algebraization.AlgebraizationTower
public import StacksFrontier.RingTheory.Rig.Algebraization.GeneratorDrop
public import StacksFrontier.RingTheory.Rig.Algebraization.RigEtaleAlgebraizationAux
public import StacksFrontier.RingTheory.Rig.Algebraization.RigEtaleAlgebraizationTower
public import StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroLift

/-!
# Algebraization of rig-étale algebras

Let `A` be a Noetherian ring and `I ⊆ A` an ideal, and let `B` be an `I`-adically complete
`A`-algebra whose reduction modulo `I` is of finite type over `A ⧸ I` (an object of
`Rig.AdicFiniteTypeAlgebra A I`). If `B` is rig-étale over `(A, I)`, then it is the `I`-adic
completion of a finite type `A`-algebra. Moreover `B` is rig-étale if and only if `B ≅ C^∧` for a
finite type `A`-algebra `C` étale over `Spec(A) ∖ V(I)`.

## Main results

* `Rig.exists_finiteType_algEquiv_of_isRigEtale_span`: the algebraization for `I` the span of a
  finite set and `B` in the universe of `A`.
* `Rig.exists_finiteType_algEquiv_adicCompletion_of_isRigEtale`: a rig-étale `B` is the `I`-adic
  completion of a finite type `A`-algebra.
* `Rig.isRigEtale_iff_exists_isEtaleOutside_algEquiv`: `B` is rig-étale if and only if `B ≅ C^∧`
  for a finite type `A`-algebra `C` étale over `Spec(A) ∖ V(I)`.

## References

* [Stacks Project, Tag 0AKA](https://stacks.math.columbia.edu/tag/0AKA)
* [Stacks Project, Tag 0AKG](https://stacks.math.columbia.edu/tag/0AKG)
* [Stacks Project, Tag 0ALQ](https://stacks.math.columbia.edu/tag/0ALQ)
* [Stacks Project, Tag 0ALS](https://stacks.math.columbia.edu/tag/0ALS)
-/

@[expose] public section

namespace Rig

universe u v

/-- Let `A` be a Noetherian ring and `s` a finite subset of `A` with at most `n` elements. A
rig-étale object `B` over `(A, (s))` whose carrier lies in the universe of `A` is isomorphic to
the `(s)`-adic completion of a finite type `A`-algebra. -/
public theorem exists_finiteType_algEquiv_of_isRigEtale_span (n : ℕ) :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (s : Finset A), s.card ≤ n →
      ∀ B : AdicFiniteTypeAlgebra.{u, u} A (Ideal.span (s : Set A)), IsRigEtale B →
        ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C),
          Algebra.FiniteType A C ∧
            Nonempty (B.carrier ≃ₐ[A]
              AdicCompletion ((Ideal.span (s : Set A)).map (algebraMap A C)) C) := by
  classical
  induction n with
  | zero =>
    intro A _ _ s hs B hB
    exact exists_finiteType_algEquiv_of_isRigEtale_of_card_le_one (hs.trans zero_le_one) B hB
  | succ n ih =>
    intro A _ _ s hs B hB
    rcases le_or_gt s.card 1 with h1 | h1
    · exact exists_finiteType_algEquiv_of_isRigEtale_of_card_le_one h1 B hB
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (zero_lt_one.trans h1)
    have hcard : (s.erase a).card ≤ n := by
      rw [Finset.card_erase_of_mem ha]
      lia
    have hs' : Ideal.span (s : Set A) = Ideal.span (insert a ((s.erase a : Finset A) : Set A)) := by
      rw [← Finset.coe_insert, Finset.insert_erase ha]
    revert B
    rw [hs']
    intro B hB
    refine exists_finiteType_algEquiv_of_algebraizes_quotients (s.erase a) a ?_ B hB
    intro m _ B' hB'
    have h := ih ((s.erase a).image (Ideal.Quotient.mk (Ideal.span {a ^ m})))
      (Finset.card_image_le.trans hcard)
    rw [Finset.coe_image] at h
    exact h B' hB'

/-- Let `A` be a Noetherian ring and `I ⊆ A` an ideal. If `B` is an object of
`Rig.AdicFiniteTypeAlgebra A I` which is rig-étale over `(A, I)`, then there is a finite type
`A`-algebra `C` and an isomorphism `B ≅ C^∧` with its `I`-adic completion. -/
@[stacks 0AKA]
public theorem exists_finiteType_algEquiv_adicCompletion_of_isRigEtale
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (hB : IsRigEtale B) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C),
      Algebra.FiniteType A C ∧
        Nonempty (B.carrier ≃ₐ[A] AdicCompletion (I.map (algebraMap A C)) C) := by
  obtain ⟨P⟩ := nonempty_completedPolynomialPresentation (Ideal.fg_of_isNoetherianRing I) B
  have he : (PerturbedPresentation.quotientObj A I P.variableCount P.ideal).carrier ≃ₐ[A]
      B.carrier := P.quotientEquiv
  obtain ⟨s, rfl⟩ := Ideal.fg_of_isNoetherianRing I
  obtain ⟨C, _, _, hCft, ⟨E⟩⟩ := exists_finiteType_algEquiv_of_isRigEtale_span s.card s le_rfl
    (PerturbedPresentation.quotientObj A _ P.variableCount P.ideal)
    (isRigEtale_of_algEquiv he hB)
  exact ⟨C, inferInstance, inferInstance, hCft, ⟨he.symm.trans E⟩⟩

/-- Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `B` an `I`-adically complete `A`-algebra
with `A ⧸ I → B ⧸ IB` of finite type. Then `B` is rig-étale if and only if there is a finite type
`A`-algebra `C` with `Spec(C) → Spec(A)` étale over `Spec(A) ∖ V(I)` and an isomorphism
`B ≅ C^∧` of `A`-algebras. -/
@[stacks 0AKG]
public theorem isRigEtale_iff_exists_isEtaleOutside_algEquiv
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    (B : AdicFiniteTypeAlgebra.{u, v} A I) :
    IsRigEtale B ↔
      ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C),
        Algebra.FiniteType A C ∧ IsEtaleOutside I C ∧
          Nonempty (B.carrier ≃ₐ[A] AdicCompletion (I.map (algebraMap A C)) C) := by
  constructor
  · intro hB
    obtain ⟨C, _, _, hCft, ⟨e⟩⟩ := exists_finiteType_algEquiv_adicCompletion_of_isRigEtale B hB
    have hC : IsRigEtale (adicCompletionObj I (B := C)) := isRigEtale_of_algEquiv e.symm hB
    obtain ⟨g, hg, hgEt⟩ := exists_isEtaleOutside_localization_of_isRigEtale_adicCompletionObj I hC
    obtain ⟨E, -⟩ := exists_adicCompletion_algEquiv_away (I.map (algebraMap A C)) hg
    have hJ : (I.map (algebraMap A C)).map (algebraMap C (Localization.Away g)) =
        I.map (algebraMap A (Localization.Away g)) := by
      rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    exact ⟨Localization.Away g, inferInstance, inferInstance, inferInstance, hgEt,
      ⟨(e.trans (E.restrictScalars A)).trans (AdicCompletion.congrAlgEquiv AlgEquiv.refl
        (by rw [AlgEquiv.refl_toRingHom, Ideal.map_id, hJ]))⟩⟩
  · rintro ⟨C, _, _, hCft, hCet, ⟨e⟩⟩
    exact isRigEtale_of_isEtaleOutside_of_algEquiv hCet e

end Rig

end
