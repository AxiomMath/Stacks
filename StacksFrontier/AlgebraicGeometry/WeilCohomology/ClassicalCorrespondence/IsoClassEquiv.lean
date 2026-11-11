module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalCorrespondence.Injective
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalCorrespondence.Surjective

/-!
# Stacks 0FH3: classical Weil cohomology theories are realizations of Chow motives

For `k` algebraically closed and `F` of characteristic zero, isomorphism classes of classical Weil
cohomology theories (Stacks 0FGV, over the Chow groups of Chapter 42) are in bijection with
isomorphism classes of `ℚ`-linear functors `G : M_k ⥤ graded F-vector spaces` of symmetric monoidal
categories with an isomorphism `F[2] ≅ G(𝟏(1))`, `G(h(X))` in nonnegative degrees and
`dim_F G⁰(h(X)) = 1` (`Stacks.WeilCohomology.ClassicalMotiveRealization`), a theory corresponding
to a realization exactly when `H^*(X) = G(h(X))` with all its structure.

* A realization gives the theory `H^*(X) = G(h(X))` (the first paragraph of the proof;
  `ClassicalMotiveRealization.toClassicalWeilCohomologyTheory`), which corresponds to it.
* Every theory corresponds to a realization (the second paragraph, through Stacks 0FH2, 0FHL,
  0FHM; `ClassicalWeilCohomologyTheory.exists_corresponds`).
* A realization is determined up to isomorphism by its theory (through Stacks 0FHM and the
  uniqueness of Stacks 0FGH; `ClassicalMotiveRealization.nonempty_iso_of_iso`).

## Main results

* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.exists_isoClassEquiv`: **Stacks 0FH3**.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [CharZero F]

/-- **Stacks Project, Tag 0FH3.** Let `k` be an algebraically closed field and `F` a field of
characteristic `0`. A classical Weil cohomology theory (Stacks 0FGV, over the Chow groups of
Chapter 42) is the same thing as a `ℚ`-linear functor `G : M_k ⥤ graded F-vector spaces` of
symmetric monoidal categories together with an isomorphism `F[2] ≅ G(𝟏(1))` such that `G(h(X))`
lives in nonnegative degrees and `dim_F G⁰(h(X)) = 1` for every smooth projective variety `X`
(`ClassicalMotiveRealization`): there is a bijection `e` between isomorphism classes of the two,
under which a theory `H^*` and a realization `R = (G, F[2] ≅ G(𝟏(1)))` correspond exactly when
`H^*(X) = G(h(X))` with all its structure (`ClassicalWeilCohomologyTheory.Corresponds`: natural
isomorphisms of graded algebras `H^*(X) ≅ G(h(X))`, carrying `γ(α)` to `G(a_α)(e_{-r})` and `∫_X`
to `x ↦ G([X])(x ⊗ e_d)`, for the generators `eₙ` of `F[2] ≅ G(𝟏(1))`). The inverse bijection
sends `R` to the theory `H^*(X) = G(h(X))` of the first paragraph of the proof
(`ClassicalMotiveRealization.toClassicalWeilCohomologyTheory`). -/
@[stacks 0FH3 "a classical Weil cohomology theory is the same thing as a Q-linear symmetric \
monoidal G : M_k → graded F-vector spaces with F[2] ≅ G(1(1)), G(h(X)) in nonnegative degrees \
and dim G⁰(h(X)) = 1: a bijection of isomorphism classes, through H^*(X) = G(h(X)) with its cup \
product, pullbacks, cycle classes and traces"]
theorem ClassicalWeilCohomologyTheory.exists_isoClassEquiv :
    ∃ e : Quotient (ClassicalWeilCohomologyTheory.isoSetoid.{u, v, v, u} k F (chowCycleData k)) ≃
        Quotient (ClassicalMotiveRealization.isoSetoid k F),
      (∀ (T : ClassicalWeilCohomologyTheory.{u, v, v, u} k F (chowCycleData k))
        (R : ClassicalMotiveRealization k F), e ⟦T⟧ = ⟦R⟧ ↔ T.Corresponds R) ∧
      ∀ R : ClassicalMotiveRealization k F, e.symm ⟦R⟧ = ⟦R.toClassicalWeilCohomologyTheory⟧ := by
  have hΦ : ∀ T : ClassicalWeilCohomologyTheory.{u, v, v, u} k F (chowCycleData k),
      T.Corresponds (ClassicalWeilCohomologyTheory.exists_corresponds T).choose :=
    fun T ↦ (ClassicalWeilCohomologyTheory.exists_corresponds T).choose_spec
  have hβ : ∀ (T : ClassicalWeilCohomologyTheory.{u, v, v, u} k F (chowCycleData k))
      (R R' : ClassicalMotiveRealization k F), T.Corresponds R → T.Corresponds R' →
      Nonempty (ClassicalMotiveRealization.Iso R R') := by
    intro T R R' hR hR'
    obtain ⟨e₁⟩ := R.corresponds_toClassicalWeilCohomologyTheory.nonempty_iso hR
    obtain ⟨e₂⟩ := hR'.nonempty_iso R'.corresponds_toClassicalWeilCohomologyTheory
    exact ClassicalMotiveRealization.nonempty_iso_of_iso (e₁.trans e₂)
  obtain ⟨e, he, he'⟩ := exists_quotientEquiv_of_rel
    (sα := ClassicalWeilCohomologyTheory.isoSetoid.{u, v, v, u} k F (chowCycleData k))
    (sβ := ClassicalMotiveRealization.isoSetoid k F)
    ClassicalWeilCohomologyTheory.Corresponds
    (fun T ↦ (ClassicalWeilCohomologyTheory.exists_corresponds T).choose)
    ClassicalMotiveRealization.toClassicalWeilCohomologyTheory hΦ
    (fun R ↦ R.corresponds_toClassicalWeilCohomologyTheory)
    (fun _ _ _ ⟨e⟩ h ↦ h.of_iso e) (fun _ _ _ ⟨e⟩ h ↦ h.of_realizationIso e)
    (fun _ _ _ h h' ↦ h.nonempty_iso h') (fun T R h ↦ hβ T _ R (hΦ T) h)
  refine ⟨e, fun T R ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩, he'⟩
  · rw [he] at h
    obtain ⟨i⟩ := Quotient.exact h
    exact (hΦ T).of_realizationIso i
  · rw [he]
    exact Quotient.sound (hβ T _ R (hΦ T) h)

end Stacks.WeilCohomology

end
