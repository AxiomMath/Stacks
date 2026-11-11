module

public import StacksFrontier.Algebra.Homology.SpectralSequence.Defs.FilteredComplex
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Canonical
public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex.Convergence

/-!
# Convergence of the spectral sequence of a degreewise finite filtered complex

Let `(K^•, F)` be a filtered complex of an abelian category whose filtration is finite in every
degree. [Stacks, Tag 012W] and, for double complexes, [Stacks, Tag 0132] conclude that its
spectral sequence is bounded, induces finite filtrations on cohomology and converges to
`H^*(K^•)`; in `CochainComplex.isBounded_and_converges_of_isDegreewiseFinite` and
`HomologicalComplex₂.isBounded_and_converges_totalFiltration₁` this convergence is stated by its
ingredients. This file assembles them into the convergence predicate of [Stacks, Tag 012U],
`CochainComplex.Filtered.Converges`: the spectral sequence is regular, abuts to `H^*(K^•)`
(the induced filtrations are separated and exhaustive and `gr^pH^n(K^•) = E_∞^{p,n-p}`), and each
`H^n(K^•)` is the limit of its quotients by the induced filtration.

## Main results

* `CategoryTheory.Filtration.isComplete_of_eventually_eq_zero`: a `ℤᵒᵖ`-filtration which is zero
  from some step on is complete.
* `CochainComplex.Filtered.converges_of_isDegreewiseFinite`: the spectral sequence of a degreewise
  finite filtered complex converges to `H^*(K^•)` ([Stacks, Tag 012U]).
* `HomologicalComplex₂.convergesToTotalHomology₁_of_finite`,
  `HomologicalComplex₂.convergesToTotalHomology₂_of_finite`: both spectral sequences of a double
  complex with finite antidiagonals converge to `H^*(Tot(K^{•,•}))` ([Stacks, Tag 0131]).

## References

* [Stacks Project, Tag 012U](https://stacks.math.columbia.edu/tag/012U)
* [Stacks Project, Tag 012W](https://stacks.math.columbia.edu/tag/012W)
* [Stacks Project, Tag 0131](https://stacks.math.columbia.edu/tag/0131)
* [Stacks Project, Tag 0132](https://stacks.math.columbia.edu/tag/0132)
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Filtration

variable {C : Type*} [Category* C] [Preadditive C] [HasCokernels C] {X : C}

/-- The projection `X ⟶ X/F^pX` is an isomorphism when the step `F^pX` is zero. -/
lemma isIso_quotientCone_π_app (F : Filtration X ℤᵒᵖ) {p : ℤ} (h : F.ι.app (op p) = 0) :
    IsIso (F.quotientCone.π.app (op p)) := by
  change IsIso (cokernel.π (F.ι.app (op p)))
  exact ⟨⟨cokernel.desc _ (𝟙 X) (by rw [h, zero_comp]), cokernel.π_desc _ _ _,
    coequalizer.hom_ext (by simp)⟩⟩

/-- **A filtration which is zero from some step on is complete.** If `F^pX = 0` for `p ≥ b`, then
`X = lim_p X/F^pX`: the projection to `X/F^bX` is an isomorphism, and every other projection
factors through the one to `X/F^{max(p, b)}X`, which is again an isomorphism. -/
theorem isComplete_of_eventually_eq_zero (F : Filtration X ℤᵒᵖ) (b : ℤ)
    (hb : ∀ p, b ≤ p → F.ι.app (op p) = 0) : F.IsComplete := by
  have hπ : ∀ p, b ≤ p → IsIso (F.quotientCone.π.app (op p)) :=
    fun p hp => F.isIso_quotientCone_π_app (hb p hp)
  have := hπ b le_rfl
  refine ⟨IsLimit.mk (fun s => s.π.app (op b) ≫ inv (F.quotientCone.π.app (op b)))
    (fun s j => ?_) (fun s m hm => ?_)⟩
  · induction j using Opposite.rec with | op i => ?_
    have := hπ (max i b) (le_max_right _ _)
    let f : op (max i b) ⟶ op i := (homOfLE (le_max_left i b)).op
    let g : op (max i b) ⟶ op b := (homOfLE (le_max_right i b)).op
    have h1 := s.w f
    have h2 := s.w g
    have h3 := F.quotientCone.w f
    have h4 := F.quotientCone.w g
    have h5 : F.quotientDiagram.map g =
        inv (F.quotientCone.π.app (op (max i b))) ≫ F.quotientCone.π.app (op b) := by
      rw [← h4, IsIso.inv_hom_id_assoc]
    rw [← h1, ← h2, ← h3, h5]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc, IsIso.inv_hom_id_assoc]
  · rw [← hm (op b), Category.assoc, IsIso.hom_inv_id, Category.comp_id]

end CategoryTheory.Filtration

namespace CochainComplex.Filtered

open FilteredComplexSpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C] (K : Filtered C)

/-- **The spectral sequence of a degreewise finite filtered complex converges to its cohomology**
([Stacks, Tag 012U], (3)), in the form `ConvergesToHomology` of the filtered complex. Regularity
holds because `F^{p + r}K^{n + 1} = 0` for `r ≫ 0`; weak convergence is the equality of (012S) and
(012T) of [Stacks, Tag 012W]; the induced filtration of each `H^n(K^•)` reaches `⊤` and `⊥`
([Stacks, Tag 012W]), so it is separated, exhaustive and, being zero from some step on, complete. -/
theorem convergesToHomology_of_isDegreewiseFinite (hK : K.filtration.IsDegreewiseFinite) :
    K.ConvergesToHomology := by
  obtain ⟨e, -⟩ := exists_pageIso_d K
  obtain ⟨-, hbounds, -, hweak, -⟩ := isBounded_and_converges_of_isDegreewiseFinite K hK
    (filtrationSubobject K) (fun _ _ => rfl) (cycles K.X (filtrationSubobject K))
    (fun _ _ _ => rfl) (boundaries K.X (filtrationSubobject K)) (fun _ _ _ => rfl)
    (fun n p => K.inducedFiltrationStep n p) (fun _ _ => rfl) _ e
  refine ⟨fun p n => ?_, ⟨hweak, fun n => ⟨?_, ?_⟩⟩, fun n => ?_⟩
  · obtain ⟨b, hb⟩ := exists_F_eq_bot K (filtrationSubobject K) (fun _ _ => rfl) hK (n + 1)
    refine ⟨(b - p).toNat, fun r hr => ?_⟩
    have h1 : K.step (p + r) (n + 1) = ⊥ := hb _ (by omega)
    have h2 : K.step (p + ((b - p).toNat : ℕ)) (n + 1) = ⊥ := hb _ (by omega)
    rw [h1, h2]
  · obtain ⟨a, b, -, -, hb⟩ := hbounds n
    rw [Filtration.IsSeparated, range_inducedFiltration_subobject]
    exact IsLeast.isGLB ⟨⟨b, hb⟩, fun _ _ => bot_le⟩
  · obtain ⟨a, b, -, ha, -⟩ := hbounds n
    rw [Filtration.IsExhaustive, range_inducedFiltration_subobject]
    exact IsGreatest.isLUB ⟨⟨a, ha⟩, fun _ _ => le_top⟩
  · obtain ⟨a, b, -, -, hb⟩ := hbounds n
    refine Filtration.isComplete_of_eventually_eq_zero _ b fun p hp => ?_
    have h : K.inducedFiltrationStep n p = ⊥ :=
      le_bot_iff.mp ((K.inducedFiltrationStep_antitone n hp).trans hb.le)
    rw [inducedFiltration, Filtration.ofAntitone_ι_app, ← Subobject.mk_eq_bot_iff_zero,
      Subobject.mk_arrow]
    exact h

/-- **The spectral sequence of a degreewise finite filtered complex converges to its cohomology**
in the sense of [Stacks, Tag 012U], (3). -/
theorem converges_of_isDegreewiseFinite (hK : K.filtration.IsDegreewiseFinite) : K.Converges :=
  (K.converges_iff_convergesToHomology).2 (K.convergesToHomology_of_isDegreewiseFinite hK)

end CochainComplex.Filtered

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
  [K.HasTotal (ComplexShape.up ℤ)]

/-- **The first spectral sequence of a double complex with finite antidiagonals converges.** If
every antidiagonal of `K^{•,•}` has only finitely many nonzero terms, then `('E_r, 'd_r)` converges
to `H^*(Tot(K^{•,•}))` in the sense of [Stacks, Tag 012U] ([Stacks, Tag 0132]). -/
theorem convergesToTotalHomology₁_of_finite
    (hK : ∀ n : ℤ, {pq : ℤ × ℤ | pq.1 + pq.2 = n ∧ ¬ IsZero ((K.X pq.1).X pq.2)}.Finite) :
    K.ConvergesToTotalHomology₁ :=
  CochainComplex.Filtered.converges_of_isDegreewiseFinite _
    (K.isDegreewiseFinite_totalFiltration₁ hK)

/-- **The second spectral sequence of a double complex with finite antidiagonals converges.** If
every antidiagonal of `K^{•,•}` has only finitely many nonzero terms, then `(''E_r, ''d_r)`
converges to `H^*(Tot(K^{•,•}))` in the sense of [Stacks, Tag 012U] ([Stacks, Tag 0132]). -/
theorem convergesToTotalHomology₂_of_finite
    (hK : ∀ n : ℤ, {pq : ℤ × ℤ | pq.1 + pq.2 = n ∧ ¬ IsZero ((K.X pq.1).X pq.2)}.Finite) :
    K.ConvergesToTotalHomology₂ :=
  CochainComplex.Filtered.converges_of_isDegreewiseFinite _
    (K.isDegreewiseFinite_totalFiltration₂ hK)

end HomologicalComplex₂

end
