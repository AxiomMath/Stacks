module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.AffineTarget
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.QuasiFiniteUniversallyBounded

/-!
# An open subscheme of a finite scheme over a field, and its rank

Over the spectrum of a field a finite morphism is finite locally free of some rank, and
restricting it to an open subscheme of its source can only lower the rank. This file proves both
statements, and their combination in which a bound on the rank is given negatively, as the failure
of every larger rank.

## Main results

* `AlgebraicGeometry.rank_eq_of_isFiniteLocallyFreeOfRank`: over the spectrum of a field the
  rank of a finite locally free morphism is unique.
* `AlgebraicGeometry.exists_isFiniteLocallyFreeOfRank_of_isFinite`: a finite morphism to the
  spectrum of a field is finite locally free of some rank.
* `AlgebraicGeometry.exists_isFiniteLocallyFreeOfRank_le_of_isFinite`: a finite morphism to the
  spectrum of a field which is finite locally free of no rank at least `n + 1` is finite locally
  free of some rank at most `n`.
* `AlgebraicGeometry.not_isFiniteLocallyFreeOfRank_of_rank_le`: a morphism to the spectrum of a
  field which is finite locally free of a rank at most `n` is finite locally free of no rank at
  least `n + 1`.
* `AlgebraicGeometry.exists_isFiniteLocallyFreeOfRank_le_of_isOpenImmersion`: an open subscheme
  of a scheme finite locally free of rank `r` over the spectrum of a field is finite locally
  free of some rank at most `r`.
* `AlgebraicGeometry.exists_isFiniteLocallyFreeOfRank_le_of_isOpenImmersion_of_isFinite`: an open
  subscheme of a scheme finite over the spectrum of a field and finite locally free of no rank at
  least `n + 1` is finite locally free of some rank at most `n`.

## References

* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 03J4](https://stacks.math.columbia.edu/tag/03J4)
* [Stacks Project, Tag 03JL](https://stacks.math.columbia.edu/tag/03JL)
* [Stacks Project, Tag 086T](https://stacks.math.columbia.edu/tag/086T)
* [Stacks Project, Tag 086U](https://stacks.math.columbia.edu/tag/086U)
-/


@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Over the spectrum of a field the rank of a finite locally free morphism is unique: if `p` is
finite locally free of ranks `r` and `r'`, then `r = r'`. -/
theorem rank_eq_of_isFiniteLocallyFreeOfRank {k : Type u} [Field k] {Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of k)) {r r' : ℕ}
    (h : Stacks.Morphisms.IsFiniteLocallyFreeOfRank p r)
    (h' : Stacks.Morphisms.IsFiniteLocallyFreeOfRank p r') : r = r' := by
  have _hpa : IsAffineHom p := h.toIsAffineHom
  let _ : Algebra k ↑Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom.toAlgebra
  rw [← (finite_and_finrank_sections_of_isFiniteLocallyFreeOfRank p r (h := h)).2,
    ← (finite_and_finrank_sections_of_isFiniteLocallyFreeOfRank p r' (h := h')).2]

/-- A morphism from an affine scheme to the spectrum of a field with finite-dimensional global
sections is finite locally free of rank the dimension of those sections. -/
private theorem isFiniteLocallyFreeOfRank_finrank_of_finite {k : Type u} [Field k]
    {Z : Scheme.{u}} [IsAffine Z] (p : Z ⟶ Spec (.of k))
    (h : letI : Algebra k ↑Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom.toAlgebra
      Module.Finite k ↑Γ(Z, ⊤)) :
    letI : Algebra k ↑Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom.toAlgebra
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank p (Module.finrank k ↑Γ(Z, ⊤)) := by
  let : Algebra k ↑Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom.toAlgebra
  have : Module.Finite k ↑Γ(Z, ⊤) := h
  exact Stacks.Morphisms.isFiniteLocallyFreeOfRank_of_basis p _ ⟨Module.finBasis k ↑Γ(Z, ⊤)⟩

/-- A finite morphism to the spectrum of a field is finite locally free of some rank. -/
theorem exists_isFiniteLocallyFreeOfRank_of_isFinite {k : Type u} [Field k] {Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of k)) [IsFinite p] :
    ∃ r : ℕ, Stacks.Morphisms.IsFiniteLocallyFreeOfRank p r := by
  have _hZ : IsAffine Z := isAffine_of_isAffineHom p
  let _ : Algebra k ↑Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom.toAlgebra
  have hfin : ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom.Finite := by
    rw [CommRingCat.hom_comp]
    exact (IsFinite.finite_app p ⊤ (isAffineOpen_top _)).comp
      (RingHom.Finite.of_surjective _
        ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2))
  exact ⟨_, isFiniteLocallyFreeOfRank_finrank_of_finite p hfin⟩

/-- A finite morphism to the spectrum of a field which is finite locally free of no rank at least
`n + 1` is finite locally free of some rank at most `n`. -/
theorem exists_isFiniteLocallyFreeOfRank_le_of_isFinite {k : Type u} [Field k] {Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of k)) [IsFinite p] (n : ℕ)
    (hn : ∀ r : ℕ, n + 1 ≤ r → ¬ Stacks.Morphisms.IsFiniteLocallyFreeOfRank p r) :
    ∃ r : ℕ, r ≤ n ∧ Stacks.Morphisms.IsFiniteLocallyFreeOfRank p r := by
  obtain ⟨r, hr⟩ := exists_isFiniteLocallyFreeOfRank_of_isFinite p
  exact ⟨r, Nat.le_of_not_lt fun h => hn r h hr, hr⟩

/-- A morphism to the spectrum of a field which is finite locally free of a rank `r ≤ n` is
finite locally free of no rank at least `n + 1`. -/
theorem not_isFiniteLocallyFreeOfRank_of_rank_le {k : Type u} [Field k] {Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of k)) {r n : ℕ}
    (h : Stacks.Morphisms.IsFiniteLocallyFreeOfRank p r) (hrn : r ≤ n) :
    ∀ r' : ℕ, n + 1 ≤ r' → ¬ Stacks.Morphisms.IsFiniteLocallyFreeOfRank p r' :=
  fun _ hr' h' => absurd (rank_eq_of_isFiniteLocallyFreeOfRank p h h') (by omega)

/-- If `p : Z ⟶ Spec k` is finite locally free of rank `r` over a field `k` and `ι : Z' ⟶ Z` is an
open immersion, then `ι ≫ p` is finite locally free of some rank at most `r`. -/
theorem exists_isFiniteLocallyFreeOfRank_le_of_isOpenImmersion {k : Type u} [Field k]
    {Z Z' : Scheme.{u}} (p : Z ⟶ Spec (.of k)) (ι : Z' ⟶ Z) [IsOpenImmersion ι] (r : ℕ)
    [h : Stacks.Morphisms.IsFiniteLocallyFreeOfRank p r] :
    ∃ r' : ℕ, r' ≤ r ∧ Stacks.Morphisms.IsFiniteLocallyFreeOfRank (ι ≫ p) r' := by
  have _hpa : IsAffineHom p := h.toIsAffineHom
  have _hZ : IsAffine Z := isAffine_of_isAffineHom p
  let _ : Algebra k ↑Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom.toAlgebra
  obtain ⟨hfin, hrank⟩ := finite_and_finrank_sections_of_isFiniteLocallyFreeOfRank p r
  obtain ⟨hZ', hfin', hle⟩ :=
    isAffine_and_finrank_le_of_isOpenImmersion p ι r ⟨hfin, hrank.le⟩
  have : IsAffine Z' := hZ'
  exact ⟨_, hle, isFiniteLocallyFreeOfRank_finrank_of_finite (ι ≫ p) hfin'⟩

/-- If `p : Z ⟶ Spec k` is finite over a field `k` and finite locally free of no rank at least
`n + 1`, and `ι : Z' ⟶ Z` is an open immersion, then `ι ≫ p` is finite locally free of some rank
at most `n`. -/
theorem exists_isFiniteLocallyFreeOfRank_le_of_isOpenImmersion_of_isFinite {k : Type u}
    [Field k] {Z Z' : Scheme.{u}} (p : Z ⟶ Spec (.of k)) (ι : Z' ⟶ Z) [IsOpenImmersion ι]
    [IsFinite p] (n : ℕ)
    (hn : ∀ r : ℕ, n + 1 ≤ r → ¬ Stacks.Morphisms.IsFiniteLocallyFreeOfRank p r) :
    ∃ r : ℕ, r ≤ n ∧ Stacks.Morphisms.IsFiniteLocallyFreeOfRank (ι ≫ p) r := by
  obtain ⟨r, hrn, hr⟩ := exists_isFiniteLocallyFreeOfRank_le_of_isFinite p n hn
  obtain ⟨r', hr'r, hr'⟩ :=
    exists_isFiniteLocallyFreeOfRank_le_of_isOpenImmersion p ι r (h := hr)
  exact ⟨r', hr'r.trans hrn, hr'⟩

end AlgebraicGeometry

end
