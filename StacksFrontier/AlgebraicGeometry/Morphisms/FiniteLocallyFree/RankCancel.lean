module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.AlgClosedField
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.RankComp
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.Descent

/-!
# Cancelling a finite locally free factor of a composition

`Stacks.Morphisms.IsFiniteLocallyFreeOfRank.comp` says that degrees multiply in a composition of
finite locally free morphisms. This file proves the converse needed when the degree of a
composite and of its first factor are known: if `f : X ⟶ Y` is finite locally free of degree
`r ≠ 0`, the composite `f ≫ g` is finite locally free of degree `r * s`, and `g` is separated and
locally of finite type, then `g` is finite locally free of degree `s`. This is the
"multiplicativity of degrees of finite locally free morphisms" step of the proof of Stacks
Tag 0B9I (3).

## Main results

* `Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_comp`: the cancellation.

## Implementation notes

A finite locally free morphism of positive degree is surjective and flat, so `g` is flat by
descent of flatness (Tag 02JZ) and universally closed because `f ≫ g` is; the fibres of `g` are
images of the finite fibres of `f ≫ g`, so `g` is locally quasi-finite, and being proper it is
finite (Tag 02LS). The degree of `g` at a point `z` is computed on the fibre over `Spec κ(z)`,
where the base changes of `f`, `g` and `f ≫ g` have degrees `r`, `deg_z g` and `r * s`, and
`r * deg_z g = r * s` by the multiplicativity over a field.

## References

* [Stacks Project, Tag 0B9I](https://stacks.math.columbia.edu/tag/0B9I)
* [Stacks Project, Tag 02JZ](https://stacks.math.columbia.edu/tag/02JZ)
* [Stacks Project, Tag 02LS](https://stacks.math.columbia.edu/tag/02LS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Morphisms

/-- **Cancelling a finite locally free factor.** Let `f : X ⟶ Y` be finite locally free of
degree `r ≠ 0` and let `g : Y ⟶ Z` be separated and locally of finite type. If `f ≫ g` is
finite locally free of degree `r * s`, then `g` is finite locally free of degree `s`. -/
theorem IsFiniteLocallyFreeOfRank.of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {r s : ℕ} (hr : r ≠ 0) [IsFiniteLocallyFreeOfRank f r]
    [IsFiniteLocallyFreeOfRank (f ≫ g) (r * s)] [IsSeparated g] [LocallyOfFiniteType g] :
    IsFiniteLocallyFreeOfRank g s := by
  obtain ⟨hffin, hfflat, -⟩ :=
    (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation f).mp
      (IsFiniteLocallyFreeOfRank.isFiniteLocallyFree f r)
  obtain ⟨hcfin, hcflat, -⟩ :=
    (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation (f ≫ g)).mp
      (IsFiniteLocallyFreeOfRank.isFiniteLocallyFree (f ≫ g) (r * s))
  have : Surjective f := surjective_of_isFiniteLocallyFreeOfRank f r hr
  have : Flat g := flat_of_comp_of_surjective_flat f g
  have : UniversallyClosed g := UniversallyClosed.of_comp_surjective f g
  have : IsProper g := { }
  have : LocallyQuasiFinite g := by
    refine LocallyQuasiFinite.of_finite_preimage_singleton g fun z ↦ ?_
    refine (((f ≫ g).finite_preimage_singleton z).image f).subset ?_
    intro y hy
    obtain ⟨x, rfl⟩ := f.surjective y
    exact ⟨x, by simpa [Scheme.Hom.comp_apply] using hy, rfl⟩
  have : IsFinite g := IsFinite.of_isProper_of_locallyQuasiFinite g
  rw [isFiniteLocallyFreeOfRank_iff_forall_finrank_eq g s]
  intro z
  -- a point of the fibre, whose image is `z`
  obtain ⟨t₀, -⟩ : ∃ t, (Z.fromSpecResidueField z) t = z := by
    have hmem : z ∈ Set.range (Z.fromSpecResidueField z).base := by
      rw [Scheme.range_fromSpecResidueField]
      exact rfl
    exact hmem
  -- the two pullback squares over `Spec κ(z)`
  have t : IsPullback (pullback.fst g (Z.fromSpecResidueField z))
      (pullback.snd g (Z.fromSpecResidueField z)) g (Z.fromSpecResidueField z) :=
    IsPullback.of_hasPullback g (Z.fromSpecResidueField z)
  have sq : IsPullback (pullback.fst f (pullback.fst g (Z.fromSpecResidueField z)))
      (pullback.snd f (pullback.fst g (Z.fromSpecResidueField z))) f
      (pullback.fst g (Z.fromSpecResidueField z)) :=
    IsPullback.of_hasPullback f (pullback.fst g (Z.fromSpecResidueField z))
  -- the fibre of `g` has degree `deg_z g`
  have hg' : IsFiniteLocallyFreeOfRank (pullback.snd g (Z.fromSpecResidueField z))
      (g.finrank z) := by
    rw [isFiniteLocallyFreeOfRank_iff_forall_finrank_eq]
    intro p
    rw [Scheme.Hom.finrank_of_isPullback _ _ g _ t p, Z.fromSpecResidueField_apply z p]
  have hf' : IsFiniteLocallyFreeOfRank
      (pullback.snd f (pullback.fst g (Z.fromSpecResidueField z))) r :=
    IsFiniteLocallyFreeOfRank.of_isPullback sq
  -- the fibre of the composite, computed in two ways
  have h₁ : IsFiniteLocallyFreeOfRank
      (pullback.snd f (pullback.fst g (Z.fromSpecResidueField z)) ≫
        pullback.snd g (Z.fromSpecResidueField z)) (r * g.finrank z) :=
    isFiniteLocallyFreeOfRank_comp_of_specTarget (K := (Z.residueField z : Type u)) _ _ r _
  have h₂ : IsFiniteLocallyFreeOfRank
      (pullback.snd f (pullback.fst g (Z.fromSpecResidueField z)) ≫
        pullback.snd g (Z.fromSpecResidueField z)) (r * s) :=
    IsFiniteLocallyFreeOfRank.of_isPullback (sq.paste_vert t)
  obtain ⟨hfin₁, hflat₁, -⟩ :=
    (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mp
      (IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ (r * s) (h := h₂))
  have e₁ := (isFiniteLocallyFreeOfRank_iff_forall_finrank_eq _ _).mp h₁ t₀
  have e₂ := (isFiniteLocallyFreeOfRank_iff_forall_finrank_eq _ _).mp h₂ t₀
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hr) (e₁.symm.trans e₂)

end Stacks.Morphisms

end
