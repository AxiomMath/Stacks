module

public import StacksFrontier.AlgebraicGeometry.AlgClosed.SectionsCardinal
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.TorsionPoints
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.ZPowRank

/-!
# Points of infinite order on an abelian variety over an uncountable algebraically closed field

Let `k` be an algebraically closed field and `A` an abelian variety over `k` of positive
dimension. This file proves:

* for every `n ≠ 0` the group `A(k)[n]` is finite, since multiplication by `n` is finite
  (Tag 0BFG, `Stacks.Groupoids.isFiniteLocallyFreeOfRank_zpow_id_left_of_ne_zero`); hence the
  torsion of `A(k)` is countable;
* `A(k)` has at least `#k` elements (`AlgebraicGeometry.cardinalMk_le_sections`);
* so if `k` is uncountable, `A(k)` has a point of infinite order.

## Relation to Stacks Tag 0AFB

The proof of part (a) of Lemma 0AFB (Section 0AF8, "An example of a non-algebraic Hom-stack")
uses a non-torsion point `a₀ ∈ A₀(k)` for a non-zero abelian variety `A₀` over an algebraically
closed field `k` which is not the algebraic closure of a finite field, and says this is "actually
not trivial to prove"; Stacks gives no argument (see `errata.md`, entry of 2026-10-28). This file
proves the statement for uncountable `k`. For countable `k` (for example `ℚ̄`, or the algebraic
closure of `𝔽_p(t)`) the statement is proved by specialization to finite fields, in
`StacksFrontier/AlgebraicGeometry/GroupScheme/OverField/AbelianVarietyNonTorsionPointCharZero.lean`
and `StacksFrontier/AlgebraicGeometry/GroupScheme/OverField/AbelianVarietyNonTorsionPointGeneral.lean`
(`Stacks.Groupoids.exists_not_isOfFinAddOrder`).

## Main results

* `Stacks.Groupoids.cardinalMk_le_points`: `#k ≤ #A(k)`.
* `Stacks.Groupoids.finite_torsionBy_of_ne_zero`: `A(k)[n]` is finite for `n ≠ 0`.
* `Stacks.Groupoids.countable_setOf_isOfFinAddOrder`: the torsion of `A(k)` is countable.
* `Stacks.Groupoids.exists_not_isOfFinAddOrder_of_uncountable`: a point of infinite order when
  `k` is uncountable.

## References

* [Stacks Project, Tag 0AFB](https://stacks.math.columbia.edu/tag/0AFB)
* [Stacks Project, Tag 0BFG](https://stacks.math.columbia.edu/tag/0BFG)
* G. Frey and M. Jarden, *Approximation theory and the rank of abelian varieties over large
  algebraic fields*, Proc. London Math. Soc. (3) 28 (1974), 112–128.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Groupoids

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- **An abelian variety of positive dimension over an algebraically closed field `k` has at least
`#k` rational points**: rational points are sections of the structure morphism, which is of finite
type. -/
theorem cardinalMk_le_points [IsAlgClosed k] [AlgebraicGeometry.IsAbelianVariety k A]
    (hA : 0 < topologicalKrullDim A.left) :
    Cardinal.mk k ≤ Cardinal.mk (𝟙_ (Over (Spec (.of k))) ⟶ A) := by
  refine (AlgebraicGeometry.cardinalMk_le_sections A.hom hA).trans
    (Cardinal.mk_le_of_injective (f := fun s => Over.homMk s.1 (by simpa using s.2)) ?_)
  intro s t h
  exact Subtype.ext (congrArg CommaMorphism.left h)

/-- **For every `n ≠ 0` the group `A(k)[n]` is finite**, `k` algebraically closed: multiplication
by `n` is finite locally free of rank `n ^ {2 dim A}` (Tag 0BFG), in particular finite, a rational
point is determined by its image point, which is closed, and the image of an `n`-torsion point lies
in the finite fibre of `[n]` over the identity. -/
theorem finite_torsionBy_of_ne_zero [IsAlgClosed k] [AlgebraicGeometry.IsAbelianVariety k A]
    (n : ℕ) (hn : n ≠ 0) :
    Finite (Submodule.torsionBy ℤ (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) (n : ℤ)) := by
  have := (isFinite_zpow_id_left_iff_isAffineHom A (n : ℤ)).2
    (isFiniteLocallyFreeOfRank_zpow_id_left_of_ne_zero A (n : ℤ)
      (by exact_mod_cast hn)).toIsAffineHom
  set pk : Spec (.of k) := IsLocalRing.closedPoint k
  set e := ((η[A]).left : Spec (.of k) ⟶ A.left) pk
  have := (Scheme.Hom.finite_preimage_singleton ((𝟙 A : A ⟶ A) ^ (n : ℤ)).left e).to_subtype
  change Finite (AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) (n : ℤ))
  rw [(torsionKernelEquiv k A n).finite_iff]
  refine Finite.of_injective (β := ((𝟙 A : A ⟶ A) ^ (n : ℤ)).left ⁻¹' {e})
    (fun p => ⟨(p.1.left : Spec (.of k) ⟶ A.left) pk, ?_⟩) ?_
  · exact congrArg (fun f : 𝟙_ (Over (Spec (.of k))) ⟶ A => (f.left : Spec (.of k) ⟶ A.left) pk)
      p.2
  · intro p q hpq
    apply Subtype.ext
    have hci : IsClosedImmersion p.1.left :=
      AlgebraicGeometry.isClosedImmersion_of_comp_eq_id A.hom p.1.left (by simp)
    have hc : IsClosed {(p.1.left : Spec (.of k) ⟶ A.left) pk} := by
      have hpk : IsClosed ({pk} : Set (Spec (.of k))) := isClosed_discrete _
      have h := p.1.left.isClosedMap _ hpk
      rwa [Set.image_singleton] at h
    exact Over.OverMorphism.ext (AlgebraicGeometry.ext_of_apply_closedPoint_eq_of_comp_eq A.hom hc
      rfl (congrArg Subtype.val hpq).symm ((Over.w p.1).trans (Over.w q.1).symm))

/-- **The torsion points of `A(k)` form a countable set**, `k` algebraically closed: they are the
union over `n ≥ 1` of the finite groups `A(k)[n]`. -/
theorem countable_setOf_isOfFinAddOrder [IsAlgClosed k] [AlgebraicGeometry.IsAbelianVariety k A] :
    {a : Additive (𝟙_ (Over (Spec (.of k))) ⟶ A) | IsOfFinAddOrder a}.Countable := by
  have hsub : {a : Additive (𝟙_ (Over (Spec (.of k))) ⟶ A) | IsOfFinAddOrder a} ⊆
      ⋃ n : ℕ, ((Submodule.torsionBy ℤ (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A))
        (((n + 1 : ℕ) : ℤ)) : Set _)) := by
    intro a ha
    obtain ⟨m, hm, hma⟩ := (isOfFinAddOrder_iff_nsmul_eq_zero (x := a)).mp ha
    refine Set.mem_iUnion.2 ⟨m - 1, ?_⟩
    rw [SetLike.mem_coe, Submodule.mem_torsionBy_iff, Nat.sub_add_cancel hm, natCast_zsmul]
    exact hma
  refine Set.Countable.mono hsub (Set.countable_iUnion fun n => ?_)
  have := finite_torsionBy_of_ne_zero A (n + 1) n.succ_ne_zero
  exact (Set.toFinite _).countable

/-- **An abelian variety `A ≠ 0` over an uncountable algebraically closed field `k` has a rational
point of infinite order.** The torsion of `A(k)` is countable, while `A(k)` has at least `#k`
elements.

This is the case of uncountable `k` of the fact the proof of Stacks Tag 0AFB, part (a), uses
without proof ("there is such a nontorsion point as `k` is algebraically closed and not the
algebraic closure of a finite field -- this is actually not trivial to prove"). -/
theorem exists_not_isOfFinAddOrder_of_uncountable [IsAlgClosed k] [Uncountable k]
    [AlgebraicGeometry.IsAbelianVariety k A] (hA : 0 < topologicalKrullDim A.left) :
    ∃ a : Additive (𝟙_ (Over (Spec (.of k))) ⟶ A), ¬ IsOfFinAddOrder a := by
  by_contra h
  simp only [not_exists, not_not] at h
  have hc : (Set.univ : Set (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A))).Countable :=
    (countable_setOf_isOfFinAddOrder A).mono fun a _ => h a
  have : Countable (𝟙_ (Over (Spec (.of k))) ⟶ A) :=
    (Set.countable_univ_iff.mp hc : Countable (Additive _))
  have h1 := cardinalMk_le_points A hA
  have h2 : Cardinal.mk (𝟙_ (Over (Spec (.of k))) ⟶ A) ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
  exact absurd (h1.trans h2) (not_le.mpr (Cardinal.aleph0_lt_mk_iff.mpr ‹_›))

end Stacks.Groupoids

end
