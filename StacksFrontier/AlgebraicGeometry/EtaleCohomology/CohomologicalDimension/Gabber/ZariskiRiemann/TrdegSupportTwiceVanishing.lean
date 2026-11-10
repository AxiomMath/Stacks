module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.FiniteTypeTwiceDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.SeparablyClosed
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.SupportedSheaves

/-!
# Gabber's `δ`-bound at finite level: cohomology of sheaves supported in transcendence degree `δ`

Let `K` be a field, `X` a quasi-compact scheme locally of finite type over `K` and `A` a torsion
abelian sheaf on `X_étale` whose stalks vanish at every geometric point over a point `x` with
`trdeg_K κ(x) > δ`. Then `H^b(X, A) = 0` for `b > 2δ + cd(K)`; over a separably closed field,
for `b > 2δ`.

This is the finite-type case of the claim in Gabber's Zariski–Riemann proof of the bound
`cd(Frac B) ≤ 2 dim B - 1` (Travaux de Gabber, Exposé XVIII-A, last remark of §2): "if `A` is an
`ℓ`-torsion sheaf on the étale topos of `ZRS₀`, let `δ(A)` be the sup of transcendence degrees of
points where the stalk is non-zero. I claim that `H^n(ZRS₀, A)` vanishes for `n > 2δ(A)`. One
reduces it to the finite type case (passage to the limit SGA 4 VI 8.7.4)". The finite type case
is proved here.

The proof is that of the tree's `cd(X) ≤ 2 dim X + cd(K)`: by Stacks 0F0N the sheaf `A` is a
filtered colimit of subsheaves supported on closed subsets of `E_δ`, each the direct image from a
closed subscheme of dimension at most `δ` (Stacks 0A21, 04CA), where the bound `2δ + cd(K)` is
`AlgebraicGeometry.subsingleton_H_of_topologicalKrullDim_le`; this reduction is
`AlgebraicGeometry.subsingleton_H_of_smallEtaleSupport_subset_of_finiteTypeBound`. In the form
with `δ` read off pointwise (`2 trdeg_K κ(x) < b` at every point of the support) the case
`b = 0` is the case of empty support, in which `A = 0`.

## Main results

* `AlgebraicGeometry.subsingleton_H_of_smallEtaleSupport_subset_trdegLESet_twice` —
  `H^b(X, A) = 0` for `b > 2δ + cd(K)`.
* `AlgebraicGeometry.subsingleton_H_of_smallEtaleSupport_subset_trdegLESet_twice_of_isSepClosed` —
  `H^b(X, A) = 0` for `b > 2δ`, `K` separably closed.
* `Stacks.EtaleCohomology.subsingleton_H_of_smallEtaleSupport_eq_empty` — a sheaf with empty
  support has no cohomology.
* `AlgebraicGeometry.subsingleton_H_of_forall_mem_smallEtaleSupport_two_mul_lt` — Gabber's
  `δ`-claim at finite level: over a separably closed field, `H^b(X, A) = 0` as soon as every point
  of the support of `A` has `2 trdeg_K κ(x) < b`.

## References

* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
* [Stacks Project, Tag 0F0W](https://stacks.math.columbia.edu/tag/0F0W)
* [Stacks Project, Tag 0F0N](https://stacks.math.columbia.edu/tag/0F0N)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

/-- **A sheaf with empty support has no cohomology**: its stalks all vanish, so it is zero
(`Stacks.EtaleCohomology.isZero_of_forall_isZero_smallEtaleStalkAb`), and `Ext` into a zero
object vanishes. -/
theorem subsingleton_H_of_smallEtaleSupport_eq_empty {X : AlgebraicGeometry.Scheme.{u}}
    (A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hA : smallEtaleSupport A = ∅)
    (b : ℕ) : Subsingleton (Sheaf.H.{u + 1, u + 1} A b) := by
  have hz : IsZero A := isZero_of_forall_isZero_smallEtaleStalkAb A fun s ↦ by
    by_contra h
    have hs : s.hom (IsLocalRing.closedPoint s.residueField) ∈ smallEtaleSupport A := by
      have hpt : s.hom default = s.hom (IsLocalRing.closedPoint s.residueField) :=
        congrArg s.hom (Subsingleton.elim _ _)
      exact hpt ▸ ⟨s, rfl, h⟩
    rw [hA] at hs
    exact hs
  have h0 : ∀ e : Sheaf.H.{u + 1, u + 1} A b, e = 0 := fun e ↦ by
    rw [← Abelian.Ext.comp_mk₀_id e, hz.eq_of_src (𝟙 A) 0, Abelian.Ext.mk₀_zero,
      Abelian.Ext.comp_zero]
  exact ⟨fun e₁ e₂ ↦ by rw [h0 e₁, h0 e₂]⟩

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

/-- The sets `E_a` increase with `a`. -/
theorem Scheme.trdegLESet_mono (K : Type u) [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    {a a' : ℕ} (h : a ≤ a') : Scheme.trdegLESet K f a ⊆ Scheme.trdegLESet K f a' := by
  intro x hx
  simp only [Scheme.trdegLESet, Set.mem_ofPred_eq] at hx ⊢
  exact hx.trans (by exact_mod_cast h)

/-- **Cohomology of a sheaf supported in transcendence degree `δ`, on a scheme of finite type
over a field, vanishes above `2δ + cd(K)`.** Let `X` be quasi-compact and locally of finite type
over a field `K`, and `A` a torsion abelian sheaf on `X_étale` whose support lies in the set
`E_δ` of points `x` with `trdeg_K κ(x) ≤ δ`. Then `H^b(X, A) = 0` for `b > 2δ + cd(K)`. -/
theorem subsingleton_H_of_smallEtaleSupport_subset_trdegLESet_twice (K : Type u) [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [CompactSpace X] [LocallyOfFiniteType f] (δ : ℕ)
    (A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hA : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology A)
    (hsupp : smallEtaleSupport A ⊆ Scheme.trdegLESet K f δ) (b : ℕ)
    (hb : ((2 * δ : ℕ) : ℕ∞) + Scheme.etaleCohomologicalDimension (Spec (.of K)) < b) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} A b) :=
  subsingleton_H_of_smallEtaleSupport_subset_of_finiteTypeBound K f δ _
    (fun Z g _ _ hZ G hG b' hb' ↦ subsingleton_H_of_topologicalKrullDim_le K δ Z g hZ G hG b' hb')
    A hA hsupp b hb

/-- **Over a separably closed field, cohomology of a sheaf supported in transcendence degree `δ`
vanishes above `2δ`.** This is the previous statement with `cd(K) = 0`
(`AlgebraicGeometry.Scheme.etaleCohomologicalDimension_spec_le_zero_of_isSepClosed`). -/
theorem subsingleton_H_of_smallEtaleSupport_subset_trdegLESet_twice_of_isSepClosed (K : Type u)
    [Field K] [IsSepClosed K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [CompactSpace X]
    [LocallyOfFiniteType f] (δ : ℕ) (A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hA : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology A)
    (hsupp : smallEtaleSupport A ⊆ Scheme.trdegLESet K f δ) (b : ℕ) (hb : 2 * δ < b) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} A b) := by
  refine subsingleton_H_of_smallEtaleSupport_subset_trdegLESet_twice K f δ A hA hsupp b ?_
  have h0 := Scheme.etaleCohomologicalDimension_spec_le_zero_of_isSepClosed K
  rw [nonpos_iff_eq_zero.1 h0, add_zero]
  exact_mod_cast hb

/-- **Gabber's `δ`-claim at finite level.** Let `X` be quasi-compact and locally of finite type
over a separably closed field `K`, and `A` a torsion abelian sheaf on `X_étale`. If every point
`x` of the support of `A` has `2 trdeg_K κ(x) < b` (that is, lies in some `E_a` with `2a < b`),
then `H^b(X, A) = 0`. For `b = 0` the hypothesis says the support is empty. -/
theorem subsingleton_H_of_forall_mem_smallEtaleSupport_two_mul_lt (K : Type u) [Field K]
    [IsSepClosed K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [CompactSpace X]
    [LocallyOfFiniteType f] (A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hA : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology A) (b : ℕ)
    (hsupp : ∀ x ∈ smallEtaleSupport A, ∃ a : ℕ, 2 * a < b ∧ x ∈ Scheme.trdegLESet K f a) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} A b) := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · refine subsingleton_H_of_smallEtaleSupport_eq_empty A ?_ 0
    refine Set.eq_empty_of_forall_notMem fun x hx ↦ ?_
    obtain ⟨a, ha, -⟩ := hsupp x hx
    omega
  · refine subsingleton_H_of_smallEtaleSupport_subset_trdegLESet_twice_of_isSepClosed K f
      ((b - 1) / 2) A hA (fun x hx ↦ ?_) b (by omega)
    obtain ⟨a, ha, hxa⟩ := hsupp x hx
    exact Scheme.trdegLESet_mono K f (by omega) hxa

end AlgebraicGeometry

end
