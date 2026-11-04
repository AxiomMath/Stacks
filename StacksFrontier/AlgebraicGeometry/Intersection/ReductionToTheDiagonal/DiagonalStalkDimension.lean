module

public import StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.DiagonalRegularImmersion

/-!
# The dimension of the local ring of `X ×ₖ X` at a point of the diagonal

Let `X` be a variety over a field `k` and `ξ` a point of `X`. The local ring of the product at
the image of `ξ` under the diagonal has dimension

`dim 𝒪_{X ×ₖ X, Δ(ξ)} = dim X + dim 𝒪_{X, ξ}`.

This is the numerical half of the reduction to the diagonal: the codimension of the diagonal at
`Δ(ξ)` is `dim X`, so the regular sequence cutting out the diagonal there — which exists by
Stacks tag 0B0Q, see
`Stacks.Intersection.Diagonal.exists_isRegular_generating_ker_stalkMap_diagonal` — has length
`dim X`, and the deficit of a properly intersecting pair transfers from `X` to `X ×ₖ X`.

The proof is the one `Stacks.Intersection.codimension_diagonal_eq_topologicalKrullDim` gives at
the generic point, run at an arbitrary point: the local dimension of the product at `Δ(ξ)` is
twice the local dimension of `X` at `ξ` by Stacks tag 0B2M, the local dimension at a point of a
scheme of finite type over a field is the transcendence degree of the residue field plus the
dimension of the local ring by Stacks tag 0A21, the diagonal is a closed immersion so it does
not change that transcendence degree, and the local dimension of an irreducible scheme of finite
type over a field is its dimension at every point. Cancelling the transcendence-degree term —
legitimate because it is finite — leaves the displayed formula. No nonsingularity is used.

## Main results

* `Stacks.Intersection.Diagonal.ringKrullDim_stalk_pullback_diagonal` — the displayed formula.
* `Stacks.Intersection.Diagonal.exists_ringKrullDim_stalk_pullback_diagonal_eq_add` — the same
  with the dimension of `X` exhibited as a natural number `n`, which is the form in which the
  length of the regular sequence cutting out the diagonal is to be compared with it.

## Implementation notes

Both dimensions are read as coheights through
`Stacks.AlgebraicGeometry.ringKrullDim_stalk_eq_coheight`, so that the whole computation takes
place among coercions of `ℕ∞` into `WithBot ℕ∞` and the transcendence-degree term can be
cancelled with `WithTop.add_left_cancel`. Its finiteness is
`Stacks.Intersection.trdeg_residueField_lt_aleph0_of_locallyOfFiniteType` and the invariance of
the residue field under the diagonal is
`Stacks.Intersection.trdeg_residueField_eq_of_isClosedImmersion_of_eq`.

## References

* [Stacks Project, Lemma 43.13.3 (Tag 0B0Q)](https://stacks.math.columbia.edu/tag/0B0Q)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
* [Stacks Project, Tag 0B2M](https://stacks.math.columbia.edu/tag/0B2M)
* [Stacks Project, Tag 0B0U](https://stacks.math.columbia.edu/tag/0B0U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.Intersection.Diagonal

/-- **The dimension of the local ring of `X ×ₖ X` at a point of the diagonal.** For a variety `X`
over a field `k` and a point `ξ` of `X`,

`dim 𝒪_{X ×ₖ X, Δ(ξ)} = dim X + dim 𝒪_{X, ξ}`.

Equivalently the diagonal has codimension `dim X` at `Δ(ξ)`. Nonsingularity is not needed. -/
theorem ringKrullDim_stalk_pullback_diagonal {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsVariety k f] (ξ : X) :
    ringKrullDim ((pullback f f).presheaf.stalk (pullback.diagonal f ξ)) =
      topologicalKrullDim X + ringKrullDim (X.presheaf.stalk ξ) := by
  set Z := (pullback f f : Scheme.{u}) with hZ
  set p : Z ⟶ Spec (.of k) := pullback.fst f f ≫ f with hp
  set z : Z := pullback.diagonal f ξ with hz
  have : IsClosedImmersion (pullback.diagonal f) := inferInstance
  set g : X ⟶ Spec (.of k) := pullback.diagonal f ≫ p with hg
  have : LocallyOfFiniteType g := by
    rw [hg, hp, ← Category.assoc, pullback.diagonal_fst, Category.id_comp]; infer_instance
  let : Algebra k (X.residueField ξ) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫ X.Γevaluation ξ).hom.toAlgebra
  let : Algebra k (Z.residueField z) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ Z.Γevaluation z).hom.toAlgebra
  have hstalkZ := ringKrullDim_stalk_eq_coheight z
  have hstalkX := ringKrullDim_stalk_eq_coheight ξ
  have hzπ : ∀ π : (pullback f f : Scheme.{u}) ⟶ X, pullback.diagonal f ≫ π = 𝟙 X → π z = ξ :=
    fun π h => congrArg (fun g => g ξ) h
  have hAt : topologicalKrullDimAt Z z =
      topologicalKrullDimAt X ξ + topologicalKrullDimAt X ξ := by
    rw [topologicalKrullDimAt_pullback k f f z, hzπ _ (pullback.diagonal_fst f),
      hzπ _ (pullback.diagonal_snd f)]
  have hformZ := topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k Z p z
  have hformX := topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k X g ξ
  have htr : Algebra.trdeg k (Z.residueField z) = Algebra.trdeg k (X.residueField ξ) :=
    trdeg_residueField_eq_of_isClosedImmersion_of_eq p (pullback.diagonal f) ξ rfl
  set t : ℕ∞ := Cardinal.toENat (Algebra.trdeg k (X.residueField ξ)) with ht
  have htne : t ≠ ⊤ :=
    ne_of_lt ((Cardinal.toENat_lt_top).2
      (Stacks.Intersection.trdeg_residueField_lt_aleph0_of_locallyOfFiniteType g ξ))
  have hZ' : (t : WithBot ℕ∞) + (Order.coheight z : WithBot ℕ∞) =
      topologicalKrullDimAt Z z := by
    rw [hformZ, htr, hstalkZ]
  have hX' : (t : WithBot ℕ∞) + (Order.coheight ξ : WithBot ℕ∞) =
      topologicalKrullDimAt X ξ := by
    rw [hformX, hstalkX]
  have hE : (t : WithBot ℕ∞) + (Order.coheight z : WithBot ℕ∞) =
      (t : WithBot ℕ∞) + ((Order.coheight ξ : WithBot ℕ∞) +
        ((t : WithBot ℕ∞) + (Order.coheight ξ : WithBot ℕ∞))) := by
    rw [hZ', hAt, ← hX', add_assoc]
  have hE' : t + Order.coheight z = t + (Order.coheight ξ + (t + Order.coheight ξ)) := by
    apply WithBot.coe_injective
    simpa only [WithBot.coe_add] using hE
  have hcancel : Order.coheight z = Order.coheight ξ + (t + Order.coheight ξ) :=
    WithTop.add_left_cancel htne hE'
  have hdimX : topologicalKrullDim X =
      (t : WithBot ℕ∞) + (Order.coheight ξ : WithBot ℕ∞) :=
    (topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X f ξ).trans hX'.symm
  rw [hstalkZ, hstalkX, hdimX, hcancel, WithBot.coe_add, WithBot.coe_add]
  exact add_comm _ _

/-- The dimension formula at a point of the diagonal with the dimension of `X` exhibited as a
natural number `n`: `dim 𝒪_{X ×ₖ X, Δ(ξ)} = n + dim 𝒪_{X, ξ}` with `dim X = n`. This is the form
in which `n` is compared with the length of the regular sequence cutting out the diagonal. -/
theorem exists_ringKrullDim_stalk_pullback_diagonal_eq_add {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsVariety k f] (ξ : X) :
    ∃ n : ℕ, topologicalKrullDim X = (n : WithBot ℕ∞) ∧
      ringKrullDim ((pullback f f).presheaf.stalk (pullback.diagonal f ξ)) =
        (n : WithBot ℕ∞) + ringKrullDim (X.presheaf.stalk ξ) := by
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_eq_natCast f
  exact ⟨n, hn, (ringKrullDim_stalk_pullback_diagonal f ξ).trans (by rw [hn])⟩

end Stacks.Intersection.Diagonal

end
