module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceAssembly
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersection
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.GlobalTop

/-!
# Chow classes in the top degree are determined locally

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `W` be locally of
finite type over `S` with `dim_δ(W) ≤ k`. Then `W` has no integral closed subscheme of
`δ`-dimension `k + 1`, so no nonzero `k`-cycle on `W` is rationally equivalent to zero and
`CH_k(W) = Z_k(W)` is the free abelian group on the irreducible closed subsets of `W` of
`δ`-dimension `k`, that is on the irreducible components of `W` of that dimension. A class in
`CH_k(W)` is therefore determined by the coefficients of its unique representative at the generic
points of those components, and since restriction to an open subscheme does not change the
coefficient at a point of the open, two classes agree as soon as they agree after restriction to
a family of opens containing all points of `δ`-dimension `k`.

This is the description of `CH_{n-r}(Z ×_X Y)` that the proof of Stacks 0FEA uses to reduce the
statement to a neighbourhood of each generic point of `Z ×_X Y` of `δ`-dimension `n - r`.

## Main results

* `Stacks.Chow.mk_injective_of_relativeDimension_le` — for `dim_δ(W) ≤ k` the quotient map
  `Z_k(W) ⟶ CH_k(W)` is injective, so `CH_k(W) = Z_k(W)`.
* `Stacks.Chow.eq_of_forall_chowGroupRestrict_eq` — two classes in `CH_k(W)`, `dim_δ(W) ≤ k`,
  are equal as soon as every point of `δ`-dimension `k` lies in an open subscheme over which
  their restrictions agree.

## References

* [Stacks Project, Tag 0FEA](https://stacks.math.columbia.edu/tag/0FEA)
* [Stacks Project, Tag 02QR](https://stacks.math.columbia.edu/tag/02QR)
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-- **`CH_k(W) = Z_k(W)` in the top degree.** If every point of `W` has `δ`-dimension at most
`k`, the quotient map from `k`-cycles to `CH_k(W)` is injective: there are no rational
equivalences in degree `k`. -/
theorem mk_injective_of_relativeDimension_le (C : ChowSituation.{u}) {W : Scheme.{u}}
    (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (k : ℤ)
    (hdim : ∀ w : W, relativeDimension C.dimensionFunction sW w ≤ k) :
    Function.Injective (QuotientAddGroup.mk' (rationalEquivalences C sW k)) := by
  intro a b hab
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq,
    rationalEquivalences_eq_bot_of_relativeDimension_le C sW k hdim,
    AddSubgroup.mem_bot] at hab
  exact (neg_add_eq_zero.mp hab)

/-- **Classes in the top degree are determined locally.** Let `dim_δ(W) ≤ k`. If every point of
`W` of `δ`-dimension `k` lies in the image of an open immersion `v : U ⟶ W` along which the
restrictions of `α` and `β` agree, then `α = β` in `CH_k(W)`.

Both classes are cycles, by `Stacks.Chow.mk_injective_of_relativeDimension_le`, and so is each
restriction; the coefficient of a restriction at a point of `U` is the coefficient at its image,
and a `k`-cycle has nonzero coefficients only at points of `δ`-dimension `k`. -/
theorem eq_of_forall_chowGroupRestrict_eq (C : ChowSituation.{u}) {W : Scheme.{u}}
    (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (k : ℤ)
    (hdim : ∀ w : W, relativeDimension C.dimensionFunction sW w ≤ k)
    {α β : chowGroup C sW k}
    (h : ∀ w : W, relativeDimension C.dimensionFunction sW w = k →
      ∃ (U : Scheme.{u}) (sU : U ⟶ C.S) (_ : LocallyOfFiniteType sU) (v : U ⟶ W)
        (_ : IsOpenImmersion v) (hv : v ≫ sW = sU),
        w ∈ Set.range v.base ∧
          chowGroupRestrict C sW sU v hv k α = chowGroupRestrict C sW sU v hv k β) :
    α = β := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (rationalEquivalences C sW k) α
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective (rationalEquivalences C sW k) β
  congr 1
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun w => ?_)
  by_cases hw : relativeDimension C.dimensionFunction sW w = k
  · obtain ⟨U, sU, _, v, _, hv, ⟨u, rfl⟩, hres⟩ := h w hw
    have hdimU : ∀ u' : U, relativeDimension C.dimensionFunction sU u' ≤ k := fun u' => by
      rw [← hv, relativeDimension_comp_isOpenImmersion]
      exact hdim _
    rw [chowGroupRestrict_mk, chowGroupRestrict_mk] at hres
    have hcyc := congrArg (fun c : CycleGroup C sU k => c.1 u)
      (mk_injective_of_relativeDimension_le C sU k hdimU hres)
    simpa only [cycleGroupRestrict_apply] using hcyc
  · have hz : ∀ c : CycleGroup C sW k, c.1 w = 0 := fun c => by
      by_contra hne
      exact hw ((mem_cyclesOfDimension_iff_forall_point C sW k c.1).mp c.2 w hne)
    rw [hz a, hz b]

end Stacks.Chow

end
