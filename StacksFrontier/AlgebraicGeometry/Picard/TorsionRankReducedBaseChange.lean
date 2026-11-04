module

public import StacksFrontier.AlgebraicGeometry.Picard.TorsionRankBaseChange
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionRankReduction

/-!
# The reduction of Stacks 0CE6 to the reduced case over an algebraically closed field

[Stacks, Tag 0CE6](https://stacks.math.columbia.edu/tag/0CE6) bounds the `ℓ`-torsion of the
Picard group of a proper scheme `X` of dimension at most one over a field `k`, for a prime `ℓ`
invertible in `k`:

`dim_{F_ℓ} Pic(X)[ℓ] ≤ dim_k H¹(X, 𝒪_X) + g_geom(X/k)`.

Its proof makes three reductions before quoting [Stacks, Tag 0C20]: base change to an algebraic
closure `k̄` (injectivity of `Pic(X) → Pic(X_{k̄})` by [Stacks, Tag 0CC5], invariance of
`dim H¹` by [Stacks, Tag 02KH]), and passage to the reduction (the genus drops, the geometric
genus is unchanged by [Stacks, Tag 0CE2] (1), and the `ℓ`-torsion of the Picard group is
unchanged).  Those three steps are
`AlgebraicGeometry.picardTorsion_bound_of_baseChange_algebraicClosure` and
`AlgebraicGeometry.picardTorsion_bound_of_reduction`; this file composes them into the single
statement that the inequality for `(X_{k̄})_red` over `k̄` implies the inequality for `X` over
`k`.

## Main results

* `AlgebraicGeometry.picardTorsion_bound_of_reducedBaseChange`: **the whole reduction of
  [Stacks, Tag 0CE6] to the reduced case over an algebraically closed field.**

## Implementation notes

The dimension bound and the invertibility of `ℓ` are transported to `X_{k̄}` on the way: the
Krull dimension is unchanged by extension of the ground field
(`AlgebraicGeometry.topologicalKrullDim_baseChange`, the dimension clause of
[Stacks, Tag 0BY9]), and `ℓ` stays invertible in `k̄`.

**No `@[stacks 0CE6]` attribute is attached here.**  The tag is registered on
`AlgebraicGeometry.finrank_picardTorsion_le_genus_add_geometricGenus` in
`StacksFrontier.AlgebraicGeometry.Picard.TorsionRankConnectedComponents`, which supplies what this
file left open: the decomposition of a reduced proper scheme of dimension at most one into its
finitely many clopen connected components, the additivity over those of the `ℓ`-torsion rank of
the Picard group, of the genus and of the geometric genus, and the dimension-zero case, where the
Picard group is trivial, and applies [Stacks, Tag 0C20] to the one-dimensional components.

## References

* [Stacks Project, Tag 0CE6](https://stacks.math.columbia.edu/tag/0CE6)
* [Stacks Project, Tag 0C20](https://stacks.math.columbia.edu/tag/0C20)
* [Stacks Project, Tag 0CC5](https://stacks.math.columbia.edu/tag/0CC5)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0CE2](https://stacks.math.columbia.edu/tag/0CE2)
* [Stacks Project, Tag 0CE3](https://stacks.math.columbia.edu/tag/0CE3)
* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Picard (ofScheme)

universe u

namespace AlgebraicGeometry

attribute [local instance] AddSubgroup.torsionBy.zmodModule

/-- **The reduction of [Stacks, Tag 0CE6] to the reduced case over an algebraically closed
field.** Let `k` be a field, let `X` be a proper scheme of dimension at most one over `k` and let
`ℓ` be a prime invertible in `k`.  Write `Y = X_{k̄}` for the base change to an algebraic closure
and `Y_red` for its reduction.  If the `ℓ`-torsion of `Pic(Y_red)` is finite-dimensional over
`F_ℓ` and bounded by the genus of `Y_red` plus its geometric genus over `k̄`, then the `ℓ`-torsion
of `Pic(X)` is finite-dimensional over `F_ℓ` and

`dim_{F_ℓ} Pic(X)[ℓ] ≤ dim_k H¹(X, 𝒪_X) + g_geom(X/k)`.

This is the composite of the base-change step
`AlgebraicGeometry.picardTorsion_bound_of_baseChange_algebraicClosure` and the reduction step
`AlgebraicGeometry.picardTorsion_bound_of_reduction`; what it leaves is exactly
[Stacks, Tag 0C20] for the connected components of `Y_red`. -/
theorem picardTorsion_bound_of_reducedBaseChange (k : Type u) [Field k] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of k)) [IsProper g] (hdim : topologicalKrullDim (X : Type u) ≤ 1)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : k))
    (hfin : FiniteDimensional (ZMod ℓ) (AddSubgroup.torsionBy
      (ofScheme (pullback g
        (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))).reduction) (ℓ : ℤ)))
    (hbound : Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy
        (ofScheme (pullback g
          (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))).reduction)
          (ℓ : ℤ)) ≤
      genus ((pullback g
            (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))).reductionι ≫
          pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) +
        geometricGenus (AlgebraicClosure k) ((pullback g
            (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))).reductionι ≫
          pullback.snd g
            (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))) :
    FiniteDimensional (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme X) (ℓ : ℤ)) ∧
      Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme X) (ℓ : ℤ)) ≤
        genus g + geometricGenus k g := by
  set a := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))) with ha
  have hdimY : topologicalKrullDim ((pullback g a : Scheme.{u}) : Type u) ≤ 1 := by
    rw [topologicalKrullDim_baseChange k (AlgebraicClosure k) (pullback.fst g a)
      (pullback.snd g a) g (IsPullback.of_hasPullback g a)]
    exact hdim
  have hℓ' : IsUnit ((ℓ : ℕ) : AlgebraicClosure k) := by
    simpa using hℓ.map (algebraMap k (AlgebraicClosure k))
  obtain ⟨h1, h2⟩ := picardTorsion_bound_of_reduction (AlgebraicClosure k)
    (pullback.snd g a) hdimY ℓ hℓ' hfin hbound
  exact picardTorsion_bound_of_baseChange_algebraicClosure k g hdim ℓ h1 h2

end AlgebraicGeometry

end
