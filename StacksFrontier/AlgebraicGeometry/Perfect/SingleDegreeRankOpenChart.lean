module

public import StacksFrontier.AlgebraicGeometry.Perfect.SingleDegreeRankOpen

/-!
# The open subscheme of a single-degree rank locus, read on a chart

Let `X` be a scheme, `E` an object of the derived category of sheaves of modules on `X`, `i` an
integer and `r` a natural number, and let `U = singleDegreeRankOpen E i r` be the largest open
subscheme of `X` on which `E` is a finite locally free module of rank `r` placed in degree `i`.

This file converts a *local* statement — that `E` has that shape on some chart around a point —
into the *global* statement that the point lies in `U`, and shows the conversion is reversible.
That passage is the step the proof of [stacks 0BDK] performs when it concludes, from the local
structure of a perfect complex on an affine neighbourhood, that a point lies in the asserted open
subscheme; the same passage, for a locally closed subscheme in place of an open one, is what the
proof of [stacks 0BDL] calls gluing and leaves to the reader.

## Main results

* `AlgebraicGeometry.Scheme.Modules.mem_singleDegreeRankOpen_of_isOpenImmersion`: if `E`
  restricted along an open immersion `h : W ⟶ X` is a finite locally free module of rank `r`
  placed in degree `i`, then every point in the range of `h` lies in `U`.
* `AlgebraicGeometry.Scheme.Modules.mem_singleDegreeRankOpen_iff_exists_isAffineOpen`: a point
  lies in `U` exactly when some **affine** open neighbourhood of it carries `E` in degree `i`
  with rank `r`. This is the chart-level reading of membership in `U`, and the interface an
  argument on an affine chart meets.

## Implementation notes

Neither direction is new mathematics: the first is the universal property for open immersions,
`AlgebraicGeometry.Scheme.Modules.factorsThrough_singleDegreeRankOpen_iff`, read on ranges, and
the second adds to it that the affine opens are a basis, through Mathlib's
`AlgebraicGeometry.Scheme.exists_affine_mem_range_and_range_subset`, together with the locality
of the condition, `AlgebraicGeometry.Scheme.Modules.IsSingleDegreeRank.mono`. What is recorded is
the composite, because it is the form in which the local structure theorem for perfect complexes
on an affine chart ([stacks 0BCD]) has to be consumed, and the library had no statement
concluding membership in `singleDegreeRankOpen` at all.

Nothing here uses perfectness of `E`, for the same reason that the construction of `U` does not:
the condition on an open and its locality hold for every object of the derived category.

These results carry no Stacks attribute. They are a reformulation of the characterisation
`AlgebraicGeometry.Scheme.Modules.nonempty_iso_singleFunctor_restrict_iff_le`, a step of the proof
of [stacks 0BDK], whose statement is
`AlgebraicGeometry.Scheme.Modules.existsUnique_opens_singleDegreeRank_int`.

## References

* [The Stacks Project, Lemma 36.31.3 (0BDK)](https://stacks.math.columbia.edu/tag/0BDK)
* [The Stacks Project, Lemma 36.31.4 (0BDL)](https://stacks.math.columbia.edu/tag/0BDL)
* [The Stacks Project, Lemma 15.77.7 (0BCD)](https://stacks.math.columbia.edu/tag/0BCD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (E : DerivedCategory X.Modules) (i : ℤ) (r : ℕ)

/-- **A chart on which `E` has the right shape puts its points in the open subscheme of
[stacks 0BDK].** If `E` restricted along an open immersion `h : W ⟶ X` is isomorphic to a finite
locally free module of rank `r` placed in degree `i`, then every point of `X` in the range of `h`
lies in `singleDegreeRankOpen E i r`.

The hypothesis is exactly the right-hand side of the universal property for open immersions, so
that property produces a factorisation of `h` through the open subscheme, and the range of `h` is
then contained in the range of its structural map. -/
theorem mem_singleDegreeRankOpen_of_isOpenImmersion {W : Scheme.{u}} (h : W ⟶ X)
    [IsOpenImmersion h]
    (hW : ∃ M : W.Modules,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r ∧
        Nonempty ((restrictFunctor h).mapDerivedCategory.obj E ≅
          (DerivedCategory.singleFunctor W.Modules i).obj M))
    {x : X} (hx : x ∈ Set.range h.base) :
    x ∈ singleDegreeRankOpen E i r := by
  obtain ⟨g, hg⟩ := (factorsThrough_singleDegreeRankOpen_iff E i r h).2 hW
  obtain ⟨w, rfl⟩ := hx
  have hmem : (g ≫ (singleDegreeRankOpen E i r).ι).base w ∈
      Set.range (singleDegreeRankOpen E i r).ι.base := ⟨g.base w, by simp⟩
  rwa [hg, Scheme.Opens.range_ι] at hmem

/-- **Membership in the open subscheme of [stacks 0BDK] is an affine-chart condition.** A point
of `X` lies in `singleDegreeRankOpen E i r` exactly when it has an affine open neighbourhood
which carries `E` in degree `i` with rank `r`.

From left to right the affine opens contained in `singleDegreeRankOpen E i r` cover it, and the
condition passes to smaller opens; from right to left an open carrying `E` in degree `i` with
rank `r` is contained in `singleDegreeRankOpen E i r` by construction. -/
theorem mem_singleDegreeRankOpen_iff_exists_isAffineOpen {x : X} :
    x ∈ singleDegreeRankOpen E i r ↔
      ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ IsSingleDegreeRank E i r V := by
  constructor
  · intro hx
    obtain ⟨R, f, hf, hxf, hsub⟩ :=
      Scheme.exists_affine_mem_range_and_range_subset (U := singleDegreeRankOpen E i r) hx
    exact ⟨f.opensRange, isAffineOpen_opensRange f, hxf,
      IsSingleDegreeRank.mono E i r (isSingleDegreeRank_singleDegreeRankOpen E i r) hsub⟩
  · rintro ⟨V, -, hxV, hV⟩
    exact le_singleDegreeRankOpen E i r hV hxV

end AlgebraicGeometry.Scheme.Modules

end
