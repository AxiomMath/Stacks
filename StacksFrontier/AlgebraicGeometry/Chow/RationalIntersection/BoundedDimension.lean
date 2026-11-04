module

public import StacksFrontier.AlgebraicGeometry.Chow.ChowHomologyCoherentKZeroBijective
public import StacksFrontier.Topology.Dimension.CatenaryOfDimensionFunction
public import StacksFrontier.Topology.Dimension.DimensionFunctionIsCatenary

/-!
# Bounded delta-dimension and finite dimension

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `X` be locally of
finite type over `S`, with relative dimension function `δ_{X/S}`. Lemma 0FEY of the Stacks
Project assumes `δ_{X/S}` bounded, while Section 0FEX introduces the intersection product for `X`
Noetherian and finite dimensional. This file relates the two hypotheses.

Since `δ_{X/S}` is a dimension function on the sober space `X`, for a specialization `ξ ⤳ x` the
difference `δ(ξ) - δ(x)` is the codimension of `\overline{\{x\}}` in `\overline{\{ξ\}}`
(Stacks 02IA), the supremum of the lengths of chains of irreducible closed subsets between them.
So a chain of irreducible closed subsets of `X` of length `e` forces `δ` to vary by at least
`e`, and conversely a specialization along which `δ` drops by `e` yields a chain of length `e`.

* If `X` is Noetherian of finite dimension `n`, every point specializes from one of the finitely
  many generic points of `X`, and `δ` drops by at most `n` along each such specialization; so
  `δ_{X/S}` is bounded.
* If `δ_{X/S}` takes values in `[lo, hi]`, every chain of irreducible closed subsets has length
  at most `hi - lo`, so `X` has dimension at most `hi - lo`.

## Main results

* `Stacks.Chow.relativeDimension_sub_le_of_specializes` — `δ(ξ) - δ(x) ≤ dim X` for `ξ ⤳ x`.
* `Stacks.Chow.exists_bounds_relativeDimension` — on a finite dimensional Noetherian `X`,
  `δ_{X/S}` is bounded.
* `Stacks.Chow.topologicalKrullDim_le_of_relativeDimension_bounds` — if `δ_{X/S}` takes values
  in `[lo, hi]` then `dim X ≤ hi - lo`.

## References

* [Stacks Project, Tag 0FEX](https://stacks.math.columbia.edu/tag/0FEX)
* [Stacks Project, Tag 0FEY](https://stacks.math.columbia.edu/tag/0FEY)
* [Stacks Project, Tag 02IA](https://stacks.math.columbia.edu/tag/02IA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Order

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **The relative dimension drops by at most the dimension of `X` along a specialization.** For
`ξ ⤳ x`, `δ(ξ) - δ(x)` is the codimension of `\overline{\{x\}}` in `\overline{\{ξ\}}`
(Stacks 02IA), which is at most the dimension of `X`. -/
theorem relativeDimension_sub_le_of_specializes {n : ℕ} (hn : topologicalKrullDim X ≤ n)
    {ξ x : X} (h : ξ ⤳ x) :
    relativeDimension C.dimensionFunction sX ξ -
      relativeDimension C.dimensionFunction sX x ≤ n := by
  obtain ⟨d, hd⟩ :=
    relativeDimension_isDimensionFunction C.isUniversallyCatenary C.dimensionFunction sX
  have hcodim := (isCatenarySpace_and_topCodim_eq_of_isDimensionFunction X (scheme_stacksSober X)
    d d.isDimensionFunctionForCatenary).2 ξ x h
  have hle : IrreducibleClosedsCodim.topCodim (IrreducibleCloseds.closureSingleton x)
      (IrreducibleCloseds.closureSingleton ξ) ≤ n := by
    refine iSup_le fun p ↦ ?_
    have h1 := (p.1.length_le_krullDim).trans hn
    exact_mod_cast h1
  rw [hcodim] at hle
  have h2 : (d ξ - d x).toNat ≤ n := by exact_mod_cast hle
  rw [← hd, ← hd]
  omega

/-- **On a finite dimensional Noetherian scheme the relative dimension is bounded.** It is bounded
above on any Noetherian scheme (`Stacks.Chow.exists_relativeDimension_le`), and below because every
point specializes from one of the finitely many generic points of `X`, along a specialization on
which it drops by at most `dim X`. -/
theorem exists_bounds_relativeDimension [IsNoetherian X] (hdim : topologicalKrullDim X ≠ ⊤) :
    ∃ lo hi : ℤ, ∀ x : X, lo ≤ relativeDimension C.dimensionFunction sX x ∧
      relativeDimension C.dimensionFunction sX x ≤ hi := by
  classical
  obtain ⟨n, hn⟩ : ∃ n : ℕ, topologicalKrullDim X ≤ n := by
    rcases h : topologicalKrullDim X with _ | m
    · exact ⟨0, bot_le⟩
    · rcases m with _ | m
      · exact absurd h hdim
      · exact ⟨m, le_rfl⟩
  obtain ⟨hi, hhi⟩ := exists_relativeDimension_le C sX
  let g : Set X → ℤ := fun W ↦
    if hW : IsIrreducible W then relativeDimension C.dimensionFunction sX hW.genericPoint else 0
  obtain ⟨lo, hlo⟩ :=
    ((TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := X)).image g).bddBelow
  refine ⟨lo - n, hi, fun x ↦ ⟨?_, hhi x⟩⟩
  obtain ⟨W, hW, hxW⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible {x} isIrreducible_singleton
  have hgen := hW.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents W hW)
  have hx : hW.1.genericPoint ⤳ x := hgen.specializes (hxW rfl)
  have h1 : lo ≤ g W := hlo ⟨W, hW, rfl⟩
  have h2 : g W = relativeDimension C.dimensionFunction sX hW.1.genericPoint := by
    simp only [g, dite_eq_left hW.1]
  have h3 := relativeDimension_sub_le_of_specializes C sX hn hx
  omega

/-- **Bounded relative dimension bounds the dimension.** If `δ_{X/S}` takes values in `[lo, hi]`
then every chain of irreducible closed subsets of `X` has length at most `hi - lo`, since `δ`
strictly increases along it; so `dim X ≤ hi - lo`. -/
theorem topologicalKrullDim_le_of_relativeDimension_bounds (lo hi : ℤ)
    (h : ∀ x : X, lo ≤ relativeDimension C.dimensionFunction sX x ∧
      relativeDimension C.dimensionFunction sX x ≤ hi) :
    topologicalKrullDim X ≤ (hi - lo).toNat := by
  obtain ⟨d, hd⟩ :=
    relativeDimension_isDimensionFunction C.isUniversallyCatenary C.dimensionFunction sX
  refine iSup_le fun p ↦ ?_
  obtain ⟨y, hy⟩ := QuasiSober.sober p.head.isIrreducible p.head.isClosed
  obtain ⟨x, hx⟩ := QuasiSober.sober p.last.isIrreducible p.last.isClosed
  have hchain := chain_length_le_delta_diff (scheme_stacksSober X) d
    d.isDimensionFunctionForCatenary x y p.length (fun i ↦ (p i : Set X))
    (isClosedIrreducibleChain_coe p hy.symm hx.symm)
  rw [hd, hd] at hchain
  have hx' := (h x).2
  have hy' := (h y).1
  have hlen : p.length ≤ (hi - lo).toNat := by omega
  exact_mod_cast hlen

end Stacks.Chow

end
