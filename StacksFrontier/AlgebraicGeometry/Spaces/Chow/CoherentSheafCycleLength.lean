module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CoherentSheafCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.LengthAtPoint

/-!
# The coefficients of the cycle of a coherent sheaf are lengths

In Situation 0EDT let `X/B` be good and let `F` be a coherent `𝒪_X`-module with
`dim_δ(Supp(F)) ≤ k`. **Stacks 0EEC** says that the coefficient of an integral closed subspace `Z`
of δ-dimension `k` in the cycle `[F]_k` of Stacks 0EEB is the length of `F` at the generic point
`ξ` of `Z`, in the sense of Definition 0EE2.

## Main results

* `AlgebraicGeometry.Space.exists_associatedCycle_apply_eq_and_hasLengthAt`: **Stacks 0EEC**. The
  coefficient of `Z` in `[F]_k` and the length of `F` at `ξ` are the same natural number, and that
  length is read at every geometric point above `ξ`.

## Implementation notes

The cycle `AlgebraicGeometry.Space.associatedCycle` is built from a choice `γ` of a geometric point
above each point of `|X|`, and its coefficient at `Z` is the length at `γ ξ` read in `ℤ` through
`ENat.toNat` (`AlgebraicGeometry.Space.associatedCycle_apply_eq_geometricLength`). Two inputs turn
this into the statement of the source: the length at `ξ` is finite, by Stacks 0EE6 and 0EE4 when
`ξ ∈ Supp(F)` and because it vanishes otherwise, so `ENat.toNat` loses nothing; and it does not
depend on the geometric point above `ξ`, by Stacks 0EE1
(`AlgebraicGeometry.Space.geometricLength_eq_of_image_eq`).

## References

* [Stacks Project, Tag 0EEC](https://stacks.math.columbia.edu/tag/0EEC)
* [Stacks Project, Tag 0EEB](https://stacks.math.columbia.edu/tag/0EEB)
* [Stacks Project, Tag 0EE1](https://stacks.math.columbia.edu/tag/0EE1)
* [Stacks Project, Tag 0EE2](https://stacks.math.columbia.edu/tag/0EE2)
* [Stacks Project, Tag 0EE4](https://stacks.math.columbia.edu/tag/0EE4)
* [Stacks Project, Tag 0EE6](https://stacks.math.columbia.edu/tag/0EE6)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- **Stacks 0EEC.** In Situation 0EDT let `X/B` be good, let `F` be a coherent `𝒪_X`-module with
`dim_δ(Supp(F)) ≤ k`, let `Z` be an integral closed subspace of `X` with `dim_δ(Z) = k` and let `ξ`
be its generic point. Then the coefficient of `Z` in `[F]_k` is the length of `F` at `ξ`.

The length at a point of `|X|` is that of Definition 0EE2, `AlgebraicGeometry.Space.HasLengthAt`,
and the statement reads it at *every* geometric point `x̄` above `ξ`, not only at the one `γ`
chooses. The coefficient is an integer and the length lies in `ℕ∞`; the statement says that both
are the same natural number `n`, so in particular the length at `ξ` is finite.

The generic point is `AlgebraicGeometry.Space.IntegralClosedSubspace.ambientGenericPoint`. As in
the source, the proof splits on whether `ξ` lies in `Supp(F)`. If it does, the δ-dimension bound
makes `ξ` a generic point of an irreducible component of `Supp(F)` by Stacks 0EE6, where the length
is finite by Stacks 0EE4; if not, the length vanishes by Stacks 07TZ. In both cases the coefficient
is the length at `γ ξ`, by `AlgebraicGeometry.Space.associatedCycle_apply_eq_geometricLength`, and
Stacks 0EE1 (`AlgebraicGeometry.Space.geometricLength_eq_of_image_eq`) moves it to any other
geometric point above `ξ`. -/
@[stacks 0EEC "the length at the generic point is that of Definition 0EE2, read at every geometric
  point above it; the integer coefficient and the ℕ∞-valued length are the same natural number"]
theorem exists_associatedCycle_apply_eq_and_hasLengthAt (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (F : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    [IsCoherent D.site D.base D.base_mem X hX.1 F] (k : ℤ)
    (γ : points D.site D.base D.base_mem X → GeometricPoint D.site D.base D.base_mem X)
    (hγ : ∀ x, (γ x).LiesOver x)
    (hdim : deltaDimensionClosed D sX hX (moduleSupport D.site D.base D.base_mem hX.1 F)
      (isClosed_moduleSupport D.site D.base D.base_mem hX.1 F) ≤ (k : EInt))
    {Z : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hZ : deltaDimension D sX Z = k) :
    ∃ n : ℕ, (associatedCycle D sX hX F k γ hγ hdim).1 Z = n ∧
      HasLengthAt D.site D.base D.base_mem hX.1 F (Z.ambientGenericPoint D.site D.base D.base_mem)
        n ∧
      ∀ xbar : GeometricPoint D.site D.base D.base_mem X,
        xbar.LiesOver (Z.ambientGenericPoint D.site D.base D.base_mem) →
          geometricLength D.site D.base D.base_mem ⟨X, hX.1⟩ xbar F = n := by
  set ξ := Z.ambientGenericPoint D.site D.base D.base_mem
  have htop : geometricLength D.site D.base D.base_mem ⟨X, hX.1⟩ (γ ξ) F ≠ ⊤ := by
    by_cases hmem : ξ ∈ moduleSupport D.site D.base D.base_mem hX.1 F
    · obtain ⟨C, hC⟩ := isGenericPoint_of_deltaDimensionClosed_le D sX hX
        (moduleSupport D.site D.base D.base_mem hX.1 F)
        (isClosed_moduleSupport D.site D.base D.base_mem hX.1 F) _ hmem k hdim hZ
      exact (geometricLength_ne_top_and_pos_of_isGenericPoint_supportOfSheaf D.site D.base
        D.base_mem ⟨X, hX.1⟩
        (isLocallyNoetherian_of_isLocallyOfFiniteType D.site D.base D.base_mem hX.1
          D.isAlgebraicSpace sX hX.2.2 D.locallyNoetherian)
        (D.isDecentSpace_of_isGood sX hX) F hmem C hC _ (hγ ξ)).1
    · exact moduleMultiplicity_ne_top_of_notMem_moduleSupport D.site D.base D.base_mem
        hX.1 F γ hγ Z hmem
  have hall : ∀ xbar : GeometricPoint D.site D.base D.base_mem X, xbar.LiesOver ξ →
      geometricLength D.site D.base D.base_mem ⟨X, hX.1⟩ xbar F =
        ((geometricLength D.site D.base D.base_mem ⟨X, hX.1⟩ (γ ξ) F).toNat : ℕ∞) := by
    intro xbar hxbar
    rw [ENat.natCast_toNat htop]
    exact geometricLength_eq_of_image_eq D.site D.base D.base_mem hX.1 xbar (γ ξ)
      (hxbar.trans (hγ ξ).symm) F
  refine ⟨(geometricLength D.site D.base D.base_mem ⟨X, hX.1⟩ (γ ξ) F).toNat,
    associatedCycle_apply_eq_geometricLength D sX hX F k γ hγ hdim hZ,
    ⟨γ ξ, hγ ξ, hall _ (hγ ξ)⟩, hall⟩

end AlgebraicGeometry.Space

end
