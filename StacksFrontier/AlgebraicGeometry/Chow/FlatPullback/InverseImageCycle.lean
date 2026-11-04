module

public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductAssociativity
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.CoherentSheafCycle
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InverseImageDeltaDimension

/-!
# Flat pullback of the cycle of a closed subscheme and of a coherent sheaf

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` and `Y` be
locally of finite type over `S` and let `f : X ⟶ Y` be flat of relative dimension `r`.

1. If `Z ⊆ Y` is a closed subscheme with `dim_δ(Z) ≤ k`, then `dim_δ(f⁻¹ Z) ≤ k + r` and
   `[f⁻¹ Z]_{k+r} = f^*[Z]_k` in `Z_{k+r}(X)`.
2. If `F` is a coherent sheaf on `Y` with `dim_δ(Supp F) ≤ k`, then `f^*F` is coherent,
   `dim_δ(Supp f^*F) ≤ k + r` and `f^*[F]_k = [f^*F]_{k+r}` in `Z_{k+r}(X)`.

This is Stacks 02RE, each part stated as one result carrying both its dimension bound and its
cycle identity.

## Main results

* `Stacks.Chow.flatPullback_closedSubscheme_cycle` — **Stacks 02RE, part (1)**.
* `Stacks.Chow.flatPullback_coherentSheaf_cycle` — **Stacks 02RE, part (2)**.

## Implementation notes

The scheme-theoretic inverse image of the closed subscheme `i : Z ⟶ Y` is
`pullback.fst f i : X ×_Y Z ⟶ X`. The cycle `[F]_k` is only formed once the bound
`dim_δ(Supp F) ≤ k` is known, so in part (2) the cycle identity is stated for the proof of the
bound on `Supp f^*F` that the existential provides; the coherence of `f^*F`, which `[f^*F]_{k+r}`
requires, is `AlgebraicGeometry.isCoherent_pullback` (Stacks 0EBF), using that `X` is locally
Noetherian because it is locally of finite type over the locally Noetherian `S`.

The dimension bounds are `Stacks.Chow.schemeDeltaDimension_pullback_le` and
`Stacks.Chow.schemeDeltaDimension_support_pullback_le` (the source deduces them from Stacks 02R8).
The cycle identity of part (2) is `Stacks.Chow.flatPullback_cycleAssociatedToCoherentSheaf`,
the length identity of Stacks 02M1 on stalks, and that of part (1) is deduced from part (2) as in
the source: by Stacks 02QY the cycle of a closed subscheme is the cycle of the direct image of its
structure sheaf, and `f^*(i_* 𝒪_Z) ≅ (pullback.fst f i)_* 𝒪_{X ×_Y Z}`; this is
`Stacks.Chow.flatPullback_cycleAssociatedToClosedSubscheme_of_le`.

## References

* [Stacks Project, Tag 02RE](https://stacks.math.columbia.edu/tag/02RE)
* [Stacks Project, Tag 02R8](https://stacks.math.columbia.edu/tag/02R8)
* [Stacks Project, Tag 02QY](https://stacks.math.columbia.edu/tag/02QY)
* [Stacks Project, Tag 02M1](https://stacks.math.columbia.edu/tag/02M1)
* [Stacks Project, Tag 0EBF](https://stacks.math.columbia.edu/tag/0EBF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- **Stacks 02RE, part (1).** Let `f : X ⟶ Y` be flat of relative dimension `r` between schemes
locally of finite type over the base of chapter 42, and let `i : Z ⟶ Y` be a closed subscheme
with `dim_δ(Z) ≤ k`. Then the inverse image `f⁻¹ Z = X ×_Y Z` satisfies
`dim_δ(f⁻¹ Z) ≤ k + r`, and `[f⁻¹ Z]_{k+r} = f^*[Z]_k` in `Z_{k+r}(X)`. -/
@[stacks 02RE "part (1)"]
theorem flatPullback_closedSubscheme_cycle (C : ChowSituation.{u}) {X Y Z : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f] (hbase : f ≫ sY = sX) (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) (i : Z ⟶ Y) [IsClosedImmersion i] (k : ℤ)
    (hZ : schemeDeltaDimension C (i ≫ sY) ≤ (k : EInt)) :
    schemeDeltaDimension C (pullback.fst f i ≫ sX) ≤ ((k + (r : ℤ) : ℤ) : EInt) ∧
      cycleAssociatedToClosedSubscheme C sX (pullback.fst f i) (k + (r : ℤ)) =
        flatPullback C sX sY f hbase r hf k (cycleAssociatedToClosedSubscheme C sY i k) :=
  ⟨schemeDeltaDimension_pullback_le C sX sY f hbase r hf i k hZ,
    (flatPullback_cycleAssociatedToClosedSubscheme_of_le C sX sY f hbase r hf i k hZ).symm⟩

/-- **Stacks 02RE, part (2).** Let `f : X ⟶ Y` be flat of relative dimension `r` between schemes
locally of finite type over the base of chapter 42, and let `F` be a coherent sheaf on `Y` with
`dim_δ(Supp F) ≤ k`. Then `f^*F` is coherent, `dim_δ(Supp f^*F) ≤ k + r`, and
`f^*[F]_k = [f^*F]_{k+r}` in `Z_{k+r}(X)`. -/
@[stacks 02RE "part (2)"]
theorem flatPullback_coherentSheaf_cycle (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f] (hbase : f ≫ sY = sX) (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) (F : Y.Modules) [hF : F.IsCoherent] (k : ℤ)
    (hFk : schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ sY) ≤ (k : EInt)) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    letI : ((Scheme.Modules.pullback f).obj F).IsCoherent :=
      AlgebraicGeometry.isCoherent_pullback f F
    ∃ hFk' : schemeDeltaDimension C
        ((reducedSupport ((Scheme.Modules.pullback f).obj F)).subschemeι ≫ sX) ≤
          ((k + (r : ℤ) : ℤ) : EInt),
      flatPullback C sX sY f hbase r hf k (cycleAssociatedToCoherentSheaf C sY F k hFk) =
        cycleAssociatedToCoherentSheaf C sX ((Scheme.Modules.pullback f).obj F)
          (k + (r : ℤ)) hFk' :=
  ⟨schemeDeltaDimension_support_pullback_le C sX sY f hbase r hf F k hFk,
    flatPullback_cycleAssociatedToCoherentSheaf C sX sY f hbase r hf F k hFk⟩

end Stacks.Chow

end
