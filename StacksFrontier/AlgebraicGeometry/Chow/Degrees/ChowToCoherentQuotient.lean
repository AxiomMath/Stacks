module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ChowToWideLayerGeneral
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.CoherentQuotientKGroup

/-!
# The canonical map `CH_k(X) → K₀(Coh(X)/Coh_{≤k-1}(X))`

Let `(S, δ)` be as in Situation 02QL and let `X` be a scheme locally of finite type over `S`.
Remark 02SD composes the canonical map of Lemma 0FDS,

`CH_k(X) ⟶ K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))`,

with the canonical map `K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X)) ⟶ K₀(Coh(X)/Coh_{≤k-1}(X))` induced by
the exact functor that drops the upper dimension bound, and so obtains a canonical map

`CH_k(X) ⟶ K₀(Coh(X)/Coh_{≤k-1}(X))`.

The first map is `Stacks.Chow.chowToWideLayerHom`, constructed for every `X` locally of finite
type over the base: it is the descent to the Chow group of the map of Tag 02S9 read in the wide
layer, which kills the cycles rationally equivalent to zero. The second is
`Stacks.Chow.coherentDimensionToQuotientHom`. Neither is a parameter here.

## Main definitions

* `Stacks.Chow.chowToCoherentQuotientHom` — **Stacks 02SD**: the canonical map
  `CH_k(X) ⟶ K₀(Coh(X)/Coh_{≤k-1}(X))`.

## Main results

* `Stacks.Chow.chowToCoherentQuotientHom_eq_comp` — it is the composite of the map of Tag 0FDS
  with the map dropping the upper dimension bound.
* `Stacks.Chow.chowToCoherentQuotientHom_mk` — the class of a `k`-cycle `∑ n_Z[Z]` goes to
  `[⨁_{n_Z > 0} 𝒪_Z^{⊕ n_Z}] - [⨁_{n_Z < 0} 𝒪_Z^{⊕ -n_Z}]`.
* `Stacks.Chow.chowToCoherentQuotientHom_mk_dimensionLayerCycle` — the class of the cycle
  `[F]_k` of a coherent module `F` whose support has delta-dimension at most `k` goes to the class
  of `F`.

## Implementation notes

The source writes `Coh_{k+1}(X)` in the displayed maps of the remark; it means
`Coh_{≤k+1}(X)`, the category of Lemma 0FDS, and that is what is formalized.

The remark also recalls that the map of Lemma 0FDS is injective (Tag 02SC). That is a forward
reference which the remark does not use to build the composite, and it is not part of the
statement here; the composite itself need not be injective.

## References

* [Stacks Project, Tag 02SD](https://stacks.math.columbia.edu/tag/02SD)
* [Stacks Project, Tag 0FDS](https://stacks.math.columbia.edu/tag/0FDS)
* [Stacks Project, Tag 02S9](https://stacks.math.columbia.edu/tag/02S9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}}

/-- **Stacks 02SD**, the canonical map `CH_k(X) → K₀(Coh(X)/Coh_{≤k-1}(X))` for `X` locally of
finite type over the base of a Chow situation: the canonical map
`CH_k(X) → K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))` of Lemma 0FDS (`Stacks.Chow.chowToWideLayerHom`)
followed by the canonical map `K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X)) → K₀(Coh(X)/Coh_{≤k-1}(X))`
(`Stacks.Chow.coherentDimensionToQuotientHom`). -/
@[stacks 02SD "the canonical map `CH_k(X) → K₀(Coh(X)/Coh_{≤k-1}(X))`, built from Lemma 0FDS"]
def chowToCoherentQuotientHom (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (k : ℤ) : chowGroup C f k →+ coherentQuotientKZero C f (k - 1) :=
  chowToCoherentQuotientKZero C f k (chowToWideLayerHom C f k)

/-- The canonical map `CH_k(X) → K₀(Coh(X)/Coh_{≤k-1}(X))` is the map of Lemma 0FDS followed by
the map dropping the upper dimension bound. -/
theorem chowToCoherentQuotientHom_eq_comp (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) :
    chowToCoherentQuotientHom C f k =
      (coherentDimensionToQuotientHom C f (k - 1) (k + 1)).comp (chowToWideLayerHom C f k) :=
  rfl

/-- The canonical map `CH_k(X) → K₀(Coh(X)/Coh_{≤k-1}(X))` sends the class of a `k`-cycle
`∑ n_Z[Z]` to `[⨁_{n_Z > 0} 𝒪_Z^{⊕ n_Z}] - [⨁_{n_Z < 0} 𝒪_Z^{⊕ -n_Z}]`. -/
theorem chowToCoherentQuotientHom_mk (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) (c : CycleGroup C f k) :
    chowToCoherentQuotientHom C f k (QuotientAddGroup.mk' (rationalEquivalences C f k) c) =
      coherentQuotientKZeroMk C f (k - 1) (cycleStructureSheafDimLE C f k
          (cyclePositivePart C f k c)).obj -
        coherentQuotientKZeroMk C f (k - 1) (cycleStructureSheafDimLE C f k
          (cycleNegativePart C f k c)).obj := by
  rw [chowToCoherentQuotientHom_eq_comp, AddMonoidHom.comp_apply, chowToWideLayerHom,
    chowToDimensionLayerHom_mk, cycleDimensionLayerWideHom_apply, map_sub,
    coherentDimensionToQuotientHom_apply_mk, coherentDimensionToQuotientHom_apply_mk]
  rfl

/-- The canonical map `CH_k(X) → K₀(Coh(X)/Coh_{≤k-1}(X))` sends the class of the cycle `[F]_k`
of a coherent `𝒪_X`-module `F` whose support has delta-dimension at most `k` to the class of
`F`. -/
theorem chowToCoherentQuotientHom_mk_dimensionLayerCycle (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) (F : CoherentModulesDimLE C f k) :
    chowToCoherentQuotientHom C f k
        (QuotientAddGroup.mk' (rationalEquivalences C f k) (dimensionLayerCycle C f k F)) =
      coherentQuotientKZeroMk C f (k - 1) F.obj := by
  rw [chowToCoherentQuotientHom_eq_comp, AddMonoidHom.comp_apply, chowToWideLayerHom,
    chowToDimensionLayerHom_mk, cycleDimensionLayerWideHom_dimensionLayerCycle,
    coherentDimensionToQuotientHom_apply_mk]
  rfl

end Stacks.Chow
