module

public import StacksFrontier.RingTheory.AdicCompletion.BlowupChartCompletionDepth.ChartCompletions
public import StacksFrontier.RingTheory.AdicCompletion.BlowupChartCompletionDepth.TensorModel
public import StacksFrontier.RingTheory.AdicCompletion.BlowupChartCompletionDepth.DepthDimension

/-!
# Depth and dimension along the completion of an affine blowup chart

Let `A` be a Noetherian ring with a dualizing complex, let `f ∈ I ⊆ A`, and let `Q` be a prime of
the affine blowup algebra `A[I/f]` lying over `𝔮 ⊂ A`. Write `R = (A_𝔮)^∧` and
`R' = (A[I/f]_Q)^∧` for the `I`-adic completions and `φ : R → R'` for the induced map. For a
prime `𝔭' ⊂ R'` with `I R' ⊄ 𝔭'`, its contraction `𝔭 = φ⁻¹𝔭'` and a finite `R`-module `M`,
`depth (M_𝔭) + dim (R/𝔭) = depth ((R' ⊗_R M)_{𝔭'}) + dim (R'/𝔭') + trdeg_{κ(𝔮)} κ(Q)`,
and in particular `dim (R'/𝔭') + trdeg_{κ(𝔮)} κ(Q) ≤ dim (R/𝔭)`. This is the computation in
the proof of Stacks 0EJK that leads to its display (0EJL).

The proof runs through the local ring `T` of `R ⊗_A A[I/f]` at the prime under the closed point
of `R'`. The map `A[I/f]_Q → T` is flat (because `R` is flat over `A`) and an isomorphism modulo
`I`, so the `I`-adic completion of `T` is `R'`, compatibly with the maps from `R`. Away from `f`
the ring `R ⊗_A A[I/f]` agrees with `R`, so for `𝔭_T = 𝔭' ∩ T` the local ring `T_{𝔭_T}` is
`R_𝔭` and `R_𝔭 → R'_{𝔭'}` is a localization of the completion map of `T`. Since `T` is
essentially of finite type over `R`, it has a dualizing complex, so this map is flat with
Cohen--Macaulay fibres, and the depth formula (Stacks 0338) reads
`depth ((R' ⊗_R M)_{𝔭'}) = depth (M_𝔭) + dim (fibre)`. The fibre dimension plus `dim (R'/𝔭')` is
`dim (T/𝔭_T)` by Ratliff's theorem (Stacks 0AW6), and the dimension formula (Stacks 02IJ) for the
birational extension `R/𝔭 → (R ⊗_A A[I/f])/𝔭_T` gives `dim (T/𝔭_T) + trdeg = dim (R/𝔭)`.

## Main definitions

* `Stacks.Algebraization.affineBlowupBaseCompletion`: the ring `R = (A_𝔮)^∧`.
* `Stacks.Algebraization.affineBlowupChartCompletion`: the ring `R' = (A[I/f]_Q)^∧`.
* `Stacks.Algebraization.affineBlowupCompletionMap`: the map `φ : R → R'`.

## Main results

* `Stacks.Algebraization.depth_add_ringKrullDim_le_blowupChart`:
  `depth (M_𝔭) + dim (R/𝔭) ≤ depth ((R' ⊗_R M)_{𝔭'}) + dim (R'/𝔭') + trdeg_{κ(𝔮)} κ(Q)`.
* `Stacks.Algebraization.ringKrullDim_add_trdeg_le_blowupChart`:
  `dim (R'/𝔭') + trdeg_{κ(𝔮)} κ(Q) ≤ dim (R/𝔭)`.
* `Stacks.Algebraization.depth_add_ringKrullDim_add_trdeg_eq`: the equality behind both.
* `Stacks.Algebraization.ringKrullDim_quotient_le_one_of_le_jacobson`: if `t` lies in the
  Jacobson radical of a Noetherian ring and `V(𝔭) ∩ V(t)` is a single maximal ideal, then
  `dim (R/𝔭) ≤ 1`.
* `Stacks.Algebraization.depth_localizedModule_tensorProduct_eq_add`: the depth formula
  (Stacks 0338) at a pair of primes where the map is flat.

## Implementation notes

Stacks uses the affine blowup algebra `R[IR/f]` localized at the image of the closed point of
`R'`. Since `R` is flat over `A`, that algebra is `R ⊗_A A[I/f]` (Stacks 0BIP); the tensor
product is used here because its flatness over `A[I/f]` is immediate. Rather than proving that
`R'` is the completion of a localization of `R[IR/f]`, the proof identifies the completion of `T`
with `R'` through the flat map `A[I/f]_Q → T`.

The completions `R`, `R'` and the auxiliary rings of `Stacks.Algebraization.BlowupChartModel`
are `def`s carrying their ring and algebra structures as instances, so that instance search does
not unfold adic completions, tensor products and localizations.

## References

* [Stacks Project, Tag 0EJK](https://stacks.math.columbia.edu/tag/0EJK)
* [Stacks Project, Tag 0338](https://stacks.math.columbia.edu/tag/0338)
* [Stacks Project, Tag 02IJ](https://stacks.math.columbia.edu/tag/02IJ)
* [Stacks Project, Tag 0AW6](https://stacks.math.columbia.edu/tag/0AW6)
* [Stacks Project, Tag 0BIP](https://stacks.math.columbia.edu/tag/0BIP)
-/
