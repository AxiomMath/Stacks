module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPushforwardRelative
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentSummand

/-!
# A summand of a relatively `m`-pseudo-coherent object is relatively `m`-pseudo-coherent

Let `f : X ⟶ S` be a morphism of schemes locally of finite type and let `E`, `K` be objects of
the derived category of `𝒪_X`-modules. If the direct sum `E ⊕ K` is `m`-pseudo-coherent relative
to `S` then so are `E` and `K`. This is Stacks 09UN.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_of_biprod`: both summands at once.
* `AlgebraicGeometry.Scheme.Hom.IsPseudoCoherentFrom.of_biprod_left` and
  `AlgebraicGeometry.Scheme.Hom.IsPseudoCoherentFrom.of_biprod_right`: the two conclusions
  separately.

## Implementation notes

No gluing is involved: the covers witnessing relative `m`-pseudo-coherence of `E ⊞ K` serve
verbatim for each summand, so the whole argument happens at one closed immersion
`i : U ⟶ 𝔸ⁿ_V` at a time. There the local condition of Stacks 09UI is sheaf-level
`m`-pseudo-coherence of `i_*` of the restriction
(`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_iff`), and both
restriction along an open immersion and pushforward along a closed immersion are additive, hence
carry the biproduct to a biproduct. Stacks 064X at the ringed space `𝔸ⁿ_V`, which is
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_biprod`, then splits it.

`CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBiproducts` is a lemma rather than an
instance, so it is made a local instance here; that is what makes
`CategoryTheory.Functor.mapBiprod` available for the two functors involved.

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`,
which is made a local instance; there is no global instance, so a user of these results makes the
same declaration.

## References

* [The Stacks Project, Lemma 36.61.9 (09UN)](https://stacks.math.columbia.edu/tag/09UN)
* [The Stacks Project, Definition 36.61.1 (09UI)](https://stacks.math.columbia.edu/tag/09UI)
* [The Stacks Project, Lemma 15.64.4 (064X)](https://stacks.math.columbia.edu/tag/064X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance] CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBiproducts

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

namespace Scheme.Modules

/-- Both summands of a binary biproduct satisfying the local condition of Stacks 09UI at a closed
immersion `i` satisfy it as well: the condition is sheaf-level `m`-pseudo-coherence of `i_*` of
the object, `i_*` is additive, and Stacks 064X splits the resulting biproduct. -/
public theorem isPseudoCoherentFromAfterPushforward_of_biprod {X Y : Scheme.{u}} (i : X ⟶ Y)
    [IsClosedImmersion i] (E K : DerivedCategory X.Modules) (m : ℤ)
    (h : IsPseudoCoherentFromAfterPushforward i (E ⊞ K) m) :
    IsPseudoCoherentFromAfterPushforward i E m ∧ IsPseudoCoherentFromAfterPushforward i K m := by
  rw [isPseudoCoherentFromAfterPushforward_iff] at h ⊢
  rw [isPseudoCoherentFromAfterPushforward_iff]
  exact RingedSpace.isPseudoCoherentFrom_of_biprod.{u + 1, u + 1, u} m
    (h.of_iso ((pushforward i).mapDerivedCategory.mapBiprod E K))

end Scheme.Modules

namespace Scheme.Hom

/-- **Stacks 09UN.** Let `f : X ⟶ S` be locally of finite type and let `E`, `K` be objects of the
derived category of `𝒪_X`-modules. If `E ⊕ K` is `m`-pseudo-coherent relative to `S`, then so are
`E` and `K`.

The covers witnessing the hypothesis are reused unchanged; at each of their closed immersions
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_of_biprod` splits the
local condition, the restriction of the biproduct having been identified with the biproduct of
the restrictions. -/
public theorem isPseudoCoherentFrom_of_biprod {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (E K : DerivedCategory X.Modules) (m : ℤ)
    (h : IsPseudoCoherentFrom f (E ⊞ K) m) :
    IsPseudoCoherentFrom f E m ∧ IsPseudoCoherentFrom f K m := by
  obtain ⟨ι, V, hV, hU⟩ := h
  constructor <;>
  · refine ⟨ι, V, hV, fun j ↦ ?_⟩
    obtain ⟨κ, U, hUcover, hUloc⟩ := hU j
    refine ⟨κ, U, hUcover, fun k ↦ ?_⟩
    obtain ⟨hle, n, g, hg, hcomm, hpc⟩ := hUloc k
    have := hg
    have hsplit := Scheme.Modules.isPseudoCoherentFromAfterPushforward_of_biprod g
      ((Scheme.Modules.restrictFunctor (U k).1.ι).mapDerivedCategory.obj E)
      ((Scheme.Modules.restrictFunctor (U k).1.ι).mapDerivedCategory.obj K) m
      (hpc.of_iso g
        ((Scheme.Modules.restrictFunctor (U k).1.ι).mapDerivedCategory.mapBiprod E K))
    first
      | exact ⟨hle, n, g, hg, hcomm, hsplit.1⟩
      | exact ⟨hle, n, g, hg, hcomm, hsplit.2⟩

/-- **Stacks 09UN, first summand.** If `E ⊕ K` is `m`-pseudo-coherent relative to `S` then so is
`E`. -/
@[stacks 09UN "first summand"]
public theorem IsPseudoCoherentFrom.of_biprod_left {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (E K : DerivedCategory X.Modules) (m : ℤ)
    (h : IsPseudoCoherentFrom f (E ⊞ K) m) : IsPseudoCoherentFrom f E m :=
  (isPseudoCoherentFrom_of_biprod f E K m h).1

/-- **Stacks 09UN, second summand.** If `E ⊕ K` is `m`-pseudo-coherent relative to `S` then so is
`K`. -/
@[stacks 09UN "second summand"]
public theorem IsPseudoCoherentFrom.of_biprod_right {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (E K : DerivedCategory X.Modules) (m : ℤ)
    (h : IsPseudoCoherentFrom f (E ⊞ K) m) : IsPseudoCoherentFrom f K m :=
  (isPseudoCoherentFrom_of_biprod f E K m h).2

end Scheme.Hom

end AlgebraicGeometry

end
