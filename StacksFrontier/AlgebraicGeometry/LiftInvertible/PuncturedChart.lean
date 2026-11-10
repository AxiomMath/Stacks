module

public import StacksFrontier.AlgebraicGeometry.LiftInvertible.AffineChartDimension
public import StacksFrontier.AlgebraicGeometry.LiftInvertible.PuncturedBasicOpen
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Punctured affine charts around a closed point of a one-dimensional scheme

Let `X` be a scheme with Noetherian underlying space and `topologicalKrullDim X ≤ 1`, let `T` be
a finite set of closed points of `X` and let `x ∈ T` be a point to which some other point
specializes. Then every open neighbourhood of `x` contains an open `V` with

* `x ∈ V`,
* `V ∩ T = {x}`, and
* `V \ {x}` an open subscheme which is **affine**.

This is the step that turns the dimension bound of
[Stacks, Tag 09NY](https://stacks.math.columbia.edu/tag/09NY) into the star-shaped trivializing
cover consumed by
`Stacks.LiftInvertible.exists_modulePullback_iso_of_starChartData_of_isNilpotent_ker`: the
charts of that cover are these `V`, the centre is the complement of `T`, and the overlap of a
chart with the centre is exactly `V \ {x}`, which has to be affine for a unit on it to lift.

## Main results

* `Stacks.LiftInvertible.exists_isAffineOpen_punctured_of_topologicalKrullDim_le_one`: the
  statement above, with `V \ {x}` produced as a second open together with the equation
  identifying its carrier.

## Implementation notes

Everything happens inside an affine open `U ∋ x` taken from `Scheme.isBasis_affineOpens` and
contained in the given neighbourhood, so that `V` and `V \ {x}` can both be produced as basic
opens `X.basicOpen u` and `X.basicOpen v` of sections over `U` — `IsAffineOpen.basicOpen` then
gives the affineness with no `Spec` round trip, and `Scheme.basicOpen_le` gives `V ≤ U` for
free.

The two elements `u` and `v` come from
`Stacks.LiftInvertible.exists_basicOpen_isolating_of_topologicalKrullDim_le_one`, which states
its hypotheses on `PrimeSpectrum Γ(X, U)`; they are transported from `X` by
`Stacks.LiftInvertible.noetherianSpace_primeSpectrum_of_isAffineOpen` and
`Stacks.LiftInvertible.topologicalKrullDim_primeSpectrum_le_of_isAffineOpen`.

The transport in the other direction — of the three conclusions, from the spectrum back to `X` —
is done pointwise through `IsAffineOpen.fromSpec`, whose base map is an open embedding with
image `U` (`IsAffineOpen.range_fromSpec`) carrying `hU.primeIdealOf` to the point it came from
(`IsAffineOpen.fromSpec_primeIdealOf`) and the basic opens of the spectrum to those of `X`
(`IsAffineOpen.fromSpec_preimage_basicOpen`). The hypothesis "some other point specializes to
`x`" travels along it by `Topology.IsInducing.specializes_iff`, which is why it is stated in
that form rather than as a condition on `irreducibleComponents`.

## References

* [Stacks Project, Tag 09NY](https://stacks.math.columbia.edu/tag/09NY)
* [Stacks Project, Tag 0055](https://stacks.math.columbia.edu/tag/0055)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Set TopologicalSpace Topology

universe u

namespace Stacks.LiftInvertible

/-- **An isolating affine chart with affine puncture.** Let `X` be a scheme with Noetherian
underlying space and dimension at most one, let `T` be a finite set of closed points, let
`x ∈ T` be a point to which some other point specializes, and let `W` be an open neighbourhood
of `x`. Then there are opens `V ≤ W` and `V'` with `x ∈ V`, `V ∩ T = {x}`,
`V' = V \ {x}` and `V'` affine.

Both `V` and `V'` are basic opens of sections over an affine open `U` with `x ∈ U ≤ W`, so the
affineness of `V'` is `IsAffineOpen.basicOpen`. The two sections are produced on
`PrimeSpectrum Γ(X, U)` by
`Stacks.LiftInvertible.exists_basicOpen_isolating_of_topologicalKrullDim_le_one`. -/
@[ega "IV 21.12.9" "special case"]
theorem exists_isAffineOpen_punctured_of_topologicalKrullDim_le_one {X : Scheme.{u}}
    [NoetherianSpace X] (hdim : topologicalKrullDim X ≤ 1)
    {T : Set X} (hTfin : T.Finite) (hTcl : ∀ p ∈ T, IsClosed ({p} : Set X))
    {x : X} (hxT : x ∈ T) (hxspec : ∃ z : X, z ≠ x ∧ x ∈ closure ({z} : Set X))
    (W : X.Opens) (hxW : x ∈ W) :
    ∃ V V' : X.Opens, x ∈ V ∧ V ≤ W ∧ (V : Set X) ∩ T = {x} ∧
      (V' : Set X) = (V : Set X) \ {x} ∧ IsAffineOpen V' := by
  classical
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hxW W.2
  replace hU : IsAffineOpen U := hU
  have hemb : IsOpenEmbedding hU.fromSpec.base := hU.fromSpec.isOpenEmbedding
  have heinj : Function.Injective hU.fromSpec.base := hemb.injective
  -- membership in a basic open of `X` is membership in the corresponding basic open of `Spec`
  have hbo : ∀ (a : Γ(X, U)) (p : PrimeSpectrum Γ(X, U)),
      hU.fromSpec.base p ∈ X.basicOpen a ↔ p ∈ PrimeSpectrum.basicOpen a := by
    intro a p
    change p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen a ↔ _
    rw [hU.fromSpec_preimage_basicOpen a]
    exact Iff.rfl
  -- the same, phrased at a point of `U` through `hU.primeIdealOf`
  have hboU : ∀ (a : Γ(X, U)) (y : X) (hy : y ∈ (U : Set X)),
      (y ∈ X.basicOpen a ↔ hU.primeIdealOf ⟨y, hy⟩ ∈ PrimeSpectrum.basicOpen a) := by
    intro a y hy
    rw [← hbo a (hU.primeIdealOf ⟨y, hy⟩), hU.fromSpec_primeIdealOf ⟨y, hy⟩]
  have hpinj : ∀ (y : X) (hy : y ∈ (U : Set X)) (z : X) (hz : z ∈ (U : Set X)),
      (hU.primeIdealOf ⟨y, hy⟩ = hU.primeIdealOf ⟨z, hz⟩ ↔ y = z) := by
    intro y hy z hz
    refine ⟨fun h => ?_, fun h => by subst h; rfl⟩
    have h' := congrArg hU.fromSpec.base h
    rwa [hU.fromSpec_primeIdealOf ⟨y, hy⟩, hU.fromSpec_primeIdealOf ⟨z, hz⟩] at h'
  have hTmem : ∀ (y : X) (hy : y ∈ (U : Set X)),
      (hU.primeIdealOf ⟨y, hy⟩ ∈ hU.fromSpec.base ⁻¹' (T \ {x}) ↔ y ∈ T \ {x}) := by
    intro y hy
    change hU.fromSpec.base (hU.primeIdealOf ⟨y, hy⟩) ∈ T \ {x} ↔ _
    rw [hU.fromSpec_primeIdealOf ⟨y, hy⟩]
  -- singletons of `Spec Γ(X, U)` above closed points are closed
  have hsing : ∀ p : PrimeSpectrum Γ(X, U), IsClosed ({hU.fromSpec.base p} : Set X) →
      IsClosed ({p} : Set (PrimeSpectrum Γ(X, U))) := by
    intro p hp
    have hpre : hU.fromSpec.base ⁻¹' {hU.fromSpec.base p} =
        ({p} : Set (PrimeSpectrum Γ(X, U))) := by
      ext q
      exact ⟨fun h => heinj h, fun h => by rw [show q = p from h]; exact mem_preimage.2 rfl⟩
    rw [← hpre]
    exact hp.preimage hemb.continuous
  have : NoetherianSpace (PrimeSpectrum Γ(X, U)) :=
    noetherianSpace_primeSpectrum_of_isAffineOpen ⟨U, hU⟩
  obtain ⟨u, v, humem, hudisj, hueq⟩ :=
    exists_basicOpen_isolating_of_topologicalKrullDim_le_one
      (R := Γ(X, U))
      (topologicalKrullDim_primeSpectrum_le_of_isAffineOpen ⟨U, hU⟩ hdim)
      (𝔪 := hU.primeIdealOf ⟨x, hxU⟩)
      (hsing _ (by rw [hU.fromSpec_primeIdealOf ⟨x, hxU⟩]; exact hTcl x hxT))
      (by
        obtain ⟨z, hzne, hz⟩ := hxspec
        have hzU : z ∈ (U : Set X) := by
          by_contra hzU
          exact (closure_minimal (singleton_subset_iff.2 hzU) U.2.isClosed_compl hz) hxU
        refine ⟨hU.primeIdealOf ⟨z, hzU⟩, fun h => hzne ((hpinj z hzU x hxU).1 h), ?_⟩
        refine specializes_iff_mem_closure.1 (hemb.isInducing.specializes_iff.1 ?_)
        rw [hU.fromSpec_primeIdealOf ⟨z, hzU⟩, hU.fromSpec_primeIdealOf ⟨x, hxU⟩]
        exact specializes_iff_mem_closure.2 hz)
      (T := hU.fromSpec.base ⁻¹' (T \ {x}))
      ((hTfin.subset sdiff_subset).preimage heinj.injOn)
      (fun p hp => hsing p (hTcl _ hp.1))
      (fun h => ((hTmem x hxU).1 h).2 rfl)
  -- `V \ {x}` is the basic open of `v`, checked pointwise on `U`
  have key : ∀ (y : X) (hyU : y ∈ (U : Set X)),
      y ∈ X.basicOpen v ↔ y ∈ X.basicOpen u ∧ y ≠ x := by
    intro y hyU
    have h := Set.ext_iff.1 hueq (hU.primeIdealOf ⟨y, hyU⟩)
    rw [mem_sdiff, mem_singleton_iff, hpinj y hyU x hxU] at h
    rw [hboU v y hyU, hboU u y hyU]
    exact h.symm
  have hxV : x ∈ X.basicOpen u := (hboU u x hxU).2 humem
  refine ⟨X.basicOpen u, X.basicOpen v, hxV, (X.basicOpen_le u).trans hUW, ?_, ?_,
    hU.basicOpen v⟩
  · refine Subset.antisymm (fun y hy => ?_) (singleton_subset_iff.2 ⟨hxV, hxT⟩)
    by_contra hyx
    have hyU : y ∈ (U : Set X) := X.basicOpen_le u hy.1
    exact (Set.eq_empty_iff_forall_notMem.1 hudisj (hU.primeIdealOf ⟨y, hyU⟩))
      ⟨(hboU u y hyU).1 hy.1, (hTmem y hyU).2 ⟨hy.2, hyx⟩⟩
  · ext y
    constructor
    · intro hy
      have hyU : y ∈ (U : Set X) := X.basicOpen_le v hy
      exact (key y hyU).1 hy
    · intro hy
      exact (key y (X.basicOpen_le u hy.1)).2 hy

end Stacks.LiftInvertible

end
