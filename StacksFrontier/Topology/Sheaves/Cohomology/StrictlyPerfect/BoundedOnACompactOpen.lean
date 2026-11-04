module

public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.LocallyStrictlyPerfectComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.IntervalDescent
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSliceConservativity
import StacksCore.Tactic.StacksAttribute

/-!
# A locally bounded complex is bounded on every compact open

Let `(X, 𝒪_X)` be a ringed space and `ℱ^•` a complex of `𝒪_X`-modules which is *locally
bounded*: every point has an open neighbourhood outside finitely many degrees of which the
restriction of `ℱ^•` vanishes (`Stacks.SheafOfModules.OnSpace.IsLocallyBounded`). On a
*quasi-compact* open `W` the finitely many `Finset`s supplied by a finite subcover of `W` can be
united, so `ℱ^•` is bounded on `W` outright
(`Stacks.SheafOfModules.OnSpace.IsBoundedOn`).

## Main results

* `Stacks.SheafOfModules.OnSpace.isBoundedOn_of_isLocallyBounded_of_isCompact`: a locally
  bounded complex is bounded on every compact open.

## Implementation notes

The union of the finitely many bounds is a bound on `W` because vanishing of a sheaf of modules
is local on the site: the opens `U x ⊓ W`, for `x` running through the finite subcover, generate
a covering sieve of `W`, and the restriction of `ℱ^i` to each of them vanishes once `i` lies
outside every one of the finitely many `Finset`s. That is
`Stacks.SheafOfModules.isZero_of_coversTop` read on the slice site over `W`, exactly as in
`AlgebraicGeometry.SmallEtale.isZero_over_opensObj_imageOpen_of_isZero_over`.

This is the step by which [Stacks, Tag 0FML] passes from its hypothesis that `ℱ^•` be locally
bounded to the bounded complexes its dévissage needs: the reduction to an affine — more
generally quasi-compact — base replaces the local hypothesis by a global bound there.

## References

* [Stacks Project, Tag 0FML](https://stacks.math.columbia.edu/tag/0FML)
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace

universe u

namespace Stacks.SheafOfModules.OnSpace

/-- **A locally bounded complex of `𝒪_X`-modules is bounded on every compact open.** If every
point of `X` has a neighbourhood outside finitely many degrees of which `ℱ^•` restricts to
zero, and `W` is an open whose underlying set is compact, then there is a single finite set of
degrees outside which `ℱ^•|_W` vanishes.

Finitely many of the neighbourhoods cover `W`, and the union of their `Finset`s is the bound:
for `i` outside that union the restriction of `ℱ^i` to each `U x ⊓ W` vanishes, and those opens
generate a covering sieve of `W`, so `ℱ^i|_W` vanishes because vanishing of a sheaf of modules
is local on the site. -/
theorem isBoundedOn_of_isLocallyBounded_of_isCompact (Z : AlgebraicGeometry.RingedSpace.{u, u})
    (F : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ)
    (hF : IsLocallyBounded Z F)
    (W : Opens Z.carrier) (hW : IsCompact (W : Set Z.carrier)) :
    IsBoundedOn Z F W := by
  classical
  choose U hxU hUb using hF
  choose s hs using hUb
  obtain ⟨t, ht⟩ := hW.elim_finite_subcover (fun x : Z.carrier => (U x : Set Z.carrier))
    (fun x => (U x).isOpen) fun x hx => Set.mem_iUnion.2 ⟨x, hxU x⟩
  refine ⟨t.biUnion s, fun i hi => ?_⟩
  -- The opens `U x ⊓ W`, for `x` in the finite subcover, generate a covering sieve of `W`.
  set V : {x : Z.carrier // x ∈ t} → Opens Z.carrier := fun x => U x.1 ⊓ W
  have hle : ∀ x : {x : Z.carrier // x ∈ t}, V x ≤ W := fun _ => inf_le_right
  have hsieve : Sieve.ofArrows V (fun x => homOfLE (hle x)) ∈
      Opens.grothendieckTopology Z.carrier W := by
    rw [Opens.mem_grothendieckTopology]
    intro y hy
    obtain ⟨x, hxt, hxy⟩ := Set.mem_iUnion₂.1 (ht hy)
    exact ⟨V ⟨x, hxt⟩, homOfLE (hle ⟨x, hxt⟩), Sieve.ofArrows_mk V _ ⟨x, hxt⟩, hxy, hy⟩
  refine Stacks.SheafOfModules.isZero_of_coversTop
    (Stacks.SheafOfModules.coversTop_over_of_ofArrows_mem
      (Opens.grothendieckTopology Z.carrier) W V (fun x => homOfLE (hle x)) hsieve)
    _ fun x => ?_
  refine Stacks.SheafOfModules.isZero_over_over_of_isZero_over (F.X i) _ _ ?_
  exact isZero_over_of_le Z (inf_le_left (b := W))
    (hs x.1 i fun hmem => hi (Finset.mem_biUnion.2 ⟨x.1, x.2, hmem⟩))

end Stacks.SheafOfModules.OnSpace

end
