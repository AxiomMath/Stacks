module

public import StacksFrontier.Algebra.Homology.Resolution.NatHorseshoe
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerivedComparison.Interface

/-!
# The compatible injective resolutions of Stacks 01EN

`Stacks.Cohomology.CechComparison.CechDerivedComparison`, the comparison datum for Stacks Tag
01EN, has a field `resolutions` asserting that every
short exact sequence of presheaves of `O`-modules is covered by a short exact sequence of
`ℕ`-indexed injective resolutions whose image under degree-zero Čech cohomology, applied
degreewise, is again short exact. This file supplies it.

Both halves come from the `ℕ`-indexed injective horseshoe
`CategoryTheory.ShortComplex.ShortExact.exists_injectiveResolution_shortExact` (Stacks 013T) of
`StacksFrontier/Algebra/Homology/Resolution/NatHorseshoe.lean`: it produces the three resolutions,
the two commuting augmentation squares and the short exactness, and in addition a
`CategoryTheory.ShortComplex.Splitting` of the sequence in *every* degree. The degreewise
splitting is what makes the second half free: a split short exact sequence stays split under any
additive functor (`CategoryTheory.ShortComplex.Splitting.map`), hence stays short exact, and
short exactness of a sequence of homological complexes may be checked degreewise
(`HomologicalComplex.shortExact_of_degreewise_shortExact`). Degree-zero Čech cohomology is
additive by `Stacks.Cohomology.CechComparison.cechCohomologyFunctor_additive`, so no exactness
input beyond the splitting is used.

## Main results

* `nonempty_resolutionShortComplex`: the `resolutions` field of `CechDerivedComparison`.

## Implementation notes

The splitting the horseshoe returns is wrapped as `∃ _ : … .Splitting, True` rather than
returned as data, so it is extracted with `Exists.choose`; only its existence matters, since
`CategoryTheory.ShortComplex.Splitting.shortExact` is a proposition.

No transport is needed between
`((ShortComplex.mk f g w).map (G.mapHomologicalComplex (ComplexShape.up ℕ))).map
(HomologicalComplex.eval _ _ n)` and `(ShortComplex.mk (f.f n) (g.f n) _).map G`: a functor
applied degreewise to complexes has `((G.mapHomologicalComplex c).map φ).f n = G.map (φ.f n)` by
definition, and the `zero` field of a `ShortComplex` is a proposition, so the two short complexes
are definitionally equal.

This file does **not** carry the tag `01EN`. Of the ten fields of `CechDerivedComparison`, nine
are now available; the outstanding one is `derivedδ_eq`, the identification of the connecting
morphism coming from a distinguished triangle of `D⁺` with the one computed degreewise from a
short exact sequence of injective resolutions.

## References

* [Stacks Project, Tag 01EN](https://stacks.math.columbia.edu/tag/01EN)
* [Stacks Project, Tag 013T](https://stacks.math.columbia.edu/tag/013T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace

universe u

namespace Stacks.Cohomology.CechComparison

variable {X : Type u} [TopologicalSpace X]
  (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  (𝒰 : CechExactFunctor.CechOpenCover.{u, u} (TopCat.of X))

/-- **Every short exact sequence of presheaves of `O`-modules admits a compatible short exact
sequence of injective resolutions**, compatible in the strong sense that degree-zero Čech
cohomology of the covering `𝒰`, applied degreewise, keeps the sequence of resolving complexes
short exact. This is the `resolutions` field of
`Stacks.Cohomology.CechComparison.CechDerivedComparison`.

The resolutions, the commuting augmentation squares, the short exactness and the degreewise
splitting are all produced by the `ℕ`-indexed injective horseshoe of Stacks 013T; the splitting
is what survives the passage through an additive functor and so gives the last field. -/
theorem nonempty_resolutionShortComplex (S : ShortComplex (Modules.{u} O)) (hS : S.ShortExact) :
    Nonempty (ResolutionShortComplex.{u} O 𝒰 S) := by
  obtain ⟨J₁, J₂, J₃, f, g, w, hse, hcomm_f, hcomm_g, hsplit⟩ :=
    hS.exists_injectiveResolution_shortExact
  exact ⟨{ J₁ := J₁
           J₂ := J₂
           J₃ := J₃
           f := f
           g := g
           zero := w
           comm_f := hcomm_f
           comm_g := hcomm_g
           shortExact := hse
           mappedShortExact :=
             HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦
               (((hsplit n).choose).map (cechCohomologyZeroFunctor.{u} O 𝒰)).shortExact }⟩

end Stacks.Cohomology.CechComparison

end
