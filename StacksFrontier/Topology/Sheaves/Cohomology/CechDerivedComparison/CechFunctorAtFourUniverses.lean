module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerived.DeltaFunctorOfPresheaves
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerivedComparison.Interface

/-!
# Čech cohomology of a covering of a ringed space, at four independent universes

Let `X` be a space, `O` a sheaf of rings on `X`, and `𝒰` an indexed open covering of an open
`U ⊆ X`. The Čech cohomology functors `Ȟᵖ(𝒰, -)` on presheaves of `O`-modules, with values in
modules over the ring `O(U)` of sections on the covered open, are built here with the space
universe `u`, the ring universe `r`, the module universe `v` and the covering index universe `w`
all independent, the common module universe being `max u r v w`.

This is the shape in which the Čech-to-cohomology spectral sequence of [Stacks, Tag 01ES] needs
them, and neither of the two versions already in the library has it: the one in
`Stacks.Cohomology.CechComparison` is universe-monomorphic, because the
`EnoughInjectives` input of [Stacks, Tag 01EN] identifies all four universes, and
`Stacks.Cohomology.CechDerived.cechComplexFunctor` takes a presheaf of rings rather than a
sheaf.

## The universe situation

Nothing here needs injectives, and that is the point. `EnoughInjectives` on presheaves of
modules comes from `PresheafOfModules.instIsGrothendieckAbelian`, which is stated for a small
site in `Type u`, a presheaf of rings in `RingCat.{u}` and modules in `Type u`; at the module
universe `max u r v w` over `RingCat.{r}` it does not synthesize. The Čech complex functor of
[Stacks, Tag 01EJ] and its exactness, by contrast, are already stated at four independent
universes, and cohomology of a complex needs only an abelian category. So the functors, their
additivity, and the whole δ-functor of [Stacks, Tag 01EK] are available at `max u r v w`, while
the derived-functor comparison of [Stacks, Tag 01EN] is not; the comparison is the only thing
the one-universe restriction buys.

## Main definitions

* `cechCohomologyFunctor`: `Ȟᵖ(𝒰, -)` on presheaves of `O`-modules, at the four universes.
* `cechDeltaFunctor`: the Čech cohomology δ-functor of [Stacks, Tag 01EK] at the same universes.

## Main results

* `cechCohomologyFunctor_additive`: the Čech cohomology functors are additive.
* `cechDeltaFunctor_functor`: the degree-`p` component of the δ-functor is
  `cechCohomologyFunctor`.
* `cechCohomologyFunctor_eq_comparison`: with all four universes equal this is, on the nose, the
  functor of `Stacks.Cohomology.CechComparison`.

## Implementation notes

The module universe handed to `Stacks.Cohomology.CechExactFunctor.presheafCechComplexFunctor` is
`max u r v w` rather than `v`: that functor lands in modules over `O(U)` at universe
`max v w`, the `w` coming from the indexed products over `(p+1)`-tuples of covering indices, so
feeding it `max u r v w` gives back `max u r v w` and the four universes are genuinely free.

Nothing in this file carries the tag `01EN`: the tag's first assertion is the ten-field
comparison `Stacks.Cohomology.CechComparison.CechDerivedComparison`, which these functors do not
state, and which is in any case unavailable at these universes.

## References

* [Stacks Project, Tag 01EJ](https://stacks.math.columbia.edu/tag/01EJ)
* [Stacks Project, Tag 01EK](https://stacks.math.columbia.edu/tag/01EK)
* [Stacks Project, Tag 01EN](https://stacks.math.columbia.edu/tag/01EN)
* [Stacks Project, Tag 01ES](https://stacks.math.columbia.edu/tag/01ES)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.Cohomology.CechExactFunctor (presheafCechComplexFunctor)

universe u r v w

namespace Stacks.Cohomology.CechSpectral

variable {X : Type u} [TopologicalSpace X]
  (O : Sheaf (Opens.grothendieckTopology X) RingCat.{r})
  (𝒰 : CechExactFunctor.CechOpenCover.{u, w} (TopCat.of X))

/-- **The Čech complex functor of a covering of a ringed space**, at four independent universes:
the functor of [Stacks, Tag 01EJ] applied to the structure presheaf of `O`, the covered open
`𝒰.U` and the members of `𝒰`. Its module universe is `max u r v w`. -/
abbrev cechComplexFunctor :
    PresheafOfModules.{max u r v w} O.obj ⥤
      CochainComplex (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U))) ℕ :=
  presheafCechComplexFunctor.{u, r, max u r v w, w} O.obj 𝒰.U 𝒰.obj 𝒰.le

/-- The Čech complex functor is additive, being exact by [Stacks, Tag 01EJ]. -/
instance cechComplexFunctor_additive :
    (cechComplexFunctor.{u, r, v, w} O 𝒰).Additive :=
  exactFunctor_le_additiveFunctor _ _ _
    (CechExactFunctor.presheafCechComplexFunctor_exact.{u, r, max u r v w, w}
      O.obj 𝒰.U 𝒰.obj 𝒰.le)

/-- **Čech cohomology of the covering `𝒰` in degree `p`**, with values in modules over the ring
of sections on the covered open: the degree-`p` cohomology of the Čech complex functor of
[Stacks, Tag 01EJ]. The space universe `u`, the ring universe `r`, the module universe `v` and
the covering index universe `w` are independent; the module universe of the result is their
maximum. -/
def cechCohomologyFunctor (p : ℕ) :
    PresheafOfModules.{max u r v w} O.obj ⥤ ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U)) :=
  cechComplexFunctor.{u, r, v, w} O 𝒰 ⋙
    HomologicalComplex.homologyFunctor _ (up ℕ) p

/-- Čech cohomology in each degree is additive. -/
instance cechCohomologyFunctor_additive (p : ℕ) :
    (cechCohomologyFunctor.{u, r, v, w} O 𝒰 p).Additive := by
  dsimp only [cechCohomologyFunctor]
  infer_instance

/-- **The Čech cohomology δ-functor of [Stacks, Tag 01EK]** for the covering `𝒰` of a ringed
space, at four independent universes, including its natural connecting morphisms and the long
exact Čech cohomology sequence they fit into. -/
abbrev cechDeltaFunctor :
    DeltaFunctor (PresheafOfModules.{max u r v w} O.obj)
      (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U))) :=
  (CechCohomologyDelta.presheafCechCohomologyDeltaFunctor.{u, r, max u r v w, w}
    O.obj 𝒰.U 𝒰.obj 𝒰.le).1

/-- The degree-`p` component of the Čech δ-functor of [Stacks, Tag 01EK] is degree-`p` Čech
cohomology of the covering. -/
theorem cechDeltaFunctor_functor (p : ℕ) :
    (cechDeltaFunctor.{u, r, v, w} O 𝒰).functor p = cechCohomologyFunctor.{u, r, v, w} O 𝒰 p :=
  (CechCohomologyDelta.presheafCechCohomologyDeltaFunctor.{u, r, max u r v w, w}
    O.obj 𝒰.U 𝒰.obj 𝒰.le).2 p

/-- With all four universes equal, the Čech cohomology functor of this file is, on the nose, the
one of `Stacks.Cohomology.CechComparison`, over which the derived-functor
comparison of [Stacks, Tag 01EN] is stated. -/
theorem cechCohomologyFunctor_eq_comparison
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (𝒰 : CechExactFunctor.CechOpenCover.{u, u} (TopCat.of X)) (p : ℕ) :
    cechCohomologyFunctor.{u, u, u, u} O 𝒰 p = CechComparison.cechCohomologyFunctor O 𝒰 p :=
  rfl

end Stacks.Cohomology.CechSpectral

end
