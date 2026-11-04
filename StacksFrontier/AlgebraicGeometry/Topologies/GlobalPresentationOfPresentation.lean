module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Topologies.UliftForPresentationColimits

/-!
# A presentation of a sheaf of modules gives a global presentation

`SheafOfModules.HasGlobalPresentation`, part (6) of Stacks 03DE, says that a sheaf of modules is
a cokernel of a map between coproducts of copies of the structure sheaf, with all three
constructions expressed by universal properties so that no sheafification instance is needed.
Mathlib's `SheafOfModules.Presentation` says the same thing with the sheafified free modules
`SheafOfModules.free`.  The two are stated in different universes: a global presentation lives in
`SheafOfModules.{max u v r m} R`, reached through `SheafOfModules.uliftForPresentation`, whereas
`SheafOfModules.free` lands in `SheafOfModules.{r} R`.  This file crosses that gap.

## Main results

* `SheafOfModules.HasGlobalPresentation.of_presentation_of_preservesColimits`: a sheaf of
  modules admitting a `SheafOfModules.Presentation` has a global presentation, given that the
  universe lift preserves the colimits the presentation consists of.

## Implementation notes

The module universe here is arbitrary and the colimit preservation is taken as a hypothesis, so
that a caller may supply it in whatever form it has.  Two neighbouring statements dispose of it
in the two ways available.  `SheafOfModules.Presentation.hasGlobalPresentation` discharges it
below from `SheafOfModules.preservesColimitsOfSize_uliftForPresentationFunctor'`.
`SheafOfModules.HasGlobalPresentation.of_presentation` assumes instead that the module universe
already contains the site universes, where the lift is an isomorphism and nothing has to be
preserved; and `SheafOfModules.HasGlobalPresentation.of_presentation'` asks neither, proving
colimit preservation from `CategoryTheory.HasWeakSheafify` alone, so it is the most general of
the three and implies this one.

All the mathematics is in
`SheafOfModules.preservesColimitsOfShape_uliftForPresentationFunctor`, the statement that the
universe lift preserves colimits; it appears here as the hypothesis
`CategoryTheory.Limits.PreservesColimitsOfSize.{r, r}` on the lift, which also supplies the
`CategoryTheory.Limits.WalkingParallelPair` shape after
`CategoryTheory.Limits.preservesColimitsOfSize_shrink`.

Given that, `SheafOfModules.Presentation.isColimit` exhibits the module as a cokernel of a map
between free modules and `SheafOfModules.isColimitFreeCofan` exhibits each free module as a
coproduct of copies of `SheafOfModules.unit`; the lift carries both, by
`CategoryTheory.Limits.CokernelCofork.mapIsColimit` and
`CategoryTheory.Limits.Cofan.isColimitMapCoconeEquiv`.  What is left is bookkeeping: the index
types of a global presentation are required to lie in the presentation universe, so they are
raised by `ULift` and the two cofans are reindexed along `ULift.up`, which is a bijection.

## References

* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 01BD](https://stacks.math.columbia.edu/tag/01BD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t r v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}
  [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]

/-- Reindexing a colimit cofan of copies of a single object along the universe lift of its index
type: `ULift.up` is a bijection, so the raised family is again a colimit cofan. -/
private noncomputable def isColimitCofanULift {I : Type r} {D : Type*} [Category* D] {O T : D}
    {ι : I → (O ⟶ T)} (h : IsColimit (Cofan.mk T ι)) :
    IsColimit (Cofan.mk (f := fun _ : ULift.{t, r} I => O) T fun i => ι i.down) := by
  refine Cofan.IsColimit.mk _
    (fun s => Cofan.IsColimit.desc h fun i => s.inj (ULift.up i)) (fun s i => ?_)
    (fun s n hn => ?_)
  · exact Cofan.IsColimit.fac h (fun j => s.inj (ULift.up j)) i.down
  · refine Cofan.IsColimit.hom_ext h _ _ fun i => ?_
    exact (hn (ULift.up i)).trans (Cofan.IsColimit.fac h (fun j => s.inj (ULift.up j)) i).symm

/-- **A presentation gives a global presentation**, given colimit preservation.  The cokernel
diagram of free modules that `SheafOfModules.Presentation` provides is carried into the
presentation universe by the universe lift; the index types are raised by `ULift`.

The module universe is arbitrary and the colimit preservation of the lift is a hypothesis.
`SheafOfModules.HasGlobalPresentation.of_presentation` is the same conclusion when the module
universe already contains the site universes, where the lift is an isomorphism;
`SheafOfModules.HasGlobalPresentation.of_presentation'` is it with the hypothesis proved from
`CategoryTheory.HasWeakSheafify`. -/
public theorem HasGlobalPresentation.of_presentation_of_preservesColimits
    {M : SheafOfModules.{r} R}
    (hU : PreservesColimitsOfSize.{r, r}
      (uliftForPresentationFunctor.{u, v, r, r, max u v r} (R := R)))
    (P : M.Presentation) : M.HasGlobalPresentation := by
  let U : SheafOfModules.{r} R ⥤ SheafOfModules.{max u v r} R :=
    uliftForPresentationFunctor.{u, v, r, r, max u v r} (R := R)
  let : PreservesColimitsOfSize.{r, r} U := hU
  let : PreservesColimitsOfSize.{0, 0} U := preservesColimitsOfSize_shrink U
  set g : free P.generators.I ⟶ M := P.generators.π with hg
  set f : free P.relations.I ⟶ free P.generators.I :=
    (freeHomEquiv _).symm P.relations.s ≫ kernel.ι P.generators.π with hf
  have hfg : f ≫ g = 0 := by simp [hf, hg]
  have hcoker : IsColimit (CokernelCofork.ofπ (f := f) g hfg) := P.isColimit
  have hab : U.map f ≫ U.map g = 0 := by
    rw [← Functor.map_comp, hfg, Functor.map_zero]
  have hbcoker : IsColimit (CokernelCofork.ofπ (U.map g) hab) :=
    (CokernelCofork.ofπ (f := f) g hfg).mapIsColimit hcoker U
  have hfree (I : Type r) : IsColimit (Cofan.mk (f := fun _ : ULift.{max u v r, r} I => _)
      (U.obj (free I)) fun i => U.map (ιFree i.down)) :=
    isColimitCofanULift ((Cofan.isColimitMapCoconeEquiv U _ (Cofan.mk (free I) ιFree)).toFun
      (isColimitOfPreserves U (isColimitFreeCofan I)))
  exact ⟨ULift.{max u v r, r} P.generators.I, ULift.{max u v r, r} P.relations.I,
    U.obj (free P.generators.I), U.obj (free P.relations.I),
    (fun i => U.map (ιFree i.down)), (fun k => U.map (ιFree k.down)),
    ⟨hfree _⟩, ⟨hfree _⟩,
    U.map f, U.map g, hab, ⟨hbcoker⟩⟩

end SheafOfModules

end
