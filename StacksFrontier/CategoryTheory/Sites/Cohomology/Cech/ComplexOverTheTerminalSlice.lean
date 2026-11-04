module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexAlongASliceFunctor

/-!
# A family with fixed target, read inside the slice at that target

A family `{U_i → Y}` of morphisms of `D` with fixed target is the same data as a family in the
slice `Over Y` whose target is the terminal object `𝟙_Y` of that slice.  The two readings have
the same Čech complex, and this file says so.

## Main definitions

* `Stacks.CechSite.toTerminalSliceFamily`: a family with target `Y`, read as a family of the
  slice at `Y` with target the terminal object of that slice.

## Main results

* `Stacks.CechSite.isEquivalence_forget_of_isTerminal`: the projection `Over U ⥤ C` of the slice
  at a *terminal* object is an equivalence.
* `Stacks.CechSite.sliceImageFamily_toTerminalSliceFamily`: the slice-image of
  `Stacks.CechSite.toTerminalSliceFamily` along that projection is the original family, on the
  nose.
* `Stacks.CechSite.sliceCechComplexIsoCechComplexToTerminalSliceFamily`: **the two readings have
  the same Čech complex**, and
  `Stacks.CechSite.isZero_sliceCechCohomology_of_isZero_cechCohomology_toTerminalSliceFamily` is
  the transport of vanishing it gives.

## References

* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
-/

@[expose] public section

universe w v v' u u'

namespace Stacks.CechSite

open CategoryTheory CategoryTheory.Limits Opposite

/-- **The projection of the slice at a terminal object is an equivalence.** -/
public theorem isEquivalence_forget_of_isTerminal {C : Type u} [Category.{v} C] {U : C}
    (hU : IsTerminal U) : (Over.forget U).IsEquivalence := by
  have : (Over.forget U).Full := ⟨fun {_ _} g ↦ ⟨Over.homMk g (hU.hom_ext _ _), rfl⟩⟩
  have : (Over.forget U).EssSurj := ⟨fun Z ↦ ⟨Over.mk (hU.from Z), ⟨Iso.refl _⟩⟩⟩
  exact Functor.IsEquivalence.mk

variable {D : Type u} [Category.{v} D] {Y : D} (G : PreZeroHypercover.{w} Y)

/-- A family of morphisms with target `Y`, read as a family of the slice at `Y` whose target is
the terminal object `𝟙_Y` of that slice.  The selected object attached to a member is the member
itself, read as an object over `Y`. -/
public def toTerminalSliceFamily : PreZeroHypercover.{w} (Over.mk (𝟙 Y)) where
  I₀ := G.I₀
  X i := Over.mk (G.f i)
  f i := Over.homMk (G.f i) (Category.comp_id _)

/-- The underlying morphisms of the slice reading are the morphisms of the original family. -/
public theorem toTerminalSliceFamily_f_left (i : G.I₀) :
    ((toTerminalSliceFamily G).f i).left = G.f i :=
  rfl

/-- The total spaces of the slice reading are the members of the original family. -/
public theorem toTerminalSliceFamily_X_left (i : G.I₀) :
    ((toTerminalSliceFamily G).X i).left = G.X i :=
  rfl

/-- The slice-image of the slice reading, along the projection of the slice at the terminal
object, is the original family — on the nose. -/
public theorem sliceImageFamily_toTerminalSliceFamily :
    sliceImageFamily (toTerminalSliceFamily G) (Over.forget (Over.mk (𝟙 Y))) = G :=
  rfl

section Complex

variable [hG : ∀ (n : ℕ) (i : Fin (n + 1) → G.I₀),
    HasProduct (fun a ↦ Over.mk (G.f (i a)))]
  [hGs : ∀ (n : ℕ) (i : Fin (n + 1) → (toTerminalSliceFamily G).I₀),
    HasProduct (fun a ↦ Over.mk ((toTerminalSliceFamily G).f (i a)))]

/-- The iterated fibre products of the slice-image family of the slice reading of `G` exist: they
are those of `G`. -/
public instance hasProduct_sliceImageFamily_toTerminalSliceFamily (n : ℕ)
    (i : Fin (n + 1) → (sliceImageFamily (toTerminalSliceFamily G)
      (Over.forget (Over.mk (𝟙 Y)))).I₀) :
    HasProduct (fun a ↦ Over.mk ((sliceImageFamily (toTerminalSliceFamily G)
      (Over.forget (Over.mk (𝟙 Y)))).f (i a))) :=
  hG n i

/-- The projection of the slice at the terminal object preserves the iterated fibre products of
the slice reading of a family: it is an equivalence. -/
public theorem isIso_cechProductMapOfSliceFunctor_forget (n : ℕ)
    (i : Fin (n + 1) → (toTerminalSliceFamily G).I₀) :
    IsIso (cechProductMapOfSliceFunctor (toTerminalSliceFamily G)
      (Over.forget (Over.mk (𝟙 Y))) n i) := by
  have : (Over.forget (Over.mk (𝟙 Y))).IsEquivalence :=
    isEquivalence_forget_of_isTerminal Over.mkIdTerminal
  exact isIso_cechProductMapOfSliceFunctor (toTerminalSliceFamily G)
    (Over.forget (Over.mk (𝟙 Y))) n i

variable {A : Type u'} [Category.{v'} A] [Preadditive A] [HasProducts.{w} A]

/-- **A family with fixed target and its slice reading have the same Čech complex.** -/
public noncomputable def sliceCechComplexIsoCechComplexToTerminalSliceFamily
    (P : (Over Y)ᵒᵖ ⥤ A) :
    sliceCechComplex G P ≅ cechComplex (toTerminalSliceFamily G) P :=
  sliceCechComplexIsoOfSliceFunctor (toTerminalSliceFamily G)
    (Over.forget (Over.mk (𝟙 Y))) P (isIso_cechProductMapOfSliceFunctor_forget G)

end Complex

section Cohomology

variable [hG : ∀ (n : ℕ) (i : Fin (n + 1) → G.I₀),
    HasProduct (fun a ↦ Over.mk (G.f (i a)))]
  [hGs : ∀ (n : ℕ) (i : Fin (n + 1) → (toTerminalSliceFamily G).I₀),
    HasProduct (fun a ↦ Over.mk ((toTerminalSliceFamily G).f (i a)))]
  {A : Type u'} [Category.{v'} A] [Abelian A] [HasProducts.{w} A]

/-- **Vanishing of the Čech cohomology of the slice reading of a family transfers to the family
itself.** -/
public theorem isZero_sliceCechCohomology_of_isZero_cechCohomology_toTerminalSliceFamily
    (P : (Over Y)ᵒᵖ ⥤ A) (p : ℕ)
    (h : IsZero (cechCohomology (toTerminalSliceFamily G) P p)) :
    IsZero (sliceCechCohomology G P p) :=
  h.of_iso ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) p).mapIso
    (sliceCechComplexIsoCechComplexToTerminalSliceFamily G P))

end Cohomology

end Stacks.CechSite

end
