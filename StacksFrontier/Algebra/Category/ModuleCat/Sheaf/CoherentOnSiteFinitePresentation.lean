module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentKernelFiniteType

/-!
# A coherent sheaf of modules on a site is of finite presentation

Stacks 01BW(1) says that a coherent sheaf of modules on a ringed space is of finite
presentation.  This file proves the same implication on an arbitrary site, for the site-level
coherence predicate `SheafOfModules.IsCoherentOnSite` of Stacks 03DL(8) and Mathlib's
`SheafOfModules.IsFinitePresentation`.

## Main results

* `Stacks.SheafOfModules.shrink_isFinitePresentation`: shrinking the index type of a
  quasicoherent datum preserves finite presentation.
* `Stacks.SheafOfModules.isFinitePresentation_of_isCoherentOnSite`: **a coherent sheaf of
  modules on a site is of finite presentation.**

## Implementation notes

The two halves of the argument are `over_quasicoherentData_isFP_of_finiteGenerators_finiteKernel`
and `bind_isFinitePresentation`, the general-site forms of the two Stacks 01BW lemmas.  Coherence
enters twice: through the finite-type condition, which supplies a covering family with finitely
many generating sections of the restriction over each member, and through
`Stacks.SheafOfModules.isFiniteType_kernel_generatingSections_of_isCoherentOnSite`, which makes
the kernel of the associated map of those generating sections of finite type.  That is exactly
the hypothesis of `over_quasicoherentData_isFP_of_finiteGenerators_finiteKernel`, so each member
of the covering family carries a finitely presented quasicoherent datum, and
`SheafOfModules.QuasicoherentData.bind` glues them; it performs the slice-to-base transport
internally, so no comparison between a slice of a slice and a slice appears here.

The covering family produced by the finite-type condition is indexed in the universe of the
objects of the site, while `bind` indexes its covers in the universe of the sections of the
sheaf of rings; `UnivLE` and `Shrink` reindex it, and
`coversTop_comp_of_surjective` transports the covering property along the reindexing.

## References

* [Stacks Project, Tag 01BW](https://stacks.math.columbia.edu/tag/01BW)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits SheafOfModules

namespace Stacks.SheafOfModules

universe u v w t

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{w}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ (U : C) (V : Over U), HasSheafify ((J.over U).over V) AddCommGrpCat.{w}]
  [∀ (U : C) (V : Over U), ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

omit [∀ (U : C) (V : Over U), HasSheafify ((J.over U).over V) AddCommGrpCat.{w}]
  [∀ (U : C) (V : Over U), ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Shrinking the index type of a quasicoherent datum into the universe of the objects of the
site preserves finite presentation. -/
theorem shrink_isFinitePresentation {M : _root_.SheafOfModules.{w} R}
    (q : _root_.SheafOfModules.QuasicoherentData.{t} M) [q.IsFinitePresentation] :
    q.shrink.IsFinitePresentation where
  isFinite_presentation _i := inferInstanceAs ((q.presentation _).IsFinite)

/-- A coherent sheaf of modules on a site is of finite presentation. -/
theorem isFinitePresentation_of_isCoherentOnSite [UnivLE.{u, w}]
    (M : _root_.SheafOfModules.{w} R) (hM : _root_.SheafOfModules.IsCoherentOnSite M) :
    M.IsFinitePresentation := by
  have : M.IsFiniteType :=
    _root_.SheafOfModules.isFiniteType_of_presheaf_isFiniteType M hM.isFiniteType
  obtain ⟨σ, hσ⟩ := _root_.SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  let e := equivShrink σ.I
  let X : Shrink.{w} σ.I → C := σ.X ∘ e.symm
  have hX : J.CoversTop X := coversTop_comp_of_surjective σ.coversTop e.symm.surjective
  have hQ (k : Shrink.{w} σ.I) :
      ∃ q : _root_.SheafOfModules.QuasicoherentData.{max u v} (M.over (X k)),
        q.IsFinitePresentation := by
    have : Finite (σ.generators (e.symm k)).I := (hσ.isFiniteType _).finite
    exact over_quasicoherentData_isFP_of_finiteGenerators_finiteKernel M (X k)
      (σ.generators (e.symm k))
      (isFiniteType_kernel_generatingSections_of_isCoherentOnSite M hM (X k)
        (σ.generators (e.symm k)))
  choose D hD using hQ
  have : ∀ k, (D k).IsFinitePresentation := hD
  have := bind_isFinitePresentation M X hX D
  exact ⟨(_root_.SheafOfModules.QuasicoherentData.bind M X hX D).shrink,
    shrink_isFinitePresentation _⟩

end Stacks.SheafOfModules

end
