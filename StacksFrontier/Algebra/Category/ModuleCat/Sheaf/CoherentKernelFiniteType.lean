module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Coherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceKernels
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteFiniteTypeBridge

/-!
# The kernel of a map from a finite free sheaf of modules into a coherent one, on a site

Stacks 01BV defines a coherent sheaf of modules on a ringed space by two conditions: it is of
finite type, and for every open `U` and every map `φ` from a free sheaf of modules of finite rank
on the slice at `U` into the restriction, the kernel of `φ` is of finite type.  On a site the
predicate in use is `SheafOfModules.IsCoherentOnSite` (Stacks 03DL(8)), whose second condition is
stated *sectionwise*, on the presheaf of relations among a finite family of sections, rather than
on `CategoryTheory.Limits.kernel`.

This file derives the categorical form from the sectionwise one: a coherent sheaf of modules on a
site satisfies the second condition of Stacks 01BV, with Mathlib's `kernel` and Mathlib's
`SheafOfModules.IsFiniteType`.

## Main results

* `Stacks.SheafOfModules.isFiniteType_presheaf_kerObj_of_isCoherentOnSite`: for a coherent sheaf
  of modules `M` on a site, an object `U` and a map `φ` from a free sheaf of modules of finite
  rank on the slice at `U` into `M.over U`, the underlying presheaf of modules of the sectionwise
  kernel of `φ` is of finite type.
* `Stacks.SheafOfModules.isFiniteType_kernel_free_of_isCoherentOnSite`: **the same for Mathlib's
  categorical kernel and Mathlib's finite-type condition** — the second condition of Stacks 01BV
  on a site.
* `Stacks.SheafOfModules.isFiniteType_kernel_generatingSections_of_isCoherentOnSite`: the
  specialization to the map associated with a finite family of generating sections.

## Implementation notes

**No comparison between the relations presheaf and the kernel is needed.**  The sectionwise
condition enters only through Stacks 01BY (2) on a site,
`Stacks.SheafOfModules.isFiniteType_kerObj`: the kernel of a map from a sheaf of modules of
finite type into a coherent one is of finite type.  Applied on the slice site at `U`, its two
inputs are finite type of the free source — `Stacks.SheafOfModules`
`.isFiniteType_presheaf_of_generatingSections` at `SheafOfModules.free.generatingSections`, whose
index type is the rank — and coherence of the target, which is
`Stacks.SheafOfModules.isCoherentOnSite_over`.  In particular `φ` need not be an epimorphism.

Passing from the sectionwise kernel `SheafOfModules.kerObj` to `CategoryTheory.Limits.kernel`
uses `SheafOfModules.kerIsLimit`, and passing from the sectionwise finite-type condition to
Mathlib's uses `SheafOfModules.isFiniteType_of_presheaf_isFiniteType`, which is where the
sheafification hypotheses on the slices of the slice site come from: Mathlib's condition is
stated with sheafified free sheaves on the slices of the site it is read on, and that site is
here the slice at `U`.

## References

* [Stacks Project, Tag 01BV](https://stacks.math.columbia.edu/tag/01BV)
* [Stacks Project, Tag 01BW](https://stacks.math.columbia.edu/tag/01BW)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.SheafOfModules

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- If `M` is a coherent sheaf of modules on a site and `φ` maps a free sheaf of modules of
finite rank on the slice site at `U` into `M.over U`, then the underlying presheaf of modules of
the sectionwise kernel of `φ` is of finite type. -/
theorem isFiniteType_presheaf_kerObj_of_isCoherentOnSite
    (M : _root_.SheafOfModules.{w} R) (hM : _root_.SheafOfModules.IsCoherentOnSite M) (U : C)
    [HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    {I : Type w} [Finite I]
    (φ : _root_.SheafOfModules.free (R := R.over U) I ⟶ M.over U) :
    PresheafOfModules.IsFiniteType (J.over U) (_root_.SheafOfModules.kerObj φ).val :=
  have : HasSheafify (J.over U) AddCommGrpCat.{w} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  have : Finite (_root_.SheafOfModules.free.generatingSections (R := R.over U) I).I :=
    inferInstanceAs (Finite I)
  isFiniteType_kerObj φ
    (isFiniteType_presheaf_of_generatingSections
      (_root_.SheafOfModules.free.generatingSections (R := R.over U) I))
    (isCoherentOnSite_over M hM U)

/-- If `M` is a coherent sheaf of modules on a site and `φ` maps a free sheaf of modules of
finite rank on the slice site at `U` into `M.over U`, then the kernel of `φ` is of finite type in
Mathlib's sense. -/
theorem isFiniteType_kernel_free_of_isCoherentOnSite
    (M : _root_.SheafOfModules.{w} R) (hM : _root_.SheafOfModules.IsCoherentOnSite M) (U : C)
    [HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ V : Over U, HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{w}]
    [∀ V : Over U, ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
    {I : Type w} [Finite I]
    (φ : _root_.SheafOfModules.free (R := R.over U) I ⟶ M.over U) :
    (kernel φ).IsFiniteType :=
  _root_.SheafOfModules.isFiniteType_of_presheaf_isFiniteType (kernel φ)
    (isFiniteType_of_presheafIso
      ((_root_.SheafOfModules.forget (R.over U)).mapIso
        ((_root_.SheafOfModules.kerIsLimit φ).conePointUniqueUpToIso
          (limit.isLimit (parallelPair φ 0))))
      (isFiniteType_presheaf_kerObj_of_isCoherentOnSite M hM U φ))

/-- The kernel of the map associated with a finite family of generating sections of a coherent
sheaf of modules is of finite type. -/
theorem isFiniteType_kernel_generatingSections_of_isCoherentOnSite
    (M : _root_.SheafOfModules.{w} R) (hM : _root_.SheafOfModules.IsCoherentOnSite M) (U : C)
    [HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ V : Over U, HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{w}]
    [∀ V : Over U, ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (g : (M.over U).GeneratingSections) [Finite g.I] :
    (kernel g.π).IsFiniteType :=
  isFiniteType_kernel_free_of_isCoherentOnSite M hM U g.π

end Stacks.SheafOfModules

end
