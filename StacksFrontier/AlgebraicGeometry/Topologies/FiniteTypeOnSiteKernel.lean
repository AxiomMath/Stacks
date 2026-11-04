module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFiniteKernel
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteBridge
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeOnSiteEpi
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeOnSiteFromGeneratingSections

/-!
# The kernel of a surjection onto a finitely presented module, read with the site predicates

Stacks 082T says that on a ringed site, if `θ : G ⟶ F` is a surjection of sheaves of modules with
`F` of finite presentation and `G` of finite type, then `Ker θ` is of finite type.  Equivalently,
in a short exact sequence `0 → F' → F → F'' → 0` with `F` of finite type and `F''` of finite
presentation, the subsheaf `F'` is of finite type.

Finite type and finite presentation are the clauses (5) and (7) of Stacks 03DL, and this tree
records each of them twice.  Mathlib's `SheafOfModules.IsFiniteType` and
`SheafOfModules.IsFinitePresentation` state them with sheafified free sheaves of modules on the
slices of the site; `SheafOfModules.IsFiniteTypeOnSite` and
`SheafOfModules.IsFinitePresentationOnSite` state them with coproducts and cokernels given by
their universal properties.  Stacks 082T in the first rendering is
`Stacks.SheafOfModules.SliceFinite.isFiniteType_kernel_of_epi`, which carries the tag.  This file
transfers it to the second rendering, which is the one in which the finiteness conditions of
closed subspaces of algebraic spaces and of the quotients of their structure sheaves are stated.

The transfer is in three steps.  Finite type descends by
`Stacks.SheafOfModules.isFiniteType_of_isFiniteTypeOnSite` and ascends by
`Stacks.SheafOfModules.isFiniteTypeOnSite_of_isFiniteType` below, neither of which costs anything
beyond the restriction of a finite family of generating sections along a morphism of the site.
Finite presentation descends, and that is where the work is: the two renderings are compared
either at the module universe `max u v`, by
`AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite`, or at an
arbitrary module universe under smallness of the global sections, by
`Stacks.SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite_of_small`.  Both forms
of the transfer are given, because the first is unsatisfiable on a big site and the second
carries a hypothesis the first does not.

## Main results

* `Stacks.SheafOfModules.isFiniteTypeOnSite_of_isFiniteType`: the ascent from Mathlib's
  finite-type condition to `SheafOfModules.IsFiniteTypeOnSite`, the converse of
  `Stacks.SheafOfModules.isFiniteType_of_isFiniteTypeOnSite`.
* `Stacks.SheafOfModules.isFiniteTypeOnSite_kernel_of_isFinitePresentationOnSite_of_small` and
  `Stacks.SheafOfModules.isFiniteTypeOnSite_X₁_of_shortExact_of_small`: Stacks 082T for
  `SheafOfModules.IsFiniteTypeOnSite` and `SheafOfModules.IsFinitePresentationOnSite`, at an
  arbitrary module universe, under smallness of the global sections.
* `Stacks.SheafOfModules.isFiniteTypeOnSite_kernel_of_isFinitePresentationOnSite` and
  `Stacks.SheafOfModules.isFiniteTypeOnSite_X₁_of_shortExact`: the same with the smallness
  hypothesis traded for the module universe being `max u v`.

## Implementation notes

No tag attribute is placed.  Stacks 082T is already carried, in full generality and with no
restriction on the module universe, by
`Stacks.SheafOfModules.SliceFinite.isFiniteType_kernel_of_epi`; what is proved here is the
transfer of that statement between two renderings of the finiteness conditions of Stacks 03DL,
and each of the two forms given carries a size hypothesis that the tagged statement does not.
This follows the convention of
`StacksFrontier/AlgebraicGeometry/Topologies/FinitePresentationOnSiteBridge.lean` and
`StacksFrontier/AlgebraicGeometry/Topologies/QuasicoherentOnSiteOfPresentation.lean`, which say the
same of their comparisons of renderings.

The hypotheses `CategoryTheory.GrothendieckTopology.HasSheafify` and
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective`, on the site and on each of its
slices, are hypotheses of the constructions used — they are what makes the category of sheaves of
modules abelian and makes the free sheaf of modules on a slice exist — and not extra finiteness
conditions.  The twice iterated slice versions are not carried: the tagged statement derives them
from the once sliced ones itself.

The smallness hypothesis of the first form holds on every site with a final object, by
`SheafOfModules.small_sections_of_isTerminal`, hence on the small étale site of an algebraic
space, where the module universe lies one below the universe of the objects of the site and the
second form does not apply.  Conversely the second form carries no size hypothesis at all.
Neither implies the other as stated.

No converse is proved.  The finite-type conclusion on the kernel cannot be strengthened to finite
presentation without a hypothesis on the structure sheaf, and the source makes no such claim.

## References

* [Stacks Project, Tag 082T](https://stacks.math.columbia.edu/tag/082T)
* [Stacks Project, Tag 01BP](https://stacks.math.columbia.edu/tag/01BP)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits SheafOfModules

namespace Stacks.SheafOfModules

universe u v w

/-! ### From Mathlib's finite-type condition to the categorical one -/

section Ascent

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{w}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **From Mathlib's finite-type condition to the categorical one.**  A sheaf of modules of
finite type in Mathlib's sense satisfies `SheafOfModules.IsFiniteTypeOnSite`.

Mathlib's condition carries generating sections only on the members of one family covering the
final object, while the categorical one asks for them on a covering of *every* object.  The
passage is the sieve of objects of that family: an arrow of it has a map into a member of the
family, and a finite family of generating sections restricts along any morphism of the site by
`Stacks.SheafOfModules.LocalCokernel.exists_finiteGeneratingSections_overMap`, with no products
on the site.

This is the converse of `Stacks.SheafOfModules.isFiniteType_of_isFiniteTypeOnSite`. -/
theorem isFiniteTypeOnSite_of_isFiniteType (M : SheafOfModules.{w} R) (h : M.IsFiniteType) :
    M.IsFiniteTypeOnSite := by
  obtain ⟨σ, hσ⟩ := h.exists_localGeneratorsData
  refine isFiniteTypeOnSite_of_locally_finite_generators M fun U => ?_
  refine ⟨⟨Sieve.ofObjects σ.X U, σ.coversTop U⟩, fun V g hg => ?_⟩
  obtain ⟨i, ⟨a⟩⟩ := (Sieve.mem_ofObjects_iff _ g).1 hg
  have := hσ.isFiniteType i
  exact LocalCokernel.exists_finiteGeneratingSections_overMap M a (σ.generators i)

end Ascent

/-! ### Stacks 082T for the site predicates, at an arbitrary module universe -/

section OnSiteSmall

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Sheafification of `AddCommGrpCat`-valued presheaves on a slice of the site, at the universe
`max u v w`, which lies above the site; this is the universe in which the statements phrased with
`SheafOfModules.uliftForPresentation` are read. -/
private theorem hasSheafify_over_lift (X : C) :
    HasSheafify (J.over X) AddCommGrpCat.{max u v w} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v w, v, max u v} (J.over X)

/-- Local bijectivity on a slice of the site at the universe `max u v w`. -/
private theorem wEqualsLocallyBijective_over_lift (X : C) :
    (J.over X).WEqualsLocallyBijective AddCommGrpCat.{max u v w} :=
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v w,
    max u v, v} (J.over X)

variable {R : Sheaf J RingCat.{w}}
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{w}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ (X : C) (N : SheafOfModules.{w} (R.over X)), Small.{w} N.sections]

/-- **Stacks 082T for `SheafOfModules.IsFiniteTypeOnSite` and
`SheafOfModules.IsFinitePresentationOnSite`, at an arbitrary module universe.**  On a ringed site
whose sheaves of modules have small global sections over every object, the kernel of a surjection
from a sheaf of modules of finite type onto a sheaf of modules of finite presentation is of finite
type, both conditions being read in the rendering of Stacks 03DL by universal properties.

Stacks 082T itself is `Stacks.SheafOfModules.SliceFinite.isFiniteType_kernel_of_epi`; what is
added is the transfer of the two finiteness conditions between the renderings.  The smallness
hypothesis is what
`Stacks.SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite_of_small` needs in order
to compare the two renderings of Stacks 03DL(7) at a module universe unrelated to the universes of
the site; it is satisfied on every site with a final object, by
`SheafOfModules.small_sections_of_isTerminal`, and in particular on the small étale site of an
algebraic space, where `SheafOfModules.IsFiniteTypeOnSite` is the finite-type condition in
use. -/
theorem isFiniteTypeOnSite_kernel_of_isFinitePresentationOnSite_of_small
    {F G : SheafOfModules.{w} R} (θ : G ⟶ F) [Epi θ]
    (hF : F.IsFinitePresentationOnSite) (hG : G.IsFiniteTypeOnSite) :
    (kernel θ).IsFiniteTypeOnSite := by
  have h1 : ∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{max u v w} := hasSheafify_over_lift
  have h1' : ∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{max u v w} :=
    fun X => (h1 X).1
  have h2 : ∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{max u v w} :=
    wEqualsLocallyBijective_over_lift
  have := hF
  have : F.IsFinitePresentation := isFinitePresentation_of_isFinitePresentationOnSite_of_small F
  have : G.IsFiniteType := isFiniteType_of_isFiniteTypeOnSite G hG
  exact isFiniteTypeOnSite_of_isFiniteType _ (SliceFinite.isFiniteType_kernel_of_epi θ)

/-- **Stacks 082T for a short exact sequence, at an arbitrary module universe.**  In a short exact
sequence `0 → X₁ → X₂ → X₃ → 0` of sheaves of modules on a ringed site with `X₂` of finite type
and `X₃` of finite presentation, the subsheaf `X₁` is of finite type.

Exactness identifies `X₁` with the kernel of `X₂ ⟶ X₃`, and being of finite type on the site is
invariant under isomorphism because an isomorphism is an epimorphism. -/
theorem isFiniteTypeOnSite_X₁_of_shortExact_of_small
    {S : ShortComplex (SheafOfModules.{w} R)} (hS : S.ShortExact)
    (h₂ : S.X₂.IsFiniteTypeOnSite) (h₃ : S.X₃.IsFinitePresentationOnSite) :
    S.X₁.IsFiniteTypeOnSite := by
  have h1 : ∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{max u v w} := hasSheafify_over_lift
  have h1' : ∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{max u v w} :=
    fun X => (h1 X).1
  have h2 : ∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{max u v w} :=
    wEqualsLocallyBijective_over_lift
  have hmono : Mono S.f := hS.mono_f
  have hepi : Epi S.g := hS.epi_g
  have hker : (kernel S.g).IsFiniteTypeOnSite :=
    isFiniteTypeOnSite_kernel_of_isFinitePresentationOnSite_of_small S.g h₃ h₂
  exact isFiniteTypeOnSite_of_epi
    (IsLimit.conePointUniqueUpToIso (kernelIsKernel S.g) hS.fIsKernel).hom hker

end OnSiteSmall

/-! ### Stacks 082T for the site predicates at the module universe of the site -/

section OnSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{max u v}}
  [HasSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{max u v}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- **Stacks 082T for `SheafOfModules.IsFiniteTypeOnSite` and
`SheafOfModules.IsFinitePresentationOnSite` at the module universe `max u v`.**  The kernel of a
surjection from a sheaf of modules of finite type onto a sheaf of modules of finite presentation
is of finite type, both conditions being read in the rendering of Stacks 03DL by universal
properties.

Stacks 082T itself is `Stacks.SheafOfModules.SliceFinite.isFiniteType_kernel_of_epi`; what is
added is the transfer of the two finiteness conditions between the renderings, here through
`AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite`, which takes
the module universe to be that of the site and asks nothing else.
`Stacks.SheafOfModules.isFiniteTypeOnSite_kernel_of_isFinitePresentationOnSite_of_small` is the
same statement at an arbitrary module universe, with smallness of the global sections in place of
that restriction. -/
theorem isFiniteTypeOnSite_kernel_of_isFinitePresentationOnSite
    {F G : SheafOfModules.{max u v} R} (θ : G ⟶ F) [Epi θ]
    (hF : F.IsFinitePresentationOnSite) (hG : G.IsFiniteTypeOnSite) :
    (kernel θ).IsFiniteTypeOnSite := by
  have := hF
  have : F.IsFinitePresentation :=
    AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite F
  have : G.IsFiniteType := isFiniteType_of_isFiniteTypeOnSite G hG
  exact isFiniteTypeOnSite_of_isFiniteType _ (SliceFinite.isFiniteType_kernel_of_epi θ)

/-- **Stacks 082T for a short exact sequence, at the module universe `max u v`.**  In a short
exact sequence `0 → X₁ → X₂ → X₃ → 0` of sheaves of modules on a ringed site with `X₂` of finite
type and `X₃` of finite presentation, the subsheaf `X₁` is of finite type. -/
theorem isFiniteTypeOnSite_X₁_of_shortExact {S : ShortComplex (SheafOfModules.{max u v} R)}
    (hS : S.ShortExact) (h₂ : S.X₂.IsFiniteTypeOnSite)
    (h₃ : S.X₃.IsFinitePresentationOnSite) : S.X₁.IsFiniteTypeOnSite := by
  have hmono : Mono S.f := hS.mono_f
  have hepi : Epi S.g := hS.epi_g
  have hker : (kernel S.g).IsFiniteTypeOnSite :=
    isFiniteTypeOnSite_kernel_of_isFinitePresentationOnSite S.g h₃ h₂
  exact isFiniteTypeOnSite_of_epi
    (IsLimit.conePointUniqueUpToIso (kernelIsKernel S.g) hS.fIsKernel).hom hker

end OnSite

end Stacks.SheafOfModules

end
