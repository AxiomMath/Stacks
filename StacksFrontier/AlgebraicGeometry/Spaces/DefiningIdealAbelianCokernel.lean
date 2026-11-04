module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraDegreeZero

/-!
# The defining ideal sequence of a closed subspace, in sheaves of abelian groups

Let `Z` be a closed subspace of an algebraic space `X` over a scheme `S`, with inclusion
`i : Z ⟶ X` and defining ideal sheaf `𝓘 ⊆ 𝒪_X`.  The sequence
```
  0 ⟶ 𝓘 ⟶ 𝒪_X ⟶ i_*𝒪_Z ⟶ 0
```
is short exact as a sequence of `𝒪_X`-modules, by
`AlgebraicGeometry.Space.definingIdealShortComplex_shortExact`.  This file reads the same sequence
in sheaves of **abelian groups** on the small étale site of `X`, where it is again short exact, so
that the structure projection `𝒪_X ⟶ i_*𝒪_Z` is a cokernel of the inclusion of the ideal *in
sheaves of abelian groups* and not only in modules.

## Why the abelian-group reading is wanted

A derivation is not a morphism of modules, so a statement that descends a `B`-derivation of `𝒪_X`
annihilating `𝓘` to a `B`-derivation of `𝒪_Z` cannot appeal to the cokernel in modules: the
universal property has to be applied to a map which is only additive.  The reading below is that
universal property, in the category the additive map lives in.

The *What is not proved* section of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceDifferentials.lean` records this clause as
unavailable, on the ground that the bridge `PreservesFiniteColimits (SheafOfModules.toSheaf _)` is
carried as a hypothesis elsewhere in this tree and not proved.  **That general bridge is not
needed for this one sequence**, and nothing below uses it.  Two preservation facts are used, and
both are available:

* `CategoryTheory.SheafOfModules.toSheaf` preserves finite *limits*, which Mathlib proves.  The
  module-level sequence exhibits `𝓘 ⟶ 𝒪_X` as a *kernel* of the structure projection, on the nose
  — `AlgebraicGeometry.Space.ker_structureProjection` — so `CategoryTheory.Limits.`
  `KernelFork.mapIsLimit` carries that kernel fork to a kernel fork, which gives both the
  monomorphism at the left and the exactness at the middle.
* It preserves *epimorphisms*, which is
  `Stacks.SheafOfModules.EpiMono.epi_toSheaf_map` of
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/EpiLocallySurjective.lean`, proved there from the
  identification of the epimorphisms of sheaves of modules with the locally surjective morphisms.
  That is the clause at the right, over `AlgebraicGeometry.Space.epi_structureProjection`.

A functor that is only left exact and preserves epimorphisms does not preserve cokernels in
general.  What makes the argument go through is that this sequence is short *exact*: its
right-hand map is a cokernel of its left-hand one as soon as the mapped sequence is exact at the
middle and epimorphic at the right, by `CategoryTheory.ShortComplex.Exact.gIsCokernel`.

## Main results

* `AlgebraicGeometry.Space.definingIdealAbelianShortComplex_shortExact`:
  `0 ⟶ 𝓘 ⟶ 𝒪_X ⟶ i_*𝒪_Z ⟶ 0` is short exact in sheaves of abelian groups on the small étale
  site of `X`.
* `AlgebraicGeometry.Space.isColimitAbelianCokernelCofork`: the structure projection exhibits
  `i_*𝒪_Z` as a cokernel of `𝓘 ⟶ 𝒪_X` in sheaves of abelian groups.
* `AlgebraicGeometry.Space.abelianDesc`,
  `AlgebraicGeometry.Space.structureProjection_comp_abelianDesc` and
  `AlgebraicGeometry.Space.abelianDesc_unique`: the universal property in the form a consumer
  uses it — an additive morphism out of `𝒪_X` annihilated by the inclusion of the ideal factors
  through the structure projection, uniquely.

## Implementation notes

**The short complex is written out rather than obtained as the image of the module-level one.**
`CategoryTheory.ShortComplex.map` takes `[F.PreservesZeroMorphisms]` as an instance argument, and
instance search does not find that class for
`CategoryTheory.SheafOfModules.toSheaf (structureRingSheaf B S hS X)` at this site, although
`CategoryTheory.Functor.preservesZeroMorphisms_of_additive` *elaborates* at that type: both
categories have more than one route to their `CategoryTheory.Limits.HasZeroMorphisms` structure
here, and supplying the instance by `letI`, by `attribute [local instance]`, or by declaring it
outright does not repair the search inside `ShortComplex.map`.  So the three fields are given
directly, the vanishing of the composite being the module-level vanishing carried across by that
same term, applied explicitly.  Inside proofs, where `haveI` is reliable, the instance is simply
assumed.

**Universe metavariables.**  `CategoryTheory.Functor.`
`preservesFiniteLimits_iff_forall_exact_map_and_mono` would give exactness and the monomorphism in
one step, but applying it leaves the universe of the source category undetermined and the
elaboration gets stuck on `max (u + 1) ?u =?= u`.  The kernel-fork route above has every universe
fixed by an explicit argument and does not run into this.

## No tag is registered

Stacks 03MB supplies the two clauses this rests on — the defining ideal sheaf is the kernel of the
structure map, and the structure map is locally surjective — and they are registered where they
are proved; Stacks 09RP in degree zero is registered on
`AlgebraicGeometry.Space.conormalAlgebraDegreeZeroIso`.  Re-reading one sequence in a larger
category is a proof step rather than a clause of a tag, as for
`AlgebraicGeometry.Space.exact_modulePullback_schemeChart_iff` of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePullbackSchemeChartExactness.lean`, so nothing is
registered here.

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB), the defining ideal sheaf
  of a closed subspace as the kernel of the structure map, and its local surjectivity.
* [Stacks Project, Tag 09RP](https://stacks.math.columbia.edu/tag/09RP), whose degree-zero case is
  the module-level form of this sequence.
* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH), epimorphisms of sheaves
  and local surjectivity.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1)

/-- The sequence `𝓘 ⟶ 𝒪_X ⟶ i_*𝒪_Z` of
`AlgebraicGeometry.Space.definingIdealShortComplex`, read in sheaves of abelian groups on the
small étale site of `X`.  The implementation notes say why it is written out instead of being
obtained as the image of the module-level complex. -/
noncomputable def definingIdealAbelianShortComplex :
    ShortComplex (Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u}) :=
  ShortComplex.mk
    ((SheafOfModules.toSheaf (structureRingSheaf B S hS X)).map
      (definingIdealSheaf B S hS X Z).ι)
    ((SheafOfModules.toSheaf (structureRingSheaf B S hS X)).map
      (structureProjection B S hS X Z))
    (((SheafOfModules.toSheaf (structureRingSheaf B S hS X)).map_comp _ _).symm.trans
      ((congrArg (SheafOfModules.toSheaf (structureRingSheaf B S hS X)).map
          (SheafOfModules.Submodule.ker_ι_comp (structureProjection B S hS X Z))).trans
        ((Functor.preservesZeroMorphisms_of_additive
          (SheafOfModules.toSheaf (structureRingSheaf B S hS X))).map_zero _ _)))

/-- **`0 ⟶ 𝓘 ⟶ 𝒪_X ⟶ i_*𝒪_Z ⟶ 0` is short exact in sheaves of abelian groups.**

The inclusion of the defining ideal sheaf is a kernel of the structure projection in
`𝒪_X`-modules, by `AlgebraicGeometry.Space.ker_structureProjection`; the forgetful functor to
sheaves of abelian groups preserves finite limits, so it carries that kernel fork to a kernel
fork, which is the monomorphism at the left and the exactness at the middle at once.  The
epimorphism at the right is `AlgebraicGeometry.Space.epi_structureProjection` carried across by
`Stacks.SheafOfModules.EpiMono.epi_toSheaf_map`. -/
theorem definingIdealAbelianShortComplex_shortExact :
    (definingIdealAbelianShortComplex B S hS X Z).ShortExact := by
  have : (SheafOfModules.toSheaf (structureRingSheaf B S hS X)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  have hker := KernelFork.mapIsLimit _
    (SheafOfModules.Submodule.isLimitKernelFork (structureProjection B S hS X Z))
    (SheafOfModules.toSheaf (structureRingSheaf B S hS X))
  have := epi_structureProjection B S hS X Z
  exact
    { exact := ShortComplex.exact_of_f_is_kernel _ hker
      mono_f := mono_of_isLimit_fork hker
      epi_g := Stacks.SheafOfModules.EpiMono.epi_toSheaf_map _ }

/-- **The structure projection `𝒪_X ⟶ i_*𝒪_Z` is a cokernel of the inclusion of the defining
ideal sheaf, in sheaves of abelian groups.**

`AlgebraicGeometry.Space.isColimitCokernelCofork` is the same statement in `𝒪_X`-modules; the
point of the reading here is that the morphisms the universal property quantifies over are merely
additive. -/
noncomputable def isColimitAbelianCokernelCofork :
    IsColimit (CokernelCofork.ofπ (definingIdealAbelianShortComplex B S hS X Z).g
      (definingIdealAbelianShortComplex B S hS X Z).zero) :=
  haveI := (definingIdealAbelianShortComplex_shortExact B S hS X Z).epi_g
  (definingIdealAbelianShortComplex_shortExact B S hS X Z).exact.gIsCokernel

section Desc

variable {X Z}
variable (W : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u})
    (φ : (definingIdealAbelianShortComplex B S hS X Z).X₂ ⟶ W)
    (hφ : (definingIdealAbelianShortComplex B S hS X Z).f ≫ φ = 0)

/-- **The factorization through the structure projection.**  An additive morphism `φ` out of
`𝒪_X` which the inclusion of the defining ideal sheaf annihilates factors through
`𝒪_X ⟶ i_*𝒪_Z`.  This is `AlgebraicGeometry.Space.isColimitAbelianCokernelCofork` applied to
`φ`; `AlgebraicGeometry.Space.structureProjection_comp_abelianDesc` is the factorization and
`AlgebraicGeometry.Space.abelianDesc_unique` its uniqueness. -/
noncomputable def abelianDesc : (definingIdealAbelianShortComplex B S hS X Z).X₃ ⟶ W :=
  (isColimitAbelianCokernelCofork B S hS X Z).desc (CokernelCofork.ofπ φ hφ)

/-- `AlgebraicGeometry.Space.abelianDesc` does factor the given morphism. -/
@[simp]
theorem structureProjection_comp_abelianDesc :
    (definingIdealAbelianShortComplex B S hS X Z).g ≫ abelianDesc B S hS W φ hφ = φ :=
  (isColimitAbelianCokernelCofork B S hS X Z).fac (CokernelCofork.ofπ φ hφ)
    WalkingParallelPair.one

/-- The factorization is the only one: the structure projection is an epimorphism of sheaves of
abelian groups. -/
theorem abelianDesc_unique (ψ : (definingIdealAbelianShortComplex B S hS X Z).X₃ ⟶ W)
    (hψ : (definingIdealAbelianShortComplex B S hS X Z).g ≫ ψ = φ) :
    ψ = abelianDesc B S hS W φ hφ := by
  exact Cofork.IsColimit.hom_ext (isColimitAbelianCokernelCofork B S hS X Z)
    (hψ.trans (structureProjection_comp_abelianDesc B S hS W φ hφ).symm)

end Desc

end AlgebraicGeometry.Space

end
