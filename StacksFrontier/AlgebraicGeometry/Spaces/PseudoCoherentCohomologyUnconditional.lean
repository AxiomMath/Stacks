module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherentCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCoherentExactSequences
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleKernelQuasicoherent
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 08JL: a pseudo-coherent complex on an algebraic space has quasi-coherent cohomology

Let `S` be a scheme, let `F` be an algebraic space over `S` and let `E` be an object of
`D(𝒪_F)`.  If `E` is `n`-pseudo-coherent then `Hⁱ(E)` is a quasi-coherent `𝒪_F`-module for every
`i > n`, and if `E` is pseudo-coherent then `E` lies in `D_QCoh(𝒪_F)`.  Both statements are
proved here with no hypothesis beyond the ones Stacks 08JL itself makes.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_homology_of_isPseudoCoherentFrom_unconditional`:
  the first assertion of Stacks 08JL.
* `AlgebraicGeometry.Space.derivedCategoryB_of_isPseudoCoherent_unconditional`: the second
  assertion of Stacks 08JL.
* `Stacks.SheafOfModules.isClosedUnderKernels_of_reindex` and
  `Stacks.SheafOfModules.isClosedUnderCokernels_of_reindex`: closure of quasi-coherence under
  kernels and under cokernels descends along an equivalence of ringed sites.
* `AlgebraicGeometry.Space.isClosedUnderKernels_over` and
  `AlgebraicGeometry.Space.isClosedUnderCokernels_over`: the kernel and cokernel clauses of
  Stacks 03M1 on every slice of the small étale site of an algebraic space.

## What this file adds

The mathematics of Stacks 08JL is already in
`StacksFrontier/AlgebraicGeometry/Spaces/PseudoCoherentCohomology.lean`, whose two theorems are
stated under two instance hypotheses the source does not have — closure of quasi-coherence under
kernels and under cokernels on every *slice* of the small étale site of `F` — and which are
therefore deliberately left untagged there.  This file discharges those two hypotheses and
restates the two assertions with the hypotheses gone, which is where the `stacks 08JL`
attribute belongs.

The two closure properties are known for the small étale site of an algebraic space with no
hypothesis at all, by `AlgebraicGeometry.Space.isClosedUnderKernels` and
`AlgebraicGeometry.Space.isClosedUnderCokernels_quasicoherentSheaves`; what was missing is the
passage from the site of a space to a slice of it.  That passage is Stacks 04M0: the slice of
the small étale site of `F` at a chart `V` is the small étale site of the algebraic space
represented by `V`, and the two structure sheaves agree on the nose
(`AlgebraicGeometry.Space.reindexRing_chartLocalizationEquivalence`).  So the slice carries the
two closure properties as soon as they transport along an equivalence of ringed sites, and they
do: reindexing is an equivalence of the two module categories
(`Stacks.SheafOfModules.reindexEquivalence`), hence carries a limiting kernel fork to one and a
colimiting cokernel cofork to one, and it preserves and reflects quasi-coherence
(`Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff`, Stacks 03DM for clause (6) of
Stacks 03DL).

## Implementation notes

The module universe is the universe `u` of the structure rings throughout, as it is in
Stacks 08FT and in `StacksFrontier/AlgebraicGeometry/Spaces/PseudoCoherentCohomology.lean`: the
strictly perfect local models are built from the structure sheaf, so the sections of the models
and of the structure sheaf live in one universe.  The kernel clause on the chart is available
one universe higher, at the universe of the objects of the site, and is brought down by
`SheafOfModules.isClosedUnderKernels_isQuasicoherentOnSite_of_ulift`; the cokernel clause is
already at `u`.

Two instance arguments of the generic transport lemmas are supplied by hand at the chart rather
than found by synthesis, because the comparison functor of Stacks 04M0 is registered under the
name `AlgebraicGeometry.Space.SmallEtale.chartLocalization` while the lemmas ask for it as the
functor of `AlgebraicGeometry.Space.SmallEtale.chartLocalizationEquivalence`, which instance
search does not unfold.

The cokernel transport names the colimit-preservation of the reindexing functor explicitly, as
the adjunction of `Stacks.SheafOfModules.reindexEquivalence`.  Left to synthesis the same goal
reaches an instance whose module universe is the join of the universes of the site, the rings
and a free one, and matching that against the module universe `u` of the statement is a
universe constraint with no solution.

## References

* [Stacks Project, Tag 08JL](https://stacks.math.columbia.edu/tag/08JL)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 071X](https://stacks.math.columbia.edu/tag/071X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.SheafOfModules

universe u v w

variable {C : Type u} [Category.{v} C] {C' : Type u} [Category.{v} C']
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}

variable (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
  (R : Sheaf J RingCat.{w}) [e.inverse.IsDenseSubsite J J']

/-- **Closure of quasi-coherence under kernels descends along an equivalence of ringed sites.**
Reindexing along `e` is an equivalence of the two categories of sheaves of modules matching the
two structure sheaves, so it carries a limiting kernel fork to a limiting kernel fork, and it
both preserves and reflects quasi-coherence; hence the kernel clause for the reindexed structure
sheaf gives the kernel clause for `R`. -/
theorem isClosedUnderKernels_of_reindex
    (h : (SheafOfModules.isQuasicoherentOnSite.{u, v, w, w}
      (reindexRing J' e R)).IsClosedUnderKernels) :
    (SheafOfModules.isQuasicoherentOnSite.{u, v, w, w} R).IsClosedUnderKernels where
  kernels_le := by
    have := h
    have : (SheafOfModules.pushforward.{w}
        (𝟙 (reindexRing J' e R))).PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
    have : (SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).IsEquivalence :=
      (reindexEquivalence.{w, w, u, v, u, v} e R).isEquivalence_functor
    have hq := isQuasicoherentOnSite_reindex_iff (J' := J') e R
    rintro _ ⟨f, k, hk, hM, hN⟩
    refine (hq k.pt).1 ?_
    exact (SheafOfModules.isQuasicoherentOnSite.{u, v, w, w}
      (reindexRing J' e R)).prop_of_isLimit_kernelFork
      (k.mapIsLimit hk (SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))))
      ((hq _).2 hM) ((hq _).2 hN)

/-- **Closure of quasi-coherence under cokernels descends along an equivalence of ringed
sites.**  This is the cokernel counterpart of
`Stacks.SheafOfModules.isClosedUnderKernels_of_reindex`: reindexing is the functor of an
equivalence and so is a left adjoint, which is what carries a colimiting cokernel cofork to a
colimiting cokernel cofork. -/
theorem isClosedUnderCokernels_of_reindex
    (h : (SheafOfModules.isQuasicoherentOnSite.{u, v, w, w}
      (reindexRing J' e R)).IsClosedUnderCokernels) :
    (SheafOfModules.isQuasicoherentOnSite.{u, v, w, w} R).IsClosedUnderCokernels where
  cokernels_le := by
    have := h
    have : (SheafOfModules.pushforward.{w}
        (𝟙 (reindexRing J' e R))).PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
    have : PreservesColimitsOfSize.{0, 0}
        (SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))) :=
      (reindexEquivalence.{w, w, u, v, u, v} e R).toAdjunction.leftAdjoint_preservesColimits
    have hq := isQuasicoherentOnSite_reindex_iff (J' := J') e R
    rintro _ ⟨f, k, hk, hM, hN⟩
    refine (hq k.pt).1 ?_
    exact h.cokernels_le _ (MorphismProperty.cokernels.of_isColimit _ _
      (k.mapIsColimit hk (SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))))
      ⟨(hq _).2 hM, (hq _).2 hN⟩)

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

universe u

section Slices

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- **The kernel clause of Stacks 03M1 on a slice of the small étale site of an algebraic
space**, with no hypothesis: on the localization of the small étale site of `X` at a chart `U`,
the kernel of a morphism of quasi-coherent modules is quasi-coherent.

The slice at `U` is the small étale site of the algebraic space represented by `U`, with the
same structure sheaf, by Stacks 04M0; there the clause is
`AlgebraicGeometry.Space.isClosedUnderKernels`, one universe above the universe of the schemes,
and it descends to the universe of the schemes because limits of sheaves of modules are
computed on sections. -/
theorem isClosedUnderKernels_over (U : SmallEtale B S hS X.1) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((structureRingSheaf B S hS X).over U)).IsClosedUnderKernels := by
  have hchart : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (chartStructureRingSheaf B S hS X U)).IsClosedUnderKernels :=
    SheafOfModules.isClosedUnderKernels_isQuasicoherentOnSite_of_ulift.{u + 1, u, u, u}
      (isClosedUnderKernels.{u, u} B S hS (chartSpace B S hS X U).1
        (chartSpace B S hS X U).2)
  exact @Stacks.SheafOfModules.isClosedUnderKernels_of_reindex _ _ _ _ _ _
    (SmallEtale.chartLocalizationEquivalence B S hS X.1 U)
    (isContinuous_chartLocalization_chartSpace B S hS X U)
    (@Functor.IsDenseSubsite.instIsContinuous _ _ _ _ _ _ _
      (isDenseSubsite_chartLocalizationEquivalence_inverse B S hS X U))
    ((structureRingSheaf B S hS X).over U)
    (isDenseSubsite_chartLocalizationEquivalence_inverse B S hS X U) hchart

/-- **The cokernel clause of Stacks 03M1 on a slice of the small étale site of an algebraic
space**, with no hypothesis: on the localization of the small étale site of `X` at a chart `U`,
the cokernel of a morphism of quasi-coherent modules is quasi-coherent.

The slice at `U` is the small étale site of the algebraic space represented by `U`, with the
same structure sheaf, by Stacks 04M0; there the clause is
`AlgebraicGeometry.Space.isClosedUnderCokernels_quasicoherentSheaves`, already at the universe
of the schemes. -/
theorem isClosedUnderCokernels_over (U : SmallEtale B S hS X.1) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((structureRingSheaf B S hS X).over U)).IsClosedUnderCokernels := by
  have hchart : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (chartStructureRingSheaf B S hS X U)).IsClosedUnderCokernels :=
    isClosedUnderCokernels_quasicoherentSheaves B S hS (chartSpace B S hS X U).1
      (chartSpace B S hS X U).2
  exact @Stacks.SheafOfModules.isClosedUnderCokernels_of_reindex _ _ _ _ _ _
    (SmallEtale.chartLocalizationEquivalence B S hS X.1 U)
    (isContinuous_chartLocalization_chartSpace B S hS X U)
    (@Functor.IsDenseSubsite.instIsContinuous _ _ _ _ _ _ _
      (isDenseSubsite_chartLocalizationEquivalence_inverse B S hS X U))
    ((structureRingSheaf B S hS X).over U)
    (isDenseSubsite_chartLocalizationEquivalence_inverse B S hS X U) hchart

end Slices

section PseudoCoherent

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The `𝒪_F`-modules with sections in the universe of the schemes form an abelian category.

The content is `SheafOfModules.instAbelian`, Mathlib's abelian structure on the sheaves of
modules over a sheaf of rings, whose two hypotheses hold here by the instances of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulesAbelian.lean`.  It is named, and given a raised
priority, because `Stacks.Cohomology.SiteModules.moduleSheavesAbelian` answers the same goal
with the module universe left as the join of the universes of the site, the rings and a free one;
that join is never the universe `u` of the schemes, and a search reaching it first ends in a
universe constraint with no solution rather than in a failure it can recover from. -/
noncomputable instance (priority := high) modules_abelian :
    Abelian (Modules.{u, u} B S hS F hF) :=
  SheafOfModules.instAbelian
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))

/-- Every slice of the small étale ringed site of an algebraic space composes the sheaf
condition with the forgetful functor from rings to abelian groups, which is what makes the
underlying abelian groups of a sheaf of modules on a slice a sheaf.

This restates the available instance for the projections of
`AlgebraicGeometry.Space.smallEtaleRingedSite`, which instance search does not unfold. -/
instance smallEtaleRingedSite_hasSheafCompose_over :
    ∀ V : (smallEtaleRingedSite B S hS F hF).C,
      ((smallEtaleRingedSite B S hS F hF).J.over V).HasSheafCompose
        (forget₂ RingCat.{u} AddCommGrpCat.{u}) := by
  change ∀ V : SmallEtale B S hS F,
    ((SmallEtale.topology B S hS F).over V).HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u})
  infer_instance

/-- **Stacks 08JL, first assertion.**  Let `S` be a scheme, let `F` be an algebraic space over
`S` and let `E` be an object of `D(𝒪_F)`.  If `E` is `n`-pseudo-coherent, then `Hⁱ(E)` is a
quasi-coherent `𝒪_F`-module for every `i > n`.

The second assertion of the tag is
`AlgebraicGeometry.Space.derivedCategoryB_of_isPseudoCoherent_unconditional`.

This is `AlgebraicGeometry.Space.isQuasicoherentOnSite_homology_of_isPseudoCoherentFrom` with
its two closure hypotheses discharged by
`AlgebraicGeometry.Space.isClosedUnderKernels_over` and
`AlgebraicGeometry.Space.isClosedUnderCokernels_over`. -/
@[stacks 08JL "cohomology above the approximation degree"]
theorem isQuasicoherentOnSite_homology_of_isPseudoCoherentFrom_unconditional
    (E : DerivedCategory (Modules.{u, u} B S hS F hF)) (n i : ℤ)
    (hE : (smallEtaleRingedSite B S hS F hF).IsPseudoCoherentFrom E n) (hi : n < i) :
    ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS F hF) i).obj E).IsQuasicoherentOnSite := by
  have hker : ∀ V : (smallEtaleRingedSite B S hS F hF).C,
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O)).over V)).IsClosedUnderKernels :=
    fun V => isClosedUnderKernels_over B S hS ⟨F, hF⟩ V
  have hcok : ∀ V : (smallEtaleRingedSite B S hS F hF).C,
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O)).over V)).IsClosedUnderCokernels :=
    fun V => isClosedUnderCokernels_over B S hS ⟨F, hF⟩ V
  exact isQuasicoherentOnSite_homology_of_isPseudoCoherentFrom B S hS F hF E n i hE hi

/-- **Stacks 08JL, second assertion.**  Let `S` be a scheme, let `F` be an algebraic space over
`S` and let `E` be an object of `D(𝒪_F)`.  If `E` is pseudo-coherent, then `E` lies in
`D_QCoh(𝒪_F)`, that is, every cohomology sheaf of `E` is quasi-coherent.

The conclusion is the object property whose full subcategory is
`AlgebraicGeometry.Space.QuasicoherentDerivedCategory`, the `D_QCoh(𝒪_F)` of Stacks 071X.  The
first assertion of the tag is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_homology_of_isPseudoCoherentFrom_unconditional`.

Apply the first assertion in degree `i` using a strictly perfect approximation from degree
`i - 1`. -/
@[stacks 08JL "pseudo-coherent objects lie in the quasi-coherent derived category"]
theorem derivedCategoryB_of_isPseudoCoherent_unconditional
    (E : DerivedCategory (Modules.{u, u} B S hS F hF))
    (hE : (smallEtaleRingedSite B S hS F hF).IsPseudoCoherent E) :
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))) E := by
  obtain ⟨K, hK, ⟨e⟩⟩ := hE
  intro i
  exact isQuasicoherentOnSite_homology_of_isPseudoCoherentFrom_unconditional B S hS F hF E
    (i - 1) i ⟨K, hK (i - 1), ⟨e⟩⟩ (by omega)

end PseudoCoherent

end AlgebraicGeometry.Space

end
