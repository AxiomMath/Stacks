module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.GlobalGenerators
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPullbackStability
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRingLevelZeroLocusOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapZeroLocusLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperModuleSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportClosedFiniteType
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeOnSiteKernel
public import StacksCore.Tactic.StacksAttribute

/-!
# The three clauses of Stacks 083J with nothing carried

In the situation of Stacks 083F — a morphism `f : X ⟶ Y` of algebraic spaces and a map
`u : ℱ ⟶ 𝒢` of quasi-coherent `𝒪_X`-modules — clause (2) of Stacks 083J asserts that the
vanishing locus `F_zero` is limit preserving when `ℱ` is of finite type with scheme-theoretic
support quasi-compact over `B`, clause (1) asserts the same of the surjectivity locus `F_surj`
under the same hypotheses on `𝒢`, and clause (3) asserts the same of the isomorphism locus
`F_iso` when `ℱ` is of finite type, `𝒢` of finite presentation and both supports are
quasi-compact over `B`.

Clauses (1) and (2) were already reduced in this development to a single hypothesis, and that
hypothesis is now a theorem; clause (3) is the source's own deduction from the other two.  This
file is the wiring, and after it no clause carries anything.  The pieces:

* the theorem `limitPreserving_zeroFunctor_of_hasQuasiCompactSupportOverTarget` of this
  namespace is clause (2) carrying `hchart`, the chart case at the affine stages;
* `AlgebraicGeometry.Space.ModuleMapSituation.hasAffineStageChartZeroDescent_of_ringLevelZeroLocus`
  reduces `hchart` to the limit-free ring-level reading of the vanishing locus of the chart
  situation, supplying the limit content — Stacks 01YW for the global sections of a limit of
  affine schemes, and Algebra, Lemma 05LI part (1) along the base-changed chart system;
* `AlgebraicGeometry.Space.ModuleMapSituation.hasAffineStageChartRingLevelZeroLocus` *proves*
  that ring-level reading, for every situation and every affine stage;
* `AlgebraicGeometry.Space.ModuleMapSituation.limitPreserving_surjFunctor_iff_cokernelSituation`
  is clause (1) as an equivalence with clause (2) for the cokernel situation, whose source
  module is `𝒢`;
* `AlgebraicGeometry.Space.ModuleMapSituation.limitPreserving_isoFunctor_iff_kernelSituation` is
  clause (3) for a *surjective* `u` as an equivalence with clause (2) for the kernel situation —
  Stacks 0CVM on `ker u ⟶ ℱ ⟶ 𝒢 ⟶ 0` — and clause (1) supplies a stage at which `u` is
  surjective, to which the situation is base changed by
  `AlgebraicGeometry.Space.ModuleMapSituation.baseChangeTestScheme`;
* `Stacks.SheafOfModules.isFiniteTypeOnSite_kernel_of_isFinitePresentationOnSite_of_small` is
  Stacks 082T, the finite-type input clause (3) needs on that kernel, and it applies on the small
  étale site of an algebraic space; `isFiniteTypeOnSite_kernelSituation_F` below is the
  application.

## Main results

* `ModuleMapSituation.limitPreserving_zeroFunctor_of_isQuasiCompact_schemeTheoreticSupport`,
  `ModuleMapSituation.limitPreserving_surjFunctor_of_isQuasiCompact_schemeTheoreticSupport` and
  `ModuleMapSituation.limitPreserving_isoFunctor_of_isQuasiCompact_schemeTheoreticSupport`
  are **clauses (2), (1) and (3) of Stacks 083J** at the source's hypotheses verbatim: the
  composite of the inclusion of the scheme-theoretic support (Stacks 07U1) with `f` is a
  quasi-compact morphism.
* `ModuleMapSituation.hasQuasiCompactSupportOverTarget_of_isQuasiCompact_schemeTheoreticSupport`
  derives from that hypothesis the compactness at the affine stages which the proofs spend.
* `AlgebraicGeometry.Space.ModuleMapSituation.limitPreserving_zeroFunctor`,
  `AlgebraicGeometry.Space.ModuleMapSituation.limitPreserving_surjFunctor` and
  `AlgebraicGeometry.Space.ModuleMapSituation.limitPreserving_isoFunctor` are the three clauses
  with the support hypothesis in that spent form.
* `AlgebraicGeometry.Space.ModuleMapSituation.limitPreserving_zeroFunctor_of_isQuasiCompact`,
  `AlgebraicGeometry.Space.ModuleMapSituation.limitPreserving_surjFunctor_of_isQuasiCompact` and
  `AlgebraicGeometry.Space.ModuleMapSituation.limitPreserving_isoFunctor_of_isQuasiCompact` are
  the three clauses for a quasi-compact `f`, where the support hypotheses are discharged outright
  by Stacks 03KG and the only remaining hypotheses are the finiteness ones on the modules.

## Implementation notes

**What the support hypothesis is.**  The predicate `HasQuasiCompactSupportOverTarget` of this
namespace is the source's hypothesis — quasi-compactness of the scheme-theoretic support over
`B` — read at the affine test schemes, which is where the source's proof spends it.  The
implication from the source's sentence is
`hasQuasiCompactSupportOverTarget_of_isQuasiCompact_schemeTheoreticSupport`: the fibre product
`Z ×_X (X ×_B T)` is the base change of `Z ⟶ B` to `T` (Stacks 03HF), the support of `ℱ` is
the image of `|Z|` (Stacks 07U0 part (4)), and points of a fibre product lift (Stacks 03H4).
The registered clauses take the source's sentence itself as their hypothesis.  The two
`_of_isQuasiCompact` corollaries avoid the question entirely: for a quasi-compact `f` the
condition is a theorem.

**The index universe is the universe of the schemes, and that is forced.**
`StacksFrontier/AlgebraicGeometry/SmallnessNecessary/Basic.lean` exhibits a directed inverse system
of nonempty affine schemes indexed one universe up whose limit is the empty scheme; over it the
identity of `𝒪` on an affine chart vanishes at the limit and at no stage, so both clauses are
*false* for index universes exceeding the universe of the schemes.  That is why the chart case is
available only at `.{u, u, u}` and why these statements are at
`AlgebraicGeometry.LimitPreserving.{u, u, u, u}`.

**Why a separate module.**  Clause (2) and the clause (1) equivalence live in
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleMapZeroLocusLimitPreserving.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleMapLociLimitPreserving.lean`, both of which are
*imported* by
`StacksFrontier/AlgebraicGeometry/Spaces/ChartRingLevelZeroLocusOverAffine.lean`, where the chart
case is proved.  So the binders cannot be deleted where the clauses are stated — that would be a
cycle — and the carry-free statements are made here instead.  The conditional statements are left
exactly as they are; their notes point here.

**Where clause (3) does not follow the source.**  The source offers two proofs of clause (3): to
"proceed in exactly the same manner" as clause (2), against Algebra, Lemma 05LI part (3), or to
deduce it from clauses (1) and (2) through the kernel at a stage.  The second is what is done
here.  The balanced-category reduction
`AlgebraicGeometry.Space.ModuleMapSituation.limitPreserving_isoFunctor_of_surj_of_inj` is *not*
used: its `hinj`, limit preservation of `F_inj`, is asserted by no clause of Stacks 083J, and by
`AlgebraicGeometry.Space.ModuleMapSituation.injFunctor_eq_isoFunctor_of_epi` it coincides with
its own conclusion as soon as `u` is an epimorphism — which is the case the source's proof of
clause (3) reduces to.

**Stacks 082T is available on the small étale site.**  It is
`Stacks.SheafOfModules.SliceFinite.isFiniteType_kernel_of_epi` for Mathlib's rendering of
Stacks 03DL(5) and 03DL(7), and
`Stacks.SheafOfModules.isFiniteTypeOnSite_kernel_of_isFinitePresentationOnSite_of_small` for the
rendering by universal properties used for `𝒪_X`-modules.  The latter needs sheafification of
abelian presheaves on the site and on each of its slices, local bijectivity of the weak
equivalences there, and smallness of the global sections over each object; the first two are the
instances `AlgebraicGeometry.Space.smallEtaleRingedSite_hasSheafify_over` and
`AlgebraicGeometry.Space.smallEtaleRingedSite_wEqualsLocallyBijective_over`, and the third is
`SheafOfModules.small_sections_of_isTerminal` at `CategoryTheory.Over.mkIdTerminal`.
`isFiniteTypeOnSite_kernelSituation_F` below is that application.

## References

* [Stacks Project, Tag 083J](https://stacks.math.columbia.edu/tag/083J)
* [Stacks Project, Tag 083F](https://stacks.math.columbia.edu/tag/083F)
* [Stacks Project, Tag 049J](https://stacks.math.columbia.edu/tag/049J)
* [Stacks Project, Tag 05LI](https://stacks.math.columbia.edu/tag/05LI)
* [Stacks Project, Tag 01YW](https://stacks.math.columbia.edu/tag/01YW)
* [Stacks Project, Tag 03KG](https://stacks.math.columbia.edu/tag/03KG)
* [Stacks Project, Tag 0CVM](https://stacks.math.columbia.edu/tag/0CVM)
* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
* [Stacks Project, Tag 082T](https://stacks.math.columbia.edu/tag/082T)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

namespace ModuleMapSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Pullbacks of presheaves on the big fppf site over `S`, supplied directly: instance search
for them now times out. -/
local instance (priority := high) hasLimit_cospan_presheaf_ModuleMapLociLimitPreservingUnconditional
    {Z₁ Z₂ Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Z₁ ⟶ Z) (f : Z₂ ⟶ Z) :
    HasLimit (cospan g f) :=
  @HasLimitsOfShape.has_limit _ _ _ _ functorCategoryHasLimitsOfShape _

/-! ### Clause (2) -/

/-- **Stacks 083J, clause (2).**  In the situation of Stacks 083F, if `ℱ` is of finite type and
the scheme-theoretic support of `ℱ` is quasi-compact over `B`, then the vanishing locus `F_zero`
is limit preserving.

Nothing is carried.  This is the theorem
`limitPreserving_zeroFunctor_of_hasQuasiCompactSupportOverTarget` of this namespace — the
source's proof: reduce to descent of vanishing along a limit of affine test schemes, choose
a stage, base change the situation to it, restrict the diagram to the stages over that one, and
apply the chart reduction there — with its hypothesis `hchart` discharged by
`AlgebraicGeometry.Space.ModuleMapSituation.hasAffineStageChartRingLevelZeroLocus`, which builds
the ring-level reading of the vanishing locus of the chart situation over each affine stage, and
`AlgebraicGeometry.Space.ModuleMapSituation.hasAffineStageChartZeroDescent_of_ringLevelZeroLocus`,
which supplies the limit content of the chart case.

The support hypothesis is the source's, read at the affine test schemes over `B`; see
`hasQuasiCompactSupportOverTarget_of_isQuasiCompact_schemeTheoreticSupport` for its derivation
from the source's sentence,
`limitPreserving_zeroFunctor_of_isQuasiCompact_schemeTheoreticSupport` for the clause stated at
that sentence, and
`limitPreserving_zeroFunctor_of_isQuasiCompact` for the case in which it is discharged
outright. -/
theorem limitPreserving_zeroFunctor (D : ModuleMapSituation.{u, u} B S hS)
    (hFft : SheafOfModules.IsFiniteTypeOnSite D.F)
    (hFqc : D.HasQuasiCompactSupportOverTarget) :
    LimitPreserving.{u, u, u, u} D.testScheme
      (D.zeroFunctor (modulePullbackSystem B S hS)) :=
  D.limitPreserving_zeroFunctor_of_hasQuasiCompactSupportOverTarget hFft hFqc
    (D.hasAffineStageChartZeroDescent_of_ringLevelZeroLocus
      (hasAffineStageChartRingLevelZeroLocus B S hS D))

/-- **Clause (2) of Stacks 083J for a quasi-compact `f`.**  Then the support hypothesis is not a
hypothesis: it holds for every finite-type `ℱ` by
`AlgebraicGeometry.Space.ModuleMapSituation.hasQuasiCompactSupportOverTarget_of_isQuasiCompact`,
which is the reduction the source itself makes ("Hence we may assume `f` is quasi-compact"). -/
theorem limitPreserving_zeroFunctor_of_isQuasiCompact (D : ModuleMapSituation.{u, u} B S hS)
    (hFft : SheafOfModules.IsFiniteTypeOnSite D.F)
    (hfqc : IsQuasiCompact B S hS D.f.hom) :
    LimitPreserving.{u, u, u, u} D.testScheme
      (D.zeroFunctor (modulePullbackSystem B S hS)) :=
  D.limitPreserving_zeroFunctor hFft
    (D.hasQuasiCompactSupportOverTarget_of_isQuasiCompact hFft hfqc)

/-! ### Clause (1) -/

/-- **Stacks 083J, clause (1).**  In the situation of Stacks 083F, if `𝒢` is of finite type and
the scheme-theoretic support of `𝒢` is quasi-compact over `B`, then the surjectivity locus
`F_surj` is limit preserving.

Nothing is carried.  The surjectivity locus of `u` *is* the vanishing locus of the cokernel
situation, whose source module is `𝒢`
(`AlgebraicGeometry.Space.ModuleMapSituation.limitPreserving_surjFunctor_iff_cokernelSituation`),
so this is clause (2) for that situation and the hypotheses match on the nose: clause (1) asks of
`𝒢` exactly what clause (2) asks of the source module of its own situation.

That is not the source's route, which replaces `X` by the scheme-theoretic support of `𝒢` and
`u` by `i^*ℱ ⟶ 𝒢` to make `f` quasi-compact and then runs the chart argument of clause (2)
against Algebra, Lemma 05LI part (2).  The cokernel route reaches the same statement through
clause (2) alone. -/
theorem limitPreserving_surjFunctor (D : ModuleMapSituation.{u, u} B S hS)
    (hGft : SheafOfModules.IsFiniteTypeOnSite D.G)
    (hGqc : (D.cokernelSituation).HasQuasiCompactSupportOverTarget) :
    LimitPreserving.{u, u, u, u} D.testScheme
      (D.surjFunctor (modulePullbackSystem B S hS)) :=
  (D.limitPreserving_surjFunctor_iff_cokernelSituation).mpr
    ((D.cokernelSituation).limitPreserving_zeroFunctor hGft hGqc)

/-- **Clause (1) of Stacks 083J for a quasi-compact `f`.**  The support hypothesis on `𝒢` is
then a theorem, by
`AlgebraicGeometry.Space.ModuleMapSituation.hasQuasiCompactSupportOverTarget_of_isQuasiCompact`
applied to the cokernel situation, whose structure morphism is `f` itself. -/
theorem limitPreserving_surjFunctor_of_isQuasiCompact (D : ModuleMapSituation.{u, u} B S hS)
    (hGft : SheafOfModules.IsFiniteTypeOnSite D.G)
    (hfqc : IsQuasiCompact B S hS D.f.hom) :
    LimitPreserving.{u, u, u, u} D.testScheme
      (D.surjFunctor (modulePullbackSystem B S hS)) :=
  D.limitPreserving_surjFunctor hGft
    ((D.cokernelSituation).hasQuasiCompactSupportOverTarget_of_isQuasiCompact hGft hfqc)

/-! ### The isomorphism locus for a surjective map -/

/-- **The isomorphism locus of a surjective `u` is limit preserving once the kernel of `u` is of
finite type with quasi-compact support.**  By
`AlgebraicGeometry.Space.ModuleMapSituation.limitPreserving_isoFunctor_iff_kernelSituation`,
`F_iso` is the vanishing locus of the kernel situation `ker u ⟶ ℱ`, so this is clause (2) for
that situation.  Nothing is carried.

This is *not* clause (3) of Stacks 083J, and no `@[stacks 083J]` attribute is claimed for it:
clause (3) assumes `ℱ` of finite type, `𝒢` of finite presentation and both supports
quasi-compact over `B`, and asks nothing of `u`.  Clause (3) itself is
`limitPreserving_isoFunctor` below, which supplies the two steps between the two statements — the
source's passage to a stage at which clause (1) has made `u` surjective, and finite type of the
kernel there by Stacks 082T. -/
theorem limitPreserving_isoFunctor_of_epi (D : ModuleMapSituation.{u, u} B S hS) [Epi D.u]
    (hKft : SheafOfModules.IsFiniteTypeOnSite (D.kernelSituation).F)
    (hKqc : (D.kernelSituation).HasQuasiCompactSupportOverTarget) :
    LimitPreserving.{u, u, u, u} D.testScheme
      (D.isoFunctor (modulePullbackSystem B S hS)) :=
  (D.limitPreserving_isoFunctor_iff_kernelSituation).mpr
    ((D.kernelSituation).limitPreserving_zeroFunctor hKft hKqc)

/-! ### Clause (3) -/

/-- **Stacks 082T on the small étale site of an algebraic space: the kernel of a surjection from
a finite-type module onto a module of finite presentation is of finite type.**

Stacks 082T is `Stacks.SheafOfModules.SliceFinite.isFiniteType_kernel_of_epi`, and its transfer
to the rendering of Stacks 03DL(5) and 03DL(7) by universal properties — the rendering in which
the finiteness conditions of `𝒪_X`-modules are stated here — is
`Stacks.SheafOfModules.isFiniteTypeOnSite_kernel_of_isFinitePresentationOnSite_of_small`.  Its
three hypotheses all hold on the small étale site: sheafification of abelian presheaves on the
site and on each of its slices, and local bijectivity of the weak equivalences there, are the
instances `AlgebraicGeometry.Space.smallEtaleRingedSite_hasSheafify_over` and
`AlgebraicGeometry.Space.smallEtaleRingedSite_wEqualsLocallyBijective_over`; and smallness of
the global sections over each object is `SheafOfModules.small_sections_of_isTerminal` at the
final object `CategoryTheory.Over.mkIdTerminal` of the slice.

This is the finite-type input to clause (3) of Stacks 083J, which the source takes from Modules
on Sites, Lemma 18.24.2. -/
theorem isFiniteTypeOnSite_kernelSituation_F (D : ModuleMapSituation.{u, u} B S hS) [Epi D.u]
    (hFft : SheafOfModules.IsFiniteTypeOnSite D.F)
    (hGfp : SheafOfModules.IsFinitePresentationOnSite D.G) :
    SheafOfModules.IsFiniteTypeOnSite (D.kernelSituation).F :=
  have : ∀ (U : (smallEtaleRingedSite B S hS D.X.1 D.X.2).C)
      (N : SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS D.X.1 D.X.2).O).over U)), Small.{u} N.sections :=
    fun _ N => SheafOfModules.small_sections_of_isTerminal Over.mkIdTerminal N
  Stacks.SheafOfModules.isFiniteTypeOnSite_kernel_of_isFinitePresentationOnSite_of_small
    D.u hGfp hFft

/-- **The support of the kernel of `u` is compact as soon as the support of `ℱ` is.**  The
kernel inclusion is a monomorphism, the forgetful functor to abelian sheaves preserves finite
limits hence monomorphisms, so `AlgebraicGeometry.Space.supportOfSheaf_subset_of_mono` places
the support of `Ker u` inside that of `ℱ`; it is closed there because `Ker u` is of finite type
(`AlgebraicGeometry.Space.isClosed_supportOfSheaf_of_isFiniteTypeOnSite`), and a closed subset
of a compact set is compact.

This is the source's sentence "its support is contained in the support of `ℱ_{T₀}`, which is
quasi-compact over `T₀`". -/
theorem isCompact_supportOfSheaf_kernelSituation_F (D : ModuleMapSituation.{u, u} B S hS)
    (hKft : SheafOfModules.IsFiniteTypeOnSite (D.kernelSituation).F)
    (hFcompact : IsCompact
      (supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj D.F))) :
    IsCompact (supportOfSheaf B S hS (D.kernelSituation).X.1
      ((SheafOfModules.toSheaf _).obj (D.kernelSituation).F)) := by
  have : SheafOfModules.IsFiniteTypeOnSite (kernel D.u) := hKft
  have hmono : Mono ((SheafOfModules.toSheaf _).map (kernel.ι D.u)) :=
    preserves_mono_of_preservesLimit _ _
  exact hFcompact.of_isClosed_subset
    (isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS D.X.1 D.X.2 (kernel D.u))
    (@supportOfSheaf_subset_of_mono B S hS D.X.1 D.X.2 _ _
      ((SheafOfModules.toSheaf _).map (kernel.ι D.u)) hmono)

/-- **Being an isomorphism at a test scheme over `T₀` is the same condition for the situation and
for its base change to `T₀`.**  This is
`AlgebraicGeometry.Space.ModuleMapSituation.isIsoAt_baseChangeTarget_iff` read through the
section of `overTarget`, and it is the clause-(3) counterpart of
`AlgebraicGeometry.Space.ModuleMapSituation.isZeroAt_overTargetSection_iff`. -/
theorem isIsoAt_overTargetSection_iff (D : ModuleMapSituation.{u, u} B S hS)
    (T₀ : D.SchemesOver) (A : Over T₀) :
    (D.baseChangeTestScheme T₀).IsIsoAt (modulePullbackSystem B S hS)
        ((D.overTargetSection T₀).obj A) ↔
      D.IsIsoAt (modulePullbackSystem B S hS) A.left := by
  rw [D.isIsoAt_baseChangeTarget_iff T₀.hom ((D.overTargetSection T₀).obj A),
    D.overTarget_obj_overTargetSection_obj T₀ A]

/-- **Clause (3) over an affine base, for a surjective `u`, with nothing carried.**  For a
situation whose target is the algebraic space of an affine object of the site and whose `u` is an
epimorphism, `F_iso` is limit preserving as soon as `ℱ` is of finite type with compact support
and `𝒢` is of finite presentation.

This is the geometric step of the source's proof of clause (3), isolated at the one stage the
proof performs it at.  By `limitPreserving_isoFunctor_iff_kernelSituation` — Stacks 0CVM on
`ker u ⟶ ℱ ⟶ 𝒢 ⟶ 0` — `F_iso` is the vanishing locus of the kernel situation, and clause (2) in
the form `limitPreserving_zeroFunctor_of_isCompact_of_hasAffineChartZeroDescent` applies to it:
its source module `Ker u` is of finite type by Stacks 082T
(`isFiniteTypeOnSite_kernelSituation_F`), its support is compact
(`isCompact_supportOfSheaf_kernelSituation_F`), and the chart hypothesis is a theorem over an
affine base (`hasAffineChartRingLevelZeroLocus_of_eq`, which reads `hDY` and `hY₀` through
`kernelSituation_Y`).

No `@[stacks 083J]` attribute is claimed: this is clause (3) only for a surjective `u` over an
affine base.  The clause itself is `limitPreserving_isoFunctor` below, which applies this at the
stage clause (1) produces. -/
theorem limitPreserving_isoFunctor_of_epi_of_isCompact_of_eq
    (D : ModuleMapSituation.{u, u} B S hS) [Epi D.u] {Y₀ : BigFppfOver B S hS}
    (hDY : D.Y = schemeSpace Y₀) (hY₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj Y₀))
    (hFft : SheafOfModules.IsFiniteTypeOnSite D.F)
    (hGfp : SheafOfModules.IsFinitePresentationOnSite D.G)
    (hFcompact : IsCompact
      (supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj D.F))) :
    LimitPreserving.{u, u, u, u} D.testScheme
      (D.isoFunctor (modulePullbackSystem B S hS)) :=
  have hKft := D.isFiniteTypeOnSite_kernelSituation_F hFft hGfp
  D.limitPreserving_isoFunctor_iff_kernelSituation.mpr
    (limitPreserving_zeroFunctor_of_isCompact_of_hasAffineChartZeroDescent D.kernelSituation hKft
      (D.isCompact_supportOfSheaf_kernelSituation_F hKft hFcompact)
      (D.kernelSituation.hasAffineChartZeroDescent_of_ringLevelZeroLocus
        (hasAffineChartRingLevelZeroLocus_of_eq B S hS D.kernelSituation hDY hY₀)))

/-- **Inverse image along the projection from the base-change space of a test scheme is inverse
image along the projection from the source space of the base change to it.**  The base-change
space `X ×_Y T` of the test scheme and the source space of the base change of the situation along
its structure morphism are the same fibre product, projecting to `X` by the same
`CategoryTheory.Limits.pullback.fst`. -/
theorem modulePullback_baseChangeProjection_eq (D : ModuleMapSituation.{u, u} B S hS)
    (T : D.SchemesOver) :
    modulePullback B S hS (D.baseChangeProjection T)
      = modulePullback B S hS (D.baseChangeTargetProjection T.hom) :=
  rfl

/-- **Surjectivity of `u` at a test scheme is surjectivity of the map of the situation base
changed to that test scheme.**  Both are the inverse image of `u` along the same projection
`X ×_Y T ⟶ X`, by `modulePullback_baseChangeProjection_eq`. -/
theorem epi_u_baseChangeTestScheme (D : ModuleMapSituation.{u, u} B S hS) (T : D.SchemesOver)
    (h : D.IsSurjectiveAt (modulePullbackSystem B S hS) T) :
    Epi (D.baseChangeTestScheme T).u := by
  have h₁ : Epi ((modulePullback B S hS (D.baseChangeProjection T)).map D.u) := h
  have h₂ : Epi ((modulePullback B S hS (D.baseChangeTargetProjection T.hom)).map D.u) := by
    rw [← D.modulePullback_baseChangeProjection_eq T]
    exact h₁
  rw [D.baseChangeTarget_u T.hom]
  exact h₂

/-- **Stacks 083J, clause (3).**  In the situation of Stacks 083F, if `ℱ` is of finite type, `𝒢`
is of finite presentation, and the scheme-theoretic supports of both are quasi-compact over `B`,
then the isomorphism locus `F_iso` is limit preserving.

Nothing is carried.  This is the source's own deduction of clause (3) from clauses (1) and (2),
run in the order the source runs it.

* Limit preservation of `F_iso` is descent of "the base change of `u` is an isomorphism" along
  limits of affine test schemes
  (`AlgebraicGeometry.Space.ModuleMapSituation.limitPreserving_isoFunctor_iff`).  Given such a
  cofiltered diagram with `u` an isomorphism at the cone point, `u` is in particular surjective
  there, so clause (1) — `limitPreserving_surjFunctor` above — produces a stage `T₀` at which
  `u` is surjective.
* The situation is base changed to that stage
  (`AlgebraicGeometry.Space.ModuleMapSituation.baseChangeTestScheme`), where `u` is an
  epimorphism, and `𝒦 = Ker(u_{T₀})` is formed
  (`AlgebraicGeometry.Space.ModuleMapSituation.kernelSituation`).  By Stacks 0CVM on the exact
  sequence `𝒦 ⟶ ℱ_{T₀} ⟶ 𝒢_{T₀} ⟶ 0`, being an isomorphism is vanishing of `𝒦 ⟶ ℱ_{T₀}`
  (`limitPreserving_isoFunctor_iff_kernelSituation`), which is the source's `v`.
* `𝒦` is of finite type by Stacks 082T
  (`isFiniteTypeOnSite_kernelSituation_F` above, the source's Modules on Sites, Lemma 18.24.2),
  and its support is compact because it sits inside the support of `ℱ_{T₀}`
  (`isCompact_supportOfSheaf_kernelSituation_F` above), which is compact at an affine stage by
  Stacks 07TZ(3) and the support hypothesis.  So clause (2) applies to `𝒦 ⟶ ℱ_{T₀}` in the form
  `limitPreserving_zeroFunctor_of_isCompact_of_hasAffineChartZeroDescent`, whose chart hypothesis
  is a theorem over an affine stage
  (`AlgebraicGeometry.Space.ModuleMapSituation.hasAffineChartRingLevelZeroLocus_of_eq`).
* The diagram is restricted to the stages over `T₀`
  (`AlgebraicGeometry.Space.ModuleMapSituation.stageDiagram`, the source's "replace `I` by
  `{i | i ≥ 0}`"), whose limit is the same cone point, and being an isomorphism at such a stage
  is the same condition for the two situations
  (`isIsoAt_overTargetSection_iff` above).

The hypothesis on the support of `𝒢` enters only through clause (1), and the hypothesis on the
support of `ℱ` only through compactness of the support at the chosen affine stage; see
`hasQuasiCompactSupportOverTarget_of_isQuasiCompact_schemeTheoreticSupport` for its derivation
from the source's sentence,
`limitPreserving_isoFunctor_of_isQuasiCompact_schemeTheoreticSupport` for the clause stated at
that sentence, and
`limitPreserving_isoFunctor_of_isQuasiCompact` for the case in which both are discharged
outright. -/
theorem limitPreserving_isoFunctor (D : ModuleMapSituation.{u, u} B S hS)
    (hFft : SheafOfModules.IsFiniteTypeOnSite D.F)
    (hGfp : SheafOfModules.IsFinitePresentationOnSite D.G)
    (hFqc : D.HasQuasiCompactSupportOverTarget)
    (hGqc : (D.cokernelSituation).HasQuasiCompactSupportOverTarget) :
    LimitPreserving.{u, u, u, u} D.testScheme
      (D.isoFunctor (modulePullbackSystem B S hS)) := by
  have := hGfp
  have hGft : SheafOfModules.IsFiniteTypeOnSite D.G := inferInstance
  rw [D.limitPreserving_isoFunctor_iff (modulePullbackSystem B S hS)]
  intro I _ _ E c hc hE hpt hiso
  have hc0 : IsIso (D.baseChangeHom (modulePullbackSystem B S hS) c.pt) := hiso
  obtain ⟨i₀, hi₀⟩ := (D.limitPreserving_surjFunctor_iff (modulePullbackSystem B S hS)).mp
    (D.limitPreserving_surjFunctor hGft hGqc) I E c hc hE hpt (by
      show Epi (D.baseChangeHom (modulePullbackSystem B S hS) c.pt)
      infer_instance)
  have hepi := D.epi_u_baseChangeTestScheme _ hi₀
  have hlp :=
    limitPreserving_isoFunctor_of_epi_of_isCompact_of_eq
      (D.baseChangeTestScheme (E.obj i₀)) (Y₀ := (E.obj i₀).left) rfl (hE i₀)
      (isFiniteTypeOnSite_modulePullback B S hS
        (D.baseChangeTargetProjection (E.obj i₀).hom) D.F hFft)
      (isFinitePresentationOnSite_modulePullback B S hS
        (D.baseChangeTargetProjection (E.obj i₀).hom) D.G hGfp)
      (D.isCompact_supportOfSheaf_baseChangeTestScheme hFft hFqc (E.obj i₀) (hE i₀))
  obtain ⟨A, hA⟩ := ((D.baseChangeTestScheme (E.obj i₀)).limitPreserving_isoFunctor_iff
    (modulePullbackSystem B S hS)).mp hlp (Over i₀) (D.stageDiagram E i₀) (D.stageCone E c i₀)
    (D.isLimitStageCone E c i₀ hc) (fun A => hE A.left) hpt
    ((D.isIsoAt_overTargetSection_iff (E.obj i₀) (Over.mk (c.π.app i₀))).mpr hiso)
  exact ⟨A.left, (D.isIsoAt_overTargetSection_iff (E.obj i₀) ((Over.post E).obj A)).mp hA⟩

/-- **Clause (3) of Stacks 083J for a quasi-compact `f`.**  Both support hypotheses are then
theorems, by
`AlgebraicGeometry.Space.ModuleMapSituation.hasQuasiCompactSupportOverTarget_of_isQuasiCompact`
applied to the situation and to its cokernel situation, whose structure morphism is `f`
itself. -/
theorem limitPreserving_isoFunctor_of_isQuasiCompact (D : ModuleMapSituation.{u, u} B S hS)
    (hFft : SheafOfModules.IsFiniteTypeOnSite D.F)
    (hGfp : SheafOfModules.IsFinitePresentationOnSite D.G)
    (hfqc : IsQuasiCompact B S hS D.f.hom) :
    LimitPreserving.{u, u, u, u} D.testScheme
      (D.isoFunctor (modulePullbackSystem B S hS)) :=
  have := hGfp
  have hGft : SheafOfModules.IsFiniteTypeOnSite D.G := inferInstance
  D.limitPreserving_isoFunctor hFft hGfp
    (D.hasQuasiCompactSupportOverTarget_of_isQuasiCompact hFft hfqc)
    ((D.cokernelSituation).hasQuasiCompactSupportOverTarget_of_isQuasiCompact hGft hfqc)

/-! ### The source's support hypothesis -/

/-- **Quasi-compactness of the scheme-theoretic support over the target gives compactness of
the support at every affine stage.**  If `ℱ` is of finite type and its scheme-theoretic support
`i : Z ⟶ X` (Stacks 07U1) is quasi-compact over `B`, that is, `i ≫ f` is a quasi-compact
morphism, then `AlgebraicGeometry.Space.ModuleMapSituation.HasQuasiCompactSupportOverTarget`
holds: for every affine test scheme `T` over `B` the inverse image of the support of `ℱ` in
`|X ×_B T|` is compact.

This is the step of the source's proof of clause (2) of Stacks 083J "Set `Z_0 = Z ×_X X_0`
... Since `|Z_0|` is quasi-compact".  The fibre product `P = Z ×_X (X ×_B T)` is, by pasting
the two cartesian squares, the base change of `i ≫ f` along `T ⟶ B`
(`CategoryTheory.IsPullback.paste_vert`), so its projection to `T` is quasi-compact by
Stacks 03HF (`AlgebraicGeometry.Space.isQuasiCompact_of_isPullback`), and `P` is a
quasi-compact algebraic space because `T` is affine
(`AlgebraicGeometry.Space.isQuasiCompactSpace_source_of_isQuasiCompact`); its points form a
compact space by Stacks 03E4, so the image of `|P| ⟶ |X ×_B T|` is compact.  That image contains
the inverse image of the support: the support of `ℱ` is the image of `|Z|` by Stacks 07U0
part (4) (`AlgebraicGeometry.Space.supportOfSheaf_eq_range_pointsMap_schemeTheoreticSupport`),
and a point of `X ×_B T` over a point of `|Z|` lifts to `P` by Stacks 03H4
(`AlgebraicGeometry.Space.exists_point_of_isPullback`).  The inverse image of the support is
closed, the support being closed for a module of finite type
(`AlgebraicGeometry.Space.isClosed_supportOfSheaf_of_isFiniteTypeOnSite`) and the map of points
continuous, and a closed subset of a compact set is compact. -/
theorem hasQuasiCompactSupportOverTarget_of_isQuasiCompact_schemeTheoreticSupport
    (D : ModuleMapSituation.{u, u} B S hS)
    (hFft : SheafOfModules.IsFiniteTypeOnSite D.F)
    (hZqc : IsQuasiCompact B S hS ((schemeTheoreticSupport B S hS D.X D.F).ι ≫ D.f.hom)) :
    D.HasQuasiCompactSupportOverTarget := by
  intro T hT
  obtain ⟨hZ, -⟩ := exists_isClosedSubspace_schemeTheoreticSupport B S hS D.X D.F
    D.quasicoherent_F (Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteTypeOnSite D.F hFft)
  let Zc : ClosedSubspaces B S hS D.X.1 := ⟨schemeTheoreticSupport B S hS D.X D.F, hZ⟩
  let i := closedSubspaceInclusion B S hS D.X Zc
  let pr := D.baseChangeTargetProjection T.hom
  have sq₁ := AlgebraicSpaces.isPullback_fiberProduct B S hS i pr
  have sq := sq₁.paste_vert (D.isPullback_baseChangeTargetSpace T.hom)
  have hqc := isQuasiCompact_of_isPullback B S hS (AlgebraicSpaces.isPullback_hom B S hS sq)
    hZqc
  have haff : IsAffine ((BigFppfOver.toScheme B S hS).obj T.left) := hT
  have hPqc : IsQuasiCompactSpace B S hS (AlgebraicSpaces.fiberProduct B S hS i pr).1 :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS (isAlgebraicSpace_yoneda B S hS T.left)
      (isQuasiCompactSpace_yoneda_of_isAffine B S hS T.left haff) hqc
  have hPc := (isQuasiCompactSpace_iff_compactSpace_points B S hS _
    (AlgebraicSpaces.fiberProduct B S hS i pr).2).mp hPqc
  have hK : IsCompact (Set.range (pointsMap B S hS (AlgebraicSpaces.fiberProduct B S hS i pr).1
      (pullback.snd i.hom pr.hom))) :=
    isCompact_range (continuous_pointsMap B S hS _)
  have hclosed : IsClosed (pointsMap B S hS (D.baseChangeTestScheme T).X.1 pr.hom ⁻¹'
      supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj D.F)) := by
    have := hFft
    exact (isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS D.X.1 D.X.2 D.F).preimage
      (continuous_pointsMap B S hS _)
  refine hK.of_isClosed_subset hclosed ?_
  intro x hx
  rw [Set.mem_preimage, supportOfSheaf_eq_range_pointsMap_schemeTheoreticSupport B S hS D.X D.F
    D.quasicoherent_F hFft] at hx
  obtain ⟨z, hz⟩ := hx
  obtain ⟨w, -, hw⟩ := exists_point_of_isPullback B S hS sq₁ z x hz
  exact ⟨w, hw⟩

/-- **Stacks 083J, clause (2), at the source's hypotheses.**  In the situation of Stacks 083F,
if `ℱ` is of finite type and the scheme-theoretic support of `ℱ` (Stacks 07U1) is quasi-compact
over `B`, then the vanishing locus `F_zero` is limit preserving.

The support hypothesis is the source's sentence verbatim: the composite of the inclusion of the
scheme-theoretic support `Z ⟶ X` with `f : X ⟶ B` is a quasi-compact morphism.  It implies the
compactness at the affine stages that the proof spends, by
`hasQuasiCompactSupportOverTarget_of_isQuasiCompact_schemeTheoreticSupport`, and then this is
`limitPreserving_zeroFunctor`. -/
@[stacks 083J "clause (2): F_zero is limit preserving, at the source's hypotheses verbatim -- F \
of finite type and its scheme-theoretic support (07U1) quasi-compact over B, i.e. Z -> X -> B \
quasi-compact. Nothing is carried: the support hypothesis gives compactness of the support at \
the affine stages (hasQuasiCompactSupportOverTarget_of_isQuasiCompact_schemeTheoreticSupport: \
03HF on the pasted square Z x_X X_T = Z x_B T, 07U0(4), 03H4), and the rest is \
limitPreserving_zeroFunctor. The index universe is the universe of the schemes, and must be: \
the clause is FALSE one universe up, by SmallnessNecessary/Basic.lean"]
theorem limitPreserving_zeroFunctor_of_isQuasiCompact_schemeTheoreticSupport
    (D : ModuleMapSituation.{u, u} B S hS)
    (hFft : SheafOfModules.IsFiniteTypeOnSite D.F)
    (hFqc : IsQuasiCompact B S hS ((schemeTheoreticSupport B S hS D.X D.F).ι ≫ D.f.hom)) :
    LimitPreserving.{u, u, u, u} D.testScheme
      (D.zeroFunctor (modulePullbackSystem B S hS)) :=
  D.limitPreserving_zeroFunctor hFft
    (D.hasQuasiCompactSupportOverTarget_of_isQuasiCompact_schemeTheoreticSupport hFft hFqc)

/-- **Stacks 083J, clause (1), at the source's hypotheses.**  In the situation of Stacks 083F,
if `𝒢` is of finite type and the scheme-theoretic support of `𝒢` (Stacks 07U1) is
quasi-compact over `B`, then the surjectivity locus `F_surj` is limit preserving.

The cokernel situation has source module `𝒢`, source space `X` and structure morphism `f`, so
`hasQuasiCompactSupportOverTarget_of_isQuasiCompact_schemeTheoreticSupport` applied to it turns
the source's hypothesis on `𝒢` into the one `limitPreserving_surjFunctor` asks for. -/
@[stacks 083J "clause (1): F_surj is limit preserving, at the source's hypotheses verbatim -- G \
of finite type and its scheme-theoretic support (07U1) quasi-compact over B, i.e. Z -> X -> B \
quasi-compact. Nothing is carried: the support hypothesis on G is turned into compactness at \
the affine stages for the cokernel situation (whose source module is G) by \
hasQuasiCompactSupportOverTarget_of_isQuasiCompact_schemeTheoreticSupport, and the rest is \
limitPreserving_surjFunctor. Index universe as in clause (2)"]
theorem limitPreserving_surjFunctor_of_isQuasiCompact_schemeTheoreticSupport
    (D : ModuleMapSituation.{u, u} B S hS)
    (hGft : SheafOfModules.IsFiniteTypeOnSite D.G)
    (hGqc : IsQuasiCompact B S hS ((schemeTheoreticSupport B S hS D.X D.G).ι ≫ D.f.hom)) :
    LimitPreserving.{u, u, u, u} D.testScheme
      (D.surjFunctor (modulePullbackSystem B S hS)) :=
  D.limitPreserving_surjFunctor hGft
    (hasQuasiCompactSupportOverTarget_of_isQuasiCompact_schemeTheoreticSupport
      D.cokernelSituation hGft hGqc)

/-- **Stacks 083J, clause (3), at the source's hypotheses.**  In the situation of Stacks 083F,
if `ℱ` is of finite type, `𝒢` is of finite presentation, and the scheme-theoretic supports of
`ℱ` and `𝒢` (Stacks 07U1) are quasi-compact over `B`, then the isomorphism locus `F_iso` is
limit preserving.

Both support hypotheses are the source's sentence verbatim, and
`hasQuasiCompactSupportOverTarget_of_isQuasiCompact_schemeTheoreticSupport`, applied to the
situation and to its cokernel situation, turns them into the ones `limitPreserving_isoFunctor`
asks for; a module of finite presentation is of finite type. -/
@[stacks 083J "clause (3): F_iso is limit preserving, at the source's hypotheses verbatim -- F \
of finite type, G of finite presentation, and the scheme-theoretic supports (07U1) of F and G \
quasi-compact over B. Nothing is carried: the two support hypotheses are turned into \
compactness at the affine stages by \
hasQuasiCompactSupportOverTarget_of_isQuasiCompact_schemeTheoreticSupport (for the situation \
and for its cokernel situation), and the rest is limitPreserving_isoFunctor, the source's own \
deduction of (3) from (1) and (2) through ker(u_{T_0}) and Stacks 082T. Index universe as in \
clause (2)"]
theorem limitPreserving_isoFunctor_of_isQuasiCompact_schemeTheoreticSupport
    (D : ModuleMapSituation.{u, u} B S hS)
    (hFft : SheafOfModules.IsFiniteTypeOnSite D.F)
    (hGfp : SheafOfModules.IsFinitePresentationOnSite D.G)
    (hFqc : IsQuasiCompact B S hS ((schemeTheoreticSupport B S hS D.X D.F).ι ≫ D.f.hom))
    (hGqc : IsQuasiCompact B S hS ((schemeTheoreticSupport B S hS D.X D.G).ι ≫ D.f.hom)) :
    LimitPreserving.{u, u, u, u} D.testScheme
      (D.isoFunctor (modulePullbackSystem B S hS)) :=
  have := hGfp
  have hGft : SheafOfModules.IsFiniteTypeOnSite D.G := inferInstance
  D.limitPreserving_isoFunctor hFft hGfp
    (D.hasQuasiCompactSupportOverTarget_of_isQuasiCompact_schemeTheoreticSupport hFft hFqc)
    (hasQuasiCompactSupportOverTarget_of_isQuasiCompact_schemeTheoreticSupport
      D.cokernelSituation hGft hGqc)

end ModuleMapSituation

end AlgebraicGeometry.Space

end
