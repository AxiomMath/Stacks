module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LimitPreserving
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapSituationExact
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentKernelsOnSite
public import StacksFrontier.CategoryTheory.Sites.SubsingletonPresheaf
public import StacksCore.Tactic.StacksAttribute

/-!
# Limit preservation of the base-change loci of a map of quasi-coherent modules

In the situation of Stacks 083F — a morphism `f : X ⟶ Y` of algebraic spaces and a map
`u : ℱ ⟶ 𝒢` of quasi-coherent `𝒪_X`-modules — the four base-change loci `F_iso`, `F_inj`,
`F_surj` and `F_zero` are subterminal presheaves on the schemes over `Y`.  This file sets up
the limit-preservation question for them and proves the two formal reductions that the proof of
Stacks 083J performs before it reaches geometry.

Because the loci are subterminal, limit preservation in the sense of Stacks 049J collapses to a
single implication: for every cofiltered diagram of affine test schemes whose underlying-scheme
cone is a limit, the condition at the cone point already holds at some stage.  That is
`AlgebraicGeometry.Space.ModuleMapSituation.DescendsAlongAffineLimits`, and the collapse is
`AlgebraicGeometry.Space.ModuleMapSituation.limitPreserving_subterminalFunctor_iff`.  The
converse implication, which a colimit also asserts, is the base-change stability of the
condition already proved for all four loci in Stacks 083F.

## Main definitions

* `AlgebraicGeometry.Space.ModuleMapSituation.testScheme` is the underlying-scheme functor on
  the test category, the datum `AlgebraicGeometry.LimitPreserving` needs.
* `AlgebraicGeometry.Space.ModuleMapSituation.DescendsAlongAffineLimits` is the descent
  condition above.
* `AlgebraicGeometry.Space.ModuleMapSituation.cokernelSituation` reads the cokernel of `u` as a
  situation of Stacks 083F in its own right, with source module `𝒢`.
* `AlgebraicGeometry.Space.ModuleMapSituation.kernelSituation` reads the kernel of `u` as a
  situation of Stacks 083F in its own right, with target module `ℱ` and map the kernel
  inclusion.

## Main results

* `AlgebraicGeometry.Space.ModuleMapSituation.limitPreserving_subterminalFunctor_iff` and its
  four specialisations `limitPreserving_isoFunctor_iff`, `limitPreserving_injFunctor_iff`,
  `limitPreserving_surjFunctor_iff`, `limitPreserving_zeroFunctor_iff`.
* `AlgebraicGeometry.Space.ModuleMapSituation.limitPreserving_surjFunctor_iff_cokernelSituation`
  is **clause (1) of Stacks 083J reduced to clause (2)**: `F_surj` is limit preserving exactly
  when the vanishing locus of the cokernel situation is.  The hypotheses match on the nose,
  because the source module of the cokernel situation is `𝒢` — clause (1) asks `𝒢` to be of
  finite type with quasi-compact scheme-theoretic support, which is what clause (2) asks of the
  source module of its own situation.
* `AlgebraicGeometry.Space.ModuleMapSituation.limitPreserving_isoFunctor_of_surj_of_inj` is
  **clause (3) of Stacks 083J reduced**: `F_iso` is limit preserving once `F_surj` and `F_inj`
  are.  This is not the source's deduction of (3) from (1) and (2), which goes through the
  kernel of `u_{T_0}`; it is the balanced-category argument, available because a base change of
  `u` is an isomorphism exactly when it is both an epimorphism and universally a
  monomorphism.  Read the caveat on it in the implementation notes before using it: `F_inj` is
  not the subject of any clause of Stacks 083J.
* `AlgebraicGeometry.Space.ModuleMapSituation.limitPreserving_isoFunctor_iff_kernelSituation`
  is **clause (3) of Stacks 083J for a surjective `u`, reduced to clause (2)** — the source's
  own route: `F_iso` is limit preserving exactly when the vanishing locus of the kernel
  situation is.  Nothing is carried, and unlike the balanced-category reduction it appeals to
  no statement outside Stacks 083J.  Applied at a stage produced by clause (1) it gives clause
  (3) itself with nothing carried, in
  `StacksFrontier/AlgebraicGeometry/Spaces/ModuleMapLociLimitPreservingUnconditional.lean`.
* `AlgebraicGeometry.Space.ModuleMapSituation.injFunctor_eq_isoFunctor_of_epi`: for a surjective
  `u` the loci `F_inj` and `F_iso` are *the same* subterminal functor.

## Implementation notes

**What is not proved here.**  Neither clause (2) of Stacks 083J nor, therefore, clauses (1) and
(3) outright.  Clause (2) says that the vanishing locus of a finite-type module with
quasi-compact scheme-theoretic support descends along limits of affine test schemes; its proof
chooses an affine scheme `W_0` étale over `X_{T_0}` whose image contains the support of
`ℱ_{T_0}`, forms the limit of the base changes `W_i = W_0 ×_{T_0} T_i`, and lands in Algebra,
Lemma 05LI (1), which this library has in all four parts as
`Stacks.FinitePresentation.ModuleDescent.statement_one` and its siblings.

Clause (2) is not absent from the library; it is *carried*.  It is the theorem
`limitPreserving_zeroFunctor_of_hasQuasiCompactSupportOverTarget` of this namespace, in
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleMapZeroLocusLimitPreserving.lean`, a module above
this one, and everything of the source's proof is done there except one hypothesis, `hchart :
AlgebraicGeometry.Space.ModuleMapSituation.HasAffineStageChartZeroDescent`, which at the scheme
universe is reduced to the limit-free
`AlgebraicGeometry.Space.ModuleMapSituation.HasAffineStageChartRingLevelZeroLocus` by
`AlgebraicGeometry.Space.ModuleMapSituation.hasAffineStageChartZeroDescent_of_ringLevelZeroLocus`.
That limit-free hypothesis is in turn *proved*, for every situation and every affine stage, by
`AlgebraicGeometry.Space.ModuleMapSituation.hasAffineStageChartRingLevelZeroLocus` in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartRingLevelZeroLocusOverAffine.lean` — so all three
clauses of Stacks 083J carry nothing at all, and the wiring is
`AlgebraicGeometry.Space.ModuleMapSituation.limitPreserving_zeroFunctor`,
`AlgebraicGeometry.Space.ModuleMapSituation.limitPreserving_surjFunctor` and
`AlgebraicGeometry.Space.ModuleMapSituation.limitPreserving_isoFunctor` in
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleMapLociLimitPreservingUnconditional.lean`.  They
cannot be stated here: every module holding the pieces imports this one.

The reductions below are therefore stated with no finiteness or quasi-compactness hypothesis:
they are equivalences and implications between limit-preservation statements, so they hold for
every situation and specialise to 083J's clauses — which they now do, in the module just named,
at the index universe of the schemes, the only one at which the clauses are true.

**The caveat on the balanced-category reduction of clause (3).**  Its hypothesis `hinj`, limit
preservation of `F_inj`, is *not the subject of any clause of Stacks 083J*: the three clauses are
about `F_surj`, `F_zero` and `F_iso`.  Nothing in the source supplies it, so
`limitPreserving_isoFunctor_of_surj_of_inj` is a reduction of clause (3) to a statement outside
083J, and this is made precise here: by
`AlgebraicGeometry.Space.ModuleMapSituation.injFunctor_eq_isoFunctor_of_epi`, on the situations
whose `u` is an epimorphism `F_inj` and `F_iso` are the same functor, so there `hinj` is
verbatim the theorem's own conclusion while `hsurj` holds for free.  Those are exactly the
situations the source's proof of clause (3) reduces to, having used clause (1) to find a stage at
which `u` is surjective.  The reduction is not circular — in general neither carry follows from
the conclusion — but it carries no weight where clause (3) is applied.

`AlgebraicGeometry.Space.ModuleMapSituation.limitPreserving_isoFunctor_iff_kernelSituation` is
the source's own route in its place, and it carries nothing: for a surjective `u` the exact
sequence `ker u ⟶ ℱ ⟶ 𝒢 ⟶ 0` and Stacks 0CVM
(`AlgebraicGeometry.Space.ModuleMapSituation.isoFunctor_secondMap_eq_zeroFunctor`) identify
`F_iso` with the vanishing locus of the kernel situation, so clause (3) for such a `u` is clause
(2) for `ker u ⟶ ℱ`.  What it does not do is pass to a stage: the source forms its kernel over
the base-change space `X_{T_0}` of an affine stage, and the base change of a situation along a
test scheme (`AlgebraicGeometry.Space.ModuleMapSituation.baseChangeTestScheme`) lives above this
file.  **That passage is made, and clause (3) is a theorem with nothing carried**, in
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleMapLociLimitPreservingUnconditional.lean`:
`AlgebraicGeometry.Space.ModuleMapSituation.limitPreserving_isoFunctor`.  The finite-type input
on `Ker(u_{T_0})` which the source takes from Modules on Sites, Lemma 18.24.2 is Stacks 082T,
`Stacks.SheafOfModules.isFiniteTypeOnSite_kernel_of_isFinitePresentationOnSite_of_small`, which
does apply on the small étale site of an algebraic space.

**Universes.**  The cokernel and kernel reductions are at the module universe of the structure
rings, `m = u`, because that is where `AlgebraicGeometry.Space.modulePullbackSystem` is built
and where cokernels of `𝒪_X`-modules exist (`AlgebraicGeometry.Space.hasCokernel_modules`) and
are quasi-coherent (`AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_unconditional`),
and where quasi-coherence of a kernel is unconditional
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_kernel_of_isCartesian` against Stacks 03DX (2),
`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts`).  The subterminal
criterion is universe-polymorphic in the module universe.

The private `isSurjectiveAt_iff_secondMap_isZeroAt_of` is the surjectivity analogue of the
private `isIsoAt_secondMap_iff_isZeroAt_of` of
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleMapSituationExact.lean`.

## References

* [Stacks Project, Tag 083J](https://stacks.math.columbia.edu/tag/083J)
* [Stacks Project, Tag 083F](https://stacks.math.columbia.edu/tag/083F)
* [Stacks Project, Tag 049J](https://stacks.math.columbia.edu/tag/049J)
* [Stacks Project, Tag 05LI](https://stacks.math.columbia.edu/tag/05LI)
* [Stacks Project, Tag 0CVM](https://stacks.math.columbia.edu/tag/0CVM)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 082T](https://stacks.math.columbia.edu/tag/082T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u m w w'

namespace AlgebraicGeometry.Space

namespace ModuleMapSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The test category over the schemes -/

/-- The underlying-scheme functor on the test schemes of a situation of Stacks 083F: forget the
structure morphism to `Y`, then take the underlying scheme of the object of the big fppf site.

This is the datum `AlgebraicGeometry.LimitPreserving` consumes. -/
def testScheme (D : ModuleMapSituation.{u, m} B S hS) : D.SchemesOver ⥤ Scheme.{u} :=
  CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y ⋙ BigFppfOver.toScheme B S hS

/-- A property of the test schemes of a situation of Stacks 083F **descends along limits of
affine test schemes** when, for every cofiltered diagram of test schemes with affine underlying
schemes whose underlying-scheme cone is a limit and whose cone point is again affine, the
property at the cone point already holds at some stage of the diagram. -/
def DescendsAlongAffineLimits (D : ModuleMapSituation.{u, m} B S hS)
    (Q : D.SchemesOver → Prop) : Prop :=
  ∀ (I : Type (max w w')) [Category.{w'} I] [IsCofiltered I] (E : I ⥤ D.SchemesOver)
    (c : Cone E), IsLimit (D.testScheme.mapCone c) →
      (∀ i, IsAffine (D.testScheme.obj (E.obj i))) → IsAffine (D.testScheme.obj c.pt) →
        Q c.pt → ∃ i, Q (E.obj i)

/-! ### Limit preservation of a subterminal locus -/

/-- For a base-change-stable property of test schemes, limit preservation of the associated
subterminal locus is exactly descent of the property along limits of affine test schemes.

The nontrivial half of a colimit is the surjectivity of the canonical map; its injectivity is
automatic because the values of the locus are subsingletons, and the remaining implication is
the base-change stability the locus is built from. -/
theorem limitPreserving_subterminalFunctor_iff (D : ModuleMapSituation.{u, m} B S hS)
    (Q : D.SchemesOver → Prop)
    (stable : ∀ {T T' : D.SchemesOver}, (T' ⟶ T) → Q T → Q T') :
    LimitPreserving.{u, u, w, w'} D.testScheme (D.subterminalFunctor Q stable) ↔
      D.DescendsAlongAffineLimits.{u, m, w, w'} Q := by
  have hsub : ∀ X : (D.SchemesOver)ᵒᵖ, Subsingleton ((D.subterminalFunctor Q stable).obj X) :=
    fun _ => ⟨fun a b => Subtype.ext (Subsingleton.elim a.val b.val)⟩
  constructor
  · intro h I _ _ E c hc hE hpt hQ
    obtain ⟨i, hi⟩ := (nonempty_isColimit_mapCocone_op_iff_of_subsingleton
      (D.subterminalFunctor Q stable) E c).mp (h I E c hc hE hpt) ⟨⟨PUnit.unit, hQ⟩⟩
    exact ⟨i, hi.some.2⟩
  · intro h I _ _ E c hc hE hpt
    refine (nonempty_isColimit_mapCocone_op_iff_of_subsingleton
      (D.subterminalFunctor Q stable) E c).mpr fun hne => ?_
    obtain ⟨i, hi⟩ := h I E c hc hE hpt hne.some.2
    exact ⟨i, ⟨⟨PUnit.unit, hi⟩⟩⟩

variable (D : ModuleMapSituation.{u, m} B S hS) (P : ModulePullbackSystem.{u, m} B S hS)

/-- Limit preservation of `F_iso` is descent of "the base change of `u` is an isomorphism". -/
theorem limitPreserving_isoFunctor_iff :
    LimitPreserving.{u, u, w, w'} D.testScheme (D.isoFunctor P) ↔
      D.DescendsAlongAffineLimits.{u, m, w, w'} (D.IsIsoAt P) :=
  D.limitPreserving_subterminalFunctor_iff _ _

/-- Limit preservation of `F_inj` is descent of universal injectivity of the base change. -/
theorem limitPreserving_injFunctor_iff :
    LimitPreserving.{u, u, w, w'} D.testScheme (D.injFunctor P) ↔
      D.DescendsAlongAffineLimits.{u, m, w, w'} (D.IsUniversallyInjectiveAt P) :=
  D.limitPreserving_subterminalFunctor_iff _ _

/-- Limit preservation of `F_surj` is descent of surjectivity of the base change. -/
theorem limitPreserving_surjFunctor_iff :
    LimitPreserving.{u, u, w, w'} D.testScheme (D.surjFunctor P) ↔
      D.DescendsAlongAffineLimits.{u, m, w, w'} (D.IsSurjectiveAt P) :=
  D.limitPreserving_subterminalFunctor_iff _ _

/-- Limit preservation of `F_zero` is descent of vanishing of the base change. -/
theorem limitPreserving_zeroFunctor_iff :
    LimitPreserving.{u, u, w, w'} D.testScheme (D.zeroFunctor P) ↔
      D.DescendsAlongAffineLimits.{u, m, w, w'} (D.IsZeroAt P) :=
  D.limitPreserving_subterminalFunctor_iff _ _

/-! ### Clause (3): the isomorphism locus from the surjectivity and injectivity loci -/

/-- An isomorphic base change of `u` is universally injective, since isomorphism persists under
further base change. -/
private theorem isUniversallyInjectiveAt_of_isIsoAt (D : ModuleMapSituation.{u, m} B S hS)
    (P : ModulePullbackSystem.{u, m} B S hS) {T : D.SchemesOver} (h : D.IsIsoAt P T) :
    D.IsUniversallyInjectiveAt P T := fun _ g => by
  have : IsIso (D.baseChangeHom P _) := D.isIsoAt_of_hom P g h
  infer_instance

/-- A base change of `u` that is an epimorphism and a monomorphism is an isomorphism, in a
balanced category of modules. -/
private theorem isIsoAt_of_epi_of_mono (D : ModuleMapSituation.{u, m} B S hS)
    (P : ModulePullbackSystem.{u, m} B S hS) (T : D.SchemesOver)
    [Balanced (Modules.{u, m} B S hS (D.baseChangeSpace T).1 (D.baseChangeSpace T).2)]
    [Epi (D.baseChangeHom P T)] [Mono (D.baseChangeHom P T)] : D.IsIsoAt P T :=
  isIso_of_mono_of_epi _

/-- Descent of the isomorphism locus follows from descent of the surjectivity locus and of the
universal injectivity locus: a base change of `u` is an isomorphism exactly when it is an
epimorphism and a monomorphism, and a cofiltered diagram has a stage below the two stages the
two descents produce. -/
theorem descendsAlongAffineLimits_isIsoAt_of_surj_of_inj
    (D : ModuleMapSituation.{u, m} B S hS) (P : ModulePullbackSystem.{u, m} B S hS)
    (balanced : ∀ T : D.SchemesOver,
      Balanced (Modules.{u, m} B S hS (D.baseChangeSpace T).1 (D.baseChangeSpace T).2))
    (hsurj : D.DescendsAlongAffineLimits.{u, m, w, w'} (D.IsSurjectiveAt P))
    (hinj : D.DescendsAlongAffineLimits.{u, m, w, w'} (D.IsUniversallyInjectiveAt P)) :
    D.DescendsAlongAffineLimits.{u, m, w, w'} (D.IsIsoAt P) := by
  intro I _ _ E c hc hE hpt hiso
  have hc0 : IsIso (D.baseChangeHom P c.pt) := hiso
  obtain ⟨i, hi⟩ := hsurj I E c hc hE hpt (by
    change Epi (D.baseChangeHom P c.pt)
    infer_instance)
  obtain ⟨j, hj⟩ := hinj I E c hc hE hpt (D.isUniversallyInjectiveAt_of_isIsoAt P hiso)
  refine ⟨IsCofiltered.min i j, ?_⟩
  have hepi : Epi (D.baseChangeHom P (E.obj (IsCofiltered.min i j))) :=
    D.isSurjectiveAt_of_hom P (E.map (IsCofiltered.minToLeft i j)) hi
  have hmono : Mono (D.baseChangeHom P (E.obj (IsCofiltered.min i j))) :=
    D.isUniversallyInjectiveAt_of_hom P (E.map (IsCofiltered.minToRight i j)) hj _ (𝟙 _)
  have := balanced (E.obj (IsCofiltered.min i j))
  exact D.isIsoAt_of_epi_of_mono P _

/-- The isomorphism locus `F_iso` is limit preserving once the surjectivity locus `F_surj` and
the universal injectivity locus `F_inj` are, in a balanced category of modules. -/
theorem limitPreserving_isoFunctor_of_surj_of_inj_of_balanced
    (D : ModuleMapSituation.{u, m} B S hS) (P : ModulePullbackSystem.{u, m} B S hS)
    (balanced : ∀ T : D.SchemesOver,
      Balanced (Modules.{u, m} B S hS (D.baseChangeSpace T).1 (D.baseChangeSpace T).2))
    (hsurj : LimitPreserving.{u, u, w, w'} D.testScheme (D.surjFunctor P))
    (hinj : LimitPreserving.{u, u, w, w'} D.testScheme (D.injFunctor P)) :
    LimitPreserving.{u, u, w, w'} D.testScheme (D.isoFunctor P) :=
  (D.limitPreserving_isoFunctor_iff P).mpr
    (descendsAlongAffineLimits_isIsoAt_of_surj_of_inj D P balanced
      ((D.limitPreserving_surjFunctor_iff P).mp hsurj)
      ((D.limitPreserving_injFunctor_iff P).mp hinj))

/-- **Stacks 083J, clause (3), reduced.**  The isomorphism locus `F_iso` is limit preserving
once the surjectivity locus `F_surj` and the universal injectivity locus `F_inj` are.

The source deduces clause (3) from clauses (1) and (2) through the kernel of `u_{T_0}`; this is
the balanced-category route, available because the categories of `𝒪`-modules at hand are
abelian, hence balanced.  It needs no finiteness hypothesis at all.  What is carried is limit
preservation of `F_surj` — clause (1) — and of `F_inj`.

**`hinj` is not supplied by Stacks 083J.**  The tag's three clauses are about `F_surj`, `F_zero`
and `F_iso`; limit preservation of `F_inj` is asserted by none of them, so this is a reduction of
clause (3) to a statement the source does not prove.  Worse for its usefulness, by
`AlgebraicGeometry.Space.ModuleMapSituation.injFunctor_eq_isoFunctor_of_epi` the two functors
`F_inj` and `F_iso` coincide as soon as `u` is an epimorphism, so on the situations the source's
own proof of clause (3) reduces to — those where clause (1) has produced a stage with `u`
surjective — `hinj` is verbatim this theorem's conclusion and `hsurj` holds for free.  Neither
carry follows from the conclusion in general, so the statement is not circular; but clause (3) is
a theorem with nothing carried,
`AlgebraicGeometry.Space.ModuleMapSituation.limitPreserving_isoFunctor` in
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleMapLociLimitPreservingUnconditional.lean`, by the
source's own route — `limitPreserving_isoFunctor_iff_kernelSituation` at the stage clause (1)
provides, with Stacks 082T for finite type of the kernel there.  Prefer that.  This statement is
kept because it asks for no finiteness at all. -/
@[stacks 083J "clause (3), reduced to clause (1) and limit preservation of F_inj; both carried"]
theorem limitPreserving_isoFunctor_of_surj_of_inj
    (D : ModuleMapSituation.{u, u} B S hS) (P : ModulePullbackSystem.{u, u} B S hS)
    (hsurj : LimitPreserving.{u, u, w, w'} D.testScheme (D.surjFunctor P))
    (hinj : LimitPreserving.{u, u, w, w'} D.testScheme (D.injFunctor P)) :
    LimitPreserving.{u, u, w, w'} D.testScheme (D.isoFunctor P) :=
  limitPreserving_isoFunctor_of_surj_of_inj_of_balanced D P (fun _ => inferInstance) hsurj hinj

/-- **For a surjective `u`, universal injectivity at a test scheme *is* being an isomorphism
there.**  Every base change of an epimorphism is an epimorphism, so in the balanced category of
modules over the base-change space the base change of `u` is an isomorphism exactly when it is a
monomorphism; and being an isomorphism is stable under further base change, so that single
monomorphism condition is already universal injectivity.

This is a measurement of the reduction above, not an input to it.  On the situations whose `u` is
an epimorphism — which is where the source's own proof of clause (3) lands, after using clause (1)
to find a stage at which `u` is surjective — the hypothesis `hinj` of
`AlgebraicGeometry.Space.ModuleMapSituation.limitPreserving_isoFunctor_of_surj_of_inj` is
*verbatim its own conclusion* (by `injFunctor_eq_isoFunctor_of_epi` below), and `hsurj` is free.
The balanced-category reduction therefore has content only at situations whose `u` is not
surjective. -/
theorem isUniversallyInjectiveAt_iff_isIsoAt_of_epi (D : ModuleMapSituation.{u, u} B S hS)
    (P : ModulePullbackSystem.{u, u} B S hS) [Epi D.u] (T : D.SchemesOver) :
    D.IsUniversallyInjectiveAt P T ↔ D.IsIsoAt P T := by
  have := P.preservesEpimorphisms (D.baseChangeProjection T)
  have hepi : Epi (D.baseChangeHom P T) := by
    change Epi ((P.functor (D.baseChangeProjection T)).map D.u)
    infer_instance
  refine ⟨fun h => ?_, fun h T' g => ?_⟩
  · have : Mono (D.baseChangeHom P T) := h T (𝟙 T)
    exact D.isIsoAt_of_epi_of_mono P T
  · exact D.isUniversallyInjectiveAt_of_isIsoAt P h T' g

/-- **For a surjective `u` the universal injectivity locus `F_inj` and the isomorphism locus
`F_iso` are the same subterminal functor**, by
`AlgebraicGeometry.Space.ModuleMapSituation.isUniversallyInjectiveAt_iff_isIsoAt_of_epi`. -/
theorem injFunctor_eq_isoFunctor_of_epi (D : ModuleMapSituation.{u, u} B S hS)
    (P : ModulePullbackSystem.{u, u} B S hS) [Epi D.u] :
    D.injFunctor P = D.isoFunctor P :=
  subterminalFunctor_congr D
    (fun g h => D.isUniversallyInjectiveAt_of_hom P g h)
    (fun g h => D.isIsoAt_of_hom P g h)
    (funext fun T => propext (D.isUniversallyInjectiveAt_iff_isIsoAt_of_epi P T))

/-! ### Clause (1): the surjectivity locus as the vanishing locus of a cokernel -/

section Cokernel

variable (D : ModuleMapSituation.{u, u} B S hS)

/-- The cokernel of the map of modules of a situation of Stacks 083F is quasi-coherent. -/
theorem isQuasicoherentOnSite_cokernel_u : (cokernel D.u).IsQuasicoherentOnSite :=
  @isQuasicoherentOnSite_cokernel_unconditional B S hS D.X.1 D.X.2 D.F D.G
    D.quasicoherent_F D.quasicoherent_G D.u

/-- **The cokernel of `u`, read as a situation of Stacks 083F.**  Its source module is the
target module `𝒢` of the given situation and its map is the cokernel projection `𝒢 ⟶ coker u`;
the cokernel is quasi-coherent by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_unconditional`. -/
def cokernelSituation : ModuleMapSituation.{u, u} B S hS :=
  D.secondMap (cokernel D.u) D.isQuasicoherentOnSite_cokernel_u (cokernel.π D.u)

@[simp]
theorem cokernelSituation_X : (D.cokernelSituation).X = D.X := rfl

@[simp]
theorem cokernelSituation_Y : (D.cokernelSituation).Y = D.Y := rfl

@[simp]
theorem cokernelSituation_f : (D.cokernelSituation).f = D.f := rfl

@[simp]
theorem cokernelSituation_F : (D.cokernelSituation).F = D.G := rfl

@[simp]
theorem cokernelSituation_u : (D.cokernelSituation).u = cokernel.π D.u := rfl

@[simp]
theorem cokernelSituation_testScheme : (D.cokernelSituation).testScheme = D.testScheme := rfl

/-- The base change of `u` to a test scheme is an epimorphism exactly when the base change of
the cokernel projection of `u` vanishes.

Forward: the composite of the two base-changed maps is the base change of `u ≫ cokernel.π u`,
hence zero, and an epimorphism can be cancelled.  Backward: the pullback of modules is a left
adjoint, hence preserves the cokernel, so the base change of `cokernel.π u` is the cokernel
projection of the base-changed map up to the comparison isomorphism, and a map whose cokernel
projection vanishes is an epimorphism. -/
private theorem epi_modulePullback_map_iff_map_cokernelπ_eq_zero (T : D.SchemesOver) :
    Epi ((modulePullback B S hS (D.baseChangeProjection T)).map D.u) ↔
      (modulePullback B S hS (D.baseChangeProjection T)).map (cokernel.π D.u) = 0 := by
  have hadj := modulePullbackAdjunction B S hS (D.baseChangeProjection T)
  have := hadj.isLeftAdjoint
  have : PreservesColimitsOfSize.{0, 0}
      (modulePullback B S hS (D.baseChangeProjection T)) :=
    hadj.leftAdjoint_preservesColimits
  have hcomp : (modulePullback B S hS (D.baseChangeProjection T)).map D.u ≫
      (modulePullback B S hS (D.baseChangeProjection T)).map (cokernel.π D.u) = 0 := by
    rw [← Functor.map_comp, cokernel.condition, Functor.map_zero]
  constructor
  · intro h
    exact (cancel_epi ((modulePullback B S hS (D.baseChangeProjection T)).map D.u)).mp
      (by rw [comp_zero]; exact hcomp)
  · intro hv
    refine Preadditive.epi_of_cokernel_zero ?_
    rw [← PreservesCokernel.π_iso_hom
      (modulePullback B S hS (D.baseChangeProjection T)) D.u, hv, zero_comp]

/-- The surjectivity locus of the first map and the vanishing locus of the second map of a
sequence of quasi-coherent modules are read off the same pullback functor, so the pointwise
comparison of the two conditions is literally a comparison of the pulled-back maps. -/
private lemma isSurjectiveAt_iff_secondMap_isZeroAt_of
    (D : ModuleMapSituation.{u, m} B S hS) (P : ModulePullbackSystem.{u, m} B S hS)
    (H : Modules.{u, m} B S hS D.X.1 D.X.2) (hH : H.IsQuasicoherentOnSite) (v : D.G ⟶ H)
    (T : D.SchemesOver)
    (h : Epi ((P.functor (D.baseChangeProjection T)).map D.u) ↔
      (P.functor (D.baseChangeProjection T)).map v = 0) :
    D.IsSurjectiveAt P T ↔ (D.secondMap H hH v).IsZeroAt P T :=
  h

/-- **At a test scheme, the base change of `u` is surjective exactly when the base change of the
cokernel situation's map vanishes.**  This is the pointwise form of the reduction of clause (1)
of Stacks 083J to its clause (2). -/
theorem isSurjectiveAt_iff_cokernelSituation_isZeroAt (T : D.SchemesOver) :
    D.IsSurjectiveAt (modulePullbackSystem B S hS) T ↔
      (D.cokernelSituation).IsZeroAt (modulePullbackSystem B S hS) T :=
  isSurjectiveAt_iff_secondMap_isZeroAt_of D (modulePullbackSystem B S hS) (cokernel D.u)
    D.isQuasicoherentOnSite_cokernel_u (cokernel.π D.u) T
    (D.epi_modulePullback_map_iff_map_cokernelπ_eq_zero T)

/-- **The surjectivity locus of `u` is the vanishing locus of the cokernel situation**, as
subterminal functors on the schemes over `Y`. -/
theorem surjFunctor_eq_cokernelSituation_zeroFunctor :
    D.surjFunctor (modulePullbackSystem B S hS) =
      (D.cokernelSituation).zeroFunctor (modulePullbackSystem B S hS) :=
  subterminalFunctor_congr D
    (fun g h => D.isSurjectiveAt_of_hom (modulePullbackSystem B S hS) g h)
    (fun g h => (D.cokernelSituation).isZeroAt_of_hom (modulePullbackSystem B S hS) g h)
    (funext fun T => propext (D.isSurjectiveAt_iff_cokernelSituation_isZeroAt T))

/-- **Stacks 083J, clause (1), reduced to clause (2).**  The surjectivity locus `F_surj` of `u`
is limit preserving exactly when the vanishing locus `F_zero` of the cokernel situation is.

The hypotheses of the two clauses match on the nose: the source module of the cokernel situation
is `𝒢` (`cokernelSituation_F`), so clause (1)'s hypothesis that `𝒢` be of finite type with
quasi-compact scheme-theoretic support over `B` *is* clause (2)'s hypothesis on the source
module of the cokernel situation, and the two situations have the same test category and the
same underlying-scheme functor (`cokernelSituation_testScheme`).  What is carried is clause (2)
itself — and clause (2) is now a theorem, so clause (1) is available outright as
`AlgebraicGeometry.Space.ModuleMapSituation.limitPreserving_surjFunctor` in
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleMapLociLimitPreservingUnconditional.lean`.  This
equivalence is the whole of that proof; it is stated here because it needs nothing of
clause (2). -/
@[stacks 083J "clause (1), reduced to clause (2) for the cokernel situation; (2) is carried"]
theorem limitPreserving_surjFunctor_iff_cokernelSituation :
    LimitPreserving.{u, u, w, w'} D.testScheme (D.surjFunctor (modulePullbackSystem B S hS)) ↔
      LimitPreserving.{u, u, w, w'} D.testScheme
        ((D.cokernelSituation).zeroFunctor (modulePullbackSystem B S hS)) := by
  rw [D.surjFunctor_eq_cokernelSituation_zeroFunctor]

end Cokernel

/-! ### Clause (3) for a surjective map: the isomorphism locus as a vanishing locus -/

section Kernel

variable (D : ModuleMapSituation.{u, u} B S hS)

/-- The kernel of the map of modules of a situation of Stacks 083F is quasi-coherent, by the
kernel clause of Stacks 03M1 (3) on the small étale site of the source space. -/
theorem isQuasicoherentOnSite_kernel_u : (kernel D.u).IsQuasicoherentOnSite :=
  @isQuasicoherentOnSite_kernel_of_isCartesian B S hS D.X.1 D.X.2 D.F D.G D.u
    (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS D.X.1 D.X.2)
    D.quasicoherent_F D.quasicoherent_G

/-- **The kernel of `u`, read as a situation of Stacks 083F.**  Its source module is the kernel
of `u`, its target module is the source module `ℱ` of the given situation, and its map is the
kernel inclusion `ker u ⟶ ℱ`; the kernel is quasi-coherent by
`AlgebraicGeometry.Space.ModuleMapSituation.isQuasicoherentOnSite_kernel_u`.

This is the situation the source's proof of clause (3) of Stacks 083J forms, there over a single
affine stage `T₀` of the given limit at which `u` has been made surjective. -/
def kernelSituation : ModuleMapSituation.{u, u} B S hS where
  X := D.X
  Y := D.Y
  f := D.f
  F := kernel D.u
  G := D.F
  quasicoherent_F := D.isQuasicoherentOnSite_kernel_u
  quasicoherent_G := D.quasicoherent_F
  u := kernel.ι D.u

@[simp]
theorem kernelSituation_X : (D.kernelSituation).X = D.X := rfl

@[simp]
theorem kernelSituation_Y : (D.kernelSituation).Y = D.Y := rfl

@[simp]
theorem kernelSituation_f : (D.kernelSituation).f = D.f := rfl

@[simp]
theorem kernelSituation_F : (D.kernelSituation).F = kernel D.u := rfl

@[simp]
theorem kernelSituation_G : (D.kernelSituation).G = D.F := rfl

@[simp]
theorem kernelSituation_u : (D.kernelSituation).u = kernel.ι D.u := rfl

@[simp]
theorem kernelSituation_testScheme : (D.kernelSituation).testScheme = D.testScheme := rfl

/-- The given situation *is* the second map of its own kernel situation, on the nose. -/
theorem secondMap_kernelSituation :
    (D.kernelSituation).secondMap D.G D.quasicoherent_G D.u = D := rfl

/-- **At a test scheme, the base change of a surjective `u` is an isomorphism exactly when the
base change of the kernel situation's map vanishes.**  This is Stacks 0CVM,
`AlgebraicGeometry.Space.ModuleMapSituation.isIsoAt_secondMap_iff_isZeroAt`, applied to the
exact sequence `ker u ⟶ ℱ ⟶ 𝒢 ⟶ 0`. -/
theorem isIsoAt_iff_kernelSituation_isZeroAt [hu : Epi D.u] (T : D.SchemesOver) :
    D.IsIsoAt (modulePullbackSystem B S hS) T ↔
      (D.kernelSituation).IsZeroAt (modulePullbackSystem B S hS) T :=
  @isIsoAt_secondMap_iff_isZeroAt B S hS D.kernelSituation D.G D.quasicoherent_G D.u
    (kernel.condition D.u) (ShortComplex.exact_kernel D.u) hu T

/-- **The isomorphism locus of a surjective `u` is the vanishing locus of the kernel
situation**, as subterminal functors on the schemes over `Y`. -/
theorem isoFunctor_eq_kernelSituation_zeroFunctor [hu : Epi D.u] :
    D.isoFunctor (modulePullbackSystem B S hS) =
      (D.kernelSituation).zeroFunctor (modulePullbackSystem B S hS) :=
  @isoFunctor_secondMap_eq_zeroFunctor B S hS D.kernelSituation D.G D.quasicoherent_G D.u
    (kernel.condition D.u) (ShortComplex.exact_kernel D.u) hu

/-- **Clause (3) of Stacks 083J for a surjective `u`, reduced to clause (2) for the kernel
situation.**  The isomorphism locus `F_iso` of an epimorphism `u` is limit preserving exactly
when the vanishing locus `F_zero` of its kernel situation is.

This is the clause-(3) counterpart of
`AlgebraicGeometry.Space.ModuleMapSituation.limitPreserving_surjFunctor_iff_cokernelSituation`,
and it is the reduction the *source* performs: it deduces clause (3) from clauses (1) and (2) by
forming `𝒦 = Ker(u_{T₀})` at a stage where clause (1) has made `u` surjective and applying
clause (2) to `𝒦 ⟶ ℱ_{T₀}`.  Here that is done for the whole situation rather than over a
stage, which is why `u` itself is asked to be an epimorphism; the passage to a stage needs the
base change of a situation along a test scheme, which lives above this file.

Unlike
`AlgebraicGeometry.Space.ModuleMapSituation.limitPreserving_isoFunctor_of_surj_of_inj`, nothing
here is carried, and nothing outside Stacks 083J is appealed to: limit preservation of `F_inj`,
which that theorem carries, is not asserted by any clause of Stacks 083J.

**No `@[stacks 083J]` attribute is claimed.**  This is clause (3) only for a surjective `u`, so
it is a reduction towards the clause and not the clause; the registered statement of clause (3)
remains `limitPreserving_isoFunctor_of_surj_of_inj`. -/
theorem limitPreserving_isoFunctor_iff_kernelSituation [Epi D.u] :
    LimitPreserving.{u, u, w, w'} D.testScheme (D.isoFunctor (modulePullbackSystem B S hS)) ↔
      LimitPreserving.{u, u, w, w'} D.testScheme
        ((D.kernelSituation).zeroFunctor (modulePullbackSystem B S hS)) := by
  rw [D.isoFunctor_eq_kernelSituation_zeroFunctor]

end Kernel

end ModuleMapSituation

end AlgebraicGeometry.Space

end
