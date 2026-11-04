module

public import StacksFrontier.Algebra.Homology.DerivedCategory.AdjointAcyclicObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedAdjunction
import StacksCore.Tactic.StacksAttribute

/-!
# The acyclicity statement of Stacks 07AC for modules, from the vanishing of Stacks 0D6X

Let `u : C ⥤ D` be a continuous and cocontinuous functor of sites, let `O_D` be a sheaf of rings
on `D` and let `O_C = g^{-1} O_D` be its restriction along `u`. The existence of the unbounded
left derived functor `Lg_! : D(O_C) ⥤ D(O_D)` is reduced by
`Stacks.Cohomology.DerivedLowerShriek.hasPointwiseLeftDerivedLowerShriek_of_acyclic` to a single
statement about complexes: that `g_!` carries a bounded above acyclic complex whose terms are
direct sums of the extensions by zero `j_{U!} O_U` to an acyclic complex. That is the hypothesis
of the criterion of Stacks 0794 at the generating class, and it is the one input of Stacks 07AC
for modules that the library leaves open.

This file removes the statement about complexes. It shows that the acyclicity statement follows
from an *object-level* vanishing — `Ext^n(j_{U!} O_U, g^* I) = 0` for `n ≥ 1`, every object `U`
of `C` and every injective `O_D`-module `I` — which is Stacks 0D6X. So after this file Stacks
07AC for modules rests on an `Ext` computation over the objects of the site and on nothing about
complexes, exactly as
`Stacks.Cohomology.DerivedLowerShriek.abelianLowerShriekAcyclic_of_ext_vanishing` arranges on
the abelian side.

## Main definitions

* `Stacks.Cohomology.DerivedLowerShriek.LowerShriekAcyclic`: the acyclicity statement of
  Stacks 07AC for sheaves of modules, named. It is the hypothesis `hFP` of
  `hasPointwiseLeftDerivedLowerShriek_of_acyclic` and of
  `hasPointwiseLeftDerivedLowerShriek_of_acyclic_univLE`, written out.

## Main results

* `Stacks.Cohomology.DerivedLowerShriek.lowerShriekAcyclic_of_ext_vanishing`: the acyclicity
  statement follows from the object-level vanishing of Stacks 0D6X.
* `Stacks.Cohomology.DerivedLowerShriek.lowerShriekAcyclic_of_preservesFiniteLimits`: the
  acyclicity statement is automatic when lower shriek on modules is exact.

## Implementation notes

The reduction is `CategoryTheory.Adjunction.map_acyclic_of_extAcyclic` for the adjunction
`g_! ⊣ g^*` of `Stacks.Cohomology.DerivedLowerShriek.adjunctionModules`. The hypothesis says
exactly that each generator `j_{U!} O_U` is `Ext`-acyclic for that adjunction; the class of
`Ext`-acyclic objects is closed under the arbitrary direct sums out of which the terms of such a
complex are built (`CategoryTheory.Adjunction.extAcyclic_coproduct`), and `Ext`-acyclicity
transports along the isomorphism that exhibits a term as such a sum
(`CategoryTheory.Adjunction.extAcyclic_of_iso`). Nothing about the site or about lower shriek is
used beyond the adjunction, its additivity and its right exactness, all of which are already
available unconditionally.

Why the vanishing is Stacks 0D6X. Morphisms out of `j_{U!} O_U` are the sections over `U`
(Stacks 0G1V, `Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv`), so
`Ext^n(j_{U!} O_U, F)` is the degree `n` cohomology of `F` over `U`; at `F = g^* I` the
vanishing in positive degrees is the Čech computation of Stacks 0D6X, available in this library
as `Stacks.CechSite.injective_module_sheafCohomology_isZero_of_functor` and, in the form of the
cohomology of the underlying abelian sheaf, as
`Stacks.Cohomology.DerivedLowerShriek.vanishesOnObjects_inverseImage`. This file does not perform
the identification of module `Ext` out of `j_{U!} O_U` with that cohomology; it consumes the
vanishing in the `Ext` form in which the reduction needs it.

The universe of the `Ext`-groups is a free parameter `t`, as on the abelian side: `HasExt` is
stated at a universe of its own and no statement here constrains it.

## References

* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
* [Stacks Project, Tag 0G1V](https://stacks.math.columbia.edu/tag/0G1V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t w v₁ u₁ v₂ u₂

namespace Stacks.Cohomology.DerivedLowerShriek

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K] (O : Sheaf K RingCat.{w})
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(SheafOfModules.pushforward.{w} (F := f) (idRingMap J K f O)).IsRightAdjoint]

/-- **The acyclicity statement of Stacks 07AC for sheaves of modules.** Lower shriek carries
every bounded above acyclic complex whose terms are direct sums of the extensions by zero
`j_{U!} O_U` to an acyclic complex. This is the one open input of Stacks 07AC for modules, and
it is the hypothesis `hFP` of
`Stacks.Cohomology.DerivedLowerShriek.hasPointwiseLeftDerivedLowerShriek_of_acyclic`. -/
abbrev LowerShriekAcyclic
    [∀ U : C, (SheafOfModules.pushforward.{w} (F := Over.forget U)
      (𝟙 ((inverseImageRing J K f O).over U) :
        (inverseImageRing J K f O).over U ⟶ (inverseImageRing J K f O).over U)).IsRightAdjoint] :
    Prop :=
  ∀ (a : ℤ) (L : CochainComplex (SheafOfModules.{w} (inverseImageRing J K f O)) ℤ),
    L.IsStrictlyLE a →
    (∀ n, IsSumOfExtensionByZeroUnits (inverseImageRing J K f O) (L.X n)) → L.Acyclic →
    (((lowerShriekModules J K f O).mapHomologicalComplex (ComplexShape.up ℤ)).obj L).Acyclic

omit [f.IsCocontinuous J K] in
/-- **The acyclicity statement is automatic when lower shriek on modules is exact.** An exact
functor preserves the homology of a complex, so it carries an acyclic complex to an acyclic
complex whatever its terms. Lower shriek is always right exact, being a left adjoint; where it
is also left exact — for instance on a site where the criterion of Stacks 04BH applies — Stacks
07AC for modules is unconditional. -/
theorem lowerShriekAcyclic_of_preservesFiniteLimits
    [∀ U : C, (SheafOfModules.pushforward.{w} (F := Over.forget U)
      (𝟙 ((inverseImageRing J K f O).over U) :
        (inverseImageRing J K f O).over U ⟶ (inverseImageRing J K f O).over U)).IsRightAdjoint]
    [PreservesFiniteLimits (lowerShriekModules J K f O)] :
    LowerShriekAcyclic J K f O := by
  intro a L _ _ hL i
  rw [HomologicalComplex.exactAt_iff]
  have h := hL i
  rw [HomologicalComplex.exactAt_iff] at h
  exact h.map (lowerShriekModules J K f O)

/-- **The acyclicity statement of Stacks 07AC for modules follows from the vanishing of Stacks
0D6X.** If `Ext^n(j_{U!} O_U, g^* I) = 0` for every object `U` of the source site, every
injective `O_D`-module `I` and every `n ≥ 1`, then lower shriek carries every bounded above
acyclic complex whose terms are direct sums of the `j_{U!} O_U` to an acyclic complex.

That vanishing is **Stacks 0D6X**: `Ext^n(j_{U!} O_U, F)` is the degree `n` cohomology of `F`
over `U`, by Stacks 0G1V, and the cohomology of the restriction of an injective module vanishes
in positive degrees by the Čech computation of the source. So this reduces the whole of Stacks
07AC for sheaves of modules to an object-level cohomology vanishing, with no statement about
complexes left open.

The reduction is `CategoryTheory.Adjunction.map_acyclic_of_extAcyclic` for the adjunction
`g_! ⊣ g^*`: the hypothesis says exactly that each `j_{U!} O_U` is `Ext`-acyclic for it, the
class of `Ext`-acyclic objects is closed under the direct sums that make up the terms of such a
complex, and `Ext`-acyclicity transports along the isomorphism exhibiting a term as such a
sum. -/
theorem lowerShriekAcyclic_of_ext_vanishing
    [∀ U : C, (SheafOfModules.pushforward.{w} (F := Over.forget U)
      (𝟙 ((inverseImageRing J K f O).over U) :
        (inverseImageRing J K f O).over U ⟶ (inverseImageRing J K f O).over U)).IsRightAdjoint]
    [HasExt.{t} (SheafOfModules.{w} (inverseImageRing J K f O))]
    [EnoughInjectives (SheafOfModules.{w} (inverseImageRing J K f O))]
    [EnoughInjectives (SheafOfModules.{w} O)]
    (hExt : ∀ (U : C) (I : SheafOfModules.{w} O), Injective I → ∀ n : ℕ, 1 ≤ n →
      Subsingleton (Abelian.Ext (extensionByZeroUnit (inverseImageRing J K f O) U)
        ((restrictionModules J K f O).obj I) n)) :
    LowerShriekAcyclic J K f O := by
  intro a L hLE hLP hLac
  have := hLE
  refine (adjunctionModules J K f O).map_acyclic_of_extAcyclic L a hLac fun n => ?_
  obtain ⟨ι, U, ⟨e⟩⟩ := hLP n
  exact (adjunctionModules J K f O).extAcyclic_of_iso e
    ((adjunctionModules J K f O).extAcyclic_coproduct _ fun i => hExt (U i))

end Stacks.Cohomology.DerivedLowerShriek

end
