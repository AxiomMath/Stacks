module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentTopologiesTwo.TopologyIndependence
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleRestrictionFunctorialComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredSiteLocalizationExtensions
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredSiteLocalizationSiteKind
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredSiteLocalizationSiteKindExtensions
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentFromEtaleSite
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentIsLocallyQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SiteEquivalenceAffine

/-!
# Quasi-coherence passes from the inherited fppf topology to a coarser one

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids.  A sheaf of `𝒪_𝒳`-modules which
is quasi-coherent on the inherited fppf site in the sense of Stacks 03DL(6) stays quasi-coherent
when it is read for any one of the four coarser inherited topologies.  That is the **second of
the two inputs of Stacks 0EM8**, `AlgebraicGeometry.FibredSite.QuasicoherentOnSiteOfLeFppf`, and
it is proved with no hypothesis, at the module universe `u` of the schemes and at an arbitrary
pair of universes `𝒳 : Type v`, `Category.{w} 𝒳` for the fibred category, as
`AlgebraicGeometry.FibredSite.quasicoherentOnSiteOfLeFppf_siteKind`.  This file records a second
route to it, through the big site of a scheme, and applies it.

This is the direction the comparison of topoi does not supply: a global presentation is a
cokernel of a map between coproducts of copies of the structure sheaf taken in the category of
*sheaves* of modules, so it depends on the topology, and what carries a presentation from a
coarser topology to a finer one is sheafification, a left adjoint, while the inclusion in the
other direction is a right adjoint and preserves no colimit.  The source supplies the direction
through Descent, Proposition 03DX and Descent, Lemma 03DV, and that is the route recorded below.

## The route through the big site of a scheme

Three steps.

* Stacks 06WI at an arbitrary `AlgebraicGeometry.SiteKind`,
  `AlgebraicGeometry.FibredSite.isQuasicoherentOnSite_iff_forall_objectInverseImageKind'`, reduces
  the statement at `𝒳` to the statement at the big `τ`-site of a scheme: quasi-coherence of a
  sheaf of modules on `𝒳_τ` is quasi-coherence of its inverse images `x^*𝓕` on `(Sch/U)_τ`, one
  object `x` of `𝒳` at a time.
* At the big site of a scheme the statement is
  `AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_restrictTopology`.  A quasi-coherent
  module on `(Sch/U)_fppf` is an `𝓗^a` by the essential-surjectivity half of **Descent,
  Proposition 03DX (1)**, which is a theorem of this development at every base
  (`AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule'`);
  `𝓗^a` read for the coarser topology *is* the associated module of `(Sch/U)_τ` by
  `AlgebraicGeometry.BigFppfOver.restrictTopologyAssociatedModuleIso`, the key to Stacks 0GNE;
  and that is quasi-coherent by **Descent, Lemma 03DV** at `τ`,
  `AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_baseAssociatedModule_of_isQuasicoherent`.
* The two are joined by
  `Stacks.SheafOfModules.comparisonPushforward_reindexEquivalence_inverse`: taking the inverse
  image at an object commutes with reading a module for a coarser topology.  It holds by `rfl`,
  neither functor changing the underlying presheaf of modules, and it is stated for an arbitrary
  equivalence of sites and an arbitrary pair of comparable topologies on each side *because* of
  that: at the concrete sites of `𝒳` the two sides are definitionally equal as well, but the
  kernel cannot check it inside its budget, while the abstract statement it is an instance of
  costs nothing.

## Main results

* `Stacks.SheafOfModules.comparisonPushforward_reindexEquivalence_inverse`: transport along an
  equivalence of sites commutes with reading a sheaf of modules for a coarser topology.
* `AlgebraicGeometry.FibredSite.objectInverseImageKind_comparisonPushforward`: its instance at
  the inverse image at an object of a fibred category.
* `AlgebraicGeometry.Space.restrictionPreservesQuasicoherent`: **`hres` of Stacks 0GQD**, with no
  hypothesis, at the module universe `u`.

## The module universe

The *module* universe is the only one that is pinned.  Everything below holds at
`𝒳 : Type v`, `Category.{w} 𝒳` with `v` and `w` independent of `u`, since
`AlgebraicGeometry.FibredSite.isQuasicoherentOnSite_iff_forall_objectInverseImageKind'` does; only
`AlgebraicGeometry.Space.restrictionPreservesQuasicoherent` at the end of the file is stated at
`𝒳 : Type (u + 1)`, `Category.{u} 𝒳`, the universes of the algebraic space it is about.

Everything below is at the module universe `u` of the schemes, and that is forced, not chosen:
`AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule'`
compares quasi-coherent modules on `(Sch/U)_fppf` with quasi-coherent `𝒪_U`-modules, and the
latter are `AlgebraicGeometry.Scheme.Modules`, which is `SheafOfModules.{u}` with no module
universe parameter at all.  At a module universe `m` strictly above `u` the statement is a
different one and not a consequence of this one: a coproduct of `Type (max (u + 1) m)`-many
copies of the structure sheaf is quasi-coherent there and is not the ulift of any
`SheafOfModules.{u}`, so it is outside the essential image of the associated-module functor as
this development has it.  The two universe-raising transports
`Stacks.SheafOfModules.isQuasicoherentOnSite_uliftForPresentation'` and
`Stacks.SheafOfModules.IsQuasicoherentOnSite.of_uliftForPresentation'` do not bridge the gap:
both speak about `Stacks.SheafOfModules.uliftForPresentation` of a given module, and a module at
the higher universe is not of that form.

That is why the two carriers of Stacks 0GQD,
`AlgebraicGeometry.Space.isEquivalence_quasicoherentRestriction_of_descentInputs` and
`AlgebraicGeometry.Space.nonempty_inv_comp_toSiteModules_iso_projectionModulePullback`, keep
`hres` among their hypotheses: their module universe is `max (u + 1) w m`, which dominates
`u + 1`.  The quasi-inverse `π_X^*` does not force that universe —
`AlgebraicGeometry.Space.isRightAdjoint_moduleRestriction'` asks nothing of it and holds at
`max u m`, hence at `u` — but those carriers also use `hunit`,
`AlgebraicGeometry.Space.isIso_unit_moduleRestriction`, which is proved against the direct image
of sheaves of modules and so needs the module universe to dominate the `Type (u + 1)` the
objects of the small étale site of `X` live in.

## References

* [Stacks Project, Tag 0EM8](https://stacks.math.columbia.edu/tag/0EM8)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 06WK](https://stacks.math.columbia.edu/tag/06WK)
* [Stacks Project, Tag 0GNE](https://stacks.math.columbia.edu/tag/0GNE)
* [Stacks Project, Tag 0GQC](https://stacks.math.columbia.edu/tag/0GQC)
* [Stacks Project, Tag 0GQD](https://stacks.math.columbia.edu/tag/0GQD)
-/

@[expose] public section

open CategoryTheory

namespace Stacks.SheafOfModules

universe w m u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  {J K : GrothendieckTopology C} {J' K' : GrothendieckTopology C'}
  (hK : K ≤ J) (hK' : K' ≤ J')
  (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
  [e.functor.IsContinuous K' K] [e.inverse.IsContinuous K K']
  (R : Sheaf J RingCat.{w})

/-- **Transport along an equivalence of sites commutes with reading a sheaf of modules for a
coarser topology.**  Both `Stacks.SheafOfModules.comparisonPushforward` and the inverse of
`Stacks.SheafOfModules.reindexEquivalence` are restriction along a functor followed by a
transport of scalars along an identity or a counit, and neither depends on the topology except
through the sheaf condition it asserts; sheaf conditions are propositions, so the two composites
are equal rather than merely isomorphic.

Stated for an arbitrary equivalence `e` and arbitrary comparable topologies on each side.  That
generality is what makes it usable: at the sites of a category fibred in groupoids the instance
below is definitionally true as well, but the terms involved are large enough that the kernel
exhausts its budget reducing them, whereas here there is nothing concrete to unfold. -/
theorem comparisonPushforward_reindexEquivalence_inverse
    (M : SheafOfModules.{m} (reindexRing J' e R)) :
    (comparisonPushforward.{u₁, v₁, w, m} hK R).obj
        ((reindexEquivalence.{w, m} e R).inverse.obj M) =
      (reindexEquivalence.{w, m} e (ringOfLe hK R)).inverse.obj
        ((comparisonPushforward.{u₂, v₂, w, m} hK' (reindexRing J' e R)).obj M) :=
  rfl

end Stacks.SheafOfModules

namespace AlgebraicGeometry

universe u v w

namespace FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

/-- Taking the inverse image at an object `x` of `𝒳` commutes with reading a sheaf of modules on
`𝒳` for a coarser inherited topology: the inverse image on `(Sch/U)_τ` of the module read for the
inherited `τ`-topology is the inverse image on `(Sch/U)_fppf` of the module itself, read for the
coarser big topology of `U`.

The instance of `Stacks.SheafOfModules.comparisonPushforward_reindexEquivalence_inverse` at the
equivalence of sites `𝒳_τ/x ≌ (Sch/U)_τ` of
`AlgebraicGeometry.FibredSite.localizationModulesEquivalenceKind'`.  Together with
`AlgebraicGeometry.FibredSite.isQuasicoherentOnSite_iff_forall_objectInverseImageKind'` and
`AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_restrictTopology` it reduces the second
input of Stacks 0EM8 to the big site of a scheme. -/
theorem objectInverseImageKind_comparisonPushforward (τ : SiteKind) (x : 𝒳)
    (N : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf)) :
    objectInverseImageKind' B S hS p hp τ x
        ((Stacks.SheafOfModules.comparisonPushforward
          (BigFppfOver.associatedTopology_le_fppf B S hS p τ)
          (ringStructureSheafCore B S hS p hp .fppf)).obj N) =
      (BigFppfOver.restrictTopology.{u, u} B (baseScheme' B S hS p x)
          (contains_baseScheme' B S hS p x) τ).obj
        (objectInverseImageKind' B S hS p hp .fppf x N) :=
  (Stacks.SheafOfModules.comparisonPushforward_reindexEquivalence_inverse
    (BigFppfOver.baseOverTopology_le_fppf B (baseScheme' B S hS p x)
      (contains_baseScheme' B S hS p x) τ)
    (GrothendieckTopology.le_def.mpr fun Y _ hY =>
      BigFppfOver.associatedTopology_le_fppf B S hS p τ Y.left hY)
    (localizationEquivalence' B S hS p hp x)
    (baseRingStructureSheaf B (baseScheme' B S hS p x)
      (contains_baseScheme' B S hS p x) .fppf) (N.over x)).symm

end FibredSite

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)
  (e : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (X.1 ⋙ typeToCat)).p)

/-- **The hypothesis `hres` of Stacks 0GQD, with no hypothesis**, at the module universe `u` of
the schemes: restriction to the small étale site of the algebraic space `X` representing `𝒳`
carries quasi-coherent modules to quasi-coherent modules.

This is Stacks 0GQC applied to a module quasi-coherent on the inherited fppf site:
`AlgebraicGeometry.Space.restrictionPreservesQuasicoherent_of_forallIsLocallyQuasicoherent` with
its hypothesis supplied by `AlgebraicGeometry.Stack.forallQuasicoherentIsLocallyQuasicoherent`.

**This is not the instance the two carriers of Stacks 0GQD need.**  Their module universe is
`max (u + 1) w m`, which dominates `u + 1`; the module documentation, section "The module
universe", explains why the module universe of the proof cannot be raised. -/
theorem restrictionPreservesQuasicoherent :
    RestrictionPreservesQuasicoherent.{u, u + 1, u, u} B S hS X p hp e :=
  restrictionPreservesQuasicoherent_of_forallIsLocallyQuasicoherent.{u, u + 1, u, u} B S hS X p hp e
    (Stack.forallQuasicoherentIsLocallyQuasicoherent B S hS p hp)

end Space

end AlgebraicGeometry

end
