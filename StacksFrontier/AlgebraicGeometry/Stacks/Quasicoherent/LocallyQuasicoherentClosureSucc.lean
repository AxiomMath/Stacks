module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleQuasicoherentUniverse
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentAbelianUnivLE
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageSmoothLocalCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentGrothendieck

/-!
# Locally quasi-coherent modules form a weak Serre subcategory at section universe `u + 1`

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids whose objects lie in
`Type (u + 1)` and whose morphisms lie in `Type u`, the seating of the algebraic stacks of the
criterion of Stacks 076Z. This file proves parts (2) and (3) of **Stacks 06WM** for the étale
sheaves of `𝒪_𝒳`-modules with sections in `Type (u + 1)`, the section universe at which the
higher direct images live: local quasi-coherence (Stacks 06WJ) is closed under kernels,
cokernels and extensions, so that it cuts out a weak Serre subcategory, and that is the local
quasi-coherence half of hypothesis (1) of Stacks 076Z for the rule `LQCoh^fbc` of Stacks 0765.

The argument is the one at section universe `u`: the restriction to the small étale site of the
scheme below an object is exact, and on a small étale site quasi-coherence at section universe
`u + 1` is closed under kernels, cokernels and extensions (Stacks 0GNB).

## Main results

* `AlgebraicGeometry.Stack.isClosedUnderKernels_isLocallyQuasicoherent_succ`,
  `AlgebraicGeometry.Stack.isClosedUnderCokernels_isLocallyQuasicoherent_succ_of_category` and
  `AlgebraicGeometry.Stack.isLocallyQuasicoherent_X₂_of_shortExact_succ`: local quasi-coherence at
  section universe `u + 1` is closed under kernels, cokernels and extensions.
* `AlgebraicGeometry.Stack.isWeakSerreClass_isLocallyQuasicoherent_succ_of_category`: **local
  quasi-coherence cuts out a weak Serre subcategory of the étale sheaves of modules at section
  universe `u + 1`.**
* `AlgebraicGeometry.Stack.isWeakSerre_locallyQuasicoherentRule`: hypothesis (1) of Stacks 076Z
  for the rule of local quasi-coherence.

## References

* [Stacks Project, Tag 06WM](https://stacks.math.columbia.edu/tag/06WM)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 076Z](https://stacks.math.columbia.edu/tag/076Z)
* [Stacks Project, Tag 0GNB](https://stacks.math.columbia.edu/tag/0GNB)
-/

@[expose] public section

-- The ambient-universe instances on sheaves of modules state their module universe as a `max`
-- pattern which the module universe `u + 1` below does not match syntactically.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives
  Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_isGrothendieckAbelian
  Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory

open CategoryTheory CategoryTheory.Limits

universe u t

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- The restriction of a locally quasi-coherent sheaf to the small étale site below any object
is quasi-coherent. -/
private theorem isQuasicoherentOnSite_restrictSheafToSmallEtale_obj
    {B : BigFppfSite.{u}} {E : BigEtaleSite.{u}} {h : E.cutoff = B.cutoff} {S : Scheme.{u}}
    {hS : B.Contains S} {𝒳 : Type (u + 1)} [Category.{u} 𝒳] {p : 𝒳 ⥤ BigFppfOver B S hS}
    {hp : p.IsFiberedInGroupoids}
    {F : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS p hp
      (etaleTopology B) (etaleTopology_le_topology B))}
    (hF : IsLocallyQuasicoherent B E h S hS p hp F.val) (x : 𝒳) :
    ((restrictSheafToSmallEtale.{u, u + 1, u, u + 1} B E h S hS p hp x).obj
      F).IsQuasicoherentOnSite :=
  (isLocallyQuasicoherent_iff B E h S hS p hp _).1 hF x

/-- **Local quasi-coherence at section universe `u + 1` is closed under kernels.** -/
theorem isClosedUnderKernels_isLocallyQuasicoherent_succ :
    (isLocallyQuasicoherent.{u, u + 1, u, u + 1} B E h S hS p hp).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, hF, hG⟩
    refine (isLocallyQuasicoherent_iff B E h S hS p hp _).2 fun x ↦ ?_
    let r := restrictSheafToSmallEtale.{u, u + 1, u, u + 1} B E h S hS p hp x
    have := SmallEtale.isClosedUnderKernels_isQuasicoherentOnSite_succ E (p.obj x).left.1
      (contains_base B E h S hS p x)
    exact (SheafOfModules.isQuasicoherentOnSite _).prop_of_isLimit_kernelFork
      ((KernelFork.isLimitMapConeEquiv k r) (isLimitOfPreserves r hk))
      (isQuasicoherentOnSite_restrictSheafToSmallEtale_obj hF x)
      (isQuasicoherentOnSite_restrictSheafToSmallEtale_obj hG x)

/-- **Local quasi-coherence at section universe `u + 1` is closed under cokernels.** -/
theorem isClosedUnderCokernels_isLocallyQuasicoherent_succ_of_category :
    (isLocallyQuasicoherent.{u, u + 1, u, u + 1} B E h S hS p hp).IsClosedUnderCokernels where
  cokernels_le := by
    let := hasSheafify_associatedTopology_of_category_succ B S hS p
    let := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS p
    rintro _ ⟨f, k, hk, hF, hG⟩
    refine (isLocallyQuasicoherent_iff B E h S hS p hp _).2 fun x ↦ ?_
    let r := restrictSheafToSmallEtale.{u, u + 1, u, u + 1} B E h S hS p hp x
    have := SmallEtale.isClosedUnderCokernels_isQuasicoherentOnSite_succ E (p.obj x).left.1
      (contains_base B E h S hS p x)
    exact (SheafOfModules.isQuasicoherentOnSite _).prop_of_isColimit_cokernelCofork
      ((CokernelCofork.isColimitMapCoconeEquiv k r) (isColimitOfPreserves r hk))
      (isQuasicoherentOnSite_restrictSheafToSmallEtale_obj hF x)
      (isQuasicoherentOnSite_restrictSheafToSmallEtale_obj hG x)

/-- **Stacks 06WM (3), the extension, at section universe `u + 1`.** In a short exact sequence
of étale sheaves of modules on `𝒳` with sections in `Type (u + 1)`, if the outer terms are
locally quasi-coherent so is the middle term. -/
theorem isLocallyQuasicoherent_X₂_of_shortExact_succ
    {Sc : ShortComplex (SheafOfModules.{u + 1} (ringStructureSheafCore B S hS p hp
      (etaleTopology B) (etaleTopology_le_topology B)))}
    (hSc : Sc.ShortExact) (h₁ : IsLocallyQuasicoherent B E h S hS p hp Sc.X₁.val)
    (h₃ : IsLocallyQuasicoherent B E h S hS p hp Sc.X₃.val) :
    IsLocallyQuasicoherent B E h S hS p hp Sc.X₂.val := by
  let := hasSheafify_associatedTopology_of_category_succ B S hS p
  let := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS p
  refine (isLocallyQuasicoherent_iff B E h S hS p hp _).2 fun x ↦ ?_
  let r := restrictSheafToSmallEtale.{u, u + 1, u, u + 1} B E h S hS p hp x
  have : r.PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
  exact SmallEtale.isQuasicoherentOnSite_X₂_of_shortExact_succ E (p.obj x).left.1
    (contains_base B E h S hS p x) (hSc.map_of_exact r)
    (isQuasicoherentOnSite_restrictSheafToSmallEtale_obj h₁ x)
    (isQuasicoherentOnSite_restrictSheafToSmallEtale_obj h₃ x)

/-- Local quasi-coherence at section universe `u + 1` contains a zero object. -/
theorem containsZero_isLocallyQuasicoherent_succ_of_category :
    (isLocallyQuasicoherent.{u, u + 1, u, u + 1} B E h S hS p hp).ContainsZero := by
  let := hasSheafify_associatedTopology_of_category_succ B S hS p
  let := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS p
  refine ⟨⊤_ _, terminalIsTerminal.isZero, ?_⟩
  refine (isLocallyQuasicoherent_iff B E h S hS p hp _).2 fun x ↦ ?_
  let r := restrictSheafToSmallEtale.{u, u + 1, u, u + 1} B E h S hS p hp x
  have : r.PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
  exact SheafOfModules.IsQuasicoherentOnSite.of_isZero (r.map_isZero terminalIsTerminal.isZero)

/-- **Stacks 06WM (2) and (3), at section universe `u + 1`.** The locally quasi-coherent étale
sheaves of `𝒪_𝒳`-modules with sections in `Type (u + 1)` form a weak Serre subcategory of all
étale sheaves of `𝒪_𝒳`-modules, in the form of Stacks 0754: they contain a zero object and are
closed under isomorphisms, kernels, cokernels and extensions. -/
theorem isWeakSerreClass_isLocallyQuasicoherent_succ_of_category :
    letI := hasSheafify_associatedTopology_of_category_succ B S hS p
    letI := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS p
    (isLocallyQuasicoherent.{u, u + 1, u, u + 1} B E h S hS p hp).IsWeakSerreClass := by
  let := hasSheafify_associatedTopology_of_category_succ B S hS p
  let := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS p
  have := containsZero_isLocallyQuasicoherent_succ_of_category B E h S hS p hp
  have := isClosedUnderKernels_isLocallyQuasicoherent_succ B E h S hS p hp
  have := isClosedUnderCokernels_isLocallyQuasicoherent_succ_of_category B E h S hS p hp
  have : (isLocallyQuasicoherent.{u, u + 1, u, u + 1} B E h S hS p hp).IsClosedUnderIsomorphisms :=
    ⟨fun {F G} e hF ↦ (isLocallyQuasicoherent_iff B E h S hS p hp G).2 fun x ↦
      SheafOfModules.IsQuasicoherentOnSite.of_iso
        ((restrictSheafToSmallEtale.{u, u + 1, u, u + 1} B E h S hS p hp x).mapIso e)
        (isQuasicoherentOnSite_restrictSheafToSmallEtale_obj hF x)⟩
  have : (isLocallyQuasicoherent.{u, u + 1, u, u + 1} B E h S hS p hp).IsClosedUnderExtensions :=
    ⟨fun hT h₁ h₃ ↦ isLocallyQuasicoherent_X₂_of_shortExact_succ B E h S hS p hp hT h₁ h₃⟩
  exact {}

/-- **Hypothesis (1) of Stacks 076Z for the rule of local quasi-coherence**: on every algebraic
stack, the locally quasi-coherent étale sheaves of modules (with sections in `Type (u + 1)`) form
a weak Serre subcategory. This is parts (2) and (3) of Stacks 06WM. -/
theorem isWeakSerre_locallyQuasicoherentRule :
    StackEtaleModuleRule.IsWeakSerre.{u, t} B S hS (locallyQuasicoherentRule B E h S hS) :=
  fun 𝒳 ↦ isWeakSerreClass_isLocallyQuasicoherent_succ_of_category B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids

end AlgebraicGeometry.Stack

end
