module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalTypesUnderComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackGlobalPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.SubcategoryUnitLowerShriek
public import StacksFrontier.AlgebraicGeometry.Topologies.GlobalPresentationComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSiteOfPresentation
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# Quasi-coherence of `g_!H` for a full subsite (Stacks 07B0, the presented case)

Let `𝒳` be an algebraic stack and let `g : Sh(𝒳') ⟶ Sh(𝒳)` be the morphism of ringed topoi of
**Stacks 0788** attached to the inclusion of a continuous and cocontinuous full subsite `𝒳'`, with
`g_!` the lower shriek on sheaves of modules of **Stacks 0789**
(`AlgebraicGeometry.Stack.subsiteModuleLowerShriek`). **Stacks 07B0** asserts that `g_!` carries a
quasi-coherent module to a quasi-coherent module, in part (1) for the lisse-étale site and in part
(2) for the flat-fppf site.

This file carries out the step of the source's proof for an `H` that has a global presentation,
given `g_!O_{𝒳'} = O_𝒳` (**Stacks 078A**):

> Since `g_!` commutes with arbitrary colimits (as a left adjoint functor, see Lemma 0789 and
> Categories, Lemma 0038) we conclude that there exists an exact sequence
> `⊕_{j ∈ J} g_!O ⟶ ⊕_{i ∈ I} g_!O ⟶ g_!H ⟶ 0`. Lemma 078A shows that `g_!O = O_𝒳`.

The two parts of **Stacks 07B0** for an arbitrary quasi-coherent `H` are
`AlgebraicGeometry.Stack.LisseEtale.isQuasicoherentClause_fppf_moduleLowerShriek` and
`AlgebraicGeometry.Stack.FlatFppf.isQuasicoherentOnSite_moduleLowerShriek_of_isQuasicoherentOnSite`
in `StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LowerShriekQuasicoherent`, which reduce to
the presented case treated here.

## Main results

* `Stacks.SheafOfModules.hasGlobalPresentation_of_isPresentedByGlobalSections`: a global
  presentation at the universe of the sections is a global presentation in the sense of
  `SheafOfModules.HasGlobalPresentation`, which takes its coproducts and its cokernel after a
  universe lift. This is the step that makes the two notions of **Stacks 03DE** (6) in the library
  comparable on a big site, where the universes genuinely differ.
* `Stacks.SheafOfModules.isQuasicoherentOnSite_of_isPresentedByGlobalSections`: consequently a
  module with a global presentation at the universe of the sections is quasi-coherent on the site.
* `AlgebraicGeometry.Stack.isQuasicoherentOnSite_subsiteModuleLowerShriek`: `g_!H` is
  quasi-coherent for an `H` with a global presentation, stated once for an arbitrary continuous
  and cocontinuous full subsite.
* `AlgebraicGeometry.Stack.LisseEtale.isQuasicoherentOnSite_moduleLowerShriek` and
  `AlgebraicGeometry.Stack.FlatFppf.isQuasicoherentOnSite_moduleLowerShriek`: its two instances.

## Implementation notes

The universe gap the bridge closes is real and is why the source's argument cannot simply be
transcribed. On the site of **Stacks 06TP** of an algebraic stack the objects lie in `Type (u+1)`,
the morphisms and the structure sheaf's sections in `Type u`; so
`SheafOfModules.HasGlobalPresentation`, which is stated at `max u v r m`, asks for coproducts and
a cokernel in `SheafOfModules.{u+1}`, whereas `g_!` is a functor on `SheafOfModules.{u}`. A
presentation therefore cannot be pushed through `g_!` in the universe in which quasi-coherence is
stated. `SheafOfModules.IsPresentedByGlobalSections` is the same condition at the single universe
of the sections, where `g_!` does act, and
`SheafOfModules.preservesColimitsOfSize_uliftForPresentationFunctor'` raises the resulting
presentation afterwards. `SheafOfModules.isPresentedByGlobalSections_iff_hasGlobalPresentation`
does not apply here: it needs the sections to lie in `max u v w`, which on this site they do not.

That `g_!` carries a global presentation to one is
`Stacks.Sheaves.GlobalTypeComparison.isPresentedByGlobalSections_iff`, whose three hypotheses are
discharged here: `g_!` is full and faithful because the unit of `g_! ⊣ g^*` is an isomorphism
(**Stacks 0789**, `AlgebraicGeometry.Stack.isIso_subsiteModuleLowerShriekAdjunction_unit`, which
needs nothing beyond the subsite being continuous and cocontinuous), it preserves colimits because
it is a left adjoint (**Stacks 0038**), and it matches the two structure sheaves by the hypothesis
`g_!O_{𝒳'} = O_𝒳`.

## References

* [Stacks Project, Tag 0038](https://stacks.math.columbia.edu/tag/0038)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
* [Stacks Project, Tag 0789](https://stacks.math.columbia.edu/tag/0789)
* [Stacks Project, Tag 078A](https://stacks.math.columbia.edu/tag/078A)
* [Stacks Project, Tag 07B0](https://stacks.math.columbia.edu/tag/07B0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.RingedToposModules

universe u v w t r

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- **A global presentation at the universe of the sections is a global presentation.** The two
renderings of **Stacks 03DE** (6) in the library differ by a universe lift of the sections:
`SheafOfModules.IsPresentedByGlobalSections` takes its two coproducts and its cokernel in
`SheafOfModules.{r}`, while `SheafOfModules.HasGlobalPresentation` takes them in
`SheafOfModules.{max u v r}`, which on a big site is strictly larger.

The lift is `SheafOfModules.uliftForPresentationFunctor`, which preserves colimits by
`SheafOfModules.preservesColimitsOfSize_uliftForPresentationFunctor'` and zero morphisms, so the
whole cokernel diagram travels; the two index types are reindexed along `ULift`.

`SheafOfModules.isPresentedByGlobalSections_iff_hasGlobalPresentation` is the same comparison in
the case where the sections already contain the site universes and no lift is needed. -/
theorem hasGlobalPresentation_of_isPresentedByGlobalSections
    [HasWeakSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    {M : _root_.SheafOfModules.{r} R} (h : M.IsPresentedByGlobalSections) :
    M.HasGlobalPresentation := by
  classical
  obtain ⟨I, K, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hc⟩⟩ := h
  set F := _root_.SheafOfModules.uliftForPresentationFunctor.{u, v, r, r, max u v r} (R := R)
  have : PreservesColimitsOfSize.{r, r} F :=
    _root_.SheafOfModules.preservesColimitsOfSize_uliftForPresentationFunctor' R
  have : PreservesColimitsOfSize.{0, 0} F := preservesColimitsOfSize_shrink _
  have lift : ∀ {T : Type r} {X : _root_.SheafOfModules.{r} R}
      {f : T → (_root_.SheafOfModules.unit R ⟶ X)},
      IsColimit (Cofan.mk X f) → IsColimit (Cofan.mk (F.obj X) fun i : ULift.{max u v} T ↦
        F.map (f i.down)) := fun h ↦
    isColimitCofanULift ((Cofan.isColimitMapCoconeEquiv _ _ _) (isColimitOfPreserves _ h))
  exact ⟨ULift.{max u v} I, ULift.{max u v} K, _, _, fun i ↦ F.map (ι i.down),
    fun i ↦ F.map (κ i.down), ⟨lift hP⟩, ⟨lift hQ⟩,
    _, _, _, ⟨isColimitCoforkMapOfIsColimit' _ hab hc⟩⟩

/-- **A module with a global presentation at the universe of the sections is quasi-coherent on
the site**, the covering witnessing quasi-coherence at each object being the identity. -/
theorem isQuasicoherentOnSite_of_isPresentedByGlobalSections
    [HasWeakSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    {M : _root_.SheafOfModules.{r} R} (h : M.IsPresentedByGlobalSections) :
    M.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_hasGlobalPresentation M
    (hasGlobalPresentation_of_isPresentedByGlobalSections h)

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Subsite

variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) (P : ObjectProperty X)
  [EssentiallySmall.{u} X]
  [P.ι.IsContinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)]
  [P.ι.IsCocontinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)]

/-- **`g_!H` is quasi-coherent for an `H` with a global presentation**, for an arbitrary
continuous and cocontinuous full subsite whose canonical map `g_!O_{𝒳'} ⟶ O_𝒳` of **Stacks 078A**
is an isomorphism.

This is the case **Stacks 07B0** reduces to, with the two steps the source takes in it: `g_!` is
full, faithful and colimit-preserving and matches the two structure sheaves, so it carries the
presentation of `H` to one of `g_!H` by
`Stacks.Sheaves.GlobalTypeComparison.isPresentedByGlobalSections_iff`; and a module with a global
presentation is quasi-coherent. -/
theorem isQuasicoherentOnSite_subsiteModuleLowerShriek
    (hO : IsIso (subsiteUnitLowerShriekMap B S hS p hp τ hτ P))
    (H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (subsiteRingedTopos B S hS p hp τ hτ P).O))
    (hH : H.IsPresentedByGlobalSections) :
    ((subsiteModuleLowerShriek B S hS p hp τ hτ P).obj H).IsQuasicoherentOnSite := by
  have hu := isIso_subsiteModuleLowerShriekAdjunction_unit B S hS p hp τ hτ P
  have hff := Adjunction.fullyFaithfulLOfIsIsoUnit
    (subsiteModuleLowerShriekAdjunction B S hS p hp τ hτ P)
  have _ := hff.full
  have _ := hff.faithful
  have _ : PreservesColimitsOfSize.{u, u} (subsiteModuleLowerShriek B S hS p hp τ hτ P) :=
    Adjunction.leftAdjoint_preservesColimits
      (subsiteModuleLowerShriekAdjunction B S hS p hp τ hτ P)
  exact Stacks.SheafOfModules.isQuasicoherentOnSite_of_isPresentedByGlobalSections
    ((Stacks.Sheaves.GlobalTypeComparison.isPresentedByGlobalSections_iff
      (subsiteModuleLowerShriek B S hS p hp τ hτ P)
      (asIso (subsiteUnitLowerShriekMap B S hS p hp τ hτ P)) H).1 hH)

end Subsite

/-! ### The lisse-étale site -/

namespace LisseEtale

variable (𝒳 : Stack.AlgebraicStacks.{u, t} B S hS) [EssentiallySmall.{u} 𝒳.val.val.obj]

-- the inclusion of the smooth objects is continuous and cocontinuous for the topology inherited
-- from `𝒳_{étale}`, the closure property of **Stacks 07AK** (1) holding for every algebraic
-- stack; the general subsite declarations ask for the two as instances
attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'

/-- If `g_!O = O_𝒳` and `H` is an `O_{𝒳_{lisse,étale}}`-module with a global presentation, then
`g_!H` is quasi-coherent on `(𝒳_étale, O_𝒳)`. This is the presented case of **Stacks 07B0** (1);
the full statement is
`AlgebraicGeometry.Stack.LisseEtale.isQuasicoherentClause_fppf_moduleLowerShriek`, and the
hypothesis `g_!O = O_𝒳` (**Stacks 078A**) is
`AlgebraicGeometry.Stack.LisseEtale.isIso_unitLowerShriekMap_algebraicStack`. -/
theorem isQuasicoherentOnSite_moduleLowerShriek
    (hO : IsIso (unitLowerShriekMap.{u, t} B S hS 𝒳))
    (H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos.{u, t} B S hS 𝒳
      (closedUnderSmoothMorphisms.{u, t} B S hS 𝒳)).O))
    (hH : H.IsPresentedByGlobalSections) :
    ((moduleLowerShriek.{u, t} B S hS 𝒳).obj H).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_subsiteModuleLowerShriek B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    (etaleTopology B) (etaleTopology_le_topology B) (smoothObject.{u, t} B S hS 𝒳) hO H hH

end LisseEtale

/-! ### The flat-fppf site -/

namespace FlatFppf

variable (𝒳 : Stack.AlgebraicStacks.{u, t} B S hS) [EssentiallySmall.{u} 𝒳.val.val.obj]

attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'

/-- If `g_!O = O_𝒳` and `H` is an `O_{𝒳_{flat,fppf}}`-module with a global presentation, then
`g_!H` is quasi-coherent on `(𝒳_fppf, O_𝒳)`. This is the presented case of **Stacks 07B0** (2);
the full statement is
`AlgebraicGeometry.Stack.FlatFppf.isQuasicoherentOnSite_moduleLowerShriek_of_isQuasicoherentOnSite`,
and the hypothesis `g_!O = O_𝒳` (**Stacks 078A**) is
`AlgebraicGeometry.Stack.FlatFppf.isIso_unitLowerShriekMap_algebraicStack`. -/
theorem isQuasicoherentOnSite_moduleLowerShriek
    (hO : IsIso (unitLowerShriekMap B S hS 𝒳))
    (H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (subsiteRingedTopos B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids B.topology le_rfl (objectProperty B S hS 𝒳)).O))
    (hH : H.IsPresentedByGlobalSections) :
    ((moduleLowerShriek B S hS 𝒳).obj H).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_subsiteModuleLowerShriek B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    B.topology le_rfl (objectProperty B S hS 𝒳) hO H hH

end FlatFppf

end AlgebraicGeometry.Stack

end
