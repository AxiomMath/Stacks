module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentSeparator
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreEssentialSmallness
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AlgebraicStackColimits
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AlgebraicStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentHasSeparator
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentSmallness

/-!
# The coherator on an algebraic stack

Let `𝒳` be an algebraic stack over `S`.  This file proves Stacks 0781: the category
`QCoh(𝒪_𝒳)` of quasi-coherent modules on the fppf site of `𝒳` is a Grothendieck abelian
category, hence has enough injectives and all limits, and the inclusion
`QCoh(𝒪_𝒳) → Mod(𝒪_𝒳)` has a right adjoint `Q`, the *coherator*, whose adjunction morphism
`Q(𝓕) → 𝓕` is an isomorphism for every quasi-coherent `𝓕`.

## The proof

Part (1).  Choose a presentation `[U/R] → 𝒳` by the smooth groupoid of Stacks 04T4 (4), whose
space of objects `U` is the scheme of the chosen presentation of `𝒳`
(`AlgebraicGeometry.Stack.exists_groupoidPresentation_objects_eq`).  By Stacks 06WV (1),
`QCoh(𝒪_𝒳) ≌ QCoh(U, R, s, t, c)`
(`AlgebraicGeometry.Stack.GroupoidPresentation.quasicoherentEquivalence`), and the right hand
side is a Grothendieck abelian category: its colimits and kernels are computed on `𝒪_U`-modules,
where filtered colimits are exact, and it has a separator built, as in Groupoids in Spaces,
Lemma 0780, from bounded submodules
(`AlgebraicGeometry.Space.QuasicoherentModule.isGrothendieckAbelian_of_objects_eq`).  Being
Grothendieck abelian is invariant under equivalence, and a Grothendieck abelian category has
enough injectives and all limits (Stacks 079H, 07D8).

Part (2).  The inclusion preserves colimits (Stacks 06WV (4)), `QCoh(𝒪_𝒳)` is cocomplete,
locally small and well-copowered with a separator by part (1), and `Mod(𝒪_𝒳)` is locally small,
so the special adjoint functor theorem gives the right adjoint; the source represents
`𝒢 ↦ Hom(𝒢, 𝓕)` by Stacks 07D7, which is the same argument.  The inclusion is fully faithful, so
the counit is an isomorphism exactly on the quasi-coherent modules.

## Main results

* `AlgebraicGeometry.Stack.quasicoherentModules_isGrothendieckAbelian_enoughInjectives_hasLimits`:
  **Stacks 0781, part (1).**
* `AlgebraicGeometry.Stack.exists_quasicoherentCoherator`: **Stacks 0781, part (2).**
* `AlgebraicGeometry.Stack.isLeftAdjoint_quasicoherentInclusion`: the existence of the
  coherator, from the separator `AlgebraicGeometry.Stack.hasSeparator_quasicoherentModules`.

## Implementation notes

The abelian structure on `QCoh(𝒪_𝒳)` is the instance
`AlgebraicGeometry.Stack.abelianQuasicoherentModules` of Stacks 06WV (2).  The presentation
used here to produce the separator need not be the one that instance is transported along: a
separator, local smallness and the exactness of filtered colimits are properties of the category,
and `CategoryTheory.IsGrothendieckAbelian.of_equivalence` transports them along any equivalence.

## References

* [Stacks Project, Tag 0781](https://stacks.math.columbia.edu/tag/0781)
* [Stacks Project, Tag 06WV](https://stacks.math.columbia.edu/tag/06WV)
* [Stacks Project, Tag 0780](https://stacks.math.columbia.edu/tag/0780)
* [Stacks Project, Tag 04T3](https://stacks.math.columbia.edu/tag/04T3)
* [Stacks Project, Tag 079H](https://stacks.math.columbia.edu/tag/079H)
* [Stacks Project, Tag 07D7](https://stacks.math.columbia.edu/tag/07D7)
* [Stacks Project, Tag 07D8](https://stacks.math.columbia.edu/tag/07D8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **An algebraic stack has a presentation whose space of objects is a scheme.**  The
presentation of Stacks 04T3 (`AlgebraicGeometry.Stack.nonempty_groupoidPresentation`) is the
self-intersection groupoid of Stacks 04T4 (4) of a presentation `𝒮_W → 𝒳` by a scheme `W`, and
its space of objects is the algebraic space of `W`. -/
theorem exists_groupoidPresentation_objects_eq
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) :
    ∃ (P : GroupoidPresentation B S hS 𝒳.val) (W : BigFppfOver B S hS),
      P.groupoid.objects = schemeSpace W := by
  obtain ⟨_hfib, ⟨⟨-, -⟩, -, W, f, hf, hfprop⟩⟩ := id h𝒳
  let 𝒰 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
    schemeFibredCategory B S hS W
  let F : 𝒰 ⟶ 𝒳 := Bicategory.InducedBicategory.mkHom f
  let U : AlgebraicSpaces B S hS := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩
  let eU : StacksRepresentableCFG.EquivalenceOver
      𝒰.val.p (presheafOfCategories (U.obj ⋙ typeToCat)).p :=
    PresheafOfCategories.sliceElementsEquivalenceOver W
  obtain ⟨Robj, hRobj, ⟨eR₀⟩⟩ :=
    SelfIntersection.isRepresentableByAlgebraicSpace_relation_of_isAlgebraicStack
      B S hS 𝒰 𝒳 F.hom h𝒳 (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS W)
  let R : AlgebraicSpaces B S hS := ⟨Robj, hRobj⟩
  let eR : StacksRepresentableCFG.EquivalenceOver
      (SelfIntersection.relation B S hS 𝒰 𝒳 F.hom).val.p
      (presheafOfCategories (R.obj ⋙ typeToCat)).p := eR₀
  have hsmooth : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.smoothMorphismProperty B S hS) F hf :=
    fun V y hy G hG he => (hfprop V y hy G hG he).2
  have hsrc := SelfIntersection.isSmooth_selfIntersectionPresentation_source
    (𝒰 := 𝒰) (𝒳 := 𝒳) (F := F) (U := U) (R := R) eU eR hf hsmooth h𝒳
  have htgt := SelfIntersection.isSmooth_selfIntersectionPresentation_target
    (𝒰 := 𝒰) (𝒳 := 𝒳) (F := F) (U := U) (R := R) eU eR hf hsmooth h𝒳
  obtain ⟨e, -⟩ := SelfIntersection.exists_equivalenceOver_canonicalMap_of_isSmooth
    (𝒰 := 𝒰) (𝒳 := 𝒳) (f := F) (U := U) (R := R) eU eR h𝒳
    hsmooth (fun V y hy G hG he => (hfprop V y hy G hG he).1)
  refine ⟨{
    groupoid := GroupoidInAlgebraicSpaces.changeBase
      ((isTerminal_baseSpace B S hS).from
        (SelfIntersection.selfIntersectionPresentation eU eR h𝒳).base)
      (SelfIntersection.selfIntersectionPresentation eU eR h𝒳).groupoid
    smooth := ⟨hsrc, htgt⟩
    equivalence := (GroupoidInAlgebraicSpaces.quotientStack_changeBase _ _).symm ▸ e }, W,
    rfl⟩

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **Stacks 0781, part (1).**  Let `𝒳` be an algebraic stack over `S`.  The category
`QCoh(𝒪_𝒳)` of quasi-coherent modules on `𝒳` is a Grothendieck abelian category; consequently
it has enough injectives and all limits.

Through a presentation `[U/R] → 𝒳` whose space of objects is a scheme, `QCoh(𝒪_𝒳)` is
equivalent to `QCoh(U, R, s, t, c)` (Stacks 06WV (1)), which is Grothendieck abelian: colimits
exist, filtered colimits are exact because they and kernels are computed on `𝒪_U`-modules, and
there is a separator by the argument of Groupoids in Spaces, Lemma 0780
(`AlgebraicGeometry.Space.QuasicoherentModule.isGrothendieckAbelian_of_objects_eq`).  The
assertions on injectives and limits hold in every Grothendieck abelian category (Stacks 079H,
07D8). -/
@[stacks 0781 "part (1): QCoh(𝒪_𝒳) is a Grothendieck abelian category; consequently it has \
  enough injectives and all limits"]
theorem quasicoherentModules_isGrothendieckAbelian_enoughInjectives_hasLimits :
    IsGrothendieckAbelian.{u} (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
        𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) ∧
      EnoughInjectives (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
        𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) ∧
      HasLimitsOfSize.{u, u} (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
        𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) := by
  obtain ⟨P, W, hU⟩ := exists_groupoidPresentation_objects_eq 𝒳.val 𝒳.property
  have hs := Space.isFlat_of_isSmooth B S hS _ P.smooth.1
  have ht := Space.isFlat_of_isSmooth B S hS _ P.smooth.2
  let := Space.QuasicoherentModule.abelian_of_closure P.groupoid hs ht
  have := Space.QuasicoherentModule.isGrothendieckAbelian_of_objects_eq P.groupoid hU hs ht
  have : IsGrothendieckAbelian.{u} (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) :=
    IsGrothendieckAbelian.of_equivalence P.quasicoherentEquivalence.symm
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- `Mod(𝒪_𝒳)` is locally small at the universe of the schemes, for an algebraic stack `𝒳`: its
site is essentially small (`AlgebraicGeometry.Stack.essentiallySmall_obj_algebraicStack`), so
its modules form a Grothendieck abelian category. -/
theorem locallySmall_sheafOfModulesOfStack :
    LocallySmall.{u} (SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf)) :=
  have : HasSheafify (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p SiteKind.fppf)
      AddCommGrpCat.{u} := hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _
  have : (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p SiteKind.fppf).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u, u + 1, u + 1, u} _
  (SheafOfModules.isGrothendieckAbelian_of_essentiallySmall
    (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      .fppf)).locallySmall

/-- **The inclusion `QCoh(𝒪_𝒳) → Mod(𝒪_𝒳)` is a left adjoint**, for an algebraic stack `𝒳`.

This is the special adjoint functor theorem: the inclusion preserves colimits (Stacks 06WV (4)),
`QCoh(𝒪_𝒳)` is cocomplete, locally small and well-copowered with a separator by Stacks 0781,
part (1), and `Mod(𝒪_𝒳)` is locally small. -/
theorem isLeftAdjoint_quasicoherentInclusion :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        .fppf)).ι.IsLeftAdjoint := by
  have := locallySmall_quasicoherentOfStack B S hS 𝒳
  have := locallySmall_sheafOfModulesOfStack 𝒳
  have := hasSeparator_quasicoherentModules B S hS 𝒳
  have : WellPowered.{u} (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids)ᵒᵖ := CategoryTheory.wellPowered_op_of_hasSeparator
  exact isLeftAdjoint_of_preservesColimits_of_isSeparating.{u} (isSeparator_separator _) _

/-- **Stacks 0781, part (2).**  Let `𝒳` be an algebraic stack over `S`.  The inclusion
`QCoh(𝒪_𝒳) → Mod(𝒪_𝒳)` has a right adjoint `Q`, the *coherator*, such that for every
quasi-coherent `𝒪_𝒳`-module `𝓕` the adjunction morphism `Q(𝓕) → 𝓕` is an isomorphism.

The right adjoint exists by `AlgebraicGeometry.Stack.isLeftAdjoint_quasicoherentInclusion`.
The inclusion is fully faithful, so the counit is an isomorphism exactly on its essential image,
which contains the quasi-coherent modules. -/
@[stacks 0781 "part (2): the inclusion QCoh(𝒪_𝒳) → Mod(𝒪_𝒳) has a right adjoint Q such that \
  Q(F) → F is an isomorphism for every quasi-coherent F"]
theorem exists_quasicoherentCoherator :
    ∃ (Q : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids .fppf) ⥤
        FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids)
      (adj : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
          .fppf)).ι ⊣ Q),
      ∀ M : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids .fppf),
        M.IsQuasicoherentOnSite → IsIso (adj.counit.app M) := by
  have := isLeftAdjoint_quasicoherentInclusion 𝒳
  exact ⟨_, Adjunction.ofIsLeftAdjoint _, fun M hM =>
    (Adjunction.isIso_counit_app_iff_mem_essImage _).mpr ⟨⟨M, hM⟩, ⟨Iso.refl _⟩⟩⟩

end AlgebraicGeometry.Stack

end
