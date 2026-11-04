module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorInternalHomChart

/-!
# Stacks 0GQT: the restriction of `hom(ℱ, 𝒢)` to an algebraic space

Let `f : 𝒰 ⟶ 𝒳` be a flat 1-morphism of algebraic stacks with `𝒰` the algebraic stack of an
algebraic space `U`, and `d : ℱ ↦ f^*ℱ|_{U_étale}` the restriction of Stacks 0GQS. Stacks 0GQT
says that `d(hom(ℱ, 𝒢)) = 𝓗om_{𝒪_U}(d(ℱ), d(𝒢))` for `hom(ℱ, 𝒢) = Q(𝓗om_{𝒪_𝒳}(ℱ, 𝒢))` the
object of Stacks 0GQN. The source's chain of equalities is followed:
`d(Q(𝓗om)) = d(𝓗om)` because `d` does not see the counit of the coherator on flat objects
(item (7) of Stacks 0GQS), and `d(𝓗om(ℱ, 𝒢)) = 𝓗om(d(ℱ), d(𝒢))`
(`AlgebraicGeometry.Stack.FlatFppf.isIso_chartInternalHomComparison`), the place where the source
cites Stacks 0GN2 twice.

## Main results

* `AlgebraicGeometry.Stack.FlatFppf.spaceChartRestrictionCoheratorInternalHomIso`:
  **Stacks 0GQT**.

## Implementation notes

**Hypotheses.** The source asks `ℱ` and `𝒢` quasi-coherent and `ℱ` of finite presentation; those
are the hypotheses under which `hom(ℱ, 𝒢)` is quasi-coherent (Stacks 0GQN), so that `d` of it
makes sense in `QCoh(U_étale, 𝒪_U)`. The isomorphism itself uses only that `ℱ` is quasi-coherent
and that `f` is flat, and is stated under those hypotheses; it is the same isomorphism, the
functor `d` of Stacks 0GQS being the restriction of the functor `a` on all modules
(`AlgebraicGeometry.Stack.spaceChartRestriction`).

**The source of `f`.** `𝒰` is the algebraic stack of `U`
(`AlgebraicGeometry.Stack.algebraicSpaceStack`), the convention of
`AlgebraicGeometry.Stack.IsCoherentOnSomeFlatSpaceChart`; the restriction `d` uses the identity
presentation of it.

## References

* [Stacks Project, Tag 0GQT](https://stacks.math.columbia.edu/tag/0GQT)
* [Stacks Project, Tag 0GQS](https://stacks.math.columbia.edu/tag/0GQS)
* [Stacks Project, Tag 0GQN](https://stacks.math.columbia.edu/tag/0GQN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack.FlatFppf

universe u w

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
  (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
  (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)

/-- `d` carries isomorphisms of `𝒪_𝒳`-modules, at any universe of the sections, to isomorphisms. -/
def spaceChartRestrictionMapIso {M N : _root_.SheafOfModules.{u + 1}
    (ambientRingStructureSheaf B S hS 𝒳)} (e : M ≅ N) :
    spaceChartRestriction B S hS 𝒳 U hU f M ≅ spaceChartRestriction B S hS 𝒳 U hU f N :=
  (_root_.SheafOfModules.fullyFaithfulForget _).preimageIso
    ((PresheafOfModules.pushforward (chartRingHom B S hS 𝒳 U hU f)).mapIso
      ((_root_.SheafOfModules.forget _).mapIso e))

/-- **`d(Hom(F, G)) = Hom(d(F), d(G))`** for `F` cartesian between affine objects, with the
internal Homs at the universe of the schemes. -/
def spaceChartRestrictionSheafHomIso
    (F G : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳))
    (hF : IsCartesianBetweenAffines 𝒳.val.isFiberedInGroupoids F) :
    spaceChartRestriction B S hS 𝒳 U hU f (sheafHom B S hS 𝒳 F G) ≅
      Space.smallEtaleInternalHomSmall B S hS U hU (spaceChartRestriction B S hS 𝒳 U hU f F)
        (spaceChartRestriction B S hS 𝒳 U hU f G) :=
  haveI := isIso_chartInternalHomComparison B S hS 𝒳 U hU f F G hF
  let RU := Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B S hS U hU).O
  let e1 : spaceChartRestriction B S hS 𝒳 U hU f
      ((Stacks.SheafOfModules.moduleULift.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)).obj
        (sheafHom B S hS 𝒳 F G)) ≅
      spaceChartRestriction B S hS 𝒳 U hU f
        (RingedSite.internalHomSheaf (fppfRingedSite B S hS 𝒳) F G) :=
    spaceChartRestrictionMapIso B S hS 𝒳 U hU f
      (@RingedSite.internalHomSheafSmallIso (fppfRingedSite B S hS 𝒳)
        (essentiallySmall_obj_algebraicStack B S hS 𝒳) F G)
  let e3 : Space.smallEtaleInternalHom B S hS U hU (spaceChartRestriction B S hS 𝒳 U hU f F)
        (spaceChartRestriction B S hS 𝒳 U hU f G) ≅
      (Stacks.SheafOfModules.moduleULift.{u + 1} RU).obj
        (Space.smallEtaleInternalHomSmall B S hS U hU (spaceChartRestriction B S hS 𝒳 U hU f F)
          (spaceChartRestriction B S hS 𝒳 U hU f G)) :=
    (Space.smallEtaleInternalHomSmallIso B S hS U hU _ _).symm
  let E : (Stacks.SheafOfModules.moduleULift.{u + 1} RU).obj
        (spaceChartRestriction B S hS 𝒳 U hU f (sheafHom B S hS 𝒳 F G)) ≅
      (Stacks.SheafOfModules.moduleULift.{u + 1} RU).obj
        (Space.smallEtaleInternalHomSmall B S hS U hU (spaceChartRestriction B S hS 𝒳 U hU f F)
          (spaceChartRestriction B S hS 𝒳 U hU f G)) :=
    e1 ≪≫ asIso (chartInternalHomComparison B S hS 𝒳 U hU f F G) ≪≫ e3
  (Stacks.SheafOfModules.moduleULiftFullyFaithful.{u + 1, u} RU).preimageIso E

/-- **Stacks 0GQT.** Let `f : 𝒰 ⟶ 𝒳` be a flat 1-morphism of algebraic stacks with `𝒰` the
algebraic stack of an algebraic space `U`, and let `d : ℱ ↦ f^*ℱ|_{U_étale}` be the restriction of
Stacks 0GQS. For `𝒪_𝒳`-modules `ℱ` and `𝒢` with `ℱ` quasi-coherent,
`d(hom(ℱ, 𝒢)) = 𝓗om_{𝒪_U}(d(ℱ), d(𝒢))`, where `hom(ℱ, 𝒢) = Q(𝓗om_{𝒪_𝒳}(ℱ, 𝒢))` is the
object of Stacks 0GQN. -/
@[stacks 0GQT]
def spaceChartRestrictionCoheratorInternalHomIso (hf : AlgebraicStacks.IsFlat B S hS f)
    (F G : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳))
    (hF : F.IsQuasicoherentOnSite) :
    spaceChartRestriction B S hS 𝒳 U hU f (coheratorInternalHom B S hS 𝒳 F G) ≅
      Space.smallEtaleInternalHomSmall B S hS U hU (spaceChartRestriction B S hS 𝒳 U hU f F)
        (spaceChartRestriction B S hS 𝒳 U hU f G) :=
  @asIso _ _ _ _ ((spaceChartRestrictionFunctor B S hS 𝒳 U hU f).map
      ((coheratorCounit B S hS 𝒳).app (sheafHom B S hS 𝒳 F G)))
    (isIso_spaceChartRestrictionFunctor_map_coheratorCounit B S hS 𝒳 U hU f hf
      (sheafHom B S hS 𝒳 F G)) ≪≫
    spaceChartRestrictionSheafHomIso B S hS 𝒳 U hU f F G
      (isCartesianBetweenAffines_of_isQuasicoherentOnSite _ F hF)

end AlgebraicGeometry.Stack.FlatFppf

end
