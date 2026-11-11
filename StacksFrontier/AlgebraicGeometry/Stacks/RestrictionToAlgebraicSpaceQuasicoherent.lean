module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorInternalHom
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionComparisonFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentSiteAgreement
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeWeakSerre
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentWeakSerreUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentDirectImage

/-!
# The functors `a`, `b`, `c`, `d` of Stacks 0GQS

Let `𝒳` be an algebraic stack and `f : 𝒰 ⟶ 𝒳` a 1-morphism with `𝒰` the algebraic stack of an
algebraic space `U`. Stacks 0GQS considers

```
a : Mod(𝒳_étale, 𝒪_𝒳) ⥤ Mod(U_étale, 𝒪_U),   ℱ ↦ f^*ℱ|_{U_étale},
b : LQCoh(𝒪_𝒳) ⥤ QCoh(U_étale, 𝒪_U),
c : LQCoh^fbc(𝒪_𝒳) ⥤ QCoh(U_étale, 𝒪_U),
d : QCoh(𝒪_𝒳) ⥤ QCoh(U_étale, 𝒪_U),
```

`b`, `c` and `d` being the restrictions of `a`. This file defines them.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.spaceRestriction`: the functor `a`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.lqcohSpaceRestriction`: the functor `b`, the lift of
  `a` restricted to `LQCoh(𝒪_𝒳)` into `QCoh(U_étale, 𝒪_U)`, which exists by Stacks 0GQC.
* `AlgebraicGeometry.Stack.AlgebraicStacks.lqcohFbcSpaceRestriction`: the functor `c`, the
  inclusion `LQCoh^fbc(𝒪_𝒳) ⊆ LQCoh(𝒪_𝒳)` followed by `b`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.qcohSpaceRestriction`: the functor `d`, the inclusion
  `QCoh(𝒪_𝒳) ⊆ LQCoh(𝒪_𝒳)` of Stacks 06WN followed by `b`.

## Implementation notes

**The spellings.** `𝒰` is the algebraic stack of `U`
(`AlgebraicGeometry.Stack.algebraicSpaceStack`) with its identity presentation, the convention of
`AlgebraicGeometry.Stack.FlatFppf.spaceChartRestrictionFunctor` and of Stacks 0GQT here.
`Mod(𝒳_étale, 𝒪_𝒳)` is `AlgebraicGeometry.Space.inheritedEtaleModules`; `LQCoh(𝒪_𝒳)` is
`AlgebraicGeometry.Stack.locallyQuasicoherentModules` and `LQCoh^fbc(𝒪_𝒳)` is
`AlgebraicGeometry.Stack.lqcohSheafFbcEtaleModules`, both inside the étale modules as in the
source, with the auxiliary big étale site `AlgebraicGeometry.associatedBigEtaleSite` that Stacks
0GQC uses; `QCoh(𝒪_𝒳)` is `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModules`, on the
fppf site; `QCoh(U_étale, 𝒪_U)` is `AlgebraicGeometry.Space.QuasicoherentSheaves`. All modules have
sections in the universe `u` of the schemes.

## References

* [Stacks Project, Tag 0GQS](https://stacks.math.columbia.edu/tag/0GQS)
* [Stacks Project, Tag 0GQC](https://stacks.math.columbia.edu/tag/0GQC)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
  (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)

/-- **The functor `a : Mod(𝒳_étale, 𝒪_𝒳) ⥤ Mod(U_étale, 𝒪_U)` of Stacks 0GQS**,
`ℱ ↦ f^*ℱ|_{U_étale}`: the inverse image along `f` followed by the restriction to the small étale
site of `U`, which is `AlgebraicGeometry.Space.etaleRestrictedModuleInverseImageFunctor` for the
identity presentation of the algebraic stack of `U`. -/
abbrev spaceRestriction :
    Space.inheritedEtaleModules.{u} B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids ⥤
      Space.Modules.{u, u} B S hS U hU :=
  Space.etaleRestrictedModuleInverseImageFunctor (U := ⟨U, hU⟩) B S hS
    (algebraicSpaceStack.{u, w} B S hS U hU).val.val.p 𝒳.val.val.p
    (algebraicSpaceStack.{u, w} B S hS U hU).val.isFiberedInGroupoids
    𝒳.val.isFiberedInGroupoids
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (CatFiberedInGroupoids.homFunctor f.hom)
    (BigFppfOver.isFibredOneMorphism_homFunctor B S hS f.hom)

/-- `LQCoh(𝒪_𝒳)`, the locally quasi-coherent modules of Stacks 06WJ on the étale site of `𝒳`. -/
abbrev lqcohModules :=
  Stack.locallyQuasicoherentModules.{u, u + 1, u, u} B (associatedBigEtaleSite B) rfl S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids

/-- The inclusion `LQCoh(𝒪_𝒳) ⊆ Mod(𝒳_étale, 𝒪_𝒳)`. -/
abbrev lqcohInclusion :
    lqcohModules B S hS 𝒳 ⥤
      Space.inheritedEtaleModules.{u} B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids :=
  (Stack.isLocallyQuasicoherent.{u, u + 1, u, u} B (associatedBigEtaleSite B) rfl S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids).ι

/-- **The functor `b : LQCoh(𝒪_𝒳) ⥤ QCoh(U_étale, 𝒪_U)` of Stacks 0GQS**: the restriction of `a`
to locally quasi-coherent modules, which land in the quasi-coherent modules by Stacks 0GQC
(`Space.isQuasicoherentOnSite_etaleRestrictedModuleInverseImage_of_isLocallyQuasicoherent`). -/
def lqcohSpaceRestriction :
    lqcohModules B S hS 𝒳 ⥤ Space.QuasicoherentSheaves.{u, u} B S hS U hU :=
  ObjectProperty.lift _ (lqcohInclusion B S hS 𝒳 ⋙ spaceRestriction B S hS 𝒳 U hU f)
    fun F => Space.isQuasicoherentOnSite_etaleRestrictedModuleInverseImage_of_isLocallyQuasicoherent
      B (associatedBigEtaleSite B) rfl S hS (U := ⟨U, hU⟩)
      (algebraicSpaceStack.{u, w} B S hS U hU).val.val.p 𝒳.val.val.p
      (algebraicSpaceStack.{u, w} B S hS U hU).val.isFiberedInGroupoids
      𝒳.val.isFiberedInGroupoids
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (CatFiberedInGroupoids.homFunctor f.hom)
      (BigFppfOver.isFibredOneMorphism_homFunctor B S hS f.hom) F.obj F.property

/-- `b` followed by the inclusion `QCoh(U_étale, 𝒪_U) ⊆ Mod(U_étale, 𝒪_U)` is `a` on
`LQCoh(𝒪_𝒳)`. -/
def lqcohSpaceRestrictionCompι :
    lqcohSpaceRestriction B S hS 𝒳 U hU f ⋙ ObjectProperty.ι _ ≅
      lqcohInclusion B S hS 𝒳 ⋙ spaceRestriction B S hS 𝒳 U hU f :=
  ObjectProperty.liftCompιIso _ _ _

/-- `LQCoh^fbc(𝒪_𝒳)`, the locally quasi-coherent modules on the étale site of `𝒳` with the flat
base change property (Stacks, Section 0GQG). -/
abbrev lqcohFbcModules :=
  (lqcohSheafFbcEtaleModules.{u, w, u} B (associatedBigEtaleSite B) rfl S hS 𝒳).FullSubcategory

/-- The inclusion `LQCoh^fbc(𝒪_𝒳) ⊆ LQCoh(𝒪_𝒳)`. -/
def lqcohFbcToLqcoh : lqcohFbcModules B S hS 𝒳 ⥤ lqcohModules B S hS 𝒳 :=
  ObjectProperty.lift _ (ObjectProperty.ι _) fun F => F.property.1

/-- **The functor `c : LQCoh^fbc(𝒪_𝒳) ⥤ QCoh(U_étale, 𝒪_U)` of Stacks 0GQS**: the restriction of
`b`, hence of `a`, to `LQCoh^fbc(𝒪_𝒳)`. -/
def lqcohFbcSpaceRestriction :
    lqcohFbcModules B S hS 𝒳 ⥤ Space.QuasicoherentSheaves.{u, u} B S hS U hU :=
  lqcohFbcToLqcoh B S hS 𝒳 ⋙ lqcohSpaceRestriction B S hS 𝒳 U hU f

/-- The inclusion `QCoh(𝒪_𝒳) ⊆ LQCoh(𝒪_𝒳)` of Stacks 06WN: a quasi-coherent module read on the
étale site of `𝒳`. -/
abbrev qcohToLqcoh : AlgebraicStacks.quasicoherentModules B S hS 𝒳 ⥤ lqcohModules B S hS 𝒳 :=
  FibredSite.toLocallyQuasicoherentModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    (associatedBigEtaleSite B) rfl

/-- **The functor `d : QCoh(𝒪_𝒳) ⥤ QCoh(U_étale, 𝒪_U)` of Stacks 0GQS**: the restriction of `b`,
hence of `a`, to `QCoh(𝒪_𝒳)`. -/
def qcohSpaceRestriction :
    AlgebraicStacks.quasicoherentModules B S hS 𝒳 ⥤
      Space.QuasicoherentSheaves.{u, u} B S hS U hU :=
  qcohToLqcoh B S hS 𝒳 ⋙ lqcohSpaceRestriction B S hS 𝒳 U hU f

end AlgebraicGeometry.Stack.AlgebraicStacks

end
