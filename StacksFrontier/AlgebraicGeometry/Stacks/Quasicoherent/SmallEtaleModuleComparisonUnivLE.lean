module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeProperty

/-!
# The comparison map of restricted modules, at a module universe above the scheme universe

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids, let `F` be a presheaf of modules
over the structure sheaf of **Stacks 06TV** and let `φ : x ⟶ y` be an arrow of `𝒳` lying over a
morphism of schemes `a : U ⟶ V`. The comparison map `c_φ : a_{small}^*(F|_{V_ét}) ⟶ F|_{U_ét}` of
**Stacks 06WC** is the mate of the direct-image comparison of **Stacks 06W2** under the
pullback–direct image adjunction along the map `a_{small}^♯` of structure sheaves.

`AlgebraicGeometry.Stack.restrictModulePullbackComparison` forms that mate with the sections of
`F` in the universe `u` of the schemes, because the adjointness it uses is
`PresheafOfModules.isRightAdjoint_pushforward_of_essentiallySmall`, whose module universe is the
universe of the structure sheaf. The structure sheaf of the small étale site takes its sections
in `Type u`, so this forces the module to do the same.

This file forms it with the module universe `m` only required to satisfy `UnivLE.{u, m}`: the
sections of `F` may live above the universe of the schemes. The input is
`PresheafOfModules.isRightAdjoint_pushforward_of_essentiallySmall_univLE`, whose ring universe is
independent of its module universe; essential smallness of the small étale site of `V` in `Type u`
transports up to `Type m` by `CategoryTheory.essentiallySmall_trans_univLE`.

## Main definitions

* `AlgebraicGeometry.Stack.restrictModulePullbackComparisonUnivLE`: **Stacks 06WC** for a
  presheaf of modules whose sections live in a universe above that of the schemes.
* `AlgebraicGeometry.Stack.HasFlatBaseChangePropertyUnivLE`: **Stacks 0762** for such a presheaf
  of modules.

## Main results

* `AlgebraicGeometry.Stack.isRightAdjoint_pushforward_smallEtaleStructureComparison_univLE`: the
  direct image of presheaves of modules along `a_{small}^♯` has a left adjoint at any module
  universe above the universe of the schemes.
* `AlgebraicGeometry.Stack.restrictModulePullbackComparisonUnivLE_adjunct`: the comparison map is
  characterized by its mate being the direct-image comparison.

## References

* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 06W2](https://stacks.math.columbia.edu/tag/06W2)
* [Stacks Project, Tag 0761](https://stacks.math.columbia.edu/tag/0761)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v w m

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) {𝒳 : Type v} [Category.{w} 𝒳]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

section Comparison

variable {x y : 𝒳} (φ : x ⟶ y) (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)

/-- The direct image of presheaves of modules along `a_{small}^♯` has a left adjoint at every
module universe `m` above the universe `u` of the schemes: the small étale site of the scheme
below `y` is essentially small in `Type u`, hence in `Type m`, while the structure sheaves stay
in `RingCat.{u}`. -/
instance isRightAdjoint_pushforward_smallEtaleStructureComparison_univLE [UnivLE.{u, m}] :
    (PresheafOfModules.pushforward.{m}
      (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ))
      (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).IsRightAdjoint :=
  haveI hES : EssentiallySmall.{u}
      (SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y)) := inferInstance
  haveI hLS : LocallySmall.{u}
      (SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)) := inferInstance
  haveI : EssentiallySmall.{m}
      (SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y)) :=
    essentiallySmall_trans_univLE hES
  haveI : LocallySmall.{m}
      (SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)) :=
    locallySmall_trans_univLE hLS
  PresheafOfModules.isRightAdjoint_pushforward_of_essentiallySmall_univLE.{m}
    (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)

/-- **Stacks 06WC** at a module universe above the universe of the schemes. The comparison map
`c_φ : a_{small}^*(F|_{V_ét}) ⟶ F|_{U_ét}` of `𝒪_{U_ét}`-modules below an arrow `φ : x ⟶ y` of
`𝒳` lying over a morphism of schemes `a : U ⟶ V`: the mate, under the pullback–direct image
adjunction along `a_{small}^♯`, of the comparison of Stacks 06W2 for `F`. -/
def restrictModulePullbackComparisonUnivLE [UnivLE.{u, m}]
    (F : PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp τ hτ).obj) :
    (PresheafOfModules.pullback.{m}
        (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ))
        (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).obj
        (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F) ⟶
      restrictModuleToSmallEtale B E h S hS p hp x τ hτ F :=
  ((PresheafOfModules.pullbackPushforwardAdjunction.{m}
    (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).homEquiv _ _).symm
      (restrictModulePushforwardComparison B E h S hS p hp φ τ hτ F)

/-- The comparison map is characterized by its mate being the comparison of Stacks 06W2 for the
presheaf of modules. -/
theorem restrictModulePullbackComparisonUnivLE_adjunct [UnivLE.{u, m}]
    (F : PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp τ hτ).obj) :
    (PresheafOfModules.pullbackPushforwardAdjunction.{m}
        (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).homEquiv _ _
        (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ τ hτ F) =
      restrictModulePushforwardComparison B E h S hS p hp φ τ hτ F :=
  Equiv.apply_symm_apply _ _

end Comparison

/-- **Stacks 0762** at a module universe above the universe of the schemes. A presheaf of modules
over the structure sheaf of a category fibred in groupoids *has the flat base change property*
when the comparison map `c_φ` of Stacks 0761 is an isomorphism for every arrow `φ` of `𝒳` lying
over a flat morphism of schemes. -/
abbrev HasFlatBaseChangePropertyUnivLE [UnivLE.{u, m}]
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
    (F : PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp τ hτ).obj) : Prop :=
  ∀ {x y : 𝒳} (φ : x ⟶ y), Flat (B.inclusion.map (p.map φ).left) →
    IsIso (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ τ hτ F)

end AlgebraicGeometry.Stack

end
