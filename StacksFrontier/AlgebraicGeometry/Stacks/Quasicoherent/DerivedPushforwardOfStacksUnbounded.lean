module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExistsKInjectiveResolution
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedPlusRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedPushforwardQuasicoherent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The unbounded derived direct image of an algebraic stack

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks. This file constructs the total right
derived functor

`Rf_* : D(𝒪_𝒳) ⥤ D(𝒪_𝒴)`

of the direct image of **Stacks 06WE** on fppf modules, at module universe `u + 1`, on the
*unbounded* derived categories: the right-hand column of the diagram of **Stacks 07BC**. It
exists because the fppf modules form a Grothendieck abelian category, so every complex has a
K-injective resolution (**Stacks 079P**), and K-injective complexes compute right derived
functors.

It then identifies its restriction to `D⁺(𝒪_𝒳)` with the bounded below `Rf_*` of
`AlgebraicGeometry.Stack.fppfDerivedPushforwardPlusOfStacks`, through
`CategoryTheory.Functor.boundedDerivedIso`: both are right derived functors of degreewise
direct image on bounded below complexes.

## Main definitions

* `AlgebraicGeometry.Stack.isGrothendieckAbelian_fppfModulesUnivLESucc`: the fppf modules of an
  algebraic stack at module universe `u + 1` are a Grothendieck abelian category.
* `AlgebraicGeometry.Stack.fppfDerivedPushforwardOfStacks`: the unbounded `Rf_*`, with its
  comparison `AlgebraicGeometry.Stack.fppfDerivedPushforwardOfStacksUnit` out of degreewise
  direct image.
* `AlgebraicGeometry.Stack.fppfDerivedPushforwardPlusOfStacksCompιIso`: `Rf_*⁺ ⋙ ι ≅ ι ⋙ Rf_*`.

## References

* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 07BC](https://stacks.math.columbia.edu/tag/07BC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace CategoryTheory.Functor

universe v₁ u₁ v₂ u₂ w₁ w₂

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  (F : A ⥤ B) [F.Additive]
  (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (g : K ⟶ I),
    I.IsKInjective ∧ QuasiIso g)

omit [HasDerivedCategory A] in
include hres in
/-- **An additive functor out of an abelian category with K-injective resolutions has a total
right derived functor on the unbounded derived category**: degreewise `F` followed by the
localization has a right derived functor along `K(A) ⥤ D(A)`, computed by K-injective
resolutions. -/
@[sga "4½ Etat_0 4.2.3" "a), special case"]
theorem hasRightDerivedFunctor_mapHomotopyCategory_of_kInjective :
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  have := (hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      v₁, w₂, w₂, u₁, max u₂ v₂, max u₂ v₂}
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) hres).1
  hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _

end CategoryTheory.Functor

namespace AlgebraicGeometry.Stack

attribute [local instance] hasSheafify_fppfAssociatedTopology_succ
  wEqualsLocallyBijective_fppfAssociatedTopology_succ

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The fppf modules of an algebraic stack at module universe `u + 1` form a Grothendieck
abelian category**: the site, its homs and the structure rings all inject into `u + 1`. -/
theorem isGrothendieckAbelian_fppfModulesUnivLESucc (𝒵 : AlgebraicStacks.{u, w} B S hS) :
    IsGrothendieckAbelian.{u + 1} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒵) :=
  SheafOfModules.isGrothendieckAbelian_of_univLE.{u + 1, u, u + 1, u} _

/-- Every complex of fppf modules of an algebraic stack at module universe `u + 1` admits a
quasi-isomorphism into a K-injective complex (**Stacks 079P**). -/
theorem existsKInjectiveResolution_fppfModulesUnivLESucc (𝒵 : AlgebraicStacks.{u, w} B S hS)
    (K : CochainComplex (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒵) ℤ) :
    ∃ (I : CochainComplex (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒵) ℤ) (g : K ⟶ I),
      I.IsKInjective ∧ QuasiIso g :=
  have := isGrothendieckAbelian_fppfModulesUnivLESucc B S hS 𝒵
  Stacks.Cohomology.moduleExistsKInjectiveResolution _ K

attribute [local instance] additive_fppfModuleSheafPushforwardOfStacks
  enoughInjectives_fppfModulesUnivLESucc

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
  [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒳)]
  [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒴)]
  (f : 𝒳 ⟶ 𝒴)

/-- **The unbounded total derived direct image of an algebraic stack**,

`Rf_* : D(𝒪_𝒳) ⥤ D(𝒪_𝒴)`,

the total right derived functor of degreewise direct image of **Stacks 06WE** on fppf modules,
at module universe `u + 1`, which exists because K-injective complexes compute it. It is the
right-hand vertical arrow of the diagram of **Stacks 07BC**. -/
def fppfDerivedPushforwardOfStacks :
    DerivedCategory (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒳) ⥤
      DerivedCategory (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒴) :=
  haveI := Functor.hasRightDerivedFunctor_mapHomotopyCategory_of_kInjective
    (fppfModuleSheafPushforwardOfStacks B S hS f)
    (existsKInjectiveResolution_fppfModulesUnivLESucc B S hS 𝒳)
  ((fppfModuleSheafPushforwardOfStacks B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))

/-- The comparison `f_*K ⟶ Rf_*K` from degreewise direct image to the unbounded `Rf_*`. -/
def fppfDerivedPushforwardOfStacksUnit :
    (fppfModuleSheafPushforwardOfStacks B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ fppfDerivedPushforwardOfStacks B S hS f :=
  haveI := Functor.hasRightDerivedFunctor_mapHomotopyCategory_of_kInjective
    (fppfModuleSheafPushforwardOfStacks B S hS f)
    (existsKInjectiveResolution_fppfModulesUnivLESucc B S hS 𝒳)
  ((fppfModuleSheafPushforwardOfStacks B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))

/-- The unbounded `Rf_*` is a right derived functor of degreewise direct image, with comparison
`AlgebraicGeometry.Stack.fppfDerivedPushforwardOfStacksUnit`. -/
theorem isRightDerivedFunctor_fppfDerivedPushforwardOfStacks :
    (fppfDerivedPushforwardOfStacks B S hS f).IsRightDerivedFunctor
      (fppfDerivedPushforwardOfStacksUnit B S hS f)
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) :=
  have := Functor.hasRightDerivedFunctor_mapHomotopyCategory_of_kInjective
    (fppfModuleSheafPushforwardOfStacks B S hS f)
    (existsKInjectiveResolution_fppfModulesUnivLESucc B S hS 𝒳)
  by
    dsimp only [fppfDerivedPushforwardOfStacks, fppfDerivedPushforwardOfStacksUnit]
    infer_instance

/-- **Stacks 07BC, the right-hand column: the bounded below `Rf_*` is the restriction of the
unbounded one**, an isomorphism `Rf_*⁺ ⋙ ι ≅ ι ⋙ Rf_*` of functors `D⁺(𝒪_𝒳) ⥤ D(𝒪_𝒴)`: the
uniqueness isomorphism of the two right derived functors of degreewise direct image on bounded
below complexes (`CategoryTheory.Functor.boundedDerivedIso`). -/
def fppfDerivedPushforwardPlusOfStacksCompιIso :
    fppfDerivedPushforwardPlusOfStacks B S hS f ⋙ DerivedCategory.Plus.ι ≅
      DerivedCategory.Plus.ι ⋙ fppfDerivedPushforwardOfStacks B S hS f :=
  haveI := isRightDerivedFunctor_fppfDerivedPushforwardOfStacks B S hS f
  Functor.boundedDerivedIso (fppfModuleSheafPushforwardOfStacks B S hS f)
    (fppfDerivedPushforwardOfStacks B S hS f) (fppfDerivedPushforwardOfStacksUnit B S hS f)
    (existsKInjectiveResolution_fppfModulesUnivLESucc B S hS 𝒳)

end AlgebraicGeometry.Stack
