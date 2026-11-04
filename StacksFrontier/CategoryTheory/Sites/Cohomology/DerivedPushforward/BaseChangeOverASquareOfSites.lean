module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekCocontinuousSquare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekContinuousSquare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExactCocontinuous
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.Composition
import StacksCore.Tactic.StacksAttribute

/-!
# Base change for the total direct image over a square of sites

Let
```
  (Sh(C'), O_{C'}) --g'--> (Sh(C), O_C)
        |                      |
        f'                     f
        v                      v
  (Sh(D'), O_{D'}) --g-->  (Sh(D), O_D)
```
be a commutative square of ringed topoi in which the two horizontal morphisms `g`, `g'` come
from functors of sites `v : D' ⥤ D`, `v' : C' ⥤ C` that are continuous as well as cocontinuous,
so that `g^{-1}` and `(g')^{-1}` are restriction along `v` and `v'`, and in which the structure
sheaves pull back correctly: `O_{D'} = g^{-1} O_D` and `O_{C'} = (g')^{-1} O_C`. Then
`g^* = g^{-1}` and `(g')^* = (g')^{-1}` on sheaves of modules, these being
`Stacks.SheafOfModules.inverseImage` of Stacks 0797, and the two vertical morphisms have total
direct images `Rf_*` and `Rf'_*` on the unbounded derived categories of sheaves of modules.
Base change is the assertion
`Rf'_* ∘ (g')^* = g^* ∘ Rf_*` as functors `D(O_C) ⥤ D(O_{D'})`.

It is proved here in two shapes, according to how the vertical morphisms are presented, in each
case with a module-level substitute for condition (6) of the two tags (see *Condition (6)* below):

* the setting of Stacks 0FN7 (second conclusion), where `f` and `f'` come from *continuous*
  functors `u : D ⥤ C`, `u' : D' ⥤ C'` with `v ⋙ u = u' ⋙ v'`, so that `f_*` and `f'_*` are
  restriction along `u` and `u'`;
* Stacks 0FN6, where `f` and `f'` come from *cocontinuous* functors `u : C ⥤ D`,
  `u' : C' ⥤ D'` with `u' ⋙ v = v' ⋙ u`, so that `f_*` and `f'_*` are the direct images
  `{}_su`, `{}_su'` of Stacks 00XO, and where the comparison functors of the index categories
  of Section 00XF are assumed cofinal.

## Main definitions

* `Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeUnit`: for abelian categories and
  functors `α : A ⥤ A'`, `β : B ⥤ B'`, `F : A ⥤ B`, `F' : A' ⥤ B'` with `α ⋙ F' ≅ F ⋙ β`, the
  comparison from `K(F) ⋙ Q ⋙ Dβ` to `Q ⋙ (Dα ⋙ RF')`.
* `Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeIso`: the abstract base change
  isomorphism `Dα ⋙ RF' ≅ RF ⋙ Dβ`.
* `Stacks.Cohomology.UnboundedComplexes.totalRightDerivedOfAdditive`: the total right derived
  functor `RF : D(A) ⥤ D(B)` of an additive functor out of a Grothendieck abelian category,
  which exists with no further hypothesis.
* `Stacks.Cohomology.DerivedBaseChange.inverseImageCompDerivedPushforwardIso`: a
  universe-polymorphic variant of the second conclusion of Stacks 0FN7, for derived functors given
  as data.
* `Stacks.Cohomology.DerivedBaseChange.inverseImageCompTotalDerivedPushforwardIso`: the same
  variant, with `Rf_*` and `Rf'_*` constructed as those total right derived functors rather than
  assumed.

## Main results

* `Stacks.Cohomology.UnboundedComplexes.isIso_derivedBaseChangeUnit_app` and
  `Stacks.Cohomology.UnboundedComplexes.isRightDerivedFunctor_derivedBaseChangeUnit`: the
  comparison is invertible at the K-injective complexes, hence exhibits `Dα ⋙ RF'` as a right
  derived functor of `K(F) ⋙ Q ⋙ Dβ`.
* `Stacks.SheafOfModules.isKInjective_mapHomologicalComplex_inverseImage`: the inverse image
  `g^* = g^{-1}` of sheaves of modules along a continuous and cocontinuous functor of sites
  carries K-injective complexes to K-injective complexes, as soon as its left adjoint `g_!` of
  Stacks 0797 is left exact. This is Stacks 08BJ.
* `Stacks.Cohomology.DerivedBaseChange.nonempty_inverseImage_comp_derivedPushforwardOf_iso`: a
  universe-polymorphic variant of Stacks 0FN6, for derived functors given as data.

## Condition (6)

The source's condition (6) is exactness of the abelian `g'_! : Ab(C') ⥤ Ab(C)`. What is assumed
here instead is left exactness of the module-level `Stacks.SheafOfModules.lowerShriek` of
Stacks 0797, to which Stacks 08BJ is applied directly. By Stacks 0798 the two lower shrieks do not
agree in general, so neither hypothesis implies the other, and the statements here are variants of
the tags rather than the tags themselves. Under condition (6) itself, the second conclusion of
Stacks 0FN7 is
`Stacks.Cohomology.DerivedBaseChange.inverseImageCompTotalDerivedPushforwardIsoOfExactLowerShriek`
and Stacks 0FN6 is
`Stacks.Cohomology.DerivedBaseChange.nonempty_inverseImage_comp_totalDerivedPushforwardOf_iso`,
both for four sites at one universe. The first conclusion of Stacks 0FN7, on the bounded below
derived categories and without condition (6), is
`Stacks.Cohomology.DerivedBaseChange.inverseImageCompDerivedPushforwardPlusIsoOfRingedSite`.

## References

* [Stacks Project, Tag 0FN6](https://stacks.math.columbia.edu/tag/0FN6)
* [Stacks Project, Tag 0FN7](https://stacks.math.columbia.edu/tag/0FN7)
* [Stacks Project, Tag 0FN3](https://stacks.math.columbia.edu/tag/0FN3)
* [Stacks Project, Tag 0FN4](https://stacks.math.columbia.edu/tag/0FN4)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
* [Stacks Project, Tag 0797](https://stacks.math.columbia.edu/tag/0797)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.UnboundedComplexes

universe wA wA' dA dA' dB dB' vA uA vA' uA' vB uB vB' uB'

section BaseChange

variable {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{wA} A]
  [HasDerivedCategory.{dA} A]
  {A' : Type uA'} [Category.{vA'} A'] [Abelian A'] [IsGrothendieckAbelian.{wA'} A']
  [HasDerivedCategory.{dA'} A']
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{dB} B]
  {B' : Type uB'} [Category.{vB'} B'] [Abelian B'] [HasDerivedCategory.{dB'} B']
  (α : A ⥤ A') [α.Additive] [PreservesFiniteLimits α] [PreservesFiniteColimits α]
  (β : B ⥤ B') [β.Additive] [PreservesFiniteLimits β] [PreservesFiniteColimits β]
  (F : A ⥤ B) [F.Additive] (F' : A' ⥤ B') [F'.Additive]
  (RF : DerivedCategory A ⥤ DerivedCategory B)
  (RF' : DerivedCategory A' ⥤ DerivedCategory B')
  (αF : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF)
  (αF' : F'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF')

/-- The base change comparison `K(F) ⋙ Q ⋙ Dβ ⟶ Q ⋙ (Dα ⋙ RF')`, for exact functors
`α : A ⥤ A'`, `β : B ⥤ B'` and an isomorphism `α ⋙ F' ≅ F ⋙ β`.

It is the composite of the identification of `Q ⋙ Dβ` with `K(β) ⋙ Q`, the isomorphism
`K(F) ⋙ K(β) ≅ K(α) ⋙ K(F')` that the given isomorphism induces on homotopy categories, the
comparison `αF'` of `RF'` whiskered with `K(α)`, and the identification of `K(α) ⋙ Q` with
`Q ⋙ Dα`. Only the third factor is not invertible. -/
def derivedBaseChangeUnit (e : α ⋙ F' ≅ F ⋙ β) :
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⋙
        β.mapDerivedCategory ⟶
      DerivedCategory.Qh ⋙ (α.mapDerivedCategory ⋙ RF') :=
  Functor.whiskerLeft (F.mapHomotopyCategory (ComplexShape.up ℤ))
      β.mapDerivedCategoryFactorsh.hom ≫
    Functor.whiskerRight
      ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ β)) (ComplexShape.up ℤ)) ≪≫
        (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).symm).hom
      DerivedCategory.Qh ≫
    Functor.whiskerLeft (α.mapHomotopyCategory (ComplexShape.up ℤ)) αF' ≫
    Functor.whiskerRight α.mapDerivedCategoryFactorsh.inv RF'

omit [IsGrothendieckAbelian.{wA} A] [IsGrothendieckAbelian.{wA'} A'] in
/-- The base change comparison is invertible at a complex whose image under `α` already computes
`RF'`. -/
theorem isIso_derivedBaseChangeUnit_app_of_isIso (e : α ⋙ F' ≅ F ⋙ β) (I : CochainComplex A ℤ)
    (hI : IsIso (αF'.app ((α.mapHomotopyCategory (ComplexShape.up ℤ)).obj
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))) :
    IsIso ((derivedBaseChangeUnit α β F F' RF' αF' e).app
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) := by
  have h := hI
  dsimp only [derivedBaseChangeUnit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  infer_instance

omit [IsGrothendieckAbelian.{wA} A] in
/-- The base change comparison is invertible at a K-injective complex, if `α` preserves
K-injectivity of complexes. -/
theorem isIso_derivedBaseChangeUnit_app (e : α ⋙ F' ≅ F ⋙ β)
    [RF'.IsRightDerivedFunctor αF' (HomotopyCategory.quasiIso A' (ComplexShape.up ℤ))]
    (hKinj : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      CochainComplex.IsKInjective ((α.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))
    (I : CochainComplex A ℤ) (hI : I.IsKInjective) :
    IsIso ((derivedBaseChangeUnit α β F F' RF' αF' e).app
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) :=
  isIso_derivedBaseChangeUnit_app_of_isIso α β F F' RF' αF' e I
    (isIso_app_of_isKInjective _ _ RF' αF' _ (hKinj I hI))

omit [IsGrothendieckAbelian.{wA'} A'] in
/-- `Dα ⋙ RF'`, with the base change comparison, is a right derived functor of
`K(F) ⋙ Q ⋙ Dβ`, as soon as `α(I)` computes `RF'` for every K-injective `I`. -/
theorem isRightDerivedFunctor_derivedBaseChangeUnit_of_isIso (e : α ⋙ F' ≅ F ⋙ β)
    (hunit : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      IsIso (αF'.app ((α.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))) :
    (α.mapDerivedCategory ⋙ RF').IsRightDerivedFunctor
      (derivedBaseChangeUnit α β F F' RF' αF' e)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_of_isIso_app_isKInjective
    ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⋙
      β.mapDerivedCategory) DerivedCategory.Qh _ _
    fun I hI => isIso_derivedBaseChangeUnit_app_of_isIso α β F F' RF' αF' e I (hunit I hI)

/-- `Dα ⋙ RF'`, with the base change comparison, is a right derived functor of
`K(F) ⋙ Q ⋙ Dβ`. -/
theorem isRightDerivedFunctor_derivedBaseChangeUnit (e : α ⋙ F' ≅ F ⋙ β)
    [RF'.IsRightDerivedFunctor αF' (HomotopyCategory.quasiIso A' (ComplexShape.up ℤ))]
    (hKinj : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      CochainComplex.IsKInjective ((α.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :
    (α.mapDerivedCategory ⋙ RF').IsRightDerivedFunctor
      (derivedBaseChangeUnit α β F F' RF' αF' e)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_derivedBaseChangeUnit_of_isIso α β F F' RF' αF' e
    fun I hI => isIso_app_of_isKInjective _ _ RF' αF' _ (hKinj I hI)

/-- **Base change for right derived functors.** Let `α : A ⥤ A'` and `β : B ⥤ B'` be exact
functors of abelian categories with `A`, `A'` Grothendieck abelian, let `F : A ⥤ B` and
`F' : A' ⥤ B'` be additive with right derived functors `RF`, `RF'` on the unbounded derived
categories, let `α ⋙ F' ≅ F ⋙ β`, and assume `α(I)` computes `RF'` for every K-injective `I`.
Then `Dα ⋙ RF' ≅ RF ⋙ Dβ`. -/
def derivedBaseChangeIsoOfUnit (e : α ⋙ F' ≅ F ⋙ β)
    [RF.IsRightDerivedFunctor αF (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (hunit : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      IsIso (αF'.app ((α.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))) :
    α.mapDerivedCategory ⋙ RF' ≅ RF ⋙ β.mapDerivedCategory :=
  haveI := isRightDerivedFunctor_derivedBaseChangeUnit_of_isIso α β F F' RF' αF' e hunit
  haveI := isRightDerivedFunctor_comp (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh) DerivedCategory.Qh RF αF β.mapDerivedCategory
  haveI : IsIso ((α.mapDerivedCategory ⋙ RF').rightDerivedDesc
      (derivedBaseChangeUnit α β F F' RF' αF' e)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) (RF ⋙ β.mapDerivedCategory)
      (Functor.whiskerRight αF β.mapDerivedCategory ≫ (Functor.associator _ _ _).hom)) :=
    (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc _
      (derivedBaseChangeUnit α β F F' RF' αF' e)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) _ _).1 inferInstance
  asIso ((α.mapDerivedCategory ⋙ RF').rightDerivedDesc
    (derivedBaseChangeUnit α β F F' RF' αF' e)
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) (RF ⋙ β.mapDerivedCategory)
    (Functor.whiskerRight αF β.mapDerivedCategory ≫ (Functor.associator _ _ _).hom))

/-- **Base change for right derived functors**, with `α` assumed to preserve K-injectivity. -/
def derivedBaseChangeIso (e : α ⋙ F' ≅ F ⋙ β)
    [RF.IsRightDerivedFunctor αF (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    [RF'.IsRightDerivedFunctor αF' (HomotopyCategory.quasiIso A' (ComplexShape.up ℤ))]
    (hKinj : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      CochainComplex.IsKInjective ((α.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :
    α.mapDerivedCategory ⋙ RF' ≅ RF ⋙ β.mapDerivedCategory :=
  derivedBaseChangeIsoOfUnit α β F F' RF RF' αF αF' e
    fun I hI => isIso_app_of_isKInjective (F'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh) DerivedCategory.Qh RF' αF' _ (hKinj I hI)

end BaseChange

section Total

variable {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{wA} A]
  [HasDerivedCategory.{dA} A] {B : Type uB} [Category.{vB} B] [Abelian B]
  [HasDerivedCategory.{dB} B] (F : A ⥤ B) [F.Additive]

/-- Degreewise `F`, read as a functor from the unbounded homotopy category `K(A)` to the
unbounded derived category `D(B)`. Its right derived functor is `RF : D(A) ⥤ D(B)`. -/
abbrev onHomotopyToDerived : HomotopyCategory A (ComplexShape.up ℤ) ⥤ DerivedCategory B :=
  F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- Over a Grothendieck abelian source every functor out of `K(A)` has a pointwise right
derived functor. -/
@[sga "4 XVII 4.1.2" "partial"]
instance hasPointwiseRightDerivedFunctor_onHomotopyToDerived :
    (onHomotopyToDerived F).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  hasPointwiseRightDerivedFunctor _

/-- The total right derived functor `RF : D(A) ⥤ D(B)` of an additive functor `F : A ⥤ B` out
of a Grothendieck abelian category. -/
@[sga "4 XVII 1.2.3" "(i), special case",
  sga "4 XVII 4.1.2" "construction of Rf*",
  sga "4½ Etat_0 4.2.3" "(a), right-derived case"]
abbrev totalRightDerivedOfAdditive : DerivedCategory A ⥤ DerivedCategory B :=
  (onHomotopyToDerived F).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))

/-- The canonical comparison from degreewise `F` to the total right derived functor
`totalRightDerivedOfAdditive F`. -/
abbrev totalRightDerivedOfAdditiveUnit :
    onHomotopyToDerived F ⟶ DerivedCategory.Qh ⋙ totalRightDerivedOfAdditive F :=
  (onHomotopyToDerived F).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))

end Total

end Stacks.Cohomology.UnboundedComplexes

namespace Stacks.SheafOfModules

universe m r v₁ u₁ v₂ u₂

section InverseImage

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (w : C ⥤ D)
  [w.IsContinuous J K] [w.IsCocontinuous J K] (O : Sheaf K RingCat.{r})
  [HasSheafify J AddCommGrpCat.{m}] [HasSheafify K AddCommGrpCat.{m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [K.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- The inverse image `g^* = g^{-1}` of sheaves of modules is additive, being a direct image
along a continuous functor of sites. -/
instance additive_inverseImage_of_isCocontinuous : (inverseImage.{m} J K w O).Additive :=
  inferInstanceAs (_root_.SheafOfModules.pushforward.{m} (structureMap J K w O)).Additive

/-- The inverse image `g^* = g^{-1}` of sheaves of modules preserves finite limits, being a
direct image along a continuous functor of sites. -/
@[sga "4 IV 11.2.2" "more general"]
instance preservesFiniteLimits_inverseImage :
    PreservesFiniteLimits (inverseImage.{m} J K w O) :=
  inferInstanceAs
    (PreservesFiniteLimits (_root_.SheafOfModules.pushforward.{m} (structureMap J K w O)))

/-- The inverse image `g^* = g^{-1}` of sheaves of modules along a continuous and cocontinuous
functor of sites preserves finite colimits. -/
@[ega "0 4.3.2" "finite sums, partial",
  sga "4 IV 13.6" "special case",
  sga "4 IV 3.1.2" "partial, special case"]
instance preservesFiniteColimits_inverseImage :
    PreservesFiniteColimits (inverseImage.{m} J K w O) :=
  PushforwardRightExact.preservesFiniteColimits_pushforward_of_isAlmostCocontinuous w
    (structureMap J K w O) (isAlmostCocontinuous_of_isCocontinuous w J K)

variable [UnivLE.{r, m}] [UnivLE.{v₁, m}] [UnivLE.{v₂, m}] [UnivLE.{u₁, m}]

/-- Lower shriek `g_!` on sheaves of modules is additive, being a left adjoint between
preadditive categories with binary biproducts. -/
instance additive_lowerShriek : (lowerShriek.{m} J K w O).Additive := by
  have : PreservesColimitsOfSize.{0, 0} (lowerShriek.{m} J K w O) :=
    Adjunction.leftAdjoint_preservesColimits (lowerShriekAdjunction.{m} J K w O)
  have hz : (lowerShriek.{m} J K w O).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_initial_object
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (lowerShriek.{m} J K w O)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Lower shriek `g_!` on sheaves of modules preserves finite colimits, being a left adjoint. -/
instance preservesFiniteColimits_lowerShriek :
    PreservesFiniteColimits (lowerShriek.{m} J K w O) := by
  refine ⟨fun _ _ _ => ?_⟩
  have : PreservesColimitsOfSize.{0, 0} (lowerShriek.{m} J K w O) :=
    Adjunction.leftAdjoint_preservesColimits (lowerShriekAdjunction.{m} J K w O)
  infer_instance

/-- **Stacks 08BJ for the inverse image of sheaves of modules.** If lower shriek
`g_! : Mod(O_C) ⥤ Mod(O_D)` of Stacks 0797 is left exact — it is always right exact, being a
left adjoint — then the inverse image `g^* = g^{-1}` carries K-injective complexes of
`O_D`-modules to K-injective complexes of `O_C`-modules. -/
theorem isKInjective_mapHomologicalComplex_inverseImage
    [PreservesFiniteLimits (lowerShriek.{m} J K w O)]
    (I : CochainComplex (_root_.SheafOfModules.{m} O) ℤ) (hI : I.IsKInjective) :
    CochainComplex.IsKInjective
      (((inverseImage.{m} J K w O).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  have := hI
  CochainComplex.isKInjective_mapHomologicalComplex_of_exact (inverseImage.{m} J K w O)
    (lowerShriek.{m} J K w O) (lowerShriekAdjunction.{m} J K w O) I

end InverseImage

section Cocontinuous

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (w : C ⥤ D)
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} [w.IsCocontinuous J K]
  [∀ G : Cᵒᵖ ⥤ RingCat.{r}, w.op.HasPointwiseRightKanExtension G]
  [∀ G : Cᵒᵖ ⥤ AddCommGrpCat.{m}, w.op.HasPointwiseRightKanExtension G]
  {OC : Sheaf J RingCat.{r}} {OD : Sheaf K RingCat.{r}}

/-- Right Kan extension of presheaves of abelian groups is additive, being a right adjoint. -/
instance additive_op_ran :
    (w.op.ran : (Cᵒᵖ ⥤ AddCommGrpCat.{m}) ⥤ (Dᵒᵖ ⥤ AddCommGrpCat.{m})).Additive := by
  have : (w.op.ran : (Cᵒᵖ ⥤ AddCommGrpCat.{m}) ⥤ (Dᵒᵖ ⥤ AddCommGrpCat.{m})).IsRightAdjoint :=
    ⟨_, ⟨w.op.ranAdjunction AddCommGrpCat.{m}⟩⟩
  have : PreservesLimitsOfSize.{0, 0}
      (w.op.ran : (Cᵒᵖ ⥤ AddCommGrpCat.{m}) ⥤ (Dᵒᵖ ⥤ AddCommGrpCat.{m})) :=
    Adjunction.rightAdjoint_preservesLimits (Adjunction.ofIsRightAdjoint
      (w.op.ran : (Cᵒᵖ ⥤ AddCommGrpCat.{m}) ⥤ (Dᵒᵖ ⥤ AddCommGrpCat.{m})))
  exact Functor.additive_of_preserves_binary_products _

/-- The direct image `{}_sw` of sheaves of abelian groups along a cocontinuous functor of sites
is additive: on underlying presheaves it is right Kan extension along `w.op`, and the forgetful
functor to presheaves is faithful and additive. -/
instance additive_sheafPushforwardCocontinuous :
    (w.sheafPushforwardCocontinuous AddCommGrpCat.{m} J K).Additive where
  map_add {_ _} f g := (sheafToPresheaf K AddCommGrpCat.{m}).map_injective (by
    change w.op.ran.map ((sheafToPresheaf J AddCommGrpCat.{m}).map (f + g)) = _
    rw [Functor.map_add, Functor.map_add, Functor.map_add]; rfl)

/-- The direct image of sheaves of modules along the morphism of topoi attached to a
cocontinuous functor of sites is additive: its underlying sheaf of abelian groups is `{}_sw`,
and the forgetful functor to sheaves of abelian groups is faithful and additive. -/
instance additive_pushforwardCocontinuous
    (fSharp : OD ⟶ (w.sheafPushforwardCocontinuous RingCat.{r} J K).obj OC) :
    (pushforwardCocontinuous.{m} w fSharp).Additive where
  map_add {_ _} f g := (_root_.SheafOfModules.toSheaf.{m} OD).map_injective (by
    change (w.sheafPushforwardCocontinuous AddCommGrpCat.{m} J K).map
        ((_root_.SheafOfModules.toSheaf.{m} OC).map (f + g)) = _
    rw [Functor.map_add, Functor.map_add, Functor.map_add]; rfl)

end Cocontinuous

end Stacks.SheafOfModules

namespace Stacks.Cohomology.DerivedBaseChange

open Stacks.SheafOfModules

universe m r dC dC' dD dD' v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

section ContinuousRows

variable {C' : Type u₁} [Category.{v₁} C'] {C : Type u₂} [Category.{v₂} C] {D' : Type u₃}
  [Category.{v₃} D'] {D : Type u₄} [Category.{v₄} D] (J' : GrothendieckTopology C')
  (J : GrothendieckTopology C) (K' : GrothendieckTopology D') (K : GrothendieckTopology D)
  (u : D ⥤ C) (u' : D' ⥤ C') (v : D' ⥤ D) (v' : C' ⥤ C) [u.IsContinuous K J]
  [u'.IsContinuous K' J'] [v.IsContinuous K' K] [v.IsCocontinuous K' K] [v'.IsContinuous J' J]
  [v'.IsCocontinuous J' J] (OC : Sheaf J RingCat.{r}) (OD : Sheaf K RingCat.{r})
  (fSharp : OD ⟶ (u.sheafPushforwardContinuous RingCat.{r} K J).obj OC)
  (f'Sharp : inverseImageRing K' K v OD ⟶
    (u'.sheafPushforwardContinuous RingCat.{r} K' J').obj (inverseImageRing J' J v' OC))
  [HasSheafify J AddCommGrpCat.{m}] [HasSheafify J' AddCommGrpCat.{m}]
  [HasSheafify K AddCommGrpCat.{m}] [HasSheafify K' AddCommGrpCat.{m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [J'.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{m}] [K'.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [UnivLE.{r, m}] [UnivLE.{u₁, m}] [UnivLE.{v₁, m}] [UnivLE.{u₂, m}] [UnivLE.{v₂, m}]
  [HasDerivedCategory.{dC} (_root_.SheafOfModules.{m} OC)]
  [HasDerivedCategory.{dC'} (_root_.SheafOfModules.{m} (inverseImageRing J' J v' OC))]
  [HasDerivedCategory.{dD} (_root_.SheafOfModules.{m} OD)]
  [HasDerivedCategory.{dD'} (_root_.SheafOfModules.{m} (inverseImageRing K' K v OD))]
  (Rf : DerivedCategory (_root_.SheafOfModules.{m} OC) ⥤
    DerivedCategory (_root_.SheafOfModules.{m} OD))
  (Rf' : DerivedCategory (_root_.SheafOfModules.{m} (inverseImageRing J' J v' OC)) ⥤
    DerivedCategory (_root_.SheafOfModules.{m} (inverseImageRing K' K v OD)))
  (αf : (_root_.SheafOfModules.pushforward.{m} fSharp).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf)
  (αf' : (_root_.SheafOfModules.pushforward.{m} f'Sharp).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf')

/-- **A universe-polymorphic variant of the second conclusion of Stacks 0FN7**, not the tag's
own statement of it, with the derived functors carried as data. For a commutative square of
ringed topoi whose horizontal functors `u : D ⥤ C`, `u' : D' ⥤ C'` are continuous — giving
`f`, `f'` with `f_* = u^s`, `f'_* = (u')^s` — whose vertical functors `v : D' ⥤ D`,
`v' : C' ⥤ C` are continuous as well as cocontinuous — giving `g`, `g'` with `g^{-1}`,
`(g')^{-1}` restriction — with `v ⋙ u = u' ⋙ v'` and with `g^{-1} O_D = O_{D'}`,
`(g')^{-1} O_C = O_{C'}`, we have `Rf'_* ∘ (g')^* ≅ g^* ∘ Rf_*` as functors
`D(O_C) ⥤ D(O_{D'})`.

Condition (5) is built into the statement by taking the restrictions along `v` and `v'` as
*the* sheaves of rings on `D'` and `C'`, so that `g^* = g^{-1}` and `(g')^* = (g')^{-1}` are
`Stacks.SheafOfModules.inverseImage` and are exact; and the commutativity of the square of
ringed topoi is `hcomm`, as in Stacks 0FN4. The underived identity
`f'_* ∘ (g')^* = g^* ∘ f_*` is that tag.

In place of the source's condition (6), exactness of the abelian `g'_! : Ab(C') ⥤ Ab(C)`, the
statement assumes `PreservesFiniteLimits (lowerShriek J' J v' OC)`, left exactness of the lower
shriek of Stacks 0797 on sheaves of *modules*; by Stacks 0798 the two lower shrieks do not agree
in general. -/
def inverseImageCompDerivedPushforwardIso
    [Rf.IsRightDerivedFunctor αf
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{m} OC) (ComplexShape.up ℤ))]
    [Rf'.IsRightDerivedFunctor αf'
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{m} (inverseImageRing J' J v' OC))
        (ComplexShape.up ℤ))]
    [PreservesFiniteLimits (lowerShriek.{m} J' J v' OC)] (hsq : v ⋙ u = u' ⋙ v')
    (hcomm : f'Sharp = restrictStructureMap J' J K' K u u' v v' OC OD fSharp hsq) :
    (inverseImage.{m} J' J v' OC).mapDerivedCategory ⋙ Rf' ≅
      Rf ⋙ (inverseImage.{m} K' K v OD).mapDerivedCategory :=
  UnboundedComplexes.derivedBaseChangeIso (inverseImage.{m} J' J v' OC)
    (inverseImage.{m} K' K v OD) (_root_.SheafOfModules.pushforward.{m} fSharp)
    (_root_.SheafOfModules.pushforward.{m} f'Sharp) Rf Rf' αf αf'
    (eqToIso (inverseImage_comp_pushforward_eq.{m} J' J K' K u u' v v' OC OD fSharp f'Sharp hsq
      hcomm))
    fun I hI => isKInjective_mapHomologicalComplex_inverseImage J' J v' OC I hI

end ContinuousRows

section CocontinuousColumns

variable {C' : Type u₁} [Category.{v₁} C'] {C : Type u₂} [Category.{v₂} C] {D' : Type u₃}
  [Category.{v₃} D'] {D : Type u₄} [Category.{v₄} D] (J' : GrothendieckTopology C')
  (J : GrothendieckTopology C) (K' : GrothendieckTopology D') (K : GrothendieckTopology D)
  (u' : C' ⥤ D') (u : C ⥤ D) (v' : C' ⥤ C) (v : D' ⥤ D) [u.IsCocontinuous J K]
  [u'.IsCocontinuous J' K'] [v.IsContinuous K' K] [v.IsCocontinuous K' K]
  [v'.IsContinuous J' J] [v'.IsCocontinuous J' J]
  [∀ G : Cᵒᵖ ⥤ AddCommGrpCat.{m}, u.op.HasPointwiseRightKanExtension G]
  [∀ G : C'ᵒᵖ ⥤ AddCommGrpCat.{m}, u'.op.HasPointwiseRightKanExtension G]
  [∀ G : Cᵒᵖ ⥤ RingCat.{r}, u.op.HasPointwiseRightKanExtension G]
  [∀ G : C'ᵒᵖ ⥤ RingCat.{r}, u'.op.HasPointwiseRightKanExtension G]
  (OC : Sheaf J RingCat.{r}) (OD : Sheaf K RingCat.{r})
  (fSharp : OD ⟶ (u.sheafPushforwardCocontinuous RingCat.{r} J K).obj OC)
  (f'Sharp : inverseImageRing K' K v OD ⟶
    (u'.sheafPushforwardCocontinuous RingCat.{r} J' K').obj (inverseImageRing J' J v' OC))
  [HasSheafify J AddCommGrpCat.{m}] [HasSheafify J' AddCommGrpCat.{m}]
  [HasSheafify K AddCommGrpCat.{m}] [HasSheafify K' AddCommGrpCat.{m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [J'.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{m}] [K'.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [UnivLE.{r, m}] [UnivLE.{u₁, m}] [UnivLE.{v₁, m}] [UnivLE.{u₂, m}] [UnivLE.{v₂, m}]
  [HasDerivedCategory.{dC} (_root_.SheafOfModules.{m} OC)]
  [HasDerivedCategory.{dC'} (_root_.SheafOfModules.{m} (inverseImageRing J' J v' OC))]
  [HasDerivedCategory.{dD} (_root_.SheafOfModules.{m} OD)]
  [HasDerivedCategory.{dD'} (_root_.SheafOfModules.{m} (inverseImageRing K' K v OD))]
  (Rf : DerivedCategory (_root_.SheafOfModules.{m} OC) ⥤
    DerivedCategory (_root_.SheafOfModules.{m} OD))
  (Rf' : DerivedCategory (_root_.SheafOfModules.{m} (inverseImageRing J' J v' OC)) ⥤
    DerivedCategory (_root_.SheafOfModules.{m} (inverseImageRing K' K v OD)))
  (αf : (pushforwardCocontinuous.{m} u fSharp).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf)
  (αf' : (pushforwardCocontinuous.{m} u' f'Sharp).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf')

/-- **A universe-polymorphic variant of Stacks 0FN6**, not the tag's own statement of it, with
the derived functors carried as data. For a commutative square of ringed topoi whose four
functors `u : C ⥤ D`, `u' : C' ⥤ D'`, `v : D' ⥤ D`, `v' : C' ⥤ C` are cocontinuous — giving `f`,
`f'`, `g`, `g'` with `f_* = {}_su`, `f'_* = {}_su'` — with `u' ⋙ v = v' ⋙ u`, with `v` and `v'`
continuous as well as cocontinuous, with the comparison functors
`{}^{u'}_{V'} I ⥤ {}^u_{v(V')} I` of the index categories of Section 00XF all cofinal, and with
`g^{-1} O_D = O_{D'}`, `(g')^{-1} O_C = O_{C'}`, we have `Rf'_* ∘ (g')^* ≅ g^* ∘ Rf_*` as
functors `D(O_C) ⥤ D(O_{D'})`.

Condition (5) is built into the statement by taking the restrictions along `v` and `v'` as
*the* sheaves of rings on `D'` and `C'`, so that `g^* = g^{-1}` and `(g')^* = (g')^{-1}` are
`Stacks.SheafOfModules.inverseImage` and are exact. The underived identity is Stacks 0FN3, which
is what the cofinality hypothesis `hfinal` — condition (4) — feeds, and `(f')^♯` is the
structure map the square forces, as in that tag.

In place of the source's condition (6), exactness of the abelian `g'_! : Ab(C') ⥤ Ab(C)`, the
statement assumes `PreservesFiniteLimits (lowerShriek J' J v' OC)`, left exactness of the lower
shriek of Stacks 0797 on sheaves of *modules*; by Stacks 0798 the two lower shrieks do not agree
in general. -/
theorem nonempty_inverseImage_comp_derivedPushforwardOf_iso
    [Rf.IsRightDerivedFunctor αf
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{m} OC) (ComplexShape.up ℤ))]
    [Rf'.IsRightDerivedFunctor αf'
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{m} (inverseImageRing J' J v' OC))
        (ComplexShape.up ℤ))]
    [PreservesFiniteLimits (lowerShriek.{m} J' J v' OC)] (hsq : u' ⋙ v = v' ⋙ u)
    (hcomm : f'Sharp = structureMapSquare (J' := J') (K' := K') fSharp hsq)
    (hfinal : ∀ V' : D',
      (CostructuredArrow.map₂ (S := u') (T := V') (U := u) (V := v.obj V') (F := v') (G := v)
        (eqToHom hsq.symm) (𝟙 (v.obj V'))).Final) :
    Nonempty ((inverseImage.{m} J' J v' OC).mapDerivedCategory ⋙ Rf' ≅
      Rf ⋙ (inverseImage.{m} K' K v OD).mapDerivedCategory) := by
  subst hcomm
  obtain ⟨e⟩ := nonempty_inverseImage_comp_cocontinuousPushforwardOf_iso.{m} J' J K' K u' u v' v
    OC OD fSharp hsq hfinal
  exact ⟨UnboundedComplexes.derivedBaseChangeIso (inverseImage.{m} J' J v' OC)
    (inverseImage.{m} K' K v OD) (pushforwardCocontinuous.{m} u fSharp)
    (pushforwardCocontinuous.{m} u' (structureMapSquare (J' := J') (K' := K') fSharp hsq))
    Rf Rf' αf αf' e
    fun I hI => isKInjective_mapHomologicalComplex_inverseImage J' J v' OC I hI⟩

end CocontinuousColumns

section ContinuousRowsTotal

variable {C' : Type u₁} [Category.{v₁} C'] {C : Type u₂} [Category.{v₂} C] {D' : Type u₃}
  [Category.{v₃} D'] {D : Type u₄} [Category.{v₄} D] (J' : GrothendieckTopology C')
  (J : GrothendieckTopology C) (K' : GrothendieckTopology D') (K : GrothendieckTopology D)
  (u : D ⥤ C) (u' : D' ⥤ C') (v : D' ⥤ D) (v' : C' ⥤ C) [u.IsContinuous K J]
  [u'.IsContinuous K' J'] [v.IsContinuous K' K] [v.IsCocontinuous K' K] [v'.IsContinuous J' J]
  [v'.IsCocontinuous J' J] (OC : Sheaf J RingCat.{r}) (OD : Sheaf K RingCat.{r})
  (fSharp : OD ⟶ (u.sheafPushforwardContinuous RingCat.{r} K J).obj OC)
  (f'Sharp : inverseImageRing K' K v OD ⟶
    (u'.sheafPushforwardContinuous RingCat.{r} K' J').obj (inverseImageRing J' J v' OC))
  [HasSheafify J AddCommGrpCat.{m}] [HasSheafify J' AddCommGrpCat.{m}]
  [HasSheafify K AddCommGrpCat.{m}] [HasSheafify K' AddCommGrpCat.{m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [J'.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{m}] [K'.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [UnivLE.{r, m}] [UnivLE.{u₁, m}] [UnivLE.{v₁, m}] [UnivLE.{u₂, m}] [UnivLE.{v₂, m}]
  [HasDerivedCategory.{dC} (_root_.SheafOfModules.{m} OC)]
  [HasDerivedCategory.{dC'} (_root_.SheafOfModules.{m} (inverseImageRing J' J v' OC))]
  [HasDerivedCategory.{dD} (_root_.SheafOfModules.{m} OD)]
  [HasDerivedCategory.{dD'} (_root_.SheafOfModules.{m} (inverseImageRing K' K v OD))]

/-- **A universe-polymorphic variant of the second conclusion of Stacks 0FN7**, not the tag's
own statement of it, with the two total direct images *constructed* rather than assumed. For a
commutative square of ringed topoi whose horizontal functors `u : D ⥤ C`, `u' : D' ⥤ C'` are
continuous — giving `f`, `f'` with `f_* = u^s`, `f'_* = (u')^s` — whose vertical functors
`v : D' ⥤ D`, `v' : C' ⥤ C` are continuous as well as cocontinuous — giving `g`, `g'` with
`g^{-1}`, `(g')^{-1}` restriction — with `v ⋙ u = u' ⋙ v'` and with `g^{-1} O_D = O_{D'}`,
`(g')^{-1} O_C = O_{C'}`, we have `Rf'_* ∘ (g')^* ≅ g^* ∘ Rf_*` as functors
`D(O_C) ⥤ D(O_{D'})`.

Both `Rf_*` and `Rf'_*` are here the total right derived functors
`Stacks.Cohomology.UnboundedComplexes.totalRightDerivedOfAdditive` of the degreewise direct
images. In place of the source's condition (6), exactness of the abelian
`g'_! : Ab(C') ⥤ Ab(C)`, the statement assumes `PreservesFiniteLimits (lowerShriek J' J v' OC)`,
left exactness of the lower shriek of Stacks 0797 on sheaves of *modules*; by Stacks 0798 the two
lower shrieks do not agree in general. -/
@[sga "4 XVII 4.1.5" "(i), special case"]
def inverseImageCompTotalDerivedPushforwardIso
    [PreservesFiniteLimits (lowerShriek.{m} J' J v' OC)] (hsq : v ⋙ u = u' ⋙ v')
    (hcomm : f'Sharp = restrictStructureMap J' J K' K u u' v v' OC OD fSharp hsq) :
    (inverseImage.{m} J' J v' OC).mapDerivedCategory ⋙
        UnboundedComplexes.totalRightDerivedOfAdditive
          (_root_.SheafOfModules.pushforward.{m} f'Sharp) ≅
      UnboundedComplexes.totalRightDerivedOfAdditive
          (_root_.SheafOfModules.pushforward.{m} fSharp) ⋙
        (inverseImage.{m} K' K v OD).mapDerivedCategory :=
  inverseImageCompDerivedPushforwardIso.{m} J' J K' K u u' v v' OC OD fSharp f'Sharp
    (UnboundedComplexes.totalRightDerivedOfAdditive
      (_root_.SheafOfModules.pushforward.{m} fSharp))
    (UnboundedComplexes.totalRightDerivedOfAdditive
      (_root_.SheafOfModules.pushforward.{m} f'Sharp))
    (UnboundedComplexes.totalRightDerivedOfAdditiveUnit
      (_root_.SheafOfModules.pushforward.{m} fSharp))
    (UnboundedComplexes.totalRightDerivedOfAdditiveUnit
      (_root_.SheafOfModules.pushforward.{m} f'Sharp))
    hsq hcomm

end ContinuousRowsTotal

end Stacks.Cohomology.DerivedBaseChange

end
