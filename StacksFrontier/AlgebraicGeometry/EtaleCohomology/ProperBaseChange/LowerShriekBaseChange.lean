module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.BaseChangeCompactification
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowCoreflection
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeCommutation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.Compactifications
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.CompactificationsUnconditional
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TrivialityAndGlobalSections

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.LowerShriekCompactification

/-!
# Base change for the derived lower shriek

Consider a cartesian square of schemes
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
and a compactification `j : X ⟶ X̄`, `f̄ : X̄ ⟶ Y` of `X` over `Y`. Its base change
`j' : X' ⟶ X̄' = X̄ ×_Y Y'`, `f̄' : X̄' ⟶ Y'` is a compactification of `X'` over `Y'`, and
[Stacks, Tag 0F7L] constructs the base change isomorphism `g^{-1} ∘ Rf_! ≅ Rf'_! ∘ (g')^{-1}` as
```
g^{-1} ∘ Rf̄_* ∘ Rj_! ⟶ Rf̄'_* ∘ (ḡ')^{-1} ∘ Rj_! ≅ Rf̄'_* ∘ Rj'_! ∘ (g')^{-1},
```
the first arrow being the base change map of the proper morphism `f̄` (an isomorphism on bounded
below objects with torsion cohomology by the proper base change theorem, Tag 0DDE) and the second
the derived form of the base change of extension by zero, Tag 03S6 (Tag 0F55).

## Main definitions

All names below are in the namespace `Stacks.EtaleCohomology`.

* `etaleModuleDerivedExtensionByZeroInverseImageIso` — Tag 03S6 on `D(-_étale, Λ)`, for an
  arbitrary cartesian square along an étale morphism.
* `derivedLowerShriekBaseChangeGeneral` — the map `g^{-1} ∘ Rf_! ⟶ Rf'_! ∘ (g')^{-1}` on
  `D(-_étale, Λ)`, through `j` and its base change.

## Main results

* `isIso_derivedLowerShriekBaseChange_app_of_cohomologyCommutesWithBaseChange` — the map is an
  isomorphism on bounded below objects whose underlying complex of abelian sheaves has torsion
  cohomology, granted that cohomology commutes with base change for `f̄`.
* `isIso_derivedLowerShriekBaseChange_app_of_proper_base_change` — the same granted the proper
  base change theorem (Tag 095T) as a hypothesis.

## Implementation notes

The base change of the compactification is the base's
`AlgebraicGeometry.CompactificationOf.baseChange`.

The statement is made for a chosen compactification `j` of `f`; the existence of one for `f`
separated of finite type between quasi-compact and quasi-separated schemes is Nagata's theorem
(Tag 0F41), and the independence of the choice is Tag 0F7I. The compatibility of these
isomorphisms with the composition isomorphisms of Tag 0F7J, the second assertion of Tag 0F7L, is
`Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompIso_baseChange`.

## References

* [Stacks Project, Tag 0F7L](https://stacks.math.columbia.edu/tag/0F7L)
* [Stacks Project, Tag 0DDE](https://stacks.math.columbia.edu/tag/0DDE)
* [Stacks Project, Tag 03S6](https://stacks.math.columbia.edu/tag/03S6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u r

attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace Stacks.EtaleCohomology

open AlgebraicGeometry.CompactificationOf

variable (Λ : Type r) [Ring Λ]
  {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  (sq : IsPullback g' f' f g) (j : CompactificationOf (Over.mk f))

/-- **[Stacks, Tag 03S6] on `D(-_étale, Λ)`.** For a cartesian square
```
YU --pY--> Y
|hU        |h
v          v
U  --j-->  X
```
with `j` étale, `Rj_! ⋙ h^{-1} ≅ hU^{-1} ⋙ RpY_!`. Both extensions by zero are exact, so this
is the underived isomorphism `Stacks.EtaleCohomology.etaleModuleInverseImageExtensionByZeroIso`
applied degreewise. For the open immersion of a compactification and its base change it is the
second factor of the base change map of Tag 0F7L. -/
def etaleModuleDerivedExtensionByZeroInverseImageIso {X₁ Y₁ U₁ YU₁ : Scheme.{u}} {h : Y₁ ⟶ X₁}
    {ι : U₁ ⟶ X₁} [Etale ι] {hU : YU₁ ⟶ U₁} {pY : YU₁ ⟶ Y₁} [Etale pY]
    (upper : IsPullback hU pY ι h) :
    etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ ι ⋙
        etaleModuleDerivedInverseImageGeneral.{u, r} Λ h ≅
      etaleModuleDerivedInverseImageGeneral.{u, r} Λ hU ⋙
        etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ pY :=
  Functor.isoWhiskerRight (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ ι) _ ≪≫
    (DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _).symm ≪≫
    DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      (etaleModuleInverseImageExtensionByZeroIso.{u, r} Λ upper).symm ≪≫
    DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.isoWhiskerLeft _ (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ pY).symm

/-- **The base change map of [Stacks, Tag 0F7L]**, `g^{-1} ∘ Rf_! ⟶ Rf'_! ∘ (g')^{-1}` on
`D(-_étale, Λ)`, for a cartesian square of `f` along `g`, with `Rf_!` computed through the
compactification `j` and `Rf'_!` through its base change `j'`. It is
```
g^{-1} Rf̄_* Rj_! ⟶ Rf̄'_* ḡ'^{-1} Rj_! ≅ Rf̄'_* Rj'_! (g')^{-1},
```
the base change map of `f̄` (Tag 0A2A) followed by Tag 03S6. -/
def derivedLowerShriekBaseChangeGeneral :
    derivedLowerShriekUnbounded.{u, r} f j Λ ⋙ etaleModuleDerivedInverseImageGeneral.{u, r} Λ g ⟶
      etaleModuleDerivedInverseImageGeneral.{u, r} Λ g' ⋙
        derivedLowerShriekUnbounded.{u, r} f' (j.baseChange sq) Λ :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (etaleModuleDerivedBaseChangeGeneral.{u, r} Λ j.toBase g
      (pullback.fst j.toBase g) (pullback.snd j.toBase g) pullback.condition) ≫
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (etaleModuleDerivedExtensionByZeroInverseImageIso.{u, r} Λ
        (isPullback_baseChangeImmersion sq j)) _ ≪≫
      Functor.associator _ _ _).hom

/-- **[Stacks, Tag 0F7L], granted that cohomology commutes with base change for `f̄`.** For every
object `K` of `D(X_étale, Λ)` which is bounded below and whose underlying complex of abelian
sheaves has torsion cohomology sheaves, the base change map
`g^{-1} Rf_! K ⟶ Rf'_! (g')^{-1} K` is an isomorphism: `Rj_! K` is again bounded below with
torsion cohomology, so the base change map of `f̄` is invertible at it by Tag 0DDE, and the
second factor is an isomorphism. -/
theorem isIso_derivedLowerShriekBaseChange_app_of_cohomologyCommutesWithBaseChange
    (hf : CohomologyCommutesWithBaseChange.{u, r} j.toBase)
    (K : DerivedCategory (EtaleModules.{u, r} Λ X)) (n : ℤ) [K.IsGE n]
    (hK : Stacks.Torsion.torsionCohomologyProperty.{max (u + 1) r} X.smallEtaleTopology
      ((etaleModuleForgetDerived.{u, r} Λ X).obj K)) :
    IsIso ((derivedLowerShriekBaseChangeGeneral.{u, r} Λ sq j).app K) := by
  have hGE : ((etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j.immersion).obj K).IsGE n := by
    have := Functor.isGE_obj_mapDerivedCategory
      (etaleModuleExtensionByZero.{u, r} Λ j.immersion) K n inferInstance
    exact DerivedCategory.TStructure.t.isGE_of_iso
      ((etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ j.immersion).app K).symm n
  have := isIso_etaleModuleDerivedBaseChange_of_cohomologyCommutesWithBaseChange.{u, r} Λ hf
    (IsPullback.of_hasPullback j.toBase g)
    ((etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j.immersion).obj K) n
    (torsionCohomologyProperty_etaleModuleForgetDerived_extensionByZero.{u, r} Λ j.immersion K hK)
  change IsIso ((Functor.associator _ _ _).hom.app K ≫
    (etaleModuleDerivedBaseChangeGeneral.{u, r} Λ j.toBase g (pullback.fst j.toBase g)
      (pullback.snd j.toBase g) pullback.condition).app
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j.immersion).obj K) ≫
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (etaleModuleDerivedExtensionByZeroInverseImageIso.{u, r} Λ
        (isPullback_baseChangeImmersion sq j)) _ ≪≫
      Functor.associator _ _ _).hom.app K)
  infer_instance

/-- **[Stacks, Tag 0F7L] for a chosen compactification, granted the proper base change theorem.**
Suppose that cohomology commutes with base change for every proper morphism of schemes
([Stacks, Tag 095T], `h095T`). Then for a cartesian square of `f` along `g`, a compactification
`j` of `f` and every `K` in `D(X_étale, Λ)` bounded below whose underlying complex of abelian
sheaves has torsion cohomology sheaves, `g^{-1} Rf_! K ⟶ Rf'_! (g')^{-1} K` is an isomorphism.

closing step: `h095T` is Stacks Tag 095T,
`Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper`; substituting it for
`h095T` gives the unconditional statement. -/
theorem isIso_derivedLowerShriekBaseChange_app_of_proper_base_change
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, r} p)
    (K : DerivedCategory (EtaleModules.{u, r} Λ X)) (n : ℤ) [K.IsGE n]
    (hK : Stacks.Torsion.torsionCohomologyProperty.{max (u + 1) r} X.smallEtaleTopology
      ((etaleModuleForgetDerived.{u, r} Λ X).obj K)) :
    IsIso ((derivedLowerShriekBaseChangeGeneral.{u, r} Λ sq j).app K) :=
  isIso_derivedLowerShriekBaseChange_app_of_cohomologyCommutesWithBaseChange.{u, r} Λ sq j
    (h095T j.toBase) K n hK

end Stacks.EtaleCohomology

end
