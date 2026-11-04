module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceThickening
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryPlusCompIsoh
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
import StacksCore.Tactic.StacksAttribute

/-!
# Invariance of the derived lower shriek under thickenings

Let `f' : X' ⟶ Y` be a finite type separated morphism of quasi-compact and quasi-separated
schemes, let `i : X ⟶ X'` be a thickening and `f = f' ∘ i`. Let `Λ` be a ring.
[Stacks, Tag 0GKQ] says that `Rf_! i⁻¹ K' = Rf'_! K'` for `K'` in `D⁺_tors(X'_étale, Λ)`, or in
`D(X'_étale, Λ)` when `Λ` is torsion.

## Main results

* `Stacks.EtaleCohomology.etaleModuleInverseImageCompDirectImageIsoOfThickening`: `i_* i⁻¹ ≅ 𝟭`
  on sheaves of `Λ`-modules, for a thickening `i` (topological invariance, [Stacks, Tag 04DZ]).
* `Stacks.EtaleCohomology.derivedLowerShriekInverseImageIsoOfThickening` and
  `Stacks.EtaleCohomology.derivedLowerShriekUnboundedInverseImageIsoOfThickening`:
  `Rf_! ∘ i⁻¹ ≅ Rf'_!` on bounded below and on unbounded derived categories.
* `Stacks.EtaleCohomology.nonempty_derivedLowerShriek_inverseImage_iso_of_thickening`:
  **[Stacks, Tag 0GKQ]**, both cases.

## Implementation notes

The functor `Rf_! = R f̄_* ∘ j_!` of the repository depends on a compactification `j`, the
independence of the choice ([Stacks, Tag 0F7I]) not being available. The statement is made for an
arbitrary compactification `j'` of `f'`, with `Rf_!` computed through the compactification
`AlgebraicGeometry.CompactificationOf.restrictClosed` that `j'` induces on the closed subscheme
`X` (the scheme-theoretic closure of `X` in the compactification of `X'`). Through it,
`Rf_! = Rf'_! ∘ i_*` (`Stacks.EtaleCohomology.derivedLowerShriekRestrictClosedIso`).

A thickening is a closed immersion which is surjective, the definition
`Stacks.Thickenings.IsThickening` of [Stacks, Tag 04EX]; it enters as the two instance arguments
`[IsClosedImmersion i]` and `[Surjective i]`. The formula for `Rf_!` uses no torsion hypothesis,
so the bounded below case is proved on all of `D⁺(X'_étale, Λ)`, which contains
`D⁺_tors(X'_étale, Λ)`, and the unbounded case for an arbitrary ring `Λ`; likewise only
quasi-compactness of `f'` is used beyond the existence of the compactification.

## References

* [Stacks Project, Tag 0GKQ](https://stacks.math.columbia.edu/tag/0GKQ)
* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace CategoryTheory.Functor

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]

/-- The identity functor induces the identity functor on the bounded below derived category:
`Stacks.Homology.mapDerivedCategoryIdIso` restricted along the fully faithful inclusion. -/
def mapDerivedCategoryPlusIdIso : (𝟭 A).mapDerivedCategoryPlus ≅ 𝟭 (DerivedCategory.Plus A) :=
  (DerivedCategory.TStructure.t.plus.fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft DerivedCategory.Plus.ι Stacks.Homology.mapDerivedCategoryIdIso ≪≫
      Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)

end CategoryTheory.Functor

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable (Λ : Type r) [Ring Λ]

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

section Sheaves

variable {X X' : Scheme.{u}} (i : X ⟶ X') [IsClosedImmersion i] [Surjective i]

/-- **Topological invariance for sheaves of modules along a thickening**: for a thickening
`i : X ⟶ X'` the unit `𝟭 ⟶ i_* i⁻¹` is an isomorphism, inverse image along `i` being an
equivalence ([Stacks, Tag 04DZ]). -/
def etaleModuleInverseImageCompDirectImageIsoOfThickening :
    etaleModuleInverseImage.{u, r} Λ i ⋙ etaleModuleDirectImage.{u, r} Λ i ≅
      𝟭 (EtaleModules.{u, r} Λ X') :=
  haveI := Stacks.Etale.universalHomeomorphism_of_isClosedImmersion_of_surjective i
    (Surjective.surj (f := i))
  haveI := etaleModuleInverseImage_isEquivalence_of_universalHomeomorphism.{u, r} Λ i
  (asIso (etaleModuleInverseImageAdj.{u, r} Λ i).unit).symm

end Sheaves

variable {X X' Y : Scheme.{u}} {f' : X' ⟶ Y} [QuasiCompact f']
  (j' : CompactificationOf (Over.mk f')) (i : X ⟶ X') [IsClosedImmersion i] [Surjective i]

/-- **`Rf_! ∘ i⁻¹ ≅ Rf'_!` for a thickening, on bounded below derived categories.** With `Rf_!`
computed through the compactification `j'` induces on `X`, `Rf_! = Rf'_! ∘ i_*`, and
`i_* ∘ i⁻¹ ≅ 𝟭` since `i⁻¹` and `i_*` are inverse equivalences. -/
def derivedLowerShriekInverseImageIsoOfThickening :
    (etaleModuleInverseImage.{u, r} Λ i).mapDerivedCategoryPlus ⋙
        derivedLowerShriek.{u, r} (i ≫ f') (j'.restrictClosed i) Λ ≅
      derivedLowerShriek.{u, r} f' j' Λ :=
  Functor.isoWhiskerLeft _ (derivedLowerShriekRestrictClosedIso.{u, r} Λ j' i) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft _
          (etaleModuleDirectImage.{u, r} Λ i).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus ≪≫
        Functor.mapDerivedCategoryPlusCompIsoh
          (etaleModuleInverseImageCompDirectImageIsoOfThickening.{u, r} Λ i) ≪≫
        Functor.mapDerivedCategoryPlusIdIso)
      (derivedLowerShriek.{u, r} f' j' Λ) ≪≫
    Functor.leftUnitor _

/-- **`Rf_! ∘ i⁻¹ ≅ Rf'_!` for a thickening, on unbounded derived categories.** -/
def derivedLowerShriekUnboundedInverseImageIsoOfThickening :
    (etaleModuleInverseImage.{u, r} Λ i).mapDerivedCategory ⋙
        derivedLowerShriekUnbounded.{u, r} (i ≫ f') (j'.restrictClosed i) Λ ≅
      derivedLowerShriekUnbounded.{u, r} f' j' Λ :=
  Functor.isoWhiskerLeft _ (derivedLowerShriekUnboundedRestrictClosedIso.{u, r} Λ j' i) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryCompIsoh
          (etaleModuleInverseImageCompDirectImageIsoOfThickening.{u, r} Λ i) ≪≫
        Stacks.Homology.mapDerivedCategoryIdIso)
      (derivedLowerShriekUnbounded.{u, r} f' j' Λ) ≪≫
    Functor.leftUnitor _

/-- Let `f' : X' ⟶ Y` be a quasi-compact morphism of schemes with a compactification `j'` over
`Y` (for instance `f'` finite type and separated with `X'` and `Y` quasi-compact and
quasi-separated), let `i : X ⟶ X'` be a thickening (a surjective closed immersion, [Stacks,
Tag 04EX]) and `f = f' ∘ i`. Let `Λ` be a ring. Then

* for every `K'` in `D⁺(X'_étale, Λ)`, in particular for every `K'` in `D⁺_tors(X'_étale, Λ)`,
  `Rf_! i⁻¹ K' ≅ Rf'_! K'`, and
* for every `K'` in `D(X'_étale, Λ)`, in particular when `Λ` is torsion, `Rf_! i⁻¹ K' ≅ Rf'_! K'`.

Here `Rf'_! = R f̄'_* ∘ j'_!` is computed through `j'` and `Rf_!` through the compactification
`j'` induces on `X` (`AlgebraicGeometry.CompactificationOf.restrictClosed`). -/
@[stacks 0GKQ]
theorem nonempty_derivedLowerShriek_inverseImage_iso_of_thickening :
    (∀ K' : DerivedCategory.Plus (EtaleModules.{u, r} Λ X'),
      Nonempty ((derivedLowerShriek.{u, r} (i ≫ f') (j'.restrictClosed i) Λ).obj
          ((etaleModuleInverseImage.{u, r} Λ i).mapDerivedCategoryPlus.obj K') ≅
        (derivedLowerShriek.{u, r} f' j' Λ).obj K')) ∧
    (∀ K' : DerivedCategory (EtaleModules.{u, r} Λ X'),
      Nonempty ((derivedLowerShriekUnbounded.{u, r} (i ≫ f') (j'.restrictClosed i) Λ).obj
          ((etaleModuleInverseImage.{u, r} Λ i).mapDerivedCategory.obj K') ≅
        (derivedLowerShriekUnbounded.{u, r} f' j' Λ).obj K')) :=
  ⟨fun K' => ⟨(derivedLowerShriekInverseImageIsoOfThickening.{u, r} Λ j' i).app K'⟩,
    fun K' => ⟨(derivedLowerShriekUnboundedInverseImageIsoOfThickening.{u, r} Λ j' i).app K'⟩⟩

end Stacks.EtaleCohomology

end
