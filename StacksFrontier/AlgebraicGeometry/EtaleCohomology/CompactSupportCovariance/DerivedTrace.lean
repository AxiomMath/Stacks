module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactSupportCovariance.ModelTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ThickeningInvariance
public import StacksFrontier.AlgebraicGeometry.Perfect.Approximation.OpenSubscheme
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactPlusHomologyComposition
import StacksCore.Tactic.StacksAttribute

/-!
# The derived trace `Tr_{f, w, K} : Rf_! f^{-1}K ⟶ K`

Let `f : X ⟶ Y` be a morphism of schemes with a compactification `j : X ⟶ X̄` finite over `Y`,
let `w` be a weighting of `f` and let `Λ` be a ring. The functors `f^{-1}`, `j_!` and `f̄_*` are
exact (inverse image, extension by zero, and direct image along a finite morphism), so
`Rf_! = Rf̄_* ∘ j_!` is `f̄_* ∘ j_!` applied degreewise and the trace
`Tr_{f, w} : f^{-1} ⋙ j_! ⋙ f̄_* ⟶ 𝟭` of `Stacks.EtaleCohomology.etaleModuleCompactificationTrace`
induces a natural transformation

`Tr_{f, w, K} : Rf_! f^{-1}K ⟶ K`

on `D⁺(Y_étale, Λ)` and on `D(Y_étale, Λ)`. This is part (3) of [Stacks, Tag 0GKH], in the form
in which [Stacks, Tag 0GKS] uses it, where `Rf_! = f_!` for the quasi-finite separated `f` is
[Stacks, Tag 0GKM].

## Main definitions

* `CategoryTheory.NatTrans.mapDerivedCategoryPlusCompToId`: the derived form, on bounded below
  derived categories, of a transformation `G ⋙ F ⟶ 𝟭` of exact functors.
* `Stacks.EtaleCohomology.derivedLowerShriekWeightedTrace`: `Tr_{f, w, K}` on `D⁺(Y_étale, Λ)`.
* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedWeightedTrace`: `Tr_{f, w, K}` on
  `D(Y_étale, Λ)`.

## References

* [Stacks Project, Tag 0GKH](https://stacks.math.columbia.edu/tag/0GKH)
* [Stacks Project, Tag 0GKM](https://stacks.math.columbia.edu/tag/0GKM)
* [Stacks Project, Tag 0GKS](https://stacks.math.columbia.edu/tag/0GKS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]
  (G : C ⥤ D) (F : D ⥤ C)
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- **The derived form of a counit-shaped transformation `G ⋙ F ⟶ 𝟭` on bounded below derived
categories**: `CategoryTheory.NatTrans.mapDerivedCategoryCompToId` restricted along the fully
faithful inclusion of `D⁺` into `D`. -/
def NatTrans.mapDerivedCategoryPlusCompToId (η : G ⋙ F ⟶ 𝟭 C) :
    G.mapDerivedCategoryPlus ⋙ F.mapDerivedCategoryPlus ⟶ 𝟭 (DerivedCategory.Plus C) :=
  (DerivedCategory.TStructure.t.plus.fullyFaithfulι.whiskeringRight _).preimage
    (Functor.whiskerLeft DerivedCategory.Plus.ι (NatTrans.mapDerivedCategoryCompToId G F η) ≫
      (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv)

end CategoryTheory

open AlgebraicGeometry

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type u) [Ring Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
  (jf : CompactificationOf (Over.mk f)) [IsFinite jf.toBase] {w : X → ℤ} (hw : IsWeighting f w)

/-- For a compactification finite over the base, `Rf_! = Rf̄_* ∘ j_!` on `D⁺` is `f̄_* ∘ j_!`
applied degreewise, both functors being exact. -/
def derivedLowerShriekIsoMapDerivedCategoryPlusOfIsFinite :
    derivedLowerShriek.{u, u} f jf Λ ≅
      (etaleModuleExtensionByZero.{u, u} Λ jf.immersion ⋙
        etaleModuleDirectImage.{u, u} Λ jf.toBase).mapDerivedCategoryPlus :=
  Functor.isoWhiskerRight
      (etaleModuleExtensionByZero.{u, u} Λ
        jf.immersion).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus _ ≪≫
    Functor.isoWhiskerLeft _
      (etaleModuleDirectImage.{u, u} Λ
        jf.toBase).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus ≪≫
    Stacks.DerivedFunctor.mapDerivedCategoryPlusCompIso _ _

include hw in
/-- **The trace map `Tr_{f, w, K} : Rf_! f^{-1}K ⟶ K` on `D⁺(Y_étale, Λ)`** ([Stacks, Tag 0GKS],
from [Stacks, Tag 0GKH] (3)), for a weighting `w` of `f` and `Rf_!` computed through a
compactification of `f` finite over `Y`: the derived form of the trace
`Stacks.EtaleCohomology.etaleModuleCompactificationTrace`, through
`Rf_! = f̄_* ∘ j_!` ([Stacks, Tag 0GKM]). It is natural in `K`. -/
@[stacks 0GKS "the trace map Tr_{f,w,K} : f_! f^{-1} K ⟶ K for K in D⁺(Y_étale, Λ), natural in \
K, for a weighting w of f and Rf_! = f_! computed through a compactification of f finite over Y \
(Zariski's main theorem, 05K0, provides one for f quasi-finite separated over a qcqs Y)"]
def derivedLowerShriekWeightedTrace :
    etaleModuleDerivedInverseImagePlus.{u, u} Λ f ⋙ derivedLowerShriek.{u, u} f jf Λ ⟶
      𝟭 (DerivedCategory.Plus (EtaleModules.{u, u} Λ Y)) :=
  Functor.whiskerLeft _ (derivedLowerShriekIsoMapDerivedCategoryPlusOfIsFinite Λ f jf).hom ≫
    NatTrans.mapDerivedCategoryPlusCompToId _ _
      (etaleModuleCompactificationTrace Λ f jf hw)

/-- For a compactification finite over the base, `Rf_! = Rf̄_* ∘ j_!` on unbounded derived
categories is `f̄_* ∘ j_!` applied degreewise, both functors being exact. -/
def derivedLowerShriekUnboundedIsoMapDerivedCategoryOfIsFinite :
    derivedLowerShriekUnbounded.{u, u} f jf Λ ≅
      (etaleModuleExtensionByZero.{u, u} Λ jf.immersion ⋙
        etaleModuleDirectImage.{u, u} Λ jf.toBase).mapDerivedCategory :=
  Functor.isoWhiskerRight
      (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, u} Λ jf.immersion) _ ≪≫
    Functor.isoWhiskerLeft _
      (Stacks.Injectives.KInjectiveResolution.isoMapDerivedCategoryOfIsRightDerivedFunctor _ _
        (etaleModuleDerivedDirectImageUnboundedUnit.{u, u} Λ jf.toBase)) ≪≫
    (Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso _ _).symm

include hw in
/-- **The trace map `Tr_{f, w, K} : Rf_! f^{-1}K ⟶ K` on `D(Y_étale, Λ)`** ([Stacks, Tag 0GKS],
from [Stacks, Tag 0GKH] (3)), for a weighting `w` of `f` and `Rf_!` computed through a
compactification of `f` finite over `Y`. It is natural in `K`. -/
@[stacks 0GKS "the trace map Tr_{f,w,K} : f_! f^{-1} K ⟶ K for K in D(Y_étale, Λ), natural in K, \
for a weighting w of f and Rf_! = f_! computed through a compactification of f finite over Y"]
def derivedLowerShriekUnboundedWeightedTrace :
    (etaleModuleInverseImage.{u, u} Λ f).mapDerivedCategory ⋙
        derivedLowerShriekUnbounded.{u, u} f jf Λ ⟶
      𝟭 (DerivedCategory (EtaleModules.{u, u} Λ Y)) :=
  Functor.whiskerLeft _
      (derivedLowerShriekUnboundedIsoMapDerivedCategoryOfIsFinite Λ f jf).hom ≫
    NatTrans.mapDerivedCategoryCompToId _ _ (etaleModuleCompactificationTrace Λ f jf hw)

end Stacks.EtaleCohomology

end
