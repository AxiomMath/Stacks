module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleKunnethMap
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposTensorIsoCompositionDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorIsoOfIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormula
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.RelativeCupProductBaseChange

/-!
# The comparison of Tag 07A4 on `D(-_étale, Λ)` along composites and around squares

For morphisms of schemes `p : W ⟶ X` and `f : X ⟶ Y`, the inverse image along `p ≫ f` on
`D(-_étale, Λ)` is identified with the composite of the inverse images by
`Stacks.EtaleCohomology.EtaleCoefficients.pullbackCompIso`, and each inverse image carries the
comparison `f⁻¹(M ⊗^L N) ≅ f⁻¹M ⊗^L f⁻¹N` of [Stacks, Tag 07A4]
(`Stacks.EtaleCohomology.EtaleCoefficients.pullbackTensorIso`). This file proves that the
identification is monoidal: the comparison along `p ≫ f` is the comparison along `f`, then the
one along `p`, read through `pullbackCompIso` (`pullbackTensorIso_comp`). Around a commutative
square of schemes the four comparisons are therefore compatible
(`tensorComparisonCompatible_pullbackTensorIso`), which is the one input of the abstract
projection formula lemmas `Stacks.AffineProjectionFormula.adjunctionTensorMap_baseChange_square`
(Stacks 0E48) and `Stacks.AffineProjectionFormula.adjunctionTensorMap_pushforward_square`.

## The proof

`pullbackCompIso` is Stacks 0D6D for the composite morphism of ringed topoi followed by the
isomorphism of derived pullbacks along isomorphic morphisms of ringed topoi. The comparison of
Tag 07A4 is compatible with the first by
`Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_comp` and with the second by
`Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_isoOfIso`; both are identities of
natural transformations, and so is `pullbackTensorIso_comp`. The square is
`Stacks.Cohomology.DerivedRelativeCupProduct.comparisonCompatibleWithSquare_of_composition_laws`
at the family `m ↦ m⁻¹` of inverse images along the morphisms `P ⟶ R`.

## Main results

All in the namespace `Stacks.EtaleCohomology.EtaleCoefficients`.

* `pullbackTensorIso_comp` — the composition law of Tag 07A4, as an identity of natural
  transformations; its value at a pair of objects is the existing
  `pullbackCompIso_hom_app_comp_pullbackTensorIso_hom_app` (KunnethOverFieldMapComparison).
* `tensorComparisonCompatible_pullbackTensorIso` — the four comparisons around a commutative
  square of schemes are compatible.

## Implementation notes

The square compatibility is stated with the identification of the two composites through the
inverse image along `c ≫ d`, the left one by `pullbackCompIso` followed by `eqToIso` along `w`.
It is obtained from the two composition laws at the level of natural transformations: written out
at a pair of objects and matched against the abstract predicate, the same statement exhausts the
kernel's budget, because the product category of the abstract statement and the one of
`Functor.uncurry` are different (definitionally equal) instances.

The derived categories are the standard model: `derivedPullback` is stated for it.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 0E48](https://stacks.math.columbia.edu/tag/0E48)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open scoped CategoryTheory.Prod

universe u

namespace Stacks.EtaleCohomology.EtaleCoefficients

-- `derivedPullback` (`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/
-- AdjunctionForRingedTopoi.lean:394`) is stated for the standard model of the derived category.
attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type (u + 1)) [CommRing Λ]

section Composite

variable {W X Y : Scheme.{u}}

/-- **The comparison of Stacks 07A4 is compatible with composition.** The identification
`f⁻¹ ⋙ p⁻¹ ≅ (p ≫ f)⁻¹` followed by the comparison along `p ≫ f` is `p⁻¹` of the comparison
along `f`, then the comparison along `p`, then the identification in each tensor factor. -/
theorem pullbackTensorIso_comp (p : W ⟶ X) (f : X ⟶ Y) :
    Functor.whiskerLeft (Functor.uncurry.obj (tensor Λ Y)) (pullbackCompIso Λ p f).hom ≫
        (pullbackTensorIso Λ (p ≫ f)).hom =
      Functor.whiskerRight (pullbackTensorIso Λ f).hom (pullback Λ p) ≫
        Functor.whiskerLeft ((pullback Λ f).prod (pullback Λ f)) (pullbackTensorIso Λ p).hom ≫
          Functor.whiskerRight
            (NatTrans.prod (pullbackCompIso Λ p f).hom (pullbackCompIso Λ p f).hom)
            (Functor.uncurry.obj (tensor Λ W)) := by
  let := Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy
    (X := ringedTopos Λ W) (Y := ringedTopos Λ Y) ((ringedToposHom Λ f).comp (ringedToposHom Λ p))
    (RingedToposSiteHom.isMorphismOfSites_comp_u _ _ (isMorphismOfSites_ringedToposHom Λ p)
      (isMorphismOfSites_ringedToposHom Λ f))
  have h1 := Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_comp
    (ringedToposHom Λ p) (ringedToposHom Λ f) (isMorphismOfSites_ringedToposHom Λ p)
    (isMorphismOfSites_ringedToposHom Λ f)
  have h2 := Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_isoOfIso
    (fSharpCompatible_comp Λ p f)
    (RingedToposSiteHom.isMorphismOfSites_comp_u _ _ (isMorphismOfSites_ringedToposHom Λ p)
      (isMorphismOfSites_ringedToposHom Λ f)) (isMorphismOfSites_ringedToposHom Λ (p ≫ f))
  have h2' : Functor.whiskerLeft (Functor.uncurry.obj (tensor Λ Y))
        (derivedPullbackIsoOfIso (fSharpCompatible_comp Λ p f)).hom ≫
      (pullbackTensorIso Λ (p ≫ f)).hom = _ := h2
  have h1' : Functor.whiskerLeft (Functor.uncurry.obj (tensor Λ Y))
        (Stacks.Cohomology.DerivedPullbackCompositionOnTopoi.derivedPullbackCompIso
          (ringedToposHom Λ p) (ringedToposHom Λ f) (isMorphismOfSites_ringedToposHom Λ p)
          (isMorphismOfSites_ringedToposHom Λ f)).hom ≫
      (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso
        ((ringedToposHom Λ f).comp (ringedToposHom Λ p))
        (RingedToposSiteHom.isMorphismOfSites_comp_u _ _ (isMorphismOfSites_ringedToposHom Λ p)
          (isMorphismOfSites_ringedToposHom Λ f))).hom = _ := h1
  simp only [pullbackCompIso, Iso.trans_hom, Functor.whiskerLeft_comp, Category.assoc]
  rw [h2', reassoc_of% h1', ← Functor.whiskerRight_comp]
  rfl

variable {P Q R S : Scheme.{u}}

/-- **The comparisons of Stacks 07A4 are compatible around a commutative square of schemes.**
For `a ≫ b = c ≫ d`, identify `b⁻¹ ⋙ a⁻¹` with `(c ≫ d)⁻¹` through `(a ≫ b)⁻¹` and `w`, and
`d⁻¹ ⋙ c⁻¹` with `(c ≫ d)⁻¹`. Across these identifications the comparison along `b` followed by
the one along `a` is the comparison along `d` followed by the one along `c`. Both composites are
monoidal for the comparison along the common composite (`pullbackTensorIso_comp`). -/
theorem tensorComparisonCompatible_pullbackTensorIso (a : P ⟶ Q) (b : Q ⟶ R) (c : P ⟶ S)
    (d : S ⟶ R) (w : a ≫ b = c ≫ d) (M N : DerivedModules Λ R) :
    Stacks.AffineProjectionFormula.TensorComparisonCompatible
      (pullbackCompIso Λ a b ≪≫ eqToIso (congrArg (fun m : P ⟶ R => pullback Λ m) w))
      (pullbackCompIso Λ c d)
      (Functor.uncurry.obj (tensor Λ R)) (Functor.uncurry.obj (tensor Λ Q))
      (Functor.uncurry.obj (tensor Λ S)) (Functor.uncurry.obj (tensor Λ P))
      (pullbackTensorIso Λ d).hom (pullbackTensorIso Λ a).hom (pullbackTensorIso Λ b).hom
      (pullbackTensorIso Λ c).hom M N :=
  Stacks.Cohomology.DerivedProjectionFormula.tensorComparisonCompatible_of_comparisonSquare
    (Functor.uncurry.obj (tensor Λ R)) (Functor.uncurry.obj (tensor Λ Q))
    (Functor.uncurry.obj (tensor Λ S)) (Functor.uncurry.obj (tensor Λ P))
    (pullbackTensorIso Λ b).hom (pullbackTensorIso Λ a).hom
    (pullbackTensorIso Λ d).hom (pullbackTensorIso Λ c).hom
    (Stacks.Cohomology.DerivedRelativeCupProduct.comparisonCompatibleWithSquare_of_composition_laws
      (Functor.uncurry.obj (tensor Λ R)) (Functor.uncurry.obj (tensor Λ Q))
      (Functor.uncurry.obj (tensor Λ S)) (Functor.uncurry.obj (tensor Λ P))
      (pullbackTensorIso Λ b).hom (pullbackTensorIso Λ a).hom
      (pullbackTensorIso Λ d).hom (pullbackTensorIso Λ c).hom
      (fun m : P ⟶ R => pullback Λ m) (fun m => (pullbackTensorIso Λ m).hom) w
      (pullbackCompIso Λ a b) (pullbackCompIso Λ c d) _ rfl
      (pullbackTensorIso_comp Λ a b) (pullbackTensorIso_comp Λ c d)) M N

end Composite

end Stacks.EtaleCohomology.EtaleCoefficients

end
