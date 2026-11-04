module

public import Mathlib.CategoryTheory.Abelian.Transfer
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.CategoryTheory.Pi.Preadditive
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.InverseImage
public import StacksFrontier.Homology.Injectives.Sheaf.InternalHomExact
public import StacksCore.Tactic.StacksAttribute

/-!
# Localization at a semi-representable object preserves K-injective complexes

Let `(C, J)` be a site and `K = ⨿ i, K.obj i` a semi-representable object of `C`. The inverse
image `j⁻¹ : Ab(C) ⥤ Ab(C / K)` along the localization at `K` sends a K-injective complex of
abelian sheaves to a K-injective complex.

For a single object `U` this is the adjoint criterion for K-injectivity (Stacks 08BJ) applied to
the adjunction `j_! ⊣ j⁻¹`, whose left adjoint — extension by zero — is exact; that exactness is
the content of Stacks 01DR and is available as
`StacksDraft.Homology.Injectives.Sheaf`'s `leftAdjoint_preservesFiniteLimits`. For a
semi-representable `K` the localized site is the disjoint union of the component slices, so a
sheaf on it is a family of sheaves on those slices and `j⁻¹` is the family of the one-object
inverse images. A morphism into such a family from an acyclic complex is null-homotopic because
it is so in each component and the homotopies assemble: everything in a product of preadditive
categories is computed index by index.

## Main results

* `CategoryTheory.SemiRepresentable.isKInjective_overPullback_mapHomologicalComplex_obj`: the
  one-object case — restriction to a slice site preserves K-injective complexes of abelian
  sheaves.
* `CategoryTheory.SemiRepresentable.isKInjective_localizationInverseImage_mapHomologicalComplex`:
  **Stacks 0D88**, the semi-representable case.

## Implementation notes

The product `∏ i, Ab(C / K.obj i)` is made abelian by transporting the abelian structure of
`Ab(C / K)` along the canonical equivalence
`CategoryTheory.SemiRepresentable.formalCoproductSliceSheavesEquivalence`, on top of the
index-by-index preadditive structure of `CategoryTheory.Pi.preadditive`. Taking the preadditive
structure from the product rather than from the equivalence is what makes addition of morphisms,
and hence a null-homotopy, index by index.

The coefficient universe is `max u v w`, where `u` and `v` are the object and morphism universes
of the site and `w` is the index universe of the semi-representable object. This is the universe
in which abelian sheaves on `C`, on every slice of `C` and on the localized site all have a
sheafification (`Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp`) and in which
extension by zero is exact, so it is the universe in which the hypotheses below are available.

## References

* [Stacks Project, Tag 0D88](https://stacks.math.columbia.edu/tag/0D88)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
* [Stacks Project, Tag 01DR](https://stacks.math.columbia.edu/tag/01DR)
-/

@[expose] public section

namespace CategoryTheory.SemiRepresentable

open CategoryTheory CategoryTheory.Limits

universe u v w u' v'

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- Inverse image of abelian sheaves along the localization at an object is additive: it is
precomposition with `CategoryTheory.Over.forget`, and addition of morphisms of sheaves is
computed object by object. -/
instance overPullback_additive (A : Type u') [Category.{v'} A] [Preadditive A] (U : C) :
    (J.overPullback A U).Additive where
  map_add := rfl

variable (K : FormalCoproduct.{w} C)

/-- Restriction of abelian sheaves from the localized site `C / K` to the component slices is
additive. -/
instance restrictSheaf_additive (A : Type u') [Category.{v'} A] [Preadditive A] :
    (restrictSheaf J K A).Additive where
  map_add := rfl

/-- The family of the inverse images along the localizations at the components of a
semi-representable object is additive. -/
instance componentInverseImage_additive (A : Type u') [Category.{v'} A] [Preadditive A] :
    (componentInverseImage J K A).Additive where
  map_add := rfl

/-- Evaluation at a component preserves finite limits on the product of the categories of
abelian sheaves on the component slices. -/
theorem preservesFiniteLimits_componentEval (i : K.I) :
    PreservesFiniteLimits
      (Pi.eval (fun j : K.I => Sheaf (J.over (K.obj j)) AddCommGrpCat.{max u v w}) i) :=
  Pi.preservesFiniteLimits_eval.{w, max u v w, max u v w + 1} i

section

variable [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max u v w}]

/-- Evaluation at a component preserves finite colimits on the product of the categories of
abelian sheaves on the component slices. -/
theorem preservesFiniteColimits_componentEval (i : K.I) :
    PreservesFiniteColimits
      (Pi.eval (fun j : K.I => Sheaf (J.over (K.obj j)) AddCommGrpCat.{max u v w}) i) :=
  Pi.preservesFiniteColimits_eval.{w, max u v w, max u v w + 1} i

variable [HasSheafify J AddCommGrpCat.{max u v w}]

/-- Inverse image along the localization at an object of the site sends a K-injective complex of
abelian sheaves to a K-injective complex. The left adjoint of that inverse image is extension by
zero, which is exact, so this is the adjoint criterion for K-injectivity (Stacks 08BJ) applied
to the exactness of Stacks 01DR. -/
theorem isKInjective_overPullback_mapHomologicalComplex_obj (U : C)
    (I : CochainComplex (Sheaf J AddCommGrpCat.{max u v w}) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((J.overPullback AddCommGrpCat.{max u v w} U).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) := by
  have adj : (J.overPullback AddCommGrpCat.{max u v w} U).leftAdjoint ⊣
      J.overPullback AddCommGrpCat.{max u v w} U := Adjunction.ofIsRightAdjoint _
  have : PreservesFiniteLimits ((J.overPullback AddCommGrpCat.{max u v w} U).leftAdjoint) :=
    _root_.leftAdjoint_preservesFiniteLimits.{v, u, max u v w} J U
  have : PreservesColimitsOfSize.{0, 0}
      ((J.overPullback AddCommGrpCat.{max u v w} U).leftAdjoint) :=
    adj.leftAdjoint_preservesColimits
  have : PreservesFiniteColimits ((J.overPullback AddCommGrpCat.{max u v w} U).leftAdjoint) :=
    PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _
  have : ((J.overPullback AddCommGrpCat.{max u v w} U).leftAdjoint).Additive :=
    adj.left_adjoint_additive
  exact CochainComplex.isKInjective_mapHomologicalComplex_of_exact _ _ adj I

variable [HasSheafify (componentwiseTopology J K) AddCommGrpCat.{max u v w}]

/-- The product of the categories of abelian sheaves on the component slices of a
semi-representable object is abelian, for the index-by-index preadditive structure: it is
equivalent to the category of abelian sheaves on the localized site. -/
noncomputable instance componentSheaves_abelian :
    Abelian ((i : K.I) → Sheaf (J.over (K.obj i)) AddCommGrpCat.{max u v w}) := by
  let e := (formalCoproductSliceSheavesEquivalence J K AddCommGrpCat.{max u v w}).1
  have : HasFiniteProducts ((i : K.I) → Sheaf (J.over (K.obj i)) AddCommGrpCat.{max u v w}) :=
    ⟨fun _ => Adjunction.hasLimitsOfShape_of_equivalence e.inverse⟩
  have : (e.inverse.inv).PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_full _
  exact abelianOfEquivalence e.inverse

/-- The family of the inverse images along the localizations at the components of a
semi-representable object sends a K-injective complex of abelian sheaves to a K-injective
complex: a morphism from an acyclic complex is null-homotopic in every component, and the
homotopies assemble because addition of morphisms is index by index. -/
theorem isKInjective_componentInverseImage_mapHomologicalComplex_obj
    (I : CochainComplex (Sheaf J AddCommGrpCat.{max u v w}) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((componentInverseImage J K AddCommGrpCat.{max u v w}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) := by
  constructor
  intro M f hM
  have hhom : ∀ i : K.I, Homotopy
      (((Pi.eval (fun j : K.I => Sheaf (J.over (K.obj j)) AddCommGrpCat.{max u v w})
        i).mapHomologicalComplex (ComplexShape.up ℤ)).map f) 0 := by
    intro i
    have hlim := preservesFiniteLimits_componentEval J K i
    have hcolim := preservesFiniteColimits_componentEval J K i
    have hMi : (((Pi.eval (fun j : K.I => Sheaf (J.over (K.obj j)) AddCommGrpCat.{max u v w})
        i).mapHomologicalComplex (ComplexShape.up ℤ)).obj M).Acyclic := hM.map _
    have hI : CochainComplex.IsKInjective
        (((Pi.eval (fun j : K.I => Sheaf (J.over (K.obj j)) AddCommGrpCat.{max u v w})
          i).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((componentInverseImage J K AddCommGrpCat.{max u v w}).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj I)) :=
      isKInjective_overPullback_mapHomologicalComplex_obj J (K.obj i) I
    exact CochainComplex.IsKInjective.homotopyZero _ hMi
  exact ⟨{ hom := fun n m i => (hhom i).hom n m
           zero := fun n m hnm => funext fun i => (hhom i).zero n m hnm
           comm := fun n => funext fun i => (hhom i).comm n }⟩

/-- **Stacks 0D88.** Inverse image along the localization at a semi-representable object sends a
K-injective complex of abelian sheaves to a K-injective complex. -/
@[stacks 0D88 "K-injective complexes are preserved"]
theorem isKInjective_localizationInverseImage_mapHomologicalComplex
    (I : CochainComplex (Sheaf J AddCommGrpCat.{max u v w}) ℤ) [I.IsKInjective] :
    ((localizationInverseImageMapHomologicalComplex J K).obj I).IsKInjective := by
  let e := (formalCoproductSliceSheavesEquivalence J K AddCommGrpCat.{max u v w}).1
  have hzero : e.functor.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_full _
  have hfun : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  have hP := isKInjective_componentInverseImage_mapHomologicalComplex_obj J K I
  have hinv : CochainComplex.IsKInjective
      (((componentInverseImage J K AddCommGrpCat.{max u v w}).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        e.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    CochainComplex.isKInjective_mapHomologicalComplex_of_exact e.inverse e.functor
      e.toAdjunction _
  exact CochainComplex.isKInjective_of_iso
    ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (componentInverseImage J K AddCommGrpCat.{max u v w} ⋙ e.inverse))
      (ComplexShape.up ℤ)).app I)

end

end CategoryTheory.SemiRepresentable

end
