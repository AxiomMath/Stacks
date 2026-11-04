module

public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.LocalizationRestrictionKInjective
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentLowerShriekAdjunction
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringSituationConeFreeYoneda
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SliceAbelianLowerShriek

/-!
# The restriction hypothesis of Stacks 0D8G is Stacks 0D88, for a simplicial semi-representable
object

Let `(C, J)` be a site with fibre products and `K` a simplicial semi-representable object of `C`,
with `a : Sh((C/K)_total) ⟶ Sh(C)` the augmentation of Stacks 0D8B. The reduction
`CategoryTheory.SimplicialSemiRepresentable`
`.inverseImageComputesDerivedPushforward_of_quasiIso_lowerShriek_freeYoneda` of
`StacksFrontier/CategoryTheory/Sites/Simplicial/HypercoveringSituationConeFreeYoneda.lean` carries
*two* hypotheses, not one: besides the quasi-isomorphism on the base site it asks `hrestr`, that
the inverse image `a^{-1}I` of a K-injective complex restricts to a K-injective complex on every
component of the total site. That is Stacks 0D88, and this module discharges it.

The restriction of `a^{-1}` to the component of simplicial degree `p` is restriction along the
localization functor `j_p : C/K_p ⥤ C`. That is not read off the compatibility of Stacks 0D70 —
which would give `a_p^{-1}` in the shape
`CategoryTheory.SimplicialSiteSituation.Augmentation.componentInverseImageAb`, a second abelian
inverse image of a morphism of topoi — but from uniqueness of *right* adjoints: `g_{p!}` is left
adjoint to restriction to the component and `a_!` is left adjoint to `a^{-1}`, so their composite
is left adjoint to `a^{-1}` followed by that restriction; and that composite is `j_{p!}` by
`CategoryTheory.SimplicialSemiRepresentable.componentLowerShriekCompAugmentationAbelianIso`, whose
own right adjoint is restriction along `j_p`. Stacks 0D88 at that functor is
`StacksFrontier/CategoryTheory/Sites/SemiRepresentable/LocalizationRestrictionKInjective.lean`.

## Main definitions

* `CategoryTheory.SimplicialSemiRepresentable.situationComponentInverseImageSliceIso`: the
  inverse image along the total augmentation followed by restriction to the component of degree
  `p` is restriction along `j_p`.
* `CategoryTheory.SimplicialSemiRepresentable.situationComponentInverseImageSliceComplexIso`: the
  same on a complex of abelian sheaves.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable.isKInjective_restrictAb_totalInverseImageAb`:
  **Stacks 0D88 in the shape the reduction asks for** — `a^{-1}` of a K-injective complex
  restricts to a K-injective complex on every component.
* `CategoryTheory.SimplicialSemiRepresentable`
  `.inverseImageComputesDerivedPushforward_of_quasiIso_freeYoneda`:
  `InverseImageComputesDerivedPushforward` for the simplicial semi-representable situation from
  the quasi-isomorphism on the base site *alone*.

## Implementation notes

The comparison is built at the functors and then applied degreewise to the complex, by
`CategoryTheory.HomologicalComplex.Hom.isoOfComponents`. The nested form
`(restrictAb p).mapHomologicalComplex.obj ((totalInverseImageAb).mapHomologicalComplex.obj I)`
that the hypothesis is stated in is the composite's `mapHomologicalComplex` on the nose — both
the terms and the differentials — so no comparison of the two spellings of the composite is
needed.

No tag attribute is placed: Stacks 0D88 is carried by
`CategoryTheory.SemiRepresentable.isKInjective_localizationInverseImage_mapHomologicalComplex`,
of which this is an instance.

## References

* [Stacks Project, Tag 0D88](https://stacks.math.columbia.edu/tag/0D88)
* [Stacks Project, Tag 0D8G](https://stacks.math.columbia.edu/tag/0D8G)
* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
* [Stacks Project, Tag 09WM](https://stacks.math.columbia.edu/tag/09WM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SimplicialSiteSituation
open Stacks.Cohomology.CohomologyPresheaf

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] GrothendieckTopology.hasSheafify_addCommGrpCat

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (K : SimplicialObject (FormalCoproduct.{u} C)) [J.toCoverage.HasPullbacks]

/-- **The inverse image along the total augmentation, followed by restriction to the component of
simplicial degree `p`, is restriction along the localization functor `j_p : C/K_p ⥤ C`.**

Both are right adjoints of `j_{p!}`: the first because `g_{p!} ⊣ (-)|_p` and `a_! ⊣ a^{-1}`
compose, and because that composite of left adjoints is `j_{p!}` by
`componentLowerShriekCompAugmentationAbelianIso`; the second by
`sliceAbelianLowerShriekAdjunction`. So the identification is uniqueness of right adjoints, and
no second comparison of morphisms of topoi is built. -/
def situationComponentInverseImageSliceIso (p : SimplexCategory) :
    Augmentation.totalInverseImageAb (situation J K) (Cat.of C) J (situationAugmentation J K) ⋙
        (situation J K).restrictAb p ≅
      (sliceForget K (op p)).sheafPushforwardContinuous AddCommGrpCat.{u}
        ((situation J K).componentTopology p) J :=
  Adjunction.rightAdjointUniq
    (((SimplicialSiteSituation.componentLowerShriekAbAdjunction' (situation J K) p).comp
      (situationAbelianLowerShriekAdjunction J K)).ofNatIsoLeft
        (componentLowerShriekCompAugmentationAbelianIso J K p))
    (sliceAbelianLowerShriekAdjunction J K p)

/-- Additivity of restriction along `j_p`, stated with the source of `j_p` spelled as
`(situation J K).component p` and so carrying the `Cat.str` category instance rather than
`CategoryTheory.SemiRepresentable.instCategoryComponentOver`. As for
`sliceForget_isContinuous_component`, the registered instance
`CategoryTheory.Functor.additive_sheafPushforwardContinuous` is stated at the other spelling of
the same category and is not found here, so it is applied with its arguments given. -/
instance additive_sliceForget_sheafPushforwardContinuous (p : SimplexCategory) :
    ((sliceForget K (op p)).sheafPushforwardContinuous AddCommGrpCat.{u}
      ((situation J K).componentTopology p) J).Additive :=
  Functor.additive_sheafPushforwardContinuous (sliceForget K (op p))
    ((situation J K).componentTopology p) J AddCommGrpCat.{u}

/-- The comparison of `situationComponentInverseImageSliceIso`, applied to every term and every
differential of a complex of abelian sheaves on the base site. -/
def situationComponentInverseImageSliceComplexIso (p : SimplexCategory)
    (I : CochainComplex (Sheaf J Ab.{u}) ℤ) :
    (((situation J K).restrictAb p).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((Augmentation.totalInverseImageAb (situation J K) (Cat.of C) J
          (situationAugmentation J K)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≅
      (((sliceForget K (op p)).sheafPushforwardContinuous AddCommGrpCat.{u}
        ((situation J K).componentTopology p) J).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (situationComponentInverseImageSliceIso J K p).app (I.X n))
    (fun i j _ => by
      simp only [Functor.mapHomologicalComplex_obj_d]
      exact ((situationComponentInverseImageSliceIso J K p).hom.naturality (I.d i j)).symm)

/-- **Stacks 0D88 in the shape the reduction to the base site asks for.** The inverse image
`a^{-1}I` of a K-injective complex of abelian sheaves along the total augmentation restricts to a
K-injective complex on the component of every simplicial degree.

By `situationComponentInverseImageSliceComplexIso` that restriction is restriction along the
localization functor `j_p : C/K_p ⥤ C`, and
`CategoryTheory.SemiRepresentable.isKInjective_sheafPushforwardContinuous_componentOverForget_ofEq`
is Stacks 0D88 there; the `ofEq` form is what carries it across the spelling
`componentTopology_eq` of the topology of the component site. -/
theorem isKInjective_restrictAb_totalInverseImageAb (p : SimplexCategory)
    (I : CochainComplex (Sheaf J Ab.{u}) ℤ) (hI : I.IsKInjective) :
    CochainComplex.IsKInjective
      ((((situation J K).restrictAb p).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((Augmentation.totalInverseImageAb (situation J K) (Cat.of C) J
          (situationAugmentation J K)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) := by
  have := hI
  have : (SemiRepresentable.componentOverForget (K.obj (op p))).IsContinuous
      ((situation J K).componentTopology p) J := sliceForget_isContinuous J K p
  exact @CochainComplex.isKInjective_of_iso _ _ _ _ _
    (situationComponentInverseImageSliceComplexIso J K p I).symm
    (SemiRepresentable.isKInjective_sheafPushforwardContinuous_componentOverForget_ofEq
      J (K.obj (op p)) (componentTopology_eq J K p) I)

/-- **`InverseImageComputesDerivedPushforward` for a simplicial semi-representable object, from
the quasi-isomorphism on the base site alone.** This is
`inverseImageComputesDerivedPushforward_of_quasiIso_lowerShriek_freeYoneda` with its restriction
hypothesis discharged by `isKInjective_restrictAb_totalInverseImageAb`, that is by Stacks 0D88.

What remains is `h`: that the extension by zero `a_!` carries the augmentation of the resolution
of Stacks 0D78 of `a^{-1}ℤ_V^♯` to a quasi-isomorphism, for every object `V` of `C`. -/
theorem inverseImageComputesDerivedPushforward_of_quasiIso_freeYoneda
    (h : ∀ V : C, QuasiIso
      (((augmentationAbelianLowerShriek J K).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (Augmentation.resolutionCochainAug (situation J K) (Cat.of C) J
          (situationAugmentation J K) (freeYonedaSheaf J V)))) :
    Augmentation.InverseImageComputesDerivedPushforward (situation J K) (Cat.of C) J
      (situationAugmentation J K) :=
  inverseImageComputesDerivedPushforward_of_quasiIso_lowerShriek_freeYoneda J K
    (isKInjective_restrictAb_totalInverseImageAb J K) h

end CategoryTheory.SimplicialSemiRepresentable

end
