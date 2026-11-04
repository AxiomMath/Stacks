module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatSingleTensorNaturality
public import StacksFrontier.CategoryTheory.Sites.Simplicial.DerivedCompIsoNaturality
public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerTensorBarStructure
public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerTensorUnitDerived

/-!
# The identification `g_{n!}ℤ ⊗^L_ℤ - ≅ (g_{n!}ℤ ⊗_ℤ -)^L` is natural in the degree

Let `S` be a simplicial-site situation. For each simplicial degree `n` the identification
`CategoryTheory.SimplicialSiteSituation.integerTensorAbDerivedIso` reads the derived functor of
the endofunctor `g_{n!}ℤ ⊗_ℤ -` of abelian sheaves on the total site as the derived tensor
product with `g_{n!}ℤ` placed in degree zero. This file proves that the identification is natural
in `n`: the structure map of the simplicial abelian sheaf of simplices acts on either side, and
the identification carries one action to the other.

The proof chains the three naturality squares of the three factors of
`integerTensorAbDerivedIso`. The outer two are the naturality of the compositor of derived
functors in each of its two arguments,
`CategoryTheory.derivedCompIso_refl_hom_whiskerLeft` and
`CategoryTheory.derivedCompIso_refl_hom_whiskerRight`, the conjugating functors being the two
halves of the equivalence of abelian sheaves with modules over the constant sheaf of rings `ℤ`.
The inner one is the naturality of
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.flatSingleTensorIso` in the flat module,
together with the naturality of `CategoryTheory.Functor.mapDerivedCategorySingleFunctor`, which
is what reads `g_{n!}ℤ` in degree zero through the equivalence.

This is the transport that carries a statement about the sheaf-level comparison of Stacks 0D9E
past the identification, as the simplicial degree varies; it is what the Postnikov system of
Stacks 0D9I needs, the system living on the derived tensor product while the computations of
Stacks 0D9K are made for abelian sheaves.

## Main results

* `CategoryTheory.SimplicialSiteSituation.integerTensorFlatIso_naturality`: naturality of the
  innermost factor.
* `CategoryTheory.SimplicialSiteSituation.integerTensorAbDerivedIso_naturality`: **the
  identification `g_{n!}ℤ ⊗^L_ℤ - ≅ (g_{n!}ℤ ⊗_ℤ -)^L` is natural in the simplicial degree.**
* `CategoryTheory.SimplicialSiteSituation.integerTensorFlatIso_naturality_augmentation` and
  `CategoryTheory.SimplicialSiteSituation.integerTensorAbDerivedIso_naturality_augmentation`: the
  same two squares for the augmentation `g_{0!}ℤ ⟶ ℤ` of the resolution, whose target is the unit
  object and whose target identification is therefore the unit one
  `CategoryTheory.SimplicialSiteSituation.unitIntegerTensorAbDerivedIso`.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 09WI](https://stacks.math.columbia.edu/tag/09WI)
* [Stacks Project, Tag 0D9E](https://stacks.math.columbia.edu/tag/0D9E)
* [Stacks Project, Tag 0D9I](https://stacks.math.columbia.edu/tag/0D9I)
* [Stacks Project, Tag 0D9K](https://stacks.math.columbia.edu/tag/0D9K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

open Stacks.DerivedTensor.AbelianSheaves Stacks.SheafOfModules.Tensor
open Stacks.DerivedTensor.RingedSite.DerivedTensorProduct

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] hasSheafifyTotal
  CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat

variable (S : SimplicialSiteSituation.{u})

/-- Whiskering on the left is compatible with composition, as a bare identity of natural
transformations. -/
private theorem whiskerLeft_comp_eq {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) {G₁ G₂ G₃ : D ⥤ E} (u : G₁ ⟶ G₂) (v : G₂ ⟶ G₃) :
    Functor.whiskerLeft F u ≫ Functor.whiskerLeft F v = Functor.whiskerLeft F (u ≫ v) :=
  rfl

/-- Three naturality squares chained into one, extracted so that it is applied as a term rather
than rewritten into the goal. The target of the last square is the derived tensor product by
`g_{n!}ℤ`, which is the conjugated functor only up to unfolding a definition; a rewrite builds
its motive at a transparency at which the goal is then not type-correct, whereas applying a
lemma is elaborated at default transparency. The same device is used in
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/FlatSingleTensorNaturality.lean`. -/
private theorem chain_three {D : Type*} [Category D] {W Z₀ Z₁ Z₂ Z₃ V₁ V₂ V₃ : D}
    (f : W ⟶ Z₀) (a₁ : Z₀ ⟶ Z₁) (a₂ : Z₁ ⟶ Z₂) (a₃ : Z₂ ⟶ Z₃)
    (b₁ : W ⟶ V₁) (b₂ : V₁ ⟶ V₂) (b₃ : V₂ ⟶ V₃)
    (u₁ : V₁ ⟶ Z₁) (u₂ : V₂ ⟶ Z₂) (v : V₃ ⟶ Z₃)
    (h₁ : f ≫ a₁ = b₁ ≫ u₁) (h₂ : u₁ ≫ a₂ = b₂ ≫ u₂) (h₃ : u₂ ≫ a₃ = b₃ ≫ v) :
    f ≫ a₁ ≫ a₂ ≫ a₃ = (b₁ ≫ b₂ ≫ b₃) ≫ v := by
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃, Category.assoc, Category.assoc]

/-- **The innermost factor of `integerTensorAbDerivedIso` is natural in the simplicial degree.**
The identification of the derived functor of `g_{n!}ℤ ⊗_ℤ -` in sheaves of modules with the
derived tensor product by `g_{n!}ℤ` in degree zero carries the derived functor of tensoring with
the structure map to the derived tensor product with that map in degree zero.

It is the naturality of `flatSingleTensorIso` in the flat module, followed by the naturality of
the comparison `mapDerivedCategorySingleFunctor`, which is what reads `g_{n!}ℤ` in degree zero
through the equivalence with modules. -/
theorem integerTensorFlatIso_naturality {p q : SimplexCategory} (θ : p ⟶ q) :
    derivedNatTrans
          ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
            (componentIntegerModule S q))
          ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
            (componentIntegerModule S p))
          ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).map
            ((moduleEquivalence S.totalTopology).inverse.map (integerFace S θ))) ≫
        (integerTensorFlatIso S p).hom =
      (integerTensorFlatIso S q).hom ≫
        (intDerivedTensorProduct S.totalTopology).tensor.map
          ((moduleEquivalence S.totalTopology).inverse.mapDerivedCategory.map
            ((DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).map
              (integerFace S θ))) := by
  have hnat : (intDerivedTensorProduct S.totalTopology).tensor.map
          ((DerivedCategory.singleFunctor
            (Stacks.DerivedTensor.RingedSite.Modules (intRingSheaf S.totalTopology)) 0).map
              ((moduleEquivalence S.totalTopology).inverse.map (integerFace S θ))) ≫
        (flatSingleTensorIso (intRingSheaf S.totalTopology)
          (intDerivedTensorProduct S.totalTopology) (componentIntegerModule S p)
          (isFlat_moduleEquivalenceInverseComponentIntegerSheaf S p)).hom =
      (flatSingleTensorIso (intRingSheaf S.totalTopology)
          (intDerivedTensorProduct S.totalTopology) (componentIntegerModule S q)
          (isFlat_moduleEquivalenceInverseComponentIntegerSheaf S q)).hom ≫
        derivedNatTrans
          ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
            (componentIntegerModule S q))
          ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
            (componentIntegerModule S p))
          ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).map
            ((moduleEquivalence S.totalTopology).inverse.map (integerFace S θ))) :=
    flatSingleTensorIso_naturality (intRingSheaf S.totalTopology)
      (intDerivedTensorProduct S.totalTopology)
      (isFlat_moduleEquivalenceInverseComponentIntegerSheaf S q)
      (isFlat_moduleEquivalenceInverseComponentIntegerSheaf S p)
      ((moduleEquivalence S.totalTopology).inverse.map (integerFace S θ))
  have hsingle : (DerivedCategory.singleFunctor
          (Stacks.DerivedTensor.RingedSite.Modules (intRingSheaf S.totalTopology)) 0).map
        ((moduleEquivalence S.totalTopology).inverse.map (integerFace S θ)) ≫
      (((moduleEquivalence S.totalTopology).inverse.mapDerivedCategorySingleFunctor 0).app
        (componentIntegerSheaf S p)).inv =
    (((moduleEquivalence S.totalTopology).inverse.mapDerivedCategorySingleFunctor 0).app
          (componentIntegerSheaf S q)).inv ≫
      (moduleEquivalence S.totalTopology).inverse.mapDerivedCategory.map
        ((DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).map
          (integerFace S θ)) :=
    ((moduleEquivalence S.totalTopology).inverse.mapDerivedCategorySingleFunctor
      0).inv.naturality (integerFace S θ)
  have hinv : derivedNatTrans
          ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
            (componentIntegerModule S q))
          ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
            (componentIntegerModule S p))
          ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).map
            ((moduleEquivalence S.totalTopology).inverse.map (integerFace S θ))) ≫
        (flatSingleTensorIso (intRingSheaf S.totalTopology)
          (intDerivedTensorProduct S.totalTopology) (componentIntegerModule S p)
          (isFlat_moduleEquivalenceInverseComponentIntegerSheaf S p)).inv =
      (flatSingleTensorIso (intRingSheaf S.totalTopology)
          (intDerivedTensorProduct S.totalTopology) (componentIntegerModule S q)
          (isFlat_moduleEquivalenceInverseComponentIntegerSheaf S q)).inv ≫
        (intDerivedTensorProduct S.totalTopology).tensor.map
          ((DerivedCategory.singleFunctor
            (Stacks.DerivedTensor.RingedSite.Modules (intRingSheaf S.totalTopology)) 0).map
              ((moduleEquivalence S.totalTopology).inverse.map (integerFace S θ))) := by
    calc derivedNatTrans _ _ _ ≫ (flatSingleTensorIso (intRingSheaf S.totalTopology)
            (intDerivedTensorProduct S.totalTopology) (componentIntegerModule S p)
            (isFlat_moduleEquivalenceInverseComponentIntegerSheaf S p)).inv
        = ((flatSingleTensorIso (intRingSheaf S.totalTopology)
              (intDerivedTensorProduct S.totalTopology) (componentIntegerModule S q)
              (isFlat_moduleEquivalenceInverseComponentIntegerSheaf S q)).inv ≫
            (flatSingleTensorIso (intRingSheaf S.totalTopology)
                (intDerivedTensorProduct S.totalTopology) (componentIntegerModule S q)
                (isFlat_moduleEquivalenceInverseComponentIntegerSheaf S q)).hom ≫
              derivedNatTrans _ _ _) ≫
          (flatSingleTensorIso (intRingSheaf S.totalTopology)
            (intDerivedTensorProduct S.totalTopology) (componentIntegerModule S p)
            (isFlat_moduleEquivalenceInverseComponentIntegerSheaf S p)).inv := by
          rw [Iso.inv_hom_id_assoc]
      _ = _ := by
          rw [← hnat, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hfac : ∀ r : SimplexCategory, (integerTensorFlatIso S r).hom =
      (flatSingleTensorIso (intRingSheaf S.totalTopology)
          (intDerivedTensorProduct S.totalTopology) (componentIntegerModule S r)
          (isFlat_moduleEquivalenceInverseComponentIntegerSheaf S r)).inv ≫
        (intDerivedTensorProduct S.totalTopology).tensor.map
          ((((moduleEquivalence S.totalTopology).inverse.mapDerivedCategorySingleFunctor 0).app
            (componentIntegerSheaf S r)).inv) := fun _ => rfl
  rw [hfac, hfac, ← Category.assoc, hinv, Category.assoc, Category.assoc,
    ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, hsingle]

/-- **The identification `g_{n!}ℤ ⊗^L_ℤ - ≅ (g_{n!}ℤ ⊗_ℤ -)^L` is natural in the simplicial
degree.** For a simplex map `θ : ⦋p⦌ ⟶ ⦋q⦌` the derived functor of the sheaf-level action
`integerTensorFace` of `θ`, followed by the identification in degree `p`, is the identification
in degree `q` followed by the derived tensor product with the structure map `g_{q!}ℤ ⟶ g_{p!}ℤ`
placed in degree zero.

The three factors of the identification each contribute one square: the compositor of derived
functors is natural in its outer argument and in its inner one, and the innermost factor is
`integerTensorFlatIso_naturality`. -/
theorem integerTensorAbDerivedIso_naturality {p q : SimplexCategory} (θ : p ⟶ q) :
    derivedNatTrans (integerTensorAb S q) (integerTensorAb S p) (integerTensorFace S θ) ≫
        (integerTensorAbDerivedIso S p).hom =
      (integerTensorAbDerivedIso S q).hom ≫
        (derivedTensor S.totalTopology).map
          ((DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).map
            (integerFace S θ)) := by
  have houter : derivedNatTrans (integerTensorAb S q) (integerTensorAb S p)
          (integerTensorFace S θ) ≫
        (derivedCompIso (moduleEquivalence S.totalTopology).inverse
          ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
            (componentIntegerModule S p) ⋙
            (moduleEquivalence S.totalTopology).functor) (integerTensorAb S p)
          (Iso.refl _)).hom =
      (derivedCompIso (moduleEquivalence S.totalTopology).inverse
          ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
            (componentIntegerModule S q) ⋙
            (moduleEquivalence S.totalTopology).functor) (integerTensorAb S q)
          (Iso.refl _)).hom ≫
        Functor.whiskerLeft (moduleEquivalence S.totalTopology).inverse.mapDerivedCategory
          (derivedNatTrans
            ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
              (componentIntegerModule S q) ⋙
              (moduleEquivalence S.totalTopology).functor)
            ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
              (componentIntegerModule S p) ⋙
              (moduleEquivalence S.totalTopology).functor)
            (Functor.whiskerRight
              ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).map
                ((moduleEquivalence S.totalTopology).inverse.map (integerFace S θ)))
              (moduleEquivalence S.totalTopology).functor)) :=
    derivedCompIso_refl_hom_whiskerLeft (moduleEquivalence S.totalTopology).inverse
      ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
        (componentIntegerModule S q) ⋙
        (moduleEquivalence S.totalTopology).functor)
      ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
        (componentIntegerModule S p) ⋙
        (moduleEquivalence S.totalTopology).functor) _
  have hinner : derivedNatTrans
          ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
            (componentIntegerModule S q) ⋙
            (moduleEquivalence S.totalTopology).functor)
          ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
            (componentIntegerModule S p) ⋙
            (moduleEquivalence S.totalTopology).functor)
          (Functor.whiskerRight
            ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).map
              ((moduleEquivalence S.totalTopology).inverse.map (integerFace S θ)))
            (moduleEquivalence S.totalTopology).functor) ≫
        (derivedCompIso
          ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
            (componentIntegerModule S p))
          (moduleEquivalence S.totalTopology).functor
          ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
            (componentIntegerModule S p) ⋙
            (moduleEquivalence S.totalTopology).functor) (Iso.refl _)).hom =
      (derivedCompIso
          ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
            (componentIntegerModule S q))
          (moduleEquivalence S.totalTopology).functor
          ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
            (componentIntegerModule S q) ⋙
            (moduleEquivalence S.totalTopology).functor) (Iso.refl _)).hom ≫
        Functor.whiskerRight
          (derivedNatTrans
            ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
              (componentIntegerModule S q))
            ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
              (componentIntegerModule S p))
            ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).map
              ((moduleEquivalence S.totalTopology).inverse.map (integerFace S θ))))
          (moduleEquivalence S.totalTopology).functor.mapDerivedCategory :=
    derivedCompIso_refl_hom_whiskerRight
      ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
        (componentIntegerModule S q))
      ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
        (componentIntegerModule S p))
      (moduleEquivalence S.totalTopology).functor _
  have hflat := integerTensorFlatIso_naturality S θ
  have hmid : Functor.whiskerLeft (moduleEquivalence S.totalTopology).inverse.mapDerivedCategory
          (derivedNatTrans
            ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
              (componentIntegerModule S q) ⋙
              (moduleEquivalence S.totalTopology).functor)
            ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
              (componentIntegerModule S p) ⋙
              (moduleEquivalence S.totalTopology).functor)
            (Functor.whiskerRight
              ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).map
                ((moduleEquivalence S.totalTopology).inverse.map (integerFace S θ)))
              (moduleEquivalence S.totalTopology).functor)) ≫
        Functor.whiskerLeft (moduleEquivalence S.totalTopology).inverse.mapDerivedCategory
          (derivedCompIso
            ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
              (componentIntegerModule S p))
            (moduleEquivalence S.totalTopology).functor _ (Iso.refl _)).hom =
      Functor.whiskerLeft (moduleEquivalence S.totalTopology).inverse.mapDerivedCategory
          (derivedCompIso
            ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
              (componentIntegerModule S q))
            (moduleEquivalence S.totalTopology).functor _ (Iso.refl _)).hom ≫
        Functor.whiskerLeft (moduleEquivalence S.totalTopology).inverse.mapDerivedCategory
          (Functor.whiskerRight
            (derivedNatTrans
              ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
                (componentIntegerModule S q))
              ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
                (componentIntegerModule S p))
              ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).map
                ((moduleEquivalence S.totalTopology).inverse.map (integerFace S θ))))
            (moduleEquivalence S.totalTopology).functor.mapDerivedCategory) := by
    rw [whiskerLeft_comp_eq, hinner, ← whiskerLeft_comp_eq]
  have hlast : Functor.whiskerLeft (moduleEquivalence S.totalTopology).inverse.mapDerivedCategory
          (Functor.whiskerRight
            (derivedNatTrans
              ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
                (componentIntegerModule S q))
              ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
                (componentIntegerModule S p))
              ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).map
                ((moduleEquivalence S.totalTopology).inverse.map (integerFace S θ))))
            (moduleEquivalence S.totalTopology).functor.mapDerivedCategory) ≫
        Functor.whiskerLeft (moduleEquivalence S.totalTopology).inverse.mapDerivedCategory
          (Functor.whiskerRight (integerTensorFlatIso S p).hom
            (moduleEquivalence S.totalTopology).functor.mapDerivedCategory) =
      Functor.whiskerLeft (moduleEquivalence S.totalTopology).inverse.mapDerivedCategory
          (Functor.whiskerRight (integerTensorFlatIso S q).hom
            (moduleEquivalence S.totalTopology).functor.mapDerivedCategory) ≫
        Functor.whiskerLeft (moduleEquivalence S.totalTopology).inverse.mapDerivedCategory
          (Functor.whiskerRight
            ((intDerivedTensorProduct S.totalTopology).tensor.map
              ((moduleEquivalence S.totalTopology).inverse.mapDerivedCategory.map
                ((DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).map
                  (integerFace S θ))))
            (moduleEquivalence S.totalTopology).functor.mapDerivedCategory) := by
    rw [whiskerLeft_comp_eq, ← Functor.whiskerRight_comp, hflat, Functor.whiskerRight_comp,
      ← whiskerLeft_comp_eq]
  rw [integerTensorAbDerivedIso_hom S p, integerTensorAbDerivedIso_hom S q]
  exact chain_three _ _ _ _ _ _ _ _ _ _ houter hmid hlast

/-! ### The augmentation

The augmentation `g_{0!}ℤ ⟶ ℤ` of the integral resolution is not a structure map of the
simplicial abelian sheaf of simplices, so the two statements above do not apply to it: its target
is the unit object, where the identification of the derived functor of the tensor product with the
derived tensor product is `unitIntegerTensorFlatIso` and `unitIntegerTensorAbDerivedIso`, built
from the flatness of the constant integer sheaf rather than from that of `g_{n!}ℤ`. The two
identifications have the same three factors, so the two squares below are the two above with the
target end replaced; the flatness of the structure sheaf is the only input that changes.
-/

/-- **The innermost factor of `integerTensorAbDerivedIso` is compatible with the augmentation of
the integral resolution.** This is `integerTensorFlatIso_naturality` for the augmentation
`g_{0!}ℤ ⟶ ℤ` in place of a structure map, whose target identification is therefore the unit one
`unitIntegerTensorFlatIso`.

The last step, which fuses the two coefficient identifications and rewrites the fused map with
the naturality of `CategoryTheory.Functor.mapDerivedCategorySingleFunctor`, is taken in term mode:
the derived tensor product by the unit object and the conjugated functor agree only up to
unfolding a definition, and a `rw` whose motive mentions both builds a goal that is then not
type-correct. -/
theorem integerTensorFlatIso_naturality_augmentation :
    derivedNatTrans
          ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
            (componentIntegerModule S ⦋0⦌))
          ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
            ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S)))
          ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).map
            ((moduleEquivalence S.totalTopology).inverse.map (integerAugmentation S))) ≫
        (unitIntegerTensorFlatIso S).hom =
      (integerTensorFlatIso S ⦋0⦌).hom ≫
        (intDerivedTensorProduct S.totalTopology).tensor.map
          ((moduleEquivalence S.totalTopology).inverse.mapDerivedCategory.map
            ((DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).map
              (integerAugmentation S))) := by
  have hnat : (intDerivedTensorProduct S.totalTopology).tensor.map
          ((DerivedCategory.singleFunctor
            (Stacks.DerivedTensor.RingedSite.Modules (intRingSheaf S.totalTopology)) 0).map
              ((moduleEquivalence S.totalTopology).inverse.map (integerAugmentation S))) ≫
        (flatSingleTensorIso (intRingSheaf S.totalTopology)
          (intDerivedTensorProduct S.totalTopology)
          ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S))
          (isFlat_moduleEquivalenceInverseTotalIntegerSheaf S)).hom =
      (flatSingleTensorIso (intRingSheaf S.totalTopology)
          (intDerivedTensorProduct S.totalTopology) (componentIntegerModule S ⦋0⦌)
          (isFlat_moduleEquivalenceInverseComponentIntegerSheaf S ⦋0⦌)).hom ≫
        derivedNatTrans
          ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
            (componentIntegerModule S ⦋0⦌))
          ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
            ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S)))
          ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).map
            ((moduleEquivalence S.totalTopology).inverse.map (integerAugmentation S))) :=
    flatSingleTensorIso_naturality (intRingSheaf S.totalTopology)
      (intDerivedTensorProduct S.totalTopology)
      (isFlat_moduleEquivalenceInverseComponentIntegerSheaf S ⦋0⦌)
      (isFlat_moduleEquivalenceInverseTotalIntegerSheaf S)
      ((moduleEquivalence S.totalTopology).inverse.map (integerAugmentation S))
  have hsingle : (DerivedCategory.singleFunctor
          (Stacks.DerivedTensor.RingedSite.Modules (intRingSheaf S.totalTopology)) 0).map
        ((moduleEquivalence S.totalTopology).inverse.map (integerAugmentation S)) ≫
      (((moduleEquivalence S.totalTopology).inverse.mapDerivedCategorySingleFunctor 0).app
        (totalIntegerSheaf S)).inv =
    (((moduleEquivalence S.totalTopology).inverse.mapDerivedCategorySingleFunctor 0).app
          (componentIntegerSheaf S ⦋0⦌)).inv ≫
      (moduleEquivalence S.totalTopology).inverse.mapDerivedCategory.map
        ((DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).map
          (integerAugmentation S)) :=
    ((moduleEquivalence S.totalTopology).inverse.mapDerivedCategorySingleFunctor
      0).inv.naturality (integerAugmentation S)
  have hinv : derivedNatTrans
          ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
            (componentIntegerModule S ⦋0⦌))
          ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
            ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S)))
          ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).map
            ((moduleEquivalence S.totalTopology).inverse.map (integerAugmentation S))) ≫
        (flatSingleTensorIso (intRingSheaf S.totalTopology)
          (intDerivedTensorProduct S.totalTopology)
          ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S))
          (isFlat_moduleEquivalenceInverseTotalIntegerSheaf S)).inv =
      (flatSingleTensorIso (intRingSheaf S.totalTopology)
          (intDerivedTensorProduct S.totalTopology) (componentIntegerModule S ⦋0⦌)
          (isFlat_moduleEquivalenceInverseComponentIntegerSheaf S ⦋0⦌)).inv ≫
        (intDerivedTensorProduct S.totalTopology).tensor.map
          ((DerivedCategory.singleFunctor
            (Stacks.DerivedTensor.RingedSite.Modules (intRingSheaf S.totalTopology)) 0).map
              ((moduleEquivalence S.totalTopology).inverse.map (integerAugmentation S))) := by
    calc derivedNatTrans _ _ _ ≫ (flatSingleTensorIso (intRingSheaf S.totalTopology)
            (intDerivedTensorProduct S.totalTopology)
            ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S))
            (isFlat_moduleEquivalenceInverseTotalIntegerSheaf S)).inv
        = ((flatSingleTensorIso (intRingSheaf S.totalTopology)
              (intDerivedTensorProduct S.totalTopology) (componentIntegerModule S ⦋0⦌)
              (isFlat_moduleEquivalenceInverseComponentIntegerSheaf S ⦋0⦌)).inv ≫
            (flatSingleTensorIso (intRingSheaf S.totalTopology)
                (intDerivedTensorProduct S.totalTopology) (componentIntegerModule S ⦋0⦌)
                (isFlat_moduleEquivalenceInverseComponentIntegerSheaf S ⦋0⦌)).hom ≫
              derivedNatTrans _ _ _) ≫
          (flatSingleTensorIso (intRingSheaf S.totalTopology)
            (intDerivedTensorProduct S.totalTopology)
            ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S))
            (isFlat_moduleEquivalenceInverseTotalIntegerSheaf S)).inv := by
          rw [Iso.inv_hom_id_assoc]
      _ = _ := by
          rw [← hnat, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hfac0 : (integerTensorFlatIso S ⦋0⦌).hom =
      (flatSingleTensorIso (intRingSheaf S.totalTopology)
          (intDerivedTensorProduct S.totalTopology) (componentIntegerModule S ⦋0⦌)
          (isFlat_moduleEquivalenceInverseComponentIntegerSheaf S ⦋0⦌)).inv ≫
        (intDerivedTensorProduct S.totalTopology).tensor.map
          ((((moduleEquivalence S.totalTopology).inverse.mapDerivedCategorySingleFunctor 0).app
            (componentIntegerSheaf S ⦋0⦌)).inv) := rfl
  have hfacU : (unitIntegerTensorFlatIso S).hom =
      (flatSingleTensorIso (intRingSheaf S.totalTopology)
          (intDerivedTensorProduct S.totalTopology)
          ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S))
          (isFlat_moduleEquivalenceInverseTotalIntegerSheaf S)).inv ≫
        (intDerivedTensorProduct S.totalTopology).tensor.map
          ((((moduleEquivalence S.totalTopology).inverse.mapDerivedCategorySingleFunctor 0).app
            (totalIntegerSheaf S)).inv) := rfl
  have hmap : (intDerivedTensorProduct S.totalTopology).tensor.map
          ((DerivedCategory.singleFunctor
            (Stacks.DerivedTensor.RingedSite.Modules (intRingSheaf S.totalTopology)) 0).map
              ((moduleEquivalence S.totalTopology).inverse.map (integerAugmentation S))) ≫
        (intDerivedTensorProduct S.totalTopology).tensor.map
          ((((moduleEquivalence S.totalTopology).inverse.mapDerivedCategorySingleFunctor 0).app
            (totalIntegerSheaf S)).inv) =
      (intDerivedTensorProduct S.totalTopology).tensor.map
          ((((moduleEquivalence S.totalTopology).inverse.mapDerivedCategorySingleFunctor 0).app
            (componentIntegerSheaf S ⦋0⦌)).inv) ≫
        (intDerivedTensorProduct S.totalTopology).tensor.map
          ((moduleEquivalence S.totalTopology).inverse.mapDerivedCategory.map
            ((DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).map
              (integerAugmentation S))) :=
    (((intDerivedTensorProduct S.totalTopology).tensor.map_comp _ _).symm.trans
      (congrArg (intDerivedTensorProduct S.totalTopology).tensor.map hsingle)).trans
      ((intDerivedTensorProduct S.totalTopology).tensor.map_comp _ _)
  rw [hfac0, hfacU, reassoc_of% hinv]
  exact (whisker_eq _ hmap).trans (Category.assoc _ _ _).symm

/-- **The identification `g_{n!}ℤ ⊗^L_ℤ - ≅ (g_{n!}ℤ ⊗_ℤ -)^L` is compatible with the
augmentation of the integral resolution.** The derived functor of tensoring with the augmentation
`g_{0!}ℤ ⟶ ℤ`, followed by the unit identification `unitIntegerTensorAbDerivedIso`, is the
identification in degree zero followed by the derived tensor product with the augmentation placed
in degree zero.

This is `integerTensorAbDerivedIso_naturality` with the augmentation in place of a structure map;
the three squares are the same three, the innermost being
`integerTensorFlatIso_naturality_augmentation`. -/
theorem integerTensorAbDerivedIso_naturality_augmentation :
    derivedNatTrans (integerTensorAb S ⦋0⦌) (unitIntegerTensorAb S)
          (Functor.whiskerLeft (moduleEquivalence S.totalTopology).inverse
            (Functor.whiskerRight
              ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).map
                ((moduleEquivalence S.totalTopology).inverse.map (integerAugmentation S)))
              (moduleEquivalence S.totalTopology).functor)) ≫
        (unitIntegerTensorAbDerivedIso S).hom =
      (integerTensorAbDerivedIso S ⦋0⦌).hom ≫
        (derivedTensor S.totalTopology).map
          ((DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).map
            (integerAugmentation S)) := by
  have houter := derivedCompIso_refl_hom_whiskerLeft (moduleEquivalence S.totalTopology).inverse
    ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
      (componentIntegerModule S ⦋0⦌) ⋙
      (moduleEquivalence S.totalTopology).functor)
    ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
        ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S)) ⋙
      (moduleEquivalence S.totalTopology).functor)
    (Functor.whiskerRight
      ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).map
        ((moduleEquivalence S.totalTopology).inverse.map (integerAugmentation S)))
      (moduleEquivalence S.totalTopology).functor)
  have hinner := derivedCompIso_refl_hom_whiskerRight
    ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
      (componentIntegerModule S ⦋0⦌))
    ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
      ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S)))
    (moduleEquivalence S.totalTopology).functor
    ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).map
      ((moduleEquivalence S.totalTopology).inverse.map (integerAugmentation S)))
  have hmid := (whiskerLeft_comp_eq
      (moduleEquivalence S.totalTopology).inverse.mapDerivedCategory _ _).trans
    ((congrArg (Functor.whiskerLeft
        (moduleEquivalence S.totalTopology).inverse.mapDerivedCategory) hinner).trans
      (whiskerLeft_comp_eq
        (moduleEquivalence S.totalTopology).inverse.mapDerivedCategory _ _).symm)
  have hlast := (whiskerLeft_comp_eq
      (moduleEquivalence S.totalTopology).inverse.mapDerivedCategory _ _).trans
    ((congrArg (Functor.whiskerLeft
          (moduleEquivalence S.totalTopology).inverse.mapDerivedCategory)
        (((Functor.whiskerRight_comp _ _
              (moduleEquivalence S.totalTopology).functor.mapDerivedCategory).symm.trans
            (congrArg (fun t => Functor.whiskerRight t
                (moduleEquivalence S.totalTopology).functor.mapDerivedCategory)
              (integerTensorFlatIso_naturality_augmentation S))).trans
          (Functor.whiskerRight_comp _ _
            (moduleEquivalence S.totalTopology).functor.mapDerivedCategory))).trans
      (whiskerLeft_comp_eq
        (moduleEquivalence S.totalTopology).inverse.mapDerivedCategory _ _).symm)
  rw [integerTensorAbDerivedIso_hom S ⦋0⦌, unitIntegerTensorAbDerivedIso_hom S]
  exact chain_three _ _ _ _ _ _ _ _ _ _ houter hmid hlast

end CategoryTheory.SimplicialSiteSituation

end
