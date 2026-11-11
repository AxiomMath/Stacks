module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.DerivedExternalTensorProduct
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.DerivedColimitUnitOnKProjective

/-!
# The transposition identity of the derived product formula at a pair of generators

Let `C₁` and `C₂` be small categories with the chaotic topology and `R` a commutative ring.
`Stacks.CategoryHomology.derivedExternalTensorComparison` is the canonical comparison of
Stacks 08QB, the two-variable mate `CategoryTheory.Adjunction.externalMate` of the two derived
identifications `g_i^{-1} ∘ π_i^{-1} = π^{-1}`.  At a pair of compact generators
`j_{U!}P[0]`, `j_{V!}Q[0]` with projective coefficients the source and the target of that
comparison are both `(P ⊗_R Q)[0]`, and
`Stacks.CategoryHomology.derivedExternalTensorGeneratorIso` is the resulting isomorphism;
`CategoryTheory.Adjunction.isIso_externalMate_of_unit_comp_map` turns the invertibility of the
comparison there into one identity, the *transposition identity*

`η(S₁M₁ ⊗ S₂M₂) ≫ π^{-1}(generatorIso) = ((S₁η₁ ≫ α₁) ⊗ (S₂η₂ ≫ α₂)) ≫ μ(π^{-1})`,

in which `η`, `η₁`, `η₂` are the three derived lower-shriek units, `α₁`, `α₂` the two derived
identifications and `μ` the tensorator of the derived constant diagram.

This file carries the legs of that identity which concern the unit and the two `α`-factors.

## Main results

* `Stacks.CategoryHomology.unit_app_comp_map_totalDerivedColimitSingleFreeYonedaIso`: **the
  derived lower-shriek unit at a free generator placed in degree zero, computed outright.**
  Composed with the derived constant diagram of
  `Stacks.CategoryHomology.totalDerivedColimitSingleFreeYonedaIso`, it is the
  `DerivedCategory.Q`-image of a morphism of complexes, followed by the canonical factorization
  of the derived constant diagram read backwards; the companion
  `..._factors` is the same with that factorization cancelled, so that the whole composite is a
  `DerivedCategory.Q`-image.
* `Stacks.CategoryHomology.derivedConstCompProjFstIso_hom_app_Q_comp_factors` and its `Snd`
  companion: **the derived identification `g_i^{-1} ∘ π_i^{-1} = π^{-1}` at the image of a
  complex, with the factorization of the derived constant diagram on the product site cancelled
  against the third factor of
  `Stacks.CategoryHomology.derivedConstCompProjFstIso_hom_app_Q`.**
* `Stacks.CategoryHomology.alpha_fst_leg` and `Stacks.CategoryHomology.alpha_snd_leg`: **each
  tensor factor of the right-hand side of the transposition identity is the
  `DerivedCategory.Q`-image of a restriction**, namely of whatever morphism of complexes the
  derived unit on the factor site produces.  Together with the two lemmas above, taken at the
  generator `j_{U!}P[0]`, this computes both `α`-factors of the transposition identity in terms
  of the underived unit of `colim ⊣ const`.

## Implementation notes

`CategoryTheory.Functor.mapDerivedCategoryFactors` for a composite of two exact functors, and the
identity `π_1^{-1} ⋙ g_1^{-1} = π^{-1}` of diagram categories which holds by `rfl`, give two
spellings of one and the same object which agree only at *default* transparency.  A rewriting
tactic whose motive abstracts a morphism at such an object reports the target as not type-correct
under the `implicit` transparency level.  The cancellations that meet that seam are therefore
assembled from `Eq.trans`, `congrArg` with hand-written motives, `CategoryTheory.Category.assoc`
and `CategoryTheory.Iso.eq_comp_inv` as *terms*, exactly as in
`Stacks.CategoryHomology.totalDerivedColimitAdjunction_unit_app_Q_single` and
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryFactorsh_hom_app_comp_quotientCompQhIso_hom`.

The remaining legs -- the tensorator of the derived constant diagram, computed by
`CategoryTheory.Functor.mu_constMapDerivedCategory_derivedTensorIso`, and the defining property
of the underived mate in degree zero -- are assembled with these in the sibling module
`DerivedExternalTensorProductFormula` (in `StacksDraft.CategoryTheory.Sites.Cohomology`,
under `CategoryHomology`), which proves Stacks 08QB.

## References

* [Stacks Project, Tag 08QB](https://stacks.math.columbia.edu/tag/08QB)
* [Stacks Project, Tag 08Q6](https://stacks.math.columbia.edu/tag/08Q6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CochainComplex.KFlatMonoidal CochainComplex.KFlatBifunctor

namespace Stacks.CategoryHomology

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] CochainComplex.symmetricCategory

universe u

section

section OneSite

variable {C : Type u} [SmallCategory C] {R : Type u} [CommRing R]

/-- **The derived unit of `Lπ_! ⊣ π^{-1}` at a free generator placed in degree zero, read
through the computation of derived lower shriek there.**  Composed with the derived constant
diagram of `Stacks.CategoryHomology.totalDerivedColimitSingleFreeYonedaIso`, the derived unit is
`DerivedCategory.Q` of a morphism of complexes: the underived unit of `colim ⊣ const` at the free
diagram, the degreewise comparison of the constant diagram read backwards, and the constant
diagram of the identification of the colimit of a free diagram with its coefficients.

This is `Stacks.CategoryHomology.totalDerivedColimitAdjunction_unit_app_Q_single` with the second
factor of `totalDerivedColimitSingleFreeYonedaIso` moved across
`CategoryTheory.Functor.mapDerivedCategoryFactors` by its naturality. -/
lemma unit_app_comp_map_totalDerivedColimitSingleFreeYonedaIso
    (W : C) (N : ModuleCat.{u} R) [Projective N] :
    (totalDerivedColimitAdjunction C (ModuleCat.{u} R)).unit.app
          (DerivedCategory.Q.obj
            ((HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} R)
              (ComplexShape.up ℤ) 0).obj (Presheaf.freeYoneda W N))) ≫
        (Functor.const Cᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategory.map
          (totalDerivedColimitSingleFreeYonedaIso W N).hom =
      DerivedCategory.Q.map
          ((HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} R)
                (ComplexShape.up ℤ) 0).map (colimConstAdj.unit.app (Presheaf.freeYoneda W N)) ≫
            ((HomologicalComplex.singleMapHomologicalComplex
                (Functor.const Cᵒᵖ : ModuleCat.{u} R ⥤ _) (ComplexShape.up ℤ) 0).app
              (colimit (Presheaf.freeYoneda W N))).inv ≫
              ((Functor.const Cᵒᵖ : ModuleCat.{u} R ⥤ _).mapHomologicalComplex
                  (ComplexShape.up ℤ)).map
                ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).map
                  (colimFreeYonedaIso W N).hom)) ≫
        (Functor.const Cᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategoryFactors.inv.app
          ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj N) := by
  have := freeYonedaProjective W N
  have hiso : (totalDerivedColimitSingleFreeYonedaIso W N).hom =
      (totalDerivedColimitObjSingleIso C (ModuleCat.{u} R)
          (Presheaf.freeYoneda W N)).hom ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).map
            (colimFreeYonedaIso W N).hom) := rfl
  have hnat := (Functor.const Cᵒᵖ :
      ModuleCat.{u} R ⥤ _).mapDerivedCategoryFactors.inv.naturality
    ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).map
      (colimFreeYonedaIso W N).hom)
  dsimp only [Functor.comp_map] at hnat
  rw [hiso, CategoryTheory.Functor.map_comp, ← Category.assoc,
    totalDerivedColimitAdjunction_unit_app_Q_single]
  simp only [Category.assoc, CategoryTheory.Functor.map_comp]
  rw [hnat]
  rfl

/-- `Stacks.CategoryHomology.unit_app_comp_map_totalDerivedColimitSingleFreeYonedaIso` with the
comparison of the derived constant diagram with its degreewise action composed on the right, so
that the whole composite is a `DerivedCategory.Q`-image. -/
lemma unit_app_comp_map_totalDerivedColimitSingleFreeYonedaIso_factors
    (W : C) (N : ModuleCat.{u} R) [Projective N] :
    (totalDerivedColimitAdjunction C (ModuleCat.{u} R)).unit.app
          (DerivedCategory.Q.obj
            ((HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} R)
              (ComplexShape.up ℤ) 0).obj (Presheaf.freeYoneda W N))) ≫
        (Functor.const Cᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategory.map
            (totalDerivedColimitSingleFreeYonedaIso W N).hom ≫
          (Functor.const Cᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategoryFactors.hom.app
            ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj N) =
      DerivedCategory.Q.map
        ((HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} R)
              (ComplexShape.up ℤ) 0).map (colimConstAdj.unit.app (Presheaf.freeYoneda W N)) ≫
          ((HomologicalComplex.singleMapHomologicalComplex
              (Functor.const Cᵒᵖ : ModuleCat.{u} R ⥤ _) (ComplexShape.up ℤ) 0).app
            (colimit (Presheaf.freeYoneda W N))).inv ≫
            ((Functor.const Cᵒᵖ : ModuleCat.{u} R ⥤ _).mapHomologicalComplex
                (ComplexShape.up ℤ)).map
              ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).map
                (colimFreeYonedaIso W N).hom)) := by
  rw [← Category.assoc, unit_app_comp_map_totalDerivedColimitSingleFreeYonedaIso,
    Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

end OneSite

variable (C₁ : Type u) [SmallCategory C₁] (C₂ : Type u) [SmallCategory C₂] (R : Type u) [CommRing R]

/-- **The derived identification `g₁^{-1} ∘ π_1^{-1} = π^{-1}` at the image of a complex, with
the comparison of the derived constant diagram on the product site composed on the right.**  The
third factor of `Stacks.CategoryHomology.derivedConstCompProjFstIso_hom_app_Q` is cancelled, so
what is left is the restriction of the comparison on `C₁` followed by the comparison for the
restriction.

Term mode: the two spellings `g₁^{-1}(π_1^{-1}K)` and `π^{-1}K` of one complex of diagrams agree
only at *default* transparency, and a rewriting tactic cancelling the two comparisons there
reports the target as not type-correct. -/
lemma derivedConstCompProjFstIso_hom_app_Q_comp_factors
    (X : CochainComplex (ModuleCat.{u} R) ℤ) :
    (derivedConstCompProjFstIso C₁ C₂ R).hom.app (DerivedCategory.Q.obj X) ≫
        (Functor.const (C₁ × C₂)ᵒᵖ :
          ModuleCat.{u} R ⥤ _).mapDerivedCategoryFactors.hom.app X =
      (projFstInverseImage C₁ C₂ R).mapDerivedCategory.map
          ((Functor.const C₁ᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategoryFactors.hom.app X) ≫
        (projFstInverseImage C₁ C₂ R).mapDerivedCategoryFactors.hom.app
          (((Functor.const C₁ᵒᵖ : ModuleCat.{u} R ⥤ _).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj X) :=
  (Iso.eq_comp_inv ((Functor.const (C₁ × C₂)ᵒᵖ :
      ModuleCat.{u} R ⥤ _).mapDerivedCategoryFactors.app X)).mp
    ((derivedConstCompProjFstIso_hom_app_Q C₁ C₂ R X).trans (Category.assoc _ _ _).symm)

/-- **The derived identification `g₂^{-1} ∘ π_2^{-1} = π^{-1}` at the image of a complex, with
the comparison of the derived constant diagram on the product site composed on the right.**  The
companion of
`Stacks.CategoryHomology.derivedConstCompProjFstIso_hom_app_Q_comp_factors`. -/
lemma derivedConstCompProjSndIso_hom_app_Q_comp_factors
    (X : CochainComplex (ModuleCat.{u} R) ℤ) :
    (derivedConstCompProjSndIso C₁ C₂ R).hom.app (DerivedCategory.Q.obj X) ≫
        (Functor.const (C₁ × C₂)ᵒᵖ :
          ModuleCat.{u} R ⥤ _).mapDerivedCategoryFactors.hom.app X =
      (projSndInverseImage C₁ C₂ R).mapDerivedCategory.map
          ((Functor.const C₂ᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategoryFactors.hom.app X) ≫
        (projSndInverseImage C₁ C₂ R).mapDerivedCategoryFactors.hom.app
          (((Functor.const C₂ᵒᵖ : ModuleCat.{u} R ⥤ _).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj X) :=
  (Iso.eq_comp_inv ((Functor.const (C₁ × C₂)ᵒᵖ :
      ModuleCat.{u} R ⥤ _).mapDerivedCategoryFactors.app X)).mp
    ((derivedConstCompProjSndIso_hom_app_Q C₁ C₂ R X).trans (Category.assoc _ _ _).symm)

/-- **One `α`-factor of the transposition identity, in the first variable.**  Given a morphism
`t` out of `Lπ_{1,!}` of a generator which the derived unit turns into the
`DerivedCategory.Q`-image of a morphism `g` of complexes, the first tensor factor of the
right-hand side of the transposition identity, followed by the comparison of the derived constant
diagram on the product site with its degreewise action, is the `DerivedCategory.Q`-image of the
restriction of `g` along the first projection.

The three steps are the naturality of
`Stacks.CategoryHomology.derivedConstCompProjFstIso`, the computation
`Stacks.CategoryHomology.derivedConstCompProjFstIso_hom_app_Q` of that identification at the
image of a complex, and the naturality of
`CategoryTheory.Functor.mapDerivedCategoryFactors` for the restriction. -/
lemma alpha_fst_leg (U : C₁) (P : ModuleCat.{u} R) [Projective P]
    (X : CochainComplex (ModuleCat.{u} R) ℤ)
    (t : (totalDerivedColimit C₁ (ModuleCat.{u} R)).obj
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single (C₁ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
            (Presheaf.freeYoneda U P))) ⟶ DerivedCategory.Q.obj X)
    (g : (HomologicalComplex.single (C₁ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
        (Presheaf.freeYoneda U P) ⟶
      ((Functor.const C₁ᵒᵖ : ModuleCat.{u} R ⥤ _).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj X)
    (hg : (totalDerivedColimitAdjunction C₁ (ModuleCat.{u} R)).unit.app
            (DerivedCategory.Q.obj
              ((HomologicalComplex.single (C₁ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
                (Presheaf.freeYoneda U P))) ≫
          (Functor.const C₁ᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategory.map t ≫
            (Functor.const C₁ᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategoryFactors.hom.app X =
        DerivedCategory.Q.map g) :
    (projFstInverseImage C₁ C₂ R).mapDerivedCategory.map
          ((totalDerivedColimitAdjunction C₁ (ModuleCat.{u} R)).unit.app
            (DerivedCategory.Q.obj
              ((HomologicalComplex.single (C₁ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
                (Presheaf.freeYoneda U P)))) ≫
        (derivedConstCompProjFstIso C₁ C₂ R).hom.app
            ((totalDerivedColimit C₁ (ModuleCat.{u} R)).obj
              (DerivedCategory.Q.obj
                ((HomologicalComplex.single (C₁ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
                  (Presheaf.freeYoneda U P)))) ≫
          (Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategory.map t ≫
            (Functor.const (C₁ × C₂)ᵒᵖ :
              ModuleCat.{u} R ⥤ _).mapDerivedCategoryFactors.hom.app X =
      (projFstDerivedSingleIso C₁ C₂ R (Presheaf.freeYoneda U P)).hom ≫
        DerivedCategory.Q.map
          (((HomologicalComplex.singleMapHomologicalComplex (projFstInverseImage C₁ C₂ R)
                (ComplexShape.up ℤ) 0).app (Presheaf.freeYoneda U P)).inv ≫
            ((projFstInverseImage C₁ C₂ R).mapHomologicalComplex (ComplexShape.up ℤ)).map g) := by
  have hnat := (derivedConstCompProjFstIso C₁ C₂ R).hom.naturality t
  dsimp only [Functor.comp_map] at hnat
  have hsplit := congrArg (projFstInverseImage C₁ C₂ R).mapDerivedCategory.map hg
  simp only [CategoryTheory.Functor.map_comp] at hsplit
  have hAnat := (projFstInverseImage C₁ C₂ R).mapDerivedCategoryFactors.hom.naturality g
  dsimp only [Functor.comp_map] at hAnat
  have hpf : (projFstDerivedSingleIso C₁ C₂ R (Presheaf.freeYoneda U P)).hom =
      (projFstInverseImage C₁ C₂ R).mapDerivedCategoryFactors.hom.app
          ((HomologicalComplex.single (C₁ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
            (Presheaf.freeYoneda U P)) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex (projFstInverseImage C₁ C₂ R)
            (ComplexShape.up ℤ) 0).app (Presheaf.freeYoneda U P)).hom := rfl
  rw [hpf, ← reassoc_of% hnat, derivedConstCompProjFstIso_hom_app_Q_comp_factors]
  refine Eq.trans ((Category.assoc _ _ _).symm.trans
    (((Category.assoc _ _ _).symm.trans
        (congrArg (fun s => s ≫ (projFstInverseImage C₁ C₂ R).mapDerivedCategoryFactors.hom.app
            (((Functor.const C₁ᵒᵖ : ModuleCat.{u} R ⥤ _).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj X))
          ((Category.assoc _ _ _).trans hsplit))).trans hAnat)) ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  exact congrArg (fun s => (projFstInverseImage C₁ C₂ R).mapDerivedCategoryFactors.hom.app
      ((HomologicalComplex.single (C₁ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
        (Presheaf.freeYoneda U P)) ≫ s)
    ((congrArg DerivedCategory.Q.map (Iso.hom_inv_id_assoc _ _)).symm.trans
      (DerivedCategory.Q.map_comp _ _))

/-- **One `α`-factor of the transposition identity, in the second variable.**  The companion of
`Stacks.CategoryHomology.alpha_fst_leg`. -/
lemma alpha_snd_leg (V : C₂) (Q : ModuleCat.{u} R) [Projective Q]
    (X : CochainComplex (ModuleCat.{u} R) ℤ)
    (t : (totalDerivedColimit C₂ (ModuleCat.{u} R)).obj
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single (C₂ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
            (Presheaf.freeYoneda V Q))) ⟶ DerivedCategory.Q.obj X)
    (g : (HomologicalComplex.single (C₂ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
        (Presheaf.freeYoneda V Q) ⟶
      ((Functor.const C₂ᵒᵖ : ModuleCat.{u} R ⥤ _).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj X)
    (hg : (totalDerivedColimitAdjunction C₂ (ModuleCat.{u} R)).unit.app
            (DerivedCategory.Q.obj
              ((HomologicalComplex.single (C₂ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
                (Presheaf.freeYoneda V Q))) ≫
          (Functor.const C₂ᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategory.map t ≫
            (Functor.const C₂ᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategoryFactors.hom.app X =
        DerivedCategory.Q.map g) :
    (projSndInverseImage C₁ C₂ R).mapDerivedCategory.map
          ((totalDerivedColimitAdjunction C₂ (ModuleCat.{u} R)).unit.app
            (DerivedCategory.Q.obj
              ((HomologicalComplex.single (C₂ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
                (Presheaf.freeYoneda V Q)))) ≫
        (derivedConstCompProjSndIso C₁ C₂ R).hom.app
            ((totalDerivedColimit C₂ (ModuleCat.{u} R)).obj
              (DerivedCategory.Q.obj
                ((HomologicalComplex.single (C₂ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
                  (Presheaf.freeYoneda V Q)))) ≫
          (Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategory.map t ≫
            (Functor.const (C₁ × C₂)ᵒᵖ :
              ModuleCat.{u} R ⥤ _).mapDerivedCategoryFactors.hom.app X =
      (projSndDerivedSingleIso C₁ C₂ R (Presheaf.freeYoneda V Q)).hom ≫
        DerivedCategory.Q.map
          (((HomologicalComplex.singleMapHomologicalComplex (projSndInverseImage C₁ C₂ R)
                (ComplexShape.up ℤ) 0).app (Presheaf.freeYoneda V Q)).inv ≫
            ((projSndInverseImage C₁ C₂ R).mapHomologicalComplex (ComplexShape.up ℤ)).map g) := by
  have hnat := (derivedConstCompProjSndIso C₁ C₂ R).hom.naturality t
  dsimp only [Functor.comp_map] at hnat
  have hsplit := congrArg (projSndInverseImage C₁ C₂ R).mapDerivedCategory.map hg
  simp only [CategoryTheory.Functor.map_comp] at hsplit
  have hAnat := (projSndInverseImage C₁ C₂ R).mapDerivedCategoryFactors.hom.naturality g
  dsimp only [Functor.comp_map] at hAnat
  have hpf : (projSndDerivedSingleIso C₁ C₂ R (Presheaf.freeYoneda V Q)).hom =
      (projSndInverseImage C₁ C₂ R).mapDerivedCategoryFactors.hom.app
          ((HomologicalComplex.single (C₂ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
            (Presheaf.freeYoneda V Q)) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex (projSndInverseImage C₁ C₂ R)
            (ComplexShape.up ℤ) 0).app (Presheaf.freeYoneda V Q)).hom := rfl
  rw [hpf, ← reassoc_of% hnat, derivedConstCompProjSndIso_hom_app_Q_comp_factors]
  refine Eq.trans ((Category.assoc _ _ _).symm.trans
    (((Category.assoc _ _ _).symm.trans
        (congrArg (fun s => s ≫ (projSndInverseImage C₁ C₂ R).mapDerivedCategoryFactors.hom.app
            (((Functor.const C₂ᵒᵖ : ModuleCat.{u} R ⥤ _).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj X))
          ((Category.assoc _ _ _).trans hsplit))).trans hAnat)) ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  exact congrArg (fun s => (projSndInverseImage C₁ C₂ R).mapDerivedCategoryFactors.hom.app
      ((HomologicalComplex.single (C₂ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
        (Presheaf.freeYoneda V Q)) ≫ s)
    ((congrArg DerivedCategory.Q.map (Iso.hom_inv_id_assoc _ _)).symm.trans
      (DerivedCategory.Q.map_comp _ _))

end

end Stacks.CategoryHomology

end
